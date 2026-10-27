module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.CanonicalHeart
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltBaumComb

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
  Equiv

variable {n : ℕ}

theorem altBaumY_injective (hn : Odd n) :
    Function.Injective (altBaumY hn : Fin n → evenWeight n) := by
  intro x y h
  by_contra hxy
  have := congrArg (fun v : evenWeight n => (v : Fin n → ZMod 2) x) h
  simp only [altBaumY_apply, if_true, if_neg hxy] at this
  exact absurd this (by decide)

theorem eq_one_of_evenWeightPerm_eq_self (hn : Odd n) {σ : Perm (Fin n)}
    (h : ∀ v : evenWeight n, evenWeightPerm σ v = v) : σ = 1 := by
  refine Equiv.ext fun x => ?_
  have := h (altBaumY hn x)
  rw [evenWeightPerm_altBaumY] at this
  exact altBaumY_injective hn this

theorem eq_zero_of_alt_fixed (hn : Odd n) (h4 : 4 ≤ n) {v : evenWeight n}
    (h : ∀ σ ∈ alternatingGroup (Fin n), evenWeightPerm σ v = v) : v = 0 := by
  have h0 := altHeart_fixed_eq_zero h4 v fun σ hσ => by rw [h σ hσ]
  have : (QuotientAddGroup.mk v : altHeart n) = QuotientAddGroup.mk 0 := by
    rw [h0]; rfl
  exact altHeart_mk_injective hn this

theorem evenWeight_irreducible (hn : Odd n) (h4 : 4 ≤ n) (S : AddSubgroup (evenWeight n))
    (hS : ∀ σ ∈ alternatingGroup (Fin n), ∀ v ∈ S, evenWeightPerm σ v ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  let ε : evenWeight n ≃+ altHeart n :=
    AddEquiv.ofBijective (QuotientAddGroup.mk' (evenWeightOnes n))
      ⟨altHeart_mk_injective hn, QuotientAddGroup.mk_surjective⟩
  have hε : ∀ x : evenWeight n, ε x = (QuotientAddGroup.mk x : altHeart n) := fun x => rfl
  have hmem : ∀ x : evenWeight n, (QuotientAddGroup.mk x : altHeart n) ∈ S.map ε.toAddMonoidHom ↔
      x ∈ S := by
    intro x
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := ε.injective (hyx.trans (hε x).symm)
      rw [← this]; exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have key := altHeart_irreducible h4 (S.map ε.toAddMonoidHom) fun σ hσ x hx =>
    (hmem _).2 (hS σ hσ x ((hmem x).1 hx))
  rcases key with h | h
  · left
    rw [AddSubgroup.eq_bot_iff_forall]
    intro x hx
    have h1 : (QuotientAddGroup.mk x : altHeart n) ∈ S.map ε.toAddMonoidHom := (hmem x).2 hx
    rw [h, AddSubgroup.mem_bot] at h1
    exact altHeart_mk_injective hn (by rw [h1]; rfl)
  · right
    rw [eq_top_iff]
    intro x _
    have h1 : (QuotientAddGroup.mk x : altHeart n) ∈ S.map ε.toAddMonoidHom := by rw [h]; trivial
    exact (hmem x).1 h1

section Natural

variable {G : Type*} [Group G]

@[expose] def altBlockImage {U : Subgroup G} (β : ↥U →* Multiplicative (evenWeight n)) (W : Subgroup G) :
    AddSubgroup (evenWeight n) :=
  AddSubgroup.toSubgroup'.symm ((W.subgroupOf U).map β)

theorem mem_altBlockImage {U : Subgroup G} {β : ↥U →* Multiplicative (evenWeight n)} {W : Subgroup G}
    {v : evenWeight n} :
    v ∈ altBlockImage β W ↔ ∃ w : ↥U, (w : G) ∈ W ∧ β w = Multiplicative.ofAdd v := by
  constructor
  · rintro ⟨w, hw, hwv⟩
    exact ⟨w, hw, hwv⟩
  · rintro ⟨w, hw, hwv⟩
    exact ⟨w, hw, hwv⟩

theorem natural_block_facts {Y U : Subgroup G} (hn : Odd n) (h4 : 4 ≤ n)
    (α : ↥Y →* alternatingGroup (Fin n)) (hα : Function.Surjective α)
    (β : ↥U →* Multiplicative (evenWeight n)) (hβ : Function.Injective β)
    (hUN : ∀ y ∈ Y, ∀ u ∈ U, y * u * y⁻¹ ∈ U)
    (hβe : ∀ (ℓ : ↥Y) (u v : ↥U), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) = evenWeightPerm (α ℓ : Perm (Fin n)) (Multiplicative.toAdd (β u)))
    (hne : U ≠ ⊥) :
    Function.Surjective β ∧
      (∀ W : Subgroup G, W ≤ U → (∀ y ∈ Y, ∀ w ∈ W, y * w * y⁻¹ ∈ W) → W = ⊥ ∨ W = U) ∧
      (∀ z ∈ U, (∀ y ∈ Y, y * z * y⁻¹ = z) → z = 1) := by
  have key : ∀ W : Subgroup G, W ≤ U → (∀ y ∈ Y, ∀ w ∈ W, y * w * y⁻¹ ∈ W) →
      (altBlockImage β W = ⊥ → W = ⊥) ∧ (altBlockImage β W = ⊤ → ∀ u : ↥U, (u : G) ∈ W) ∧
        (altBlockImage β W = ⊥ ∨ altBlockImage β W = ⊤) := by
    intro W hWU hWN
    have hinv : ∀ σ ∈ alternatingGroup (Fin n), ∀ v ∈ altBlockImage β W,
        evenWeightPerm σ v ∈ altBlockImage β W := by
      intro σ hσ v hv
      obtain ⟨w, hwW, hwv⟩ := mem_altBlockImage.1 hv
      obtain ⟨y, hy⟩ := hα ⟨σ, hσ⟩
      have hyw : (y : G) * w * (y : G)⁻¹ ∈ U := hUN y y.2 w w.2
      refine mem_altBlockImage.2 ⟨⟨(y : G) * w * (y : G)⁻¹, hyw⟩, hWN y y.2 w hwW, ?_⟩
      have h1 := hβe y w ⟨(y : G) * w * (y : G)⁻¹, hyw⟩ rfl
      have h2 : (α y : Perm (Fin n)) = σ := congrArg Subtype.val hy
      apply Multiplicative.toAdd.injective
      rw [h1, h2, hwv]
      rfl
    refine ⟨fun hbot => ?_, fun htop u => ?_, evenWeight_irreducible hn h4 _ hinv⟩
    · rw [Subgroup.eq_bot_iff_forall]
      intro w hw
      have h2 : Multiplicative.toAdd (β ⟨w, hWU hw⟩) ∈ altBlockImage β W :=
        mem_altBlockImage.2 ⟨⟨w, hWU hw⟩, hw, rfl⟩
      rw [hbot, AddSubgroup.mem_bot] at h2
      have h3 : β ⟨w, hWU hw⟩ = 1 := Multiplicative.toAdd.injective (by rw [h2]; rfl)
      have := hβ (h3.trans (map_one β).symm)
      exact congrArg Subtype.val this
    · have h1 : Multiplicative.toAdd (β u) ∈ altBlockImage β W := by rw [htop]; trivial
      obtain ⟨w, hw, hwu⟩ := mem_altBlockImage.1 h1
      have : w = u := hβ (by simpa using hwu)
      rw [← this]; exact hw
  obtain ⟨hb1, hb2, hb3⟩ := key U le_rfl hUN
  have hsurj : Function.Surjective β := by
    rcases hb3 with h | h
    · exact absurd (hb1 h) hne
    · intro v
      have h1 : Multiplicative.toAdd v ∈ altBlockImage β U := by rw [h]; trivial
      obtain ⟨w, -, hwu⟩ := mem_altBlockImage.1 h1
      exact ⟨w, by simpa using hwu⟩
  refine ⟨hsurj, fun W hWU hWN => ?_, fun z hz hzc => ?_⟩
  · obtain ⟨c1, c2, c3⟩ := key W hWU hWN
    rcases c3 with h | h
    · exact Or.inl (c1 h)
    · exact Or.inr (le_antisymm hWU fun u hu => c2 h ⟨u, hu⟩)
  · set u : ↥U := ⟨z, hz⟩
    have hfix : ∀ σ ∈ alternatingGroup (Fin n),
        evenWeightPerm σ (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β u) := by
      intro σ hσ
      obtain ⟨y, hy⟩ := hα ⟨σ, hσ⟩
      have h2 : (α y : Perm (Fin n)) = σ := congrArg Subtype.val hy
      have h1 := hβe y u u (by simp only [u]; exact (hzc y y.2).symm)
      rw [h2] at h1
      exact h1.symm
    have h0 := eq_zero_of_alt_fixed hn h4 hfix
    have : β u = 1 := Multiplicative.toAdd.injective (by rw [h0]; rfl)
    have := hβ (this.trans (map_one β).symm)
    exact congrArg Subtype.val this

end Natural

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
