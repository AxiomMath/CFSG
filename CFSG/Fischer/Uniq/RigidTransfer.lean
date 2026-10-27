module

public import CFSG.Fischer.Uniq.StabBound
public import CFSG.Fischer.Uniq.PolarIntrinsic

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}

theorem mem_range_innerTau_of_preserves (hF : Pair Y F) (hidx : (innerTau hF).range.index = 2)
    {𝒮₀ 𝒮₁ : Set (Set F)} (hfin : 𝒮₀.Finite) (hdisj : Disjoint 𝒮₀ 𝒮₁)
    (hinv : ∀ g : Y, ∀ T ∈ 𝒮₀, ⇑(Pair.conjPerm hF g) '' T ∈ 𝒮₀)
    {u : tauGroup hF} {T₀ : Set F} (hT₀ : T₀ ∈ 𝒮₀) (hu : ⇑(u : Equiv.Perm F) '' T₀ ∈ 𝒮₁)
    (σ : tauGroup hF) (hσ : ∀ T ∈ 𝒮₀, ⇑(σ : Equiv.Perm F) '' T ∈ 𝒮₀) :
    σ ∈ (innerTau hF).range := by
  by_contra hσI
  have huI : u ∉ (innerTau hF).range := by
    rintro ⟨g, rfl⟩
    exact Set.disjoint_left.1 hdisj (hinv g T₀ hT₀) hu
  have hσu : σ * u ∈ (innerTau hF).range := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    exact iff_of_false hσI huI
  obtain ⟨g, hg⟩ := hσu
  have h1 : ⇑(σ : Equiv.Perm F) '' (⇑(u : Equiv.Perm F) '' T₀) ∈ 𝒮₀ := by
    have := hinv g T₀ hT₀
    rw [show Pair.conjPerm hF g = ((σ * u : tauGroup hF) : Equiv.Perm F) from
      congrArg Subtype.val hg] at this
    rw [Set.image_image]
    exact this
  have hsurj : (fun T => ⇑(σ : Equiv.Perm F) '' T) '' 𝒮₀ = 𝒮₀ := by
    apply Set.eq_of_subset_of_ncard_le
    · rintro _ ⟨T, hT, rfl⟩
      exact hσ T hT
    · rw [Set.ncard_image_of_injective _ (Set.image_injective.2 (σ : Equiv.Perm F).injective)]
    · exact hfin
  rw [← hsurj] at h1
  obtain ⟨T, hT, hTe⟩ := h1
  have : T = ⇑(u : Equiv.Perm F) '' T₀ :=
    Set.image_injective.2 (σ : Equiv.Perm F).injective hTe
  rw [this] at hT
  exact Set.disjoint_left.1 hdisj hT hu

theorem tauGroup_mem_localClass_iff (hE : Pair X E) {σ : Equiv.Perm E} (hσ : σ ∈ tauGroup hE)
    (x y : E) : (x : X) ∈ LocalClass E y ↔ ((σ x : E) : X) ∈ LocalClass E (σ y : X) := by
  have hc := tauGroup_commute_iff hE hσ x y
  have hne : (x : X) ≠ y ↔ ((σ x : E) : X) ≠ σ y := by
    rw [ne_eq, ne_eq, Subtype.val_inj, Subtype.val_inj, σ.injective.eq_iff]
  exact ⟨fun h => ⟨(σ x).2, hne.1 h.2.1, hc.1 h.2.2⟩, fun h => ⟨x.2, hne.2 h.2.1, hc.2 h.2.2⟩⟩

section Star

variable (hF : Pair Y F) (hE : Pair X E) {d : X} (hd : d ∈ E)

theorem resStar_mul_mul (σ : stabT hE hd) (p q : LocalClass E d) :
    ((resStar hE hd σ ⟨_, LocalPoints.mul_mul_mem_localClass hE p q⟩ : LocalClass E d) : X) =
      (resStar hE hd σ p : X) * resStar hE hd σ q * resStar hE hd σ p :=
  congrArg Subtype.val ((σ : tauGroup hE).2 ⟨p, p.2.1⟩ ⟨q, q.2.1⟩)

theorem resStar_symm_apply (σ : stabT hE hd) (f : LocalClass E d) :
    (((resStar hE hd σ).symm f : LocalClass E d) : X) =
      ((((σ : tauGroup hE) : Equiv.Perm E)⁻¹ ⟨f, f.2.1⟩ : E) : X) := rfl

variable (L : LocalPoints (pairModel hF) E d)

theorem LocalPoints.permCongr_resStar_mem_tauGroup (σ : stabT hE hd) :
    Equiv.permCongrHom L.χ (resStar hE hd σ) ∈ tauGroup hF := by
  rw [mem_tauGroup]
  intro x y
  obtain ⟨p, rfl⟩ := L.χ.surjective x
  obtain ⟨q, rfl⟩ := L.χ.surjective y
  set ρ := resStar hE hd σ
  have hpq := LocalPoints.mul_mul_mem_localClass hE p q
  have hρ := LocalPoints.mul_mul_mem_localClass hE (ρ p) (ρ q)
  have e1 : tauE hF (L.χ p) (L.χ q) = L.χ ⟨_, hpq⟩ := (L.tau p q hpq).symm
  have e2 : ρ ⟨_, hpq⟩ = ⟨_, hρ⟩ := Subtype.ext (resStar_mul_mul hE hd σ p q)
  have e3 : L.χ ⟨_, hρ⟩ = tauE hF (L.χ (ρ p)) (L.χ (ρ q)) := L.tau (ρ p) (ρ q) hρ
  show L.χ (ρ (L.χ.symm (tauE hF (L.χ p) (L.χ q)))) =
    tauE hF (L.χ (ρ (L.χ.symm (L.χ p)))) (L.χ (ρ (L.χ.symm (L.χ q))))
  rw [e1, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, e2, e3]

theorem LocalPoints.muImg_stab (σ : stabT hE hd) {c : X} (hc : c ∈ E) :
    L.muImg ((((σ : tauGroup hE) : Equiv.Perm E) ⟨c, hc⟩ : E) : X) =
      ⇑(Equiv.permCongrHom L.χ (resStar hE hd σ)) '' L.muImg c := by
  ext p
  rw [Set.mem_image_equiv, L.mem_muImg, L.mem_muImg]
  set q := L.χ.symm p
  have hq : L.χ.symm ((Equiv.permCongrHom L.χ (resStar hE hd σ)).symm p) =
      (resStar hE hd σ).symm q := by
    show L.χ.symm (L.χ ((resStar hE hd σ).symm (L.χ.symm p))) = _
    rw [Equiv.symm_apply_apply]
  rw [hq, resStar_symm_apply]
  set τσ := ((σ : tauGroup hE) : Equiv.Perm E)
  have h1 := tauGroup_mem_localClass_iff hE (σ : tauGroup hE).2 (τσ⁻¹ ⟨q, q.2.1⟩) ⟨c, hc⟩
  have h2 : τσ (τσ⁻¹ ⟨q, q.2.1⟩) = ⟨q, q.2.1⟩ := Equiv.Perm.eq_inv_iff_eq.1 rfl
  rw [h2] at h1
  exact h1.symm

variable {L}

theorem LocalPoints.permCongr_resStar_preserves {𝒮 : Set (Set F)} (h : CoverHyp L 𝒮)
    (hmu : ∀ c ∈ E, c * d ≠ d * c → (muSet E d c).Nonempty) (σ : stabT hE hd) :
    ∀ T ∈ 𝒮, ⇑(Equiv.permCongrHom L.χ (resStar hE hd σ)) '' T ∈ 𝒮 := by
  intro T hT
  obtain ⟨c, hc, rfl⟩ := h.surj T hT
  rw [← L.muImg_stab hF hE hd σ hc.1]
  set τσ := ((σ : tauGroup hE) : Equiv.Perm E)
  have hσd : τσ ⟨d, hd⟩ = ⟨d, hd⟩ := σ.2
  have hnc : ((τσ ⟨c, hc.1⟩ : E) : X) * d ≠ d * ((τσ ⟨c, hc.1⟩ : E) : X) := by
    intro e
    apply hc.2.1
    have := (tauGroup_commute_iff hE (σ : tauGroup hE).2 ⟨c, hc.1⟩ ⟨d, hd⟩).2
    rw [hσd] at this
    exact this e
  exact h.mem _ ⟨(τσ ⟨c, hc.1⟩).2, hnc, hmu _ (τσ ⟨c, hc.1⟩).2 hnc⟩

theorem Pair.card_stabT_le_of_rigid (hZF : Subgroup.center Y = ⊥)
    (L : LocalPoints (pairModel hF) E d) {𝒮 : Set (Set F)} (h : CoverHyp L 𝒮)
    (hXi : ((pairModel hF).xi 𝒮).Connected)
    (hmu : ∀ c ∈ E, c * d ≠ d * c → (muSet E d c).Nonempty)
    (hrig : ∀ σ : tauGroup hF, (∀ T ∈ 𝒮, ⇑(σ : Equiv.Perm F) '' T ∈ 𝒮) →
      σ ∈ (innerTau hF).range) :
    Nat.card (stabT hE hd) ≤ 2 * Nat.card Y := by
  set K : Subgroup (Equiv.Perm F) := (innerTau hF).range.map (tauGroup hF).subtype
  have hK : ∀ σ : stabT hE hd, Equiv.permCongrHom L.χ (resStar hE hd σ) ∈ K := by
    intro σ
    obtain ⟨g, hg⟩ := hrig ⟨_, L.permCongr_resStar_mem_tauGroup hF hE hd σ⟩
      (LocalPoints.permCongr_resStar_preserves hF hE hd h hmu σ)
    exact ⟨innerTau hF g, ⟨g, rfl⟩, by rw [hg]; rfl⟩
  have hcardK : Nat.card K = Nat.card Y := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective,
      ← Nat.card_congr (MonoidHom.ofInjective (innerTau_injective hF hZF)).toEquiv]
  have := Pair.card_stabT_le hE hd L h hXi hmu hK
  rwa [hcardK] at this

end Star

theorem Pair.mem_range_innerTau_of_card_stabT (hE : Pair X E) (hZ : Subgroup.center X = ⊥)
    {d : X} (hd : d ∈ E)
    (hcard : Nat.card (stabT hE hd) ≤ Nat.card (Subgroup.centralizer ({d} : Set X)))
    (σ : tauGroup hE) : σ ∈ (innerTau hE).range := by
  have := Pair.finite hE
  have hinj := innerTau_injective hE hZ
  have hfix : ∀ h : Subgroup.centralizer ({d} : Set X), innerTau hE (h : X) ∈ stabT hE hd := by
    intro h
    show Pair.conjPerm hE (h : X) ⟨d, hd⟩ = ⟨d, hd⟩
    apply Subtype.ext
    rw [Pair.conjPerm_apply]
    have hc : (h : X) * d = d * h := Subgroup.mem_centralizer_singleton_iff.1 h.2
    rw [hc, mul_inv_cancel_right]
  let ι : Subgroup.centralizer ({d} : Set X) → stabT hE hd :=
    fun h => ⟨innerTau hE (h : X), hfix h⟩
  have hιinj : Function.Injective ι := fun a b e =>
    Subtype.ext (hinj (congrArg Subtype.val e))
  have : Finite (stabT hE hd) := Subtype.finite
  have hbij := hιinj.bijective_of_nat_card_le hcard
  obtain ⟨g, hg⟩ := isConj_iff.1 (Pair.isConj hE hd ((σ : Equiv.Perm E) ⟨d, hd⟩).2)
  have hσ₁ : (innerTau hE g)⁻¹ * σ ∈ stabT hE hd := by
    show ((Pair.conjPerm hE g)⁻¹ * (σ : Equiv.Perm E)) ⟨d, hd⟩ = ⟨d, hd⟩
    apply Subtype.ext
    show ((Pair.conjPerm hE g)⁻¹ ((σ : Equiv.Perm E) ⟨d, hd⟩) : X) = d
    rw [← map_inv, Pair.conjPerm_apply, ← hg, inv_inv]
    group
  obtain ⟨h, hh⟩ := hbij.2 ⟨_, hσ₁⟩
  have e : innerTau hE (h : X) = (innerTau hE g)⁻¹ * σ := congrArg Subtype.val hh
  exact ⟨g * h, by rw [map_mul, e, mul_inv_cancel_left]⟩

end CFSG.Fischer
