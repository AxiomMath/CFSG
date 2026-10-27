module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.TitsCoverCert
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverTitsReduce

public section

namespace CFSG.QuasithinUnique.Ch1

open scoped IsMulCommutative

open CFSG.QuasithinUnique.Ch1.TitsCover CFSG.Sporadic.Schreier.Tits

theorem titsNoDoubleCover
    : TitsNoDoubleCover := by
  classical
  intro X _ _ hX E _ _ _ π hπ hker hcard
  obtain ⟨ρ⟩ := titsModelEquiv X 2 1 hX
  let φ : E →* Equiv.Perm (Fin 1755) := titsD.subtype.comp (ρ.toMonoidHom.comp π)
  have hφ : ∀ e, φ e = ((ρ (π e) : titsD) : Equiv.Perm (Fin 1755)) := fun e => rfl
  have hφ1 : ∀ e, φ e = 1 ↔ π e = 1 := by
    intro e
    rw [hφ]
    constructor
    · intro h
      have : ρ (π e) = 1 := Subtype.ext h
      simpa using this
    · intro h
      rw [h]
      simp
  obtain ⟨ζ, hζ1, hζ⟩ := (Nat.card_eq_two_iff' (1 : π.ker)).1 hcard
  have hker2 : ∀ e, π e = 1 → e = 1 ∨ e = (ζ : E) := by
    intro e he
    by_cases h : (⟨e, he⟩ : π.ker) = 1
    · left; exact congrArg Subtype.val h
    · right; exact congrArg Subtype.val (hζ _ h)
  have hζsq : (ζ : E) * ζ = 1 := by
    by_cases h : ((ζ * ζ : π.ker)) = 1
    · exact congrArg Subtype.val h
    · exfalso
      have := hζ _ h
      have h2 : ζ * ζ = ζ * 1 := by rw [mul_one]; exact this
      exact hζ1 (mul_left_cancel h2)
  have hζne : (ζ : E) ≠ 1 := fun h => hζ1 (Subtype.ext h)
  have hζc : ∀ e : E, (ζ : E) * e = e * ζ := fun e =>
    ((Subgroup.mem_center_iff.1 (hker ζ.2)) e).symm
  let X' : CentralExt E (Equiv.Perm (Fin 1755)) :=
    ⟨φ, ζ, hζne, hζsq, hζc, fun e he => hker2 e ((hφ1 e).1 he)⟩
  have hrange : ∀ y ∈ titsD, ∃ e : E, φ e = y := by
    intro y hy
    obtain ⟨e, he⟩ := hπ (ρ.symm ⟨y, hy⟩)
    exact ⟨e, by rw [hφ, he]; simp⟩
  have hφmem : ∀ e, φ e ∈ titsD := fun e => (ρ (π e)).2
  have hxmem : ∀ i, covData.x i ∈ titsD := fun i => wordIn_titsT_mem_titsD _
  choose xt hxt using fun i => hrange _ (hxmem i)
  have hlift : ∀ bl ∈ covData.blocks, ∃ gt : E, X'.φ gt = bl.g := fun bl _ => hrange _ bl.g_mem
  have hT := covCheck_good covCheck_covData
  have hzero := covCheck_vanish covData covCheck_covData X' xt hxt hlift
  obtain ⟨s, hs⟩ := exists_section X' xt hT hxt hzero
  let Sg := covData.tab.sub covData.x hT
  have hSgD : Sg ≤ titsD := by
    rintro g ⟨v, -, rfl⟩
    exact Subgroup.list_prod_mem _ fun y hy => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
      exact hxmem i
  have hcardSg : Nat.card Sg = 2048 := by
    rw [CayTab.card_sub hT]
    exact covData_nV
  have hidx : (Sg.subgroupOf titsD).index = 8775 := by
    have h1 := Subgroup.card_mul_index (Sg.subgroupOf titsD)
    rw [card_subgroupOf_titsD hSgD, hcardSg, card_titsD] at h1
    omega
  let V : Subgroup E := π.ker
  let P : Subgroup E := Sg.comap φ
  let K : Subgroup E := s.range
  have hVφ : ∀ v ∈ V, φ v = 1 := fun v hv => (hφ1 v).2 hv
  have hrangeφ : φ.range = titsD := by
    ext y
    constructor
    · rintro ⟨e, rfl⟩; exact hφmem e
    · intro hy; exact hrange y hy
  have hPidx : P.index = 8775 := by
    rw [Subgroup.index_comap, hrangeφ]
    exact hidx
  have hVP : V ≤ P := fun v hv => by
    show φ v ∈ Sg
    rw [hVφ v hv]
    exact Sg.one_mem
  have hKP : K ≤ P := by
    rintro _ ⟨g, rfl⟩
    show φ (s g) ∈ Sg
    rw [hs g]
    exact g.2
  have hVcentral : ∀ v ∈ V, ∀ e : E, v * e = e * v := fun v hv e =>
    (Subgroup.mem_center_iff.1 (hker hv) e).symm
  have hVK : V ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyV, g, rfl⟩
    have h1 : g = 1 := by
      apply Subtype.ext
      have := hVφ _ hyV
      rw [hs g] at this
      exact this
    rw [h1, map_one]
    exact Subgroup.one_mem _
  have hVKP : V ⊔ K = P := by
    apply le_antisymm (sup_le hVP hKP)
    intro p hp
    have hpS : φ p ∈ Sg := hp
    have hmem : p * (s ⟨φ p, hpS⟩)⁻¹ ∈ V := by
      show π _ = 1
      rw [← hφ1, map_mul, map_inv, hs ⟨φ p, hpS⟩]
      simp
    have hK' : s (⟨φ p, hpS⟩ : Sg) ∈ K := ⟨_, rfl⟩
    have := Subgroup.mul_mem_sup hmem hK'
    simpa using this
  have hVn : V.Normal := inferInstanceAs π.ker.Normal
  have hVcomm : IsMulCommutative V :=
    ⟨⟨fun a b => Subtype.ext (hVcentral a a.2 b)⟩⟩
  have hcop : Nat.Coprime P.index (Nat.card V) := by
    show Nat.Coprime P.index (Nat.card π.ker)
    rw [hPidx, hcard]
    decide
  obtain ⟨D', -, hVD, hsupD⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting V P K hcop hVK hVKP
  have hDn : D'.Normal := by
    refine ⟨fun d hd g => ?_⟩
    have hg : g ∈ V ⊔ D' := by rw [hsupD]; trivial
    obtain ⟨v, hv, d₀, hd₀, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
    have h1 : v * d₀ * d * (v * d₀)⁻¹ = v * (d₀ * d * d₀⁻¹) * v⁻¹ := by group
    have h2 : v * (d₀ * d * d₀⁻¹) * v⁻¹ = d₀ * d * d₀⁻¹ := by
      rw [hVcentral v hv, mul_inv_cancel_right]
    rw [h1, h2]
    exact D'.mul_mem (D'.mul_mem hd₀ hd) (D'.inv_mem hd₀)
  have hcomm' : ∀ a b : E ⧸ D', a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | _ a =>
      induction b using QuotientGroup.induction_on with
      | _ b =>
        have ha : a ∈ V ⊔ D' := by rw [hsupD]; trivial
        have hb : b ∈ V ⊔ D' := by rw [hsupD]; trivial
        obtain ⟨v₁, hv₁, d₁, hd₁, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 ha
        obtain ⟨v₂, hv₂, d₂, hd₂, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hb
        have e1 : ((v₁ * d₁ : E) : E ⧸ D') = (v₁ : E ⧸ D') := by
          rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff d₁).2 hd₁, mul_one]
        have e2 : ((v₂ * d₂ : E) : E ⧸ D') = (v₂ : E ⧸ D') := by
          rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff d₂).2 hd₂, mul_one]
        rw [e1, e2, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hVcentral v₁ hv₁ v₂]
  have : IsMulCommutative (E ⧸ D') := ⟨⟨hcomm'⟩⟩
  have hsub : Subsingleton (E ⧸ D') := inferInstance
  have hζV : (ζ : E) ∈ V := ζ.2
  have hζD : (ζ : E) ∈ D' := (QuotientGroup.eq_one_iff _).1 (Subsingleton.elim _ _)
  have : (ζ : E) ∈ V ⊓ D' := ⟨hζV, hζD⟩
  rw [hVD] at this
  exact hζne ((Subgroup.mem_bot).1 this)

theorem titsTwoCoverTrivial
    : TitsTwoCoverTrivial :=
  titsTwoCoverTrivial_of_noDoubleCover titsNoDoubleCover

end CFSG.QuasithinUnique.Ch1
