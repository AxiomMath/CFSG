module

public import CFSG.CharacterTheory.Semidihedral.Local.FourGroupOddCycling
public import CFSG.CharacterTheory.Semidihedral.Local.PerfectFullLocalFusionSupport
public import CFSG.CharacterTheory.Semidihedral.TwoCoverOddCore

public section

namespace CFSG.Semidihedral.StationaryConfinement

open CFSG.Open
open CFSG.Semidihedral.Local
  (full_four_group_action_has_an_odd_cycling_element_inverted_by_each_outer_involution)

variable {G : Type} [Group G] [Finite G]

theorem exists_inverted_odd_cycling_element [Group.IsPerfect G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hcomm : Commute t s) (hts : t ≠ s)
    (K : Subgroup G) (hKodd : Odd (Nat.card K))
    (hKV : K ≤ Subgroup.normalizer (Subgroup.closure ({t, s} : Set G) : Set G))
    (hKn : Subgroup.normalizer (Subgroup.closure ({t, s} : Set G) : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (hCV : Subgroup.centralizer (Subgroup.closure ({t, s} : Set G) : Set G) =
      Subgroup.closure ({t, s} : Set G) ⊔ K)
    (k : G) (hkM : k ∈ Subgroup.normalizer (Subgroup.closure ({t, s} : Set G) : Set G))
    (hk : orderOf k = 2)
    (hkact : ∃ v ∈ Subgroup.closure ({t, s} : Set G), k * v * k⁻¹ ≠ v) :
    ∃ a ∈ Subgroup.normalizer (Subgroup.closure ({t, s} : Set G) : Set G),
      Odd (orderOf a) ∧ k * a * k⁻¹ = a⁻¹ ∧
      ∀ P : Subgroup G, Subgroup.centralizer (Subgroup.closure ({t, s} : Set G) : Set G) ≤ P →
        k ∈ P → a ∈ P → Subgroup.normalizer (Subgroup.closure ({t, s} : Set G) : Set G) ≤ P := by
  classical
  set V := Subgroup.closure ({t, s} : Set G) with hVdef
  set M := Subgroup.normalizer (V : Set G) with hMdef
  have hV : IsKleinFour V := TwoCoverOddCore.original_four_group_isKleinFour t s ht hs hcomm hts
  have hVM : V ≤ M := Subgroup.le_normalizer
  let V' : Subgroup M := V.subgroupOf M
  let eV : V' ≃* V := Subgroup.subgroupOfEquivOfLe hVM
  have hV'K : IsKleinFour V' :=
    { card_four := by rw [Nat.card_congr eV.toEquiv]; exact hV.card_four
      exponent_two := by rw [Monoid.exponent_eq_of_mulEquiv eV]; exact hV.exponent_two }
  let := hV'K
  let K' : Subgroup M := K.subgroupOf M
  have hK'normal : K'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKV).mpr hKn
  let := hK'normal
  have hK'odd : Odd (Nat.card K') := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKV).toEquiv]
    exact hKodd
  have hcentM : Subgroup.centralizer (V' : Set M) = V' ⊔ K' := by
    rw [← Subgroup.subgroupOf_sup hVM hKV, ← hCV]
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h v hv
      have := h ⟨v, hVM hv⟩ hv
      exact congrArg Subtype.val this
    · intro h v hv
      exact Subtype.ext (h (v : G) hv)
  have hVtwo : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hVS⟩ := hVtwo.exists_le_sylow
  let fS : SemidihedralGroup n ≃* S := f0.trans (S0.equiv S)
  have hrange := CFSG.Semidihedral.Local.kleinFour_normalizer_image_eq_top hn S fS V hVS hV
  have hsurj : Function.Surjective (MulAut.conjNormal : M →* MulAut V') := by
    intro σ
    let σ' : MulAut V := (eV.symm.trans σ).trans eV
    obtain ⟨m, hm⟩ : σ' ∈ V.normalizerMonoidHom.range := by
      rw [hrange]
      trivial
    refine ⟨m, ?_⟩
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have h1 := congrArg (fun α : MulAut V => ((α (eV v) : V) : G)) hm
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    have h2 : ((σ' (eV v) : V) : G) = (((σ v : V') : M) : G) := by
      change ((eV (σ (eV.symm (eV v))) : V) : G) = _
      rw [MulEquiv.symm_apply_apply]
      rfl
    rw [h2] at h1
    exact h1
  let k' : M := ⟨k, hkM⟩
  have hk' : orderOf k' = 2 := (Subgroup.orderOf_coe k').symm.trans hk
  have hk'V : ∃ v ∈ V', k' * v * k'⁻¹ ≠ v := by
    obtain ⟨v, hv, hkv⟩ := hkact
    refine ⟨⟨v, hVM hv⟩, hv, fun h => hkv ?_⟩
    exact congrArg Subtype.val h
  obtain ⟨b, -, a', ha'ord, -, -, hka', hgen⟩ :=
    full_four_group_action_has_an_odd_cycling_element_inverted_by_each_outer_involution
      V' K' hK'odd hcentM hsurj k' hk' hk'V
  refine ⟨(a' : G), a'.2, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, ha'ord]
    exact Odd.pow (by decide)
  · exact congrArg Subtype.val hka'
  · intro P hCP hkP haP
    have hle : Subgroup.closure ((Subgroup.centralizer (V' : Set M) : Set M) ∪ {k', a'}) ≤
        P.subgroupOf M := by
      rw [Subgroup.closure_le]
      rintro x (hx | hx | hx)
      · apply hCP
        rw [hcentM, ← Subgroup.subgroupOf_sup hVM hKV, ← hCV] at hx
        exact hx
      · rw [hx]
        exact hkP
      · rw [Set.mem_singleton_iff.mp hx]
        exact haP
    rw [hgen] at hle
    intro m hm
    exact hle (Subgroup.mem_top (⟨m, hm⟩ : M))

end CFSG.Semidihedral.StationaryConfinement
