module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporComp
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCrit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Census
public import Certificates.Certificate36911

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th.Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def Cls {G : Type*} [Group G] (x : G) : Prop :=
  (∃ v ∈ Subgroup.centralizer ({x} : Set G), orderOf v = 13 ∧
      ¬ 5 ∣ Nat.card (Subgroup.centralizer ({v} : Set G))) ∨
  ¬ 5 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) ∨
  (¬ 25 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) ∧ ∃ T : Set G,
      T ⊆ Subgroup.centralizer ({x} : Set G) ∧ (∀ g ∈ T, orderOf g = 5) ∧
      1080 < Nat.card (Subgroup.closure T))

private theorem cls_conj {G : Type*} [Group G] (c t : G) (h : Cls t) : Cls (c⁻¹ * t * c) := by
  let φ : G ≃* G := MulAut.conj c⁻¹
  have hφ : ∀ y, φ y = c⁻¹ * y * c := fun y => by
    change MulAut.conj c⁻¹ y = _
    rw [MulAut.conj_apply, inv_inv]
  have hcard : ∀ y, Nat.card (Subgroup.centralizer ({φ y} : Set G)) =
      Nat.card (Subgroup.centralizer ({y} : Set G)) :=
    CFSG.Sporadic.FischerOddCore.card_centralizer_mulEquiv φ
  have hmem : ∀ {y z : G}, y ∈ Subgroup.centralizer ({z} : Set G) →
      φ y ∈ Subgroup.centralizer ({φ z} : Set G) := by
    intro y z h
    rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
    rw [← map_mul, ← map_mul, h]
  rw [← hφ]
  rcases h with ⟨v, hv, hv13, hv5⟩ | h5 | ⟨h25, T, hT, hT5, hbig⟩
  · exact Or.inl ⟨φ v, hmem hv, by rw [MulEquiv.orderOf_eq]; exact hv13, by rw [hcard]; exact hv5⟩
  · exact Or.inr (Or.inl (by rw [hcard]; exact h5))
  · refine Or.inr (Or.inr ⟨by rw [hcard]; exact h25, φ '' T, ?_, ?_, ?_⟩)
    · rintro _ ⟨g, hg, rfl⟩
      exact hmem (hT hg)
    · rintro _ ⟨g, hg, rfl⟩
      rw [MulEquiv.orderOf_eq]; exact hT5 g hg
    · have e : Subgroup.closure (φ '' T) = (Subgroup.closure T).map φ.toMonoidHom := by
        rw [MonoidHom.map_closure]; rfl
      rw [e, Subgroup.card_map_of_injective φ.injective]
      exact hbig

section Fi23Facts


private theorem classes_J (x : J) (hx : orderOf x = 3) :
    (∃ v ∈ Subgroup.centralizer ({x} : Set J), orderOf v = 13 ∧
        ¬ 5 ∣ Nat.card (Subgroup.centralizer ({v} : Set J))) ∨
    ¬ 5 ∣ Nat.card (Subgroup.centralizer ({x} : Set J)) ∨
    (¬ 25 ∣ Nat.card (Subgroup.centralizer ({x} : Set J)) ∧ ∃ T : Set J,
        T ⊆ Subgroup.centralizer ({x} : Set J) ∧ (∀ g ∈ T, orderOf g = 5) ∧
        1080 < Nat.card (Subgroup.closure T)) := by
  obtain ⟨h0, h1, h2, ⟨y₁, hy₁, y₂, hy₂, ho1, ho2, hbig⟩, h3⟩ :=
    Certificates.certificate36911
  obtain ⟨i, hi⟩ := fi23_three_classes x hx
  obtain ⟨c, hc⟩ := isConj_iff.1 hi
  have hx' : x = c⁻¹ * t3 i * c := by rw [← hc]; group
  rw [hx']
  refine cls_conj (G := J) c (t3 i) ?_
  fin_cases i
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · refine Or.inr (Or.inr ⟨h2, {y₁, y₂}, ?_, ?_, hbig⟩)
    · rintro _ (rfl | rfl)
      · exact hy₁
      · exact hy₂
    · rintro _ (rfl | rfl)
      · exact ho1
      · exact ho2
  · exact Or.inr (Or.inl h3)

end Fi23Facts

private theorem noComp_generic {S H : Type*} [Group S] [Finite S] [Group H] (φ : S ≃* H)
    (hcls : ∀ x : H, orderOf x = 3 →
      (∃ v ∈ Subgroup.centralizer ({x} : Set H), orderOf v = 13 ∧
        ¬ 5 ∣ Nat.card (Subgroup.centralizer ({v} : Set H))) ∨
      ¬ 5 ∣ Nat.card (Subgroup.centralizer ({x} : Set H)) ∨
      (¬ 25 ∣ Nat.card (Subgroup.centralizer ({x} : Set H)) ∧ ∃ T : Set H,
        T ⊆ Subgroup.centralizer ({x} : Set H) ∧ (∀ g ∈ T, orderOf g = 5) ∧
          1080 < Nat.card (Subgroup.closure T)))
    (hS : ¬ 5 ^ 13 ∣ Nat.card S) {s : S} (hs : orderOf s = 3) {K : Subgroup S}
    (hK : IsComponentOf K (Subgroup.centralizer ({s} : Set S))) (h : IsHatSix ↥K) : False := by
  have hs' : orderOf (φ s) = 3 := by rw [MulEquiv.orderOf_eq]; exact hs
  have hcard := CFSG.Sporadic.FischerOddCore.card_centralizer_mulEquiv φ s
  rcases hcls (φ s) hs' with ⟨v, hvC, hv13, hv5⟩ | h5 | ⟨h25', T, hTC, hT5, hbig⟩
  · have hvC' : φ.symm v ∈ Subgroup.centralizer ({s} : Set S) := by
      have hv' : v * φ s = φ s * v := (Subgroup.mem_centralizer_singleton_iff (g := φ s) (k := v)).1 hvC
      refine (Subgroup.mem_centralizer_singleton_iff (g := s) (k := φ.symm v)).2 ?_
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hv'
    have hv5' : ¬ 5 ∣ Nat.card (Subgroup.centralizer ({φ.symm v} : Set S)) := by
      have := CFSG.Sporadic.FischerOddCore.card_centralizer_mulEquiv φ (φ.symm v)
      rw [MulEquiv.apply_symm_apply] at this
      rw [← this]; exact hv5
    refine false_of_component_of_prime_elem hK (Or.inl h) hvC' (p := 13) (by norm_num)
      (by norm_num) ?_ ?_ hv5'
    · rw [MulEquiv.orderOf_eq]; exact hv13
    · exact fun hd => hS (hd.trans (Subgroup.card_subgroup_dvd_card _))
  · exact false_of_isHatSix_of_not_five hK.1 (Or.inl h) (by rw [← hcard]; exact h5)
  · have h25 : ¬ 25 ∣ Nat.card (Subgroup.centralizer ({s} : Set S)) := by
      rw [← hcard]; exact h25'
    have hT'C : φ.symm '' T ⊆ Subgroup.centralizer ({s} : Set S) := by
      rintro _ ⟨g, hg, rfl⟩
      have hg' : g * φ s = φ s * g :=
        (Subgroup.mem_centralizer_singleton_iff (g := φ s) (k := g)).1 (hTC hg)
      refine (Subgroup.mem_centralizer_singleton_iff (g := s) (k := φ.symm g)).2 ?_
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hg'
    have hT'5 : ∀ g ∈ φ.symm '' T, orderOf g = 5 := by
      rintro _ ⟨g, hg, rfl⟩
      rw [MulEquiv.orderOf_eq]; exact hT5 g hg
    have hbig' : 1080 < Nat.card (Subgroup.closure (φ.symm '' T)) := by
      have e : Subgroup.closure (φ.symm '' T) = (Subgroup.closure T).map φ.symm.toMonoidHom := by
        rw [MonoidHom.map_closure]; rfl
      rw [e, Subgroup.card_map_of_injective φ.symm.injective]
      exact hbig
    exact false_of_isHatSix_of_five_gen hK h h25 hT'C hT'5 hbig'

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier in
theorem sporNoPumpup_Fi23
    (hSpM : SporadicMultipliers) (hOG : UniquenessMaximal.InputONGroup)
    (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) : SporNoPumpup .Fi23 := by
  have e0 : (TauCeti.CFSGIndex.sporadic .Fi23).Group ≃* NativeSporadic.Fi23 := (hbr .Fi23).some.symm
  haveI : Finite (TauCeti.CFSGIndex.sporadic .Fi23).Group := Finite.of_equiv _ e0.symm.toEquiv
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .Fi23).Group :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi23.isSimpleGroup_Fi23 e0
  let φ : (TauCeti.CFSGIndex.sporadic .Fi23).Group ≃* CFSG.Sporadic.Fi23.J :=
    e0.trans CFSG.Sporadic.Fi23.fi23EquivJ
  have hcard : Nat.card (TauCeti.CFSGIndex.sporadic .Fi23).Group = 4089470473293004800 := by
    rw [Nat.card_congr e0.toEquiv, CFSG.Sporadic.Fi23.card_Fi23]
  refine sporNoPumpup_of_components hSpM hOG hOut ?_ ?_ ?_ ?_
  · rw [hcard]
    norm_num [sporOrd, orderFi23]
  · exact sporadicOPrimeHolds_Fi23_three _ ⟨e0⟩
  · intro s hs K hK h
    rcases h with h | ⟨h, -⟩
    · exact @noComp_generic _ ↥CFSG.Sporadic.Fi23.J _ _ inferInstance φ classes_J
        (by rw [hcard]; norm_num) s hs K hK h
    · exact absurd h (by decide)
  · intro h
    exact absurd h (by decide)

end CFSG.HardMathSupport.Solomon.Coordinator
