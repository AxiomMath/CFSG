module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Toolbox
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Three

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

namespace S5A6

abbrev A6 : Type := alternatingGroup (Fin 6)

abbrev Inn : Subgroup (MulAut A6) := (MulAut.conj : A6 →* MulAut A6).range

theorem commutator_le_inn : commutator (MulAut A6) ≤ Inn := by
  have hN : (Inn).Normal :=
    { conj_mem := by
        rintro _ ⟨s, rfl⟩ x
        exact ⟨x s, (mul_conj_mul_inv x s).symm⟩ }
  have hcard : Nat.card (MulAut A6 ⧸ Inn) = 2 ^ 2 := by
    rw [← Subgroup.index, CFSG.QuasithinUnique.Setup.X3Aut.index_inner_alt6]
    norm_num
  have : IsMulCommutative (MulAut A6 ⧸ Inn) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hcard
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.1 this

theorem mem_commutator_map {H K : Type*} [Group H] [Group K] (f : H →* K) {x : H}
    (hx : x ∈ commutator H) : f x ∈ commutator K := by
  have h : f x ∈ (commutator H).map f := ⟨x, hx, rfl⟩
  rw [commutator_def, Subgroup.map_commutator] at h
  exact Subgroup.commutator_mono le_top le_top h

theorem inn_le_commutator (g : A6) : (MulAut.conj g : MulAut A6) ∈ commutator (MulAut A6) := by
  have hg : g ∈ commutator A6 := by
    rw [commutator_alternatingGroup_eq_top (by simp)]
    exact mem_top g
  exact mem_commutator_map (MulAut.conj : A6 →* MulAut A6) hg

theorem exists_third {G : Type*} [Group G] (Abar : Subgroup G) (e : ↥Abar ≃* MulAut A6) {y : G}
    (hy3 : orderOf y = 3) (hyJ : y ∈ derivedIn Abar) :
    ∃ w ∈ derivedIn Abar, w * y = y * w ∧ w ∉ zpowers y ∧ w * w * w = 1 := by
  have hyA : y ∈ Abar := derivedIn_le _ hyJ
  set y' : ↥Abar := ⟨y, hyA⟩ with hy'
  have hy'c : y' ∈ commutator ↥Abar := by
    obtain ⟨x, hx, hxy⟩ := hyJ
    have : x = y' := Subtype.ext hxy
    rwa [← this]
  have hα : e y' ∈ commutator (MulAut A6) := mem_commutator_map e.toMonoidHom hy'c
  obtain ⟨g, hg⟩ := commutator_le_inn hα
  have hord' : orderOf y' = 3 := by rw [← hy3]; exact Subgroup.orderOf_mk y hyA
  have hordα : orderOf (e y') = 3 := by rw [MulEquiv.orderOf_eq, hord']
  have hinj : Function.Injective (MulAut.conj : A6 →* MulAut A6) :=
    CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.inner_conjugation_injective
  have hg3 : orderOf g = 3 := by
    rw [← orderOf_injective _ hinj g]
    simpa [MonoidHom.coe_mk] using (by rw [hg]; exact hordα : orderOf (MulAut.conj g) = 3)
  have hcard : Nat.card (centralizer ({g} : Set A6)) = 9 :=
    CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_centralizer_of_orderOf_eq_three hg3
  have hex : ∃ w' ∈ centralizer ({g} : Set A6), w' ∉ zpowers g := by
    by_contra hne
    push Not at hne
    have hle : centralizer ({g} : Set A6) ≤ zpowers g := fun w hw => hne w hw
    have := Subgroup.card_le_of_le hle
    rw [hcard, Nat.card_zpowers, hg3] at this
    omega
  obtain ⟨w', hw'c, hw'n⟩ := hex
  have hw'3 : w' * w' * w' = 1 := by
    have := CFSG.EvenSporadicStandard.HSStd.Zassenhaus.pow_three_of_mem_centralizer hg3 w' hw'c
    rwa [pow_three] at this
  have hw'g : w' * g = g * w' := mem_centralizer_singleton_iff.1 hw'c
  set w : ↥Abar := e.symm (MulAut.conj w') with hw
  have hwc : w ∈ commutator ↥Abar :=
    mem_commutator_map e.symm.toMonoidHom (inn_le_commutator w')
  refine ⟨(w : G), ⟨w, hwc, rfl⟩, ?_, ?_, ?_⟩
  · have : w * y' = y' * w := by
      apply e.injective
      rw [map_mul, map_mul, hw, MulEquiv.apply_symm_apply, ← hg]
      show (MulAut.conj w') * (MulAut.conj g) = (MulAut.conj g) * (MulAut.conj w')
      rw [← map_mul, ← map_mul, hw'g]
    exact congrArg Subtype.val this
  · intro hmem
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
    have h1 : y' ^ k = w := Subtype.ext (by simpa [hy'] using hk)
    have h2 : (MulAut.conj w' : MulAut A6) = (MulAut.conj g) ^ k := by
      have := congrArg e h1
      rw [map_zpow, hw, MulEquiv.apply_symm_apply, ← hg] at this
      exact this.symm
    rw [← map_zpow] at h2
    exact hw'n (mem_zpowers_iff.2 ⟨k, (hinj h2).symm⟩)
  · have : w * w * w = 1 := by
      apply e.injective
      rw [map_mul, map_mul, hw, MulEquiv.apply_symm_apply, map_one, ← map_mul, ← map_mul, hw'3,
        map_one]
    simpa using congrArg Subtype.val this

end S5A6

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
