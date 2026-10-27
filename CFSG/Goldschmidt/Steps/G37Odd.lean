module

public import CFSG.Goldschmidt.Steps.G37CoreX
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.SelfCommutatorFixedPointFreeQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.OddQuotientFixedPointFree
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Goldschmidt.G37

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normal_subgroupOf_of_commutator_le {V D : Subgroup G} (hDV : D ≤ V)
    (hVD : ⁅V, V⁆ ≤ D) : (D.subgroupOf V).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hDV]
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · intro hd
    have h1 := hVD (Subgroup.commutator_mem_commutator hv (hDV hd))
    rw [commutatorElement_def] at h1
    rw [show v * d * v⁻¹ = v * d * v⁻¹ * d⁻¹ * d by group]
    exact D.mul_mem h1 hd
  · intro hd
    have h1 := hVD (Subgroup.commutator_mem_commutator (V.inv_mem hv) (hDV hd))
    rw [commutatorElement_def] at h1
    rw [show d = v⁻¹ * (v * d * v⁻¹) * v⁻¹⁻¹ * (v * d * v⁻¹)⁻¹ * (v * d * v⁻¹) by group]
    exact D.mul_mem h1 hd

theorem le_centralizer_of_inf_centralizer_le {W : Subgroup G} {t : G} (ht : orderOf t = 2)
    (hWp : Group.IsPerfect W) (hWt : ⁅W, Subgroup.zpowers t⁆ = W) (V : Subgroup G)
    (hVodd : Odd (Nat.card V)) (hWV : W ≤ Subgroup.normalizer (V : Set G))
    (htV : t ∈ Subgroup.normalizer (V : Set G))
    (hfix : V ⊓ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.centralizer (W : Set G)) :
    V ≤ Subgroup.centralizer (W : Set G) := by
  have htinv : BenderSuzuki.PFAppendixIII.IsInvolution t := by
    refine ⟨fun h => ?_, ?_⟩
    · rw [h, orderOf_one] at ht
      omega
    · have h := pow_orderOf_eq_one t
      rwa [ht] at h
  induction h : Nat.card V using Nat.strong_induction_on generalizing V with
  | _ n ih =>
  have hVs : Group.IsSolvable V := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hVodd
  set V' := ⁅V, V⁆ with hV'
  have hV'V : V' ≤ V := commutator_self_le V
  by_cases hlt : V' < V
  swap
  ·
    have hVeq : V' = V := hV'V.eq_of_not_lt hlt
    have hVb : V = ⊥ := by
      by_contra hne
      have : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).mpr hne
      have : Group.IsPerfect V := Subgroup.isPerfect_iff.mpr hVeq
      exact Group.IsPerfect.not_isSolvable V hVs
    rw [hVb]
    exact bot_le
  have hV'C : V' ≤ Subgroup.centralizer (W : Set G) :=
    ih (Nat.card V') (h ▸ Subgroup.card_lt_of_lt hlt) V'
      (hVodd.of_dvd_nat (Subgroup.card_dvd_of_le hV'V))
      (fun w hw => CFSG.Walter.mem_normalizer_commutator (hWV hw) (hWV hw))
      (CFSG.Walter.mem_normalizer_commutator htV htV)
      ((inf_le_inf_right _ hV'V).trans hfix) rfl
  set D := V ⊓ Subgroup.centralizer ({t} : Set G) ⊔ V' with hD
  have hDV : D ≤ V := sup_le inf_le_left hV'V
  have hDC : D ≤ Subgroup.centralizer (W : Set G) := sup_le hfix hV'C
  have hDn : (D.subgroupOf V).Normal := normal_subgroupOf_of_commutator_le hDV le_sup_right
  have hWD : W ≤ Subgroup.normalizer (D : Set G) := fun w hw =>
    Subgroup.centralizer_le_normalizer (D : Set G) (Subgroup.le_centralizer_iff.mp hDC hw)
  have htD : t ∈ Subgroup.normalizer (D : Set G) := by
    have htC : t ∈ Subgroup.normalizer
        ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨htV, Subgroup.le_normalizer
        (Subgroup.mem_centralizer_singleton_iff.mpr rfl)⟩
    exact CFSG.Walter.mem_normalizer_sup htC (CFSG.Walter.mem_normalizer_commutator htV htV)
  have hfpf := CFSG.GorensteinWalter.fixedPointFree_quotient_of_odd_solvable_and_fixedPoints_le
    V D hDV hDn htV htD htinv hVs hVodd le_sup_left
  have hVW : ⁅V, W⁆ ≤ D :=
    CFSG.GorensteinWalter.commutator_le_of_selfCommutator_fixedPointFree_involution_quotient
      V D W hDV hDn hWV htV hWD htD htinv hWt hfpf
  have h2 : ⁅⁅W, V⁆, W⁆ = ⊥ := by
    rw [Subgroup.commutator_comm W V, eq_bot_iff]
    calc ⁅⁅V, W⁆, W⁆ ≤ ⁅D, W⁆ := Subgroup.commutator_mono hVW le_rfl
      _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hDC
      _ ≤ ⊥ := le_rfl
  have h3 := CFSG.LocalCores.perfect_double_commutator hWp h2
  rw [Subgroup.commutator_comm] at h3
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3

end CFSG.Goldschmidt.G37
