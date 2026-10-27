module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottSporOddCent
public import CFSG.Sporadic.SuzOddCore.OddCore
public import CFSG.Sporadic.SuzOddCore.SmallModel
public import CFSG.Sporadic.Bridge.SuzSurj

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Sporadic.SuzOddCore CFSG.QuasithinUnique.Lin2.RankCert
open scoped Pointwise

theorem suzM_elemAbelianLt :
    ElemAbelianLt ↥suzM (2 ^ 10) := by
  intro E hE
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ι : ↥suzM →* ↥suzT := Subgroup.inclusion suzM_le_suzT
  let F : Subgroup ↥suzT := E.map ι
  have hFcard : Nat.card F = Nat.card E :=
    (Nat.card_congr
      (E.equivMapOfInjective ι (Subgroup.inclusion_injective suzM_le_suzT)).toEquiv).symm
  have hFsq : ∀ x ∈ F, x ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]
  have hFp : IsPGroup 2 F := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hFsq x x.2)⟩
  obtain ⟨P, hP⟩ := hFp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥suzT P suzSylowTwo
  have hmem : ∀ x ∈ F, ((g * x * g⁻¹ : ↥suzT) : Equiv.Perm (Fin 1782)) ∈ invSylow := by
    intro x hx
    have h1 : MulAut.conj g • x ∈ MulAut.conj g • (P : Subgroup ↥suzT) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hP hx)
    rw [← Sylow.coe_subgroup_smul, hg, suzSylowTwo_coe, Subgroup.mem_subgroupOf] at h1
    simpa [MulAut.smul_def, MulAut.conj_apply] using h1
  have hsub : ∀ x ∈ (F : Set ↥suzT), ((g * x * g⁻¹ : ↥suzT) : Equiv.Perm (Fin 1782)) ∈
      insert (1 : Equiv.Perm (Fin 1782)) {h | h ∈ invSylow ∧ orderOf h = 2} := by
    intro x hx
    by_cases h1 : x = 1
    · left
      simp [h1]
    · right
      refine ⟨hmem x hx, orderOf_eq_prime ?_ ?_⟩
      · rw [← Subgroup.coe_pow, conj_pow, hFsq x hx, mul_one, mul_inv_cancel, Subgroup.coe_one]
      · intro h
        apply h1
        have h' : g * x * g⁻¹ = 1 := Subtype.ext h
        calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = 1 := by rw [h']; group
  have hinj : Set.InjOn (fun x : ↥suzT => ((g * x * g⁻¹ : ↥suzT) : Equiv.Perm (Fin 1782)))
      (F : Set ↥suzT) := by
    intro x _ y _ hxy
    have h' : g * x * g⁻¹ = g * y * g⁻¹ := Subtype.ext hxy
    simpa using h'
  have hle := Set.ncard_le_ncard_of_injOn _ hsub hinj (Set.toFinite _)
  have hins : (insert (1 : Equiv.Perm (Fin 1782)) {h | h ∈ invSylow ∧ orderOf h = 2}).ncard ≤
      912 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [ncard_sylowInvolutions]
  have hF : Nat.card F = (F : Set ↥suzT).ncard := Nat.card_coe_set_eq (F : Set ↥suzT)
  have : (F : Set ↥suzT).ncard ≤ 912 := hle.trans hins
  rw [← hFcard, hF]
  omega

theorem suzM_inv_not_commute
    {p : ℕ} (hp0 : ¬ p ∣ 161280) (hp1 : ¬ p ∣ 3317760) :
    ∀ t z : ↥suzM, orderOf t = 2 → orderOf z = p → t * z ≠ z * t := by
  intro t z ht hz htz
  have ht' : orderOf (t : Equiv.Perm (Fin 1782)) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  obtain ⟨c, hc, h⟩ := suzM_involution_class t.2 ht'
  have key : ∀ i < 4, c * suzInv i * c⁻¹ = (t : Equiv.Perm (Fin 1782)) →
      Nat.card ↥(suzM ⊓ Subgroup.centralizer {(t : Equiv.Perm (Fin 1782))}) =
        Nat.card (invE i) := by
    intro i hi hci
    rw [← hci, ← map_conj_inf_centralizer (suzM_conj_iff hc) (suzInv i),
      ← Nat.card_congr ((suzM ⊓ Subgroup.centralizer {suzInv i}).equivMapOfInjective _
        (MulAut.conj c).injective).toEquiv, invE_eq_centM hi, centM, inf_comm]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hE0, hE1, -, -, -⟩ :=
    CTUC_Suz_four_exact_involution_centralizers
  have hzmem : (z : Equiv.Perm (Fin 1782)) ∈
      suzM ⊓ Subgroup.centralizer {(t : Equiv.Perm (Fin 1782))} :=
    ⟨z.2, Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val htz).symm⟩
  have hdvd : p ∣ Nat.card ↥(suzM ⊓ Subgroup.centralizer {(t : Equiv.Perm (Fin 1782))}) := by
    rw [← hz, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_mk _ hzmem]
    exact orderOf_dvd_natCard _
  rcases h with h | h
  · rw [key 0 (by norm_num) h, hE0] at hdvd
    exact hp0 hdvd
  · rw [key 1 (by norm_num) h, hE1] at hdvd
    exact hp1 hdvd

theorem row_Suz_11 :
    KFactSporLocalRow .Suz 11 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  have h10 : orderOf (2 : ZMod 11) = 10 :=
    orderOf_two_zmod_eq 11 10 (by norm_num) (by decide) (by decide)
  refine row_of_oddCent_rank ↥suzM ⟨suzEquivM.symm.trans b⟩
    (suzM_inv_not_commute (by norm_num) (by norm_num)) ?_
  rw [h10]
  exact suzM_elemAbelianLt

theorem row_Suz_13 :
    KFactSporLocalRow .Suz 13 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  have h12 : orderOf (2 : ZMod 13) = 12 :=
    orderOf_two_zmod_eq 13 12 (by norm_num) (by decide) (by decide)
  refine row_of_oddCent_rank ↥suzM ⟨suzEquivM.symm.trans b⟩
    (suzM_inv_not_commute (by norm_num) (by norm_num)) ?_
  rw [h12]
  exact fun E hE => lt_of_lt_of_le (suzM_elemAbelianLt E hE) (by norm_num)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
