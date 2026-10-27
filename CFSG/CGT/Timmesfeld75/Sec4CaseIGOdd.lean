module

public import CFSG.CGT.Timmesfeld75.WeaklyClosed
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.NoncyclicAbelianPGroup

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG CFSG.Open
open scoped commutatorElement

section Abstract

variable {K : Type*} [Group K] [Finite K]

theorem oddNormal_comm_of_dichotomy {P : Subgroup K} (hP : IsElemAbelian 2 P)
    (h4 : 4 ≤ Nat.card P) (N : Subgroup K) [N.Normal] (hNodd : Odd (Nat.card N))
    (hdich : ∀ n ∈ N, ∀ u ∈ P, u ≠ 1 → u * n = n * u → ∀ y ∈ P, y * n = n * y) :
    ∀ n ∈ N, ∀ y ∈ P, y * n = n * y := by
  have hPN : P ≤ Subgroup.normalizer (N : Set K) := fun x _ =>
    Subgroup.mem_normalizer_iff.2 fun m => ⟨fun hm => Subgroup.Normal.conj_mem ‹N.Normal› m hm x,
      fun hm => by
        have h := Subgroup.Normal.conj_mem ‹N.Normal› _ hm x⁻¹
        have e : x⁻¹ * (x * m * x⁻¹) * x⁻¹⁻¹ = m := by group
        rwa [e] at h⟩
  let _ : MulDistribMulAction P N :=
    MulDistribMulAction.compHom N (N.normalizerMonoidHom.comp (Subgroup.inclusion hPN))
  have : Fact (IsPGroup 2 P) := ⟨isPGroup_two_of_isElemAbelian hP⟩
  let _ : CommGroup P :=
    { (inferInstance : Group P) with mul_comm := fun a b => hP.1.is_comm.comm a b }
  have hncyc : ¬ IsCyclic P := by
    intro hcyc
    obtain ⟨c, hc⟩ := hcyc.exists_generator
    have h1 : orderOf c = Nat.card P := orderOf_eq_card_of_forall_mem_zpowers hc
    have h2 : orderOf c ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hP.2 c c.2))
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have htop := iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := N) (A := P) 2 (Nat.coprime_two_left.2 hNodd) hncyc
  intro n hn y hy
  have hmem : (⟨n, hn⟩ : N) ∈ ⨆ (a : P) (_ : a ≠ 1),
      fixedPointSubgroup (↥(Subgroup.zpowers a)) N := by
    rw [htop]
    exact Subgroup.mem_top _
  have hle : (⨆ (a : P) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) N) ≤
      (Subgroup.centralizer (P : Set K)).comap N.subtype := by
    refine iSup₂_le fun a ha1 m hm => ?_
    rw [FixedPoints.mem_subgroup] at hm
    have h2 : (a : K) * m * (a : K)⁻¹ = m := congrArg Subtype.val (hm ⟨a, Subgroup.mem_zpowers a⟩)
    rw [mul_inv_eq_iff_eq_mul] at h2
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro z hz
    exact hdich m m.2 a a.2 (fun h => ha1 (Subtype.ext h)) h2 z hz
  exact Subgroup.mem_centralizer_iff.1 (hle hmem) y hy

end Abstract

end CFSG.CGT.Timmesfeld75
