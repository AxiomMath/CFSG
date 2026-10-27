module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.NoncyclicAbelianPGroup
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LargeExtraspecial.S9

open Subgroup CFSG.CGT.Timmesfeld75 CFSG.Open

variable {K : Type} [Group K] [Finite K]

theorem coprime_card_fusionOddCore : Nat.Coprime 2 (Nat.card (fusionOddCore K)) := by
  have e : fusionOddCore K = CFSG.pPrimeCore 2 K := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext N
    exact and_congr Iff.rfl Nat.coprime_two_left.symm
  rw [e]
  exact CFSG.pPrimeCore_coprime_card

theorem eq_one_of_mul_self_of_mem_fusionOddCore {o : K} (ho : o ∈ fusionOddCore K)
    (h2 : o * o = 1) : o = 1 := by
  have hdvd1 : orderOf (⟨o, ho⟩ : fusionOddCore K) ∣ Nat.card (fusionOddCore K) :=
    orderOf_dvd_natCard _
  have hdvd2 : orderOf (⟨o, ho⟩ : fusionOddCore K) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simp [pow_two, h2]))
  have h1 : orderOf (⟨o, ho⟩ : fusionOddCore K) = 1 :=
    Nat.eq_one_of_dvd_coprimes coprime_card_fusionOddCore hdvd2 hdvd1
  have := congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
  simpa using this

omit [Finite K] in
theorem not_isCyclic_of_isElemAbelian {T : Subgroup K} (hT : IsElemAbelian 2 T)
    (h4 : 4 ≤ Nat.card T) : ¬ IsCyclic T := by
  intro hc
  have hexp : Monoid.exponent T ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by simpa using hT.2 x x.2)
  rw [IsCyclic.exponent_eq_card] at hexp
  have := Nat.le_of_dvd (by norm_num) hexp
  omega

theorem not_zStarCase {T : Subgroup K} (hT : IsElemAbelian 2 T) (h4 : 4 ≤ Nat.card T)
    (hTI : ∀ g : K, T ⊓ conjSubgroup g T = ⊥ ∨ T ⊓ conjSubgroup g T = T)
    (hO2 : ∀ N : Subgroup K, N.Normal → IsPGroup 2 N → N = ⊥) : ¬ ZStarCase K := by
  intro hZ
  have hOn : (fusionOddCore K).Normal := fusionOddCore_normal K
  have hab : ∀ x y : K, x * y * x⁻¹ * y⁻¹ ∈ fusionOddCore K := by
    intro x y
    have hx : x ∈ fusionZStar K := hZ ▸ mem_top x
    have hc := mem_center_iff.mp hx (QuotientGroup.mk' (fusionOddCore K) y)
    have h1 : QuotientGroup.mk' (fusionOddCore K) (x * y * x⁻¹ * y⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      calc QuotientGroup.mk' (fusionOddCore K) x * QuotientGroup.mk' (fusionOddCore K) y *
            (QuotientGroup.mk' (fusionOddCore K) x)⁻¹ * (QuotientGroup.mk' (fusionOddCore K) y)⁻¹
          = (QuotientGroup.mk' (fusionOddCore K) x * QuotientGroup.mk' (fusionOddCore K) y) *
            (QuotientGroup.mk' (fusionOddCore K) y * QuotientGroup.mk' (fusionOddCore K) x)⁻¹ := by
            group
        _ = 1 := by rw [hc, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hsq : ∀ s ∈ T, s * s = 1 := fun s hs => by rw [← pow_two]; exact hT.2 s hs
  have h3 : ∀ o ∈ fusionOddCore K, ∀ t ∈ T, t ≠ 1 → o * t = t * o → ∀ s ∈ T,
      o * s = s * o := by
    intro o ho t ht ht1 hot s hs
    have htc : t ∈ T ⊓ conjSubgroup o T := ⟨ht, mem_conjSubgroup.mpr (by
      rw [mul_assoc, ← hot, ← mul_assoc, inv_mul_cancel, one_mul]; exact ht)⟩
    rcases hTI o with h | h
    · rw [h] at htc
      exact absurd ((mem_bot).mp htc) ht1
    · have hs2 : s ∈ T ⊓ conjSubgroup o T := by rw [h]; exact hs
      have hs' : o⁻¹ * s * o ∈ T := mem_conjSubgroup.mp hs2.2
      have hmem : o⁻¹ * s * o * s⁻¹ ∈ fusionOddCore K := by
        have := mul_mem (inv_mem ho) (hOn.conj_mem o ho s)
        rwa [show o⁻¹ * (s * o * s⁻¹) = o⁻¹ * s * o * s⁻¹ by group] at this
      have hT1 : o⁻¹ * s * o * s⁻¹ ∈ T := mul_mem hs' (inv_mem hs)
      have h1 : o⁻¹ * s * o * s⁻¹ = 1 :=
        eq_one_of_mul_self_of_mem_fusionOddCore hmem (hsq _ hT1)
      have e : s * o = o * (o⁻¹ * s * o * s⁻¹) * s := by group
      rw [h1, mul_one] at e
      exact e.symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN : T ≤ normalizer (fusionOddCore K : Set K) := fun x _ =>
    mem_normalizer_iff.mpr fun o => ⟨fun h => hOn.conj_mem o h x, fun h => by
      have := hOn.conj_mem _ h x⁻¹
      rwa [show x⁻¹ * (x * o * x⁻¹) * x⁻¹⁻¹ = o by group] at this⟩
  have hTp : IsPGroup 2 T := fun x => ⟨1, Subtype.ext (by simpa using hT.2 x x.2)⟩
  let : IsMulCommutative T := hT.1
  let : CommGroup T := IsMulCommutative.instCommGroup
  let : Fact (IsPGroup 2 T) := ⟨hTp⟩
  let : MulDistribMulAction T (fusionOddCore K) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer T (fusionOddCore K) hTN
  have htop := iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := fusionOddCore K) (A := T) (p := 2) coprime_card_fusionOddCore
    (not_isCyclic_of_isElemAbelian hT h4)
  have hC : ∀ o ∈ fusionOddCore K, ∀ s ∈ T, o * s = s * o := by
    intro o ho
    have hle : (⨆ (a : T) (_ : a ≠ 1), fixedPointSubgroup (zpowers a) (fusionOddCore K)) ≤
        (centralizer (T : Set K)).subgroupOf (fusionOddCore K) := by
      refine iSup₂_le fun a ha1 o' ho' => ?_
      have hfix : a • o' = o' := ho' ⟨a, mem_zpowers a⟩
      have hfix' : (a : K) * (o' : K) * (a : K)⁻¹ = o' := congrArg Subtype.val hfix
      have hcomm : (o' : K) * a = a * o' := by
        calc (o' : K) * a = (a : K) * (o' : K) * (a : K)⁻¹ * a := by rw [hfix']
          _ = a * o' := by group
      rw [mem_subgroupOf, mem_centralizer_iff]
      intro s hs
      exact (h3 o' o'.2 a a.2 (fun h => ha1 (Subtype.ext h)) hcomm s hs).symm
    have hmem := hle (htop ▸ mem_top (⟨o, ho⟩ : fusionOddCore K))
    rw [mem_subgroupOf, mem_centralizer_iff] at hmem
    exact fun s hs => (hmem s hs).symm
  have hcen : ∀ x : K, ∀ s ∈ T, x * s * x⁻¹ = s := by
    intro x s hs
    have ho : x * s * x⁻¹ * s⁻¹ ∈ fusionOddCore K := hab x s
    have hos := hC _ ho s hs
    have he : x * s * x⁻¹ = (x * s * x⁻¹ * s⁻¹) * s := by group
    have hsq' : (x * s * x⁻¹) * (x * s * x⁻¹) = 1 := by
      rw [show x * s * x⁻¹ * (x * s * x⁻¹) = x * (s * s) * x⁻¹ by group, hsq s hs, mul_one,
        mul_inv_cancel]
    rw [he] at hsq'
    have ho2 : (x * s * x⁻¹ * s⁻¹) * (x * s * x⁻¹ * s⁻¹) = 1 := by
      set o := x * s * x⁻¹ * s⁻¹
      calc o * o = o * o * (s * s) := by rw [hsq s hs, mul_one]
        _ = o * (o * s) * s := by group
        _ = o * (s * o) * s := by rw [hos]
        _ = (o * s) * (o * s) := by group
        _ = 1 := hsq'
    rw [he, eq_one_of_mul_self_of_mem_fusionOddCore ho ho2, one_mul]
  have hTn : T.Normal := ⟨fun s hs x => by rw [hcen x s hs]; exact hs⟩
  have hbot := hO2 T hTn hTp
  rw [hbot, card_bot] at h4
  omega

end CFSG.LargeExtraspecial.S9
