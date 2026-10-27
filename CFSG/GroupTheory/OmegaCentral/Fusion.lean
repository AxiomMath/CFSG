module

public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.CoprimeOmega
import TauCeti.GroupTheory.OrderOfElement.PPart
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer

public section

namespace CFSG.GroupTheory

open Subgroup

open scoped Pointwise

variable {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]

private def ocFusionAux_omega (p : ℕ) (Q : Subgroup K) : Set K :=
  {w : K | w ∈ Q ∧ w ^ p = 1}

private def ocFusionAux_R (p : ℕ) (Q : Subgroup K) : Subgroup K :=
  Subgroup.normalizer (Q : Set K) ⊓ Subgroup.centralizer (ocFusionAux_omega p Q)

omit [Finite K] [Fact p.Prime] in
private theorem ocFusionAux_normalizer_le_normalizer_R (Q : Subgroup K) :
    Subgroup.normalizer (Q : Set K) ≤
      Subgroup.normalizer (ocFusionAux_R p Q : Set K) := by
  rw [Subgroup.le_normalizer_iff]
  intro n hn r hr
  constructor
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hr.1) (Subgroup.inv_mem _ hn)
  · refine Subgroup.mem_centralizer_iff.mpr ?_
    intro w hw
    have hwQ : w ∈ Q := hw.1
    have hw'Q : n⁻¹ * w * n ∈ Q := (Subgroup.mem_normalizer_iff''.mp hn w).mp hwQ
    have hw'p : (n⁻¹ * w * n) ^ p = 1 := by
      calc (n⁻¹ * w * n) ^ p = n⁻¹ * w ^ p * n := by
            simpa using (conj_pow (a := n⁻¹) (b := w) (i := p))
        _ = 1 := by rw [hw.2]; group
    have hw'Ω : n⁻¹ * w * n ∈ ocFusionAux_omega p Q := ⟨hw'Q, hw'p⟩
    have hcomm := (Subgroup.mem_centralizer_iff.mp hr.2) (n⁻¹ * w * n) hw'Ω
    calc w * (n * r * n⁻¹) = n * ((n⁻¹ * w * n) * r) * n⁻¹ := by group
      _ = n * (r * (n⁻¹ * w * n)) * n⁻¹ := by rw [hcomm]
      _ = (n * r * n⁻¹) * w := by group

private theorem ocFusionAux_isPGroup_quotient (hp2 : p ≠ 2) (S : Sylow p K)
    {Q : Subgroup K} (hQS : Q ≤ (S : Subgroup K))
    [hCn : ((Subgroup.centralizer (Q : Set K)).subgroupOf
      (ocFusionAux_R p Q)).Normal] :
    IsPGroup p (ocFusionAux_R p Q ⧸
      (Subgroup.centralizer (Q : Set K)).subgroupOf (ocFusionAux_R p Q)) := by
  classical
  let R : Subgroup K := ocFusionAux_R p Q
  let C : Subgroup R := (Subgroup.centralizer (Q : Set K)).subgroupOf R
  let : C.Normal := hCn
  intro y
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective C y
  let x : K := (r : K)
  let a : K := TauCeti.pPart p x
  let z : K := TauCeti.pFreePart p x
  have haR : a ∈ R := (Subgroup.zpowers_le.mpr r.2) (TauCeti.pPart_mem_zpowers p x)
  have hzR : z ∈ R := (Subgroup.zpowers_le.mpr r.2) (TauCeti.pFreePart_mem_zpowers p x)
  have hxeq : (r : K) = a * z := (TauCeti.pPart_mul_pFreePart p x).symm
  have hzN : z ∈ Subgroup.normalizer (Q : Set K) := hzR.1
  have hzCΩ : z ∈ Subgroup.centralizer (ocFusionAux_omega p Q) := hzR.2
  have hzCQ : z ∈ Subgroup.centralizer (Q : Set K) := by
    let α : MulAut ↥Q := Q.normalizerMonoidHom ⟨z, hzN⟩
    have hαdvd : orderOf α ∣ orderOf z := by
      have h := orderOf_map_dvd Q.normalizerMonoidHom
        (⟨z, hzN⟩ : Subgroup.normalizer (Q : Set K))
      rwa [Subgroup.orderOf_mk] at h
    have hzcop : Nat.Coprime (orderOf z) p :=
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr
        (TauCeti.not_dvd_orderOf_pFreePart (p := p) Fact.out (x := x)
          (orderOf_pos x).ne')).symm
    have hαcop : Nat.Coprime (orderOf α) p := hzcop.coprime_dvd_left hαdvd
    have hfix : ∀ w : ↥Q, w ^ p = 1 → α w = w := by
      intro w hw
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hwp : (w : K) ^ p = 1 := by
        simpa using congrArg (fun q : ↥Q => (q : K)) hw
      have hwΩ : (w : K) ∈ ocFusionAux_omega p Q := ⟨w.2, hwp⟩
      have hcomm : z * (w : K) = (w : K) * z :=
        ((Subgroup.mem_centralizer_iff.mp hzCΩ) (w : K) hwΩ).symm
      rw [hcomm]
      group
    have hα1 : α = 1 :=
      CFSG.HardMathSupport.Timmesfeld.ComponentBalance.mulAut_eq_one_of_coprime_of_fix_omega
        (P := ↥Q) hp2 (S.isPGroup'.to_le hQS) hαcop hfix
    have hzker : (⟨z, hzN⟩ : Subgroup.normalizer (Q : Set K)) ∈
        Q.normalizerMonoidHom.ker := by
      rw [MonoidHom.mem_ker]
      exact hα1
    rw [Subgroup.normalizerMonoidHom_ker] at hzker
    exact Subgroup.mem_subgroupOf.mp hzker
  have hzC : (QuotientGroup.mk' C) (⟨z, hzR⟩ : R) = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact Subgroup.mem_subgroupOf.mpr hzCQ
  have hxquot : (QuotientGroup.mk' C) r = (QuotientGroup.mk' C) (⟨a, haR⟩ : R) := by
    have hr : r = (⟨a, haR⟩ : R) * (⟨z, hzR⟩ : R) := by
      apply Subtype.ext
      exact hxeq
    rw [hr, map_mul, hzC, mul_one]
  refine ⟨(orderOf x).factorization p, ?_⟩
  have haord : orderOf (⟨a, haR⟩ : R) = p ^ (orderOf x).factorization p := by
    rw [Subgroup.orderOf_mk]
    exact TauCeti.orderOf_pPart Fact.out (orderOf_pos x).ne'
  have hk : (⟨a, haR⟩ : R) ^ p ^ (orderOf x).factorization p = 1 := by
    rw [← haord, pow_orderOf_eq_one]
  rw [hxquot, ← map_pow, hk, map_one]

omit [Finite K] [Fact p.Prime] in
private theorem ocFusionAux_inner_normalizer_le (S : Sylow p K)
    (hcen : ∀ w ∈ (S : Subgroup K), w ^ p = 1 →
      ∀ s ∈ (S : Subgroup K), s * w = w * s)
    {Q : Subgroup K} (hQS : Q ≤ (S : Subgroup K))
    (hcent : Subgroup.centralizer (Q : Set K) ⊓ (S : Subgroup K) ≤ Q)
    (hR : ocFusionAux_R p Q = Q ⊔ Subgroup.centralizer (Q : Set K)) :
    (S : Subgroup K) ⊓ Subgroup.normalizer (Q : Set K) ≤ Q := by
  intro s hs
  have hsS : s ∈ (S : Subgroup K) := hs.1
  have hsN : s ∈ Subgroup.normalizer (Q : Set K) := hs.2
  have hsR : s ∈ ocFusionAux_R p Q := by
    refine ⟨hsN, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro w hw
    exact (hcen w (hQS hw.1) hw.2 s hsS).symm
  have hsup : s ∈ Subgroup.centralizer (Q : Set K) ⊔ Q := by
    rw [sup_comm, ← hR]
    exact hsR
  have hset : ((Subgroup.centralizer (Q : Set K) ⊔ Q : Subgroup K) : Set K) =
      (Subgroup.centralizer (Q : Set K) : Set K) * (Q : Set K) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ (Subgroup.centralizer_le_normalizer _)
  have hsup' : s ∈ ((Subgroup.centralizer (Q : Set K) ⊔ Q : Subgroup K) : Set K) := hsup
  rw [hset] at hsup'
  obtain ⟨c, hcC, q, hqQ, hcq⟩ := Set.mem_mul.mp hsup'
  have hcS : c ∈ (S : Subgroup K) := by
    have hqS : q ∈ (S : Subgroup K) := hQS hqQ
    have hc_eq : c = s * q⁻¹ := by rw [← hcq]; group
    rw [hc_eq]
    exact Subgroup.mul_mem _ hsS (Subgroup.inv_mem _ hqS)
  have hcQ : c ∈ Q := hcent ⟨hcC, hcS⟩
  rw [← hcq]
  exact Subgroup.mul_mem _ hcQ hqQ

theorem isAlperinSubgroup_eq_of_omega_central (hp2 : p ≠ 2) (S : Sylow p K)
    (hcen : ∀ w ∈ (S : Subgroup K), w ^ p = 1 → ∀ s ∈ (S : Subgroup K), s * w = w * s)
    {Q : Subgroup K} (hQ : CFSG.RankTwoShapes.IsAlperinSubgroup p (S : Subgroup K) Q) :
    Q = (S : Subgroup K) := by
  obtain ⟨hQS, hcop, hcent, hrad⟩ := hQ
  have hQleR : Q ≤ ocFusionAux_R p Q := by
    refine le_inf Subgroup.le_normalizer ?_
    intro q hq
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro w hw
    exact (hcen w (hQS hw.1) hw.2 q (hQS hq)).symm
  have hCQleR : Subgroup.centralizer (Q : Set K) ≤ ocFusionAux_R p Q := by
    refine le_inf (Subgroup.centralizer_le_normalizer (Q : Set K)) ?_
    exact Subgroup.centralizer_le (fun w hw => hw.1)
  have hsup_le_R : Q ⊔ Subgroup.centralizer (Q : Set K) ≤ ocFusionAux_R p Q :=
    sup_le hQleR hCQleR
  have hRleNC : ocFusionAux_R p Q ≤
      Subgroup.normalizer (Subgroup.centralizer (Q : Set K) : Set K) :=
    inf_le_left.trans (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup Q)
  let : ((Subgroup.centralizer (Q : Set K)).subgroupOf (ocFusionAux_R p Q)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hRleNC
  have hindex : ∃ k : ℕ,
      ((Q ⊔ Subgroup.centralizer (Q : Set K)).subgroupOf (ocFusionAux_R p Q)).index = p ^ k := by
    have hpquot := ocFusionAux_isPGroup_quotient (p := p) hp2 S hQS
    have hCindex : ∃ k : ℕ,
        ((Subgroup.centralizer (Q : Set K)).subgroupOf (ocFusionAux_R p Q)).index = p ^ k := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p)
        (G := ocFusionAux_R p Q ⧸
          (Subgroup.centralizer (Q : Set K)).subgroupOf (ocFusionAux_R p Q))).mp hpquot
      exact ⟨k, by rw [Subgroup.index_eq_card]; exact hk⟩
    obtain ⟨k, hk⟩ := hCindex
    have hdvd : ((Q ⊔ Subgroup.centralizer (Q : Set K)).subgroupOf
          (ocFusionAux_R p Q)).index ∣
        ((Subgroup.centralizer (Q : Set K)).subgroupOf (ocFusionAux_R p Q)).index :=
      Subgroup.index_dvd_of_le (Subgroup.subgroupOf_mono (ocFusionAux_R p Q) le_sup_right)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out (m := k)).mp (hk ▸ hdvd)
    exact ⟨j, hj⟩
  have hR_eq : ocFusionAux_R p Q = Q ⊔ Subgroup.centralizer (Q : Set K) :=
    hrad (ocFusionAux_R p Q) hsup_le_R inf_le_left
      (ocFusionAux_normalizer_le_normalizer_R (p := p) Q) hindex
  have hNSQ : (S : Subgroup K) ⊓ Subgroup.normalizer (Q : Set K) ≤ Q :=
    ocFusionAux_inner_normalizer_le (p := p) S hcen hQS hcent hR_eq
  by_contra hne
  have hHne : Q.subgroupOf (S : Subgroup K) ≠ ⊤ := by
    intro htop
    exact hne (le_antisymm hQS (Subgroup.subgroupOf_eq_top.mp htop))
  have hHlt : Q.subgroupOf (S : Subgroup K) < ⊤ := lt_top_iff_ne_top.mpr hHne
  have hnil : Group.IsNilpotent (↥(S : Subgroup K)) := S.isPGroup'.isNilpotent
  have hnc : NormalizerCondition (↥(S : Subgroup K)) :=
    @Group.normalizerCondition_of_isNilpotent (↥(S : Subgroup K)) _ hnil
  obtain ⟨x, hxN, hxnot⟩ := SetLike.exists_of_lt (hnc _ hHlt)
  have hxNorm : (x : K) ∈ Subgroup.normalizer (Q : Set K) := by
    have hxsub : x ∈ (Subgroup.normalizer (Q : Set K)).subgroupOf (S : Subgroup K) := by
      rw [Subgroup.subgroupOf_normalizer_eq hQS]
      exact hxN
    exact Subgroup.mem_subgroupOf.mp hxsub
  have hxQ : (x : K) ∈ Q := hNSQ ⟨x.2, hxNorm⟩
  exact hxnot (Subgroup.mem_subgroupOf.mpr hxQ)

private theorem ocFusionAux_mem_normalizer_of_alperinDecomposition (hp2 : p ≠ 2)
    (S : Sylow p K)
    (hcen : ∀ w ∈ (S : Subgroup K), w ^ p = 1 →
      ∀ s ∈ (S : Subgroup K), s * w = w * s)
    {P : Subgroup K} {c : K}
    (hc : CFSG.RankTwoShapes.AlperinDecomposition p (S : Subgroup K) P c) :
    c ∈ Subgroup.normalizer ((S : Subgroup K) : Set K) := by
  induction hc with
  | one => exact Subgroup.one_mem _
  | @step c n Q _ hQ hPQ hn ih =>
      have hQeq : Q = (S : Subgroup K) :=
        isAlperinSubgroup_eq_of_omega_central hp2 S hcen hQ
      rw [hQeq] at hn
      exact Subgroup.mul_mem _ ih hn

theorem exists_normalizer_conj_of_omega_central (hp2 : p ≠ 2) (S : Sylow p K)
    (hcen : ∀ w ∈ (S : Subgroup K), w ^ p = 1 → ∀ s ∈ (S : Subgroup K), s * w = w * s)
    {x g : K} (hx : x ∈ (S : Subgroup K)) (hg : g⁻¹ * x * g ∈ (S : Subgroup K)) :
    ∃ c ∈ normalizer ((S : Subgroup K) : Set K), c⁻¹ * x * c = g⁻¹ * x * g := by
  have hP : Subgroup.zpowers x ≤ (S : Subgroup K) := Subgroup.zpowers_le.mpr hx
  have hPg : (Subgroup.zpowers x).map (MulAut.conj g⁻¹).toMonoidHom ≤ (S : Subgroup K) := by
    rw [MonoidHom.map_zpowers]
    refine Subgroup.zpowers_le.mpr ?_
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  obtain ⟨c, hc, hcg⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion S hP hPg
  exact ⟨c, ocFusionAux_mem_normalizer_of_alperinDecomposition hp2 S hcen hc,
    hcg x (Subgroup.mem_zpowers x)⟩

theorem sylow_eq_closure_of_omega_central (hp2 : p ≠ 2) (S : Sylow p K)
    (hcen : ∀ w ∈ (S : Subgroup K), w ^ p = 1 → ∀ s ∈ (S : Subgroup K), s * w = w * s)
    (hperf : commutator K = ⊤) :
    (S : Subgroup K) = closure {z : K | ∃ x ∈ (S : Subgroup K),
      ∃ c ∈ normalizer ((S : Subgroup K) : Set K), z = x⁻¹ * (c⁻¹ * x * c)} := by
  have hfocal : (S : Subgroup K) = closure {z : K | ∃ x : K, x ∈ (S : Subgroup K) ∧
      ∃ y : K, y ∈ (S : Subgroup K) ∧ IsConj x y ∧ z = x⁻¹ * y} := by
    have h := CFSG.sylow_inf_derivedSubgroup_eq_focalSubgroup p S
    rw [CFSG.derivedSubgroup, derivedSeries_one, hperf, inf_top_eq] at h
    exact h
  apply le_antisymm
  · conv_lhs => rw [hfocal]
    refine (Subgroup.closure_le _).mpr ?_
    rintro z ⟨x, hx, y, hy, hxy, rfl⟩
    obtain ⟨c, hc⟩ := isConj_iff.mp hxy
    have hgS : (c⁻¹)⁻¹ * x * c⁻¹ ∈ (S : Subgroup K) := by
      rw [inv_inv, hc]
      exact hy
    obtain ⟨d, hd, hdconj⟩ :=
      exists_normalizer_conj_of_omega_central hp2 S hcen hx hgS
    have hdconj' : d⁻¹ * x * d = y := by
      rw [hdconj]
      simpa using hc
    exact Subgroup.subset_closure ⟨x, hx, d, hd, by rw [hdconj']⟩
  · refine (Subgroup.closure_le (S : Subgroup K)).mpr ?_
    rintro z ⟨x, hx, c, hc, rfl⟩
    have hconj : c⁻¹ * x * c ∈ (S : Subgroup K) :=
      (Subgroup.mem_normalizer_iff''.mp hc x).mp hx
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hconj

