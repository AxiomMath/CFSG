module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.I414Comp
public import CFSG.GH74.GLS.Stage2.Final.Thm6.I414Head

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.I414

open CFSG CFSG.LocalCores CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatalogueBHeldSmallCore (primeCore_subnormal_intersection)

theorem commutator_sup_le_of_normal {K : Type*} [Group K] (W A : Subgroup K) [W.Normal] :
    ⁅W ⊔ A, W ⊔ A⁆ ≤ W ⊔ ⁅A, A⁆ := by
  let π := QuotientGroup.mk' W
  have h1 : (W ⊔ A).map π = A.map π := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have h2 : (⁅W ⊔ A, W ⊔ A⁆).map π ≤ (⁅A, A⁆).map π := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, h1]
  intro x hx
  have h4 : x ∈ ⁅A, A⁆ ⊔ π.ker := by
    rw [← Subgroup.comap_map_eq]
    exact h2 (Subgroup.mem_map_of_mem π hx)
  rw [QuotientGroup.ker_mk', sup_comm] at h4
  exact h4

theorem normal_sup_centralizer {K : Type*} [Group K] (W R : Subgroup K) [W.Normal]
    (hfr : Subgroup.normalizer (R : Set K) ⊔ W = ⊤) :
    (W ⊔ Subgroup.centralizer (R : Set K)).Normal := by
  have key : ∀ g ∈ Subgroup.normalizer (R : Set K), ∀ x ∈ W ⊔ Subgroup.centralizer (R : Set K),
      g * x * g⁻¹ ∈ W ⊔ Subgroup.centralizer (R : Set K) := by
    intro g hg
    have hginv : g⁻¹ ∈ Subgroup.normalizer (R : Set K) := inv_mem hg
    have hle : W ⊔ Subgroup.centralizer (R : Set K) ≤
        (W ⊔ Subgroup.centralizer (R : Set K)).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact (le_sup_left : W ≤ W ⊔ Subgroup.centralizer (R : Set K))
          (‹W.Normal›.conj_mem x hx g)
      · refine (le_sup_right : Subgroup.centralizer (R : Set K) ≤ _) ?_
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hy' : g⁻¹ * y * g ∈ R := by
          have := (Subgroup.mem_normalizer_iff.mp hginv y).mp hy
          simpa using this
        have hc := Subgroup.mem_centralizer_iff.mp hx _ hy'
        calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
          _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc]
          _ = g * x * g⁻¹ * y := by group
    exact fun x hx => hle hx
  have hnorm : Subgroup.normalizer (R : Set K) ≤
      Subgroup.normalizer ((W ⊔ Subgroup.centralizer (R : Set K) : Subgroup K) : Set K) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨key g hg h, fun hh => ?_⟩
    have h3 := key g⁻¹ (inv_mem hg) _ hh
    have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rwa [e] at h3
  have hW : W ≤ Subgroup.normalizer
      ((W ⊔ Subgroup.centralizer (R : Set K) : Subgroup K) : Set K) :=
    le_sup_left.trans Subgroup.le_normalizer
  have htop : Subgroup.normalizer
      ((W ⊔ Subgroup.centralizer (R : Set K) : Subgroup K) : Set K) = ⊤ :=
    top_le_iff.mp (hfr ▸ sup_le hnorm hW)
  exact Subgroup.normalizer_eq_top_iff.mp htop

theorem ig414_core {K : Type} [Group K] [Finite K] {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hperf : Group.IsPerfect K)
    (hgen : ∀ N : Subgroup K, N.Normal → p.Coprime N.index → N = ⊤)
    (O : Subgroup K) [O.Normal] (hOp : p.Coprime (Nat.card O)) (hS : HasPropS ↥O)
    (hr : pPrimeCore r K = ⊥)
    {R : Subgroup K} (hR : IsSylowOf r R ⁅O, ⊤⁆) (hR1 : R ≠ ⊥)
    (Q : Subgroup K) (hQ : ∀ N : Subgroup K, N.Normal → N ≠ ⊤ → N ≤ Q) :
    Subgroup.centralizer (R : Set K) ≤ Q := by
  by_contra hnot
  set W : Subgroup K := ⁅O, ⊤⁆ with hW
  have hWn : W.Normal := Subgroup.commutator_normal O ⊤
  have hWO : W ≤ O := Subgroup.commutator_le_left O ⊤
  have hRW : R ≤ W := hR.le
  set C : Subgroup K := Subgroup.centralizer (R : Set K) with hC
  obtain ⟨P, hP⟩ := hR
  have hfr : Subgroup.normalizer (R : Set K) ⊔ W = ⊤ := by
    have := Sylow.normalizer_sup_eq_top P
    rwa [hP] at this
  have hN0 : (W ⊔ C).Normal := normal_sup_centralizer W R hfr
  have hWC : W ⊔ C = ⊤ := by
    by_contra h
    exact hnot ((le_sup_right : C ≤ W ⊔ C).trans (hQ _ hN0 h))
  obtain ⟨A, ⟨hAC, hWA⟩, hAmin⟩ :=
    (Set.toFinite {B : Subgroup K | B ≤ C ∧ W ⊔ B = (⊤ : Subgroup K)}).exists_minimal
      ⟨C, le_rfl, hWC⟩
  have hperfK : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := by
    have := Group.isPerfect_def.mp hperf
    rwa [_root_.commutator_def] at this
  have hAperf : ⁅A, A⁆ = A := by
    have hle : ⁅A, A⁆ ≤ A := Subgroup.commutator_le.mpr fun x hx y hy => by
      rw [commutatorElement_def]
      exact A.mul_mem (A.mul_mem (A.mul_mem hx hy) (A.inv_mem hx)) (A.inv_mem hy)
    have h1 : W ⊔ ⁅A, A⁆ = ⊤ := by
      have h2 := commutator_sup_le_of_normal W A
      rw [hWA, hperfK] at h2
      exact top_le_iff.mp h2
    exact le_antisymm hle (hAmin ⟨hle.trans hAC, h1⟩ hle)
  have : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.mpr hAperf
  let α : ↥A →* MulAut ↥W := (MulAut.conjNormal : K →* MulAut ↥W).comp A.subtype
  have hα : ∀ (a : A) (w : W), ((α a w : W) : K) = (a : K) * w * (a : K)⁻¹ := fun a w => rfl
  have hS' : HasPropS ↥W := HasPropS.of_le hWO hS
  have hXp : p.Coprime (Nat.card W) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hWO) hOp
  have hO' : pPrimeCore r ↥W = ⊥ := by
    rw [primeCore_subnormal_intersection r W hWn.isSubnormal, hr]
    exact Subgroup.bot_subgroupOf W
  have hfix : ∀ a : ↥A, ∀ x ∈ (P : Subgroup ↥W), α a x = x := by
    intro a x hx
    have hxR : (x : K) ∈ R := by rw [← hP]; exact ⟨x, hx, rfl⟩
    have hcomm : (x : K) * (a : K) = (a : K) * x :=
      Subgroup.mem_centralizer_iff.mp (hAC a.2) _ hxR
    apply Subtype.ext
    rw [hα]
    exact mul_inv_eq_iff_eq_mul.mpr hcomm.symm
  have hact : ∀ a : K, a ∈ A → ∀ n : ℕ, a ^ (p ^ n) = 1 →
      a ∈ Subgroup.centralizer (W : Set K) := by
    intro a ha n han
    have h1 := act_eq_one α hXp hS' hO' P hfix (a := ⟨a, ha⟩) (n := n)
      (Subtype.ext (by simpa using han))
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h2 := congrArg (fun m : MulAut ↥W => ((m ⟨w, hw⟩ : W) : K)) h1
    have h3 : a * w * a⁻¹ = w := h2
    exact (mul_inv_eq_iff_eq_mul.mp h3).symm
  set D : Subgroup K := Subgroup.centralizer (W : Set K) with hD
  have hDn : D.Normal := Subgroup.normal_centralizer
  have hN1 : W ⊔ D = ⊤ := by
    refine hgen (W ⊔ D) inferInstance (coprime_index_of_forall_quotient (W ⊔ D) fun g => ?_)
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    have hk : k ∈ W ⊔ A := by rw [hWA]; trivial
    obtain ⟨w, hw, a, ha, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hk
    obtain ⟨e, m, hm, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos a).ne' p
      (Fact.out : p.Prime).one_lt.ne'
    refine ⟨m, hm, ?_⟩
    have hmem : a ^ m ∈ W ⊔ D := (le_sup_right : D ≤ W ⊔ D)
      (hact (a ^ m) (A.pow_mem ha m) e (by
        rw [← pow_mul, mul_comm, ← hord]
        exact pow_orderOf_eq_one a))
    have hw1 : ((w : K) : K ⧸ (W ⊔ D)) = 1 :=
      (QuotientGroup.eq_one_iff w).mpr ((le_sup_left : W ≤ W ⊔ D) hw)
    rw [QuotientGroup.mk_mul, hw1, one_mul, ← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hmem
  have hD1 : D = ⊤ := by
    refine hgen D hDn (coprime_index_of_forall_quotient D fun g => ?_)
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    have hk : k ∈ W ⊔ D := by rw [hN1]; trivial
    obtain ⟨w, hw, d, hd, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hk
    refine ⟨Nat.card W, (Fact.out : p.Prime).coprime_iff_not_dvd.mp hXp, ?_⟩
    have hd1 : ((d : K) : K ⧸ D) = 1 := (QuotientGroup.eq_one_iff d).mpr hd
    have hw2 : w ^ Nat.card W = 1 := by
      have := pow_card_eq_one' (G := W) (x := ⟨w, hw⟩)
      exact congrArg Subtype.val this
    rw [QuotientGroup.mk_mul, hd1, mul_one, ← QuotientGroup.mk_pow, hw2]
    rfl
  have hWle : W ≤ Subgroup.centralizer ((⊤ : Subgroup K) : Set K) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro h _
    have : h ∈ D := by rw [hD1]; trivial
    exact (Subgroup.mem_centralizer_iff.mp this w hw).symm
  have hcomm1 : ⁅⁅(⊤ : Subgroup K), O⁆, (⊤ : Subgroup K)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (⊤ : Subgroup K) O]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hWle
  have hPerfTop : Group.IsPerfect ↥(⊤ : Subgroup K) := Subgroup.isPerfect_iff.mpr hperfK
  have hbot : ⁅(⊤ : Subgroup K), O⁆ = ⊥ := perfect_double_commutator hPerfTop hcomm1
  have hWbot : W = ⊥ := by
    rw [hW, Subgroup.commutator_comm]
    exact hbot
  exact hR1 (le_bot_iff.mp (hWbot ▸ hRW))

end CFSG.GH74.GLS.Stage2.Final.Thm6.I414
