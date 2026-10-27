module

public import CFSG.HardMathSupport.Malle.E27Lie.Cross.Index
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.HardMathSupport.Foote.E27.Split

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 CFSG.LocalAnalysis.ComponentInitial TauCeti
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSL)
open Subgroup CFSG.BenderSuzuki.MatrixGroups CFSG.GorensteinWalter

theorem false_of_cyclic_sylow_three {G : Type*} [Group G] [Finite G]
    (hcyc : ∀ P : Sylow 3 G, IsCyclic P) {R : Subgroup G}
    (hR : CFSG.Assembly.IsElemAbelian 3 R) (hc : Nat.card R = 27) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 R := fun x => ⟨1, Subtype.ext (by simpa using hR.2 x x.2)⟩
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have h1 : IsCyclic ↥(P : Subgroup G) := hcyc P
  have h2 : IsCyclic ↥R := by
    have := Subgroup.isCyclic_of_le hP
    exact this
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := R)
  have hg3 : g ^ 3 = 1 := Subtype.ext (hR.2 g g.2)
  have hord : orderOf g = 27 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hc]
  have := orderOf_dvd_of_pow_eq_one hg3
  rw [hord] at this
  omega

theorem isElemAbelian_map {H G : Type*} [Group H] [Group G] (θ : H ≃* G) {A : Subgroup H}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) :
    CFSG.Assembly.IsElemAbelian 3 (A.map θ.toMonoidHom) := CFSG.SectionRank.isElemAbelian_map hA _

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem false_of_psl2_model (h : E27Config X K R T z) (hz : z ∈ K) {p f : ℕ}
    (hcl : StatedClassicalModel K .PSL 2 p f) (hp3 : p ≠ 3) (hq4 : 4 ≤ p ^ f) : False := by
  obtain ⟨⟨hp, hf, -⟩, F, hF, hFin, hFc, ⟨e⟩⟩ := hcl
  haveI : Fact p.Prime := ⟨hp⟩
  let θ : ↥K ≃* PSL2MatrixGroup F :=
    ((e.trans (statedProjSLEquiv' 2 F)).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 F).symm)
  have hRK : R ≤ K := h.le_of_mem hz
  let R' : Subgroup ↥K := R.subgroupOf K
  have hR'c : Nat.card R' = 27 := by
    rw [← h.card_R]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv
  have hR'e : CFSG.Assembly.IsElemAbelian 3 R' := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => ?_⟩
    · have := congrArg Subtype.val (h.elem.1.is_comm.comm ⟨(a : K), a.2⟩ ⟨(b : K), b.2⟩)
      exact this
    · exact Subtype.ext (h.elem.2 _ ha)
  have hG : Finite (PSL2MatrixGroup F) := Finite.of_equiv _ θ.toEquiv
  have hc27 : Nat.card (R'.map θ.toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective θ.injective, hR'c]
  have he27 := isElemAbelian_map θ hR'e
  have hFc' : Nat.card F = p ^ f := hFc
  by_cases h7 : 7 ≤ p ^ f
  · refine false_of_cyclic_sylow_three (fun P => ?_) he27 hc27
    have hcop : Nat.Coprime 3 (Nat.card F) := by
      rw [hFc']
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3))
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact psl2_sylow_isCyclic_of_coprime_field_card F hFc' (by omega) 3 (by norm_num) hcop P
  ·
    have h27 : 27 ∣ Nat.card K := by
      have := Subgroup.card_subgroup_dvd_card R'
      rwa [hR'c] at this
    have hform := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F) (n := 2)
      (by norm_num)
    rw [← Nat.card_congr e.toEquiv] at hform
    have hgd : Nat.gcd 2 (Nat.card F - 1) ∣ Nat.card F ^ (2 * (2 - 1) / 2) *
        (∏ j ∈ Finset.Icc 2 2, (Nat.card F ^ j - 1)) := by
      simp only [Finset.Icc_self, Finset.prod_singleton]
      have h1 : Nat.gcd 2 (Nat.card F - 1) ∣ Nat.card F - 1 := Nat.gcd_dvd_right _ _
      have h2 : Nat.card F - 1 ∣ Nat.card F ^ 2 - 1 := by
        simpa using Nat.sub_dvd_pow_sub_pow (Nat.card F) 1 2
      exact (h1.trans h2).mul_left _
    have hNd := (hform ▸ Nat.div_dvd_of_dvd hgd : Nat.card K ∣ _)
    have h27' := h27.trans hNd
    rw [hFc'] at h27'
    simp only [Finset.Icc_self, Finset.prod_singleton] at h27'
    have hq7 : p ^ f < 7 := by omega
    generalize p ^ f = q at hq4 hq7 h27'
    interval_cases q <;> omega

theorem false_of_typeA_one (h : E27Config X K R T z) (hz : z ∈ K) {q : PrimePower}
    (hv : (LieTypeIndex.A 1 q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.A 1 q, hv⟩)) (hp3 : q.p ≠ 3) : False := by
  obtain ⟨e⟩ := e
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have h4 : 4 ≤ q.p ^ q.exponent := by
    simpa [PrimePower.card_def] using hrange.2 rfl
  exact false_of_psl2_model h hz (statedClassicalModel_typeA' hv e) hp3 h4

end CFSG.HardMathSupport.Malle.E27Lie
