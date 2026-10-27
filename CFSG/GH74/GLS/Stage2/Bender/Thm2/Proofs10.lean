module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Consumer
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Stmt10
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Stmt9

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Ten

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
  {Q T U : Subgroup G} {t g : G}

theorem remark_10F (h47 : Prop4_7cS) (ctx : Ctx10 G z k S M p Q T U t g) {H X : Subgroup G}
    (hH : Sig4Sub G z H p X) (hTH : T ≤ H) : X ≤ Op p H :=
  h47 G z k S ctx.ctx9.ctx H X T p hH (le_inf hTH ctx.T_le_S) ctx.T4CS
    (fun c hc => hH.A.inv c (hTH hc) (ctx.T_le_Cen hc))

theorem prop_10_1 (h914 : Prop9_14c) (h927 : Prop9_27) (h47 : Prop4_7cS) : Prop10_1 := by
  intro G _ _ z k S M p Q T U t g ctx R N hRne hRp hRM hTR hnQ hN hQN hTN
  have hz2 : z * z = 1 := ctx.ctx9.z_mul_z
  have hzN : z ∈ N := hTN ctx.z_mem_T
  have hzQ : z ∈ normalizer (Q : Set G) := ctx.M_le_normalizer_Q ctx.ctx9.z_mem
  have hzNn : z ∈ normalizer (N : Set G) := Subgroup.le_normalizer hzN
  have hzA : z ∈ normalizer ((Q ⊓ N : Subgroup G) : Set G) := mem_normalizer_inf hzQ hzNn
  have hzz : z ∈ normalizer ((zpowers z : Subgroup G) : Set G) := Subgroup.le_normalizer (mem_zpowers z)
  set A : Subgroup G := Q ⊓ N with hA
  set X : Subgroup G := ⁅A, zpowers z⁆ with hX
  have hXA : X ≤ A := commutator_le_of_normalizes (Subgroup.zpowers_le.mpr hzA)
  have hXQ : X ≤ Q := hXA.trans inf_le_left
  have hXN : X ≤ N := hXA.trans inf_le_right
  have hzX : z ∈ normalizer (X : Set G) := mem_normalizer_commutator hzA hzz
  have hXne : X ≠ ⊥ := by
    intro hXb
    apply hnQ
    intro y hy
    have hyA : y ∈ A := ⟨hy.1, hQN hy⟩
    have hmem : ⁅y, z⁆ ∈ X := Subgroup.commutator_mem_commutator hyA (mem_zpowers z)
    rw [hXb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact Subgroup.mem_centralizer_singleton_iff.mpr hmem
  have hNN : NN z p (Op p M) X := h914 G z k S M p ctx.ctx9 Q ctx.Q_mem X hXQ hXne hzX
  have hpg : IsPGroup p ↥X := ctx.Q_pgroup.to_le hXQ
  have hodd : ∀ a ∈ A, Odd (orderOf a) :=
    odd_orderOf_of_pgroup ctx.ctx9.prime ctx.ctx9.odd_p (ctx.Q_pgroup.to_le inf_le_left)
  have hinv : ∀ c ∈ N, c ∈ centralizer ({z} : Set G) → c ∈ normalizer (X : Set G) := by
    intro c hcN hcz
    have hcM : c ∈ M := ctx.ctx9.cen_le hcz
    have hcA : c ∈ normalizer (A : Set G) :=
      mem_normalizer_inf (ctx.M_le_normalizer_Q hcM) (Subgroup.le_normalizer hcN)
    have hcz' : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hcz
    exact mem_normalizer_commutator hcA (mem_normalizer_zpowers_of_comm hcz')
  have hsig : Sig4Sub G z N p X :=
    ⟨hN.1, ⟨ctx.ctx9.prime, ctx.ctx9.odd, hzN, hXN, hpg, hXne, hinv,
      comm_comm_eq_of_odd hz2 hzA hodd⟩⟩
  have hXO : X ≤ Op p N := remark_10F h47 ctx hsig hTN
  exact h927 G z k S M p ctx.ctx9 N X hN hNN hXN hXO

omit [Finite G] in
theorem Cov10.mono {k : Kind} {U A A' : Subgroup G} (h : A ≤ A') (hc : Cov10 k U A) : Cov10 k U A' := by
  intro hn
  have := hc hn
  unfold Covers at this ⊢
  exact this.trans (sup_le_sup_right (inf_le_inf_right _ h) _)

omit [Finite G] in
theorem R0_mono {H H' R : Subgroup G} {k : Kind} {p : ℕ} {T U : Subgroup G} (h : H ≤ H')
    (hR : R0 k p T U H R) : R0 k p T U H' R :=
  ⟨hR.1, hR.2.1, hR.2.2.1.trans h, hR.2.2.2.1, Cov10.mono (inf_le_inf_right _ h) hR.2.2.2.2⟩

theorem lemma_10_2 (hC2 : Lemma10_2b_C2) : Lemma10_2 := by
  intro G _ _ z k S M p Q T U t g ctx H H' hH _hH' hHOK _hHOK'
  refine ⟨fun hle R hR => R0_mono hle hR, fun R hR => ?_, fun R R₀ hR hR₀R hR₀ne hchar => ?_⟩
  · have hR1 : R0 k p T U (H ⊓ normalizer (R : Set G)) R :=
      ⟨hR.1, hR.2.1, le_inf hR.2.2.1 Subgroup.le_normalizer, hR.2.2.2.1, by
        rw [inf_assoc, inf_idem]; exact hR.2.2.2.2⟩
    refine ⟨hR1, ⟨fun hmax => ⟨hR1, fun R' hR' hRR' => hmax.2 R' (R0_mono inf_le_left hR') hRR'⟩, ?_⟩⟩
    intro hmax
    by_cases hTO : TypeOneCase G k
    · refine ⟨hR, fun R' hR' hRR' => ?_⟩
      have hR'' : R0 k p T U (H ⊓ normalizer (R : Set G)) (R' ⊓ normalizer (R : Set G)) := by
        refine ⟨?_, hR'.2.1.to_le inf_le_left, le_inf (inf_le_left.trans hR'.2.2.1) inf_le_right, ?_,
          fun hn => absurd hTO hn⟩
        · intro hb
          apply hR.1
          rw [eq_bot_iff]
          exact (le_inf hRR' Subgroup.le_normalizer).trans hb.le
        · intro x hx
          exact mem_normalizer_inf (hR'.2.2.2.1 hx) (Subgroup.le_normalizer (hR.2.2.2.1 hx))
      have hRR'' : R ≤ R' ⊓ normalizer (R : Set G) := le_inf hRR' Subgroup.le_normalizer
      have heq := hmax.2 _ hR'' hRR''
      exact (eq_of_inf_normalizer_le ctx.ctx9.prime hR'.2.1 hRR' heq.le).symm
    · exact hC2 G z k S M p Q T U t g ctx hTO H hH hHOK R hR hmax
  · refine ⟨hR₀ne, hR.2.1.to_le hR₀R, hR₀R.trans hR.2.2.1, fun x hx =>
      mem_normalizer_of_characteristic hR₀R hchar (hR.2.2.2.1 hx), ?_⟩
    exact Cov10.mono (inf_le_inf_left H (fun x hx => mem_normalizer_of_characteristic hR₀R hchar hx))
      hR.2.2.2.2

end Ten

end CFSG.GH74.GLS.Stage2.Bender.Thm2
