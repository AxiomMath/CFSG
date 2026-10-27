module

public import CFSG.Quasithin.H13.L32AC43c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC43b

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

namespace Top43

variable {W K : Subgroup G} (C : Top43 T L V H W K) [IsMulCommutative ↥(conjClosure V H)]
include C

theorem pCoreOf_autK_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    pCoreOf 2 C.autK = ⊥ :=
  C.toTopW.pCoreOf_autOf C.hKH C.hKn (C.pCoreOf_range_F4 h1222 h1332 h1334)

theorem commV_autK_ne_bot_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    commV C.autK ≠ ⊥ :=
  C.toTopW.commV_autOf_ne_bot (C.autK_ne_bot_F4 h1222 h1332 h1334)

theorem mem_pCoreOf_of_comm_act_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) {B : Subgroup G} (hBT : B ≤ T) (b : ↥H) (hb : (b : G) ∈ B)
    (hc : ∀ k : ↥H, (k : G) ∈ K → C.act b * C.act k = C.act k * C.act b) :
    (b : G) ∈ pCoreOf 2 H :=
  C.mem_pCoreOf_of_commute_F4 h1222 h1332 h1334 (hBT hb) fun k hk => hc ⟨k, C.hKH hk⟩ hk

theorem qOff_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B) (hBT : B ≤ T) {Vs : Subgroup (Hat V H W)}
    (hVs : Vs ∈ IrrPlus C.autK ⊤) : QOff C.autK C.autT (C.autE B) (orbSup C.autT Vs) := by
  refine C.toTopW.qOff hB hBT (fun _ hf h => (C.mem_pCoreOf_iff_comm_F4 h1222 h1332 h1334
    (hBT hf)).mpr h) (C.mem_pCoreOf_of_comm_act_F4 h1222 h1332 h1334 hBT) ?_
  show C.autE B ⊓ centSub (orbSup C.autT Vs) = ⊥
  rw [C.orbSup_eq_top hVs, eq_bot_iff]
  intro a ha
  exact Subgroup.mem_bot.mpr (MulEquiv.ext fun v => ha.2 v (Subgroup.mem_top v))

theorem irr_or_d310Two_F4 (h310 : D310) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B) (hBT : B ≤ T) :
    (∀ J : Subgroup (Hat V H W), (∀ l ∈ C.autK, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤) ∨
      ∃ Vs : Subgroup (Hat V H W), D310Two C.autT C.autK Vs := by
  obtain ⟨Vs, hVs, hst | h2⟩ := C.toTopW.d310 h310 C.hK C.hKn C.hq
    (C.autK_ne_bot_F4 h1222 h1332 h1334) (C.pCoreOf_range_F4 h1222 h1332 h1334) hB hBT
    (fun _ hf h => (C.mem_pCoreOf_iff_comm_F4 h1222 h1332 h1334 (hBT hf)).mpr h)
    (C.mem_pCoreOf_of_comm_act_F4 h1222 h1332 h1334 hBT) fun Vs hVs =>
      (C.qOff_F4 h1222 h1332 h1334 hB hBT ⟨le_top, hVs.1.2⟩).faithVT
  · left
    have hVs1 : Vs ∈ IrrPlus C.autK ⊤ := ⟨le_top, hVs.1.2⟩
    obtain ⟨hinv, -, hlt, hirr⟩ := mem_irrPlus_top_iff.mp hVs1
    have hKs : C.autK ≤ stabSub Vs := fun l hl =>
      mem_stabSub_of_inv' (hinv l hl) (hinv l⁻¹ (C.autK.inv_mem hl))
    have hR : C.act.range ≤ stabSub Vs := by
      rw [C.range_eq_sup]
      exact sup_le hKs hst
    have hVtop : Vs = ⊤ := by
      rcases C.irr Vs (fun h y hy => (hR ⟨h, rfl⟩ y).mpr hy) with h0 | h1
      · exfalso
        rw [h0] at hlt
        exact (lt_irrefl _ (lt_of_le_of_lt bot_le hlt)).elim
      · exact h1

    have hfix : fixV C.autK = ⊥ := by
      have hH : ∀ h : ↥H, ∀ y ∈ fixV C.autK, C.act h y ∈ fixV C.autK := by
        intro h y hy l hl
        have hl' : (C.act h)⁻¹ * l * C.act h ∈ C.autK := by
          have := (Subgroup.mem_normalizer_iff.mp (C.range_le_normalizer
            (C.act.range.inv_mem ⟨h, rfl⟩)) l).mp hl
          simpa using this
        have := hy _ hl'
        calc l (C.act h y) = C.act h (((C.act h)⁻¹ * l * C.act h) y) := by
              simp [MulAut.mul_apply]
          _ = C.act h y := by rw [this]
      rcases C.irr _ hH with h0 | h1
      · exact h0
      · exfalso
        apply C.commV_autK_ne_bot_F4 h1222 h1332 h1334
        rw [eq_bot_iff]
        refine (Subgroup.closure_le _).mpr ?_
        rintro _ ⟨l, hl, v, rfl⟩
        have hv : v ∈ fixV C.autK := by rw [h1]; exact Subgroup.mem_top v
        rw [SetLike.mem_coe, hv l hl, mul_inv_cancel]
        exact Subgroup.one_mem _
    intro J hJ
    rw [hVtop, hfix, top_inf_eq] at hirr
    exact hirr J hJ bot_le le_top
  · exact Or.inr ⟨Vs, h2⟩

end Top43

end CFSG.Quasithin.H13.L32A.C
