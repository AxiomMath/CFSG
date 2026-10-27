module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.NQOvergroups
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.PlaneCheck
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.SylowTransport
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import Certificates.Certificate753501

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.HardMathSupport.Dickson.I271
  CFSG.RankThree.Native CFSG.Sporadic.ON.Native CFSG.Open
open CFSG.AGLEmbedding.Norton.OrdinaryProofs (GLBCore_map_equiv GLBCore_map_conj)
open scoped commutatorElement

theorem isSubnormal_inf_eq_bot_or_le {X : Type*} [Group X] {A C S : Subgroup X}
    (h : IsSubnormal A C) (hSC : S ≤ C) (hS : IsSimpleGroup S) : A ⊓ S = ⊥ ∨ S ≤ A := by
  induction h with
  | refl => exact Or.inr hSC
  | @step A M C hAM hn _ ih =>
    rcases ih hSC with h | h
    · exact Or.inl (eq_bot_iff.mpr ((inf_le_inf_right S hAM).trans h.le))
    · rw [Subgroup.normal_subgroupOf_iff hAM] at hn
      have hN : (A.subgroupOf S).Normal := by
        refine ⟨fun x hx g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        simpa using hn _ _ hx (h g.2)
      rcases hS.eq_bot_or_eq_top_of_normal (A.subgroupOf S) with h' | h'
      · exact Or.inl (disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h'))
      · exact Or.inr (Subgroup.subgroupOf_eq_top.mp h')

theorem mem_normalizer_closure {G : Type*} [Group G] [Finite G] {s : Set G} {g : G}
    (h : ∀ x ∈ s, g * x * g⁻¹ ∈ Subgroup.closure s) :
    g ∈ Subgroup.normalizer ((Subgroup.closure s : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact h y hy
  | one => simp
  | mul y z _ _ hy hz =>
    have : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
    rw [this]
    exact mul_mem hy hz
  | inv y _ hy =>
    have : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hy

theorem one_le_pRank_of_mem {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Q : Subgroup G} {b : G} (hb : b ∈ Q) (hb1 : b ≠ 1) (hbp : b ^ p = 1) :
    1 ≤ CFSG.Open.pRank p Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.zpowers_le.2 hb)
    (isElemAbelian_zpowers hbp) ?_
  rw [Nat.card_zpowers, orderOf_eq_prime hbp hb1, pow_one]

theorem pow_pair_mul {G : Type*} [Group G] {x y : G} (hc : Commute x y) (hx : x ^ 7 = 1)
    (hy : y ^ 7 = 1) (e f e' f' a b : ℕ) :
    (x ^ e * y ^ f) ^ a * (x ^ e' * y ^ f') ^ b =
      x ^ ((e * a + e' * b) % 7) * y ^ ((f * a + f' * b) % 7) := by
  rw [(hc.pow_pow e f).mul_pow, (hc.pow_pow e' f').mul_pow, ← pow_mul, ← pow_mul, ← pow_mul,
    ← pow_mul, ← pow_eq_pow_mod _ hx, ← pow_eq_pow_mod _ hy, pow_add, pow_add]
  have hc' := (hc.pow_pow (e' * b) (f * a)).eq
  calc x ^ (e * a) * y ^ (f * a) * (x ^ (e' * b) * y ^ (f' * b))
      = x ^ (e * a) * (y ^ (f * a) * x ^ (e' * b)) * y ^ (f' * b) := by group
    _ = x ^ (e * a) * (x ^ (e' * b) * y ^ (f * a)) * y ^ (f' * b) := by rw [hc']
    _ = x ^ (e * a) * x ^ (e' * b) * (y ^ (f * a) * y ^ (f' * b)) := by group

theorem planeInv_spec : ∀ j < 28,
    (planeE[j]!.1 * planeInv[j]!.1 + planeE[j]!.2.2.1 * planeInv[j]!.2.1) % 7 = 1 ∧
    (planeE[j]!.2.1 * planeInv[j]!.1 + planeE[j]!.2.2.2 * planeInv[j]!.2.1) % 7 = 0 ∧
    (planeE[j]!.1 * planeInv[j]!.2.2.1 + planeE[j]!.2.2.1 * planeInv[j]!.2.2.2) % 7 = 0 ∧
    (planeE[j]!.2.1 * planeInv[j]!.2.2.1 + planeE[j]!.2.2.2 * planeInv[j]!.2.2.2) % 7 = 1 := by
  decide

section Abar


@[expose] noncomputable def b2P : Pv := qP 2

@[expose] noncomputable def Abar : Subgroup Pv := Subgroup.closure {b1P, b2P}

theorem b1P_mem_Abar : b1P ∈ Abar := Subgroup.subset_closure (by simp)

theorem b2P_mem_Abar : b2P ∈ Abar := Subgroup.subset_closure (by simp)


theorem b1P_ne_one : b1P ≠ 1 := Certificates.certificate753501.1

theorem b2P_ne_one : b2P ≠ 1 := Certificates.certificate753501.2.1

theorem b1P_pow_seven : b1P ^ 7 = 1 := Certificates.certificate753501.2.2.1

theorem b2P_pow_seven : b2P ^ 7 = 1 := Certificates.certificate753501.2.2.2.1

theorem commute_b1P_b2P : Commute b1P b2P := Certificates.certificate753501.2.2.2.2.1

theorem conj_q0_b1 : qP 0 * b1P * (qP 0)⁻¹ = b1P := Certificates.certificate753501.2.2.2.2.2.1

theorem conj_q0_b2 : qP 0 * b2P * (qP 0)⁻¹ = b1P * b2P :=
  Certificates.certificate753501.2.2.2.2.2.2.1

theorem conj_q1_b1 : qP 1 * b1P * (qP 1)⁻¹ = b1P * b2P :=
  Certificates.certificate753501.2.2.2.2.2.2.2.1

theorem conj_q1_b2 : qP 1 * b2P * (qP 1)⁻¹ = b2P :=
  Certificates.certificate753501.2.2.2.2.2.2.2.2.1

theorem qP0_mem_normalizer_Abar : qP 0 ∈ Subgroup.normalizer ((Abar : Subgroup Pv) : Set Pv) := by
  refine mem_normalizer_closure fun x hx => ?_
  rcases hx with rfl | rfl
  · rw [conj_q0_b1]; exact b1P_mem_Abar
  · rw [conj_q0_b2]; exact mul_mem b1P_mem_Abar b2P_mem_Abar

theorem qP1_mem_normalizer_Abar : qP 1 ∈ Subgroup.normalizer ((Abar : Subgroup Pv) : Set Pv) := by
  refine mem_normalizer_closure fun x hx => ?_
  rcases hx with rfl | rfl
  · rw [conj_q1_b1]; exact mul_mem b1P_mem_Abar b2P_mem_Abar
  · rw [conj_q1_b2]; exact b2P_mem_Abar

theorem tOut_mem_normalizer_b1 :
    tOut ∈ Subgroup.normalizer ((Subgroup.zpowers b1P : Subgroup Pv) : Set Pv) := by
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, tOut_conj_b1]
  exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 4) k

theorem M1_le_GLBCore_Abar :
    M1 ≤ GLBCore 7 1 Abar := by
  rw [← Mflat_eq_M1, Mflat, Subgroup.closure_le]
  have hA : Subgroup.normalizer ((Abar : Subgroup Pv) : Set Pv) ≤ GLBCore 7 1 Abar :=
    le_sSup ⟨Abar, le_rfl, one_le_pRank_of_mem Nat.prime_seven b2P_mem_Abar b2P_ne_one
      b2P_pow_seven, rfl⟩
  have hB : Subgroup.normalizer ((Subgroup.zpowers b1P : Subgroup Pv) : Set Pv) ≤
      GLBCore 7 1 Abar :=
    le_sSup ⟨_, Subgroup.zpowers_le.2 b1P_mem_Abar,
      one_le_pRank_of_mem Nat.prime_seven (Subgroup.mem_zpowers _) b1P_ne_one b1P_pow_seven, rfl⟩
  rintro _ (rfl | rfl | rfl | rfl)
  · exact hA qP0_mem_normalizer_Abar
  · exact hA qP1_mem_normalizer_Abar
  · exact hA (Subgroup.le_normalizer b2P_mem_Abar)
  · exact hB tOut_mem_normalizer_b1

end Abar

section PlaneConj


@[expose] noncomputable def planeY0 (j : ℕ) : Pv := if j < 14 then onLine 0 else alphaP (onLine 0)

@[expose] noncomputable def planeYj (j : ℕ) : Pv :=
  if j < 14 then onLine (j + 1) else alphaP (onLine (j + 1))

theorem planeY0_conj {j : ℕ} (hj : j < 28) :
    (planeC j)⁻¹ * planeY0 j * planeC j = b1P ^ planeE[j]!.1 * b2P ^ planeE[j]!.2.1 :=
  (Certificates.certificate753501.2.2.2.2.2.2.2.2.2 alphaP alphaP_a0 alphaP_a1 j hj).1

theorem planeYj_conj {j : ℕ} (hj : j < 28) :
    (planeC j)⁻¹ * planeYj j * planeC j = b1P ^ planeE[j]!.2.2.1 * b2P ^ planeE[j]!.2.2.2 :=
  (Certificates.certificate753501.2.2.2.2.2.2.2.2.2 alphaP alphaP_a0 alphaP_a1 j hj).2

theorem b1P_eq_planeY {j : ℕ} (hj : j < 28) :
    b1P = ((planeC j)⁻¹ * planeY0 j * planeC j) ^ planeInv[j]!.1 *
      ((planeC j)⁻¹ * planeYj j * planeC j) ^ planeInv[j]!.2.1 := by
  rw [planeY0_conj hj, planeYj_conj hj,
    pow_pair_mul commute_b1P_b2P b1P_pow_seven b2P_pow_seven, (planeInv_spec j hj).1,
    (planeInv_spec j hj).2.1, pow_one, pow_zero, mul_one]

theorem b2P_eq_planeY {j : ℕ} (hj : j < 28) :
    b2P = ((planeC j)⁻¹ * planeY0 j * planeC j) ^ planeInv[j]!.2.2.1 *
      ((planeC j)⁻¹ * planeYj j * planeC j) ^ planeInv[j]!.2.2.2 := by
  rw [planeY0_conj hj, planeYj_conj hj,
    pow_pair_mul commute_b1P_b2P b1P_pow_seven b2P_pow_seven, (planeInv_spec j hj).2.2.1,
    (planeInv_spec j hj).2.2.2, pow_one, pow_zero, one_mul]

theorem closure_planeY_conj {j : ℕ} (hj : j < 28) :
    Subgroup.closure {(planeC j)⁻¹ * planeY0 j * planeC j,
      (planeC j)⁻¹ * planeYj j * planeC j} = Abar := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [planeY0_conj hj]
      exact mul_mem (pow_mem b1P_mem_Abar _) (pow_mem b2P_mem_Abar _)
    · rw [planeYj_conj hj]
      exact mul_mem (pow_mem b1P_mem_Abar _) (pow_mem b2P_mem_Abar _)
  · rw [Abar, Subgroup.closure_le]
    have h0 : (planeC j)⁻¹ * planeY0 j * planeC j ∈ Subgroup.closure
        {(planeC j)⁻¹ * planeY0 j * planeC j, (planeC j)⁻¹ * planeYj j * planeC j} :=
      Subgroup.subset_closure (by simp)
    have h1 : (planeC j)⁻¹ * planeYj j * planeC j ∈ Subgroup.closure
        {(planeC j)⁻¹ * planeY0 j * planeC j, (planeC j)⁻¹ * planeYj j * planeC j} :=
      Subgroup.subset_closure (by simp)
    rintro _ (rfl | rfl)
    · rw [b1P_eq_planeY hj]
      exact mul_mem (pow_mem h0 _) (pow_mem h1 _)
    · rw [b2P_eq_planeY hj]
      exact mul_mem (pow_mem h0 _) (pow_mem h1 _)

theorem closure_planeY {j : ℕ} (hj : j < 28) :
    Subgroup.closure {planeY0 j, planeYj j} =
      Abar.map (MulAut.conj (planeC j) : Pv ≃* Pv).toMonoidHom := by
  rw [← closure_planeY_conj hj, MonoidHom.map_closure, Set.image_pair]
  congr 2 <;> simp [MulAut.conj_apply, mul_assoc]

theorem le_GLBCore_planeY
    {j : ℕ} (hj : j < 28) :
    M1.map (MulAut.conj (planeC j) : Pv ≃* Pv).toMonoidHom ≤
      GLBCore 7 1 (Subgroup.closure {planeY0 j, planeYj j}) := by
  rw [closure_planeY hj, GLBCore_map_conj]
  exact Subgroup.map_mono M1_le_GLBCore_Abar

end PlaneConj

end CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

end
