module

public import CFSG.Certificates.Kernel.MonsterPcFive.E3Sound
public import CFSG.Certificates.Kernel.MonsterPcFive.ProdAsc
public import Certificates.Data.CFSGNative.Timmesfeld.PcFive
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbedding.CoverCore

public section

namespace CFSG.KC.MonPcFive

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveCensus (prodAsc)
open _root_.Timmesfeld.PcFive (pw cw)
open CFSG.KC.BM.PcFive (pow_mod_five)
open Subgroup

@[expose] def vecV (v : Array ℕ) : V9 :=
  ⟨v[0]!, v[1]!, ⟨v[2]!, v[3]!, v[4]!, v[5]!, v[6]!, v[7]!, v[8]!⟩⟩

@[expose] def bG {G : Type*} (g : Fin 9 → G) : Fin 6 → G := fun i => g ⟨i.val + 2, by omega⟩

theorem cw_c1 : ∀ i < 6, (vecV cw[1 * 9 + (i + 2)]!).beq ⟨0, 0, act1.get i⟩ = true := by
  decide +kernel

theorem cw_c2 : ∀ i < 6, (vecV cw[0 * 9 + (i + 2)]!).beq ⟨0, 0, act2.get i⟩ = true := by
  decide +kernel

theorem cw_x : ∀ i < 8, (vecV cw[i * 9 + 8]!).beq ⟨0, 0, RV.xg⟩ = true := by
  decide +kernel

theorem cw_sw : ∀ i j : Fin 6, i < j → (vecV cw[(i.val + 2) * 9 + (j.val + 2)]!).beq
    ⟨0, 0, { unitR j.val with c := (5 - cmAt cmM i j) % 5 }⟩ = true := by
  decide +kernel

theorem cw_r0 : (vecV cw[0 * 9 + 1]!).beq ⟨0, 1, rU⟩ = true := by decide +kernel

theorem pw_one : ∀ i < 9, i ≠ 1 → (vecV pw[i]!).beq V9.one = true := by
  decide +kernel

theorem pw_u1 : (vecV pw[1]!).beq ⟨0, 0, x2⟩ = true := by decide +kernel

theorem cm_sum : ∀ i j : Fin 6, ((5 - cmAt cmM i j) % 5 + cmAt cmM i j) % 5 = 0 := by
  decide +kernel

variable {G : Type*} [Group G] (g : Fin 9 → G)

theorem prodAsc_nine (v : Array ℕ) : prodAsc g v = g 0 ^ v[0]! * (g 1 ^ v[1]! * (g 2 ^ v[2]! *
    (g 3 ^ v[3]! * (g 4 ^ v[4]! * (g 5 ^ v[5]! * (g 6 ^ v[6]! * (g 7 ^ v[7]! *
    (g 8 ^ v[8]! * 1)))))))) := rfl

theorem prodAsc_eq_psi (v : Array ℕ) : prodAsc g v = psi (g 0) (g 1) (bG g) (g 8) (vecV v) := by
  rw [prodAsc_nine]
  simp only [psi, nfR, vecV, mul_one, mul_assoc]
  rfl

theorem psi_r (u2 u1 : G) (b : Fin 6 → G) (x : G) (r : RV) : psi u2 u1 b x ⟨0, 0, r⟩ = nfR b x r := by
  simp [psi]

theorem psi_r1 (u2 u1 : G) (b : Fin 6 → G) (x : G) (r : RV) :
    psi u2 u1 b x ⟨0, 1, r⟩ = u1 * nfR b x r := by
  simp [psi]

theorem nfR_unit_c (b : Fin 6 → G) (x : G) (k : Fin 6) (c : ℕ) :
    nfR b x { unitR k.val with c := c } = b k * x ^ c := by
  fin_cases k <;> simp [nfR, unitR]

theorem nfR_x2 (b : Fin 6 → G) (x : G) : nfR b x x2 = x ^ 2 := by simp [nfR, x2]

variable {g}

theorem pcHyp_of_rel (hpow : ∀ i : Fin 9, g i ^ 5 = prodAsc g pw[i.val]!)
    (hcomm : ∀ i j : Fin 9, i < j → g i * g j * (g i)⁻¹ = prodAsc g cw[i.val * 9 + j.val]!) :
    PcHyp (g 0) (g 1) (bG g) (g 8) := by
  have hc : ∀ (i j : ℕ) (hi : i < 9) (hj : j < 9), i < j →
      g ⟨i, hi⟩ * g ⟨j, hj⟩ * (g ⟨i, hi⟩)⁻¹ = psi (g 0) (g 1) (bG g) (g 8) (vecV cw[i * 9 + j]!) :=
    fun i j hi hj hij => by rw [hcomm ⟨i, hi⟩ ⟨j, hj⟩ hij, prodAsc_eq_psi]
  have hp : ∀ (i : ℕ) (hi : i < 9),
      g ⟨i, hi⟩ ^ 5 = psi (g 0) (g 1) (bG g) (g 8) (vecV pw[i]!) :=
    fun i hi => by rw [hpow ⟨i, hi⟩, prodAsc_eq_psi]
  have hone : ∀ (i : ℕ) (hi : i < 9), i ≠ 1 → g ⟨i, hi⟩ ^ 5 = 1 := fun i hi h1 => by
    rw [hp i hi, V9.beq_eq (pw_one i hi h1), psi_one]
  have x5 : g 8 ^ 5 = 1 := hone 8 (by omega) (by omega)
  have hxg : ∀ (i : ℕ) (hi : i < 8), g ⟨i, by omega⟩ * g 8 * (g ⟨i, by omega⟩)⁻¹ = g 8 := by
    intro i hi
    have e := hc i 8 (by omega) (by omega) hi
    rw [V9.beq_eq (cw_x i hi), psi_r, nfR_xg] at e
    exact e
  have xc : ∀ i : Fin 6, g 8 * bG g i = bG g i * g 8 := by
    intro i
    have e : bG g i * g 8 * (bG g i)⁻¹ = g 8 := hxg (i.val + 2) (by omega)
    calc g 8 * bG g i = (bG g i * g 8 * (bG g i)⁻¹) * bG g i := by rw [e]
      _ = bG g i * g 8 := by group
  have rel : RRel cmM (bG g) (g 8) := by
    refine ⟨x5, fun i => hone (i.val + 2) (by omega) (by omega), xc, ?_⟩
    intro i j hij
    have e := hc (i.val + 2) (j.val + 2) (by omega) (by omega) (by omega)
    rw [V9.beq_eq (cw_sw i j hij), psi_r, nfR_unit_c] at e
    have e0 : bG g i * bG g j * (bG g i)⁻¹ = bG g j * g 8 ^ ((5 - cmAt cmM i j) % 5) := e
    have e1 : bG g i * bG g j = bG g j * g 8 ^ ((5 - cmAt cmM i j) % 5) * bG g i :=
      mul_inv_eq_iff_eq_mul.mp e0
    have hxk : g 8 ^ ((5 - cmAt cmM i j) % 5) * bG g i =
        bG g i * g 8 ^ ((5 - cmAt cmM i j) % 5) := (Commute.pow_left (xc i) _).eq
    have hsum : g 8 ^ ((5 - cmAt cmM i j) % 5) * g 8 ^ cmAt cmM i j = 1 := by
      rw [← pow_add, pow_mod_five x5, cm_sum, pow_zero]
    calc bG g j * bG g i
        = bG g j * bG g i * (g 8 ^ ((5 - cmAt cmM i j) % 5) * g 8 ^ cmAt cmM i j) := by
          rw [hsum, mul_one]
      _ = bG g j * (bG g i * g 8 ^ ((5 - cmAt cmM i j) % 5)) * g 8 ^ cmAt cmM i j := by
          simp only [mul_assoc]
      _ = bG g j * g 8 ^ ((5 - cmAt cmM i j) % 5) * bG g i * g 8 ^ cmAt cmM i j := by
          rw [← hxk]
          simp only [mul_assoc]
      _ = bG g i * bG g j * g 8 ^ cmAt cmM i j := by rw [← e1]
  have c1 : ∀ i : Fin 6, g 1 * bG g i * (g 1)⁻¹ = nfR (bG g) (g 8) (act1.get i.val) := by
    intro i
    have e := hc 1 (i.val + 2) (by omega) (by omega) (by omega)
    rw [V9.beq_eq (cw_c1 i.val i.2), psi_r] at e
    exact e
  have c2 : ∀ i : Fin 6, g 0 * bG g i * (g 0)⁻¹ = nfR (bG g) (g 8) (act2.get i.val) := by
    intro i
    have e := hc 0 (i.val + 2) (by omega) (by omega) (by omega)
    rw [V9.beq_eq (cw_c2 i.val i.2), psi_r] at e
    exact e
  have r0 : g 0 * g 1 * (g 0)⁻¹ = g 1 * nfR (bG g) (g 8) rU := by
    have e := hc 0 1 (by omega) (by omega) (by omega)
    rw [V9.beq_eq cw_r0, psi_r1] at e
    exact e
  have u15 : g 1 ^ 5 = g 8 ^ 2 := by
    have e := hp 1 (by omega)
    rw [V9.beq_eq pw_u1, psi_r, nfR_x2] at e
    exact e
  exact ⟨rel, hone 0 (by omega) (by omega), u15, c1, c2, hxg 1 (by omega), hxg 0 (by omega), r0⟩

theorem closure_range_eq (H : PcHyp (g 0) (g 1) (bG g) (g 8)) :
    closure (Set.range g) = PSub (g 0) (g 1) (bG g) := by
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨k, rfl⟩
    have hR : closure (Set.range (bG g)) ≤ PSub (g 0) (g 1) (bG g) :=
      closure_mono (fun _ hy => Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hy))
    have hb : ∀ i : Fin 6, bG g i ∈ PSub (g 0) (g 1) (bG g) := fun i =>
      subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
    fin_cases k
    · exact subset_closure (Set.mem_insert _ _)
    · exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · exact hb 0
    · exact hb 1
    · exact hb 2
    · exact hb 3
    · exact hb 4
    · exact hb 5
    · exact hR H.rel.mem_x
  · unfold PSub
    rw [closure_le]
    rintro _ (rfl | rfl | ⟨i, rfl⟩)
    · exact subset_closure ⟨0, rfl⟩
    · exact subset_closure ⟨1, rfl⟩
    · exact subset_closure ⟨_, rfl⟩

theorem gen_comm_last (H : PcHyp (g 0) (g 1) (bG g) (g 8)) (k : Fin 9) : g k * g 8 = g 8 * g k := by
  fin_cases k
  · exact mul_inv_eq_iff_eq_mul.mp H.ux2
  · exact mul_inv_eq_iff_eq_mul.mp H.ux1
  · exact (H.rel.xc 0).symm
  · exact (H.rel.xc 1).symm
  · exact (H.rel.xc 2).symm
  · exact (H.rel.xc 3).symm
  · exact (H.rel.xc 4).symm
  · exact (H.rel.xc 5).symm
  · rfl

theorem comm_last_of_mem (H : PcHyp (g 0) (g 1) (bG g) (g 8)) {y : G}
    (hy : y ∈ closure (Set.range g)) : y * g 8 = g 8 * y := by
  induction hy using closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact gen_comm_last H k
  | one => simp
  | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  | inv x _ hx =>
    calc x⁻¹ * g 8 = x⁻¹ * (g 8 * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * g 8) * x⁻¹ := by rw [hx]
      _ = g 8 * x⁻¹ := by group

variable {G : Type} [Group G]

theorem elemAbelian_of_triple {T A B : G} (hTA : T * A = A * T) (hTB : T * B = B * T)
    (hAB : A * B = B * A) (hT : T ^ 5 = 1) (hA : A ^ 5 = 1) (hB : B ^ 5 = 1)
    (hind : ∀ i < 5, ∀ j < 5, ∀ l < 5, T ^ i * A ^ j * B ^ l = 1 → i = 0 ∧ j = 0 ∧ l = 0) :
    ∃ E : Subgroup G, CFSG.Open.IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 3 ∧ T ∈ E := by
  have hp : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  let D : CFSG.AGLEmbedding.ModuleSpec G 5 :=
    { n := 3, m := 0, a := ![T, A, B], g := fun j => j.elim0, M := fun j => j.elim0
      comm := by
        intro i j
        fin_cases i <;> fin_cases j
        · rfl
        · exact hTA
        · exact hTB
        · exact hTA.symm
        · rfl
        · exact hAB
        · exact hTB.symm
        · exact hAB.symm
        · rfl
      pow := by
        intro i
        fin_cases i
        · exact hT
        · exact hA
        · exact hB
      indep := by
        intro c hc
        simp only [List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil,
          List.prod_cons, List.prod_nil, mul_one] at hc
        simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Fin.isValue, Matrix.head_cons,
          Matrix.cons_val_succ, Matrix.tail_cons] at hc
        rw [← mul_assoc] at hc
        obtain ⟨e0, e1, e2⟩ := hind _ (ZMod.val_lt (c 0)) _ (ZMod.val_lt (c 1)) _
          (ZMod.val_lt (c 2)) hc
        funext k
        fin_cases k
        · exact (ZMod.val_eq_zero _).1 e0
        · exact (ZMod.val_eq_zero _).1 e1
        · exact (ZMod.val_eq_zero _).1 e2
      act := fun j => j.elim0 }
  have hEA : CFSG.Open.IsElemAbelian 5 D.span :=
    ⟨inferInstance, fun x hx => D.pow_eq_one_of_mem hx⟩
  exact ⟨D.span, hEA, D.card_span hp, Subgroup.subset_closure ⟨(0 : Fin 3), rfl⟩⟩

end CFSG.KC.MonPcFive

end
