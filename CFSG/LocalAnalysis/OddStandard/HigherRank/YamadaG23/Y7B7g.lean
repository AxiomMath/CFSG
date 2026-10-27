module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7Abs2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7Abs3
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7f

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y7b_B_le_H_aux (c : Ctx7 G L) (hb : B5Std c) : c.s.fr.B ≤ c.s.H :=
  (s3_B_le_S c.s).trans ((s3_S_le_L c.s).trans (s3_L_le_H c.s hb.hH.hS))

private theorem y7b_t_conj_M3 (c : Ctx7 G L) (hb : B5Std c) {m : G} (hm : m ∈ M3 c.s) :
    c.s.t * m * c.s.t⁻¹ ∈ M3 c.s :=
  y54_R_norm_M3 c.toCtx5 hb.hH c.s.t (s3_t_mem_R c.s) m hm

private theorem y7b_conjBM_mem_M3 (c : Ctx7 G L) (hb : B5Std c) {u : G}
    (hu : u ∈ y7bBM c.s) {x : G} (hx : x ∈ M3 c.s) : u * x * u⁻¹ ∈ M3 c.s :=
  (Subgroup.mem_normalizer_iff.mp
    (y7b_W_le_NM3 c hb (y7b_BM_le_W c hb hu)) x).mp hx

private theorem y7b_comm_B_M3 (c : Ctx7 G L) (hb : B5Std c) {b : G}
    (hbB : b ∈ c.s.fr.B) {m : G} (hm : m ∈ M3 c.s) : ⁅b, m⁆ ∈ M3 c.s := by
  have hconj : b * m * b⁻¹ ∈ M3 c.s :=
    (Subgroup.mem_normalizer_iff.mp (y7b_B_le_NM3 c hb hbB) m).mp hm
  have heq : ⁅b, m⁆ = (b * m * b⁻¹) * m⁻¹ := by rw [commutatorElement_def]
  rw [heq]
  exact (M3 c.s).mul_mem hconj ((M3 c.s).inv_mem hm)

private theorem y7b_BM_comm_mem_M3 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ u ∈ y7bBM c.s, ∀ v ∈ y7bBM c.s, ⁅u, v⁆ ∈ M3 c.s := by
  have hFM3 : c.s.fr.F ≤ M3 c.s := fun _ hx => Subgroup.mem_sup_right hx
  have hmm : ∀ m ∈ M3 c.s, ∀ m' ∈ M3 c.s, ⁅m, m'⁆ = 1 := by
    intro m hm m' hm'
    refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
    obtain ⟨hcomm, -⟩ := y7b_M3_elem c hb
    simpa using congrArg Subtype.val (hcomm.is_comm.comm ⟨m, hm⟩ ⟨m', hm'⟩)
  have hBm : ∀ b ∈ c.s.fr.B, ∀ m ∈ M3 c.s, ⁅b, m⁆ ∈ M3 c.s :=
    fun b hbB m hm => y7b_comm_B_M3 c hb hbB hm
  have hmB : ∀ m ∈ M3 c.s, ∀ b ∈ c.s.fr.B, ⁅m, b⁆ ∈ M3 c.s := by
    intro m hm b hbB
    rw [← commutatorElement_inv]
    exact (M3 c.s).inv_mem (hBm b hbB m hm)
  have hBB : ∀ b ∈ c.s.fr.B, ∀ b' ∈ c.s.fr.B, ⁅b, b'⁆ ∈ M3 c.s := by
    intro b hbB b' hb'B
    have h := y7b_B_comm_mem_V hb.hH b hbB b' hb'B
    rw [← y7b_E_inf_F hb.hH] at h
    exact hFM3 (Subgroup.mem_inf.mp h).2
  intro u hu v hv
  obtain ⟨b, hbB, m, hm, rfl⟩ := (y7b_mem_BM c hb).mp hu
  obtain ⟨b', hb'B, m', hm', rfl⟩ := (y7b_mem_BM c hb).mp hv
  have hbBM : b ∈ y7bBM c.s := Subgroup.mem_sup_left hbB
  have hb'BM : b' ∈ y7bBM c.s := Subgroup.mem_sup_left hb'B
  have hbm : ⁅m, b' * m'⁆ ∈ M3 c.s := by
    rw [commutatorElement_mul_right_eq_mul_conj, hmm m hm m' hm']
    rw [show ⁅m, b'⁆ * b' * 1 * b'⁻¹ = ⁅m, b'⁆ by group]
    exact hmB m hm b' hb'B
  have hbbm : ⁅b, b' * m'⁆ ∈ M3 c.s := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    rw [show ⁅b, b'⁆ * b' * ⁅b, m'⁆ * b'⁻¹ =
        ⁅b, b'⁆ * (b' * ⁅b, m'⁆ * b'⁻¹) by group]
    exact (M3 c.s).mul_mem (hBB b hbB b' hb'B)
      (y7b_conjBM_mem_M3 c hb hb'BM (hBm b hbB m' hm'))
  rw [commutatorElement_mul_left_eq_conj_mul]
  exact (M3 c.s).mul_mem (y7b_conjBM_mem_M3 c hb hbBM hbm) hbbm

private theorem y7b_BM_comm_t_mem_M3 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ u ∈ y7bBM c.s, ⁅u, c.s.t⁆ ∈ M3 c.s := by
  intro u hu
  obtain ⟨b, hbB, m, hm, rfl⟩ := (y7b_mem_BM c hb).mp hu
  have hbt : ⁅b, c.s.t⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (y7b_B_le_H_aux c hb hbB))
  have hmt : ⁅m, c.s.t⁆ ∈ M3 c.s := by
    have htm : ⁅c.s.t, m⁆ ∈ M3 c.s := by
      have hconj : c.s.t * m * c.s.t⁻¹ ∈ M3 c.s := y7b_t_conj_M3 c hb hm
      have heq : ⁅c.s.t, m⁆ = (c.s.t * m * c.s.t⁻¹) * m⁻¹ := by
        rw [commutatorElement_def]
      rw [heq]
      exact (M3 c.s).mul_mem hconj ((M3 c.s).inv_mem hm)
    rw [← commutatorElement_inv]
    exact (M3 c.s).inv_mem htm
  rw [commutatorElement_mul_left_eq_conj_mul, hbt, mul_one]
  exact y7b_conjBM_mem_M3 c hb (Subgroup.mem_sup_left hbB) hmt

private theorem y7b_t_comm_BM_mem_M3 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ u ∈ y7bBM c.s, ⁅c.s.t, u⁆ ∈ M3 c.s := by
  intro u hu
  rw [← commutatorElement_inv]
  exact (M3 c.s).inv_mem (y7b_BM_comm_t_mem_M3 c hb u hu)

theorem y7b_W_comm_mem_M3 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ w ∈ y7bW c.s, ∀ w' ∈ y7bW c.s, ⁅w, w'⁆ ∈ M3 c.s := by
  intro w hw w' hw'
  obtain ⟨u, hu, hwu | hwu⟩ := (y7b_mem_W c hb).mp hw
  · rw [hwu]
    obtain ⟨v, hv, hw'v | hw'v⟩ := (y7b_mem_W c hb).mp hw'
    · rw [hw'v]; exact y7b_BM_comm_mem_M3 c hb u hu v hv
    · rw [hw'v, commutatorElement_mul_right_eq_mul_conj]
      have huv := y7b_BM_comm_mem_M3 c hb u hu v hv
      have hv_conj : v * ⁅u, c.s.t⁆ * v⁻¹ ∈ M3 c.s :=
        y7b_conjBM_mem_M3 c hb hv (y7b_BM_comm_t_mem_M3 c hb u hu)
      rw [show ⁅u, v⁆ * v * ⁅u, c.s.t⁆ * v⁻¹ =
          ⁅u, v⁆ * (v * ⁅u, c.s.t⁆ * v⁻¹) by group]
      exact (M3 c.s).mul_mem huv hv_conj
  · rw [hwu]
    obtain ⟨v, hv, hw'v | hw'v⟩ := (y7b_mem_W c hb).mp hw'
    · rw [hw'v, commutatorElement_mul_left_eq_conj_mul]
      exact (M3 c.s).mul_mem
        (y7b_conjBM_mem_M3 c hb hu (y7b_t_comm_BM_mem_M3 c hb v hv))
        (y7b_BM_comm_mem_M3 c hb u hu v hv)
    · rw [hw'v, commutatorElement_mul_left_eq_conj_mul]
      have h1 : ⁅c.s.t, v * c.s.t⁆ ∈ M3 c.s := by
        rw [commutatorElement_mul_right_eq_mul_conj, commutatorElement_self]
        rw [show ⁅c.s.t, v⁆ * v * 1 * v⁻¹ = ⁅c.s.t, v⁆ by group]
        exact y7b_t_comm_BM_mem_M3 c hb v hv
      have h2 : ⁅u, v * c.s.t⁆ ∈ M3 c.s := by
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hv_conj : v * ⁅u, c.s.t⁆ * v⁻¹ ∈ M3 c.s :=
          y7b_conjBM_mem_M3 c hb hv (y7b_BM_comm_t_mem_M3 c hb u hu)
        rw [show ⁅u, v⁆ * v * ⁅u, c.s.t⁆ * v⁻¹ =
            ⁅u, v⁆ * (v * ⁅u, c.s.t⁆ * v⁻¹) by group]
        exact (M3 c.s).mul_mem (y7b_BM_comm_mem_M3 c hb u hu v hv) hv_conj
      exact (M3 c.s).mul_mem (y7b_conjBM_mem_M3 c hb hu h1) h2

theorem y7b_W_le_X0 (c : Ctx7 G L) (hb : B5Std c) : y7bW c.s ≤ y7bX0 c.s := by
  intro w hw
  refine ⟨(Subgroup.le_normalizer (H := y7bW c.s)) hw, y7b_W_le_NM3 c hb hw, ?_⟩
  intro k hk
  exact y7b_W_comm_mem_M3 c hb k hk w hw

theorem y7b_X0_le_X (c : Ctx7 G L) : y7bX0 c.s ≤ y7bX c.s := by
  intro x hx
  exact Subgroup.mem_inf.mpr ⟨hx.1, hx.2.1⟩

theorem y7b_X0_le_X7 (c : Ctx7 G L) (hb : B5Std c) : y7bX0 c.s ≤ X7 c.s := by
  intro x hx
  have hxX : x ∈ y7bX c.s := y7b_X0_le_X c hx
  refine Subgroup.mem_inf.mpr ⟨hxX, ?_⟩
  refine ⟨Subgroup.le_normalizer_iff.mpr (y7b_X_norm_BM c hb) hxX, hx.2.1, ?_⟩
  intro u hu
  exact hx.2.2 u (y7b_BM_le_W c hb hu)

theorem y7b_X0_normal (c : Ctx7 G L) (hb : B5Std c) :
    ∀ x ∈ y7bX c.s, ∀ a ∈ y7bX0 c.s, x * a * x⁻¹ ∈ y7bX0 c.s := by
  intro x hx a ha
  have hxW : x ∈ normalizer (y7bW c.s : Set G) := hx.1
  have hxM3 : x ∈ normalizer (M3 c.s : Set G) := hx.2
  have haW : a ∈ normalizer (y7bW c.s : Set G) := ha.1
  have haM3 : a ∈ normalizer (M3 c.s : Set G) := ha.2.1
  refine ⟨?_, ?_, ?_⟩
  · exact (normalizer (y7bW c.s : Set G)).mul_mem
      ((normalizer (y7bW c.s : Set G)).mul_mem hxW haW)
      ((normalizer (y7bW c.s : Set G)).inv_mem hxW)
  · exact (normalizer (M3 c.s : Set G)).mul_mem
      ((normalizer (M3 c.s : Set G)).mul_mem hxM3 haM3)
      ((normalizer (M3 c.s : Set G)).inv_mem hxM3)
  · intro k hk
    have hxinvW : x⁻¹ ∈ normalizer (y7bW c.s : Set G) :=
      (normalizer (y7bW c.s : Set G)).inv_mem hxW
    have hkW : x⁻¹ * k * x ∈ y7bW c.s := by
      have h := (Subgroup.mem_normalizer_iff.mp hxinvW k).mp hk
      simpa only [inv_inv] using h
    have hcomm : ⁅x⁻¹ * k * x, a⁆ ∈ M3 c.s := ha.2.2 _ hkW
    have hconj : x * ⁅x⁻¹ * k * x, a⁆ * x⁻¹ ∈ M3 c.s :=
      (Subgroup.mem_normalizer_iff.mp hxM3 _).mp hcomm
    have heq : ⁅k, x * a * x⁻¹⁆ = x * ⁅x⁻¹ * k * x, a⁆ * x⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]; group
    rw [heq]
    exact hconj

theorem y7b_exists_rhoB (c : Ctx7 G L) (hb : B5Std c) :
    ∃ ρ : ↥(y7bX c.s) →* Equiv.Perm (Fin 3),
      (∀ x : ↥(y7bX c.s), ρ x = 1 ↔ (x : G) ∈ X7 c.s) ∧ Function.Surjective ρ := by
  have hXM : ∀ x ∈ y7bX c.s, ∀ m ∈ M3 c.s, x * m * x⁻¹ ∈ M3 c.s :=
    fun x hx m hm => (Subgroup.mem_normalizer_iff.mp hx.2 m).mp hm
  obtain ⟨ρ, hρ⟩ := y7b_exists_perm3_hom (X := y7bX c.s) (M := M3 c.s) (U := y7bBM c.s)
    le_sup_right (fun u hu m hm => y7b_conjBM_mem_M3 c hb hu hm) (y7b_X_norm_BM c hb) hXM
    (y7b_relIndex_M3_BM c hb) (y7b_BM_sq_mem_M3 c hb)
  have hker : ∀ n : ↥(y7bX c.s), (n : G) ∈ normIn L c.s.fr.B →
      (ρ n = 1 ↔ (n : G) ∈ c.s.fr.B) := by
    intro n hnN
    rw [hρ n]
    constructor
    · intro hn1
      have hnNrmB : (n : G) ∈ normalizer (c.s.fr.B : Set G) := (Subgroup.mem_inf.mp hnN).2
      have hcommF : ∀ b ∈ c.s.fr.B, (n : G) * b * (n : G)⁻¹ * b⁻¹ ∈ c.s.fr.F := by
        intro b hbB
        have hcommM3 : ⁅(n : G), b⁆ ∈ M3 c.s := hn1 b (Subgroup.mem_sup_left hbB)
        have hcommB : ⁅(n : G), b⁆ ∈ c.s.fr.B := by
          have hconj : (n : G) * b * (n : G)⁻¹ ∈ c.s.fr.B :=
            (Subgroup.mem_normalizer_iff.mp hnNrmB b).mp hbB
          have heq : ⁅(n : G), b⁆ = ((n : G) * b * (n : G)⁻¹) * b⁻¹ := by
            rw [commutatorElement_def]
          rw [heq]
          exact (c.s.fr.B).mul_mem hconj ((c.s.fr.B).inv_mem hbB)
        have hinf : ⁅(n : G), b⁆ ∈ c.s.fr.B ⊓ M3 c.s :=
          Subgroup.mem_inf.mpr ⟨hcommB, hcommM3⟩
        rwa [y7b_B_inf_M3 c hb] at hinf
      have hcent : (n : G) ∈ centIn L (cen c.s.fr.B) := by
        refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hnN).1, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have hnv := y7b_cent_V_of_comm_F hb.hH hnNrmB hcommF v hv
        calc v * (n : G) = ((n : G) * v * (n : G)⁻¹) * (n : G) := by rw [hnv]
          _ = (n : G) * v := by group
      rwa [f3_centIn_L_V hb.hH] at hcent
    · intro hnB u hu
      obtain ⟨b, hbB, m, hm, rfl⟩ := (y7b_mem_BM c hb).mp hu
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hnb : ⁅(n : G), b⁆ ∈ M3 c.s := by
        have h := y7b_B_comm_mem_V hb.hH (n : G) hnB b hbB
        rw [← y7b_E_inf_F hb.hH] at h
        have hF : ⁅(n : G), b⁆ ∈ c.s.fr.F := (Subgroup.mem_inf.mp h).2
        change ⁅(n : G), b⁆ ∈ ⁅C3 c.s, normIn L c.s.fr.F⁆ ⊔ c.s.fr.F
        exact Subgroup.mem_sup_right hF
      have hnm : ⁅(n : G), m⁆ ∈ M3 c.s := by
        have hconj : (n : G) * m * (n : G)⁻¹ ∈ M3 c.s :=
          (Subgroup.mem_normalizer_iff.mp (y7b_B_le_NM3 c hb hnB) m).mp hm
        have heq : ⁅(n : G), m⁆ = ((n : G) * m * (n : G)⁻¹) * m⁻¹ := by
          rw [commutatorElement_def]
        rw [heq]
        exact (M3 c.s).mul_mem hconj ((M3 c.s).inv_mem hm)
      have hb_conj : b * ⁅(n : G), m⁆ * b⁻¹ ∈ M3 c.s :=
        (Subgroup.mem_normalizer_iff.mp (y7b_B_le_NM3 c hb hbB) _).mp hnm
      rw [show ⁅(n : G), b⁆ * b * ⁅(n : G), m⁆ * b⁻¹ =
          ⁅(n : G), b⁆ * (b * ⁅(n : G), m⁆ * b⁻¹) by group]
      exact (M3 c.s).mul_mem hnb hb_conj
  have hNX : normIn L c.s.fr.B ≤ y7bX c.s := by
    intro n hn
    refine y7b_N_le_X c hb ?_
    obtain ⟨hnL, hnNrm⟩ := Subgroup.mem_inf.mp hn
    exact Subgroup.mem_inf.mpr ⟨s3_L_le_H c.s hb.hH.hS hnL, hnNrm⟩
  have hKN : c.s.fr.B ≤ normIn L c.s.fr.B := fun b hbB =>
    Subgroup.mem_inf.mpr ⟨f3_B_le_L c.s hbB, (Subgroup.le_normalizer (H := c.s.fr.B)) hbB⟩
  have hsurj := y7b_perm3_surj_of_relIndex (X := y7bX c.s) (N := normIn L c.s.fr.B)
    (K := c.s.fr.B) hNX hKN ρ hker (y7b_relIndex_B_NLB hb.hH)
  refine ⟨ρ, ?_, ?_⟩
  · intro x
    rw [hρ x]
    constructor
    · intro hx
      rw [y7b_mem_X7 c hb]
      exact ⟨x.2, hx⟩
    · intro hx7
      rw [y7b_mem_X7 c hb] at hx7
      exact hx7.2
  · intro σ
    obtain ⟨n, -, hn⟩ := hsurj σ
    exact ⟨n, hn⟩

theorem y7b_relIndex_X7_X (c : Ctx7 G L) (hb : B5Std c) :
    (X7 c.s).relIndex (y7bX c.s) = 6 := by
  obtain ⟨ρ, hker, hsurj⟩ := y7b_exists_rhoB c hb
  exact y7b_relIndex_eq_six ρ hsurj hker

end CFSG.OddStandard.HigherRank.YamadaG23
