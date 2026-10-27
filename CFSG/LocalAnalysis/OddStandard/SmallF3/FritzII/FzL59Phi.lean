module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59Dict


public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
  CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G]

private def fz59phiE (i : Fin 3) : Fz59Mod := fz59Gen i 0 * fz59Gen i 0

private def fz59phiKer (q q' : Fz59Mod) : Prop := q' = q ∨ q' = q * fz59Zeta

private instance fz59phiKer.decidable (q q' : Fz59Mod) : Decidable (fz59phiKer q q') :=
  inferInstanceAs (Decidable (q' = q ∨ q' = q * fz59Zeta))

private theorem fz59phi_sq_cases : ∀ q : Fz59Mod, q * q = 1 →
    fz59phiKer 1 q ∨ fz59phiKer (fz59phiE 0) q ∨ fz59phiKer (fz59phiE 1) q ∨
      fz59phiKer (fz59phiE 2) q := by
  decide +kernel

private theorem fz59phi_ker_one : ∀ q : Fz59Mod, fz59phiKer 1 q → q * q = 1 := by
  decide +kernel

private theorem fz59phi_ker_E :
    ∀ (i : Fin 3) (q : Fz59Mod), fz59phiKer (fz59phiE i) q → q * q = 1 := by
  decide +kernel

private theorem fz59phi_cell_sq :
    ∀ c : Fz59Cell, fz59CellElt fz59Gen c * fz59CellElt fz59Gen c ≠ 1 := by
  decide +kernel

private theorem fz59phi_cell_inj_mod : ∀ c c' : Fz59Cell,
    (fz59CellElt fz59Gen c')⁻¹ * fz59CellElt fz59Gen c *
      ((fz59CellElt fz59Gen c')⁻¹ * fz59CellElt fz59Gen c) = 1 → c = c' := by
  decide +kernel

private theorem fz59phi_cell_comm_mod : ∀ (c : Fz59Cell) (p : Fz59Mod),
    fz59CellElt fz59Gen c * p * (fz59CellElt fz59Gen c)⁻¹ * p⁻¹ = 1 ∨
      fz59CellElt fz59Gen c * p * (fz59CellElt fz59Gen c)⁻¹ * p⁻¹ = fz59phiE c.1 := by
  decide +kernel

private theorem fz59phi_cell_comm_ex : ∀ c : Fz59Cell, ∃ p : Fz59Mod,
    fz59CellElt fz59Gen c * p * (fz59CellElt fz59Gen c)⁻¹ * p⁻¹ = fz59phiE c.1 := by
  decide +kernel

private theorem fz59phi_rowvec_mod : ∀ (q : Fz59Mod) (j : Fin 3), q * q ≠ 1 →
    (∀ (i : Fin 3) (k : Fin 2), fz59phiKer 1 (q * fz59Gen i k * q⁻¹ * (fz59Gen i k)⁻¹) ∨
      fz59phiKer (fz59phiE j) (q * fz59Gen i k * q⁻¹ * (fz59Gen i k)⁻¹)) →
    ∃ c : Fz59Cell, (fz59CellElt fz59Gen c)⁻¹ * q * ((fz59CellElt fz59Gen c)⁻¹ * q) = 1 := by
  decide +kernel

private theorem fz59phi_prod_inj_mod : ∀ a b c a' b' c' : Fin 3,
    (fz59Prod fz59Gen ![a', b', c'])⁻¹ * fz59Prod fz59Gen ![a, b, c] *
      ((fz59Prod fz59Gen ![a', b', c'])⁻¹ * fz59Prod fz59Gen ![a, b, c]) = 1 →
    a = a' ∧ b = b' ∧ c = c' := by
  decide +kernel

private theorem fz59phi_mem_R (b : Fin 3 → Fin 2 → G) (i : Fin 3) (k : Fin 2) :
    b i k ∈ fz59R b :=
  Subgroup.subset_closure ⟨(i, k), rfl⟩

private theorem fz59phi_cell_mem (b : Fin 3 → Fin 2 → G) (c : Fz59Cell) :
    fz59CellElt b c ∈ fz59R b := by
  obtain ⟨i, k⟩ := c
  fin_cases k
  · exact fz59phi_mem_R b i 0
  · exact fz59phi_mem_R b i 1
  · exact (fz59R b).mul_mem (fz59phi_mem_R b i 0) (fz59phi_mem_R b i 1)

private theorem fz59phi_zz_mem {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) (i : Fin 3) :
    b i 0 ^ 2 ∈ fz59Z b := by
  rw [fz59_mem_Z hb]
  fin_cases i <;> simp

private theorem fz59phi_zz_inj {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) {i j : Fin 3}
    (h : b i 0 ^ 2 = b j 0 ^ 2) : i = j := by
  have ha : ∀ i, b i 0 ^ 2 * b i 0 ^ 2 = 1 := fun i => (hb.quat i).sq_mul_sq
  have hn : ∀ i, b i 0 ^ 2 ≠ 1 := fun i => (hb.quat i).2.2.2
  have hs : b 2 0 ^ 2 = b 0 0 ^ 2 * b 1 0 ^ 2 := hb.sq_eq
  have h01 : b 0 0 ^ 2 ≠ b 1 0 ^ 2 := fun h => hn 2 (by rw [hs, ← h]; exact ha 0)
  have h02 : b 0 0 ^ 2 ≠ b 2 0 ^ 2 := fun h =>
    hn 1 (mul_left_cancel (a := b 0 0 ^ 2) (by rw [mul_one]; rw [hs] at h; exact h.symm))
  have h12 : b 1 0 ^ 2 ≠ b 2 0 ^ 2 := fun h =>
    hn 0 (mul_right_cancel (b := b 1 0 ^ 2) (by rw [one_mul]; rw [hs] at h; exact h.symm))
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | exact absurd h h01
    | exact absurd h h01.symm
    | exact absurd h h02
    | exact absurd h h02.symm
    | exact absurd h h12
    | exact absurd h h12.symm

private theorem fz59phi_sq_eq_comm {p q : G} (h : IsQ8Pair p q) :
    p ^ 2 = p * q * p⁻¹ * q⁻¹ := by
  have h1 : q * p * q⁻¹ = p⁻¹ := h.2.2.1
  calc p ^ 2 = p * p := sq p
    _ = p * (q * p * q⁻¹)⁻¹ := by rw [h1, inv_inv]
    _ = p * q * p⁻¹ * q⁻¹ := by group

private theorem fz59phi_conj_Z {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) {n : G}
    (hn : n ∈ normalizer ((fz59R b : Subgroup G) : Set G)) {z : G} (hz : z ∈ fz59Z b) :
    n * z * n⁻¹ ∈ fz59Z b := by
  have hn' : ∀ h : G, h ∈ fz59R b → n * h * n⁻¹ ∈ fz59R b := fun h hh =>
    (Subgroup.mem_set_normalizer_iff.mp hn h).mp hh
  have key : ∀ i : Fin 3, n * b i 0 ^ 2 * n⁻¹ ∈ fz59Z b := by
    intro i
    rw [fz59phi_sq_eq_comm (hb.quat i)]
    have e : n * (b i 0 * b i 1 * (b i 0)⁻¹ * (b i 1)⁻¹) * n⁻¹ =
        (n * b i 0 * n⁻¹) * (n * b i 1 * n⁻¹) * (n * b i 0 * n⁻¹)⁻¹ * (n * b i 1 * n⁻¹)⁻¹ := by
      group
    rw [e]
    exact fz59_comm_mem_Z hb _ (hn' _ (fz59phi_mem_R b i 0)) _ (hn' _ (fz59phi_mem_R b i 1))
  rcases (fz59_mem_Z hb z).mp hz with rfl | rfl | rfl | rfl
  · simpa using (fz59Z b).one_mem
  · exact key 0
  · exact key 1
  · exact key 2

private theorem fz59phi_conj_Z_inv {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) {n : G}
    (hn : n ∈ normalizer ((fz59R b : Subgroup G) : Set G)) {z : G} (hz : z ∈ fz59Z b) :
    n⁻¹ * z * n ∈ fz59Z b := by
  simpa using fz59phi_conj_Z hb (inv_mem hn) hz

private def Fz59HasVal (b : Fin 3 → Fin 2 → G) (y w : G) : Prop :=
  ∀ r ∈ fz59R b, y * r * y⁻¹ * r⁻¹ = 1 ∨ y * r * y⁻¹ * r⁻¹ = w

private def Fz59RowVec (b : Fin 3 → Fin 2 → G) (y : G) : Prop :=
  y ∈ fz59R b ∧ y ∉ fz59Z b ∧ ∃ w ∈ fz59Z b, w ≠ 1 ∧ Fz59HasVal b y w

private theorem fz59phi_hasVal_mul {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) {y w z : G}
    (h : Fz59HasVal b y w) (hz : z ∈ fz59Z b) : Fz59HasVal b (y * z) w := by
  intro r hr
  have hc : z * r = r * z := fz59_Z_central hb z hz r hr
  have e : y * z * r * (y * z)⁻¹ * r⁻¹ = y * r * y⁻¹ * r⁻¹ := by
    calc y * z * r * (y * z)⁻¹ * r⁻¹ = y * (z * r) * z⁻¹ * y⁻¹ * r⁻¹ := by group
      _ = y * (r * z) * z⁻¹ * y⁻¹ * r⁻¹ := by rw [hc]
      _ = y * r * y⁻¹ * r⁻¹ := by group
  rw [e]
  exact h r hr

private theorem fz59phi_hasVal_of_mul {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) {y w z : G}
    (h : Fz59HasVal b (y * z) w) (hz : z ∈ fz59Z b) : Fz59HasVal b y w := by
  have := fz59phi_hasVal_mul hb h ((fz59Z b).inv_mem hz)
  rwa [mul_inv_cancel_right] at this

private theorem fz59phi_hasVal_conj {b : Fin 3 → Fin 2 → G} {n : G}
    (hn : n ∈ normalizer ((fz59R b : Subgroup G) : Set G)) {y w : G} (h : Fz59HasVal b y w) :
    Fz59HasVal b (n * y * n⁻¹) (n * w * n⁻¹) := by
  intro r hr
  have hr' : n⁻¹ * r * n ∈ fz59R b := (Subgroup.mem_set_normalizer_iff''.mp hn r).mp hr
  have e : n * y * n⁻¹ * r * (n * y * n⁻¹)⁻¹ * r⁻¹ =
      n * (y * (n⁻¹ * r * n) * y⁻¹ * (n⁻¹ * r * n)⁻¹) * n⁻¹ := by
    group
  rw [e]
  rcases h _ hr' with h1 | h1
  · left
    rw [h1]
    group
  · right
    rw [h1]

private theorem fz59phi_rowVec_conj {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) {n : G}
    (hn : n ∈ normalizer ((fz59R b : Subgroup G) : Set G)) {y : G} (hy : Fz59RowVec b y) :
    Fz59RowVec b (n * y * n⁻¹) := by
  obtain ⟨hyR, hyZ, w, hwZ, hw1, hval⟩ := hy
  refine ⟨(Subgroup.mem_set_normalizer_iff.mp hn y).mp hyR, ?_, n * w * n⁻¹,
    fz59phi_conj_Z hb hn hwZ, ?_, fz59phi_hasVal_conj hn hval⟩
  · intro h
    apply hyZ
    have := fz59phi_conj_Z_inv hb hn h
    have e : n⁻¹ * (n * y * n⁻¹) * n = y := by group
    rwa [e] at this
  · intro h
    apply hw1
    calc w = n⁻¹ * (n * w * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group

private theorem fz59phi_facts {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) :
    ∃ π : Fz59Mod →* G, (∀ i k, π (fz59Gen i k) = b i k) ∧
      (∀ c, π (fz59CellElt fz59Gen c) = fz59CellElt b c) ∧
      (∀ i, π (fz59phiE i) = b i 0 ^ 2) ∧ (∀ q, π q ∈ fz59R b) ∧
      (∀ r ∈ fz59R b, ∃ q, π q = r) ∧ (∀ q q', π q = π q' ↔ fz59phiKer q q') ∧
      (∀ q, π q ∈ fz59Z b ↔ q * q = 1) := by
  obtain ⟨π, hgen, hrange, hker⟩ := fz59_dict hb
  have hKer : ∀ q q', π q = π q' ↔ fz59phiKer q q' := hker
  have hE : ∀ i, π (fz59phiE i) = b i 0 ^ 2 := by
    intro i
    rw [fz59phiE, map_mul, hgen, sq]
  refine ⟨π, hgen, ?_, hE, ?_, ?_, hKer, ?_⟩
  · rintro ⟨i, k⟩
    fin_cases k <;> simp [fz59CellElt, hgen]
  · intro q
    rw [← hrange]
    exact MonoidHom.mem_range.mpr ⟨q, rfl⟩
  · intro r hr
    rw [← hrange] at hr
    exact hr
  · intro q
    rw [fz59_mem_Z hb]
    constructor
    · rintro (h | h | h | h)
      · exact fz59phi_ker_one q ((hKer 1 q).mp (by rw [map_one]; exact h.symm))
      · exact fz59phi_ker_E 0 q ((hKer _ q).mp (by rw [hE]; exact h.symm))
      · exact fz59phi_ker_E 1 q ((hKer _ q).mp (by rw [hE]; exact h.symm))
      · exact fz59phi_ker_E 2 q ((hKer _ q).mp (by rw [hE]; exact h.symm))
    · intro h
      rcases fz59phi_sq_cases q h with h | h | h | h
      · left
        rw [← (hKer 1 q).mpr h, map_one]
      · right; left
        rw [← hE 0, ← (hKer _ q).mpr h]
      · right; right; left
        rw [← hE 1, ← (hKer _ q).mpr h]
      · right; right; right
        rw [← hE 2, ← (hKer _ q).mpr h]

private theorem fz59phi_cell {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) (c : Fz59Cell) :
    fz59CellElt b c ∉ fz59Z b ∧ Fz59HasVal b (fz59CellElt b c) (b c.1 0 ^ 2) ∧
      ∃ r ∈ fz59R b, fz59CellElt b c * r * (fz59CellElt b c)⁻¹ * r⁻¹ = b c.1 0 ^ 2 := by
  obtain ⟨π, hgen, hcell, hE, hπR, hRπ, hKer, hZ⟩ := fz59phi_facts hb
  have hcomm : ∀ p q : Fz59Mod, π (p * q * p⁻¹ * q⁻¹) = π p * π q * (π p)⁻¹ * (π q)⁻¹ := by
    intro p q
    simp only [map_mul, map_inv]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hcell, hZ]
    exact fz59phi_cell_sq c
  · intro r hr
    obtain ⟨p, rfl⟩ := hRπ r hr
    rw [← hcell, ← hcomm]
    rcases fz59phi_cell_comm_mod c p with h | h
    · left
      rw [h, map_one]
    · right
      rw [h, hE]
  · obtain ⟨p, hp⟩ := fz59phi_cell_comm_ex c
    refine ⟨π p, hπR p, ?_⟩
    rw [← hcell, ← hcomm, hp, hE]

private theorem fz59phi_rowVec_cell {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) (c : Fz59Cell)
    {z : G} (hz : z ∈ fz59Z b) : Fz59RowVec b (fz59CellElt b c * z) := by
  obtain ⟨hnZ, hval, -⟩ := fz59phi_cell hb c
  refine ⟨(fz59R b).mul_mem (fz59phi_cell_mem b c) (fz59_Z_le_R b hz), ?_, b c.1 0 ^ 2,
    fz59phi_zz_mem hb c.1, (hb.quat c.1).2.2.2, fz59phi_hasVal_mul hb hval hz⟩
  intro h
  apply hnZ
  have := (fz59Z b).mul_mem h ((fz59Z b).inv_mem hz)
  rwa [mul_inv_cancel_right] at this

private theorem fz59phi_rowVec {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) {y : G}
    (hy : Fz59RowVec b y) : ∃ (c : Fz59Cell) (z : G), z ∈ fz59Z b ∧ y = fz59CellElt b c * z := by
  obtain ⟨π, hgen, hcell, hE, hπR, hRπ, hKer, hZ⟩ := fz59phi_facts hb
  have hcomm : ∀ p q : Fz59Mod, π (p * q * p⁻¹ * q⁻¹) = π p * π q * (π p)⁻¹ * (π q)⁻¹ := by
    intro p q
    simp only [map_mul, map_inv]
  obtain ⟨hyR, hyZ, w, hwZ, hw1, hval⟩ := hy
  obtain ⟨q, rfl⟩ := hRπ y hyR
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, w = b j 0 ^ 2 := by
    rcases (fz59_mem_Z hb w).mp hwZ with h | h | h | h
    · exact absurd h hw1
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  have hq : q * q ≠ 1 := fun h => hyZ ((hZ q).mpr h)
  obtain ⟨c, hc⟩ := fz59phi_rowvec_mod q j hq (fun i k => by
    have h := hval (b i k) (fz59phi_mem_R b i k)
    rw [← hgen i k, ← hcomm] at h
    rcases h with h | h
    · left
      exact (hKer 1 _).mp (by rw [map_one]; exact h.symm)
    · right
      exact (hKer _ _).mp (by rw [hE, ← hj]; exact h.symm))
  refine ⟨c, (fz59CellElt b c)⁻¹ * π q, ?_, by group⟩
  rw [← hcell c, ← map_inv, ← map_mul]
  exact (hZ _).mpr hc

private theorem fz59phi_cell_inj {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) {c c' : Fz59Cell}
    {z z' : G} (hz : z ∈ fz59Z b) (hz' : z' ∈ fz59Z b)
    (h : fz59CellElt b c * z = fz59CellElt b c' * z') : c = c' := by
  obtain ⟨π, hgen, hcell, hE, hπR, hRπ, hKer, hZ⟩ := fz59phi_facts hb
  refine fz59phi_cell_inj_mod c c' ((hZ _).mp ?_)
  rw [map_mul, map_inv, hcell, hcell]
  have e : (fz59CellElt b c')⁻¹ * fz59CellElt b c = z' * z⁻¹ := by
    calc (fz59CellElt b c')⁻¹ * fz59CellElt b c
        = (fz59CellElt b c')⁻¹ * (fz59CellElt b c * z) * z⁻¹ := by group
      _ = (fz59CellElt b c')⁻¹ * (fz59CellElt b c' * z') * z⁻¹ := by rw [h]
      _ = z' * z⁻¹ := by group
  rw [e]
  exact (fz59Z b).mul_mem hz' ((fz59Z b).inv_mem hz)

private theorem fz59phi_act_exists {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b)
    (n : normalizer ((fz59R b : Subgroup G) : Set G)) (c : Fz59Cell) :
    ∃ c' : Fz59Cell, ∃ z ∈ fz59Z b,
      (n : G) * fz59CellElt b c * (n : G)⁻¹ = fz59CellElt b c' * z := by
  have h0 := fz59phi_rowVec_cell hb c (fz59Z b).one_mem
  rw [mul_one] at h0
  obtain ⟨c', z, hz, h⟩ := fz59phi_rowVec hb (fz59phi_rowVec_conj hb n.2 h0)
  exact ⟨c', z, hz, h⟩

private theorem fz59phi_rowval {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) {n : G}
    (hn : n ∈ normalizer ((fz59R b : Subgroup G) : Set G)) {c d : Fz59Cell} {z : G}
    (hz : z ∈ fz59Z b) (h : n * fz59CellElt b c * n⁻¹ = fz59CellElt b d * z) :
    b d.1 0 ^ 2 = n * b c.1 0 ^ 2 * n⁻¹ := by
  obtain ⟨-, hval, -⟩ := fz59phi_cell hb c
  obtain ⟨-, -, r, hr, hrv⟩ := fz59phi_cell hb d
  have h1 := fz59phi_hasVal_conj hn hval
  rw [h] at h1
  have h2 := fz59phi_hasVal_of_mul hb h1 hz
  rcases h2 r hr with h3 | h3
  · exact absurd (hrv.symm.trans h3) (hb.quat d.1).2.2.2
  · exact hrv.symm.trans h3

theorem fz59_phi {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) :
    ∃ Φ : normalizer ((fz59R b : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell,
      Fz59CellAction b Φ := by
  choose f z hz hf using fz59phi_act_exists hb
  have hfinv : ∀ n c, f n⁻¹ (f n c) = c := by
    intro n c
    have h1 := hf n c
    have h2 := hf n⁻¹ (f n c)
    simp only [Subgroup.coe_inv, inv_inv] at h2
    refine (fz59phi_cell_inj hb (fz59Z b).one_mem
      ((fz59Z b).mul_mem (hz n⁻¹ (f n c)) (fz59phi_conj_Z_inv hb n.2 (hz n c))) ?_).symm
    calc fz59CellElt b c * 1
        = (n : G)⁻¹ * ((n : G) * fz59CellElt b c * (n : G)⁻¹) * (n : G) := by group
      _ = (n : G)⁻¹ * (fz59CellElt b (f n c) * z n c) * (n : G) := by rw [h1]
      _ = ((n : G)⁻¹ * fz59CellElt b (f n c) * (n : G)) * ((n : G)⁻¹ * z n c * (n : G)) := by
          group
      _ = fz59CellElt b (f n⁻¹ (f n c)) * z n⁻¹ (f n c) * ((n : G)⁻¹ * z n c * (n : G)) := by
          rw [h2]
      _ = fz59CellElt b (f n⁻¹ (f n c)) *
          (z n⁻¹ (f n c) * ((n : G)⁻¹ * z n c * (n : G))) := by rw [mul_assoc]
  have hf1 : ∀ c, f 1 c = c := by
    intro c
    have h := hf 1 c
    simp only [Subgroup.coe_one, inv_one, one_mul, mul_one] at h
    exact (fz59phi_cell_inj hb (fz59Z b).one_mem (hz 1 c) (by rw [mul_one]; exact h)).symm
  have hfmul : ∀ n m c, f (n * m) c = f n (f m c) := by
    intro n m c
    have e : fz59CellElt b (f (n * m) c) * z (n * m) c =
        fz59CellElt b (f n (f m c)) *
          (z n (f m c) * ((n : G) * z m c * (n : G)⁻¹)) := by
      calc fz59CellElt b (f (n * m) c) * z (n * m) c
          = ((n * m : normalizer ((fz59R b : Subgroup G) : Set G)) : G) * fz59CellElt b c *
            ((n * m : normalizer ((fz59R b : Subgroup G) : Set G)) : G)⁻¹ := (hf (n * m) c).symm
        _ = (n : G) * ((m : G) * fz59CellElt b c * (m : G)⁻¹) * (n : G)⁻¹ := by
            simp only [Subgroup.coe_mul]
            group
        _ = (n : G) * (fz59CellElt b (f m c) * z m c) * (n : G)⁻¹ := by rw [hf m c]
        _ = ((n : G) * fz59CellElt b (f m c) * (n : G)⁻¹) * ((n : G) * z m c * (n : G)⁻¹) := by
            group
        _ = fz59CellElt b (f n (f m c)) * z n (f m c) * ((n : G) * z m c * (n : G)⁻¹) := by
            rw [hf n (f m c)]
        _ = fz59CellElt b (f n (f m c)) *
            (z n (f m c) * ((n : G) * z m c * (n : G)⁻¹)) := by rw [mul_assoc]
    exact fz59phi_cell_inj hb (hz (n * m) c)
      ((fz59Z b).mul_mem (hz n (f m c)) (fz59phi_conj_Z hb n.2 (hz m c))) e
  let Φ₀ : normalizer ((fz59R b : Subgroup G) : Set G) → Equiv.Perm Fz59Cell := fun n =>
    { toFun := f n
      invFun := f n⁻¹
      left_inv := hfinv n
      right_inv := fun c => by simpa using hfinv n⁻¹ c }
  refine ⟨{ toFun := Φ₀, map_one' := Equiv.ext hf1, map_mul' := fun n m => Equiv.ext (hfmul n m) },
    ?_⟩
  refine ⟨fun n c => ⟨z n c, hz n c, hf n c⟩, fun n i k k' => ?_⟩
  exact fz59phi_zz_inj hb ((fz59phi_rowval hb n.2 (hz n (i, k)) (hf n (i, k))).trans
    (fz59phi_rowval hb n.2 (hz n (i, k')) (hf n (i, k'))).symm)

theorem fz59_phi_unique {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b)
    {Φ : normalizer ((fz59R b : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell}
    (hΦ : Fz59CellAction b Φ) (n : normalizer ((fz59R b : Subgroup G) : Set G))
    (σ : Equiv.Perm Fz59Cell)
    (h : ∀ c : Fz59Cell, ∃ z ∈ fz59Z b,
      (n : G) * fz59CellElt b c * (n : G)⁻¹ = fz59CellElt b (σ c) * z) : Φ n = σ := by
  refine Equiv.ext fun c => ?_
  obtain ⟨z₁, hz₁, e₁⟩ := hΦ.1 n c
  obtain ⟨z₂, hz₂, e₂⟩ := h c
  exact fz59phi_cell_inj hb hz₁ hz₂ (e₁.symm.trans e₂)

theorem fz59_phi_one_of_mem {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b)
    {Φ : normalizer ((fz59R b : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell}
    (hΦ : Fz59CellAction b Φ) (n : normalizer ((fz59R b : Subgroup G) : Set G))
    (hn : (n : G) ∈ fz59R b) : Φ n = 1 := by
  refine fz59_phi_unique hb hΦ n 1 fun c => ?_
  have hx := fz59phi_cell_mem b c
  have hc := fz59_comm_mem_Z hb (n : G) hn (fz59CellElt b c) hx
  refine ⟨_, hc, ?_⟩
  have hcen := fz59_Z_central hb _ hc _ hx
  calc (n : G) * fz59CellElt b c * (n : G)⁻¹
      = ((n : G) * fz59CellElt b c * (n : G)⁻¹ * (fz59CellElt b c)⁻¹) * fz59CellElt b c := by
        group
    _ = fz59CellElt b c * ((n : G) * fz59CellElt b c * (n : G)⁻¹ * (fz59CellElt b c)⁻¹) := hcen

private theorem fz59phi_perm_mul {f : Fin 3 → G} (hc : ∀ i j, i ≠ j → f i * f j = f j * f i)
    (e : Equiv.Perm (Fin 3)) : f (e 0) * f (e 1) * f (e 2) = f 0 * f 1 * f 2 := by
  have h01 : e 0 ≠ e 1 := fun h => absurd (e.injective h) (by decide)
  have h02 : e 0 ≠ e 2 := fun h => absurd (e.injective h) (by decide)
  have h12 : e 1 ≠ e 2 := fun h => absurd (e.injective h) (by decide)
  have key : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c →
      (a = 0 ∧ b = 1 ∧ c = 2) ∨ (a = 0 ∧ b = 2 ∧ c = 1) ∨ (a = 1 ∧ b = 0 ∧ c = 2) ∨
      (a = 1 ∧ b = 2 ∧ c = 0) ∨ (a = 2 ∧ b = 0 ∧ c = 1) ∨ (a = 2 ∧ b = 1 ∧ c = 0) := by
    decide
  rcases key _ _ _ h01 h02 h12 with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
    ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> rw [h0, h1, h2]
  · rw [mul_assoc, hc 2 1 (by decide), ← mul_assoc]
  · rw [hc 1 0 (by decide)]
  · rw [mul_assoc, hc 2 0 (by decide), ← mul_assoc, hc 1 0 (by decide)]
  · rw [hc 2 0 (by decide), mul_assoc, hc 2 1 (by decide), ← mul_assoc]
  · rw [hc 2 1 (by decide), mul_assoc, hc 2 0 (by decide), ← mul_assoc, hc 1 0 (by decide)]

private theorem fz59phi_mul3 {a b c z₀ z₁ z₂ : G} (h₀₁ : z₀ * b = b * z₀) (h₀₂ : z₀ * c = c * z₀)
    (h₁₂ : z₁ * c = c * z₁) : a * z₀ * (b * z₁) * (c * z₂) = a * b * c * (z₀ * z₁ * z₂) := by
  calc a * z₀ * (b * z₁) * (c * z₂) = a * (z₀ * b) * (z₁ * c) * z₂ := by group
    _ = a * (b * z₀) * (c * z₁) * z₂ := by rw [h₀₁, h₁₂]
    _ = a * b * (z₀ * c) * z₁ * z₂ := by group
    _ = a * b * (c * z₀) * z₁ * z₂ := by rw [h₀₂]
    _ = a * b * c * (z₀ * z₁ * z₂) := by group

private theorem fz59phi_cell_commute {b : Fin 3 → Fin 2 → G} {c : Fz59Cell} {g : G}
    (h : ∀ k, Commute (b c.1 k) g) : Commute (fz59CellElt b c) g := by
  obtain ⟨i, k⟩ := c
  fin_cases k
  · exact h 0
  · exact h 1
  · exact (h 0).mul_left (h 1)

private theorem fz59phi_cell_commute' {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b)
    {c c' : Fz59Cell} (h : c.1 ≠ c'.1) : fz59CellElt b c * fz59CellElt b c' =
      fz59CellElt b c' * fz59CellElt b c :=
  (fz59phi_cell_commute fun k => (fz59phi_cell_commute fun l =>
    (hb.comm c.1 c'.1 h k l).symm).symm).eq

theorem fz59_phi_prod {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b)
    {Φ : normalizer ((fz59R b : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell}
    (hΦ : Fz59CellAction b Φ) (n : normalizer ((fz59R b : Subgroup G) : Set G))
    (ω : Fin 3 → Fin 3) :
    ∃ (ω' : Fin 3 → Fin 3) (z : G), z ∈ fz59Z b ∧
      (n : G) * fz59Prod b ω * (n : G)⁻¹ = fz59Prod b ω' * z ∧
      (fz59Tr ω).image (Φ n) = fz59Tr ω' := by
  obtain ⟨hΦ1, hΦ2⟩ := hΦ
  have hψ : ∀ i k, (Φ n (i, k)).1 = (Φ n (i, 0)).1 := fun i k => hΦ2 n i k 0
  have hψs : Function.Surjective fun i => (Φ n (i, 0)).1 := by
    intro j
    refine ⟨((Φ n).symm (j, 0)).1, ?_⟩
    have h := hψ ((Φ n).symm (j, 0)).1 ((Φ n).symm (j, 0)).2
    rw [Prod.mk.eta, Equiv.apply_symm_apply] at h
    exact h.symm
  let e : Fin 3 ≃ Fin 3 := Equiv.ofBijective (fun i => (Φ n (i, 0)).1)
    ⟨Finite.injective_iff_surjective.mpr hψs, hψs⟩
  have he : ∀ i k, (Φ n (i, k)).1 = e i := fun i k => hψ i k
  choose zz hzz hzz' using fun i : Fin 3 => hΦ1 n (i, ω i)
  let ω' : Fin 3 → Fin 3 := fun j => (Φ n (e.symm j, ω (e.symm j))).2
  have hstar : ∀ i, Φ n (i, ω i) = (e i, ω' (e i)) := by
    intro i
    refine Prod.ext (he i (ω i)) ?_
    show (Φ n (i, ω i)).2 = (Φ n (e.symm (e i), ω (e.symm (e i)))).2
    rw [e.symm_apply_apply]
  let f : Fin 3 → G := fun j => fz59CellElt b (j, ω' j)
  have hxd : ∀ i, fz59CellElt b (Φ n (i, ω i)) = f (e i) := fun i => by rw [hstar i]
  have hcen : ∀ (i j : Fin 3), zz i * f j = f j * zz i := fun i j =>
    fz59_Z_central hb _ (hzz i) _ (fz59phi_cell_mem b _)
  have hconj : (n : G) * fz59Prod b ω * (n : G)⁻¹ =
      f (e 0) * f (e 1) * f (e 2) * (zz 0 * zz 1 * zz 2) := by
    have e1 : (n : G) * fz59Prod b ω * (n : G)⁻¹ =
        ((n : G) * fz59CellElt b (0, ω 0) * (n : G)⁻¹) *
          ((n : G) * fz59CellElt b (1, ω 1) * (n : G)⁻¹) *
          ((n : G) * fz59CellElt b (2, ω 2) * (n : G)⁻¹) := by
      unfold fz59Prod
      group
    rw [e1, hzz' 0, hzz' 1, hzz' 2, hxd 0, hxd 1, hxd 2]
    exact fz59phi_mul3 (hcen 0 _) (hcen 0 _) (hcen 1 _)
  have hperm : f (e 0) * f (e 1) * f (e 2) = fz59Prod b ω' :=
    (fz59phi_perm_mul (fun i j hij => fz59phi_cell_commute' hb (c := (i, ω' i)) (c' := (j, ω' j))
      hij) e).trans rfl
  refine ⟨ω', zz 0 * zz 1 * zz 2,
    (fz59Z b).mul_mem ((fz59Z b).mul_mem (hzz 0) (hzz 1)) (hzz 2), hconj.trans (by rw [hperm]), ?_⟩
  ext x
  simp only [fz59Tr, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨e i, (hstar i).symm⟩
  · rintro ⟨j, rfl⟩
    refine ⟨(e.symm j, ω (e.symm j)), ⟨e.symm j, rfl⟩, ?_⟩
    rw [hstar, Equiv.apply_symm_apply]

theorem fz59_prod_inj {b : Fin 3 → Fin 2 → G} (hb : Fz59Rows b) {ω ω' : Fin 3 → Fin 3}
    {z z' : G} (hz : z ∈ fz59Z b) (hz' : z' ∈ fz59Z b)
    (h : fz59Prod b ω * z = fz59Prod b ω' * z') : ω = ω' := by
  obtain ⟨π, hgen, hcell, hE, hπR, hRπ, hKer, hZ⟩ := fz59phi_facts hb
  have hP : ∀ ω : Fin 3 → Fin 3, π (fz59Prod fz59Gen ω) = fz59Prod b ω := by
    intro ω
    simp only [fz59Prod, map_mul, hcell]
  have hω : ∀ ω : Fin 3 → Fin 3, ω = ![ω 0, ω 1, ω 2] := by
    intro ω
    funext i
    fin_cases i <;> rfl
  have hmem : π ((fz59Prod fz59Gen ω')⁻¹ * fz59Prod fz59Gen ω) ∈ fz59Z b := by
    rw [map_mul, map_inv, hP, hP]
    have e : (fz59Prod b ω')⁻¹ * fz59Prod b ω = z' * z⁻¹ := by
      calc (fz59Prod b ω')⁻¹ * fz59Prod b ω
          = (fz59Prod b ω')⁻¹ * (fz59Prod b ω * z) * z⁻¹ := by group
        _ = (fz59Prod b ω')⁻¹ * (fz59Prod b ω' * z') * z⁻¹ := by rw [h]
        _ = z' * z⁻¹ := by group
    rw [e]
    exact (fz59Z b).mul_mem hz' ((fz59Z b).inv_mem hz)
  have hsq := (hZ _).mp hmem
  have := fz59phi_prod_inj_mod (ω 0) (ω 1) (ω 2) (ω' 0) (ω' 1) (ω' 2)
    (by rw [← hω ω, ← hω ω']; exact hsq)
  funext i
  fin_cases i
  · exact this.1
  · exact this.2.1
  · exact this.2.2

end CFSG.OddStandard.SmallF3.FritzII
