module

public import CFSG.HardMathSupport.Foote.E27.LieTwo.OrthChecks
public import CFSG.HardMathSupport.Foote.E27.LieTwo.Kill
public import CFSG.Timmesfeld.Orders.Classical
public import Certificates.Certificate131004
public import Certificates.Certificate131005
public import Certificates.Certificate131006
public import Certificates.Certificate131007
public import CFSG.HardMathSupport.Foote.E27.LieTwo.MatChecks

public section

namespace CFSG.HardMathSupport.Foote.E27

open Matrix Subgroup CFSG.Assembly.LowTwoRank

theorem conj_mem_commutator {G : Type*} [Group G] (N : Subgroup G) {g : G} (hg : g ∈ N) {x : G}
    (hx : x ∈ ⁅N, N⁆) : g * x * g⁻¹ ∈ ⁅N, N⁆ := by
  rw [Subgroup.commutator_def] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨g * a * g⁻¹, N.mul_mem (N.mul_mem hg ha) (N.inv_mem hg), g * b * g⁻¹,
      N.mul_mem (N.mul_mem hg hb) (N.inv_mem hg), ?_⟩
    simp only [commutatorElement_def]
    group
  | one => simp
  | mul x y _ _ hx hy =>
    have := Subgroup.mul_mem _ hx hy
    convert this using 1
    group
  | inv x _ hx =>
    have := Subgroup.inv_mem _ hx
    convert this using 1
    group

section Orth

variable {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2)

theorem statedOmega_normal (g : ↥(OrthN Q)) {x : ↥(OrthN Q)}
    (hx : x ∈ (StatedOmega Q).subgroupOf (OrthN Q)) :
    g * x * g⁻¹ ∈ (StatedOmega Q).subgroupOf (OrthN Q) := by
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact conj_mem_commutator (OrthN Q) g.2 hx

noncomputable def fixN {H : Subgroup (GL ι (ZMod 2))} (x : H) : ℕ :=
  Nat.card {v : ι → ZMod 2 // ((x : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ v = v}

theorem fixN_conj {H : Subgroup (GL ι (ZMod 2))} (g x : H) : fixN (g * x * g⁻¹) = fixN x := by
  unfold fixN
  have hm : ∀ a b : H, (((a * b : H) : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) =
      ((a : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) * ((b : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) :=
    fun a b => by rw [Subgroup.coe_mul, Units.val_mul]
  have h1 : ∀ v : ι → ZMod 2, ((g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ
      ((((g⁻¹ : H) : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, ← hm, mul_inv_cancel, Subgroup.coe_one, Units.val_one, one_mulVec]
  have h2 : ∀ v : ι → ZMod 2, (((g⁻¹ : H) : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ
      (((g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, ← hm, inv_mul_cancel, Subgroup.coe_one, Units.val_one, one_mulVec]
  refine Nat.card_congr (Equiv.subtypeEquiv ⟨fun v => (((g⁻¹ : H) : GL ι (ZMod 2)) :
    Matrix ι ι (ZMod 2)) *ᵥ v, fun v => ((g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ v, h1, h2⟩
    fun v => ?_)
  dsimp only [Equiv.coe_fn_mk]
  rw [hm, hm]
  simp only [← mulVec_mulVec]
  constructor
  · intro h
    have := congrArg ((((g⁻¹ : H) : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ ·) h
    simpa only [h2] using this
  · intro h
    rw [h, h1]

end Orth

theorem false_of_omega_cover {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}
    (h : E27Config X K R T z) (hz : z ∈ K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : (ι → ZMod 2) → ZMod 2) (e : ↥K ≃* ↥(StatedOmega Q)) {n k : ℕ}
    (hcard : Nat.card ↥(StatedOmega Q) = 3 ^ k * n) (hn : ¬ 3 ∣ n)
    (S₀ B₀ : Subgroup ↥(OrthN Q)) (hS : Nat.card S₀ = 3 ^ k)
    (hB : 81 ∣ Nat.card B₀)
    (hSJ : S₀ ≤ (StatedOmega Q).subgroupOf (OrthN Q))
    (hBJ : B₀ ≤ (StatedOmega Q).subgroupOf (OrthN Q))
    (hBab : ∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x)
    (hcov : ∀ s ∈ S₀, s ^ 3 = 1 → s ≠ 1 → ∃ x : ↥(OrthN Q), x * s * x⁻¹ ∈ B₀) : False := by
  haveI : Finite ↥(OrthN Q) := inferInstance
  let J := (StatedOmega Q).subgroupOf (OrthN Q)
  let φ : ↥K ≃* ↥J := e.trans (Subgroup.subgroupOfEquivOfLe (statedOmega_le_OrthN Q)).symm
  have hcardJ : Nat.card ↥J = 3 ^ k * n := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (statedOmega_le_OrthN Q)).toEquiv
  have hfac : (Nat.card ↥J).factorization 3 = k := factorization_three_of_eq hcardJ hn
  exact h.false_of_torus_cover_amb hz J (fun g x hx => statedOmega_normal Q g hx) φ S₀ B₀ hSJ hBJ
    (by rw [hS, hfac]) hBab hB hcov

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

section O8m


theorem E27Config.false_of_omegaMinus_four (h : E27Config X K R T z)
    (hcl : StatedClassicalModel (↥K) .POmegaMinus 4 2 1) : False := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaMinus hcl
  obtain ⟨S, hS, hC, hno⟩ := Certificates.certificate131004
  have hcard : Nat.card ↥(StatedOmega (StatedQuadMinus 4 (ZMod 2) 1 1)) = 3 ^ 4 * 2437120 := by
    rw [← Nat.card_congr e.toEquiv, (CFSG.Timmesfeld.card_statedClassicalModel_two hcl).2.2.2.2 rfl]
    decide
  have hfac := factorization_three_of_eq hcard (by norm_num)
  exact h.false_of_central_T e S (by rw [hS, hfac]; norm_num) fixN (fun g x => fixN_conj g x)
    {n | n = 4} hC hno

end O8m

section O10m


theorem E27Config.false_of_omegaMinus_five (h : E27Config X K R T z) (hz : z ∈ K)
    (hcl : StatedClassicalModel (↥K) .POmegaMinus 5 2 1) : False := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaMinus hcl
  haveI : Finite ↥(StatedOmega (StatedQuadMinus 5 (ZMod 2) 1 1)) := Finite.of_equiv ↥K e.toEquiv
  obtain ⟨S, hS, hprop⟩ := Certificates.certificate131005
  have hcard : Nat.card ↥(StatedOmega (StatedQuadMinus 5 (ZMod 2) 1 1)) =
      3 ^ 6 * 34314649600 := by
    rw [← Nat.card_congr e.toEquiv, (CFSG.Timmesfeld.card_statedClassicalModel_two hcl).2.2.2.2 rfl]
    decide
  have hfac := factorization_three_of_eq hcard (by norm_num)
  exact h.false_of_sylow_table hz e S (by rw [hS, hfac]; norm_num) hprop

end O10m

section O8p


theorem E27Config.false_of_omegaPlus_four (h : E27Config X K R T z) (hz : z ∈ K)
    (hcl : StatedClassicalModel (↥K) .POmegaPlus 4 2 1) : False := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaPlus hcl
  obtain ⟨S₀, B₀, hS, hB, hSJ, hBJ, hBab, hcov⟩ := Certificates.certificate131006
  have hcard : Nat.card ↥(StatedOmega (StatedQuadPlus 4 (ZMod 2))) = 3 ^ 5 * 716800 := by
    rw [← Nat.card_congr e.toEquiv, (CFSG.Timmesfeld.card_statedClassicalModel_two hcl).2.2.2.1 rfl]
    decide
  exact false_of_omega_cover h hz (StatedQuadPlus 4 (ZMod 2)) e hcard (by norm_num) S₀ B₀
    (by rw [hS]; norm_num) (by rw [hB]) hSJ hBJ hBab hcov

end O8p

section O10p


theorem E27Config.false_of_omegaPlus_five (h : E27Config X K R T z) (hz : z ∈ K)
    (hcl : StatedClassicalModel (↥K) .POmegaPlus 5 2 1) : False := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaPlus hcl
  obtain ⟨S₀, B₀, hS, hB, hSJ, hBJ, hBab, hcov⟩ := Certificates.certificate131007
  have hcard : Nat.card ↥(StatedOmega (StatedQuadPlus 5 (ZMod 2))) = 3 ^ 5 * 96704921600 := by
    rw [← Nat.card_congr e.toEquiv, (CFSG.Timmesfeld.card_statedClassicalModel_two hcl).2.2.2.1 rfl]
    decide
  exact false_of_omega_cover h hz (StatedQuadPlus 5 (ZMod 2)) e hcard (by norm_num) S₀ B₀
    (by rw [hS]; norm_num) (by rw [hB]) hSJ hBJ hBab hcov

end O10p

end CFSG.HardMathSupport.Foote.E27
