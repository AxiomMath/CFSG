module

public import CFSG.HardMathSupport.Solomon.Coordinator.U38Base
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10U38Tor
public import CFSG.HardMathSupport.Solomon.Coordinator.WeakModel
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Setup
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisCore
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossUniHeisPair
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.U38

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Solomon.Coordinator

variable {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)

local notation "ρ" => primeFormConjHom h (idGram K 3)

theorem u38_hne : ¬(3 = 3 ∧ 2 ^ 3 = 2) := by decide

theorem u38_eq_one_of_pow_nine {G : Type*} [Group G] {g : G} (h9 : g ^ 9 = 1)
    (hcop : Nat.Coprime 3 (orderOf g)) : g = 1 := by
  have hdvd : orderOf g ∣ 9 := orderOf_dvd_of_pow_eq_one h9
  have hcop9 : Nat.Coprime 9 (orderOf g) := by
    have := Nat.Coprime.pow_left 2 hcop
    simpa using this
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop9.symm hdvd)

include hω in
theorem torus_rho_uA (s : primeFormUnitary h (idGram K 3))
    (hs : ρ s * ρ (uA h hω) = ρ (uA h hω) * ρ s) (hcop : Nat.Coprime 3 (orderOf (ρ s))) :
    ρ s = 1 := by
  obtain ⟨l, hl⟩ := primeFormUnitary_exists_comm_scalar h le_rfl u38_hne hs
  have hlm : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * mA ω =
      (l : K) • (mA ω * ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hl
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at this
    rw [Matrix.smul_eq_diagonal_mul]
    exact this
  have hst : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (((s : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hu : ((((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).map h.bar)ᵀ *
      ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have := s.2
    rw [mem_primeFormUnitary] at this
    simpa [idGram] using this
  obtain ⟨c, hc⟩ := torus_A ω hω (u38_two_eq_zero h) h.bar (u38_bar_eq_pow h) hst hu hlm
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 : (((s ^ 9 : primeFormUnitary h (idGram K 3)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 0 := by
      rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hc, zero_smul]
    have h2 := ((s ^ 9 : primeFormUnitary h (idGram K 3)) : GL (Fin 3) K).isUnit
    rw [h1] at h2
    exact not_isUnit_zero h2
  have hscal : (((s ^ 9 : primeFormUnitary h (idGram K 3)) : GL (Fin 3) K)) =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) := by
    apply Units.ext
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hc, GeneralLinearGroup.coe_scalar,
      Matrix.smul_eq_diagonal_mul, Matrix.mul_one, Units.val_mk0]
    rfl
  have h9 : ρ s ^ 9 = 1 := by
    rw [← map_pow]
    exact primeFormConjHom_eq_one_of_scalar h le_rfl u38_hne hscal
  exact u38_eq_one_of_pow_nine h9 hcop

theorem u38_orderOf_conj {G : Type*} [Group G] (c r : G) : orderOf (c * r * c⁻¹) = orderOf r :=
  orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective r

theorem u38_comm_of_comm_pow {G : Type*} [Group G] {x r : G} (hx : x ^ 3 = 1) {k : ℕ}
    (hk : k = 1 ∨ k = 2) (hr : r * x ^ k = x ^ k * r) : r * x = x * r := by
  rcases hk with rfl | rfl
  · simpa using hr
  · have e : x = (x ^ 2) ^ 2 := by
      rw [← pow_mul, show (2 * 2 : ℕ) = 3 + 1 by norm_num, pow_succ, hx, one_mul]
    rw [e]
    exact (Commute.pow_right hr 2).eq

include hω in
theorem rho_uF_conj :
    ρ (uF h hω) * ρ (uP h hω) * (ρ (uF h hω))⁻¹ = ρ (uA h hω) := by
  have e : uF h hω * uP h hω = uA h hω * uF h hω := by
    apply Subtype.ext
    apply Units.ext
    exact mF_mP ω hω (u38_two_eq_zero h)
  rw [← map_mul, e, map_mul, mul_inv_cancel_right]

include hω in
theorem rho_uQ_conj :
    ρ (uQ h hω) * ρ (uP h hω) * (ρ (uQ h hω))⁻¹ = ρ (uA h hω) * ρ (uP h hω) := by
  have e : uQ h hω * uP h hω = uA h hω * uP h hω * uQ h hω := by
    apply Subtype.ext
    apply Units.ext
    change mQ ω * mP = mA ω * mP * mQ ω
    rw [mA_mP_eq_conj_Q ω hω (u38_two_eq_zero h), Matrix.mul_assoc, Matrix.mul_assoc,
      mQi_mQ ω hω (u38_two_eq_zero h), Matrix.mul_one]
  rw [← map_mul, e, map_mul, map_mul, mul_inv_cancel_right]

include hω in
theorem rho_uR_conj :
    ρ (uR h hω) * ρ (uP h hω) ^ 2 * (ρ (uR h hω))⁻¹ = ρ (uA h hω) * ρ (uP h hω) ^ 2 := by
  have e : uR h hω * uP h hω ^ 2 = uA h hω * uP h hω ^ 2 * uR h hω := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val,
      coe_uR, coe_uP, coe_uA, sq]
    rw [mA_mP_sq_eq_conj_R ω hω (u38_two_eq_zero h), Matrix.mul_assoc (mR ω * (mP * mP)),
      mRi_mR ω hω (u38_two_eq_zero h), Matrix.mul_one]
  rw [← map_pow, ← map_mul, e, map_mul, map_mul, map_pow, mul_inv_cancel_right]

theorem rho_uA_pow_three : ρ (uA h hω) ^ 3 = 1 := by
  have h3 := u38_omega_pow_three hω
  have h6 : ω ^ 6 = 1 := by rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, h3, one_pow]
  have hd : mA ω = Matrix.diagonal ![1, ω, ω ^ 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mA]
  have e : (uA h hω) ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    change mA ω ^ 3 = 1
    rw [hd, Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [← pow_mul, h3, h6]
  rw [← map_pow, e, map_one]

theorem rho_uP_pow_three : ρ (uP h hω) ^ 3 = 1 := by
  have e : (uP h hω) ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    change mP ^ 3 = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mP, pow_three, Matrix.mul_apply, Fin.sum_univ_three]
  rw [← map_pow, e, map_one]

theorem rho_uA_comm_uP : ρ (uA h hω) * ρ (uP h hω) = ρ (uP h hω) * ρ (uA h hω) := by
  have h1 : ((uA h hω * uP h hω * (uP h hω * uA h hω)⁻¹ : primeFormUnitary h (idGram K 3)) :
      GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) (uω hω) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_mul, uA_mul_uP h hω,
      ← GeneralLinearGroup.scalar_commute (uω hω), mul_assoc, mul_inv_cancel, mul_one]
  have h2 := primeFormConjHom_eq_one_of_scalar h le_rfl u38_hne h1
  rw [map_mul, map_inv, mul_inv_eq_one, map_mul, map_mul] at h2
  exact h2

theorem mem_plane_iff {b : MulAut (primeFormP h (idGram K 3))}
    (hb : b ∈ Subgroup.closure {ρ (uA h hω), ρ (uP h hω)}) :
    ∃ i j : ℕ, i < 3 ∧ j < 3 ∧ b = ρ (uA h hω) ^ i * ρ (uP h hω) ^ j := by
  set a := ρ (uA h hω)
  set p := ρ (uP h hω)
  have ha3 : a ^ 3 = 1 := rho_uA_pow_three h hω
  have hp3 : p ^ 3 = 1 := rho_uP_pow_three h hω
  have hap : Commute a p := rho_uA_comm_uP h hω
  have hmod : ∀ (x : MulAut (primeFormP h (idGram K 3))), x ^ 3 = 1 → ∀ n : ℕ,
      x ^ n = x ^ (n % 3) := by
    intro x hx n
    conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hx, one_pow, one_mul]
  suffices ∃ i j : ℕ, b = a ^ i * p ^ j by
    obtain ⟨i, j, rfl⟩ := this
    exact ⟨i % 3, j % 3, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), by
      rw [← hmod a ha3, ← hmod p hp3]⟩
  induction hb using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨1, 0, by simp⟩
    · rw [Set.mem_singleton_iff] at hx
      exact ⟨0, 1, by simp [hx]⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, j, rfl⟩ := hx
    obtain ⟨k, l, rfl⟩ := hy
    refine ⟨i + k, j + l, ?_⟩
    rw [pow_add, pow_add]
    have : p ^ j * a ^ k = a ^ k * p ^ j := ((hap.pow_left k).pow_right j).eq.symm
    calc a ^ i * p ^ j * (a ^ k * p ^ l) = a ^ i * (p ^ j * a ^ k) * p ^ l := by group
      _ = a ^ i * (a ^ k * p ^ j) * p ^ l := by rw [this]
      _ = a ^ i * a ^ k * (p ^ j * p ^ l) := by group
  | inv x _ hx =>
    obtain ⟨i, j, rfl⟩ := hx
    refine ⟨2 * i, 2 * j, ?_⟩
    have hai : (a ^ i)⁻¹ = a ^ (2 * i) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, ha3,
        one_pow]
    have hpj : (p ^ j)⁻¹ = p ^ (2 * j) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, show j + 2 * j = 3 * j by ring, pow_mul, hp3,
        one_pow]
    rw [_root_.mul_inv_rev, hai, hpj]
    exact ((hap.pow_left (2 * i)).pow_right (2 * j)).eq.symm

include hω in
theorem torus_lineP (t : primeFormUnitary h (idGram K 3))
    (ht : ρ t * ρ (uP h hω) = ρ (uP h hω) * ρ t) (hc : Nat.Coprime 3 (orderOf (ρ t))) :
    ρ t = 1 := by
  have h1 : ρ (uF h hω * t * (uF h hω)⁻¹) * ρ (uA h hω) =
      ρ (uA h hω) * ρ (uF h hω * t * (uF h hω)⁻¹) := by
    rw [← rho_uF_conj h hω, map_mul, map_mul, map_inv]
    calc ρ (uF h hω) * ρ t * (ρ (uF h hω))⁻¹ * (ρ (uF h hω) * ρ (uP h hω) * (ρ (uF h hω))⁻¹)
        = ρ (uF h hω) * (ρ t * ρ (uP h hω)) * (ρ (uF h hω))⁻¹ := by group
      _ = ρ (uF h hω) * (ρ (uP h hω) * ρ t) * (ρ (uF h hω))⁻¹ := by rw [ht]
      _ = ρ (uF h hω) * ρ (uP h hω) * (ρ (uF h hω))⁻¹ *
          (ρ (uF h hω) * ρ t * (ρ (uF h hω))⁻¹) := by group
  have h2 : Nat.Coprime 3 (orderOf (ρ (uF h hω * t * (uF h hω)⁻¹))) := by
    rw [map_mul, map_mul, map_inv, u38_orderOf_conj]
    exact hc
  have h3 := torus_rho_uA h hω _ h1 h2
  rw [map_mul, map_mul, map_inv] at h3
  have : ρ t = (ρ (uF h hω))⁻¹ * (ρ (uF h hω) * ρ t * (ρ (uF h hω))⁻¹) * ρ (uF h hω) := by group
  rw [this, h3]
  group

include hω in
theorem torus_lineAP (t : primeFormUnitary h (idGram K 3))
    (ht : ρ t * (ρ (uA h hω) * ρ (uP h hω)) = ρ (uA h hω) * ρ (uP h hω) * ρ t)
    (hc : Nat.Coprime 3 (orderOf (ρ t))) : ρ t = 1 := by
  have e := rho_uQ_conj h hω
  have h1 : ρ ((uQ h hω)⁻¹ * t * uQ h hω) * ρ (uP h hω) =
      ρ (uP h hω) * ρ ((uQ h hω)⁻¹ * t * uQ h hω) := by
    rw [map_mul, map_mul, map_inv]
    have e' : ρ (uP h hω) =
        (ρ (uQ h hω))⁻¹ * (ρ (uA h hω) * ρ (uP h hω)) * ρ (uQ h hω) := by rw [← e]; group
    rw [e']
    calc (ρ (uQ h hω))⁻¹ * ρ t * ρ (uQ h hω) *
          ((ρ (uQ h hω))⁻¹ * (ρ (uA h hω) * ρ (uP h hω)) * ρ (uQ h hω))
        = (ρ (uQ h hω))⁻¹ * (ρ t * (ρ (uA h hω) * ρ (uP h hω))) * ρ (uQ h hω) := by group
      _ = (ρ (uQ h hω))⁻¹ * (ρ (uA h hω) * ρ (uP h hω) * ρ t) * ρ (uQ h hω) := by rw [ht]
      _ = (ρ (uQ h hω))⁻¹ * (ρ (uA h hω) * ρ (uP h hω)) * ρ (uQ h hω) *
          ((ρ (uQ h hω))⁻¹ * ρ t * ρ (uQ h hω)) := by group
  have h2 : Nat.Coprime 3 (orderOf (ρ ((uQ h hω)⁻¹ * t * uQ h hω))) := by
    rw [map_mul, map_mul, map_inv]
    have := u38_orderOf_conj (ρ (uQ h hω))⁻¹ (ρ t)
    rw [inv_inv] at this
    rw [this]
    exact hc
  have h3 := torus_lineP h hω _ h1 h2
  rw [map_mul, map_mul, map_inv] at h3
  have : ρ t = ρ (uQ h hω) * ((ρ (uQ h hω))⁻¹ * ρ t * ρ (uQ h hω)) * (ρ (uQ h hω))⁻¹ := by group
  rw [this, h3]
  group

include hω in
theorem torus_lineAP2 (t : primeFormUnitary h (idGram K 3))
    (ht : ρ t * (ρ (uA h hω) * ρ (uP h hω) ^ 2) = ρ (uA h hω) * ρ (uP h hω) ^ 2 * ρ t)
    (hc : Nat.Coprime 3 (orderOf (ρ t))) : ρ t = 1 := by
  have e := rho_uR_conj h hω
  have h1 : ρ ((uR h hω)⁻¹ * t * uR h hω) * ρ (uP h hω) =
      ρ (uP h hω) * ρ ((uR h hω)⁻¹ * t * uR h hω) := by
    refine u38_comm_of_comm_pow (rho_uP_pow_three h hω) (Or.inr rfl) ?_
    rw [map_mul, map_mul, map_inv]
    have e' : ρ (uP h hω) ^ 2 =
        (ρ (uR h hω))⁻¹ * (ρ (uA h hω) * ρ (uP h hω) ^ 2) * ρ (uR h hω) := by rw [← e]; group
    rw [e']
    calc (ρ (uR h hω))⁻¹ * ρ t * ρ (uR h hω) *
          ((ρ (uR h hω))⁻¹ * (ρ (uA h hω) * ρ (uP h hω) ^ 2) * ρ (uR h hω))
        = (ρ (uR h hω))⁻¹ * (ρ t * (ρ (uA h hω) * ρ (uP h hω) ^ 2)) * ρ (uR h hω) := by group
      _ = (ρ (uR h hω))⁻¹ * (ρ (uA h hω) * ρ (uP h hω) ^ 2 * ρ t) * ρ (uR h hω) := by rw [ht]
      _ = (ρ (uR h hω))⁻¹ * (ρ (uA h hω) * ρ (uP h hω) ^ 2) * ρ (uR h hω) *
          ((ρ (uR h hω))⁻¹ * ρ t * ρ (uR h hω)) := by group
  have h2 : Nat.Coprime 3 (orderOf (ρ ((uR h hω)⁻¹ * t * uR h hω))) := by
    rw [map_mul, map_mul, map_inv]
    have := u38_orderOf_conj (ρ (uR h hω))⁻¹ (ρ t)
    rw [inv_inv] at this
    rw [this]
    exact hc
  have h3 := torus_lineP h hω _ h1 h2
  rw [map_mul, map_mul, map_inv] at h3
  have : ρ t = ρ (uR h hω) * ((ρ (uR h hω))⁻¹ * ρ t * ρ (uR h hω)) * (ρ (uR h hω))⁻¹ := by group
  rw [this, h3]
  group

include hω in
theorem torus_plane {b : MulAut (primeFormP h (idGram K 3))}
    (hb : b ∈ Subgroup.closure {ρ (uA h hω), ρ (uP h hω)}) (hb1 : b ≠ 1)
    (s : primeFormUnitary h (idGram K 3)) (hs : ρ s * b = b * ρ s)
    (hcop : Nat.Coprime 3 (orderOf (ρ s))) : ρ s = 1 := by
  have ha3 := rho_uA_pow_three h hω
  have hp3 := rho_uP_pow_three h hω
  have hap : Commute (ρ (uA h hω)) (ρ (uP h hω)) := rho_uA_comm_uP h hω
  obtain ⟨i, j, hi, hj, rfl⟩ := mem_plane_iff h hω hb
  interval_cases i <;> interval_cases j <;>
    (try simp only [pow_zero, pow_one, one_mul, mul_one] at hs hb1)
  · exact absurd rfl hb1
  · exact torus_lineP h hω s hs hcop
  · exact torus_lineP h hω s (u38_comm_of_comm_pow hp3 (Or.inr rfl) hs) hcop
  · exact torus_rho_uA h hω s hs hcop
  · exact torus_lineAP h hω s hs hcop
  · exact torus_lineAP2 h hω s hs hcop
  · exact torus_rho_uA h hω s (u38_comm_of_comm_pow ha3 (Or.inr rfl) hs) hcop
  ·
    have hx3 : (ρ (uA h hω) * ρ (uP h hω) ^ 2) ^ 3 = 1 := by
      rw [(hap.pow_right 2).mul_pow, ha3, ← pow_mul, show (2 * 3 : ℕ) = 3 * 2 by norm_num,
        pow_mul, hp3, one_pow, one_mul]
    have e : ρ (uA h hω) ^ 2 * ρ (uP h hω) = (ρ (uA h hω) * ρ (uP h hω) ^ 2) ^ 2 := by
      rw [(hap.pow_right 2).mul_pow, ← pow_mul, show (2 * 2 : ℕ) = 1 + 3 by norm_num, pow_add,
        hp3, mul_one, pow_one]
    rw [e] at hs
    exact torus_lineAP2 h hω s (u38_comm_of_comm_pow hx3 (Or.inr rfl) hs) hcop
  ·
    have hx3 : (ρ (uA h hω) * ρ (uP h hω)) ^ 3 = 1 := by rw [hap.mul_pow, ha3, hp3, one_mul]
    have e : ρ (uA h hω) ^ 2 * ρ (uP h hω) ^ 2 = (ρ (uA h hω) * ρ (uP h hω)) ^ 2 := by
      rw [hap.mul_pow]
    rw [e] at hs
    exact torus_lineAP h hω s (u38_comm_of_comm_pow hx3 (Or.inr rfl) hs) hcop

end CFSG.HardMathSupport.Solomon.Coordinator.U38
