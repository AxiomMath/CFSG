module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56Coord
public import CFSG.LocalAnalysis.EvenBN.Tits.S56J
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Coprime
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Frat

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped commutatorElement

namespace S56

theorem comm_mul_central {G : Type*} [Group G] {c c' k k' : G} (hkc : k * c = c * k)
    (hkc' : k * c' = c' * k) (hkk' : k * k' = k' * k) (hk'c : k' * c = c * k')
    (hk'c' : k' * c' = c' * k') : ⁅c * k, c' * k'⁆ = ⁅c, c'⁆ := by
  have h4 : Commute k' c := hk'c
  simp only [commutatorElement_def, mul_inv_rev]
  calc c * k * (c' * k') * (k⁻¹ * c⁻¹) * (k'⁻¹ * c'⁻¹)
      = c * (k * c') * k' * k⁻¹ * c⁻¹ * k'⁻¹ * c'⁻¹ := by group
    _ = c * (c' * k) * k' * k⁻¹ * c⁻¹ * k'⁻¹ * c'⁻¹ := by rw [hkc']
    _ = c * c' * (k * k' * k⁻¹) * c⁻¹ * k'⁻¹ * c'⁻¹ := by group
    _ = c * c' * k' * c⁻¹ * k'⁻¹ * c'⁻¹ := by rw [hkk']; group
    _ = c * c' * (k' * c⁻¹ * k'⁻¹) * c'⁻¹ := by group
    _ = c * c' * c⁻¹ * c'⁻¹ := by
      rw [show k' * c⁻¹ * k'⁻¹ = c⁻¹ by
        have := h4.inv_right
        rw [this.eq]; group]

end S56

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


@[expose] noncomputable def s56Q (d : Data G) : Subgroup G := ⁅d.s56Q0, zpowers d.x₅⁆

theorem s56_Q0_isPGroup (d : Data G) : IsPGroup 2 d.s56Q0 := by
  unfold s56Q0
  exact (CFSG.pCore_isPGroup).map _

theorem s56_M_le_normalizer_Q0 (d : Data G) : d.M ≤ normalizer (d.s56Q0 : Set G) := by
  have key : ∀ m ∈ d.M, ∀ q ∈ d.s56Q0, m * q * m⁻¹ ∈ d.s56Q0 := by
    intro m hm q hq
    obtain ⟨q', hq', rfl⟩ := hq
    refine ⟨⟨m, hm⟩ * q' * ⟨m, hm⟩⁻¹, ?_, rfl⟩
    exact (CFSG.pCore_normal (p := 2) (G := ↥d.M)).conj_mem q' hq' ⟨m, hm⟩
  intro m hm
  rw [mem_normalizer_iff]
  intro q
  refine ⟨fun hq => key m hm q hq, fun hq => ?_⟩
  have := key m⁻¹ (inv_mem hm) _ hq
  simpa [mul_assoc] using this

theorem Hyp.s56_X_isPGroup (hd : d.Hyp) : IsPGroup 5 (zpowers d.x₅) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd.s56_orderOf_x5]; simp)

theorem Hyp.s56_X_le_M (hd : d.Hyp) : zpowers d.x₅ ≤ d.M := zpowers_le.2 hd.s56_x5_mem_M

theorem Hyp.s56_X_le_normalizer_Q0 (hd : d.Hyp) :
    zpowers d.x₅ ≤ normalizer (d.s56Q0 : Set G) :=
  hd.s56_X_le_M.trans (s56_M_le_normalizer_Q0 d)

theorem Hyp.s56_Q_le_Q0 (hd : d.Hyp) : d.s56Q ≤ d.s56Q0 :=
  S56.commutator_zpowers_le (hd.s56_X_le_normalizer_Q0 (mem_zpowers _))

theorem Hyp.s56_M_le_normalizer_Q (h49 : d.Thm49Statement) (hd : d.Hyp) :
    d.M ≤ normalizer (d.s56Q : Set G) := by
  obtain ⟨-, -, -, -, -, h20, -⟩ := hd.s56_structure_M h49
  exact S56.normalizer_commutator_of_index_twenty (hd.s56_Q0_le_M h49)
    (s56_M_le_normalizer_Q0 d) (s56_Q0_isPGroup d) hd.s56_x5_mem_M hd.s56_orderOf_x5 h20

theorem Hyp.s56_Q0_decomp (hd : d.Hyp) {q : G} (hq : q ∈ d.s56Q0) :
    ∃ c ∈ d.s56Q, ∃ k ∈ d.s56Q0 ⊓ centralizer ((zpowers d.x₅ : Subgroup G) : Set G), q = c * k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact S56.coprime_decomp_mem (p := 2) (r := 5) (by norm_num) (s56_Q0_isPGroup d)
    hd.s56_X_isPGroup hd.s56_X_le_normalizer_Q0 hq

theorem Hyp.s56_Q_comm_X (hd : d.Hyp) : ⁅d.s56Q, zpowers d.x₅⁆ = d.s56Q := by
  refine le_antisymm (Subgroup.commutator_mono hd.s56_Q_le_Q0 le_rfl) ?_
  show ⁅d.s56Q0, zpowers d.x₅⁆ ≤ ⁅d.s56Q, zpowers d.x₅⁆
  refine Subgroup.commutator_le.2 fun q₀ hq₀ x' hx' => ?_
  obtain ⟨c, hc, k, hk, rfl⟩ := hd.s56_Q0_decomp hq₀
  have hkx : x' * k = k * x' := mem_centralizer_iff.1 (mem_inf.1 hk).2 x' hx'
  have e : ⁅c * k, x'⁆ = ⁅c, x'⁆ := by
    simp only [commutatorElement_def]
    calc c * k * x' * (c * k)⁻¹ * x'⁻¹ = c * (k * x' * k⁻¹) * c⁻¹ * x'⁻¹ := by group
      _ = c * x' * c⁻¹ * x'⁻¹ := by
        rw [show k * x' * k⁻¹ = x' by rw [← hkx]; group]
  rw [e]
  exact Subgroup.commutator_mem_commutator hc hx'

theorem Hyp.s56_J_eq_comm (hd : d.Hyp) : ⁅d.s56J, zpowers d.x₅⁆ = d.s56J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hJX : zpowers d.x₅ ≤ normalizer (d.s56J : Set G) := zpowers_le.2 hd.s56_x5_normalizes_J
  have hdec : ∀ j ∈ d.s56J, ∃ c ∈ ⁅d.s56J, zpowers d.x₅⁆,
      ∃ k ∈ d.s56J ⊓ centralizer ((zpowers d.x₅ : Subgroup G) : Set G), j = c * k :=
    fun j hj => S56.coprime_decomp_mem (p := 2) (r := 5) (by norm_num) hd.s56_J_isPGroup
      hd.s56_X_isPGroup hJX hj
  have hk : ∀ k ∈ d.s56J ⊓ centralizer ((zpowers d.x₅ : Subgroup G) : Set G),
      k ∈ zpowers d.z := fun k hk =>
    hd.s56_J_cent_x5 (mem_inf.1 hk).1
      (mem_centralizer_iff.1 (mem_inf.1 hk).2 d.x₅ (mem_zpowers _)).symm
  have hKJ : ⁅d.s56J, zpowers d.x₅⁆ ≤ d.s56J := S56.commutator_zpowers_le hd.s56_x5_normalizes_J
  set K := ⁅d.s56J, zpowers d.x₅⁆ with hKdef
  have hJM : d.s56J ≤ d.M := hd.s56_J_le_M
  have hzK : d.z ∈ K := by
    obtain ⟨a, ha, b, hb, hab⟩ := hd.s56_exists_comm_eq_z
    obtain ⟨c, hc, k, hkk, rfl⟩ := hdec a ha
    obtain ⟨c', hc', k', hkk', rfl⟩ := hdec b hb
    have hkz := hk k hkk
    have hkz' := hk k' hkk'
    have hcM : c ∈ d.M := hJM (hKJ hc)
    have hc'M : c' ∈ d.M := hJM (hKJ hc')
    have e : ⁅c * k, c' * k'⁆ = ⁅c, c'⁆ :=
      S56.comm_mul_central (hd.s56_M_comm_zpowers hcM hkz).symm
        (hd.s56_M_comm_zpowers hc'M hkz).symm (hd.s56_zpowers_comm hkz hkz')
        (hd.s56_M_comm_zpowers hcM hkz').symm (hd.s56_M_comm_zpowers hc'M hkz').symm
    have h2 : ⁅c, c'⁆ ∈ K := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hc hc') (inv_mem hc)) (inv_mem hc')
    rw [← hab]
    have h3 : c * k * (c' * k') * (c * k)⁻¹ * (c' * k')⁻¹ = ⁅c * k, c' * k'⁆ := by
      rw [commutatorElement_def]
    rw [h3, e]
    exact h2
  refine le_antisymm hKJ fun j hj => ?_
  obtain ⟨c, hc, k, hkk, rfl⟩ := hdec j hj
  have hkz := hk k hkk
  exact mul_mem hc ((zpowers_le.2 hzK) hkz)

theorem Hyp.s56_J_le_Q (h49 : d.Thm49Statement) (hd : d.Hyp) : d.s56J ≤ d.s56Q :=
  calc d.s56J = ⁅d.s56J, zpowers d.x₅⁆ := hd.s56_J_eq_comm.symm
    _ ≤ ⁅d.s56Q0, zpowers d.x₅⁆ := Subgroup.commutator_mono (hd.s56_J_le_Q0 h49) le_rfl

theorem Hyp.s56_E_le_Q (h49 : d.Thm49Statement) (hd : d.Hyp) : d.E ≤ d.s56Q :=
  (s56_E_le_J d).trans (hd.s56_J_le_Q h49)

theorem Hyp.s56_F_le_Q (h49 : d.Thm49Statement) (hd : d.Hyp) : d.F ≤ d.s56Q :=
  (s56_F_le_J d).trans (hd.s56_J_le_Q h49)

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
