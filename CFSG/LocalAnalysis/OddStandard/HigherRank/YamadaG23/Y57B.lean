module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y57A
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54M3b

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y57_phi_inv {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {y : G}
    (hy : y ∈ f4Y c.s) : f3phi c.s y⁻¹ = (f3phi c.s y)⁻¹ := by
  have hmul := y54_phi_mul hH y hy y⁻¹ ((f4Y c.s).inv_mem hy)
  have h : f3phi c.s y * f3phi c.s y⁻¹ = 1 := by
    rw [← hmul, mul_inv_cancel]
    unfold f3phi
    group
  exact eq_inv_of_mul_eq_one_right h

private theorem y57_comm_eq_left {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsM3Cand c.s M) {m₁ m₁' x : G} (hm₁ : m₁ ∈ M) (hm₁' : m₁' ∈ M) (hx : x ∈ M)
    (hφ : f3phi c.s m₁ = f3phi c.s m₁') : ⁅m₁, x⁆ = ⁅m₁', x⁆ := by
  have hMY : M ≤ f4Y c.s := hM.2.1
  have hm₁Y : m₁ ∈ f4Y c.s := hMY hm₁
  have hm₁'Y : m₁' ∈ f4Y c.s := hMY hm₁'
  have hxY : x ∈ f4Y c.s := hMY hx
  have hmem : m₁⁻¹ * m₁' ∈ M := M.mul_mem (M.inv_mem hm₁) hm₁'
  have hphi : f3phi c.s (m₁⁻¹ * m₁') = 1 := by
    rw [y54_phi_mul hH m₁⁻¹ ((f4Y c.s).inv_mem hm₁Y) m₁' hm₁'Y, y57_phi_inv hH hm₁Y,
      hφ, inv_mul_cancel]
  have hF : m₁⁻¹ * m₁' ∈ c.s.fr.F := y54_M_inf_ker hH hM _ hmem hphi
  have hfx : ⁅m₁⁻¹ * m₁', x⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp hxY.2 _ hF
  rw [show m₁' = m₁ * (m₁⁻¹ * m₁') by group]
  rw [commutatorElement_mul_left_eq_conj_mul, hfx]
  group

private theorem y57_comm_eq_right {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsM3Cand c.s M) {x m₂ m₂' : G} (hx : x ∈ M) (hm₂ : m₂ ∈ M) (hm₂' : m₂' ∈ M)
    (hφ : f3phi c.s m₂ = f3phi c.s m₂') : ⁅x, m₂⁆ = ⁅x, m₂'⁆ := by
  have hMY : M ≤ f4Y c.s := hM.2.1
  have hm₂Y : m₂ ∈ f4Y c.s := hMY hm₂
  have hxY : x ∈ f4Y c.s := hMY hx
  have hmem : m₂⁻¹ * m₂' ∈ M := M.mul_mem (M.inv_mem hm₂) hm₂'
  have hphi : f3phi c.s (m₂⁻¹ * m₂') = 1 := by
    rw [y54_phi_mul hH m₂⁻¹ ((f4Y c.s).inv_mem hm₂Y) m₂' (hMY hm₂'), y57_phi_inv hH hm₂Y,
      hφ, inv_mul_cancel]
  have hF : m₂⁻¹ * m₂' ∈ c.s.fr.F := y54_M_inf_ker hH hM _ hmem hphi
  have hfx : ⁅x, m₂⁻¹ * m₂'⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp hxY.2 _ hF).symm
  rw [show m₂' = m₂ * (m₂⁻¹ * m₂') by group]
  rw [commutatorElement_mul_right_eq_mul_conj, hfx]
  group

private theorem y57_comm_depend {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsM3Cand c.s M) {m₁ m₂ m₁' m₂' : G} (hm₁ : m₁ ∈ M) (hm₂ : m₂ ∈ M)
    (hm₁' : m₁' ∈ M) (hm₂' : m₂' ∈ M)
    (h₁ : f3phi c.s m₁ = f3phi c.s m₁') (h₂ : f3phi c.s m₂ = f3phi c.s m₂') :
    ⁅m₁, m₂⁆ = ⁅m₁', m₂'⁆ :=
  (y57_comm_eq_left hH hM hm₁ hm₁' hm₂ h₁).trans
    (y57_comm_eq_right hH hM hm₁' hm₂ hm₂' h₂)

theorem y57_M3_comm (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ m ∈ M3 c.s, ∀ m' ∈ M3 c.s, m * m' = m' * m := by
  intro m hm m' hm'
  rw [← commutatorElement_eq_one_iff_mul_comm]
  have hM : IsM3Cand c.s (M3 c.s) := y54_M3_cand c hH
  have hMY : M3 c.s ≤ f4Y c.s := hM.2.1
  have hNinv := hM.2.2.1
  let lift : ↥(c.s.fr.F) → G := fun a => Classical.choose (y54_phi_M hH hM a.1 a.2)
  have lift_mem : ∀ a, lift a ∈ M3 c.s :=
    fun a => (Classical.choose_spec (y54_phi_M hH hM a.1 a.2)).1
  have lift_phi : ∀ a, f3phi c.s (lift a) = (a : G) :=
    fun a => (Classical.choose_spec (y54_phi_M hH hM a.1 a.2)).2
  let c0 : ↥(c.s.fr.F) → ↥(c.s.fr.F) → ↥(c.s.fr.F) := fun a b =>
    ⟨⁅lift a, lift b⁆,
      y54_Y_comm c hH (lift a) (hMY (lift_mem a)) (lift b) (hMY (lift_mem b))⟩
  have hl : ∀ a a' b, c0 (a * a') b = c0 a b * c0 a' b := by
    intro a a' b
    apply Subtype.ext
    change ⁅lift (a * a'), lift b⁆ = ⁅lift a, lift b⁆ * ⁅lift a', lift b⁆
    have hφ : f3phi c.s (lift (a * a')) = f3phi c.s (lift a * lift a') := by
      rw [lift_phi (a := a * a'),
        y54_phi_mul hH (lift a) (hMY (lift_mem a)) (lift a') (hMY (lift_mem a')),
        lift_phi (a := a), lift_phi (a := a')]
      rfl
    have hdep := y57_comm_depend hH hM (lift_mem (a * a')) (lift_mem b)
      ((M3 c.s).mul_mem (lift_mem a) (lift_mem a')) (lift_mem b) hφ rfl
    have hFb : ⁅lift a', lift b⁆ ∈ c.s.fr.F :=
      y54_Y_comm c hH (lift a') (hMY (lift_mem a')) (lift b) (hMY (lift_mem b))
    have hFa : ⁅lift a, lift b⁆ ∈ c.s.fr.F :=
      y54_Y_comm c hH (lift a) (hMY (lift_mem a)) (lift b) (hMY (lift_mem b))
    have hconj : lift a * ⁅lift a', lift b⁆ * (lift a)⁻¹ = ⁅lift a', lift b⁆ := by
      rw [(Subgroup.mem_centralizer_iff.mp (hMY (lift_mem a)).2 _ hFb).symm]
      group
    have hcomm : ⁅lift a', lift b⁆ * ⁅lift a, lift b⁆ = ⁅lift a, lift b⁆ * ⁅lift a', lift b⁆ :=
      y54_F_comm hH _ hFb _ hFa
    rw [hdep, commutatorElement_mul_left_eq_conj_mul, hconj, hcomm]
  have hr : ∀ a b b', c0 a (b * b') = c0 a b * c0 a b' := by
    intro a b b'
    apply Subtype.ext
    change ⁅lift a, lift (b * b')⁆ = ⁅lift a, lift b⁆ * ⁅lift a, lift b'⁆
    have hφ : f3phi c.s (lift (b * b')) = f3phi c.s (lift b * lift b') := by
      rw [lift_phi (a := b * b'),
        y54_phi_mul hH (lift b) (hMY (lift_mem b)) (lift b') (hMY (lift_mem b')),
        lift_phi (a := b), lift_phi (a := b')]
      rfl
    have hdep := y57_comm_depend hH hM (lift_mem a) (lift_mem (b * b'))
      (lift_mem a) ((M3 c.s).mul_mem (lift_mem b) (lift_mem b')) rfl hφ
    have hFa : ⁅lift a, lift b'⁆ ∈ c.s.fr.F :=
      y54_Y_comm c hH (lift a) (hMY (lift_mem a)) (lift b') (hMY (lift_mem b'))
    have hb : lift b * ⁅lift a, lift b'⁆ = ⁅lift a, lift b'⁆ * lift b :=
      (Subgroup.mem_centralizer_iff.mp (hMY (lift_mem b)).2 _ hFa).symm
    calc ⁅lift a, lift (b * b')⁆
        = ⁅lift a, lift b * lift b'⁆ := hdep
      _ = ⁅lift a, lift b⁆ * lift b * ⁅lift a, lift b'⁆ * (lift b)⁻¹ :=
            commutatorElement_mul_right_eq_mul_conj _ _ _
      _ = ⁅lift a, lift b⁆ * (lift b * ⁅lift a, lift b'⁆) * (lift b)⁻¹ := by group
      _ = ⁅lift a, lift b⁆ * (⁅lift a, lift b'⁆ * lift b) * (lift b)⁻¹ := by rw [hb]
      _ = ⁅lift a, lift b⁆ * ⁅lift a, lift b'⁆ := by group
  have halt : ∀ a, c0 a a = 1 := by
    intro a
    apply Subtype.ext
    change ⁅lift a, lift a⁆ = (1 : G)
    simp
  have hσ : ∀ (α : MulAut ↥(c.s.fr.F)) (a b : ↥(c.s.fr.F)),
      c0 (α a) (α b) = α (c0 a b) := by
    intro α a b
    obtain ⟨n, hnN, hnα⟩ := y54_aut_surj hH α
    have hnF : n ∈ f4N c.s := y54_NL_le_N hH hnN
    have hna : n * lift a * n⁻¹ ∈ M3 c.s := hNinv n hnN (lift a) (lift_mem a)
    have hnb : n * lift b * n⁻¹ ∈ M3 c.s := hNinv n hnN (lift b) (lift_mem b)
    have hφa : f3phi c.s (n * lift a * n⁻¹) = f3phi c.s (lift (α a)) := by
      rw [y54_phi_conj hH n hnF (lift a), lift_phi (a := a), lift_phi (a := α a), hnα a]
    have hφb : f3phi c.s (n * lift b * n⁻¹) = f3phi c.s (lift (α b)) := by
      rw [y54_phi_conj hH n hnF (lift b), lift_phi (a := b), lift_phi (a := α b), hnα b]
    have hdep := y57_comm_depend hH hM (lift_mem (α a)) (lift_mem (α b))
      hna hnb hφa.symm hφb.symm
    apply Subtype.ext
    change ⁅lift (α a), lift (α b)⁆ = (α (c0 a b) : G)
    rw [hnα (c0 a b)]
    change ⁅lift (α a), lift (α b)⁆ = n * ⁅lift a, lift b⁆ * n⁻¹
    rw [hdep]
    exact (conjugate_commutatorElement (g₁ := lift a) (g₂ := lift b) (g₃ := n)).symm
  have hzero := gl_alt_zero (F := ↥(c.s.fr.F)) (y54_F_isE3 hH) c0 hl hr halt hσ
  have hφm : f3phi c.s m ∈ c.s.fr.F := y54_phi_mem hH m (hMY hm)
  have hφm' : f3phi c.s m' ∈ c.s.fr.F := y54_phi_mem hH m' (hMY hm')
  have h1 : f3phi c.s m = f3phi c.s (lift ⟨f3phi c.s m, hφm⟩) := by rw [lift_phi]
  have h2 : f3phi c.s m' = f3phi c.s (lift ⟨f3phi c.s m', hφm'⟩) := by rw [lift_phi]
  have hdep := y57_comm_depend hH hM hm hm' (lift_mem _) (lift_mem _) h1 h2
  rw [hdep]
  have hczero := hzero ⟨f3phi c.s m, hφm⟩ ⟨f3phi c.s m', hφm'⟩
  change ((c0 ⟨f3phi c.s m, hφm⟩ ⟨f3phi c.s m', hφm'⟩ : ↥(c.s.fr.F)) : G) = 1
  simpa using congrArg (fun x : ↥(c.s.fr.F) => (x : G)) hczero

end CFSG.OddStandard.HigherRank.YamadaG23
