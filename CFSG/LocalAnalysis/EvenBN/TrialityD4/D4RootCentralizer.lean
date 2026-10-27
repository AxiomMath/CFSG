module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalVPrelim
import CFSG.LocalAnalysis.EvenBN.Common.SL2Module
import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2
import CFSG.CGT.Timmesfeld75.L2Real

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup
open scoped commutatorElement

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem mem_normalizer_V_of_conj_mem_V {w : X} (hw : w ∈ d.weyl) {z : X} (hz : z ∈ d.V)
    (hz1 : z ≠ 1) (h : w * z * w⁻¹ ∈ d.V) : w ∈ normalizer (d.V : Set X) := by
  have := d.finite
  obtain ⟨c, rfl⟩ := hz
  have hc : c ≠ 0 := fun h0 => hz1 (by rw [h0, d.x₆_zero])
  refine mem_normalizer_fintype fun y hy => ?_
  obtain ⟨c', rfl⟩ := hy
  by_cases hc' : c' = 0
  · rw [hc', d.x₆_zero, mul_one, mul_inv_cancel]
    exact d.V.one_mem
  obtain ⟨l, hl⟩ := d.sq_surjective_units₀ (Units.mk0 (c' / c) (div_ne_zero hc' hc))
  have hl' : (l : d.Γ₀) * (l : d.Γ₀) = c' / c := by
    rw [← Units.val_mul, ← sq, hl, Units.val_mk0]
  have hj : d.torus (l, 1) * d.x₆ c * (d.torus (l, 1))⁻¹ = d.x₆ c' := by
    rw [d.torus_conj_x₆_of_snd_eq_one, hl', div_mul_cancel₀ _ hc]
  have hwj : w * d.torus (l, 1) * w⁻¹ ∈ d.J := d.conj_mem_J hw ⟨(l, 1), rfl⟩
  rw [← hj, show w * (d.torus (l, 1) * d.x₆ c * (d.torus (l, 1))⁻¹) * w⁻¹ =
    (w * d.torus (l, 1) * w⁻¹) * (w * d.x₆ c * w⁻¹) * (w * d.torus (l, 1) * w⁻¹)⁻¹ by group]
  exact (mem_normalizer_iff.1 (d.J_le_normalizer_V hwj) _).1 h

theorem centralizer_x₆_one_le_normalizer_V :
    centralizer ({d.x₆ 1} : Set X) ≤ normalizer (d.V : Set X) := by
  intro g hg
  obtain ⟨b₁, hb₁, w, hw, b₂, hb₂, rfl⟩ := d.bruhat g
  have hb₁' : b₁ ∈ normalizer (d.V : Set X) := d.B_le_normalizer_V hb₁
  have hb₂' : b₂ ∈ normalizer (d.V : Set X) := d.B_le_normalizer_V hb₂
  have hz : b₂ * d.x₆ 1 * b₂⁻¹ ∈ d.V := (mem_normalizer_iff.1 hb₂' _).1 (d.x₆_mem_V 1)
  have hz1 : b₂ * d.x₆ 1 * b₂⁻¹ ≠ 1 := by
    rw [Ne, conj_eq_one_iff, d.x₆_eq_one_iff]
    exact one_ne_zero
  have hc : b₁ * w * b₂ * d.x₆ 1 * (b₁ * w * b₂)⁻¹ = d.x₆ 1 := by
    rw [mem_centralizer_singleton_iff.1 hg, mul_inv_cancel_right]
  have hb₁V : b₁⁻¹ * d.x₆ 1 * b₁ ∈ d.V := by
    simpa only [inv_inv] using (mem_normalizer_iff.1 (inv_mem hb₁') (d.x₆ 1)).1 (d.x₆_mem_V 1)
  have hwz : w * (b₂ * d.x₆ 1 * b₂⁻¹) * w⁻¹ = b₁⁻¹ * d.x₆ 1 * b₁ := by
    calc w * (b₂ * d.x₆ 1 * b₂⁻¹) * w⁻¹
        = b₁⁻¹ * (b₁ * w * b₂ * d.x₆ 1 * (b₁ * w * b₂)⁻¹) * b₁ := by group
      _ = b₁⁻¹ * d.x₆ 1 * b₁ := by rw [hc]
  have hw' := d.mem_normalizer_V_of_conj_mem_V hw hz hz1 (hwz ▸ hb₁V)
  exact mul_mem (mul_mem hb₁' hw') hb₂'

theorem mem_centralizer_V_of_mem_J {j : X} (hj : j ∈ d.J)
    (h : j ∈ centralizer ({d.x₆ 1} : Set X)) : j ∈ centralizer (d.V : Set X) := by
  obtain ⟨k, rfl⟩ := hj
  have h1 := d.torus_x₆ k 1
  rw [mem_centralizer_singleton_iff.1 h, mul_inv_cancel_right, mul_one] at h1
  have hs := d.x₆_injective h1
  rw [mem_centralizer_iff]
  rintro _ ⟨b, rfl⟩
  have h2 := d.torus_x₆ k b
  rw [← hs, one_mul] at h2
  calc d.x₆ b * d.torus k = d.torus k * d.x₆ b * (d.torus k)⁻¹ * d.torus k := by rw [h2]
    _ = d.torus k * d.x₆ b := by group

theorem centralizer_x₆_one_eq_centralizer_V :
    centralizer ({d.x₆ 1} : Set X) = centralizer (d.V : Set X) := by
  have hsub : centralizer (d.V : Set X) ≤ centralizer ({d.x₆ 1} : Set X) :=
    centralizer_le (Set.singleton_subset_iff.2 (d.x₆_mem_V 1))
  refine le_antisymm (fun g hg => ?_) hsub
  obtain ⟨n, hn, s, hs, j, hj, rfl⟩ :=
    d.exists_mul_of_mem_normalizer_V (d.centralizer_x₆_one_le_normalizer_V hg)
  have hns : n * s ∈ centralizer (d.V : Set X) :=
    mul_mem (d.S_le_centralizer_V (d.D_le_S hn)) (d.leviShort_le_centralizer_V hs)
  have hjc : j ∈ centralizer ({d.x₆ 1} : Set X) := by
    have := mul_mem (inv_mem (hsub hns)) hg
    rwa [show (n * s)⁻¹ * (n * s * j) = j by group] at this
  exact mul_mem hns (d.mem_centralizer_V_of_mem_J hj.1 hjc)

theorem centralizer_x₆_one_eq : centralizer ({d.x₆ 1} : Set X) = d.D ⊔ d.leviShort := by
  rw [d.centralizer_x₆_one_eq_centralizer_V, d.centralizer_V_eq]

theorem mem_Y_of_forall_conj_x₁_mem_V {x : X} (hx : x ∈ d.D)
    (h : ∀ b, d.x₁ b * x * (d.x₁ b)⁻¹ * x⁻¹ ∈ d.V) : x ∈ d.Y := by
  have h' : ∀ b, ⁅x, d.x₁ b⁆ ∈ d.V := fun b => by
    rw [← commutatorElement_inv, commutatorElement_def]
    exact inv_mem (h b)
  have hF := d.mem_F_of_commutatorElement_x₁_mem_W hx (d.Y_le_W (d.V_le_Y (h' 1)))
  have hW := d.mem_W_of_forall_commutatorElement_x₁_mem_Y hF fun b => d.V_le_Y (h' b)
  exact d.mem_Y_of_forall_commutatorElement_x₁_mem_V hW h'

private theorem exists_x₂_mul_of_conj_u_mem_Y {z : X} (hz : d.u * z * d.u ∈ d.Y) :
    ∃ β, ∃ n ∈ d.V, d.x₂ β * n = z := by
  obtain ⟨β, n, hn, he⟩ := d.mem_Y_iff.1 hz
  refine ⟨β, n, hn, ?_⟩
  have hu : ∀ w, d.u * (d.u * w) = w := fun w => by rw [← mul_assoc, d.u_mul_self, one_mul]
  have hun : d.u * n * d.u = n := by
    rw [← mem_centralizer_iff.1 d.u_mem_centralizer_V n hn, mul_assoc, d.u_mul_self, mul_one]
  have h5 : d.u * d.x₅ β * d.u = d.x₂ β := by simpa only [d.u_inv] using d.u_conj_x₅ β
  calc d.x₂ β * n = d.u * d.x₅ β * d.u * (d.u * n * d.u) := by rw [h5, hun]
    _ = d.u * (d.x₅ β * n) * d.u := by simp only [mul_assoc, hu]
    _ = z := by rw [he]; simp only [mul_assoc, hu, d.u_mul_self, mul_one]

private theorem commute_of_mem_V_of_mem_S {m g : X} (hm : m ∈ d.V) (hg : g ∈ d.S) :
    Commute m g :=
  mem_centralizer_iff.1 (d.S_le_centralizer_V hg) m hm

theorem mul_ne_mul_of_mem_Y_of_conj_u_mem_Y {y z : X} (hy : y ∈ d.Y)
    (hz : d.u * z * d.u ∈ d.Y) (hyV : y ∉ d.V) (hzV : z ∉ d.V) : y * z ≠ z * y := by
  obtain ⟨α, n, hn, rfl⟩ := d.mem_Y_iff.1 hy
  obtain ⟨β, n', hn', rfl⟩ := d.exists_x₂_mul_of_conj_u_mem_Y hz
  have hα : α ≠ 0 := fun h0 => hyV (by rw [h0, d.x₅_zero, one_mul]; exact hn)
  have hβ : β ≠ 0 := fun h0 => hzV (by rw [h0, d.x₂_zero, one_mul]; exact hn')
  intro hc
  have h5 : d.x₅ α * n ∈ d.S := mul_mem (d.U₅_le_S (d.x₅_mem_U₅ α)) (d.V_le_S hn)
  have h2 : d.x₂ β * n' ∈ d.S := mul_mem (d.U₂_le_S (d.x₂_mem_U₂ β)) (d.V_le_S hn')
  have hn5 : Commute (n⁻¹) (d.x₂ β * n' * n'⁻¹) :=
    ((d.commute_of_mem_V_of_mem_S hn h2).mul_right
      (d.commute_of_mem_V_of_mem_S hn (d.V_le_S (inv_mem hn')))).inv_left
  have hcomm : Commute (d.x₅ α * n * n⁻¹) (d.x₂ β * n' * n'⁻¹) :=
    ((Commute.mul_right hc (d.commute_of_mem_V_of_mem_S (inv_mem hn') h5).symm).mul_left hn5)
  rw [mul_inv_cancel_right, mul_inv_cancel_right] at hcomm
  have h6 := d.comm₂₅ β α
  rw [hcomm.symm.commutator_eq] at h6
  exact mul_ne_zero hβ hα (d.x₆_eq_one_iff.1 h6.symm)

include d in
private theorem eight_le_q_cube : 8 ≤ q ^ 3 := by
  have := d.two_le_q
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ q ^ 3 := Nat.pow_le_pow_left this 3

theorem isSimpleGroup_leviShort : IsSimpleGroup d.leviShort := by
  have h4 : 4 ≤ Nat.card d.Γ := by
    rw [d.card_Γ]
    have := d.eight_le_q_cube
    omega
  have := CFSG.LocalAnalysis.EvenBN.Common.sl2_isSimpleGroup_of_charTwo h4
  exact d.leviShortEquiv.isSimpleGroup

theorem exists_mem_leviShort_orderOf_eq_three : ∃ g ∈ d.leviShort, orderOf g = 3 := by
  have := d.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨f, -, hq⟩ := d.two_pow
  have h3 : 3 ∣ Nat.card d.leviShort := by
    rw [d.card_leviShort, hq]
    refine Dvd.dvd.mul_left ?_ _
    rw [← pow_mul, mul_comm, pow_mul]
    have := Nat.sub_dvd_pow_sub_pow (2 ^ 6) 1 f
    rw [one_pow] at this
    exact (show 3 ∣ 2 ^ 6 - 1 by norm_num).trans this
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
  exact ⟨g, g.2, by rw [Subgroup.orderOf_coe, hg]⟩

private theorem x₁_one_ne_one : d.x₁ 1 ≠ 1 := fun h =>
  one_ne_zero (d.x₁_injective (h.trans d.x₁_zero.symm))

theorem exists_inv_x₁_one :
    ∃ τ : X, orderOf τ = q ^ 3 + 1 ∧ d.x₁ 1 * τ * (d.x₁ 1)⁻¹ = τ⁻¹ := by
  obtain ⟨A, hA⟩ := CFSG.SeitzReduction.F4Pilot.exists_orderOf_eq_natCard_add_one (K := d.Γ)
  rw [d.card_Γ] at hA
  obtain ⟨s, hs, hsA⟩ := CFSG.CGT.Timmesfeld75.exists_mul_self_eq_one_conj_eq_inv A
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [one_mul, mul_one] at hsA
    have h2 : A ^ 2 = 1 := by rw [sq]; exact mul_eq_one_iff_eq_inv.2 hsA
    have := orderOf_le_of_pow_eq_one two_pos h2
    have := d.eight_le_q_cube
    omega
  have hyL : d.x₁ 1 ∈ d.leviShort := d.x₁_mem_leviShort 1
  have hyy : d.leviShortEquiv ⟨d.x₁ 1, hyL⟩ * d.leviShortEquiv ⟨d.x₁ 1, hyL⟩ = 1 := by
    rw [← map_mul, show (⟨d.x₁ 1, hyL⟩ : d.leviShort) * ⟨d.x₁ 1, hyL⟩ = 1 from
      Subtype.ext (d.x₁_mul_self 1), map_one]
  have hy1 : d.leviShortEquiv ⟨d.x₁ 1, hyL⟩ ≠ 1 := by
    rw [Ne, MulEquiv.map_eq_one_iff]
    exact fun h => d.x₁_one_ne_one (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := isConj_iff.1
    (CFSG.CGT.Timmesfeld75.isConj_of_mul_self_eq_one hs hs1 hyy hy1)
  have hinv : d.leviShortEquiv ⟨d.x₁ 1, hyL⟩ * (c * A * c⁻¹) *
      (d.leviShortEquiv ⟨d.x₁ 1, hyL⟩)⁻¹ = (c * A * c⁻¹)⁻¹ := by
    rw [← hc]
    calc c * s * c⁻¹ * (c * A * c⁻¹) * (c * s * c⁻¹)⁻¹ = c * (s * A * s⁻¹) * c⁻¹ := by group
      _ = (c * A * c⁻¹)⁻¹ := by rw [inv_eq_of_mul_eq_one_right hs, hsA]; group
  refine ⟨(d.leviShortEquiv.symm (c * A * c⁻¹) : X), ?_, ?_⟩
  · have h1 := MulEquiv.orderOf_eq (MulAut.conj c) A
    rw [MulAut.conj_apply] at h1
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, h1, hA]
  · have h1 : ⟨d.x₁ 1, hyL⟩ * d.leviShortEquiv.symm (c * A * c⁻¹) * (⟨d.x₁ 1, hyL⟩)⁻¹ =
        (d.leviShortEquiv.symm (c * A * c⁻¹))⁻¹ := by
      apply d.leviShortEquiv.injective
      rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
      exact hinv
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] using
      congrArg Subtype.val h1

theorem isConj_x₁_x₄ (a : d.Γ) : IsConj (d.x₁ a) (d.x₄ a) := by
  refine isConj_iff.2 ⟨d.u * d.v, ?_⟩
  rw [mul_inv_rev, d.u_inv, d.v_inv]
  calc d.u * d.v * d.x₁ a * (d.v * d.u) = d.u * (d.v * d.x₁ a * d.v) * d.u := by group
    _ = d.x₄ a := by rw [d.v_x₁, d.u_x₃]

private theorem isPGroup_D : IsPGroup 2 d.D := by
  obtain ⟨P, hP⟩ := d.exists_sylow_eq_S
  exact (hP ▸ P.isPGroup').to_le d.D_le_S

private theorem sup_D_inf_leviShort_eq_bot {A : Subgroup X} (hA : IsPGroup 2 A)
    (hAC : A ≤ d.D ⊔ d.leviShort) (hN : d.leviShort ≤ normalizer (A : Set X)) :
    (A ⊔ d.D) ⊓ d.leviShort = ⊥ := by
  have hAD : A ≤ normalizer (d.D : Set X) :=
    hAC.trans (sup_le le_normalizer d.leviShort_le_normalizer_D)
  have h2 : IsPGroup 2 ↥(A ⊔ d.D) := hA.to_sup_of_normal_right' d.isPGroup_D hAD
  have hLN : d.leviShort ≤ normalizer ((A ⊔ d.D : Subgroup X) : Set X) := fun s hs =>
    inf_normalizer_le_normalizer_sup A d.D ⟨hN hs, d.leviShort_le_normalizer_D hs⟩
  have hnorm : (((A ⊔ d.D) ⊓ d.leviShort).subgroupOf d.leviShort).Normal := by
    rw [normal_subgroupOf_iff inf_le_right]
    intro x s hx hs
    rw [mem_inf] at hx ⊢
    exact ⟨(mem_normalizer_iff.1 (hLN hs) x).1 hx.1, mul_mem (mul_mem hs hx.2) (inv_mem hs)⟩
  rcases (Subgroup.isSimpleGroup_iff.1 d.isSimpleGroup_leviShort).2 _ inf_le_right hnorm with
    h | h
  · exact h
  · obtain ⟨g, hg, hg3⟩ := d.exists_mem_leviShort_orderOf_eq_three
    have hgT : g ∈ (A ⊔ d.D) ⊓ d.leviShort := by rw [h]; exact hg
    obtain ⟨k, hk⟩ := h2 ⟨g, hgT.1⟩
    have h3 : orderOf g ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    rw [hg3] at h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem le_D_of_isPGroup_of_le_sup_leviShort {A : Subgroup X} (hA : IsPGroup 2 A)
    (hAC : A ≤ d.D ⊔ d.leviShort) (hN : d.leviShort ≤ normalizer (A : Set X)) : A ≤ d.D := by
  have hT := d.sup_D_inf_leviShort_eq_bot hA hAC hN
  intro a ha
  obtain ⟨n, hn, s, hs, rfl⟩ := d.exists_mul_of_mem_D_sup_leviShort (hAC ha)
  have hs' : s ∈ (A ⊔ d.D) ⊓ d.leviShort := by
    refine ⟨?_, hs⟩
    have := mul_mem (mem_sup_right (S := A) (inv_mem hn)) (mem_sup_left (T := d.D) ha)
    rwa [inv_mul_cancel_left] at this
  rw [hT, mem_bot] at hs'
  rw [hs', mul_one]
  exact hn

end TrialityD4Data

end CFSG.LocalAnalysis.EvenBN.TrialityD4
