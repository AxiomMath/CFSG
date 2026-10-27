module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII2010Out
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII2010Late
public import CFSG.ClassicalInvolution.Asc77.AscT3CLate10AEng
public import CFSG.ClassicalInvolution.Asc77.AscT3CLate10BEng
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3D8A

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
open Out
open scoped commutatorElement MatrixGroups Pointwise

section Std

variable {G : Type} [Group G] [Finite G] [FrameCore G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

private theorem Std20Frame.late_toG (d : Std20Frame K K' J S R R' W V z t) :
    Std20G K K' J S R R' W V z t :=
  { toStd20F :=
      { d with
        hyp := d.late_hΩ
        late_ne_inv := d.late_ne_inv
        late_mnorm := mem_normalizer_of_mem_omegaStarNbr d.late_hΩ d.viol.star d.viol.hzJ
        late_card2 := fun hU hK hR =>
          Q3T6.Gen612.natCard_eq_two_mul_of_mem_USet d.late_hΩ hU hK hR }
    late_hWc := d.late_hWc
    late_t_mem_W := d.late_t_mem_W
    late_z_mem_W := d.late_z_mem_W
    late_hW := d.late_hW
    late_JW := d.late_JW
    late_exists_swap := d.late_exists_swap
    late_swap_data := fun hu huK => d.late_swap_data hu huK }

theorem Std20Frame.late_W_le_N_K (d : Std20Frame K K' J S R R' W V z t) :
    W ≤ Subgroup.normalizer (K : Set G) := by
  exact d.late_toG.late_W_le_N_K

theorem Std20Frame.late_W_le_N_K' (d : Std20Frame K K' J S R R' W V z t) :
    W ≤ Subgroup.normalizer (K' : Set G) := by
  exact d.late_toG.late_W_le_N_K'

theorem Std20Frame.late_S_act_z (d : Std20Frame K K' J S R R' W V z t) {g : G}
    (hg : g ∈ (S : Subgroup G)) : g * z * g⁻¹ = z := by
  exact d.late_toG.late_S_act_z hg

theorem Std20Frame.late_members_of_inv (d : Std20Frame K K' J S R R' W V z t) {m e : G}
    (hme : m * z * m⁻¹ = e) {L : Subgroup G} (hL : L ∈ CoreAssembly.conjClass K)
    (hLe : IsUniqueInvolution L e) : L = conjSub m K ∨ L = conjSub m K' := by
  exact d.late_toG.late_members_of_inv hme hL hLe

theorem Std20Frame.late_member_data (d : Std20Frame K K' J S R R' W V z t) (m : G) :
    conjSub m K ∈ CoreAssembly.conjClass K ∧ conjSub m K' ∈ CoreAssembly.conjClass K ∧
      conjSub m K ≠ conjSub m K' ∧ IsUniqueInvolution (conjSub m K) (m * z * m⁻¹) ∧
      IsUniqueInvolution (conjSub m K') (m * z * m⁻¹) := by
  exact d.late_toG.late_member_data m

theorem Std20Frame.late_two_lines (d : Std20Frame K K' J S R R' W V z t) {a₀ α b₁ b₂ : G}
    (ha₀ : a₀ ≠ 1) (ha₀2 : a₀ * a₀ = 1) (hα : α ∈ W) (hb₁ : b₁ ∈ W) (hb₂ : b₂ ∈ W)
    (hαa : α * α = a₀) (hb₁a : b₁ * b₁ = a₀) (hb₂a : b₂ * b₂ = a₀)
    (hne : Subgroup.zpowers b₁ ≠ Subgroup.zpowers b₂) :
    Subgroup.zpowers α = Subgroup.zpowers b₁ ∨ Subgroup.zpowers α = Subgroup.zpowers b₂ := by
  exact d.late_toG.late_two_lines d.late_zt_comm ha₀ ha₀2 hα hb₁ hb₂ hαa hb₁a hb₂a hne

theorem Std20Frame.late_exists_m (d : Std20Frame K K' J S R R' W V z t) {a₀ : G}
    (h : a₀ = z ∨ a₀ = t ∨ a₀ = z * t) :
    ∃ m ∈ Subgroup.normalizer (W : Set G), m * z * m⁻¹ = a₀ := by
  rcases h with h | h | h
  · exact ⟨1, Subgroup.one_mem _, by rw [h]; group⟩
  · obtain ⟨m, hm, hmz⟩ := d.late_exists_n
    exact ⟨m, hm, by rw [h]; exact hmz⟩
  · obtain ⟨u, r, v, t₀, T, hh⟩ := d.late_exists_hex
    exact ⟨t₀, hh.t₀_normW, by rw [h]; exact hh.htz⟩

theorem Std20Frame.late_exists_four_gens (d : Std20Frame K K' J S R R' W V z t) :
    (∃ e ∈ K ⊓ W, e * e = z) ∧ ∃ e ∈ K' ⊓ W, e * e = z := by
  obtain ⟨x, r₀, hd⟩ := late_exists_dDataGen d.late_hΩ d.hW d.late_R_mem_D
    d.late_mem_K d.hR d.viol.hzK
  obtain ⟨x', r₀', hd'⟩ := late_exists_dDataGen d.late_hΩ d.hW
    d.late_R'_mem_D d.late_mem_K' d.hR' d.late_hzK'
  exact ⟨late_sq_root_of_dData hd, late_sq_root_of_dData hd'⟩

theorem Std20Frame.late_W_four_mem (d : Std20Frame K K' J S R R' W V z t) {ξ : G} (hξW : ξ ∈ W)
    (hξ2 : ξ * ξ ≠ 1) (hξ4 : (ξ * ξ) * (ξ * ξ) = 1) :
    ∃ m ∈ Subgroup.normalizer (W : Set G), m * z * m⁻¹ = ξ * ξ ∧
      (ξ ∈ conjSub m K ∨ ξ ∈ conjSub m K') := by
  have ha₀W : ξ * ξ ∈ W := W.mul_mem hξW hξW
  have ha₀' : ξ * ξ = z ∨ ξ * ξ = t ∨ ξ * ξ = z * t := by
    rcases d.late_inv_W _ ha₀W hξ4 with h | h | h | h
    · exact absurd h hξ2
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨m, hmN, hme⟩ := d.late_exists_m ha₀'
  obtain ⟨hL₁, hL₂, hL₁₂, hL₁i, hL₂i⟩ := d.late_member_data m
  obtain ⟨⟨e, heKW, he2⟩, ⟨e', he'K'W, he'2⟩⟩ := d.late_exists_four_gens
  have hconjm : ∀ w ∈ W, m * w * m⁻¹ ∈ W := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp hmN w).mp hw
  have hb₁2 : (m * e * m⁻¹) * (m * e * m⁻¹) = ξ * ξ := by
    calc (m * e * m⁻¹) * (m * e * m⁻¹) = m * (e * e) * m⁻¹ := by group
      _ = ξ * ξ := by rw [he2]; exact hme
  have hb₂2 : (m * e' * m⁻¹) * (m * e' * m⁻¹) = ξ * ξ := by
    calc (m * e' * m⁻¹) * (m * e' * m⁻¹) = m * (e' * e') * m⁻¹ := by group
      _ = ξ * ξ := by rw [he'2]; exact hme
  have hA₂ : ∀ {w : G}, w ∈ W → IsPGroup 2 ↥(Subgroup.zpowers w) := fun hw =>
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (d.hWS hw))
  have hA₄ : ∀ {w : G}, w * w = ξ * ξ → 4 ≤ Nat.card ↥(Subgroup.zpowers w) := fun hw => by
    rw [Nat.card_zpowers, late_orderOf_four hw hξ2 hξ4]
  have hb₁L : m * e * m⁻¹ ∈ conjSub m K := conj_mem_conjSub heKW.1
  have hb₂L : m * e' * m⁻¹ ∈ conjSub m K' := conj_mem_conjSub he'K'W.1
  have hb₁W : m * e * m⁻¹ ∈ W := hconjm e heKW.2
  have hb₂W : m * e' * m⁻¹ ∈ W := hconjm e' he'K'W.2
  have hne : Subgroup.zpowers (m * e * m⁻¹) ≠ Subgroup.zpowers (m * e' * m⁻¹) := by
    intro h
    exact hL₁₂ (Sec6Gen.eq_of_le_of_le d.late_hΩ hL₁ hL₂ (hA₂ hb₁W) (hA₄ hb₁2)
      (Subgroup.zpowers_le.mpr hb₁L) (h ▸ Subgroup.zpowers_le.mpr hb₂L))
  refine ⟨m, hmN, hme, ?_⟩
  rcases d.late_two_lines hξ2 hξ4 hξW hb₁W hb₂W rfl hb₁2 hb₂2 hne with h | h
  · left
    exact (h ▸ Subgroup.zpowers_le.mpr hb₁L : Subgroup.zpowers ξ ≤ conjSub m K)
      (Subgroup.mem_zpowers ξ)
  · right
    exact (h ▸ Subgroup.zpowers_le.mpr hb₂L : Subgroup.zpowers ξ ≤ conjSub m K')
      (Subgroup.mem_zpowers ξ)

theorem Std20Frame.late_swap_not_N_member (d : Std20Frame K K' J S R R' W V z t) {σ m a₀ : G}
    (hσ : σ ∈ (S : Subgroup G)) (hσK : conjSub σ K = K') (hσa : σ * a₀ * σ⁻¹ = a₀)
    (hme : m * z * m⁻¹ = a₀) (ha₀ : a₀ = z ∨ a₀ = t ∨ a₀ = z * t) {L : Subgroup G}
    (hL : L = conjSub m K ∨ L = conjSub m K') (hσL : conjSub σ L = L) : False := by
  exact d.late_toG.late_swap_not_N_member hσ hσK hσa hme ha₀ hL hσL

theorem Std20Frame.late_no_fixed_four (d : Std20Frame K K' J S R R' W V z t) {σ ξ : G}
    (hσ : σ ∈ (S : Subgroup G)) (hσK : conjSub σ K = K') (hξW : ξ ∈ W) (hξ2 : ξ * ξ ≠ 1)
    (hξ4 : (ξ * ξ) * (ξ * ξ) = 1) (hfix : σ * ξ * σ⁻¹ = ξ) : False := by
  obtain ⟨m, hmN, hme, hL⟩ := d.late_W_four_mem hξW hξ2 hξ4
  have ha₀' : ξ * ξ = z ∨ ξ * ξ = t ∨ ξ * ξ = z * t := by
    rcases d.late_inv_W _ (W.mul_mem hξW hξW) hξ4 with h | h | h | h
    · exact absurd h hξ2
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hσa : σ * (ξ * ξ) * σ⁻¹ = ξ * ξ := by
    calc σ * (ξ * ξ) * σ⁻¹ = (σ * ξ * σ⁻¹) * (σ * ξ * σ⁻¹) := by group
      _ = ξ * ξ := by rw [hfix]
  have hA₂ : IsPGroup 2 ↥(Subgroup.zpowers ξ) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (d.hWS hξW))
  have hA₄ : 4 ≤ Nat.card ↥(Subgroup.zpowers ξ) := by
    rw [Nat.card_zpowers, late_orderOf_four rfl hξ2 hξ4]
  have hcom : ∀ w ∈ Subgroup.zpowers ξ, σ * w * σ⁻¹ = w := by
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hc : Commute σ ξ := by
      calc σ * ξ = (σ * ξ * σ⁻¹) * σ := by group
        _ = ξ * σ := by rw [hfix]
    have := (Commute.zpow_right hc k).eq
    rw [this]
    group
  obtain ⟨L, hLeq, hξL⟩ : ∃ L : Subgroup G, (L = conjSub m K ∨ L = conjSub m K') ∧ ξ ∈ L := by
    rcases hL with h | h
    · exact ⟨conjSub m K, Or.inl rfl, h⟩
    · exact ⟨conjSub m K', Or.inr rfl, h⟩
  obtain ⟨hL₁, hL₂, -, -, -⟩ := d.late_member_data m
  have hLΩ : L ∈ CoreAssembly.conjClass K := by
    rcases hLeq with h | h
    · rw [h]; exact hL₁
    · rw [h]; exact hL₂
  have hσL : conjSub σ L = L := by
    refine Sec6Gen.eq_of_le_of_le d.late_hΩ (d.hyp.conjInvariant σ L hLΩ) hLΩ hA₂ hA₄ ?_
      (Subgroup.zpowers_le.mpr hξL)
    intro w hw
    rw [mem_conjSub_iff]
    have h1 : σ⁻¹ * (σ * w * σ⁻¹) * σ = w := by group
    rw [hcom w hw] at h1
    rw [h1]
    exact Subgroup.zpowers_le.mpr hξL hw
  exact d.late_swap_not_N_member hσ hσK hσa hme ha₀' hLeq hσL

theorem Std20Frame.late_W_exp_four (d : Std20Frame K K' J S R R' W V z t) (h8 : Nat.card R = 8) :
    ∀ w ∈ W, (w * w) * (w * w) = 1 := by
  obtain ⟨u, r, v, t₀, T, hh⟩ := d.late_exists_hex
  have hTR : Nat.card R = Nat.card T :=
    Sec6Gen.natCard_isSylow2In_eq d.late_hΩ d.late_mem_K d.late_mem_J d.hR hh.hd'.sylow
  have hu4 : orderOf u = 4 := by
    have := hh.hd.card
    omega
  have hv4 : orderOf v = 4 := by
    have := hh.hd'.card
    omega
  have hu4' : u ^ 4 = 1 := by rw [← hu4]; exact pow_orderOf_eq_one u
  have hv4' : v ^ 4 = 1 := by rw [← hv4]; exact pow_orderOf_eq_one v
  intro w hw
  have hWeq : W = Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
    rw [hh.W₀_eq, inf_comm K W, inf_comm J W]
    exact d.late_hW
  have hN : Subgroup.zpowers v ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) := fun g hg =>
    Subgroup.centralizer_le_normalizer (Subgroup.zpowers u : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun h hh' => by
        have hhW : h ∈ W := Subgroup.zpowers_le.mpr hh.hd.u_memW hh'
        have hgW : g ∈ W := Subgroup.zpowers_le.mpr hh.hd'.u_memW hg
        exact d.late_hWc h hhW g hgW)
  rw [hWeq] at hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer hN hw
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hcomm : u ^ i * v ^ j = v ^ j * u ^ i := by
    have := d.late_hWc u hh.hd.u_memW v hh.hd'.u_memW
    exact ((Commute.zpow_zpow (show Commute u v from this) i j).eq)
  have hi : (u ^ i) ^ 4 = 1 := by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]; simp [hu4']
  have hj : (v ^ j) ^ 4 = 1 := by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]; simp [hv4']
  have hc : Commute (u ^ i) (v ^ j) := hcomm
  calc (u ^ i * v ^ j * (u ^ i * v ^ j)) * (u ^ i * v ^ j * (u ^ i * v ^ j))
      = (u ^ i * v ^ j) ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (u ^ i) ^ 4 * (v ^ j) ^ 4 := hc.mul_pow 4
    _ = 1 := by rw [hi, hj, one_mul]

theorem Std20Frame.late_swap_sq_data (d : Std20Frame K K' J S R R' W V z t) {σ e : G}
    (hσ : σ ∈ (S : Subgroup G)) (hσK : conjSub σ K = K') (hσ2 : σ * σ ∈ W)
    (heKW : e ∈ K ⊓ W) (he2 : e * e = z) :
    (e * (σ * e * σ⁻¹) = t ∨ e * (σ * e * σ⁻¹) = z * t) ∧ σ * t * σ⁻¹ = t := by
  exact d.late_toG.late_swap_sq_data hσ hσK hσ2 heKW he2

theorem Std20Frame.late_swap_sq_sq (d : Std20Frame K K' J S R R' W V z t) (h8 : Nat.card R = 8)
    {σ : G} (hσ : σ ∈ (S : Subgroup G)) (hσK : conjSub σ K = K') (hσ2 : σ * σ ∈ W) :
    (σ * σ) * (σ * σ) = 1 := by
  by_contra hne
  refine d.late_no_fixed_four hσ hσK hσ2 hne (d.late_W_exp_four h8 _ hσ2) ?_
  calc σ * (σ * σ) * σ⁻¹ = σ * σ := by group

theorem Std20Frame.late_exists_b (d : Std20Frame K K' J S R R' W V z t) (h8 : Nat.card R = 8)
    (c8 : Concl20_8 S K' R) :
    ∃ b ∈ (S : Subgroup G), conjSub b K = K' ∧ (b * b = t ∨ b * b = z * t) := by
  obtain ⟨u, hu, huK⟩ := d.late_exists_swap
  have hu2 : conjSub (u * u) K = K := by
    rw [conjSub_mul, huK, (d.late_swap_data hu huK).1]
  obtain ⟨σ, hσ, hσK, hσ2⟩ := d.late_exists_sq_W hu huK
    (frame_TX d c8 (Subgroup.mul_mem _ hu hu) hu2)
  obtain ⟨⟨e, heKW, he2⟩, -⟩ := d.late_exists_four_gens
  obtain ⟨ha₀, hσt⟩ := d.late_swap_sq_data hσ hσK hσ2 heKW he2
  have hs4 := d.late_swap_sq_sq h8 hσ hσK hσ2
  have hs₂ : σ * σ = 1 ∨ σ * σ = z ∨ σ * σ = t ∨ σ * σ = z * t :=
    d.late_inv_W _ hσ2 hs4
  rcases hs₂ with h | h | h | h
  ·
    refine ⟨σ * e, Subgroup.mul_mem _ hσ (d.hWS heKW.2), ?_, ?_⟩
    · rw [conjSub_mul, conjSub_eq_self_of_mem heKW.1, hσK]
    · have hb2 : (σ * e) * (σ * e) = (σ * σ) * (e * (σ * e * σ⁻¹)) := by
        have hW1 := d.late_hWc
        have heσW : σ * e * σ⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (d.hWN hσ) e).mp heKW.2
        calc (σ * e) * (σ * e) = (σ * e * σ⁻¹) * (σ * σ) * e := by group
          _ = (σ * σ) * ((σ * e * σ⁻¹) * e) := by rw [hW1 _ heσW _ hσ2]; group
          _ = (σ * σ) * (e * (σ * e * σ⁻¹)) := by rw [hW1 _ heσW _ heKW.2]
      rw [hb2, h, one_mul]
      exact ha₀
  ·
    refine ⟨σ * e, Subgroup.mul_mem _ hσ (d.hWS heKW.2), ?_, ?_⟩
    · rw [conjSub_mul, conjSub_eq_self_of_mem heKW.1, hσK]
    · have hb2 : (σ * e) * (σ * e) = (σ * σ) * (e * (σ * e * σ⁻¹)) := by
        have hW1 := d.late_hWc
        have heσW : σ * e * σ⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (d.hWN hσ) e).mp heKW.2
        calc (σ * e) * (σ * e) = (σ * e * σ⁻¹) * (σ * σ) * e := by group
          _ = (σ * σ) * ((σ * e * σ⁻¹) * e) := by rw [hW1 _ heσW _ hσ2]; group
          _ = (σ * σ) * (e * (σ * e * σ⁻¹)) := by rw [hW1 _ heσW _ heKW.2]
      rw [hb2, h]
      rcases ha₀ with ha | ha
      · right
        rw [ha]
      · left
        rw [ha, ← mul_assoc, d.viol.hzK.sq, one_mul]
  · exact ⟨σ, hσ, hσK, Or.inl h⟩
  · exact ⟨σ, hσ, hσK, Or.inr h⟩

end Std

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
