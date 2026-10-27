module

public import CFSG.GF2Type.Smith1979.IdxFourModelK2
public import Certificates.Certificate17610
public import CFSG.GF2Type.Smith1979.IdxFourModelLemma5
public import CFSG.GF2Type.Smith1979.IdxFourModelTrv
public import CFSG.GF2Type.Smith1979.IdxFourModelBaseOuter

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Module CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.RankThree.OrthogonalInvolutions

theorem thetaU_eq_omegaE : thetaU = omegaE :=
  LinearEquiv.ext fun x => by rw [thetaU_apply, omegaE_apply]

theorem x0_comm_thetaU : x0 * thetaU = thetaU * x0 := by
  rw [thetaU_eq_omegaE]
  exact x0_comm_omegaE

theorem commSpace_x0 : commSpace x0 = W0 := by
  ext w
  rw [mem_commSpace]
  constructor
  · rintro ⟨v, rfl⟩
    exact x0_sub_self_mem_W0 v
  · exact exists_x0_sub_self

theorem finrank_W0 : finrank (ZMod 2) W0 = 2 :=
  finrank_spanOf_of_indep [3, 192] (by decide) (by decide +kernel)

theorem not_two_pow_nine_dvd_card_centralizer_x0 :
    ¬ 2 ^ 9 ∣ Nat.card ↥(M0 ⊓ Subgroup.centralizer ({x0} : Set (V12 ≃ₗ[ZMod 2] V12))) := by
  rw [card_centralizer_x0]
  norm_num

theorem conj_normal_stab {M : Subgroup (V12 ≃ₗ[ZMod 2] V12)} {v : V12}
    {g : V12 ≃ₗ[ZMod 2] V12} (hg : g ∈ M) {P : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hP : P ≤ stabIn M v) (hn : ∀ s ∈ stabIn M v, ∀ p ∈ P, s * p * s⁻¹ ∈ P) :
    ∃ P' : Subgroup (V12 ≃ₗ[ZMod 2] V12), P' ≤ stabIn M (g v) ∧
      (∀ s ∈ stabIn M (g v), ∀ p ∈ P', s * p * s⁻¹ ∈ P') ∧ Nat.card P' = Nat.card P ∧
      (IsPGroup 2 P → IsPGroup 2 P') := by
  refine ⟨P.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, fun h => h.map _⟩
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨hpM, hpv⟩ := mem_stabIn.1 (hP hp)
    refine mem_stabIn.2 ⟨?_, ?_⟩
    · exact M.mul_mem (M.mul_mem hg hpM) (M.inv_mem hg)
    · simp [hpv]
  · rintro s hs _ ⟨p, hp, rfl⟩
    obtain ⟨hsM, hsv⟩ := mem_stabIn.1 hs
    have hs' : g⁻¹ * s * g ∈ stabIn M v := by
      refine mem_stabIn.2 ⟨M.mul_mem (M.mul_mem (M.inv_mem hg) hsM) hg, ?_⟩
      simp [hsv]
    refine ⟨_, hn _ hs' p hp, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem orbit_eq_of_inO378 {v : V12} (hv : inO378 v) :
    MulAction.orbit ↥M0 v = {x | inO378 x} := by
  ext x
  constructor
  · rintro ⟨⟨U, hU⟩, rfl⟩
    exact inO378_invariant hU hv
  · intro hx
    obtain ⟨U, hU, hUx⟩ := inO378_trans hv hx
    exact ⟨⟨U, hU⟩, hUx⟩

theorem orbit_eq_of_inO1701 {v : V12} (hv : inO1701 v) :
    MulAction.orbit ↥M0 v = {x | inO1701 x} := by
  ext x
  constructor
  · rintro ⟨⟨U, hU⟩, rfl⟩
    exact inO1701_invariant hU hv
  · intro hx
    obtain ⟨U, hU, hUx⟩ := inO1701_trans hv hx
    exact ⟨⟨U, hU⟩, hUx⟩

theorem card_stabIn_M0_of_inO378
    {v : V12} (hv : inO378 v) : Nat.card (stabIn M0 v) = 103680 := by
  have h := card_stabIn_mul_ncard (H := M0) (orbit_eq_of_inO378 hv)
  rw [ncard_inO378, card_M0] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 378) (h.trans (by norm_num))

theorem card_stabIn_M0_of_inO1701
    {v : V12} (hv : inO1701 v) : Nat.card (stabIn M0 v) = 23040 := by
  have h := card_stabIn_mul_ncard (H := M0) (orbit_eq_of_inO1701 hv)
  rw [ncard_inO1701, card_M0] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 1701) (h.trans (by norm_num))

theorem normal_two_subgroup_card_le_four_of_inO378
    {v : V12} (hv : inO378 v)
    {P : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hP : P ≤ stabIn M0 v)
    (hn : ∀ s ∈ stabIn M0 v, ∀ p ∈ P, s * p * s⁻¹ ∈ P) (h2 : IsPGroup 2 P) : Nat.card P ≤ 4 := by
  obtain ⟨U, hU, hUv⟩ := inO378_trans inO378_w0 hv
  have hv' : U⁻¹ v = w0 := by rw [← hUv]; simp
  obtain ⟨P', hP', hn', hcard, h2'⟩ := conj_normal_stab (inv_mem hU) hP hn
  rw [hv'] at hP' hn'
  rw [← hcard]
  exact normal_two_subgroup_card_le_four hP' hn' (h2' h2)

theorem inO378_of_mem_W0 {w : V12} (hw : w ∈ W0) (hw0 : w ≠ 0) : inO378 w := by
  have hn0 : codeOf w ≠ 0 := fun h => hw0 (by rw [← vecOf_codeOf w, h, vecOf_zero])
  rw [mem_W0_iff] at hw
  unfold inO378
  rcases hw with h | h | h | h
  · exact absurd h hn0
  all_goals (rw [h]; decide +kernel)

section Inner

variable {t : V12 ≃ₗ[ZMod 2] V12}

theorem modelInner_of_inner
    (ht : t ∈ Lbar0) (h1 : t ≠ 1) (h2 : t * omegaE = omegaE * t) : ModelInner Vt0 t :=
  Certificates.certificate17610 t ht h1 h2

theorem modelOuter_of_outer
    (ht : t ∈ Lbar0) (hE : t ∉ E0) : ModelOuter t :=
  outer_fix_le ht hE

end Inner

theorem modelFacts :
    ModelFacts M0 K2bar0 Lbar0 x0 a0V Vt0 where
  M_le := M0_le_gammaU
  K2_le := K2bar0_le_M0
  K2_index := relIndex_K2bar0
  x_mem := x0_mem_M0
  x_not_mem := x0_not_mem_K2bar0
  x_sq := x0_mul_self
  x_comm := x0_comm_thetaU
  x_dim := by rw [commSpace_x0]; exact finrank_W0
  x_sing := fun w hw => q0_eq_zero_of_mem_W0 (commSpace_x0 ▸ hw)
  x_cent := not_two_pow_nine_dvd_card_centralizer_x0
  lemma5 := fun w hw hw0 P hP hn h2 hcard => by
    have := normal_two_subgroup_card_le_four_of_inO378
      (inO378_of_mem_W0 (commSpace_x0 ▸ hw) hw0) hP hn h2
    rw [hcard] at this
    norm_num at this
  stab_two := fun v hv hq => by
    rcases (singular_cases hv hq).1 with h | h
    · have := card_stabIn_M0_of_inO378 h
      show 2 ^ 8 ∣ Nat.card (stabIn M0 v)
      rw [this]
      exact ⟨405, by norm_num⟩
    · have := card_stabIn_M0_of_inO1701 h
      show 2 ^ 8 ∣ Nat.card (stabIn M0 v)
      rw [this]
      exact ⟨90, by norm_num⟩
  base := fun v hv hq P hP hn h2 hcard => by
    rcases (singular_cases hv hq).1 with h | h
    · exfalso
      have := normal_two_subgroup_card_le_four_of_inO378 h hP hn h2
      rw [hcard] at this
      norm_num at this
    · obtain ⟨U, hU, hUv⟩ := inO1701_trans h inO1701_a0V
      exact ⟨U, hU, hUv⟩
  lbar_unique := fun P hP hn h2 hcard =>
    Subgroup.eq_of_le_of_card_ge (normal_two_subgroup_le_Lbar0 hP hn h2)
      (by rw [card_Lbar0, hcard]; norm_num)
  vt_le := Vt0_le.trans (Submodule.span_mono (by
    rintro y ⟨l, hl, x, h1, -, rfl⟩
    exact ⟨l, hl, x, h1, rfl⟩))
  vt_rank := finrank_Vt0
  inv_conj := fun _ ht _ h2 => exists_conj_Lbar0_of_involution ht h2
  lbar := fun t ht h1 => by
    by_cases hE : t ∈ E0
    · exact Or.inr (modelInner_of_inner ht h1 ((mem_E0_iff_unitary ht).1 hE))
    · exact Or.inl (modelOuter_of_outer ht hE)

end CFSG.GF2Type.Smith1979.IdxFour
