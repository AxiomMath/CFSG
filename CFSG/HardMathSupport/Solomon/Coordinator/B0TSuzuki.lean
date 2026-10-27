module

public import CFSG.HardMathSupport.Solomon.Coordinator.B0TDefs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiLayerKernel
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Blueprint CFSG.ShultStronglyClosedTI CFSG.RankThree.PartTwo.KFacts

theorem suzLike_of_suzukiModel {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a) {f : ℕ} (h : SuzukiModel S 2 f) :
    SuzLike S := by
  refine ⟨two_dvd_card_of_suzukiModel h, fun Q α hα k hk => ?_⟩
  obtain ⟨-, a, ha1, K, _, _, hf, hK, ⟨e⟩⟩ := h
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := hf ▸ hK
  let H := suzukiGroup a K
  let Q' : Sylow 2 H := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective Q
  have hQ' : (Q' : Subgroup H) = (Q : Subgroup S).map e.toMonoidHom := Sylow.coe_mapSurjective _ _
  let γ : MulAut H := (e.symm.trans α).trans e
  have hγ : ∀ x ∈ (Q' : Subgroup H), γ x = x := by
    intro x hx
    rw [hQ'] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    show e (α (e.symm (e y))) = e y
    rw [MulEquiv.symm_apply_apply, hα y hy]
  let V : Subgroup H := (CFSG.omega₁ (G := (Q' : Subgroup H)) (p := 2)).map (Q' : Subgroup H).subtype
  have hγQ : (Q' : Subgroup H).map γ.toMonoidHom = Q' := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change γ y ∈ (Q' : Subgroup H)
      rw [hγ y hy]
      exact hy
    · intro hx
      exact ⟨x, hx, hγ x hx⟩
  have hγV : ∀ v ∈ V, γ v = v := by
    rintro v ⟨y, -, rfl⟩
    exact hγ _ y.2
  have hγQV : ∀ x ∈ (Q' : Subgroup H), x⁻¹ * γ x ∈ V := by
    intro x hx
    rw [hγ x hx, inv_mul_cancel]
    exact V.one_mem
  obtain ⟨b, hb, hγb⟩ :=
    suzuki_rank_one_Sylow_layer_kernel ha1 hK' Q' V rfl γ hγQ hγV hγQV
  rw [hQ'] at hb
  obtain ⟨y, hy, rfl⟩ := hb
  have hαy : α = MulAut.conj y := by
    ext x
    have h1 : γ (e x) = e y * e x * (e y)⁻¹ := by
      rw [hγb, MulAut.conj_apply]
      rfl
    have h2 : e (α x) = e y * e x * (e y)⁻¹ := by
      rw [← h1]
      show e (α x) = e (α (e.symm (e x)))
      rw [MulEquiv.symm_apply_apply]
    rw [MulAut.conj_apply]
    apply e.injective
    rw [h2, map_mul, map_mul, map_inv]
  have hcenter : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨u, v, huv⟩ := hnab
      apply huv
      have : u ∈ Subgroup.center S := by rw [h]; exact Subgroup.mem_top u
      exact (Subgroup.mem_center_iff.1 this v).symm
  have hyk : y ^ 3 ^ k = 1 := by
    have h1 : MulAut.conj (y ^ 3 ^ k) = (1 : MulAut S) := by
      rw [map_pow, ← hαy]
      exact hk
    have : y ^ 3 ^ k ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun a : MulAut S => a g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [hcenter, Subgroup.mem_bot] at this
    exact this
  obtain ⟨j, hj⟩ := Q.isPGroup' ⟨y, hy⟩
  have hyj : y ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hord1 : orderOf y ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hyk
  have hord2 : orderOf y ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hyj
  have hcop : Nat.Coprime (3 ^ k) (2 ^ j) := Nat.Coprime.pow _ _ (by norm_num)
  have hy1 : y = 1 := orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left hord1) hord2)
  rw [hαy, hy1, map_one]

end CFSG.HardMathSupport.Solomon.Coordinator
