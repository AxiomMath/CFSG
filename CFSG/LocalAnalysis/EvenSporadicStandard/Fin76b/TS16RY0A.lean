module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RY0

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem congr_conj_apply (e : X ≃* Y) (x : X) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem map_rootGroup_of_equiv (e : X ≃* Y) (t : X) :
    (rootGroup X t).map e.toMonoidHom = rootGroup Y (e t) := by
  have hroots : {y : Y | y * y = e t} = e '' {x : X | x * x = t} := by
    ext y
    constructor
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hy
    · rintro ⟨x, hx, rfl⟩
      simp only [Set.mem_ofPred_eq, ← map_mul]
      exact congrArg e hx
  unfold rootGroup
  rw [hroots, MonoidHom.map_closure]
  rfl

theorem map_fixedSub_of_equiv (e : X ≃* Y) (r : MulAut X) :
    (fixedSub r).map e.toMonoidHom = fixedSub (MulAut.congr e r) := by
  ext y
  simp only [Subgroup.mem_map, mem_fixedSub, MulEquiv.coe_toMonoidHom, MulAut.congr_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp [hx]
  · intro h
    refine ⟨e.symm y, ?_, by simp⟩
    apply e.injective
    simpa using h

theorem map_thetaSub_le (e : X ≃* Y) (t : X) (r : MulAut X) :
    (thetaSub t r).map (MulAut.congr e).toMonoidHom ≤ thetaSub (e t) (MulAut.congr e r) := by
  unfold thetaSub
  rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  refine sup_le_sup_right ?_ _
  rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  refine ⟨e c, ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    have := mem_centralizer_singleton_iff.1 hc
    show e c * e t = e t * e c
    rw [← map_mul, ← map_mul, this]
  · simp only [MulEquiv.coe_toMonoidHom]
    exact (congr_conj_apply e c).symm

theorem quadSet_map (e : X ≃* Y) (t ξ : X) :
    ∀ a ∈ quadSet t ξ, MulAut.congr e a ∈ quadSet (e t) (e ξ) := by
  intro a ha
  simp only [quadSet, Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
  rcases ha with rfl | rfl | rfl | rfl
  · left; exact map_one _
  · right; left; exact congr_conj_apply e t
  · right; right; left; exact congr_conj_apply e ξ
  · right; right; right
    rw [map_mul, congr_conj_apply, congr_conj_apply]

theorem S16Model.of_mulEquiv (e : X ≃* Y) {t β : X} (h : S16Model X t β) :
    S16Model Y (e t) (e β) := by
  obtain ⟨r, v, ξ, h⟩ := h
  refine ⟨MulAut.congr e r, e v, e ξ, ?_⟩
  have hε : ∀ x : X, (MulAut.congr e r) (e x) = e (r x) := by
    intro x; simp [MulAut.congr_apply]
  refine
  { r_sq := by rw [← map_mul, h.r_sq, map_one]
    r_outer := ?_
    r_t := by rw [hε, h.r_t]
    r_β := by rw [hε, h.r_β, map_inv]
    v_t := by rw [← map_mul, ← map_mul, h.v_t]
    ξ_t := by rw [← map_mul, ← map_mul, h.ξ_t]
    v4 := by rw [← map_pow, h.v4]
    v8 := by rw [← map_pow, h.v8, map_one]
    ξ_sq := by rw [← map_mul, h.ξ_sq, map_one]
    ξ_ne_one := fun h1 => h.ξ_ne_one (e.injective (by rw [h1, map_one]))
    ξ_ne_t := fun h1 => h.ξ_ne_t (e.injective h1)
    ξ_v := by rw [← map_inv, ← map_mul, ← map_mul, h.ξ_v, map_inv]
    r_v := by rw [hε, h.r_v, map_mul]
    r_ξ := by rw [hε, h.r_ξ, map_mul]
    v_β := by rw [← map_inv, ← map_mul, ← map_mul, h.v_β, map_inv]
    ξ_β := by rw [← map_inv, ← map_mul, ← map_mul, h.ξ_β, map_inv]
    card_CE := ?_
    CE_eq := ?_
    card_Y := ?_
    rank5 := ?_ }
  · intro hin
    have h1 := hin.congr e.symm
    have e1 : MulAut.congr e.symm (MulAut.congr e r) = r := by
      ext w
      simp [MulAut.congr_apply]
    rw [e1] at h1
    exact h.r_outer h1
  · have hE : rootGroup Y (e t) ⊓ fixedSub (MulAut.congr e r) =
        (rootGroup X t ⊓ fixedSub r).map e.toMonoidHom := by
      rw [Subgroup.map_inf _ _ _ e.injective, map_rootGroup_of_equiv, map_fixedSub_of_equiv]
    rw [hE, Subgroup.card_map_of_injective e.injective]
    exact h.card_CE
  · have hE : rootGroup Y (e t) ⊓ fixedSub (MulAut.congr e r) =
        (rootGroup X t ⊓ fixedSub r).map e.toMonoidHom := by
      rw [Subgroup.map_inf _ _ _ e.injective, map_rootGroup_of_equiv, map_fixedSub_of_equiv]
    rw [hE, ← h.CE_eq, MonoidHom.map_closure]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨v * v, Or.inl rfl, by simp⟩
      · exact ⟨v * ξ, Or.inr rfl, by simp⟩
    · rintro ⟨x, (rfl | rfl), rfl⟩
      · left; simp
      · right; simp
  · have hY : closure ({MulAut.conj (e v), MulAut.conj (e ξ), MulAut.congr e r} :
        Set (MulAut Y)) =
        (closure ({MulAut.conj v, MulAut.conj ξ, r} : Set (MulAut X))).map
          (MulAut.congr e).toMonoidHom := by
      rw [MonoidHom.map_closure]
      congr 1
      ext y
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (rfl | rfl | rfl)
        · exact ⟨MulAut.conj v, Or.inl rfl, congr_conj_apply e v⟩
        · exact ⟨MulAut.conj ξ, Or.inr (Or.inl rfl), congr_conj_apply e ξ⟩
        · exact ⟨r, Or.inr (Or.inr rfl), rfl⟩
      · rintro ⟨x, (rfl | rfl | rfl), rfl⟩
        · left; exact congr_conj_apply e v
        · right; left; exact congr_conj_apply e ξ
        · right; right; rfl
    rw [hY, Subgroup.card_map_of_injective (MulAut.congr e).injective]
    exact h.card_Y
  · obtain ⟨C, hCΘ, htC, hξC, hCc, hCcard, hsq, hcm⟩ := h.rank5
    refine ⟨C.map (MulAut.congr e).toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (Subgroup.map_mono hCΘ).trans (map_thetaSub_le e t r)
    · exact ⟨_, htC, congr_conj_apply e t⟩
    · exact ⟨_, hξC, congr_conj_apply e ξ⟩
    · rintro _ ⟨c, hc, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have := mem_centralizer_singleton_iff.1 (hCc hc)
      show MulAut.congr e c * MulAut.conj (e ξ) = MulAut.conj (e ξ) * MulAut.congr e c
      rw [← congr_conj_apply e ξ, ← map_mul, ← map_mul, this]
    · rw [Subgroup.card_map_of_injective (MulAut.congr e).injective]
      exact hCcard
    · rintro _ ⟨c, hc, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul]
      exact quadSet_map e t ξ _ (hsq c hc)
    · rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact quadSet_map e t ξ _ (hcm c hc d hd)

end Transport

theorem S16Model.inv {X : Type*} [Group X] {t β : X} (h : S16Model X t β) :
    S16Model X t β⁻¹ := by
  obtain ⟨r, v, ξ, h⟩ := h
  refine ⟨r, v, ξ, ?_⟩
  exact
  { h with
    r_β := by rw [map_inv, h.r_β]
    v_β := by
      rw [inv_inv]
      calc v * β⁻¹ * v⁻¹ = (v * β * v⁻¹)⁻¹ := by group
        _ = β := by rw [h.v_β, inv_inv]
    ξ_β := by
      rw [inv_inv]
      calc ξ * β⁻¹ * ξ⁻¹ = (ξ * β * ξ⁻¹)⁻¹ := by group
        _ = β := by rw [h.ξ_β, inv_inv] }

end CFSG.EvenSporadicStandard.Fin76b
