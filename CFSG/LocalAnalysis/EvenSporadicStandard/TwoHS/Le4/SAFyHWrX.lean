module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHInspect
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHDec
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHWr

public section

namespace CFSG.EvenSporadicStandard.TwoHS

namespace SignInsp

open Equiv Equiv.Perm Subgroup SignWr SignS9

theorem mk_inv_one (x y : Perm (Fin 5)) : (mk x y 1)⁻¹ = mk x⁻¹ y⁻¹ 1 :=
  inv_eq_of_mul_eq_one_right
    (by rw [mk_mul_one, mul_inv_cancel, mul_inv_cancel, mk_one_one_one])

theorem mk_inv_eps (x y : Perm (Fin 5)) : (mk x y eps)⁻¹ = mk y⁻¹ x⁻¹ eps :=
  inv_eq_of_mul_eq_one_right
    (by rw [mk_mul_eps, mul_inv_cancel, mul_inv_cancel, eps_mul_eps, mk_one_one_one])

theorem trivial_coord_conj {w : Wr} (hw : w.right = 1 ∧ (w.left 1 = 1 ∨ w.left eps = 1))
    (g : Wr) : (g * w * g⁻¹).right = 1 ∧
      ((g * w * g⁻¹).left 1 = 1 ∨ (g * w * g⁻¹).left eps = 1) := by
  obtain ⟨x, y, p, rfl⟩ : ∃ x y p, g = mk x y p := ⟨_, _, _, (mk_eta g).symm⟩
  obtain ⟨a, b, rfl⟩ : ∃ a b, w = mk a b 1 :=
    ⟨w.left 1, w.left eps, by have := mk_eta w; rw [hw.1] at this; exact this.symm⟩
  simp only [mk_left_one, mk_left_eps] at hw
  rcases eq_one_or_eps p with rfl | rfl
  · rw [mk_inv_one, mk_mul_one, mk_mul_one]
    simp only [mk_left_one, mk_left_eps, mk_right, true_and]
    rcases hw.2 with h | h
    · left
      simp [h]
    · right
      simp [h]
  · rw [mk_inv_eps, mk_mul_eps, mul_one, mk_mul_eps, eps_mul_eps]
    simp only [mk_left_one, mk_left_eps, mk_right, true_and]
    rcases hw.2 with h | h
    · right
      simp [h]
    · left
      simp [h]

variable {a : Perm (Fin 5)} (ha : a ≠ 1)

theorem secondCoord_inSecond (u : Perm (Fin 5)) :
    secondCoord a ha ⟨inSecond u, inSecond_mem_centralizer a u⟩ = u := by
  simp [secondCoord_apply, inSecond_apply]

include ha in
theorem inSecond_comm_of_secondCoord (u : Perm (Fin 5))
    (g : centralizer ({mk a 1 1} : Set Wr)) (hg : secondCoord a ha g = 1) :
    inSecond u * (g : Wr) = (g : Wr) * inSecond u := by
  rw [eq_inFirst_of_secondCoord_eq_one a ha hg, inSecond_apply, inFirst_apply, mk_mul_one,
    mk_mul_one]
  simp

variable {D S : Subgroup Wr} {eD : D ≃* DihedralGroup 4} {eS : S ≃* Perm (Fin 5)}

include ha in
theorem wr_inspect_normal (h : LocalPair (mk a 1 1) D S eD eS) {d s : Wr} (hd : d ∈ D)
    (hd1 : d ≠ 1) (hdτ : d ≠ mk a 1 1) (hs : s ∈ S) (hs1 : s ≠ 1) :
    ¬ ∃ g : Wr, d * s = g * mk a 1 1 * g⁻¹ := by
  rintro ⟨g, hg⟩
  obtain ⟨d', hd', hd'1, hds⟩ := retraction_mul_decomp h (Fintype.card_fin 5) (secondCoord a ha)
    inSecond (inSecond_mem_centralizer a) (secondCoord_inSecond ha)
    (inSecond_comm_of_secondCoord ha) hd hdτ hd1 hs
  have hu1 := retraction_ne_one h (Fintype.card_fin 5) (secondCoord a ha) inSecond
    (inSecond_mem_centralizer a) (secondCoord_inSecond ha) hs hs1
  have hker : secondCoord a ha ⟨d', left_le_centralizer h hd'⟩ = 1 :=
    (retraction_ker h (Fintype.card_fin 5) (secondCoord a ha) inSecond
      (inSecond_mem_centralizer a) (secondCoord_inSecond ha) _).2 hd'
  obtain ⟨c, rfl⟩ : ∃ c, d' = inFirst c :=
    ⟨_, eq_inFirst_of_secondCoord_eq_one a ha hker⟩
  have hc1 : c ≠ 1 := fun hc => hd'1 (by rw [hc, map_one])
  have hmk : d * s = mk c (secondCoord a ha ⟨s, right_le_centralizer h hs⟩) 1 := by
    rw [hds, inFirst_apply, inSecond_apply, mk_mul_one]
    simp
  have hQ := trivial_coord_conj (w := mk a 1 1) ⟨rfl, Or.inr (by simp)⟩ g
  rw [← hg, hmk] at hQ
  simp only [mk_left_one, mk_left_eps, mk_right] at hQ
  rcases hQ.2 with hc | hu
  · exact hc1 hc
  · exact hu1 hu

variable {τ : Wr}

theorem wr_inspect (h : LocalPair τ D S eD eS) :
    ∀ d ∈ D, d ≠ 1 → d ≠ τ → d * d = 1 → chi d = 1 →
      ∀ s ∈ S, s ≠ 1 → s * s = 1 → chi s = 1 → ¬ ∃ g : Wr, d * s = g * τ * g⁻¹ := by
  have hr := tau_right_eq_one h
  obtain ⟨a, b, rfl⟩ : ∃ a b, τ = mk a b 1 :=
    ⟨τ.left 1, τ.left eps, by have := mk_eta τ; rw [hr] at this; exact this.symm⟩
  have hsq := h.tau_sq
  rw [mk_mul_one, ← mk_one_one_one, mk_inj] at hsq
  obtain ⟨ha, hb, -⟩ := hsq
  rcases structure_of_card ha hb (tau_ne_one h) (card_centralizer h) with
    ⟨rfl, hb1, hsb⟩ | ⟨ha1, hsa, rfl⟩
  · have h2 := localPair_map h (MulAut.conj swapEl)
    have hτ2 : (MulAut.conj swapEl) (mk 1 b 1) = mk b 1 1 := by
      rw [MulAut.conj_apply, swapEl_conj]
    rw [hτ2] at h2
    have key := inspect_of_map D S (MulAut.conj swapEl) chi hτ2
      (fun d hd hd1 hdτ _ _ s hs hs1 _ _ => wr_inspect_normal hb1 h2 hd hd1 hdτ hs hs1)
    intro d hd hd1 hdτ hdd hχd s hs hs1 hss hχs
    refine key d hd hd1 hdτ hdd ?_ s hs hs1 hss ?_
    · rw [MulAut.conj_apply, chi_conj]
      exact hχd
    · rw [MulAut.conj_apply, chi_conj]
      exact hχs
  · intro d hd hd1 hdτ _ _ s hs hs1 _ _
    exact wr_inspect_normal ha1 h hd hd1 hdτ hs hs1

end SignInsp

theorem signDataWrX : SignDataWrX := by
  intro X _ _ φ τ D S eD eS h
  have h' := SignS9.localPair_map h φ
  have hA := SignWr.conclusion_of_map D S eS φ SignWr.chi (SignWr.wr_main h')
  refine ⟨SignWr.chi.comp φ.toMonoidHom, ?_, ?_, ?_⟩
  · intro d hd h4
    exact hA.1 d hd h4
  · intro s hs
    exact hA.2 s hs
  · exact SignInsp.inspect_of_map D S φ SignWr.chi rfl (SignInsp.wr_inspect h')

end CFSG.EvenSporadicStandard.TwoHS
