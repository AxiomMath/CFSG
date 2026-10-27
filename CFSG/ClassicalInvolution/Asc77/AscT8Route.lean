module

public import CFSG.ClassicalInvolution.Asc77.AscT8Four
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenGraphAllWire

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8

theorem perm3_not_comm_involutions (a b : Equiv.Perm (Fin 3)) (ha : a * a = 1) (hb : b * b = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) : a * b ≠ b * a := by
  revert a b
  decide

section Mu

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem not_muIsoS3_of_std8 {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 p f Ω K J S R T W z t) : ¬ MuIsoS3 Ω W := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hP : PartIHyp p f Ω := ⟨hp, hq, hΩ, hs.stand.aEmpty⟩
  have hW : W ∈ WSet Ω := hs.hW.1
  have c : Ctx p f Ω W := ⟨hp, hq, hΩ, hW, thompsonKey G Ω hP W hW, hs.stand.aEmpty⟩
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hSN : ∀ s ∈ (S : Subgroup G), s ∈ Subgroup.normalizer (W : Set G) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 s hs')
  have hRD : R ∈ DSet Ω W := ⟨hRΩ, fun x hx => hSN x (hRS hx)⟩
  have hTD : T ∈ DSet Ω W := ⟨hTΩ, fun x hx => hSN x (hTS hx)⟩
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hJΩ hTΩ hTJ
  have hnot : ∀ {R' : Subgroup G}, R' ∈ DSet Ω W → ∃ r ∈ R', r ∉ W := by
    intro R' hR'
    by_contra h
    push Not at h
    have hle : R' ≤ W := h
    have h1 := D_card hp hq hΩ hW hR'
    rw [inf_eq_left.mpr hle] at h1
    have h2 : 0 < Nat.card R' := Nat.card_pos
    omega
  obtain ⟨r, hr, hrW⟩ := hnot hRD
  obtain ⟨t', ht', htW⟩ := hnot hTD
  let ρ : Rep Ω W := ⟨K, R, r, hK, hRD, hRsyl, hr, hrW⟩
  let σ : Rep Ω W := ⟨J, T, t', hJΩ, hTD, hTsyl, ht', htW⟩
  let x : ↥(muGroup Ω W) :=
    ⟨piG W r, piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hRD hr))⟩
  let y : ↥(muGroup Ω W) :=
    ⟨piG W t', piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hTD ht'))⟩
  have hx : x ∈ muDelta Ω W := ⟨R, hRD, r, hr, hrW, rfl⟩
  have hy : y ∈ muDelta Ω W := ⟨T, hTD, t', ht', htW, rfl⟩
  have hxy : x ≠ y := by
    intro h
    have h' : ρ.img = σ.img := congrArg Subtype.val h
    exact hs.hJ.2.1 (c.K_eq_of_img_eq ρ σ h').symm
  have hcomm : x * y = y * x := Subtype.ext (c.comm_of_omega ρ σ hs.hJ)
  rintro ⟨φ⟩
  have h1 := muDelta_mul_self hp hq hΩ hW hx
  have h2 := muDelta_mul_self hp hq hΩ hW hy
  refine perm3_not_comm_involutions (φ x) (φ y) (by rw [← map_mul, h1, map_one])
    (by rw [← map_mul, h2, map_one])
    (fun h => muDelta_ne_one hW hx (φ.injective (by rw [h, map_one])))
    (fun h => muDelta_ne_one hW hy (φ.injective (by rw [h, map_one])))
    (fun h => hxy (φ.injective h)) ?_
  rw [← map_mul, ← map_mul, hcomm]

end Mu

end T8

variable {p f : ℕ} [Fact p.Prime]

theorem c27_2_of_c27_1 (h1 : C27_1 p f) : C27_2 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc
  by_contra hne
  have hP : PartIHyp p f Ω := ⟨hs.stand.odd, hs.stand.five, hs.stand.hyp, hs.stand.aEmpty⟩
  have hW : W ∈ WSet Ω := hs.hW.1
  have hnc : ¬ DbarConnected Ω W := thompsonGraphAll G Ω hP hs.stand.mem hne hW
  have h27 := h1 G Ω K J S R T W z t hs hdisc
  rcases l7_10_proved G Ω hP W hW hnc with h3 | h4 | h5
  · exact T8.not_muIsoS3_of_std8 hs h3
  · exact h27 (Or.inr (Or.inl h4))
  · exact h27 (Or.inr (Or.inr h5))

theorem thm8A_of_inputs (h26_2 : C26_2 p f) (h26_13 : C26_13 p f) (h26_7 : C26_7 p f)
    (h26_L5 : C26_L5 p f) (h274a : C27_4a p f) (h278 : C27_8 p f) : Thm8A p f :=
  thm8A_of_steps c27_nbr_proved c27_setup_proved
    (c27_4_of_steps (c27_2_of_c27_1 (c27_1_of_steps (cf26_of_steps h26_7 h26_L5) h26_2 h26_13))
      h274a) h278

end CFSG.ClassicalInvolution.Asc77
