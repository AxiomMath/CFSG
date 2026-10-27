module

public import CFSG.Certificates.Kernel.G2Three.Sec1T3ASound
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.S11
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Words3
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.KC.G2Three.Sec1T3

open Subgroup CFSG.KD.G2Three.Sec1T3 CFSG.KC.Loop CFSG.CosetTable
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.OddStandard.HigherRank.G2Three.Sec1Proof
  CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {elt : ℕ → Γ} {P C V Q : ℕ}

theorem f11_e1 {fr : Frame Γ} (hg : ∀ s < 5, elt (s + 1) = sGen fr s) :
    elt 1 = fr.a₁ ∧ elt 2 = fr.b₁ ∧ elt 3 = fr.a₂ ∧ elt 4 = fr.b₂ ∧ elt 5 = fr.h₀ :=
  ⟨by rw [hg 0 (by norm_num), sGen_zero], by rw [hg 1 (by norm_num), sGen_one],
    by rw [hg 2 (by norm_num), sGen_two], by rw [hg 3 (by norm_num), sGen_three],
    by rw [hg 4 (by norm_num), sGen_four]⟩

theorem f11_gens5 {fr : Frame Γ} (hg : ∀ s < 5, elt (s + 1) = sGen fr s) :
    {x | ∃ g ∈ [1, 2, 3, 4, 5], elt g = x} = {fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀} := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := f11_e1 hg
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨g, hg', rfl⟩
    rcases hg' with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨1, Or.inl rfl, h1⟩
    · exact ⟨2, Or.inr (Or.inl rfl), h2⟩
    · exact ⟨3, Or.inr (Or.inr (Or.inl rfl)), h3⟩
    · exact ⟨4, Or.inr (Or.inr (Or.inr (Or.inl rfl))), h4⟩
    · exact ⟨5, Or.inr (Or.inr (Or.inr (Or.inr rfl))), h5⟩

theorem f11_gens6 {fr : Frame Γ} (hg : ∀ s < 6, elt (s + 1) = sGen fr s) :
    {x | ∃ g ∈ [1, 2, 3, 4, 5, 6], elt g = x} = {fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀, fr.σ} := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := f11_e1 (fun s hs => hg s (by omega))
  have h6 : elt 6 = fr.σ := by rw [hg 5 (by norm_num), sGen_five]
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨g, hg', rfl⟩
    rcases hg' with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6))))
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨1, Or.inl rfl, h1⟩
    · exact ⟨2, Or.inr (Or.inl rfl), h2⟩
    · exact ⟨3, Or.inr (Or.inr (Or.inl rfl)), h3⟩
    · exact ⟨4, Or.inr (Or.inr (Or.inr (Or.inl rfl))), h4⟩
    · exact ⟨5, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), h5⟩
    · exact ⟨6, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), h6⟩

theorem f11_card (hR : RealT elt P C V Q) {M : ℕ} {K : Subgroup Γ}
    (hM : mset elt M = (K : Set Γ)) : Nat.card K = pop M := by
  rw [← pop_sound hR.inj (repM_mset hR.inj M), hM]
  exact Nat.card_coe_set_eq (K : Set Γ)

theorem f11_S {fr : Frame Γ} (hR : RealT elt P C V Q) (hg : ∀ s < 5, elt (s + 1) = sGen fr s)
    {R : ℕ} (hc : closOK C [1, 2, 3, 4, 5] R = true) :
    mset elt (closK C [1, 2, 3, 4, 5] R) = (fr.S : Set Γ) := by
  rw [closK_closure hR (by decide) hc, f11_gens5 hg]
  rfl

theorem f11_Ss {fr : Frame Γ} (hR : RealT elt P C V Q) (hg : ∀ s < 6, elt (s + 1) = sGen fr s)
    {R : ℕ} (hc : closOK C [1, 2, 3, 4, 5, 6] R = true) :
    mset elt (closK C [1, 2, 3, 4, 5, 6] R) = (fr.Sσ : Set Γ) := by
  rw [closK_closure hR (by decide) hc, f11_gens6 hg]
  rfl

theorem f11_rels {fr : Frame Γ} (hR : RealT elt P C V Q) (hg : ∀ s < 6, elt (s + 1) = sGen fr s)
    (h : rel11K P C V Q 1 2 3 4 5 6 = true) : ∀ r ∈ Frame.rels11, FreeGroup.lift fr.gens11 r = 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := f11_e1 (fun s hs => hg s (by omega))
  have h6 : elt 6 = fr.σ := by rw [hg 5 (by norm_num), sGen_five]
  have g0 : fr.gens11 0 = elt 1 := by simp [Frame.gens11, h1]
  have g1 : fr.gens11 1 = elt 2 := by simp [Frame.gens11, h2]
  have g2 : fr.gens11 2 = elt 3 := by simp [Frame.gens11, h3]
  have g3 : fr.gens11 3 = elt 4 := by simp [Frame.gens11, h4]
  have g4 : fr.gens11 4 = elt 5 := by simp [Frame.gens11, h5]
  have g5 : fr.gens11 5 = elt 6 := by simp [Frame.gens11, h6]
  unfold rel11K at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19,
    r20, r21⟩ := h
  have hz : elt (atR Q 2) = elt 2 * elt 2 := hR.sq (by norm_num)
  have E : ∀ {x y : ℕ}, Nat.beq x y = true → elt x = elt y := fun h =>
    congrArg elt (Nat.eq_of_beq_eq_true h)
  have e1 := E r1
  have e2 := E r2
  have e3 := E r3
  have e4 := E r4
  have e5 := E r5
  have e6 := E r6
  have e7 := E r7
  have e8 := E r8
  have e9 := E r9
  have e10 := E r10
  have e11 := E r11
  have e12 := E r12
  have e13 := E r13
  have e14 := E r14
  have e15 := E r15
  have e16 := E r16
  have e17 := E r17
  have e18 := E r18
  have e19 := E r19
  have e20 := E r20
  have e21 := E r21
  have hm : ∀ x y, mulE P x y < 128 := fun _ _ => atR_lt _ _
  simp (disch := first | norm_num | exact atR_lt _ _ | exact hm _ _) only [hR.sq, commE_elt hR, mulE_elt hR,
    hR.one, hz] at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21
  have hz' : ∀ x, x < 128 → elt (mulE P x (atR Q 2)) = elt x * (elt 2 * elt 2) := fun x hx => by
    rw [mulE_elt hR hx (atR_lt _ _), hz]
  have hxy : ∀ x y, x < 128 → y < 128 → elt (mulE P x y) = elt x * elt y := fun x y hx hy =>
    mulE_elt hR hx hy
  rw [hR.sq (atR_lt _ _), hz] at e1
  rw [hz' _ (by norm_num)] at e9 e10
  rw [hz' _ (hm _ _), hxy _ _ (by norm_num) (by norm_num)] at e13 e14 e15 e16
  intro r hr
  simp only [Frame.rels11, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [map_mul, map_inv, map_pow, map_commutatorElement, FreeGroup.lift_apply_of,
    g0, g1, g2, g3, g4, g5, mul_inv_eq_one, pow_two]
  · exact e1
  · exact e2
  · exact e3
  · exact e4
  · exact e5
  · exact e6
  · exact e7
  · exact e8
  · exact e9
  · exact e10
  · exact e11
  · exact e12
  · exact e13
  · exact e14
  · exact e15
  · exact e16
  · exact e17
  · exact e18
  · exact e19
  · exact e20
  · exact e21

theorem fact11_of_twin {fr : Frame Γ} {L : Subgroup Γ} {R : ℕ}
    (hR : RealT elt P C V Q) (hg : ∀ s < 6, elt (s + 1) = sGen fr s)
    (h : f11K P C V Q 1 2 3 4 5 6 R = true)
    (hpg : Finite (PG 6 ws11) ∧ Nat.card (PG 6 ws11) ≤ 128) (hSL : fr.S ≤ L)
    (hL : Nat.card L = 4245696) (hΓ : Nat.card Γ = 8491392) : fr.Fact11 L := by
  unfold f11K at h
  simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨hrl, c5, p5, c6, p6⟩ := h
  have hcardS : Nat.card fr.S = 64 := by
    rw [f11_card hR (f11_S hR (fun s hs => hg s (by omega)) c5), p5]
  have hcardSs : Nat.card fr.Sσ = 128 := by
    rw [f11_card hR (f11_Ss hR hg c6), p6]
  have hrel := f11_rels hR hg hrl
  have himage : (PresentedGroup.toGroup hrel) '' Set.range
      (PresentedGroup.of : Fin 6 → PresentedGroup Frame.rels11) = Set.range fr.gens11 := by
    ext x
    constructor
    · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, (PresentedGroup.toGroup.of hrel).symm⟩
    · rintro ⟨j, rfl⟩
      exact ⟨PresentedGroup.of j, ⟨j, rfl⟩, PresentedGroup.toGroup.of hrel⟩
  have hgens : Set.range fr.gens11 = {fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀, fr.σ} := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp [Frame.gens11]
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, by simp [Frame.gens11]⟩
      · exact ⟨1, by simp [Frame.gens11]⟩
      · exact ⟨2, by simp [Frame.gens11]⟩
      · exact ⟨3, by simp [Frame.gens11]⟩
      · exact ⟨4, by simp [Frame.gens11]⟩
      · exact ⟨5, by simp [Frame.gens11]⟩
  have hrange : (PresentedGroup.toGroup hrel).range = fr.Sσ := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of (rels := Frame.rels11),
      MonoidHom.map_closure, himage, hgens]
    rfl
  have hpres : ∃ h : ∀ r ∈ Frame.rels11, FreeGroup.lift fr.gens11 r = 1,
      Function.Injective (PresentedGroup.toGroup h) ∧ (PresentedGroup.toGroup h).range = fr.Sσ := by
    refine ⟨hrel, ?_, hrange⟩
    have : Finite (PresentedGroup Frame.rels11) := by rw [rels11_eq_ws]; exact hpg.1
    have hcardPG : Nat.card (PresentedGroup Frame.rels11) ≤ 128 := by
      rw [rels11_eq_ws]; exact hpg.2
    have hcard_range : Nat.card (PresentedGroup.toGroup hrel).range = 128 := by
      rw [hrange, hcardSs]
    have hbij : Function.Bijective (PresentedGroup.toGroup hrel).rangeRestrict :=
      (MonoidHom.rangeRestrict_surjective _).bijective_of_nat_card_le
        (by rw [hcard_range]; exact hcardPG)
    intro x y hxy
    exact hbij.1 (Subtype.ext (by simpa using hxy))
  have hS2 : IsPGroup 2 fr.S := IsPGroup.of_card (n := 6) (by rw [hcardS]; norm_num)
  have hSs2 : IsPGroup 2 fr.Sσ := IsPGroup.of_card (n := 7) (by rw [hcardSs]; norm_num)
  refine ⟨hpres, ⟨hSL, hS2, ?_⟩, ⟨le_top, hSs2, ?_⟩⟩
  · have hmul := Subgroup.relIndex_mul_card (H := fr.S) (K := L)
    rw [inf_of_le_left hSL, hcardS, hL] at hmul
    have hrel' : fr.S.relIndex L = 66339 := by omega
    rw [hrel']
    norm_num
  · have hmul := Subgroup.index_mul_card (H := fr.Sσ)
    rw [← Subgroup.relIndex_top_right, hcardSs, hΓ] at hmul
    have hrel' : fr.Sσ.relIndex ⊤ = 66339 := by omega
    rw [hrel']
    norm_num

end CFSG.KC.G2Three.Sec1T3

end
