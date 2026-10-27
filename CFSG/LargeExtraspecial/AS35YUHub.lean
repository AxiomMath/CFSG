module

public import CFSG.LargeExtraspecial.AS35YULevi
public import CFSG.LargeExtraspecial.AS35YUFrB
public import CFSG.LargeExtraspecial.A2ModARS
public import CFSG.LargeExtraspecial.A2ModCfgE
public import CFSG.LargeExtraspecial.A2ModCfgTA
public import CFSG.LargeExtraspecial.AS35YTHubA
public import CFSG.LargeExtraspecial.AS35YTHubF
public import CFSG.LargeExtraspecial.AS35YTOrd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35YU

open Module CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.Blueprint
open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley CFSG.Timmesfeld.ARS.ExclNS A2Mod AS35YT

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}


theorem frame_dim_le_eight_YU [Finite X] (F : NSLFrameData X (rootSet D)) (hD : RootClass X D)
    (hA : A2Action D Q ρ)
    (hL4 : LieModel X .POmegaPlus 4 2 1 ∨ LieModel X .POmegaMinus 4 2 1) :
    finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 8 := by
  have h := hD.arsHyp
  have hZ := hD.2.2.1
  have hRD : ∀ E ∈ rootSet D, ∃ d ∈ D, E = Subgroup.zpowers d := fun E hE => hE
  have hX : Nat.card (F.D.rootGroup (Pi.single F.i₀ 1)) = 2 :=
    (Frame.card_map_rootGroup_single F F.i₀).symm.trans (hD.card_eq_two _ F.mem)
  have hL : ∀ {t : StatedLieTag} {n p f : ℕ},
      LieModel (F.K ⧸ Subgroup.center F.K) t n p f → LieModel X t n p f :=
    fun h => Frame.lieModel_of_centerQuotient F hZ h
  have he := Frame.centerQuotientEquiv F hZ
  have hle : Finite F.K → Nat.card X ≤ Nat.card F.K := fun _ =>
    Nat.card_le_card_of_surjective F.Ψ F.surj
  have hE6 : (F.D.rank = Tag.rank .F4 ∧ HEq F.D.cartan (Tag.cartan .F4)) → ∀ {f : ℕ}, 1 ≤ f →
      LieModel X .twistedE6 0 2 f → False := fun hF4 f hf hm => by
    obtain rfl := hD.eq_one_of_lieModel (by decide) hf hm
    exact FrF.false_of_nslFrame_lieModel F hF4 h.root h.noIsolated hRD hD.conj_mem hA (Or.inr hm)
  obtain ⟨d, hd, hdA⟩ := hRD _ F.mem
  obtain ⟨K, D', nW, H, hct, hext, hdiv, i₀, type, pg, Ψ, surj, ker, mem, opp, comm, conc⟩ := F
  dsimp only at hX hL he hle hE6 hdA ⊢
  cases conc with
  | symplectic n F' =>
    have hn : 3 ≤ n := Frame.three_le_of_nslType_cartanC (n := n) type
    have hF : Nat.card F' = 2 := (Frame.card_rootGroup_symplectic n F' i₀).symm.trans hX
    have : Finite F' := Nat.finite_of_card_ne_zero (by omega)
    have hadm : StatedLieAdmissible .PSp n 2 1 :=
      ⟨Nat.prime_two, le_rfl, by omega, fun h => by simp only [Prod.mk.injEq] at h; omega⟩
    exact (Ord.lieModel_PSp_false_of_POmega (hL (Or.inl ⟨by decide,
      Symplectic.statedClassicalModel_center_quotient n F' hadm (by rw [hF]; norm_num)⟩)) hL4).elim
  | @minus n K' _ b c hirr =>
    obtain ⟨hm, hi₀⟩ := Frame.of_nslType_cartanB (m := n - 1) type
    have hK : Nat.card K' = 2 := (Frame.card_rootGroup_minus n hirr hi₀).symm.trans hX
    have : Finite K' := Nat.finite_of_card_ne_zero (by omega)
    have hadm : StatedLieAdmissible .POmegaMinus n 2 1 :=
      ⟨Nat.prime_two, le_rfl, show 4 ≤ n by omega⟩
    have hLm : LieModel X .POmegaMinus n 2 1 := hL (Or.inl ⟨by decide,
      Spin.statedClassicalModel_spin_quadMinus hadm (by rw [hK]; norm_num) hirr⟩)
    exact frame_finrank_commSpaceOf_top_le_eight hD.conj_mem hA
      (Ord.eq_of_lieModel_POmega (Or.inr hLm) hL4) hK hirr Ψ surj hi₀ hd hdA
  | g2 K' =>
    have hK : Nat.card K' = 2 := (Frame.card_rootGroup_g2 K' i₀).symm.trans hX
    have : Finite K' := Nat.finite_of_card_ne_zero (by omega)
    have hcard : Nat.card (adjointGroup .G2 K') = 12096 := by
      rw [Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK]
      decide
    have : Finite (adjointGroup .G2 K') := Nat.finite_of_card_ne_zero (by omega)
    have hbig : 12096 < Nat.card X := by
      rcases hL4 with h' | h'
      · exact Ord.twelve_thousand_lt_card_of_lieModel_classical (Or.inr (Or.inr (Or.inl h')))
      · exact Ord.twelve_thousand_lt_card_of_lieModel_classical (Or.inr (Or.inr (Or.inr h')))
    have := hcard ▸ hle this
    omega
  | twistedD4 f => exact (hD.false_of_twistedD4 hA Fact.out he).elim
  | f4 K' =>
    have hi₀ : i₀.val < 2 := by
      rcases NSLType.elim type with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨h, -, -⟩ | ⟨-, h, -⟩
      · exact absurd h cartan_F4_ne_cartanC
      · exact absurd (show Tag.cartan .F4 = Spin.cartanB (Tag.rank .F4) from h) (by decide)
      · exact absurd (show Tag.rank .F4 = 2 from h) (by decide)
      · exact h
    exact (FrF.false_of_f4Datum hct hext hi₀ pg Ψ surj ker mem opp h.root h.noIsolated hRD
      hD.conj_mem hA).elim
  | twistedE6 f =>
    have hf : 1 ≤ f := Fact.out
    have hadm : StatedLieAdmissible .twistedE6 0 2 f := ⟨Nat.prime_two, hf, rfl⟩
    exact (hE6 ⟨rfl, HEq.rfl⟩ hf
      (hL (CurtisTits.curtisTitsConclusion_twistedE6.{0} 2 f hadm).1.2.2)).elim



theorem dim_le_eight_of_pomega4_YU [Finite X] (hD : RootClass X D) (hA : A2Action D Q ρ)
    (hL : LieModel X .POmegaPlus 4 2 1 ∨ LieModel X .POmegaMinus 4 2 1) :
    finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 8 := by
  have h := hD.arsHyp
  have hR := h.root
  have hiso := h.noIsolated
  have hZ := h.center
  have h2 := hD.card_eq_two
  have hRD : ∀ E ∈ rootSet D, ∃ d ∈ D, E = Subgroup.zpowers d := fun E hE => hE
  have hDc := hD.conj_mem
  have hf1 : ∀ {f : ℕ} {E : Subgroup X}, E ∈ rootSet D → Nat.card E = 2 ^ f → f = 1 :=
    fun hE hc => Nat.pow_right_injective le_rfl ((hc.symm.trans (h2 _ hE)).trans (pow_one 2).symm)
  have hbig : 12096 < Nat.card X := by
    rcases hL with h | h
    · exact Ord.twelve_thousand_lt_card_of_lieModel_classical (Or.inr (Or.inr (Or.inl h)))
    · exact Ord.twelve_thousand_lt_card_of_lieModel_classical (Or.inr (Or.inr (Or.inr h)))
  rcases arsOutputPlus_of_card_eq_two h h2 with ⟨m, hm, A, B, hX, hgen⟩ | ⟨m, hm, hX⟩ |
      ⟨A, B, hX, -⟩ | ⟨A, B, hX, -⟩ | ⟨A, B, hX, -⟩ | ⟨-, ⟨F⟩⟩ | ⟨-, hm⟩ | hm
  ·
    exfalso
    rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
    · obtain ⟨f, -, hcard, hL'⟩ := hX.lieModel_A_two hR hiso hZ hgen
      obtain rfl := hf1 (hX.memA 0) (hcard _ (hX.memA 0))
      exact Ord.lieModel_PSL_false_of_POmega hL' hL
    · obtain ⟨f, -, hcard, hL'⟩ := hX.lieModel_A hR hiso hZ hm3 hgen
      obtain rfl := hf1 (hX.memA ⟨0, by omega⟩) (hcard _ (hX.memA ⟨0, by omega⟩))
      exact Ord.lieModel_PSL_false_of_POmega hL' hL
  ·
    obtain ⟨A, B, hX', hgen⟩ := id hX
    obtain ⟨f, -, hcard, hL'⟩ := hX'.lieModel_D hR hiso hZ hm hgen
    obtain rfl := hf1 (hX'.memA ⟨0, by omega⟩) (hcard _ (hX'.memA ⟨0, by omega⟩))
    obtain rfl := Ord.eq_of_lieModel_POmega (Or.inl hL') hL
    exact typeD_four_finrank_commSpaceOf_le_eight hR hiso hRD hDc hA hX
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · exact frame_dim_le_eight_YU F hD hA hL
  · exact (hD.not_lieModel_trialityD4 hA hm).elim
  · rw [Ord.card_of_lieModel_PSU33 hm] at hbig
    omega

theorem fix_or_dim_six_of_psl4_YU [Finite X] (hD : RootClass X D) (hA : A2Action D Q ρ)
    (hL : LieModel X .PSL 4 2 1) :
    (∀ v ∈ commSpaceOf ρ ⊤, (∀ x, ρ x v = v) → v = 0) ∨
      finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 6 := by
  have h := hD.arsHyp
  have hR := h.root
  have hiso := h.noIsolated
  have hZ := h.center
  have h2 := hD.card_eq_two
  have hRD : ∀ E ∈ rootSet D, ∃ d ∈ D, E = Subgroup.zpowers d := fun E hE => hE
  have hDc := hD.conj_mem
  have hf1 : ∀ {f : ℕ} {E : Subgroup X}, E ∈ rootSet D → Nat.card E = 2 ^ f → f = 1 :=
    fun hE hc => Nat.pow_right_injective le_rfl ((hc.symm.trans (h2 _ hE)).trans (pow_one 2).symm)
  have hcardX : Nat.card X = 20160 := by
    rw [(Ord.card_of_lieModel_PSL hL).2]
    decide
  rcases arsOutputPlus_of_card_eq_two h h2 with ⟨m, hm, hX⟩ | ⟨m, hm, A, B, hX, hgen⟩ |
      ⟨A, B, hX, -⟩ | ⟨A, B, hX, -⟩ | ⟨A, B, hX, -⟩ | ⟨-, ⟨F⟩⟩ | ⟨-, hm⟩ | hm
  ·
    have hm3 : m = 3 := by
      obtain ⟨A, B, hX', hgen⟩ := id hX
      have hLm : LieModel X .PSL (m + 1) 2 1 := by
        rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
        · obtain ⟨f, -, hcard, hL'⟩ := hX'.lieModel_A_two hR hiso hZ hgen
          obtain rfl := hf1 (hX'.memA 0) (hcard _ (hX'.memA 0))
          exact hL'
        · obtain ⟨f, -, hcard, hL'⟩ := hX'.lieModel_A hR hiso hZ hm3 hgen
          obtain rfl := hf1 (hX'.memA ⟨0, by omega⟩) (hcard _ (hX'.memA ⟨0, by omega⟩))
          exact hL'
      have hc := (Ord.card_of_lieModel_PSL hLm).2
      rw [hcardX, Nat.add_sub_cancel] at hc
      by_contra hne
      rcases (show m = 2 ∨ 4 ≤ m by omega) with rfl | hm4
      · revert hc
        decide
      · have h31 : 31 ∣ CFSG.Open.ordA m 2 :=
          Ord.dvd_ordA_two (a := 5) (by norm_num) (by omega) (by norm_num)
        rw [← hc] at h31
        revert h31
        decide
    subst hm3
    obtain ⟨Ψ, hs, hΨ⟩ := typeA_exists_surjective hR hiso hRD hDc hm hX
    obtain ⟨-, hA'⟩ := hA.comp_sl (by omega) hΨ
    have hrange : commSpaceOf ρ ⊤ = commSpaceOf (ρ.comp Ψ) ⊤ := by
      rw [← commSpaceOf_range, MonoidHom.range_eq_top.mpr hs]
    rcases exists_isPointMaps_or_finrank_le_six hA' with ⟨P, Pd, hP⟩ | hle
    · left
      intro v hv hfix
      rw [hrange] at hv
      exact fix_eq_zero_of_isPointMaps (by omega) hP hv fun g => hfix (Ψ g)
    · right
      rw [hrange]
      exact hle
  · obtain ⟨f, -, hcard, hL'⟩ := hX.lieModel_D hR hiso hZ hm hgen
    obtain rfl := hf1 (hX.memA ⟨0, by omega⟩) (hcard _ (hX.memA ⟨0, by omega⟩))
    exact (Ord.lieModel_PSL_false_of_POmega hL (Or.inl hL')).elim
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · rcases frame_cases_dim F hD hA with ⟨n, -, hC, -⟩ | ⟨n, -, hB, -⟩ | hle
    · exact (lieModel_PSL_false_of_PSp hL hC).elim
    · exact (Ord.lieModel_PSL_false_of_POmega hL (Or.inr hB)).elim
    · omega
  · exact (hD.not_lieModel_trialityD4 hA hm).elim
  · rw [Ord.card_of_lieModel_PSU33 hm] at hcardX
    omega

end CFSG.LargeExtraspecial.AS35YU
