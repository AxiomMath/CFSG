module

public import CFSG.LargeExtraspecial.A2ModARS
public import CFSG.LargeExtraspecial.A2ModCfgE
public import CFSG.LargeExtraspecial.A2ModHubFrame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod

open Module CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.Blueprint
open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley CFSG.Timmesfeld.ARS.ExclNS

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}


theorem frame_cases_fine [Finite X] (F : NSLFrameData X (rootSet D)) (hD : RootClass X D)
    (hA : A2Action D Q ρ) :
    (∃ n, 3 ≤ n ∧ LieModel X .PSp n 2 1) ∨ (∃ n, 4 ≤ n ∧ LieModel X .POmegaMinus n 2 1) ∨
      ∃ (K' : Type) (_ : Field K') (_ : Finite K'), Nat.card K' = 2 ∧
        Nonempty (↥(adjointGroup .G2 K') ≃* X) := by
  have h := hD.arsHyp
  have hZ := hD.2.2.1
  have hRD : ∀ E ∈ rootSet D, ∃ d ∈ D, E = Subgroup.zpowers d := fun E hE => hE
  have hX : Nat.card (F.D.rootGroup (Pi.single F.i₀ 1)) = 2 :=
    (Frame.card_map_rootGroup_single F F.i₀).symm.trans (hD.card_eq_two _ F.mem)
  have hL : ∀ {t : StatedLieTag} {n p f : ℕ},
      LieModel (F.K ⧸ Subgroup.center F.K) t n p f → LieModel X t n p f :=
    fun h => Frame.lieModel_of_centerQuotient F hZ h
  have he := Frame.centerQuotientEquiv F hZ
  have hE6 : (F.D.rank = Tag.rank .F4 ∧ HEq F.D.cartan (Tag.cartan .F4)) → ∀ {f : ℕ}, 1 ≤ f →
      LieModel X .twistedE6 0 2 f → False := fun hF4 f hf hm => by
    obtain rfl := hD.eq_one_of_lieModel (by decide) hf hm
    exact FrF.false_of_nslFrame_lieModel F hF4 h.root h.noIsolated hRD hD.conj_mem hA (Or.inr hm)
  obtain ⟨K, D', nW, H, hct, hext, hdiv, i₀, type, pg, Ψ, surj, ker, mem, opp, comm, conc⟩ := F
  dsimp only at hX hL he hE6 ⊢
  cases conc with
  | symplectic n F' =>
    have hn : 3 ≤ n := Frame.three_le_of_nslType_cartanC (n := n) type
    have hF : Nat.card F' = 2 := (Frame.card_rootGroup_symplectic n F' i₀).symm.trans hX
    have : Finite F' := Nat.finite_of_card_ne_zero (by omega)
    have hadm : StatedLieAdmissible .PSp n 2 1 :=
      ⟨Nat.prime_two, le_rfl, by omega, fun h => by simp only [Prod.mk.injEq] at h; omega⟩
    exact Or.inl ⟨n, hn, hL (Or.inl ⟨by decide,
      Symplectic.statedClassicalModel_center_quotient n F' hadm (by rw [hF]; norm_num)⟩)⟩
  | @minus n K' _ b c hirr =>
    obtain ⟨hm, hi₀⟩ := Frame.of_nslType_cartanB (m := n - 1) type
    have hK : Nat.card K' = 2 := (Frame.card_rootGroup_minus n hirr hi₀).symm.trans hX
    have : Finite K' := Nat.finite_of_card_ne_zero (by omega)
    have hadm : StatedLieAdmissible .POmegaMinus n 2 1 :=
      ⟨Nat.prime_two, le_rfl, show 4 ≤ n by omega⟩
    exact Or.inr (Or.inl ⟨n, by omega, hL (Or.inl ⟨by decide,
      Spin.statedClassicalModel_spin_quadMinus hadm (by rw [hK]; norm_num) hirr⟩)⟩)
  | g2 K' =>
    have hK : Nat.card K' = 2 := (Frame.card_rootGroup_g2 K' i₀).symm.trans hX
    have : Finite K' := Nat.finite_of_card_ne_zero (by omega)
    have hinj : Function.Injective Ψ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      refine eq_bot_iff.mpr (ker.trans ?_)
      rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot]
    exact Or.inr (Or.inr ⟨K', inferInstance, this, hK,
      ⟨MulEquiv.ofBijective Ψ ⟨hinj, surj⟩⟩⟩)
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


theorem hub_any_fine [Finite X] (hD : RootClass X D) (hA : A2Action D Q ρ) :
    (∃ m, 3 ≤ m ∧ LieModel X .PSL m 2 1) ∨ (∃ m, 4 ≤ m ∧ LieModel X .POmegaPlus m 2 1) ∨
      (∃ n, 3 ≤ n ∧ LieModel X .PSp n 2 1) ∨ (∃ n, 4 ≤ n ∧ LieModel X .POmegaMinus n 2 1) ∨
      LieModel X .PSU 3 3 1 ∨
      ∃ (K' : Type) (_ : Field K') (_ : Finite K'), Nat.card K' = 2 ∧
        Nonempty (↥(adjointGroup .G2 K') ≃* X) := by
  have h := hD.arsHyp
  have hR := h.root
  have hiso := h.noIsolated
  have hZ := h.center
  have h2 := hD.card_eq_two
  have hRD : ∀ E ∈ rootSet D, ∃ d ∈ D, E = Subgroup.zpowers d := fun E hE => hE
  have hDc := hD.conj_mem
  have hf1 : ∀ {f : ℕ} {E : Subgroup X}, E ∈ rootSet D → Nat.card E = 2 ^ f → f = 1 :=
    fun hE hc => Nat.pow_right_injective le_rfl ((hc.symm.trans (h2 _ hE)).trans (pow_one 2).symm)
  rcases arsOutputPlus_of_card_eq_two h h2 with ⟨m, hm, A, B, hX, hgen⟩ |
      ⟨m, hm, A, B, hX, hgen⟩ | ⟨A, B, hX, -⟩ | ⟨A, B, hX, -⟩ | ⟨A, B, hX, -⟩ | ⟨-, ⟨F⟩⟩ |
      ⟨-, hm⟩ | hm
  · rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
    · obtain ⟨f, -, hcard, hL⟩ := hX.lieModel_A_two hR hiso hZ hgen
      obtain rfl := hf1 (hX.memA 0) (hcard _ (hX.memA 0))
      exact Or.inl ⟨3, le_rfl, hL⟩
    · obtain ⟨f, -, hcard, hL⟩ := hX.lieModel_A hR hiso hZ hm3 hgen
      obtain rfl := hf1 (hX.memA ⟨0, by omega⟩) (hcard _ (hX.memA ⟨0, by omega⟩))
      exact Or.inl ⟨m + 1, by omega, hL⟩
  · obtain ⟨f, -, hcard, hL⟩ := hX.lieModel_D hR hiso hZ hm hgen
    obtain rfl := hf1 (hX.memA ⟨0, by omega⟩) (hcard _ (hX.memA ⟨0, by omega⟩))
    exact Or.inr (Or.inl ⟨m, hm, hL⟩)
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · rcases frame_cases_fine F hD hA with hC | hB | hG
    · exact Or.inr (Or.inr (Or.inl hC))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hB)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hG))))
  · exact (hD.not_lieModel_trialityD4 hA hm).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))


end CFSG.LargeExtraspecial.A2Mod
