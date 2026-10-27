module

public import CFSG.LargeExtraspecial.A2ModFrB4Swap
public import CFSG.LargeExtraspecial.A2ModNaturalHub

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod.FrB

open Module CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.RankThree.OrthogonalInvolutions CFSG.Blueprint

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}
  {n : ℕ} {K : Type} [Field K] [Finite K] {b c : K}

theorem frame_finrank_commSpaceOf_top_le_eight (hDc : ∀ g, ∀ e ∈ D, g * e * g⁻¹ ∈ D)
    (hA : A2Action D Q ρ) (hn : n = 4) (hK : Nat.card K = 2)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (Ψ : spinGroup (quadMinus n K b c) →* X)
    (hsurj : Function.Surjective Ψ) {i₀ : Fin (n - 1)} (hi₀ : i₀.val + 1 < n - 1) {d : X}
    (hd : d ∈ D)
    (hmem : ((minusDatum n hirr).rootGroup (Pi.single i₀ 1)).map Ψ = Subgroup.zpowers d) :
    finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 8 := by
  subst hn
  have h := map_lr_eq_of_map_rootGroup hirr hK Ψ hi₀ (hA.ne_one hd) (hA.mul_self hd) hmem
  exact finrank_commSpaceOf_top_le_eight hirr hK Ψ hsurj hDc hA _ (h ▸ hd)

end CFSG.LargeExtraspecial.A2Mod.FrB

namespace CFSG.LargeExtraspecial.A2Mod

open Module CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.Blueprint
open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley CFSG.Timmesfeld.ARS.ExclNS
open CFSG.Open Matrix

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}


theorem frame_finrank_le_eight_of_lieModel [Finite X] (F : NSLFrameData X (rootSet D))
    (hD : RootClass X D) (hA : A2Action D Q ρ) (hL : LieModel X .POmegaMinus 4 2 1) :
    finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 8 := by
  have h := hD.arsHyp
  have hZ := hD.2.2.1
  have hRD : ∀ E ∈ rootSet D, ∃ d ∈ D, E = Subgroup.zpowers d := fun E hE => hE
  have hX : Nat.card (F.D.rootGroup (Pi.single F.i₀ 1)) = 2 :=
    (Frame.card_map_rootGroup_single F F.i₀).symm.trans (hD.card_eq_two _ F.mem)
  have hLc : ∀ {t : StatedLieTag} {n p f : ℕ},
      LieModel (F.K ⧸ Subgroup.center F.K) t n p f → LieModel X t n p f :=
    fun h => Frame.lieModel_of_centerQuotient F hZ h
  have he := Frame.centerQuotientEquiv F hZ
  have hle : Finite F.K → Nat.card X ≤ Nat.card F.K := fun _ =>
    Nat.card_le_card_of_surjective F.Ψ F.surj
  have hE6 : (F.D.rank = Tag.rank .F4 ∧ HEq F.D.cartan (Tag.cartan .F4)) → ∀ {f : ℕ}, 1 ≤ f →
      LieModel X .twistedE6 0 2 f → False := fun hF4 f hf hm => by
    obtain rfl := hD.eq_one_of_lieModel (by decide) hf hm
    exact FrF.false_of_nslFrame_lieModel F hF4 h.root h.noIsolated hRD hD.conj_mem hA (Or.inr hm)
  have hbig : 12096 < Nat.card X :=
    Ord.twelve_thousand_lt_card_of_lieModel_classical (Or.inr (Or.inr (Or.inr hL)))
  obtain ⟨d, hd, hdA⟩ := hRD _ F.mem
  obtain ⟨K, D', nW, H, hct, hext, hdiv, i₀, type, pg, Ψ, surj, ker, mem, opp, comm, conc⟩ := F
  dsimp only at hX hLc he hle hE6 hdA ⊢
  cases conc with
  | symplectic n F' =>
    have hn : 3 ≤ n := Frame.three_le_of_nslType_cartanC (n := n) type
    have hF : Nat.card F' = 2 := (Frame.card_rootGroup_symplectic n F' i₀).symm.trans hX
    have : Finite F' := Nat.finite_of_card_ne_zero (by omega)
    have hadm : StatedLieAdmissible .PSp n 2 1 :=
      ⟨Nat.prime_two, le_rfl, by omega, fun h => by simp only [Prod.mk.injEq] at h; omega⟩
    exact (Ord.lieModel_PSp_false_of_POmega (hLc (Or.inl ⟨by decide,
      Symplectic.statedClassicalModel_center_quotient n F' hadm (by rw [hF]; norm_num)⟩))
      (Or.inr hL)).elim
  | @minus n K' _ b c hirr =>
    obtain ⟨hm, hi₀⟩ := Frame.of_nslType_cartanB (m := n - 1) type
    have hK : Nat.card K' = 2 := (Frame.card_rootGroup_minus n hirr hi₀).symm.trans hX
    have : Finite K' := Nat.finite_of_card_ne_zero (by omega)
    have hadm : StatedLieAdmissible .POmegaMinus n 2 1 :=
      ⟨Nat.prime_two, le_rfl, show 4 ≤ n by omega⟩
    have hLn : LieModel X .POmegaMinus n 2 1 := hLc (Or.inl ⟨by decide,
      Spin.statedClassicalModel_spin_quadMinus hadm (by rw [hK]; norm_num) hirr⟩)
    have hn4 : n = 4 := Ord.eq_of_lieModel_POmega (Or.inr hLn) (Or.inr hL)
    exact FrB.frame_finrank_commSpaceOf_top_le_eight hD.conj_mem hA hn4 hK hirr Ψ surj hi₀ hd
      hdA
  | g2 K' =>
    have hK : Nat.card K' = 2 := (Frame.card_rootGroup_g2 K' i₀).symm.trans hX
    have : Finite K' := Nat.finite_of_card_ne_zero (by omega)
    have hcard : Nat.card (adjointGroup .G2 K') = 12096 := by
      rw [Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK]
      decide
    have : Finite (adjointGroup .G2 K') := Nat.finite_of_card_ne_zero (by omega)
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
      (hLc (CurtisTits.curtisTitsConclusion_twistedE6.{0} 2 f hadm).1.2.2)).elim

theorem finrank_commSpaceOf_top_le_eight_of_lieModel [Finite X] (hD : RootClass X D)
    (hA : A2Action D Q ρ) (hL : LieModel X .POmegaMinus 4 2 1) :
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
  have hbig : 12096 < Nat.card X :=
    Ord.twelve_thousand_lt_card_of_lieModel_classical (Or.inr (Or.inr (Or.inr hL)))
  rcases arsOutputPlus_of_card_eq_two h h2 with ⟨m, hm, A, B, hX, hgen⟩ | ⟨m, hm, A, B, hX, hgen⟩ |
      ⟨A, B, hX, -⟩ | ⟨A, B, hX, -⟩ | ⟨A, B, hX, -⟩ | ⟨-, ⟨F⟩⟩ | ⟨-, hm⟩ | hm
  · exfalso
    rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
    · obtain ⟨f, -, hcard, hL'⟩ := hX.lieModel_A_two hR hiso hZ hgen
      obtain rfl := hf1 (hX.memA 0) (hcard _ (hX.memA 0))
      exact Ord.lieModel_PSL_false_of_POmega hL' (Or.inr hL)
    · obtain ⟨f, -, hcard, hL'⟩ := hX.lieModel_A hR hiso hZ hm3 hgen
      obtain rfl := hf1 (hX.memA ⟨0, by omega⟩) (hcard _ (hX.memA ⟨0, by omega⟩))
      exact Ord.lieModel_PSL_false_of_POmega hL' (Or.inr hL)
  · exfalso
    obtain ⟨f, -, hcard, hL'⟩ := hX.lieModel_D hR hiso hZ hm hgen
    obtain rfl := hf1 (hX.memA ⟨0, by omega⟩) (hcard _ (hX.memA ⟨0, by omega⟩))
    obtain rfl := Ord.eq_of_lieModel_POmega (Or.inl hL') (Or.inr hL)
    have e := (Ord.card_of_lieModel_POmegaPlus hL').2.symm.trans
      (Ord.card_of_lieModel_POmegaMinus hL).2
    revert e
    decide
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · exact (typeE_false_of_isConfig hR hiso hRD hDc hA (by norm_num) hX).elim
  · exact frame_finrank_le_eight_of_lieModel F hD hA hL
  · exact (hD.not_lieModel_trialityD4 hA hm).elim
  · rw [Ord.card_of_lieModel_PSU33 hm] at hbig
    omega

theorem exists_natural_pOmegaMinus [Finite X] (hD : RootClass X D) (hA : A2Action D Q ρ)
    {m : ℕ} (hm : 4 ≤ m) (hL : LieModel X .POmegaMinus m 2 1) :
    ∃ (φ : X ≃* ↥(StatedOmega (StatedQuadMinus m (ZMod 2) 1 1)))
      (π : V →ₗ[ZMod 2] (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2)),
      (commSpaceOf ρ ⊤).map π = ⊤ ∧ commSpaceOf ρ ⊤ ⊓ LinearMap.ker π = ⊥ ∧
      (∀ x, ∀ v ∈ commSpaceOf ρ ⊤, π (ρ x v) =
        ((φ x : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
            (ZMod 2)) *ᵥ π v) ∧
      (∀ v ∈ commSpaceOf ρ ⊤, StatedQuadMinus m (ZMod 2) 1 1 (π v) = Q v) := by
  rcases (show m = 4 ∨ 5 ≤ m by omega) with rfl | hm5
  · exact exists_natural_pOmegaMinus_of_finrank_le hD hA hm hL
      (finrank_commSpaceOf_top_le_eight_of_lieModel hD hA hL)
  · exact exists_natural_pOmegaMinus_of_five_le hD hA hm5 hL

end CFSG.LargeExtraspecial.A2Mod
