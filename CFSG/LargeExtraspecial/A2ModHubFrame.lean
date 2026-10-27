module

public import CFSG.LargeExtraspecial.A2ModHub
public import CFSG.LargeExtraspecial.A2ModFrCFrame
public import CFSG.LargeExtraspecial.A2ModFrBFinal
public import CFSG.LargeExtraspecial.A2ModFrFAdj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod

open Module CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.Blueprint
open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley CFSG.Timmesfeld.ARS.ExclNS

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

section Frames


theorem RootClass.false_of_twistedD4 [Finite X] (hD : RootClass X D) (hA : A2Action D Q ρ)
    {f : ℕ} (hf : 1 ≤ f)
    (e : Steinberg.TwistedD4.twistedGroup (iterateFrobenius (GaloisField 2 (3 * f)) 2 f) ⧸
      Subgroup.center
        (Steinberg.TwistedD4.twistedGroup (iterateFrobenius (GaloisField 2 (3 * f)) 2 f)) ≃*
      X) : False := by
  have hK : Nat.card (GaloisField 2 (3 * f)) = (2 ^ f) ^ 3 := by
    rw [GaloisField.card 2 (3 * f) (by omega), ← pow_mul, mul_comm]
  have hm := Frame.lieModel_trialityD4_of_twistedGroup hf hK (fun c => iterateFrobenius_def 2 f c)
    e
  obtain rfl := hD.eq_one_of_lieModel (by decide) hf hm
  exact hD.not_lieModel_trialityD4 hA hm

theorem frame_cases [Finite X] (F : NSLFrameData X (rootSet D)) (hD : RootClass X D)
    (hA : A2Action D Q ρ) :
    (∃ n, 3 ≤ n ∧ LieModel X .PSp n 2 1) ∨ (∃ n, 4 ≤ n ∧ LieModel X .POmegaMinus n 2 1) ∨
      Nat.card X ≤ 12096 := by
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
  obtain ⟨K, D', nW, H, hct, hext, hdiv, i₀, type, pg, Ψ, surj, ker, mem, opp, comm, conc⟩ := F
  dsimp only at hX hL he hle hE6 ⊢
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
    have hcard : Nat.card (adjointGroup .G2 K') = 12096 := by
      rw [Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK]
      decide
    have : Finite (adjointGroup .G2 K') := Nat.finite_of_card_ne_zero (by omega)
    exact Or.inr (Or.inr (hcard ▸ hle this))
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

theorem frame_cases_irr [Finite X] (F : NSLFrameData X (rootSet D)) (hD : RootClass X D)
    (hA : A2Action D Q ρ)
    (hirr : ∀ W : Submodule (ZMod 2) V, (∀ x, ∀ w ∈ W, ρ x w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hV : 10 ≤ finrank (ZMod 2) V) :
    (∃ n, 5 ≤ n ∧ finrank (ZMod 2) V = 2 * n ∧ LieModel X .POmegaMinus n 2 1) ∨
      Nat.card X ≤ 12096 := by
  have h := hD.arsHyp
  have hZ := hD.2.2.1
  have hRD : ∀ E ∈ rootSet D, ∃ d ∈ D, E = Subgroup.zpowers d := fun E hE => hE
  obtain ⟨d, hd, hdA⟩ := F.mem
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
  have hfalse : F.D.cartan = Symplectic.cartanC F.D.rank → False := fun hC =>
    FrC.frame_false_of_cartan_eq F hC (fun A hA => hA) hD hA hirr hV
  obtain ⟨K, D', nW, H, hct, hext, hdiv, i₀, type, pg, Ψ, surj, ker, mem, opp, comm, conc⟩ := F
  dsimp only at hX hL he hle hE6 hfalse hdA ⊢
  cases conc with
  | symplectic n F' => exact (hfalse rfl).elim
  | @minus n K' _ b c hirr' =>
    obtain ⟨hm, hi₀⟩ := Frame.of_nslType_cartanB (m := n - 1) type
    have hK : Nat.card K' = 2 := (Frame.card_rootGroup_minus n hirr' hi₀).symm.trans hX
    have : Finite K' := Nat.finite_of_card_ne_zero (by omega)
    obtain ⟨h5, hdim, hmod⟩ := FrB.frame_irreducible_of_ten_le hD.conj_mem hA hirr hV
      (by omega) hK hirr' Ψ surj ker hZ hi₀ hd hdA
    exact Or.inl ⟨n, h5, hdim, hmod⟩
  | g2 K' =>
    have hK : Nat.card K' = 2 := (Frame.card_rootGroup_g2 K' i₀).symm.trans hX
    have : Finite K' := Nat.finite_of_card_ne_zero (by omega)
    have hcard : Nat.card (adjointGroup .G2 K') = 12096 := by
      rw [Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK]
      decide
    have : Finite (adjointGroup .G2 K') := Nat.finite_of_card_ne_zero (by omega)
    exact Or.inr (hcard ▸ hle this)
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

end Frames

end CFSG.LargeExtraspecial.A2Mod
