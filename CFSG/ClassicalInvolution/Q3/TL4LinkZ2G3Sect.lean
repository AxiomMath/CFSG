module

public import CFSG.ClassicalInvolution.Q3.TL4E3TQSect
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G3Defs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.Blueprint

namespace TQ

variable {Y : Type} [Group Y] [Finite Y]

section Cit3

omit [Finite Y] in
theorem lieModel_of_hasOrthTypeU {Λ : Set (Subgroup Y)} (hgen : omegaGen Λ = ⊤)
    (hY : ∃ a b : Y, a * b ≠ b * a) {d : ℕ} {ε : Bool} (h : HasOrthTypeU 3 1 Λ d ε) :
    ∃ t k, IsOrthTag d ε t k ∧ CFSG.Blueprint.LieModel (Y ⧸ Subgroup.center Y) t k 3 1 := by
  obtain ⟨t, k, hOrth, D, hcard, i, e, he, hft, hadm, hc⟩ := h
  have he1 : e = 1 := by rcases he with h | ⟨-, h⟩ <;> omega
  subst he1
  have hsurj : Function.Surjective (castHom hc (D.hom i)) := by
    have h := Q3.Q3T7.hom_surjective_of_gen3 D hcard hgen i
    rw [← MonoidHom.range_eq_top] at h ⊢
    rw [range_castHom]
    exact h
  obtain ⟨hq, hLie⟩ := ModelFacts.modelClauseZero t k 3 1 Nat.prime_three hft hadm
  exact ⟨t, k, hOrth, lieModel_quot_center_of_surj hq hLie (castHom hc (D.hom i)) hsurj hY⟩

theorem orthFundCover_of_hasLift {n : ℕ} (hA : CIT3Below n) (hlt : Nat.card Y < n)
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} (hd : PhilipHall.QuaternionBridge.Q8TwinDatum R S t)
    (hg : TightSelfGen R) (hO : TightOddFree Y)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hAE : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (htw : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      K' ≠ tightCore R)
    (hL : TightHasLift R t) : ∃ d ε, 5 ≤ d ∧ Z2W.OrthFundCover Y (tightCore R) d ε := by
  classical
  have hu₀ : IsUniqueInvolution (tightCore R) t := Q8Datum.isUniqueInvolution_core hd
  obtain ⟨L₀, hle₀, hL₀⟩ := hL
  have hlift₀ : IsLiftOf (tightCore R) L₀ t := ⟨hu₀, hle₀, hL₀⟩
  have hl : HasLifts (CoreAssembly.conjClass (tightCore R)) := hasLifts_conjClass hu₀ hle₀ hL₀
  have hK₀Δ : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hM₀Λ : satU (.sl2 3 1) L₀ t ∈ liftFam (CoreAssembly.conjClass (tightCore R)) :=
    satU_mem_liftFam hK₀Δ hlift₀
  have hΛeq : liftFam (CoreAssembly.conjClass (tightCore R)) =
      CoreAssembly.conjClass (satU (.sl2 3 1) L₀ t) := liftFam_conjClass hΩ hlift₀
  have hΛ := hypOmegaModU_liftFam hΩ.conjInvariant
  have hgenΔ : (⨆ J ∈ CoreAssembly.conjClass (tightCore R), J) = ⊤ := by
    rw [iSup_conjClass_eq]
    exact hg
  have hIn := inClass3_liftFam hΩ.conjInvariant ⟨_, hK₀Δ⟩ hl hgenΔ
  have hgenΛ : omegaGen (liftFam (CoreAssembly.conjClass (tightCore R))) = ⊤ := hIn.generated
  have htrΛ : ∀ K ∈ liftFam (CoreAssembly.conjClass (tightCore R)),
      ∀ L ∈ liftFam (CoreAssembly.conjClass (tightCore R)), ∃ g : Y, conjSub g K = L := by
    rw [hΛeq]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    refine ⟨b * a⁻¹, ?_⟩
    show conjSub (b * a⁻¹) (conjSub a _) = conjSub b _
    rw [← conjSub_mul, inv_mul_cancel_right]
  have hcit : CITBelowT (.sl2 3 1) n := (citBelowT_three_iff (by norm_num) n).mpr hA
  obtain ⟨D, -⟩ := Q3.Q3T7.exists_omegaLieU_sect hcit hlt hΛ hO hgenΛ htrΛ ⟨_, hM₀Λ⟩
  have h24 : ∀ M ∈ liftFam (CoreAssembly.conjClass (tightCore R)), Nat.card ↥M = 24 :=
    D.card_eq (by norm_num)
  have hO24 : ∀ (M : Subgroup Y) (z : Y), IsClassicalMember3 M z → Nat.card ↥M = 24 →
      classicalInvolutionOddCore ↥M = ⊥ := by
    intro M z hMc hM24
    obtain ⟨e⟩ := hMc.nonempty_equiv
    have h1 : Nat.card (↥M ⧸ classicalInvolutionOddCore ↥M) = 24 := by
      rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field (𝔽 := ZMod 3) 2, ZMod.card,
        Fin.prod_univ_two]
      norm_num
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore ↥M)
    rw [hM24, h1] at h2
    have h3 : Nat.card ↥(classicalInvolutionOddCore ↥M) = 1 := by omega
    exact Subgroup.card_eq_one.mp h3
  have hex : ExactSylow (CoreAssembly.conjClass (tightCore R)) := by
    intro M hM P Q hP hQ
    have hc24 := h24 M hM
    obtain ⟨J, -, L, u, h, rfl⟩ := hM
    exact eq_of_isSylow2In_of_oddCore_eq_bot h.member_sat (hO24 _ _ h.member_sat hc24) hP hQ
  have hK₀2 : IsPGroup 2 ↥(tightCore R) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (P := satU (.sl2 3 1) L₀ t)
      (IsPGroup.of_bot (p := 2)) bot_le
    have hKP : tightCore R ≤ P := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨hxR, hx2⟩
      have hxM : x ∈ satU (.sl2 3 1) L₀ t :=
        le_satU (hle₀ (Subgroup.subset_closure ⟨hxR, hx2⟩))
      obtain ⟨Q, hQ, hxQ⟩ := IsSylow2In.exists_ge hx2 (Subgroup.zpowers_le.mpr hxM)
      rw [hex _ hM₀Λ P Q hP hQ]
      exact hxQ (Subgroup.mem_zpowers x)
    exact hP.2.1.to_le hKP
  have h2 : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J := by
    rintro _ ⟨g, rfl⟩
    exact hK₀2.map (MulAut.conj g).toMonoidHom
  have hAΔ : ∀ J ∈ CoreAssembly.conjClass (tightCore R),
      AEmpty (CoreAssembly.conjClass (tightCore R)) J := by
    rintro _ ⟨g, rfl⟩
    exact aEmpty_conj hΩ.conjInvariant hAE g
  have hAΛ := ExactSylow.aEmpty_liftFam hΩ h2 hl hex hAΔ
  have hTS : Q3.Q3T7.TransSect3 (liftFam (CoreAssembly.conjClass (tightCore R))) :=
    ⟨hΛ, hO, hgenΛ, htrΛ, hAΛ⟩
  obtain ⟨K', ⟨hK'Δ, z, hzK₀, hzK'⟩, hK'ne⟩ := htw
  have hzt : z = t := hzK₀.eq hu₀
  have hK't : IsUniqueInvolution K' t := hzt ▸ hzK'
  obtain ⟨L', u', h'⟩ := hl K' hK'Δ
  have hM'Λ := satU_mem_liftFam hK'Δ h'
  have hM₀t : IsUniqueInvolution (satU (.sl2 3 1) L₀ t) t :=
    isUniqueInvolution_liftFam_of_le hM₀Λ hu₀ hlift₀.le_sat
  have hM't : IsUniqueInvolution (satU (.sl2 3 1) L' u') t :=
    isUniqueInvolution_liftFam_of_le hM'Λ hK't h'.le_sat
  have hne : satU (.sl2 3 1) L' u' ≠ satU (.sl2 3 1) L₀ t := by
    intro heq
    apply hK'ne
    have hK'M₀ : K' ≤ satU (.sl2 3 1) L₀ t := by
      rw [← heq]
      exact h'.le_sat
    exact (ExactSylow.core_unique hΩ h2 hex hM₀Λ hK₀Δ hK'Δ hlift₀.le_sat hK'M₀).symm
  obtain ⟨d, ε, hd5, hT⟩ := Q3.Q3T7.thm7SectBelowU_of hcit Y hlt _ hTS _ hM₀Λ
    ⟨_, ⟨hM'Λ, t, hM₀t, hM't⟩, hne⟩
  refine ⟨d, ε, hd5, satU (.sl2 3 1) L₀ t, hlift₀.le_sat, ?_⟩
  rw [← hΛeq]
  exact hT

theorem orthFundCover_of_longFundSet3 {n : ℕ} (hA : CIT3Below n) (hlt : Nat.card Y < n)
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} (hd : PhilipHall.QuaternionBridge.Q8TwinDatum R S t)
    (hg : TightSelfGen R) (hO : TightOddFree Y)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hAE : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (htw : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      K' ≠ tightCore R)
    (hL : LongFundSet3 R t) : ∃ d ε, 5 ≤ d ∧ Z2W.OrthFundCover Y (tightCore R) d ε :=
  orthFundCover_of_hasLift hA hlt hd hg hO hΩ hAE htw (hL.hasLift htw)

end Cit3

end TQ

section Cit3

theorem twinSectSetFType3 (n : ℕ) (hA : CIT3Below n)
    (hlift : PhilipHall.Frame.Thm1RTwinLiftSetBelow n) :
    ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
      ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), PhilipHall.QuaternionBridge.Q8TwinDatum R S t →
        Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) → TightSelfGen R → TightOddFree Y →
        HypOmegaGen (CoreAssembly.conjClass (tightCore R)) →
        AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
        (∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
          K' ≠ tightCore R) →
        TightInO2 t ∨ PhilipHall.Frame.TwinE4 Y ∨
          (PhilipHall.Frame.CentOmega3 Y ∧
            (∃ d ε, 5 ≤ d ∧ Z2W.OrthFundCover Y (tightCore R) d ε) ∧
            PhilipHall.Frame.LongFundSet3 R t) := by
  intro Y _ _ hlt R S t hd hq hg hO hΩ hAE htw
  rcases hlift Y hlt R S t hd hq hg hO hΩ hAE htw with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨TQ.centOmega3_of_longFundSet3 hA hlt hd hg hO hΩ hAE htw h,
      TQ.orthFundCover_of_longFundSet3 hA hlt hd hg hO hΩ hAE htw h, h⟩)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
