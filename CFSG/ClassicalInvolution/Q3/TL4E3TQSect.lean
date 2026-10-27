module

public import CFSG.ClassicalInvolution.Q3.TL4E3TQ
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.LiftTransfer
public import CFSG.ClassicalInvolution.Q3.Q3T7SectB
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmA

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.Blueprint

namespace TQ

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem lieModel_quot_center_of_surj {K : Type} [Group K] (hK : CFSG.Open.IsQuasisimple K)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p e : ℕ}
    (hL : LieModel (K ⧸ Subgroup.center K) t n p e) (ψ : K →* Y) (hψ : Function.Surjective ψ)
    (hY : ∃ a b : Y, a * b ≠ b * a) : LieModel (Y ⧸ Subgroup.center Y) t n p e := by
  classical
  set φ : K →* Y ⧸ Subgroup.center Y := (QuotientGroup.mk' (Subgroup.center Y)).comp ψ with hφd
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hψ
  have hZle : Subgroup.center K ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hφd, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := hψ y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx k]
  have hker : φ.ker = Subgroup.center K := by
    refine le_antisymm ?_ hZle
    have hs : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2
    have hn : (φ.ker.map (QuotientGroup.mk' (Subgroup.center K))).Normal :=
      (MonoidHom.normal_ker φ).map _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (φ.ker.map (QuotientGroup.mk' (Subgroup.center K))) with h | h
    · intro x hx
      have hx' : QuotientGroup.mk' (Subgroup.center K) x ∈
          φ.ker.map (QuotientGroup.mk' (Subgroup.center K)) := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
      exact hx'
    · exfalso
      have htop : ∀ x : K, x ∈ φ.ker := by
        intro x
        have hx : QuotientGroup.mk' (Subgroup.center K) x ∈
            φ.ker.map (QuotientGroup.mk' (Subgroup.center K)) := h ▸ Subgroup.mem_top _
        obtain ⟨y, hy, hyx⟩ := hx
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
        have h1 := φ.ker.mul_mem hy (hZle hyx)
        rwa [mul_inv_cancel_left] at h1
      obtain ⟨a, b, hab⟩ := hY
      apply hab
      have ha : QuotientGroup.mk' (Subgroup.center Y) a = 1 := by
        obtain ⟨k, hk⟩ := hφ (QuotientGroup.mk' (Subgroup.center Y) a)
        rw [← hk]
        exact (MonoidHom.mem_ker).mp (htop k)
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha
      exact (Subgroup.mem_center_iff.mp ha b).symm
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)) hL

section Cit3

omit [Finite Y] in
theorem centOmega3_of_hasOrthTypeU {Λ : Set (Subgroup Y)} (hgen : omegaGen Λ = ⊤)
    (hY : ∃ a b : Y, a * b ≠ b * a) {d : ℕ} {ε : Bool} (h : HasOrthTypeU 3 1 Λ d ε) :
    CentOmega3 Y := by
  obtain ⟨t, k, hOrth, D, hcard, i, e, he, hft, hadm, hc⟩ := h
  have he1 : e = 1 := by rcases he with h | ⟨-, h⟩ <;> omega
  subst he1
  have hsurj : Function.Surjective (castHom hc (D.hom i)) := by
    have h := Q3.Q3T7.hom_surjective_of_gen3 D hcard hgen i
    rw [← MonoidHom.range_eq_top] at h ⊢
    rw [range_castHom]
    exact h
  obtain ⟨hq, hLie⟩ := ModelFacts.modelClauseZero t k 3 1 Nat.prime_three hft hadm
  have hM := lieModel_quot_center_of_surj hq hLie (castHom hc (D.hom i)) hsurj hY
  unfold CentOmega3
  rcases hOrth with ⟨-, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨hd7, -, rfl, hk⟩ |
      ⟨hd8, -, -, rfl, hk⟩ | ⟨hd8, -, -, rfl, hk⟩
  · exact Or.inl hM
  · exact Or.inr (Or.inl hM)
  · exact Or.inr (Or.inr (Or.inl hM))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, by omega, hM⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, by omega, hM⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, by omega, hM⟩))))

theorem centOmega3_of_hasLift {n : ℕ} (hA : CIT3Below n) (hlt : Nat.card Y < n)
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} (hd : PhilipHall.QuaternionBridge.Q8TwinDatum R S t)
    (hg : TightSelfGen R) (hO : TightOddFree Y)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hAE : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (htw : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      K' ≠ tightCore R)
    (hL : TightHasLift R t) : CentOmega3 Y := by
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
  obtain ⟨d, ε, -, hT⟩ := Q3.Q3T7.thm7SectBelowU_of hcit Y hlt _ hTS _ hM₀Λ
    ⟨_, ⟨hM'Λ, t, hM₀t, hM't⟩, hne⟩
  have hY : ∃ a b : Y, a * b ≠ b * a := by
    obtain ⟨P, -, hnc⟩ := (hΩ.omega1 _ hK₀Δ).2
    by_contra hc
    push Not at hc
    exact hnc ⟨⟨fun a b => Subtype.ext (hc a b)⟩⟩
  exact centOmega3_of_hasOrthTypeU hgenΛ hY hT

theorem centOmega3_of_longFundSet3 {n : ℕ} (hA : CIT3Below n) (hlt : Nat.card Y < n)
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} (hd : PhilipHall.QuaternionBridge.Q8TwinDatum R S t)
    (hg : TightSelfGen R) (hO : TightOddFree Y)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hAE : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (htw : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      K' ≠ tightCore R)
    (hL : LongFundSet3 R t) : CentOmega3 Y :=
  centOmega3_of_hasLift hA hlt hd hg hO hΩ hAE htw (hL.hasLift htw)

end Cit3

end TQ

section Cit3

theorem twinSectSetType3 (n : ℕ) : CIT3Below n → PhilipHall.Frame.Thm1RTwinLiftSetBelow n → Thm1RTwinSetBelow n := by
  intro hA hlift Y _ _ hlt R S t hd hq hg hO hΩ hAE htw
  rcases hlift Y hlt R S t hd hq hg hO hΩ hAE htw with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨TQ.centOmega3_of_longFundSet3 hA hlt hd hg hO hΩ hAE htw h, h⟩)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
