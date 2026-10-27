module

public import CFSG.CGT.PushingUpLit.CGT6.SixTwoJ
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightHolds

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin
open CFSG.CGT.PushingUpLit.CGT6
open CFSG.QuasithinUnique.Setup.Campbell (elemFamilyIn mem_elemFamilyIn elemThompsonIn_eq
  card_le_pow_pRank_of_le)
open scoped commutatorElement

variable {L : Type} [Group L] [Finite L]

theorem isMaxElemAbelian_of_mem_elemFamilyIn {T B : Subgroup L} (hB : B ∈ elemFamilyIn 2 T) :
    IsMaxElemAbelian T B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBT, hBe, hBc⟩ := mem_elemFamilyIn.mp hB
  refine ⟨hBT, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 B).mp hBe,
    fun E hET hEe => ?_⟩
  rw [hBc]
  exact card_le_pow_pRank_of_le hET
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).mpr hEe)

theorem le_normalizer_jIn_of_commutator_le {T X : Subgroup L}
    (h : ∀ B ∈ elemFamilyIn 2 T, ⁅B, X⁆ ≤ T) :
    X ≤ Subgroup.normalizer ((jIn T : Subgroup L) : Set L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ x ∈ X, ∀ j ∈ jIn T, x * j * x⁻¹ ∈ jIn T := by
    intro x hx j hj
    rw [jIn_eq_elemThompsonIn, elemThompsonIn_eq] at hj ⊢
    have hle : sSup (elemFamilyIn 2 T) ≤
        (sSup (elemFamilyIn 2 T)).comap (MulAut.conj x).toMonoidHom := by
      refine sSup_le fun B hB => ?_
      obtain ⟨hBT, hBe, hBc⟩ := mem_elemFamilyIn.mp hB
      rw [← Subgroup.map_le_iff_le_comap]
      refine le_sSup (mem_elemFamilyIn.mpr ⟨?_, ?_, ?_⟩)
      · rintro _ ⟨b, hb, rfl⟩
        have hc : ⁅x, b⁆ ∈ T := h B hB (by
          rw [Subgroup.commutator_comm]
          exact Subgroup.commutator_mem_commutator hx hb)
        have e : (MulAut.conj x).toMonoidHom b = ⁅x, b⁆ * b := by
          simp [commutatorElement_def, MulAut.conj_apply]
        rw [e]
        exact T.mul_mem hc (hBT hb)
      · exact BlueprintB2.isElementaryAbelian_map hBe _
      · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
        exact hBc
    exact hle hj
  intro x hx
  refine Subgroup.mem_normalizer_iff.mpr fun j => ⟨key x hx j, fun hj => ?_⟩
  simpa [mul_assoc] using key x⁻¹ (X.inv_mem hx) _ hj

theorem commutator_le_oTwoIn_of_isMaxElemAbelian {V Y X T B : Subgroup L} [V.Normal]
    (hV : CFSG.Open.IsElemAbelian 2 V) (hΩ : OmegaFourOutcome V Y X) (hYX : Y ≤ X)
    (hXs : X.IsSubnormal)
    (hCX : Subgroup.centralizer (V : Set L) ≤ Subgroup.normalizer (X : Set L))
    (hN0 : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set L)))
    (hCY : Subgroup.centralizer (V : Set L) ≤ centralizerModCore Y) (hY : InClassX ↥Y)
    (hYV : ¬ Y ≤ Subgroup.centralizer (V : Set L)) (hVT : V ≤ T) (hB : IsMaxElemAbelian T B) :
    B ≤ Subgroup.normalizer (X : Set L) ∧ ⁅B, X⁆ ≤ oTwoIn X := by
  obtain ⟨hXC', hP1, -⟩ :=
    sixTwoOmegaInput_of_twoEight aschbacherTwoEight_holds L V Y X hV hΩ hYX hXs hCX hN0 hCY hY hYV
  by_cases hBC : B ≤ Subgroup.centralizer (V : Set L)
  · exact ⟨hBC.trans hCX, commutator_le_oTwoIn_of_le_centralizer hXC' (hBC.trans hCX) hBC⟩
  have hXV : X ≤ Subgroup.normalizer (V : Set L) := by
    rw [Subgroup.normalizer_eq_top V]
    exact le_top
  have hOff : IsOffG V B := isOffG_of_isMaxElemAbelian hV hVT
    (by rw [Subgroup.normalizer_eq_top V]; exact le_top) hB hBC
  have hBN : B ≤ Subgroup.normalizer (X : Set L) := hP1 B hOff
  refine ⟨hBN, ?_⟩
  obtain ⟨-, -, n, hn2, hnat, hC0, hker, -⟩ := hΩ
  have hWV : (⁅X, V⁆ : Subgroup L) ≤ V := Subgroup.commutator_le_right X V
  have hker' : X ⊓ Subgroup.centralizer (V : Set L) =
      X ⊓ Subgroup.centralizer ((⁅X, V⁆ : Subgroup L) : Set L) :=
    le_antisymm (inf_le_inf_left X (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hWV)))
      (le_inf inf_le_left hker)
  obtain ⟨-, hcomp⟩ := omega_data hV hXs hn2 hnat hker
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV.2 v v.2)
  have hoff : IsOff (autOn B V) := (isOffG_iff_isOff_autOn hV hOff.1).mp hOff
  have hfac : ∀ w ∈ (⁅X, V⁆ : Subgroup L), ∃ p ∈ (⁅X, V⁆ : Subgroup L),
      ∃ c ∈ (⁅X, V⁆ : Subgroup L) ⊓ Subgroup.centralizer (X : Set L), w = p * c :=
    fun w hw => ⟨w, hw, 1, one_mem _, (mul_one w).symm⟩
  have hZ : commV (autOn X V) ⊓ fixV (autOn X V) = ⊥ := by
    have h1 : commOn hV X ⊓ fixOn hV X =
        (⁅X, V⁆ ⊓ Subgroup.centralizer (X : Set L)).subgroupOf V := by
      rw [commOn_eq hV hXV, fixOn_eq hV hXV]
      exact (Subgroup.comap_inf _ _ _).symm
    rw [hC0, Subgroup.bot_subgroupOf] at h1
    exact h1
  have hbot : ⁅autOn X V, autOn B V⁆ = ⊥ := by
    rcases hnat with hplus | hminus
    · exact aschbacherTwoEight_holds ↥V hV2 (autOn X V) (autOn B V) n hn2 (hcomp B hOff) hoff
        (Or.inl (isNatSectionBy_autOn hV hXV hplus le_rfl hfac hker')) hZ
    · exact aschbacherTwoEight_holds ↥V hV2 (autOn X V) (autOn B V) n hn2 (hcomp B hOff) hoff
        (Or.inr (isNatSectionBy_autOn hV hXV hminus le_rfl hfac hker')) hZ
  refine Subgroup.commutator_le.mpr fun a ha x hx => ?_
  refine hXC'.inf_le_oTwoIn (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
  · rw [commutatorElement_def]
    exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hBN ha) x).mp hx) (X.inv_mem hx)
  · have hBV : B ≤ Subgroup.normalizer (V : Set L) := hOff.1
    have h1 : conjAct V ⟨a, hBV ha⟩ ∈ autOn B V := mem_autOn_iff.mpr ⟨⟨a, hBV ha⟩, ha, rfl⟩
    have h2 : conjAct V ⟨x, hXV hx⟩ ∈ autOn X V := mem_autOn_iff.mpr ⟨⟨x, hXV hx⟩, hx, rfl⟩
    have h3 := Subgroup.commutator_mem_commutator h2 h1
    rw [hbot, Subgroup.mem_bot, ← map_commutatorElement] at h3
    have h4 := (conjAct_eq_one_iff V _).mp h3
    rw [← commutatorElement_inv x a]
    exact (Subgroup.centralizer (V : Set L)).inv_mem h4

theorem le_normalizer_jIn_of_omegaFourOutcome {V Y X T : Subgroup L} [V.Normal]
    (hV : CFSG.Open.IsElemAbelian 2 V) (hΩ : OmegaFourOutcome V Y X) (hYX : Y ≤ X)
    (hXs : X.IsSubnormal)
    (hCX : Subgroup.centralizer (V : Set L) ≤ Subgroup.normalizer (X : Set L))
    (hN0 : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set L)))
    (hCY : Subgroup.centralizer (V : Set L) ≤ centralizerModCore Y) (hY : InClassX ↥Y)
    (hYV : ¬ Y ≤ Subgroup.centralizer (V : Set L)) (hVT : V ≤ T) (hOT : oTwoIn X ≤ T) :
    X ≤ Subgroup.normalizer ((jIn T : Subgroup L) : Set L) :=
  le_normalizer_jIn_of_commutator_le fun _ hB =>
    (commutator_le_oTwoIn_of_isMaxElemAbelian hV hΩ hYX hXs hCX hN0 hCY hY hYV hVT
      (isMaxElemAbelian_of_mem_elemFamilyIn hB)).2.trans hOT

end CFSG.CGT.PushingUpLit.ThmOne
