module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27
public import CFSG.HardMathSupport.Solomon.Coordinator.B3RedAlg
public import CFSG.HardMathSupport.Timmesfeld.Balance.Basic
import CFSG.HardMathSupport.Timmesfeld.Balance.Moved
import CFSG.HardMathSupport.Timmesfeld.Balance.Normalizes
import CFSG.HardMathSupport.Timmesfeld.Balance.Faithful
import CFSG.HardMathSupport.Timmesfeld.Proving.MapGLAPPrimeCore
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_Normalizes
import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld
  CFSG.ClassicalInvolution.Balance.LocalBalance
open scoped commutatorElement

@[expose] def B3Quasi : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → GLAPPrimeCore 3 K = ⊥ →
    IsCatalogGroup (K ⧸ Subgroup.center K) → ∀ α : MulAut K, α ^ 3 = 1 →
      ⁅GLAPLayer 3 (MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id K)),
        GLAPPrimeCoreOf 3 (MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id K))⁆ = ⊥

theorem h1Stmt_holds : CFSG.HardMathSupport.Timmesfeld.Balance.H1Stmt.{0} := fun φ hφ _ hp _ hQ =>
  Proving.map_glaPPrimeCoreOf_centralizer_le φ hφ hp hQ

theorem openIsKGroup_of_subgroup {Y : Type} [Group Y] (hK : CFSG.IsKGroup Y) (X : Subgroup Y) :
    CFSG.Open.IsKGroup ↥X :=
  CFSG.KCore.KGroupAllSimple.kGroupNonab (hK.subgroup X)

theorem mem_normalizer_of_conjSub_eq {Y : Type*} [Group Y] {g : Y} {L : Subgroup Y}
    (h : conjSub g L = L) : g ∈ Subgroup.normalizer (L : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have := conj_mem_conjSub (g := g) hy
    rwa [h] at this
  · intro hy
    have h1 : g * y * g⁻¹ ∈ conjSub g L := by rw [h]; exact hy
    have := mem_conjSub_iff.1 h1
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rwa [e] at this

theorem glaPPrimeCore_eq_bot_of_isSubnormal {Y : Type} [Group Y] [Finite Y]
    (hO : GLAPPrimeCore 3 Y = ⊥) {L : Subgroup Y} (hL : IsSubnormal L ⊤) :
    GLAPPrimeCore 3 ↥L = ⊥ := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hN : IsSubnormal ((GLAPPrimeCore 3 ↥L).map L.subtype) ⊤ := by
    refine IsSubnormal.step (M := L) (Subgroup.map_subtype_le _) ?_ hL
    rw [show ((GLAPPrimeCore 3 ↥L).map L.subtype).subgroupOf L = GLAPPrimeCore 3 ↥L from
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective _]
    infer_instance
  have hcop : Nat.Coprime 3 (Nat.card ↥((GLAPPrimeCore 3 ↥L).map L.subtype)) := by
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore hp3 ↥L
  have := Balance.eq_bot_of_isSubnormal_coprime hp3 hO hN hcop
  exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 this

theorem caseA (hB : B3Quasi) {Y : Type} [Group Y] [Finite Y] (hK : CFSG.IsKGroup Y)
    (hO : GLAPPrimeCore 3 Y = ⊥) {x : Y} (hx3 : x ^ 3 = 1) {L : Subgroup Y}
    (hL : CFSG.IsComponent L) (hxL : conjSub x L = L) {J : Subgroup Y}
    (hJ : GLAPComponent 3 (Subgroup.centralizer ({x} : Set Y)) J) (hJL : J ≤ L) :
    ∀ g ∈ J, ∀ o ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set Y)), o * g = g * o := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set C : Subgroup Y := Subgroup.centralizer ({x} : Set Y) with hC
  have hLo := (CFSG.isComponent_iff_open L).1 hL
  have hLp : 3 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := Balance.p_dvd_card_center_quot hp3 hO hL
  have hOL : GLAPPrimeCore 3 ↥L = ⊥ := glaPPrimeCore_eq_bot_of_isSubnormal hO hLo.2.1
  have hLcat : IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) := hK L (Subgroup.center ↥L) hL.1.2.1
  have hxN : x ∈ Subgroup.normalizer (L : Set Y) := mem_normalizer_of_conjSub_eq hxL
  set C₁ : Subgroup Y := L ⊓ C with hC₁
  have hJC : J ≤ C := hJ.1
  have hJC₁ : J ≤ C₁ := le_inf hJL hJC
  have hJ₁ : GLAPComponent 3 C₁ J := glaPComponent_of_le hp3 hJ hJC₁ inf_le_right
  have hOn : ∀ o ∈ GLAPPrimeCoreOf 3 C, conjSub o L = L := fun o ho =>
    Balance.conjSub_eq_of_mem_gLAPPrimeCoreOf h1Stmt_holds hp3 hL hLp hx3 hxL ho
  let α : MulAut ↥L := Subgroup.normalizerMonoidHom L ⟨x, hxN⟩
  have hα : ∀ l : ↥L, ((α l : ↥L) : Y) = x * l * x⁻¹ := fun l => rfl
  have hα3 : α ^ 3 = 1 := by
    have : (⟨x, hxN⟩ : Subgroup.normalizer (L : Set Y)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    show (Subgroup.normalizerMonoidHom L ⟨x, hxN⟩) ^ 3 = 1
    rw [← map_pow, this, map_one]
  set F : Subgroup ↥L := MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id ↥L) with hF
  have hFmap : F.map L.subtype = C₁ := by
    ext y
    simp only [Subgroup.mem_map, hC₁, Subgroup.mem_inf, hC, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨l, hl, rfl⟩
      have h1 : x * (l : Y) * x⁻¹ = l := by
        have := congrArg Subtype.val (show α l = l from hl)
        rwa [hα] at this
      refine ⟨l.2, ?_⟩
      show (l : Y) * x = x * (l : Y)
      calc (l : Y) * x = (x * (l : Y) * x⁻¹) * x := by rw [h1]
        _ = x * (l : Y) := by group
    · rintro ⟨hyL, hyC⟩
      refine ⟨⟨y, hyL⟩, ?_, rfl⟩
      show α ⟨y, hyL⟩ = ⟨y, hyL⟩
      apply Subtype.ext
      rw [hα]
      show x * y * x⁻¹ = y
      calc x * y * x⁻¹ = (y * x) * x⁻¹ := by rw [← hyC]
        _ = y := by group
  have hres := hB ↥L hL.1 hOL hLcat α hα3
  have hcentF : ∀ k ∈ GLAPLayer 3 F, ∀ q ∈ GLAPPrimeCoreOf 3 F, q * k = k * q := by
    intro k hk q hq
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hres hk) q hq
  have hker : Nat.Coprime 3 (Nat.card ↥(F ⊓ L.subtype.ker)) := by
    rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right _
  have hJF : GLAPComponent 3 (F.map L.subtype) J := by rw [hFmap]; exact hJ₁
  obtain ⟨K, hK3, hKJ⟩ := exists_glaPComponent_map_eq hp3 L.subtype hker hJF
  have hOF : GLAPPrimeCoreOf 3 C₁ = (GLAPPrimeCoreOf 3 F).map L.subtype := by
    rw [← hFmap]
    exact (Coordinator.map_glaPPrimeCoreOf_of_injective 3 L.subtype L.subtype_injective F).symm
  have hcentJ : ∀ q ∈ GLAPPrimeCoreOf 3 C₁, ∀ j ∈ J, q * j = j * q := by
    intro q hq j hj
    rw [hOF] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    rw [← hKJ] at hj
    obtain ⟨k, hk, rfl⟩ := hj
    have hKl : K ≤ GLAPLayer 3 F := le_sSup hK3
    have := hcentF k (hKl hk) q' hq'
    exact congrArg Subtype.val this
  have hOcomm : ⁅J, GLAPPrimeCoreOf 3 C⁆ ≤ GLAPPrimeCoreOf 3 C₁ := by
    rw [Subgroup.commutator_le]
    intro j hj o ho
    have hjL : j ∈ L := hJL hj
    have hjC : j ∈ C := hJC hj
    have hSle : L ⊓ GLAPPrimeCoreOf 3 C ≤ GLAPPrimeCoreOf 3 C₁ := by
      refine Proving.le_GLAPPrimeCoreOf_of_normal (p := 3) ?_ ?_ ?_
      · exact le_inf inf_le_left ((inf_le_right).trans (Proving.GLAPPrimeCoreOf_le C))
      · rintro g ⟨hgL, hgC⟩ y ⟨hyL, hyO⟩
        exact ⟨L.mul_mem (L.mul_mem hgL hyL) (L.inv_mem hgL),
          Proving.GLAPPrimeCoreOf_conj_mem g hgC y hyO⟩
      · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
          (Proving.coprime_card_GLAPPrimeCoreOf hp3 C)
    refine hSle ⟨?_, ?_⟩
    · have h1 : o * j⁻¹ * o⁻¹ ∈ L := by
        have := conj_mem_conjSub (g := o) (L := L) (L.inv_mem hjL)
        rwa [hOn o ho] at this
      have : ⁅j, o⁆ = j * (o * j⁻¹ * o⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact L.mul_mem hjL h1
    · have h1 : j * o * j⁻¹ ∈ GLAPPrimeCoreOf 3 C := Proving.GLAPPrimeCoreOf_conj_mem j hjC o ho
      have : ⁅j, o⁆ = (j * o * j⁻¹) * o⁻¹ := by simp [commutatorElement_def]
      rw [this]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ ho)
  have hbot := commutator_eq_bot_of_perfect_of_le (glaPComponent_perfect hJ) hOcomm hcentJ
  intro g hg o ho
  have : ⁅g, o⁆ ∈ (⊥ : Subgroup Y) := hbot ▸ Subgroup.commutator_mem_commutator hg ho
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this.symm

theorem b3Cent_of_quasisimple_of_i183 (i183 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4)
    (hB : B3Quasi) : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.Input14_5 := by
  intro Y _ _ hK hO x hx3
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set C : Subgroup Y := Subgroup.centralizer ({x} : Set Y) with hC
  have key : ∀ J : Subgroup Y, GLAPComponent 3 C J → ∀ g ∈ J,
      ∀ o ∈ GLAPPrimeCoreOf 3 C, o * g = g * o := by
    intro J hJ
    have hE : IsElemAbelian 3 (Subgroup.zpowers x) := by
      refine ⟨inferInstance, fun y hy => ?_⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
    have hJ' : GLAPComponent 3 (⊤ ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup Y) : Set Y)) J := by
      rw [top_inf_eq, Balance.centralizer_zpowers_eq_singleton]
      exact hJ
    obtain ⟨𝒞, h1, h2, h3, h4⟩ := i183 Y ⊤ (openIsKGroup_of_subgroup hK ⊤) 3 hp3
      (Subgroup.zpowers x) le_top hE J hJ'
    have hJM : J ≤ ⨆ L ∈ 𝒞, L := by
      rw [h2]
      refine le_iSup₂_of_le (1 : Y) (one_mem _) ?_
      intro y hy
      simpa [GLBConj] using hy
    by_cases h𝒞 : 𝒞.Nonempty
    · obtain ⟨L₀, hL₀⟩ := h𝒞
      have hcomp : ∀ L ∈ 𝒞, CFSG.IsComponent L := fun L hL =>
        (CFSG.isComponent_iff_open L).2
          (ComponentBalance.i116n_isComponentOf_of_glaPComponent hO (h1 L hL))
      by_cases hfix : conjSub x L₀ = L₀
      · have hxN : x ∈ Subgroup.normalizer (L₀ : Set Y) := mem_normalizer_of_conjSub_eq hfix
        have hJL : J ≤ L₀ := by
          refine hJM.trans (iSup₂_le fun L hL => ?_)
          obtain ⟨e, he, rfl⟩ := h4 L₀ hL₀ L hL
          exact (gLBConj_eq_of_mem_normalizer ((Subgroup.zpowers_le.2 hxN) he)).le
        exact caseA hB hK hO hx3 (hcomp L₀ hL₀) hfix hJ hJL
      · have hmoved : ∀ L ∈ 𝒞, conjSub x L ≠ L := by
          intro L hL hxL
          obtain ⟨e, he, hLe⟩ := h4 L₀ hL₀ L hL
          have hxN : x ∈ Subgroup.normalizer (L : Set Y) := mem_normalizer_of_conjSub_eq hxL
          have heN : e⁻¹ ∈ Subgroup.normalizer (L : Set Y) :=
            Subgroup.inv_mem _ ((Subgroup.zpowers_le.2 hxN) he)
          have h5 : conjSub e L = L := by
            have := gLBConj_eq_of_mem_normalizer heN
            unfold GLBConj at this
            rw [inv_inv] at this
            exact this
          have h6 : conjSub e L = L₀ := by
            rw [← hLe]
            show conjSub e (conjSub e⁻¹ L₀) = L₀
            rw [conjSub_conjSub, mul_inv_cancel, conjSub_one]
          have hLL₀ : L = L₀ := h5.symm.trans h6
          exact hfix (hLL₀ ▸ hxL)
        intro g hg o ho
        have hcen : ∀ L ∈ 𝒞, ∀ y ∈ L, o * y = y * o := fun L hL y hy =>
          Balance.commute_of_moved_p hp3 (hcomp L hL)
            (Balance.p_dvd_card_center_quot hp3 hO (hcomp L hL)) hx3 (hmoved L hL) ho y hy
        have hle : (⨆ L ∈ 𝒞, L) ≤ Subgroup.centralizer ({o} : Set Y) :=
          iSup₂_le fun L hL y hy =>
            Subgroup.mem_centralizer_singleton_iff.2 (hcen L hL y hy).symm
        exact (Subgroup.mem_centralizer_singleton_iff.1 (hle (hJM hg))).symm
    · rw [Set.not_nonempty_iff_eq_empty.1 h𝒞] at hJM
      simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, le_bot_iff] at hJM
      intro g hg o ho
      rw [hJM, Subgroup.mem_bot] at hg
      rw [hg]
      simp
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.2
    (sSup_le fun J hJ g hg => Subgroup.mem_centralizer_iff.2 fun o ho => key J hJ g hg o ho)

end CFSG.HardMathSupport.Solomon.Coordinator
