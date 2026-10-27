module

public import CFSG.LocalAnalysis.GLTheoremA.S4.PGroupCover
public import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_ne_one_mem_inf_of_hyperplane {p : ℕ} (hp : p.Prime) {A B₀ E : Subgroup G}
    (hA : IsElemAbelian p A) (hB₀ : B₀ ≤ A) (hB₀c : Nat.card B₀ * p = Nat.card A) (hEA : E ≤ A)
    (hE : Nat.card E = p ^ 3) : ∃ y ∈ E ⊓ B₀, y ≠ 1 := by
  by_contra h
  push Not at h
  have hbot : E ⊓ B₀ = ⊥ := (Subgroup.eq_bot_iff_forall _).2 h
  have hN : B₀ ≤ Subgroup.normalizer (E : Set G) := fun b hb =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun e he =>
      isElemAbelian_commute hA (hEA he) (hB₀ hb))
  have h1 := card_sup_mul_card_inf_of_le_normalizer hN
  rw [hbot, Subgroup.card_bot, mul_one] at h1
  have h2 : Nat.card (E ⊔ B₀ : Subgroup G) ≤ Nat.card A := Subgroup.card_le_of_le (sup_le hEA hB₀)
  rw [h1, hE, ← hB₀c] at h2
  have hB₀pos : 0 < Nat.card B₀ := Nat.card_pos
  have h3 : p ^ 3 * Nat.card B₀ ≤ p * Nat.card B₀ := by linarith [h2]
  have h4 : p ^ 3 ≤ p := Nat.le_of_mul_le_mul_right h3 hB₀pos
  have h5 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  rw [pow_one] at h5
  omega

theorem lemma43 {p : ℕ} (hp : p.Prime) (hS3 : Stage3 G p) (h183 : Input18_3_4)
    (hKP : CFSG.Open.IsKProper G) (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (h1131 : I1131At G p) (h1122 : I1122IsoAt G p) (h1132 : I1132UsedAt G p)
    (hLB : LBalanceAt G p) : Lemma43At G p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro B x L hS hBL
  obtain ⟨hB, hx, hLc⟩ := hS
  have hZL : Nat.card (Subgroup.center (PQuot p L)) = p :=
    card_center_of_isExcType (h1131 B x L hB hx hLc hBL)
  obtain ⟨A, hA, hBA, hAL, hdec, E, hE, hEe, hEcard⟩ := h1132 B x L hB hx hLc hBL
  have hEA : E ≤ A := hE.trans (inf_le_left.trans inf_le_left)
  have hEZ : E ≤ centModSubgroup p L := hE.trans inf_le_right
  set Cx := Subgroup.centralizer ({x} : Set G)
  have hxL : CentMod p L x :=
    centMod_of_mem_centralizer (IsSTriple.mem_centralizer ⟨hB, hx, hLc⟩)
  have hxA : x ∈ A := hBA ⟨hx.1, centMod_iff.1 hxL⟩
  obtain ⟨B₀, hB₀A, hB₀c, hB₀e⟩ := hS3.2.1 A hA
  obtain ⟨x', ⟨hx'E, hx'B₀⟩, hx'1⟩ :=
    exists_ne_one_mem_inf_of_hyperplane hp hA.1 hB₀A hB₀c hEA hEcard
  have hx' : IsEssential p A x' := hB₀e x' hx'B₀ hx'1
  have hx'A : x' ∈ A := hEA hx'E
  have hx'L : CentMod p L x' := centMod_iff.2 (hEZ hx'E)
  set Cx' := Subgroup.centralizer ({x'} : Set G)
  have hACx' : A ≤ Cx' := isElemAbelian_le_centralizer hA.1 hx'A
  have hx'p : IsPGroup p (Subgroup.zpowers x') := isPGroup_zpowers_of_mem hA.1 hx'A
  have hCx'ne : Cx' ≠ ⊤ := centralizer_ne_top_of_ne_one hsimple hnonab hx'.2.1
  obtain ⟨hIc, -, -, -, hIsup, ⟨eIL⟩⟩ := glaPLayer_inf_centralizer hp hLc hx'p hx'L
  set I := GLAPLayer p (L ⊓ Cx')
  have hIL : I ≤ L := hIc.1.trans inf_le_left
  have hICx : I ≤ Cx := hIL.trans hLc.1
  have hCzx : Subgroup.centralizer (Subgroup.zpowers x : Set G) = Cx := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hI2 : GLAPComponent p (Cx' ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) I := by
    rw [hCzx, inf_comm]
    exact glaPComponent_of_isSubnormal' hp (hLc.2.1.inf Cx') hIc
  have hALCx' : ∀ a ∈ A, a ∈ Subgroup.normalizer ((L ⊓ Cx' : Subgroup G) : Set G) := by
    intro a ha
    have haCx' : a ∈ Subgroup.normalizer (Cx' : Set G) := Subgroup.le_normalizer (hACx' ha)
    rw [mem_normalizer_iff_gLBConj_eq] at haCx' ⊢
    rw [gLBConj_inf, mem_normalizer_iff_gLBConj_eq.1 (hAL ha), haCx']
  have hKx' : CFSG.Open.IsKGroup ↥Cx' := isKGroup_of_isKProper hKP hCx'ne
  have hxCx' : Subgroup.zpowers x ≤ Cx' := Subgroup.zpowers_le.2 (hACx' hxA)
  obtain ⟨𝒞, h𝒞c, h𝒞sup, -, h𝒞tr⟩ := h183 G Cx' hKx' p hp (Subgroup.zpowers x) hxCx'
    (isElemAbelian_zpowers_of_mem hA.1 hxA) I hI2
  set J := closureIn I (GLAPLayer p Cx')
  have hJ : J = ⨆ K ∈ 𝒞, K := (closureIn_eq_iSup_gLBConj I _).trans h𝒞sup.symm
  have hKJ : ∀ K ∈ 𝒞, K ≤ J := fun K hK => hJ ▸ le_biSup (fun K => K) hK
  have hJCx' : J ≤ Cx' := hJ ▸ iSup₂_le fun K hK => (h𝒞c K hK).1
  have hIJ : I ≤ J := le_closureIn_self I _
  obtain ⟨L', hL'𝒞⟩ : 𝒞.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hbot : J = ⊥ := by
      rw [hJ, h]
      simp
    exact glaPComponent_ne_bot' hIc (eq_bot_iff.2 (hbot ▸ hIJ))
  have hL'c : GLAPComponent p Cx' L' := h𝒞c L' hL'𝒞
  have hxN : x ∈ Subgroup.normalizer (L' : Set G) := by
    by_contra hxN
    have hJcl : J ≤ closureIn L' A := by
      rw [hJ]
      refine iSup₂_le fun K hK => ?_
      obtain ⟨e, he, rfl⟩ := h𝒞tr L' hL'𝒞 K hK
      rw [closureIn_eq_iSup_gLBConj]
      exact le_biSup (fun b => GLBConj b L') (Subgroup.zpowers_le.2 hxA he)
    have hclN : closureIn L' A ≤ Subgroup.normalizer (J : Set G) := by
      rw [closureIn_eq_iSup_gLBConj]
      refine iSup₂_le fun b hb => ?_
      have hbC : GLAPComponent p Cx' (GLBConj b L') := by
        have := glaPComponent_gLBConj hL'c b
        rwa [mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hACx' hb))] at this
      intro k hk
      rw [hJ, ← sSup_eq_iSup]
      refine mem_normalizer_sSup fun K hK => ?_
      by_cases hKb : K = GLBConj b L'
      · rw [hKb]
        exact Subgroup.le_normalizer hk
      · exact CFSG.HardMathSupport.Solomon.LocalBalance.mem_normalizer_of_ne hp (h𝒞c K hK) hbC
          hKb hk
    have hIJx : GLAPComponent p (J ⊓ Cx) I := by
      refine glaPComponent_of_le hp hI2 (le_inf hIJ hICx) ?_
      rw [hCzx]
      exact inf_le_inf_right _ hJCx'
    have hJxle : J ⊓ Cx ≤ closureIn L' A ⊓ Cx := inf_le_inf_right _ hJcl
    have hsn : IsSubnormal (J ⊓ Cx) (closureIn L' A ⊓ Cx) := by
      refine IsSubnormal.step hJxle ((Subgroup.normal_subgroupOf_iff_le_normalizer hJxle).2 ?_)
        (IsSubnormal.refl _)
      intro g hg
      have h1 : GLBConj g J = J := mem_normalizer_iff_gLBConj_eq.1 (hclN hg.1)
      have h2 : GLBConj g Cx = Cx := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hg.2)
      rw [mem_normalizer_iff_gLBConj_eq, gLBConj_inf, h1, h2]
    have hIdiag : GLAPComponent p (closureIn L' A ⊓ Cx) I :=
      glaPComponent_of_isSubnormal' hp hsn hIJx
    obtain ⟨e⟩ := h1122 A x' L' x hA hx' hL'c hxA hxN I hIdiag
    have h1 : Nat.card (Subgroup.center (PQuot p L)) =
        Nat.card (Subgroup.center (PSimple p L')) :=
      Nat.card_congr (Subgroup.centerCongr (eIL.symm.trans e)).toEquiv
    rw [center_pSimple_eq_bot hp hL'c, Subgroup.card_bot, hZL] at h1
    exact hp.one_lt.ne' h1
  have huniq : ∀ K ∈ 𝒞, K = L' := fun K hK => by
    obtain ⟨e, he, hee⟩ := h𝒞tr L' hL'𝒞 K hK
    have heN : e ∈ Subgroup.normalizer (L' : Set G) := Subgroup.zpowers_le.2 hxN he
    rw [← hee, mem_normalizer_iff_gLBConj_eq.1 heN]
  have hJL' : J = L' := by
    rw [hJ]
    exact le_antisymm (iSup₂_le fun K hK => (huniq K hK).le) (le_biSup (fun K => K) hL'𝒞)
  have hIL' : I ≤ L' := hJL' ▸ hIJ
  have hIL'x : GLAPComponent p (L' ⊓ Cx) I := by
    refine glaPComponent_of_le hp hI2 (le_inf hIL' hICx) ?_
    rw [hCzx]
    exact inf_le_inf_right _ hL'c.1
  have hAI : ∀ a ∈ A, a ∈ Subgroup.normalizer (I : Set G) := fun a ha =>
    mem_normalizer_glaPLayer (hALCx' a ha)
  have hAL' : A ≤ Subgroup.normalizer (L' : Set G) := by
    intro a ha
    rw [← hJL']
    exact mem_normalizer_closureIn (hAI a ha)
      (mem_normalizer_glaPLayer (Subgroup.le_normalizer (hACx' ha)))
  refine ⟨A, x', L', Relation.ReflTransGen.single ⟨⟨hB, hx, hLc⟩, ⟨hA, hx', hL'c⟩, hxA,
    fun b hb => ?_, hx'A, hx'L, glaPComponent_of_le hp hL'c (hKJ L' hL'𝒞) hJCx'⟩, hAL',
    E, hEA, hEe, hEcard, hEA.trans hAL', ?_⟩
  · obtain ⟨u, hu, v, hv, rfl⟩ := hdec b hb
    exact ⟨u, ⟨hu.2, hu.1⟩, v, hv.1, centMod_iff.2 hv.2, rfl⟩
  have hEp : IsPGroup p E := isPGroup_of_isElemAbelian hEe
  have hOI : GLAPPrimeCoreOf p I = I ⊓ GLAPPrimeCoreOf p L := (cover_facts hp hIL hIsup).1
  have hEI : E ≤ centModSubgroup p I := by
    intro e he
    have heN := hAI e (hEA he)
    refine ⟨heN, fun i hi => ?_⟩
    rw [hOI]
    refine ⟨?_, (hEZ he).2 i (hIL hi)⟩
    have : e * i⁻¹ * e⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.1 heN i⁻¹).1 (I.inv_mem hi)
    have e1 : ⁅i, e⁆ = i * (e * i⁻¹ * e⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e1]
    exact I.mul_mem hi this
  obtain ⟨hDc, -⟩ := glaPLayer_inf_centralizer_of_isPGroup hp hIc hEp hEI
  have hsn : IsSubnormal (I ⊓ Subgroup.centralizer (E : Set G))
      ((L' ⊓ Cx) ⊓ Subgroup.centralizer (E : Set G)) := hIL'x.2.1.inf _
  have h1 := glaPLayer_le_of_isSubnormal hp hsn
  have hxE : x ∈ Subgroup.normalizer
      ((L' ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) := by
    have hxCE : x ∈ Subgroup.centralizer (E : Set G) := Subgroup.mem_centralizer_iff.2 fun e he =>
      isElemAbelian_commute hA.1 (hEA he) hxA
    have h2 : GLBConj x (Subgroup.centralizer (E : Set G)) = Subgroup.centralizer (E : Set G) :=
      mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hxCE)
    rw [mem_normalizer_iff_gLBConj_eq, gLBConj_inf, mem_normalizer_iff_gLBConj_eq.1 hxN, h2]
  have hKX : CFSG.Open.IsKGroup ↥((L' ⊓ Subgroup.centralizer (E : Set G)) ⊔ Subgroup.zpowers x) :=
    isKGroup_of_isKProper hKP (ne_top_of_le_ne_top hCx'ne
      (sup_le (inf_le_left.trans hL'c.1) hxCx'))
  have h2 := glaPLayer_inf_centralizer_le hp hLB hKX (isPGroup_zpowers_of_mem hA.1 hxA)
    (Subgroup.zpowers_le.2 hxE)
  rw [hCzx, inf_right_comm] at h2
  intro hbot
  exact glaPComponent_ne_bot' hDc (eq_bot_iff.2 (hbot ▸ h1.trans h2))

end CFSG.LocalAnalysis.GLTheoremA
