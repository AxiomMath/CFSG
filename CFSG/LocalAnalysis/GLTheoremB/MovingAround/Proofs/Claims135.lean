module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma135
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1110
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Ii
public import CFSG.LocalAnalysis.GLTheoremA.S4.StepTools
public import CFSG.LocalAnalysis.GLTheoremA.S12.Diag

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims135

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround

variable {G : Type} [Group G] [Finite G]

theorem isSubnormal_Iof {p : ℕ} (hp : p.Prime) (M D : Subgroup G) :
    IsSubnormal (Iof p M D) M := by
  have e : Iof p M D = sSup {L | GLAPComponent p M L ∧ ¬ barX p M (gammaStar p D) ≤
      Subgroup.centralizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M))} := by
    rw [sSup_eq_iSup]
    rfl
  rw [e]
  exact CFSG.LocalAnalysis.GLTheoremA.isSubnormal_sSup_glaPComponent hp _ fun _ h => h.1

theorem glaPComponent_of_Iof {p : ℕ} (hp : p.Prime) {M D L : Subgroup G}
    (hL : GLAPComponent p (Iof p M D) L) : GLAPComponent p M L :=
  CFSG.LocalAnalysis.GLTheoremA.glaPComponent_of_isSubnormal' hp (isSubnormal_Iof hp M D) hL

theorem gLBConj_le_of_mem {M K : Subgroup G} (hKM : K ≤ M) {g : G} (hg : g ∈ M) :
    GLBConj g K ≤ M := by
  have h := gLBConj_mono g hKM
  rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hg)] at h

theorem glaPComponent_conj {p : ℕ} {M L : Subgroup G} (hL : GLAPComponent p M L) {g : G}
    (hg : g ∈ M) : GLAPComponent p M (GLBConj g L) := by
  have h := glaPComponent_gLBConj hL g
  rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hg)] at h

theorem lstarsub_le {M D L : Subgroup G} (hDM : D ≤ M) (hLM : L ≤ M) : Lstarsub D L ≤ M :=
  iSup₂_le fun _ hd => gLBConj_le_of_mem hLM (hDM hd)

theorem barX_le_cent_of_ne {M D L K : Subgroup G} (hL : GLAPComponent 3 M L) (hDM : D ≤ M)
    (hK : GLAPComponent 3 M K) (hne : ∀ d ∈ D, barX 3 M K ≠ barX 3 M (GLBConj d L)) :
    barX 3 M K ≤ Lemma135.cent M D L := by
  unfold Lemma135.cent
  rw [Subgroup.le_centralizer_iff, Prop95Parts.barX_le_iff (lstarsub_le hDM hL.1)]
  refine iSup₂_le fun d hd => ?_
  rw [← Prop95Parts.barX_le_iff (gLBConj_le_of_mem hL.1 (hDM hd))]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
      (glaPComponent_conj hL (hDM hd)).2.2.1 hK.2.2.1 fun h => hne d hd h.symm)

theorem three_dvd_card_cent {m : ℕ} {B M E A D T L : Subgroup G}
    (h : Cex134 G m 3 B M E A D T L) (hC : Lemma135.cent M D L ≠ ⊥) :
    3 ∣ Nat.card (Lemma135.cent M D L) := by
  by_contra h3
  have hp : Nat.Prime 3 := Nat.prime_three
  have hLc : GLAPComponent 3 M L := glaPComponent_of_Iof hp h.hL
  have hDM : D ≤ M := h.hD.1.trans h.pair.1.2.1.1.1.1
  have key : ∀ g ∈ M, barX 3 M (GLBConj g L) ≤ barX 3 M (Lstarsub D L) := by
    intro g hg
    by_cases hex : ∃ d ∈ D, barX 3 M (GLBConj g L) = barX 3 M (GLBConj d L)
    · obtain ⟨d, hd, heq⟩ := hex
      rw [heq]
      exact barX_mono_of_le 3 (le_iSup₂_of_le (f := fun d (_ : d ∈ D) => GLBConj d L) d hd le_rfl)
    · simp only [not_exists, not_and] at hex
      exact absurd ((CFSG.LocalAnalysis.GLTheoremA.S12.dvd_card_barX_of_component hp
        (glaPComponent_conj hLc hg)).trans (Subgroup.card_dvd_of_le
          (barX_le_cent_of_ne hLc hDM (glaPComponent_conj hLc hg) hex))) h3
  set N : Subgroup G := ⨆ g ∈ M, GLBConj g L
  have hNM : N ≤ M := iSup₂_le fun _ hg => gLBConj_le_of_mem hLc.1 hg
  have hMN : M ≤ Subgroup.normalizer (N : Set G) := fun y hy =>
    Lemma135.mem_normalizer_of_gLBConj_le (conj_iSup_mem_le hy) (conj_iSup_mem_le (M.inv_mem hy))
  have hNn : (barX 3 M N).Normal := by
    have h1 := barX_le_normalizer (p := 3) (C := M) hMN
    rw [barX_self] at h1
    exact Subgroup.normalizer_eq_top_iff.1 (eq_top_iff.2 h1)
  have hLN : barX 3 M (Lstarsub D L) = barX 3 M N := by
    refine le_antisymm (barX_mono_of_le 3 (iSup₂_le fun d hd =>
      le_iSup₂_of_le (f := fun g (_ : g ∈ M) => GLBConj g L) d (hDM hd) le_rfl)) ?_
    rw [Prop95Parts.barX_le_iff hNM]
    exact iSup₂_le fun g hg =>
      (Prop95Parts.barX_le_iff (gLBConj_le_of_mem hLc.1 hg)).1 (key g hg)
  have hCn : (Lemma135.cent M D L).Normal := by
    unfold Lemma135.cent
    rw [hLN]
    infer_instance
  have hcop : Nat.Coprime 3 (Nat.card (Lemma135.cent M D L)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 h3
  exact hC (CFSG.pPrimeCore_eq_bot_iff.1
    (CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCore_quotient_eq_bot hp) _ hCn hcop)

theorem centThreeInput_holds : Lemma135.CentThreeInput := by
  intro G _ _ m B M E A D T L h hC
  exact three_dvd_card_cent h hC

theorem mem_of_alperinDecomposition {p : ℕ} {S X M : Subgroup G} {c : G}
    (hN : ∀ Q : Subgroup G, CFSG.RankTwoShapes.IsAlperinSubgroup p S Q →
      Subgroup.normalizer (Q : Set G) ≤ M)
    (h : CFSG.RankTwoShapes.AlperinDecomposition p S X c) : c ∈ M := by
  induction h with
  | one => exact M.one_mem
  | step _ hQ _ hn ih => exact M.mul_mem ih (hN _ hQ hn)

theorem exists_centralizer_mul_of_alperin {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    {M : Subgroup G} (hN : ∀ Q : Subgroup G,
      CFSG.RankTwoShapes.IsAlperinSubgroup p (S : Subgroup G) Q →
        Subgroup.normalizer (Q : Set G) ≤ M)
    {X : Subgroup G} (hX : X ≤ S) {g : G} (hg : GLBConj g X ≤ S) :
    ∃ c ∈ Subgroup.centralizer (X : Set G), ∃ k ∈ M, g = c * k := by
  obtain ⟨k, hk, hkg⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion S hX hg
  refine ⟨g * k⁻¹, ?_, k, mem_of_alperinDecomposition hN hk, by group⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  calc x * (g * k⁻¹) = g * (g⁻¹ * x * g) * k⁻¹ := by group
    _ = g * (k⁻¹ * x * k) * k⁻¹ := by rw [hkg x hx]
    _ = g * k⁻¹ * x := by group

theorem mem_centerOf_iff {R : Subgroup G} {z : G} :
    z ∈ centerOf R ↔ z ∈ R ∧ ∀ y ∈ R, y * z = z * y := by
  unfold centerOf
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, fun y hy => congrArg Subtype.val (Subgroup.mem_center_iff.1 hw ⟨y, hy⟩)⟩
  · rintro ⟨hzR, hz⟩
    exact ⟨⟨z, hzR⟩, Subgroup.mem_center_iff.2 fun y => Subtype.ext (hz y y.2), rfl⟩

theorem normalizer_le_normalizer_centerOf (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer ((centerOf R : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro z
  rw [mem_centerOf_iff, mem_centerOf_iff]
  constructor
  · rintro ⟨hzR, hz⟩
    refine ⟨(hg z).1 hzR, fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ R := (hg (g⁻¹ * y * g)).2 (by simpa [mul_assoc] using hy)
    have hc := hz _ hy'
    calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc]
      _ = g * z * g⁻¹ * y := by group
  · rintro ⟨hzR, hz⟩
    refine ⟨(hg z).2 hzR, fun y hy => ?_⟩
    have hc := hz _ ((hg y).1 hy)
    have e : g * (y * z) * g⁻¹ = g * (z * y) * g⁻¹ := by
      calc g * (y * z) * g⁻¹ = g * y * g⁻¹ * (g * z * g⁻¹) := by group
        _ = g * z * g⁻¹ * (g * y * g⁻¹) := hc
        _ = g * (z * y) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)

theorem normalizer_le_normalizer_omegaOne (p : ℕ) (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer ((omegaOne p H : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (H : Set G), GLBConj g (omegaOne p H) ≤ omegaOne p H := by
    intro g hg
    unfold omegaOne GLBConj
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨hxH, hxp⟩, rfl⟩
    refine ⟨?_, by rw [← map_pow, hxp, map_one]⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) x).1 hxH
    simpa using h1
  exact fun g hg => Lemma135.mem_normalizer_of_gLBConj_le (key g hg) (key g⁻¹ (inv_mem hg))

theorem pRank_le_pRank_omegaOne {p : ℕ} (hp : 1 < p) (H : Subgroup G) :
    CFSG.Open.pRank p H ≤ CFSG.Open.pRank p (omegaOne p H) := by
  obtain ⟨E, hEH, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp H
  have hEO : E ≤ omegaOne p H := by
    intro x hx
    unfold omegaOne
    exact Subgroup.subset_closure ⟨hEH hx, hE.2 x hx⟩
  exact CFSG.SectionRank.le_pRank hp hEO hE hEc

theorem normalizer_le_of_le_B {m : ℕ} {B M E A D T L Q : Subgroup G}
    (h : Cex134 G m 3 B M E A D T L) (hQB : Q ≤ B) (hQ : 2 ≤ CFSG.Open.pRank 3 Q) :
    Subgroup.normalizer (Q : Set G) ≤ M :=
  le_trans (le_sSup (show Subgroup.normalizer (Q : Set G) ∈ {N : Subgroup G | ∃ Q' : Subgroup G,
    Q' ≤ B ∧ 2 ≤ CFSG.Open.pRank 3 Q' ∧ N = Subgroup.normalizer (Q' : Set G)} from
      ⟨Q, hQB, hQ, rfl⟩)) h.uniq.clause_d

theorem exists_plane_of_two_le_pRank {X : Subgroup G} (hX : 2 ≤ CFSG.Open.pRank 3 X) :
    ∃ Q : Subgroup G, Q ≤ X ∧ IsElemAbelian 3 Q ∧ Nat.card Q = 3 ^ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEX, hE, hEc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) X
  obtain ⟨Q0, hQ0⟩ := Sylow.exists_subgroup_card_pow_prime 3
    (show 3 ^ 2 ∣ Nat.card E by rw [hEc]; exact pow_dvd_pow 3 hX)
  refine ⟨Q0.map E.subtype, (Subgroup.map_subtype_le Q0).trans hEX,
    CFSG.Open.IsElemAbelian.mono hE (Subgroup.map_subtype_le Q0), ?_⟩
  rw [Subgroup.card_map_of_injective E.subtype_injective, hQ0]

@[expose] def CenterInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ) {B M E A D T L : Subgroup G}
    (_ : Cex134 G m 3 B M E A D T L), Lemma135.cent M D L = ⊥ →
    ∀ P : Subgroup G, IsSylowIn 3 M P → B ⊔ D ≤ P → 2 ≤ CFSG.Open.pRank 3 (centerOf P)

@[expose] def FamilyCoreInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ) {B M E A D T L : Subgroup G}
    (_ : Cex134 G m 3 B M E A D T L), Lemma135.cent M D L = ⊥ →
    ∀ P : Subgroup G, IsSylowIn 3 M P → B ⊔ D ≤ P → IsSylowIn 3 ⊤ P →
      ∀ F : Subgroup G, CFSG.RankTwoShapes.IsAlperinSubgroup 3 P F → ¬ F ≤ B →
        centerOf F ≠ centerOf P → Subgroup.normalizer (F : Set G) ≤ M

@[expose] def CentralizerInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ) {B M E A D T L : Subgroup G}
    (_ : Cex134 G m 3 B M E A D T L), Lemma135.cent M D L = ⊥ →
    ∀ P : Subgroup G, IsSylowIn 3 M P → B ⊔ D ≤ P → IsSylowIn 3 ⊤ P →
      (∀ X : Subgroup G, X ≤ P → ∀ g : G, GLBConj g X ≤ P →
        ∃ c ∈ Subgroup.centralizer (X : Set G), ∃ k ∈ M, g = c * k) →
      ∀ Q : Subgroup G, Q ≤ P → IsElemAbelian 3 Q → Nat.card Q = 3 ^ 2 → ¬ Q ≤ B →
        Subgroup.centralizer (Q : Set G) ≤ M

theorem normalizer_le_of_alperin (hF : FamilyCoreInput) {m : ℕ} {B M E A D T L : Subgroup G}
    (h : Cex134 G m 3 B M E A D T L) (hcent : Lemma135.cent M D L = ⊥) {P : Subgroup G}
    (hPM : IsSylowIn 3 M P) (hBDP : B ⊔ D ≤ P) (hPS : IsSylowIn 3 ⊤ P)
    (hZ2 : 2 ≤ CFSG.Open.pRank 3 (centerOf P))
    (hNZ : Subgroup.normalizer ((centerOf P : Subgroup G) : Set G) ≤ M) {F : Subgroup G}
    (hFA : CFSG.RankTwoShapes.IsAlperinSubgroup 3 P F) :
    Subgroup.normalizer (F : Set G) ≤ M := by
  have hZF : centerOf P ≤ F := by
    intro z hz
    refine hFA.2.2.1 (Subgroup.mem_inf.2 ⟨?_, (mem_centerOf_iff.1 hz).1⟩)
    rw [Subgroup.mem_centralizer_iff]
    exact fun f hf => (mem_centerOf_iff.1 hz).2 f (hFA.1 hf)
  by_cases hFB : F ≤ B
  · exact normalizer_le_of_le_B h hFB
      (hZ2.trans (CFSG.SectionRank.pRank_mono (by norm_num) hZF))
  by_cases hZZ : centerOf F = centerOf P
  · refine (normalizer_le_normalizer_centerOf F).trans ?_
    rw [hZZ]
    exact hNZ
  exact hF G m h hcent P hPM hBDP hPS F hFA hFB hZZ

theorem normalizer_le_of_inputs (hZ : CenterInput) (hF : FamilyCoreInput)
    (hCQ : CentralizerInput) {m : ℕ} {B M E A D T L : Subgroup G}
    (h : Cex134 G m 3 B M E A D T L) (hcent : Lemma135.cent M D L = ⊥) {P : Subgroup G}
    (hPM : IsSylowIn 3 M P) (hBDP : B ⊔ D ≤ P) {X : Subgroup G} (hXP : X ≤ P)
    (hX : 2 ≤ CFSG.Open.pRank 3 X) : Subgroup.normalizer (X : Set G) ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBP : B ≤ P := le_sup_left.trans hBDP
  have hBSC : IsSCp 3 ⊤ B := lemma23_proved G m 3 h.standing B h.bOne
  have hZ2 : 2 ≤ CFSG.Open.pRank 3 (centerOf P) := hZ G m h hcent P hPM hBDP
  have hNZ : Subgroup.normalizer ((centerOf P : Subgroup G) : Set G) ≤ M :=
    (normalizer_le_normalizer_omegaOne 3 (centerOf P)).trans (normalizer_le_of_le_B h
      (l1110_omegaOne_centerOf_le hBSC hBP)
      (hZ2.trans (pRank_le_pRank_omegaOne (by norm_num) (centerOf P))))
  have hPG := Lemma135.sylow_of_normalizer_le hPM ((normalizer_le_normalizer_centerOf P).trans hNZ)
  have hPS : IsSylowIn 3 ⊤ P := ⟨le_top, hPM.2.1, fun R _ hR hPR => hPG R hR hPR⟩
  let PS : Sylow 3 G := ⟨P, hPM.2.1, fun {R} hR hPR => hPG R hR hPR⟩
  have hfus : ∀ Y : Subgroup G, Y ≤ P → ∀ g : G, GLBConj g Y ≤ P →
      ∃ c ∈ Subgroup.centralizer (Y : Set G), ∃ k ∈ M, g = c * k :=
    fun Y hY g hg => exists_centralizer_mul_of_alperin PS
      (fun F hFA => normalizer_le_of_alperin hF h hcent hPM hBDP hPS hZ2 hNZ hFA) hY hg
  obtain ⟨Q, hQX, hQe, hQc⟩ := exists_plane_of_two_le_pRank hX
  have hCQ' : Subgroup.centralizer (Q : Set G) ≤ M := by
    by_cases hQB : Q ≤ B
    · exact (Subgroup.centralizer_le_normalizer (Q : Set G)).trans (normalizer_le_of_le_B h hQB
        (CFSG.SectionRank.le_pRank (by norm_num) le_rfl hQe hQc))
    · exact hCQ G m h hcent P hPM hBDP hPS hfus Q (hQX.trans hXP) hQe hQc hQB
  intro g hg
  obtain ⟨c, hc, k, hk, rfl⟩ :=
    hfus X hXP g ((gLBConj_eq_of_mem_normalizer hg).symm ▸ hXP)
  exact M.mul_mem (hCQ' (Subgroup.centralizer_le hQX hc)) hk

theorem nineCoreInput_of_inputs (hZ : CenterInput) (hF : FamilyCoreInput)
    (hCQ : CentralizerInput) : Lemma135.NineCoreInput := by
  intro G _ _ m B M E A D T L h hcent P hPM hBDP X hXP hX _
  exact normalizer_le_of_inputs hZ hF hCQ h hcent hPM hBDP hXP hX

theorem lemma135_i_of_inputs'' (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hcomp : Sec13_compStatement) (h133 : Lemma133Statement)
    (hZ : CenterInput) (hF : FamilyCoreInput) (hCQ : CentralizerInput) : Lemma135_iStatement :=
  lemma135_i_of_inputs hP95 h111 h121 hcomp h133 centThreeInput_holds
    (nineCoreInput_of_inputs hZ hF hCQ)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims135
