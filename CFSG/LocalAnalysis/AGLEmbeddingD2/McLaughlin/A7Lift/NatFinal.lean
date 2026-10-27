module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Lift.NatOver
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Lift.BaumNormal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Lift.Step
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.Natural
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.SixPermData
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7SixModule
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.SubS
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7SixBlock

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Six

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.A7Six
  CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry Equiv Equiv.Perm MulAction

namespace SixCtx

variable {X : Type} [Group X] [Finite X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)}

section SubSR

variable (c : SixCtx T L) (pd : PermData) {R : Subgroup X}

@[expose] def subSR (R : Subgroup X) : Subgroup X :=
  R ⊓ (pd.E.comap c.θ).map (nL T L).subtype

theorem mem_subSR (hRL : R ≤ nL T L) {t : X} :
    t ∈ c.subSR pd R ↔ ∃ ht : t ∈ R, c.θ ⟨t, hRL ht⟩ ∈ pd.E := by
  constructor
  · rintro ⟨ht, ⟨⟨g, hg⟩, hgE, rfl⟩⟩
    exact ⟨ht, hgE⟩
  · rintro ⟨ht, hE⟩
    exact ⟨ht, ⟨⟨t, hRL ht⟩, hE, rfl⟩⟩

theorem subSR_le : c.subSR pd R ≤ R := inf_le_left

theorem inf_gnC_le_subSR (hRL : R ≤ nL T L) (hCR : T ⊓ gnC T ≤ R) :
    T ⊓ gnC T ≤ c.subSR pd R := by
  rintro t ⟨ht, htC⟩
  refine (c.mem_subSR pd hRL).2 ⟨hCR ⟨ht, htC⟩, ?_⟩
  rw [c.theta_eq_one_of_mem_gnC (hRL (hCR ⟨ht, htC⟩)) htC]
  exact pd.E.one_mem

private theorem theta_eq_one_of_mem_pCore_R (hRL : R ≤ nL T L)
    (hQR : pCoreOf 2 (⊤ : Subgroup X) ≤ R) {q : X}
    (hq : q ∈ pCoreOf 2 (⊤ : Subgroup X)) :
    c.θ ⟨q, hRL (hQR hq)⟩ = 1 := by
  rw [c.hθ1]
  intro l hl
  set π := QuotientGroup.mk' (gnC T)
  have hQn : (pCoreOf 2 (⊤ : Subgroup X)).Normal := CFSG.AGLEmbeddingD2.GN.normal_pCoreOf_top
  set Qs : Subgroup (X ⧸ gnC T) := (pCoreOf 2 (⊤ : Subgroup X)).map π
  have hQsn : Qs.Normal := hQn.map π (QuotientGroup.mk'_surjective _)
  have hQs2 : IsPGroup 2 Qs := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤).map π
  set x := π q * l * (π q)⁻¹ * l⁻¹ with hx
  have hxQ : x ∈ Qs := by
    have h1 : l * (π q)⁻¹ * l⁻¹ ∈ Qs := hQsn.conj_mem _ (Qs.inv_mem ⟨q, hq, rfl⟩) l
    have := Qs.mul_mem ⟨q, hq, rfl⟩ h1
    simpa [hx, mul_assoc] using this
  have hqL : π q * l * (π q)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.1 (hRL (hQR hq)) l).1 hl
  have hxL : x ∈ L := L.mul_mem hqL (L.inv_mem hl)
  have hsimp : IsSimpleGroup ↥L := c.eL.isSimpleGroup
  have hN : ((Qs ⊓ L).subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨hQsn.conj_mem _ hn.1 g, L.mul_mem (L.mul_mem g.2 hn.2) (L.inv_mem g.2)⟩
  have hcard : Nat.card ↥L = 2520 := by
    rw [Nat.card_congr c.eL.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Qs ⊓ L).subgroupOf L) with h | h
  · have : (⟨x, hxL⟩ : ↥L) ∈ (Qs ⊓ L).subgroupOf L := ⟨hxQ, hxL⟩
    rw [h, Subgroup.mem_bot] at this
    have hx1 : x = 1 := congrArg Subtype.val this
    rw [hx] at hx1
    calc π q * l * (π q)⁻¹ = π q * l * (π q)⁻¹ * l⁻¹ * l := by group
      _ = l := by rw [hx1, one_mul]
  · exfalso
    have hLQ : L ≤ Qs := fun y hy => by
      have : (⟨y, hy⟩ : ↥L) ∈ (Qs ⊓ L).subgroupOf L := h ▸ Subgroup.mem_top _
      exact this.1
    have h2 : IsPGroup 2 ↥L := hQs2.to_le hLQ
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
    rw [hcard] at hk
    have h3 : (2 : ℕ) ^ k % 9 = 0 := by rw [← hk]
    have h4 : ¬ (3 : ℕ) ∣ 2 ^ k := by
      intro h3'
      exact absurd ((Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3')) (by decide)
    exact h4 (by rw [← hk]; decide)

theorem pCoreOf_le_subSR (hX : GNSetting X T) (hRL : R ≤ nL T L)
    (hQR : pCoreOf 2 (⊤ : Subgroup X) ≤ R) :
    pCoreOf 2 (⊤ : Subgroup X) ≤ c.subSR pd R := by
  intro q hq
  refine (c.mem_subSR pd hRL).2 ⟨hQR hq, ?_⟩
  rw [c.theta_eq_one_of_mem_pCore_R hRL hQR hq]
  exact pd.E.one_mem

theorem baum_le_subSR (hX : GNSetting X T) (hRL : R ≤ nL T L) (hJR : thompsonJ T ≤ R)
    (hbR : baum T ≤ R) (hD : c.img R = pd.D) : baum T ≤ c.subSR pd R :=
  fun g hg =>
    (c.mem_subSR pd hRL).2
      ⟨hbR hg, c.theta_mem_E_of_mem_baum_R pd hX hRL hJR hbR hD hg⟩

theorem baum_subSR (hX : GNSetting X T) (hRL : R ≤ nL T L) (hRT : R ≤ T)
    (hJR : thompsonJ T ≤ R) (hbR : baum T ≤ R) (hD : c.img R = pd.D) :
    baum (c.subSR pd R) = baum T :=
  (CFSG.Quasithin.baum_eq_of_le (c.baum_le_subSR pd hX hRL hJR hbR hD)
    ((c.subSR_le pd).trans hRT)).symm

theorem omegaOneCenterOf_le_subSR (hX : GNSetting X T) (hRL : R ≤ nL T L) (hRT : R ≤ T)
    (hJR : thompsonJ T ≤ R) (hbR : baum T ≤ R) (hD : c.img R = pd.D) :
    omegaOneCenterOf T ≤ omegaOneCenterOf (c.subSR pd R) := by
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  have hZS : centerOf T ≤ c.subSR pd R := by
    intro z hz
    refine c.baum_le_subSR pd hX hRL hJR hbR hD (Subgroup.mem_inf.2 ⟨hz.1,
      Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩)
    have hyT : y ∈ T := hJT ((Subgroup.closure_le _).mpr (fun x hx => hx.1.1) hy)
    exact (Subgroup.mem_centralizer_iff.1 hz.2 y hyT)
  refine (Subgroup.closure_le _).mpr fun x hx => Subgroup.subset_closure
    ⟨Subgroup.mem_inf.2 ⟨hZS hx.1, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩, hx.2⟩
  exact Subgroup.mem_centralizer_iff.1 hx.1.2 y (hRT (c.subSR_le pd hy))

theorem img_subSR (hRL : R ≤ nL T L) (hD : c.img R = pd.D) :
    c.img (c.subSR pd R) = pd.E := by
  apply le_antisymm
  · rintro _ ⟨⟨t, ht'⟩, ht, rfl⟩
    exact ((c.mem_subSR pd hRL).1 ht).2
  · intro σ hσ
    have hσD : σ ∈ c.img R := hD ▸ pd.E_le_D hσ
    obtain ⟨⟨t, ht'⟩, ht, rfl⟩ := hσD
    exact ⟨⟨t, ht'⟩, (c.mem_subSR pd hRL).2 ⟨ht, hσ⟩, rfl⟩

theorem exists_preimage_of_mem_D_R (hX : GNSetting X T) (hRL : R ≤ nL T L)
    (hLR : T ⊓ lT T L ≤ R) (hL : IsComponentOf L ⊤) (hD : c.img R = pd.D)
    {σ : Perm (Fin 7)} (hσ : σ ∈ pd.D ⊓ alternatingGroup (Fin 7)) :
    ∃ (t : X) (ht : t ∈ R), QuotientGroup.mk' (gnC T) t ∈ L ∧
      c.θ ⟨t, hRL ht⟩ = σ := by
  classical
  have hD8 : Nat.card (pd.D ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))) = 8 := by
    have hrel : (alternatingGroup (Fin 7)).relIndex pd.D = 2 := by
      have hdvd : (alternatingGroup (Fin 7)).relIndex pd.D ∣ 2 := by
        rw [← alternatingGroup.index_eq_two (α := Fin 7)]
        exact Subgroup.relIndex_dvd_index_of_normal (H := alternatingGroup (Fin 7)) (K := pd.D)
      have hne1 : (alternatingGroup (Fin 7)).relIndex pd.D ≠ 1 := by
        rw [Ne, Subgroup.relIndex_eq_one]
        intro hle
        have := Equiv.Perm.mem_alternatingGroup.mp (hle (pd.E_le_D pd.swap_mem_E))
        rw [Equiv.Perm.sign_swap (by decide)] at this
        exact absurd this (by decide)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    have hmul := Subgroup.relIndex_mul_card (alternatingGroup (Fin 7)) pd.D
    rw [hrel, pd.card_D, inf_comm] at hmul
    omega
  have hinf := c.toSevenCtx0.card_img_inf_lT hX hL
  have h8 : Nat.card (c.img (T ⊓ lT T L)) = 8 := hinf.1
  have hA : c.img (T ⊓ lT T L) ≤ alternatingGroup (Fin 7) := hinf.2
  have hle : c.img (T ⊓ lT T L) ≤ pd.D ⊓ alternatingGroup (Fin 7) :=
    le_inf (hD ▸ c.img_mono hLR) hA
  have heq : c.img (T ⊓ lT T L) = pd.D ⊓ alternatingGroup (Fin 7) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [h8, hD8])
  have hσ' : σ ∈ c.img (T ⊓ lT T L) := heq ▸ hσ
  obtain ⟨t, ht, htθ⟩ := (c.mem_img (hLR.trans hRL)).1 hσ'
  exact ⟨t, hLR ht, ht.2, by simpa using htθ⟩

end SubSR

private theorem colour_contradiction (c' : A7Lift.SevenCtx0 T L) (pd : PermData)
    {C₁ C₂ : Subgroup X} (hY : GNYComponent T C₁ C₂ L)
    (hstepS : ∀ i, c'.wP (pd.P i) ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
      c'.wP (pd.P i) ≤ gnImg T (Subgroup.normalizer (C₂ : Set X)))
    (hstepN : c'.wP pd.PN ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
      c'.wP pd.PN ≤ gnImg T (Subgroup.normalizer (C₂ : Set X))) : False := by
  classical
  set CC := gnImg T (Subgroup.centralizer (C₁ : Set X))
  set NN := gnImg T (Subgroup.normalizer (C₂ : Set X))
  have hL_le : ∀ K : Subgroup (X ⧸ gnC T), (∀ i, c'.wP (pd.P i) ≤ K) → L ≤ K := by
    intro K hK
    refine c'.le_of_closure pd.gen_P fun σ hσ => ?_
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hσ
    exact c'.mem_of_wP_le (hK i) hi
  have hL_le' : ∀ (K : Subgroup (X ⧸ gnC T)) (i : Fin 3), c'.wP pd.PN ≤ K →
      c'.wP (pd.P i) ≤ K → L ≤ K := by
    intro K i hN hi
    refine c'.le_of_closure (pd.gen_PN i) fun σ hσ => ?_
    rcases hσ with h | h
    · exact c'.mem_of_wP_le hN h
    · exact c'.mem_of_wP_le hi h
  rcases hstepN with hNC | hNN
  · by_cases hex : ∃ i, c'.wP (pd.P i) ≤ CC
    · obtain ⟨i, hi⟩ := hex
      exact hY.2.1 (hL_le' _ i hNC hi)
    · push Not at hex
      exact hY.2.2 (hL_le _ fun i => (hstepS i).resolve_left (hex i))
  · by_cases hex : ∃ i, c'.wP (pd.P i) ≤ NN
    · obtain ⟨i, hi⟩ := hex
      exact hY.2.2 (hL_le' _ i hNN hi)
    · push Not at hex
      exact hY.2.1 (hL_le _ fun i => (hstepS i).resolve_right (hex i))

private theorem steps_R (c : SixCtx T L) (pd : PermData) (hX : GNSetting X T)
    {C₁ C₂ : Subgroup X} (hP : IsC118Pair T C₁ C₂) (hY : GNYComponent T C₁ C₂ L)
    (hDL : gnD T ⊓ lT T L ≤ gnC T) (h1Z : C₁ ≤ omegaOneCenterOf T)
    (hωR : omegaOneCenterOf T ≤ omegaOneCenterOf (T ⊓ nL T L))
    (hD : c.img (T ⊓ nL T L) = pd.D)
    (hRT : T ⊓ nL T L ≤ T) (hCR : T ⊓ gnC T ≤ T ⊓ nL T L)
    (hQR : pCoreOf 2 (⊤ : Subgroup X) ≤ T ⊓ nL T L)
    (hbR : baum (T ⊓ nL T L) = baum T) (hbT : baum T ≤ T ⊓ nL T L)
    (hJR : thompsonJ T ≤ T ⊓ nL T L) (hLR : T ⊓ lT T L ≤ T ⊓ nL T L) :
    (∀ i, (c.toSevenCtx0).wP (pd.P i) ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
      (c.toSevenCtx0).wP (pd.P i) ≤ gnImg T (Subgroup.normalizer (C₂ : Set X))) ∧
    ((c.toSevenCtx0).wP pd.PN ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
      (c.toSevenCtx0).wP pd.PN ≤ gnImg T (Subgroup.normalizer (C₂ : Set X))) := by
  classical
  let c' : A7Lift.SevenCtx0 T L := c.toSevenCtx0
  have hRL : T ⊓ nL T L ≤ nL T L := inf_le_right
  let S := c.subSR pd (T ⊓ nL T L)
  have hRLS : S ≤ nL T L := (c.subSR_le pd).trans hRL
  have himg : c'.img = c.img := rfl
  have hSimg : c'.img S = pd.E := by
    rw [himg]
    exact c.img_subSR pd hRL hD
  have hE8 : Nat.card (c'.img S) = 8 := by rw [hSimg, pd.card_E]
  have hD' : c'.img (T ⊓ nL T L) = pd.D := by rw [himg]; exact hD
  have hodd02 : swap (0 : Fin 7) 2 ∉ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by decide)]; decide
  have hQLS : ∀ σ ∈ c'.img S ⊓ alternatingGroup (Fin 7), ∃ (t : X) (ht : t ∈ S),
      QuotientGroup.mk' (gnC T) t ∈ L ∧ c'.θ ⟨t, hRLS ht⟩ = σ := by
    rintro σ ⟨hσE, hσA⟩
    rw [hSimg] at hσE
    obtain ⟨t, ht, htL, htθ⟩ := c.exists_preimage_of_mem_D_R pd hX hRL hLR hY.1 hD
      ⟨pd.E_le_D hσE, hσA⟩
    exact ⟨t, (c.mem_subSR pd hRL).2 ⟨ht, htθ ▸ hσE⟩, htL, htθ⟩
  have hQLT : ∀ σ ∈ c'.img (T ⊓ nL T L) ⊓ alternatingGroup (Fin 7),
      ∃ (t : X) (ht : t ∈ T ⊓ nL T L),
      QuotientGroup.mk' (gnC T) t ∈ L ∧ c'.θ ⟨t, hRL ht⟩ = σ := by
    rintro σ ⟨hσD, hσA⟩
    rw [hD'] at hσD
    exact c.exists_preimage_of_mem_D_R pd hX hRL hLR hY.1 hD ⟨hσD, hσA⟩
  constructor
  · intro i
    refine c'.step (C₁ := C₁) (C₂ := C₂) (R := S) (P := pd.P i) hX hP hDL
      hRLS ((c.subSR_le pd).trans hRT) (c.inf_gnC_le_subSR pd hRL hCR)
      (c.pCoreOf_le_subSR pd hX hRL hQR)
      (c.baum_subSR pd hX hRL hRT hJR hbT hD)
      (h1Z.trans (c.omegaOneCenterOf_le_subSR pd hX hRL hRT hJR hbT hD)) ?_ ?_ ?_ ?_ hQLS
      (pd.solv_P i)
    · rw [hSimg]; exact pd.E_le_P i
    · rw [pd.card_P i, hE8]
    · exact Or.inr ⟨swap 0 2, hSimg ▸ pd.swap_mem_E, hodd02⟩
    · rw [hSimg]; exact pd.P_notNormal i
  · refine c'.step (C₁ := C₁) (C₂ := C₂) (R := T ⊓ nL T L) (P := pd.PN) hX hP hDL
      hRL hRT hCR hQR hbR (h1Z.trans hωR) ?_ ?_ ?_ ?_ hQLT pd.solv_PN
    · rw [hD']; exact pd.D_le_PN
    · rw [pd.card_PN, hD', pd.card_D]
    · exact Or.inr ⟨swap 0 2, hD' ▸ pd.E_le_D pd.swap_mem_E, hodd02⟩
    · rw [hD']; exact pd.PN_notNormal

theorem false_of_sixCtx_R (c : SixCtx T L) (pd : PermData) (hX : GNSetting X T)
    {C₁ C₂ : Subgroup X} (hP : IsC118Pair T C₁ C₂) (hY : GNYComponent T C₁ C₂ L)
    (hbL : baum T ≤ nL T L) (hD : c.img (T ⊓ nL T L) = pd.D)
    (hC : nV T L ⊓ Subgroup.centralizer (lT T L : Set X) = ⊥) : False := by
  classical
  obtain ⟨hRT, hCR, hQR, hbR, hωR, -⟩ := A7Lift.nT_facts (L := L) hX hbL
  have hbT : baum T ≤ T ⊓ nL T L := hbR ▸ (inf_le_left : baum (T ⊓ nL T L) ≤ T ⊓ nL T L)
  have hLR : T ⊓ lT T L ≤ T ⊓ nL T L :=
    inf_le_inf_left T (Subgroup.comap_mono (Subgroup.le_normalizer (H := L)))
  have hJR : thompsonJ T ≤ T ⊓ nL T L :=
    le_inf (iSup₂_le fun _ hA => hA.1)
      (fun x hx => thompsonJ_le_normalizer_of_isComponentOf hX hY.1 ⟨x, hx, rfl⟩)
  obtain ⟨-, h1Z, -, -, -, -, -⟩ := id hP
  have hL := hY.1
  have hDL : gnD T ⊓ lT T L ≤ gnC T := by
    by_contra hcon
    refine FiveThreeAlt.false_of_gnD_alt7 hX hL c.eL hC c.φ c.hφ (fun l hl u v huv => ?_) hcon
    have hlN : l ∈ nL T L := Subgroup.le_normalizer hl
    rw [c.hφe' ⟨l, hlN⟩ u v huv, c.hθL ⟨l, hlN⟩ ⟨_, hl⟩ rfl]
  obtain ⟨hstepS, hstepN⟩ :=
    steps_R c pd hX hP hY hDL h1Z hωR hD hRT hCR hQR hbR hbT hJR hLR
  exact colour_contradiction c.toSevenCtx0 pd hY hstepS hstepN

end SixCtx

end CFSG.AGLEmbeddingD2.McLaughlin.A7Six

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Lift

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.A7Six
  CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry Equiv Equiv.Perm

variable {X : Type} [Group X] [Finite X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)}

private theorem centralizes_nV_of_centralizes_L (c : SixCtx T L) {g : X}
    (hg : ∀ l ∈ L, QuotientGroup.mk' (gnC T) g * l = l * QuotientGroup.mk' (gnC T) g) :
    ∀ u ∈ nV T L, g * u * g⁻¹ = u := by
  intro u hu
  have hgnL : g ∈ nL T L := by
    rw [nL, Subgroup.mem_comap, Subgroup.mem_normalizer_iff_map_conj_eq]
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      rw [← hxy]
      show QuotientGroup.mk' (gnC T) g * y * (QuotientGroup.mk' (gnC T) g)⁻¹ ∈ L
      rw [show QuotientGroup.mk' (gnC T) g * y * (QuotientGroup.mk' (gnC T) g)⁻¹ = y by
        rw [hg y hy]; group]
      exact hy
    · intro hx
      refine ⟨x, hx, ?_⟩
      show QuotientGroup.mk' (gnC T) g * x * (QuotientGroup.mk' (gnC T) g)⁻¹ = x
      rw [hg x hx]; group
  have hθg : c.θ ⟨g, hgnL⟩ = 1 := by
    rw [c.hθ1]
    intro l hl
    rw [hg l hl]
    group
  have hv : g * u * g⁻¹ ∈ nV T L :=
    (Subgroup.mem_normalizer_iff.1 (SixCtx.nL_le_normalizer_nV (normal_gnV T) hgnL) u).1 hu
  have h1 := c.hφe' ⟨g, hgnL⟩ ⟨u, hu⟩ ⟨g * u * g⁻¹, hv⟩ rfl
  rw [hθg, altAct_one] at h1
  have h2 : c.φ ⟨g * u * g⁻¹, hv⟩ = c.φ ⟨u, hu⟩ :=
    Multiplicative.toAdd.injective h1
  exact congrArg Subtype.val (c.hφ.1 h2)

theorem false_of_alt7_natural_gen
    (hX : GNSetting X T) {C₁ C₂ : Subgroup X} (hP : IsC118Pair T C₁ C₂)
    (hY : GNYComponent T C₁ C₂ L) (eL : ↥L ≃* alternatingGroup (Fin 7))
    (hn : FiveThreeAlt.A7NaturalCase T L) : False := by
  classical
  obtain ⟨-, h1Z, -, -, h2B, h2c, -⟩ := id hP
  have hJ := commutator_eq_of_gnYComponent hX h1Z h2B h2c hY
  have h6 := relIndex_six_of_natural hX hP hY eL hn
  have h6' : (nV T L ⊓ Subgroup.centralizer (lT T L : Set X)).relIndex (nV T L) = 2 ^ 6 := h6
  have hne : nV T L ≠ ⊥ := by
    intro hbot
    have h1 : (nV T L ⊓ Subgroup.centralizer (lT T L : Set X)).relIndex (nV T L) = 1 := by
      rw [hbot, bot_inf_eq, Subgroup.relIndex_bot_right]
    rw [h6'] at h1
    norm_num at h1
  obtain ⟨θs, hθs, hθsL, hθs1⟩ := exists_thetaS T L eL
  obtain ⟨hC, φ, hφ, hφe⟩ := FiveThreeAlt.natural_of_relIndex_six hX hY.1 hJ eL h6
    (θs.comp (πN T L)) (fun g l l' h => hθs (πN T L g) l l' h)
    (fun g l h => hθsL (πN T L g) l h)
  let c₀ : SixCtx T L := ⟨eL, θs, hθs, hθsL, hθs1, φ, hφ, hφe⟩
  have hcent : ∀ g : X, (∀ l ∈ L, QuotientGroup.mk' (gnC T) g * l =
      l * QuotientGroup.mk' (gnC T) g) → ∀ u ∈ nV T L, g * u * g⁻¹ = u :=
    fun g hg => centralizes_nV_of_centralizes_L c₀ hg
  have hbL : baum T ≤ nL T L := baum_le_nL hX hY.1 hne hC hcent
  let R := T ⊓ nL T L
  have hRL : R ≤ nL T L := inf_le_right
  have hRT : R ≤ T := inf_le_left
  have hLR : T ⊓ lT T L ≤ R :=
    inf_le_inf_left T (Subgroup.comap_mono (Subgroup.le_normalizer (H := L)))
  have hJR : thompsonJ T ≤ R :=
    le_inf (iSup₂_le fun _ hA => hA.1)
      (fun x hx => thompsonJ_le_normalizer_of_isComponentOf hX hY.1 ⟨x, hx, rfl⟩)
  obtain ⟨σ, hσ⟩ := c₀.exists_conj_img_R hX hRL hRT hJR hLR hY.1 hJ sixPermData.card_D
  exact (c₀.conj σ).false_of_sixCtx_R sixPermData hX hP hY hbL hσ hC

end CFSG.AGLEmbeddingD2.McLaughlin.A7Lift
