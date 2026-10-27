module

public import CFSG.LocalAnalysis.AGLEmbedding.A9MSideBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
import CFSG.LocalAnalysis.AGLEmbedding.EscapeRankBar

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Conj

variable {G : Type} [Group G]

private theorem map_conj_inv_map_conj_self (A : Subgroup G) (g : G) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
  rw [← map_conj_mul_eq, inv_mul_cancel]
  ext x
  simp

private theorem inv_mul_mem_normalizer_of_map_conj_eq {A : Subgroup G} {a g : G}
    (he : A.map (MulAut.conj g).toMonoidHom = A.map (MulAut.conj a).toMonoidHom) :
    a⁻¹ * g ∈ Subgroup.normalizer (A : Set G) := by
  have h1 : A.map (MulAut.conj (a⁻¹ * g)).toMonoidHom = A := by
    rw [map_conj_mul_eq, he]
    exact map_conj_inv_map_conj_self A a
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1

private theorem mem_normalizer_map_conj_of_conj_mem {A : Subgroup G} {a g : G}
    (h : a⁻¹ * g * a ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ Subgroup.normalizer ((A.map (MulAut.conj a).toMonoidHom : Subgroup G) : Set G) := by
  have h' : A.map (MulAut.conj (a⁻¹ * g * a)).toMonoidHom = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp h
  have h1 : (A.map (MulAut.conj a).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj a).toMonoidHom := by
    rw [← map_conj_mul_eq, show g * a = a * (a⁻¹ * g * a) by group, map_conj_mul_eq, h']
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1

private theorem card_le_of_inf_eq_bot {U A B C : Subgroup G} (hker : U ⊓ (A ⊓ B ⊓ C) = ⊥)
    (hA : A.relIndex U ≤ 3) (hB : B.relIndex U ≤ 3) (hC : C.relIndex U ≤ 3) :
    Nat.card U ≤ 3 ^ 3 := by
  have hle : (A ⊓ B ⊓ C).relIndex U ≤ A.relIndex U * B.relIndex U * C.relIndex U :=
    Subgroup.relIndex_inf_le.trans (Nat.mul_le_mul_right _ Subgroup.relIndex_inf_le)
  rw [← Subgroup.inf_relIndex_left U, hker, Subgroup.relIndex_bot_left] at hle
  exact hle.trans (Nat.mul_le_mul (Nat.mul_le_mul hA hB) hC)

end Conj

section A9MSide

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X : Subgroup G} {σ z : G}

theorem D1A9DataCore.closure_le_centralizer (h : D1A9DataCore P M H R X σ z) :
    Subgroup.closure ({σ, z} : Set G) ≤
      Subgroup.centralizer ((Subgroup.closure ({σ, z} : Set G) : Subgroup G) : Set G) := by
  have hσz : σ * z = z * σ := Subgroup.mem_centralizer_iff.mp h.z_center σ h.σ_mem
  have hcomm : ({σ, z} : Set G).Pairwise Commute := by
    intro a ha b hb _
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    all_goals first | exact Commute.refl _ | exact hσz | exact hσz.symm
  exact Subgroup.le_centralizer_iff_isMulCommutative.mpr (Subgroup.isMulCommutative_closure hcomm)

theorem D1A9DataCore.not_mem_normalizer_of_isWeakSBlock (h : D1A9DataCore P M H R X σ z)
    (hB3 : StmtBlockThree) {L L' : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hL' : IsWeakSBlock M (pCoreOf 2 H) L') (hσL : σ ∉ Subgroup.normalizer (L : Set G)) :
    σ ∉ Subgroup.normalizer (L' : Set G) := by
  intro hσL'
  apply hσL
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hσL' ⊢
  obtain he | he | he := h.eq_of_not_mem_normalizer hB3 hL hL' hσL
  · rwa [he] at hσL'
  · rw [he] at hσL'
    exact Subgroup.map_injective (MulAut.conj σ).injective hσL'
  · rw [he] at hσL'
    exact Subgroup.map_injective (MulAut.conj σ).injective
      (Subgroup.map_injective (MulAut.conj σ).injective hσL')

theorem D1A9DataCore.not_mem_blockCentralizer (h : D1A9DataCore P M H R X σ z)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥)
    {L L' : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hL' : IsWeakSBlock M (pCoreOf 2 H) L') (hσL : σ ∉ Subgroup.normalizer (L : Set G)) :
    z ∉ blockCentralizer M L' := by
  intro hz
  have hσM : σ ∈ M := h.surv.ph3.le_M h.σ_mem
  have hσz : σ * z * σ⁻¹ = z := by
    rw [Subgroup.mem_centralizer_iff.mp h.z_center σ h.σ_mem, mul_inv_cancel_right]
  have step : ∀ A : Subgroup G, z ∈ blockCentralizer M A →
      z ∈ blockCentralizer M (A.map (MulAut.conj σ).toMonoidHom) := fun A hA => by
    have h1 := conj_mem_blockCentralizer (L := A.map (MulAut.conj σ).toMonoidHom) hσM (w := z)
      (by rwa [map_conj_inv_map_conj_self])
    rwa [hσz] at h1
  refine h.z_ne (h.surv.eq_one_of_forall_mem h84 hD2 hB3 hO h.z_mem fun L'' hL'' => ?_)
  obtain he | he | he := h.eq_of_not_mem_normalizer hB3 hL' hL''
    (h.not_mem_normalizer_of_isWeakSBlock hB3 hL hL' hσL)
  · rwa [he]
  · rw [he]
    exact step _ hz
  · rw [he]
    exact step _ (step _ hz)

theorem D1A9DataCore.eq_one_of_mem_sylow (h : D1A9DataCore P M H R X σ z) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hB3 : StmtBlockThree) (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥)
    {u : G} (hu : u ∈ (P : Subgroup G))
    (huC : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → u ∈ blockCentralizer M L) :
    u = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := h.surv.ph3
  have hPM : (P : Subgroup G) ≤ M := h3.sylow_le
  set W : Subgroup G := (P : Subgroup G) ⊓
    ⨅ (L : Subgroup G) (_ : IsWeakSBlock M (pCoreOf 2 H) L), blockCentralizer M L with hWdef
  have hmemW : ∀ w, w ∈ W ↔ w ∈ (P : Subgroup G) ∧ ∀ L : Subgroup G,
      IsWeakSBlock M (pCoreOf 2 H) L → w ∈ blockCentralizer M L := by
    intro w
    simp only [hWdef, Subgroup.mem_inf, Subgroup.mem_iInf]
  have key : ∀ g ∈ (P : Subgroup G), ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
    intro g hg w hw
    rw [hmemW] at hw ⊢
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hw.1) (Subgroup.inv_mem _ hg), fun L hL =>
      conj_mem_blockCentralizer (hPM hg)
        (hw.2 _ (h.isWeakSBlock_map_conj hB3 hL (M.inv_mem (hPM hg))))⟩
  have hWn : (P : Subgroup G) ≤ Subgroup.normalizer (W : Set G) := fun g hg =>
    Subgroup.mem_normalizer_iff.mpr fun w => ⟨key g hg w, fun hw => by
      simpa [mul_assoc] using key g⁻¹ (Subgroup.inv_mem _ hg) _ hw⟩
  by_contra hu1
  have hWP : W ≤ P := inf_le_left
  have : Group.IsNilpotent ↥(P : Subgroup G) := P.isPGroup'.isNilpotent
  have : (W.subgroupOf (P : Subgroup G)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWP).mpr hWn
  have hW1 : W.subgroupOf (P : Subgroup G) ≠ ⊥ := by
    intro hbot
    have hmem : (⟨u, hu⟩ : ↥(P : Subgroup G)) ∈ W.subgroupOf (P : Subgroup G) :=
      Subgroup.mem_subgroupOf.mpr ((hmemW u).mpr ⟨hu, huC⟩)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hu1 (congrArg Subtype.val hmem)
  have hA := Group.IsNilpotent.inf_center_ne_bot_of_normal hW1
  have hA3 : 3 ∣ Nat.card ↥(W.subgroupOf (P : Subgroup G) ⊓ Subgroup.center ↥(P : Subgroup G)) := by
    rcases (P.isPGroup'.to_subgroup _).card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hA
    · exact h1
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 hA3
  obtain ⟨y, hyW, hy3, hyC⟩ : ∃ y : G, y ∈ W ∧ orderOf y = 3 ∧
      y ∈ Subgroup.centralizer ((P : Subgroup G) : Set G) := by
    refine ⟨((w : ↥(P : Subgroup G)) : G), Subgroup.mem_subgroupOf.mp w.2.1, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2.2 ⟨g, hg⟩)
  have hDR : Subgroup.closure ({σ, z} : Set G) ≤ R := (Subgroup.closure_le R).mpr
    (Set.insert_subset_iff.mpr ⟨h.σ_mem, Set.singleton_subset_iff.mpr (h.surv.le_R h.z_mem)⟩)
  have hDP : Subgroup.closure ({σ, z} : Set G) ≤ P := hDR.trans h3.le_P
  have hyCD : y ∈ Subgroup.centralizer
      ((Subgroup.closure ({σ, z} : Set G) : Subgroup G) : Set G) :=
    Subgroup.centralizer_le hDP hyC
  by_cases hyD : y ∈ Subgroup.closure ({σ, z} : Set G)
  · have hyX : y ∈ X := h.centerOf_le ⟨hDR hyD, Subgroup.centralizer_le h3.le_P hyC⟩
    have h1 := h.surv.eq_one_of_forall_mem h84 hD2 hB3 hO hyX ((hmemW y).mp hyW).2
    rw [h1, orderOf_one] at hy3
    exact absurd hy3 (by norm_num)
  · obtain ⟨E, hED, hE, hEc⟩ := pRank_attained 3 Nat.prime_three
      (Subgroup.closure ({σ, z} : Set G))
    have h2 := pRank_centralizer_le_two_of_normalizer_not_le Nat.prime_three P hPM
      h3.weakCore_le (hDR.trans h3.le_M) (h3.isPGroup_R.to_le hDR) h.two_le_pRank_closure
      h.escape
    have hy3' : y ^ 3 = 1 := by
      rw [← hy3]
      exact pow_orderOf_eq_one y
    have h4 := succ_le_pRank_of_isElemAbelian_of_mem_centralizer Nat.prime_three hE hEc hy3'
      (fun hyE => hyD (hED hyE)) (Subgroup.centralizer_le hED hyCD)
      (le_inf (hED.trans (hDR.trans h3.le_M)) (hED.trans h.closure_le_centralizer))
      ⟨hPM (hWP hyW), hyCD⟩
    have h5 := h.two_le_pRank_closure
    omega

theorem D1A9DataCore.index_normalizer_le (h : D1A9DataCore P M H R X σ z) (hB3 : StmtBlockThree)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hσL : σ ∉ Subgroup.normalizer (L : Set G)) :
    ((Subgroup.normalizer (L : Set G)).subgroupOf (P : Subgroup G)).index ≤ 3 := by
  have h3 := h.surv.ph3
  have hσP : σ ∈ (P : Subgroup G) := h3.le_P h.σ_mem
  have hsurj : Function.Surjective fun i : Fin 3 =>
      (QuotientGroup.mk ((⟨σ, hσP⟩ : ↥(P : Subgroup G)) ^ (i : ℕ)) :
        ↥(P : Subgroup G) ⧸ (Subgroup.normalizer (L : Set G)).subgroupOf (P : Subgroup G)) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain he | he | he := h.eq_of_not_mem_normalizer hB3 hL
      (h.isWeakSBlock_map_conj hB3 hL (h3.sylow_le g.2)) hσL
    · refine ⟨⟨0, by norm_num⟩, QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ?_)⟩
      simpa using Subgroup.mem_normalizer_iff_map_conj_eq.mpr he
    · refine ⟨⟨1, by norm_num⟩, QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ?_)⟩
      simpa using inv_mul_mem_normalizer_of_map_conj_eq he
    · refine ⟨⟨2, by norm_num⟩, QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ?_)⟩
      have he' : L.map (MulAut.conj (g : G)).toMonoidHom =
          L.map (MulAut.conj (σ ^ 2)).toMonoidHom := by
        rw [he, pow_two, map_conj_mul_eq]
      simpa using inv_mul_mem_normalizer_of_map_conj_eq he'
  calc ((Subgroup.normalizer (L : Set G)).subgroupOf (P : Subgroup G)).index
      = Nat.card (↥(P : Subgroup G) ⧸
          (Subgroup.normalizer (L : Set G)).subgroupOf (P : Subgroup G)) := rfl
    _ ≤ Nat.card (Fin 3) := Nat.card_le_card_of_surjective _ hsurj
    _ = 3 := by simp

theorem D1A9DataCore.normalizer_subgroupOf_normal (h : D1A9DataCore P M H R X σ z)
    (hB3 : StmtBlockThree) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hσL : σ ∉ Subgroup.normalizer (L : Set G)) :
    ((Subgroup.normalizer (L : Set G)).subgroupOf (P : Subgroup G)).Normal := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N₁ := (Subgroup.normalizer (L : Set G)).subgroupOf (P : Subgroup G) with hN₁
  have hσP : σ ∈ (P : Subgroup G) := h.surv.ph3.le_P h.σ_mem
  have hle : N₁.index ≤ 3 := h.index_normalizer_le hB3 hL hσL
  have hne : N₁.index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one] at h1
    have hmem : (⟨σ, hσP⟩ : ↥(P : Subgroup G)) ∈ N₁ := by
      rw [h1]
      exact Subgroup.mem_top _
    exact hσL (Subgroup.mem_subgroupOf.mp hmem)
  obtain ⟨n, hn⟩ := P.isPGroup'.index N₁
  have hi : N₁.index = 3 := by
    rcases n with _ | _ | n
    · exact absurd (by rw [hn, pow_zero]) hne
    · rw [hn, pow_one]
    · have h9 : 9 ≤ 3 ^ (n + 1 + 1) :=
        (show 9 = 3 ^ 2 by norm_num).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [← hn] at h9
      omega
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hk0 : k ≠ 0 := by
    rintro rfl
    have hdvd := N₁.index_dvd_card
    rw [hi, hk, pow_zero] at hdvd
    exact absurd (Nat.le_of_dvd one_pos hdvd) (by norm_num)
  exact Subgroup.normal_of_index_eq_minFac_card
    (by rw [hi, hk, Nat.Prime.pow_minFac Nat.prime_three hk0])

theorem D1A9DataCore.mem_normalizer_map_conj (h : D1A9DataCore P M H R X σ z) (hB3 : StmtBlockThree)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hσL : σ ∉ Subgroup.normalizer (L : Set G)) {g : G} (hgP : g ∈ (P : Subgroup G))
    (hgL : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer ((L.map (MulAut.conj σ).toMonoidHom : Subgroup G) : Set G) ∧
      g ∈ Subgroup.normalizer (((L.map (MulAut.conj σ).toMonoidHom).map
        (MulAut.conj σ).toMonoidHom : Subgroup G) : Set G) := by
  have hn := h.normalizer_subgroupOf_normal hB3 hL hσL
  have hσP : σ ∈ (P : Subgroup G) := h.surv.ph3.le_P h.σ_mem
  have step : ∀ g ∈ (P : Subgroup G), g ∈ Subgroup.normalizer (L : Set G) →
      σ⁻¹ * g * σ ∈ (P : Subgroup G) ∧ σ⁻¹ * g * σ ∈ Subgroup.normalizer (L : Set G) := by
    intro g hgP hgL
    have h1 := hn.conj_mem ⟨g, hgP⟩ (Subgroup.mem_subgroupOf.mpr hgL)
      (⟨σ, hσP⟩ : ↥(P : Subgroup G))⁻¹
    rw [Subgroup.mem_subgroupOf] at h1
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hσP) hgP) hσP, ?_⟩
    simpa using h1
  obtain ⟨h1P, h1L⟩ := step g hgP hgL
  exact ⟨mem_normalizer_map_conj_of_conj_mem h1L,
    mem_normalizer_map_conj_of_conj_mem (mem_normalizer_map_conj_of_conj_mem (step _ h1P h1L).2)⟩

theorem D1A9DataCore.eq_sylow_of_forall_card_le_three (h : D1A9DataCore P M H R X σ z)
    (hB3 : StmtBlockThree) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (hD2 : D1NoXBlock)
    (ha : KFactBlockCyclicThree) (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hσL : σ ∉ Subgroup.normalizer (L : Set G))
    (hcyc : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M L' → IsElemAbelian 3 E →
        Nat.card E ≤ 3) : R = (P : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := h.surv.ph3
  have hPM : (P : Subgroup G) ≤ M := h3.sylow_le
  have hσK : σ ∈ H ⊓ M := h3.le_inf h.σ_mem
  have hσS : σ ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    (h3.inf_eq_inf_normalizer_twoCore ▸ hσK).2
  have hL₁ := hL.map_conj hσK.2 hσS
  have hL₂ := hL₁.map_conj hσK.2 hσS
  set N₁ := (Subgroup.normalizer (L : Set G)).subgroupOf (P : Subgroup G) with hN₁
  set P₁ : Subgroup G := N₁.map (P : Subgroup G).subtype with hP₁
  have hP₁P : P₁ ≤ P := Subgroup.map_subtype_le _
  have hP₁M : P₁ ≤ M := hP₁P.trans hPM
  have hP₁3 : IsPGroup 3 P₁ := P.isPGroup'.to_le hP₁P
  have hP₁L : ∀ g ∈ P₁, g ∈ Subgroup.normalizer (L : Set G) := by
    rintro _ ⟨g, hg, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hg
  have hU3 : IsPGroup 3 (barM M P₁) :=
    (hP₁3.comap_subtype (K := M)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
  have hUN : ∀ A : Subgroup G, (∀ g ∈ P₁, g ∈ Subgroup.normalizer (A : Set G)) →
      barM M P₁ ≤ Subgroup.normalizer (barM M A : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro A hA _ ⟨m, hm, rfl⟩
    have hmA : A.map (MulAut.conj (m : G)).toMonoidHom = A :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA _ (Subgroup.mem_subgroupOf.mp hm))
    have h1 := barM_map_conj m.2 A
    rw [hmA] at h1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1.symm
  have hU₀ := hUN L hP₁L
  have hU₁ := hUN _ fun g hg => (h.mem_normalizer_map_conj hB3 hL hσL (hP₁P hg) (hP₁L g hg)).1
  have hU₂ := hUN _ fun g hg => (h.mem_normalizer_map_conj hB3 hL hσL (hP₁P hg) (hP₁L g hg)).2
  have hk : ∀ A : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) A →
      barM M P₁ ≤ Subgroup.normalizer (barM M A : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      (Subgroup.centralizer (barM M A : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex (barM M P₁) ≤
        3 := fun A hA hUA => by
    have h1 := ha G M (pCoreOf 2 H) A h3.isKGroup.1 h3.asc81bHyp hA
      (h3.nineThree_not_one h85 hD2 hA).1 (h3.not_isSylowTwoOf_inf h85 hD2 hA)
      (fun Y hY hYp => h.coprime_card_of_perfect hY hYp)
      (coprime_three_card_center hO hA.component.2.1) (hcyc A hA) (barM M P₁) hUA hU3
    rwa [Subgroup.inf_relIndex_left] at h1
  have hker : barM M P₁ ⊓
      (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.centralizer (barM M (L.map (MulAut.conj σ).toMonoidHom) :
          Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.centralizer (barM M ((L.map (MulAut.conj σ).toMonoidHom).map
          (MulAut.conj σ).toMonoidHom) : Set (↥M ⧸ CFSG.pCore 2 ↥M))) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨m, hm, rfl⟩, ⟨hc₀, hc₁⟩, hc₂⟩
    have hm1 : (m : G) = 1 := h.eq_one_of_mem_sylow h84 hD2 hB3 hO
      (hP₁P (Subgroup.mem_subgroupOf.mp hm)) fun L' hL' => by
        obtain he | he | he := h.eq_of_not_mem_normalizer hB3 hL hL' hσL
        · rw [he]
          exact (mem_blockCentralizer_iff m).mpr hc₀
        · rw [he]
          exact (mem_blockCentralizer_iff m).mpr hc₁
        · rw [he]
          exact (mem_blockCentralizer_iff m).mpr hc₂
    rw [Subgroup.mem_bot, show m = 1 from Subtype.ext hm1, map_one]
  have hU27 : Nat.card (barM M P₁) ≤ 3 ^ 3 :=
    card_le_of_inf_eq_bot hker (hk L hL hU₀) (hk _ hL₁ hU₁) (hk _ hL₂ hU₂)
  have hP₁U : Nat.card P₁ = Nat.card (barM M P₁) :=
    Nat.card_congr (nonempty_mulEquiv_barM hP₁M hP₁3).some.toEquiv.symm
  have hN₁P₁ : Nat.card N₁ = Nat.card P₁ :=
    (Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective).symm
  have hcardP : Nat.card ↥(P : Subgroup G) ≤ 3 ^ 4 := by
    rw [← N₁.index_mul_card, hN₁P₁, hP₁U]
    calc N₁.index * Nat.card (barM M P₁) ≤ 3 * 3 ^ 3 :=
          Nat.mul_le_mul (h.index_normalizer_le hB3 hL hσL) hU27
      _ = 3 ^ 4 := by norm_num
  exact Subgroup.eq_of_le_of_card_ge h3.le_P (by rw [h.card_R]; exact hcardP)

end A9MSide

end CFSG.AGLEmbedding
