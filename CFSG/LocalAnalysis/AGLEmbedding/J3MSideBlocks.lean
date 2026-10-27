module

public import CFSG.LocalAnalysis.AGLEmbedding.J3Facts
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaPThree
import CFSG.LocalAnalysis.AGLEmbedding.TwoLocalPairBlockRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section J3MSide

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}

theorem D1J3Data.not_injective_blocks (h : D1J3Data P M H R) (hB3 : StmtBlockThree)
    (L : Fin 4 → Subgroup G) (hL : ∀ i, IsWeakSBlock M (pCoreOf 2 H) (L i)) :
    ¬ Function.Injective L := by
  intro hinj
  have h1 := h.surv.ph3.toD1Escape.toTwoLocalPair.card_le_pRank_three_of_blocks
    (fun _ hL' => hB3 h.surv.ph3 hL') L hL hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  have := h.pRank_le
  omega

theorem D1J3Data.sq_mem_normalizer (h : D1J3Data P M H R) (hB3 : StmtBlockThree) {s : G}
    (hsK : s ∈ H ⊓ M) (hs2 : IsPGroup 2 (Subgroup.zpowers s)) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) : s ^ 2 ∈ Subgroup.normalizer (L : Set G) := by
  by_contra hs
  have hKeq := h.surv.ph3.inf_eq_inf_normalizer_twoCore
  have hsS : s ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := (hKeq ▸ hsK).2
  have hsM : s ∈ M := hsK.2
  have key : ∀ k : ℕ, 0 < k → k < 4 → s ^ k ∉ Subgroup.normalizer (L : Set G) := by
    intro k hk0 hk4 hk
    apply hs
    interval_cases k
    · simpa using Subgroup.pow_mem _ hk 2
    · exact hk
    · obtain ⟨a, ha⟩ := hs2 ⟨s, Subgroup.mem_zpowers s⟩
      have hs1 : s ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
      obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hs1)
      have hcop : (3 : ℕ).Coprime (orderOf s) := by
        rw [hb]
        exact Nat.Coprime.pow_right b (by norm_num)
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
      exact Subgroup.pow_mem _ (hm ▸ Subgroup.pow_mem _ hk m) 2
  let Lj : Fin 4 → Subgroup G := fun j => L.map (MulAut.conj (s ^ (j : ℕ))).toMonoidHom
  have hLj : ∀ j, IsWeakSBlock M (pCoreOf 2 H) (Lj j) := fun j =>
    hL.map_conj (M.pow_mem hsM _) (Subgroup.pow_mem _ hsS _)
  refine h.not_injective_blocks hB3 Lj hLj ?_
  have hstep : ∀ i j : ℕ, i < j → L.map (MulAut.conj (s ^ i)).toMonoidHom =
      L.map (MulAut.conj (s ^ j)).toMonoidHom →
        s ^ (j - i) ∈ Subgroup.normalizer (L : Set G) := by
    intro i j hij hh
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hj : s ^ j = s ^ i * s ^ (j - i) := by rw [← pow_add]; congr 1; omega
    rw [hj, map_conj_mul_eq] at hh
    exact (Subgroup.map_injective (MulAut.conj (s ^ i)).injective hh).symm
  intro i j hij
  simp only [Lj] at hij
  by_contra hne
  have hne' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
  · exact key (j - i) (by omega) (by omega) (hstep i j hlt hij)
  · exact key (i - j) (by omega) (by omega) (hstep j i hlt hij.symm)

theorem D1J3Data.le_normalizer_block (h : D1J3Data P M H R) (hB3 : StmtBlockThree)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    R ≤ Subgroup.normalizer (L : Set G) := by
  by_contra hRL
  have h3 := h.surv.ph3
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  have hR3 : IsPGroup 3 R := h3.isPGroup_R
  set N₀ : Subgroup G := R ⊓ Subgroup.normalizer (L : Set G) with hN₀
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR3
  have hdvd : N₀.relIndex R ∣ 3 ^ k := hk ▸ Subgroup.relIndex_dvd_card _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hne1 : N₀.relIndex R ≠ 1 := fun h1 =>
    hRL ((Subgroup.relIndex_eq_one.mp h1).trans inf_le_right)
  rcases j with _ | _ | j
  · exact hne1 (by simpa using hj)
  ·
    obtain ⟨s, hsK, hsR, hs2, hsing⟩ := h.singer
    exact hsing N₀ inf_le_left (by simpa using hj)
      (Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.pow_mem _ hsR 2, Subgroup.le_normalizer (h.sq_mem_normalizer hB3 hsK hs2 hL)⟩)
  ·
    set N₀' : Subgroup R := N₀.subgroupOf R with hN₀'
    have hcard : 4 ≤ Nat.card (R ⧸ N₀') := by
      have h9 : 3 ^ 2 ≤ 3 ^ (j + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : Nat.card (R ⧸ N₀') = N₀.relIndex R := rfl
      rw [this, hj]
      have : (9 : ℕ) ≤ 3 ^ (j + 1 + 1) := by simpa using h9
      omega
    have : Fintype (R ⧸ N₀') := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card] at hcard
    let f : Fin 4 → R ⧸ N₀' := fun i =>
      (Fintype.equivFin (R ⧸ N₀')).symm (Fin.castLE hcard i)
    have hf : Function.Injective f := fun i j hij =>
      Fin.castLE_injective hcard ((Fintype.equivFin (R ⧸ N₀')).symm.injective hij)
    let r : Fin 4 → R := fun i => (f i).out
    let Lj : Fin 4 → Subgroup G := fun i => L.map (MulAut.conj ((r i : R) : G)).toMonoidHom
    have hLj : ∀ i, IsWeakSBlock M (pCoreOf 2 H) (Lj i) := fun i =>
      hL.map_conj (h3.le_M (r i).2) (hKeq ▸ h3.le_inf (r i).2).2
    refine h.not_injective_blocks hB3 Lj hLj fun i₁ i₂ he => hf ?_
    have hmem : ((r i₁)⁻¹ * r i₂ : R) ∈ N₀' := by
      refine Subgroup.mem_subgroupOf.mpr ⟨((r i₁)⁻¹ * r i₂).2,
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_⟩
      have he' : L.map (MulAut.conj ((r i₁ : R) : G)).toMonoidHom =
          L.map (MulAut.conj ((r i₂ : R) : G)).toMonoidHom := he
      have e2 : ((r i₂ : R) : G) = (r i₁ : G) * (((r i₁)⁻¹ * r i₂ : R) : G) := by simp
      rw [e2, map_conj_mul_eq] at he'
      exact (Subgroup.map_injective (MulAut.conj ((r i₁ : R) : G)).injective he').symm
    calc f i₁ = ((r i₁ : R) : R ⧸ N₀') := (QuotientGroup.out_eq' (f i₁)).symm
      _ = ((r i₂ : R) : R ⧸ N₀') := QuotientGroup.eq.mpr hmem
      _ = f i₂ := QuotientGroup.out_eq' (f i₂)

theorem D1J3Data.faithful (h : D1J3Data P M H R) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hB3 : StmtBlockThree) (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥) {r : G} (hr : r ∈ R)
    (hrC : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → r ∈ blockCentralizer M L) :
    r = 1 := by
  have h3 := h.surv.ph3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hKM : H ⊓ M ≤ M := inf_le_right
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  have hRM : R ≤ M := h3.le_M
  have hR3 : IsPGroup 3 R := h3.isPGroup_R
  set W : Subgroup G := R ⊓ ⨅ (L : Subgroup G) (_ : IsWeakSBlock M (pCoreOf 2 H) L),
    blockCentralizer M L with hWdef
  have hmemW : ∀ w, w ∈ W ↔ w ∈ R ∧ ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      w ∈ blockCentralizer M L := by
    intro w
    simp only [hWdef, Subgroup.mem_inf, Subgroup.mem_iInf]
  have hWn : R ≤ Subgroup.normalizer (W : Set G) := by
    have key : ∀ g ∈ R, ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
      intro g hg w hw
      rw [hmemW] at hw ⊢
      refine ⟨R.mul_mem (R.mul_mem hg hw.1) (R.inv_mem hg), fun L hL => ?_⟩
      have hgK : g⁻¹ ∈ H ⊓ M := h3.le_inf (R.inv_mem hg)
      have hL' := hw.2 _ (hL.map_conj hgK.2 (hKeq ▸ hgK).2)
      obtain ⟨⟨m, hmM⟩, hm, hmw⟩ := hL'
      have hwM : w ∈ M := hRM hw.1
      have hm' : mk ⟨w, hwM⟩ ∈ Subgroup.centralizer
          (barM M (L.map (MulAut.conj g⁻¹).toMonoidHom) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
        have : (⟨m, hmM⟩ : M) = ⟨w, hwM⟩ := Subtype.ext hmw
        rw [← this]
        exact hm
      have hgM : g ∈ M := hRM hg
      refine (mem_blockCentralizer_iff (⟨g, hgM⟩ * ⟨w, hwM⟩ * (⟨g, hgM⟩)⁻¹)).mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [barM_map_conj (M.inv_mem hgM)] at hm'
      have hz' : (mk ⟨g, hgM⟩)⁻¹ * z * mk ⟨g, hgM⟩ ∈ (barM M L).map
          (MulAut.conj (mk ⟨g⁻¹, M.inv_mem hgM⟩)).toMonoidHom := by
        refine ⟨z, hz, ?_⟩
        have e : (⟨g⁻¹, M.inv_mem hgM⟩ : M) = (⟨g, hgM⟩ : M)⁻¹ := rfl
        simp only [MulEquiv.coe_toMonoidHom, e, map_inv]
        rw [MulAut.conj_inv_apply]
      have hc := Subgroup.mem_centralizer_iff.mp hm' _ hz'
      rw [map_mul, map_mul, map_inv]
      calc z * (mk ⟨g, hgM⟩ * mk ⟨w, hwM⟩ * (mk ⟨g, hgM⟩)⁻¹)
          = mk ⟨g, hgM⟩ * (((mk ⟨g, hgM⟩)⁻¹ * z * mk ⟨g, hgM⟩) * mk ⟨w, hwM⟩) *
              (mk ⟨g, hgM⟩)⁻¹ := by group
        _ = mk ⟨g, hgM⟩ * (mk ⟨w, hwM⟩ * ((mk ⟨g, hgM⟩)⁻¹ * z * mk ⟨g, hgM⟩)) *
              (mk ⟨g, hgM⟩)⁻¹ := by rw [hc]
        _ = mk ⟨g, hgM⟩ * mk ⟨w, hwM⟩ * (mk ⟨g, hgM⟩)⁻¹ * z := by group
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨key g hg w, fun hw => ?_⟩
    have := key g⁻¹ (R.inv_mem hg) _ hw
    simpa [mul_assoc] using this
  by_contra hr1
  have hWR : W ≤ R := inf_le_left
  have : Group.IsNilpotent ↥R := hR3.isNilpotent
  have hWn' : (W.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWR).mpr hWn
  have hW1 : W.subgroupOf R ≠ ⊥ := by
    intro hbot
    have hmem : (⟨r, hr⟩ : R) ∈ W.subgroupOf R :=
      Subgroup.mem_subgroupOf.mpr ((hmemW r).mpr ⟨hr, hrC⟩)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hr1 (congrArg Subtype.val hmem)
  obtain ⟨⟨y, hyW, hyZ⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hW1)
  set x : G := (y : G) with hxdef
  have hxR : x ∈ R := y.2
  have hxM : x ∈ M := hRM hxR
  have hxW : x ∈ W := Subgroup.mem_subgroupOf.mp hyW
  have hxX : x ∈ centerOf R := ⟨hxR, Subgroup.mem_centralizer_iff.mpr fun g hg =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hyZ ⟨g, hg⟩)⟩
  have hx1 : x ≠ 1 := fun h1 => hy1 (Subtype.ext (Subtype.ext h1))
  obtain ⟨L₀, hL₀⟩ := h3.exists_weakSBlock h84 hD2
  have hXE := h.surv.le_blockClosure rfl hL₀ (hB3 h3 hL₀)
  set A := Subgroup.zpowers x with hA
  have hAX : A ≤ centerOf R := (Subgroup.zpowers_le).mpr hxX
  set E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := GLBLayer ⊤ with hEdef
  have hAE : barM M A ≤ E := barM_le_of_le_preimage ((hAX.trans hXE).trans
    (blockClosure_le_preimage hKM hL₀.toIsTwoPrimeComponent (fun k hk =>
      le_sSup (hL₀.toIsTwoPrimeComponent.map_conj (hKM hk)).component)))
  have hAcent : ∀ L' : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf L' ⊤ →
      barM M A ≤ Subgroup.centralizer (L' : Set _) := by
    intro L' hL'
    by_cases hex : ∃ k ∈ H ⊓ M, barM M (L₀.map (MulAut.conj k).toMonoidHom) = L'
    · obtain ⟨k, hk, rfl⟩ := hex
      have hxC := ((hmemW x).mp hxW).2 _ (hL₀.map_conj (hKM hk) (hKeq ▸ hk).2)
      have hxC' := (mem_blockCentralizer_iff ⟨x, hxM⟩).mp hxC
      rintro _ ⟨⟨a, haM⟩, ha, rfl⟩
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp ha)
      have e : (⟨a, haM⟩ : M) = (⟨x, hxM⟩ : M) ^ n := Subtype.ext (by
        simp only [Subgroup.coe_zpow]
        exact hn.symm)
      rw [e, map_zpow]
      exact Subgroup.zpow_mem _ hxC' n
    · push Not at hex
      refine barM_le_of_le_preimage ((hAX.trans hXE).trans
        (blockClosure_le_preimage hKM hL₀.toIsTwoPrimeComponent (fun k hk => ?_)))
      have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
        (hL₀.toIsTwoPrimeComponent.map_conj (hKM hk)).component hL' (hex k hk)
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc
  have hAC : barM M A ≤ Subgroup.centralizer (E : Set _) := by
    rw [Subgroup.le_centralizer_iff]
    exact sSup_le fun L' hL' => Subgroup.le_centralizer_iff.mp (hAcent L' hL')
  have hEn : E.Normal := glbLayer_top_normal
  have hZn : (E ⊓ Subgroup.centralizer (E : Set _)).Normal := inferInstance
  have hZ : ∀ a ∈ E ⊓ Subgroup.centralizer (E : Set _),
      ∀ b ∈ E ⊓ Subgroup.centralizer (E : Set _), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb.2 a ha.1
  have hAp : IsPGroup 3 (barM M A) :=
    ((hR3.to_le (hAX.trans inf_le_left)).comap_subtype (K := M)).map _
  have hle := le_pCore_of_le_normal_comm hZn hZ (le_inf hAE hAC) hAp
  rw [hO] at hle
  have hxbar : mk ⟨x, hxM⟩ = 1 := by
    have hmem : mk ⟨x, hxM⟩ ∈ barM M A :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers x))
    exact (Subgroup.mem_bot).mp (hle hmem)
  have hxQ : x ∈ pCoreOf 2 M := coe_mem_pCoreOf_two_of_mk_eq_one _ hxbar
  have hRQ : R ⊓ pCoreOf 2 M = ⊥ := inf_eq_bot_of_isPGroup Nat.prime_three hR3 (by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num))
  have hmem : x ∈ R ⊓ pCoreOf 2 M := ⟨hxR, hxQ⟩
  rw [hRQ, Subgroup.mem_bot] at hmem
  exact hx1 hmem

end J3MSide

end CFSG.AGLEmbedding
