module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackage
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackageCore
import CFSG.GroupTheory.CommutatorPreimageCenter
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevCentralQuotient
import CFSG.GH74.BNPair.Lemma3013

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.ABGLocalTools CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {L U P D M : Subgroup G} {ℳ : Set (Subgroup G)}

private theorem relIndex_sup_eq_of_le_normalizer {H N : Subgroup G}
    (h : H ≤ Subgroup.normalizer (N : Set G)) : N.relIndex (H ⊔ N) = N.relIndex H := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N h).toEquiv.symm

theorem IsGomiLeviPackage.le_normalizer_sup (h : IsGomiLeviPackage L U P ℳ)
    (hD : IsGomiLeviCore P D) (hM : M ∈ ℳ) : P ≤ normalizer ((D ⊔ M : Subgroup G) : Set G) := by
  have hsup : D ⊔ M = D ⊔ (pCoreOf 2 P ⊔ M) := by
    rw [← sup_assoc, sup_eq_left.mpr hD.pCoreOf_le]
  rw [hsup]
  exact (le_inf hD.le_normalizer (h.normal M hM)).trans
    (Subgroup.inf_normalizer_le_normalizer_sup D (pCoreOf 2 P ⊔ M))

theorem IsGomiLeviPackage.inf_eq_center (h : IsGomiLeviPackage L U P ℳ)
    (hD : IsGomiLeviCore P D) (hM : M ∈ ℳ) : D ⊓ M = (center ↥M).map M.subtype := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxD, hxM⟩ := hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    have hR : ⁅x, (y : G)⁆ ∈ pCoreOf 2 P := ((hD x).mp hxD).2 (y : G) (h.le_parabolic M hM y.2)
    have hMmem : ⁅x, (y : G)⁆ ∈ M :=
      Subgroup.commutator_le_self M (Subgroup.commutator_mem_commutator hxM y.2)
    have hbot : ⁅x, (y : G)⁆ = 1 := by
      have hmem : ⁅x, (y : G)⁆ ∈ (⊥ : Subgroup G) := by
        rw [← h.inf_eq_bot M hM]
        exact ⟨hR, hMmem⟩
      simpa using hmem
    exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp hbot).symm
  · rintro _ ⟨m, hm, rfl⟩
    rw [Subgroup.mem_inf]
    refine ⟨?_, m.2⟩
    exact (hD (m : G)).mpr ⟨h.le_parabolic M hM m.2, fun p hp =>
      h.center_commutator_le M hM (Subgroup.commutator_mem_commutator
        (Subgroup.mem_map.mpr ⟨m, hm, rfl⟩) hp)⟩

theorem IsGomiLeviPackage.pCore_eq_bot [Finite G] (h : IsGomiLeviPackage L U P ℳ)
    (hM : M ∈ ℳ) : CFSG.pCore 2 ↥M = ⊥ := by
  let R : Subgroup G := pCoreOf 2 P
  let Q : Subgroup G := (CFSG.pCore 2 ↥M).map M.subtype
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
  have hQ2 : IsPGroup 2 Q :=
    (CFSG.LieType.BorelTits.pCore_isPGroup 2).map M.subtype
  have hQM : Q ≤ M := Subgroup.map_subtype_le _
  have hMP : M ≤ P := h.le_parabolic M hM
  have hRnorm : P ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hRQ2 : IsPGroup 2 ↥(R ⊔ Q) :=
    hR2.to_sup_of_normal_left' hQ2 (hQM.trans (hMP.trans hRnorm))
  have hRQle : R ⊔ Q ≤ R ⊔ M := sup_le le_sup_left (hQM.trans le_sup_right)
  have hnormRQ : R ⊔ M ≤ Subgroup.normalizer ((R ⊔ Q : Subgroup G) : Set G) := by
    refine sup_le (le_sup_left.trans Subgroup.le_normalizer) ?_
    exact (le_inf (hMP.trans hRnorm)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup R Q)
  have hRQcore : R ⊔ Q ≤ pCoreOf 2 (R ⊔ M) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRQle hnormRQ hRQ2
  have hcoreR : pCoreOf 2 (R ⊔ M) ≤ R := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (R ⊔ M))
    · exact (CFSG.LieType.BorelTits.pCoreOf_le 2 (R ⊔ M)).trans
        (sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 P) hMP)
    · exact (h.normal M hM).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (R ⊔ M))
  have hQbot : Q ≤ (⊥ : Subgroup G) := by
    rw [← h.inf_eq_bot M hM]
    exact le_inf (le_sup_right.trans (hRQcore.trans hcoreR)) hQM
  exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp
    (le_bot_iff.mp hQbot)

theorem IsGomiLeviPackage.coprime_card_center [Finite G] (h : IsGomiLeviPackage L U P ℳ)
    (hM : M ∈ ℳ) : Nat.Coprime (Nat.card (center ↥M)) 2 :=
  ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
    (CFSG.GH74.BNPair.not_dvd_card_center (p := 2) (G := ↥M)
      (h.pCore_eq_bot hM))).symm

theorem IsGomiLeviPackage.ne_bot (h : IsGomiLeviPackage L U P ℳ) (hM : M ∈ ℳ) : M ≠ ⊥ := by
  intro hbot
  subst M
  have : Nonempty ↥(⊥ : Subgroup G) := ⟨⟨1, Subgroup.one_mem _⟩⟩
  have : Subsingleton ↥(⊥ : Subgroup G) :=
    ⟨fun a b => Subtype.ext (by rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
  have hfac := h.factor ⊥ hM
  rcases hfac with hq | hs6 | hcov
  · have hsimple := IsGomiChevTwo.isSimpleGroup hq
    obtain ⟨x, y, hxy⟩ := hsimple.toNontrivial.exists_pair_ne
    exact hxy (Subsingleton.elim x y)
  · obtain ⟨e⟩ := hs6
    have hcard : Nat.card ↥(⊥ : Subgroup G) = Nat.card (Equiv.Perm (Fin 6)) :=
      Nat.card_congr e.toEquiv
    have h1 : Nat.card ↥(⊥ : Subgroup G) = 1 := Nat.card_unique
    have h720 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      norm_num
    omega
  · rw [inf_bot_eq] at hcov
    exact (lt_irrefl (⊥ : Subgroup G)) hcov.lt

theorem IsGomiLeviPackage.two_dvd_relIndex [Finite G] (h : IsGomiLeviPackage L U P ℳ)
    (hD : IsGomiLeviCore P D) (hM : M ∈ ℳ) : 2 ∣ D.relIndex (D ⊔ M) := by
  have hMN : M ≤ Subgroup.normalizer (D : Set G) := (h.le_parabolic M hM).trans hD.le_normalizer
  have hrel : D.relIndex (D ⊔ M) = (D ⊓ M).relIndex M := by
    rw [sup_comm, relIndex_sup_eq_of_le_normalizer hMN, Subgroup.inf_relIndex_right]
  have hcenter : ((center ↥M).map M.subtype).relIndex M = (center ↥M).index := by
    change (((center ↥M).map M.subtype).subgroupOf M).index = (center ↥M).index
    rw [← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self (by rw [Subgroup.ker_subtype]; exact bot_le)]
  have hZodd : ¬ 2 ∣ Nat.card (center ↥M) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp (h.coprime_card_center hM).symm
  have h2M : 2 ∣ Nat.card ↥M := by
    by_contra h2
    have hbot : pElementSubgroup 2 M = ⊥ := by
      rw [eq_bot_iff, pElementSubgroup, Subgroup.closure_le]
      rintro x ⟨hxM, k, hk⟩
      change x ∈ (⊥ : Subgroup G)
      rw [Subgroup.mem_bot]
      by_contra hx1
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hx1 (orderOf_eq_one_iff.mp (by simpa using hk))
      have hdvd : 2 ∣ orderOf x := by
        rw [hk]
        exact dvd_pow_self 2 hk0
      exact h2 (hdvd.trans (Subgroup.orderOf_dvd_natCard M hxM))
    exact h.ne_bot hM (by rw [← h.pElementSubgroup_eq M hM, hbot])
  have hindex : 2 ∣ (center ↥M).index := by
    have hmul : 2 ∣ Nat.card (center ↥M) * (center ↥M).index := by
      rw [Subgroup.card_mul_index]
      exact h2M
    rcases (Nat.prime_two.dvd_mul).mp hmul with h' | h'
    · exact absurd h' hZodd
    · exact h'
  rw [hrel, h.inf_eq_center hD hM, hcenter]
  exact hindex

theorem IsGomiLeviPackage.commutator_le_of_ne (h : IsGomiLeviPackage L U P ℳ)
    (hD : IsGomiLeviCore P D) {M₁ M₂ : Subgroup G} (hM₁ : M₁ ∈ ℳ) (hM₂ : M₂ ∈ ℳ)
    (hne : D ⊔ M₁ ≠ D ⊔ M₂) : ⁅D ⊔ M₁, D ⊔ M₂⁆ ≤ D := by
  have hM₁P : M₁ ≤ P := h.le_parabolic M₁ hM₁
  have hM₂P : M₂ ≤ P := h.le_parabolic M₂ hM₂
  have hne' : M₁ ≠ M₂ := fun hEq => hne (by rw [hEq])
  have hcomm : ⁅M₁, M₂⁆ = ⊥ := h.commute M₁ hM₁ M₂ hM₂ hne'
  let D' : Subgroup ↥P := D.subgroupOf P
  have : D'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hD.le).mpr hD.le_normalizer
  let π : ↥P →* ↥P ⧸ D' := QuotientGroup.mk' D'
  have hker : π.ker = D' := QuotientGroup.ker_mk' D'
  have hM' : ⁅M₁.subgroupOf P, M₂.subgroupOf P⁆ = ⊥ := by
    refine (Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).mp ?_
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hM₁P,
      Subgroup.map_subgroupOf_eq_of_le hM₂P, hcomm]
  have hmap : (⁅(D ⊔ M₁).subgroupOf P, (D ⊔ M₂).subgroupOf P⁆).map π = ⊥ := by
    have h1 : ((D ⊔ M₁).subgroupOf P).map π = (M₁.subgroupOf P).map π := by
      rw [Subgroup.subgroupOf_sup hD.le hM₁P, Subgroup.map_sup, QuotientGroup.map_mk'_self,
        bot_sup_eq]
    have h2 : ((D ⊔ M₂).subgroupOf P).map π = (M₂.subgroupOf P).map π := by
      rw [Subgroup.subgroupOf_sup hD.le hM₂P, Subgroup.map_sup, QuotientGroup.map_mk'_self,
        bot_sup_eq]
    rw [Subgroup.map_commutator, h1, h2, ← Subgroup.map_commutator, hM', Subgroup.map_bot]
  have hle : ⁅(D ⊔ M₁).subgroupOf P, (D ⊔ M₂).subgroupOf P⁆ ≤ D' := by
    rw [← hker]
    exact (Subgroup.map_eq_bot_iff _).mp hmap
  calc ⁅D ⊔ M₁, D ⊔ M₂⁆
      = (⁅(D ⊔ M₁).subgroupOf P, (D ⊔ M₂).subgroupOf P⁆).map P.subtype := by
        rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (sup_le hD.le hM₁P),
          Subgroup.map_subgroupOf_eq_of_le (sup_le hD.le hM₂P)]
    _ ≤ D'.map P.subtype := Subgroup.map_mono hle
    _ = D := Subgroup.map_subgroupOf_eq_of_le hD.le

theorem IsGomiLeviPackage.inf_sSup_le (h : IsGomiLeviPackage L U P ℳ)
    (hD : IsGomiLeviCore P D) (hM : M ∈ ℳ) :
    (D ⊔ M) ⊓ sSup ((fun M' => D ⊔ M') '' ℳ \ {D ⊔ M}) ≤ D := by
  let N : Subgroup G := sSup {M' : Subgroup G | M' ∈ ℳ ∧ D ⊔ M' ≠ D ⊔ M}
  have hNP : N ≤ P := sSup_le fun M' hM' => h.le_parabolic M' hM'.1
  have hNM : N ≤ Subgroup.centralizer (M : Set G) := by
    refine sSup_le fun M' hM' => ?_
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (h.commute M' hM'.1 M hM fun hEq => hM'.2 (by rw [hEq]))
  have hcore : (D ⊔ M) ⊓ (D ⊔ N) ≤ D :=
    sup_inf_sup_le_of_commutator_le
      ((h.le_parabolic M hM).trans hD.le_normalizer)
      (hNP.trans hD.le_normalizer) hNM
      ((Subgroup.commutator_mono le_rfl (h.le_parabolic M hM)).trans hD.commutator_le)
      (h.inf_eq_bot M hM) ((h.inf_eq_center hD hM).ge.trans inf_le_left)
  have hsSup : sSup ((fun M' => D ⊔ M') '' ℳ \ {D ⊔ M}) ≤ D ⊔ N := by
    refine sSup_le fun K hK => ?_
    rw [Set.mem_diff] at hK
    obtain ⟨M', hM', hEq⟩ := (Set.mem_image (fun M' => D ⊔ M') ℳ K).mp hK.1
    rw [← hEq]
    have hmem : M' ∈ {M'' : Subgroup G | M'' ∈ ℳ ∧ D ⊔ M'' ≠ D ⊔ M} :=
      ⟨hM', fun h => hK.2 (hEq.symm.trans h)⟩
    exact sup_le_sup_left (le_sSup hmem) D
  exact (inf_le_inf_left (D ⊔ M) hsSup).trans hcore

theorem IsGomiLeviPackage.nonempty [Finite G] (hU : IsSylowOf 2 U L)
    (hBP : L ⊓ normalizer (U : Set G) < P) (hPL : P ≤ L) (h : IsGomiLeviPackage L U P ℳ) :
    ℳ.Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hUP : U ≤ P := (le_inf hU.le Subgroup.le_normalizer).trans (le_of_lt hBP)
  have hUR : U ≤ pCoreOf 2 P := by
    have hle := h.sylow_le
    rw [hne, sSup_empty, sup_bot_eq] at hle
    exact hle
  have hRU : pCoreOf 2 P ≤ U := pCoreOf_le_of_isSylowOf_of_le hU hUP hPL
  have hPN : P ≤ normalizer (U : Set G) := by
    rw [le_antisymm hUR hRU]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  exact (not_le_of_gt hBP) (le_inf hPL hPN)

theorem IsGomiLeviPackage.le_sup_sSup [Finite G] (hU : IsSylowOf 2 U L)
    (hBP : L ⊓ normalizer (U : Set G) < P) (hPL : P ≤ L) (h : IsGomiLeviPackage L U P ℳ) :
    P ≤ L ⊓ normalizer (U : Set G) ⊔ sSup ℳ := by
  obtain ⟨M₀, hM₀⟩ := h.nonempty hU hBP hPL
  have : Nonempty ℳ := ⟨⟨M₀, hM₀⟩⟩
  let R : Subgroup G := pCoreOf 2 P
  let K : Subgroup G := R ⊔ sSup ℳ
  have hKP : K ≤ P := sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 P)
    (sSup_le fun M hM => h.le_parabolic M hM)
  have hKN : P ≤ Subgroup.normalizer (K : Set G) := by
    have hMsup : P ≤ Subgroup.normalizer ((⨆ M : ℳ, (R ⊔ (M : Subgroup G))) : Subgroup G) := by
      refine (le_iInf ?_).trans
        (Subgroup.iInf_normalizer_le_normalizer_iSup (fun M : ℳ => R ⊔ (M : Subgroup G)))
      intro M
      exact h.normal (M : Subgroup G) M.2
    have hK : (⨆ M : ℳ, (R ⊔ (M : Subgroup G))) = K := by
      change (⨆ M : ℳ, (R ⊔ (M : Subgroup G))) = R ⊔ sSup ℳ
      rw [sSup_eq_iSup', ← sup_iSup]
    rwa [hK] at hMsup
  have hUP : U ≤ P := h.sylow_le.trans hKP
  have hU' : IsSylowOf 2 (U.subgroupOf P) (K.subgroupOf P) := by
    refine (isSylowOf_map_subtype_iff (p := 2) P).mp ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hUP, Subgroup.map_subgroupOf_eq_of_le hKP]
    exact IsSylowOf.of_le hU h.sylow_le (hKP.trans hPL)
  have : (K.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKP).mpr hKN
  obtain ⟨Q, hQ⟩ := hU'
  have hfr : Subgroup.normalizer (Q.map (K.subgroupOf P).subtype) ⊔ K.subgroupOf P = ⊤ :=
    Sylow.normalizer_sup_eq_top Q
  rw [hQ] at hfr
  have hfr' : (P ⊓ normalizer (U : Set G)) ⊔ K = P := by
    have h := congrArg (Subgroup.map P.subtype) hfr
    rwa [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
      ← inf_normalizer_eq_map_normalizer_subgroupOf hUP,
      Subgroup.map_subgroupOf_eq_of_le hKP] at h
  have hPle : P ≤ K ⊔ (P ⊓ normalizer (U : Set G)) :=
    hfr'.ge.trans (le_of_eq (sup_comm _ _))
  have hRB : R ≤ L ⊓ normalizer (U : Set G) := by
    have hRU : R ≤ U := pCoreOf_le_of_isSylowOf_of_le hU hUP hPL
    exact le_inf (hRU.trans hU.le) (hRU.trans Subgroup.le_normalizer)
  calc P ≤ K ⊔ (P ⊓ normalizer (U : Set G)) := hPle
    _ ≤ (L ⊓ normalizer (U : Set G)) ⊔ sSup ℳ := by
        refine sup_le ?_ ?_
        · exact sup_le (hRB.trans le_sup_left) le_sup_right
        · exact (inf_le_inf_right (normalizer (U : Set G)) hPL).trans le_sup_left

end CFSG.GroupTheory
