module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614F

open CFSG.Open Subgroup
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (pElementSubgroup pElementSubgroup_le)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
  (relPPrimeCore_normal coprime_card_relPPrimeCore coprime_orderOf_of_mem_relPPrimeCore)

section Generic

variable {G : Type} [Group G]

@[expose] def conjAut {X : Subgroup G} {g : G} (hg : g ∈ normalizer (X : Set G)) : MulAut ↥X where
  toFun x := ⟨g * x * g⁻¹, (mem_normalizer_iff.mp hg x).mp x.2⟩
  invFun x := ⟨g⁻¹ * x * g, (mem_normalizer_iff''.mp hg x).mp x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

@[simp] theorem coe_conjAut {X : Subgroup G} {g : G} (hg : g ∈ normalizer (X : Set G))
    (x : ↥X) : ((conjAut hg x : ↥X) : G) = g * x * g⁻¹ := rfl

theorem mem_normalizer_map_of_characteristic {X : Subgroup G} {C : Subgroup ↥X}
    [C.Characteristic] {g : G} (hg : g ∈ normalizer (X : Set G)) :
    g ∈ normalizer ((C.map X.subtype : Subgroup G) : Set G) := by
  have key : ∀ g' ∈ normalizer (X : Set G), ∀ c ∈ C.map X.subtype,
      g' * c * g'⁻¹ ∈ C.map X.subtype := by
    rintro g' hg' _ ⟨c, hc, rfl⟩
    exact ⟨conjAut hg' c, (characteristic_iff_le_comap.mp inferInstance (conjAut hg')) hc, rfl⟩
  rw [mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun h => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ h
  simpa [mul_assoc] using this

theorem le_normalizer_pCoreOf (p : ℕ) (H : Subgroup G) :
    H ≤ normalizer (pCoreOf p H : Set G) := fun _ hh =>
  mem_normalizer_map_of_characteristic (C := CFSG.pCore p ↥H) (Subgroup.le_normalizer hh)

theorem isPGroup_pCoreOf (p : ℕ) (H : Subgroup G) : IsPGroup p (pCoreOf p H) :=
  CFSG.pCore_isPGroup.map H.subtype

theorem not_nontrivial_of_perfect {Q : Type*} [Group Q] [Group.IsSolvable Q]
    (hQ : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤) : ¬ Nontrivial Q := fun _ =>
  (Group.IsSolvable.commutator_lt_top_of_nontrivial Q).ne hQ

theorem commutator_top_of_surjective {A Q : Type*} [Group A] [Group Q] (f : A →* Q)
    (hf : Function.Surjective f) (hA : ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ = ⊤) :
    ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤ := by
  have h := congrArg (Subgroup.map f) hA
  rwa [Subgroup.map_commutator, Subgroup.map_top_of_surjective f hf] at h

theorem commutator_top_of_commutator_eq {K : Subgroup G} (hK : ⁅K, K⁆ = K) :
    ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hK]

theorem eq_top_of_isPGroup_quotient {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    (hA : ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ = ⊤) (N : Subgroup A) [N.Normal]
    (hN : IsPGroup p (A ⧸ N)) : N = ⊤ := by
  haveI : Group.IsNilpotent (A ⧸ N) := hN.isNilpotent
  by_contra hne
  exact not_nontrivial_of_perfect (commutator_top_of_surjective (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) hA) (QuotientGroup.nontrivial_iff.mpr hne)

theorem isSimpleGroup_quotient {A : Type*} [Group A] (O : Subgroup A) [O.Normal] (hO : O ≠ ⊤)
    (hmax : ∀ N : Subgroup A, N.Normal → O ≤ N → N = O ∨ N = ⊤) :
    IsSimpleGroup (A ⧸ O) := by
  refine { toNontrivial := QuotientGroup.nontrivial_iff.mpr hO,
           eq_bot_or_eq_top_of_normal := fun Q hQ => ?_ }
  have hle : O ≤ Q.comap (QuotientGroup.mk' O) := by
    intro a ha
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff a).mpr ha]
    exact Q.one_mem
  rcases hmax _ (hQ.comap _) hle with h | h
  · left
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective O q
    have ha : a ∈ Q.comap (QuotientGroup.mk' O) := hq
    rw [h] at ha
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff a).mpr ha
  · right
    rw [eq_top_iff]
    intro q _
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective O q
    have ha : a ∈ Q.comap (QuotientGroup.mk' O) := by
      rw [h]
      exact Subgroup.mem_top a
    exact ha

theorem isPGroup_quotient_of_sup {p : ℕ} {W : Type*} [Group W] {J T : Subgroup W} [J.Normal]
    (hJT : J ⊔ T = ⊤) (hT : IsPGroup p T) : IsPGroup p (W ⧸ J) := by
  intro q
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨j, hj, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hJT ▸ Subgroup.mem_top w)
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have ht1 : t ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k, ?_⟩
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff j).mpr hj, one_mul, ← QuotientGroup.mk_pow,
    ht1, QuotientGroup.mk_one]

theorem isPGroup_of_quotient {p : ℕ} {W : Type*} [Group W] {J N : Subgroup W} [J.Normal]
    (hQ : IsPGroup p (W ⧸ J)) (hJ : ∀ w ∈ N, w ∈ J → ∃ k : ℕ, w ^ p ^ k = 1) :
    IsPGroup p ↥N := by
  intro n
  obtain ⟨a, ha⟩ := hQ ((n : W) : W ⧸ J)
  have h1 : (n : W) ^ p ^ a ∈ J := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact ha
  obtain ⟨b, hb⟩ := hJ _ (pow_mem n.2 _) h1
  refine ⟨a + b, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, pow_add, pow_mul, hb, Subgroup.coe_one]

theorem conj_mem_pElementSubgroup {p : ℕ} {K : Subgroup G} {k : G} (hk : k ∈ K) {x : G}
    (hx : x ∈ pElementSubgroup p K) : k * x * k⁻¹ ∈ pElementSubgroup p K := by
  unfold pElementSubgroup at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    refine Subgroup.subset_closure ⟨K.mul_mem (K.mul_mem hk hy.1) (K.inv_mem hk), ?_⟩
    obtain ⟨n, hn⟩ := hy.2
    refine ⟨n, ?_⟩
    have h := orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective y
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply] at h
    rw [h, hn]
  | one => simp
  | mul a b _ _ ha hb =>
    have := Subgroup.mul_mem _ ha hb
    simpa [mul_assoc] using this
  | inv a _ ha =>
    have := Subgroup.inv_mem _ ha
    simpa [mul_assoc] using this

variable [Finite G]

theorem comap_inclusion_pPrimeCore_le {p : ℕ} [Fact p.Prime] {J W : Subgroup G} (hJW : J ≤ W) :
    (CFSG.pPrimeCore p ↥W).comap (Subgroup.inclusion hJW) ≤ CFSG.pPrimeCore p ↥J :=
  le_sSup ⟨CFSG.pPrimeCore_normal.comap _, Nat.Coprime.coprime_dvd_right
    (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hJW))
    CFSG.pPrimeCore_coprime_card⟩

theorem pPrimeCore_le_comap_inclusion {p : ℕ} [Fact p.Prime] {J W : Subgroup G} (hJW : J ≤ W)
    (hWJ : W ≤ normalizer (J : Set G)) :
    CFSG.pPrimeCore p ↥J ≤ (CFSG.pPrimeCore p ↥W).comap (Subgroup.inclusion hJW) := by
  have hNW : (CFSG.pPrimeCore p ↥J).map J.subtype ≤ W := (Subgroup.map_subtype_le _).trans hJW
  have hn : (((CFSG.pPrimeCore p ↥J).map J.subtype).subgroupOf W).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNW).mpr fun _ hw =>
      mem_normalizer_map_of_characteristic (hWJ hw)
  have hc : Nat.Coprime p (Nat.card (((CFSG.pPrimeCore p ↥J).map J.subtype).subgroupOf W)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNW).toEquiv,
      Subgroup.card_map_of_injective J.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hle : ((CFSG.pPrimeCore p ↥J).map J.subtype).subgroupOf W ≤ CFSG.pPrimeCore p ↥W :=
    le_sSup ⟨hn, hc⟩
  intro k hk
  exact hle (Subgroup.mem_subgroupOf.mpr ⟨k, hk, rfl⟩)

theorem comap_inclusion_pPrimeCore_eq {p : ℕ} [Fact p.Prime] {J W : Subgroup G} (hJW : J ≤ W)
    (hWJ : W ≤ normalizer (J : Set G)) :
    (CFSG.pPrimeCore p ↥W).comap (Subgroup.inclusion hJW) = CFSG.pPrimeCore p ↥J :=
  le_antisymm (comap_inclusion_pPrimeCore_le hJW) (pPrimeCore_le_comap_inclusion hJW hWJ)

end Generic

section Component

variable {G : Type} [Group G] [Finite G] {Y H K : Subgroup G} {z : G}

theorem three_dvd_card (hK : PComp 3 Y H K z) : 3 ∣ Nat.card K := by
  obtain ⟨E, hEK, -, hE⟩ := CFSG.RankThreeCoreUniqueness.Helpers.pRank_attained 3 K
    (by rw [hK.rank_one]; norm_num)
  rw [hK.rank_one, pow_one] at hE
  rw [← hE]
  exact Subgroup.card_dvd_of_le hEK

theorem inf_subgroupOf_normal (hK : PComp 3 Y H K z) :
    ((K ⊓ rankThreePrimeCore 3 H).subgroupOf K).Normal := by
  have hD := relPPrimeCore_normal Nat.prime_three H
  refine ⟨fun n hn k => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  refine ⟨K.mul_mem (K.mul_mem k.2 hn.1) (K.inv_mem k.2), ?_⟩
  have := hD.conj_mem ⟨n, hK.le hn.1⟩ (Subgroup.mem_subgroupOf.mpr hn.2) ⟨k, hK.le k.2⟩
  exact Subgroup.mem_subgroupOf.mp this

theorem inf_le_pPrimeCore_map (hK : PComp 3 Y H K z) :
    K ⊓ rankThreePrimeCore 3 H ≤ (CFSG.pPrimeCore 3 ↥K).map K.subtype := by
  have hc : Nat.Coprime 3 (Nat.card ((K ⊓ rankThreePrimeCore 3 H).subgroupOf K)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      (coprime_card_relPPrimeCore Nat.prime_three H)
  have hle : (K ⊓ rankThreePrimeCore 3 H).subgroupOf K ≤ CFSG.pPrimeCore 3 ↥K :=
    le_sSup ⟨inf_subgroupOf_normal hK, hc⟩
  calc K ⊓ rankThreePrimeCore 3 H
      = ((K ⊓ rankThreePrimeCore 3 H).subgroupOf K).map K.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le inf_le_left).symm
    _ ≤ _ := Subgroup.map_mono hle

theorem pPrimeCore_map_eq (hK : PComp 3 Y H K z) :
    (CFSG.pPrimeCore 3 ↥K).map K.subtype = K ⊓ rankThreePrimeCore 3 H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn : (((CFSG.pPrimeCore 3 ↥K).map K.subtype).subgroupOf K).Normal := by
    show (Subgroup.comap K.subtype ((CFSG.pPrimeCore 3 ↥K).map K.subtype)).Normal
    rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    infer_instance
  rcases hK.maximal _ (Subgroup.map_subtype_le _) hn (inf_le_pPrimeCore_map hK) with h | h
  · exact h
  · exfalso
    have hc : Nat.Coprime 3 (Nat.card ((CFSG.pPrimeCore 3 ↥K).map K.subtype)) := by
      rw [Subgroup.card_map_of_injective K.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    rw [h] at hc
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hc (three_dvd_card hK)

theorem pPrimeCore_ne_top (hK : PComp 3 Y H K z) : CFSG.pPrimeCore 3 ↥K ≠ ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h
  have hc : Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 ↥K)) := CFSG.pPrimeCore_coprime_card
  rw [h, Subgroup.card_top] at hc
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hc (three_dvd_card hK)

theorem isSimpleGroup_kbar (hK : PComp 3 Y H K z) : IsSimpleGroup (Kbar K) := by
  refine isSimpleGroup_quotient _ (pPrimeCore_ne_top hK) fun N hN hON => ?_
  have hNK : N.map K.subtype ≤ K := Subgroup.map_subtype_le _
  have hn : ((N.map K.subtype).subgroupOf K).Normal := by
    show (Subgroup.comap K.subtype (N.map K.subtype)).Normal
    rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    exact hN
  have hle : K ⊓ rankThreePrimeCore 3 H ≤ N.map K.subtype :=
    (pPrimeCore_map_eq hK).symm.le.trans (Subgroup.map_mono hON)
  rcases hK.maximal _ hNK hn hle with h | h
  · left
    apply Subgroup.map_injective K.subtype_injective
    rw [h, pPrimeCore_map_eq hK]
  · right
    apply Subgroup.map_injective K.subtype_injective
    rw [h, Subgroup.map_top, Subgroup.range_subtype]

theorem kbar_nonabelian (hK : PComp 3 Y H K z) : ∃ a b : Kbar K, a * b ≠ b * a := by
  haveI := isSimpleGroup_kbar hK
  by_contra h
  haveI : Group.IsSolvable (Kbar K) := Group.isSolvable_of_comm fun a b => by
    by_contra hab
    exact h ⟨a, b, hab⟩
  exact not_nontrivial_of_perfect
    (commutator_top_of_surjective (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))
      (QuotientGroup.mk'_surjective _) (commutator_top_of_commutator_eq hK.perfect)) inferInstance

theorem center_kbar (hK : PComp 3 Y H K z) : center (Kbar K) = ⊥ := by
  haveI := isSimpleGroup_kbar hK
  obtain ⟨a, b, hab⟩ := kbar_nonabelian hK
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (Kbar K)) with h | h
  · exact h
  · have ha : a ∈ center (Kbar K) := h ▸ Subgroup.mem_top a
    exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab

theorem three_dvd_card_kbar (hK : PComp 3 Y H K z) : 3 ∣ Nat.card (Kbar K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := three_dvd_card hK
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pPrimeCore 3 ↥K)] at h3
  exact Nat.Coprime.dvd_of_dvd_mul_right CFSG.pPrimeCore_coprime_card h3

theorem pElementSubgroup_eq (hK : PComp 3 Y H K z)
    (hD2 : IsPGroup 2 (rankThreePrimeCore 3 H)) : pElementSubgroup 3 K = K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJK : pElementSubgroup 3 K ≤ K := pElementSubgroup_le K
  haveI hJn : ((pElementSubgroup 3 K).subgroupOf K).Normal := ⟨fun n hn k =>
    Subgroup.mem_subgroupOf.mpr (conj_mem_pElementSubgroup k.2 (Subgroup.mem_subgroupOf.mp hn))⟩
  haveI := inf_subgroupOf_normal hK
  have hsup : pElementSubgroup 3 K ⊔ (K ⊓ rankThreePrimeCore 3 H) = K := by
    have hn : ((pElementSubgroup 3 K ⊔ (K ⊓ rankThreePrimeCore 3 H)).subgroupOf K).Normal := by
      rw [Subgroup.subgroupOf_sup hJK inf_le_left]
      infer_instance
    rcases hK.maximal _ (sup_le hJK inf_le_left) hn le_sup_right with h | h
    · exfalso
      obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 (three_dvd_card hK)
      have hkJ : (k : G) ∈ pElementSubgroup 3 K := Subgroup.subset_closure ⟨k.2, 1, by
        rw [pow_one, Subgroup.orderOf_coe, hk]⟩
      have hkD : (k : G) ∈ rankThreePrimeCore 3 H := (le_sup_left.trans h.le hkJ).2
      have hc := coprime_orderOf_of_mem_relPPrimeCore hkD
      rw [Subgroup.orderOf_coe, hk] at hc
      exact absurd ((Nat.coprime_self 3).mp hc) (by norm_num)
    · exact h
  have htop : (pElementSubgroup 3 K).subgroupOf K ⊔ (K ⊓ rankThreePrimeCore 3 H).subgroupOf K =
      ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJK,
      Subgroup.map_subgroupOf_eq_of_le inf_le_left, hsup, Subgroup.map_top,
      Subgroup.range_subtype]
  have hQ : IsPGroup 2 (↥K ⧸ (pElementSubgroup 3 K).subgroupOf K) :=
    isPGroup_quotient_of_sup htop (hD2.to_le inf_le_right).comap_subtype
  have hJtop : (pElementSubgroup 3 K).subgroupOf K = ⊤ :=
    eq_top_of_isPGroup_quotient (commutator_top_of_commutator_eq hK.perfect) _ hQ
  calc pElementSubgroup 3 K = ((pElementSubgroup 3 K).subgroupOf K).map K.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hJK).symm
    _ = K := by rw [hJtop, Subgroup.map_top, Subgroup.range_subtype]

end Component

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614F
