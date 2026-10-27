module

public import CFSG.LocalAnalysis.GH72.Sec5Roles
public import CFSG.LocalAnalysis.GH72.MaxInvariant
import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.LocalAnalysis.ComponentClassification.FooteLitCoprime
public import CFSG.LocalAnalysis.GH72.Sec5Tools

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools

namespace G5a

section Sup

variable {G : Type*} [Group G]

theorem relIndex_sup_of_le_normalizer {H K : Subgroup G} (hHK : H ≤ normalizer (K : Set G)) :
    K.relIndex (H ⊔ K) = K.relIndex H := by
  have := normal_subgroupOf_sup_of_le_normalizer hHK
  have h := relIndex_sup_right (H.subgroupOf (H ⊔ K)) (K.subgroupOf (H ⊔ K))
  rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self, relIndex_top_right,
    relIndex_subgroupOf le_sup_left] at h
  exact h

theorem card_sup_eq_relIndex_mul_card {H K : Subgroup G} (hHK : H ≤ normalizer (K : Set G)) :
    Nat.card (H ⊔ K : Subgroup G) = K.relIndex H * Nat.card K := by
  have h := relIndex_mul_card K (H ⊔ K)
  rw [inf_eq_left.mpr le_sup_right, relIndex_sup_of_le_normalizer hHK] at h
  exact h.symm

theorem odd_card_sup_of_le_normalizer {H K : Subgroup G} (hHK : H ≤ normalizer (K : Set G))
    (hH : Odd (Nat.card H)) (hK : Odd (Nat.card K)) : Odd (Nat.card (H ⊔ K : Subgroup G)) := by
  rw [card_sup_eq_relIndex_mul_card hHK]
  exact (hH.of_dvd_nat (relIndex_dvd_card K H)).mul hK

theorem relIndex_sup_left_of_le_normalizer [Finite G] {H K : Subgroup G}
    (hHK : H ≤ normalizer (K : Set G)) : H.relIndex (H ⊔ K) = H.relIndex K := by
  have h1 := relIndex_mul_card H (H ⊔ K)
  have h2 := relIndex_mul_card K H
  have h3 := relIndex_mul_card H K
  rw [inf_eq_left.mpr le_sup_left, card_sup_eq_relIndex_mul_card hHK] at h1
  rw [inf_comm] at h2
  have hpos : 0 < K.relIndex H * Nat.card (H ⊓ K : Subgroup G) := by
    rw [h2]
    exact Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc H.relIndex (H ⊔ K) * (K.relIndex H * Nat.card (H ⊓ K : Subgroup G))
      = H.relIndex (H ⊔ K) * Nat.card H := by rw [h2]
    _ = K.relIndex H * Nat.card K := h1
    _ = H.relIndex K * (K.relIndex H * Nat.card (H ⊓ K : Subgroup G)) := by
        rw [← h3]
        ring

end Sup

section Sylow

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem isSylowOf_of_not_dvd_relIndex {T J K : Subgroup G} (hT : IsSylowOf p T J) (hJK : J ≤ K)
    (hp : ¬ p ∣ J.relIndex K) : IsSylowOf p T K := by
  rw [isSylowOf_iff] at hT ⊢
  obtain ⟨hTJ, hTp, hdvd⟩ := hT
  refine ⟨hTJ.trans hJK, hTp, fun h => ?_⟩
  rw [← relIndex_mul_relIndex T J K hTJ hJK] at h
  exact ((Nat.Prime.dvd_mul Fact.out).mp h).elim hdvd hp

theorem eq_of_inf_normalizer_le {P Q : Subgroup G} (hQ : IsPGroup p Q) (hPQ : P ≤ Q)
    (h : Q ⊓ normalizer (P : Set G) ≤ P) : P = Q := by
  by_contra hne
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hU : P.subgroupOf Q < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [subgroupOf_eq_top] at htop
    exact hne (le_antisymm hPQ htop)
  obtain ⟨y, hy, hyU⟩ := SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hU)
  rw [← subgroupOf_normalizer_eq hPQ, mem_subgroupOf] at hy
  exact hyU (mem_subgroupOf.mpr (h ⟨y.2, hy⟩))

end Sylow

section Odd

variable {G : Type*} [Group G]

theorem map_subgroupOf_eq_top_of_le_sup {K₀ OK J : Subgroup G} {L : Type*} [Group L]
    (f : K₀ →* L) (hf : Function.Surjective f) (hker : f.ker = OK.subgroupOf K₀) (hOK : OK ≤ K₀)
    (hJK : J ≤ K₀) (hcov : K₀ ≤ J ⊔ OK) : (J.subgroupOf K₀).map f = ⊤ := by
  have hK₀OK : K₀ ≤ normalizer (OK : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hOK).mp (hker ▸ f.normal_ker)
  rw [eq_top_iff]
  intro l _
  obtain ⟨k, rfl⟩ := hf l
  have hk : (k : G) ∈ ((J ⊔ OK : Subgroup G) : Set G) := hcov k.2
  rw [coe_mul_of_left_le_normalizer_right J OK (hJK.trans hK₀OK)] at hk
  obtain ⟨j, hj, o, ho, hjo⟩ := hk
  have hjk : (⟨j, hJK hj⟩ : K₀) * ⟨o, hOK ho⟩ = k := Subtype.ext hjo
  have ho1 : f ⟨o, hOK ho⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact ho
  refine ⟨⟨j, hJK hj⟩, hj, ?_⟩
  rw [← hjk, map_mul, ho1, mul_one]

theorem normal_map_subgroupOf_of_le_normalizer {K₀ J T : Subgroup G} {L : Type*} [Group L]
    (f : K₀ →* L) (hJ : (J.subgroupOf K₀).map f = ⊤) (hTK : T ≤ K₀)
    (hJT : J ≤ normalizer (T : Set G)) : ((T.subgroupOf K₀).map f).Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff, ← hJ]
  refine (map_mono ?_).trans (le_normalizer_map f)
  rw [← subgroupOf_normalizer_eq hTK]
  exact fun x hx => hJT hx

theorem covers_of_inf_le {H H' K₀ OK : Subgroup G} (h : Covers H K₀ OK) (hle : H ⊓ K₀ ≤ H') :
    Covers H' K₀ OK := by
  unfold Covers at h ⊢
  exact h.trans (sup_le_sup_right (le_inf hle inf_le_right) _)

theorem covers_mono {H H' K₀ OK : Subgroup G} (h : Covers H K₀ OK) (hHH' : H ≤ H') :
    Covers H' K₀ OK :=
  covers_of_inf_le h (inf_le_left.trans hHH')

theorem commutator_le_of_normal {H L Q J : Subgroup G} (hLH : L ≤ H)
    (hL : (L.subgroupOf H).Normal) (hQH : Q ≤ H) (hJL : J ≤ L) : ⁅Q, J⁆ ≤ L := by
  rw [commutator_le]
  intro a ha b hb
  have hconj : a * b * a⁻¹ ∈ L :=
    mem_subgroupOf.mp (hL.conj_mem ⟨b, hLH (hJL hb)⟩ (mem_subgroupOf.mpr (hJL hb)) ⟨a, hQH ha⟩)
  rw [commutatorElement_def]
  exact mul_mem hconj (inv_mem (hJL hb))

theorem commutator_le_O {K Q J : Subgroup G} (hQ : Q ≤ O K) (hJ : J ≤ K) : ⁅Q, J⁆ ≤ O K := by
  rw [commutator_le]
  intro a ha b hb
  rw [commutatorElement_def, show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
  exact mul_mem (hQ ha)
    ((mem_normalizer_iff.mp (le_normalizer_O K (hJ hb)) _).mp (inv_mem (hQ ha)))

theorem eq_or_eq_of_isSimpleGroup_of_le_sup {K K₀ OK J N : Subgroup G} {T : Type*} [Group T]
    [IsSimpleGroup T] (f : K₀ →* T) (hf : Function.Surjective f)
    (hker : f.ker = OK.subgroupOf K₀) (hOK : OK ≤ K₀) (hJK₀ : J ≤ K₀) (hcov : K₀ ≤ J ⊔ OK)
    (hJK : J ≤ K) (hJO : J ⊓ OK ≤ O K) (hJN : J ≤ normalizer (N : Set G)) (hON : O K ≤ N)
    (hNL : N ≤ J ⊔ O K) : N = O K ∨ N = J ⊔ O K := by
  have hJmap := map_subgroupOf_eq_top_of_le_sup f hf hker hOK hJK₀ hcov
  have hn : (((N ⊓ J).subgroupOf K₀).map f).Normal :=
    normal_map_subgroupOf_of_le_normalizer f hJmap (inf_le_right.trans hJK₀)
      (fun j hj => inf_normalizer_le_normalizer_inf ⟨hJN hj, le_normalizer hj⟩)
  have hJOK : J ≤ normalizer (O K : Set G) := hJK.trans (le_normalizer_O K)
  have := hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((N ⊓ J).subgroupOf K₀).map f) with h | h
  · left
    refine le_antisymm (fun n hn' => ?_) hON
    have hn'' : n ∈ ((J ⊔ O K : Subgroup G) : Set G) := hNL hn'
    rw [coe_mul_of_left_le_normalizer_right J (O K) hJOK] at hn''
    obtain ⟨j, hj, o, ho, rfl⟩ := hn''
    have hjN : j ∈ N := by
      have : j = j * o * o⁻¹ := by group
      rw [this]
      exact N.mul_mem hn' (N.inv_mem (hON ho))
    have hjker : (⟨j, hJK₀ hj⟩ : K₀) ∈ f.ker :=
      (Subgroup.map_eq_bot_iff _).mp h (mem_subgroupOf.mpr ⟨hjN, hj⟩)
    rw [hker] at hjker
    exact (O K).mul_mem (hJO ⟨hj, hjker⟩) ho
  · right
    refine le_antisymm hNL (sup_le (fun j hj => ?_) hON)
    have hfj : f ⟨j, hJK₀ hj⟩ ∈ ((N ⊓ J).subgroupOf K₀).map f := by
      rw [h]
      exact mem_top _
    obtain ⟨n, hn', hnj⟩ := hfj
    have hker' : n⁻¹ * ⟨j, hJK₀ hj⟩ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hnj, inv_mul_cancel]
    rw [hker, mem_subgroupOf] at hker'
    have hnN : (n : G) ∈ N := (mem_subgroupOf.mp hn').1
    have hnJ : (n : G) ∈ J := (mem_subgroupOf.mp hn').2
    have hmem : (n : G)⁻¹ * j ∈ J ⊓ OK := ⟨J.mul_mem (J.inv_mem hnJ) hj, by simpa using hker'⟩
    have : j = n * ((n : G)⁻¹ * j) := by group
    rw [this]
    exact N.mul_mem hnN (hON (hJO hmem))

variable [Finite G]

theorem sup_eq_of_card_le {K₀ OK Z : Subgroup G} {L : Type*} [Group L] (f : K₀ →* L)
    (hf : Function.Surjective f) (hker : f.ker = OK.subgroupOf K₀) (hOKK₀ : OK ≤ K₀)
    (hOK : Odd (Nat.card OK)) (hZK₀ : Z ≤ K₀) (hZ2 : IsPGroup 2 Z)
    (hcard : Nat.card L ≤ Nat.card Z) : Z ⊔ OK = K₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK₀OK : K₀ ≤ normalizer (OK : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hOKK₀).mp (hker ▸ f.normal_ker)
  have hcop : Nat.Coprime (Nat.card OK) (Nat.card Z) := by
    obtain ⟨n, hn⟩ := hZ2.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hOK)
  have hrel : OK.relIndex Z = Nat.card Z := by
    have h := relIndex_mul_card OK Z
    rw [inf_eq_bot_of_coprime hcop, card_bot, mul_one] at h
    exact h
  have hcardK₀ : Nat.card K₀ = Nat.card L * Nat.card OK := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv, hker,
      Nat.card_congr (subgroupOfEquivOfLe hOKK₀).toEquiv]
  refine eq_of_le_of_card_ge (sup_le hZK₀ hOKK₀) ?_
  rw [hcardK₀, card_sup_eq_relIndex_mul_card (hZK₀.trans hK₀OK), hrel]
  exact Nat.mul_le_mul_right _ hcard

theorem O_inf_centralizer_le_of_mem {K W : Subgroup G} {w : G} (hw : w ∈ W)
    (h : O K ⊓ C w ≤ O (C w)) :
    O K ⊓ centralizer (W : Set G) ≤ O (centralizer (W : Set G)) := by
  have hCW : centralizer (W : Set G) ≤ C w := centralizer_le (Set.singleton_subset_iff.mpr hw)
  exact fun x hx => G5d.O_inf_le_O_of_le hCW ⟨h ⟨hx.1, hCW hx.2⟩, hx.2⟩

theorem le_O_of_odd_of_le_sup {H K₀ OK J E : Subgroup G} {L : Type*} [Group L] (f : K₀ →* L)
    (hf : Function.Surjective f) (hker : f.ker = OK.subgroupOf K₀) (hL : CFSG.oddCore L = ⊥)
    (hOK : OK ≤ K₀) (hJH : J ≤ H) (hJK : J ≤ K₀) (hcov : K₀ ≤ J ⊔ OK) (hint : J ⊓ OK ≤ O H)
    (hE : E ≤ J ⊔ O H) (hEodd : Odd (Nat.card E)) (hJE : J ≤ normalizer (E : Set G)) :
    E ≤ O H := by
  have hEH : E ≤ H := hE.trans (sup_le hJH (map_subtype_le _))
  set T : Subgroup G := (E ⊔ O H) ⊓ J with hT
  have hTK : T ≤ K₀ := inf_le_right.trans hJK
  have hTodd : Odd (Nat.card T) :=
    (odd_card_sup_of_le_normalizer (hEH.trans (le_normalizer_O H)) hEodd
      (card_O_odd H)).of_dvd_nat (card_dvd_of_le inf_le_left)
  have hJT : J ≤ normalizer (T : Set G) := fun j hj =>
    inf_normalizer_le_normalizer_inf
      ⟨inf_normalizer_le_normalizer_sup E (O H) ⟨hJE hj, le_normalizer_O H (hJH hj)⟩,
        le_normalizer hj⟩
  have hTn : ((T.subgroupOf K₀).map f).Normal :=
    normal_map_subgroupOf_of_le_normalizer f
      (map_subgroupOf_eq_top_of_le_sup f hf hker hOK hJK hcov) hTK hJT
  have hTodd' : Odd (Nat.card ((T.subgroupOf K₀).map f)) := by
    refine Odd.of_dvd_nat ?_ (card_map_dvd _ f)
    rwa [Nat.card_congr (subgroupOfEquivOfLe hTK).toEquiv]
  have hbot : (T.subgroupOf K₀).map f = ⊥ :=
    le_bot_iff.mp ((le_oddCore_of_normal hTn hTodd').trans hL.le)
  have hTO : T ≤ O H := by
    intro t ht
    have ht' : (⟨t, hTK ht⟩ : K₀) ∈ f.ker := (Subgroup.map_eq_bot_iff _).mp hbot ht
    rw [hker] at ht'
    exact hint ⟨ht.2, ht'⟩
  intro e he
  have he' : e ∈ ((J ⊔ O H : Subgroup G) : Set G) := hE he
  rw [coe_mul_of_left_le_normalizer_right _ _ (hJH.trans (le_normalizer_O H))] at he'
  obtain ⟨j, hj, o, ho, rfl⟩ := he'
  have hjT : j ∈ T := by
    refine ⟨?_, hj⟩
    have : j = j * o * o⁻¹ := by group
    rw [this]
    exact mul_mem_sup he ((O H).inv_mem ho)
  exact (O H).mul_mem (hTO hjT) ho

end Odd

section PConstraint

variable {G : Type} [Group G] [Finite G]

theorem pConstrainedWrt_of_commutator_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A H Q Z : Subgroup G} (hA : IsPGroup 2 A) (hAH : A ≤ H) (hZA : Z ≤ A)
    (hAZ : A ≤ normalizer (Z : Set G)) (hQ : IsPGroup p Q) (hAQ : A ≤ normalizer (Q : Set G))
    (hZQ : ¬ Z ≤ centralizer (Q : Set G)) (hle : ⁅Q, Z⁆ ≤ O H) :
    Sec4Setting.PConstrainedWrt p A H Z := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZQn : Z ≤ normalizer (Q : Set G) := hZA.trans hAQ
  have hRQ : ⁅Q, Z⁆ ≤ Q := le_normalizer_iff_commutator_le_left.mp hZQn
  have hAR : A ≤ normalizer ((⁅Q, Z⁆ : Subgroup G) : Set G) :=
    ComponentClassification.FooteLit.le_normalizer_commutator_of_le_normalizers hAQ hAZ
  have hAO : A ≤ normalizer (O H : Set G) := hAH.trans (le_normalizer_O H)
  have hO2 : ¬ 2 ∣ Nat.card (O H) := fun h =>
    Nat.not_even_iff_odd.mpr (card_O_odd H) (even_iff_two_dvd.mpr h)
  obtain ⟨P, hP, hRP, hAP⟩ := ABGTheoremB.exists_isSylowOf_normalized_ge_of_coprime
    Nat.prime_two hp hA hAO hO2 hle (hQ.to_le hRQ) hAR
  refine ⟨P, hP, hAP, fun hZP => hZQ ?_⟩
  have hdouble : ⁅⁅Q, Z⁆, Z⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer, le_centralizer_iff]
    exact hZP.trans (centralizer_le hRP)
  have hcop : Nat.Coprime (Nat.card Z) (Nat.card Q) :=
    IsPGroup.coprime_card_of_ne 2 p (Ne.symm hp2) Z Q (hA.to_le hZA) hQ
  have h := GorensteinWalter.commutator_eq_bot_of_coprime_double_commutator_eq_bot Q Z hZQn hcop
    hdouble
  rw [commutator_eq_bot_iff_le_centralizer, le_centralizer_iff] at h
  exact h

end PConstraint

section OneKind

variable {G : Type} [Group G] [Finite G]

theorem oddCore_eq_bot_of_isL2OrA7_or_isKleinFour {L : Type} [Group L] [Finite L] {qmin : ℕ}
    (hq : 5 ≤ qmin) (hL : IsL2OrA7 L qmin ∨ IsKleinFour L) : CFSG.oddCore L = ⊥ := by
  refine oddCore_eq_bot_of_isL2PGL2OrA7OrV4 ?_
  rcases hL with (h | ⟨p, k, hp, hp2, hpk, he⟩) | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr ⟨p, k, hp, hp2, hq.trans hpk, he⟩)
  · exact Or.inr (Or.inr h)

theorem pConstrainedWrt_of_le_O_C {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup G}
    (hA2 : IsPGroup 2 A) {H K₀ OK Z W : Subgroup G} {x : G} {L : Type*} [Group L]
    (f : K₀ →* L) (hf : Function.Surjective f) (hker : f.ker = OK.subgroupOf K₀)
    (hL : CFSG.oddCore L = ⊥) (hOK : OK ≤ K₀) (hAH : A ≤ H) (hWH : W ≤ H) (hWK : W ≤ K₀)
    (hWcov : K₀ ≤ W ⊔ OK) (hWn : ((W ⊔ O H).subgroupOf H).Normal) (hWint : O H ⊓ W = W ⊓ OK)
    (hZ : Z ≤ A) (hAZ : A ≤ normalizer (Z : Set G)) (hZW : Z ≤ W) (hKx : K₀ ≤ C x)
    {P : Subgroup G} (hPH : P ≤ H) (hPp : IsPGroup p P) (hAP : A ≤ normalizer (P : Set G))
    (hPx : P ≤ O (C x)) (hZP : ¬ Z ≤ centralizer (P : Set G)) :
    Sec4Setting.PConstrainedWrt p A H Z := by
  have hEL : ⁅P, W⁆ ≤ W ⊔ O H :=
    commutator_le_of_normal (sup_le hWH (map_subtype_le _)) hWn hPH le_sup_left
  have hEodd : Odd (Nat.card (⁅P, W⁆ : Subgroup G)) :=
    (card_O_odd (C x)).of_dvd_nat (card_dvd_of_le (commutator_le_O hPx (hWK.trans hKx)))
  have hEO : ⁅P, W⁆ ≤ O H :=
    le_O_of_odd_of_le_sup f hf hker hL hOK hWH hWK hWcov (by rw [← hWint]; exact inf_le_left)
      hEL hEodd (normalizer_commutator_ge_right P W)
  exact pConstrainedWrt_of_commutator_le hp hp2 hA2 hAH hZ hAZ hPp hAP hZP
    ((commutator_mono le_rfl hZW).trans hEO)

end OneKind

end G5a

namespace Sec5Roles

open G5a

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} (ρ : Sec5Roles G A)

theorem lemma_5_1_first_of {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h1M : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.M₀ (O ρ.M) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.M₀ ∧ ρ.Y ≤ W ∧ Covers W ρ.M₀ (O ρ.M) ∧
        H ⊓ ρ.M₀ ≤ W ⊔ (H ⊓ O ρ.M) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.M ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.Y ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H A : Set (Bar H)))
    (h47 : QuotIs ρ.M₀ (O ρ.M) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 ρ.S₂ ρ.M₀ ∧
      ρ.M = ρ.M₀ ⊔ (ρ.M ⊓ normalizer (A : Set G)) ∧
      ρ.M = ρ.M₀ ⊔ (ρ.M ⊓ normalizer (ρ.S₂ : Set G)) ∧
      (∀ x ∈ ρ.X, x ≠ 1 → O2 (C x) = (O2 ρ.M ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ ρ.X, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (ρ.M₀ ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (H : Subgroup G) (hH : H ≠ ⊤) (hAH : A ≤ H) :
    Covers H ρ.M₀ (O ρ.M) → (∃ x ∈ ρ.X, x ≠ 1 ∧ ∃ P ≤ H, IsPGroup p P ∧
      A ≤ normalizer (P : Set G) ∧ P ≤ O (C x) ∧ ¬ ρ.Y ≤ centralizer (P : Set G)) →
      Sec4Setting.PConstrainedWrt p A H ρ.Y := by
  rintro hcov ⟨x, hx, -, P, hPH, hPp, hAP, hPx, hYP⟩
  obtain ⟨W, hWHM, hYW, hWcov, -, hWn, hWint, -⟩ := h1M H hH hAH hcov
  obtain ⟨L, _, f, hf, hker, hL⟩ := h47.1
  have : Finite L := Finite.of_surjective f hf
  exact pConstrainedWrt_of_le_O_C hp hp2 ρ.isPGroup_A f hf hker
    (oddCore_eq_bot_of_isL2OrA7_or_isKleinFour le_rfl hL) ρ.O_M_le_M₀ hAH
    (hWHM.trans inf_le_left) (hWHM.trans inf_le_right)
    (hWcov.trans (sup_le_sup_right inf_le_left _)) hWn hWint ρ.Y_le_A
    (ρ.A_le_N.trans ρ.N_le_normalizer_Y) hYW (ρ.M₀_le.trans (ρ.M_le_C hx)) hPH hPp hAP hPx hYP

theorem lemma_5_1_of {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h1M : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.M₀ (O ρ.M) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.M₀ ∧ ρ.Y ≤ W ∧ Covers W ρ.M₀ (O ρ.M) ∧
        H ⊓ ρ.M₀ ≤ W ⊔ (H ⊓ O ρ.M) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.M ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.Y ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H A : Set (Bar H)))
    (h1N : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.N₀ (O ρ.N) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.N₀ ∧ ρ.X ≤ W ∧ Covers W ρ.N₀ (O ρ.N) ∧
        H ⊓ ρ.N₀ ≤ W ⊔ (H ⊓ O ρ.N) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.N ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.X ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.N) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.N) ≤ centralizer (bar H A : Set (Bar H)))
    (h47 : QuotIs ρ.M₀ (O ρ.M) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 ρ.S₂ ρ.M₀ ∧
      ρ.M = ρ.M₀ ⊔ (ρ.M ⊓ normalizer (A : Set G)) ∧
      ρ.M = ρ.M₀ ⊔ (ρ.M ⊓ normalizer (ρ.S₂ : Set G)) ∧
      (∀ x ∈ ρ.X, x ≠ 1 → O2 (C x) = (O2 ρ.M ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ ρ.X, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (ρ.M₀ ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (h48 : QuotIs ρ.N₀ (O ρ.N) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 ρ.S₁ ρ.N₀ ∧
      ρ.N = ρ.N₀ ⊔ (ρ.N ⊓ normalizer (A : Set G)) ∧
      ρ.N = ρ.N₀ ⊔ (ρ.N ⊓ normalizer (ρ.S₁ : Set G)) ∧
      (∀ y ∈ ρ.Y, y ≠ 1 → O2 (C y) = (O2 ρ.N ⊓ O2 (C y)) ⊔ O (C y)) ∧
      (∀ y ∈ ρ.Y, y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
        (ρ.N₀ ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y)))
    (H : Subgroup G) (hH : H ≠ ⊤) (hAH : A ≤ H) :
    (Covers H ρ.M₀ (O ρ.M) → (∃ x ∈ ρ.X, x ≠ 1 ∧ ∃ P ≤ H, IsPGroup p P ∧
      A ≤ normalizer (P : Set G) ∧ P ≤ O (C x) ∧ ¬ ρ.Y ≤ centralizer (P : Set G)) →
      Sec4Setting.PConstrainedWrt p A H ρ.Y) ∧
    (Covers H ρ.N₀ (O ρ.N) → (∃ y ∈ ρ.Y, y ≠ 1 ∧ ∃ P ≤ H, IsPGroup p P ∧
      A ≤ normalizer (P : Set G) ∧ P ≤ O (C y) ∧ ¬ ρ.X ≤ centralizer (P : Set G)) →
      Sec4Setting.PConstrainedWrt p A H ρ.X) :=
  ⟨ρ.lemma_5_1_first_of hp hp2 h1M h47 H hH hAH, ρ.swap.lemma_5_1_first_of hp hp2 h1N h48 H hH hAH⟩

end Sec5Roles

namespace Sec4Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}

theorem lemma_4_7_weaken
    (h47 : QuotIs (𝔖.M₀ A) (O (𝔖.M A)) (fun L _ => IsL2OrA7 L 7) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (A : Set G)) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (𝔖.S₂ : Set G)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → O2 (C x) = (O2 (𝔖.M A) ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (𝔖.M₀ A ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x))) :
    QuotIs (𝔖.M₀ A) (O (𝔖.M A)) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (A : Set G)) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (𝔖.S₂ : Set G)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → O2 (C x) = (O2 (𝔖.M A) ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (𝔖.M₀ A ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)) := by
  obtain ⟨⟨L, _, f, hf, hker, hL⟩, h₂⟩ := h47
  exact ⟨⟨L, _, f, hf, hker, Or.inl (hL.mono (by norm_num))⟩, h₂⟩

theorem sec5_one_M_weaken
    (h1M : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H (𝔖.M₀ A) (O (𝔖.M A)) →
      ∃ W : Subgroup G, W ≤ H ⊓ 𝔖.M₀ A ∧ 𝔖.Y A ≤ W ∧ Covers W (𝔖.M₀ A) (O (𝔖.M A)) ∧
        H ⊓ 𝔖.M₀ A ≤ W ⊔ (H ⊓ O (𝔖.M A)) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O (𝔖.M A) ∧ IsL2OrA7 (bar H W) 7 ∧
        bar H (H ⊓ O (𝔖.M A)) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O (𝔖.M A)) ≤ centralizer (bar H A : Set (Bar H)))
    (H : Subgroup G) (hH : H ≠ ⊤) (hAH : A ≤ H) (hcov : Covers H (𝔖.M₀ A) (O (𝔖.M A))) :
    ∃ W : Subgroup G, W ≤ H ⊓ 𝔖.M₀ A ∧ 𝔖.Y A ≤ W ∧ Covers W (𝔖.M₀ A) (O (𝔖.M A)) ∧
      H ⊓ 𝔖.M₀ A ≤ W ⊔ (H ⊓ O (𝔖.M A)) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
      O H ⊓ W = W ⊓ O (𝔖.M A) ∧
      (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H (𝔖.Y A) ∧ IsKleinFour (bar H W))) ∧
      bar H (H ⊓ O (𝔖.M A)) ≤ centralizer (bar H W : Set (Bar H)) ∧
      bar H (H ⊓ O (𝔖.M A)) ≤ centralizer (bar H A : Set (Bar H)) := by
  obtain ⟨W, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ := h1M H hH hAH hcov
  exact ⟨W, h₁, h₂, h₃, h₄, h₅, h₆, Or.inl (h₇.mono (by norm_num)), h₈, h₉⟩

theorem lemma_5_1_of (_hAS : A ≤ 𝔖.S) (hA : IsE16 A) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h1M : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H (𝔖.M₀ A) (O (𝔖.M A)) →
      ∃ W : Subgroup G, W ≤ H ⊓ 𝔖.M₀ A ∧ 𝔖.Y A ≤ W ∧ Covers W (𝔖.M₀ A) (O (𝔖.M A)) ∧
        H ⊓ 𝔖.M₀ A ≤ W ⊔ (H ⊓ O (𝔖.M A)) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O (𝔖.M A) ∧ IsL2OrA7 (bar H W) 7 ∧
        bar H (H ⊓ O (𝔖.M A)) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O (𝔖.M A)) ≤ centralizer (bar H A : Set (Bar H)))
    (h1N : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H (𝔖.N₀ A) (O (𝔖.N A)) →
      ∃ W : Subgroup G, W ≤ H ⊓ 𝔖.N₀ A ∧ 𝔖.X A ≤ W ∧ Covers W (𝔖.N₀ A) (O (𝔖.N A)) ∧
        H ⊓ 𝔖.N₀ A ≤ W ⊔ (H ⊓ O (𝔖.N A)) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O (𝔖.N A) ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H (𝔖.X A) ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O (𝔖.N A)) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O (𝔖.N A)) ≤ centralizer (bar H A : Set (Bar H)))
    (h47 : QuotIs (𝔖.M₀ A) (O (𝔖.M A)) (fun L _ => IsL2OrA7 L 7) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (A : Set G)) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (𝔖.S₂ : Set G)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → O2 (C x) = (O2 (𝔖.M A) ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (𝔖.M₀ A ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (h48 : QuotIs (𝔖.N₀ A) (O (𝔖.N A)) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (A : Set G)) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (𝔖.S₁ : Set G)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → O2 (C y) = (O2 (𝔖.N A) ⊓ O2 (C y)) ⊔ O (C y)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
        (𝔖.N₀ A ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y)))
    (H : Subgroup G) (hH : H ≠ ⊤) (hAH : A ≤ H) :
    (Covers H (𝔖.M₀ A) (O (𝔖.M A)) → (∃ x ∈ 𝔖.X A, x ≠ 1 ∧ ∃ P ≤ H, IsPGroup p P ∧
      A ≤ normalizer (P : Set G) ∧ P ≤ O (C x) ∧ ¬ 𝔖.Y A ≤ centralizer (P : Set G)) →
      PConstrainedWrt p A H (𝔖.Y A)) ∧
    (Covers H (𝔖.N₀ A) (O (𝔖.N A)) → (∃ y ∈ 𝔖.Y A, y ≠ 1 ∧ ∃ P ≤ H, IsPGroup p P ∧
      A ≤ normalizer (P : Set G) ∧ P ≤ O (C y) ∧ ¬ 𝔖.X A ≤ centralizer (P : Set G)) →
      PConstrainedWrt p A H (𝔖.X A)) :=
  (𝔖.sec5Roles _hAS hA).lemma_5_1_of hp hp2 (sec5_one_M_weaken 𝔖 h1M) h1N
    (lemma_4_7_weaken 𝔖 h47) h48 H hH hAH

end Sec4Setting

end CFSG.GH72
