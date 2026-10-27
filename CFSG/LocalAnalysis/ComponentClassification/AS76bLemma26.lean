module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21Basic
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
public import CFSG.LocalAnalysis.ComponentClassification.AS76bExistBasic

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

theorem mem_of_pow_mem_of_coprime {C : Type*} [Group C] [Finite C] {H : Subgroup C} {x : C}
    {n : ℕ} (hx : x ^ n ∈ H) (hcop : Nat.Coprime n (orderOf x)) : x ∈ H := by
  by_cases h1 : 1 < orderOf x
  · obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    have : x = (x ^ n) ^ m := by
      rw [← pow_mul, ← pow_mod_orderOf, hm, pow_one]
    rw [this]
    exact H.pow_mem hx m
  · have h1' : orderOf x = 1 := by have := orderOf_pos x; omega
    rw [orderOf_eq_one_iff.mp h1']
    exact H.one_mem

theorem mem_of_two_pow_mem_of_odd {C : Type*} [Group C] [Finite C] {H : Subgroup C} {x : C}
    {k : ℕ} (hx : x ^ 2 ^ k ∈ H) (hodd : Odd (orderOf x)) : x ∈ H :=
  mem_of_pow_mem_of_coprime hx (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd))

theorem le_of_generalizedFitting_mod_center {C : Type*} [Group C] [Finite C] {Z W : Subgroup C}
    (hZ : Z ≤ center C) (hF : ∀ f ∈ CFSG.generalizedFitting C, ∃ k : ℕ, f ^ 2 ^ k ∈ Z)
    (hW : W.Normal) (hWodd : Odd (Nat.card W)) : W ≤ Z := by
  have hFn : (CFSG.generalizedFitting C).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := C)).2
  have hoddW : ∀ w ∈ W, Odd (orderOf w) := fun w hw =>
    hWodd.of_dvd_nat (by simpa using Subgroup.orderOf_dvd_natCard W hw)
  have hWZ : ∀ w ∈ W, w ∈ CFSG.generalizedFitting C → w ∈ Z := fun w hw hwF => by
    obtain ⟨k, hk⟩ := hF w hwF
    exact mem_of_two_pow_mem_of_odd hk (hoddW w hw)
  have hWC : W ≤ centralizer (CFSG.generalizedFitting C : Set C) := by
    intro w hw
    rw [mem_centralizer_iff]
    intro f hf
    set z := w * f * w⁻¹ * f⁻¹ with hz
    have hzW : z ∈ W := by
      have : f * w⁻¹ * f⁻¹ ∈ W := hW.conj_mem _ (W.inv_mem hw) f
      rw [hz, show w * f * w⁻¹ * f⁻¹ = w * (f * w⁻¹ * f⁻¹) by group]
      exact W.mul_mem hw this
    have hzF : z ∈ CFSG.generalizedFitting C :=
      mul_mem (hFn.conj_mem f hf w) (inv_mem hf)
    have hzc : z ∈ center C := hZ (hWZ z hzW hzF)
    have hwf : w * f * w⁻¹ = z * f := by rw [hz]; group
    have hpow : ∀ n : ℕ, w * f ^ n * w⁻¹ = z ^ n * f ^ n := fun n => by
      rw [← conj_pow, hwf, (Commute.mul_pow ((mem_center_iff.mp hzc f).symm) n)]
    obtain ⟨k, hk⟩ := hF f hf
    have hkc : f ^ 2 ^ k ∈ center C := hZ hk
    have hzk : z ^ 2 ^ k = 1 := by
      have h1 := hpow (2 ^ k)
      have h2 : w * f ^ 2 ^ k * w⁻¹ = f ^ 2 ^ k := by
        rw [mem_center_iff.mp hkc w, mul_inv_cancel_right]
      rw [h2] at h1
      exact (mul_eq_right.mp h1.symm)
    have hz1 : z = 1 := by
      have hdvd : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hzk
      have h1 : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes
        (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr (hoddW z hzW))) dvd_rfl hdvd
      exact orderOf_eq_one_iff.mp h1
    rw [hz] at hz1
    have : w * f * w⁻¹ = f := by
      calc w * f * w⁻¹ = w * f * w⁻¹ * f⁻¹ * f := by group
        _ = f := by rw [hz1, one_mul]
    calc f * w = w * f * w⁻¹ * w := by rw [this]
      _ = w * f := by group
  intro w hw
  exact hWZ w hw (CFSG.centralizer_generalizedFitting_le C (hWC hw))

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_odd_of_relIndex {N X : Subgroup G} (hNn : (N.subgroupOf X).Normal) {k : ℕ}
    (hk : N.relIndex X = 2 ^ k) {x : G} (hx : x ∈ X) (hodd : Odd (orderOf x)) : x ∈ N := by
  have h1 : orderOf (QuotientGroup.mk' (N.subgroupOf X) ⟨x, hx⟩) ∣ orderOf x := by
    have h := orderOf_map_dvd (QuotientGroup.mk' (N.subgroupOf X)) (⟨x, hx⟩ : X)
    rwa [Subgroup.orderOf_mk] at h
  have h2 : orderOf (QuotientGroup.mk' (N.subgroupOf X) ⟨x, hx⟩) ∣ 2 ^ k := by
    rw [← hk]
    exact orderOf_dvd_natCard _
  have h3 := Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)) h1 h2
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

omit [Finite G] in
theorem mem_normalizer_of_mem_normalizer_subgroupOf {X M : Subgroup G} (hXM : X ≤ M) {c : M}
    (hc : c ∈ normalizer ((X.subgroupOf M : Subgroup M) : Set M)) :
    (c : G) ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h := (mem_normalizer_iff.mp hc ⟨x, hXM hx⟩).mp hx
    exact h
  · intro hx
    have hxM : x ∈ M := by
      have h := M.mul_mem (M.mul_mem (M.inv_mem c.2) (hXM hx)) c.2
      simpa [mul_assoc] using h
    have h := (mem_normalizer_iff.mp hc ⟨x, hxM⟩).mpr hx
    exact h

omit [Finite G] in
theorem mem_normalizer_of_tightlyEmbedded_subgroupOf {X M : Subgroup G} (hXM : X ≤ M)
    (htight : TightlyEmbedded (X.subgroupOf M)) {c : G} (hc : c ∈ M) {s : G} (hs : s ∈ X)
    (hcs : c * s * c⁻¹ ∈ X) (hs2 : orderOf s = 2) : c ∈ normalizer (X : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcN
  have hcN' : (⟨c, hc⟩ : M) ∉ normalizer ((X.subgroupOf M : Subgroup M) : Set M) :=
    fun h => hcN (mem_normalizer_of_mem_normalizer_subgroupOf hXM h)
  have hodd := htight.2 ⟨c, hc⟩ hcN'
  have hsmem : (⟨s, hXM hs⟩ : M) ∈ X.subgroupOf M ⊓ rightConjugate (X.subgroupOf M) ⟨c, hc⟩ :=
    ⟨hs, (mem_rightConjugate_iff _ _ _).mpr hcs⟩
  have h2 : 2 ∣ Nat.card (X.subgroupOf M ⊓ rightConjugate (X.subgroupOf M) ⟨c, hc⟩ :
      Subgroup M) := by
    have h := Subgroup.orderOf_dvd_natCard _ hsmem
    rwa [Subgroup.orderOf_mk, hs2] at h
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem mem_normalizer_of_odd_of_relIndex {N X : Subgroup G} (hNX : N ≤ X)
    (hNn : (N.subgroupOf X).Normal) (hodd : Odd (Nat.card N)) {k : ℕ}
    (hk : N.relIndex X = 2 ^ k) {c : G} (hc : c ∈ normalizer (X : Set G)) :
    c ∈ normalizer (N : Set G) := by
  refine mem_normalizer_of_map_conj_le ?_
  rintro _ ⟨n, hn, rfl⟩
  refine mem_of_odd_of_relIndex hNn hk ((mem_normalizer_iff.mp hc n).mp (hNX hn)) ?_
  change Odd (orderOf (c * n * c⁻¹))
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  exact hodd.of_dvd_nat (by simpa using Subgroup.orderOf_dvd_natCard N hn)

theorem lemma26 {A T : Subgroup G} (hT : IsElemAbelian 2 T) (h4 : 4 ≤ Nat.card T)
    (hTN : T ≤ normalizer (A : Set G)) (hX : SylowInTightTwoNilpotent T A)
    (hZ : (center A).map A.subtype ≤ centralizer (T : Set G))
    (hF : ∀ t ∈ T, t ≠ 1 → ∀ x ∈ CFSG.inSubgroup CFSG.generalizedFitting
      (A ⊓ centralizer ({t} : Set G)), ∃ k : ℕ, x ^ 2 ^ k ∈ (center A).map A.subtype) :
    ∀ x ∈ T ⊔ A, T ⊓ rightConjugate T x ≠ ⊥ → rightConjugate T x = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X, hXTA, hTX, ⟨N, hNX, hNn, hNodd, k, hk⟩, htight⟩ := hX
  have hoddN : ∀ n ∈ N, Odd (orderOf n) := fun n hn =>
    hNodd.of_dvd_nat (by simpa using Subgroup.orderOf_dvd_natCard N hn)
  have hAn : (A.subgroupOf (A ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le le_normalizer hTN)
  have hAidx : ∃ j : ℕ, A.relIndex (A ⊔ T) = 2 ^ j := by
    rw [AschbacherTheorem3.relIndex_sup_of_le_normalizer hTN]
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hTX.isPGroup
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show A.relIndex T ∣ 2 ^ m by rw [← hm]; exact relIndex_dvd_card _ _)
    exact ⟨j, hj⟩
  obtain ⟨j, hj⟩ := hAidx
  have hNA : N ≤ A := fun n hn =>
    mem_of_odd_of_relIndex hAn hj (sup_comm T A ▸ hXTA (hNX hn)) (hoddN n hn)
  have hT2 : ∀ t ∈ T, t ≠ 1 → orderOf t = 2 := fun t ht ht1 => orderOf_eq_prime (hT.2 t ht) ht1
  have hCN : ∀ t ∈ T, t ≠ 1 → ∀ c ∈ T ⊔ A, c * t * c⁻¹ = t → c ∈ normalizer (X : Set G) :=
    fun t ht ht1 c hc hct => mem_normalizer_of_tightlyEmbedded_subgroupOf hXTA htight hc
      (hTX.le ht) (by rw [hct]; exact hTX.le ht) (hT2 t ht ht1)
  have hW : ∀ t ∈ T, t ≠ 1 → N ⊓ centralizer ({t} : Set G) ≤ (center A).map A.subtype := by
    intro t ht ht1
    set C := A ⊓ centralizer ({t} : Set G) with hCdef
    have hWC : N ⊓ centralizer ({t} : Set G) ≤ C := inf_le_inf_right _ hNA
    have hWn : ((N ⊓ centralizer ({t} : Set G)).subgroupOf C).Normal := by
      refine (normal_subgroupOf_iff_le_normalizer hWC).mpr fun c hc => ?_
      have hct : c * t * c⁻¹ = t := by
        have := mem_centralizer_singleton_iff.mp hc.2
        rw [this, mul_inv_cancel_right]
      have hcX := hCN t ht ht1 c (mem_sup_right hc.1) hct
      have hcN := mem_normalizer_of_odd_of_relIndex hNX hNn hNodd hk hcX
      rw [mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨hy1, hy2⟩
        refine ⟨(mem_normalizer_iff.mp hcN y).mp hy1, ?_⟩
        exact (mem_normalizer_iff.mp (le_normalizer hc.2) y).mp hy2
      · rintro ⟨hy1, hy2⟩
        exact ⟨(mem_normalizer_iff.mp hcN y).mpr hy1,
          (mem_normalizer_iff.mp (le_normalizer hc.2) y).mpr hy2⟩
    have hWodd : Odd (Nat.card ((N ⊓ centralizer ({t} : Set G)).subgroupOf C)) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv]
      exact hNodd.of_dvd_nat (card_dvd_of_le inf_le_left)
    have hZC : ((center A).map A.subtype).subgroupOf C ≤ center C := by
      rintro ⟨z, hzC⟩ hz
      rw [mem_subgroupOf] at hz
      obtain ⟨z', hz', rfl⟩ := hz
      rw [mem_center_iff]
      intro y
      apply Subtype.ext
      have h := mem_center_iff.mp hz' ⟨y, (y.2 : (y : G) ∈ C).1⟩
      simpa using congrArg Subtype.val h
    have hFC : ∀ f ∈ CFSG.generalizedFitting C,
        ∃ k : ℕ, f ^ 2 ^ k ∈ ((center A).map A.subtype).subgroupOf C := by
      intro f hf
      obtain ⟨k, hk⟩ := hF t ht ht1 (f : G) ⟨f, hf, rfl⟩
      exact ⟨k, by simpa [mem_subgroupOf] using hk⟩
    have hle := le_of_generalizedFitting_mod_center hZC hFC hWn hWodd
    intro y hy
    have := hle (show (⟨y, hWC hy⟩ : C) ∈ (N ⊓ centralizer ({t} : Set G)).subgroupOf C from hy)
    exact this
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hTX.isPGroup
  have hm2 : 2 ≤ m := by
    by_contra h
    have : Nat.card T ≤ 2 := by
      rw [hm]
      calc 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by norm_num
    omega
  have hrank : 1 < Open.pRank 2 T :=
    lt_of_lt_of_le (by omega) (CFSG.SectionRank.le_pRank one_lt_two le_rfl hT hm)
  obtain ⟨E, hET, hE, hE4⟩ := exists_elemAbelian_four hrank
  have hTNN : T ≤ normalizer (N : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hNX).mp hNn |>.trans' hTX.le
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    2 Nat.prime_two E N (fun e => Subtype.ext (by simpa using hE.2 _ e.2)) (by rw [hE4]; norm_num)
    (fun h => (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h)) (hET.trans hTNN)
  have hNC : N ≤ centralizer (T : Set G) := by
    rw [hgen]
    refine iSup₂_le fun e he => ?_
    exact (hW e (hET e.2) fun h => he (Subtype.ext h)).trans hZ
  have hNTX : N ⊔ T = X := by
    have hcard : Nat.card (N ⊔ T : Subgroup G) = Nat.card N * Nat.card T :=
      AschbacherTheorem3.card_sup_of_le_normalizer hTNN
        (eq_bot_of_isPGroup_of_odd (hTX.isPGroup.to_le inf_le_right)
          (hNodd.of_dvd_nat (card_dvd_of_le inf_le_left)))
    have hXcard : Nat.card X = 2 ^ k * Nat.card N := by
      have h := Subgroup.relIndex_mul_card N X
      rw [inf_eq_left.mpr hNX, hk] at h
      exact h.symm
    have hkT : 2 ^ k ≤ Nat.card T := Nat.le_of_dvd Nat.card_pos
      (pow_dvd_card_of_isSylowOf hTX (by rw [hXcard]; exact dvd_mul_right _ _))
    refine eq_of_le_of_card_ge (sup_le hNX hTX.le) ?_
    rw [hcard, hXcard, mul_comm (Nat.card N)]
    exact Nat.mul_le_mul_right _ hkT
  have hXT : X ≤ normalizer (T : Set G) := by
    rw [← hNTX]
    refine sup_le (fun n hn => ?_) le_normalizer
    have hy : ∀ y ∈ T, n * y * n⁻¹ = y := fun y hy => by
      rw [(mem_centralizer_iff.mp (hNC hn) y hy).symm, mul_inv_cancel_right]
    refine mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨y, hyT, rfl⟩
    change n * y * n⁻¹ ∈ T
    rw [hy y hyT]
    exact hyT
  intro x hx hTx
  obtain ⟨⟨s, hs⟩, hs1⟩ := ne_bot_iff_exists_ne_one.mp hTx
  have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hxs : x * s * x⁻¹ ∈ T := (mem_rightConjugate_iff _ _ _).mp hs.2
  have hxX : x ∈ normalizer (X : Set G) :=
    mem_normalizer_of_tightlyEmbedded_subgroupOf hXTA htight hx (hTX.le hs.1)
      (hTX.le hxs) (hT2 s hs.1 hs1')
  have hTxX : rightConjugate T x ≤ X := by
    intro y hy
    rw [mem_rightConjugate_iff] at hy
    have h := (mem_normalizer_iff.mp (inv_mem hxX) _).mp (hTX.le hy)
    simpa [mul_assoc] using h
  have hTxT : rightConjugate T x ≤ T := by
    obtain ⟨S, hS⟩ := hTX.exists_sylow_eq_subgroupOf
    have hSn : (S : Subgroup X).Normal := by
      rw [hS]
      exact (normal_subgroupOf_iff_le_normalizer hTX.le).mpr hXT
    have hp : IsPGroup 2 ((rightConjugate T x).subgroupOf X) :=
      (AschbacherTheorem3.isPGroup_rightConjugate hTX.isPGroup x).comap_subtype
    have hle : (rightConjugate T x).subgroupOf X ≤ (S : Subgroup X) := by
      have hsup := S.is_maximal' (hp.to_sup_of_normal_right S.isPGroup') le_sup_right
      exact hsup ▸ le_sup_left
    intro y hy
    have h := hle (show (⟨y, hTxX hy⟩ : X) ∈ (rightConjugate T x).subgroupOf X from hy)
    rw [hS] at h
    exact h
  exact eq_of_le_of_card_ge hTxT (by rw [rightConjugate_card])

theorem lemma27 {A T : Subgroup G} (hT : IsElemAbelian 2 T) (h4 : 4 ≤ Nat.card T)
    (hTN : T ≤ normalizer (A : Set G)) (hX : SylowInTightTwoNilpotent T A)
    (hZ : (center A).map A.subtype ≤ centralizer (T : Set G))
    (hF : ∀ t ∈ T, t ≠ 1 → ∀ x ∈ CFSG.inSubgroup CFSG.generalizedFitting
      (A ⊓ centralizer ({t} : Set G)), ∃ k : ℕ, x ^ 2 ^ k ∈ (center A).map A.subtype)
    (hAT : A ⊓ T = ⊥) :
    ∀ t ∈ T, t ≠ 1 → ⁅A ⊓ centralizer ({t} : Set G), T⁆ = ⊥ := by
  intro t ht ht1
  have hTI := lemma26 hT h4 hTN hX hZ hF
  rw [commutator_eq_bot_iff_le_centralizer]
  intro c hc
  have hct : c * t * c⁻¹ = t := by
    rw [mem_centralizer_singleton_iff.mp hc.2, mul_inv_cancel_right]
  have hcT : rightConjugate T c = T := by
    refine hTI c (mem_sup_right hc.1) ?_
    refine ne_bot_iff_exists_ne_one.mpr ⟨⟨t, ht, (mem_rightConjugate_iff _ _ _).mpr ?_⟩, ?_⟩
    · rw [hct]
      exact ht
    · exact fun h => ht1 (congrArg Subtype.val h)
  have hcN : c ∈ normalizer (T : Set G) := (rightConjugate_eq_self_iff T c).mp hcT
  rw [mem_centralizer_iff]
  intro τ hτ
  have h1 : c * τ * c⁻¹ * τ⁻¹ ∈ T := T.mul_mem ((mem_normalizer_iff.mp hcN τ).mp hτ) (T.inv_mem hτ)
  have h2 : c * τ * c⁻¹ * τ⁻¹ ∈ A := by
    have h := (mem_normalizer_iff.mp (hTN hτ) c⁻¹).mp (A.inv_mem hc.1)
    rw [show c * τ * c⁻¹ * τ⁻¹ = c * (τ * c⁻¹ * τ⁻¹) by group]
    exact A.mul_mem hc.1 h
  have h3 : c * τ * c⁻¹ * τ⁻¹ ∈ A ⊓ T := ⟨h2, h1⟩
  rw [hAT, mem_bot] at h3
  have h4' : c * τ * c⁻¹ = τ := mul_inv_eq_one.mp h3
  calc τ * c = c * τ * c⁻¹ * c := by rw [h4']
    _ = c * τ := by group

theorem lemma26_of_isAdmissible {A T : Subgroup G} (hA : IsAdmissible T A)
    (hZ : (center A).map A.subtype ≤ centralizer (T : Set G))
    (hF : ∀ t ∈ T, t ≠ 1 → ∀ x ∈ CFSG.inSubgroup CFSG.generalizedFitting
      (A ⊓ centralizer ({t} : Set G)), ∃ k : ℕ, x ^ 2 ^ k ∈ (center A).map A.subtype) :
    ∀ x ∈ T ⊔ A, T ⊓ rightConjugate T x ≠ ⊥ → rightConjugate T x = T :=
  lemma26 hA.1.1 hA.1.2.1 hA.1.2.2.1 hA.2.1 hZ hF

theorem lemma27_of_isAdmissible {A T : Subgroup G} (hA : IsAdmissible T A)
    (hZ : (center A).map A.subtype ≤ centralizer (T : Set G))
    (hF : ∀ t ∈ T, t ≠ 1 → ∀ x ∈ CFSG.inSubgroup CFSG.generalizedFitting
      (A ⊓ centralizer ({t} : Set G)), ∃ k : ℕ, x ^ 2 ^ k ∈ (center A).map A.subtype)
    (hAT : A ⊓ T = ⊥) :
    ∀ t ∈ T, t ≠ 1 → ⁅A ⊓ centralizer ({t} : Set G), T⁆ = ⊥ :=
  lemma27 hA.1.1 hA.1.2.1 hA.1.2.2.1 hA.2.1 hZ hF hAT

end CFSG.ComponentClassification.AS76b
