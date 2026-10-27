module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Lemma22Thm3
public import CFSG.LocalAnalysis.ComponentClassification.AS76bInputs
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.ComponentClassification.Asc76.Lemma22

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
open CFSG.ComponentClassification.AS76b (oddCoreIn oUpperTwoPrime)
open CFSG.SignalizerFunctor.Helpers (relativeWeakClosure relative_weak_closure_le)
open scoped commutatorElement

section General

variable {X : Type*} [Group X]

theorem isElemAbelian_of_le_sup {T A B L : Subgroup X} (hTL : T ⊓ L = ⊥) (hBL : B ≤ L)
    (hA : CFSG.Open.IsElemAbelian 2 A) (hAB : ⁅A, B⁆ = ⊥) (hT : T ≤ A ⊔ B) :
    CFSG.Open.IsElemAbelian 2 T := by
  have hBA : B ≤ normalizer (A : Set X) :=
    (le_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer).mp hAB)).trans
      (centralizer_le_normalizer _)
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer).mp hAB ha) b hb).symm
  have hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hone : ∀ x ∈ T, x ∈ B → x = 1 := fun x hxT hxB => by
    have hmem : x ∈ T ⊓ L := ⟨hxT, hBL hxB⟩
    rw [hTL] at hmem
    exact hmem
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := NormalizedProduct.coordinates A B hBA x (hT x.2)
    obtain ⟨a', ha', b', hb', hab'⟩ := NormalizedProduct.coordinates A B hBA y (hT y.2)
    have hC : ∀ d ∈ A, ∀ c ∈ B, Commute d c := fun d hd c hc => hcomm d hd c hc
    have hxy : (x : X) * y = a * a' * (b * b') := by
      rw [← hab, ← hab']
      exact (hC a' ha' b hb).symm.mul_mul_mul_comm a b'
    have hyx : (y : X) * x = a * a' * (b' * b) := by
      rw [← hab, ← hab', hAc a ha a' ha']
      exact (hC a ha b' hb').symm.mul_mul_mul_comm a' b
    have hc : b * b' * (b' * b)⁻¹ ∈ B :=
      B.mul_mem (B.mul_mem hb hb') (B.inv_mem (B.mul_mem hb' hb))
    have hcom : Commute (a * a') (b * b' * (b' * b)⁻¹) :=
      (hC a ha _ hc).mul_left (hC a' ha' _ hc)
    have heq : (x : X) * y * (x : X)⁻¹ * (y : X)⁻¹ = b * b' * (b' * b)⁻¹ := by
      calc (x : X) * y * (x : X)⁻¹ * (y : X)⁻¹ = ((x : X) * y) * ((y : X) * x)⁻¹ := by group
        _ = a * a' * (b * b') * (a * a' * (b' * b))⁻¹ := by rw [hxy, hyx]
        _ = a * a' * (b * b' * (b' * b)⁻¹) * (a * a')⁻¹ := by group
        _ = b * b' * (b' * b)⁻¹ := by rw [hcom.eq, mul_inv_cancel_right]
    have h1 := hone _ (T.mul_mem (T.mul_mem (T.mul_mem x.2 y.2) (T.inv_mem x.2))
      (T.inv_mem y.2)) (heq ▸ hc)
    have h2 : (x : X) * y * (x : X)⁻¹ = y := by
      rw [mul_inv_eq_one] at h1
      exact h1
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2
  · obtain ⟨a, ha, b, hb, rfl⟩ := NormalizedProduct.coordinates A B hBA x (hT hx)
    have hsq : (a * b) ^ 2 = b ^ 2 := by
      rw [pow_two, pow_two, mul_assoc, ← mul_assoc b, ← hcomm a ha b hb, mul_assoc, ← mul_assoc,
        ← pow_two, hA.2 a ha, one_mul]
    rw [hsq]
    refine hone _ ?_ (B.pow_mem hb 2)
    rw [← hsq]
    exact T.pow_mem hx 2

theorem card_le_two_of_isCyclic {E H : Subgroup X} [Finite H] (hEH : E ≤ H) (hH : IsCyclic H)
    (hE : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ 2 := by
  have : IsCyclic (E.subgroupOf H) := inferInstance
  have : IsCyclic E := isCyclic_of_surjective (subgroupOfEquivOfLe hEH).toMonoidHom
    (subgroupOfEquivOfLe hEH).surjective
  have : Finite E := Finite.of_injective _ (inclusion_injective hEH)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have h1 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hE g g.2))
  rw [hg] at h1
  exact Nat.le_of_dvd two_pos h1

end General

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_isSylowOf {K J T R : Subgroup G} (hK : TightlyEmbedded K)
    (hJ : TightlyEmbedded J) (hKJ : Odd (Nat.card (K ⊓ J : Subgroup G)))
    (hfac : (Nat.card K).factorization 2 = (Nat.card J).factorization 2)
    (hT : IsSylowOf 2 T (J ⊓ normalizer (K : Set G))) (hT1 : T ≠ ⊥) (hR : IsSylowOf 2 R K)
    (hTR : T ≤ normalizer (R : Set G)) (hTJ : IsSylowOf 2 T J) :
    Nat.card T = Nat.card R ∧ R ≤ normalizer (T : Set G) := by
  have hcard := card_inf_normalizer hK hJ hKJ hfac hT hT1 hR hTR
  have hTR' : Nat.card T = Nat.card R := by rw [hTJ.card_eq, ← hfac, ← hR.card_eq]
  refine ⟨hTR', inf_eq_left.mp (Subgroup.eq_of_le_of_card_ge inf_le_left ?_)⟩
  rw [hcard, hTR']

theorem exists_isElemAbelian_le {J T : Subgroup G} (hTJ : IsSylowOf 2 T J)
    (hm : 1 < CFSG.Open.pRank 2 J) :
    ∃ E : Subgroup G, E ≤ T ∧ CFSG.Open.IsElemAbelian 2 E ∧ 4 ≤ Nat.card E := by
  obtain ⟨E, hEJ, hE, hcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two J
  have hE2 : IsPGroup 2 E := IsPGroup.of_card hcard
  obtain ⟨c, -, hle⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hTJ hE2 hEJ
  refine ⟨_, hle, CFSG.SectionRank.isElemAbelian_map hE (MulAut.conj c⁻¹).toMonoidHom, ?_⟩
  rw [rightConjugate_card, hcard]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ CFSG.Open.pRank 2 J := Nat.pow_le_pow_right (by norm_num) hm

omit [Finite G] in
theorem commutator_le_oddCoreIn_of_forall {K T : Subgroup G}
    (h : ∀ t ∈ T, ∀ k ∈ K, (∃ n : ℕ, k ^ (2 ^ n) = 1) → ⁅t, k⁆ ∈ oddCoreIn K) :
    ⁅T, oUpperTwoPrime K⁆ ≤ oddCoreIn K := by
  rw [commutator_le]
  intro t ht x hx
  have hN : normalizer (K : Set G) ≤ normalizer (oddCoreIn K : Set G) :=
    normalizer_le_normalizer_core K
  have hle : oUpperTwoPrime K ≤ K := (closure_le _).mpr fun y hy => hy.1
  induction hx using Subgroup.closure_induction with
  | mem k hk => exact h t ht k hk.1 hk.2
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxN : x ∈ normalizer (oddCoreIn K : Set G) := hN (le_normalizer (hle hx))
    have hconj : x * ⁅t, y⁆ * x⁻¹ ∈ oddCoreIn K := (mem_normalizer_iff.mp hxN _).mp ihy
    have heq : ⁅t, x * y⁆ = ⁅t, x⁆ * (x * ⁅t, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact mul_mem ihx hconj
  | inv x hx ihx =>
    have hxN : x⁻¹ ∈ normalizer (oddCoreIn K : Set G) := hN (le_normalizer (hle (inv_mem hx)))
    have hconj : x⁻¹ * ⁅t, x⁆⁻¹ * x⁻¹⁻¹ ∈ oddCoreIn K :=
      (mem_normalizer_iff.mp hxN _).mp (inv_mem ihx)
    have heq : ⁅t, x⁻¹⁆ = x⁻¹ * ⁅t, x⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact hconj

omit [Finite G] in
theorem commutator_mem_oddCoreIn_of_commute {K : Subgroup G} {t k : normalizer (K : Set G)}
    (h : toBar K t * toBar K k = toBar K k * toBar K t) :
    ⁅(t : G), (k : G)⁆ ∈ oddCoreIn K := by
  have h1 : toBar K ⁅t, k⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h
  have h2 := (toBar_eq_one_iff K _).mp h1
  have h3 : ((⁅t, k⁆ : normalizer (K : Set G)) : G) = ⁅(t : G), (k : G)⁆ := by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← h3]
  exact h2

theorem commutator_le_or_isElemAbelian (h3 : AschbacherTheorem3.Theorem3Statement)
    {K J T R : Subgroup G} (hK : TightlyEmbedded K) (hJ : TightlyEmbedded J)
    (hKJ : Odd (Nat.card (K ⊓ J : Subgroup G)))
    (hfac : (Nat.card K).factorization 2 = (Nat.card J).factorization 2)
    (hT : IsSylowOf 2 T (J ⊓ normalizer (K : Set G))) (hT1 : T ≠ ⊥) (hR : IsSylowOf 2 R K)
    (hTR : T ≤ normalizer (R : Set G)) (hmJ : 1 < CFSG.Open.pRank 2 J)
    (hTJ : IsSylowOf 2 T J) :
    ⁅T, oUpperTwoPrime K⁆ ≤ oddCoreIn K ∨ CFSG.Open.IsElemAbelian 2 T := by
  have hTJle : T ≤ J := hT.le.trans inf_le_left
  have hTK : T ≤ normalizer (K : Set G) := hT.le.trans inf_le_right
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hTKb := inf_eq_bot_of_le hKJ hT2 hTJle
  have hKN : K ≤ normalizer (K : Set G) := le_normalizer
  have hRN : R ≤ normalizer (K : Set G) := hR.le.trans hKN
  have hS2 : IsPGroup 2 (R ⊔ T : Subgroup G) := hR.isPGroup.to_sup_of_normal_left' hT2 hTR
  have hSN : R ⊔ T ≤ normalizer (K : Set G) := sup_le hRN hTK
  obtain ⟨hTRcard, hRT⟩ := le_normalizer_of_isSylowOf hK hJ hKJ hfac hT hT1 hR hTR hTJ
  have hRTb : R ⊓ T = ⊥ := le_bot_iff.mp (by
    rw [inf_comm]
    exact (inf_le_inf_left T hR.le).trans hTKb.le)
  have hTRc : ∀ t ∈ T, ∀ r ∈ R, t * r = r * t := fun t ht r hr =>
    normalizer_base_commutes R T hTR (disjoint_iff.mpr (by rw [inf_comm]; exact hRTb)) t ht r
      ⟨hRT hr, hr⟩
  have hTKbar : bar K T ⊓ bar K K = ⊥ := by
    rw [← bar_inf_of_core_le (core_le K), hTKb, bar, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  have hTbcard : Nat.card (bar K T) = Nat.card T := card_bar_of_isPGroup hT2 hTK
  have hSbcard : Nat.card (bar K (R ⊔ T)) = Nat.card T * Nat.card T := by
    rw [card_bar_of_isPGroup hS2 hSN, AschbacherTheorem3.card_sup_of_le_normalizer hTR hRTb,
      hTRcard]
  rcases thm3Conclusion h3 hK hJ hKJ hfac hT hT1 hR hTR with
      ⟨hcyc, -, -⟩ | h2 | ⟨n, -, hO, -, hOc, hOel, -, -⟩ | ⟨x, -, -, -, -, hW, hNW, -, -⟩ |
      ⟨-, hW5, -⟩
  ·
    exfalso
    obtain ⟨E, hET, hE, hE4⟩ := exists_isElemAbelian_le hTJ hmJ
    have hE2 : IsPGroup 2 E := hT2.to_le hET
    have hEb : ∀ y ∈ bar K E, y ^ 2 = 1 := by
      intro y hy
      obtain ⟨e, he, rfl⟩ := (mem_bar_iff K E y).mp hy
      rw [← map_pow]
      have he2 : (e : G) ^ 2 = 1 := hE.2 e he
      have : e ^ 2 = 1 := Subtype.ext (by simpa using he2)
      rw [this, map_one]
    have hle := card_le_two_of_isCyclic (bar_mono K hET) hcyc hEb
    rw [card_bar_of_isPGroup hE2 (hET.trans hTK)] at hle
    omega
  ·
    left
    refine commutator_le_oddCoreIn_of_forall fun t ht k hk _ => ?_
    let t' : normalizer (K : Set G) := ⟨t, hTK ht⟩
    let k' : normalizer (K : Set G) := ⟨k, hKN hk⟩
    have htb : toBar K t' ∈ bar K T := toBar_mem_bar K ht
    have hkb : toBar K k' ∈ bar K K := toBar_mem_bar K hk
    have hc1 : ⁅toBar K t', toBar K k'⁆ ∈ bar K T := by
      have hkN := h2 (mem_sup_left hkb)
      have heq : ⁅toBar K t', toBar K k'⁆ =
          toBar K t' * (toBar K k' * (toBar K t')⁻¹ * (toBar K k')⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [heq]
      exact mul_mem htb ((mem_normalizer_iff.mp hkN _).mp (inv_mem htb))
    have hc2 : ⁅toBar K t', toBar K k'⁆ ∈ bar K K := by
      have htN : toBar K t' ∈ normalizer (bar K K : Set (Bar K)) :=
        bar_le_normalizer hTK hKN htb
      rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.mp htN _).mp hkb) (inv_mem hkb)
    have hc : ⁅toBar K t', toBar K k'⁆ = 1 := by
      have hmem : ⁅toBar K t', toBar K k'⁆ ∈ bar K T ⊓ bar K K := ⟨hc1, hc2⟩
      rw [hTKbar] at hmem
      exact hmem
    exact commutator_mem_oddCoreIn_of_commute (commutatorElement_eq_one_iff_mul_comm.mp hc)
  ·
    right
    have hTb : CFSG.Open.IsElemAbelian 2 (bar K T) := by
      refine isElemAbelian_of_le_sup hTKbar
        ((closure_le _).mpr fun y hy => hy.1) hOel hOc (hO ▸ ?_)
      intro y hy
      obtain ⟨m, hm⟩ := (isPGroup_bar hT2) ⟨y, hy⟩
      exact subset_closure ⟨mem_sup_right hy, m, by simpa using congrArg Subtype.val hm⟩
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun t ht => ?_⟩
    · let a' : normalizer (K : Set G) := ⟨a, hTK a.2⟩
      let b' : normalizer (K : Set G) := ⟨b, hTK b.2⟩
      have h := congrArg Subtype.val (hTb.1.is_comm.comm ⟨toBar K a', toBar_mem_bar K a.2⟩
        ⟨toBar K b', toBar_mem_bar K b.2⟩)
      simp only [Subgroup.coe_mul] at h
      rw [← map_mul, ← map_mul] at h
      have h' := congrArg Subtype.val (toBar_injOn_of_isPGroup (u := a' * b') (v := b' * a') hT2
        (T.mul_mem a.2 b.2) (T.mul_mem b.2 a.2) h)
      exact h'
    · let t' : normalizer (K : Set G) := ⟨t, hTK ht⟩
      have h := hTb.2 _ (toBar_mem_bar K ht : toBar K t' ∈ bar K T)
      rw [← map_pow, ← map_one (toBar K)] at h
      have h' := congrArg Subtype.val (toBar_injOn_of_isPGroup (u := t' ^ 2) (v := 1) hT2
        (T.pow_mem ht 2) (one_mem T) h)
      exact h'
  ·
    left
    have hSbN : bar K (R ⊔ T) ≤ normalizer (bar K T : Set (Bar K)) :=
      bar_le_normalizer (sup_le hRT le_normalizer) hTK
    rw [hW, inf_eq_left.mpr hSbN] at hNW
    have hSyl : IsSylowOf 2 (bar K (R ⊔ T)) (bar K K ⊔ bar K T) := by
      rw [← bar_sup hKN hTK]
      exact isSylowOf_bar (isSylowOf_sup hR hT2 hTK hTR hTKb) (sup_le hKN hTK)
    have hRbar : bar K (R ⊔ T) ⊓ bar K K = bar K R := by
      rw [← bar_inf_of_core_le (core_le K), sup_inf_eq hR.le hTR hTKb]
    refine commutator_le_oddCoreIn_of_forall fun t ht k hk ⟨m, hm⟩ => ?_
    let t' : normalizer (K : Set G) := ⟨t, hTK ht⟩
    let k' : normalizer (K : Set G) := ⟨k, hKN hk⟩
    have hkb : toBar K k' ∈ bar K K := toBar_mem_bar K hk
    have hk2 : IsPGroup 2 (zpowers (toBar K k')) := by
      have hpow : toBar K k' ^ 2 ^ m = 1 := by
        rw [← map_pow]
        have : k' ^ 2 ^ m = 1 := Subtype.ext (by simpa using hm)
        rw [this, map_one]
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    have hkS : toBar K k' ∈ bar K (R ⊔ T) := by
      have hzN : zpowers (toBar K k') ≤ normalizer (bar K (R ⊔ T) : Set (Bar K)) :=
        (zpowers_le).mpr (hNW (mem_sup_left hkb))
      have h2' := (isPGroup_bar hS2).to_sup_of_normal_left' hk2 hzN
      have heq := hSyl.eq_of_le le_sup_left
        (sup_le hSyl.le ((zpowers_le).mpr (mem_sup_left hkb))) h2'
      rw [← heq]
      exact mem_sup_right (mem_zpowers _)
    have hkR : toBar K k' ∈ bar K R := by
      rw [← hRbar]
      exact ⟨hkS, hkb⟩
    obtain ⟨r, hr, hrk⟩ := (mem_bar_iff K R _).mp hkR
    refine commutator_mem_oddCoreIn_of_commute (t := t') (k := k') ?_
    rw [← hrk, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hTRc t ht r hr)
  ·
    exfalso
    have hle := Subgroup.card_le_of_le (relative_weak_closure_le (bar K K) (bar K T)
      (bar K (R ⊔ T)))
    rw [hW5, hSbcard, hTbcard] at hle
    have h1 : 1 < Nat.card T := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      exact hT1
    have h2 : Nat.card T * Nat.card T < Nat.card T ^ 3 := by
      rw [pow_succ, pow_two]
      exact lt_mul_of_one_lt_right (Nat.mul_pos Nat.card_pos Nat.card_pos) h1
    omega

end CFSG.ComponentClassification.Asc76.Lemma22
