module

public import CFSG.GH74.Uniqueness.Section4Lemma46
public import CFSG.GH74.Uniqueness.Section4Basic

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

namespace Simple

open CFSG.ABGLocalTools

section Helpers

variable {X : Type} [Group X]

theorem le_normalizer_of_normal {A : Subgroup X} (hA : A.Normal) (K : Subgroup X) :
    K ≤ normalizer (A : Set X) := by
  intro g _
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => hA.conj_mem x hx g
  · intro hx
    have := hA.conj_mem _ hx g⁻¹
    simpa [mul_assoc] using this

theorem normal_of_forall_mem_normalizer {H : Subgroup X}
    (h : ∀ g : X, g ∈ normalizer (H : Set X)) : H.Normal :=
  ⟨fun n hn g => ((Subgroup.mem_normalizer_iff.mp (h g)) n).mp hn⟩

theorem mem_or_mul_mem_of_sup_zpowers_eq_top {A : Subgroup X} (hA : A.Normal) {z : X}
    (hz : z * z = 1) (hAz : A ⊔ zpowers z = ⊤) (m : X) : m ∈ A ∨ m * z ∈ A :=
  mem_sup_zpowers_of_involution hz (fun x hx => hA.conj_mem x hx z) (by rw [hAz]; trivial)

theorem commutator_mem_of_sup_zpowers_eq_top {A : Subgroup X} (hA : A.Normal) {z : X}
    (hz : z * z = 1) (hAz : A ⊔ zpowers z = ⊤) (m : X) : m * z * m⁻¹ * z⁻¹ ∈ A := by
  rcases mem_or_mul_mem_of_sup_zpowers_eq_top hA hz hAz m with hm | hm
  · have h1 : z * m⁻¹ * z⁻¹ ∈ A := hA.conj_mem m⁻¹ (A.inv_mem hm) z
    have : m * z * m⁻¹ * z⁻¹ = m * (z * m⁻¹ * z⁻¹) := by group
    rw [this]
    exact A.mul_mem hm h1
  · have h1 : z * (m * z)⁻¹ * z⁻¹ ∈ A := hA.conj_mem _ (A.inv_mem hm) z
    have : m * z * m⁻¹ * z⁻¹ = (m * z) * (z * (m * z)⁻¹ * z⁻¹) := by group
    rw [this]
    exact A.mul_mem hm h1

end Helpers

section Cauchy

variable {X : Type} [Group X] [Finite X]

theorem exists_mem_orderOf_eq_two_of_even_card {K : Subgroup X} (hK : Even (Nat.card K)) :
    ∃ y ∈ K, orderOf y = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (even_iff_two_dvd.mp hK)
  exact ⟨x, x.2, (Subgroup.orderOf_coe x).trans hx⟩

theorem odd_card_of_forall_orderOf_ne_two {K : Subgroup X} (hK : ∀ y ∈ K, orderOf y ≠ 2) :
    Odd (Nat.card K) := by
  by_contra h
  obtain ⟨y, hy, hy2⟩ := exists_mem_orderOf_eq_two_of_even_card (Nat.not_odd_iff_even.mp h)
  exact hK y hy hy2

omit [Finite X] in
theorem even_card_of_mem_orderOf_eq_two {K : Subgroup X} {y : X} (hy : y ∈ K)
    (h2 : orderOf y = 2) : Even (Nat.card K) :=
  even_iff_two_dvd.mpr (h2 ▸ Subgroup.orderOf_dvd_natCard K hy)

omit [Finite X] in
theorem eq_one_of_mem_odd_of_mem_isPGroup {N P : Subgroup X} (hN : Odd (Nat.card N))
    (hP : IsPGroup 2 P) {x : X} (hxN : x ∈ N) (hxP : x ∈ P) : x = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨x, hxP⟩
  rw [Subgroup.orderOf_mk] at hk
  have hodd : Odd (orderOf x) := Odd.of_dvd_nat hN (Subgroup.orderOf_dvd_natCard N hxN)
  rw [hk] at hodd
  have hk0 : k = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.mp hk

theorem isSylowOf_top (T : Sylow 2 X) : IsSylowOf 2 (T : Subgroup X) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff]
  refine ⟨le_top, T.isPGroup', ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact T.not_dvd_index

theorem exists_mem_inf_orderOf_eq_two {P K N : Subgroup X} (hP : IsSylowOf 2 P K) (hNK : N ≤ K)
    (hKN : K ≤ normalizer (N : Set X)) (hN : Even (Nat.card N)) :
    ∃ y ∈ P ⊓ N, orderOf y = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hP.inf_of_le_normalizer hNK hKN
  have hcard := h.card_eq
  have h2 : 2 ∣ Nat.card N := even_iff_two_dvd.mp hN
  have hpos : 1 ≤ (Nat.card N).factorization 2 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').mp h2
  apply exists_mem_orderOf_eq_two_of_even_card
  rw [hcard]
  exact Nat.even_pow.mpr ⟨even_two, by omega⟩

end Cauchy

section SE

theorem exists_conj_of_isStronglyEmbedded {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : CFSG.IsStronglyEmbedded K) {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2) :
    ∃ g : G, g⁻¹ * x * g = y := by
  have hnat : CFSG.BenderSuzuki.IsStronglyEmbedded K :=
    CFSG.BenderSuzuki.isStronglyEmbedded_of_parity K
      (isStronglyEmbeddedOrder_of_isStronglyEmbedded hK)
  have hinv : ∀ w : G, orderOf w = 2 → CFSG.BenderSuzuki.PFAppendixIII.IsInvolution w := by
    intro w hw
    exact ⟨(orderOf_eq_prime_iff.mp hw).2, (orderOf_eq_prime_iff.mp hw).1⟩
  obtain ⟨g, hg⟩ := hnat.involutions_conjugate (hinv x hx) (hinv y hy)
  exact ⟨g, hg⟩

end SE

section ZStar

variable {X : Type} [Group X] [Finite X]

theorem isZStarIn_of_isolated {W : Subgroup X} {t : X} (htW : t ∈ W) (ht2 : t * t = 1)
    (ht1 : t ≠ 1)
    (hiso : ∀ g ∈ W, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t) :
    IsZStarIn W t := by
  have : Fintype W := Fintype.ofFinite W
  let t' : W := ⟨t, htW⟩
  have ht'1 : t' ≠ 1 := fun h1 => ht1 (congrArg Subtype.val h1)
  have ht'2 : t' * t' = 1 := Subtype.ext ht2
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar W t' ht'1 ht'2 (fun g hg =>
    Subtype.ext (hiso g g.2 (congrArg Subtype.val hg)))
  have hsub : (N.map W.subtype).subgroupOf W = N :=
    Subgroup.comap_map_eq_self_of_injective W.subtype_injective N
  refine ⟨htW, N.map W.subtype, Subgroup.map_subtype_le N, ?_, ?_, ?_⟩
  · rw [hsub]
    exact hNn
  · rw [Subgroup.card_map_of_injective W.subtype_injective]
    exact hNodd
  · intro m hm
    exact Subgroup.mem_map.mpr ⟨⟨m, hm⟩ * t' * ⟨m, hm⟩⁻¹ * t'⁻¹, hN ⟨m, hm⟩, rfl⟩

end ZStar

section MinNormal

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem exists_minimal_normal [Nontrivial X] :
    ∃ A : Subgroup X, A.Normal ∧ A ≠ ⊥ ∧
      ∀ B : Subgroup X, B.Normal → B ≠ ⊥ → B ≤ A → B = A := by
  obtain ⟨A, ⟨hAn, hA0⟩, hmin⟩ := (wellFounded_lt (α := Subgroup X)).has_min
    {N : Subgroup X | N.Normal ∧ N ≠ ⊥}
    ⟨⊤, inferInstance, (Subgroup.nontrivial_iff_ne_bot ⊤).mp inferInstance⟩
  refine ⟨A, hAn, hA0, fun B hBn hB0 hBA => ?_⟩
  by_contra hne
  exact hmin B ⟨hBn, hB0⟩ (lt_of_le_of_ne hBA hne)

theorem exists_minimal_even {A : Subgroup X} (hA : Even (Nat.card A)) :
    ∃ A₁ : Subgroup X, A₁ ≤ A ∧ A ≤ normalizer (A₁ : Set X) ∧ Even (Nat.card A₁) ∧
      ∀ B : Subgroup X, B ≤ A₁ → A ≤ normalizer (B : Set X) → Even (Nat.card B) → B = A₁ := by
  obtain ⟨A₁, ⟨h1, h2, h3⟩, hmin⟩ := (wellFounded_lt (α := Subgroup X)).has_min
    {B : Subgroup X | B ≤ A ∧ A ≤ normalizer (B : Set X) ∧ Even (Nat.card B)}
    ⟨A, le_rfl, Subgroup.le_normalizer, hA⟩
  refine ⟨A₁, h1, h2, h3, fun B hB hAB hEven => ?_⟩
  by_contra hne
  exact hmin B ⟨hB.trans h1, hAB, hEven⟩ (lt_of_le_of_ne hB hne)

theorem mem_normalizer_of_isCentralInvolution {A A₁ : Subgroup X} (hAn : A.Normal)
    (hA₁A : A₁ ≤ A) (hA₁n : A ≤ normalizer (A₁ : Set X)) (hA₁e : Even (Nat.card A₁))
    (hmin : ∀ B : Subgroup X, B ≤ A₁ → A ≤ normalizer (B : Set X) → Even (Nat.card B) → B = A₁)
    {w : X} (hw2 : w * w = 1) (hw : IsCentralInvolution w) : w ∈ normalizer (A₁ : Set X) := by
  obtain ⟨-, S', -, hcomm⟩ := hw
  have hSA : IsSylowOf 2 ((S' : Subgroup X) ⊓ A) A :=
    (isSylowOf_top S').inf_of_le_normalizer le_top (le_normalizer_of_normal hAn ⊤)
  obtain ⟨y, hy, hy2⟩ := exists_mem_inf_orderOf_eq_two hSA hA₁A hA₁n hA₁e
  obtain ⟨⟨hyS', -⟩, hyA₁⟩ := Subgroup.mem_inf.mp hy
  set B : Subgroup X := A₁ ⊓ conjugate A₁ w with hB
  have hBA₁ : B ≤ A₁ := inf_le_left
  have hAB : A ≤ normalizer (B : Set X) := by
    intro a ha
    refine mem_normalizer_inf (hA₁n ha) ?_
    rw [normalizer_conjugate, mem_conjugate_iff]
    exact hA₁n (hAn.conj_mem a ha w)
  have hyB : y ∈ B := by
    refine Subgroup.mem_inf.mpr ⟨hyA₁, ?_⟩
    rw [mem_conjugate_iff]
    have : w * y * w⁻¹ = y := by
      have h := hcomm y hyS'
      calc w * y * w⁻¹ = (y * w) * w⁻¹ := by rw [h]
        _ = y := by group
    rw [this]
    exact hyA₁
  have hBeq : B = A₁ := hmin B hBA₁ hAB (even_card_of_mem_orderOf_eq_two hyB hy2)
  have hfwd : ∀ x ∈ A₁, w * x * w⁻¹ ∈ A₁ := fun x hx => by
    have : x ∈ B := hBeq ▸ hx
    exact mem_conjugate_iff.mp (Subgroup.mem_inf.mp this).2
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hfwd x hx, fun hx => ?_⟩
  have h1 := hfwd _ hx
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have e : w * (w * x * w⁻¹) * w⁻¹ = x := by
    rw [hwi]
    calc w * (w * x * w) * w = (w * w) * x * (w * w) := by group
      _ = x := by rw [hw2]; group
  rwa [e] at h1


theorem eq_of_normal_of_even (S : ZDSetup X Z M) {A : Subgroup X} (hAn : A.Normal)
    (hAmin : ∀ B : Subgroup X, B.Normal → B ≠ ⊥ → B ≤ A → B = A)
    (hAe : Even (Nat.card A)) {B : Subgroup X} (hBA : B ≤ A)
    (hBn : A ≤ normalizer (B : Set X)) (hBe : Even (Nat.card B)) : B = A := by
  obtain ⟨A₁, h1, h2, h3, hmin⟩ := exists_minimal_even hAe
  have hZ : ∀ z' ∈ Z, z' ∈ normalizer (A₁ : Set X) := fun z' hz' =>
    mem_normalizer_of_isCentralInvolution hAn h1 h2 h3 hmin (S.invariant.mul_self_eq_one hz')
      (S.isCentralInvolution hz')
  have hnorm : A₁.Normal := by
    have : (⊤ : Subgroup X) ≤ normalizer (A₁ : Set X) := by
      rw [← S.gen, Subgroup.closure_le]
      exact hZ
    exact normalizer_eq_top_iff.mp (top_le_iff.mp this)
  have hA₁0 : A₁ ≠ ⊥ := by
    intro h
    rw [h] at h3
    simp at h3
  have hA₁A : A₁ = A := hAmin A₁ hnorm hA₁0 h1
  have := hmin B (hA₁A ▸ hBA) hBn hBe
  rw [this, hA₁A]

theorem eq_bot_of_normal_of_odd (h45 : ∀ N : Subgroup X, N.Normal → Group.IsSolvable ↥N → N = ⊥)
    {A : Subgroup X} (hAn : A.Normal) {B : Subgroup X} (hBA : B ≤ A)
    (hBn : A ≤ normalizer (B : Set X)) (hBo : Odd (Nat.card B)) : B = ⊥ := by
  have h1 : B ≤ pPrimeCoreIn A := le_pPrimeCoreIn hBA hBn hBo
  have hP : (pPrimeCoreIn A).Normal := normal_of_forall_mem_normalizer fun g =>
    mem_normalizer_pPrimeCoreIn (le_normalizer_of_normal hAn ⊤ (Subgroup.mem_top g))
  have hsolv : Group.IsSolvable ↥(pPrimeCoreIn A) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_pPrimeCoreIn A)
  have h2 := h45 _ hP hsolv
  rw [h2] at h1
  exact le_bot_iff.mp h1

theorem even_card_of_normal_ne_bot (h45 : ∀ N : Subgroup X, N.Normal → Group.IsSolvable ↥N → N = ⊥)
    {A : Subgroup X} (hAn : A.Normal) (hA0 : A ≠ ⊥) : Even (Nat.card A) := by
  by_contra h
  exact hA0 (h45 A hAn (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp h)))

omit [Finite X] in
theorem exists_not_commute_of_normal_ne_bot
    (h45 : ∀ N : Subgroup X, N.Normal → Group.IsSolvable ↥N → N = ⊥)
    {A : Subgroup X} (hAn : A.Normal) (hA0 : A ≠ ⊥) : ∃ a b : ↥A, a * b ≠ b * a := by
  by_contra h
  push Not at h
  apply hA0
  refine h45 A hAn ?_
  have : IsMulCommutative ↥A := ⟨⟨h⟩⟩
  infer_instance

theorem isSimpleGroup_of_minimal (S : ZDSetup X Z M)
    (h45 : ∀ N : Subgroup X, N.Normal → Group.IsSolvable ↥N → N = ⊥)
    {A : Subgroup X} (hAn : A.Normal) (hA0 : A ≠ ⊥)
    (hAmin : ∀ B : Subgroup X, B.Normal → B ≠ ⊥ → B ≤ A → B = A) : IsSimpleGroup ↥A := by
  have hAe := even_card_of_normal_ne_bot h45 hAn hA0
  have : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA0
  refine { eq_bot_or_eq_top_of_normal := fun K hK => ?_ }
  set B : Subgroup X := K.map A.subtype with hB
  have hBA : B ≤ A := Subgroup.map_subtype_le K
  have hsub : B.subgroupOf A = K :=
    Subgroup.comap_map_eq_self_of_injective A.subtype_injective K
  have hBn : A ≤ normalizer (B : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBA).mp (by rw [hsub]; exact hK)
  by_cases hBe : Even (Nat.card B)
  · right
    have hBA' : B = A := eq_of_normal_of_even S hAn hAmin hAe hBA hBn hBe
    rw [← hsub, hBA']
    exact Subgroup.subgroupOf_self A
  · left
    have hBo : Odd (Nat.card B) := Nat.not_even_iff_odd.mp hBe
    have hB0 := eq_bot_of_normal_of_odd h45 hAn hBA hBn hBo
    rw [← hsub, hB0]
    simp

theorem commute_of_normal_of_gen (S : ZDSetup X Z M) {A : Subgroup X} (hAn : A.Normal) {z : X}
    (hz : z ∈ Z) (hcent : ∀ a ∈ A, a * z = z * a) : ∀ a ∈ A, ∀ x : X, a * x = x * a := by
  intro a ha x
  have hle : (⊤ : Subgroup X) ≤ centralizer ({a} : Set X) := by
    rw [← S.gen, Subgroup.closure_le]
    intro y hy
    obtain ⟨c, hc⟩ := isConj_iff.mp (S.prodDisc.isConj_of_mem S.invariant hz hy)
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have hca : c⁻¹ * a * c ∈ A := by simpa using hAn.conj_mem a ha c⁻¹
    have h1 := hcent _ hca
    rw [← hc]
    calc c * z * c⁻¹ * a = c * (z * (c⁻¹ * a * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * a * c) * z) * c⁻¹ := by rw [h1]
      _ = a * (c * z * c⁻¹) := by group
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top x))).symm

theorem eq_top_of_mem_normal (S : ZDSetup X Z M) {A : Subgroup X} (hAn : A.Normal) {z : X}
    (hz : z ∈ Z) (hzA : z ∈ A) : A = ⊤ := by
  rw [eq_top_iff, ← S.gen, Subgroup.closure_le]
  intro y hy
  obtain ⟨c, hc⟩ := isConj_iff.mp (S.prodDisc.isConj_of_mem S.invariant hz hy)
  rw [SetLike.mem_coe, ← hc]
  exact hAn.conj_mem z hzA c

theorem not_le_of_minimal (S : ZDSetup X Z M)
    (h45 : ∀ N : Subgroup X, N.Normal → Group.IsSolvable ↥N → N = ⊥)
    {A : Subgroup X} (hAn : A.Normal) (hA0 : A ≠ ⊥) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) :
    ¬ A ≤ M := by
  intro hAM
  have hz2 : z * z = 1 := S.invariant.mul_self_eq_one hz
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hz1 : z ≠ 1 := fun h => by
    have := S.invariant.1 z hz
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hiso_A : ∀ a ∈ A, (a * z * a⁻¹) * z = z * (a * z * a⁻¹) → a * z * a⁻¹ = z := by
    intro a ha hcomm
    by_contra hne
    obtain ⟨z', hz'⟩ : ∃ z', z' = a * z * a⁻¹ := ⟨_, rfl⟩
    rw [← hz'] at hcomm hne
    have hz'Z : z' ∈ Z := by
      have := S.invariant.2 z hz a⁻¹
      rw [inv_inv] at this
      rwa [hz']
    have hz'M : z' ∈ M := by
      rw [hz']
      exact M.mul_mem (M.mul_mem (hAM ha) hzM) (M.inv_mem (hAM ha))
    have hz'2 : z' * z' = 1 := S.invariant.mul_self_eq_one hz'Z
    have hcz : z * z' = z' * z := hcomm.symm
    have hu2 : orderOf (z * z') = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · calc (z * z') ^ 2 = (z * z') * (z * z') := sq _
          _ = z * (z' * z) * z' := by group
          _ = z * (z * z') * z' := by rw [hcomm]
          _ = (z * z) * (z' * z') := by group
          _ = 1 := by rw [hz2, hz'2, one_mul]
      · intro h1
        apply hne
        have := eq_inv_of_mul_eq_one_right h1
        rw [this, hzi]
    have huA : z * z' ∈ A := by
      have : z * z' = (z * a * z⁻¹) * a⁻¹ := by rw [hz', hzi]; group
      rw [this]
      exact A.mul_mem (hAn.conj_mem a ha z) (A.inv_mem ha)
    have hu𝒱 : z * z' ∈ productInvolutions Z := ⟨hu2, z, hz, z', hz'Z, hcz, rfl⟩
    have huM : z * z' ∈ M := M.mul_mem hzM hz'M
    have huU := S.mem_uniqU_of_mem_productInvolutions hu𝒱 huM
    have hUniq : IsUniqueSubgroup M (zpowers (z * z')) :=
      isUniqueSubgroup_zpowers huM ((mem_uniqU_iff 2).mp huU).2.2
    have hnorm : normalizer (A : Set X) ≤ M :=
      hUniq.normalizer_le (Subgroup.zpowers_le.mpr huA) hAM
    exact S.prodDisc.ne_top (top_le_iff.mp fun g _ =>
      hnorm (le_normalizer_of_normal hAn ⊤ (Subgroup.mem_top g)))
  have hiso : ∀ g ∈ A ⊔ zpowers z, (g * z * g⁻¹) * z = z * (g * z * g⁻¹) →
      g * z * g⁻¹ = z := by
    intro g hg hcomm
    rcases mem_sup_zpowers_of_involution hz2 (fun x hx => hAn.conj_mem x hx z) hg with hgA | hgA
    · exact hiso_A g hgA hcomm
    · have e : g * z * g⁻¹ = (g * z) * z * (g * z)⁻¹ := by group
      rw [e] at hcomm ⊢
      exact hiso_A _ hgA hcomm
  obtain ⟨-, N, hNW, hNn, hNodd, hN⟩ := isZStarIn_of_isolated (W := A ⊔ zpowers z)
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers z)) hz2 hz1 hiso
  have hWN : A ⊔ zpowers z ≤ normalizer (N : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNW).mp hNn
  have hNA : N ≤ A := by
    intro n hn
    have hnW : n ∈ A ⊔ zpowers z := hNW hn
    have hnn : n * n ∈ A := mul_self_mem_of_mem_sup_zpowers hz2
      (le_normalizer_of_normal hAn ⊤ (Subgroup.mem_top z)) hnW
    have hodd : Odd (orderOf n) := Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard N hn)
    exact mem_of_mul_self_mem_of_odd_orderOf hodd hnn
  have hN0 : N = ⊥ := eq_bot_of_normal_of_odd h45 hAn hNA (le_sup_left.trans hWN) hNodd
  have hcent : ∀ a ∈ A, a * z = z * a := by
    intro a ha
    have h1 := hN a (Subgroup.mem_sup_left ha)
    rw [hN0, Subgroup.mem_bot] at h1
    calc a * z = (a * z * a⁻¹ * z⁻¹) * (z * a) := by group
      _ = z * a := by rw [h1, one_mul]
  obtain ⟨a, b, hab⟩ := exists_not_commute_of_normal_ne_bot h45 hAn hA0
  exact hab (Subtype.ext (commute_of_normal_of_gen S hAn hz hcent a a.2 b))

theorem sup_eq_top_of_minimal (S : ZDSetup X Z M)
    (h45 : ∀ N : Subgroup X, N.Normal → Group.IsSolvable ↥N → N = ⊥)
    (h44 : ∀ H : Subgroup X, H ≠ ⊤ → ¬ H ≤ M → (Z ∩ ((H ⊓ M : Subgroup X) : Set X)).Nonempty →
      IsStronglyEmbedded ((M ⊓ zHull Z H).subgroupOf (zHull Z H)))
    {A : Subgroup X} (hAn : A.Normal) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) (hAM : ¬ A ≤ M) :
    A ⊔ zpowers z = ⊤ := by
  by_contra hne
  have hz2 : z * z = 1 := S.invariant.mul_self_eq_one hz
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hz1 : z ≠ 1 := fun h => by
    have := S.invariant.1 z hz
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hzA' : z ∈ A ⊔ zpowers z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hHM : ¬ A ⊔ zpowers z ≤ M := fun h => hAM (le_sup_left.trans h)
  have hSE := h44 (A ⊔ zpowers z) hne hHM
    ⟨z, hz, Subgroup.mem_inf.mpr ⟨hzA', hzM⟩⟩
  have hzL : z ∈ zHull Z (A ⊔ zpowers z) := Subgroup.subset_closure ⟨hz, hzA'⟩
  have hA'L : A ⊔ zpowers z ≤ normalizer (zHull Z (A ⊔ zpowers z) : Set X) :=
    le_normalizer_zHull S.invariant _
  have hconjL : ∀ y ∈ zHull Z (A ⊔ zpowers z), orderOf y = 2 → ∃ g : X, g⁻¹ * z * g = y := by
    intro y hyL hy2
    obtain ⟨g, hg⟩ := exists_conj_of_isStronglyEmbedded hSE (x := (⟨z, hzL⟩ : zHull Z (A ⊔ zpowers z)))
      (y := ⟨y, hyL⟩) (by rw [Subgroup.orderOf_mk]; exact S.invariant.1 z hz)
      (by rw [Subgroup.orderOf_mk]; exact hy2)
    exact ⟨g, congrArg Subtype.val hg⟩
  by_cases hinv : ∃ y ∈ A ⊓ zHull Z (A ⊔ zpowers z), orderOf y = 2
  · obtain ⟨y, hy, hy2⟩ := hinv
    obtain ⟨g, hg⟩ := hconjL y (Subgroup.mem_inf.mp hy).2 hy2
    have hzA : z ∈ A := by
      have : z = g * y * g⁻¹ := by rw [← hg]; group
      rw [this]
      exact hAn.conj_mem y (Subgroup.mem_inf.mp hy).1 g
    have hA : A = ⊤ := eq_top_of_mem_normal S hAn hz hzA
    exact hne (top_le_iff.mp (by rw [← hA]; exact le_sup_left))
  · push Not at hinv
    have hodd : Odd (Nat.card ↥(A ⊓ zHull Z (A ⊔ zpowers z))) :=
      odd_card_of_forall_orderOf_ne_two fun y hy => hinv y hy
    have hbot : A ⊓ zHull Z (A ⊔ zpowers z) = ⊥ := by
      refine eq_bot_of_normal_of_odd h45 hAn inf_le_left ?_ hodd
      intro a ha
      exact mem_normalizer_inf (le_normalizer_of_normal hAn ⊤ (Subgroup.mem_top a))
        (hA'L (Subgroup.mem_sup_left ha))
    apply hAM
    intro a ha
    have hz'Z : a * z * a⁻¹ ∈ Z := by
      have := S.invariant.2 z hz a⁻¹
      rwa [inv_inv] at this
    have hz'A' : a * z * a⁻¹ ∈ A ⊔ zpowers z :=
      (A ⊔ zpowers z).mul_mem ((A ⊔ zpowers z).mul_mem (Subgroup.mem_sup_left ha) hzA')
        ((A ⊔ zpowers z).inv_mem (Subgroup.mem_sup_left ha))
    have hz'L : a * z * a⁻¹ ∈ zHull Z (A ⊔ zpowers z) := Subgroup.subset_closure ⟨hz'Z, hz'A'⟩
    have hz'z : a * z * a⁻¹ = z := by
      rcases mem_sup_zpowers_of_involution hz2 (fun x hx => hAn.conj_mem x hx z) hz'A' with h1 | h1
      · exfalso
        have h2 : a * z * a⁻¹ ∈ A ⊓ zHull Z (A ⊔ zpowers z) := Subgroup.mem_inf.mpr ⟨h1, hz'L⟩
        rw [hbot, Subgroup.mem_bot] at h2
        apply hz1
        calc z = a⁻¹ * (a * z * a⁻¹) * a := by group
          _ = 1 := by rw [h2]; group
      · have h2 : (a * z * a⁻¹) * z ∈ A ⊓ zHull Z (A ⊔ zpowers z) :=
          Subgroup.mem_inf.mpr ⟨h1, (zHull Z (A ⊔ zpowers z)).mul_mem hz'L hzL⟩
        rw [hbot, Subgroup.mem_bot] at h2
        have := eq_inv_of_mul_eq_one_left h2
        rw [this, hzi]
    have hazC : a ∈ centralizer ({z} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc a * z = (a * z * a⁻¹) * a := by group
        _ = z * a := by rw [hz'z]
    exact S.prodDisc.centralizer_le_of_mem hz hzM hazC

end MinNormal

section Lemma410Aux

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

open CFSG.LocalAnalysis.ComponentInitial.FourGroup in
theorem exists_conj_mem_sylow_of_commute {z y : X} (hz2 : z * z = 1) (hy2 : y * y = 1)
    (hzy : z * y = y * z) (hz1 : z ≠ 1) (hy1 : y ≠ 1) (hne : z ≠ y) (P : Sylow 2 X) :
    ∃ g : X, g * z * g⁻¹ ∈ (P : Subgroup X) ∧ g * y * g⁻¹ ∈ (P : Subgroup X) := by
  have hVp : IsPGroup 2 (kleinFourOf z y hz2 hy2 hzy) :=
    IsPGroup.of_card (n := 2) (by rw [card_kleinFourOf hz1 hy1 hne]; norm_num)
  obtain ⟨Q, hVQ⟩ := hVp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q P
  refine ⟨g, ?_, ?_⟩
  · rw [← hg]
    exact (mem_smul_sylow_iff Q g _).mpr ⟨z, hVQ left_mem_kleinFourOf, rfl⟩
  · rw [← hg]
    exact (mem_smul_sylow_iff Q g _).mpr ⟨y, hVQ right_mem_kleinFourOf, rfl⟩

theorem odd_card_zHull_inf (S : ZDSetup X Z M)
    (h44 : ∀ H : Subgroup X, H ≠ ⊤ → ¬ H ≤ M → (Z ∩ ((H ⊓ M : Subgroup X) : Set X)).Nonempty →
      IsStronglyEmbedded ((M ⊓ zHull Z H).subgroupOf (zHull Z H)))
    {A : Subgroup X} (hAn : A.Normal) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) (hzA : z ∉ A)
    {H : Subgroup X} (hH : H ≠ ⊤) (hHM : ¬ H ≤ M) (hzH : z ∈ H) :
    Odd (Nat.card ↥(zHull Z H ⊓ A)) := by
  have hSE := h44 H hH hHM ⟨z, hz, Subgroup.mem_inf.mpr ⟨hzH, hzM⟩⟩
  have hzL : z ∈ zHull Z H := Subgroup.subset_closure ⟨hz, hzH⟩
  apply odd_card_of_forall_orderOf_ne_two
  intro y hy hy2
  obtain ⟨hyL, hyA⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨g, hg⟩ := exists_conj_of_isStronglyEmbedded hSE (x := (⟨z, hzL⟩ : zHull Z H))
    (y := ⟨y, hyL⟩) (by rw [Subgroup.orderOf_mk]; exact S.invariant.1 z hz)
    (by rw [Subgroup.orderOf_mk]; exact hy2)
  obtain ⟨g', hg'⟩ : ∃ g' : X, g'⁻¹ * z * g' = y := ⟨(g : X), congrArg Subtype.val hg⟩
  apply hzA
  have : z = g' * y * g'⁻¹ := by rw [← hg']; group
  rw [this]
  exact hAn.conj_mem y hyA g'

theorem mul_inv_mem_zHull_inf (S : ZDSetup X Z M) {A : Subgroup X} (hAn : A.Normal) {z : X}
    (hz : z ∈ Z) (hzM : z ∈ M) (hAz : A ⊔ zpowers z = ⊤) {H : Subgroup X} (hHM : ¬ H ≤ M)
    (hzH : z ∈ H) {t : X} (ht : t ∈ Z) (htH : t ∈ H) : t * z⁻¹ ∈ zHull Z H ⊓ A := by
  have hz2 : z * z = 1 := S.invariant.mul_self_eq_one hz
  have hzL : z ∈ zHull Z H := Subgroup.subset_closure ⟨hz, hzH⟩
  have htL : t ∈ zHull Z H := Subgroup.subset_closure ⟨ht, htH⟩
  obtain ⟨l, -, hlt⟩ := S.exists_conj_zHull hHM ⟨z, hz, Subgroup.mem_inf.mpr ⟨hzH, hzM⟩⟩ hz hzH
    hzM ht htH
  refine Subgroup.mem_inf.mpr ⟨(zHull Z H).mul_mem htL ((zHull Z H).inv_mem hzL), ?_⟩
  have := commutator_mem_of_sup_zpowers_eq_top hAn hz2 hAz l⁻¹
  rw [← hlt]
  simpa using this

end Lemma410Aux

section Prop43Aux

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem exists_mem_orderOf_eq_two_of_isPGroup {K : Subgroup X} (hK : IsPGroup 2 K) (hK1 : K ≠ ⊥) :
    ∃ x ∈ K, orderOf x = 2 := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hK1 (Subgroup.card_eq_one.mp (by simpa using hn))
  have h2 : 2 ∣ Nat.card K := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 h2
  exact ⟨c, c.2, (Subgroup.orderOf_coe c).trans hc⟩

theorem exists_involution_normal_inf_center {A : Subgroup X} (hAn : A.Normal)
    (hAe : Even (Nat.card A)) (T : Sylow 2 X) :
    ∃ c ∈ A, c ∈ (T : Subgroup X) ∧ orderOf c = 2 ∧ ∀ s ∈ (T : Subgroup X), s * c = c * s := by
  obtain ⟨y, hy, hy2⟩ := exists_mem_inf_orderOf_eq_two (isSylowOf_top T) le_top
    (le_normalizer_of_normal hAn ⊤) hAe
  obtain ⟨hyT, hyA⟩ := Subgroup.mem_inf.mp hy
  have hnil : Group.IsNilpotent ↥(T : Subgroup X) := T.isPGroup'.isNilpotent
  have hN : (A.subgroupOf (T : Subgroup X)).Normal := hAn.subgroupOf _
  have hN0 : A.subgroupOf (T : Subgroup X) ≠ ⊥ := by
    intro h
    have hmem : (⟨y, hyT⟩ : ↥(T : Subgroup X)) ∈ A.subgroupOf (T : Subgroup X) := hyA
    rw [h, Subgroup.mem_bot] at hmem
    have := congrArg Subtype.val hmem
    simp only [OneMemClass.coe_one] at this
    rw [this, orderOf_one] at hy2
    exact absurd hy2 (by norm_num)
  have h1 := Group.IsNilpotent.inf_center_ne_bot_of_normal hN0
  have hKp : IsPGroup 2 ↥(A.subgroupOf (T : Subgroup X) ⊓ center ↥(T : Subgroup X)) :=
    T.isPGroup'.to_subgroup _
  obtain ⟨κ, hκ, hκ2⟩ := exists_mem_orderOf_eq_two_of_isPGroup hKp h1
  obtain ⟨hκA, hκC⟩ := Subgroup.mem_inf.mp hκ
  refine ⟨(κ : X), hκA, κ.2, (Subgroup.orderOf_coe κ).trans hκ2, fun s hs => ?_⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hκC ⟨s, hs⟩)

end Prop43Aux

end Simple

section Main

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.lemma49 (S : ZDSetup X Z M)
    (h45 : ∀ N : Subgroup X, N.Normal → Group.IsSolvable ↥N → N = ⊥)
    (h44 : ∀ H : Subgroup X, H ≠ ⊤ → ¬ H ≤ M → (Z ∩ ((H ⊓ M : Subgroup X) : Set X)).Nonempty →
      IsStronglyEmbedded ((M ⊓ zHull Z H).subgroupOf (zHull Z H)))
    (hX : ¬ IsSimpleGroup X) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) :
    ∃ A : Subgroup X, A.Normal ∧ IsSimpleGroup ↥A ∧ (∃ a b : ↥A, a * b ≠ b * a) ∧
      Even (Nat.card A) ∧ z ∉ A ∧ A ⊔ zpowers z = ⊤ ∧ ¬ A ≤ M := by
  have hz1 : z ≠ 1 := fun h => by
    have := S.invariant.1 z hz
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have : Nontrivial X := ⟨⟨z, 1, hz1⟩⟩
  obtain ⟨A, hAn, hA0, hAmin⟩ := Simple.exists_minimal_normal (X := X)
  have hAM : ¬ A ≤ M := Simple.not_le_of_minimal S h45 hAn hA0 hz hzM
  have hAz := Simple.sup_eq_top_of_minimal S h45 h44 hAn hz hzM hAM
  refine ⟨A, hAn, Simple.isSimpleGroup_of_minimal S h45 hAn hA0 hAmin,
    Simple.exists_not_commute_of_normal_ne_bot h45 hAn hA0, Simple.even_card_of_normal_ne_bot h45 hAn hA0, ?_,
    hAz, hAM⟩
  intro hzA
  have hA : A = ⊤ := Simple.eq_top_of_mem_normal S hAn hz hzA
  apply hX
  refine { eq_bot_or_eq_top_of_normal := fun N hN => ?_ }
  by_cases hN0 : N = ⊥
  · exact Or.inl hN0
  · right
    have := hAmin N hN hN0 (hA ▸ le_top)
    rw [this, hA]

theorem ZDSetup.lemma410 (S : ZDSetup X Z M)
    (h45 : ∀ N : Subgroup X, N.Normal → Group.IsSolvable ↥N → N = ⊥)
    (h44 : ∀ H : Subgroup X, H ≠ ⊤ → ¬ H ≤ M → (Z ∩ ((H ⊓ M : Subgroup X) : Set X)).Nonempty →
      IsStronglyEmbedded ((M ⊓ zHull Z H).subgroupOf (zHull Z H)))
    {A : Subgroup X} (hAn : A.Normal) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) (hzA : z ∉ A)
    (hAz : A ⊔ zpowers z = ⊤) {u : X} (hu : orderOf u = 2) (huz : u * z = z * u)
    (hH : ¬ centralizer ({u} : Set X) ≤ M) :
    IsZStarIn (centralizer ({u} : Set X)) z ∧ ¬ pPrimeCoreIn (centralizer ({u} : Set X)) ≤ M ∧
      ¬ IsCentralInvolution u := by
  set H := centralizer ({u} : Set X) with hHdef
  have hz2 : z * z = 1 := S.invariant.mul_self_eq_one hz
  have hzH : z ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr huz.symm
  have hHtop : H ≠ ⊤ := by
    intro htop
    have hcomm : ∀ g : X, g * u = u * g := fun g =>
      Subgroup.mem_centralizer_singleton_iff.mp (show g ∈ H from htop ▸ Subgroup.mem_top g)
    have hn : (zpowers u).Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have h1 : g * u * g⁻¹ = u := by rw [hcomm g]; group
      rw [← conj_zpow, h1]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) _
    have hs : Group.IsSolvable ↥(zpowers u) := inferInstance
    have h0 := h45 _ hn hs
    have hu1 : u ∈ (⊥ : Subgroup X) := h0 ▸ Subgroup.mem_zpowers u
    rw [Subgroup.mem_bot] at hu1
    rw [hu1, orderOf_one] at hu
    exact absurd hu (by norm_num)
  have hodd := Simple.odd_card_zHull_inf S h44 hAn hz hzM hzA hHtop hH hzH
  have hzL : z ∈ zHull Z H := Subgroup.subset_closure ⟨hz, hzH⟩
  have hLH : zHull Z H ≤ H := (Subgroup.closure_le _).mpr Set.inter_subset_right
  have hHL : H ≤ normalizer (zHull Z H : Set X) := le_normalizer_zHull S.invariant H
  have hHN : H ≤ normalizer ((zHull Z H ⊓ A : Subgroup X) : Set X) := fun h hh =>
    mem_normalizer_inf (hHL hh) (Simple.le_normalizer_of_normal hAn ⊤ (Subgroup.mem_top h))
  have hLAH : zHull Z H ⊓ A ≤ H := inf_le_left.trans hLH
  have hne : (Z ∩ ((H ⊓ M : Subgroup X) : Set X)).Nonempty :=
    ⟨z, hz, Subgroup.mem_inf.mpr ⟨hzH, hzM⟩⟩
  refine ⟨⟨hzH, zHull Z H ⊓ A, hLAH,
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLAH).mpr hHN, hodd, fun m hm => ?_⟩, ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨?_, Simple.commutator_mem_of_sup_zpowers_eq_top hAn hz2 hAz m⟩
    exact (zHull Z H).mul_mem (((Subgroup.mem_normalizer_iff.mp (hHL hm)) z).mp hzL)
      ((zHull Z H).inv_mem hzL)
  · intro hP
    have hLAle : zHull Z H ⊓ A ≤ pPrimeCoreIn H := le_pPrimeCoreIn hLAH hHN hodd
    have hLM : zHull Z H ≤ M := by
      intro l hl
      rcases Simple.mem_or_mul_mem_of_sup_zpowers_eq_top hAn hz2 hAz l with h1 | h1
      · exact hP (hLAle (Subgroup.mem_inf.mpr ⟨hl, h1⟩))
      · have h2 : l * z ∈ M :=
          hP (hLAle (Subgroup.mem_inf.mpr ⟨(zHull Z H).mul_mem hl hzL, h1⟩))
        have := M.mul_mem h2 (M.inv_mem hzM)
        simpa using this
    exact S.not_zHull_le hH hne hLM
  · rintro ⟨-, P, -, hcommP⟩
    have hPH : (P : Subgroup X) ≤ H := fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcommP s hs)
    obtain ⟨y, hy, hyne, hyz⟩ := S.exists_commuting_ne hz
    have hy2 : y * y = 1 := S.invariant.mul_self_eq_one hy
    have hz1 : z ≠ 1 := fun h => by
      have := S.invariant.1 z hz
      rw [h, orderOf_one] at this
      exact absurd this (by norm_num)
    have hy1 : y ≠ 1 := fun h => by
      have := S.invariant.1 y hy
      rw [h, orderOf_one] at this
      exact absurd this (by norm_num)
    obtain ⟨g, hgz, hgy⟩ := Simple.exists_conj_mem_sylow_of_commute hz2 hy2 hyz.symm hz1 hy1 hyne.symm P
    have hgzZ : g * z * g⁻¹ ∈ Z := by
      have := S.invariant.2 z hz g⁻¹
      rwa [inv_inv] at this
    have hgyZ : g * y * g⁻¹ ∈ Z := by
      have := S.invariant.2 y hy g⁻¹
      rwa [inv_inv] at this
    have h1 := Simple.mul_inv_mem_zHull_inf S hAn hz hzM hAz hH hzH hgzZ (hPH hgz)
    have h2 := Simple.mul_inv_mem_zHull_inf S hAn hz hzM hAz hH hzH hgyZ (hPH hgy)
    have h3 : (g * z * g⁻¹) * (g * y * g⁻¹)⁻¹ ∈ zHull Z H ⊓ A := by
      have := (zHull Z H ⊓ A).mul_mem h1 ((zHull Z H ⊓ A).inv_mem h2)
      simpa [mul_assoc] using this
    have h4 : (g * z * g⁻¹) * (g * y * g⁻¹)⁻¹ ∈ (P : Subgroup X) :=
      (P : Subgroup X).mul_mem hgz ((P : Subgroup X).inv_mem hgy)
    have h5 := Simple.eq_one_of_mem_odd_of_mem_isPGroup hodd P.isPGroup' h3 h4
    apply hyne
    have h6 : g * z * g⁻¹ = g * y * g⁻¹ := mul_inv_eq_one.mp h5
    have := mul_left_cancel (mul_right_cancel h6)
    exact this.symm

theorem ZDSetup.isSimpleGroup (S : ZDSetup X Z M)
    (h45 : ∀ N : Subgroup X, N.Normal → Group.IsSolvable ↥N → N = ⊥)
    (h44 : ∀ H : Subgroup X, H ≠ ⊤ → ¬ H ≤ M → (Z ∩ ((H ⊓ M : Subgroup X) : Set X)).Nonempty →
      IsStronglyEmbedded ((M ⊓ zHull Z H).subgroupOf (zHull Z H))) : IsSimpleGroup X := by
  by_contra hX
  obtain ⟨z, hz, hzM⟩ := S.exists_mem_inter
  obtain ⟨A, hAn, -, -, hAe, hzA, hAz, -⟩ := S.lemma49 h45 h44 hX hz hzM
  have hz2 : z * z = 1 := S.invariant.mul_self_eq_one hz
  have hz1 : z ≠ 1 := fun h => by
    have := S.invariant.1 z hz
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hnotSE : ¬ IsStronglyEmbedded M := by
    intro hSE
    obtain ⟨y, hyA, hy2⟩ := Simple.exists_mem_orderOf_eq_two_of_even_card hAe
    obtain ⟨g, hg⟩ := Simple.exists_conj_of_isStronglyEmbedded hSE (S.invariant.1 z hz) hy2
    apply hzA
    have : z = g * y * g⁻¹ := by rw [← hg]; group
    rw [this]
    exact hAn.conj_mem y hyA g
  obtain ⟨T, hTM, hzT, hTcomm⟩ := S.exists_sylow_central hz hzM
  have hclaim : ∃ u ∈ (T : Subgroup X), orderOf u = 2 ∧ ¬ centralizer ({u} : Set X) ≤ M := by
    by_contra hno
    push Not at hno
    apply hnotSE
    refine ⟨S.prodDisc.ne_top, Simple.even_card_of_mem_orderOf_eq_two hzM (S.invariant.1 z hz),
      fun g hg => ?_⟩
    apply Simple.odd_card_of_forall_orderOf_ne_two
    intro t ht ht2
    obtain ⟨htM, htg⟩ := Subgroup.mem_inf.mp ht
    rw [mem_conjugate_iff] at htg
    have ht2' : IsPGroup 2 (zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
    have hCt : centralizer ({t} : Set X) ≤ M := by
      obtain ⟨h, hhM, hhT⟩ := exists_mem_conj_mem_sylow hTM htM ht2'
      have hord : orderOf (h⁻¹ * t * h) = 2 := by
        have := orderOf_injective (MulAut.conj h⁻¹).toMonoidHom (MulAut.conj h⁻¹).injective t
        simpa [MulAut.conj_apply, ht2] using this
      have hC' := hno (h⁻¹ * t * h) hhT hord
      intro c hc
      have hc' : h⁻¹ * c * h ∈ centralizer ({h⁻¹ * t * h} : Set X) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
        calc h⁻¹ * c * h * (h⁻¹ * t * h) = h⁻¹ * (c * t) * h := by group
          _ = h⁻¹ * (t * c) * h := by rw [hc]
          _ = h⁻¹ * t * h * (h⁻¹ * c * h) := by group
      have h1 := hC' hc'
      have e : c = h * (h⁻¹ * c * h) * h⁻¹ := by group
      rw [e]
      exact M.mul_mem (M.mul_mem hhM h1) (M.inv_mem hhM)
    obtain ⟨m, hmM, hm⟩ := S.exists_mem_conj_of_isPGroup htM ht2' (g := g⁻¹)
      (by rwa [inv_inv])
    rw [inv_inv] at hm
    have hmg : m * g ∈ centralizer ({t} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc m * g * t = m * (g * t * g⁻¹) * g := by group
        _ = m * (m⁻¹ * t * m) * g := by rw [hm]
        _ = t * (m * g) := by group
    apply hg
    have := M.mul_mem (M.inv_mem hmM) (hCt hmg)
    simpa using this
  obtain ⟨u, huT, hu2, huH⟩ := hclaim
  have huz : u * z = z * u := hTcomm u huT
  have hYM : ¬ pPrimeCoreIn (centralizer ({u} : Set X)) ≤ M :=
    (S.lemma410 h45 h44 hAn hz hzM hzA hAz hu2 huz huH).2.1
  obtain ⟨c, hcA, hcT, hc2, hcT'⟩ := Simple.exists_involution_normal_inf_center hAn hAe T
  have hc2' : c * c = 1 := by
    have := pow_orderOf_eq_one c
    rwa [hc2, pow_two] at this
  have hc1 : c ≠ 1 := fun h => by
    rw [h, orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  have hzc : z * c = c * z := hcT' z hzT
  have hczne : z ≠ c := fun h => hzA (h ▸ hcA)
  have hVcard : Nat.card (CFSG.LocalAnalysis.ComponentInitial.FourGroup.kleinFourOf z c hz2 hc2' hzc)
      = 2 ^ 2 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.FourGroup.card_kleinFourOf hz1 hc1 hczne]
    norm_num
  have hcz : c * z = z * c := hzc.symm
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hcent_of_central : ∀ v ∈ (T : Subgroup X), (∀ s ∈ (T : Subgroup X), s * v = v * s) →
      orderOf v = 2 → v * z = z * v → centralizer ({v} : Set X) ≤ M := by
    intro v hvT hvcomm hv2 hvz
    by_contra hvM
    exact (S.lemma410 h45 h44 hAn hz hzM hzA hAz hv2 hvz hvM).2.2 ⟨hv2, T, hvT, hvcomm⟩
  have hzC : centralizer ({z} : Set X) ≤ M := S.prodDisc.centralizer_le_of_mem hz hzM
  have hcC : centralizer ({c} : Set X) ≤ M := hcent_of_central c hcT hcT' hc2 hcz
  have hzcT : z * c ∈ (T : Subgroup X) := (T : Subgroup X).mul_mem hzT hcT
  have hzc22 : (z * c) * (z * c) = 1 := by
    calc (z * c) * (z * c) = z * (c * z) * c := by group
      _ = z * (z * c) * c := by rw [hcz]
      _ = (z * z) * (c * c) := by group
      _ = 1 := by rw [hz2, hc2', one_mul]
  have hzc2 : orderOf (z * c) = 2 := by
    refine orderOf_eq_prime (by rw [pow_two]; exact hzc22) ?_
    intro h1
    apply hczne
    have := eq_inv_of_mul_eq_one_right h1
    rw [this, hzi]
  have hzcC : centralizer ({z * c} : Set X) ≤ M := by
    refine hcent_of_central (z * c) hzcT (fun s hs => ?_) hzc2 ?_
    · calc s * (z * c) = (s * z) * c := by group
        _ = (z * s) * c := by rw [hTcomm s hs]
        _ = z * (s * c) := by group
        _ = z * (c * s) := by rw [hcT' s hs]
        _ = (z * c) * s := by group
    · calc z * c * z = z * (c * z) := by group
        _ = z * (z * c) := by rw [hcz]
  set V := CFSG.LocalAnalysis.ComponentInitial.FourGroup.kleinFourOf z c hz2 hc2' hzc with hV
  have hzH : z ∈ centralizer ({u} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr huz.symm
  have hcH : c ∈ centralizer ({u} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcT' u huT).symm
  have hVH : V ≤ centralizer ({u} : Set X) :=
    CFSG.LocalAnalysis.ComponentInitial.FourGroup.kleinFourOf_le hzH hcH
  have hVN : V ≤ normalizer (pPrimeCoreIn (centralizer ({u} : Set X)) : Set X) := fun v hv =>
    pPrimeCoreIn_normalizes _ (hVH hv)
  have hVsq : ∀ v ∈ V, v * v = 1 := by
    intro v hv
    rcases CFSG.LocalAnalysis.ComponentInitial.FourGroup.mem_kleinFourOf.mp hv with
      h | h | h | h <;> rw [h]
    · exact one_mul 1
    · exact hz2
    · exact hc2'
    · exact hzc22
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two V (pPrimeCoreIn (centralizer ({u} : Set X)))
    (fun m => Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]; exact hVsq m m.2))
    hVcard
    (fun h2 => (Nat.not_even_iff_odd.mpr (odd_card_pPrimeCoreIn _)) (even_iff_two_dvd.mpr h2)) hVN
  apply hYM
  conv_lhs => rw [hgen]
  refine iSup₂_le fun v hv1 => inf_le_right.trans ?_
  rcases CFSG.LocalAnalysis.ComponentInitial.FourGroup.mem_kleinFourOf.mp v.2 with
    h | h | h | h
  · exact absurd (Subtype.ext h) hv1
  · rw [h]
    exact hzC
  · rw [h]
    exact hcC
  · rw [h]
    exact hzcC

end Main

end CFSG.GH74.Uniqueness
