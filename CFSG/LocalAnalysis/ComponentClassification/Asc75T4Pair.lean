module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Layer
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Basic

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

@[expose] def HasFourGroup (X : Subgroup G) : Prop :=
  ∃ E : Subgroup G, E ≤ X ∧ (∀ e ∈ E, e ^ 2 = 1) ∧ Nat.card E = 4

omit [Finite G] in
theorem HasFourGroup.mono {X Y : Subgroup G} (h : HasFourGroup X) (hXY : X ≤ Y) :
    HasFourGroup Y := by
  obtain ⟨E, hEX, hE, hE4⟩ := h
  exact ⟨E, hEX.trans hXY, hE, hE4⟩

omit [Finite G] in
theorem HasFourGroup.even_card {X : Subgroup G} (h : HasFourGroup X) : Even (Nat.card X) := by
  obtain ⟨E, hEX, -, hE4⟩ := h
  exact even_iff_two_dvd.mpr ((show 2 ∣ Nat.card E by rw [hE4]; norm_num).trans
    (card_dvd_of_le hEX))

omit [Finite G] in
theorem isPGroup_of_sq_eq_one {E : Subgroup G} (hE : ∀ e ∈ E, e ^ 2 = 1) : IsPGroup 2 E :=
  fun e => ⟨1, Subtype.ext (by simpa using hE e e.2)⟩

theorem hasFourGroup_of_one_lt_pRank {X : Subgroup G} (h : 1 < CFSG.Open.pRank 2 X) :
    HasFourGroup X := by
  obtain ⟨E, hEX, hE, hcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two X
  have hdiv : 2 ^ 2 ∣ Nat.card E := by
    rw [hcard]
    exact Nat.pow_dvd_pow 2 h
  obtain ⟨F, hFcard, -, hFE⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (H := (⊥ : Subgroup G)) (L := E) (by simp) hdiv bot_le
  exact ⟨F, hFE.trans hEX, fun e he => hE.2 e (hFE he), by simpa using hFcard⟩

@[expose] def CaseIPair (B A : Subgroup G) : Prop :=
  HasFourGroup (A ⊓ normalizer (B : Set G)) → twoPrimeLayerIn B ≤ normalizer (A : Set G)

omit [Finite G] in
theorem mem_of_two_element_of_le_sup {B Y O : Subgroup G} (hYB : Y ≤ B) (hO : Odd (Nat.card O))
    (hYO : Y ≤ normalizer (O : Set G)) (hOB : O ≤ normalizer (B : Set G)) {x : G}
    (hx : x ∈ Y ⊔ O) {k : ℕ} (hxk : x ^ (2 ^ k) = 1) : x ∈ B := by
  set V := Y ⊔ O with hV
  have hVB : V ≤ normalizer (B : Set G) := sup_le (hYB.trans le_normalizer) hOB
  set W : Subgroup V := B.subgroupOf V with hW
  have hWn : W.Normal := ⟨fun n hn g => by
    rw [hW, mem_subgroupOf] at hn ⊢
    simpa using (mem_normalizer_iff.mp (hVB g.2) n).mp hn⟩
  have hOV : O ≤ V := le_sup_right
  have hsurj : Function.Surjective ((QuotientGroup.mk' W).comp (O.subgroupOf V).subtype) := by
    intro z
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective W z
    have hv : (v : G) ∈ (Y : Set G) * O := by
      rw [← coe_mul_of_left_le_normalizer_right Y O hYO]
      exact v.2
    obtain ⟨y, hy, o, ho, hyo⟩ := Set.mem_mul.mp hv
    have hyV : y ∈ V := mem_sup_left hy
    have hveq : v = ⟨y, hyV⟩ * ⟨o, hOV ho⟩ := Subtype.ext hyo.symm
    have hy1 : QuotientGroup.mk' W ⟨y, hyV⟩ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hYB hy
    refine ⟨⟨⟨o, hOV ho⟩, mem_subgroupOf.mpr ho⟩, ?_⟩
    rw [hveq, map_mul, hy1, one_mul]
    rfl
  have hodd : Odd (Nat.card (V ⧸ W)) := by
    have h1 := Subgroup.card_dvd_of_surjective hsurj
    rw [Nat.card_congr (subgroupOfEquivOfLe hOV).toEquiv] at h1
    exact hO.of_dvd_nat h1
  have hpow : (⟨x, hx⟩ : V) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hxk)
  have h1 : orderOf (QuotientGroup.mk' W ⟨x, hx⟩) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hpow, map_one])
  have h2 : orderOf (QuotientGroup.mk' W ⟨x, hx⟩) ∣ Nat.card (V ⧸ W) := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (V ⧸ W)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem exists_sylow_le_normalizer {U V : Subgroup G} (hU : IsPGroup 2 U)
    (hUV : U ≤ normalizer (V : Set G)) :
    ∃ P : Subgroup G, P ≤ V ∧ IsPGroup 2 P ∧ (Even (Nat.card V) → Even (Nat.card P)) ∧
      U ≤ normalizer (P : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : U →* MulAut V := V.normalizerMonoidHom.comp (Subgroup.inclusion hUV)
  let _ : MulDistribMulAction U V := MulDistribMulAction.compHom V φ
  let _ : MulAction U (Sylow 2 V) := Sylow.pointwiseMulAction
  have hcard : ¬ 2 ∣ Nat.card (Sylow 2 V) := by
    intro h
    have h1 := card_sylow_modEq_one 2 V
    have h2 : Nat.card (Sylow 2 V) ≡ 0 [MOD 2] := Nat.modEq_zero_iff_dvd.mpr h
    have h3 : 1 ≡ 0 [MOD 2] := h1.symm.trans h2
    exact absurd h3 (by decide)
  obtain ⟨P₀, hP₀⟩ := hU.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 V) hcard
  refine ⟨(P₀ : Subgroup V).map V.subtype, map_subtype_le _, P₀.isPGroup'.map _,
    fun hV => ?_, ?_⟩
  · rw [card_map_of_injective V.subtype_injective]
    have h1 : 2 ^ 1 ∣ Nat.card (P₀ : Subgroup V) :=
      P₀.pow_dvd_card_of_pow_dvd_card (by simpa using even_iff_two_dvd.mp hV)
    exact even_iff_two_dvd.mpr (by simpa using h1)
  have key : ∀ u ∈ U, ∀ z ∈ (P₀ : Subgroup V).map V.subtype,
      u * z * u⁻¹ ∈ (P₀ : Subgroup V).map V.subtype := by
    intro u hu z hz
    obtain ⟨z', hz', rfl⟩ := hz
    have h1 : (⟨u, hu⟩ : U) • P₀ = P₀ := hP₀ ⟨u, hu⟩
    have h2 : (⟨u, hu⟩ : U) • (P₀ : Subgroup V) = P₀ := by
      rw [← Sylow.pointwise_smul_def, h1]
    have h3 : (⟨u, hu⟩ : U) • z' ∈ (P₀ : Subgroup V) := by
      rw [← h2]
      exact Subgroup.smul_mem_pointwise_smul z' _ _ hz'
    exact ⟨_, h3, rfl⟩
  intro u hu
  rw [mem_normalizer_iff]
  intro y
  constructor
  · exact key u hu y
  · intro hy
    have h1 := key u⁻¹ (U.inv_mem hu) _ hy
    have e : u⁻¹ * (u * y * u⁻¹) * u⁻¹⁻¹ = y := by group
    rwa [e] at h1

theorem le_normalizer_of_le_normalizer_sup {B Y O U : Subgroup G} (htight : TightlyEmbedded B)
    (hYB : Y ≤ B) (hY : Even (Nat.card Y)) (hO : Odd (Nat.card O))
    (hYO : Y ≤ normalizer (O : Set G)) (hOB : O ≤ normalizer (B : Set G)) (hU : IsPGroup 2 U)
    (hUV : U ≤ normalizer ((Y ⊔ O : Subgroup G) : Set G)) : U ≤ normalizer (B : Set G) := by
  obtain ⟨P, hPV, hP, hPeven, hUP⟩ := exists_sylow_le_normalizer hU hUV
  have hPB : P ≤ B := fun p hp => by
    obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
    exact mem_of_two_element_of_le_sup hYB hO hYO hOB (hPV hp) (k := k)
      (by simpa using congrArg Subtype.val hk)
  have hVeven : Even (Nat.card (Y ⊔ O : Subgroup G)) := by
    obtain ⟨m, hm⟩ := even_iff_two_dvd.mp hY
    exact even_iff_two_dvd.mpr ((dvd_mul_right 2 m).trans (hm ▸ card_dvd_of_le le_sup_left))
  exact hUP.trans (normalizer_le_of_even htight hPB (hPeven hVeven))

theorem oddCoreIn_le_normalizer {B M Y : Subgroup G} (htight : TightlyEmbedded B)
    (hYB : Y ≤ B) (hYM : Y ≤ M) (hY : HasFourGroup Y) :
    oddCoreIn M ≤ normalizer (B : Set G) := by
  obtain ⟨E, hEY, hE, hE4⟩ := hY
  exact le_normalizer_of_fourGroup htight (hEY.trans hYB) hE hE4 (odd_card_oddCoreIn M)
    ((hEY.trans hYM).trans (normalIn_le_normalizer (oddCoreIn_normalIn M)))

theorem le_normalizer_sup_oddCoreIn {M U Y : Subgroup G} (hUM : U ≤ M)
    (hc : ∀ u ∈ U, ∀ y ∈ Y, u * y * u⁻¹ * y⁻¹ ∈ oddCoreIn M) :
    U ≤ normalizer ((Y ⊔ oddCoreIn M : Subgroup G) : Set G) := by
  intro u hu
  set V := Y ⊔ oddCoreIn M
  have hle : V.map (MulAut.conj u).toMonoidHom ≤ V := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      have h : (MulAut.conj u).toMonoidHom y = (u * y * u⁻¹ * y⁻¹) * y := by
        simp [mul_assoc]
      rw [h]
      exact mul_mem (mem_sup_right (hc u hu y hy)) (mem_sup_left hy)
    · rintro _ ⟨o, ho, rfl⟩
      refine mem_sup_right ?_
      have := normalIn_le_normalizer (oddCoreIn_normalIn M) (hUM hu)
      simpa using (mem_normalizer_iff.mp this o).mp ho
  have heq : V.map (MulAut.conj u).toMonoidHom = V :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj u).injective])
  exact mem_normalizer_iff_map_conj_eq.mpr heq

section Image

variable (M : Subgroup G)

@[expose] def quotImage (X : Subgroup G) : Subgroup (M ⧸ CFSG.Assembly.oddCore M) :=
  (X.subgroupOf M).map (QuotientGroup.mk' (CFSG.Assembly.oddCore M))

variable {M}

theorem isSubnormal_quotImage {X : Subgroup G} (hX : NormalIn X (twoPrimeLayerIn M)) :
    (quotImage M X).IsSubnormal := by
  set L := twoPrimeLayerIn M
  have hLM : L ≤ M := twoPrimeLayerIn_le M
  have hXM : X ≤ M := hX.1.trans hLM
  have hsub : (X.subgroupOf M).IsSubnormal := by
    refine IsSubnormal.step _ (L.subgroupOf M) (subgroupOf_mono M hX.1)
      ((twoPrimeLayerIn_normalIn M).2.isSubnormal) ?_
    rw [normal_subgroupOf_iff_le_normalizer (subgroupOf_mono M hX.1),
      ← subgroupOf_normalizer_eq hXM]
    exact subgroupOf_mono M (normalIn_le_normalizer hX)
  exact hsub.map (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem isSubnormal_quotImage_of_subgroupOf {X : Subgroup G} (h : (X.subgroupOf M).IsSubnormal) :
    (quotImage M X).IsSubnormal :=
  h.map (QuotientGroup.mk'_surjective _)

theorem layer_quotImage_eq_top {X : Subgroup G} (hX : NormalIn X (twoPrimeLayerIn M))
    (hs : IsSemisimpleQ X) : CFSG.layer (quotImage M X) = ⊤ := by
  have hinf : X ⊓ oddCoreIn M = oddCoreIn X := by
    rw [← oddCoreIn_twoPrimeLayerIn M]
    exact inf_oddCoreIn_eq hX
  exact layer_map_mk_eq_top (hX.1.trans (twoPrimeLayerIn_le M)) hinf hs

omit [Finite G] in
theorem mem_sup_oddCoreIn_of_mk_mem {X : Subgroup G} {m : M}
    (hm : QuotientGroup.mk' (CFSG.Assembly.oddCore M) m ∈ quotImage M X) :
    (m : G) ∈ X ⊔ oddCoreIn M := by
  obtain ⟨x, hx, hxm⟩ := hm
  have h1 : x⁻¹ * m ∈ CFSG.Assembly.oddCore M := by
    rw [← QuotientGroup.eq]
    exact hxm
  have h2 : (m : G) = (x : G) * ((x⁻¹ * m : M) : G) := by
    simp
  rw [h2]
  exact mul_mem (mem_sup_left hx) (mem_sup_right ⟨_, h1, rfl⟩)

omit [Finite G] in
theorem commutator_mem_oddCoreIn {X Y : Subgroup G} (hXM : X ≤ M) (hYM : Y ≤ M)
    (h : ⁅quotImage M X, quotImage M Y⁆ = ⊥) :
    ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ oddCoreIn M := by
  intro x hx y hy
  set π := QuotientGroup.mk' (CFSG.Assembly.oddCore M)
  have hc := commutator_eq_bot_iff_le_centralizer.mp h
    (show π ⟨x, hXM hx⟩ ∈ quotImage M X from ⟨⟨x, hXM hx⟩, hx, rfl⟩)
  have hxy : π ⟨y, hYM hy⟩ * π ⟨x, hXM hx⟩ = π ⟨x, hXM hx⟩ * π ⟨y, hYM hy⟩ :=
    mem_centralizer_iff.mp hc _ ⟨⟨y, hYM hy⟩, hy, rfl⟩
  have h1 : π (⟨x, hXM hx⟩ * ⟨y, hYM hy⟩ * ⟨x, hXM hx⟩⁻¹ * ⟨y, hYM hy⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hxy]
    group
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨_, h1, rfl⟩

theorem exists_involution_mk_mem {C : Subgroup (M ⧸ CFSG.Assembly.oddCore M)}
    (hC : Even (Nat.card C)) :
    ∃ m : M, orderOf m = 2 ∧ QuotientGroup.mk' (CFSG.Assembly.oddCore M) m ∈ C := by
  set π := QuotientGroup.mk' (CFSG.Assembly.oddCore M)
  have h2 : 2 ∣ Nat.card (C.comap π) :=
    (even_iff_two_dvd.mp hC).trans (Subgroup.card_dvd_of_surjective
      (π.subgroupComap_surjective C (QuotientGroup.mk'_surjective _)))
  obtain ⟨⟨m, hm⟩, hm2⟩ := exists_prime_orderOf_dvd_card' (G := C.comap π) 2 h2
  exact ⟨m, by rwa [Subgroup.orderOf_mk] at hm2, hm⟩

end Image

theorem even_card_of_isComponent {A : Type*} [Group A] [Finite A] {C : Subgroup A}
    (hC : CFSG.IsComponent C) : Even (Nat.card C) := by
  by_contra hodd
  have hs : Group.IsSolvable C := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp hodd)
  have : Nontrivial C := CFSG.LocalCores.isQuasisimple_nontrivial hC.1
  have : Group.IsPerfect C := hC.1.1
  exact Group.IsPerfect.not_isSolvable C hs

theorem exists_component_or_commutator_eq_bot {A : Type*} [Group A] [Finite A]
    {M₁ M₂ : Subgroup A} (h₁ : M₁.IsSubnormal) (hs : CFSG.layer M₁ = ⊤) (h₂ : M₂.IsSubnormal) :
    (∃ C : Subgroup A, CFSG.IsComponent C ∧ C ≤ M₁ ⊓ M₂) ∨ ⁅M₁, M₂⁆ = ⊥ := by
  by_cases h : ∃ C : Subgroup A, CFSG.IsComponent C ∧ C ≤ M₁ ⊓ M₂
  · exact Or.inl h
  right
  push Not at h
  have hM₁ : M₁ = (CFSG.layer M₁).map M₁.subtype := by
    rw [hs, ← MonoidHom.range_eq_map, range_subtype]
  rw [hM₁, commutator_eq_bot_iff_le_centralizer, map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← map_le_iff_le_comap]
  have hC : CFSG.IsComponent (L.map M₁.subtype) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (L.equivMapOfInjective M₁.subtype M₁.subtype_injective) hL.1, hL.2.trans' h₁⟩
  rcases CFSG.LocalCores.component_subnormal_subgroup hC h₂ with hle | hcomm
  · exact absurd (le_inf (map_subtype_le _) hle) (h _ hC)
  · exact commutator_eq_bot_iff_le_centralizer.mp hcomm

theorem eq_or_normalizes_of_quotImage {A B M X Y : Subgroup G} (hA : TightlyEmbedded A)
    (hB : TightlyEmbedded B) (hAB : Even (Nat.card (A ⊓ B : Subgroup G)) → A = B)
    (hIAB : CaseIPair A B) (hIBA : CaseIPair B A) (hXA : X ≤ A) (hYB : Y ≤ B) (hXM : X ≤ M)
    (hYM : Y ≤ M) (hXsub : (quotImage M X).IsSubnormal)
    (hXlay : CFSG.layer (quotImage M X) = ⊤) (hYsub : (quotImage M Y).IsSubnormal)
    (hX4 : HasFourGroup X) (hY4 : HasFourGroup Y) :
    A = B ∨ (twoPrimeLayerIn B ≤ normalizer (A : Set G) ∧
      twoPrimeLayerIn A ≤ normalizer (B : Set G)) := by
  have hOodd := odd_card_oddCoreIn M
  have hOn : M ≤ normalizer (oddCoreIn M : Set G) :=
    normalIn_le_normalizer (oddCoreIn_normalIn M)
  have hOA := oddCoreIn_le_normalizer hA hXA hXM hX4
  have hOB := oddCoreIn_le_normalizer hB hYB hYM hY4
  have hXe := hX4.even_card
  have hYe := hY4.even_card
  rcases exists_component_or_commutator_eq_bot hXsub hXlay hYsub with ⟨C, hC, hCle⟩ | hcomm
  ·
    left
    obtain ⟨m, hm2, hmC⟩ := exists_involution_mk_mem (even_card_of_isComponent hC)
    have hm2' : (m : G) ^ 2 ^ 1 = 1 := by
      have h := pow_orderOf_eq_one m
      rw [hm2] at h
      simpa using congrArg Subtype.val h
    have hmA : (m : G) ∈ A := mem_of_two_element_of_le_sup hXA hOodd (hXM.trans hOn) hOA
      (mem_sup_oddCoreIn_of_mk_mem (hCle hmC).1) hm2'
    have hmB : (m : G) ∈ B := mem_of_two_element_of_le_sup hYB hOodd (hYM.trans hOn) hOB
      (mem_sup_oddCoreIn_of_mk_mem (hCle hmC).2) hm2'
    apply hAB
    have hz : Nat.card (zpowers (m : G)) = 2 := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hm2]
    exact even_iff_two_dvd.mpr (hz ▸ card_dvd_of_le ((zpowers_le).mpr ⟨hmA, hmB⟩))
  ·
    right
    obtain ⟨E, hEX, hE, hE4⟩ := hX4
    obtain ⟨F, hFY, hF, hF4⟩ := hY4
    have hEB : E ≤ normalizer (B : Set G) :=
      le_normalizer_of_le_normalizer_sup hB hYB hYe hOodd (hYM.trans hOn) hOB
        (isPGroup_of_sq_eq_one hE)
        (le_normalizer_sup_oddCoreIn (hEX.trans hXM) fun u hu y hy =>
          commutator_mem_oddCoreIn hXM hYM hcomm u (hEX hu) y hy)
    have hFA : F ≤ normalizer (A : Set G) :=
      le_normalizer_of_le_normalizer_sup hA hXA hXe hOodd (hXM.trans hOn) hOA
        (isPGroup_of_sq_eq_one hF)
        (le_normalizer_sup_oddCoreIn (hFY.trans hYM) fun u hu x hx =>
          commutator_mem_oddCoreIn hYM hXM (by rw [commutator_comm]; exact hcomm) u (hFY hu) x hx)
    exact ⟨hIBA ⟨E, le_inf (hEX.trans hXA) hEB, hE, hE4⟩,
      hIAB ⟨F, le_inf (hFY.trans hYB) hFA, hF, hF4⟩⟩

theorem eq_or_normalizes_of_normalIn {A B M X Y : Subgroup G} (hA : TightlyEmbedded A)
    (hB : TightlyEmbedded B) (hAB : Even (Nat.card (A ⊓ B : Subgroup G)) → A = B)
    (hIAB : CaseIPair A B) (hIBA : CaseIPair B A) (hXA : X ≤ A) (hYB : Y ≤ B)
    (hX : NormalIn X (twoPrimeLayerIn M)) (hY : NormalIn Y (twoPrimeLayerIn M))
    (hXs : IsSemisimpleQ X) (hX4 : HasFourGroup X) (hY4 : HasFourGroup Y) :
    A = B ∨ (twoPrimeLayerIn B ≤ normalizer (A : Set G) ∧
      twoPrimeLayerIn A ≤ normalizer (B : Set G)) :=
  eq_or_normalizes_of_quotImage hA hB hAB hIAB hIBA hXA hYB
    (hX.1.trans (twoPrimeLayerIn_le M)) (hY.1.trans (twoPrimeLayerIn_le M))
    (isSubnormal_quotImage hX) (layer_quotImage_eq_top hX hXs) (isSubnormal_quotImage hY) hX4 hY4

end CFSG.ComponentClassification.Asc75T4
