module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212Steps
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_not_mem {P A : Subgroup G} (hP : IsPGroup 2 P) (hAP : A ≤ P)
    (hne : A ≠ P) : ∃ x ∈ P, x ∈ normalizer (A : Set G) ∧ x ∉ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥P)
  set A' := A.subgroupOf P with hA'
  have hlt : A' < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne (le_antisymm hAP fun x hx => ?_)
    have : (⟨x, hx⟩ : ↥P) ∈ A' := h ▸ mem_top _
    exact mem_subgroupOf.mp this
  obtain ⟨x, hxN, hxA⟩ := IsConcreteLE.exists_of_lt (hnc A' hlt)
  refine ⟨x, x.2, ?_, fun h => hxA (mem_subgroupOf.mpr h)⟩
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have := (mem_normalizer_iff.mp hxN ⟨g, hAP hg⟩).mp (mem_subgroupOf.mpr hg)
    exact mem_subgroupOf.mp this
  · intro hg
    have hgP : g ∈ P := by
      set x' : G := (x : G) with hx'
      have h1 : x' * g * x'⁻¹ ∈ P := hAP hg
      have : g = x'⁻¹ * (x' * g * x'⁻¹) * x' := by group
      rw [this]
      exact mul_mem (mul_mem (inv_mem x.2) h1) x.2
    have := (mem_normalizer_iff.mp hxN ⟨g, hgP⟩).mpr (mem_subgroupOf.mpr hg)
    exact mem_subgroupOf.mp this

theorem exists_sq_mem_of_ne {P A : Subgroup G} (hP : IsPGroup 2 P) (hAP : A ≤ P) (hne : A ≠ P) :
    ∃ s ∈ P, s ∈ normalizer (A : Set G) ∧ s ∉ A ∧ s ^ 2 ∈ A := by
  classical
  obtain ⟨x, hxP, hxN, hxA⟩ := exists_mem_normalizer_not_mem hP hAP hne
  obtain ⟨n, hn⟩ := hP ⟨x, hxP⟩
  have hex : ∃ k : ℕ, x ^ (2 ^ k) ∈ A := by
    refine ⟨n, ?_⟩
    have h1 := congrArg Subtype.val hn
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at h1
    rw [h1]
    exact one_mem A
  have hk := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h, pow_zero, pow_one] at hk
    exact hxA hk
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  refine ⟨x ^ (2 ^ m), pow_mem hxP _, pow_mem hxN _, fun h => ?_, ?_⟩
  · exact Nat.find_min hex (show m < Nat.find hex by omega) h
  · rw [← pow_mul, show 2 ^ m * 2 = 2 ^ Nat.find hex by rw [hm, pow_succ]]
    exact hk

theorem twoLayer_le_of_le_of_isPGroup {L T P : Subgroup G} (hL : L ∈ solomonKStar G)
    (hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L)) (hP : IsPGroup 2 P)
    (hPQ : P ≤ coreActionKernel L) (hT : T ≠ ⊥) :
    ∀ A : Subgroup G, T ≤ A → A ≤ P →
      twoLayerIn (L ⊓ centralizer (A : Set G)) ≤ twoLayerIn (centralizer (A : Set G)) →
      twoLayerIn (L ⊓ centralizer (P : Set G)) ≤ twoLayerIn (centralizer (P : Set G)) := by
  suffices key : ∀ n : ℕ, ∀ A : Subgroup G, Nat.card P - Nat.card A = n → T ≤ A → A ≤ P →
      twoLayerIn (L ⊓ centralizer (A : Set G)) ≤ twoLayerIn (centralizer (A : Set G)) →
      twoLayerIn (L ⊓ centralizer (P : Set G)) ≤ twoLayerIn (centralizer (P : Set G)) from
    fun A => key _ A rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hn hTA hAP hA
    by_cases hAP' : A = P
    · rw [← hAP']; exact hA
    obtain ⟨s, hsP, hsN, hsA, hs2⟩ := exists_sq_mem_of_ne hP hAP hAP'
    set A' := A ⊔ zpowers s with hA'
    have hA'P : A' ≤ P := sup_le hAP (zpowers_le.mpr hsP)
    have hAA' : A < A' := lt_of_le_of_ne le_sup_left fun h =>
      hsA (h ▸ mem_sup_right (mem_zpowers s))
    have hcard : Nat.card A < Nat.card A' := Subgroup.card_lt_of_lt hAA'
    have hcardP : Nat.card A' ≤ Nat.card P := card_le_of_le hA'P
    have hA'star := twoLayer_inf_centralizer_sup_zpowers hL hLq (ne_bot_of_le_ne_bot hT hTA)
      (hP.to_le hAP) (hAP.trans hPQ) (hP.to_le (zpowers_le.mpr hsP)) (hPQ hsP) hsN hs2 hA
    exact ih _ (by omega) A' rfl (hTA.trans le_sup_left) hA'P hA'star

theorem twoLayer_le_of_isPGroup {L P : Subgroup G} (hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L))
    (hP : IsPGroup 2 P) (hPQ : P ≤ coreActionKernel L)
    (hPs : twoLayerIn (L ⊓ centralizer (P : Set G)) ≤ twoLayerIn (centralizer (P : Set G))) :
    ∀ A : Subgroup G, A ≤ P →
      twoLayerIn (L ⊓ centralizer (A : Set G)) ≤ twoLayerIn (centralizer (A : Set G)) := by
  suffices key : ∀ n : ℕ, ∀ A : Subgroup G, Nat.card P - Nat.card A = n → A ≤ P →
      twoLayerIn (L ⊓ centralizer (A : Set G)) ≤ twoLayerIn (centralizer (A : Set G)) from
    fun A => key _ A rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hn hAP
    by_cases hAP' : A = P
    · rw [hAP']; exact hPs
    obtain ⟨x, hxP, hxN, hxA⟩ := exists_mem_normalizer_not_mem hP hAP hAP'
    set N := P ⊓ normalizer (A : Set G) with hN
    have hAN : A ≤ N := le_inf hAP le_normalizer
    have hlt : A < N := lt_of_le_of_ne hAN fun h => hxA (h ▸ mem_inf.mpr ⟨hxP, hxN⟩)
    have hcard : Nat.card A < Nat.card N := Subgroup.card_lt_of_lt hlt
    have hcardP : Nat.card N ≤ Nat.card P := card_le_of_le inf_le_left
    have hNs := ih _ (by omega) N rfl inf_le_left
    exact twoLayer_inf_centralizer_le_of_normalizes hLq (hP.to_le hAP) (hP.to_le inf_le_left)
      hAN inf_le_right (inf_le_left.trans hPQ) hNs

theorem le_normalizer_solomonKStarOf (X : Subgroup G) :
    X ≤ normalizer (solomonKStarOf X : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq]
  have h1 := map_solomonKStarOf (MulAut.conj x) X
  have h2 : X.map (MulAut.conj x).toMonoidHom = X :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer hx)
  rw [h2] at h1
  exact h1

theorem le_solomonKStarOf_of_moved {X J : Subgroup G} (hJX : J ≤ twoLayerIn X) (hJ : ⁅J, J⁆ = J)
    (hmov : ∀ K : Subgroup G, IsTwoComponentIn K X → ¬ J ≤ coreActionKernel K →
      K ∈ solomonKStar G) :
    J ≤ solomonKStarOf X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJX' : J ≤ X := hJX.trans (map_subtype_le _)
  have hJperf : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJ
  set O := pPrimeCore 2 ↥X with hO
  have hOn : O.Normal := pPrimeCore_normal
  have hOcop : Nat.Coprime 2 (Nat.card O) := pPrimeCore_coprime_card (p := 2) (G := ↥X)
  set π := QuotientGroup.mk' O with hπ
  let ρ : ↥J →* ↥X ⧸ O := π.comp (Subgroup.inclusion hJX')
  have hρ : ∀ j : ↥J, ρ j = π ⟨j, hJX' j.2⟩ := fun _ => rfl
  set Jb := ρ.range with hJb
  have hJE : Jb ≤ layer (↥X ⧸ O) := by
    refine le_trans ?_ (LBalance.Quot.map_pLayer_eq_layer_quotient (H := ↥X) (p := 2)).le
    rintro _ ⟨j, rfl⟩
    refine mem_map_of_mem π ?_
    obtain ⟨y, hy, hyj⟩ := hJX j.2
    have : Subgroup.inclusion hJX' j = y := Subtype.ext hyj.symm
    rw [this]
    exact hy
  have hJp : ⁅Jb, Jb⁆ = Jb := Subgroup.isPerfect_iff.mp (Group.IsPerfect.range ρ)
  set D := solomonKStarOf X with hD
  have hDX : D ≤ X := iSup₂_le fun K hK => hK.1.1
  set T := (D.subgroupOf X).map π with hT
  have hfix : ∀ K : Subgroup (↥X ⧸ O), IsComponent K → ¬ Jb ≤ centralizer (K : Set _) →
      K.map (MulAut.conj (1 : ↥X ⧸ O)).toMonoidHom = K → K ≤ T := by
    intro K hK hJK _
    obtain ⟨hK0, hK0map, -, -⟩ := (CatalogueBPrimeJoin.canonical_prime_component_lift
      (X := ↥X) 2).1 K hK
    set K0 := CatalogueBPrimeJoin.canonicalPrimeLift 2 K with hK0def
    set Kt := K0.map X.subtype with hKt
    have hKtX : IsTwoComponentIn Kt X := by
      refine ⟨map_subtype_le _, ?_⟩
      rw [hKt, ← comap_subtype, comap_map_eq_self_of_injective X.subtype_injective]
      exact hK0
    have hmove : ¬ J ≤ coreActionKernel Kt := by
      intro hc
      apply hJK
      rintro _ ⟨j, rfl⟩
      rw [mem_centralizer_iff]
      intro x hx
      rw [SetLike.mem_coe, ← hK0map] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      have h1 := (hc j.2).2 (k : G) (mem_map_of_mem X.subtype hk)
      have h2 := oddCoreIn_le_of_isTwoComponentIn hKtX h1
      obtain ⟨o, ho, hoe⟩ := h2
      have h3 : o = k⁻¹ * ⟨j, hJX' j.2⟩⁻¹ * k * ⟨j, hJX' j.2⟩ :=
        Subtype.ext (by simpa using hoe)
      rw [h3] at ho
      rw [hρ, ← map_mul, ← map_mul]
      refine (QuotientGroup.eq (s := O)).mpr ?_
      have e : (k * ⟨(j : G), hJX' j.2⟩)⁻¹ * (⟨(j : G), hJX' j.2⟩ * k) =
          (k⁻¹ * ⟨(j : G), hJX' j.2⟩⁻¹ * k * ⟨(j : G), hJX' j.2⟩)⁻¹ := by group
      rw [e]
      exact inv_mem ho
    have hKtD : Kt ≤ D := le_iSup₂_of_le Kt ⟨hKtX, hmov Kt hKtX hmove⟩ le_rfl
    rw [← hK0map, hT]
    refine map_mono fun k hk => mem_subgroupOf.mpr (hKtD (mem_map_of_mem X.subtype hk))
  have hTb : Jb ≤ T := by
    refine le_of_pieces hJp hJE (fun _ _ => Commute.one_left _) (fun x _ => by simp)
      (fun x _ => mem_centralizer_singleton_iff.mpr (by simp)) hfix ?_
    intro K _ _ hK1
    exfalso
    apply hK1
    have : (MulAut.conj (1 : ↥X ⧸ O)).toMonoidHom = MonoidHom.id _ := by
      ext x; simp
    rw [this, map_id]
  have hDn : (D.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hDX).mpr (le_normalizer_solomonKStarOf X)
  set J2 := J.subgroupOf X with hJ2
  have hJ2sup : J2 ≤ D.subgroupOf X ⊔ O := by
    intro x hx
    have h1 : π x ∈ T := hTb ⟨⟨x, mem_subgroupOf.mp hx⟩, rfl⟩
    rw [hT, ← mem_comap, comap_map_eq, QuotientGroup.ker_mk'] at h1
    exact h1
  have hJ2res : CatalogueBPrimeJoin.primeResidual 2 ↥J2 = ⊤ := by
    have : Group.IsPerfect ↥J2 :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hJX').symm.toMonoidHom)
        (subgroupOfEquivOfLe hJX').symm.surjective
    exact primeResidual_two_eq_top this
  have hJ2D : J2 ≤ D.subgroupOf X := by
    have h1 := LBalance.Quot.range_le_of_range_le_sup hJ2res hOcop J2.subtype
      (by rw [range_subtype]; exact hJ2sup)
    rwa [range_subtype] at h1
  calc J = J2.map X.subtype := (map_subgroupOf_eq_of_le hJX').symm
    _ ≤ (D.subgroupOf X).map X.subtype := map_mono hJ2D
    _ = D := map_subgroupOf_eq_of_le hDX

theorem lemma212Input : Lemma212Input := by
  intro G _ _ L S hL hS hS2 hSQ
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLq := isQuasisimple_coreQuot_of_isSolomonMember hL.1.1
  obtain ⟨hLp, T, hT, hT2, hTQ, hK0⟩ := hL.1.1
  set Q := coreActionKernel L with hQ
  have hstarT := twoLayer_inf_centralizer_le_of_witness hLq hT2 hTQ hK0
  have hT2' : IsPGroup 2 ↥(T.subgroupOf Q) := hT2.comap_subtype
  have hS2' : IsPGroup 2 ↥(S.subgroupOf Q) := hS2.comap_subtype
  obtain ⟨P₁, hTP₁⟩ := hT2'.exists_le_sylow
  obtain ⟨P₂, hSP₂⟩ := hS2'.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq ↥Q P₁ P₂
  set P := (P₂ : Subgroup ↥Q).map Q.subtype with hP
  have hP2 : IsPGroup 2 P := P₂.isPGroup'.map Q.subtype
  have hPQ : P ≤ Q := map_subtype_le _
  have hSP : S ≤ P := by
    intro x hx
    exact ⟨⟨x, hSQ hx⟩, hSP₂ (mem_subgroupOf.mpr hx), rfl⟩
  set Ty := T.map (MulAut.conj (y : G)).toMonoidHom with hTy
  have hTyP : Ty ≤ P := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 : (⟨t, hTQ ht⟩ : ↥Q) ∈ (P₁ : Subgroup ↥Q) := hTP₁ (mem_subgroupOf.mpr ht)
    have h2 := Subgroup.smul_mem_pointwise_smul (⟨t, hTQ ht⟩ : ↥Q) (MulAut.conj y)
      (P₁ : Subgroup ↥Q) h1
    rw [← Sylow.coe_subgroup_smul, hy] at h2
    refine ⟨_, h2, ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply]
  have hTy : Ty ≠ ⊥ := by
    intro h
    apply hT
    rw [eq_bot_iff]
    intro t ht
    have h1 : (MulAut.conj (y : G)) t ∈ Ty := mem_map_of_mem _ ht
    rw [h, mem_bot] at h1
    exact (mem_bot).mpr ((MulAut.conj (y : G)).map_eq_one_iff.mp h1)
  have hyN : (y : G) ∈ normalizer (L : Set G) := (mem_coreActionKernel.mp y.2).1
  have hstarTy := twoLayer_inf_centralizer_le_map_conj hyN hstarT
  have hstarP := twoLayer_le_of_le_of_isPGroup hL hLq hP2 hPQ hTy Ty le_rfl hTyP hstarTy
  have hstarS := twoLayer_le_of_isPGroup hLq hP2 hPQ hstarP S hSP
  obtain ⟨hJc, hLS, -, -⟩ := cover_facts hLq inf_le_left
    (inf_centralizer_sup_oddCoreIn_eq hS2 hSQ)
  refine le_solomonKStarOf_of_moved hstarS ?_ fun K hK hmove => ?_
  · rw [hLS]
    exact UnbalancedCorr.commutator_eq_of_isPComponent hJc.1 hJc.2
  · have hKP : IsTwoComponentIn K
        (conjClosure (twoLayerIn (L ⊓ centralizer (S : Set G)))
          (twoLayerIn (centralizer (S : Set G)))) :=
      isTwoComponentIn_conjClosure_of_not_le hK hstarS hmove
    have hlt : SolomonLt L K :=
      ⟨hL.1.1, isSolomonMember_of_isTwoComponentIn hS hS2 hK, S, hS2, hSQ, hKP⟩
    exact mem_solomonKStar_of_solomonEquiv hL (hL.1.2 L K ⟨hL.1.1, Relation.ReflTransGen.refl⟩ hlt)

end CFSG.ComponentClassification.Sol76
