module

public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFiveCent

public section

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace CFSG.AGLEmbedding

namespace AscEightFive

open AscEightFour

section EightFiveE

variable {G : Type} [Group G]


theorem isSubnormal_of_le {A B C : Subgroup G} (h : IsSubnormal A B) (hAC : A ≤ C)
    (hCB : C ≤ B) : IsSubnormal A C := by
  have := AscEightFour.isSubnormal_inf h C
  rwa [inf_eq_left.mpr hAC, inf_eq_right.mpr hCB] at this

theorem commutator_subgroupOf_eq {L H : Subgroup G} (hLH : L ≤ H) (hp : ⁅L, L⁆ = L) :
    ⁅L.subgroupOf H, L.subgroupOf H⁆ = L.subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLH, hp]

theorem isPerfect_of_commutator_eq {K : Subgroup G} (h : ⁅K, K⁆ = K) : Group.IsPerfect ↥K := by
  refine ⟨?_⟩
  apply Subgroup.map_injective K.subtype_injective
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    h]

theorem commutator_eq_of_short [Finite G] {Y : Subgroup G} (hs : IsShort2 Y)
    (hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y)) : ⁅Y, Y⁆ = Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup ↥Y := commutator ↥Y with hN
  have hNn : N.Normal := inferInstance
  have hsup : N ⊔ CFSG.pCore 2 ↥Y = ⊤ := by
    have h1 : N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) = ⊤ := by
      rw [hN, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), ← commutator_def]
      exact hq.1.commutator_eq_top
    have h2 := congrArg (Subgroup.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))) h1
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h2
  have h2 : IsPGroup 2 (↥Y ⧸ N) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      have hy : y ∈ ((CFSG.pCore 2 ↥Y ⊔ N : Subgroup ↥Y) : Set ↥Y) := by
        rw [sup_comm, hsup]; exact Subgroup.mem_top y
      rw [Subgroup.mul_normal] at hy
      obtain ⟨q, hq', n, hn, rfl⟩ := hy
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)) ⟨q, hq'⟩
      have hq1 : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      have hqN : q ∈ Subgroup.normalizer (N : Set ↥Y) :=
        Subgroup.mem_normalizer_iff.mpr fun n => ⟨fun h => hNn.conj_mem n h q, fun h => by
          simpa [mul_assoc] using hNn.conj_mem _ h q⁻¹⟩
      have := pow_mul_mem_of_normalizes hqN hn (2 ^ k)
      rw [hq1, inv_one, one_mul] at this
      exact this
  have htop := hs.1 N h2
  have hY : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  calc ⁅Y, Y⁆ = ⁅(⊤ : Subgroup ↥Y).map Y.subtype, (⊤ : Subgroup ↥Y).map Y.subtype⁆ := by
        rw [hY]
    _ = (commutator ↥Y).map Y.subtype := by rw [commutator_def, Subgroup.map_commutator]
    _ = Y := by rw [← hN, htop, hY]

end EightFiveE

section EightFiveW

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

theorem exists_conj_le_barM {Y : Subgroup G} (hL : IsTwoPrimeComponent X L)
    (hYH : Y ≤ hGrp5 X S L) (hYs : (Y.subgroupOf (hGrp5 X S L)).IsSubnormal)
    (hYN : ¬ Y ≤ nGrp5 X S L) :
    ∃ g : ↥X, QuotientGroup.mk' (CFSG.pCore 2 ↥X) g ∈ hBar X S L ∧
      (barM X L).map (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥X) g)).toMonoidHom ≤
        barM X Y := by
  have hHX : hGrp5 X S L ≤ X := hGrp5_le
  have hYX : Y ≤ X := hYH.trans hHX
  obtain ⟨y, hyY, hyN⟩ := Set.not_subset.mp hYN
  have hyC : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨y, hYX hyY⟩ ∉ cBar X S L :=
    fun h => hyN ⟨⟨y, hYX hyY⟩, h, rfl⟩
  have hyH : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨y, hYX hyY⟩ ∈ hBar X S L :=
    (mem_hGrp5 (x := ⟨y, hYX hyY⟩)).mp (hYH hyY)
  have hyZ : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨y, hYX hyY⟩ ∉ Subgroup.centralizer
      (⋃ h ∈ hBar X S L, ((barM X L).map (MulAut.conj h).toMonoidHom :
        Set (↥X ⧸ CFSG.pCore 2 ↥X))) := fun h => hyC ⟨hyH, h⟩
  rw [Subgroup.mem_centralizer_iff] at hyZ
  push Not at hyZ
  obtain ⟨z, hz, hzy⟩ := hyZ
  obtain ⟨h, hh, hzh⟩ := Set.mem_iUnion₂.mp hz
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) h
  refine ⟨g, hh, ?_⟩
  set h := QuotientGroup.mk' (CFSG.pCore 2 ↥X) g with hhdef
  set Lh := (barM X L).map (MulAut.conj h).toMonoidHom with hLhdef
  have hLhc : IsComponentOf Lh ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj h) _).mpr hL.component
  have hLhH : Lh ≤ hBar X S L := by
    rintro _ ⟨ℓ, hℓ, rfl⟩
    have hℓH : ℓ ∈ hBar X S L := (barM_le_dBar.trans le_sup_left) hℓ
    simpa using (hBar X S L).mul_mem ((hBar X S L).mul_mem hh hℓH) ((hBar X S L).inv_mem hh)
  let ρ : ↥(hGrp5 X S L) →* ↥(hBar X S L) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp (Subgroup.inclusion hHX)).codRestrict
      (hBar X S L) (fun x => (mem_hGrp5 (x := Subgroup.inclusion hHX x)).mp x.2)
  have hρ : Function.Surjective ρ := by
    rintro ⟨b, hb⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) b
    exact ⟨⟨x, (mem_hGrp5 (x := x)).mpr hb⟩, rfl⟩
  have hmap : (Y.subgroupOf (hGrp5 X S L)).map ρ = (barM X Y).subgroupOf (hBar X S L) := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Subgroup.inclusion hHX x, hx, rfl⟩
    · rintro ⟨x, hxY, hxw⟩
      refine ⟨⟨x, hYH hxY⟩, hxY, Subtype.ext ?_⟩
      exact hxw
  have hsub : ((barM X Y).subgroupOf (hBar X S L)).IsSubnormal := hmap ▸ hYs.map hρ
  rcases CFSG.ComponentClassification.LocalComponents.subnormal_contains_or_commutes
      (Lh.subgroupOf (hBar X S L)) ((barM X Y).subgroupOf (hBar X S L))
      (CFSG.ComponentClassification.LocalComponents.of_overgroup hLhc hLhH)
      (CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hsub) with hle | hc
  · intro w hw
    exact hle (show (⟨w, hLhH hw⟩ : ↥(hBar X S L)) ∈ Lh.subgroupOf (hBar X S L) from hw)
  · exfalso
    have hz' : (⟨z, hLhH hzh⟩ : ↥(hBar X S L)) ∈ Lh.subgroupOf (hBar X S L) := hzh
    have hy' : (⟨_, hyH⟩ : ↥(hBar X S L)) ∈ (barM X Y).subgroupOf (hBar X S L) :=
      ⟨⟨y, hYX hyY⟩, hyY, rfl⟩
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc hz'
    have h2 := Subgroup.mem_centralizer_iff.mp h1 _ hy'
    exact hzy (congrArg Subtype.val h2).symm

end EightFiveW

section EightFiveFinal

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

theorem isSolvable_subgroupOf_twoCore (K H : Subgroup G) :
    Group.IsSolvable ↥((pCoreOf 2 K).subgroupOf H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 ↥((pCoreOf 2 K).subgroupOf H) :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 K).comap_subtype
  have := h2.isNilpotent
  infer_instance

theorem eq_conj_of_short (hL : IsTwoPrimeComponent X L) {Y : Subgroup G}
    (hYH : Y ≤ hGrp5 X S L) (hYs : (Y.subgroupOf (hGrp5 X S L)).IsSubnormal)
    (hs : IsShort2 Y) (hYN : ¬ Y ≤ nGrp5 X S L) :
    ∃ g : ↥X, QuotientGroup.mk' (CFSG.pCore 2 ↥X) g ∈ hBar X S L ∧
      Y = L.map (MulAut.conj (g : G)).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHX : hGrp5 X S L ≤ X := hGrp5_le
  have hYX : Y ≤ X := hYH.trans hHX
  obtain ⟨g, hgH, hgY⟩ := exists_conj_le_barM hL hYH hYs hYN
  refine ⟨g, hgH, ?_⟩
  set L' := L.map (MulAut.conj (g : G)).toMonoidHom with hL'def
  have hL' : IsTwoPrimeComponent X L' := IsTwoPrimeComponent.map_conj g.2 hL
  have hbar' : barM X L' =
      (barM X L).map (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥X) g)).toMonoidHom :=
    barM_map_conj g.2 L
  have hLhH : barM X L' ≤ hBar X S L := by
    rw [hbar']
    rintro _ ⟨ℓ, hℓ, rfl⟩
    have hℓH : ℓ ∈ hBar X S L := (barM_le_dBar.trans le_sup_left) hℓ
    simpa using (hBar X S L).mul_mem ((hBar X S L).mul_mem hgH hℓH) ((hBar X S L).inv_mem hgH)
  have hL'H : L' ≤ hGrp5 X S L := le_hGrp5_of_barM_le hL'.le hLhH
  have hR : ((pCoreOf 2 X).subgroupOf (hGrp5 X S L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer twoCore_le_hGrp5).mpr
      (hHX.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X))
  have hRs := isSolvable_subgroupOf_twoCore X (hGrp5 X S L)
  have hL'Y : L' ≤ Y := by
    have key := le_of_perfect_of_le_sup_of_isSubnormal (K := Y.subgroupOf (hGrp5 X S L))
      (R := (pCoreOf 2 X).subgroupOf (hGrp5 X S L)) (P := L'.subgroupOf (hGrp5 X S L)) hYs
      (commutator_subgroupOf_eq hL'H hL'.perfect) ?_
    · intro ℓ hℓ
      exact key (show (⟨ℓ, hL'H hℓ⟩ : ↥(hGrp5 X S L)) ∈ L'.subgroupOf (hGrp5 X S L) from hℓ)
    · rintro ⟨ℓ, hℓH⟩ hℓ
      have hℓX := hHX hℓH
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨ℓ, hℓX⟩ ∈ barM X Y :=
        hgY (hbar' ▸ ⟨⟨ℓ, hℓX⟩, hℓ, rfl⟩)
      obtain ⟨y₀, hy₀Y, hy₀⟩ := h1
      have hq : y₀⁻¹ * ⟨ℓ, hℓX⟩ ∈ CFSG.pCore 2 ↥X := by
        rw [← QuotientGroup.eq]
        exact hy₀
      have hqQ : ((y₀⁻¹ * ⟨ℓ, hℓX⟩ : ↥X) : G) ∈ pCoreOf 2 X := ⟨_, hq, rfl⟩
      have hy₀H : (y₀ : G) ∈ hGrp5 X S L := hYH hy₀Y
      have hqH : ((y₀⁻¹ * ⟨ℓ, hℓX⟩ : ↥X) : G) ∈ hGrp5 X S L := twoCore_le_hGrp5 hqQ
      have heq : (⟨ℓ, hℓH⟩ : ↥(hGrp5 X S L)) = ⟨y₀, hy₀H⟩ * ⟨_, hqH⟩ := by
        apply Subtype.ext
        simp
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (show _ ∈ Y.subgroupOf _ from hy₀Y))
        (Subgroup.mem_sup_right (show _ ∈ (pCoreOf 2 X).subgroupOf _ from hqQ))
  set φ := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) with hφ
  set P₁ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y) := (L'.subgroupOf Y).map φ with hP₁
  have hL'sY : CFSG.Open.IsSubnormal L' Y := isSubnormal_of_le hL'.subnormal hL'Y hYX
  have hsubY : (L'.subgroupOf Y).IsSubnormal := NoXBlock.isSubnormal_subgroupOf_of_open hL'sY
  have hP₁s : CFSG.Open.IsSubnormal P₁ ⊤ :=
    CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal
      (hsubY.map (QuotientGroup.mk'_surjective _))
  have hP₁p : ⁅P₁, P₁⁆ = P₁ := by
    rw [hP₁, ← Subgroup.map_commutator, commutator_subgroupOf_eq hL'Y hL'.perfect]
  have hP₁ne : P₁ ≠ ⊥ := by
    intro hbot
    have h2 : IsPGroup 2 ↥L' := by
      intro ℓ
      have hmem : (⟨ℓ, hL'Y ℓ.2⟩ : ↥Y) ∈ CFSG.pCore 2 ↥Y := by
        rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥Y), MonoidHom.mem_ker]
        have : φ ⟨ℓ, hL'Y ℓ.2⟩ ∈ P₁ := ⟨_, ℓ.2, rfl⟩
        rw [hbot] at this
        exact this
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)) ⟨_, hmem⟩
      refine ⟨k, Subtype.ext ?_⟩
      have := congrArg (fun t : ↥(CFSG.pCore 2 ↥Y) => ((t : ↥Y) : G)) hk
      simpa using this
    have hle := CFSG.RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 2
      hL'.subnormal h2
    have hb : barM X L' = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      have hxQ : (x : G) ∈ pCoreOf 2 X := hle hx
      obtain ⟨y, hy, hyx⟩ := hxQ
      obtain rfl : y = x := Subtype.ext hyx
      rw [Subgroup.mem_bot, QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff y).mpr hy
    have hc := hL'.component
    rw [hb] at hc
    obtain ⟨-, -, -, hsimp⟩ := hc
    obtain ⟨a, b, hab⟩ := hsimp.toNontrivial.exists_pair_ne
    apply hab
    induction a using QuotientGroup.induction_on with
    | H a => induction b using QuotientGroup.induction_on with
      | H b => rw [Subsingleton.elim a b]
  rcases hs.2.2.2.1 with hq | h3
  · have hqo : CFSG.Open.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := ⟨hq.1.commutator_eq_top, hq.2.1⟩
    have : Group.IsPerfect ↥P₁ := isPerfect_of_commutator_eq hP₁p
    rcases CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top hqo P₁
        hP₁s with hb | htop
    · exact absurd hb hP₁ne
    · have hYp := commutator_eq_of_short hs hq
      have hYsO : CFSG.Open.IsSubnormal Y (hGrp5 X S L) :=
        LocalCGT.open_isSubnormal_of_subgroupOf hYH hYs
      have hO2 := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_subnormal 2 hYsO
      have hR2 : ((pCoreOf 2 (hGrp5 X S L)).subgroupOf (hGrp5 X S L)).Normal :=
        CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_normal 2 _
      have hR2s := isSolvable_subgroupOf_twoCore (hGrp5 X S L) (hGrp5 X S L)
      have hL'sH : (L'.subgroupOf (hGrp5 X S L)).IsSubnormal :=
        NoXBlock.isSubnormal_subgroupOf_of_open (isSubnormal_of_le hL'.subnormal hL'H hHX)
      have key := le_of_perfect_of_le_sup_of_isSubnormal (K := L'.subgroupOf (hGrp5 X S L))
        (R := (pCoreOf 2 (hGrp5 X S L)).subgroupOf (hGrp5 X S L))
        (P := Y.subgroupOf (hGrp5 X S L)) hL'sH (commutator_subgroupOf_eq hYH hYp) ?_
      · have hYL' : Y ≤ L' := fun y hy =>
          key (show (⟨y, hYH hy⟩ : ↥(hGrp5 X S L)) ∈ Y.subgroupOf _ from hy)
        exact le_antisymm hYL' hL'Y
      · rintro ⟨y, hyH⟩ hy
        have hmem : φ ⟨y, hy⟩ ∈ P₁ := htop ▸ Subgroup.mem_top _
        obtain ⟨ℓ, hℓ, hℓy⟩ := hmem
        have hq' : ℓ⁻¹ * ⟨y, hy⟩ ∈ CFSG.pCore 2 ↥Y := by
          rw [← QuotientGroup.eq]
          exact hℓy
        have hqY : ((ℓ⁻¹ * ⟨y, hy⟩ : ↥Y) : G) ∈ pCoreOf 2 Y := ⟨_, hq', rfl⟩
        have hqH : ((ℓ⁻¹ * ⟨y, hy⟩ : ↥Y) : G) ∈ pCoreOf 2 (hGrp5 X S L) := hO2 hqY
        have hℓH : (ℓ : G) ∈ hGrp5 X S L := hYH ℓ.2
        have hqH' : ((ℓ⁻¹ * ⟨y, hy⟩ : ↥Y) : G) ∈ hGrp5 X S L :=
          CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _ hqH
        have heq : (⟨y, hyH⟩ : ↥(hGrp5 X S L)) = ⟨ℓ, hℓH⟩ * ⟨_, hqH'⟩ := by
          apply Subtype.ext
          simp
        rw [heq]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (show _ ∈ L'.subgroupOf _ from hℓ))
          (Subgroup.mem_sup_right (show _ ∈ (pCoreOf 2 _).subgroupOf _ from hqH))
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcyc : IsCyclic (↥Y ⧸ CFSG.pCore 2 ↥Y) := isCyclic_of_prime_card h3
    have hcomm : ∀ a b : ↥Y ⧸ CFSG.pCore 2 ↥Y, a * b = b * a := fun a b =>
      (IsCyclic.isMulCommutative (α := ↥Y ⧸ CFSG.pCore 2 ↥Y)).is_comm.comm a b
    have hb : ⁅P₁, P₁⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (fun x _ => Subgroup.mem_centralizer_iff.mpr fun y _ => hcomm y x)
    exact hP₁ne (hP₁p.symm.trans hb)

theorem inClassXBlock_of_eightFive (hLF : CFSG.CGT.PushingUpLit.AschbacherLocalFactorization)
    (hK : CFSG.Open.IsKGroup ↥X) (hyp : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L)
    (hsyl : IsSylowTwoOf (S ⊓ L) L) : InClassXBlock L := by
  obtain ⟨Y, ⟨hYH, hYs, hYx⟩, hYM⟩ := exists_block5 hLF hK hyp hL hsyl
  obtain ⟨g, -, rfl⟩ := eq_conj_of_short hL hYH hYs (LocalCGT.inClassXBlock_of_inClassX hYx).1
    (fun h => hYM (h.trans le_sup_left))
  let e : ↥(L.map (MulAut.conj (g : G)).toMonoidHom) ≃* ↥L :=
    (L.equivMapOfInjective (MulAut.conj (g : G)).toMonoidHom (MulAut.conj (g : G)).injective).symm
  exact LocalCGT.inClassXBlock_of_inClassX (CFSG.CGT.PushingUpLit.InClassX.of_mulEquiv e hYx)

end EightFiveFinal

end AscEightFive

theorem asc81bEightFive_of_factorization
    (hLF : CFSG.CGT.PushingUpLit.AschbacherLocalFactorization) : Asc81bEightFive :=
  fun _ _ _ _ _ _ hK hyp hL hsyl => AscEightFive.inClassXBlock_of_eightFive hLF hK hyp hL hsyl

end CFSG.AGLEmbedding
