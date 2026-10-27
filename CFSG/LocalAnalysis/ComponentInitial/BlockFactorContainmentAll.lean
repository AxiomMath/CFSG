module

public import CFSG.LocalAnalysis.ComponentInitial.BlockTransporter
public import CFSG.GroupTheory.InvolutionFixedCentralSylow

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace BlockFactorContainment

theorem mem_center_iff_mem_centralizer {B : Subgroup G} (x : B) :
    x ∈ center B ↔ (x : G) ∈ centralizer (B : Set G) := by
  rw [mem_center_iff, mem_centralizer_iff]
  constructor
  · intro h b hb
    exact congrArg Subtype.val (h ⟨b, hb⟩)
  · intro h b
    exact Subtype.ext (h b b.2)

theorem conjSub_one_eq (K : Subgroup G) : conjSub 1 K = K := by
  rw [conjSub, show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G from by ext; simp,
    Subgroup.map_id]

theorem conjSub_biSup_le {Ω : Set (Subgroup G)} {g : G} (h : ∀ L ∈ Ω, conjSub g L ∈ Ω) :
    conjSub g (⨆ L ∈ Ω, L) ≤ ⨆ L ∈ Ω, L := by
  rw [conjSub, Subgroup.map_iSup]
  refine iSup_le fun L => ?_
  rw [Subgroup.map_iSup]
  exact iSup_le fun hL => le_iSup₂ (f := fun L (_ : L ∈ Ω) => L) _ (h L hL)

theorem exists_pair_of_four_le_index {R : Type*} [Group R] [Finite R] (hR : IsPGroup 2 R)
    (I : Subgroup R) [I.Normal] (h4 : 4 ≤ I.index) :
    ∃ y r : R, y ∉ I ∧ y ^ 2 ∈ I ∧ r ∉ I ∧ y⁻¹ * r ∉ I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (R ⧸ I) = I.index := (Subgroup.index_eq_card I).symm
  obtain ⟨n, hn⟩ := (hR.to_quotient I).exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [hcard, pow_zero] at hn
    omega
  have h2 : 2 ∣ Nat.card (R ⧸ I) := hn ▸ dvd_pow_self 2 hn0
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨q', hq'1, hq'q⟩ : ∃ q' : R ⧸ I, q' ≠ 1 ∧ q' ≠ q := by
    by_contra hall
    have hsurj : Function.Surjective (fun b : Bool => if b then q else (1 : R ⧸ I)) := by
      intro x
      by_cases hx1 : x = 1
      · exact ⟨false, by simp [hx1]⟩
      · by_cases hxq : x = q
        · exact ⟨true, by simp [hxq]⟩
        · exact absurd ⟨x, hx1, hxq⟩ hall
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, hcard] at this
    omega
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q'
  refine ⟨y, r, fun hyI => ?_, ?_, fun hrI => hq'1 ((QuotientGroup.eq_one_iff r).mpr hrI),
    fun h => hq'q ?_⟩
  · rw [(QuotientGroup.eq_one_iff y).mpr hyI, orderOf_one] at hq
    omega
  · rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hq, pow_orderOf_eq_one]
  · have := (QuotientGroup.eq_one_iff (y⁻¹ * r)).mpr h
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at this
    exact (inv_mul_eq_one.mp this).symm

variable [Finite G] {J : Subgroup G}

theorem mem_blockInvolutions_of_mem (hJ : IsUniversalComponent J) (heven : Even (Nat.card J))
    (hΔ : (block J).Nontrivial) {A : Subgroup G} (hA : A ∈ block J) {a : G} (haA : a ∈ A)
    (ha2 : orderOf a = 2) : a ∈ blockInvolutions J := by
  obtain ⟨L, hL, hLA⟩ := hΔ.exists_ne A
  rcases commRel_of_mem_block hJ heven hA hL with h | h
  · exact absurd h.symm hLA
  · exact ⟨ha2, L, hL, Subgroup.commutator_eq_bot_iff_le_centralizer.1 h haA⟩

theorem le_of_mem_of_le_normalizer (hq : CFSG.Assembly.IsQuasisimple J)
    (heven : Even (Nat.card J)) (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial)
    {K : Subgroup G} (hK : K ∈ block J) {g : G} (hg : g ∉ normalizer (blockGroup J : Set G))
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPB : P ≤ conjSub g K)
    (hPc : ¬ P ≤ centralizer (conjSub g K : Set G)) {a : G} (ha : a ∈ blockInvolutions J)
    (haP : ∀ p ∈ P, p * a = a * p) {Y : Subgroup G} (haY : a ∈ Y)
    (hBY : conjSub g K ≤ normalizer (Y : Set G)) : conjSub g K ≤ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := conjSub g K with hBdef
  have hPne : P ≠ ⊥ := fun h => hPc (h ▸ bot_le)
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPne
  obtain ⟨n, hn, hcard⟩ := hP.nontrivial_iff_card.mp this
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := P) 2
    (by rw [hcard]; exact dvd_pow_self 2 hn.ne')
  have hy2 : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe, hy]
  obtain ⟨k, hkK, hky⟩ := Subgroup.mem_map.mp (hPB y.2)
  have hky' : (y : G) = g * k * g⁻¹ := hky.symm
  have hk2 : orderOf k = 2 := by
    rw [show k = g⁻¹ * y * g by rw [hky']; group, orderOf_inv_mul_mul, hy2]
  set c := g⁻¹ * a * g with hcdef
  have hcH : c ∈ normalizer (blockGroup J : Set G) := by
    apply centralizer_le_normalizer_blockGroup_of_mem hJ heven hΔ hK hkK hk2
    rw [mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    have hay : a * y = y * a := (haP y y.2).symm
    calc k * c = g⁻¹ * (y * a) * g := by rw [hcdef, hky']; group
      _ = g⁻¹ * (a * y) * g := by rw [hay]
      _ = c * k := by rw [hcdef, hky']; group
  have hcK : conjSub c K ∈ block J := ((mem_normalizer_blockGroup_iff hq hJ heven c).mp hcH K).mp hK
  have hconj : conjSub g (conjSub c K) = conjSub a B := by
    rw [← conjSub_mul, hBdef, ← conjSub_mul, show g * c = a * g by rw [hcdef]; group]
  have hcKK : conjSub c K = K := by
    by_contra hne
    have hcomm : ⁅conjSub c K, K⁆ = ⊥ := (commRel_of_mem_block hJ heven hcK hK).resolve_left hne
    have hcomm' : ⁅conjSub a B, B⁆ = ⊥ := by
      rw [← hconj, hBdef, commutator_conjSub, hcomm, conjSub, Subgroup.map_bot]
    refine hPc fun p hp => Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm' ?_
    refine ⟨p, hPB hp, ?_⟩
    change a * p * a⁻¹ = p
    rw [← haP p hp, mul_inv_cancel_right]
  have haB : conjSub a B = B := by rw [← hconj, hcKK]
  have haN : a ∈ normalizer (B : Set G) := by
    refine mem_normalizer_of_conjSub_le haB.le ?_
    have := conjSub_inv_conjSub a B
    rw [haB] at this
    exact this.le
  have hanc : a ∉ centralizer (B : Set G) := by
    intro haC
    refine hg (mem_normalizer_of_inv_mul_mul_mem hJ heven ha ⟨?_, K, hK, ?_⟩)
    · rw [orderOf_inv_mul_mul]
      exact ha.1
    · have : g⁻¹ * a * g⁻¹⁻¹ ∈ conjSub g⁻¹ (centralizer (B : Set G)) := ⟨a, haC, rfl⟩
      rwa [conjSub_centralizer, hBdef, conjSub_inv_conjSub, inv_inv] at this
  have hqB := (AssemblyBPredicates.isQuasisimple_iff_native B).1
    (isQuasisimple_of_isConjOf hq (isConjOf_conjSub hK.1 g))
  have hnormal : ((Y ⊓ B).subgroupOf B).Normal := by
    refine ⟨fun x hx b => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨?_, (b * x * b⁻¹).2⟩
    simpa using (mem_normalizer_iff.mp (hBY b.2) x).mp hx.1
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hqB hnormal with htop | hcen
  · intro b hb
    have : (⟨b, hb⟩ : B) ∈ (Y ⊓ B).subgroupOf B := htop ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp this).1
  ·
    exfalso
    apply hanc
    have hba : ∀ b ∈ B, ⁅b, a⁆ ∈ centralizer (B : Set G) := by
      intro b hb
      have h1 : a * b⁻¹ * a⁻¹ ∈ B := (mem_normalizer_iff.mp haN b⁻¹).mp (B.inv_mem hb)
      have hmemB : ⁅b, a⁆ ∈ B := by
        rw [commutatorElement_def, show b * a * b⁻¹ * a⁻¹ = b * (a * b⁻¹ * a⁻¹) by group]
        exact B.mul_mem hb h1
      have hmemY : ⁅b, a⁆ ∈ Y := by
        rw [commutatorElement_def]
        exact Y.mul_mem ((mem_normalizer_iff.mp (hBY hb) a).mp haY) (Y.inv_mem haY)
      have : (⟨⁅b, a⁆, hmemB⟩ : B) ∈ center B :=
        hcen (Subgroup.mem_subgroupOf.mpr ⟨hmemY, hmemB⟩)
      exact (mem_center_iff_mem_centralizer _).mp this
    have hX : ⁅B, zpowers a⁆ ≤ centralizer (B : Set G) := by
      rw [Subgroup.commutator_le]
      intro b hb x hx
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hpow : a ^ m = a ^ (m % 2) := by
        have := (zpow_mod_orderOf a m).symm
        rwa [ha.1, Nat.cast_ofNat] at this
      rcases Int.emod_two_eq_zero_or_one m with h | h
      · rw [hpow, h, zpow_zero, commutatorElement_one_right]
        exact one_mem _
      · rw [hpow, h, zpow_one]
        exact hba b hb
    have h3 := CFSG.LocalCores.perfect_double_commutator hqB.1
      (Subgroup.commutator_eq_bot_iff_le_centralizer.2 hX)
    rw [mem_centralizer_iff]
    intro b hb
    exact (mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3 hb) a
      (mem_zpowers a)).symm

theorem false_of_le_blockGroup (hq : CFSG.Assembly.IsQuasisimple J)
    (heven : Even (Nat.card J)) (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial)
    {K : Subgroup G} (hK : K ∈ block J) {g : G} (hg : g ∉ normalizer (blockGroup J : Set G))
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPB : P ≤ conjSub g K)
    (hPc : ¬ P ≤ centralizer (conjSub g K : Set G)) (hBM : conjSub g K ≤ blockGroup J) :
    False := by
  have hJn : blockGroup J ≤ normalizer (J : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (le_blockGroup mem_block_self)).1
      (normal_of_mem_block hJ heven mem_block_self)
  obtain ⟨a, haJ, ha2, haP⟩ := CFSG.GroupTheory.exists_involution_commute_of_isPGroup_le_normalizer
    hP ((hPB.trans hBM).trans hJn) heven
  have hBJ := le_of_mem_of_le_normalizer hq heven hJ hΔ hK hg hP hPB hPc
    (mem_blockInvolutions_of_mem hJ heven hΔ mem_block_self haJ ha2) haP haJ (hBM.trans hJn)
  have hcard : Nat.card J ≤ Nat.card (conjSub g K) := by
    obtain ⟨c, hc⟩ := hK.1
    rw [card_conjSub, hc, card_conjSub]
  have hBeq : conjSub g K = J := Subgroup.eq_of_le_of_card_ge hBJ hcard
  exact hg (mem_normalizer_blockGroup hJ heven hK (by rw [hBeq]; exact mem_block_self))

theorem false_of_invariant (hq : CFSG.Assembly.IsQuasisimple J)
    (heven : Even (Nat.card J)) (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial)
    {K : Subgroup G} (hK : K ∈ block J) {g : G}
    (hKg : conjSub g K ≤ normalizer (blockGroup J : Set G))
    (hg : g ∉ normalizer (blockGroup J : Set G)) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPB : P ≤ conjSub g K) (hPc : ¬ P ≤ centralizer (conjSub g K : Set G))
    {Ω : Set (Subgroup G)} (hΩ : Ω ⊆ block J) (hΩP : ∀ p ∈ P, ∀ L ∈ Ω, conjSub p L ∈ Ω)
    {A : Subgroup G} (hAΩ : A ∈ Ω) (hsmall : Ω = {A} ∨ ∃ A' ∈ block J, A' ∉ Ω) : False := by
  set X := ⨆ L ∈ Ω, L with hXdef
  have hXM : X ≤ blockGroup J := iSup₂_le fun L hL => le_blockGroup (hΩ hL)
  have hPX : P ≤ normalizer (X : Set G) := fun p hp =>
    mem_normalizer_of_conjSub_le (conjSub_biSup_le (hΩP p hp))
      (conjSub_biSup_le (hΩP p⁻¹ (P.inv_mem hp)))
  have hAX : A ≤ X := le_iSup₂ (f := fun L (_ : L ∈ Ω) => L) A hAΩ
  have hXeven : Even (Nat.card X) := by
    have hA : Nat.card A = Nat.card J := by
      obtain ⟨c, hc⟩ := (hΩ hAΩ).1
      rw [hc, card_conjSub]
    have := Subgroup.card_dvd_of_le hAX
    rw [hA] at this
    exact even_iff_two_dvd.2 ((even_iff_two_dvd.1 heven).trans this)
  obtain ⟨a, haX, ha2, haP⟩ :=
    CFSG.GroupTheory.exists_involution_commute_of_isPGroup_le_normalizer hP hPX hXeven
  have ha : a ∈ blockInvolutions J := by
    rcases hsmall with hΩA | ⟨A', hA', hA'Ω⟩
    · have hXA : X = A := by rw [hXdef, hΩA]; simp
      exact mem_blockInvolutions_of_mem hJ heven hΔ (hΩ hAΩ) (hXA ▸ haX) ha2
    · refine ⟨ha2, A', hA', ?_⟩
      have hXc : X ≤ centralizer (A' : Set G) := iSup₂_le fun L hL =>
        Subgroup.commutator_eq_bot_iff_le_centralizer.1
          ((commRel_of_mem_block hJ heven (hΩ hL) hA').resolve_left fun h => hA'Ω (h ▸ hL))
      exact hXc haX
  exact false_of_le_blockGroup hq heven hJ hΔ hK hg hP hPB hPc
    (le_of_mem_of_le_normalizer hq heven hJ hΔ hK hg hP hPB hPc ha haP (hXM haX) hKg)

end BlockFactorContainment

variable [Finite G] {J : Subgroup G}

open BlockFactorContainment in
theorem commuting_block_factor_containment_transporter_all
    (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial)
    {K : Subgroup G} (hK : K ∈ block J) {g : G}
    (hKg : conjSub g K ≤ normalizer (blockGroup J : Set G)) :
    g ∈ normalizer (blockGroup J : Set G) := by
  by_contra hg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := conjSub g K with hBdef
  have hqB := (AssemblyBPredicates.isQuasisimple_iff_native B).1
    (isQuasisimple_of_isConjOf hq (isConjOf_conjSub hK.1 g))
  have : Group.IsPerfect B := hqB.1
  have hBeven : 2 ∣ Nat.card B := by
    obtain ⟨c, hc⟩ := hK.1
    rw [hBdef, card_conjSub, hc, card_conjSub]
    exact even_iff_two_dvd.1 heven
  obtain ⟨R⟩ : Nonempty (Sylow 2 B) := inferInstance
  obtain ⟨y, r, hy, hy2, hr, hyr⟩ := exists_pair_of_four_le_index R.isPGroup'
    ((center B).subgroupOf (R : Subgroup B))
    (CFSG.GroupTheory.four_le_index_center_subgroupOf_sylow_two R (R.ne_bot_of_dvd_card hBeven))
  set RG := (R : Subgroup B).map B.subtype with hRGdef
  have hRG : IsPGroup 2 RG := R.isPGroup'.map B.subtype
  have hRGB : RG ≤ B := Subgroup.map_subtype_le _
  set y' : G := ((y : B) : G) with hy'def
  set r' : G := ((r : B) : G) with hr'def
  have hyRG : y' ∈ RG := ⟨y, y.2, rfl⟩
  have hrRG : r' ∈ RG := ⟨r, r.2, rfl⟩
  have hnc : ∀ x : (R : Subgroup B), x ∉ (center B).subgroupOf (R : Subgroup B) →
      ((x : B) : G) ∉ centralizer (B : Set G) := fun x hx hxc =>
    hx (Subgroup.mem_subgroupOf.mpr ((mem_center_iff_mem_centralizer _).mpr hxc))
  have hy'c : y' ∉ centralizer (B : Set G) := hnc y hy
  have hr'c : r' ∉ centralizer (B : Set G) := hnc r hr
  have hyr'c : y'⁻¹ * r' ∉ centralizer (B : Set G) := hnc (y⁻¹ * r) hyr
  have hy2c : y' ^ (2 : ℤ) ∈ centralizer (B : Set G) := by
    have := (mem_center_iff_mem_centralizer _).mp (Subgroup.mem_subgroupOf.mp hy2)
    rwa [zpow_two, ← pow_two]
  have hfix : ∀ x ∈ RG, conjSub x J = J → x ∈ centralizer (B : Set G) := by
    intro x hx hxJ
    by_contra hxc
    have hxN : x ∈ normalizer (J : Set G) := by
      refine mem_normalizer_of_conjSub_le hxJ.le ?_
      have := conjSub_inv_conjSub x J
      rw [hxJ] at this
      exact this.le
    refine false_of_invariant hq heven hJ hΔ hK hKg hg (hRG.to_le (zpowers_le.mpr hx))
      ((zpowers_le.mpr hx).trans hRGB) (fun h => hxc (h (mem_zpowers x)))
      (Ω := {J}) (Set.singleton_subset_iff.mpr mem_block_self) ?_ (Set.mem_singleton J)
      (Or.inl rfl)
    intro p hp L hL
    rw [Set.mem_singleton_iff] at hL ⊢
    rw [hL]
    exact conjSub_eq_of_mem_normalizer ((zpowers_le.mpr hxN) hp)
  have hyB : y' ∈ B := hRGB hyRG
  have hstab : ∀ x ∈ B, conjSub x J ∈ block J := fun x hx =>
    ((mem_normalizer_blockGroup_iff hq hJ heven x).mp (hKg hx) J).mp mem_block_self
  have horbit : ∀ A' ∈ block J, ∃ k : ℤ, conjSub (y' ^ k) J = A' := by
    intro A' hA'
    by_contra hnot
    refine false_of_invariant hq heven hJ hΔ hK hKg hg (hRG.to_le (zpowers_le.mpr hyRG))
      ((zpowers_le.mpr hyRG).trans hRGB) (fun h => hy'c (h (mem_zpowers y')))
      (Ω := {L | ∃ k : ℤ, conjSub (y' ^ k) J = L}) ?_ ?_ ⟨0, by rw [zpow_zero, conjSub_one_eq]⟩
      (Or.inr ⟨A', hA', hnot⟩)
    · rintro L ⟨k, rfl⟩
      exact hstab _ (B.zpow_mem hyB k)
    · rintro p hp L ⟨k, rfl⟩
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hp
      exact ⟨m + k, by rw [zpow_add, conjSub_mul]⟩
  obtain ⟨k, hk⟩ := horbit _ (hstab r' (hRGB hrRG))
  have hxJ : conjSub (y' ^ (-k) * r') J = J := by
    rw [conjSub_mul, ← hk, ← conjSub_mul, ← zpow_add, neg_add_cancel, zpow_zero, conjSub_one_eq]
  have hxC := hfix _ (RG.mul_mem (RG.zpow_mem hyRG _) hrRG) hxJ
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' k
  · apply hr'c
    have hyk : y' ^ k ∈ centralizer (B : Set G) := by
      rw [hj, zpow_mul]
      exact Subgroup.zpow_mem _ hy2c j
    rw [show r' = y' ^ k * (y' ^ (-k) * r') by group]
    exact Subgroup.mul_mem _ hyk hxC
  · apply hyr'c
    have hyk : y' ^ (2 * j) ∈ centralizer (B : Set G) := by
      rw [zpow_mul]
      exact Subgroup.zpow_mem _ hy2c j
    rw [show y'⁻¹ * r' = y' ^ (2 * j) * (y' ^ (-k) * r') by rw [hj]; group]
    exact Subgroup.mul_mem _ hyk hxC

end CFSG.LocalAnalysis.ComponentInitial
