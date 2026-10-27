module

public import CFSG.ClassicalInvolution.Q3.Q3NSShape
public import CFSG.ClassicalInvolution.Q3.Q3NLFrame
import CFSG.ClassicalInvolution.Asc77.WP3SCUTq

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NS

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.RouteD
open scoped MatrixGroups commutatorElement

section Sylow

variable {G : Type} [Group G]

theorem exists_conj_involution_commuting3 {N F : Subgroup G} (hN : Odd (Nat.card N))
    (hFN : F ≤ Subgroup.normalizer (N : Set G)) (hF2 : IsPGroup 2 F) {w : G} (hw2 : w * w = 1)
    (hcomm : ∀ x ∈ F, (x * w * x⁻¹) * w ∈ N) :
    ∃ o ∈ N, ∀ x ∈ F, x * (o * w * o⁻¹) = (o * w * o⁻¹) * x :=
  CFSG.ClassicalInvolution.Asc77.exists_conj_involution_commuting hN hFN hF2 hw2 hcomm

end Sylow

section ConjImage

variable {G : Type} [Group G]

theorem locElt_congr {Ω : Set (Subgroup G)} {z a b : G} (h : a = b) (ha : a ∈ locLayer Ω z)
    (hb : b ∈ locLayer Ω z) : locElt Ω z a ha = locElt Ω z b hb := by
  subst h
  rfl

theorem mem_locImg_iff' {Ω : Set (Subgroup G)} {z : G} {L : Subgroup G} {w : locQuot Ω z} :
    w ∈ locImg Ω z L ↔ ∃ (u : G) (hu : u ∈ locLayer Ω z), u ∈ L ∧ locElt Ω z u hu = w := by
  unfold locImg
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, u.2, Subgroup.mem_subgroupOf.mp hu, rfl⟩
  · rintro ⟨u, hu, huL, rfl⟩
    exact ⟨⟨u, hu⟩, Subgroup.mem_subgroupOf.mpr huL, rfl⟩

theorem locElt_conj_eq {Ω : Set (Subgroup G)} {z y v : G} (hy : y ∈ locLayer Ω z)
    (hv : v ∈ locLayer Ω z) (hc : ⁅y, v⁆ ∈ oddCoreIn (locLayer Ω z))
    (huv : y * v * y⁻¹ ∈ locLayer Ω z) : locElt Ω z (y * v * y⁻¹) huv = locElt Ω z v hv := by
  have h1 := (mk_comm_eq_iff hy hv).mpr hc
  show QuotientGroup.mk' _ (⟨y * v * y⁻¹, huv⟩ : ↥(locLayer Ω z)) =
    QuotientGroup.mk' _ (⟨v, hv⟩ : ↥(locLayer Ω z))
  have e : (⟨y * v * y⁻¹, huv⟩ : ↥(locLayer Ω z)) = ⟨y, hy⟩ * ⟨v, hv⟩ * ⟨y, hy⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, h1]
  group

theorem locImg_conjSub_eq {Ω : Set (Subgroup G)} {z : G} {N : Subgroup G}
    (hN : N ≤ locLayer Ω z) {y : G} (hy : y ∈ locLayer Ω z)
    (hc : ∀ x ∈ N, ⁅y, x⁆ ∈ oddCoreIn (locLayer Ω z)) :
    locImg Ω z (conjSub y N) = locImg Ω z N := by
  ext w
  rw [mem_locImg_iff', mem_locImg_iff']
  constructor
  · rintro ⟨u, hu, huL, rfl⟩
    have hv := mem_conjSub_iff.mp huL
    have hvY : y⁻¹ * u * y ∈ locLayer Ω z := hN hv
    refine ⟨y⁻¹ * u * y, hvY, hv, ?_⟩
    have e : y * (y⁻¹ * u * y) * y⁻¹ = u := by group
    have hy' : y * (y⁻¹ * u * y) * y⁻¹ ∈ locLayer Ω z := by rw [e]; exact hu
    have h2 := locElt_conj_eq hy hvY (hc _ hv) hy'
    rw [← h2]
    exact locElt_congr e hy' hu
  · rintro ⟨v, hv, hvN, rfl⟩
    have hyv : y * v * y⁻¹ ∈ locLayer Ω z :=
      (locLayer Ω z).mul_mem ((locLayer Ω z).mul_mem hy hv) ((locLayer Ω z).inv_mem hy)
    refine ⟨y * v * y⁻¹, hyv, ?_, locElt_conj_eq hy hv (hc v hvN) hyv⟩
    rw [mem_conjSub_iff]
    have e : y⁻¹ * (y * v * y⁻¹) * y = v := by group
    rw [e]
    exact hvN

theorem inf_oddCoreIn_le_oddCoreIn [Finite G] {Y M : Subgroup G} (hMY : M ≤ Y) :
    M ⊓ oddCoreIn Y ≤ oddCoreIn M := by
  refine le_oddCoreIn_of_normalizes inf_le_left ?_ ?_
  · intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hu)) h
    have h2 := (Subgroup.mem_normalizer_iff.mp (normalizer_oddCoreIn Y (hMY hu))) h
    simp only [Subgroup.mem_inf]
    exact and_congr h1 h2
  · have hdvd : Nat.card (M ⊓ oddCoreIn Y : Subgroup G) ∣ Nat.card (oddCoreIn Y) :=
      Subgroup.card_dvd_of_le inf_le_right
    exact Odd.of_dvd_nat (odd_card_oddCoreIn _) hdvd

end ConjImage

section Statements


@[expose] def NTUniqPair3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G), NTCommon3 K z →
    ∀ (L L' : Subgroup G) (l : G), L ∈ centralizingMembers (conjClass3 K) {z} →
      L' ∈ centralizingMembers (conjClass3 K) {z} → IsClassicalMember3 L l →
      IsClassicalMember3 L' l → locImg (conjClass3 K) z L = locImg (conjClass3 K) z L' → L = L'

@[expose] def NTFuzzyFrameTriple3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G), NTCommon3 K z →
    ∀ A : Subgroup G, FuzzyFrame3 (conjClass3 K) A → IndepTriple3 (conjClass3 K)

end Statements

section Frame3


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem isPGroup_zpowers_of_sq_eq_one3 {c : G} (hc : c * c = 1) :
    IsPGroup 2 (Subgroup.zpowers c) := by
  refine isPGroup_two_of_sq_eq_one fun x hx => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← (Commute.refl c).mul_zpow, hc, one_zpow]

theorem exactTriple_zpowers {a b c : G} (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hc1 : c ≠ 1) (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) (hne_ab : a ≠ b) (hne_ac : a ≠ c) (hne_bc : b ≠ c) :
    ExactTriple (Subgroup.zpowers a) (Subgroup.zpowers b) (Subgroup.zpowers c) a b c where
  mem₁ := Subgroup.mem_zpowers a
  mem₂ := Subgroup.mem_zpowers b
  mem₃ := Subgroup.mem_zpowers c
  central₁ := fun k hk => by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact (Commute.refl a).zpow_left n
  central₂ := fun k hk => by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact (Commute.refl b).zpow_left n
  central₃ := fun k hk => by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact (Commute.refl c).zpow_left n
  sq₁ := ha
  sq₂ := hb
  sq₃ := hc
  ne_one₁ := ha1
  ne_one₂ := hb1
  ne_one₃ := hc1
  comm₁₂ := fun x hx y hy => by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Commute.zpow_zpow hab n m
  comm₁₃ := fun x hx y hy => by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Commute.zpow_zpow hac n m
  comm₂₃ := fun x hx y hy => by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Commute.zpow_zpow hbc n m
  ne₁₂ := hne_ab
  ne₁₃ := hne_ac
  ne₂₃ := hne_bc

theorem images_ne_of_indepModOdd {Ω : Set (Subgroup G)} {n₁ n₂ : G} (h₁ : n₁ ∈ locLayer Ω z)
    (h₂ : n₂ ∈ locLayer Ω z) (hz : z ∈ locLayer Ω z) (h : IndepModOdd Ω z n₁ n₂) :
    locElt Ω z n₁ h₁ ≠ locElt Ω z z hz ∧ locElt Ω z n₂ h₂ ≠ locElt Ω z z hz ∧
      locElt Ω z n₁ h₁ ≠ locElt Ω z n₂ h₂ ∧
      locElt Ω z n₁ h₁ * locElt Ω z n₂ h₂ ≠ locElt Ω z z hz :=
  ⟨fun e => h.1 ((locElt_eq_iff h₁ hz).mp e), fun e => h.2.1 ((locElt_eq_iff h₂ hz).mp e),
    fun e => h.2.2.1 ((locElt_eq_iff h₁ h₂).mp e), fun e => h.2.2.2 (by
      rw [locElt_mul h₁ h₂] at e
      exact (locElt_eq_iff _ hz).mp e)⟩

theorem commutes_locImg_K_of_ne {ι : Type}
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z) (locFamily (conjClass3 K) z)) {i₀ : ι}
    (hi₀ : D.kind i₀ = CompData.sl23)
    (hKi₀ : locImg (conjClass3 K) z K = (D.hom i₀).range) (hKc : IsClassicalMember3 K z)
    (hKm : K ∈ centralizingMembers (conjClass3 K) {z})
    (hz : z ∈ locLayer (conjClass3 K) z) {N : Subgroup G} {n : G}
    (hN : N ∈ centralizingMembers (conjClass3 K) {z}) (hn : IsClassicalMember3 N n)
    (hne : locElt (conjClass3 K) z n (mem_locLayer_of_member hN hn) ≠
      locElt (conjClass3 K) z z hz) :
    Commutes (locImg (conjClass3 K) z K) (locImg (conjClass3 K) z N) := by
  obtain ⟨j, hj⟩ := Q3W.exists_range_of_mem3 D
    (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩ : locImg (conjClass3 K) z N ∈ locFamily (conjClass3 K) z)
  by_cases hji : j = i₀
  · exfalso
    subst hji
    have hNcard : Nat.card (locImg (conjClass3 K) z N) = 24 :=
      D.card_eq _ (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
    have hcard : Nat.card (D.hom j).range = 24 := by
      rw [← hKi₀]
      exact D.card_eq _ (mem_locFamily_iff.mpr ⟨K, hKm, rfl⟩)
    have heq : locImg (conjClass3 K) z N = (D.hom j).range :=
      Subgroup.eq_of_le_of_card_ge hj (by rw [hNcard, hcard])
    have hπn : locElt (conjClass3 K) z n (mem_locLayer_of_member hN hn) ∈ (D.hom j).range := by
      rw [← heq]
      exact locElt_mem_locImg (le_centralizingLayer hN) hn.mem
    have hπz : locElt (conjClass3 K) z z hz ∈ (D.hom j).range := by
      rw [← hKi₀]
      exact locElt_mem_locImg (le_centralizingLayer hKm) hKc.mem
    apply hne
    exact Q3NT.eq_of_involutions_of_kind_eq_sl23 (D.kind j) hi₀ (D.hom j) hcard hπn hπz
      (locElt_mul_self _ (mul_self_eq_one_of_member hn))
      (locElt_mul_self _ (mul_self_eq_one_of_member hKc))
      (fun e => by
        have := orderOf_locElt_of_member hN hn
        rw [e, orderOf_one] at this
        omega)
      (fun e => by
        have := orderOf_locElt (Ω := conjClass3 K) hz hKc.orderOf_eq_two
        rw [e, orderOf_one] at this
        omega)
  · exact commutes_locImg_of_ne D (Ne.symm hji) (le_of_eq hKi₀) hj

theorem mem_trivialOnQuot_of_uniq (hU : NTUniqPair3) (h : NTCommon3 K z) {M : Subgroup G} {m : G}
    (hM : M ∈ centralizingMembers (conjClass3 K) {z}) (hm : IsClassicalMember3 M m) {a : G}
    (ha : a ∈ locLayer (conjClass3 K) z) (hma : a * m = m * a)
    (hc : ∀ x ∈ M, ⁅a, x⁆ ∈ oddCoreIn (locLayer (conjClass3 K) z)) : a ∈ trivialOnQuot M := by
  have haC : a ∈ Subgroup.centralizer ({z} : Set G) := centralizingLayer_le_centralizer _ _ ha
  have hL : conjSub a M ∈ centralizingMembers (conjClass3 K) {z} :=
    conjSub_mem_centralizingMembers h.inClass.conjInvariant haC hM
  have hcls : IsClassicalMember3 (conjSub a M) m := by
    have h1 := hm.conj a
    have e : a * m * a⁻¹ = m := by
      rw [hma]
      group
    rwa [e] at h1
  have himg := locImg_conjSub_eq (le_centralizingLayer hM) ha hc
  have heq : conjSub a M = M := hU G K z h _ _ m hL hM hcls hm himg
  have hnorm : a ∈ Subgroup.normalizer (M : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  refine ⟨hnorm, fun x hx => ?_⟩
  have h1 : ⁅a, x⁆ ∈ M := by
    have e : ⁅a, x⁆ = (a * x * a⁻¹) * x⁻¹ := rfl
    rw [e]
    exact M.mul_mem ((Subgroup.mem_normalizer_iff.mp hnorm x).mp hx) (M.inv_mem hx)
  exact inf_oddCoreIn_le_oddCoreIn (le_centralizingLayer hM) ⟨h1, hc x hx⟩

theorem commutator_swap_mem {Ω : Set (Subgroup G)} {A B : Subgroup G}
    (hA : A ∈ centralizingMembers Ω {z}) (hB : B ∈ centralizingMembers Ω {z})
    (hc : Commutes (locImg Ω z A) (locImg Ω z B)) {x a : G} (hx : x ∈ A) (ha : a ∈ B) :
    ⁅a, x⁆ ∈ oddCoreIn (locLayer Ω z) := by
  have h1 := (commutes_locImg_iff hA hB).mp hc x hx a ha
  rw [← commutatorElement_inv]
  exact (oddCoreIn _).inv_mem h1

theorem mem_trivialOnQuot_self3 {M : Subgroup G} {m : G} (hm : IsClassicalMember3 M m) :
    m ∈ trivialOnQuot M :=
  mem_trivialOnQuot_of_centralizes fun _ hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le hm.subnormal hx)).symm

theorem mem_trivialOnQuot_of_member_le {Ω : Set (Subgroup G)} {M : Subgroup G}
    (hM : M ∈ centralizingMembers Ω {z}) : z ∈ trivialOnQuot M :=
  mem_trivialOnQuot_of_centralizes fun _ hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hM.2 hx)).symm

theorem fuzzyFrame3_of_fuzzyPair (hU : NTUniqPair3) (h : NTCommon3 K z) {N₁ N₂ : Subgroup G}
    {n₁ n₂ : G} (fp : FuzzyPair3 K z N₁ N₂ n₁ n₂) :
    ∃ A : Subgroup G, FuzzyFrame3 (conjClass3 K) A := by
  have hMFZ := RouteD.Gaps.fundNoncentral 3
  have hΩ := h.inClass
  have hz := h.mem_locLayer
  have hKm := h.mem_centralizingMembers
  have hz2 : z * z = 1 := mul_self_eq_one_of_member h.cls
  have hn₁2 := mul_self_eq_one_of_member fp.cls₁
  have hn₂2 := mul_self_eq_one_of_member fp.cls₂
  have hn₁Y := mem_locLayer_of_member fp.mem₁ fp.cls₁
  have hn₂Y := mem_locLayer_of_member fp.mem₂ fp.cls₂
  obtain ⟨hne₁, hne₂, hne₁₂, hne₁₂z⟩ := images_ne_of_indepModOdd hn₁Y hn₂Y hz fp.indep
  obtain ⟨ι, hι, ⟨D⟩⟩ := h.lieSystems {z} h.not_subset_center
  obtain ⟨i₀, hi₀, hKi₀⟩ := exists_kind_eq_sl23 hMFZ D hKm h.cls
  have hK₁ := commutes_locImg_K_of_ne D hi₀ hKi₀ h.cls hKm hz fp.mem₁ fp.cls₁ hne₁
  have hK₂ := commutes_locImg_K_of_ne D hi₀ hKi₀ h.cls hKm hz fp.mem₂ fp.cls₂ hne₂
  obtain ⟨o, ho, hoc⟩ := exists_conj_involution_commuting3
    (N := oddCoreIn (locLayer (conjClass3 K) z)) (F := Subgroup.zpowers n₁)
    (odd_card_oddCoreIn _) (Subgroup.zpowers_le.mpr (normalizer_oddCoreIn _ hn₁Y))
    (isPGroup_zpowers_of_sq_eq_one3 hn₁2) hn₂2 (fun x hx => by
      have hxN₁ : x ∈ N₁ := (Subgroup.zpowers_le.mpr fp.cls₁.mem) hx
      have hcm := (commutes_locImg_iff fp.mem₁ fp.mem₂).mp fp.commute x hxN₁ n₂ fp.cls₂.mem
      have e : n₂⁻¹ = n₂ := inv_eq_of_mul_eq_one_left hn₂2
      have e2 : ⁅x, n₂⁆ = (x * n₂ * x⁻¹) * n₂ := by rw [commutatorElement_def, e]
      rwa [e2] at hcm)
  have hoY : o ∈ locLayer (conjClass3 K) z := oddCoreIn_le _ ho
  have hoC : o ∈ Subgroup.centralizer ({z} : Set G) := centralizingLayer_le_centralizer _ _ hoY
  have hN₂'m : conjSub o N₂ ∈ centralizingMembers (conjClass3 K) {z} :=
    conjSub_mem_centralizingMembers hΩ.conjInvariant hoC fp.mem₂
  have hcls₂' : IsClassicalMember3 (conjSub o N₂) (o * n₂ * o⁻¹) := fp.cls₂.conj o
  have hoP : ∀ x ∈ locLayer (conjClass3 K) z,
      ⁅o, x⁆ ∈ oddCoreIn (locLayer (conjClass3 K) z) := fun x hx => by
    have e : ⁅o, x⁆ = o * (x * o⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact (oddCoreIn _).mul_mem ho (conj_mem_oddCoreIn hx ((oddCoreIn _).inv_mem ho))
  have himg₂' : locImg (conjClass3 K) z (conjSub o N₂) = locImg (conjClass3 K) z N₂ :=
    locImg_conjSub_eq (le_centralizingLayer fp.mem₂) hoY fun x hx =>
      hoP x (le_centralizingLayer fp.mem₂ hx)
  have hn₂'Y := mem_locLayer_of_member hN₂'m hcls₂'
  have hbar : locElt (conjClass3 K) z (o * n₂ * o⁻¹) hn₂'Y = locElt (conjClass3 K) z n₂ hn₂Y :=
    locElt_conj_eq hoY hn₂Y (hoP n₂ hn₂Y) hn₂'Y
  have hzn₁ : n₁ * z = z * n₁ := mul_comm_of_member fp.mem₁ fp.cls₁
  have hzn₂' : (o * n₂ * o⁻¹) * z = z * (o * n₂ * o⁻¹) := mul_comm_of_member hN₂'m hcls₂'
  have hn₁₂' : n₁ * (o * n₂ * o⁻¹) = (o * n₂ * o⁻¹) * n₁ := hoc n₁ (Subgroup.mem_zpowers n₁)
  have hind : IndepModOdd (conjClass3 K) z n₁ (o * n₂ * o⁻¹) :=
    indepModOdd_of_images hn₁Y hn₂'Y hz hne₁ (by rw [hbar]; exact hne₂)
      (by rw [hbar]; exact hne₁₂) (by rw [hbar]; exact hne₁₂z)
  obtain ⟨hnz₁, hnz₂, hn₁₂ne, hn₁₂z⟩ := hind.ne
  have hc₁₂' : Commutes (locImg (conjClass3 K) z N₁) (locImg (conjClass3 K) z (conjSub o N₂)) := by
    rw [himg₂']
    exact fp.commute
  have hK₂' : Commutes (locImg (conjClass3 K) z K) (locImg (conjClass3 K) z (conjSub o N₂)) := by
    rw [himg₂']
    exact hK₂
  have hKn₁ : n₁ ∈ trivialOnQuot K :=
    mem_trivialOnQuot_of_uniq hU h hKm h.cls hn₁Y hzn₁ fun x hx =>
      commutator_swap_mem hKm fp.mem₁ hK₁ hx fp.cls₁.mem
  have hKn₂ : o * n₂ * o⁻¹ ∈ trivialOnQuot K :=
    mem_trivialOnQuot_of_uniq hU h hKm h.cls hn₂'Y hzn₂' fun x hx =>
      commutator_swap_mem hKm hN₂'m hK₂' hx hcls₂'.mem
  have hN₁n₂ : o * n₂ * o⁻¹ ∈ trivialOnQuot N₁ :=
    mem_trivialOnQuot_of_uniq hU h fp.mem₁ fp.cls₁ hn₂'Y hn₁₂'.symm fun x hx =>
      commutator_swap_mem fp.mem₁ hN₂'m hc₁₂' hx hcls₂'.mem
  have hN₂n₁ : n₁ ∈ trivialOnQuot (conjSub o N₂) :=
    mem_trivialOnQuot_of_uniq hU h hN₂'m hcls₂' hn₁Y hn₁₂' fun x hx =>
      (commutes_locImg_iff fp.mem₁ hN₂'m).mp hc₁₂' n₁ fp.cls₁.mem x hx
  have T := exactTriple_zpowers (a := n₁) (b := o * n₂ * o⁻¹) (c := z) hn₁2
    (mul_self_eq_one_of_member hcls₂') hz2 fp.cls₁.ne_one hcls₂'.ne_one h.cls.ne_one hn₁₂' hzn₁
    hzn₂' hn₁₂ne hnz₁ hnz₂
  have hrange : Set.range ![n₁, o * n₂ * o⁻¹, z] = ({n₁, o * n₂ * o⁻¹, z} : Set G) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  have hAle : ∀ M : Subgroup G, n₁ ∈ trivialOnQuot M → o * n₂ * o⁻¹ ∈ trivialOnQuot M →
      z ∈ trivialOnQuot M → T.group ≤ trivialOnQuot M := fun M h1 h2 h3 => by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [h1, h2, h3]
  refine ⟨T.group, ![N₁, conjSub o N₂, K], ![n₁, o * n₂ * o⁻¹, z], ?_, ?_, T.isElemAbelian,
    T.card_eq_eight hn₁₂z, ?_⟩
  · intro i
    fin_cases i
    exacts [⟨fp.mem₁.1, fp.cls₁⟩, ⟨hN₂'m.1, hcls₂'⟩, ⟨hKm.1, h.cls⟩]
  · rw [hrange]
    rfl
  · intro i
    fin_cases i
    · exact hAle N₁ (mem_trivialOnQuot_self3 fp.cls₁) hN₁n₂ (mem_trivialOnQuot_of_member_le fp.mem₁)
    · exact hAle _ hN₂n₁ (mem_trivialOnQuot_self3 hcls₂') (mem_trivialOnQuot_of_member_le hN₂'m)
    · exact hAle K hKn₁ hKn₂ (mem_trivialOnQuot_self3 h.cls)

theorem ntFuzzyTriple3_of_uniq_ff (hU : NTUniqPair3) (hF : NTFuzzyFrameTriple3) :
    NTFuzzyTriple3 := by
  intro G _ _ _ K z h N₁ N₂ n₁ n₂ fp
  obtain ⟨A, hA⟩ := fuzzyFrame3_of_fuzzyPair hU h fp
  exact hF G K z h A hA

theorem ntNoCommImages3_of_uniq_ff (hU : NTUniqPair3) (hF : NTFuzzyFrameTriple3) :
    NTNoCommImages3 :=
  ntNoCommImages3_of_fuzzyTriple3 (ntFuzzyTriple3_of_uniq_ff hU hF)

end Frame3

end CFSG.ClassicalInvolution.Q3.Q3NS
