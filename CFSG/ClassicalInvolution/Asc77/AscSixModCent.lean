module

public import CFSG.ClassicalInvolution.Asc77.ModOApi

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_oddCoreOf_of_mem_normalizer {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ oddCoreOf K) :
    g * x * g⁻¹ ∈ oddCoreOf K := by
  obtain ⟨n, hn, rfl⟩ := hx
  set α : MulAut ↥K := K.normalizerMonoidHom ⟨g, hg⟩ with hα
  have hαN : (classicalInvolutionOddCore ↥K).map (α : ↥K →* ↥K) =
      classicalInvolutionOddCore ↥K :=
    CFSG.ComponentClassification.OddCore.equiv_invariant (α : ↥K ≃* ↥K)
  have hmem : α n ∈ classicalInvolutionOddCore ↥K := hαN ▸ Subgroup.mem_map_of_mem _ hn
  refine ⟨α n, hmem, ?_⟩
  rw [hα]
  simp

theorem mem_normalizer_oddCore_of_mem_normalizer {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (oddCoreOf K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => mem_normalizer_oddCoreOf_of_mem_normalizer hg hx, fun hx => ?_⟩
  have := mem_normalizer_oddCoreOf_of_mem_normalizer ((Subgroup.normalizer _).inv_mem hg) hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at this

theorem mem_normalizer_of_forall_commutator_mem [Finite G] {K : Subgroup G} {g : G}
    (h : ∀ k ∈ K, ⁅g, k⁆ ∈ K) : g ∈ Subgroup.normalizer (K : Set G) := by
  have hle : conjSub g K ≤ K := by
    intro y hy
    rw [mem_conjSub_iff] at hy
    have h1 := K.mul_mem (h _ hy) hy
    have e : ⁅g, g⁻¹ * y * g⁆ * (g⁻¹ * y * g) = y := by
      rw [commutatorElement_def]
      group
    rwa [e] at h1
  have hcard : Nat.card (conjSub g K) = Nat.card K :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  exact mem_normalizer_iff_conjSub_eq.mpr
    (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]))

theorem le_normalizer_of_commutator_le_oddCoreOf {K J : Subgroup G} (h : ⁅J, K⁆ ≤ oddCoreOf K) :
    J ≤ Subgroup.normalizer (K : Set G) := by
  have key : ∀ j ∈ J, ∀ k ∈ K, j * k * j⁻¹ ∈ K := by
    intro j hj k hk
    have h1 : ⁅j, k⁆ ∈ oddCoreOf K := h (Subgroup.commutator_mem_commutator hj hk)
    have e : j * k * j⁻¹ = ⁅j, k⁆ * k := by rw [commutatorElement_def]; group
    rw [e]
    exact K.mul_mem (oddCoreOf_le_self K h1) hk
  intro j hj
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨fun hk => key j hj k hk, fun hk => ?_⟩
  have := key j⁻¹ (J.inv_mem hj) _ hk
  have e : j⁻¹ * (j * k * j⁻¹) * j⁻¹⁻¹ = k := by group
  rwa [e] at this

@[expose] def centModOddCore [Finite G] (K : Subgroup G) : Subgroup G where
  carrier := {g | ∀ k ∈ K, ⁅g, k⁆ ∈ oddCoreOf K}
  one_mem' := fun k _ => by simp [commutatorElement_def]
  mul_mem' := by
    intro g h hg hh k hk
    have hgN : g ∈ Subgroup.normalizer (K : Set G) :=
      mem_normalizer_of_forall_commutator_mem fun k hk => oddCoreOf_le_self K (hg k hk)
    have h1 : g * ⁅h, k⁆ * g⁻¹ ∈ oddCoreOf K :=
      mem_normalizer_oddCoreOf_of_mem_normalizer hgN (hh k hk)
    have e : ⁅g * h, k⁆ = (g * ⁅h, k⁆ * g⁻¹) * ⁅g, k⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (oddCoreOf K).mul_mem h1 (hg k hk)
  inv_mem' := by
    intro g hg k hk
    have hgN : g ∈ Subgroup.normalizer (K : Set G) :=
      mem_normalizer_of_forall_commutator_mem fun k hk => oddCoreOf_le_self K (hg k hk)
    have h1 : g⁻¹ * ⁅g, k⁆⁻¹ * g⁻¹⁻¹ ∈ oddCoreOf K :=
      mem_normalizer_oddCoreOf_of_mem_normalizer ((Subgroup.normalizer _).inv_mem hgN)
        ((oddCoreOf K).inv_mem (hg k hk))
    have e : ⁅g⁻¹, k⁆ = g⁻¹ * ⁅g, k⁆⁻¹ * g⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact h1

theorem mem_centModOddCore_iff [Finite G] {K : Subgroup G} {g : G} :
    g ∈ centModOddCore K ↔ ∀ k ∈ K, ⁅g, k⁆ ∈ oddCoreOf K := Iff.rfl

theorem exists_isPGroup_zpowers_lift {H H' : Type*} [Group H] [Group H'] [Finite H]
    (φ : H →* H') (hφ : Function.Surjective φ) {b : H'} (hb : IsPGroup 2 (Subgroup.zpowers b)) :
    ∃ a : H, φ a = b ∧ IsPGroup 2 (Subgroup.zpowers a) := by
  have : Finite H' := Finite.of_surjective φ hφ
  obtain ⟨n, hn⟩ := hb.exists_card_eq
  rw [Nat.card_zpowers] at hn
  obtain ⟨a₀, rfl⟩ := hφ b
  obtain ⟨i, r, hr, hor⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf a₀) (orderOf_pos a₀).ne'
  have hr2 : Nat.Coprime 2 r := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
    (by rintro ⟨c, hc⟩; obtain ⟨d, hd⟩ := hr; omega)
  have hcop : Nat.Coprime r (2 ^ n) := (Nat.Coprime.pow_left n hr2).symm
  obtain ⟨s, hs0, hs1⟩ := Nat.chineseRemainder hcop 0 1
  obtain ⟨c, hc⟩ : r ∣ s := Nat.modEq_zero_iff_dvd.mp hs0
  refine ⟨a₀ ^ s, ?_, ?_⟩
  · rw [map_pow]
    have h1 : (φ a₀) ^ s = (φ a₀) ^ (s % orderOf (φ a₀)) := (pow_mod_orderOf _ _).symm
    have h2 : s % orderOf (φ a₀) = 1 % orderOf (φ a₀) := by rw [hn]; exact hs1
    rw [h1, h2, pow_mod_orderOf, pow_one]
  · have h3 : (a₀ ^ s) ^ 2 ^ i = 1 := by
      rw [← pow_mul, hc]
      have : r * c * 2 ^ i = orderOf a₀ * c := by rw [hor]; ring
      rw [this, pow_mul, pow_orderOf_eq_one, one_pow]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h3)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem padicValNat_natCard_le_one_of_forall_isPGroup {H : Type*} [Group H] [Finite H]
    {L : Subgroup H} {z : H}
    (h : ∀ x ∈ L, IsPGroup 2 (Subgroup.zpowers x) → x = 1 ∨ x = z) :
    padicValNat 2 (Nat.card L) ≤ 1 := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥L) := inferInstance
  have hP := Sylow.card_eq_multiplicity P
  have hAcard : Nat.card ((P : Subgroup ↥L).map L.subtype) = Nat.card ↥(P : Subgroup ↥L) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hA2 : ∀ x ∈ (P : Subgroup ↥L).map L.subtype, x = 1 ∨ x = z := by
    intro x hx
    have hxL : x ∈ L := by
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    exact h x hxL ((P.isPGroup'.map _).to_le (Subgroup.zpowers_le.mpr hx))
  have hle2 := natCard_subgroup_le_two_of_subset hA2
  rw [hAcard, hP] at hle2
  have hv : (Nat.card L).factorization 2 ≤ 1 := by
    by_contra hgt
    push Not at hgt
    have : 2 ^ 2 ≤ 2 ^ (Nat.card L).factorization 2 := Nat.pow_le_pow_right (by norm_num) hgt
    omega
  rwa [Nat.factorization_def _ Nat.prime_two] at hv

theorem le_of_forall_isSylow2In_of_isPerfect [Finite G] {J M : Subgroup G}
    (hperf : Group.IsPerfect ↥J) (hM : ∀ V : Subgroup G, IsSylow2In V J → V ≤ M) : J ≤ M := by
  obtain ⟨Q₀⟩ : Nonempty (Sylow 2 ↥J) := inferInstance
  set V₀ : Subgroup G := (Q₀ : Subgroup ↥J).map J.subtype with hV₀def
  have hV₀ : IsSylow2In V₀ J := isSylow2In_map_sylow J Q₀
  have hV₀sub : V₀.subgroupOf J = (Q₀ : Subgroup ↥J) :=
    Subgroup.comap_map_eq_self_of_injective J.subtype_injective _
  set N : Subgroup ↥J := Subgroup.normalClosure ((V₀.subgroupOf J : Subgroup ↥J) : Set ↥J) with hN
  have hNn : N.Normal := Subgroup.normalClosure_normal
  have hle : N ≤ M.subgroupOf J := by
    refine (Subgroup.closure_le (M.subgroupOf J)).mpr fun a ha => ?_
    obtain ⟨b, hb, hab⟩ := Group.mem_conjugatesOfSet_iff.mp ha
    obtain ⟨c, hc⟩ := isConj_iff.mp hab
    have hae : (a : G) = (c : G) * (b : G) * (c : G)⁻¹ := by rw [← hc]; rfl
    have hmem : (a : G) ∈ conjSub (c : G) V₀ := by
      rw [hae]
      exact conj_mem_conjSub hb
    have hsyl : IsSylow2In (conjSub (c : G) V₀) J := by
      have := IsSylow2In.conj hV₀ (c : G)
      rwa [conjSub_eq_self_of_mem c.2] at this
    exact hM _ hsyl hmem
  have hodd : Odd (Nat.card (↥J ⧸ N)) := by
    have h1 : N.index ∣ (Q₀ : Subgroup ↥J).index := by
      refine Subgroup.index_dvd_of_le ?_
      rw [← hV₀sub]
      exact fun x hx => Subgroup.subset_normalClosure hx
    have h2 : Odd (Q₀ : Subgroup ↥J).index := by
      rcases Nat.even_or_odd (Q₀ : Subgroup ↥J).index with h | h
      · exact absurd (even_iff_two_dvd.mp h) (Sylow.not_dvd_index Q₀)
      · exact h
    rw [← Subgroup.index_eq_card]
    exact h2.of_dvd_nat h1
  have hsolv : Group.IsSolvable (↥J ⧸ N) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Group.IsPerfect ↥J := hperf
  have : Group.IsPerfect (↥J ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hsub : Subsingleton (↥J ⧸ N) := by
    by_contra hns
    have : Nontrivial (↥J ⧸ N) := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isSolvable (↥J ⧸ N) hsolv
  have hidx : N.index = 1 := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
  have htop : N = ⊤ := Subgroup.index_eq_one.mp hidx
  intro j hj
  have hjN : (⟨j, hj⟩ : ↥J) ∈ N := by rw [htop]; exact Subgroup.mem_top _
  exact hle hjN

theorem mem_of_isPGroup_of_mem_sup_of_odd {H : Type*} [Group H] [Finite H] {A O : Subgroup H}
    [A.Normal] (hO : Odd (Nat.card O)) {v : H} (hv : IsPGroup 2 (Subgroup.zpowers v))
    (hvAO : v ∈ A ⊔ O) : v ∈ A := by
  have hmap : (A ⊔ O).map (QuotientGroup.mk' A) = O.map (QuotientGroup.mk' A) := by
    rw [Subgroup.map_sup, (QuotientGroup.map_mk'_self A), bot_sup_eq]
  obtain ⟨o, ho, hov⟩ : QuotientGroup.mk' A v ∈ O.map (QuotientGroup.mk' A) :=
    hmap ▸ Subgroup.mem_map_of_mem _ hvAO
  obtain ⟨n, hn⟩ := hv.exists_card_eq
  rw [Nat.card_zpowers] at hn
  have h1 : orderOf (QuotientGroup.mk' A v) ∣ 2 ^ n := hn ▸ orderOf_map_dvd _ v
  have h2 : orderOf (QuotientGroup.mk' A v) ∣ Nat.card O := by
    rw [← hov]
    exact (orderOf_map_dvd _ o).trans (Subgroup.orderOf_dvd_natCard O ho)
  have h3 : Odd (orderOf (QuotientGroup.mk' A v)) := hO.of_dvd_nat h2
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hi0 : i = 0 := by
    by_contra h
    rw [hi] at h3
    exact (Nat.not_even_iff_odd.mpr h3) (Nat.even_pow.mpr ⟨even_two, h⟩)
  rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
  exact (QuotientGroup.eq_one_iff v).mp hi

theorem inf_le_oddCoreOf_of_le_normalizer [Finite G] {K X : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (X : Set G)) (hodd : Odd (Nat.card ↥(X ⊓ K))) :
    K ⊓ X ≤ oddCoreOf K := by
  have hN : (X.subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hK g.2) n).mp hn
  have hcard : Nat.card (X.subgroupOf K) = Nat.card ↥(X ⊓ K) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hle : X.subgroupOf K ≤ classicalInvolutionOddCore ↥K :=
    le_sSup ⟨hN, by rw [hcard]; exact hodd⟩
  intro x hx
  exact mem_oddCoreOf_iff.mpr ⟨hx.1, hle (show (⟨x, hx.1⟩ : ↥K) ∈ X.subgroupOf K from hx.2)⟩

end CFSG.ClassicalInvolution.Asc77
