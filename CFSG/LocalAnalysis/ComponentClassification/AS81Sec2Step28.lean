module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step26V

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

namespace Sec2

section Count

variable {S Z : Subgroup G} (hS : Special S Z)
include hS

omit [Finite G] in
theorem card_abelianization_mul : Nat.card (Abelianization ↥S) * Nat.card Z = Nat.card S := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator ↥S)
  have h2 : Nat.card (commutator ↥S) = Nat.card Z := by
    rw [← Subgroup.card_map_of_injective (K := commutator ↥S) S.subtype_injective,
      _root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype,
      hS.comm]
  rw [← h2]
  exact h1.symm

theorem card_commutator_mul_card_le {d : G} (hd : d ∈ normalizer (S : Set G)) {C : Subgroup G}
    (hZC : Z ≤ C) (hCS : C ≤ S) (hC : ∀ c ∈ C, c⁻¹ * (d * c * d⁻¹) ∈ Z) :
    Nat.card (⁅S, zpowers d⁆ ⊔ Z : Subgroup G) * Nat.card C ≤ Nat.card S * Nat.card Z := by
  set Q := Abelianization ↥S
  let F : Q →* Q := (MonoidHom.id Q)⁻¹ * abelConj d hd
  have hF : ∀ m, F m = m⁻¹ * abelConj d hd m := fun m => rfl
  set W : Subgroup G := (F.range.comap Abelianization.of).map S.subtype with hWdef
  have hmemW : ∀ {s : G} (hs : s ∈ S), Abelianization.of (⟨s, hs⟩ : ↥S) ∈ F.range → s ∈ W :=
    fun {s} hs h => ⟨⟨s, hs⟩, h, rfl⟩
  have hWS : W ≤ S := map_subtype_le _
  have hFc : ∀ m, abelConj d hd (F m) = F (abelConj d hd m) := fun m => by
    rw [hF, hF, map_mul, map_inv]
  have hWd : ∀ w ∈ W, d * w * d⁻¹ ∈ W := by
    rintro _ ⟨x, ⟨m, hm⟩, rfl⟩
    show d * (x : G) * d⁻¹ ∈ W
    have hx : d * (x : G) * d⁻¹ ∈ S := (mem_normalizer_iff.mp hd x).mp x.2
    refine hmemW hx ⟨abelConj d hd m, ?_⟩
    have e : (⟨d * (x : G) * d⁻¹, hx⟩ : ↥S) = conjS d hd x := rfl
    rw [e, ← abelConj_of hd, ← hFc, hm]
  have hcomm1 : ∀ s ∈ S, s * d * s⁻¹ * d⁻¹ ∈ W := fun s hs => by
    have hx : s * d * s⁻¹ * d⁻¹ ∈ S := by
      have h1 : d * s⁻¹ * d⁻¹ ∈ S := (mem_normalizer_iff.mp hd s⁻¹).mp (inv_mem hs)
      have e : s * d * s⁻¹ * d⁻¹ = s * (d * s⁻¹ * d⁻¹) := by group
      rw [e]
      exact mul_mem hs h1
    refine hmemW hx ⟨(Abelianization.of (⟨s, hs⟩ : ↥S))⁻¹, ?_⟩
    rw [hF, inv_inv, ← map_inv, abelConj_of, ← map_mul]
    congr 1
    exact Subtype.ext (by simp only [Subgroup.coe_mul, coe_conjS, Subgroup.coe_inv]; group)
  have hcommn : ∀ n : ℕ, ∀ s ∈ S, s * d ^ n * s⁻¹ * (d ^ n)⁻¹ ∈ W := by
    intro n
    induction n with
    | zero => intro s _; simp
    | succ n ih =>
      intro s hs
      have e : s * d ^ (n + 1) * s⁻¹ * (d ^ (n + 1))⁻¹ =
          (s * d * s⁻¹ * d⁻¹) * (d * (s * d ^ n * s⁻¹ * (d ^ n)⁻¹) * d⁻¹) := by
        rw [pow_succ']
        group
      rw [e]
      exact mul_mem (hcomm1 s hs) (hWd _ (ih s hs))
  have hZW : Z ≤ W := fun z hz => hmemW (hS.le hz) ⟨1, by
    rw [map_one]
    exact ((abel_of_eq_one_iff hS).mpr hz).symm⟩
  have hle : ⁅S, zpowers d⁆ ⊔ Z ≤ W := by
    refine sup_le ?_ hZW
    rw [Subgroup.commutator_le]
    intro s hs t ht
    rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at ht
    obtain ⟨n, rfl⟩ := ht
    rw [commutatorElement_def]
    exact hcommn n s hs
  have hcardW : Nat.card W = Nat.card F.range * Nat.card Z := by
    rw [hWdef, Subgroup.card_map_of_injective S.subtype_injective,
      CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.card_comap_of_surjective
        (f := Abelianization.of) (fun x => QuotientGroup.mk_surjective x),
      Abelianization.ker_of]
    congr 1
    rw [← Subgroup.card_map_of_injective (K := commutator ↥S) S.subtype_injective,
      _root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype,
      hS.comm]
  have hker : (C.subgroupOf S).map Abelianization.of ≤ F.ker := by
    rintro _ ⟨c, hc, rfl⟩
    rw [MonoidHom.mem_ker, hF, abelConj_of, inv_mul_eq_one, abel_of_eq_of_iff hS]
    exact hC c (mem_subgroupOf.mp hc)
  have hcardC : Nat.card ((C.subgroupOf S).map Abelianization.of) * Nat.card Z = Nat.card C := by
    let ψ : ↥(C.subgroupOf S) →* Abelianization ↥S :=
      (Abelianization.of : ↥S →* Abelianization ↥S).comp (C.subgroupOf S).subtype
    have hrange : ψ.range = (C.subgroupOf S).map Abelianization.of := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_map, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    have hkerψ : Nat.card ψ.ker = Nat.card Z := by
      have hle' : commutator ↥S ≤ C.subgroupOf S := fun x hx => by
        rw [mem_subgroupOf]
        exact hZC (hS.comm ▸ (mem_commutator_iff_mem x).mp hx)
      have e : ψ.ker = (commutator ↥S).subgroupOf (C.subgroupOf S) := by
        ext x
        rw [MonoidHom.mem_ker, mem_subgroupOf]
        show Abelianization.of (x : ↥S) = 1 ↔ _
        rw [← MonoidHom.mem_ker, Abelianization.ker_of]
      rw [e, Nat.card_congr (subgroupOfEquivOfLe hle').toEquiv,
        ← Subgroup.card_map_of_injective (K := commutator ↥S) S.subtype_injective,
        _root_.commutator_def,
        Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hS.comm]
    have h1 := Subgroup.card_ker_mul_card_range ψ
    rw [hrange, hkerψ, Nat.card_congr (subgroupOfEquivOfLe hCS).toEquiv] at h1
    rw [mul_comm]
    exact h1
  have hrk := Subgroup.card_ker_mul_card_range F
  have h3 := Subgroup.card_le_of_le hle
  have h4 := Subgroup.card_le_of_le hker
  have h5 := card_abelianization_mul hS
  rw [hcardW] at h3
  calc Nat.card (⁅S, zpowers d⁆ ⊔ Z : Subgroup G) * Nat.card C
      ≤ (Nat.card F.range * Nat.card Z) * Nat.card C := Nat.mul_le_mul_right _ h3
    _ = (Nat.card F.range * Nat.card Z) *
        (Nat.card ((C.subgroupOf S).map Abelianization.of) * Nat.card Z) := by rw [hcardC]
    _ ≤ (Nat.card F.range * Nat.card Z) * (Nat.card F.ker * Nat.card Z) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h4)
    _ = (Nat.card F.ker * Nat.card F.range) * Nat.card Z * Nat.card Z := by ring
    _ = Nat.card S * Nat.card Z := by rw [hrk, ← h5]

end Count

section Offender

variable {S Z T₀ : Subgroup G} (hS : Special S Z)
  (hc1 : ∀ s ∈ S, s ∉ Z → {c | ∃ t ∈ S, c = s⁻¹ * t⁻¹ * s * t} = (Z : Set G))
  (hc6 : IsSylowOf 2 S (centralizerMod (normalizer (S : Set G)) S Z))
  (hT₀ : IsSylowOf 2 T₀ (normalizer (S : Set G)))
include hS hc6 hT₀

omit hS in
theorem le_of_isSylowOf_normalizer : S ≤ T₀ :=
  le_of_isSylowOf_of_le_normalizer hT₀ hc6.isPGroup le_normalizer le_rfl

theorem mem_of_forall_inv_mul_conj_mem {t : G} (ht : t ∈ T₀)
    (hts : ∀ s ∈ S, s⁻¹ * (t * s * t⁻¹) ∈ Z) : t ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hST₀ := le_of_isSylowOf_normalizer hc6 hT₀
  have htN : t ∈ normalizer (S : Set G) := hT₀.le ht
  have htZ : t ∈ normalizer (Z : Set G) := by
    rw [← hS.center]
    exact mem_normalizer_centerIn htN
  have htC : t ∈ centralizerMod (normalizer (S : Set G)) S Z := by
    refine ⟨htN, htZ, fun y hy => ?_⟩
    have hy' : t⁻¹ * y * t ∈ S := by
      have := (mem_normalizer_iff.mp (inv_mem htN) y).mp hy
      simpa using this
    have h1 := hts _ hy'
    have e : y⁻¹ * t⁻¹ * y * t = ((t⁻¹ * y * t)⁻¹ * (t * (t⁻¹ * y * t) * t⁻¹))⁻¹ := by group
    rw [e]
    exact inv_mem h1
  have h2 : IsPGroup 2 (zpowers t ⊔ S : Subgroup G) :=
    hT₀.isPGroup.to_le (sup_le (zpowers_le.mpr ht) hST₀)
  have h3 := hc6.eq_of_le le_sup_right (sup_le (zpowers_le.mpr htC) hc6.le) h2
  rw [← h3]
  exact mem_sup_left (mem_zpowers t)

theorem centerIn_le_of_isSylowOf : centerIn T₀ ≤ Z := fun z hz => by
  have hST₀ := le_of_isSylowOf_normalizer hc6 hT₀
  have hzS : z ∈ S := mem_of_forall_inv_mul_conj_mem hS hc6 hT₀ hz.1 fun s hs => by
    have h1 : s * z = z * s := mem_centralizer_iff.mp hz.2 s (hST₀ hs)
    have e : s⁻¹ * (z * s * z⁻¹) = 1 := by rw [← h1, mul_inv_cancel_right, inv_mul_cancel]
    rw [e]
    exact one_mem _
  rw [← hS.center]
  exact ⟨hzS, mem_centralizer_iff.mpr fun s hs => mem_centralizer_iff.mp hz.2 s (hST₀ hs)⟩

include hc1 in
theorem mem_of_forall_mem_centerIn {x : G} (hx : x ∈ T₀) (hZ₀ : ¬ Z ≤ centerIn T₀)
    (hxc : ∀ t ∈ T₀, x⁻¹ * (t * x * t⁻¹) ∈ centerIn T₀) : x ∈ Z := by
  have hST₀ := le_of_isSylowOf_normalizer hc6 hT₀
  have hZT₀ := centerIn_le_of_isSylowOf hS hc6 hT₀
  have hN : ∀ y ∈ T₀, y ∈ normalizer (centerIn T₀ : Set G) := fun y hy =>
    mem_normalizer_centerIn (le_normalizer hy)
  have hxS : x ∈ S := mem_of_forall_inv_mul_conj_mem hS hc6 hT₀ hx fun s hs => by
    have hc := inv_mem (hxc s (hST₀ hs))
    have e1 : s⁻¹ * (x * s * x⁻¹) =
        x * (s⁻¹ * (x⁻¹ * (s * x * s⁻¹))⁻¹ * s⁻¹⁻¹) * x⁻¹ := by group
    rw [e1]
    have h1 := (mem_normalizer_iff.mp (hN s⁻¹ (inv_mem (hST₀ hs))) _).mp hc
    exact hZT₀ ((mem_normalizer_iff.mp (hN x hx) _).mp h1)
  by_contra hxZ
  apply hZ₀
  intro z hz
  have hz' : z ∈ (Z : Set G) := hz
  rw [← hc1 x hxS hxZ] at hz'
  obtain ⟨t, ht, rfl⟩ := hz'
  have := hxc t⁻¹ (hST₀ (inv_mem ht))
  simpa [mul_assoc] using this

omit hc6 in
theorem eq_of_le_of_card_le
    (ha : ∀ t ∈ normalizer (S : Set G), t ∉ S → t * t ∈ S →
      16 ≤ Nat.card (⁅S, zpowers t⁆ ⊔ Z : Subgroup G))
    (hb : ∀ D : Subgroup G, D ≤ normalizer (S : Set G) →
      (∀ a ∈ D, ∀ b ∈ D, a * a ∈ S ∧ a * b * a⁻¹ * b⁻¹ ∈ S) →
      4 ≤ (D ⊓ S).relIndex D → ∃ d ∈ D, 64 ≤ Nat.card (⁅S, zpowers d⁆ ⊔ Z : Subgroup G))
    (hcc : ∀ D : Subgroup G, D ≤ normalizer (S : Set G) →
      (∀ a ∈ D, ∀ b ∈ D, a * a ∈ S ∧ a * b * a⁻¹ * b⁻¹ ∈ S) → (D ⊓ S).relIndex D ≤ 8)
    {U : Subgroup G} (hZU : Z ≤ U) (hUT : U ≤ T₀)
    (hUe : ∀ a ∈ U, ∀ b ∈ U, a * a ∈ Z ∧ a * b * a⁻¹ * b⁻¹ ∈ Z)
    (hcard : Nat.card S ≤ Nat.card U) : U = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUN : U ≤ normalizer (S : Set G) := hUT.trans hT₀.le
  have hZS : Z ≤ S := hS.le
  have hUe' : ∀ a ∈ U, ∀ b ∈ U, a * a ∈ S ∧ a * b * a⁻¹ * b⁻¹ ∈ S := fun a ha b hb =>
    ⟨hZS (hUe a ha b hb).1, hZS (hUe a ha b hb).2⟩
  have hcount : ∀ d ∈ U, Nat.card (⁅S, zpowers d⁆ ⊔ Z : Subgroup G) *
      Nat.card (U ⊓ S : Subgroup G) ≤ Nat.card S * Nat.card Z := fun d hd =>
    card_commutator_mul_card_le hS (hUN hd) (le_inf hZU hZS) inf_le_right fun c hc => by
      have := (hUe c⁻¹ (inv_mem hc.1) d hd).2
      simpa [mul_assoc] using this
  have hk : (U ⊓ S).relIndex U * Nat.card (U ⊓ S : Subgroup G) = Nat.card U := by
    have h := relIndex_mul_card (U ⊓ S) U
    rwa [inf_right_comm, inf_idem] at h
  have hcpos : 0 < Nat.card (U ⊓ S : Subgroup G) := Nat.card_pos
  have hZ4 := hS.card
  by_cases hk1 : (U ⊓ S).relIndex U = 1
  · have hUS : U ≤ S := fun u hu => (relIndex_eq_one.mp hk1 hu).2
    exact Subgroup.eq_of_le_of_card_ge hUS hcard
  exfalso
  obtain ⟨d₀, hd₀U, hd₀S⟩ : ∃ d ∈ U, d ∉ S := by
    by_contra hall
    push Not at hall
    exact hk1 (relIndex_eq_one.mpr fun u hu => ⟨hu, hall u hu⟩)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (U ⊓ S).relIndex U = 2 ^ m := by
    obtain ⟨n, hn⟩ := (hT₀.isPGroup.to_le hUT).exists_card_eq
    have hdvd : (U ⊓ S).relIndex U ∣ 2 ^ n := hn ▸ relIndex_dvd_card _ _
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨m, hm⟩
  have hk8 := hcc U hUN hUe'
  have hm0 : m ≠ 0 := fun h => hk1 (by rw [hm, h, pow_zero])
  by_cases hm1 : m = 1
  · have h16 := ha d₀ (hUN hd₀U) hd₀S (hUe' d₀ hd₀U d₀ hd₀U).1
    have hc := hcount d₀ hd₀U
    rw [hm, hm1, pow_one] at hk
    have h1 : Nat.card (⁅S, zpowers d₀⁆ ⊔ Z : Subgroup G) * Nat.card (U ⊓ S : Subgroup G) ≤
        8 * Nat.card (U ⊓ S : Subgroup G) := by
      calc _ ≤ Nat.card S * Nat.card Z := hc
        _ ≤ Nat.card U * 4 := by rw [hZ4]; exact Nat.mul_le_mul_right _ hcard
        _ = 8 * Nat.card (U ⊓ S : Subgroup G) := by rw [← hk]; ring
    have h2 := Nat.le_of_mul_le_mul_right h1 hcpos
    omega
  · have hk4 : 4 ≤ (U ⊓ S).relIndex U := by
      rw [hm]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨d, hdU, h64⟩ := hb U hUN hUe' hk4
    have hc := hcount d hdU
    have h1 : Nat.card (⁅S, zpowers d⁆ ⊔ Z : Subgroup G) * Nat.card (U ⊓ S : Subgroup G) ≤
        32 * Nat.card (U ⊓ S : Subgroup G) := by
      calc _ ≤ Nat.card S * Nat.card Z := hc
        _ ≤ Nat.card U * 4 := by rw [hZ4]; exact Nat.mul_le_mul_right _ hcard
        _ = (U ⊓ S).relIndex U * 4 * Nat.card (U ⊓ S : Subgroup G) := by rw [← hk]; ring
        _ ≤ 8 * 4 * Nat.card (U ⊓ S : Subgroup G) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hk8)
        _ = 32 * Nat.card (U ⊓ S : Subgroup G) := by ring
    have h2 := Nat.le_of_mul_le_mul_right h1 hcpos
    omega

theorem centerIn_ne_bot_of_isSylowOf : centerIn T₀ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hST₀ := le_of_isSylowOf_normalizer hc6 hT₀
  have hT₀1 : T₀ ≠ ⊥ := fun h => by
    have h1 : Z ≤ (⊥ : Subgroup G) := h ▸ hS.le.trans hST₀
    have h2 := Subgroup.card_le_of_le h1
    rw [hS.card, card_bot] at h2
    omega
  have : Nontrivial ↥T₀ := (Subgroup.nontrivial_iff_ne_bot T₀).mpr hT₀1
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (IsPGroup.bot_lt_center hT₀.isPGroup).ne'
  intro hbot
  apply hz1
  have hzc : (z : G) ∈ centerIn T₀ := ⟨z.2, mem_centralizer_iff.mpr fun t ht =>
    congrArg Subtype.val (mem_center_iff.mp hz ⟨t, ht⟩)⟩
  rw [hbot, mem_bot] at hzc
  exact Subtype.ext (Subtype.ext hzc)

include hc1 in
theorem mem_normalizer_of_mem_normalizer {g : G} (hg : g ∈ normalizer (T₀ : Set G)) :
    g ∈ normalizer (Z : Set G) := by
  have hST₀ := le_of_isSylowOf_normalizer hc6 hT₀
  have hZ₀ := centerIn_le_of_isSylowOf hS hc6 hT₀
  by_cases hZZ₀ : Z ≤ centerIn T₀
  · rw [← le_antisymm hZ₀ hZZ₀]
    exact mem_normalizer_centerIn hg
  have hZ₀2 : Nat.card (centerIn T₀) = 2 := by
    have hdvd := Subgroup.card_dvd_of_le hZ₀
    rw [hS.card] at hdvd
    have h1 : Nat.card (centerIn T₀) ≠ 1 := fun h => centerIn_ne_bot_of_isSylowOf hS hc6 hT₀
      (Subgroup.card_eq_one.mp h)
    have h4 : Nat.card (centerIn T₀) ≠ 4 := fun h =>
      hZZ₀ (le_of_eq (Subgroup.eq_of_le_of_card_ge hZ₀ (by rw [h, hS.card])).symm)
    have : Nat.card (centerIn T₀) ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [hdiv] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  have hidx : ((centerIn T₀).subgroupOf Z).index = 2 := by
    have h := relIndex_mul_card (centerIn T₀) Z
    rw [inf_eq_left.mpr hZ₀, hZ₀2, hS.card] at h
    exact (by omega : (centerIn T₀).relIndex Z = 2)
  have hT₀Z : ∀ t ∈ T₀, ∀ z ∈ Z, z⁻¹ * (t * z * t⁻¹) ∈ centerIn T₀ := by
    intro t ht z hz
    have htN : t ∈ normalizer (Z : Set G) := by
      rw [← hS.center]
      exact mem_normalizer_centerIn (hT₀.le ht)
    have htZ₀ : t ∈ normalizer (centerIn T₀ : Set G) := mem_normalizer_centerIn (le_normalizer ht)
    have hw : t * z * t⁻¹ ∈ Z := (mem_normalizer_iff.mp htN z).mp hz
    have hiff : z ∈ centerIn T₀ ↔ t * z * t⁻¹ ∈ centerIn T₀ := mem_normalizer_iff.mp htZ₀ z
    have h1 := mul_mem_iff_of_index_two hidx (a := (⟨z, hz⟩ : ↥Z)⁻¹) (b := ⟨t * z * t⁻¹, hw⟩)
    have h2 : (⟨z, hz⟩ : ↥Z)⁻¹ ∈ (centerIn T₀).subgroupOf Z ↔
        (⟨t * z * t⁻¹, hw⟩ : ↥Z) ∈ (centerIn T₀).subgroupOf Z := by
      rw [inv_mem_iff, mem_subgroupOf, mem_subgroupOf]
      exact hiff
    have h3 := h1.mpr h2
    rw [mem_subgroupOf] at h3
    simpa using h3
  apply mem_normalizer_fintype
  intro z hz
  have hgz : g * z * g⁻¹ ∈ T₀ := (mem_normalizer_iff.mp hg z).mp (hST₀ (hS.le hz))
  refine mem_of_forall_mem_centerIn hS hc1 hc6 hT₀ hgz hZZ₀ fun t ht => ?_
  have ht' : g⁻¹ * t * g ∈ T₀ := by
    have := (mem_normalizer_iff.mp (inv_mem hg) t).mp ht
    simpa using this
  have h1 := hT₀Z _ ht' z hz
  have h2 := (mem_normalizer_iff.mp (mem_normalizer_centerIn hg) _).mp h1
  have e : (g * z * g⁻¹)⁻¹ * (t * (g * z * g⁻¹) * t⁻¹) =
      g * (z⁻¹ * (g⁻¹ * t * g * z * (g⁻¹ * t * g)⁻¹)) * g⁻¹ := by group
  rw [e]
  exact h2

include hc1 in
theorem isSylowOf_top_of_isSylowOf
    (ha : ∀ t ∈ normalizer (S : Set G), t ∉ S → t * t ∈ S →
      16 ≤ Nat.card (⁅S, zpowers t⁆ ⊔ Z : Subgroup G))
    (hb : ∀ D : Subgroup G, D ≤ normalizer (S : Set G) →
      (∀ a ∈ D, ∀ b ∈ D, a * a ∈ S ∧ a * b * a⁻¹ * b⁻¹ ∈ S) →
      4 ≤ (D ⊓ S).relIndex D → ∃ d ∈ D, 64 ≤ Nat.card (⁅S, zpowers d⁆ ⊔ Z : Subgroup G))
    (hcc : ∀ D : Subgroup G, D ≤ normalizer (S : Set G) →
      (∀ a ∈ D, ∀ b ∈ D, a * a ∈ S ∧ a * b * a⁻¹ * b⁻¹ ∈ S) → (D ⊓ S).relIndex D ≤ 8) :
    IsSylowOf 2 T₀ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hST₀ := le_of_isSylowOf_normalizer hc6 hT₀
  obtain ⟨T, hT, hT₀T⟩ := AschbacherTheorem3.exists_isSylowOf_le hT₀.isPGroup (le_top : T₀ ≤ ⊤)
  by_contra hns
  have hne : T₀ ≠ T := fun h => hns (h ▸ hT)
  have hlt : T₀.subgroupOf T < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hne (le_antisymm hT₀T fun t ht => ?_)
    have : (⟨t, ht⟩ : ↥T) ∈ T₀.subgroupOf T := h ▸ mem_top _
    exact this
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have : Group.IsNilpotent ↥T := hT2.isNilpotent
  obtain ⟨⟨g, hgT⟩, hgN, hgT₀⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := ↥T) _ hlt)
  have hgT₀' : g ∉ T₀ := fun h => hgT₀ (mem_subgroupOf.mpr h)
  have hgN' : g ∈ normalizer (T₀ : Set G) := by
    refine mem_normalizer_fintype fun y hy => ?_
    have h1 := (mem_normalizer_iff.mp hgN ⟨y, hT₀T hy⟩).mp (mem_subgroupOf.mpr hy)
    rw [mem_subgroupOf] at h1
    simpa using h1
  have hgZ := mem_normalizer_of_mem_normalizer hS hc1 hc6 hT₀ hgN'
  set S' := S.map (MulAut.conj g).toMonoidHom with hS'
  have hmemS' : ∀ s ∈ S, g * s * g⁻¹ ∈ S' := fun s hs => ⟨s, hs, rfl⟩
  have hZS' : Z ≤ S' := fun z hz => by
    have h1 : g⁻¹ * z * g ∈ Z := by
      have := (mem_normalizer_iff.mp (inv_mem hgZ) z).mp hz
      simpa using this
    have e : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    rw [e]
    exact hmemS' _ (hS.le h1)
  have hS'T₀ : S' ≤ T₀ := by
    rintro _ ⟨s, hs, rfl⟩
    exact (mem_normalizer_iff.mp hgN' s).mp (hST₀ hs)
  have hS'e : ∀ a ∈ S', ∀ b ∈ S', a * a ∈ Z ∧ a * b * a⁻¹ * b⁻¹ ∈ Z := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · have e : g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      rw [e]
      exact (mem_normalizer_iff.mp hgZ _).mp (hS.sq a ha)
    · have e : g * a * g⁻¹ * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹ =
          g * (a * b * a⁻¹ * b⁻¹) * g⁻¹ := by group
      rw [e]
      exact (mem_normalizer_iff.mp hgZ _).mp (hS.comm_mem ha hb)
  have hS'card : Nat.card S ≤ Nat.card S' := by
    rw [hS', Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hSS' := eq_of_le_of_card_le hS hT₀ ha hb hcc hZS' hS'T₀ hS'e hS'card
  have hgS : g ∈ normalizer (S : Set G) := mem_normalizer_fintype fun s hs => by
    rw [← hSS']
    exact hmemS' s hs
  have h2 : IsPGroup 2 (zpowers g ⊔ T₀ : Subgroup G) :=
    hT2.to_le (sup_le (zpowers_le.mpr hgT) hT₀T)
  have h3 := hT₀.eq_of_le le_sup_right (sup_le (zpowers_le.mpr hgS) hT₀.le) h2
  exact hgT₀' (h3 ▸ mem_sup_left (mem_zpowers g))

end Offender

end Sec2

@[expose] def Step26iiAB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec2Setting G A R g E F →
      (∀ t ∈ normalizer (sec2S A R E F : Set G), t ∉ sec2S A R E F → t * t ∈ sec2S A R E F →
        16 ≤ Nat.card (⁅sec2S A R E F, zpowers t⁆ ⊔ sec2Z A E F : Subgroup G)) ∧
      ∀ D : Subgroup G, D ≤ normalizer (sec2S A R E F : Set G) →
        (∀ a ∈ D, ∀ b ∈ D, a * a ∈ sec2S A R E F ∧ a * b * a⁻¹ * b⁻¹ ∈ sec2S A R E F) →
        4 ≤ (D ⊓ sec2S A R E F).relIndex D →
        ∃ d ∈ D, 64 ≤ Nat.card (⁅sec2S A R E F, zpowers d⁆ ⊔ sec2Z A E F : Subgroup G)

@[expose] def Step26iiC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec2Setting G A R g E F →
      ∀ D : Subgroup G, D ≤ normalizer (sec2S A R E F : Set G) →
        (∀ a ∈ D, ∀ b ∈ D, a * a ∈ sec2S A R E F ∧ a * b * a⁻¹ * b⁻¹ ∈ sec2S A R E F) →
        (D ⊓ sec2S A R E F).relIndex D ≤ 8

theorem step26iiAB_of (h : Step26ii) : Step26iiAB := fun G _ _ A R g E F hS =>
  ⟨(h G A R g E F hS).1, (h G A R g E F hS).2.1⟩

theorem step26iiC_of (h : Step26ii) : Step26iiC := fun G _ _ A R g E F hS =>
  (h G A R g E F hS).2.2

theorem step28_of (h24 : Step24) (h26 : Step26) (hab : Step26iiAB) (hc : Step26iiC) :
    Step28 := by
  intro G _ _ A R g E F hset T₀ hT₀
  have hS := Sec2.special_of h24 hset
  obtain ⟨hc1, -, -, -, -, hc6, -, -, -⟩ := h26 G A R g E F hset
  obtain ⟨ha, hb⟩ := hab G A R g E F hset
  have hcc := hc G A R g E F hset
  refine ⟨fun U hZU hUT hUe hcard => Sec2.eq_of_le_of_card_le hS hT₀ ha hb hcc hZU hUT hUe hcard,
    Sec2.isSylowOf_top_of_isSylowOf hS hc1 hc6 hT₀ ha hb hcc,
    fun x hx => Sec2.mem_normalizer_of_mem_normalizer hS hc1 hc6 hT₀ hx⟩

end CFSG.ComponentClassification.AS81
