module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.ComponentClassification.Foote5

open Subgroup

variable {G : Type*} [Group G]

theorem harE16_card_mul_card_le [Finite G] {H K L : Subgroup G} (hH : H ≤ L) (hK : K ≤ L) :
    Nat.card H * Nat.card K ≤ Nat.card L * Nat.card ↥(H ⊓ K) := by
  have h1 := relIndex_mul_card H L
  have h2 := relIndex_mul_card K L
  have h3 := relIndex_mul_card (H ⊓ K) L
  have h4 : (H ⊓ K).relIndex L ≤ H.relIndex L * K.relIndex L := relIndex_inf_le
  rw [inf_eq_left.mpr hH] at h1
  rw [inf_eq_left.mpr hK] at h2
  rw [inf_eq_left.mpr (inf_le_left.trans hH)] at h3
  have hpos : 0 < (H ⊓ K).relIndex L := by
    rcases Nat.eq_zero_or_pos ((H ⊓ K).relIndex L) with h0 | h0
    · rw [h0, zero_mul] at h3
      exact absurd h3.symm Nat.card_pos.ne'
    · exact h0
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc (H ⊓ K).relIndex L * (Nat.card H * Nat.card K)
      ≤ (H.relIndex L * K.relIndex L) * (Nat.card H * Nat.card K) := Nat.mul_le_mul_right _ h4
    _ = (H.relIndex L * Nat.card H) * (K.relIndex L * Nat.card K) := by ring
    _ = Nat.card L * Nat.card L := by rw [h1, h2]
    _ = (H ⊓ K).relIndex L * Nat.card ↥(H ⊓ K) * Nat.card L := by rw [h3]
    _ = (H ⊓ K).relIndex L * (Nat.card L * Nat.card ↥(H ⊓ K)) := by ring

theorem harE16_le_or_le {H K₁ K₂ : Subgroup G} (h : ∀ x ∈ H, x ∈ K₁ ∨ x ∈ K₂) :
    H ≤ K₁ ∨ H ≤ K₂ := by
  by_contra hne
  obtain ⟨a, ha, ha1⟩ := IsConcreteLE.not_le_iff_exists.mp fun h1 => hne (Or.inl h1)
  obtain ⟨b, hb, hb2⟩ := IsConcreteLE.not_le_iff_exists.mp fun h2 => hne (Or.inr h2)
  have ha2 : a ∈ K₂ := (h a ha).resolve_left ha1
  have hb1 : b ∈ K₁ := (h b hb).resolve_right hb2
  rcases h (a * b) (H.mul_mem ha hb) with hab | hab
  · exact ha1 (by simpa using K₁.mul_mem hab (K₁.inv_mem hb1))
  · exact hb2 (by simpa using K₂.mul_mem (K₂.inv_mem ha2) hab)

theorem harE16_exists_mem_normalizer [Finite G] {P K : Subgroup G} (hPK : P ≤ K)
    (hK : IsPGroup 2 K) (hne : P ≠ K) : ∃ y ∈ K, y ∉ P ∧ y ∈ normalizer (P : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥K := hK.isNilpotent
  have hlt : P.subgroupOf K < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    apply le_antisymm hPK
    intro x hx
    have : (⟨x, hx⟩ : ↥K) ∈ P.subgroupOf K := by rw [htop]; trivial
    exact this
  obtain ⟨y, hyN, hyP⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (G := ↥K) (P.subgroupOf K) hlt)
  refine ⟨y, y.2, fun h => hyP h, ?_⟩
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact (mem_normalizer_iff.1 hyN ⟨g, hPK hg⟩).1 hg
  · intro hg
    have hgK : g ∈ K := by
      have h2 := K.mul_mem (K.mul_mem (K.inv_mem y.2) (hPK hg)) y.2
      simpa [mul_assoc] using h2
    exact (mem_normalizer_iff.1 hyN ⟨g, hgK⟩).2 hg

theorem harE16_exists_mem_mul [Finite G] {H K L : Subgroup G} (hHL : H ≤ L) (hKL : K ≤ L)
    (hLN : L ≤ normalizer (H : Set G))
    (hcard : Nat.card L * Nat.card ↥(H ⊓ K) ≤ Nat.card H * Nat.card K) {l : G} (hl : l ∈ L) :
    ∃ k ∈ K, k⁻¹ * l ∈ H := by
  have : (H.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer hLN
  let f : ↥K →* ↥L ⧸ H.subgroupOf L := (QuotientGroup.mk' _).comp (inclusion hKL)
  have hker : Nat.card f.ker = Nat.card ↥(H ⊓ K) := by
    have h1 : f.ker = H.subgroupOf K := by
      ext k
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, mem_subgroupOf, mem_subgroupOf, coe_inclusion]
    rw [h1, ← card_map_of_injective K.subtype_injective, subgroupOf_map_subtype]
  have hQ : Nat.card ↥L = Nat.card (↥L ⧸ H.subgroupOf L) * Nat.card H := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hHL).toEquiv]
    exact card_eq_card_quotient_mul_card_subgroup _
  have hsurj : Function.Surjective f := by
    apply MonoidHom.surjective_of_card_ker_le_div
    rw [hker, Nat.le_div_iff_mul_le Nat.card_pos]
    have h3 : Nat.card H * (Nat.card ↥(H ⊓ K) * Nat.card (↥L ⧸ H.subgroupOf L)) ≤
        Nat.card H * Nat.card K := by
      calc Nat.card H * (Nat.card ↥(H ⊓ K) * Nat.card (↥L ⧸ H.subgroupOf L))
          = Nat.card (↥L ⧸ H.subgroupOf L) * Nat.card H * Nat.card ↥(H ⊓ K) := by ring
        _ = Nat.card L * Nat.card ↥(H ⊓ K) := by rw [← hQ]
        _ ≤ Nat.card H * Nat.card K := hcard
    exact Nat.le_of_mul_le_mul_left h3 Nat.card_pos
  obtain ⟨k, hk⟩ := hsurj (QuotientGroup.mk ⟨l, hl⟩)
  refine ⟨k, k.2, ?_⟩
  have h2 := QuotientGroup.eq.mp hk
  rw [mem_subgroupOf] at h2
  simpa using h2

theorem harE16_comm_eq_one_iff {s y : G} : s * y * s⁻¹ * y⁻¹ = 1 ↔ s * y = y * s := by
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

@[expose] def harE16CommHom {T : Subgroup G} (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    {s : G} (hs : s ∈ normalizer (T : Set G)) : ↥T →* ↥T where
  toFun x := ⟨s * x * s⁻¹ * (x : G)⁻¹,
    T.mul_mem ((mem_normalizer_iff.mp hs x).mp x.2) (T.inv_mem x.2)⟩
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    have hY : s * (y : G) * s⁻¹ ∈ T := (mem_normalizer_iff.mp hs y).mp y.2
    have hc := hTab _ (T.inv_mem x.2) _ (T.mul_mem hY (T.inv_mem y.2))
    simp only [coe_mul]
    calc s * ((x : G) * y) * s⁻¹ * ((x : G) * y)⁻¹
        = s * x * s⁻¹ * ((s * y * s⁻¹ * (y : G)⁻¹) * (x : G)⁻¹) := by group
      _ = s * x * s⁻¹ * ((x : G)⁻¹ * (s * y * s⁻¹ * (y : G)⁻¹)) := by rw [hc]
      _ = s * x * s⁻¹ * (x : G)⁻¹ * (s * y * s⁻¹ * (y : G)⁻¹) := by group

theorem harE16CommHom_apply {T : Subgroup G} (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    {s : G} (hs : s ∈ normalizer (T : Set G)) (x : ↥T) :
    (harE16CommHom hTab hs x : G) = s * x * s⁻¹ * (x : G)⁻¹ :=
  rfl

theorem harE16CommHom_eq_one_iff {T : Subgroup G} (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    {s : G} (hs : s ∈ normalizer (T : Set G)) (x : ↥T) :
    harE16CommHom hTab hs x = 1 ↔ s * (x : G) = x * s := by
  rw [← harE16_comm_eq_one_iff, ← harE16CommHom_apply hTab hs x, ← OneMemClass.coe_one T,
    Subtype.ext_iff]

theorem harE16_exists_central_mod [Finite G] {R T : Subgroup G} (hR : IsPGroup 2 R)
    (hRN : R ≤ normalizer (T : Set G)) {r₀ : G} (hr₀ : r₀ ∈ R) (hr₀T : r₀ ∉ T) :
    ∃ s ∈ R, s ∉ T ∧ s * s ∈ T ∧ ∀ r ∈ R, s⁻¹ * (r * s * r⁻¹) ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (T.subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer hRN
  have key : ∀ b : ↥R, (b : ↥R ⧸ T.subgroupOf R) = 1 → (b : G) ∈ T := fun b hb =>
    (QuotientGroup.eq_one_iff b).mp hb
  have hQ : IsPGroup 2 (↥R ⧸ T.subgroupOf R) := hR.to_quotient _
  have : Nontrivial (↥R ⧸ T.subgroupOf R) :=
    ⟨⟨QuotientGroup.mk ⟨r₀, hr₀⟩, 1, fun h => hr₀T (key _ h)⟩⟩
  have : Nontrivial (center (↥R ⧸ T.subgroupOf R)) := hQ.center_nontrivial
  have h2 : 2 ∣ Nat.card (center (↥R ⧸ T.subgroupOf R)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hQ.to_subgroup (center (↥R ⧸ T.subgroupOf R)))
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact (Finite.one_lt_card (α := center (↥R ⧸ T.subgroupOf R))).ne' hn
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (z : ↥R ⧸ T.subgroupOf R)
  have hz1 : (z : ↥R ⧸ T.subgroupOf R) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    omega
  have hzz : (z : ↥R ⧸ T.subgroupOf R) * z = 1 := by
    have h := pow_orderOf_eq_one (z : ↥R ⧸ T.subgroupOf R)
    rw [Subgroup.orderOf_coe, hz, sq] at h
    exact h
  refine ⟨a, a.2, fun h => hz1 ?_, key (a * a) ?_, fun r hr => key (a⁻¹ * (⟨r, hr⟩ * a *
    (⟨r, hr⟩ : ↥R)⁻¹)) ?_⟩
  · rw [← ha]
    exact (QuotientGroup.eq_one_iff a).mpr h
  · rw [QuotientGroup.mk_mul, ha, hzz]
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, ha, mem_center_iff.mp z.2, mul_assoc, mul_inv_cancel, mul_one,
      inv_mul_cancel]

theorem harE16_exists_mem_center [Finite G] {R C : Subgroup G} (hR : IsPGroup 2 R) (hCR : C ≤ R)
    (hRN : R ≤ normalizer (C : Set G)) (hC : C ≠ ⊥) :
    ∃ c ∈ C, c ≠ 1 ∧ ∀ r ∈ R, r * c = c * r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥R := hR.isNilpotent
  have : (C.subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer hRN
  have hne : C.subgroupOf R ≠ ⊥ := by
    intro h
    apply hC
    rw [← map_subgroupOf_eq_of_le hCR, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨y, (mem_inf.mp hy).1, fun h => hy1 (Subtype.ext (Subtype.ext h)), fun r hr => ?_⟩
  have h1 := mem_center_iff.mp (mem_inf.mp hy).2 ⟨r, hr⟩
  exact congrArg Subtype.val h1

theorem harE16_card_le_of_conj [Finite G] {R T C : Subgroup G} (hTR : T ≤ R) (hCR : C ≤ R)
    {x : G} (hxR : x ∈ R) (hstab : ∀ r ∈ R, r * x = x * r → r ∈ T)
    (hTx : ∀ t ∈ T, t * x = x * t) (hC : ∀ r ∈ R, x⁻¹ * (r * x * r⁻¹) ∈ C) :
    Nat.card R ≤ Nat.card T * Nat.card C := by
  classical
  let g : ↥R := ⟨x, hxR⟩
  have hcen : centralizer ({g} : Set ↥R) = T.subgroupOf R := by
    ext r
    rw [mem_centralizer_singleton_iff, mem_subgroupOf]
    constructor
    · intro h
      exact hstab r r.2 (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext (hTx r h)
  have h1 := index_centralizer_eq_ncard g
  rw [hcen] at h1
  have hsub : conjugatesOf g ⊆ (fun c : ↥C => g * ⟨c, hCR c.2⟩) '' Set.univ := by
    intro y hy
    obtain ⟨r, rfl⟩ := isConj_iff.mp hy
    refine ⟨⟨x⁻¹ * (r * x * r⁻¹), hC r r.2⟩, Set.mem_univ _, ?_⟩
    apply Subtype.ext
    simp [g]
  have h2 : (conjugatesOf g).ncard ≤ Nat.card C :=
    calc (conjugatesOf g).ncard ≤ ((fun c : ↥C => g * ⟨c, hCR c.2⟩) '' Set.univ).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (Set.univ : Set ↥C).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = Nat.card C := Set.ncard_univ _
  have h3 := (T.subgroupOf R).card_mul_index
  rw [h1, show Nat.card (T.subgroupOf R) = Nat.card T from
    Nat.card_congr (subgroupOfEquivOfLe hTR).toEquiv] at h3
  rw [← h3]
  exact Nat.mul_le_mul_left _ h2

end CFSG.ComponentClassification.Foote5
