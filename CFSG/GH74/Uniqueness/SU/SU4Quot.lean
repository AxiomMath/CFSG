module

public import CFSG.GH74.Uniqueness.SU.SU4Sylow
public import CFSG.GH74.Uniqueness.SU.SU4Stmts
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.GH74.Uniqueness.SU.SU4

open Subgroup

section OddKernel

variable {Y Y' : Type} [Group Y] [Finite Y] [Group Y'] (π : Y →* Y')

omit [Finite Y] in
theorem inf_ker_eq_bot {P : Subgroup Y} (hP : IsPGroup 2 P) (hker : Odd (Nat.card π.ker)) :
    P ⊓ π.ker = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  obtain ⟨hyP, hyK⟩ := hy
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).mp hP ⟨y, hyP⟩
  have h1 : orderOf y = 2 ^ k := (Subgroup.orderOf_coe _).trans hk
  have h2 : orderOf y ∣ Nat.card π.ker := by
    have := orderOf_dvd_natCard (⟨y, hyK⟩ : π.ker)
    rwa [Subgroup.orderOf_mk] at this
  rw [h1] at h2
  have h3 : Nat.Coprime (2 ^ k) (Nat.card π.ker) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hker)
  have h4 : 2 ^ k = 1 := Nat.Coprime.eq_one_of_dvd h3 h2
  rw [h4, orderOf_eq_one_iff] at h1
  exact h1

omit [Finite Y] in
theorem eq_of_proj_eq {P : Subgroup Y} (hP : IsPGroup 2 P) (hker : Odd (Nat.card π.ker)) {a b : Y}
    (ha : a ∈ P) (hb : b ∈ P) (h : π a = π b) : a = b := by
  have h1 : a⁻¹ * b ∈ P ⊓ π.ker :=
    ⟨P.mul_mem (P.inv_mem ha) hb, MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, h]; simp)⟩
  rw [inf_ker_eq_bot π hP hker, Subgroup.mem_bot] at h1
  exact (inv_mul_eq_one.mp h1)

omit [Finite Y] in
theorem card_map_of_isPGroup {P : Subgroup Y} (hP : IsPGroup 2 P) (hker : Odd (Nat.card π.ker)) :
    Nat.card (P.map π) = Nat.card P := by
  have h1 := Subgroup.relIndex_mul_card (H := π.ker) (K := P)
  rw [inf_comm, inf_ker_eq_bot π hP hker, Subgroup.card_bot, mul_one, Subgroup.relIndex_ker] at h1
  exact h1

omit [Finite Y] in
theorem isElemAbelian_map {E : Subgroup Y} (hE : Open.IsElemAbelian 2 E) :
    Open.IsElemAbelian 2 (E.map π) := CFSG.SectionRank.isElemAbelian_map hE _

theorem isSylowIn_map [Finite Y'] (hker : Odd (Nat.card π.ker)) {X R : Subgroup Y}
    (hR : IsSylowIn X R) :
    IsSylowIn (X.map π) (R.map π) := by
  obtain ⟨hRX, k, m, hk, hm, hX⟩ := isSylowIn_iff_card.mp hR
  rw [isSylowIn_iff_card]
  refine ⟨Subgroup.map_mono hRX, k, ?_⟩
  have h1 := Subgroup.relIndex_mul_card (H := π.ker) (K := X)
  rw [Subgroup.relIndex_ker] at h1
  have hd : Odd (Nat.card ↥(π.ker ⊓ X)) :=
    Odd.of_dvd_nat hker (Subgroup.card_dvd_of_le inf_le_left)
  have hdX : Nat.card ↥(π.ker ⊓ X) ∣ Nat.card X := Dvd.intro_left _ h1
  have hd2 : Nat.card ↥(π.ker ⊓ X) ∣ 2 ^ k * m := hX ▸ hdX
  have hcop : Nat.Coprime (Nat.card ↥(π.ker ⊓ X)) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hd)
  obtain ⟨m₁, hm₁⟩ := hcop.dvd_of_dvd_mul_left hd2
  refine ⟨m₁, by rw [card_map_of_isPGroup π hR.2.1 hker, hk], (Nat.odd_mul.mp (hm₁ ▸ hm)).2, ?_⟩
  have h2 : Nat.card ↥(X.map π) * Nat.card ↥(π.ker ⊓ X) =
      (2 ^ k * m₁) * Nat.card ↥(π.ker ⊓ X) := by
    rw [h1, hX, hm₁]; ring
  exact Nat.eq_of_mul_eq_mul_right hd.pos h2

theorem pRank_map [Finite Y'] (hker : Odd (Nat.card π.ker)) (X : Subgroup Y) :
    Open.pRank 2 (X.map π) = Open.pRank 2 X := by
  obtain ⟨R, hR⟩ := exists_isSylowIn X
  have hR' := isSylowIn_map π hker hR
  rw [← hR'.pRank_eq, ← hR.pRank_eq]
  apply le_antisymm
  · refine SU1.pRank_le_of (fun Eb hEb hEbel k hk => ?_)
    set E : Subgroup Y := Eb.comap π ⊓ R with hEdef
    have hER : E ≤ R := inf_le_right
    have hEbel' := SU1.isElemAbelian_iff.mp hEbel
    have hEel : Open.IsElemAbelian 2 E := by
      rw [SU1.isElemAbelian_iff]
      refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
      · refine eq_of_proj_eq π hR.2.1 hker (R.mul_mem (hER ha) (hER hb))
          (R.mul_mem (hER hb) (hER ha)) ?_
        rw [map_mul, map_mul]
        exact hEbel'.1 _ ha.1 _ hb.1
      · refine eq_of_proj_eq π hR.2.1 hker (R.pow_mem (hER ha) 2) R.one_mem ?_
        rw [map_pow, map_one]
        exact hEbel'.2 _ ha.1
    have hEmap : E.map π = Eb := by
      apply le_antisymm
      · rintro _ ⟨e, he, rfl⟩
        exact he.1
      · intro eb heb
        obtain ⟨r, hr, rfl⟩ := hEb heb
        exact ⟨r, ⟨heb, hr⟩, rfl⟩
    have hEcard : Nat.card E = 2 ^ k := by
      rw [← card_map_of_isPGroup π (hR.2.1.to_le hER) hker, hEmap]
      exact hk
    exact SU1.le_pRank (by norm_num) hER hEel hEcard
  · refine SU1.pRank_le_of (fun E hER hEel k hk => ?_)
    refine SU1.le_pRank (by norm_num) (Subgroup.map_mono hER) (isElemAbelian_map π hEel) ?_
    rw [card_map_of_isPGroup π (hR.2.1.to_le hER) hker, hk]

theorem centralizer_map_eq (hπ : Function.Surjective π) (hker : Odd (Nat.card π.ker)) {x : Y}
    (hx : x * x = 1) :
    centralizer ({π x} : Set Y') = (centralizer ({x} : Set Y)).map π := by
  apply le_antisymm
  · intro yb hyb
    obtain ⟨y, rfl⟩ := hπ yb
    have hcomm : π y * π x = π x * π y := Subgroup.mem_centralizer_singleton_iff.mp hyb
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    let A := {w : Y // π w = π y}
    have hfA : ∀ w : A, π (x * w.1 * x⁻¹) = π y := by
      intro w
      rw [map_mul, map_mul, w.2, map_inv]
      calc π x * π y * (π x)⁻¹ = (π y * π x) * (π x)⁻¹ := by rw [hcomm]
        _ = π y := by group
    let f : A → A := fun w => ⟨x * w.1 * x⁻¹, hfA w⟩
    have hf : Function.Involutive f := by
      intro w
      apply Subtype.ext
      show x * (x * w.1 * x⁻¹) * x⁻¹ = w.1
      rw [hxinv]
      calc x * (x * w.1 * x) * x = (x * x) * w.1 * (x * x) := by group
        _ = w.1 := by rw [hx]; group
    let σ : Equiv.Perm A := hf.toPerm
    have hσ : σ ^ 2 ^ 1 = 1 := by
      ext w
      simp only [pow_one, pow_two, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one,
        id_eq]
      exact congrArg Subtype.val (hf w)
    have hcardA : Nat.card A = Nat.card π.ker := by
      refine Nat.card_congr ⟨fun w => ⟨y⁻¹ * w.1, ?_⟩, fun k => ⟨y * k.1, ?_⟩, ?_, ?_⟩
      · rw [MonoidHom.mem_ker, map_mul, map_inv, w.2]; simp
      · rw [map_mul, MonoidHom.mem_ker.mp k.2, mul_one]
      · intro w; apply Subtype.ext; simp
      · intro k; apply Subtype.ext; simp
    have : Fintype A := Fintype.ofFinite A
    have hnd : ¬ 2 ∣ Fintype.card A := by
      rw [← Nat.card_eq_fintype_card, hcardA]
      have := hker
      rw [Nat.odd_iff] at this
      omega
    obtain ⟨w, hw⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hnd hσ
    have hw' : x * w.1 * x⁻¹ = w.1 := congrArg Subtype.val hw
    refine ⟨w.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_, w.2⟩
    calc w.1 * x = (x * w.1 * x⁻¹) * x := by rw [hw']
      _ = x * w.1 := by group
  · intro yb hyb
    have := Subgroup.map_centralizer_le_centralizer_image ({x} : Set Y) π hyb
    simpa using this

theorem exists_conj_of_map_eq [Finite Y'] (hker : Odd (Nat.card π.ker)) {K₁ K₂ : Subgroup Y}
    (h₁ : IsPGroup 2 K₁) (h₂ : IsPGroup 2 K₂) (h : K₁.map π = K₂.map π) :
    ∃ c : Y, conjSub c K₁ = K₂ := by
  set X : Subgroup Y := K₂ ⊔ π.ker with hX
  have hK₁X : K₁ ≤ X := by
    intro a ha
    have : π a ∈ K₂.map π := h ▸ Subgroup.mem_map_of_mem π ha
    obtain ⟨b, hb, hba⟩ := this
    have hker' : b⁻¹ * a ∈ π.ker := MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hba]; simp)
    have : a = b * (b⁻¹ * a) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hb hker'
  have hK₂X : K₂ ≤ X := le_sup_left
  have hXmap : X.map π = K₂.map π := by
    rw [hX, Subgroup.map_sup, Subgroup.map_ker_self]
    simp
  have hXcard : Nat.card X = Nat.card K₂ * Nat.card π.ker := by
    have h1 := Subgroup.relIndex_mul_card (H := π.ker) (K := X)
    rw [Subgroup.relIndex_ker, inf_eq_left.mpr le_sup_right, hXmap,
      card_map_of_isPGroup π h₂ hker] at h1
    rw [← h1]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp h₂
  have hsyl : IsSylowIn X K₂ := by
    rw [isSylowIn_iff_card]
    exact ⟨hK₂X, k, Nat.card π.ker, hk, hker, by rw [hXcard, hk]⟩
  obtain ⟨c, hcX, hc⟩ := hsyl.exists_conj_le hK₁X h₁
  refine ⟨c⁻¹, ?_⟩
  have hcard : Nat.card K₂ ≤ Nat.card (conjSub c⁻¹ K₁) := by
    rw [card_conjSub, ← card_map_of_isPGroup π h₁ hker, h, card_map_of_isPGroup π h₂ hker]
  exact Subgroup.eq_of_le_of_card_ge hc hcard

end OddKernel

section Inj

variable {Y Y' : Type} [Group Y] [Finite Y] [Group Y'] [Finite Y']

theorem pRank_map_of_injective (f : Y →* Y') (hf : Function.Injective f) (K : Subgroup Y) :
    Open.pRank 2 (K.map f) = Open.pRank 2 K := by
  apply le_antisymm
  · refine SU1.pRank_le_of (fun E hEK hEel k hk => ?_)
    have hE' : E.comap f ≤ K := by
      intro e he
      obtain ⟨k', hk', hkf⟩ := hEK he
      rw [hf hkf] at hk'
      exact hk'
    have hEel' : Open.IsElemAbelian 2 (E.comap f) := by
      have h := SU1.isElemAbelian_iff.mp hEel
      rw [SU1.isElemAbelian_iff]
      refine ⟨fun a ha b hb => hf ?_, fun a ha => hf ?_⟩
      · rw [map_mul, map_mul]; exact h.1 _ ha _ hb
      · rw [map_pow, map_one]; exact h.2 _ ha
    have hcard : Nat.card (E.comap f) = 2 ^ k := by
      rw [← hk]
      have : (E.comap f).map f = E := by
        apply le_antisymm
        · rintro _ ⟨e, he, rfl⟩; exact he
        · intro e he
          obtain ⟨k', -, rfl⟩ := hEK he
          exact ⟨k', he, rfl⟩
      rw [← this, Subgroup.card_map_of_injective hf]
      rw [this]
    exact SU1.le_pRank (by norm_num) hE' hEel' hcard
  · refine SU1.pRank_le_of (fun E hEK hEel k hk => ?_)
    refine SU1.le_pRank (by norm_num) (Subgroup.map_mono hEK) ?_ ?_
    · rw [SU1.isElemAbelian_iff] at hEel ⊢
      refine ⟨?_, ?_⟩
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        rw [← map_mul, ← map_mul, hEel.1 a ha b hb]
      · rintro _ ⟨a, ha, rfl⟩
        rw [← map_pow, hEel.2 a ha, map_one]
    · rw [Subgroup.card_map_of_injective hf, hk]

end Inj

section Quot

variable {G : Type} [Group G] [Finite G] (M : Subgroup G)

@[expose] def proj : ↥M →* Mbar M := QuotientGroup.mk' (pPrimeCore 2 ↥M)

omit [Finite G] in
theorem proj_surjective : Function.Surjective (proj M) := QuotientGroup.mk'_surjective _

omit [Finite G] in
theorem ker_proj : (proj M).ker = pPrimeCore 2 ↥M := QuotientGroup.ker_mk' _

theorem odd_card_ker_proj : Odd (Nat.card (proj M).ker) := by
  rw [ker_proj]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥M))

omit [Finite G] in
theorem barImage_eq (X : Subgroup G) : barImage M X = (X.subgroupOf M).map (proj M) := rfl

omit [Finite G] in
theorem mem_barImage {X : Subgroup G} {y : Mbar M} :
    y ∈ barImage M X ↔ ∃ m : ↥M, (m : G) ∈ X ∧ proj M m = y := by
  rw [barImage_eq, Subgroup.mem_map]
  simp only [Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem isPGroup_subgroupOf {X : Subgroup G} (hX : IsPGroup 2 X) (hXM : X ≤ M) :
    IsPGroup 2 ↥(X.subgroupOf M) :=
  IsPGroup.of_equiv hX (Subgroup.subgroupOfEquivOfLe hXM).symm

theorem eq_of_proj_eq_of_isPGroup {X : Subgroup G} (hX : IsPGroup 2 X) (hXM : X ≤ M) {a b : ↥M}
    (ha : (a : G) ∈ X) (hb : (b : G) ∈ X) (h : proj M a = proj M b) : a = b :=
  eq_of_proj_eq (proj M) (isPGroup_subgroupOf M hX hXM) (odd_card_ker_proj M)
    (Subgroup.mem_subgroupOf.mpr ha) (Subgroup.mem_subgroupOf.mpr hb) h

noncomputable def mulEquivBarImage {X : Subgroup G} (hX : IsPGroup 2 X) (hXM : X ≤ M) :
    ↥X ≃* ↥(barImage M X) := by
  let X₀ : Subgroup ↥M := X.subgroupOf M
  let φ : ↥X₀ →* ↥(barImage M X) :=
    ((proj M).comp X₀.subtype).codRestrict (barImage M X) (fun a => ⟨a.1, a.2, rfl⟩)
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b hab => ?_, fun y => ?_⟩
    · apply Subtype.ext
      exact eq_of_proj_eq (proj M) (isPGroup_subgroupOf M hX hXM) (odd_card_ker_proj M) a.2 b.2
        (congrArg Subtype.val hab)
    · obtain ⟨m, hm, hmy⟩ := y.2
      exact ⟨⟨m, hm⟩, Subtype.ext hmy⟩
  exact (Subgroup.subgroupOfEquivOfLe hXM).symm.trans (MulEquiv.ofBijective φ hφ)

theorem pRank_barImage {X : Subgroup G} (hXM : X ≤ M) :
    Open.pRank 2 (barImage M X) = Open.pRank 2 X := by
  rw [barImage_eq, pRank_map (proj M) (odd_card_ker_proj M)]
  have h : (X.subgroupOf M).map M.subtype = X := by
    rw [Subgroup.subgroupOf_map_subtype]; exact inf_eq_left.mpr hXM
  have h2 := pRank_map_of_injective M.subtype M.subtype_injective (X.subgroupOf M)
  rw [h] at h2
  exact h2.symm

end Quot

end CFSG.GH74.Uniqueness.SU.SU4
