module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.Assembly.Defs

public section

open CFSG.Quasithin

namespace CFSG.QuasithinUnique.Setup.X5

section Odd

theorem exists_ne_one_fixed_of_pgroup {A : Type*} [Group A] [Finite A] {p : ℕ} [hp : Fact p.Prime]
    (hA : IsPGroup p A) (hA1 : 1 < Nat.card A) {Y : Subgroup (MulAut A)} (hY : IsPGroup p Y) :
    ∃ a : A, a ≠ 1 ∧ ∀ y ∈ Y, (y : MulAut A) a = a := by
  classical
  have hmod := hY.card_modEq_card_fixedPoints A
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    omega
  have hpA : Nat.card A ≡ 0 [MOD p] := by
    rw [hn, Nat.modEq_zero_iff_dvd]
    exact dvd_pow_self p hn0
  have hfix : Nat.card (MulAction.fixedPoints Y A) ≡ 0 [MOD p] := hmod.symm.trans hpA
  have h1 : (1 : A) ∈ MulAction.fixedPoints Y A := fun y => map_one (y : MulAut A)
  have hcard : 1 < Nat.card (MulAction.fixedPoints Y A) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints Y A) := Nat.card_pos_iff.mpr
      ⟨⟨⟨1, h1⟩⟩, inferInstance⟩
    have := Nat.modEq_zero_iff_dvd.mp hfix
    have := Nat.le_of_dvd hpos this
    have := hp.out.two_le
    omega
  have := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨⟨a, ha⟩, ha1⟩ := exists_ne (⟨1, h1⟩ : MulAction.fixedPoints Y A)
  exact ⟨a, fun h0 => ha1 (Subtype.ext h0), fun y hy => ha ⟨y, hy⟩⟩

variable {W : Type*} [CommGroup W]

theorem mem_fixV_zpowers' {c : MulAut W} {v : W} : v ∈ fixV (Subgroup.zpowers c) ↔ c v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem eq_one_of_centralizes_irreducible [Finite W] [Nontrivial W] (hW : ∀ w : W, w * w = 1)
    (L : Subgroup (MulAut W))
    (hirr : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    {z : MulAut W} (hz : ∀ g ∈ L, g * z = z * g) {k : ℕ} (hzk : z ^ (2 ^ k) = 1) : z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsPGroup 2 W := fun w => ⟨1, by simpa [sq] using hW w⟩
  have hA1 : 1 < Nat.card W := Finite.one_lt_card
  have hY : IsPGroup 2 (Subgroup.zpowers z) := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzk, one_zpow]
  obtain ⟨a, ha1, hafix⟩ := exists_ne_one_fixed_of_pgroup hA hA1 hY
  have hUne : fixV (Subgroup.zpowers z) ≠ ⊥ := by
    intro hbot
    have : a ∈ fixV (Subgroup.zpowers z) := fun y hy => hafix y hy
    rw [hbot, Subgroup.mem_bot] at this
    exact ha1 this
  have hinv : ∀ g ∈ L, ∀ u ∈ fixV (Subgroup.zpowers z), g u ∈ fixV (Subgroup.zpowers z) := by
    intro g hg u hu
    rw [mem_fixV_zpowers'] at hu ⊢
    have := congrArg (fun m : MulAut W => m u) (hz g hg)
    simp only [MulAut.mul_apply] at this
    rw [← this, hu]
  rcases hirr _ hinv with h0 | htop
  · exact absurd h0 hUne
  · apply MulEquiv.ext
    intro w
    have : w ∈ fixV (Subgroup.zpowers z) := by rw [htop]; exact Subgroup.mem_top w
    rw [mem_fixV_zpowers'] at this
    simpa using this

theorem centralizer_odd [Finite W] [Nontrivial W] (hW : ∀ w : W, w * w = 1)
    (L : Subgroup (MulAut W))
    (hirr : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) :
    Odd (Nat.card (Subgroup.centralizer (L : Set (MulAut W)))) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have h2 : 2 ∣ Nat.card (Subgroup.centralizer (L : Set (MulAut W))) := even_iff_two_dvd.mp hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hzc : (z : MulAut W) ∈ Subgroup.centralizer (L : Set (MulAut W)) := z.2
  have hcomm : ∀ g ∈ L, g * (z : MulAut W) = (z : MulAut W) * g :=
    Subgroup.mem_centralizer_iff.mp hzc
  have hz2 : (z : MulAut W) ^ (2 ^ 1) = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    have h' := congrArg Subtype.val this
    simpa using h'
  have := eq_one_of_centralizes_irreducible hW L hirr hcomm hz2
  have hz1 : z = 1 := Subtype.ext this
  rw [hz1, orderOf_one] at hz
  omega

end Odd

section Normalizer

open CFSG.ComponentClassification

variable {G : Type*} [Group G] (L : Subgroup G)

@[expose] noncomputable def conjOn (a : Subgroup.normalizer (L : Set G)) : MulAut L where
  toFun x := ⟨(a : G) * x * (a : G)⁻¹, (Subgroup.mem_normalizer_iff.mp a.2 x).mp x.2⟩
  invFun x := ⟨(a : G)⁻¹ * x * (a : G), by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem a.2) (x : G)).mp x.2
    simpa using this⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem coe_conjOn (a : Subgroup.normalizer (L : Set G)) (x : L) :
    ((conjOn L a x : L) : G) = (a : G) * x * (a : G)⁻¹ := rfl

noncomputable def normalizerAct : Subgroup.normalizer (L : Set G) →* MulAut (L ⧸ Subgroup.center L) where
  toFun a := PerfectAutomorphisms.onCenterQuotient (conjOn L a)
  map_one' := by
    ext y
    obtain ⟨x, rfl⟩ := (QuotientGroup.mk'_surjective (Subgroup.center L)) y
    rw [PerfectAutomorphisms.onCenterQuotient_apply_mk]
    have : conjOn L (1 : Subgroup.normalizer (L : Set G)) x = x := Subtype.ext (by simp [coe_conjOn])
    rw [this]; rfl
  map_mul' a b := by
    ext y
    obtain ⟨x, rfl⟩ := (QuotientGroup.mk'_surjective (Subgroup.center L)) y
    rw [MulAut.mul_apply, PerfectAutomorphisms.onCenterQuotient_apply_mk,
      PerfectAutomorphisms.onCenterQuotient_apply_mk, PerfectAutomorphisms.onCenterQuotient_apply_mk]
    have : conjOn L (a * b) x = conjOn L a (conjOn L b x) :=
      Subtype.ext (by simp [coe_conjOn, mul_assoc])
    rw [this]

theorem normalizerAct_apply_mk (a : Subgroup.normalizer (L : Set G)) (x : L) :
    normalizerAct L a (QuotientGroup.mk x) = QuotientGroup.mk (conjOn L a x) :=
  PerfectAutomorphisms.onCenterQuotient_apply_mk (conjOn L a) x

theorem mem_centralizer_of_normalizerAct_eq_one [Group.IsPerfect L]
    {a : Subgroup.normalizer (L : Set G)} (ha : normalizerAct L a = 1) :
    (a : G) ∈ Subgroup.centralizer (L : Set G) := by
  have h1 : conjOn L a = 1 := by
    apply PerfectAutomorphisms.onCenterQuotient_eq_one_imp
    exact ha
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have := congrArg (fun m : MulAut L => ((m ⟨l, hl⟩ : L) : G)) h1
  simp only [coe_conjOn, MulAut.one_apply] at this
  calc l * (a : G) = (a : G) * l * (a : G)⁻¹ * (a : G) := by rw [this]
    _ = (a : G) * l := by group

theorem normalizerAct_of_mem {l : G} (hl : l ∈ L) :
    normalizerAct L ⟨l, Subgroup.le_normalizer hl⟩ =
      MulAut.conj (QuotientGroup.mk (⟨l, hl⟩ : L) : L ⧸ Subgroup.center L) := by
  ext y
  obtain ⟨x, rfl⟩ := (QuotientGroup.mk'_surjective (Subgroup.center L)) y
  have h1 := normalizerAct_apply_mk L ⟨l, Subgroup.le_normalizer hl⟩ x
  have h2 : conjOn L ⟨l, Subgroup.le_normalizer hl⟩ x = ⟨l, hl⟩ * x * ⟨l, hl⟩⁻¹ :=
    Subtype.ext (by simp [coe_conjOn])
  change normalizerAct L ⟨l, _⟩ (QuotientGroup.mk x) = _
  rw [h1, h2]
  rfl

theorem pow_card_centralizer_eq_one {C : Subgroup G} {c : G} (hc : c ∈ C) :
    c ^ Nat.card C = 1 := by
  have h2 : ((⟨c, hc⟩ : C) ^ Nat.card C : C) = (1 : C) := pow_card_eq_one'
  have h3 := congrArg (fun z : C => (z : G)) h2
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at h3
  exact h3

theorem eq_one_of_involution_mem_odd {C : Subgroup G}
    (hodd : Odd (Nat.card C)) {a : G} (ha : a ∈ C) (ha2 : a * a = 1) : a = 1 := by
  have h1 := pow_card_centralizer_eq_one ha
  obtain ⟨k, hk⟩ := hodd
  rw [hk, pow_succ, pow_mul, sq, ha2, one_pow, one_mul] at h1
  exact h1

theorem eq_one_of_normalizerAct_eq_one [Group.IsPerfect L]
    (hodd : Odd (Nat.card (Subgroup.centralizer (L : Set G))))
    {a : Subgroup.normalizer (L : Set G)} (ha2 : (a : G) * a = 1) (ha : normalizerAct L a = 1) :
    (a : G) = 1 :=
  eq_one_of_involution_mem_odd hodd (mem_centralizer_of_normalizerAct_eq_one L ha) ha2

theorem mem_of_involution_inner [Group.IsPerfect L]
    (hodd : Odd (Nat.card (Subgroup.centralizer (L : Set G)))) {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (ha2 : a * a = 1)
    (hinner : normalizerAct L ⟨a, ha⟩ ∈
      (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range) :
    a ∈ L := by
  obtain ⟨y, hy⟩ := hinner
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  have h1 : normalizerAct L ⟨a, ha⟩ = normalizerAct L ⟨(l : G), Subgroup.le_normalizer l.2⟩ := by
    rw [← hy, normalizerAct_of_mem L l.2]
  have h2 : normalizerAct L (⟨a, ha⟩ * ⟨(l : G), Subgroup.le_normalizer l.2⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  have hc := mem_centralizer_of_normalizerAct_eq_one L h2
  have hc' : a * (l : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by simpa using hc
  have hcomm : Commute (a * (l : G)⁻¹) (l : G) := by
    have := Subgroup.mem_centralizer_iff.mp hc' (l : G) l.2
    exact this.symm
  have hpow := pow_card_centralizer_eq_one hc'
  obtain ⟨k, hk⟩ := hodd
  have hal : a = (a * (l : G)⁻¹) * l := by group
  have hapow : a ^ (Nat.card (Subgroup.centralizer (L : Set G))) = a := by
    rw [hk, pow_succ, pow_mul, sq, ha2, one_pow, one_mul]
  have : a = (l : G) ^ (Nat.card (Subgroup.centralizer (L : Set G))) := by
    calc a = a ^ (Nat.card (Subgroup.centralizer (L : Set G))) := hapow.symm
      _ = ((a * (l : G)⁻¹) * l) ^ (Nat.card (Subgroup.centralizer (L : Set G))) := by rw [← hal]
      _ = (a * (l : G)⁻¹) ^ (Nat.card (Subgroup.centralizer (L : Set G))) *
          (l : G) ^ (Nat.card (Subgroup.centralizer (L : Set G))) := hcomm.mul_pow _
      _ = (l : G) ^ (Nat.card (Subgroup.centralizer (L : Set G))) := by rw [hpow, one_mul]
  rw [this]
  exact L.pow_mem l.2 _

theorem exists_zpow_pow_eq_of_pow_three {M : Type*} [Group M] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓ3 : ℓ ≠ 3) {z : M} (h3 : z ^ 3 = 1) : ∃ n : ℤ, (z ^ n) ^ ℓ = z := by
  have hcop : Nat.Coprime ℓ 3 := (Nat.coprime_primes hℓ Nat.prime_three).mpr hℓ3
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have huv' : u * (ℓ : ℤ) = 1 - ((3 : ℕ) : ℤ) * v := by linarith [huv]
  refine ⟨u, ?_⟩
  rw [← zpow_natCast, ← zpow_mul, huv', zpow_sub, zpow_one, zpow_mul, zpow_natCast, h3, one_zpow,
    inv_one, mul_one]

theorem eq_one_of_pow_prime_of_pow_three {M : Type*} [Group M] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓ3 : ℓ ≠ 3) {z : M} (h1 : z ^ ℓ = 1) (h3 : z ^ 3 = 1) : z = 1 := by
  obtain ⟨n, hn⟩ := exists_zpow_pow_eq_of_pow_three hℓ hℓ3 h3
  rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h1, one_zpow]

theorem exists_inverted_lift {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3)
    (hZ3 : ∀ z ∈ Subgroup.center L, z ^ 3 = 1) {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G))
    {y : L ⧸ Subgroup.center L} (hy : orderOf y = ℓ)
    (hay : normalizerAct L ⟨a, ha⟩ y = y⁻¹) :
    ∃ c : L, c ^ ℓ = 1 ∧ c ≠ 1 ∧ a * (c : G) * a⁻¹ = (c : G)⁻¹ := by
  obtain ⟨yl, rfl⟩ := QuotientGroup.mk_surjective y
  have hz₀ : yl ^ ℓ ∈ Subgroup.center L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hy]
    exact pow_orderOf_eq_one _
  obtain ⟨n, hn⟩ := exists_zpow_pow_eq_of_pow_three hℓ hℓ3 (hZ3 _ hz₀)
  set z₀ : L := yl ^ ℓ with hz₀def
  set w : L := z₀ ^ n with hw
  have hwc : w ∈ Subgroup.center L := Subgroup.zpow_mem _ hz₀ n
  have hwℓ : w ^ ℓ = z₀ := hn
  set c : L := yl * w⁻¹ with hc
  have hcomm : Commute yl w⁻¹ := (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hwc)) yl
  have hcℓ : c ^ ℓ = 1 := by
    rw [hc, hcomm.mul_pow, inv_pow, hwℓ, ← hz₀def, mul_inv_cancel]
  have hcy : (QuotientGroup.mk c : L ⧸ Subgroup.center L) = QuotientGroup.mk yl := by
    rw [hc, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      (QuotientGroup.eq_one_iff w).mpr hwc, inv_one, mul_one]
  have hc1 : c ≠ 1 := by
    intro h0
    rw [h0] at hcy
    have : (QuotientGroup.mk yl : L ⧸ Subgroup.center L) = 1 := by rw [← hcy]; rfl
    rw [this, orderOf_one] at hy
    exact hℓ.one_lt.ne hy
  refine ⟨c, hcℓ, hc1, ?_⟩
  set d : L := c * conjOn L ⟨a, ha⟩ c with hd
  have hdc : d ∈ Subgroup.center L := by
    rw [← QuotientGroup.eq_one_iff]
    have h1 := normalizerAct_apply_mk L ⟨a, ha⟩ c
    rw [hcy] at h1
    rw [hd, QuotientGroup.mk_mul, ← h1, hay, hcy, mul_inv_cancel]
  have h2 : conjOn L ⟨a, ha⟩ c = c⁻¹ * d := by rw [hd]; group
  have hdℓ : d ^ ℓ = 1 := by
    have h1 : (conjOn L ⟨a, ha⟩ c) ^ ℓ = 1 := by rw [← map_pow, hcℓ, map_one]
    rw [h2] at h1
    have hcd : Commute c⁻¹ d := (Subgroup.mem_center_iff.mp hdc) c⁻¹
    rw [hcd.mul_pow, inv_pow, hcℓ, inv_one, one_mul] at h1
    exact h1
  have hd1 : d = 1 :=
    eq_one_of_pow_prime_of_pow_three hℓ hℓ3 hdℓ (hZ3 d hdc)
  have hconj : conjOn L ⟨a, ha⟩ c = c⁻¹ := by rw [h2, hd1, mul_one]
  have := congrArg Subtype.val hconj
  rw [coe_conjOn] at this
  simpa using this

theorem conj_involution_inverting {M : Type*} [Group M] {a C : M} {m : ℕ} (ha2 : a * a = 1)
    (hac : a * C * a⁻¹ = C⁻¹) (hCℓ : C ^ (2 * m + 1) = 1) :
    C ^ m * a * (C ^ m)⁻¹ = a * C ∧ C = a * (a * C) := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hX : a * C ^ m * a⁻¹ = (C ^ m)⁻¹ := by
    rw [← conj_pow, hac, inv_pow]
  rw [ha'] at hX
  have h2 : C ^ m * C ^ m = C⁻¹ := by
    rw [← pow_add, ← two_mul]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hCℓ)
  have h3 : C ^ m * a = a * (C ^ m)⁻¹ := by
    calc C ^ m * a = (a * a) * C ^ m * a := by rw [ha2, one_mul]
      _ = a * (a * C ^ m * a) := by group
      _ = a * (C ^ m)⁻¹ := by rw [hX]
  refine ⟨?_, by rw [← mul_assoc, ha2, one_mul]⟩
  calc C ^ m * a * (C ^ m)⁻¹ = a * (C ^ m)⁻¹ * (C ^ m)⁻¹ := by rw [h3]
    _ = a * (C ^ m * C ^ m)⁻¹ := by rw [mul_assoc, ← mul_inv_rev]
    _ = a * C := by rw [h2, inv_inv]

end Normalizer

end CFSG.QuasithinUnique.Setup.X5
