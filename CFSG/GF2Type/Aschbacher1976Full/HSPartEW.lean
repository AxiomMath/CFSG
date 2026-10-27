module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GF2Type.Aschbacher1976Full.HSPartEBasis
public import CFSG.GF2Type.Aschbacher1976Full.WidthTI

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.PartE

variable {G : Type} [Group G] [Finite G] {z : G} {T V : Subgroup G}

@[expose] noncomputable def z4Hom {W : Type*} [Group W] (k : W) (hk : k ^ 4 = 1) :
    Multiplicative (ZMod 4) →* W :=
  AddMonoidHom.toMultiplicativeLeft (ZMod.lift 4
    ⟨zmultiplesHom (Additive W) (Additive.ofMul k), by
      rw [zmultiplesHom_apply]
      show ((4 : ℕ) : ℤ) • Additive.ofMul k = 0
      rw [natCast_zsmul, ← ofMul_pow, hk]
      rfl⟩)

theorem z4Hom_apply {W : Type*} [Group W] (k : W) (hk : k ^ 4 = 1) (i : ℤ) :
    z4Hom k hk (Multiplicative.ofAdd (i : ZMod 4)) = k ^ i := by
  simp [z4Hom, ZMod.lift_coe]

theorem isZ4Cube_of_gens {W : Type*} [Group W] [Finite W] (hW : Nat.card W = 64)
    (hcomm : ∀ a b : W, a * b = b * a) (k₀ k₁ k₂ : W)
    (h₀ : k₀ ^ 4 = 1) (h₁ : k₁ ^ 4 = 1) (h₂ : k₂ ^ 4 = 1)
    (hind : ∀ i j l : ℤ, k₀ ^ i * k₁ ^ j * k₂ ^ l = 1 →
      (4 : ℤ) ∣ i ∧ (4 : ℤ) ∣ j ∧ (4 : ℤ) ∣ l) :
    CFSG.Quasithin.HSType.IsZ4Cube W := by
  let ψ : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* W :=
    (z4Hom k₀ h₀).noncommCoprod
      ((z4Hom k₁ h₁).noncommCoprod (z4Hom k₂ h₂) fun _ _ => hcomm _ _) fun _ _ => hcomm _ _
  have hψ : ∀ i j l : ℤ, ψ (Multiplicative.ofAdd (i : ZMod 4), Multiplicative.ofAdd (j : ZMod 4),
      Multiplicative.ofAdd (l : ZMod 4)) = k₀ ^ i * (k₁ ^ j * k₂ ^ l) := by
    intro i j l
    show z4Hom k₀ h₀ _ * (z4Hom k₁ h₁ _ * z4Hom k₂ h₂ _) = _
    rw [z4Hom_apply, z4Hom_apply, z4Hom_apply]
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b, c⟩ h
    obtain ⟨i, hi⟩ := ZMod.intCast_surjective (Multiplicative.toAdd a)
    obtain ⟨j, hj⟩ := ZMod.intCast_surjective (Multiplicative.toAdd b)
    obtain ⟨l, hl⟩ := ZMod.intCast_surjective (Multiplicative.toAdd c)
    have ha : a = Multiplicative.ofAdd (i : ZMod 4) := by rw [hi]; rfl
    have hb : b = Multiplicative.ofAdd (j : ZMod 4) := by rw [hj]; rfl
    have hc : c = Multiplicative.ofAdd (l : ZMod 4) := by rw [hl]; rfl
    rw [ha, hb, hc, hψ, ← mul_assoc] at h
    obtain ⟨h1, h2, h3⟩ := hind i j l h
    have e : ∀ n : ℤ, (4 : ℤ) ∣ n →
        (Multiplicative.ofAdd (n : ZMod 4) : Multiplicative (ZMod 4)) = 1 := fun n hn => by
      rw [← ofAdd_zero]
      congr 1
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd n 4).mpr hn
    rw [ha, hb, hc, e i h1, e j h2, e l h3]
    rfl
  have hbij : Function.Bijective ψ := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [hW]
    simp [Nat.card_prod]
  exact ⟨(MulEquiv.ofBijective ψ hbij).symm⟩

theorem exists_sqrt_mem_ZF (hset : HSSetting G z) {v : G} (hv : IsConj z v) :
    ∃ y ∈ ZF v, y ^ 2 = v := by
  have hz : orderOf z = 2 := hset.1.2.2.1
  have hF2 : IsPGroup 2 ↥(Fz z) := hset.1.2.2.2.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hset.2
  obtain ⟨k, hkZ, -, -, hk2⟩ := Width.exists_gen_Z hD hz
  obtain ⟨c, rfl⟩ := isConj_iff.mp hv
  refine ⟨c * k * c⁻¹, ?_, by rw [conj_pow, hk2]⟩
  have h1 : c⁻¹⁻¹ * z * c⁻¹ = c * z * c⁻¹ := by rw [inv_inv]
  show c * k * c⁻¹ ∈ CFSG.GF2Type.CenterFour.centerAt (c * z * c⁻¹)
  rw [← h1, CFSG.GF2Type.CenterFour.centerAt_conj, Width.mem_conjugate_iff,
    show c⁻¹ * (c * k * c⁻¹) * c⁻¹⁻¹ = k by group]
  exact (Width.mem_centerAt_iff hD hz hF2).mpr hkZ

theorem isZ4Cube_WT (hset : HSSetting G z) (hV : HSV z T V) :
    CFSG.Quasithin.HSType.IsZ4Cube ↥(WT T z) := by
  have hz : orderOf z = 2 := hset.1.2.2.1
  have hF2 : IsPGroup 2 ↥(Fz z) := hset.1.2.2.2.1
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  have hz2 : z * z = 1 := by rw [← sq]; exact Width.z_sq hz
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hset.2
  obtain ⟨t₁, t₂, hb⟩ := exists_basis hz hV
  have ht1 := (ne_one_ne_z_of_not_mem hb.not_mem₁).1
  have ht2 := (ne_one_ne_z_of_not_mem hb.not_mem₂).1
  have h1 : t₁ * t₁ = 1 := hsAut_mul_self hV hb.mem₁
  have h2 : t₂ * t₂ = 1 := hsAut_mul_self hV hb.mem₂
  obtain ⟨k₀, hk₀Z, -, -, hk₀⟩ := Width.exists_gen_Z hD hz
  have hk₀W : k₀ ∈ WT T z :=
    hV.ZF_le_W z hV.z_mem hz1 ((Width.mem_centerAt_iff hD hz hF2).mpr hk₀Z)
  obtain ⟨k₁, hk₁ZF, hk₁⟩ := exists_sqrt_mem_ZF hset (hV.isConj t₁ hb.mem₁ ht1)
  obtain ⟨k₂, hk₂ZF, hk₂⟩ := exists_sqrt_mem_ZF hset (hV.isConj t₂ hb.mem₂ ht2)
  have hk₁W : k₁ ∈ WT T z := hV.ZF_le_W t₁ hb.mem₁ ht1 hk₁ZF
  have hk₂W : k₂ ∈ WT T z := hV.ZF_le_W t₂ hb.mem₂ ht2 hk₂ZF
  have hfour : ∀ {k v : G}, k ^ 2 = v → v * v = 1 → k ^ 4 = 1 := fun hk hv => by
    rw [show 4 = 2 * 2 by norm_num, pow_mul, hk, sq, hv]
  have c01 : Commute k₀ k₁ := hV.W_comm k₀ hk₀W k₁ hk₁W
  have c02 : Commute k₀ k₂ := hV.W_comm k₀ hk₀W k₂ hk₂W
  have c12 : Commute k₁ k₂ := hV.W_comm k₁ hk₁W k₂ hk₂W
  have sqpow : ∀ (g : G) (n : ℤ), (g ^ n) ^ 2 = (g ^ 2) ^ n := fun g n => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  have evenpow : ∀ (g v : G) (r : ℤ), g ^ 2 = v → g ^ (2 * r) = v ^ r := fun g v r hg => by
    rw [zpow_mul]
    simp [hg]
  refine isZ4Cube_of_gens (W := ↥(WT T z)) hV.card_W
    (fun a b => Subtype.ext (hV.W_comm a a.2 b b.2)) ⟨k₀, hk₀W⟩ ⟨k₁, hk₁W⟩ ⟨k₂, hk₂W⟩
    (Subtype.ext (hfour hk₀ hz2)) (Subtype.ext (hfour hk₁ h1)) (Subtype.ext (hfour hk₂ h2)) ?_
  intro i j l h
  have hrel : k₀ ^ i * k₁ ^ j * k₂ ^ l = 1 := by
    have := congrArg Subtype.val h
    simpa using this
  have hsq : z ^ i * t₁ ^ j * t₂ ^ l = 1 := by
    have e : (k₀ ^ i * k₁ ^ j * k₂ ^ l) ^ 2 =
        (k₀ ^ 2) ^ i * (k₁ ^ 2) ^ j * (k₂ ^ 2) ^ l := by
      have cab : Commute (k₀ ^ i) (k₁ ^ j) := c01.zpow_zpow i j
      have cac : Commute (k₀ ^ i) (k₂ ^ l) := c02.zpow_zpow i l
      have cbc : Commute (k₁ ^ j) (k₂ ^ l) := c12.zpow_zpow j l
      rw [(cac.mul_left cbc).mul_pow, cab.mul_pow, sqpow, sqpow, sqpow]
    have h' : (k₀ ^ i * k₁ ^ j * k₂ ^ l) ^ 2 = 1 := by rw [hrel]; exact one_pow _
    rw [e, hk₀, hk₁, hk₂] at h'
    exact h'
  obtain ⟨hi, hj, hl⟩ := independent_of_basis hz1 hz2 h1 h2 hb i j l hsq
  obtain ⟨r, rfl⟩ := even_iff_two_dvd.mp hi
  obtain ⟨r', rfl⟩ := even_iff_two_dvd.mp hj
  obtain ⟨r'', rfl⟩ := even_iff_two_dvd.mp hl
  rw [evenpow k₀ z r hk₀, evenpow k₁ t₁ r' hk₁, evenpow k₂ t₂ r'' hk₂] at hrel
  obtain ⟨hr, hr', hr''⟩ := independent_of_basis hz1 hz2 h1 h2 hb r r' r'' hrel
  obtain ⟨s, rfl⟩ := even_iff_two_dvd.mp hr
  obtain ⟨s', rfl⟩ := even_iff_two_dvd.mp hr'
  obtain ⟨s'', rfl⟩ := even_iff_two_dvd.mp hr''
  exact ⟨⟨s, by ring⟩, ⟨s', by ring⟩, ⟨s'', by ring⟩⟩

end CFSG.GF2Type.Aschbacher1976Full.HS.PartE
