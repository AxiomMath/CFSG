module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL36a
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisOddCore

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

abbrev zM : D.M := ⟨D.z, D.z_mem_M⟩

abbrev lM : D.M := ⟨D.l, D.l_mem_M⟩

omit [Finite G] in
theorem zM_comm (g : D.M) : g * D.zM = D.zM * g :=
  Subtype.ext (mem_centralizer_singleton_iff.mp g.2)

omit [Finite G] in
instance zpowers_zM_normal : (zpowers D.zM).Normal := by
  constructor
  intro n hn g
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
  rw [((Commute.zpow_right (D.zM_comm g) k)).eq, mul_inv_cancel_right]
  exact zpow_mem (mem_zpowers _) k

omit [Finite G] in
theorem orderOf_zM : orderOf D.zM = 2 := by
  rw [Subgroup.orderOf_mk]
  exact orderOf_eq_prime (by rw [pow_two]; exact D.z_mul_z) D.z_ne_one

theorem mem_zpowers_zM_iff (x : D.M) : x ∈ zpowers D.zM ↔ (x : G) = 1 ∨ (x : G) = D.z := by
  classical
  constructor
  · intro hx
    rw [mem_zpowers_iff_mem_range_orderOf, D.orderOf_zM] at hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    interval_cases k
    · left; simp
    · right; simp
  · rintro (h | h)
    · rw [show x = 1 from Subtype.ext h]
      exact one_mem _
    · rw [show x = D.zM from Subtype.ext h]
      exact mem_zpowers _

theorem comm_l_mem_OM {g : G} (hg : g ∈ D.M) :
    g * D.l * g⁻¹ * D.l⁻¹ ∈ D.OM ∨ D.z * (g * D.l * g⁻¹ * D.l⁻¹) ∈ D.OM := by
  classical
  let : Fintype (D.M ⧸ zpowers D.zM) := Fintype.ofFinite _
  set t : D.M ⧸ zpowers D.zM := (D.lM : D.M ⧸ zpowers D.zM) with ht
  have ht1 : t ≠ 1 := by
    intro h
    rw [ht, QuotientGroup.eq_one_iff] at h
    rcases (D.mem_zpowers_zM_iff _).mp h with h | h
    · exact SE.gen1_ne_one (D.toG_injective (h.trans (map_one _).symm))
    · exact SE.gen1_ne_gen0 (D.toG_injective h)
  have ht2 : t * t = 1 := by
    rw [ht, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact (D.mem_zpowers_zM_iff _).mpr (Or.inr D.l_mul_l)
  have hiso : ∀ y : D.M ⧸ zpowers D.zM, (y * t * y⁻¹) * t = t * (y * t * y⁻¹) →
      y * t * y⁻¹ = t := by
    intro y
    refine QuotientGroup.induction_on y fun x hc => ?_
    rw [ht, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hc
    rw [ht, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      QuotientGroup.eq, D.mem_zpowers_zM_iff]
    rcases (D.mem_zpowers_zM_iff _).mp hc with h | h <;>
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    · have hcomm : (x : G) * D.l * (x : G)⁻¹ * D.l = D.l * ((x : G) * D.l * (x : G)⁻¹) :=
        inv_mul_eq_one.mp h
      have := D.isolated_l_mod_z x.2 (Or.inl hcomm)
      rcases this with h1 | h1 <;> simp only [Subgroup.coe_mul, Subgroup.coe_inv] <;> rw [h1]
      · left; group
      · right
        rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
        exact inv_eq_of_mul_eq_one_right D.z_mul_z
    · have hz2 : D.z * D.z = 1 := D.z_mul_z
      have h' : D.l * ((x : G) * D.l * (x : G)⁻¹) =
          (x : G) * D.l * (x : G)⁻¹ * D.l * D.z := by
        rw [← h]; group
      have := D.isolated_l_mod_z x.2 (Or.inr (by
        calc (x : G) * D.l * (x : G)⁻¹ * D.l =
            (x : G) * D.l * (x : G)⁻¹ * D.l * D.z * D.z := by rw [mul_assoc _ D.z, hz2, mul_one]
          _ = D.l * ((x : G) * D.l * (x : G)⁻¹) * D.z := by rw [← h']))
      rcases this with h1 | h1 <;> simp only [Subgroup.coe_mul, Subgroup.coe_inv] <;> rw [h1]
      · left; group
      · right
        rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
        exact inv_eq_of_mul_eq_one_right hz2
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar (D.M ⧸ zpowers D.zM) t ht1 ht2 hiso
  set N' := N.comap (QuotientGroup.mk' (zpowers D.zM)) with hN'
  have hN'n : N'.Normal := hNn.comap _
  set f := (QuotientGroup.mk' (zpowers D.zM)).subgroupComap N with hf
  have hfs : Function.Surjective f :=
    MonoidHom.subgroupComap_surjective _ _ (QuotientGroup.mk'_surjective _)
  have hzN' : D.zM ∈ N' := by
    rw [hN', mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr (mem_zpowers _)]
    exact one_mem _
  set zN : N' := ⟨D.zM, hzN'⟩ with hzN
  have hzNc : ∀ n : N', n * zN = zN * n := fun n => Subtype.ext (D.zM_comm n)
  have hzN2 : orderOf zN = 2 := by rw [Subgroup.orderOf_mk]; exact D.orderOf_zM
  have hker : f.ker = zpowers zN := by
    ext n
    rw [MonoidHom.mem_ker]
    have hiff : n ∈ zpowers zN ↔ (n : D.M) ∈ zpowers D.zM := by
      rw [mem_zpowers_iff, mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, by rw [← hk, Subgroup.coe_zpow]⟩
      · rintro ⟨k, hk⟩
        exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow, hk])⟩
    rw [hiff, ← QuotientGroup.eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  obtain ⟨K, hK, hKz⟩ := exists_oddPart hzNc hzN2 f hfs hker hNodd
  set KG : Subgroup G := (K.map N'.subtype).map D.M.subtype with hKG
  have hKodd : Odd (Nat.card K) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (even_iff_two_dvd.mp hev)
    have := (hK k).mp k.2
    rw [Subgroup.orderOf_coe, hk] at this
    exact (Nat.not_odd_iff_even.mpr even_two) this
  have hKGOM : KG ≤ D.OM := by
    refine D.le_OM (map_subtype_le _) (fun g hg k hk => ?_) (by
      rw [hKG, card_map_of_injective D.M.subtype_injective,
        card_map_of_injective N'.subtype_injective]
      exact hKodd)
    obtain ⟨_, ⟨k₀, hk₀, rfl⟩, rfl⟩ := hk
    have hmem : (⟨g, hg⟩ : D.M) * (k₀ : D.M) * (⟨g, hg⟩ : D.M)⁻¹ ∈ N' :=
      hN'n.conj_mem _ k₀.2 _
    have hodd : Odd (orderOf (⟨_, hmem⟩ : N')) := by
      have hord : orderOf ((⟨g, hg⟩ : D.M) * (k₀ : D.M) * (⟨g, hg⟩ : D.M)⁻¹) =
          orderOf (k₀ : D.M) := (MulAut.conj (⟨g, hg⟩ : D.M)).orderOf_eq k₀.1
      rw [Subgroup.orderOf_mk, hord, Subgroup.orderOf_coe]
      exact (hK k₀).mp hk₀
    exact ⟨_, ⟨_, (hK _).mpr hodd, rfl⟩, rfl⟩
  have hc : (⟨g, hg⟩ : D.M) * D.lM * (⟨g, hg⟩ : D.M)⁻¹ * D.lM⁻¹ ∈ N' := by
    rw [hN', mem_comap, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hN _
  rcases hKz ⟨_, hc⟩ with h | h
  · left
    exact hKGOM ⟨_, ⟨_, h, rfl⟩, rfl⟩
  · right
    exact hKGOM ⟨_, ⟨_, h, rfl⟩, rfl⟩

end GHSylow

end CFSG.ComponentClassification.GHarris
