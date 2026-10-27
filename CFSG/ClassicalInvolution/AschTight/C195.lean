module

public import CFSG.ClassicalInvolution.AschTight.C195Field
public import CFSG.ClassicalInvolution.AschTight.E3ModAut
public import CFSG.ClassicalInvolution.AschTight.TzFusion

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62 CFSG.ABGLocalTools
  CFSG.GorensteinWalter
open scoped MatrixGroups

section Action

variable {G : Type} [Group G] {K : Subgroup G} {F : Type} [Field F] [Finite F]

theorem pGammaL2ToMulAutPSL2_normalizerToPGammaL2Mod
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (hF : IsOddPrimePower (Nat.card F)) (h3 : 3 < Nat.card F)
    (n : Subgroup.normalizer (K : Set G)) :
    pGammaL2ToMulAutPSL2 F hF h3 (normalizerToPGammaL2Mod e hFcard hF h3 n) =
      psl2MulAutOf (MulAut.congr e (oddCoreQuotientAut K (normalizerConj K n))) := by
  simp only [normalizerToPGammaL2Mod, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom]
  exact (MulEquiv.apply_symm_apply (MulEquiv.ofBijective (pGammaL2ToMulAutPSL2 F hF h3)
    ⟨pGammaL2ToMulAutPSL2_injective F hF h3,
      pGammaL2ToMulAutPSL2_surjective F hFcard hF h3⟩) _).trans rfl

omit [Finite F] in
theorem congr_oddCoreQuotientAut_apply (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F))
    (n : Subgroup.normalizer (K : Set G)) (y : K) :
    MulAut.congr e (oddCoreQuotientAut K (normalizerConj K n)) (e (QuotientGroup.mk y)) =
      e (QuotientGroup.mk (normalizerConj K n y)) := by
  rw [MulAut.congr_apply]
  simp [oddCoreQuotientAut_mk]

theorem normalizerToPGammaL2Mod_mem_range_inl_of_mem
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (hF : IsOddPrimePower (Nat.card F)) (h3 : 3 < Nat.card F)
    {k : G} (hk : k ∈ K) (hkN : k ∈ Subgroup.normalizer (K : Set G)) :
    normalizerToPGammaL2Mod e hFcard hF h3 ⟨k, hkN⟩ ∈
      (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range := by
  set γ := normalizerToPGammaL2Mod e hFcard hF h3 ⟨k, hkN⟩ with hγdef
  obtain ⟨Gm, hGm⟩ := exists_eq_semilinHom hF h3
    (pGammaL2ToMulAutPSL2_normalizerToPGammaL2Mod e hFcard hF h3 ⟨k, hkN⟩)
  have hσ : γ.right = 1 := by
    refine eq_one_of_semilinHom_eq_conj Gm γ.right (e (QuotientGroup.mk ⟨k, hk⟩)) fun b => ?_
    rw [← hGm]
    obtain ⟨κ, hκ⟩ := QuotientGroup.mk_surjective (e.symm b)
    have hb : b = e (QuotientGroup.mk κ) := by rw [hκ, MulEquiv.apply_symm_apply]
    have hc : normalizerConj K ⟨k, hkN⟩ κ = ⟨k, hk⟩ * κ * ⟨k, hk⟩⁻¹ :=
      Subtype.ext (by rw [normalizerConj_apply_coe]; rfl)
    rw [hb, congr_oddCoreQuotientAut_apply, hc, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, map_mul, map_mul, map_inv]
  refine ⟨γ.left, ?_⟩
  conv_rhs => rw [← SemidirectProduct.inl_left_mul_inr_right γ]
  rw [hσ, map_one, mul_one]

end Action

section Image

variable {G : Type} [Group G]

theorem card_map_of_inf_ker_eq_bot {A B : Type*} [Group A] [Group B] (φ : A →* B)
    {H : Subgroup A} (h : H ⊓ φ.ker = ⊥) : Nat.card ↥(H.map φ) = Nat.card H := by
  refine (Nat.card_eq_of_bijective (fun x : H => (⟨φ x, x, x.2, rfl⟩ : ↥(H.map φ)))
    ⟨fun x y hxy => ?_, ?_⟩).symm
  · have h1 : φ ((x : A)⁻¹ * y) = 1 := by
      have h2 := congrArg Subtype.val hxy
      simp only at h2
      rw [map_mul, map_inv, h2, inv_mul_cancel]
    have h2 : (x : A)⁻¹ * y ∈ H ⊓ φ.ker := ⟨H.mul_mem (H.inv_mem x.2) y.2, h1⟩
    rw [h, Subgroup.mem_bot] at h2
    exact Subtype.ext (inv_mul_eq_one.mp h2)
  · rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem inf_oddCore_eq_bot {L : Type} [Group L] [Finite L] {H : Subgroup L} (hH : IsPGroup 2 H) :
    H ⊓ classicalInvolutionOddCore L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [hk]
  exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr
    (CFSG.ComponentClassification.OddCore.odd_card L))

theorem isPGroup_zpowers_mk {H A : Subgroup G} (hA : IsPGroup 2 A) {a : G} (ha : a ∈ A)
    (haH : a ∈ H) : IsPGroup 2 (Subgroup.zpowers (⟨a, haH⟩ : H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hA ⟨a, ha⟩
  refine IsPGroup.of_card (n := n) ?_
  rw [Nat.card_zpowers, Subgroup.orderOf_mk, ← hn, Subgroup.orderOf_mk]

theorem mem_range_inl_of_right_eq_one {F : Type} [Field F] {γ : PGammaL2 F} (h : γ.right = 1) :
    γ ∈ (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range := by
  refine ⟨γ.left, ?_⟩
  conv_rhs => rw [← SemidirectProduct.inl_left_mul_inr_right γ]
  rw [h, map_one, mul_one]

end Image

section Tight

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem centralizer_le_normalizer_conjSub (ht : S19R.TightStdDelta p f K z) (g : G) :
    Subgroup.centralizer ({g * z * g⁻¹} : Set G) ≤
      Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) := by
  intro c hc
  have h1 : g⁻¹ * c * g ∈ Subgroup.normalizer (K : Set G) := by
    rw [normalizer_eq_centralizer_of_tight ht, Subgroup.mem_centralizer_singleton_iff]
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc g⁻¹ * c * g * z = g⁻¹ * (c * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * c) * g := by rw [h2]
      _ = z * (g⁻¹ * c * g) := by group
  rw [mem_normalizer_iff_conjSub_eq]
  have h3 := mem_normalizer_iff_conjSub_eq.mp h1
  calc conjSub c (conjSub g K) = conjSub (c * g) K := (conjSub_mul c g K).symm
    _ = conjSub (g * (g⁻¹ * c * g)) K := by congr 1; group
    _ = conjSub g (conjSub (g⁻¹ * c * g) K) := conjSub_mul _ _ _
    _ = conjSub g K := by rw [h3]

theorem exists_mul_self_eq_of_isCyclic {V J : Subgroup G} {t : G} (hJt : IsUniqueInvolution J t)
    (hVJ : V ≤ J) (hVc : IsCyclic V) (hV2 : IsPGroup 2 V) (hV4 : 4 ≤ Nat.card V) :
    ∃ w ∈ V, w * w = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := hVc.exists_generator
  have hxo : orderOf (x : G) = Nat.card V := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hx]
  obtain ⟨k, hk⟩ := hV2.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra hk2
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hpow : 2 ^ k = 4 * 2 ^ (k - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  obtain ⟨m, hm⟩ : ∃ m, m = 2 ^ (k - 2) := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; positivity
  have hn : orderOf (x : G) = 4 * m := by rw [hxo, hk, hpow, hm]
  have hx2 : (x : G) ^ (2 * m) * (x : G) ^ (2 * m) = 1 := by
    rw [← pow_add, show 2 * m + 2 * m = 4 * m by ring, ← hn, pow_orderOf_eq_one]
  have hx1 : (x : G) ^ (2 * m) ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
  have hxt := (hJt.unique _ (hVJ (V.pow_mem x.2 _)) hx2).resolve_left hx1
  refine ⟨(x : G) ^ m, V.pow_mem x.2 _, ?_⟩
  rw [← pow_add, show m + m = 2 * m by ring, hxt]

theorem mem_range_inl_of_centralizes (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hfe : Even f)
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    (hFcard : Nat.card (GaloisField p f) = p ^ f)
    (hF : IsOddPrimePower (Nat.card (GaloisField p f))) (h3 : 3 < Nat.card (GaloisField p f))
    {R₀ B : Subgroup G} (hR₀R : R₀ ∈ RSet (CoreAssembly.conjClass K)) (hR₀K : R₀ ≤ K)
    (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hBcard : Nat.card R₀ ≤ 2 * Nat.card ↥(R₀ ⊓ B))
    {a : G} (ha2 : ∃ n : ℕ, orderOf a = 2 ^ n) (haN : a ∈ Subgroup.normalizer (K : Set G))
    (hac : ∀ y ∈ R₀ ⊓ B, a * y = y * a) :
    normalizerToPGammaL2Mod e hFcard hF h3 ⟨a, haN⟩ ∈
      (SemidirectProduct.inl : PGL2 (GaloisField p f) →* PGammaL2 (GaloisField p f)).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR₀2 : IsPGroup 2 R₀ := isPGroup_of_mem_rSet hR₀R
  obtain ⟨J₀, hJ₀, Q₀, hQ₀⟩ := hR₀R
  obtain ⟨g₀, rfl⟩ := CoreAssembly.single_class K J₀ hJ₀
  have hR₀card : Nat.card ↥(R₀.subgroupOf K) = 2 ^ (Nat.card K).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀K).toEquiv, hQ₀,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _), Sylow.card_eq_multiplicity,
      show Nat.card ↥(conjSub g₀ K) = Nat.card K from
        Subgroup.card_map_of_injective (MulAut.conj g₀).injective]
  set Q₁ : Sylow 2 K := Sylow.ofCard (R₀.subgroupOf K) hR₀card with hQ₁
  set φ : K →* SL(2, GaloisField p f) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore ↥K)) with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφker : φ.ker = classicalInvolutionOddCore ↥K := by
    ext x
    simp [hφ]
  set P₁ : Sylow 2 SL(2, GaloisField p f) := Q₁.mapSurjective hφs with hP₁
  set D₁ : Subgroup SL(2, GaloisField p f) := ((R₀ ⊓ B).subgroupOf K).map φ with hD₁
  have hD₁P : D₁ ≤ P₁ := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx).1
  have hD₁ab : ∀ x ∈ D₁, ∀ y ∈ D₁, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext
      (hBab _ (Subgroup.mem_subgroupOf.mp hx).2 _ (Subgroup.mem_subgroupOf.mp hy).2)
  have hk1 : R₀.subgroupOf K ⊓ φ.ker = ⊥ := by
    rw [hφker]
    exact inf_oddCore_eq_bot hR₀2.comap_subtype
  have hk2 : (R₀ ⊓ B).subgroupOf K ⊓ φ.ker = ⊥ := by
    rw [hφker]
    exact inf_oddCore_eq_bot (hR₀2.to_le inf_le_left).comap_subtype
  have hD₁card : Nat.card P₁ ≤ 2 * Nat.card D₁ := by
    have h1 : Nat.card P₁ = Nat.card R₀ := by
      change Nat.card ↥((R₀.subgroupOf K).map φ) = _
      rw [card_map_of_inf_ker_eq_bot φ hk1]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀K).toEquiv
    have h2 : Nat.card D₁ = Nat.card ↥(R₀ ⊓ B) := by
      change Nat.card ↥(((R₀ ⊓ B).subgroupOf K).map φ) = _
      rw [card_map_of_inf_ker_eq_bot φ hk2]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hR₀K)).toEquiv
    omega
  have hfix : ∀ x ∈ D₁,
      MulAut.congr e (oddCoreQuotientAut K (normalizerConj K ⟨a, haN⟩)) x = x := by
    rintro _ ⟨y, hy, rfl⟩
    change MulAut.congr e (oddCoreQuotientAut K (normalizerConj K ⟨a, haN⟩))
      (e (QuotientGroup.mk y)) = e (QuotientGroup.mk y)
    rw [congr_oddCoreQuotientAut_apply]
    congr 2
    apply Subtype.ext
    rw [normalizerConj_apply_coe]
    have hc := hac y (Subgroup.mem_subgroupOf.mp hy)
    calc a * (y : G) * a⁻¹ = y * a * a⁻¹ := by rw [hc]
      _ = y := by group
  obtain ⟨n, hn⟩ := ha2
  have hγn : normalizerToPGammaL2Mod e hFcard hF h3 ⟨a, haN⟩ ^ 2 ^ n = 1 := by
    have hord : orderOf (⟨a, haN⟩ : Subgroup.normalizer (K : Set G)) = 2 ^ n := by
      rw [Subgroup.orderOf_mk, hn]
    rw [← map_pow, ← hord, pow_orderOf_eq_one, map_one]
  exact mem_range_inl_of_right_eq_one (right_eq_one_of_fixes_index_two hp hq hfe hF h3 P₁ hD₁P
    hD₁ab hD₁card n _ _ (pGammaL2ToMulAutPSL2_normalizerToPGammaL2Mod e hFcard hF h3 ⟨a, haN⟩)
    hγn hfix)

end Tight

end CFSG.ClassicalInvolution.Disconnected.AschTight
