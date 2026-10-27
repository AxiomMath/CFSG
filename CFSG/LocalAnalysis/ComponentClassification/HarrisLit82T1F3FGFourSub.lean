module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1NoSLTwoSolv
public import CFSG.ClassicalInvolution.Q3.Q3ZMat
public import CFSG.Monster.B.TwoA.Census.PermClasses

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup
open scoped MatrixGroups

theorem oPrimeResidual_normal (p : ℕ) (X : Type*) [Group X] :
    (GH74.GLS.oPrimeResidual p X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  unfold GH74.GLS.oPrimeResidual at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := hx
    exact subset_closure ⟨k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact inv_mem hx

theorem exists_pow_mul_coprime {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (g : X) :
    ∃ a ∈ zpowers g, ∃ b ∈ zpowers g, g = a * b ∧ (∃ k : ℕ, a ^ p ^ k = 1) ∧
      Nat.Coprime p (orderOf b) := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p hp.ne_one
  have hpm : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hm
  have hcop : Nat.Coprime (p ^ k) m := Nat.Coprime.pow_left _ hpm
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have hg : g ^ ((p ^ k * m : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, ← hn, pow_orderOf_eq_one]
  refine ⟨g ^ (v * m), zpow_mem (mem_zpowers g) _, g ^ (u * p ^ k),
    zpow_mem (mem_zpowers g) _, ?_, ⟨k, ?_⟩, ?_⟩
  · rw [← zpow_add, show v * (m : ℤ) + u * p ^ k = 1 by push_cast at huv; linear_combination huv,
      zpow_one]
  · rw [← zpow_natCast, ← zpow_mul, show v * (m : ℤ) * ((p ^ k : ℕ) : ℤ) =
      ((p ^ k * m : ℕ) : ℤ) * v by push_cast; ring, zpow_mul, hg, one_zpow]
  · apply Nat.Coprime.coprime_dvd_right _ hpm
    apply orderOf_dvd_of_pow_eq_one
    rw [← zpow_natCast, ← zpow_mul, show u * (p : ℤ) ^ k * (m : ℤ) =
      ((p ^ k * m : ℕ) : ℤ) * u by push_cast; ring, zpow_mul, hg, one_zpow]

theorem exists_pow_eq_one_of_surjective {X Y : Type*} [Group X] [Group Y] [Finite X] {p : ℕ}
    (hp : p.Prime) {π : X →* Y} (hπ : Function.Surjective π) {s : Y} {m : ℕ}
    (hs : s ^ p ^ m = 1) : ∃ a : X, (∃ k : ℕ, a ^ p ^ k = 1) ∧ π a = s := by
  obtain ⟨x, rfl⟩ := hπ s
  obtain ⟨a, -, b, hb, rfl, hak, hbc⟩ := exists_pow_mul_coprime hp x
  refine ⟨a, hak, ?_⟩
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hb
  have hbp : π b ^ p ^ m = 1 := by
    rw [← hn, map_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs,
      one_zpow]
  have h1 : orderOf (π b) ∣ p ^ m := orderOf_dvd_of_pow_eq_one hbp
  have h2 : Nat.Coprime (orderOf (π b)) (p ^ m) :=
    (Nat.Coprime.pow_left m (Nat.Coprime.coprime_dvd_right (orderOf_map_dvd π b) hbc)).symm
  have h3 : π b = 1 := orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 h1)
  rw [map_mul, h3, mul_one]

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem map_oPrimeResidual_three_eq_top (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, ZMod 3)) :
    (GH74.GLS.oPrimeResidual 3 ↥L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥L))) = ⊤ := by
  set π := e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥L)) with hπdef
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have key : ∀ s : SL(2, ZMod 3), s ^ 3 = 1 → s ∈ (GH74.GLS.oPrimeResidual 3 ↥L).map π := by
    intro s hs
    obtain ⟨a, ⟨k, hk⟩, rfl⟩ := exists_pow_eq_one_of_surjective Nat.prime_three hπ (m := 1)
      (by rw [pow_one]; exact hs)
    exact ⟨a, subset_closure ⟨k, hk⟩, rfl⟩
  rw [eq_top_iff, ← ClassicalInvolution.Q3.Q3Z.closure_xp_xm, closure_le]
  rintro s (rfl | rfl)
  · exact key _ (Subtype.ext (by decide +kernel))
  · exact key _ (Subtype.ext (by decide +kernel))

theorem exists_inv_mul_mem_pPrimeCore (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, ZMod 3)) (x : ↥L) :
    ∃ r ∈ GH74.GLS.oPrimeResidual 3 ↥L, r⁻¹ * x ∈ pPrimeCore 2 ↥L := by
  have hx : e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥L)) x ∈
      (GH74.GLS.oPrimeResidual 3 ↥L).map
        (e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥L))) := by
    rw [map_oPrimeResidual_three_eq_top e]
    exact mem_top _
  obtain ⟨r, hr, hrx⟩ := hx
  refine ⟨r, hr, ?_⟩
  rw [← QuotientGroup.eq_one_iff]
  apply e.injective
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, map_one]
  have h1 : e (QuotientGroup.mk r) = e (QuotientGroup.mk x) := hrx
  rw [h1, inv_mul_cancel]

theorem odd_index_oPrimeResidual_three (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, ZMod 3)) :
    Odd (GH74.GLS.oPrimeResidual 3 ↥L).index := by
  have := oPrimeResidual_normal 3 ↥L
  set R₀ := GH74.GLS.oPrimeResidual 3 ↥L
  let ψ : ↥(pPrimeCore 2 ↥L) →* ↥L ⧸ R₀ := (QuotientGroup.mk' R₀).comp (pPrimeCore 2 ↥L).subtype
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R₀ y
    obtain ⟨r, hr, hro⟩ := exists_inv_mul_mem_pPrimeCore e x
    refine ⟨⟨r⁻¹ * x, hro⟩, ?_⟩
    change QuotientGroup.mk' R₀ (r⁻¹ * x) = QuotientGroup.mk' R₀ x
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [show (r⁻¹ * x)⁻¹ * x = x⁻¹ * r * x by group]
    have h1 := (oPrimeResidual_normal 3 ↥L).conj_mem r hr x⁻¹
    rwa [inv_inv] at h1
  have hdvd : R₀.index ∣ Nat.card ↥(pPrimeCore 2 ↥L) := by
    rw [Subgroup.index]
    exact Subgroup.card_dvd_of_surjective hψ
  exact Odd.of_dvd_nat (Nat.coprime_two_left.mp
    (pPrimeCore_coprime_card : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥L)))) hdvd

theorem mem_oPrimeResidual_three_of_orderOf (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, ZMod 3))
    {z : ↥L} (hz : orderOf z = 2) : z ∈ GH74.GLS.oPrimeResidual 3 ↥L := by
  have := oPrimeResidual_normal 3 ↥L
  set R₀ := GH74.GLS.oPrimeResidual 3 ↥L
  have h1 : orderOf (QuotientGroup.mk z : ↥L ⧸ R₀) ∣ 2 := by
    rw [← hz]
    exact orderOf_map_dvd (QuotientGroup.mk' R₀) z
  have h2 : orderOf (QuotientGroup.mk z : ↥L ⧸ R₀) ∣ R₀.index := orderOf_dvd_natCard _
  have hcop : Nat.Coprime 2 R₀.index :=
    Nat.coprime_two_left.mpr (odd_index_oPrimeResidual_three e)
  have h3 : orderOf (QuotientGroup.mk z : ↥L ⧸ R₀) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  exact (QuotientGroup.eq_one_iff z).mp (orderOf_eq_one_iff.mp h3)

theorem nonempty_quot_equiv_sl23_of_isSubnormal {C : Subgroup G} (hLC : L ≤ C)
    (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, ZMod 3))
    (hJs : (((pPrimeCore 2 ↥C).map C.subtype ⊔ GH74.GLS.oPrimeResidualOf 3 L).subgroupOf
      C).IsSubnormal) :
    Nonempty (↥((pPrimeCore 2 ↥C).map C.subtype ⊔ GH74.GLS.oPrimeResidualOf 3 L) ⧸
      pPrimeCore 2 ↥((pPrimeCore 2 ↥C).map C.subtype ⊔ GH74.GLS.oPrimeResidualOf 3 L) ≃*
        SL(2, ZMod 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set OC := (pPrimeCore 2 ↥C).map C.subtype with hOC
  set R₀ := GH74.GLS.oPrimeResidual 3 ↥L with hR₀
  have hRL : GH74.GLS.oPrimeResidualOf 3 L ≤ L := map_subtype_le _
  have hOCC : OC ≤ C := map_subtype_le _
  have hJC : OC ⊔ GH74.GLS.oPrimeResidualOf 3 L ≤ C := sup_le hOCC (hRL.trans hLC)
  set J' := (OC ⊔ GH74.GLS.oPrimeResidualOf 3 L).subgroupOf C with hJ'
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hρ
  set ι : ↥L →* ↥C := Subgroup.inclusion hLC with hι
  set σ : ↥R₀ →* ↥C ⧸ pPrimeCore 2 ↥C := ρ.comp (ι.comp R₀.subtype) with hσ
  set π₀ : ↥R₀ →* SL(2, ZMod 3) :=
    (e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥L))).comp R₀.subtype with hπ₀def
  have hπ₀ : Function.Surjective π₀ := by
    intro s
    have hs : s ∈ R₀.map (e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥L))) := by
      rw [map_oPrimeResidual_three_eq_top e]
      exact mem_top s
    obtain ⟨r, hr, rfl⟩ := hs
    exact ⟨⟨r, hr⟩, rfl⟩
  have hrange : J'.map ρ = σ.range := by
    have h1 : J' = pPrimeCore 2 ↥C ⊔ R₀.map ι := by
      rw [hJ', subgroupOf_sup hOCC (hRL.trans hLC)]
      congr 1
      · ext x
        rw [mem_subgroupOf, hOC, mem_map]
        constructor
        · rintro ⟨y, hy, hyx⟩
          rwa [← Subtype.ext hyx]
        · intro hx
          exact ⟨x, hx, rfl⟩
      · ext x
        simp only [mem_subgroupOf, GH74.GLS.oPrimeResidualOf, mem_map]
        constructor
        · rintro ⟨y, hy, hyx⟩
          exact ⟨y, hy, Subtype.ext hyx⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨y, hy, rfl⟩
    rw [h1, Subgroup.map_sup,
      (Subgroup.map_eq_bot_iff _).mpr (by rw [hρ, QuotientGroup.ker_mk']), bot_sup_eq,
      hσ, MonoidHom.range_comp, MonoidHom.range_comp, range_subtype]
  have hJs' : σ.range.IsSubnormal := by
    rw [← hrange]
    exact hJs.map (QuotientGroup.mk'_surjective _)
  have hO : pPrimeCore 2 ↥σ.range = ⊥ := by
    rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 _ hJs',
      pPrimeCore_quotient_pPrimeCore_eq_bot 2]
    exact Subgroup.bot_subgroupOf _
  have hker : σ.ker = π₀.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : ι (x : ↥L) ∈ pPrimeCore 2 ↥C := (QuotientGroup.eq_one_iff _).mp hx
      have h2 : (pPrimeCore 2 ↥C).comap ι ≤ pPrimeCore 2 ↥L := by
        apply le_sSup
        refine ⟨(pPrimeCore_normal : (pPrimeCore 2 ↥C).Normal).comap ι, ?_⟩
        exact Nat.Coprime.coprime_dvd_right
          (Subgroup.card_comap_dvd_of_injective _ ι (Subgroup.inclusion_injective hLC))
          (pPrimeCore_coprime_card : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥C)))
      have h3 : (x : ↥L) ∈ pPrimeCore 2 ↥L := h2 h1
      change e (QuotientGroup.mk (x : ↥L)) = 1
      rw [(QuotientGroup.eq_one_iff _).mpr h3, map_one]
    · intro hx
      have h1 : (x : ↥L) ∈ pPrimeCore 2 ↥L := by
        have h0 : (QuotientGroup.mk (x : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) = 1 :=
          e.injective (by rw [map_one]; exact hx)
        exact (QuotientGroup.eq_one_iff _).mp h0
      set T : Subgroup ↥R₀ := (pPrimeCore 2 ↥L).comap R₀.subtype with hT
      have hTn : T.Normal := (pPrimeCore_normal : (pPrimeCore 2 ↥L).Normal).comap _
      set T' := T.map σ.rangeRestrict with hT'
      have hT'n : T'.Normal := hTn.map _ σ.rangeRestrict_surjective
      have hT'c : Nat.Coprime 2 (Nat.card T') := by
        refine Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) ?_
        exact Nat.Coprime.coprime_dvd_right
          (Subgroup.card_comap_dvd_of_injective _ _ R₀.subtype_injective)
          (pPrimeCore_coprime_card : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥L)))
      have hT'le : T' ≤ pPrimeCore 2 ↥σ.range := le_sSup ⟨hT'n, hT'c⟩
      rw [hO, le_bot_iff] at hT'le
      have hxT' : σ.rangeRestrict x ∈ T' := mem_map_of_mem _ (show x ∈ T from h1)
      rw [hT'le, mem_bot] at hxT'
      exact congrArg Subtype.val hxT'
  let e1 : ↥σ.range ≃* SL(2, ZMod 3) :=
    (QuotientGroup.quotientKerEquivRange σ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective π₀ hπ₀))
  set φ : ↥J' →* ↥C ⧸ pPrimeCore 2 ↥C := ρ.comp J'.subtype with hφ
  have hφk : φ.ker = pPrimeCore 2 ↥J' := by
    rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 J' hJs, hφ,
      ← MonoidHom.comap_ker, hρ, QuotientGroup.ker_mk']
    rfl
  have hφr : φ.range = σ.range := by
    rw [hφ, MonoidHom.range_comp, range_subtype, hrange]
  let e2 : ↥J' ⧸ pPrimeCore 2 ↥J' ≃* ↥σ.range :=
    (QuotientGroup.quotientMulEquivOfEq hφk.symm).trans
      ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hφr))
  let eJ : ↥(OC ⊔ GH74.GLS.oPrimeResidualOf 3 L) ≃* ↥J' := (subgroupOfEquivOfLe hJC).symm
  exact ⟨(QuotientGroup.congr _ _ eJ (pPrimeCore_map_iso 2 eJ)).trans (e2.trans e1)⟩

theorem not_isSubnormal_sup_oPrimeResidualOf_three
    (hCI : GSLit.ClassicalInvolutionInput) [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hcat : ¬ Blueprint.Catalog G) {z₁ : G} (hz₁ : orderOf z₁ = 2) {L₁ : Subgroup G}
    (hL₁C : L₁ ≤ centralizer {z₁}) (hz₁L : z₁ ∈ L₁)
    (e₁ : ↥L₁ ⧸ pPrimeCore 2 ↥L₁ ≃* SL(2, ZMod 3)) :
    ¬ (((pPrimeCore 2 ↥(centralizer ({z₁} : Set G))).map (centralizer {z₁}).subtype ⊔
        GH74.GLS.oPrimeResidualOf 3 L₁).subgroupOf (centralizer {z₁})).IsSubnormal := by
  intro hs
  obtain ⟨e₃⟩ := nonempty_quot_equiv_sl23_of_isSubnormal hL₁C e₁ hs
  have hz₁J : z₁ ∈ (pPrimeCore 2 ↥(centralizer ({z₁} : Set G))).map (centralizer {z₁}).subtype ⊔
      GH74.GLS.oPrimeResidualOf 3 L₁ := by
    apply mem_sup_right
    exact ⟨⟨z₁, hz₁L⟩, mem_oPrimeResidual_three_of_orderOf e₁
      (by rw [Subgroup.orderOf_mk]; exact hz₁), rfl⟩
  have hJC : (pPrimeCore 2 ↥(centralizer ({z₁} : Set G))).map (centralizer {z₁}).subtype ⊔
      GH74.GLS.oPrimeResidualOf 3 L₁ ≤ centralizer {z₁} :=
    sup_le (map_subtype_le _) ((map_subtype_le _).trans hL₁C)
  rcases oddLieType_or_m11_of_intrinsic_slTwoThree hCI hnonab hz₁ hJC hs hz₁J e₃ with
    ⟨t, n, p, f, -, -, -, hm⟩ | h
  · exact hcat (Blueprint.lieModel_catalog G t n p f hm)
  · exact hcat (.inr (.inr (.inr (.inr ⟨.M11, h⟩))))

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
