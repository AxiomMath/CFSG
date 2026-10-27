module

public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPair

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.Walter.Ree.Model
open CFSG.ComponentClassification.CatalogueBSmallRee

theorem smallReeInvCentralizer_simple_normal (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    ∃ (N : Subgroup (smallReeInvCentralizer a K)) (_ : N.Normal), IsSimpleGroup N ∧
      Group.IsSolvable (smallReeInvCentralizer a K ⧸ N) := by
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨ψ, hψC, -, -, -, -, -, ⟨hsup, -, hcent⟩, e, -⟩ :=
    small_Ree_involution_centralizer_PSL2_structure a K hK w₀ hw₀
  set C := smallReeInvCentralizer a K with hCdef
  set t := smallReeH a K (-1) with htdef
  have hLC : ψ.range ≤ C := by
    rintro _ ⟨g, rfl⟩
    exact hψC g
  have htC : t ∈ C := hsup ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  set N := ψ.range.subgroupOf C with hNdef
  have hNn : N.Normal := by
    rw [hNdef, Subgroup.normal_subgroupOf_iff_le_normalizer hLC, ← hsup]
    exact sup_le (hcent.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hT : Subgroup.zpowers (⟨t, htC⟩ : C) ⊔ N = ⊤ := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hNdef, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hLC, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hsup
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' N).comp (Subgroup.zpowers (⟨t, htC⟩ : C)).subtype) := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hc : c ∈ (Subgroup.zpowers (⟨t, htC⟩ : C) ⊔ N : Subgroup C) := hT ▸ Subgroup.mem_top c
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hc
    obtain ⟨x, hx, n, hn, rfl⟩ := hc
    refine ⟨⟨x, hx⟩, ?_⟩
    have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    change QuotientGroup.mk' N x = QuotientGroup.mk' N (x * n)
    rw [map_mul, hn1, mul_one]
  have : IsCyclic (C ⧸ N) := isCyclic_of_surjective _ hsurj
  have hq27 : 27 ≤ Nat.card K := by
    rw [hK]
    calc 27 = 3 ^ (2 * 1 + 1) := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  let e' : N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    (Subgroup.subgroupOfEquivOfLe hLC).trans e.symm
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2 K le_rfl (Or.inr (by omega))
      (Or.inr (by omega))
  exact ⟨N, hNn, e'.isSimpleGroup, isSolvable_of_isCyclic⟩

theorem pairConfig_smallRee_false {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1))
    {x : ReeTag.G2.reeGamma K a} {K₁ K₂ : Subgroup (ReeTag.G2.reeGamma K a)}
    (hc : PairConfig _ x K₁ K₂) : False := by
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨-, -, -, -, -, hfus⟩ := small_Ree_prime_field_involution_fusion a K hK w₀ hw₀
  obtain ⟨g, hgΓ, hgx⟩ := hfus x x.2
    (by rw [Subgroup.orderOf_coe]; exact hc.orderOf_x)
  have h1 : (centralizer ({x} : Set (ReeTag.G2.reeGamma K a))).map
      (ReeTag.G2.reeGamma K a).subtype =
      (ReeTag.G2.reeGamma K a) ⊓ centralizer ({(x : ModGL ReeTag.G2.tag K)} : Set _) := by
    ext y
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, congrArg Subtype.val hy⟩
    · rintro ⟨hy, hyx⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hyx, rfl⟩
  have h2 : ((ReeTag.G2.reeGamma K a) ⊓ centralizer ({(x : ModGL ReeTag.G2.tag K)} : Set _)).map
      (MulAut.conj g).toMonoidHom = smallReeInvCentralizer a K := by
    ext y
    rw [smallReeInvCentralizer]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hzΓ, hzx⟩ := mem_inf.1 hz
      rw [mem_centralizer_singleton_iff] at hzx
      refine mem_inf.2 ⟨?_, ?_⟩
      · change g * z * g⁻¹ ∈ (ReeTag.G2.reeGamma K a)
        exact (ReeTag.G2.reeGamma K a).mul_mem ((ReeTag.G2.reeGamma K a).mul_mem hgΓ hzΓ)
          ((ReeTag.G2.reeGamma K a).inv_mem hgΓ)
      · rw [mem_centralizer_singleton_iff, ← hgx]
        change g * z * g⁻¹ * (g * (x : ModGL ReeTag.G2.tag K) * g⁻¹) =
          g * (x : ModGL ReeTag.G2.tag K) * g⁻¹ * (g * z * g⁻¹)
        calc g * z * g⁻¹ * (g * (x : ModGL ReeTag.G2.tag K) * g⁻¹)
            = g * (z * x) * g⁻¹ := by group
          _ = g * (x * z) * g⁻¹ := by rw [hzx]
          _ = _ := by group
    · intro hy
      obtain ⟨hyΓ, hyt⟩ := mem_inf.1 hy
      rw [mem_centralizer_singleton_iff, ← hgx] at hyt
      refine ⟨g⁻¹ * y * g, mem_inf.2 ⟨(ReeTag.G2.reeGamma K a).mul_mem
        ((ReeTag.G2.reeGamma K a).mul_mem ((ReeTag.G2.reeGamma K a).inv_mem hgΓ) hyΓ) hgΓ, ?_⟩,
        ?_⟩
      · rw [mem_centralizer_singleton_iff]
        calc g⁻¹ * y * g * (x : ModGL ReeTag.G2.tag K)
            = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hyt]
          _ = _ := by group
      · change g * (g⁻¹ * y * g) * g⁻¹ = y
        group
  have e : ↥(centralizer ({x} : Set (ReeTag.G2.reeGamma K a))) ≃*
      ↥(smallReeInvCentralizer a K) :=
    ((centralizer ({x} : Set (ReeTag.G2.reeGamma K a))).equivMapOfInjective
      (ReeTag.G2.reeGamma K a).subtype (ReeTag.G2.reeGamma K a).subtype_injective).trans
      ((MulEquiv.subgroupCongr h1).trans
        ((((ReeTag.G2.reeGamma K a) ⊓
          centralizer ({(x : ModGL ReeTag.G2.tag K)} : Set _)).equivMapOfInjective
          (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
          (MulEquiv.subgroupCongr h2)))
  obtain ⟨N, hNn, hNs, hsolv⟩ := smallReeInvCentralizer_simple_normal a ha K hK
  exact hc.false_of_equiv_simple_normal e N

namespace Config

variable {H : Type} [Group H] [Finite H] (c : Sp4Rec.Config H)

include c in
theorem false_of_ree {p f : ℕ} (hG : ReeTitsModel ↥(generalizedFitting H) .twistedG2 p f) :
    False := by
  obtain ⟨-, -, hp, ⟨a₀, ha₀, hfa₀⟩, hiso⟩ := small_Ree_model_Schreier _ p f hG
  subst hp
  obtain ⟨-, a, hfa, hrel⟩ := hG
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hrel
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.G2.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨psi⟩ := hiso a K hfa hK ⟨e⟩
  have ha : 1 ≤ a := by omega
  have hK' : Nat.card K = 3 ^ (2 * a + 1) := hfa ▸ hK
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  exact pairConfig_smallRee_false ha hK' (c.pairConfig psi)

end Config

end CFSG.ComponentClassification.Sp4Rec
