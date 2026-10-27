module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarAutL2
public import CFSG.LocalAnalysis.SeitzReduction.RankOneStart
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Basic
public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamilies

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.Blueprint CFSG.GH74.Uniqueness.Bender CFSG.ComponentClassification

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_autFixed_normalizerMonoidHom {L : Subgroup G} {w : G}
    (hwN : w ∈ normalizer (L : Set G)) :
    (autFixed (L.normalizerMonoidHom ⟨w, hwN⟩)).map L.subtype =
      L ⊓ centralizer ({w} : Set G) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine mem_inf.mpr ⟨z.2, ?_⟩
    have h1 : w * (z : G) * w⁻¹ = z := by
      have := congrArg Subtype.val (mem_autFixed_iff.mp hz)
      rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at this
    rw [mem_centralizer_singleton_iff]
    calc (z : G) * w = w * z * w⁻¹ * w := by rw [h1]
      _ = w * z := by group
  · intro hy
    obtain ⟨hyL, hyw⟩ := mem_inf.mp hy
    refine ⟨⟨y, hyL⟩, mem_autFixed_iff.mpr (Subtype.ext ?_), rfl⟩
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have := mem_centralizer_singleton_iff.mp hyw
    calc w * y * w⁻¹ = y * w * w⁻¹ := by rw [this]
      _ = y := by group

omit [Finite G] in
theorem not_mem_centralizer_of_not_inner {L : Subgroup G} {w : G}
    (hwout : ¬ ∃ l ∈ L, ∀ x ∈ L, w * x * w⁻¹ = l * x * l⁻¹) :
    w ∉ centralizer (L : Set G) := by
  intro hwC
  refine hwout ⟨1, one_mem _, fun x hx => ?_⟩
  have := mem_centralizer_iff.mp hwC x hx
  calc w * x * w⁻¹ = x * w * w⁻¹ := by rw [this]
    _ = 1 * x * 1⁻¹ := by group

theorem statedClassicalModel_of_lieModel_psu3 {X : Type} [Group X] {f : ℕ}
    (h : LieModel X .PSU 3 2 f) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 2 f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem exists_benderType_of_lieModel_psu3 {X : Type} [Group X] {f : ℕ} (hf : 2 ≤ f)
    (h : LieModel X .PSU 3 2 f) : ∃ e : ℕ, BenderType X f 3 e := by
  obtain ⟨e⟩ := GMS78.nonempty_mulEquiv_psu3_of_stated hf (statedClassicalModel_of_lieModel_psu3 h)
  have hmodel : CFSG.Theory.Comparator.PSU3Model f = CFSG.Open.PSU3 2 f :=
      CFSG.Models.benderPSU3Model_eq_psu3 f
  exact ⟨_, BenderType.unitary (K := X) f hf (e.trans (MulEquiv.subgroupCongr hmodel.symm))⟩

theorem lieModel_psl2_of_mulEquiv {X : Type} [Group X] {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* CFSG.Theory.Comparator.PSL2Model f) : LieModel X .PSL 2 2 f := by
  have hq : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩,
    GaloisField 2 f, inferInstance, inferInstance, GaloisField.card 2 f (by omega),
    ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
      (GaloisField 2 f))⟩⟩
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega

theorem u3Star_fixed {L : Subgroup G} {f : ℕ} (hf : 2 ≤ f) (hL : LieModel L .PSU 3 2 f)
    {w : G} (hw : orderOf w = 2) (hwN : w ∈ normalizer (L : Set G))
    (hwout : ¬ ∃ l ∈ L, ∀ x ∈ L, w * x * w⁻¹ = l * x * l⁻¹) :
    Nonempty (↥(L ⊓ centralizer ({w} : Set G)) ≃* CFSG.Theory.Comparator.PSL2Model f) ∧
    IsSimpleGroup ↥(L ⊓ centralizer ({w} : Set G)) ∧
    (∃ a b : ↥(L ⊓ centralizer ({w} : Set G)), a * b ≠ b * a) ∧
    LieModel ↥(L ⊓ centralizer ({w} : Set G)) .PSL 2 2 f ∧
    ∀ Q : Subgroup G, IsPGroup 2 Q → ∀ hQN : Q ≤ normalizer (L : Set G),
      Q ≤ centralizer ((L ⊓ centralizer ({w} : Set G) : Subgroup G) : Set G) →
      Nat.card (L.normalizerMonoidHom.comp (inclusion hQN)).range ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, hB⟩ := exists_benderType_of_lieModel_psu3 hf hL
  set x : MulAut L := L.normalizerMonoidHom ⟨w, hwN⟩ with hxdef
  have hxapp : ∀ l : L, ((x l : L) : G) = w * l * w⁻¹ := fun l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨w, hwN⟩ l
  have hw2 : w * w = 1 := by rw [← sq, ← hw, pow_orderOf_eq_one]
  have hxx : x * x = 1 := by
    refine MulEquiv.ext fun l => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.one_apply, hxapp, hxapp]
    calc w * (w * (l : G) * w⁻¹) * w⁻¹ = (w * w) * l * (w * w)⁻¹ := by group
      _ = l := by rw [hw2]; group
  have hout : ¬ ∃ g : L, ∀ y : L, x y = g * y * g⁻¹ := by
    rintro ⟨g, hg⟩
    refine hwout ⟨g, g.2, fun y hy => ?_⟩
    have := congrArg Subtype.val (hg ⟨y, hy⟩)
    rw [hxapp] at this
    simpa using this
  have hx1 : x ≠ 1 := by
    intro h1
    apply hout
    refine ⟨1, fun y => ?_⟩
    rw [h1]
    simp
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hxx) hx1
  have hmap := map_autFixed_normalizerMonoidHom hwN
  let e₁ : autFixed x ≃* ↥(L ⊓ centralizer ({w} : Set G)) :=
    (Subgroup.equivMapOfInjective (autFixed x) L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  obtain ⟨φ⟩ := hB.fixed_unitary x hxx hout
  let eL : ↥(L ⊓ centralizer ({w} : Set G)) ≃* CFSG.Theory.Comparator.PSL2Model f := e₁.symm.trans φ
  obtain ⟨hs, a, b, hab⟩ := psl2Model_simple_nonabelian hf
  refine ⟨⟨eL⟩, eL.isSimpleGroup, ⟨eL.symm a, eL.symm b, fun h => hab ?_⟩,
    lieModel_psl2_of_mulEquiv hf eL, ?_⟩
  · have := congrArg eL h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  · intro Q hQ hQN hQc
    refine card_le_two_of_fix_unitary hB hxo hout _
      (hQ.of_surjective _ (MonoidHom.rangeRestrict_surjective _)) ?_
    rintro β ⟨q, rfl⟩ j hj
    apply Subtype.ext
    rw [MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
    have hjw : (j : G) ∈ L ⊓ centralizer ({w} : Set G) := hmap ▸ ⟨j, hj, rfl⟩
    have hqj := mem_centralizer_iff.mp (hQc q.2) j hjw
    calc (q : G) * j * (q : G)⁻¹ = j * q * (q : G)⁻¹ := by rw [hqj]
      _ = j := by group

theorem u3Star_local {L : Subgroup G} (h : SeitzSetting G L) {f : ℕ} (hf : 2 ≤ f)
    (hL : LieModel L .PSU 3 2 f) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {t : G} (ht : orderOf t = 2) (htC : t ∈ centralizer (L : Set G))
    {w : G} (hw : orderOf w = 2) (hwN : w ∈ normalizer (L : Set G))
    (hwout : ¬ ∃ l ∈ L, ∀ x ∈ L, w * x * w⁻¹ = l * x * l⁻¹) :
    Nonempty (↥(L ⊓ centralizer ({w} : Set G)) ≃* CFSG.Theory.Comparator.PSL2Model f) ∧
    IsSimpleGroup ↥(L ⊓ centralizer ({w} : Set G)) ∧
    (∃ a b : ↥(L ⊓ centralizer ({w} : Set G)), a * b ≠ b * a) ∧
    LieModel ↥(L ⊓ centralizer ({w} : Set G)) .PSL 2 2 f ∧
    L ⊓ centralizer ({w} : Set G) ≤ centralizer ({w} : Set G) ⊓ centralizer ({t} : Set G) ∧
    (∀ c ∈ centralizer ({w} : Set G) ⊓ centralizer ({t} : Set G),
      ∀ d ∈ L ⊓ centralizer ({w} : Set G), c * d * c⁻¹ ∈ L ⊓ centralizer ({w} : Set G)) ∧
    (∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ centralizer ({w} : Set G) ⊓ centralizer ({t} : Set G) ⊓
        centralizer ((L ⊓ centralizer ({w} : Set G) : Subgroup G) : Set G) → Nat.card Q ≤ 4) ∧
    ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ centralizer ({w} : Set G) ⊓ centralizer ({t} : Set G) →
      Nat.card Q ≤ 4 * 2 ^ f * 2 ^ padicValNat 2 f := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hst := h.standardSetting
  obtain ⟨heL, hLs, hLnab, hLlie, hfix⟩ := u3Star_fixed hf hL hw hwN hwout
  obtain ⟨eL⟩ := heL
  have hCH : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
    inf_centralizer_eq_zpowers_of_card_sylow_eq_two hst.standard hS2 htC ht (hst.core t ht)
  have hHN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hst.standard
      htC ht).1
  set Lw := L ⊓ centralizer ({w} : Set G) with hLw
  set C := centralizer ({w} : Set G) ⊓ centralizer ({t} : Set G) with hC
  have hLwC : Lw ≤ C := fun y hy => mem_inf.mpr ⟨(mem_inf.mp hy).2,
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp htC y (mem_inf.mp hy).1)⟩
  have hnorm : ∀ c ∈ C, ∀ d ∈ Lw, c * d * c⁻¹ ∈ Lw := by
    intro c hc d hd
    obtain ⟨hcw, hct⟩ := mem_inf.mp hc
    obtain ⟨hdL, hdw⟩ := mem_inf.mp hd
    exact mem_inf.mpr ⟨(mem_normalizer_iff.mp (hHN hct) d).mp hdL,
      mul_mem (mul_mem hcw hdw) (inv_mem hcw)⟩
  have hL4 : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ C ⊓ centralizer (Lw : Set G) →
      Nat.card Q ≤ 4 := by
    intro Q hQ hQle
    have hQt : Q ≤ centralizer ({t} : Set G) := fun q hq => (mem_inf.mp (mem_inf.mp (hQle hq)).1).2
    have hQN : Q ≤ normalizer (L : Set G) := hQt.trans hHN
    have hQc : Q ≤ centralizer (Lw : Set G) := fun q hq => (mem_inf.mp (hQle hq)).2
    have hrange := hfix Q hQ hQN hQc
    have hker : Nat.card (Q ⊓ centralizer (L : Set G) : Subgroup G) ≤ 2 := by
      have hle : Q ⊓ centralizer (L : Set G) ≤ zpowers t := by
        rw [← hCH]
        exact fun q hq => mem_inf.mpr ⟨(mem_inf.mp hq).2, hQt (mem_inf.mp hq).1⟩
      calc Nat.card (Q ⊓ centralizer (L : Set G) : Subgroup G) ≤ Nat.card (zpowers t) :=
            card_le_of_le hle
        _ = 2 := by rw [Nat.card_zpowers, ht]
    rw [card_eq_card_inf_centralizer_mul_card_range hQN]
    calc _ ≤ 2 * 2 := Nat.mul_le_mul hker hrange
      _ = 4 := by norm_num
  have hCN : C ≤ normalizer (Lw : Set G) := fun c hc => mem_normalizer_iff.mpr fun d =>
    ⟨fun hd => hnorm c hc d hd, fun hd => by
      have := hnorm c⁻¹ (inv_mem hc) _ hd
      simpa [mul_assoc] using this⟩
  refine ⟨⟨eL⟩, hLs, hLnab, hLlie, hLwC, hnorm, hL4, fun Q hQ hQC => ?_⟩
  have hQN := hQC.trans hCN
  rw [card_eq_card_inf_centralizer_mul_card_range hQN]
  have h1 : Nat.card (Q ⊓ centralizer (Lw : Set G) : Subgroup G) ≤ 4 :=
    hL4 _ (hQ.to_le inf_le_left) (inf_le_inf_right _ hQC)
  have h2 := card_le_of_isPGroup_mulAut_psl2 hf eL
    (P := (Lw.normalizerMonoidHom.comp (inclusion hQN)).range)
    (hQ.of_surjective _ (MonoidHom.rangeRestrict_surjective _))
  calc _ ≤ 4 * (2 ^ f * 2 ^ padicValNat 2 f) := Nat.mul_le_mul h1 h2
    _ = 4 * 2 ^ f * 2 ^ padicValNat 2 f := by ring

end CFSG.SeitzReduction.RankOne
