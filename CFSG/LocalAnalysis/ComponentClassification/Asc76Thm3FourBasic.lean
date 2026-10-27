module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Basic
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Hall32Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.Asc76X.Thm3Four

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.Asc76X
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {G : Type} [Group G]

structure Setting (K R S : Subgroup G) : Prop where
  tight : TightlyEmbedded K
  top : normalClosure (K : Set G) = ⊤
  odd : standardComponentOddCore G = ⊥
  sylowK : IsSylowOf 2 R K
  card : Nat.card R = 4
  elem : IsElemAbelian 2 R
  sylow : IsSylowOf 2 S ⊤
  le : R ≤ S
  wc : ∀ g : G, rightConjugate R g ≤ S → rightConjugate R g = R

namespace Setting

variable {K R S : Subgroup G}

theorem R_le (h : Setting K R S) : R ≤ K := h.sylowK.le

theorem R_ne_bot (h : Setting K R S) : R ≠ ⊥ := fun e => by
  have h1 := h.card
  rw [e, card_bot] at h1
  exact absurd h1 (by norm_num)

theorem eq_bot_of_normal_odd (h : Setting K R S) (N : Subgroup G) [hN : N.Normal]
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have h1 : N ≤ standardComponentOddCore G := le_sSup ⟨hN, hodd⟩
  rw [h.odd] at h1
  exact le_bot_iff.mp h1

theorem map_conj_eq_of_mem_normalizer {A : Subgroup G} {c : G}
    (hc : c ∈ normalizer (A : Set G)) : A.map (MulAut.conj c).toMonoidHom = A := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (mem_normalizer_iff.mp hc a).mp ha
  · intro hy
    refine ⟨c⁻¹ * y * c, ?_, ?_⟩
    · have h1 := (mem_normalizer_iff.mp (inv_mem hc) y).mp hy
      simpa using h1
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

variable [Finite G]

omit [Finite G] in
theorem isPGroup_R (h : Setting K R S) : IsPGroup 2 R := h.sylowK.isPGroup

theorem normal_of_normal_le (h : Setting K R S) (L : Subgroup G) [hL : L.Normal] (hLK : L ≤ K)
    (heven : Even (Nat.card L)) : K.Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff]
  intro g _
  refine CFSG.ComponentClassification.Asc75T4.mem_normalizer_of_le_rightConjugate h.tight hLK
    heven fun x hx => ?_
  rw [mem_rightConjugate_iff]
  exact hLK (hL.conj_mem x hx g)

theorem normal_of_normal_R (h : Setting K R S) (hR : R.Normal) : K.Normal := by
  refine h.normal_of_normal_le R h.R_le ?_
  rw [h.card]
  exact even_two_mul 2

theorem centralizer_le (h : Setting K R S) :
    centralizer (R : Set G) ≤ normalizer (K : Set G) :=
  centralizer_two_subgroup_le K R h.tight h.isPGroup_R h.R_le h.R_ne_bot

theorem odd_relIndex (h : Setting K R S) : Odd (R.relIndex K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (isSylowOf_iff.mp h.sylowK).2.2)

theorem odd_card_map (h : Setting K R S) {H : Type*} [Group H] (φ : G →* H) (hR : R ≤ φ.ker) :
    Odd (Nat.card (K.map φ)) := by
  have h1 : Nat.card (K.map φ) = (φ.ker.subgroupOf K).index := by
    rw [← MonoidHom.domRestrict_range, ← MonoidHom.ker_domRestrict, Subgroup.index,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (φ.domRestrict K)).toEquiv]
  have h2 : (φ.ker.subgroupOf K).index ∣ R.relIndex K :=
    index_dvd_of_le fun x hx => hR hx
  rw [h1]
  exact Odd.of_dvd_nat h.odd_relIndex h2

theorem le_ker_of_dvd (h : Setting K R S) {H : Type*} [Group H] [Finite H] (φ : G →* H)
    (hR : R ≤ φ.ker) {n : ℕ} (hH : Nat.card H ∣ 2 ^ n) : K ≤ φ.ker := by
  have h1 : Nat.card (K.map φ) ∣ 2 ^ n := (card_subgroup_dvd_card _).trans hH
  have h2 : Nat.card (K.map φ) = 1 := by
    have hcop : Nat.Coprime (Nat.card (K.map φ)) (2 ^ n) :=
      Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr (h.odd_card_map φ hR))
    exact Nat.Coprime.eq_one_of_dvd hcop h1
  have h3 : K.map φ = ⊥ := (card_eq_one).mp h2
  exact (Subgroup.map_eq_bot_iff K).mp h3

theorem not_le_normalizer (h : Setting K R S) (hKn : ¬ K.Normal) (L : Subgroup G) [L.Normal]
    (hLs : IsSimpleGroup L) (hRL : R ⊓ L ≠ ⊥) : ¬ L ≤ normalizer (K : Set G) := by
  intro hLN
  have hn : ((K ⊓ L).subgroupOf L).Normal := by
    refine (normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun x hx => ?_
    rw [mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyK, hyL⟩
      exact ⟨(mem_normalizer_iff.mp (hLN hx) y).mp hyK, (inferInstance : L.Normal).conj_mem y
        hyL x⟩
    · rintro ⟨hyK, hyL⟩
      refine ⟨(mem_normalizer_iff.mp (hLN hx) y).mpr hyK, ?_⟩
      have e : y = x⁻¹ * (x * y * x⁻¹) * x := by group
      rw [e]
      have := (inferInstance : L.Normal).conj_mem _ hyL x⁻¹
      simpa using this
  rcases hn.eq_bot_or_eq_top with hb | ht
  · apply hRL
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hx.2⟩ : L) ∈ (K ⊓ L).subgroupOf L := ⟨h.R_le hx.1, hx.2⟩
    rw [hb, mem_bot] at h1
    rw [mem_bot]
    exact congrArg Subtype.val h1
  · have hLK : L ≤ K := fun x hx => by
      have h1 : (⟨x, hx⟩ : L) ∈ (K ⊓ L).subgroupOf L := by rw [ht]; exact mem_top _
      exact h1.1
    apply hKn
    refine h.normal_of_normal_le L hLK ?_
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 ↥(R ⊓ L) := h.isPGroup_R.to_le inf_le_left
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    have hk0 : k ≠ 0 := fun e => hRL ((card_eq_one).mp (by rw [hk, e, pow_zero]))
    have h2 : 2 ∣ Nat.card ↥(R ⊓ L) := by
      rw [hk]
      exact dvd_pow_self 2 hk0
    exact even_iff_two_dvd.mpr (h2.trans (card_dvd_of_le inf_le_right))

theorem eq_top_of_normal (h : Setting K R S) (L : Subgroup G) [hL : L.Normal] (hRL : R ≤ L)
    (hZ : center L = ⊥) {n : ℕ} (hout : Nat.card (Outer L) ∣ 2 ^ n) : L = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (L : Set G) with hCdef
  let φ : G →* Outer L := (QuotientGroup.mk' (inner L)).comp (MulAut.conjNormal (H := L))
  have hφL : ∀ l : L, MulAut.conjNormal (H := L) (l : G) = MulAut.conj l := fun l => by
    ext x
    simp [MulAut.conjNormal_apply, MulAut.conj_apply]
  have hRker : R ≤ φ.ker := fun r hr => by
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk (MulAut.conjNormal (H := L) r) : Outer L) = 1
    rw [QuotientGroup.eq_one_iff, show r = ((⟨r, hRL hr⟩ : L) : G) from rfl, hφL]
    exact ⟨_, rfl⟩
  have : Finite (Outer L) := by
    have : Finite (MulAut L) := inferInstance
    infer_instance
  have hKker : K ≤ φ.ker := h.le_ker_of_dvd φ hRker hout
  have hker : φ.ker ≤ L ⊔ C := fun g hg => by
    rw [MonoidHom.mem_ker] at hg
    change (QuotientGroup.mk (MulAut.conjNormal (H := L) g) : Outer L) = 1 at hg
    rw [QuotientGroup.eq_one_iff] at hg
    obtain ⟨l, hl⟩ := hg
    have hc : (l : G)⁻¹ * g ∈ C := by
      rw [hCdef, mem_centralizer_iff]
      intro x hx
      have h1 := congrArg (fun α : MulAut L => ((α ⟨x, hx⟩ : L) : G)) hl
      simp only [MulAut.conj_apply, MulAut.conjNormal_apply, coe_mul, coe_inv] at h1
      calc x * ((l : G)⁻¹ * g) = (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹) * g := by group
        _ = (l : G)⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
        _ = (l : G)⁻¹ * g * x := by group
    have e : g = (l : G) * ((l : G)⁻¹ * g) := by group
    rw [e]
    exact mul_mem (mem_sup_left l.2) (mem_sup_right hc)
  have hLC : L ⊔ C = ⊤ := by
    rw [eq_top_iff, ← h.top]
    exact normalClosure_le_normal fun x hx => hker (hKker hx)
  have hCN : C ≤ normalizer (K : Set G) :=
    (Subgroup.centralizer_le (by exact_mod_cast hRL)).trans h.centralizer_le
  have hKLn : (K ⊔ L).Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff, ← hLC]
    refine sup_le ((le_sup_right : L ≤ K ⊔ L).trans le_normalizer) fun c hc => ?_
    have hcK := hCN hc
    have hcL : c ∈ normalizer (L : Set G) := by
      rw [normalizer_eq_top_iff.mpr hL]
      exact mem_top c
    have hmap : (K ⊔ L).map (MulAut.conj c).toMonoidHom = K ⊔ L := by
      rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hcK, map_conj_eq_of_mem_normalizer hcL]
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [← hmap]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← hmap] at hy
      obtain ⟨y', hy', e⟩ := hy
      have : y' = y := by
        have e' : c * y' * c⁻¹ = c * y * c⁻¹ := e
        exact mul_left_cancel (mul_right_cancel e')
      rwa [← this]
  have hKL : K ⊔ L = ⊤ := by
    rw [eq_top_iff, ← h.top]
    exact normalClosure_le_normal fun x hx => mem_sup_left hx
  have hGL : Odd (Nat.card (G ⧸ L)) := by
    have h1 : K.map (QuotientGroup.mk' L) = ⊤ := by
      have h2 := congrArg (Subgroup.map (QuotientGroup.mk' L)) hKL
      rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
        (map_top_of_surjective _ (QuotientGroup.mk'_surjective L))] at h2
    have h3 := h.odd_card_map (QuotientGroup.mk' L) (by
      rw [QuotientGroup.ker_mk']
      exact hRL)
    rwa [h1, card_top] at h3
  have hCL : ∀ x ∈ C, x ∈ L → x = 1 := fun x hxC hxL => by
    have h1 : (⟨x, hxL⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro y
      apply Subtype.ext
      exact (mem_centralizer_iff.mp hxC y y.2)
    rw [hZ, mem_bot] at h1
    exact congrArg Subtype.val h1
  have hinj : Function.Injective ((QuotientGroup.mk' L).comp C.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    rw [mem_bot]
    exact Subtype.ext (hCL x x.2 hx)
  have hCodd : Odd (Nat.card C) := by
    have h1 : Nat.card C ∣ Nat.card (G ⧸ L) := by
      have h2 := card_subgroup_dvd_card ((QuotientGroup.mk' L).comp C.subtype).range
      rwa [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at h2
    exact Odd.of_dvd_nat hGL h1
  have hCbot : C = ⊥ := h.eq_bot_of_normal_odd C hCodd
  rw [hCbot, sup_bot_eq] at hLC
  exact hLC

end Setting

end CFSG.ComponentClassification.Asc76X.Thm3Four
