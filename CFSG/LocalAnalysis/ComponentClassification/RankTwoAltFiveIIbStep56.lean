module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbM12
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbDefs
import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical

namespace IIbSyl

@[expose] def vv : IIbSyl := vElt (0, 1) 0

@[expose] def c1' : IIbSyl := c1 * vv

@[expose] def ss : IIbSyl := ⟨⟨Multiplicative.ofAdd (0, 1), Multiplicative.ofAdd (1, 0)⟩, 1⟩

theorem d8d8_rels :
    z0 ≠ 1 ∧ z0 * z0 = 1 ∧ vv * vv = 1 ∧ t * t = 1 ∧ a * a = 1 ∧ c1' * c1' = 1 ∧
    z0 * vv = vv * z0 ∧ z0 * t = t * z0 ∧ z0 * a = a * z0 ∧ z0 * c1' = c1' * z0 ∧
    vv * t = t * vv * z0 ∧ a * c1' = c1' * a * z0 ∧ vv * a = a * vv ∧ vv * c1' = c1' * vv ∧
    t * a = a * t ∧ t * c1' = c1' * t := by decide

theorem s_rels :
    ss * ss = 1 ∧ ss * z0 = z0 * ss ∧ ss * vv = vv * ss ∧
    (ss * a * ss⁻¹ = vv * a ∨ ss * a * ss⁻¹ = vv * a * z0) ∧
    (ss * c1' * ss⁻¹ = vv * c1' ∨ ss * c1' * ss⁻¹ = vv * c1' * z0) ∧
    (ss * t * ss⁻¹ = vv * t * a * c1' ∨ ss * t * ss⁻¹ = vv * t * a * c1' * z0) := by decide

theorem chi_eq_one :
    chi z0 = 1 ∧ chi vv = 1 ∧ chi a = 1 ∧ chi c1' = 1 ∧ chi t = 1 ∧ chi ss = 1 := by decide

theorem v0Hom_cases : ∀ y : Multiplicative (ZMod 2 × ZMod 2),
    v0Hom y = 1 ∨ v0Hom y = z0 ∨ v0Hom y = vv ∨ v0Hom y = z0 * vv := by decide

theorem z0_eq : v0Hom (Multiplicative.ofAdd (1, 0)) = z0 := by decide

theorem vv_eq : v0Hom (Multiplicative.ofAdd (0, 1)) = vv := by decide

end IIbSyl

end CFSG.ComponentClassification.RankTwoAltFive

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical
open IIbM12

@[expose] def IIbStep5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (T V₀ P : Subgroup G)
    (t z₀ a σ c₁ : G), Setting310 A R g T V₀ →
    centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G) →
    IIbData A R T V₀ P t z₀ a σ c₁ →
    rankTwoX A ⊓ centralizer ({z₀} : Set G) ≤
        normalizer ((V₀ ⊔ zpowers c₁ : Subgroup G) : Set G) ∧
      rankTwoX A ⊓ centralizer ((V₀ ⊔ zpowers c₁ : Subgroup G) : Set G) ≤ V₀ ⊔ zpowers c₁ ∧
      Nat.card ↥(rankTwoX A ⊓ centralizer ({z₀} : Set G)) = 192

variable {G : Type} [Group G] [Finite G]

theorem hyp31_of_setting310 {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀) :
    Hyp31 A := by
  obtain ⟨e⟩ := h.equiv
  have hZ : center ↥A = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : e x ∈ center A5 := mem_center_iff.mpr fun y => by
      obtain ⟨y', rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, mem_center_iff.mp hx y']
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at h1
    exact mem_bot.mpr (e.injective (h1.trans (map_one e).symm))
  exact ⟨h.hyp.standard, hypIIAlt5 ↥A h.hyp.standard.1.1
    ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)⟩,
    h.oddCore, by have := h.hyp.rank; omega, h.hyp.not_normal⟩

theorem iIbCz0_of_data {A R T V₀ P : Subgroup G} {g : G} {t z₀ a σ c₁ : G}
    (hS : Setting310 A R g T V₀) (hD : IIbData A R T V₀ P t z₀ a σ c₁)
    (h5 : rankTwoX A ⊓ centralizer ({z₀} : Set G) ≤
        normalizer ((V₀ ⊔ zpowers c₁ : Subgroup G) : Set G) ∧
      rankTwoX A ⊓ centralizer ((V₀ ⊔ zpowers c₁ : Subgroup G) : Set G) ≤ V₀ ⊔ zpowers c₁ ∧
      Nat.card ↥(rankTwoX A ⊓ centralizer ({z₀} : Set G)) = 192) :
    ∃ v s : G, IIbCz0 (rankTwoX A) z₀ v a (c₁ * v) t s := by
  obtain ⟨f, hfinj, -, hfS0, -, hfV0, -, hft, hfz, hfa, -, hfc⟩ := hD.emb
  obtain ⟨h5N, h5C, h5card⟩ := h5
  refine ⟨f IIbSyl.vv, f IIbSyl.ss, ?_⟩
  have hc' : f IIbSyl.c1' = c₁ * f IIbSyl.vv := by rw [IIbSyl.c1', map_mul, hfc]
  have tr : ∀ {x y : IIbSyl}, x = y → f x = f y := fun e => congrArg f e
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩ :=
    IIbSyl.d8d8_rels
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ := IIbSyl.s_rels
  obtain ⟨m0, m1, m2, m3, m4, m5⟩ := IIbSyl.chi_eq_one
  have hX : ∀ {x : IIbSyl}, IIbSyl.chi x = 1 → f x ∈ rankTwoX A := by
    intro x hx
    have : f x ∈ IIbSyl.S0.map f := mem_map_of_mem f (MonoidHom.mem_ker.mpr hx)
    rw [hfS0] at this
    exact this.2
  have hz1 : z₀ ≠ 1 := by
    rw [← hfz]
    intro e
    exact r0 (hfinj (e.trans (map_one f).symm))
  have d8 : D8D8 z₀ (f IIbSyl.vv) t a (c₁ * f IIbSyl.vv) := by
    refine ⟨hz1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [← hfz, ← hft, ← hfa, ← hc', ← map_mul, ← map_one f]
    exacts [tr r1, tr r2, tr r3, tr r4, tr r5, tr r6, tr r7, tr r8, tr r9, tr r10, tr r11,
      tr r12, tr r13, tr r14, tr r15]
  have hV₀ : ∀ y ∈ V₀, y = 1 ∨ y = z₀ ∨ y = f IIbSyl.vv ∨ y = z₀ * f IIbSyl.vv := by
    intro y hy
    rw [← hfV0] at hy
    obtain ⟨_, ⟨w, rfl⟩, rfl⟩ := hy
    rcases IIbSyl.v0Hom_cases w with e | e | e | e <;> rw [e]
    · exact Or.inl (map_one f)
    · exact Or.inr (Or.inl hfz)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (by rw [map_mul, hfz])))
  have hzV : z₀ ∈ V₀ := by
    rw [← hfV0, ← hfz, ← IIbSyl.z0_eq]
    exact mem_map_of_mem f ⟨_, rfl⟩
  have hvV : f IIbSyl.vv ∈ V₀ := by
    rw [← hfV0, ← IIbSyl.vv_eq]
    exact mem_map_of_mem f ⟨_, rfl⟩
  have hv1 : f IIbSyl.vv ≠ 1 := fun e => by
    have := hfinj (e.trans (map_one f).symm)
    exact absurd this (by decide)
  have hE : closure ({z₀, f IIbSyl.vv, c₁ * f IIbSyl.vv} : Set G) = V₀ ⊔ zpowers c₁ := by
    apply le_antisymm
    · rw [closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact mem_sup_left hzV
      · exact mem_sup_left hvV
      · exact mul_mem (mem_sup_right (mem_zpowers c₁)) (mem_sup_left hvV)
    · refine sup_le ?_ (zpowers_le.mpr ?_)
      · intro y hy
        rcases hV₀ y hy with rfl | rfl | rfl | rfl
        · exact one_mem _
        · exact subset_closure (by simp)
        · exact subset_closure (by simp)
        · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
      · have : c₁ = c₁ * f IIbSyl.vv * (f IIbSyl.vv)⁻¹ := by group
        rw [this]
        exact mul_mem (subset_closure (by simp)) (inv_mem (subset_closure (by simp)))
  obtain ⟨eA⟩ := hS.equiv
  obtain ⟨y, hyA, -, -, hy3, -⟩ := exists_klein_three eA hS.loc.sylowV₀.le hS.card_V₀
  obtain ⟨k, hk⟩ := hy3 z₀ hzV (f IIbSyl.vv) hvV hz1 hv1
  have hAX : A ≤ rankTwoX A := le_normalClosure
  refine
    { d8 := d8
      z₀_mem := hfz ▸ hX m0
      v_mem := hX m1
      a_mem := hfa ▸ hX m2
      c₁_mem := hc' ▸ hX m3
      t_mem := hft ▸ hX m4
      s_mem := hX m5
      s_sq := by rw [← map_mul, q0, map_one]
      s_z₀ := by rw [← hfz, ← map_mul, ← map_mul, q1]
      s_v := by rw [← map_mul, ← map_mul, q2]
      s_a := ?_
      s_c₁ := ?_
      s_t := ?_
      fusion := ⟨(y ^ k)⁻¹, hAX (inv_mem (pow_mem hyA k)), by rw [inv_inv]; exact hk⟩
      E₁_normal := ?_
      centralizer_E₁ := ?_
      card := h5card }
  · rcases q3 with e | e
    · exact Or.inl (by rw [← hfa, ← map_inv, ← map_mul, ← map_mul, e, map_mul])
    · exact Or.inr (by rw [← hfa, ← hfz, ← map_inv, ← map_mul, ← map_mul, e,
        map_mul, map_mul])
  · rcases q4 with e | e
    · exact Or.inl (by rw [← hc', ← map_inv, ← map_mul, ← map_mul, e, map_mul])
    · exact Or.inr (by rw [← hc', ← hfz, ← map_inv, ← map_mul, ← map_mul, e,
        map_mul, map_mul])
  · rcases q5 with e | e
    · exact Or.inl (by rw [← hft, ← hfa, ← hc', ← map_inv, ← map_mul, ← map_mul,
        e, map_mul, map_mul, map_mul])
    · exact Or.inr (by rw [← hft, ← hfa, ← hc', ← hfz, ← map_inv, ← map_mul,
        ← map_mul, e, map_mul, map_mul, map_mul, map_mul])
  · intro x hx hxz
    have hN := h5N ⟨hx, mem_centralizer_singleton_iff.mpr hxz⟩
    rw [hE]
    have hvE : f IIbSyl.vv ∈ V₀ ⊔ zpowers c₁ := mem_sup_left hvV
    have hcE : c₁ * f IIbSyl.vv ∈ V₀ ⊔ zpowers c₁ :=
      mul_mem (mem_sup_right (mem_zpowers c₁)) hvE
    exact ⟨(mem_normalizer_iff.mp hN _).mp hvE, (mem_normalizer_iff.mp hN _).mp hcE⟩
  · intro x hx hxz hxv hxc
    rw [hE]
    refine h5C (mem_inf.mpr ⟨hx, ?_⟩)
    rw [← hE, mem_centralizer_iff]
    have hcl : closure ({z₀, f IIbSyl.vv, c₁ * f IIbSyl.vv} : Set G) ≤
        centralizer ({x} : Set G) := by
      rw [closure_le]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      rcases hw with rfl | rfl | rfl
      · exact hxz.symm
      · exact hxv.symm
      · exact hxc.symm
    intro w hw
    exact mem_centralizer_singleton_iff.mp (hcl hw)

theorem isSimpleGroup_rankTwoX {A R T V₀ : Subgroup G} {g : G}
    (h : Setting310 A R g T V₀) : IsSimpleGroup ↥(rankTwoX A) := by
  obtain ⟨hXF, hXs⟩ := asc08Lemma34 G A (hyp31_of_setting310 h)
  rw [show rankTwoX A = CFSG.generalizedFitting G from hXF]
  exact hXs

theorem asc310IIbStep56_of
    (h5 : IIbStep5) : Asc310IIbStep56 := by
  intro G _ _ A R g T V₀ P t z₀ a σ c₁ hS hb hD
  obtain ⟨v, s, hcz⟩ := iIbCz0_of_data hS hD (h5 G A R g T V₀ P t z₀ a σ c₁ hS hb hD)
  exact hcz.isSporadic_M12 (isSimpleGroup_rankTwoX hS)

end CFSG.ComponentClassification.RankTwoAltFive
