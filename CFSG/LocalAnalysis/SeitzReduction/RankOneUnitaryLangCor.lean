module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryLang
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryStartOuter

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.Blueprint CFSG.GH74.Uniqueness.Bender

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem outer_involution_conj_of_card_sylow
    (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {v w : G} (hvT : v ∈ T)
    (hv2 : v ^ 2 = 1) (hvout : ¬ ∃ l ∈ L, ∀ x ∈ L, v * x * v⁻¹ = l * x * l⁻¹)
    (hw2 : w ^ 2 = 1) (hwt : w ∈ centralizer ({t} : Set G))
    (hwout : ¬ ∃ l ∈ L, ∀ x ∈ L, w * x * w⁻¹ = l * x * l⁻¹) :
    ∃ c ∈ centralizer ({t} : Set G), c * w * c⁻¹ = v ∨ c * w * c⁻¹ = t * v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hst := h.setting.standardSetting
  have hHN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hst.standard
      h.mem h.inv).1
  have hCH : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
    inf_centralizer_eq_zpowers_of_card_sylow_eq_two hst.standard hS2 h.mem h.inv (hst.core t h.inv)
  have hLt : L ≤ centralizer ({t} : Set G) := fun y hy =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp h.mem y hy)
  obtain ⟨e, hB⟩ := exists_benderType_of_lieModel_psu3 h.two_le h.model
  set H := centralizer ({t} : Set G) with hH
  obtain ⟨P, hP⟩ := h.sylow
  have hww : (⟨w, hwt⟩ : H) * ⟨w, hwt⟩ = 1 := Subtype.ext (by simpa [sq] using hw2)
  obtain ⟨P', hP'⟩ := (isPGroup_two_zpowers_of_mul_self_eq_one hww).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H P' P
  have hxT : (c : G) * w * (c : G)⁻¹ ∈ T := by
    have h1 : (c * ⟨w, hwt⟩ * c⁻¹ : H) ∈ ((c • P' : Sylow 2 H) : Subgroup H) := by
      rw [mem_smul_sylow_iff]
      simpa [mul_assoc] using hP' (mem_zpowers _)
    rw [hc, hP, mem_subgroupOf] at h1
    simpa using h1
  set x := (c : G) * w * (c : G)⁻¹ with hx
  have hx2 : x ^ 2 = 1 := by
    calc x ^ 2 = c * w ^ 2 * (c : G)⁻¹ := by rw [hx, sq, sq]; group
      _ = 1 := by rw [hw2]; group
  have hxS : x ∉ szT₁ L T ⊔ zpowers t := by
    intro hxS
    obtain ⟨l, hl, hxl⟩ := (h.inner_iff_mem_of_card_sylow hS2 hxT).mpr hxS
    have hcN := hHN c.2
    refine hwout ⟨(c : G)⁻¹ * l * c, (mem_normalizer_iff''.mp hcN l).mp hl, fun y hy => ?_⟩
    have hy' : (c : G) * y * (c : G)⁻¹ ∈ L := (mem_normalizer_iff.mp hcN y).mp hy
    have e1 := hxl _ hy'
    rw [hx] at e1
    calc w * y * w⁻¹ = (c : G)⁻¹ * (c * w * (c : G)⁻¹ * (c * y * (c : G)⁻¹) *
          (c * w * (c : G)⁻¹)⁻¹) * c := by group
      _ = (c : G)⁻¹ * (l * (c * y * (c : G)⁻¹) * l⁻¹) * c := by rw [e1]
      _ = (c : G)⁻¹ * l * c * y * ((c : G)⁻¹ * l * c)⁻¹ := by group
  have hvS : v ∉ szT₁ L T ⊔ zpowers t := fun hvS =>
    hvout ((h.inner_iff_mem_of_card_sylow hS2 hvT).mpr hvS)
  obtain ⟨a, ha, z, hz, hxv⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁
    (h.mul_mem_of_outer_of_card_sylow hS2 hxT hvT hx2 hv2 hxS hvS)
  have haL : a ∈ L := szT₁_le_right L T ha
  have hvt : v * t = t * v := mem_centralizer_singleton_iff.mp (h.le hvT)
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp (h.le hxT)
  have hvz : v * z = z * v := commute_of_mem_zpowers hz hvt
  have hxz : x * z = z * x := commute_of_mem_zpowers hz hxt
  have hz2 : z ^ 2 = 1 := by
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with rfl | rfl
    · exact one_pow 2
    · exact h.sq_eq_one
  have hvv : v * v = 1 := by rw [← sq, hv2]
  have hzz : z * z = 1 := by rw [← sq, hz2]
  set x' := a * v with hx'
  have hx'eq : x' = x * z := by
    have e1 : x = a * z * v := by
      calc x = x * v * v := by rw [mul_assoc, hvv, mul_one]
        _ = a * z * v := by rw [hxv]
    rw [hx', e1, mul_assoc a z v]
    calc a * v = a * v * (z * z) := by rw [hzz, mul_one]
      _ = a * (v * z) * z := by group
      _ = a * (z * v) * z := by rw [hvz]
  have hx'2 : x' * x' = 1 := by
    rw [hx'eq]
    calc x * z * (x * z) = x * (z * x) * z := by group
      _ = x * (x * z) * z := by rw [hxz]
      _ = x ^ 2 * (z * z) := by rw [sq]; group
      _ = 1 := by rw [hx2, hzz, one_mul]
  have hvN : v ∈ normalizer (L : Set G) := hHN (h.le hvT)
  have hx'N : x' ∈ normalizer (L : Set G) := mul_mem (Subgroup.le_normalizer haL) hvN
  set σv := L.normalizerMonoidHom ⟨v, hvN⟩ with hσv
  set σx := L.normalizerMonoidHom ⟨x', hx'N⟩ with hσx
  have hσvapp : ∀ y : L, ((σv y : L) : G) = v * y * v⁻¹ := fun y =>
    normalizerMonoidHom_apply_apply_coe L _ y
  have hσxapp : ∀ y : L, ((σx y : L) : G) = x' * y * x'⁻¹ := fun y =>
    normalizerMonoidHom_apply_apply_coe L _ y
  have hσinv : ∀ {u : G} (hu : u ∈ normalizer (L : Set G)), u * u = 1 →
      L.normalizerMonoidHom ⟨u, hu⟩ * L.normalizerMonoidHom ⟨u, hu⟩ = 1 := by
    intro u hu huu
    rw [← map_mul]
    have : (⟨u, hu⟩ : normalizer (L : Set G)) * ⟨u, hu⟩ = 1 := Subtype.ext huu
    rw [this, map_one]
  have hσvout : ¬ ∃ g : L, ∀ y : L, σv y = g * y * g⁻¹ := by
    rintro ⟨g, hg⟩
    refine hvout ⟨g, g.2, fun y hy => ?_⟩
    have := congrArg Subtype.val (hg ⟨y, hy⟩)
    rw [hσvapp] at this
    simpa using this
  have hcoset : σx = MulAut.conj (⟨a, haL⟩ : L) * σv := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.conj_apply, hσxapp]
    simp only [coe_mul, coe_inv]
    rw [hσvapp, hx']
    group
  obtain ⟨ℓ, hℓ⟩ := conj_of_outer_involution_unitary hB (hσinv hvN hvv) (hσinv hx'N hx'2)
    hσvout ⟨_, hcoset⟩
  set k := ((ℓ : G) * v * (ℓ : G)⁻¹)⁻¹ * x' with hk
  have hkL : k ∈ centralizer (L : Set G) := by
    refine mem_centralizer_iff.mpr fun y hy => ?_
    have e1 := congrArg (fun σ : MulAut L => ((σ ⟨y, hy⟩ : L) : G)) hℓ
    simp only [normalizerMonoidHom_apply_apply_coe, MulAut.mul_apply, MulAut.conj_apply,
      MulAut.conj_inv_apply, coe_mul, coe_inv] at e1
    have e2 : x' * y = (ℓ : G) * v * (ℓ : G)⁻¹ * y * ((ℓ : G) * v * (ℓ : G)⁻¹)⁻¹ * x' := by
      calc x' * y = x' * y * x'⁻¹ * x' := by group
        _ = _ := by rw [e1]; group
    rw [hk]
    calc y * (((ℓ : G) * v * (ℓ : G)⁻¹)⁻¹ * x') =
        ((ℓ : G) * v * (ℓ : G)⁻¹)⁻¹ * ((ℓ : G) * v * (ℓ : G)⁻¹ * y *
          ((ℓ : G) * v * (ℓ : G)⁻¹)⁻¹ * x') := by group
      _ = ((ℓ : G) * v * (ℓ : G)⁻¹)⁻¹ * (x' * y) := by rw [e2]
      _ = ((ℓ : G) * v * (ℓ : G)⁻¹)⁻¹ * x' * y := by group
  have hℓt : (ℓ : G) ∈ centralizer ({t} : Set G) := hLt ℓ.2
  have hx't : x' ∈ centralizer ({t} : Set G) := by
    rw [hx'eq]
    exact mul_mem (h.le hxT) (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl) hz)
  have hkt : k ∈ centralizer ({t} : Set G) :=
    mul_mem (inv_mem (mul_mem (mul_mem hℓt (h.le hvT)) (inv_mem hℓt))) hx't
  have hkz : k ∈ zpowers t := by
    rw [← hCH]
    exact mem_inf.mpr ⟨hkL, hkt⟩
  have hkzt : k * z ∈ zpowers t := mul_mem hkz hz
  have hℓkz : (ℓ : G) * (k * z) = k * z * ℓ :=
    commute_of_mem_zpowers hkzt (mem_centralizer_singleton_iff.mp hℓt)
  have hfin : (ℓ : G)⁻¹ * x * ℓ = v * (k * z) := by
    have e1 : x = x' * z := by
      rw [hx'eq, mul_assoc, hzz, mul_one]
    have e2 : x' = (ℓ : G) * v * (ℓ : G)⁻¹ * k := by rw [hk]; group
    rw [e1, e2]
    calc (ℓ : G)⁻¹ * ((ℓ : G) * v * (ℓ : G)⁻¹ * k * z) * ℓ =
        v * ((ℓ : G)⁻¹ * (k * z) * ℓ) := by group
      _ = v * (k * z) := by
          rw [show (ℓ : G)⁻¹ * (k * z) * ℓ = k * z by rw [mul_assoc, ← hℓkz]; group]
  refine ⟨(ℓ : G)⁻¹ * c, mul_mem (inv_mem hℓt) c.2, ?_⟩
  have e3 : (ℓ : G)⁻¹ * c * w * ((ℓ : G)⁻¹ * c)⁻¹ = v * (k * z) := by
    rw [← hfin, hx]
    group
  rw [e3]
  rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hkzt with h1 | h1
  · left
    rw [h1, mul_one]
  · right
    rw [h1, hvt]

end U3Start

end CFSG.SeitzReduction.RankOne
