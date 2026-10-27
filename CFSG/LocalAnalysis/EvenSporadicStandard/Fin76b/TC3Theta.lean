module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Pull
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Defs

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

namespace PullHyp

variable {G : Type} [Group G] {L : Subgroup G} {z t : G} {T : Subgroup G}
  {EY : Subgroup (MulAut (↥L ⧸ center ↥L))} (h : PullHyp G L z t T EY)

include h in
theorem th_apply_iff {c : G} (hc : c ∈ centralizer ({z} : Set G)) {β : G} (hβL : β ∈ L) :
    h.th c hc (QuotientGroup.mk (⟨β, hβL⟩ : ↥L)) = QuotientGroup.mk (⟨β, hβL⟩ : ↥L) ↔
      c * β = β * c := by
  have hmem : c * β * c⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (h.cfg.cent_le hc) β).1 hβL
  have happ := thetaH_apply h.cfg.cent_le ⟨c, hc⟩ ⟨β, hβL⟩ ⟨c * β * c⁻¹, hmem⟩ rfl
  change thetaH h.cfg.cent_le ⟨c, hc⟩ (QuotientGroup.mk (⟨β, hβL⟩ : ↥L)) = _ ↔ _
  rw [happ, QuotientGroup.eq, h.hZ, mem_bot]
  constructor
  · intro h1
    have h2 : c * β * c⁻¹ = β := congrArg Subtype.val (inv_mul_eq_one.1 h1)
    exact mul_inv_eq_iff_eq_mul.1 h2
  · intro h1
    apply inv_mul_eq_one.2
    apply Subtype.ext
    show c * β * c⁻¹ = β
    rw [h1]
    group

include h in
theorem isInnerAut_th_of_mem {c : G} (hc : c ∈ centralizer ({z} : Set G))
    (hcL : c ∈ L ⊔ zpowers z) : IsInnerAut (h.th c hc) := by
  obtain ⟨l, hl, w, hw, hcl⟩ := exists_mul_of_mem_sup_of_le_centralizer
    (zpowers_le.2 h.cfg.z_cent) hcL
  have h1 : h.th c hc = h.th l (h.L_le_H hl) := by
    rw [h.th_eq_iff]
    have : c⁻¹ * l = w⁻¹ := by rw [hcl]; group
    rw [this]
    exact inv_mem hw
  refine ⟨((⟨l, hl⟩ : ↥L) : ↥L ⧸ center ↥L), ?_⟩
  rw [h1, h.th_L hl]
  rfl

include h in
theorem exists_outer_fix (hsurj : Function.Surjective (thetaH h.cfg.cent_le)) {β : G}
    (hβL : β ∈ L)
    (hO : OuterBetaFor (↥L ⧸ center ↥L) (QuotientGroup.mk (⟨β, hβL⟩ : ↥L))) :
    ∃ c ∈ centralizer ({z} : Set G), c * β = β * c ∧ c ∉ L ⊔ zpowers z := by
  obtain ⟨r, hrinn, hrβ⟩ := hO.fix
  obtain ⟨⟨c, hc⟩, hcr⟩ := hsurj r
  have hth : h.th c hc = r := hcr
  refine ⟨c, hc, (h.th_apply_iff hc hβL).1 (by rw [hth]; exact hrβ), fun hcL => hrinn ?_⟩
  obtain ⟨l, hl, w, hw, hcl⟩ := exists_mul_of_mem_sup_of_le_centralizer
    (zpowers_le.2 h.cfg.z_cent) hcL
  have h1 : h.th c hc = h.th l (h.L_le_H hl) := by
    rw [h.th_eq_iff]
    have : c⁻¹ * l = w⁻¹ := by rw [hcl]; group
    rw [this]
    exact inv_mem hw
  refine ⟨((⟨l, hl⟩ : ↥L) : ↥L ⧸ center ↥L), ?_⟩
  rw [← hth, h1, h.th_L hl]
  rfl

include h in
theorem mem_of_sq_mem {β : G} (hβL : β ∈ L) (hβ3 : orderOf β = 3)
    (hO : OuterBetaFor (↥L ⧸ center ↥L) (QuotientGroup.mk (⟨β, hβL⟩ : ↥L)))
    {c : G} (hc : c ∈ centralizer ({z} : Set G)) (hcβ : c * β = β * c)
    (hsq : c * c ∈ zpowers z ⊔ zpowers β) : c ∈ L ⊔ zpowers z := by
  set b : ↥L ⧸ center ↥L := QuotientGroup.mk (⟨β, hβL⟩ : ↥L) with hb
  set a : MulAut (↥L ⧸ center ↥L) := MulAut.conj b with ha
  set r : MulAut (↥L ⧸ center ↥L) := h.th c hc with hr
  have hrb : r b = b := (h.th_apply_iff hc hβL).2 hcβ
  have hb3 : b ^ 3 = 1 := by
    rw [hb, ← QuotientGroup.mk_pow]
    have : (⟨β, hβL⟩ : ↥L) ^ 3 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hβ3]
      exact pow_orderOf_eq_one β
    rw [this, QuotientGroup.mk_one]
  have ha3 : a ^ 3 = 1 := by rw [ha, ← map_pow, hb3, map_one]
  have hab : ∀ j : ℤ, (a ^ j) b = b := by
    intro j
    induction j using Int.induction_on with
    | zero => simp
    | succ n ih =>
      rw [zpow_add_one, MulAut.mul_apply, ha, MulAut.conj_apply]
      simpa using ih
    | pred n ih =>
      rw [zpow_sub_one, MulAut.mul_apply]
      have h1 : a⁻¹ b = b := by
        rw [MulAut.inv_apply]
        simp [ha, MulAut.conj_symm_apply]
      rw [h1]
      exact ih
  have hra : r * a = a * r := by
    have := conj_aut_apply r b
    rw [hrb] at this
    have h2 : a = r * a * r⁻¹ := this
    calc r * a = (r * a * r⁻¹) * r := by group
      _ = a * r := by rw [← h2]
  have hraj : ∀ j : ℤ, r * a ^ j = a ^ j * r := fun j =>
    (Commute.zpow_right (show Commute r a from hra) j).eq
  have hz_le : zpowers β ≤ centralizer (zpowers z : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    exact ((Commute.zpow_left (show Commute z β from (h.cfg.z_comm_of_mem_A hβL).symm) k).eq)
  obtain ⟨y1, hy1, y2, hy2, hcc⟩ := exists_mul_of_mem_sup_of_le_centralizer hz_le
    hsq
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hy2
  have hy1H : y1 ∈ centralizer ({z} : Set G) := by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hy1
    exact mem_centralizer_singleton_iff.2 ((Commute.zpow_left (Commute.refl z) i).eq)
  have hβjL : β ^ j ∈ L := zpow_mem hβL j
  have hth1 : h.th y1 hy1H = 1 := (h.th_eq_one_iff hy1H).2 hy1
  have hthβ : h.th (β ^ j) (h.L_le_H hβjL) = a ^ j := by
    rw [h.th_L hβjL, nuL_apply]
    have : ((⟨β ^ j, hβjL⟩ : ↥L) : ↥L ⧸ center ↥L) = b ^ j := by
      rw [hb, ← QuotientGroup.mk_zpow]
      rfl
    rw [this, map_zpow]
  have hrr : r * r = a ^ j := by
    have hcmem : c * c ∈ centralizer ({z} : Set G) := mul_mem hc hc
    have h1 : h.th (c * c) hcmem = r * r := h.th_mul hc hc
    have h2 : c * c = y1 * β ^ j := hcc
    have h3 : h.th (c * c) hcmem = h.th (y1 * β ^ j) (mul_mem hy1H (h.L_le_H hβjL)) := by
      congr 1
    rw [← h1, h3, h.th_mul hy1H (h.L_le_H hβjL), hth1, hthβ, one_mul]
  have hr'sq : (r * a ^ j) * (r * a ^ j) = 1 := by
    calc (r * a ^ j) * (r * a ^ j) = (r * r) * (a ^ j * a ^ j) := by
          rw [mul_assoc, ← mul_assoc (a ^ j) r, ← hraj j]
          group
      _ = a ^ (3 * j) := by rw [hrr, ← zpow_add, ← zpow_add]; congr 1; ring
      _ = 1 := by
        rw [zpow_mul]
        have : a ^ (3 : ℤ) = 1 := by exact_mod_cast ha3
        rw [this, one_zpow]
  have hr'b : (r * a ^ j) b = b := by
    rw [MulAut.mul_apply, hab j, hrb]
  obtain ⟨y, hy⟩ := hO.noInv _ hr'sq hr'b
  have hrin : IsInnerAut r := by
    have h1 : r = (r * a ^ j) * (a ^ j)⁻¹ := by group
    rw [h1]
    refine IsInnerAut.mul ⟨y, hy⟩ ?_
    refine IsInnerAut.inv ?_
    exact ⟨b ^ j, by rw [ha, map_zpow]⟩
  obtain ⟨y', hy'⟩ := hrin
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y'
  have h1 : h.th c hc = h.th l (h.L_le_H l.2) := by
    rw [h.th_L l.2, nuL_apply]
    exact hy'
  rw [h.th_eq_iff] at h1
  obtain ⟨m, hm⟩ := mem_zpowers_iff.1 h1
  have : c = (l : G) * (z ^ m)⁻¹ := by
    have h2 : (l : G) = c * z ^ m := by rw [hm]; group
    rw [h2]
    group
  rw [this]
  exact mul_mem (mem_sup_left l.2) (inv_mem (mem_sup_right (zpow_mem (mem_zpowers z) m)))

end PullHyp

end CFSG.EvenSporadicStandard.Fin76b
