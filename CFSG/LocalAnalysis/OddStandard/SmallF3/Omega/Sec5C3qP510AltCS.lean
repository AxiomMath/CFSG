module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Cls
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5L511
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BZClass

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G}

theorem sec5p510c_exists_p (h52a : Asc82Lemma52a) (c : Sec5RCtx G t L S z r B A)
    (hne : ¬ S ⊓ centralizer (L : Set G) ≤ zpowers t) :
    ∃ p ∈ S ⊓ centralizer (L : Set G), p * p = t := by
  rw [SetLike.not_le_iff_exists] at hne
  obtain ⟨x, hx, hxt⟩ := hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp c.sylow.2.1 ⟨x, hx.1⟩
  rw [Subgroup.orderOf_mk] at hk
  have htC : t ∈ centralizer (L : Set G) := sec4_t_mem_centralizer c.toSec3Setting
  have hxtc : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp (c.sylow.1 hx.1)
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hlt' : k < 2 := not_le.mp hlt
    interval_cases k
    · have hx1 : x = 1 := orderOf_eq_one_iff.mp (by rw [hk]; norm_num)
      exact hxt (by rw [hx1]; exact one_mem _)
    · have hxx : x * x = 1 := by
        rw [← pow_two, ← pow_orderOf_eq_one x, hk]
        norm_num
      rcases sec4_eq_of_commute (h52a G t L c.toSec5Setting) hx.2 htC hxx c.involution hxtc with
        h1 | h1
      · exact hxt (by rw [h1]; exact one_mem _)
      · exact hxt (by rw [h1]; exact mem_zpowers t)
  set p := x ^ 2 ^ (k - 2) with hp
  have hdvd : 2 ^ (k - 2) ∣ orderOf x := by
    rw [hk]
    exact pow_dvd_pow 2 (Nat.sub_le k 2)
  have hord : orderOf p = 4 := by
    rw [hp, orderOf_pow_of_dvd (by positivity) hdvd, hk, Nat.pow_div (Nat.sub_le k 2)
      (by norm_num)]
    have : k - (k - 2) = 2 := by omega
    rw [this]
  have hpC : p ∈ S ⊓ centralizer (L : Set G) := (S ⊓ centralizer (L : Set G)).pow_mem hx _
  have hp4 : p ^ 4 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one p
  have hpt : p ∉ zpowers t := fun hpz => by
    have := orderOf_dvd_of_mem_zpowers hpz
    rw [hord, c.involution] at this
    omega
  exact ⟨p, hpC, csl_sq_eq_t h52a c hpC hp4 hpt⟩

theorem sec5p510c_comm_cases (h36 : Asc82Lemma36) (h52a : Asc82Lemma52a)
    (c : Sec5RCtx G t L S z r B A) {x : G} (hx : x ∈ S ⊓ centralizer (L : Set G))
    (hx2t : x * x = t) : r * x * r⁻¹ * x⁻¹ = 1 ∨ r * x * r⁻¹ * x⁻¹ = t := by
  have htC : t ∈ centralizer (L : Set G) := sec4_t_mem_centralizer c.toSec3Setting
  have hcyc := h52a G t L c.toSec5Setting
  have hrA : r ∈ A := c.A_eq ▸ Subgroup.mem_sup_left (mem_zpowers r)
  have hrS : r ∈ S := c.A_le hrA
  have hrt : r ∈ centralizer ({t} : Set G) := c.sylow.1 hrS
  have hrt' : r * t = t * r := Subgroup.mem_centralizer_singleton_iff.mp hrt
  have hrN : r ∈ normalizer (L : Set G) :=
    mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_lemma36 h36 c.toSec3SettingLB r hrt)
  have hx' : r * x * r⁻¹ ∈ S ⊓ centralizer (L : Set G) := by
    refine ⟨S.mul_mem (S.mul_mem hrS hx.1) (S.inv_mem hrS), ?_⟩
    show r * x * r⁻¹ ∈ centralizer (L : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : r⁻¹ * l * r ∈ L := by
      refine (Subgroup.mem_normalizer_iff.mp hrN (r⁻¹ * l * r)).mpr ?_
      have : r * (r⁻¹ * l * r) * r⁻¹ = l := by group
      rw [this]
      exact hl
    have hc := Subgroup.mem_centralizer_iff.mp hx.2 _ hl'
    calc l * (r * x * r⁻¹) = r * ((r⁻¹ * l * r) * x) * r⁻¹ := by group
      _ = r * (x * (r⁻¹ * l * r)) * r⁻¹ := by rw [hc]
      _ = r * x * r⁻¹ * l := by group
  have hcomm : Commute (r * x * r⁻¹) x := csl_comm h52a c _ hx' _ hx
  have hdX : r * x * r⁻¹ * x⁻¹ ∈ S ⊓ centralizer (L : Set G) :=
    Subgroup.mul_mem _ hx' (Subgroup.inv_mem _ hx)
  have hdd : r * x * r⁻¹ * x⁻¹ * (r * x * r⁻¹ * x⁻¹) = 1 := by
    have hci : x⁻¹ * (r * x * r⁻¹) = (r * x * r⁻¹) * x⁻¹ := hcomm.inv_right.eq.symm
    calc r * x * r⁻¹ * x⁻¹ * (r * x * r⁻¹ * x⁻¹)
        = (r * x * r⁻¹) * (x⁻¹ * (r * x * r⁻¹)) * x⁻¹ := by group
      _ = (r * x * r⁻¹) * ((r * x * r⁻¹) * x⁻¹) * x⁻¹ := by rw [hci]
      _ = r * (x * x) * r⁻¹ * (x * x)⁻¹ := by group
      _ = 1 := by rw [hx2t, hrt', mul_inv_cancel_right, mul_inv_cancel]
  have hdt : r * x * r⁻¹ * x⁻¹ * t = t * (r * x * r⁻¹ * x⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp (c.sylow.1 hdX.1)
  exact sec4_eq_of_commute hcyc hdX.2 htC hdd c.involution hdt

theorem sec5p510c_cent_A (c : Sec5RCtx G t L S z r B A) {x : G}
    (hx : x ∈ S ⊓ centralizer (L : Set G)) (hrx : r * x * r⁻¹ * x⁻¹ = 1) :
    x ∈ centralizer (A : Set G) := by
  have hxB : ∀ b ∈ B, x * b = b * x := fun b hb =>
    (Subgroup.mem_centralizer_iff.mp hx.2 b (c.B_le hb).1).symm
  have hrx' : r * x = x * r := by
    calc r * x = (r * x * r⁻¹ * x⁻¹) * (x * r) := by group
      _ = x * r := by rw [hrx, one_mul]
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨b, hb, rfl | rfl⟩ := csl_A_cases c a ha
  · exact (hxB a hb).symm
  · calc r * b * x = r * (x * b) := by rw [mul_assoc, hxB b hb]
      _ = x * (r * b) := by rw [← mul_assoc, hrx', mul_assoc]

theorem sec5p510c_mem_normalizer_A (c : Sec5RCtx G t L S z r B A) {g : G}
    (hgB : ∀ b ∈ B, g * b = b * g) (hgr : g * r * g⁻¹ ∈ A) (hgr' : g⁻¹ * r * g ∈ A) :
    g ∈ normalizer (A : Set G) := by
  have hBA : B ≤ A := c.A_eq ▸ le_sup_right
  have hconj : ∀ g : G, (∀ b ∈ B, g * b = b * g) → g * r * g⁻¹ ∈ A →
      ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
    intro g hgB hgr a ha
    have hle : zpowers r ⊔ B ≤ A.comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_comap.mpr ?_)) fun b hb =>
        Subgroup.mem_comap.mpr ?_
      · simpa [MulAut.conj_apply] using hgr
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [hgB b hb, mul_inv_cancel_right]
        exact hBA hb
    rw [c.A_eq] at ha
    simpa [MulAut.conj_apply] using Subgroup.mem_comap.mp (hle ha)
  have hgiB : ∀ b ∈ B, g⁻¹ * b = b * g⁻¹ := fun b hb =>
    (Commute.inv_left (show Commute g b from hgB b hb)).eq
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · exact hconj g hgB hgr a
  · intro ha
    have := hconj g⁻¹ hgiB (by simpa using hgr') _ ha
    rwa [show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group] at this

theorem sec5p510c_no_inv (hy : Sec5B59Hyp) (h : Sec510Ctx G t L S z r ρ B A φ) {x : G}
    (hx : x ∈ S ⊓ centralizer (L : Set G)) (hx2t : x * x = t)
    (hd : r * x * r⁻¹ * x⁻¹ = t) : False := by
  have c := h.toSec5RCtx
  have htt := sec5p510c_t_mul_t h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hBA : B ≤ A := c.A_eq ▸ le_sup_right
  have hrA : r ∈ A := c.A_eq ▸ Subgroup.mem_sup_left (mem_zpowers r)
  have htA : t ∈ A := hBA c.B_split.1
  have hxt' : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp (c.sylow.1 hx.1)
  have hxB : ∀ b ∈ B, x * b = b * x := fun b hb =>
    (Subgroup.mem_centralizer_iff.mp hx.2 b (c.B_le hb).1).symm
  have hrx : r * x * r⁻¹ = t * x := by
    calc r * x * r⁻¹ = (r * x * r⁻¹ * x⁻¹) * x := by group
      _ = t * x := by rw [hd]
  have hxr : x * r * x⁻¹ = t * r := by
    calc x * r * x⁻¹ = x * (r * x * r⁻¹)⁻¹ * r := by group
      _ = x * (t * x)⁻¹ * r := by rw [hrx]
      _ = t⁻¹ * r := by group
      _ = t * r := by rw [htinv]
  have hxr' : x⁻¹ * r * x = t * r := by
    calc x⁻¹ * r * x = x⁻¹ * (r * x * r⁻¹) * r := by group
      _ = x⁻¹ * (t * x) * r := by rw [hrx]
      _ = x⁻¹ * (x * t) * r := by rw [hxt']
      _ = t * r := by group
  have hxN : x ∈ normalizer (A : Set G) :=
    sec5p510c_mem_normalizer_A c hxB (hxr ▸ A.mul_mem htA hrA) (hxr' ▸ A.mul_mem htA hrA)
  have hrN : r ∈ normalizer (L : Set G) :=
    mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_lemma36 hy.h36 c.toSec3SettingLB r
      (c.sylow.1 (c.A_le hrA)))
  obtain ⟨g, hg⟩ := c.conj_r
  have hrD : r ∈ conjClassIn (normalizer (A : Set G)) t := by
    have := sec5p510_tG_inter_A h (g := g) (by rw [hg]; exact hrA)
    rwa [hg] at this
  have hrt : r ≠ t := by
    intro hrt
    have htC : t ∈ centralizer (L : Set G) := sec4_t_mem_centralizer c.toSec3Setting
    exact hy.tab.kind_ne_central G L c.toSec5Setting.isOm6Z2 r (sec5b_orderOf_r c) hrN
      (Or.inr (Or.inl c.type_r)) (hrt ▸ htC)
  have hr1 : r ∈ wclass φ 1 := by
    have hrD' := hrD
    rw [h.delta] at hrD'
    rcases hrD' with h6 | h1
    · exfalso
      have ht6 : (wclass φ 6 : Set G) = {t} := by
        simpa only [Pi.one_def, h.model.map_one] using h.model.perm.wclass_six
      exact hrt (by simpa [ht6] using h6)
    · exact h1
  have h5 : t * r ∈ wclass φ 5 := by
    simpa using sec5p510c_t_mul_mem h (k := 1) (by norm_num) hr1
  have hD : x * r * x⁻¹ ∈ conjClassIn (normalizer (A : Set G)) t := by
    obtain ⟨m, hm, hmr⟩ := hrD
    exact ⟨x * m, mul_mem hxN hm, by rw [hmr]; group⟩
  rw [hxr, h.delta] at hD
  rcases hD with h6 | h1
  · exact Set.disjoint_left.mp (h.model.perm.disjoint_wclass (by norm_num : (5 : ℕ) ≠ 6)) h5 h6
  · exact Set.disjoint_left.mp (h.model.perm.disjoint_wclass (by norm_num : (5 : ℕ) ≠ 1)) h5 h1

end CFSG.OddStandard.SmallF3.Omega
