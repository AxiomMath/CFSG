module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Bundles
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Cb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Da

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10C_two_elem_R [Finite G] (h36 : Asc82Lemma36) (h106 : Asc82Lemma106) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {w : G}
    (hwt : w ∈ centralizer ({t} : Set G)) (hwL : w ∈ centralizer (L : Set G))
    (hw2 : IsPGroup 2 (zpowers w)) : w ∈ zpowers t := by
  obtain ⟨Q, hQ, hwQ⟩ := exists_isSylow2Of_ge hw2 (Subgroup.zpowers_le.mpr hwt)
  obtain ⟨a, ha, haQ⟩ := IsSylow2Of.exists_conj_mem hctx.sylow hQ
  have haL : a ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 hctx.toSec10Z.toSec10Setting.toSec3SettingLB a ha
  have hwS : a⁻¹ * w * a ∈ S := (haQ w).mp (hwQ (Subgroup.mem_zpowers w))
  have hwC : a⁻¹ * w * a ∈ centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : a * l * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp haL l).mp hl
    have h1 := Subgroup.mem_centralizer_iff.mp hwL _ hl'
    calc l * (a⁻¹ * w * a) = a⁻¹ * (a * l * a⁻¹ * w) * a := by group
      _ = a⁻¹ * (w * (a * l * a⁻¹)) * a := by rw [h1]
      _ = a⁻¹ * w * a * l := by group
  have hmem : a⁻¹ * w * a ∈ zpowers t := by
    rw [← h106 G t L S z K1 K2 hctx]
    exact ⟨hwC, hwS⟩
  have haN : a ∈ normalizer (zpowers t : Set G) := by
    refine sec10C_mem_normalizer_of_comm fun x hx => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (show Commute t a from (Subgroup.mem_centralizer_singleton_iff.mp
      ha).symm) n).eq
  have h2 := (Subgroup.mem_normalizer_iff.mp haN (a⁻¹ * w * a)).mp hmem
  have e : a * (a⁻¹ * w * a) * a⁻¹ = w := by group
  rwa [e] at h2

theorem sec10C_dihedral_core {c z' : G} (hz2 : z' * z' = 1) (hinv : z' * c * z' = c⁻¹) (j : ℕ) :
    c ^ j * (c * z') * (c ^ j)⁻¹ = c ^ (2 * j + 1) * z' := by
  have hz'inv : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz2
  have h1 : z' * c ^ j * z' = (c ^ j)⁻¹ := by
    have h := conj_pow (i := j) (a := z') (b := c)
    rw [hz'inv, hinv, inv_pow] at h
    exact h.symm
  have h2 : z' * (c ^ j)⁻¹ * z' = c ^ j := by
    have e : (z' * c ^ j * z')⁻¹ = z' * (c ^ j)⁻¹ * z' := by
      rw [mul_inv_rev, mul_inv_rev, hz'inv, mul_assoc]
    rw [← e, h1, inv_inv]
  have e : c ^ j * c * c ^ j = c ^ (2 * j + 1) := by
    rw [← pow_succ, ← pow_add]
    congr 1
    ring
  calc c ^ j * (c * z') * (c ^ j)⁻¹ = c ^ j * c * z' * (c ^ j)⁻¹ * (z' * z') := by
        rw [hz2, mul_one]; group
    _ = c ^ j * c * (z' * (c ^ j)⁻¹ * z') * z' := by group
    _ = c ^ (2 * j + 1) * z' := by rw [h2, e]

theorem sec10C_exists_odd_pow_pgroup [Finite G] (c : G) :
    ∃ m : ℕ, Odd m ∧ IsPGroup 2 (zpowers (c ^ m)) := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  refine ⟨m, hm, IsPGroup.of_card (n := k) ?_⟩
  rw [Nat.card_zpowers, orderOf_pow_of_dvd hm.pos.ne' (Dvd.intro_left (2 ^ k) hn.symm), hn]
  exact Nat.mul_div_cancel _ hm.pos

theorem sec10C_dihedral [Finite G] {c z' t : G} (hz2 : z' * z' = 1) (ht2 : t * t = 1)
    (hinv : z' * c * z' = c⁻¹)
    (h2 : ∀ w ∈ zpowers c, IsPGroup 2 (zpowers w) → w ∈ zpowers t) :
    (∃ x : G, x * (c * z') * x⁻¹ = z') ∨ (∃ x : G, x * (c * z') * x⁻¹ = t * z') := by
  obtain ⟨m, hm, hpg⟩ := sec10C_exists_odd_pow_pgroup c
  obtain ⟨j, hj⟩ := hm
  have hmem : c ^ m ∈ zpowers t := h2 _ (Subgroup.npow_mem_zpowers c m) hpg
  have hx := sec10C_dihedral_core hz2 hinv j
  rw [← hj] at hx
  rcases sec10D_eq_one_or_of_mem_zpowers ht2 hmem with h1 | h1
  · exact Or.inl ⟨c ^ j, by rw [hx, h1, one_mul]⟩
  · exact Or.inr ⟨c ^ j, by rw [hx, h1]⟩

theorem sec10C_tz_conj [Finite G] (h36 : Asc82Lemma36) (h106 : Asc82Lemma106)
    (hf : Asc82Facts10) (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {s z' : G} (hs : s ∈ S)
    (hs2 : s * s = 1) (hsty : InducesTypeSome L s 5 1 2 1) (hsk : ∃ k : G, k⁻¹ * t * k = s)
    (hz' : z' ∈ S) (hz'2 : z' * z' = 1) (hz'ty : InducesTypeSome L z' 5 1 2 1)
    (hz'nt : ∀ k : G, k⁻¹ * z' * k ≠ t) : ∃ k : G, k⁻¹ * t * k = t * z' := by
  obtain ⟨hpsp, htC, -, -, -, -⟩ := hb G t L S z hctx.toSec10Z
  have ht2 : t * t = 1 := (sec10D_basic hb hctx).1
  obtain ⟨l, hl, hc⟩ := hf.factsC.i2p G L hpsp s z' hsty hz'ty
  obtain ⟨s', hs'def⟩ : ∃ s', s' = l⁻¹ * s * l := ⟨_, rfl⟩
  rw [← hs'def] at hc
  have hs'2 : s' * s' = 1 := by
    rw [hs'def]
    calc l⁻¹ * s * l * (l⁻¹ * s * l) = l⁻¹ * (s * s) * l := by group
      _ = 1 := by rw [hs2]; group
  have hs'inv : s'⁻¹ = s' := inv_eq_of_mul_eq_one_right hs'2
  have hz'inv : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'2
  rw [hs'inv] at hc
  have hct_l : Commute t l := (Subgroup.mem_centralizer_iff.mp htC l hl).symm
  have hct_s : Commute t s :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 hs)).symm
  have hct_z : Commute t z' :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 hz')).symm
  have hct_s' : Commute t s' := by
    rw [hs'def]
    exact (hct_l.inv_right.mul_right hct_s).mul_right hct_l
  have hcC : s' * z' ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hct_s'.mul_right hct_z).eq.symm
  have hinv : z' * (s' * z') * z' = (s' * z')⁻¹ := by
    calc z' * (s' * z') * z' = z' * s' * (z' * z') := by group
      _ = z' * s' := by rw [hz'2, mul_one]
      _ = (s' * z')⁻¹ := by rw [mul_inv_rev, hs'inv, hz'inv]
  have h2 : ∀ w ∈ zpowers (s' * z'), IsPGroup 2 (zpowers w) → w ∈ zpowers t := fun w hw hw2 =>
    sec10C_two_elem_R h36 h106 hctx
      ((Subgroup.zpowers_le.mpr hcC) hw) ((Subgroup.zpowers_le.mpr hc) hw) hw2
  have e : s' * z' * z' = s' := by rw [mul_assoc, hz'2, mul_one]
  obtain ⟨k, hk⟩ := hsk
  rcases sec10C_dihedral hz'2 ht2 hinv h2 with ⟨x, hx⟩ | ⟨x, hx⟩
  · rw [e] at hx
    exfalso
    refine hz'nt (x * l⁻¹ * k⁻¹) ?_
    rw [← hx, hs'def, ← hk]
    group
  · rw [e] at hx
    refine ⟨k * l * x⁻¹, ?_⟩
    rw [← hx, hs'def, ← hk]
    group

end CFSG.OddStandard.SmallF3.Omega
