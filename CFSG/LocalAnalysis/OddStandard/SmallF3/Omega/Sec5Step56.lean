module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5L56
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Growth
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Conj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Asc82Pair56 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ t : G, t ∈ centerIn L → orderOf t = 2 → ∀ z : G, IsI4PlusIn L z →
      ∃ w : G, IsI4PlusIn L w ∧ w * z = z * w ∧ IsI4PlusIn L (t * z * w)

@[expose] def Asc82Coset56 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ t : G, t ∈ centerIn L → orderOf t = 2 →
      ∀ b e : G, orderOf b = 2 → orderOf e = 2 →
        (∃ α : ℤˣ, InducesTypeSome L b 6 (-1) 3 α) → (∃ u ∈ L, e = u * b) →
          e ∈ conjClassIn L b ∨ e ∈ conjClassIn L (t * b) ∨
            ∃ β : ℤˣ, InducesTypeSome L e 6 (-1) 1 β

structure Asc82Tab56 : Prop where
  pair : Asc82Pair56
  coset : Asc82Coset56

theorem sec5_isSylow2Of_centralizer_conj [Finite G] {t t' : G} {S : Subgroup G}
    (hS : IsSylow2Of S (centralizer ({t} : Set G))) {g : G} (hg : g⁻¹ * t * g = t')
    (hle : S ≤ centralizer ({t'} : Set G)) : IsSylow2Of S (centralizer ({t'} : Set G)) := by
  obtain ⟨hS1, hS2, hS3⟩ := hS
  refine ⟨hle, hS2, ?_⟩
  have hconj : CFSG.conjugate (centralizer ({t} : Set G)) g = centralizer ({t'} : Set G) := by
    rw [← hg]
    exact conjugate_centralizer_singleton t g
  have hcard : Nat.card (centralizer ({t'} : Set G)) = Nat.card (centralizer ({t} : Set G)) := by
    rw [← hconj]
    exact Nat.card_congr (Subgroup.equivMapOfInjective (centralizer ({t} : Set G))
      (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).symm.toEquiv
  have hidx : (centralizer ({t'} : Set G)).index = (centralizer ({t} : Set G)).index := by
    have h1 := Subgroup.card_mul_index (centralizer ({t} : Set G))
    have h2 := Subgroup.card_mul_index (centralizer ({t'} : Set G))
    rw [hcard] at h2
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h2.trans h1.symm)
  have hr1 := Subgroup.relIndex_mul_index hS1
  have hr2 := Subgroup.relIndex_mul_index hle
  have hne : (centralizer ({t} : Set G)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have heq : S.relIndex (centralizer ({t'} : Set G)) = S.relIndex (centralizer ({t} : Set G)) := by
    rw [hidx] at hr2
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) (hr2.trans hr1.symm)
  rw [heq]
  exact hS3

theorem sec5_step56_ctx [Finite G] (h52b : Asc82Lemma52b) (h53 : Asc82Lemma53)
    (h37 : Asc82Lemma37) (hZ : Asc82ZExists) (tab : Asc82Tab5) {t : G} {L S : Subgroup G}
    {z : G} (h : Sec5Ctx G t L S z) {g₀ : G} (hg₀ : g₀⁻¹ * t * g₀ = t * z) :
    Sec5Ctx G (t * z) (CFSG.conjugate L g₀) S z := by
  have ht2 : orderOf t = 2 := h.involution
  have hz2 : orderOf z = 2 := h.pocket.1
  have htS : t ∈ S := sec4_t_mem_S h.sylow ht2
  have htz : t * z = z * t := h.central t htS
  have h' : Sec5Setting G (t * z) (CFSG.conjugate L g₀) := by
    have := h.toSec5Setting.conjugate g₀
    rwa [hg₀] at this
  have hle : S ≤ centralizer ({t * z} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : s * t = t * s := Subgroup.mem_centralizer_singleton_iff.mp (h.sylow.1 hs)
    have h2 : s * z = z * s := h.central s hs
    calc s * (t * z) = (s * t) * z := by group
      _ = (t * s) * z := by rw [h1]
      _ = t * (s * z) := by group
      _ = t * (z * s) := by rw [h2]
      _ = (t * z) * s := by group
  have hS' : IsSylow2Of S (centralizer ({t * z} : Set G)) :=
    sec5_isSylow2Of_centralizer_conj h.sylow hg₀ hle
  obtain ⟨z'', hnot⟩ := hZ G (t * z) (CFSG.conjugate L g₀) h'.toSec3SettingLB S hS'
  have hctx : Sec5Ctx G (t * z) (CFSG.conjugate L g₀) S z'' := ⟨h', hnot⟩
  have hΩ1 := h53 G t L S z h
  have hΩ2 := h53 G (t * z) (CFSG.conjugate L g₀) S z'' hctx
  have hmem : z'' ∈ zpowers t ⊔ zpowers z := by
    rw [← hΩ1, hΩ2]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z'')
  have hz''2 : orderOf z'' = 2 := hnot.pocket.1
  have hL' : IsOm6Z2 (CFSG.conjugate L g₀) := h'.isOm6Z2
  rcases sec5_klein_involutions ht2 hz2 htz hmem hz''2 with h1 | h2 | h3
  ·
    exfalso
    obtain ⟨a, -, hab⟩ := sec5_pocket_class h52b tab hctx
      (h.pocket.conjugate g₀ : IsI4PlusIn (CFSG.conjugate L g₀) (g₀⁻¹ * z * g₀))
    refine sec5_t_not_conj_z h37 h (g₀ * a) ?_
    calc (g₀ * a)⁻¹ * z * (g₀ * a) = a⁻¹ * (g₀⁻¹ * z * g₀) * a := by group
      _ = a⁻¹ * (a * z'' * a⁻¹) * a := by rw [hab]
      _ = z'' := by group
      _ = t := h1
  · rw [h2] at hctx
    exact hctx
  ·
    exfalso
    have hZ' : t * z ∈ centerIn (CFSG.conjugate L g₀) := sec5_t_mem_centerIn h52b h'
    have hcen : t * z ∈ centralizer ((CFSG.conjugate L g₀ : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy => ((sec5_mem_centerIn_iff.mp hZ').2 y hy).symm
    exact (tab.pocket_kind G _ hL' z'' hctx.pocket).2 (h3 ▸ hcen)

theorem sec5_step56_pocket_of_mem [Finite G] (h52b : Asc82Lemma52b) (h54 : Asc82Lemma54)
    (tab : Asc82Tab5) {t : G} {L L' S : Subgroup G} {z : G} (h : Sec5Ctx G t L S z)
    (h' : Sec5Ctx G (t * z) L' S z) {w : G} (hw : IsI4PlusIn L w) (hwz : w * z = z * w)
    (hwL' : w ∈ L') : IsI4PlusIn L' w := by
  obtain ⟨a, haL, hwa⟩ := sec5_pocket_class h52b tab h hw
  have htZ : t ∈ centerIn L := sec5_t_mem_centerIn h52b h.toSec5Setting
  have htw : t * w = w * t := (sec5_mem_centerIn_iff.mp htZ).2 w hw.mem
  have hwC : w ∈ centralizer ({t * z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc w * (t * z) = (w * t) * z := by group
      _ = (t * w) * z := by rw [htw]
      _ = t * (w * z) := by group
      _ = t * (z * w) := by rw [hwz]
      _ = (t * z) * w := by group
  have hcw : (a⁻¹)⁻¹ * z * a⁻¹ = w := by rw [inv_inv, hwa]
  have hL' : IsOm6Z2 L' := h'.toSec5Setting.isOm6Z2
  rcases h54 G (t * z) L' S z h' a⁻¹ (by rw [hcw]; exact hwC) with hcl | ⟨α, hα⟩
  · rw [hcw] at hcl
    obtain ⟨c, hc, hwc⟩ := hcl
    rw [hwc]
    exact IsI4PlusIn.conj_of_mem h'.pocket hc
  · exfalso
    rw [hcw] at hα
    have hw2 : orderOf w = 2 := hw.1
    have hwN : w ∈ normalizer (L' : Set G) := Subgroup.le_normalizer hwL'
    have hk3 : Kind5 L' w 3 := ⟨α, hα⟩
    have hnc := tab.kind_ne_central G L' hL' w hw2 hwN (Or.inr (Or.inr (Or.inl hk3)))
    have hk0 : Kind5 L' w 0 := ⟨Subgroup.mem_sup_left hwL', hnc⟩
    exact tab.excl G L' hL' w hw2 hwN 0 3 (by norm_num) (by norm_num) (by norm_num) hk0 hk3

theorem sec5_step56_key [Finite G] (h52b : Asc82Lemma52b) (h54 : Asc82Lemma54)
    (h37 : Asc82Lemma37) (tab : Asc82Tab5) (tab56 : Asc82Tab56) {t : G} {L L' S : Subgroup G}
    {z : G} (h : Sec5Ctx G t L S z) (h' : Sec5Ctx G (t * z) L' S z) {g₀ : G}
    (hg₀ : g₀⁻¹ * t * g₀ = t * z) {b : G} (hb : IsI4PlusIn L b)
    (hb' : IsI4PlusIn L (t * z * b)) (hbz : b * z = z * b) (hbL' : b ∉ L') :
    ∃ β : ℤˣ, InducesTypeSome L' (t * b) 6 (-1) 1 β := by
  have htZ : t ∈ centerIn L := sec5_t_mem_centerIn h52b h.toSec5Setting
  have ht2 : orderOf t = 2 := h.involution
  have hz2 : orderOf z = 2 := h.pocket.1
  have htc : ∀ y ∈ L, t * y = y * t := (sec5_mem_centerIn_iff.mp htZ).2
  have hb2 : orderOf b = 2 := hb.1
  have hbL : b ∈ L := hb.mem
  have ht1 : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hz1 : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hb1 : b * b = 1 := by rw [← pow_two, ← hb2, pow_orderOf_eq_one]
  obtain ⟨a, haL, hba⟩ := sec5_pocket_class h52b tab h hb
  have hL' : IsOm6Z2 L' := h'.toSec5Setting.isOm6Z2
  have ht'Z : t * z ∈ centerIn L' := sec5_t_mem_centerIn h52b h'.toSec5Setting
  have ht'2 : orderOf (t * z) = 2 := h'.involution
  have hzL' : z ∈ L' := h'.pocket.mem
  have htL' : t ∈ L' := by
    have h1 : t * z ∈ L' := (sec5_mem_centerIn_iff.mp ht'Z).1
    have h2 : t = (t * z) * z := by
      calc t = t * (z * z) := by rw [hz1, mul_one]
        _ = (t * z) * z := by group
    rw [h2]
    exact mul_mem h1 hzL'
  have htb : t * b = b * t := htc b hbL
  have hbC : b ∈ centralizer ({t * z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc b * (t * z) = (b * t) * z := by group
      _ = (t * b) * z := by rw [htb]
      _ = t * (b * z) := by group
      _ = t * (z * b) := by rw [hbz]
      _ = (t * z) * b := by group
  obtain ⟨α, hα⟩ : ∃ α : ℤˣ, InducesTypeSome L' b 6 (-1) 3 α := by
    have hcw : (a⁻¹)⁻¹ * z * a⁻¹ = b := by rw [inv_inv, hba]
    rcases h54 G (t * z) L' S z h' a⁻¹ (by rw [hcw]; exact hbC) with hcl | hk
    · exfalso
      rw [hcw] at hcl
      obtain ⟨c, hc, hbc⟩ := hcl
      exact hbL' (hbc ▸ mul_mem (mul_mem hc hzL') (inv_mem hc))
    · rw [hcw] at hk
      exact hk
  have he2 : orderOf (t * b) = 2 := by
    have hsq : (t * b) ^ 2 = 1 := by
      calc (t * b) ^ 2 = (t * b) * (t * b) := by rw [pow_two]
        _ = t * (b * t) * b := by group
        _ = t * (t * b) * b := by rw [htb]
        _ = (t * t) * (b * b) := by group
        _ = 1 := by rw [ht1, hb1, one_mul]
    have hne : t * b ≠ 1 := by
      intro h1
      have h2 : b = t⁻¹ := eq_inv_of_mul_eq_one_right h1
      have h3 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht1
      refine sec5_t_not_conj_z h37 h a⁻¹ ?_
      rw [inv_inv, ← hba, h2, h3]
    exact orderOf_eq_prime hsq hne
  have hnot : ∀ c : G, c * z * c⁻¹ ≠ t * b := by
    intro c hc
    have h1 : t * b = (a * g₀⁻¹) * t * (a * g₀⁻¹)⁻¹ := by
      calc t * b = t * (a * z * a⁻¹) := by rw [hba]
        _ = a * (t * z) * a⁻¹ := by
          have hta : t * a = a * t := htc a haL
          calc t * (a * z * a⁻¹) = (t * a) * z * a⁻¹ := by group
            _ = (a * t) * z * a⁻¹ := by rw [hta]
            _ = a * (t * z) * a⁻¹ := by group
        _ = a * (g₀⁻¹ * t * g₀) * a⁻¹ := by rw [hg₀]
        _ = (a * g₀⁻¹) * t * (a * g₀⁻¹)⁻¹ := by group
    refine sec5_t_not_conj_z h37 h (c⁻¹ * (a * g₀⁻¹)) ?_
    calc (c⁻¹ * (a * g₀⁻¹))⁻¹ * z * (c⁻¹ * (a * g₀⁻¹))
        = (a * g₀⁻¹)⁻¹ * (c * z * c⁻¹) * (a * g₀⁻¹) := by group
      _ = (a * g₀⁻¹)⁻¹ * (t * b) * (a * g₀⁻¹) := by rw [hc]
      _ = t := by rw [h1]; group
  rcases tab56.coset G L' hL' (t * z) ht'Z ht'2 b (t * b) hb2 he2 ⟨α, hα⟩ ⟨t, htL', rfl⟩
    with h1 | h2 | h3
  · exfalso
    obtain ⟨x, -, hx⟩ := h1
    refine hnot (x * a) ?_
    rw [hx, hba]
    group
  · exfalso
    obtain ⟨x, -, hx⟩ := h2
    obtain ⟨a', -, hba'⟩ := sec5_pocket_class h52b tab h hb'
    refine hnot (x * a') ?_
    rw [hx, hba']
    group
  · exact h3

theorem asc82Step56_of (h52b : Asc82Lemma52b) (h53 : Asc82Lemma53) (h54 : Asc82Lemma54)
    (h37 : Asc82Lemma37) (hZ : Asc82ZExists) (tab : Asc82Tab5) (tab56 : Asc82Tab56) :
    Asc82Step56 := by
  intro G _ _ t L S z h g₀ hg₀
  have h' := sec5_step56_ctx h52b h53 h37 hZ tab h hg₀
  have hL : IsOm6Z2 L := h.toSec5Setting.isOm6Z2
  have htZ : t ∈ centerIn L := sec5_t_mem_centerIn h52b h.toSec5Setting
  obtain ⟨w, hw, hwz, hw'⟩ := tab56.pair G L hL t htZ h.involution z h.pocket
  have ht2 : orderOf t = 2 := h.involution
  have hz2 : orderOf z = 2 := h.pocket.1
  have htS : t ∈ S := sec4_t_mem_S h.sylow ht2
  have htz : t * z = z * t := h.central t htS
  have ht1 : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hz1 : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hw'z : (t * z * w) * z = z * (t * z * w) := by
    have e1 : (t * z * w) * z = t * w := by
      calc (t * z * w) * z = t * z * (w * z) := by group
        _ = t * z * (z * w) := by rw [hwz]
        _ = t * (z * z) * w := by group
        _ = t * w := by rw [hz1, mul_one]
    have e2 : z * (t * z * w) = t * w := by
      calc z * (t * z * w) = (z * t) * z * w := by group
        _ = (t * z) * z * w := by rw [← htz]
        _ = t * (z * z) * w := by group
        _ = t * w := by rw [hz1, mul_one]
    rw [e1, e2]
  have hpp : t * z * (t * z * w) = w := by
    calc t * z * (t * z * w) = t * (z * t) * z * w := by group
      _ = t * (t * z) * z * w := by rw [← htz]
      _ = (t * t) * (z * z) * w := by group
      _ = w := by rw [ht1, hz1, one_mul, one_mul]
  by_cases hwL' : w ∈ CFSG.conjugate L g₀
  · have hw'L' : t * z * w ∉ CFSG.conjugate L g₀ := by
      intro hw'L'
      have hp1 := sec5_step56_pocket_of_mem h52b h54 tab h h' hw hwz hwL'
      have hp2 := sec5_step56_pocket_of_mem h52b h54 tab h h' hw' hw'z hw'L'
      exact (tab.tz_not_pocket G _ h'.toSec5Setting.isOm6Z2 (t * z)
        (sec5_t_mem_centerIn h52b h'.toSec5Setting) h'.involution w hp1) hp2
    obtain ⟨β, hβ⟩ := sec5_step56_key h52b h54 h37 tab tab56 h h' hg₀ hw'
      (by rw [hpp]; exact hw) hw'z hw'L'
    exact ⟨t * z * w, hw', β, hβ⟩
  · obtain ⟨β, hβ⟩ := sec5_step56_key h52b h54 h37 tab tab56 h h' hg₀ hw hw' hwz hwL'
    exact ⟨w, hw, β, hβ⟩

end CFSG.OddStandard.SmallF3.Omega
