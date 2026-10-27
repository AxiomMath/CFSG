module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Defs
import CFSG.LocalAnalysis.GLTheoremB.LayerTools
import CFSG.Quasithin.Background.F918V5GComp
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.GLTheoremB.GammaBasic

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

set_option linter.unusedSectionVars false

section Joins

variable {Q : Type*} [Group Q]

theorem t113_mem_normalizer_of_commute {J : Subgroup Q} {e : Q}
    (h : ∀ j ∈ J, e * j = j * e) : e ∈ Subgroup.normalizer (J : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro j
  constructor
  · intro hj
    have : e * j * e⁻¹ = j := by rw [h j hj]; group
    rw [this]; exact hj
  · intro hj
    have h1 := h _ hj
    have h2 : e * j * e⁻¹ = j := by
      have : e * (e * j * e⁻¹) = e * j := by rw [h1]; group
      exact mul_left_cancel this
    rwa [h2] at hj

theorem t113_mem_sup {P R : Subgroup Q} (h : ∀ p ∈ P, ∀ r ∈ R, p * r = r * p) {z : Q}
    (hz : z ∈ P ⊔ R) : ∃ p ∈ P, ∃ r ∈ R, p * r = z := by
  have hle : P ≤ Subgroup.normalizer (R : Set Q) := fun p hp =>
    t113_mem_normalizer_of_commute (fun r hr => h p hp r hr)
  have := Subgroup.coe_mul_of_left_le_normalizer_right P R hle
  have hz' : z ∈ (↑(P ⊔ R) : Set Q) := hz
  rw [this] at hz'
  obtain ⟨p, hp, r, hr, rfl⟩ := hz'
  exact ⟨p, hp, r, hr, rfl⟩

theorem t113_sup_elemAbelian {n : ℕ} {P R : Subgroup Q} (hP : IsElemAbelian n P)
    (hR : IsElemAbelian n R) (h : ∀ p ∈ P, ∀ r ∈ R, p * r = r * p) (hi : P ⊓ R = ⊥) :
    IsElemAbelian n (P ⊔ R) ∧ Nat.card ↥(P ⊔ R) = Nat.card P * Nat.card R := by
  have hcomm : ∀ z ∈ P ⊔ R, ∀ w ∈ P ⊔ R, z * w = w * z := by
    intro z hz w hw
    obtain ⟨p, hp, r, hr, rfl⟩ := t113_mem_sup h hz
    obtain ⟨p', hp', r', hr', rfl⟩ := t113_mem_sup h hw
    have e1 : p * p' = p' * p := by
      have := hP.1.is_comm.comm (⟨p, hp⟩ : P) ⟨p', hp'⟩
      exact congrArg Subtype.val this
    have e2 : r * r' = r' * r := by
      have := hR.1.is_comm.comm (⟨r, hr⟩ : R) ⟨r', hr'⟩
      exact congrArg Subtype.val this
    calc p * r * (p' * r') = p * (r * p') * r' := by group
      _ = p * (p' * r) * r' := by rw [← h p' hp' r hr]
      _ = (p * p') * (r * r') := by group
      _ = (p' * p) * (r' * r) := by rw [e1, e2]
      _ = p' * (p * r') * r := by group
      _ = p' * (r' * p) * r := by rw [h p hp r' hr']
      _ = p' * r' * (p * r) := by group
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)⟩⟩, ?_⟩, ?_⟩
  · intro z hz
    obtain ⟨p, hp, r, hr, rfl⟩ := t113_mem_sup h hz
    have hc : Commute p r := h p hp r hr
    rw [hc.mul_pow, hP.2 p hp, hR.2 r hr, one_mul]
  · let f : P × R → ↥(P ⊔ R) := fun pr =>
      ⟨pr.1.1 * pr.2.1, Subgroup.mul_mem _ (Subgroup.mem_sup_left pr.1.2)
        (Subgroup.mem_sup_right pr.2.2)⟩
    have hf : Function.Bijective f := by
      constructor
      · rintro ⟨⟨p, hp⟩, ⟨r, hr⟩⟩ ⟨⟨p', hp'⟩, ⟨r', hr'⟩⟩ he
        have he' : p * r = p' * r' := congrArg Subtype.val he
        have h1 : p'⁻¹ * p = r' * r⁻¹ := by
          have : p'⁻¹ * (p * r) * r⁻¹ = p'⁻¹ * (p' * r') * r⁻¹ := by rw [he']
          simpa [mul_assoc] using this
        have h2 : p'⁻¹ * p ∈ P ⊓ R := ⟨P.mul_mem (P.inv_mem hp') hp, h1 ▸ R.mul_mem hr' (R.inv_mem hr)⟩
        rw [hi, Subgroup.mem_bot] at h2
        have h3 : p = p' := inv_mul_eq_one.1 h2 |>.symm
        subst h3
        have : r = r' := mul_left_cancel he'
        subst this
        rfl
      · rintro ⟨z, hz⟩
        obtain ⟨p, hp, r, hr, rfl⟩ := t113_mem_sup h hz
        exact ⟨(⟨p, hp⟩, ⟨r, hr⟩), rfl⟩
    rw [← Nat.card_prod]
    exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem t113_zpowers_elem {y : Q} (hy : orderOf y = 3) :
    IsElemAbelian 3 (Subgroup.zpowers y) ∧ Nat.card (Subgroup.zpowers y) = 3 := by
  refine ⟨⟨inferInstance, ?_⟩, by rw [Nat.card_zpowers, hy]⟩
  rintro _ ⟨n, rfl⟩
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hy, pow_orderOf_eq_one,
    one_zpow]

theorem t113_orderOf_conj (g y : Q) : orderOf (g⁻¹ * y * g) = orderOf y := by
  have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective y
  simpa [MulAut.conj_apply] using this

theorem t113_bot_elem : IsElemAbelian 3 (⊥ : Subgroup Q) ∧ Nat.card (⊥ : Subgroup Q) = 1 := by
  refine ⟨⟨inferInstance, fun z hz => ?_⟩, Subgroup.card_bot⟩
  rw [Subgroup.mem_bot] at hz
  simp [hz]

theorem t113_elemAbelian_of_le {n : ℕ} {B E : Subgroup Q} (hB : IsElemAbelian n B) (h : E ≤ B) :
    IsElemAbelian n E := CFSG.Open.IsElemAbelian.mono hB h

end Joins

section Triple

variable {Q : Type} [Group Q] [Finite Q]

@[expose] def t113K (B L : Subgroup Q) : Subgroup Q := ⨆ g ∈ B, GLBConj g L

@[expose] def t113A (B L : Subgroup Q) : Subgroup Q := Subgroup.normalizer (L : Set Q) ⊓ B

@[expose] def t113B0 (B L : Subgroup Q) : Subgroup Q :=
  B ⊓ Subgroup.centralizer (t113K B L : Set Q)

@[expose] noncomputable def t113Rho (B L : Subgroup Q) : ↥(t113A B L) →* MulAut ↥L :=
  L.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_left)

@[expose] noncomputable def t113H (B L : Subgroup Q) : Subgroup (MulAut ↥L) :=
  (t113Rho B L).range

structure Triple113 (B L : Subgroup Q) (x : Q) : Prop where
  elem : IsElemAbelian 3 B
  comp : IsComponentOf L ⊤
  center : Subgroup.center ↥L = ⊥
  mem : x ∈ B
  not_mem : x ∉ Subgroup.normalizer (L : Set Q)
  index : (Subgroup.normalizer (L : Set Q)).relIndex B = 3

namespace Triple113

variable {B L : Subgroup Q} {x : Q} (T : Triple113 B L x)

include T

theorem comm_B {a b : Q} (ha : a ∈ B) (hb : b ∈ B) : a * b = b * a := by
  have := T.elem.1.is_comm.comm (⟨a, ha⟩ : B) ⟨b, hb⟩
  exact congrArg Subtype.val this

theorem pow_three_mem : x ^ 3 ∈ Subgroup.normalizer (L : Set Q) := by
  set N := Subgroup.normalizer (L : Set Q)
  have : (N.subgroupOf B).Normal := ⟨fun n hn g => by
    have : ((g * n * g⁻¹ : B) : Q) = (n : Q) := by
      have h := T.comm_B g.2 n.2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [h]; group
    rw [Subgroup.mem_subgroupOf, this]
    exact hn⟩
  have h := Subgroup.pow_index_mem (N.subgroupOf B) (⟨x, T.mem⟩ : B)
  have hi : (N.subgroupOf B).index = 3 := T.index
  rw [hi, Subgroup.mem_subgroupOf] at h
  exact h

theorem pow_two_not_mem : x ^ 2 ∉ Subgroup.normalizer (L : Set Q) := by
  intro h
  apply T.not_mem
  have : x = x ^ 3 * (x ^ 2)⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ T.pow_three_mem (Subgroup.inv_mem _ h)

theorem conj1_ne : GLBConj x L ≠ L := fun h => T.not_mem (mem_normalizer_iff_gLBConj_eq.2 h)

theorem conj2_ne : GLBConj (x ^ 2) L ≠ L := fun h =>
  T.pow_two_not_mem (mem_normalizer_iff_gLBConj_eq.2 h)

theorem conj21_ne : GLBConj (x ^ 2) L ≠ GLBConj x L := by
  intro h
  have h1 := congrArg (GLBConj x⁻¹) h
  rw [gLBConj_gLBConj, gLBConj_gLBConj, mul_inv_cancel, gLBConj_one,
    show x ^ 2 * x⁻¹ = x by group] at h1
  exact T.conj1_ne h1

theorem comp_conj (g : Q) : IsComponentOf (GLBConj g L) ⊤ := isComponentOf_gLBConj T.comp g

theorem comm_of_ne {g h : Q} (hne : GLBConj g L ≠ GLBConj h L) :
    ∀ u ∈ GLBConj g L, ∀ w ∈ GLBConj h L, u * w = w * u := by
  rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute (T.comp_conj g) (T.comp_conj h) with
    h1 | h1
  · exact absurd h1 hne
  · exact h1

theorem eq_one_of_central {g z : Q} (hz : z ∈ GLBConj g L)
    (hc : ∀ w ∈ GLBConj g L, z * w = w * z) : z = 1 := by
  have h1 : g * z * g⁻¹ ∈ L := mem_gLBConj.1 hz
  have h2 : (⟨g * z * g⁻¹, h1⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro u
    have hw : g⁻¹ * u * g ∈ GLBConj g L := by
      rw [mem_gLBConj]; simp [mul_assoc]
    have := hc _ hw
    apply Subtype.ext
    show (u : Q) * (g * z * g⁻¹) = (g * z * g⁻¹) * u
    calc (u : Q) * (g * z * g⁻¹) = g * ((g⁻¹ * u * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * u * g)) * g⁻¹ := by rw [this]
      _ = (g * z * g⁻¹) * u := by group
  rw [T.center, Subgroup.mem_bot] at h2
  have h3 : g * z * g⁻¹ = 1 := congrArg Subtype.val h2
  calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
    _ = 1 := by rw [h3]; group

theorem inf_eq_bot {g h : Q} (hne : GLBConj g L ≠ GLBConj h L) :
    GLBConj g L ⊓ GLBConj h L = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  exact T.eq_one_of_central hz.1 fun w hw => (T.comm_of_ne hne w hw z hz.2).symm

theorem conj_le_K {g : Q} (hg : g ∈ B) : GLBConj g L ≤ t113K B L :=
  le_iSup₂_of_le g hg le_rfl

theorem L_le_K : L ≤ t113K B L := by
  have := T.conj_le_K (g := 1) B.one_mem
  rwa [gLBConj_one] at this

theorem K_le : t113K B L ≤ L ⊔ Subgroup.centralizer (L : Set Q) := by
  refine iSup₂_le fun g hg => ?_
  rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute T.comp (T.comp_conj g) with h | h
  · rw [← h]; exact le_sup_left
  · intro w hw
    exact Subgroup.mem_sup_right (Subgroup.mem_centralizer_iff.2 fun u hu => h u hu w hw)

theorem centralizes_K {z : Q} (hz : z ∈ B) (hc : ∀ l ∈ L, l * z = z * l) :
    ∀ k ∈ t113K B L, k * z = z * k := by
  have hle : t113K B L ≤ Subgroup.centralizer ({z} : Set Q) := by
    refine iSup₂_le fun g hg w hw => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hl : Commute z (g * w * g⁻¹) := (hc _ (mem_gLBConj.1 hw)).symm
    have hg' : Commute z g := T.comm_B hz hg
    have : Commute z (g⁻¹ * (g * w * g⁻¹) * g) := (hg'.inv_right.mul_right hl).mul_right hg'
    have e : g⁻¹ * (g * w * g⁻¹) * g = w := by group
    rw [e] at this
    exact this.eq.symm
  intro k hk
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hk)

theorem B0_le_B {b : Q} (hb : b ∈ t113B0 B L) : b ∈ B := hb.1

theorem B0_comm_K {b : Q} (hb : b ∈ t113B0 B L) : ∀ k ∈ t113K B L, k * b = b * k :=
  Subgroup.mem_centralizer_iff.1 hb.2

theorem B0_mem_A {b : Q} (hb : b ∈ t113B0 B L) : b ∈ t113A B L := by
  refine ⟨?_, hb.1⟩
  refine t113_mem_normalizer_of_commute fun j hj => ?_
  exact (T.B0_comm_K hb j (T.L_le_K hj)).symm

theorem rho_apply (a : ↥(t113A B L)) (l : ↥L) :
    ((t113Rho B L a l : ↥L) : Q) = (a : Q) * l * (a : Q)⁻¹ := rfl

theorem rho_eq_one_iff (a : ↥(t113A B L)) :
    t113Rho B L a = 1 ↔ (a : Q) ∈ t113B0 B L := by
  constructor
  · intro h
    have hc : ∀ l ∈ L, l * (a : Q) = (a : Q) * l := by
      intro l hl
      have := congrArg (fun f : MulAut ↥L => ((f ⟨l, hl⟩ : ↥L) : Q)) h
      have e : ((t113Rho B L a ⟨l, hl⟩ : ↥L) : Q) = (a : Q) * l * (a : Q)⁻¹ := rfl
      simp only [MulAut.one_apply] at this
      rw [e] at this
      calc l * (a : Q) = ((a : Q) * l * (a : Q)⁻¹) * (a : Q) := by rw [this]
        _ = (a : Q) * l := by group
    exact ⟨a.2.2, Subgroup.mem_centralizer_iff.2 (T.centralizes_K a.2.2 hc)⟩
  · intro h
    ext l
    rw [T.rho_apply, MulAut.one_apply]
    have := T.B0_comm_K h (l : Q) (T.L_le_K l.2)
    calc (a : Q) * (l : Q) * (a : Q)⁻¹ = ((l : Q) * a) * (a : Q)⁻¹ := by rw [this]
      _ = l := by group

theorem map_ker_rho : (t113Rho B L).ker.map (t113A B L).subtype = t113B0 B L := by
  ext z
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (T.rho_eq_one_iff a).1 ha
  · intro hz
    exact ⟨⟨z, T.B0_mem_A hz⟩, (T.rho_eq_one_iff _).2 hz, rfl⟩

theorem card_ker_rho : Nat.card (t113Rho B L).ker = Nat.card (t113B0 B L) := by
  rw [← T.map_ker_rho]
  exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm

theorem card_A : Nat.card B = 3 * Nat.card (t113A B L) := by
  have h := Subgroup.relIndex_mul_card (H := Subgroup.normalizer (L : Set Q)) (K := B)
  rw [T.index] at h
  exact h.symm

theorem card_B : Nat.card B = 3 * Nat.card (t113H B L) * Nat.card (t113B0 B L) := by
  have h := Subgroup.card_ker_mul_card_range (t113Rho B L)
  rw [T.card_ker_rho] at h
  rw [T.card_A, ← h]
  unfold t113H
  ring

theorem H_elem : IsElemAbelian 3 (t113H B L) := by
  refine ⟨⟨⟨fun α β => ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha⟩ := α.2
    obtain ⟨b, hb⟩ := β.2
    apply Subtype.ext
    show (α : MulAut ↥L) * β = β * α
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact T.comm_B a.2.2 b.2.2
  · intro α hα
    obtain ⟨a, rfl⟩ := hα
    rw [← map_pow]
    have : a ^ 3 = 1 := by
      apply Subtype.ext
      exact T.elem.2 _ a.2.2
    rw [this, map_one]

theorem rho_inner_of_mem_K {k : Q} (hk : k ∈ t113K B L) (hA : k ∈ t113A B L) :
    t113Rho B L ⟨k, hA⟩ ∈ innerAut113 L := by
  obtain ⟨l, hl, c, hc, rfl⟩ :=
    t113_mem_sup (fun p hp r hr => Subgroup.mem_centralizer_iff.1 hr p hp) (T.K_le hk)
  refine ⟨⟨l, hl⟩, ?_⟩
  ext m
  rw [T.rho_apply]
  have h1 : c * (m : Q) = (m : Q) * c := (Subgroup.mem_centralizer_iff.1 hc m m.2).symm
  show l * (m : Q) * l⁻¹ = l * c * (m : Q) * (l * c)⁻¹
  calc l * (m : Q) * l⁻¹ = l * (c * m * c⁻¹) * l⁻¹ := by rw [h1]; group
    _ = l * c * (m : Q) * (l * c)⁻¹ := by group

theorem comm01 : ∀ u ∈ L, ∀ w ∈ GLBConj x L, u * w = w * u := by
  have := T.comm_of_ne (g := 1) (h := x) (by rw [gLBConj_one]; exact T.conj1_ne.symm)
  simpa only [gLBConj_one] using this

theorem comm02 : ∀ u ∈ L, ∀ w ∈ GLBConj (x ^ 2) L, u * w = w * u := by
  have := T.comm_of_ne (g := 1) (h := x ^ 2) (by rw [gLBConj_one]; exact T.conj2_ne.symm)
  simpa only [gLBConj_one] using this

theorem comm12 : ∀ u ∈ GLBConj x L, ∀ w ∈ GLBConj (x ^ 2) L, u * w = w * u :=
  T.comm_of_ne (g := x) (h := x ^ 2) T.conj21_ne.symm

theorem inf01 : L ⊓ GLBConj x L = ⊥ := by
  have := T.inf_eq_bot (g := 1) (h := x) (by rw [gLBConj_one]; exact T.conj1_ne.symm)
  simpa only [gLBConj_one] using this

theorem inf02 : L ⊓ GLBConj (x ^ 2) L = ⊥ := by
  have := T.inf_eq_bot (g := 1) (h := x ^ 2) (by rw [gLBConj_one]; exact T.conj2_ne.symm)
  simpa only [gLBConj_one] using this

theorem inf12 : GLBConj x L ⊓ GLBConj (x ^ 2) L = ⊥ :=
  T.inf_eq_bot (g := x) (h := x ^ 2) T.conj21_ne.symm

theorem eq_one_of_central0 {z : Q} (hz : z ∈ L) (hc : ∀ w ∈ L, z * w = w * z) : z = 1 := by
  refine T.eq_one_of_central (g := 1) ?_ ?_ <;> simpa only [gLBConj_one] using ‹_›

theorem conj1_mem {y : Q} (hy : y ∈ L) : x⁻¹ * y * x ∈ GLBConj x L := by
  rw [mem_gLBConj]
  simpa [mul_assoc] using hy

theorem conj2_mem {y : Q} (hy : y ∈ L) : (x ^ 2)⁻¹ * y * x ^ 2 ∈ GLBConj (x ^ 2) L := by
  rw [mem_gLBConj]
  simpa [mul_assoc] using hy

theorem commute_conj {g f y : Q} (hg : g ∈ B) (hf : f ∈ B) (hfy : f * y = y * f) :
    f * (g⁻¹ * y * g) = (g⁻¹ * y * g) * f := by
  have hc : Commute f g := T.comm_B hf hg
  have : Commute f (g⁻¹ * y * g) := (hc.inv_right.mul_right hfy).mul_right hc
  exact this.eq

theorem sup01_comm2 {P0 P1 P2 : Subgroup Q} (h0 : P0 ≤ L) (h1 : P1 ≤ GLBConj x L)
    (h2 : P2 ≤ GLBConj (x ^ 2) L) : ∀ p ∈ P0 ⊔ P1, ∀ r ∈ P2, p * r = r * p := by
  intro p hp r hr
  have hle : P0 ⊔ P1 ≤ Subgroup.centralizer ({r} : Set Q) := by
    refine sup_le (fun u hu => ?_) (fun u hu => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact T.comm02 u (h0 hu) r (h2 hr)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact T.comm12 u (h1 hu) r (h2 hr)
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hp)

theorem sup01_comm_L2 {P0 P1 : Subgroup Q} (h0 : P0 ≤ L) (h1 : P1 ≤ GLBConj x L) :
    ∀ p ∈ P0 ⊔ P1, ∀ r ∈ GLBConj (x ^ 2) L, p * r = r * p :=
  fun p hp r hr => T.sup01_comm2 h0 h1 le_rfl p hp r hr

theorem mem_join {P0 P1 P2 : Subgroup Q} (h0 : P0 ≤ L) (h1 : P1 ≤ GLBConj x L)
    (h2 : P2 ≤ GLBConj (x ^ 2) L) {z : Q} (hz : z ∈ P0 ⊔ P1 ⊔ P2) :
    ∃ u ∈ P0, ∃ v ∈ P1, ∃ w ∈ P2, u * v * w = z := by
  obtain ⟨q, hq, w, hw, rfl⟩ := t113_mem_sup (T.sup01_comm2 h0 h1 h2) hz
  obtain ⟨u, hu, v, hv, rfl⟩ := t113_mem_sup
    (fun p hp r hr => T.comm01 p (h0 hp) r (h1 hr)) hq
  exact ⟨u, hu, v, hv, w, hw, rfl⟩

theorem join_eq_one {P0 P1 P2 : Subgroup Q} (h0 : P0 ≤ L) (h1 : P1 ≤ GLBConj x L)
    (h2 : P2 ≤ GLBConj (x ^ 2) L) {z : Q} (hz : z ∈ P0 ⊔ P1 ⊔ P2)
    (c0 : ∀ m ∈ L, z * m = m * z) (c1 : ∀ m ∈ GLBConj x L, z * m = m * z)
    (c2 : ∀ m ∈ GLBConj (x ^ 2) L, z * m = m * z) : z = 1 := by
  obtain ⟨u, hu, v, hv, w, hw, rfl⟩ := T.mem_join h0 h1 h2 hz
  have hu1 : u = 1 := by
    refine T.eq_one_of_central0 (h0 hu) fun m hm => ?_
    have a1 : Commute (u * v * w) m := c0 m hm
    have a2 : Commute v m := (T.comm01 m hm v (h1 hv)).symm
    have a3 : Commute w m := (T.comm02 m hm w (h2 hw)).symm
    have : Commute (u * v * w * w⁻¹ * v⁻¹) m := ((a1.mul_left a3.inv_left).mul_left a2.inv_left)
    have e : u * v * w * w⁻¹ * v⁻¹ = u := by group
    rw [e] at this
    exact this.eq
  subst hu1
  have hv1 : v = 1 := by
    refine T.eq_one_of_central (g := x) (h1 hv) fun m hm => ?_
    have a1 : Commute (1 * v * w) m := c1 m hm
    have a3 : Commute w m := (T.comm12 m hm w (h2 hw)).symm
    have : Commute (1 * v * w * w⁻¹) m := a1.mul_left a3.inv_left
    have e : 1 * v * w * w⁻¹ = v := by group
    rw [e] at this
    exact this.eq
  subst hv1
  have hw1 : w = 1 := by
    refine T.eq_one_of_central (g := x ^ 2) (h2 hw) fun m hm => ?_
    simpa using c2 m hm
  subst hw1
  simp

theorem join_elem {P0 P1 P2 : Subgroup Q} (h0 : P0 ≤ L) (h1 : P1 ≤ GLBConj x L)
    (h2 : P2 ≤ GLBConj (x ^ 2) L) (e0 : IsElemAbelian 3 P0) (e1 : IsElemAbelian 3 P1)
    (e2 : IsElemAbelian 3 P2) :
    IsElemAbelian 3 (P0 ⊔ P1 ⊔ P2) ∧
      Nat.card ↥(P0 ⊔ P1 ⊔ P2) = Nat.card P0 * Nat.card P1 * Nat.card P2 := by
  have hi01 : P0 ⊓ P1 = ⊥ := by
    rw [eq_bot_iff, ← T.inf01]; exact inf_le_inf h0 h1
  obtain ⟨f01, c01⟩ := t113_sup_elemAbelian e0 e1 (fun p hp r hr => T.comm01 p (h0 hp) r (h1 hr)) hi01
  have hi2 : (P0 ⊔ P1) ⊓ P2 = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    refine T.join_eq_one h0 h1 h2 (Subgroup.mem_sup_left hz.1) ?_ ?_ ?_
    · exact fun m hm => (T.comm02 m hm z (h2 hz.2)).symm
    · exact fun m hm => (T.comm12 m hm z (h2 hz.2)).symm
    · exact fun m hm => T.sup01_comm_L2 h0 h1 z hz.1 m hm
  obtain ⟨f, c⟩ := t113_sup_elemAbelian f01 e2 (T.sup01_comm2 h0 h1 h2) hi2
  exact ⟨f, by rw [c, c01]⟩

theorem join_inf_B0 {P0 P1 P2 : Subgroup Q} (h0 : P0 ≤ L) (h1 : P1 ≤ GLBConj x L)
    (h2 : P2 ≤ GLBConj (x ^ 2) L) {z : Q} (hz : z ∈ P0 ⊔ P1 ⊔ P2) (hb : z ∈ t113B0 B L) :
    z = 1 := by
  refine T.join_eq_one h0 h1 h2 hz ?_ ?_ ?_
  · exact fun m hm => (T.B0_comm_K hb m (T.L_le_K hm)).symm
  · exact fun m hm => (T.B0_comm_K hb m (T.conj_le_K T.mem hm)).symm
  · exact fun m hm => (T.B0_comm_K hb m (T.conj_le_K (B.pow_mem T.mem 2) hm)).symm

end Triple113

@[expose] def t113Y (x y : Q) : Subgroup Q :=
  Subgroup.zpowers y ⊔ Subgroup.zpowers (x⁻¹ * y * x) ⊔ Subgroup.zpowers ((x ^ 2)⁻¹ * y * x ^ 2)

@[expose] def t113Y12 (x y : Q) : Subgroup Q :=
  Subgroup.zpowers (x⁻¹ * y * x) ⊔ Subgroup.zpowers ((x ^ 2)⁻¹ * y * x ^ 2)

namespace Triple113

variable {B L : Subgroup Q} {x : Q} (T : Triple113 B L x)

include T

theorem Y_spec {y : Q} (hy : y ∈ L) (ho : orderOf y = 3) :
    IsElemAbelian 3 (t113Y x y) ∧ Nat.card (t113Y x y) = 27 ∧ t113Y x y ≤ t113K B L ∧
      (∀ z ∈ t113Y x y, z ∈ t113B0 B L → z = 1) := by
  have m1 := T.conj1_mem hy
  have m2 := T.conj2_mem hy
  have o1 : orderOf (x⁻¹ * y * x) = 3 := by rw [t113_orderOf_conj, ho]
  have o2 : orderOf ((x ^ 2)⁻¹ * y * x ^ 2) = 3 := by rw [t113_orderOf_conj, ho]
  have h0 : Subgroup.zpowers y ≤ L := Subgroup.zpowers_le.2 hy
  have h1 : Subgroup.zpowers (x⁻¹ * y * x) ≤ GLBConj x L := Subgroup.zpowers_le.2 m1
  have h2 : Subgroup.zpowers ((x ^ 2)⁻¹ * y * x ^ 2) ≤ GLBConj (x ^ 2) L :=
    Subgroup.zpowers_le.2 m2
  obtain ⟨e0, c0⟩ := t113_zpowers_elem ho
  obtain ⟨e1, c1⟩ := t113_zpowers_elem o1
  obtain ⟨e2, c2⟩ := t113_zpowers_elem o2
  obtain ⟨hel, hcard⟩ := T.join_elem h0 h1 h2 e0 e1 e2
  refine ⟨hel, by unfold t113Y; rw [hcard, c0, c1, c2], ?_, fun z hz hb => T.join_inf_B0 h0 h1 h2 hz hb⟩
  exact sup_le (sup_le (h0.trans T.L_le_K) (h1.trans (T.conj_le_K T.mem)))
    (h2.trans (T.conj_le_K (B.pow_mem T.mem 2)))

theorem Y12_spec {y : Q} (hy : y ∈ L) (ho : orderOf y = 3) :
    IsElemAbelian 3 (t113Y12 x y) ∧ Nat.card (t113Y12 x y) = 9 ∧ t113Y12 x y ≤ t113K B L ∧
      (∀ z ∈ t113Y12 x y, z ∈ t113B0 B L → z = 1) := by
  have m1 := T.conj1_mem hy
  have m2 := T.conj2_mem hy
  have o1 : orderOf (x⁻¹ * y * x) = 3 := by rw [t113_orderOf_conj, ho]
  have o2 : orderOf ((x ^ 2)⁻¹ * y * x ^ 2) = 3 := by rw [t113_orderOf_conj, ho]
  have h1 : Subgroup.zpowers (x⁻¹ * y * x) ≤ GLBConj x L := Subgroup.zpowers_le.2 m1
  have h2 : Subgroup.zpowers ((x ^ 2)⁻¹ * y * x ^ 2) ≤ GLBConj (x ^ 2) L :=
    Subgroup.zpowers_le.2 m2
  obtain ⟨e1, c1⟩ := t113_zpowers_elem o1
  obtain ⟨e2, c2⟩ := t113_zpowers_elem o2
  obtain ⟨eb, cb⟩ := t113_bot_elem (Q := Q)
  obtain ⟨hel, hcard⟩ := T.join_elem (bot_le : (⊥ : Subgroup Q) ≤ L) h1 h2 eb e1 e2
  have hb : (⊥ : Subgroup Q) ⊔ t113Y12 x y = t113Y12 x y := bot_sup_eq _
  have hb' : (⊥ : Subgroup Q) ⊔ Subgroup.zpowers (x⁻¹ * y * x) ⊔
      Subgroup.zpowers ((x ^ 2)⁻¹ * y * x ^ 2) = t113Y12 x y := by
    rw [sup_assoc]; exact hb
  rw [hb'] at hel hcard
  refine ⟨hel, by rw [hcard, cb, c1, c2], ?_, fun z hz hz0 => ?_⟩
  · exact sup_le (h1.trans (T.conj_le_K T.mem)) (h2.trans (T.conj_le_K (B.pow_mem T.mem 2)))
  · refine T.join_inf_B0 (bot_le : (⊥ : Subgroup Q) ≤ L) h1 h2 ?_ hz0
    rw [← hb'] at hz
    exact hz

theorem Y_comm {y f : Q} (hf : f ∈ B) (hfy : f * y = y * f) :
    ∀ z ∈ t113Y x y, f * z = z * f := by
  have hle : t113Y x y ≤ Subgroup.centralizer ({f} : Set Q) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · refine Subgroup.zpowers_le.2 ?_
      rw [Subgroup.mem_centralizer_singleton_iff]; exact hfy.symm
    · refine Subgroup.zpowers_le.2 ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (T.commute_conj T.mem hf hfy).symm
    · refine Subgroup.zpowers_le.2 ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (T.commute_conj (B.pow_mem T.mem 2) hf hfy).symm
  intro z hz
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hz)).symm

theorem Y12_comm {y f : Q} (hf : f ∈ B) (hfy : f * y = y * f) :
    ∀ z ∈ t113Y12 x y, f * z = z * f := by
  have hle : t113Y12 x y ≤ Subgroup.centralizer ({f} : Set Q) := by
    refine sup_le ?_ ?_
    · refine Subgroup.zpowers_le.2 ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (T.commute_conj T.mem hf hfy).symm
    · refine Subgroup.zpowers_le.2 ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (T.commute_conj (B.pow_mem T.mem 2) hf hfy).symm
  intro z hz
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hz)).symm

theorem B0_elem : IsElemAbelian 3 (t113B0 B L) :=
  t113_elemAbelian_of_le T.elem inf_le_left

theorem rho_zpow (a : ↥(t113A B L)) (n : ℤ) :
    t113Rho B L (a ^ n) = t113Rho B L a ^ n := map_zpow _ _ _

theorem pow_eq_one_of_inner {a : Q} (ha : a ∈ t113A B L)
    (hout : t113Rho B L ⟨a, ha⟩ ∉ innerAut113 L) (n : ℤ)
    (hn : t113Rho B L ⟨a, ha⟩ ^ n ∈ innerAut113 L) : a ^ n = 1 := by
  have ha3 : a ^ 3 = 1 := T.elem.2 a ha.2
  have hα3 : t113Rho B L ⟨a, ha⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨a, ha⟩ : ↥(t113A B L)) ^ 3 = 1 := Subtype.ext ha3
    rw [this, map_one]
  have e1 := zpow_eq_zpow_emod' (x := a) n ha3
  have e2 := zpow_eq_zpow_emod' (x := t113Rho B L ⟨a, ha⟩) n hα3
  have hr : n % (3 : ℕ) = 0 ∨ n % (3 : ℕ) = 1 ∨ n % (3 : ℕ) = 2 := by omega
  rcases hr with h | h | h
  · rw [e1, h]; simp
  · rw [e2, h] at hn
    exact absurd (by simpa using hn) hout
  · rw [e2, h] at hn
    refine absurd ?_ hout
    have h2 : t113Rho B L ⟨a, ha⟩ = (t113Rho B L ⟨a, ha⟩ ^ (2 : ℤ)) ^ (2 : ℤ) := by
      rw [← zpow_mul]
      have : t113Rho B L ⟨a, ha⟩ ^ (4 : ℤ) = t113Rho B L ⟨a, ha⟩ := by
        have := hα3
        rw [show (4 : ℤ) = ((3 : ℕ) : ℤ) + 1 by norm_num, zpow_add, zpow_natCast, hα3]; simp
      simpa using this.symm
    rw [h2]
    exact (innerAut113 L).zpow_mem hn _

theorem F_spec {a : Q} (ha : a ∈ t113A B L) (hout : t113Rho B L ⟨a, ha⟩ ∉ innerAut113 L) :
    IsElemAbelian 3 (Subgroup.zpowers a ⊔ t113B0 B L) ∧
      Nat.card ↥(Subgroup.zpowers a ⊔ t113B0 B L) = 3 * Nat.card (t113B0 B L) ∧
      Subgroup.zpowers a ⊔ t113B0 B L ≤ B ∧
      ∀ Y : Subgroup Q, Y ≤ t113K B L → (∀ z ∈ Y, z ∈ t113B0 B L → z = 1) →
        ∀ z ∈ Subgroup.zpowers a ⊔ t113B0 B L, z ∈ Y → z = 1 := by
  have hcomm : ∀ p ∈ Subgroup.zpowers a, ∀ r ∈ t113B0 B L, p * r = r * p := by
    rintro p ⟨n, rfl⟩ r hr
    have hc : Commute a r := T.comm_B ha.2 hr.1
    exact (hc.zpow_left n).eq
  have hα1 : t113Rho B L ⟨a, ha⟩ ≠ 1 := fun h => hout (h ▸ (innerAut113 L).one_mem)
  have ha1 : a ≠ 1 := fun h => hα1 (by
    have : (⟨a, ha⟩ : ↥(t113A B L)) = 1 := Subtype.ext h
    rw [this, map_one])
  have ho : orderOf a = 3 := orderOf_eq_prime (T.elem.2 a ha.2) ha1
  obtain ⟨ez, cz⟩ := t113_zpowers_elem ho
  have hi : Subgroup.zpowers a ⊓ t113B0 B L = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨⟨n, rfl⟩, hz⟩
    rw [Subgroup.mem_bot]
    refine T.pow_eq_one_of_inner ha hout n ?_
    have hzA : a ^ n ∈ t113A B L := (t113A B L).zpow_mem ha n
    have : t113Rho B L ⟨a ^ n, hzA⟩ = 1 := (T.rho_eq_one_iff _).2 hz
    have e : (⟨a ^ n, hzA⟩ : ↥(t113A B L)) = (⟨a, ha⟩ : ↥(t113A B L)) ^ n := Subtype.ext (by simp)
    rw [e, T.rho_zpow] at this
    rw [this]; exact (innerAut113 L).one_mem
  obtain ⟨hel, hcard⟩ := t113_sup_elemAbelian ez T.B0_elem hcomm hi
  refine ⟨hel, by rw [hcard, cz], ?_, ?_⟩
  · exact sup_le (Subgroup.zpowers_le.2 ha.2) inf_le_left
  · intro Y hYK hY z hz hzY
    obtain ⟨p, ⟨n, rfl⟩, r, hr, rfl⟩ := t113_mem_sup hcomm hz
    beta_reduce at hz hzY
    have hzA : a ^ n * r ∈ t113A B L :=
      (t113A B L).mul_mem ((t113A B L).zpow_mem ha n) (T.B0_mem_A hr)
    have hin := T.rho_inner_of_mem_K (hYK hzY) hzA
    have e : (⟨a ^ n * r, hzA⟩ : ↥(t113A B L)) =
        (⟨a, ha⟩ : ↥(t113A B L)) ^ n * ⟨r, T.B0_mem_A hr⟩ := Subtype.ext (by simp)
    have h1 : t113Rho B L ⟨r, T.B0_mem_A hr⟩ = 1 := (T.rho_eq_one_iff _).2 hr
    rw [e, map_mul, T.rho_zpow, h1, mul_one] at hin
    have h2 := T.pow_eq_one_of_inner ha hout n hin
    rw [h2, one_mul] at hzY
    show a ^ n * r = 1
    rw [h2, one_mul]
    exact hY r hzY hr

end Triple113

end Triple

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
