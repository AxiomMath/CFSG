module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDPrelim

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def actTriv (C N : Subgroup G) : Subgroup G where
  carrier := {y | y ∈ normalizer (C : Set G) ∧ y ∈ normalizer (N : Set G) ∧
    ∀ c ∈ C, y * c * y⁻¹ * c⁻¹ ∈ N}
  one_mem' := ⟨one_mem _, one_mem _, fun c _ => by simp⟩
  mul_mem' := by
    rintro y z ⟨hyC, hyN, hy⟩ ⟨hzC, hzN, hz⟩
    refine ⟨mul_mem hyC hzC, mul_mem hyN hzN, fun c hc => ?_⟩
    have h1 := hy c hc
    have h2 : y * (z * c * z⁻¹ * c⁻¹) * y⁻¹ ∈ N := (mem_normalizer_iff.mp hyN _).mp (hz c hc)
    have e : y * z * c * (y * z)⁻¹ * c⁻¹ =
        y * (z * c * z⁻¹ * c⁻¹) * y⁻¹ * (y * c * y⁻¹ * c⁻¹) := by group
    rw [e]
    exact mul_mem h2 h1
  inv_mem' := by
    rintro y ⟨hyC, hyN, hy⟩
    refine ⟨inv_mem hyC, inv_mem hyN, fun c hc => ?_⟩
    have hc' : y⁻¹ * c * y ∈ C := (mem_normalizer_iff''.mp hyC c).mp hc
    have h1 := hy _ hc'
    have e1 : y * (y⁻¹ * c * y) * y⁻¹ * (y⁻¹ * c * y)⁻¹ = c * (y⁻¹ * c * y)⁻¹ := by group
    rw [e1] at h1
    have e2 : y⁻¹ * c * y⁻¹⁻¹ * c⁻¹ = (y⁻¹ * c * y) * c⁻¹ := by group
    rw [e2]
    have := inv_mem h1
    rwa [show (c * (y⁻¹ * c * y)⁻¹)⁻¹ = (y⁻¹ * c * y) * c⁻¹ by group] at this

theorem conj_mem_actTriv {C N : Subgroup G} {u y : G} (huC : u ∈ normalizer (C : Set G))
    (huN : u ∈ normalizer (N : Set G)) (hy : y ∈ actTriv C N) : u * y * u⁻¹ ∈ actTriv C N := by
  obtain ⟨hyC, hyN, hy⟩ := hy
  refine ⟨mul_mem (mul_mem huC hyC) (inv_mem huC), mul_mem (mul_mem huN hyN) (inv_mem huN),
    fun c hc => ?_⟩
  have hc' : u⁻¹ * c * u ∈ C := (mem_normalizer_iff''.mp huC c).mp hc
  have h1 : u * (y * (u⁻¹ * c * u) * y⁻¹ * (u⁻¹ * c * u)⁻¹) * u⁻¹ ∈ N :=
    (mem_normalizer_iff.mp huN _).mp (hy _ hc')
  have e : u * y * u⁻¹ * c * (u * y * u⁻¹)⁻¹ * c⁻¹ =
      u * (y * (u⁻¹ * c * u) * y⁻¹ * (u⁻¹ * c * u)⁻¹) * u⁻¹ := by group
  rw [e]
  exact h1

theorem commutator_mem_actTriv {C N : Subgroup G} {u k : G} (huC : u ∈ normalizer (C : Set G))
    (huN : u ∈ normalizer (N : Set G)) (hk : k ∈ actTriv C N) : ⁅u, k⁆ ∈ actTriv C N := by
  rw [commutatorElement_def]
  exact mul_mem (conj_mem_actTriv huC huN hk) (inv_mem hk)

theorem conj_mem_centralizer {B : Subgroup G} {x n : G} (hx : x ∈ normalizer (B : Set G))
    (hn : n ∈ centralizer (B : Set G)) : x * n * x⁻¹ ∈ centralizer (B : Set G) := by
  rw [mem_centralizer_iff]
  intro b hb
  have hb' : x⁻¹ * b * x ∈ B := (mem_normalizer_iff''.mp hx b).mp hb
  have hc := mem_centralizer_iff.mp hn _ hb'
  calc b * (x * n * x⁻¹) = x * ((x⁻¹ * b * x) * n) * x⁻¹ := by group
    _ = x * (n * (x⁻¹ * b * x)) * x⁻¹ := by rw [hc]
    _ = x * n * x⁻¹ * b := by group

theorem mem_normalizer_zpowers {t x : G} (hx : x * t = t * x) :
    x ∈ normalizer ((zpowers t : Subgroup G) : Set G) := by
  refine centralizer_le_normalizer _ ?_
  rw [mem_centralizer_iff]
  intro g hg
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
  exact ((Commute.zpow_left (show Commute t x from hx.symm) k))

namespace Hyp

variable {d : Data G} (h : Hyp d)
include h

theorem A₄_le_L : d.A₄ ≤ d.L := h.A₄_le_A₃.trans h.A₃_le_L

theorem A₄_sq {a : G} (ha : a ∈ d.A₄) : a * a = 1 := h.A₂_sq a (h.A₄_le_A₂ ha)

theorem A₄_comm {a b : G} (ha : a ∈ d.A₄) (hb : b ∈ d.A₄) : a * b = b * a :=
  h.A₂_comm a (h.A₄_le_A₂ ha) b (h.A₄_le_A₂ hb)

theorem withT_A₃_le : d.withT d.A₃ ≤ centralizer (d.A₄ : Set G) ⊓ d.H := by
  refine le_inf (sup_le h.A₃_le_cent_A₄ ?_) (h.withT_le_H h.A₃_le_L)
  rw [zpowers_le, mem_centralizer_iff]
  intro a ha
  exact h.comm_of_mem_L (h.A₄_le_L ha)

omit h in
theorem mem_cent_withT_A₄ {n : G} (hn : n ∈ centralizer (d.A₄ : Set G) ⊓ d.H) :
    n ∈ centralizer ((d.withT d.A₄ : Subgroup G) : Set G) := by
  refine mem_centralizer_sup hn.1 ?_
  rw [mem_centralizer_iff]
  intro g hg
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
  have hnt : n * d.t = d.t * n := mem_centralizer_singleton_iff.mp hn.2
  exact Commute.zpow_left (show Commute d.t n from hnt.symm) k

omit h in
theorem mem_CA₄_of_cent {n : G} (hn : n ∈ centralizer ((d.withT d.A₄ : Subgroup G) : Set G)) :
    n ∈ centralizer (d.A₄ : Set G) ⊓ d.H := by
  refine ⟨mem_centralizer_iff.mpr fun a ha => mem_centralizer_iff.mp hn a (le_withT _ ha), ?_⟩
  exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hn d.t (t_mem_withT _)).symm

omit h in
theorem CA₄_le_X₄ : centralizer (d.A₄ : Set G) ⊓ d.H ≤
    normalizer ((d.withT d.A₄ : Subgroup G) : Set G) :=
  fun _ hn => centralizer_le_normalizer _ (mem_cent_withT_A₄ hn)

omit h in
theorem conj_mem_CA₄ {x n : G} (hx : x ∈ normalizer ((d.withT d.A₄ : Subgroup G) : Set G))
    (hn : n ∈ centralizer (d.A₄ : Set G) ⊓ d.H) :
    x * n * x⁻¹ ∈ centralizer (d.A₄ : Set G) ⊓ d.H :=
  mem_CA₄_of_cent (conj_mem_centralizer hx (mem_cent_withT_A₄ hn))

omit h in
theorem X₄_le_normalizer_CA₄ [Finite G] : normalizer ((d.withT d.A₄ : Subgroup G) : Set G) ≤
    normalizer ((centralizer (d.A₄ : Set G) ⊓ d.H : Subgroup G) : Set G) :=
  fun _ hx => mem_normalizer_of_conj_mem fun _ hn => conj_mem_CA₄ hx hn

theorem CA₄_le_normalizer_T₃ [Finite G] : centralizer (d.A₄ : Set G) ⊓ d.H ≤
    normalizer ((d.withT d.A₃ : Subgroup G) : Set G) := fun _ hn =>
  mem_normalizer_sup (h.centA₄_le hn)
    (mem_normalizer_zpowers (mem_centralizer_singleton_iff.mp hn.2))

theorem isPGroup_T₃ : IsPGroup 2 (d.withT d.A₃) :=
  h.isPGroup_withT h.A₃_le_L (IsPGroup.of_card h.card_A₃)

theorem X₄_le_normalizer_T₃ [Finite G] : normalizer ((d.withT d.A₄ : Subgroup G) : Set G) ≤
    normalizer ((d.withT d.A₃ : Subgroup G) : Set G) := by
  intro x hx
  set P := (d.withT d.A₃).map (MulAut.conj x⁻¹).toMonoidHom with hP
  have hPC : P ≤ centralizer (d.A₄ : Set G) ⊓ d.H := by
    rintro _ ⟨b, hb, rfl⟩
    have := conj_mem_CA₄ (inv_mem hx) (h.withT_A₃_le hb)
    simpa using this
  have hCP : centralizer (d.A₄ : Set G) ⊓ d.H ≤ normalizer (P : Set G) := by
    intro n hn
    apply mem_normalizer_of_conj_mem
    rintro _ ⟨b, hb, rfl⟩
    have hn' := conj_mem_CA₄ hx hn
    have hb' : (x * n * x⁻¹) * b * (x * n * x⁻¹)⁻¹ ∈ d.withT d.A₃ :=
      (mem_normalizer_iff.mp (h.CA₄_le_normalizer_T₃ hn') b).mp hb
    refine ⟨_, hb', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hP2 : IsPGroup 2 P := h.isPGroup_T₃.map _
  have hle := h.oTwo_CA₄ P hPC hCP hP2
  have hx' : x⁻¹ ∈ normalizer ((d.withT d.A₃ : Subgroup G) : Set G) :=
    mem_normalizer_of_conj_mem fun b hb => hle ⟨b, hb, rfl⟩
  simpa using inv_mem hx'

end Hyp

namespace Hyp

variable {d : Data G} (h : Hyp d)
include h

theorem crossed_X₄ [Finite G] {x : G} (hx : x ∈ normalizer ((d.withT d.A₄ : Subgroup G) : Set G)) :
    x⁻¹ * d.t * x * d.t ∈ d.A₄ :=
  h.crossed_mem_of_normalizer h.A₄_le_A₂ hx

theorem exists_conj_U [Finite G] {a : G} (ha : a ∈ d.A₄) :
    ∃ c ∈ normalizer ((d.withT d.A₄ : Subgroup G) : Set G) ⊓ centralizer (d.A₄ : Set G),
      c⁻¹ * d.t * c = a * d.t := by
  obtain ⟨c, hc, hct⟩ := h.C₂_conj a (h.A₄_le_A₂ ha)
  have hcA : c ∈ centralizer (d.A₄ : Set G) := centralizer_le h.A₄_le_A₂ (h.C₂_le_cent hc)
  refine ⟨c, ⟨?_, hcA⟩, hct⟩
  have hle : d.withT d.A₄ ≤ (d.withT d.A₄).comap (MulAut.conj c⁻¹).toMonoidHom := by
    refine sup_le (fun b hb => ?_) ?_
    · change c⁻¹ * b * c⁻¹⁻¹ ∈ d.withT d.A₄
      have hbc := mem_centralizer_iff.mp hcA b hb
      rw [inv_inv, mul_assoc, hbc, ← mul_assoc, inv_mul_cancel, one_mul]
      exact le_withT _ hb
    · rw [zpowers_le]
      change c⁻¹ * d.t * c⁻¹⁻¹ ∈ d.withT d.A₄
      rw [inv_inv, hct]
      exact mul_mem (le_withT _ ha) (t_mem_withT _)
  have hc' : c⁻¹ ∈ normalizer ((d.withT d.A₄ : Subgroup G) : Set G) :=
    mem_normalizer_of_conj_mem fun b hb => hle hb
  simpa using inv_mem hc'

theorem X₄_le_normalizer_A₄ [Finite G] : normalizer ((d.withT d.A₄ : Subgroup G) : Set G) ≤
    normalizer (d.A₄ : Set G) := by
  intro x hx
  apply mem_normalizer_of_conj_mem
  intro a ha
  have h1 : x * a * x⁻¹ ∈ d.withT d.A₄ := (mem_normalizer_iff.mp hx a).mp (le_withT _ ha)
  rcases (h.mem_withT_iff h.A₄_le_L).mp h1 with h2 | h2
  · exact h2
  · exfalso
    obtain ⟨c, -, hct⟩ := h.exists_conj_U h2
    apply h.not_conj_mem_A₂ (c * x)
    have : (c * x)⁻¹ * d.t * (c * x) = a := by
      calc (c * x)⁻¹ * d.t * (c * x) = x⁻¹ * (c⁻¹ * d.t * c) * x := by group
        _ = x⁻¹ * (x * a * x⁻¹ * d.t * d.t) * x := by rw [hct]
        _ = a := by rw [mul_assoc (x * a * x⁻¹), h.t_sq]; group
    rw [this]
    exact h.A₄_le_A₂ ha

theorem Λ_le_X₄ [Finite G] : d.Λ ≤ normalizer ((d.withT d.A₄ : Subgroup G) : Set G) :=
  fun _ hl => mem_normalizer_sup (h.Λ_le_normalizer hl)
    (mem_normalizer_zpowers (h.comm_of_mem_L (h.Λ_le_L hl)))

end Hyp

namespace Data

variable (d : Data G)

abbrev X₄ : Subgroup G := normalizer ((d.withT d.A₄ : Subgroup G) : Set G)

abbrev CA₄ : Subgroup G := centralizer (d.A₄ : Set G) ⊓ d.H

abbrev U₄ : Subgroup G := d.X₄ ⊓ centralizer (d.A₄ : Set G)

abbrev Q₄ : Subgroup G := d.U₄ ⊓ actTriv d.CA₄ (d.withT d.A₃)

end Data

namespace Hyp

variable {d : Data G} (h : Hyp d)
include h

theorem crossed_U₄_mul [Finite G] {x y : G} (hx : x ∈ d.U₄) (hy : y ∈ d.U₄) :
    (x * y)⁻¹ * d.t * (x * y) * d.t = (x⁻¹ * d.t * x * d.t) * (y⁻¹ * d.t * y * d.t) :=
  crossed_mul h.t_sq (mem_centralizer_iff.mp hy.2 _ (h.crossed_X₄ hx.1))

theorem crossed_U₄_inv [Finite G] {x : G} (hx : x ∈ d.U₄) :
    x⁻¹⁻¹ * d.t * x⁻¹ * d.t = (x⁻¹ * d.t * x * d.t)⁻¹ :=
  crossed_inv h.t_sq (mem_centralizer_iff.mp hx.2 _ (h.crossed_X₄ hx.1))

theorem T₃_le_X₄ [Finite G] : d.withT d.A₃ ≤ d.X₄ := h.withT_A₃_le.trans CA₄_le_X₄

theorem T₃_le_U₄ [Finite G] : d.withT d.A₃ ≤ d.U₄ :=
  le_inf h.T₃_le_X₄ (fun _ hx => (h.withT_A₃_le hx).1)

theorem T₃_le_actTriv [Finite G] : d.withT d.A₃ ≤ actTriv d.CA₄ (d.withT d.A₃) := by
  intro x hx
  have hxC := h.withT_A₃_le hx
  refine ⟨Subgroup.le_normalizer hxC, Subgroup.le_normalizer hx, fun c hc => ?_⟩
  have hc' : c * x⁻¹ * c⁻¹ ∈ d.withT d.A₃ :=
    (mem_normalizer_iff.mp (h.CA₄_le_normalizer_T₃ hc) _).mp (inv_mem hx)
  rw [show x * c * x⁻¹ * c⁻¹ = x * (c * x⁻¹ * c⁻¹) by group]
  exact mul_mem hx hc'

theorem X₄_le_normalizer_actTriv [Finite G] {x : G} (hx : x ∈ d.X₄) :
    x ∈ normalizer ((actTriv d.CA₄ (d.withT d.A₃) : Subgroup G) : Set G) :=
  mem_normalizer_of_conj_mem fun _ hy =>
    conj_mem_actTriv (X₄_le_normalizer_CA₄ hx) (h.X₄_le_normalizer_T₃ hx) hy

theorem X₄_le_normalizer_U₄ [Finite G] {x : G} (hx : x ∈ d.X₄) :
    x ∈ normalizer ((d.U₄ : Subgroup G) : Set G) :=
  mem_normalizer_of_conj_mem fun _ hy =>
    ⟨(mem_normalizer_iff.mp (Subgroup.le_normalizer hx) _).mp hy.1,
      conj_mem_centralizer (h.X₄_le_normalizer_A₄ hx) hy.2⟩

theorem X₄_le_normalizer_Q₄ [Finite G] {x : G} (hx : x ∈ d.X₄) :
    x ∈ normalizer ((d.Q₄ : Subgroup G) : Set G) :=
  mem_normalizer_of_conj_mem fun _ hy =>
    ⟨(mem_normalizer_iff.mp (h.X₄_le_normalizer_U₄ hx) _).mp hy.1,
      (mem_normalizer_iff.mp (h.X₄_le_normalizer_actTriv hx) _).mp hy.2⟩

theorem Λ_le_actTriv [Finite G] : d.Λ ≤ actTriv d.CA₄ (d.withT d.A₃) := fun l hl =>
  ⟨X₄_le_normalizer_CA₄ (h.Λ_le_X₄ hl), h.X₄_le_normalizer_T₃ (h.Λ_le_X₄ hl),
    fun n hn => by simpa [commutatorElement_def] using h.Λ_comm_CA₄ l hl n hn⟩

theorem commutator_mem_Q₄ [Finite G] {u l : G} (hu : u ∈ d.U₄) (hl : l ∈ d.Λ) :
    ⁅u, l⁆ ∈ d.Q₄ ∧ ⁅u, l⁆⁻¹ * d.t * ⁅u, l⁆ * d.t = ⁅u⁻¹ * d.t * u * d.t, l⁆ := by
  have hlX := h.Λ_le_X₄ hl
  have hlU : l * u⁻¹ * l⁻¹ ∈ d.U₄ := (mem_normalizer_iff.mp (h.X₄_le_normalizer_U₄ hlX) _).mp
    (inv_mem hu)
  have hcU : ⁅u, l⁆ ∈ d.U₄ := by
    rw [commutatorElement_def, show u * l * u⁻¹ * l⁻¹ = u * (l * u⁻¹ * l⁻¹) by group]
    exact mul_mem hu hlU
  refine ⟨⟨hcU, ?_⟩, ?_⟩
  · have := commutator_mem_actTriv (X₄_le_normalizer_CA₄ hu.1) (h.X₄_le_normalizer_T₃ hu.1)
      (h.Λ_le_actTriv hl)
    exact this
  · have hlt : l * d.t = d.t * l := h.comm_of_mem_L (h.Λ_le_L hl)
    have e1 : ⁅u, l⁆ = u * (l * u⁻¹ * l⁻¹) := by rw [commutatorElement_def]; group
    rw [e1, h.crossed_U₄_mul hu hlU, crossed_conj hlt, h.crossed_U₄_inv hu,
      commutatorElement_def]
    group

end Hyp

namespace Hyp

variable {d : Data G} (h : Hyp d)
include h

theorem sq_mem_CA₄ [Finite G] {q : G} (hq : q ∈ d.U₄) : q * q ∈ d.CA₄ := by
  refine ⟨(mul_mem hq hq).2, ?_⟩
  change q * q ∈ centralizer ({d.t} : Set G)
  rw [mem_centralizer_singleton_iff, ← crossed_eq_one_iff h.t_sq, h.crossed_U₄_mul hq hq]
  exact h.A₄_sq (h.crossed_X₄ hq.1)

theorem commutator_mem_CA₄ [Finite G] {x y : G} (hx : x ∈ d.U₄) (hy : y ∈ d.U₄) :
    ⁅x, y⁆ ∈ d.CA₄ := by
  have hc : ⁅x, y⁆ ∈ d.U₄ := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  refine ⟨hc.2, ?_⟩
  change ⁅x, y⁆ ∈ centralizer ({d.t} : Set G)
  rw [mem_centralizer_singleton_iff, ← crossed_eq_one_iff h.t_sq, commutatorElement_def,
    h.crossed_U₄_mul (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy),
    h.crossed_U₄_mul (mul_mem hx hy) (inv_mem hx), h.crossed_U₄_mul hx hy,
    h.crossed_U₄_inv hx, h.crossed_U₄_inv hy]
  have ha := h.crossed_X₄ hx.1
  have hb := h.crossed_X₄ hy.1
  rw [h.A₄_comm ha hb]
  group

theorem cube_mem_T₃ [Finite G] {c : G} (hc : c ∈ d.Q₄) (hcC : c ∈ d.CA₄) :
    c ^ 3 ∈ d.withT d.A₃ :=
  h.center_CA₄ c hcC fun m hm => by
    simpa [commutatorElement_def] using hc.2.2.2 m hm

theorem commutator_mem_T₃ [Finite G] {a b : G} (ha : a ∈ d.Q₄) (hb : b ∈ d.Q₄)
    (ha2 : a * a ∈ d.withT d.A₃) : ⁅a, b⁆ ∈ d.withT d.A₃ := by
  set c := ⁅a, b⁆ with hcdef
  have hcQ : c ∈ d.Q₄ := by
    rw [hcdef, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hcC : c ∈ d.CA₄ := h.commutator_mem_CA₄ ha.1 hb.1
  have hT : ∀ x ∈ d.X₄, ∀ y ∈ d.withT d.A₃, x * y * x⁻¹ ∈ d.withT d.A₃ := fun x hx y hy =>
    (mem_normalizer_iff.mp (h.X₄_le_normalizer_T₃ hx) y).mp hy
  have h3 := h.cube_mem_T₃ hcQ hcC
  have hcac : c * (a * c * a⁻¹) ∈ d.withT d.A₃ := by
    have e : c * (a * c * a⁻¹) = (c * (a * a) * c⁻¹) * ((a * b) * (a * a)⁻¹ * (a * b)⁻¹) := by
      rw [hcdef, commutatorElement_def]; group
    rw [e]
    exact mul_mem (hT c hcQ.1.1 _ ha2)
      (hT _ (mul_mem ha.1.1 hb.1.1) _ (inv_mem ha2))
  have hτ : a * c * a⁻¹ * c⁻¹ ∈ d.withT d.A₃ := ha.2.2.2 c hcC
  clear_value c
  have h2 : c * c ∈ d.withT d.A₃ := by
    have e : c * c = (c * (a * c * a⁻¹ * c⁻¹) * c⁻¹)⁻¹ * (c * (a * c * a⁻¹)) := by
      rw [← sq]; group
    rw [e]
    exact mul_mem (inv_mem (hT c hcQ.1.1 _ hτ)) hcac
  have e : c = c ^ 3 * (c * c)⁻¹ := by rw [← sq]; group
  rw [e]
  exact mul_mem h3 (inv_mem h2)

end Hyp

namespace Hyp

variable {d : Data G}

@[expose] def P₄ [Finite G] (h : Hyp d) : Subgroup G where
  carrier := {q | q ∈ d.Q₄ ∧ q * q ∈ d.withT d.A₃}
  one_mem' := ⟨one_mem _, by rw [mul_one]; exact one_mem _⟩
  mul_mem' := by
    rintro x y ⟨hx, hx2⟩ ⟨hy, hy2⟩
    refine ⟨mul_mem hx hy, ?_⟩
    have e : x * y * (x * y) = ⁅x, y⁆ * (y * (x * x) * y⁻¹) * (y * y) := by
      rw [commutatorElement_def]; group
    rw [e]
    refine mul_mem (mul_mem (h.commutator_mem_T₃ hx hy hx2) ?_) hy2
    exact (mem_normalizer_iff.mp (h.X₄_le_normalizer_T₃ hy.1.1) _).mp hx2
  inv_mem' := by
    rintro x ⟨hx, hx2⟩
    refine ⟨inv_mem hx, ?_⟩
    rw [← mul_inv_rev]
    exact inv_mem hx2

variable (h : Hyp d)
include h

theorem P₄_le_X₄ [Finite G] : h.P₄ ≤ d.X₄ := fun _ hq => hq.1.1.1

theorem P₄_le_cent [Finite G] : h.P₄ ≤ centralizer (d.A₄ : Set G) := fun _ hq => hq.1.1.2

theorem X₄_le_normalizer_P₄ [Finite G] : d.X₄ ≤ normalizer ((h.P₄ : Subgroup G) : Set G) := by
  intro x hx
  apply mem_normalizer_of_conj_mem
  rintro q ⟨hq, hq2⟩
  refine ⟨(mem_normalizer_iff.mp (h.X₄_le_normalizer_Q₄ hx) q).mp hq, ?_⟩
  have e : x * q * x⁻¹ * (x * q * x⁻¹) = x * (q * q) * x⁻¹ := by group
  rw [e]
  exact (mem_normalizer_iff.mp (h.X₄_le_normalizer_T₃ hx) _).mp hq2

theorem isPGroup_P₄ [Finite G] : IsPGroup 2 h.P₄ := by
  rintro ⟨q, hq, hq2⟩
  obtain ⟨k, hk⟩ := h.isPGroup_T₃ ⟨q * q, hq2⟩
  refine ⟨k + 1, Subtype.ext ?_⟩
  have hk' : (q * q) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [pow_succ', pow_mul, sq, hk']

theorem T₃_le_P₄ [Finite G] : d.withT d.A₃ ≤ h.P₄ :=
  fun _ hx => ⟨⟨h.T₃_le_U₄ hx, h.T₃_le_actTriv hx⟩, mul_mem hx hx⟩

theorem P₄_inf_H [Finite G] : h.P₄ ⊓ d.H = d.withT d.A₃ := by
  refine le_antisymm ?_ (le_inf h.T₃_le_P₄ (h.withT_le_H h.A₃_le_L))
  rintro c ⟨⟨hcQ, hc2⟩, hcH⟩
  have hcC : c ∈ d.CA₄ := ⟨hcQ.1.2, hcH⟩
  have h3 := h.cube_mem_T₃ hcQ hcC
  have e : c = c ^ 3 * (c * c)⁻¹ := by rw [← sq]; group
  rw [e]
  exact mul_mem h3 (inv_mem hc2)

theorem exists_P₄_conj [Finite G] {a : G} (ha : a ∈ d.A₄) :
    ∃ p ∈ h.P₄, p⁻¹ * d.t * p = a * d.t := by
  let R : Subgroup G :=
    { carrier := {b | ∃ p ∈ h.P₄, p⁻¹ * d.t * p * d.t = b}
      one_mem' := ⟨1, one_mem _, by rw [inv_one, one_mul, mul_one, h.t_sq]⟩
      mul_mem' := by
        rintro _ _ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
        exact ⟨p * q, mul_mem hp hq, h.crossed_U₄_mul hp.1.1 hq.1.1⟩
      inv_mem' := by
        rintro _ ⟨p, hp, rfl⟩
        exact ⟨p⁻¹, inv_mem hp, h.crossed_U₄_inv hp.1.1⟩ }
  have hle : ⁅d.A₄, d.Λ⁆ ≤ R := by
    rw [commutator_le]
    intro b hb l hl
    obtain ⟨u, hu, hut⟩ := h.exists_conj_U hb
    obtain ⟨hqQ, hqt⟩ := h.commutator_mem_Q₄ hu hl
    set q := ⁅u, l⁆ with hqdef
    have hub : u⁻¹ * d.t * u * d.t = b := by rw [hut, mul_assoc, h.t_sq, mul_one]
    rw [hub] at hqt
    have hq2 := h.sq_mem_CA₄ hqQ.1
    have hq2Q : q * q ∈ d.Q₄ := mul_mem hqQ hqQ
    refine ⟨q ^ 3, ⟨pow_mem hqQ 3, ?_⟩, ?_⟩
    · have e : q ^ 3 * q ^ 3 = (q * q) ^ 3 := by rw [← pow_add, ← sq, ← pow_mul]
      rw [e]
      exact h.cube_mem_T₃ hq2Q hq2
    · have e : q ^ 3 = q * q * q := pow_three' q
      rw [e, h.crossed_U₄_mul (mul_mem hqQ.1 hqQ.1) hqQ.1, h.crossed_U₄_mul hqQ.1 hqQ.1, hqt]
      have hc : ⁅b, l⁆ ∈ d.A₄ := by
        rw [commutatorElement_def, show b * l * b⁻¹ * l⁻¹ = b * (l * b⁻¹ * l⁻¹) by group]
        exact mul_mem hb ((mem_normalizer_iff.mp (h.Λ_le_normalizer hl) _).mp (inv_mem hb))
      rw [h.A₄_sq hc, one_mul]
  obtain ⟨p, hp, hpa⟩ := hle (h.A₄_le_comm ha)
  refine ⟨p, hp, ?_⟩
  rw [← hpa, mul_assoc _ d.t d.t, h.t_sq, mul_one]

end Hyp

namespace Hyp

variable {d : Data G} (h : Hyp d)
include h

theorem C₄_eq [Finite G] : d.C₄ = h.P₄ := by
  have hle : h.P₄ ≤ d.C₄ := le_oTwo h.P₄_le_X₄ h.X₄_le_normalizer_P₄ h.isPGroup_P₄
  refine le_antisymm (fun c hc => ?_) hle
  have hcX : c ∈ d.X₄ := oTwo_le _ hc
  have hca := h.crossed_X₄ hcX
  obtain ⟨p, hp, hpt⟩ := h.exists_P₄_conj hca
  have hcp : c * p⁻¹ ∈ d.C₄ ⊓ d.H := by
    refine mem_inf.mpr ⟨mul_mem hc (inv_mem (hle hp)), ?_⟩
    change c * p⁻¹ ∈ centralizer ({d.t} : Set G)
    rw [mem_centralizer_singleton_iff]
    have e1 : c⁻¹ * d.t * c = p⁻¹ * d.t * p := by
      rw [hpt]
      calc c⁻¹ * d.t * c = c⁻¹ * d.t * c * d.t * d.t := by rw [mul_assoc _ d.t d.t, h.t_sq, mul_one]
        _ = _ := rfl
    calc c * p⁻¹ * d.t = c * (p⁻¹ * d.t * p) * p⁻¹ := by group
      _ = c * (c⁻¹ * d.t * c) * p⁻¹ := by rw [e1]
      _ = d.t * (c * p⁻¹) := by group
  have hO : d.C₄ ⊓ d.H ≤ d.withT d.A₃ := by
    refine h.oTwo_NA₄ _ (inf_le_inf_right _ (oTwo_le _)) ?_ ((isPGroup_oTwo _).to_le inf_le_left)
    intro x hx
    apply mem_normalizer_of_conj_mem
    rintro y ⟨hy1, hy2⟩
    exact ⟨(mem_normalizer_iff.mp (le_normalizer_oTwo _ hx.1) y).mp hy1,
      (mem_normalizer_iff.mp (Subgroup.le_normalizer hx.2) y).mp hy2⟩
  have hcp' := h.T₃_le_P₄ (hO hcp)
  have e : c = (c * p⁻¹) * p := by group
  rw [e]
  exact mul_mem hcp' hp

omit h in
theorem isPGroup_C₄ [Finite G] : IsPGroup 2 d.C₄ := isPGroup_oTwo _

omit h in
theorem C₄_le_X₄ : d.C₄ ≤ d.X₄ := oTwo_le _

omit h in
theorem X₄_le_normalizer_C₄ : d.X₄ ≤ normalizer (d.C₄ : Set G) := le_normalizer_oTwo _

theorem C₄_inf_H [Finite G] : d.C₄ ⊓ d.H = d.withT d.A₃ := by
  rw [h.C₄_eq]
  exact h.P₄_inf_H

theorem C₄_le_cent [Finite G] : d.C₄ ≤ centralizer (d.A₄ : Set G) := by
  rw [h.C₄_eq]
  exact h.P₄_le_cent

theorem exists_C₄_conj [Finite G] {a : G} (ha : a ∈ d.A₄) :
    ∃ c ∈ d.C₄, c⁻¹ * d.t * c = a * d.t := by
  rw [h.C₄_eq]
  exact h.exists_P₄_conj ha

theorem T₃_le_C₄ [Finite G] : d.withT d.A₃ ≤ d.C₄ := by
  rw [h.C₄_eq]
  exact h.T₃_le_P₄

theorem X₄_factor [Finite G] {x : G} (hx : x ∈ d.X₄) : ∃ c ∈ d.C₄, x * c⁻¹ ∈ d.H := by
  obtain ⟨c, hc, hct⟩ := h.exists_C₄_conj (h.crossed_X₄ hx)
  refine ⟨c, hc, ?_⟩
  change x * c⁻¹ ∈ centralizer ({d.t} : Set G)
  rw [mem_centralizer_singleton_iff]
  have e1 : x⁻¹ * d.t * x = c⁻¹ * d.t * c := by
    rw [hct, mul_assoc _ d.t d.t, h.t_sq, mul_one]
  calc x * c⁻¹ * d.t = x * (c⁻¹ * d.t * c) * c⁻¹ := by group
    _ = x * (x⁻¹ * d.t * x) * c⁻¹ := by rw [e1]
    _ = d.t * (x * c⁻¹) := by group

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
