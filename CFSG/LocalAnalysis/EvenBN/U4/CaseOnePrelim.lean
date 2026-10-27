module

public import CFSG.LocalAnalysis.EvenBN.U4.NaturalModule

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped commutatorElement

section Model

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem miyamotoXGL_commutator_rootA_rootB_not_mem_Z {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hbb : h.bar b = b) : ⁅miyamotoXGL h a 0 0 0, miyamotoXGL h 0 b 0 0⁆ ∉ miyamotoZ h := by
  rw [miyamotoXGL_commutator h (map_zero _) hbb]
  rintro ⟨d, -, e⟩
  rw [miyamotoXGL_inj] at e
  obtain ⟨-, -, ec, -⟩ := e
  simp only [mul_zero, zero_add] at ec
  exact mul_ne_zero hb ha ec

end Model

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓦" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)

local notation "𝓥" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G)

theorem commutator_rootA_rootB_not_mem_ZG (_hS : Setting h L η t Q T) {u b : G}
    (hu : u ∈ miyamotoPull h L η (miyamotoRootA h)) (hu1 : u ≠ 1)
    (hb : b ∈ miyamotoPull h L η (miyamotoRootB h)) (hb1 : b ≠ 1) :
    u * b * u⁻¹ * b⁻¹ ∉ miyamotoZG h L η := by
  have : CharP K 2 := h.charP
  obtain ⟨g, ⟨a, ha⟩, rfl⟩ := (mem_miyamotoPull h L η).1 hu
  obtain ⟨g', ⟨c, hc, hgc⟩, rfl⟩ := (mem_miyamotoPull h L η).1 hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hu1
    have : g = 1 := Subtype.ext (by rw [ha, miyamotoXGL_zero]; rfl)
    rw [this, map_one]
    rfl
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hb1
    have : g' = 1 := Subtype.ext (by rw [hgc, miyamotoXGL_zero]; rfl)
    rw [this, map_one]
    rfl
  have e : ((η.symm g : L) : G) * ((η.symm g' : L) : G) * ((η.symm g : L) : G)⁻¹ *
      ((η.symm g' : L) : G)⁻¹ = ((η.symm ⁅g, g'⁆ : L) : G) := by
    simp only [commutatorElement_def, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e, symm_mem_miyamotoPull_iff]
  have e2 : ((⁅g, g'⁆ : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) =
      ⁅miyamotoXGL h a 0 0 0, miyamotoXGL h 0 c 0 0⁆ := by
    rw [← ha, ← hgc]
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e2]
  exact miyamotoXGL_commutator_rootA_rootB_not_mem_Z h ha0 hc0 hc

theorem commutator_W_rootB_not_mem_E (hS : Setting h L η t Q T) {w b : G} (hw : w ∈ 𝓦)
    (hw1 : w ≠ 1) (hb : b ∈ miyamotoPull h L η (miyamotoRootB h)) (hb1 : b ≠ 1) :
    w * b * w⁻¹ * b⁻¹ ∉ miyamotoEG h L η Q := by
  intro hwb
  set E := miyamotoEG h L η Q with hE
  have hRE : ∀ r ∈ miyamotoRG h L η t Q, ∀ e ∈ E, r * e * r⁻¹ ∈ E := fun r hr e he => by
    rw [← mem_centralizer_iff.1 (hS.RG_le_centralizer_E hr) e he, mul_inv_cancel_right]
    exact he
  let X : Subgroup G :=
    { carrier := {x | x ∈ 𝓦 ∧ x * b * x⁻¹ * b⁻¹ ∈ E}
      mul_mem' := by
        rintro x y ⟨hx, hxe⟩ ⟨hy, hye⟩
        refine ⟨mul_mem hx hy, ?_⟩
        have e : x * y * b * (x * y)⁻¹ * b⁻¹ =
            x * (y * b * y⁻¹ * b⁻¹) * x⁻¹ * (x * b * x⁻¹ * b⁻¹) := by group
        rw [e]
        exact mul_mem (hRE x (mem_inf.1 hx).1 _ hye) hxe
      one_mem' := ⟨one_mem _, by rw [one_mul, inv_one, mul_one, mul_inv_cancel]; exact one_mem _⟩
      inv_mem' := by
        rintro x ⟨hx, hxe⟩
        refine ⟨inv_mem hx, ?_⟩
        have e : x⁻¹ * b * x⁻¹⁻¹ * b⁻¹ = x⁻¹ * (x * b * x⁻¹ * b⁻¹)⁻¹ * x⁻¹⁻¹ := by group
        rw [e]
        exact hRE _ (inv_mem (mem_inf.1 hx).1) _ (inv_mem hxe) }
  have hX2 : IsPGroup 2 X := hS.isPGroup_RG.to_le fun x hx => (mem_inf.1 hx.1).1
  have hX1 : X ≠ ⊥ := by
    intro hbot
    have : w ∈ X := ⟨hw, hwb⟩
    rw [hbot, mem_bot] at this
    exact hw1 this
  have hbP : b ∈ miyamotoPG h L η := by
    have := (hS.A1G_inf_centralizer_I2).symm ▸ hb
    exact hS.A1G_le_PG (mem_inf.1 this).1
  have htb : t * b = b * t := (mem_centralizer_singleton_iff.1 (hS.PG_le_C hbP)).symm
  have htE : t ∈ normalizer (E : Set G) :=
    hS.normalizer_P1_le_normalizer_E hS.t_mem_normalizer_P1
  have htX : t ∈ normalizer (X : Set G) := by
    refine mem_normalizer_fintype fun x hx => ⟨(mem_normalizer_iff.1 hS.t_mem_normalizer_W x).1
      hx.1, ?_⟩
    have e : t * x * t⁻¹ * b * (t * x * t⁻¹)⁻¹ * b⁻¹ = t * (x * b * x⁻¹ * b⁻¹) * t⁻¹ := by
      have htb' : t⁻¹ * b = b * t⁻¹ := by
        calc t⁻¹ * b = t⁻¹ * (b * t) * t⁻¹ := by group
          _ = t⁻¹ * (t * b) * t⁻¹ := by rw [htb]
          _ = b * t⁻¹ := by group
      calc t * x * t⁻¹ * b * (t * x * t⁻¹)⁻¹ * b⁻¹
          = t * x * (t⁻¹ * b) * t * x⁻¹ * t⁻¹ * b⁻¹ := by group
        _ = t * x * (b * t⁻¹) * t * x⁻¹ * t⁻¹ * b⁻¹ := by rw [htb']
        _ = t * x * b * x⁻¹ * (t⁻¹ * b⁻¹) := by group
        _ = t * x * b * x⁻¹ * (b⁻¹ * t⁻¹) := by
          congr 1
          rw [← mul_inv_rev, ← mul_inv_rev, htb]
        _ = t * (x * b * x⁻¹ * b⁻¹) * t⁻¹ := by group
    show _ ∈ E
    rw [e]
    exact (mem_normalizer_iff.1 htE _).1 hx.2
  obtain ⟨u, ⟨huW, hue⟩, hu1, hut⟩ := hS.exists_ne_one_commute_t hX2 hX1 htX
  have huU : u ∈ miyamotoPull h L η (miyamotoRootA h) := by
    rw [← hS.W_inf_C]
    exact mem_inf.2 ⟨huW, mem_centralizer_singleton_iff.2 hut⟩
  have huP : u ∈ miyamotoPG h L η := hS.rootA_le_PG huU
  have hZ : u * b * u⁻¹ * b⁻¹ ∈ miyamotoZG h L η := by
    rw [← hS.E_inf_PG]
    exact mem_inf.2 ⟨hue, mul_mem (mul_mem (mul_mem huP hbP) (inv_mem huP)) (inv_mem hbP)⟩
  exact hS.commutator_rootA_rootB_not_mem_ZG huU hu1 hb hb1 hZ

theorem exists_mem_rootB_ne_one (hS : Setting h L η t Q T) :
    ∃ b ∈ miyamotoPull h L η (miyamotoRootB h), b ≠ 1 := by
  have h1 : 1 < Nat.card (miyamotoPull h L η (miyamotoRootB h)) := by
    rw [hS.card_rootB]
    exact Nat.one_lt_two_pow (by have := hS.two_le; omega)
  have : Nontrivial (miyamotoPull h L η (miyamotoRootB h)) := Finite.one_lt_card_iff_nontrivial.1 h1
  obtain ⟨⟨b, hb⟩, hb1⟩ := exists_ne (1 : miyamotoPull h L η (miyamotoRootB h))
  exact ⟨b, hb, fun e => hb1 (Subtype.ext e)⟩

theorem commutator_W_V2_not_mem_E (hS : Setting h L η t Q T) {J : Subgroup G}
    (hJW : J ≤ normalizer (𝓦 : Set G)) (hJE : J ≤ normalizer (miyamotoEG h L η Q : Set G))
    (htrans : ∀ a ∈ 𝓥, ∀ b ∈ 𝓥, a ≠ 1 → b ≠ 1 → ∃ j ∈ J, j * a * j⁻¹ = b) {w v : G}
    (hw : w ∈ 𝓦) (hw1 : w ≠ 1) (hv : v ∈ 𝓥) (hv1 : v ≠ 1) :
    w * v * w⁻¹ * v⁻¹ ∉ miyamotoEG h L η Q := by
  intro hwv
  obtain ⟨b, hb, hb1⟩ := hS.exists_mem_rootB_ne_one
  obtain ⟨j, hj, hjv⟩ := htrans v hv b (hS.rootB_le_V2 hb) hv1 hb1
  have hjw : j * w * j⁻¹ ∈ 𝓦 := (mem_normalizer_iff.1 (hJW hj) w).1 hw
  have hjw1 : j * w * j⁻¹ ≠ 1 := fun e => hw1 (by
    calc w = j⁻¹ * (j * w * j⁻¹) * j := by group
      _ = 1 := by rw [e]; group)
  apply hS.commutator_W_rootB_not_mem_E hjw hjw1 hb hb1
  rw [← hjv]
  have e : j * w * j⁻¹ * (j * v * j⁻¹) * (j * w * j⁻¹)⁻¹ * (j * v * j⁻¹)⁻¹ =
      j * (w * v * w⁻¹ * v⁻¹) * j⁻¹ := by group
  rw [e]
  exact (mem_normalizer_iff.1 (hJE hj) _).1 hwv

theorem mem_F_of_commute_W (hS : Setting h L η t Q T) {J : Subgroup G}
    (hJW : J ≤ normalizer (𝓦 : Set G)) (hJE : J ≤ normalizer (miyamotoEG h L η Q : Set G))
    (htrans : ∀ a ∈ 𝓥, ∀ b ∈ 𝓥, a ≠ 1 → b ≠ 1 → ∃ j ∈ J, j * a * j⁻¹ = b) {w y : G}
    (hw : w ∈ 𝓦) (hw1 : w ≠ 1) (hy : y ∈ miyamotoF1G h L η t) (hc : w * y = y * w) :
    y ∈ miyamotoFG h L η t Q := by
  obtain ⟨φ, hφ, v, hv, rfl⟩ := hS.exists_mul_of_mem_F1 hy
  have hvV : v ∈ 𝓥 := by
    rw [hS.RG_inf_centralizer_I2]
    exact hv
  have hwR : w ∈ miyamotoRG h L η t Q := (mem_inf.1 hw).1
  by_contra hφv
  have hv1 : v ≠ 1 := by
    rintro rfl
    rw [mul_one] at hφv
    exact hφv hφ
  apply hS.commutator_W_V2_not_mem_E hJW hJE htrans hw hw1 hvV hv1
  have hc' : w * (φ * v) * w⁻¹ = φ * v := by rw [hc, mul_inv_cancel_right]
  have e : w * v * w⁻¹ * v⁻¹ = (φ⁻¹ * w * φ * w⁻¹)⁻¹ := by
    calc w * v * w⁻¹ * v⁻¹ = (w * φ⁻¹ * w⁻¹) * (w * (φ * v) * w⁻¹) * v⁻¹ := by group
      _ = (w * φ⁻¹ * w⁻¹) * (φ * v) * v⁻¹ := by rw [hc']
      _ = (φ⁻¹ * w * φ * w⁻¹)⁻¹ := by group
  rw [e]
  have := hS.commutator_F_RG_mem_E (inv_mem hφ) hwR
  rw [inv_inv] at this
  exact inv_mem this

theorem mem_F1_or_mem_F2_of_mul_self (hS : Setting h L η t Q T) {J : Subgroup G}
    (hJW : J ≤ normalizer (𝓦 : Set G)) (hJE : J ≤ normalizer (miyamotoEG h L η Q : Set G))
    (htrans : ∀ a ∈ 𝓥, ∀ b ∈ 𝓥, a ≠ 1 → b ≠ 1 → ∃ j ∈ J, j * a * j⁻¹ = b) {x : G}
    (hx : x ∈ miyamotoRG h L η t Q) (hxx : x * x = 1) :
    x ∈ miyamotoF1G h L η t ∨ x ∈ miyamotoF2G h L η t Q := by
  obtain ⟨w, hw, y, hy, rfl⟩ := hS.exists_mul_of_mem_RG hx
  by_cases hw1 : w = 1
  · left
    rw [hw1, one_mul]
    exact hy
  right
  have hww : w * w = 1 := hS.W_mul_self hw
  have hyy : y * y = 1 := hS.F1_mul_self y hy
  have hc : w * y = y * w := by
    have e1 : w * y * (w * y) = 1 := hxx
    calc w * y = w * y * (w * y) * (y * w) := by
            rw [show w * y * (w * y) * (y * w) = w * y * (w * (y * y) * w) by group, hyy,
              mul_one, hww, mul_one]
      _ = y * w := by rw [e1, one_mul]
  have hyF := hS.mem_F_of_commute_W hJW hJE htrans hw hw1 hy hc
  rw [hS.F2_eq]
  exact mul_mem (mem_sup_right hw) (mem_sup_left hyF)

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
