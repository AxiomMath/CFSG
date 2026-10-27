module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSAbs
import CFSG.LocalAnalysis.SeitzReduction.Endgame

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup

variable {G : Type*} [Group G]

section Glue

variable {W : Subgroup G} {t : G}

theorem mem_normalizer_inf_centralizer_of_commute {g : G} (hgW : g ∈ normalizer (W : Set G))
    (hgt : g * t = t * g) :
    g ∈ normalizer ((W ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) := by
  have h1 : g⁻¹ * t * g = t := by
    calc g⁻¹ * t * g = g⁻¹ * (t * g) := by group
      _ = g⁻¹ * (g * t) := by rw [hgt]
      _ = t := by group
  rw [mem_normalizer_iff]
  intro z
  simp only [Subgroup.mem_inf, mem_centralizer_singleton_iff]
  rw [← mem_normalizer_iff.1 hgW z]
  refine and_congr_right fun _ => ⟨fun hz => ?_, fun hz => ?_⟩
  · calc g * z * g⁻¹ * t = g * (z * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * (z * t) * g⁻¹ := by rw [h1]
      _ = g * (t * z) * g⁻¹ := by rw [hz]
      _ = g * ((g⁻¹ * t * g) * z) * g⁻¹ := by rw [h1]
      _ = t * (g * z * g⁻¹) := by group
  · calc z * t = z * (g⁻¹ * t * g) := by rw [h1]
      _ = g⁻¹ * ((g * z * g⁻¹) * t) * g := by group
      _ = g⁻¹ * (t * (g * z * g⁻¹)) * g := by rw [hz]
      _ = (g⁻¹ * t * g) * z := by group
      _ = t * z := by rw [h1]

theorem tcomm_mem_of_mem_sup (hW : ∀ w ∈ W, w * w = 1) (ht : t * t = 1)
    (htW : t ∈ normalizer (W : Set G)) {C : Subgroup G} (hCW : C ≤ normalizer (W : Set G))
    (hCt : C ≤ centralizer ({t} : Set G)) :
    ∀ s ∈ W ⊔ C ⊔ zpowers t, t * s * t⁻¹ * s⁻¹ ∈ W ⊓ centralizer ({t} : Set G) := by
  set V : Subgroup G := W ⊓ centralizer ({t} : Set G) with hV
  let K : Subgroup G :=
    { carrier := {s | s ∈ normalizer (V : Set G) ∧ t * s * t⁻¹ * s⁻¹ ∈ V}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
        refine ⟨mul_mem haN hbN, ?_⟩
        have h1 : a * (t * b * t⁻¹ * b⁻¹) * a⁻¹ ∈ V := (mem_normalizer_iff.1 haN _).1 hb
        rw [show t * (a * b) * t⁻¹ * (a * b)⁻¹ =
          (t * a * t⁻¹ * a⁻¹) * (a * (t * b * t⁻¹ * b⁻¹) * a⁻¹) by group]
        exact mul_mem ha h1
      inv_mem' := by
        rintro a ⟨haN, ha⟩
        refine ⟨inv_mem haN, ?_⟩
        have h1 : a⁻¹ * (t * a * t⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ ∈ V :=
          (mem_normalizer_iff.1 (inv_mem haN) _).1 (inv_mem ha)
        rwa [show a⁻¹ * (t * a * t⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ = t * a⁻¹ * t⁻¹ * a⁻¹⁻¹ by group] at h1 }
  have hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW hv hw
  have hWK : W ≤ K := by
    intro w hw
    refine ⟨?_, Subgroup.mem_inf.2 ⟨tcomm_mem htW hw, tcomm_mem_centralizer hW ht htW hw⟩⟩
    rw [mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have h1 := hWc w hw z (Subgroup.mem_inf.1 hz).1
      rw [h1, mul_inv_cancel_right]
      exact hz
    · intro hz
      have h2 : w * z * w⁻¹ ∈ W := (Subgroup.mem_inf.1 hz).1
      have hzW : z ∈ W := by
        have h3 : w⁻¹ * (w * z * w⁻¹) * w ∈ W := W.mul_mem (W.mul_mem (W.inv_mem hw) h2) hw
        rwa [show w⁻¹ * (w * z * w⁻¹) * w = z by group] at h3
      have h1 := hWc w hw z hzW
      rwa [h1, mul_inv_cancel_right] at hz
  have hCK : C ≤ K := by
    intro c hc
    have hct : c * t = t * c := mem_centralizer_singleton_iff.1 (hCt hc)
    refine ⟨mem_normalizer_inf_centralizer_of_commute (hCW hc) hct, ?_⟩
    rw [show t * c * t⁻¹ * c⁻¹ = 1 by rw [← hct]; group]
    exact one_mem _
  have htK : t ∈ K := by
    refine ⟨mem_normalizer_inf_centralizer_of_commute htW rfl, ?_⟩
    rw [show t * t * t⁻¹ * t⁻¹ = 1 by group]
    exact one_mem _
  intro s hs
  exact (sup_le (sup_le hWK hCK) ((zpowers_le).2 htK) hs).2

theorem eq_of_le_sup_zpowers_of_mul_self [Finite G] (hW : ∀ w ∈ W, w * w = 1) (ht : t * t = 1)
    (htW : t ∈ normalizer (W : Set G))
    (hcard : 2 * Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) < Nat.card W)
    {B : Subgroup G} (hBW : B ≤ W ⊔ zpowers t) (hB2 : ∀ b ∈ B, b * b = 1)
    (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (hBcard : Nat.card B = Nat.card W) : B = W := by
  have hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW hv hw
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  by_cases hle : B ≤ W
  · exact Subgroup.eq_of_le_of_card_ge hle hBcard.ge
  exfalso
  obtain ⟨b₀, hb₀B, hb₀W⟩ := Set.not_subset.1 hle
  set V : Subgroup G := W ⊓ centralizer ({t} : Set G) with hV
  have hb₀t : b₀ * t ∈ W := by
    rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers ht htW (hBW hb₀B) with h | h
    · exact absurd h hb₀W
    · exact h
  have hsub : B ≤ V ⊔ zpowers t := by
    intro b hb
    rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers ht htW (hBW hb) with h | h
    ·
      refine mem_sup_left (Subgroup.mem_inf.2 ⟨h, ?_⟩)
      rw [mem_centralizer_singleton_iff]
      have h1 : b * b₀ = b₀ * b := hBc b hb b₀ hb₀B
      have h2 : b * (b₀ * t) = (b₀ * t) * b := hWc b h _ hb₀t
      have h3 : b₀ = (b₀ * t) * t := by rw [mul_assoc, ht, mul_one]
      have h4 : (b₀ * t) * (b * t) = (b₀ * t) * (t * b) := by
        calc (b₀ * t) * (b * t) = (b * (b₀ * t)) * t := by rw [h2]; group
          _ = b * b₀ * (t * t) := by group
          _ = b₀ * b * (t * t) := by rw [h1]
          _ = (b₀ * t) * (t * b) := by
            rw [ht, mul_one, show b₀ * t * (t * b) = b₀ * (t * t) * b by group, ht, mul_one]
      exact mul_left_cancel h4
    ·
      have hbt : b * t ∈ V := by
        refine Subgroup.mem_inf.2 ⟨h, ?_⟩
        rw [mem_centralizer_singleton_iff]
        have h1 : b * b = 1 := hB2 b hb
        have h2 : (b * t) * (b * t) = 1 := hW _ h
        calc b * t * t = b := by rw [mul_assoc, ht, mul_one]
          _ = b * (b * t * (b * t)) := by rw [h2, mul_one]
          _ = (b * b) * t * b * t := by group
          _ = t * (b * t) := by rw [h1, one_mul]; group
      have h3 : b = (b * t) * t := by rw [mul_assoc, ht, mul_one]
      rw [h3]
      exact mul_mem (mem_sup_left hbt) (mem_sup_right (mem_zpowers t))
  have hcardVt : Nat.card (V ⊔ zpowers t : Subgroup G) ≤ 2 * Nat.card V := by
    have hN : zpowers t ≤ normalizer (V : Set G) :=
      (zpowers_le).2 (mem_normalizer_inf_centralizer_of_commute htW rfl)
    have h1 := card_sup_mul_card_inf_of_le_normalizer_sOne hN
    have h2 : Nat.card (zpowers t) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [sq, ht])
    have h3 : 0 < Nat.card (V ⊓ zpowers t : Subgroup G) := Nat.card_pos
    nlinarith
  have h1 := Subgroup.card_le_of_le hsub
  omega

end Glue

section Key

variable [Finite G] {W : Subgroup G} {t h : G}

theorem card_inf_centralizer_mul_le_of_sq (hW : ∀ w ∈ W, w * w = 1) (ht : t * t = 1)
    (htW : t ∈ normalizer (W : Set G)) (hhW : h ∈ normalizer (W : Set G)) (hh : h * h = 1)
    (hsq : Nat.card (W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({h} : Set G) : Subgroup G) ^ 2
      ≤ Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G)) :
    Nat.card (W ⊓ centralizer ({h * t} : Set G) : Subgroup G) ≤
      Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  have h1 := card_inf_centralizer_mul_le_card_mul (B := ⊤) hW ht htW hhW hh fun _ _ => mem_top _
  rw [inf_top_eq, ← sq] at h1
  exact h1.trans hsq

theorem exists_commutator_subgroup_of_root (hW : ∀ w ∈ W, w * w = 1) (ht : t * t = 1)
    (htW : t ∈ normalizer (W : Set G))
    (hWV : Nat.card W = Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2)
    {x : G} (hxW : x ∈ normalizer (W : Set G)) (hxt : x * t = t * x)
    (hroot : Nat.card W ≤ 4 * Nat.card (W ⊓ centralizer ({x} : Set G) : Subgroup G))
    (hxV : x ∉ centralizer ((W ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G)) :
    ∃ M : Subgroup G, (∀ w ∈ W, x * w * x⁻¹ * w⁻¹ ∈ M) ∧ M ≤ W ∧
      Nat.card (M ⊓ (W ⊓ centralizer ({t} : Set G)) : Subgroup G) ≤ 2 := by
  have hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW hv hw
  set V : Subgroup G := W ⊓ centralizer ({t} : Set G) with hV
  have hAB : ∀ a ∈ W, x * a * x⁻¹ * a⁻¹ ∈ W := fun a ha => tcomm_mem hxW ha
  set φ := tcommHom (t := x) hWc hxW le_rfl hAB with hφ
  have hker : Nat.card φ.ker = Nat.card (W ⊓ centralizer ({x} : Set G) : Subgroup G) :=
    card_ker_tcommHom hWc hxW le_rfl hAB inf_le_left fun a _ =>
      ⟨fun h => (Subgroup.mem_inf.1 h).2, fun h => Subgroup.mem_inf.2 ⟨‹_›, h⟩⟩
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hker] at hcard
  set M : Subgroup G := φ.range.map W.subtype with hM
  have hMc : Nat.card M = Nat.card φ.range :=
    Subgroup.card_map_of_injective W.subtype_injective
  have hMmem : ∀ w ∈ W, x * w * x⁻¹ * w⁻¹ ∈ M := fun w hw => ⟨φ ⟨w, hw⟩, ⟨_, rfl⟩, rfl⟩
  have hMW : M ≤ W := map_subtype_le _
  have hM4 : Nat.card M ≤ 4 := by
    have hpos : 0 < Nat.card (W ⊓ centralizer ({x} : Set G) : Subgroup G) := Nat.card_pos
    rw [hMc]
    rw [hcard] at hroot
    exact Nat.le_of_mul_le_mul_right hroot hpos
  obtain ⟨v, hvV, hvx⟩ : ∃ v ∈ V, ¬ (v * x = x * v) := by
    by_contra hcon
    exact hxV (mem_centralizer_iff.2 fun v hv => by_contra fun hne => hcon ⟨v, hv, hne⟩)
  obtain ⟨w, hw, hwv⟩ := tcomm_surjective_of_card hW ht htW hWV v hvV
  have hmV : x * w * x⁻¹ * w⁻¹ ∉ V := by
    intro hm
    have h1 : t * (x * w * x⁻¹ * w⁻¹) * t⁻¹ * (x * w * x⁻¹ * w⁻¹)⁻¹ = 1 :=
      tcomm_eq_one_iff.2 (Subgroup.mem_inf.1 hm).2
    have hxw : x * w * x⁻¹ ∈ W := (mem_normalizer_iff.1 hxW w).1 hw
    rw [tcomm_mul hWc htW hxw (W.inv_mem hw), tcomm_conj_of_commute hxt] at h1
    have h2 : t * w⁻¹ * t⁻¹ * w⁻¹⁻¹ = (t * w * t⁻¹ * w⁻¹)⁻¹ := by
      have h3 := tcomm_mul hWc htW hw (W.inv_mem hw)
      rw [mul_inv_cancel, show t * 1 * t⁻¹ * 1⁻¹ = 1 by group] at h3
      exact eq_inv_of_mul_eq_one_right h3.symm
    rw [h2, hwv] at h1
    apply hvx
    calc v * x = (x * v * x⁻¹ * v⁻¹)⁻¹ * (x * v) := by group
      _ = x * v := by rw [h1, inv_one, one_mul]
  have hlt : M ⊓ V < M := by
    refine lt_of_le_of_ne inf_le_left fun h => hmV ?_
    have h1 : x * w * x⁻¹ * w⁻¹ ∈ M ⊓ V := by rw [h]; exact hMmem w hw
    exact (Subgroup.mem_inf.1 h1).2
  have h2 := two_mul_card_le_of_lt hlt
  exact ⟨M, hMmem, hMW, by omega⟩

theorem card_inf_centralizer_mul_le_of_root (hW : ∀ w ∈ W, w * w = 1) (ht : t * t = 1)
    (htW : t ∈ normalizer (W : Set G))
    (hWV : Nat.card W = Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2)
    (hhW : h ∈ normalizer (W : Set G)) (hht : h * t = t * h) (hh : h * h = 1)
    (hroot : Nat.card W ≤ 4 * Nat.card (W ⊓ centralizer ({h} : Set G) : Subgroup G))
    (hV : h ∉ centralizer ((W ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G)) :
    Nat.card (W ⊓ centralizer ({h * t} : Set G) : Subgroup G) ≤
      Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  obtain ⟨M, hMmem, -, hM2⟩ := exists_commutator_subgroup_of_root hW ht htW hWV hhW hht hroot hV
  have h1 := card_inf_centralizer_mul_le_card_mul hW ht htW hhW hh hMmem
  have h2 : Nat.card (W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({h} : Set G) ⊓ M :
      Subgroup G) ≤ 2 :=
    (Subgroup.card_le_of_le (show W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({h} : Set G) ⊓ M ≤
      M ⊓ (W ⊓ centralizer ({t} : Set G)) from fun z hz => Subgroup.mem_inf.2
        ⟨(Subgroup.mem_inf.1 hz).2, (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hz).1).1⟩)).trans hM2
  have hlt : W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({h} : Set G) <
      W ⊓ centralizer ({t} : Set G) := by
    refine lt_of_le_of_ne inf_le_left fun heq => hV ?_
    rw [mem_centralizer_iff]
    intro v hv
    rw [← heq] at hv
    exact mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hv).2
  have h3 := two_mul_card_le_of_lt hlt
  calc Nat.card (W ⊓ centralizer ({h * t} : Set G) : Subgroup G)
      ≤ Nat.card (W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({h} : Set G) : Subgroup G) *
        Nat.card (W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({h} : Set G) ⊓ M :
          Subgroup G) := h1
    _ ≤ Nat.card (W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({h} : Set G) : Subgroup G) * 2 :=
        Nat.mul_le_mul_left _ h2
    _ ≤ _ := by omega

end Key

section Root

variable {W : Subgroup G} {t : G}

theorem tcomm_commutator_eq (hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v)
    (htW : t ∈ normalizer (W : Set G)) {x : G} (hxW : x ∈ normalizer (W : Set G))
    (hxt : x * t = t * x) {w : G} (hw : w ∈ W) :
    t * (x * w * x⁻¹ * w⁻¹) * t⁻¹ * (x * w * x⁻¹ * w⁻¹)⁻¹ =
      x * (t * w * t⁻¹ * w⁻¹) * x⁻¹ * (t * w * t⁻¹ * w⁻¹)⁻¹ := by
  have hxw : x * w * x⁻¹ ∈ W := (mem_normalizer_iff.1 hxW w).1 hw
  have h2 : t * w⁻¹ * t⁻¹ * w⁻¹⁻¹ = (t * w * t⁻¹ * w⁻¹)⁻¹ := by
    have h3 := tcomm_mul hWc htW hw (W.inv_mem hw)
    rw [mul_inv_cancel, show t * 1 * t⁻¹ * 1⁻¹ = 1 by group] at h3
    exact eq_inv_of_mul_eq_one_right h3.symm
  rw [tcomm_mul hWc htW hxw (W.inv_mem hw), tcomm_conj_of_commute hxt, h2]

theorem mem_normalizer_of_root [Finite G] (hW : ∀ w ∈ W, w * w = 1) (ht : t * t = 1)
    (htW : t ∈ normalizer (W : Set G))
    (hWV : Nat.card W = Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2)
    {W₀ V₀ : Subgroup G} (hV₀W₀ : V₀ ≤ W₀) (hW₀W : W₀ ≤ W)
    (hW₀t : ∀ w ∈ W₀, t * w * t⁻¹ * w⁻¹ ∈ V₀)
    {x : G} (hxW : x ∈ normalizer (W : Set G)) (hxt : x * t = t * x) (hx2 : x * x = 1)
    (hroot : Nat.card W ≤ 4 * Nat.card (W ⊓ centralizer ({x} : Set G) : Subgroup G))
    (hxV : x ∉ centralizer ((W ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G))
    (hxV₀ : V₀ ≤ centralizer ({x} : Set G))
    (hVx : ∀ v ∈ W ⊓ centralizer ({t} : Set G), x * v * x⁻¹ * v⁻¹ ∈ V₀) :
    x ∈ normalizer (W₀ : Set G) := by
  have hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW hv hw
  set V : Subgroup G := W ⊓ centralizer ({t} : Set G) with hV
  obtain ⟨M, hMmem, hMW, hM2⟩ := exists_commutator_subgroup_of_root hW ht htW hWV hxW hxt hroot hxV
  have hxNV : x ∈ normalizer (V : Set G) := mem_normalizer_inf_centralizer_of_commute hxW hxt
  obtain ⟨v₀, hv₀V, hv₀x⟩ : ∃ v ∈ V, ¬ (v * x = x * v) := by
    by_contra hcon
    exact hxV (mem_centralizer_iff.2 fun v hv => by_contra fun hne => hcon ⟨v, hv, hne⟩)
  set m₀ : G := x * v₀ * x⁻¹ * v₀⁻¹ with hm₀
  have hm₀V : m₀ ∈ V := mul_mem ((mem_normalizer_iff.1 hxNV v₀).1 hv₀V) (inv_mem hv₀V)
  have hm₀1 : m₀ ≠ 1 := by
    intro h1
    apply hv₀x
    calc v₀ * x = (x * v₀ * x⁻¹ * v₀⁻¹)⁻¹ * (x * v₀) := by group
      _ = x * v₀ := by rw [← hm₀, h1, inv_one, one_mul]
  have hMV : M ⊓ V ≤ V₀ := by
    have hz : zpowers m₀ ≤ M ⊓ V :=
      (zpowers_le).2 (Subgroup.mem_inf.2 ⟨hMmem v₀ (Subgroup.mem_inf.1 hv₀V).1, hm₀V⟩)
    have hoz : orderOf m₀ = 2 := orderOf_eq_prime (by rw [sq]; exact hW m₀ (hV ▸ hm₀V).1) hm₀1
    have heq : zpowers m₀ = M ⊓ V :=
      Subgroup.eq_of_le_of_card_ge hz (by rw [Nat.card_zpowers, hoz]; exact hM2)
    rw [← heq, zpowers_le]
    exact hVx v₀ hv₀V
  refine mem_normalizer_of_mul_self_of_conj_mem hx2 fun w hw => ?_
  have hwW : w ∈ W := hW₀W hw
  have hm : x * w * x⁻¹ * w⁻¹ ∈ M ⊓ V := by
    refine Subgroup.mem_inf.2 ⟨hMmem w hwW, Subgroup.mem_inf.2 ⟨tcomm_mem hxW hwW, ?_⟩⟩
    rw [← tcomm_eq_one_iff, tcomm_commutator_eq hWc htW hxW hxt hwW]
    have hc := mem_centralizer_singleton_iff.1 (hxV₀ (hW₀t w hw))
    rw [← hc]
    group
  have h1 : x * w * x⁻¹ = (x * w * x⁻¹ * w⁻¹) * w := by group
  rw [h1]
  exact mul_mem (hV₀W₀ (hMV hm)) hw

theorem commutator_mem_centralizer {W₀ : Subgroup G} {a b : G}
    (ha : a ∈ centralizer (W₀ : Set G)) (hb : b ∈ normalizer (W₀ : Set G)) :
    a * b * a⁻¹ * b⁻¹ ∈ centralizer (W₀ : Set G) := by
  rw [mem_centralizer_iff]
  intro w hw
  have hw' : b⁻¹ * w * b ∈ W₀ := by
    have h1 := (mem_normalizer_iff.1 hb (b⁻¹ * w * b)).2
    apply h1
    rwa [show b * (b⁻¹ * w * b) * b⁻¹ = w by group]
  have h2 : (b⁻¹ * w * b) * a = a * (b⁻¹ * w * b) := (mem_centralizer_iff.1 ha) _ hw'
  have h3 : w * a = a * w := (mem_centralizer_iff.1 ha) w hw
  calc w * (a * b * a⁻¹ * b⁻¹) = (w * a) * b * a⁻¹ * b⁻¹ := by group
    _ = a * w * b * a⁻¹ * b⁻¹ := by rw [h3]
    _ = a * b * ((b⁻¹ * w * b) * a⁻¹) * b⁻¹ := by group
    _ = a * b * (a⁻¹ * (b⁻¹ * w * b)) * b⁻¹ := by
        rw [show (b⁻¹ * w * b) * a⁻¹ = a⁻¹ * (b⁻¹ * w * b) by
          rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← h2, mul_assoc, mul_inv_cancel, mul_one]]
    _ = a * b * a⁻¹ * b⁻¹ * w := by group

end Root

end CFSG.SeitzReduction.LinearPilot
