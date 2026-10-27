module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Generic

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open
open scoped Pointwise

section Conj

variable {Γ : Type*} [Group Γ]

theorem mem_map_conj_iff' {X : Subgroup Γ} {a y : Γ} :
    y ∈ X.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * y * a ∈ X := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rwa [show a⁻¹ * (a * x * a⁻¹) * a = x by group]
  · intro h
    exact ⟨_, h, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

theorem card_map_conj' (X : Subgroup Γ) (a : Γ) :
    Nat.card (X.map (MulAut.conj a).toMonoidHom) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj a).injective

theorem map_conj_map_conj' (X : Subgroup Γ) (a b : Γ) :
    (X.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      X.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply]
  group

theorem map_conj_one' (X : Subgroup Γ) : X.map (MulAut.conj (1 : Γ)).toMonoidHom = X := by
  ext x
  simp

theorem map_conj_inf (X Y : Subgroup Γ) (a : Γ) :
    (X ⊓ Y).map (MulAut.conj a).toMonoidHom =
      X.map (MulAut.conj a).toMonoidHom ⊓ Y.map (MulAut.conj a).toMonoidHom :=
  Subgroup.map_inf_eq X Y _ (MulAut.conj a).injective

theorem mem_normalizer_map_conj_iff {X : Subgroup Γ} {k g : Γ} :
    g ∈ normalizer ((X.map (MulAut.conj k).toMonoidHom : Subgroup Γ) : Set Γ) ↔
      k⁻¹ * g * k ∈ normalizer (X : Set Γ) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro H x
    have h := H (k * x * k⁻¹)
    rw [mem_map_conj_iff', mem_map_conj_iff'] at h
    rw [show k⁻¹ * (k * x * k⁻¹) * k = x by group,
      show k⁻¹ * (g * (k * x * k⁻¹) * g⁻¹) * k = k⁻¹ * g * k * x * (k⁻¹ * g * k)⁻¹ by group] at h
    exact h
  · intro H x
    have h := H (k⁻¹ * x * k)
    rw [mem_map_conj_iff', mem_map_conj_iff']
    rw [show k⁻¹ * g * k * (k⁻¹ * x * k) * (k⁻¹ * g * k)⁻¹ = k⁻¹ * (g * x * g⁻¹) * k by group] at h
    exact h

theorem normalizer_map_conj (X : Subgroup Γ) (k : Γ) :
    normalizer ((X.map (MulAut.conj k).toMonoidHom : Subgroup Γ) : Set Γ) =
      (normalizer (X : Set Γ)).map (MulAut.conj k).toMonoidHom := by
  ext g
  rw [mem_normalizer_map_conj_iff, mem_map_conj_iff']

theorem card_normalizer_map_conj (X : Subgroup Γ) (k : Γ) :
    Nat.card (normalizer ((X.map (MulAut.conj k).toMonoidHom : Subgroup Γ) : Set Γ)) =
      Nat.card (normalizer (X : Set Γ)) := by
  rw [normalizer_map_conj, card_map_conj']

theorem eq_map_conj_inv_of_map_conj_eq {X Y : Subgroup Γ} {c : Γ}
    (h : X.map (MulAut.conj c).toMonoidHom = Y) : X = Y.map (MulAut.conj c⁻¹).toMonoidHom := by
  rw [← h, map_conj_map_conj', inv_mul_cancel, map_conj_one']

theorem isElemAbelian_map_conj {p : ℕ} {X : Subgroup Γ} (hX : IsElemAbelian p X) (a : Γ) :
    IsElemAbelian p (X.map (MulAut.conj a).toMonoidHom) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨x', hx', hx''⟩ := x.2
    obtain ⟨y', hy', hy''⟩ := y.2
    apply Subtype.ext
    show (x : Γ) * y = y * x
    rw [← hx'', ← hy'']
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have := hX.1.1.comm ⟨x', hx'⟩ ⟨y', hy'⟩
    have h2 : x' * y' = y' * x' := by simpa using congrArg Subtype.val this
    rw [show a * x' * a⁻¹ * (a * y' * a⁻¹) = a * (x' * y') * a⁻¹ by group,
      show a * y' * a⁻¹ * (a * x' * a⁻¹) = a * (y' * x') * a⁻¹ by group, h2]
  · obtain ⟨x', hx', rfl⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_pow]
    have := hX.2 x' hx'
    rw [this]
    simp

theorem elemAbelian_comm {E : Subgroup Γ} (h : IsElemAbelian 2 E) {a b : Γ} (ha : a ∈ E) (hb : b ∈ E) :
    a * b = b * a := by
  have := h.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val this

theorem elemAbelian_sq {E : Subgroup Γ} (h : IsElemAbelian 2 E) {a : Γ} (ha : a ∈ E) : a * a = 1 := by
  have := h.2 a ha
  simpa [pow_two] using this

theorem isElemAbelian_of_comm_sq {E : Subgroup Γ} (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (h2 : ∀ a ∈ E, a * a = 1) : IsElemAbelian 2 E :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, fun x hx => by rw [pow_two]; exact h2 x hx⟩

end Conj

section Rank

variable {Γ : Type*} [Group Γ]

theorem map_conj_eq_of_le [Finite Γ] {X : Subgroup Γ} {g : Γ}
    (h : X.map (MulAut.conj g).toMonoidHom ≤ X) : X.map (MulAut.conj g).toMonoidHom = X :=
  Subgroup.eq_of_le_of_card_ge h (by rw [card_map_conj'])

theorem mul_conj_mem_centralizer {V : Subgroup Γ} (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    {s : Γ} (hs : s ∈ normalizer (V : Set Γ)) (hs2 : s * s = 1) {v : Γ} (hv : v ∈ V) :
    v * (s * v * s⁻¹) ∈ centralizer ({s} : Set Γ) := by
  rw [mem_centralizer_singleton_iff]
  have hsv : s * v * s⁻¹ ∈ V := (mem_normalizer_iff.1 hs v).1 hv
  have hsu : s * (s * v * s⁻¹) * s⁻¹ = v := by
    calc s * (s * v * s⁻¹) * s⁻¹ = (s * s) * v * (s * s)⁻¹ := by group
      _ = v := by rw [hs2]; group
  have key : s * (v * (s * v * s⁻¹)) * s⁻¹ = v * (s * v * s⁻¹) := by
    calc s * (v * (s * v * s⁻¹)) * s⁻¹
        = (s * v * s⁻¹) * (s * (s * v * s⁻¹) * s⁻¹) := by group
      _ = (s * v * s⁻¹) * v := by rw [hsu]
      _ = v * (s * v * s⁻¹) := hcomm _ hsv v hv
  calc v * (s * v * s⁻¹) * s = (s * (v * (s * v * s⁻¹)) * s⁻¹) * s := by rw [key]
    _ = s * (v * (s * v * s⁻¹)) := by group

noncomputable def commMap (V : Subgroup Γ) (s : Γ) (hs : s ∈ normalizer (V : Set Γ))
    (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) : ↥V →* ↥V :=
  MonoidHom.mk' (fun v => ⟨(v : Γ) * (s * v * s⁻¹),
      V.mul_mem v.2 ((mem_normalizer_iff.1 hs v).1 v.2)⟩)
    (fun a b => by
      apply Subtype.ext
      have ha : s * (a : Γ) * s⁻¹ ∈ V := (mem_normalizer_iff.1 hs a).1 a.2
      have hcomm := hV (b : Γ) b.2 (s * a * s⁻¹) ha
      show (a : Γ) * b * (s * (a * b) * s⁻¹) = (a * (s * a * s⁻¹)) * (b * (s * b * s⁻¹))
      calc (a : Γ) * b * (s * (a * b) * s⁻¹) = a * (b * (s * a * s⁻¹)) * (s * b * s⁻¹) := by group
        _ = a * ((s * a * s⁻¹) * b) * (s * b * s⁻¹) := by rw [hcomm]
        _ = _ := by group)

theorem two_pow_five_le_card_inf_centralizer [Finite Γ] {V : Subgroup Γ}
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hsq : ∀ a ∈ V, a * a = 1)
    (hV : Nat.card V = 2 ^ 10) {s : Γ} (hs : s ∈ normalizer (V : Set Γ)) (hs2 : s * s = 1) :
    2 ^ 5 ≤ Nat.card ↥(V ⊓ centralizer ({s} : Set Γ)) := by
  set φ := commMap V s hs hcomm with hφ
  have hφv : ∀ v : ↥V, ((φ v : ↥V) : Γ) = (v : Γ) * (s * v * s⁻¹) := fun v => rfl
  have hker : φ.ker ≤ (centralizer ({s} : Set Γ)).subgroupOf V := by
    intro v hv
    have h1 : (v : Γ) * (s * v * s⁻¹) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hv)
      rw [hφv] at this
      simpa using this
    have h2 : s * (v : Γ) * s⁻¹ = (v : Γ) := by
      have h3 : (v : Γ)⁻¹ = v := inv_eq_of_mul_eq_one_right (hsq v v.2)
      calc s * (v : Γ) * s⁻¹ = (v : Γ)⁻¹ := eq_inv_of_mul_eq_one_right h1
        _ = v := h3
    rw [mem_subgroupOf, mem_centralizer_singleton_iff]
    calc (v : Γ) * s = s * v * s⁻¹ * s := by rw [h2]
      _ = s * v := by group
  have hrange : φ.range ≤ (centralizer ({s} : Set Γ)).subgroupOf V := by
    rintro _ ⟨v, rfl⟩
    rw [mem_subgroupOf, hφv]
    exact mul_conj_mem_centralizer hcomm hs hs2 v.2
  have hcard := Subgroup.card_ker_mul_card_range φ
  have h1 := Subgroup.card_le_of_le hker
  have h2 := Subgroup.card_le_of_le hrange
  have hc : Nat.card ((centralizer ({s} : Set Γ)).subgroupOf V) =
      Nat.card ↥(V ⊓ centralizer ({s} : Set Γ)) := by
    have e : Nat.card ((centralizer ({s} : Set Γ)).subgroupOf V) =
        Nat.card ↥(centralizer ({s} : Set Γ) ⊓ V) := by
      rw [← Subgroup.inf_subgroupOf_right]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
        centralizer ({s} : Set Γ) ⊓ V ≤ V)).toEquiv
    rw [e, inf_comm]
  rw [hc] at h1 h2
  rw [hV] at hcard
  by_contra hlt
  push_neg at hlt
  have : Nat.card ↥(V ⊓ centralizer ({s} : Set Γ)) ≤ 31 := by omega
  have := Nat.mul_le_mul (h1.trans this) (h2.trans this)
  omega

theorem le_normalizer_sup_inf_centralizer [Finite Γ] {V : Subgroup Γ}
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hsq : ∀ a ∈ V, a * a = 1)
    {s : Γ} (hs : s ∈ normalizer (V : Set Γ)) (hs2 : s * s = 1) :
    V ≤ normalizer ((zpowers s ⊔ (V ⊓ centralizer ({s} : Set Γ)) : Subgroup Γ) : Set Γ) := by
  intro v hv
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply map_conj_eq_of_le
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rw [MonoidHom.map_zpowers, zpowers_le]
    have hvv : (v : Γ)⁻¹ = v := inv_eq_of_mul_eq_one_right (hsq v hv)
    have hw : v * (s * v * s⁻¹) ∈ V ⊓ centralizer ({s} : Set Γ) :=
      ⟨V.mul_mem hv ((mem_normalizer_iff.1 hs v).1 hv), mul_conj_mem_centralizer hcomm hs hs2 hv⟩
    have e : (MulAut.conj v).toMonoidHom s = v * (s * v * s⁻¹) * s := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hvv]
      group
    rw [e]
    exact mul_mem (mem_sup_right hw) (mem_sup_left (mem_zpowers s))
  · rintro _ ⟨c, hc, rfl⟩
    have hcv : v * c = c * v := hcomm v hv c hc.1
    have e : (MulAut.conj v).toMonoidHom c = c := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hcv]
      group
    rw [e]
    exact mem_sup_right hc

theorem le_pRank_of_isElemAbelian [Finite Γ] {H E : Subgroup Γ} (hE : E ≤ H)
    (hEa : IsElemAbelian 2 E) {k : ℕ} (hk : Nat.card E = 2 ^ k) : k ≤ pRank 2 H := by
  unfold pRank
  apply le_csSup
  · refine ⟨Nat.card Γ, ?_⟩
    rintro j ⟨E', -, -, hj⟩
    have h1 : 2 ^ j ≤ Nat.card Γ := hj ▸ Subgroup.card_le_card_group E'
    exact (Nat.lt_two_pow_self (n := j)).le.trans h1
  · exact ⟨E, hE, hEa, hk⟩

theorem mem_maxElemAbelian2_of_card_eq {R V E : Subgroup Γ} (hV : V ∈ maxElemAbelian2 R)
    (hE : E ≤ R) (hEa : IsElemAbelian 2 E) (hcard : Nat.card E = Nat.card V) :
    E ∈ maxElemAbelian2 R :=
  ⟨hE, hEa, fun D hD hDa => by rw [hcard]; exact hV.2.2 D hD hDa⟩

end Rank


end CFSG.LocalAnalysis.EvenBN.Tits.N
