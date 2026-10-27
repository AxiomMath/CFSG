module

public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup Equiv Equiv.Perm

section LocalRank

variable {G : Type*} [Group G] [Finite G]

theorem le_localRank_of_elemAbelian {W E : Subgroup G} (hW : W ≠ ⊥) (hW2 : IsPGroup 2 W)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hEN : E ≤ Subgroup.normalizer (W : Set G)) {k : ℕ}
    (hk : Nat.card E = 3 ^ k) : k ≤ CFSG.Assembly.RankThreeEven.localRank 3 G := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have h1 : k ≤ CFSG.Assembly.pRank 3 (Subgroup.normalizer (W : Set G)) := by
    refine le_csSup ⟨Nat.card G, ?_⟩ ⟨E, hEN, hE, hk⟩
    rintro n ⟨F, -, -, hF⟩
    have h1 : n < 3 ^ n := Nat.lt_pow_self hp.one_lt
    have h2 : Nat.card F ≤ Nat.card G := Subgroup.card_le_card_group F
    omega
  have h2 : CFSG.Assembly.pRank 3 (Subgroup.normalizer (W : Set G)) ≤
      CFSG.Assembly.RankThreeEven.localRank 3 G := by
    refine le_csSup ⟨Nat.card G, ?_⟩ ⟨_, ⟨W, hW, hW2, rfl⟩, rfl⟩
    rintro n ⟨H, -, rfl⟩
    refine csSup_le' ?_
    rintro m ⟨F, -, -, hF⟩
    have h1 : m < 3 ^ m := Nat.lt_pow_self hp.one_lt
    have h2 : Nat.card F ≤ Nat.card G := Subgroup.card_le_card_group F
    omega
  exact h1.trans h2

end LocalRank

section A6

def u6 : Perm (Fin 6) := swap 0 1 * swap 2 3
def v6 : Perm (Fin 6) := swap 0 2 * swap 1 3
def y6 : Perm (Fin 6) := swap 0 1 * swap 1 2

theorem u6_mem : u6 ∈ alternatingGroup (Fin 6) := by rw [mem_alternatingGroup]; decide
theorem v6_mem : v6 ∈ alternatingGroup (Fin 6) := by rw [mem_alternatingGroup]; decide
theorem y6_mem : y6 ∈ alternatingGroup (Fin 6) := by rw [mem_alternatingGroup]; decide

theorem u6_v6 : u6 * v6 = v6 * u6 := by decide
theorem u6_sq : u6 * u6 = 1 := by decide
theorem v6_sq : v6 * v6 = 1 := by decide
theorem y6_cube : y6 ^ 3 = 1 := by decide
theorem y6_ne : y6 ≠ 1 := by decide
theorem u6_ne : u6 ≠ 1 := by decide
theorem y6_u6 : y6 * u6 * y6⁻¹ = u6 * v6 := by decide
theorem y6_v6 : y6 * v6 * y6⁻¹ = u6 := by decide

theorem A6_aux : ∃ y : alternatingGroup (Fin 6), y ^ 3 = 1 ∧ y ≠ 1 ∧
    ∃ W : Subgroup (alternatingGroup (Fin 6)), W ≠ ⊥ ∧ (∀ w ∈ W, w ^ 2 = 1) ∧
      y ∈ Subgroup.normalizer (W : Set (alternatingGroup (Fin 6))) := by
  set u' : alternatingGroup (Fin 6) := ⟨u6, u6_mem⟩ with hu'
  set v' : alternatingGroup (Fin 6) := ⟨v6, v6_mem⟩ with hv'
  set y' : alternatingGroup (Fin 6) := ⟨y6, y6_mem⟩ with hy'
  have huv : u' * v' = v' * u' := Subtype.ext u6_v6
  have huu : u' ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using u6_sq)
  have hvv : v' ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using v6_sq)
  have hy3 : y' ^ 3 = 1 := Subtype.ext y6_cube
  have hyu : y' * u' * y'⁻¹ = u' * v' := Subtype.ext y6_u6
  have hyv : y' * v' * y'⁻¹ = u' := Subtype.ext y6_v6
  set W : Subgroup (alternatingGroup (Fin 6)) := Subgroup.closure {u', v'} with hW
  have hu1 : ∀ w ∈ W, Commute u' w := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact Commute.refl _
      · exact huv
    | one => exact Commute.one_right _
    | mul a b _ _ ha hb => exact ha.mul_right hb
    | inv a _ ha => exact ha.inv_right
  have hv1 : ∀ w ∈ W, Commute v' w := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact huv.symm
      · exact Commute.refl _
    | one => exact Commute.one_right _
    | mul a b _ _ ha hb => exact ha.mul_right hb
    | inv a _ ha => exact ha.inv_right
  have hcomm : ∀ w ∈ W, ∀ w' ∈ W, Commute w w' := by
    intro w hw w' hw'
    induction hw' using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact (hu1 w hw).symm
      · exact (hv1 w hw).symm
    | one => exact Commute.one_right _
    | mul a b _ _ ha hb => exact ha.mul_right hb
    | inv a _ ha => exact ha.inv_right
  have hsq : ∀ w ∈ W, w ^ 2 = 1 := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact huu
      · exact hvv
    | one => simp
    | mul a b ha hb ha' hb' =>
      rw [(hcomm a ha b hb).mul_pow, ha', hb', one_mul]
    | inv a _ ha => rw [inv_pow, ha, inv_one]
  have hfwd : ∀ w ∈ W, y' * w * y'⁻¹ ∈ W := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · rw [hyu]; exact mul_mem (subset_closure (Or.inl rfl)) (subset_closure (Or.inr rfl))
      · rw [hyv]; exact subset_closure (Or.inl rfl)
    | one => simpa using W.one_mem
    | mul a b _ _ ha hb =>
      have : y' * (a * b) * y'⁻¹ = (y' * a * y'⁻¹) * (y' * b * y'⁻¹) := by group
      rw [this]; exact mul_mem ha hb
    | inv a _ ha =>
      have : y' * a⁻¹ * y'⁻¹ = (y' * a * y'⁻¹)⁻¹ := by group
      rw [this]; exact inv_mem ha
  refine ⟨y', hy3, ?_, W, ?_, hsq, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    exact y6_ne this
  · intro h
    have hu : u' ∈ W := subset_closure (Or.inl rfl)
    rw [h] at hu
    have := (Subgroup.mem_bot.1 hu)
    exact u6_ne (congrArg Subtype.val this)
  · rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => hfwd w hw, fun hw => ?_⟩
    have h2 := hfwd _ hw
    have h3 := hfwd _ h2
    have e3 : y' * y' * y' = 1 := by
      have : y' ^ 3 = y' * y' * y' := pow_three' y'
      rw [← this, hy3]
    have : y' * (y' * (y' * w * y'⁻¹) * y'⁻¹) * y'⁻¹ = (y' * y' * y') * w * (y' * y' * y')⁻¹ := by
      group
    rw [this, e3] at h3
    simpa using h3

theorem exists_three_normalizing_two_subgroup {X : Type*} [Group X] (I : Subgroup X)
    (φ : ↥I ≃* alternatingGroup (Fin 6)) :
    ∃ y : X, y ∈ I ∧ y ^ 3 = 1 ∧ y ≠ 1 ∧ ∃ W : Subgroup X, W ≤ I ∧ W ≠ ⊥ ∧ IsPGroup 2 W ∧
      y ∈ Subgroup.normalizer (W : Set X) := by
  obtain ⟨y₀, hy3, hy1, W₀, hW0, hWsq, hyN⟩ := A6_aux
  set ψ : alternatingGroup (Fin 6) →* X := I.subtype.comp φ.symm.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := I.subtype_injective.comp φ.symm.injective
  refine ⟨ψ y₀, (φ.symm y₀).2, by rw [← map_pow, hy3, map_one], ?_, W₀.map ψ, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hy1 (hψinj (by rw [h, map_one]))
  · rintro _ ⟨w, -, rfl⟩
    exact (φ.symm w).2
  · intro h
    apply hW0
    rw [eq_bot_iff]
    intro w hw
    have : ψ w ∈ (⊥ : Subgroup X) := h ▸ Subgroup.mem_map_of_mem ψ hw
    rw [Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (hψinj (by rw [this, map_one]))
  · intro g
    obtain ⟨w, hw, hgw⟩ := g.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    show (g : X) ^ (2 ^ 1) = 1
    rw [← hgw, pow_one, ← map_pow, hWsq w hw, map_one]
  · exact Subgroup.le_normalizer_map ψ (Subgroup.mem_map_of_mem ψ hyN)

theorem V4_aux {B : Type*} [Group B] (y u v : B) (hy3 : y ^ 3 = 1) (huv : u * v = v * u)
    (huu : u ^ 2 = 1) (hvv : v ^ 2 = 1) (hyu : y * u * y⁻¹ = v) (hyv : y * v * y⁻¹ = u * v)
    (hu1 : u ≠ 1) :
    ∃ W : Subgroup B, W = Subgroup.closure ({u, v} : Set B) ∧ W ≠ ⊥ ∧ (∀ w ∈ W, w ^ 2 = 1) ∧
      (∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w) ∧ y ∈ Subgroup.normalizer (W : Set B) := by
  set W : Subgroup B := Subgroup.closure {u, v} with hW
  have hu1' : ∀ w ∈ W, Commute u w := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact Commute.refl _
      · exact huv
    | one => exact Commute.one_right _
    | mul a b _ _ ha hb => exact ha.mul_right hb
    | inv a _ ha => exact ha.inv_right
  have hv1' : ∀ w ∈ W, Commute v w := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact huv.symm
      · exact Commute.refl _
    | one => exact Commute.one_right _
    | mul a b _ _ ha hb => exact ha.mul_right hb
    | inv a _ ha => exact ha.inv_right
  have hcomm : ∀ w ∈ W, ∀ w' ∈ W, Commute w w' := by
    intro w hw w' hw'
    induction hw' using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact (hu1' w hw).symm
      · exact (hv1' w hw).symm
    | one => exact Commute.one_right _
    | mul a b _ _ ha hb => exact ha.mul_right hb
    | inv a _ ha => exact ha.inv_right
  have hsq : ∀ w ∈ W, w ^ 2 = 1 := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact huu
      · exact hvv
    | one => simp
    | mul a b ha hb ha' hb' =>
      rw [(hcomm a ha b hb).mul_pow, ha', hb', one_mul]
    | inv a _ ha => rw [inv_pow, ha, inv_one]
  have hfwd : ∀ w ∈ W, y * w * y⁻¹ ∈ W := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · rw [hyu]; exact subset_closure (Or.inr rfl)
      · rw [hyv]; exact mul_mem (subset_closure (Or.inl rfl)) (subset_closure (Or.inr rfl))
    | one => simpa using W.one_mem
    | mul a b _ _ ha hb =>
      have : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [this]; exact mul_mem ha hb
    | inv a _ ha =>
      have : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      rw [this]; exact inv_mem ha
  refine ⟨W, rfl, ?_, hsq, fun w hw w' hw' => (hcomm w hw w' hw').eq, ?_⟩
  · intro h
    have hu : u ∈ W := subset_closure (Or.inl rfl)
    rw [h] at hu
    exact hu1 (Subgroup.mem_bot.1 hu)
  · rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => hfwd w hw, fun hw => ?_⟩
    have h2 := hfwd _ hw
    have h3 := hfwd _ h2
    have e3 : y * y * y = 1 := by
      have : y ^ 3 = y * y * y := pow_three' y
      rw [← this, hy3]
    have : y * (y * (y * w * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * w * (y * y * y)⁻¹ := by group
    rw [this, e3] at h3
    simpa using h3

theorem card_closure_pair_of_involutions {B : Type*} [Group B] (u v : B) (huv : u * v = v * u)
    (huu : u ^ 2 = 1) (hvv : v ^ 2 = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hne : u ≠ v) :
    Nat.card (Subgroup.closure ({u, v} : Set B)) = 4 := by
  set S : Set B := {1, u, v, u * v} with hS
  have hu' : u⁻¹ = u := by rw [inv_eq_iff_mul_eq_one, ← sq, huu]
  have hv' : v⁻¹ = v := by rw [inv_eq_iff_mul_eq_one, ← sq, hvv]
  have huv' : (u * v)⁻¹ = u * v := by rw [mul_inv_rev, hu', hv', huv]
  have hsub : (Subgroup.closure ({u, v} : Set B) : Set B) ⊆ S := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl <;> simp [hS]
    | one => simp [hS]
    | mul a b _ _ ha hb =>
      have e1 : u * u = 1 := by rw [← sq, huu]
      have e2 : v * v = 1 := by rw [← sq, hvv]
      have e3 : v * u = u * v := huv.symm
      have e4 : u * (u * v) = v := by rw [← mul_assoc, e1, one_mul]
      have e5 : v * (u * v) = u := by rw [← e3, ← mul_assoc, e2, one_mul]
      have e6 : u * v * u = v := by rw [mul_assoc, e3, ← mul_assoc, e1, one_mul]
      have e7 : u * v * v = u := by rw [mul_assoc, e2, mul_one]
      have e8 : u * v * (u * v) = 1 := by rw [← mul_assoc, e6, e2]
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
      rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
        simp [e1, e2, e3, e4, e5, e6, e7, e8]
    | inv a _ ha =>
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
      rcases ha with rfl | rfl | rfl | rfl <;> simp [hu', hv', huv']
  have hsup : S ⊆ (Subgroup.closure ({u, v} : Set B) : Set B) := by
    intro w hw
    simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hncard : S.ncard = 4 := by
    have h1 : (1 : B) ≠ u := hu1.symm
    have h2 : (1 : B) ≠ v := hv1.symm
    have h3 : (1 : B) ≠ u * v := by
      intro h
      apply hne
      have : u = v⁻¹ := eq_inv_of_mul_eq_one_left h.symm
      rw [this, hv']
    have h4 : u ≠ u * v := by
      intro h
      apply hv1
      exact (mul_eq_left.1 h.symm)
    have h5 : v ≠ u * v := by
      intro h
      apply hu1
      exact (mul_eq_right.1 h.symm)
    rw [hS, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair h5]
    · simp [hne, h4, hv1]
    · simp [h1, h2, h3]
  have : (Subgroup.closure ({u, v} : Set B) : Set B) = S := Set.Subset.antisymm hsub hsup
  rw [← hncard, ← this]
  exact Nat.card_coe_set_eq _

theorem S6_all : ∀ y : Perm (Fin 6), y ^ 3 = 1 → y ≠ 1 →
    ∃ u : Perm (Fin 6), u * u = 1 ∧ u ≠ 1 ∧ sign u = 1 ∧
      u * (y * u * y⁻¹) = (y * u * y⁻¹) * u ∧
      u * (y * u * y⁻¹) * (y * y * u * y⁻¹ * y⁻¹) = 1 := by
  decide +kernel

theorem A6_uv (y : alternatingGroup (Fin 6)) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    ∃ u v : alternatingGroup (Fin 6), u * v = v * u ∧ u ^ 2 = 1 ∧ v ^ 2 = 1 ∧
      y * u * y⁻¹ = v ∧ y * v * y⁻¹ = u * v ∧ u ≠ 1 := by
  obtain ⟨u, hu2, hu1, hus, hc, hp⟩ := S6_all (y : Perm (Fin 6))
    (by simpa using congrArg Subtype.val hy3) (fun h => hy1 (Subtype.ext h))
  have hueven : u ∈ alternatingGroup (Fin 6) := mem_alternatingGroup.2 hus
  set u' : alternatingGroup (Fin 6) := ⟨u, hueven⟩ with hu'
  set v' : alternatingGroup (Fin 6) := y * u' * y⁻¹ with hv'
  have hv'val : (v' : Perm (Fin 6)) = (y : Perm (Fin 6)) * u * (y : Perm (Fin 6))⁻¹ := rfl
  have huv : u' * v' = v' * u' := Subtype.ext (by simpa [hv'val] using hc)
  have huu : u' ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hu2)
  have hvv : v' ^ 2 = 1 := by
    have : v' ^ 2 = y * u' ^ 2 * y⁻¹ := by rw [hv']; exact conj_pow
    rw [this, huu]; group
  have hyu : y * u' * y⁻¹ = v' := rfl
  have hyv : y * v' * y⁻¹ = u' * v' := by
    have h3 : u' * v' * (y * y * u' * y⁻¹ * y⁻¹) = 1 := Subtype.ext (by simpa [hv'val] using hp)
    have e : y * v' * y⁻¹ = y * y * u' * y⁻¹ * y⁻¹ := by rw [hv']; group
    rw [e]
    have : y * y * u' * y⁻¹ * y⁻¹ = (u' * v')⁻¹ := eq_inv_of_mul_eq_one_right h3
    have hu'inv : u'⁻¹ = u' := by
      rw [inv_eq_iff_mul_eq_one, ← sq, huu]
    have hv'inv : v'⁻¹ = v' := by
      rw [inv_eq_iff_mul_eq_one, ← sq, hvv]
    rw [this, mul_inv_rev, hu'inv, hv'inv]
    exact huv.symm
  exact ⟨u', v', huv, huu, hvv, hyu, hyv, fun h => hu1 (congrArg Subtype.val h)⟩

theorem exists_V4_data {X : Type*} [Group X] (I : Subgroup X)
    (φ : ↥I ≃* alternatingGroup (Fin 6)) {y : X} (hyI : y ∈ I) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    ∃ u v : X, u ∈ I ∧ v ∈ I ∧ u * v = v * u ∧ u ^ 2 = 1 ∧ v ^ 2 = 1 ∧ y * u * y⁻¹ = v ∧
      y * v * y⁻¹ = u * v ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
  have hy3' : (φ ⟨y, hyI⟩) ^ 3 = 1 := by
    rw [← map_pow]; have : (⟨y, hyI⟩ : ↥I) ^ 3 = 1 := Subtype.ext hy3
    rw [this, map_one]
  have hy1' : φ ⟨y, hyI⟩ ≠ 1 := by
    intro h
    have : (⟨y, hyI⟩ : ↥I) = 1 := (map_eq_one_iff _ φ.injective).1 h
    exact hy1 (congrArg Subtype.val this)
  obtain ⟨u₀, v₀, huv, huu, hvv, hyu, hyv, hu1⟩ := A6_uv _ hy3' hy1'
  set ψ : alternatingGroup (Fin 6) →* X := I.subtype.comp φ.symm.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := I.subtype_injective.comp φ.symm.injective
  have hψy : ψ (φ ⟨y, hyI⟩) = y := by simp [hψ]
  have hu1X : ψ u₀ ≠ 1 := fun h => hu1 (hψinj (by rw [h, map_one]))
  have hyuX : y * ψ u₀ * y⁻¹ = ψ v₀ := by
    rw [← hψy, ← map_inv, ← map_mul, ← map_mul, hyu]
  have hyvX : y * ψ v₀ * y⁻¹ = ψ u₀ * ψ v₀ := by
    rw [← hψy, ← map_inv, ← map_mul, ← map_mul, hyv, map_mul]
  have hv1X : ψ v₀ ≠ 1 := by
    intro h
    apply hu1X
    have : y * ψ u₀ * y⁻¹ = 1 := by rw [hyuX, h]
    simpa using this
  have hneX : ψ u₀ ≠ ψ v₀ := by
    intro h
    apply hu1X
    have h1 : y * ψ v₀ * y⁻¹ = ψ u₀ * ψ v₀ := hyvX
    rw [← h] at h1
    have h2 : ψ u₀ ^ 2 = 1 := by rw [← map_pow, huu, map_one]
    rw [← sq, h2] at h1
    have h3 : y * ψ u₀ * y⁻¹ = 1 := h1
    simpa using h3
  refine ⟨ψ u₀, ψ v₀, (φ.symm u₀).2, (φ.symm v₀).2, by rw [← map_mul, ← map_mul, huv],
    by rw [← map_pow, huu, map_one], by rw [← map_pow, hvv, map_one], hyuX, hyvX, hu1X, hv1X,
    hneX⟩

open scoped commutatorElement in
theorem comm_V4 {B : Type*} [Group B] (y u v : B) (huu : u ^ 2 = 1) (hvv : v ^ 2 = 1)
    (hyu : y * u * y⁻¹ = v) (hyv : y * v * y⁻¹ = u * v) :
    ⁅v, y⁆ = u ∧ ⁅u, y⁆ = u * v := by
  have hinvu : u⁻¹ = u := by rw [inv_eq_iff_mul_eq_one, ← sq, huu]
  have hinvv : v⁻¹ = v := by rw [inv_eq_iff_mul_eq_one, ← sq, hvv]
  constructor
  · calc ⁅v, y⁆ = v * (y * v * y⁻¹)⁻¹ := by rw [commutatorElement_def]; group
      _ = v * (u * v)⁻¹ := by rw [hyv]
      _ = u⁻¹ := by rw [mul_inv_rev]; group
      _ = u := hinvu
  · calc ⁅u, y⁆ = u * (y * u * y⁻¹)⁻¹ := by rw [commutatorElement_def]; group
      _ = u * v⁻¹ := by rw [hyu]
      _ = u * v := by rw [hinvv]

end A6

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
