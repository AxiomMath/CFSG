module

public import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer2

@[expose] def AModel (m : ℕ) : Prop :=
  ∀ (S : Subgroup (alternatingGroup (Fin m))) (v : alternatingGroup (Fin m)),
    CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ → v ∈ S → (∀ s ∈ S, s * v = v * s) → orderOf v = 2 →
    numMoved (v : Equiv.Perm (Fin m)) = 8 →
    ∃ E : Subgroup (alternatingGroup (Fin m)),
      E ≤ S ∧ v ∈ E ∧ Nat.card E = 8 ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a * a = 1) ∧
      (∀ c, c * v = v * c → ∀ e ∈ E, c * e * c⁻¹ ∈ E) ∧
      (∀ y, y * y = 1 → y ≠ 1 → y * v = v * y → numMoved (y : Equiv.Perm (Fin m)) = 4 →
        numMoved ((y * v : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) = 4 → y ∈ E) ∧
      (∀ y ∈ E, y ≠ 1 → y ≠ v → numMoved (y : Equiv.Perm (Fin m)) = 4 ∧
        numMoved ((y * v : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) = 4) ∧
      (∀ y₁ ∈ E, ∀ y₂ ∈ E, y₁ ≠ 1 → y₁ ≠ v → y₂ ≠ 1 → y₂ ≠ v →
        ∃ c, c * v = v * c ∧ c * y₁ * c⁻¹ = y₂) ∧
      (∀ s ∈ S, (∀ t ∈ S, s * t = t * s) → s * s = 1 → s ≠ 1 → s = v) ∧
      (∃ s ∈ S, s * s = 1 ∧ s ∉ E)

section Epw

variable {m : ℕ}

theorem perm_apply_inv_self {α : Type*} (σ : Perm α) (p : α) : σ (σ⁻¹ p) = p := by simp

theorem perm_inv_apply_self {α : Type*} (σ : Perm α) (p : α) : σ⁻¹ (σ p) = p := by simp

theorem apply_apply_of_mul_self {v : alternatingGroup (Fin m)} (hv : v * v = 1) (p : Fin m) :
    (v : Perm (Fin m)) ((v : Perm (Fin m)) p) = p := by
  have := congrArg (fun a : alternatingGroup (Fin m) => (a : Perm (Fin m)) p) hv
  simpa [Perm.mul_apply] using this

@[expose] def Epw (v : alternatingGroup (Fin m)) (hv : v * v = 1) :
    Subgroup (alternatingGroup (Fin m)) where
  carrier := {g | ∀ p, (g : Perm (Fin m)) p = p ∨ (g : Perm (Fin m)) p = (v : Perm (Fin m)) p}
  one_mem' := fun _ => Or.inl rfl
  mul_mem' := by
    intro g h hg hh p
    have hvp := apply_apply_of_mul_self hv p
    show (g : Perm (Fin m)) ((h : Perm (Fin m)) p) = p ∨
      (g : Perm (Fin m)) ((h : Perm (Fin m)) p) = (v : Perm (Fin m)) p
    rcases hh p with h1 | h1
    · rw [h1]
      exact hg p
    · rw [h1]
      rcases hg ((v : Perm (Fin m)) p) with h2 | h2
      · exact Or.inr h2
      · exact Or.inl (h2.trans hvp)
  inv_mem' := by
    intro g hg p
    show ((g : Perm (Fin m))⁻¹) p = p ∨ ((g : Perm (Fin m))⁻¹) p = (v : Perm (Fin m)) p
    have hq : (g : Perm (Fin m)) (((g : Perm (Fin m))⁻¹) p) = p := perm_apply_inv_self _ _
    rcases hg (((g : Perm (Fin m))⁻¹) p) with h1 | h1
    · left
      rw [h1] at hq
      exact hq
    · right
      rw [h1] at hq
      have := apply_apply_of_mul_self hv (((g : Perm (Fin m))⁻¹) p)
      rw [hq] at this
      exact this.symm

theorem mem_Epw {v : alternatingGroup (Fin m)} {hv : v * v = 1} {g : alternatingGroup (Fin m)} :
    g ∈ Epw v hv ↔
      ∀ p, (g : Perm (Fin m)) p = p ∨ (g : Perm (Fin m)) p = (v : Perm (Fin m)) p := Iff.rfl

theorem v_mem_Epw {v : alternatingGroup (Fin m)} (hv : v * v = 1) : v ∈ Epw v hv :=
  fun _ => Or.inr rfl

theorem Epw_sq {v : alternatingGroup (Fin m)} {hv : v * v = 1} {g : alternatingGroup (Fin m)}
    (hg : g ∈ Epw v hv) : g * g = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  show (g : Perm (Fin m)) ((g : Perm (Fin m)) p) = p
  rcases hg p with h1 | h1
  · rw [h1, h1]
  · rw [h1]
    rcases hg ((v : Perm (Fin m)) p) with h2 | h2
    · have h3 : (g : Perm (Fin m)) ((v : Perm (Fin m)) p) = (g : Perm (Fin m)) p := by rw [h2, h1]
      have hp := (g : Perm (Fin m)).injective h3
      rw [h2]
      exact hp
    · rw [h2]
      exact apply_apply_of_mul_self hv p

theorem Epw_comm {v : alternatingGroup (Fin m)} {hv : v * v = 1} {g h : alternatingGroup (Fin m)}
    (hg : g ∈ Epw v hv) (hh : h ∈ Epw v hv) : g * h = h * g := by
  have h1 := Epw_sq hg
  have h2 := Epw_sq hh
  have h3 := Epw_sq ((Epw v hv).mul_mem hg hh)
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right h1
  have hhi : h⁻¹ = h := inv_eq_of_mul_eq_one_right h2
  have hgh : (g * h)⁻¹ = g * h := inv_eq_of_mul_eq_one_right h3
  calc g * h = (g * h)⁻¹ := hgh.symm
    _ = h⁻¹ * g⁻¹ := mul_inv_rev g h
    _ = h * g := by rw [hgi, hhi]

theorem Epw_conj_mem {v : alternatingGroup (Fin m)} {hv : v * v = 1} {c : alternatingGroup (Fin m)}
    (hc : c * v = v * c) {e : alternatingGroup (Fin m)} (he : e ∈ Epw v hv) :
    c * e * c⁻¹ ∈ Epw v hv := by
  intro p
  show (c : Perm (Fin m)) ((e : Perm (Fin m)) (((c : Perm (Fin m))⁻¹) p)) = p ∨
    (c : Perm (Fin m)) ((e : Perm (Fin m)) (((c : Perm (Fin m))⁻¹) p)) = (v : Perm (Fin m)) p
  have hcv : ∀ q, (c : Perm (Fin m)) ((v : Perm (Fin m)) q) = (v : Perm (Fin m)) ((c : Perm (Fin m)) q) := by
    intro q
    exact congrArg (fun a : alternatingGroup (Fin m) => (a : Perm (Fin m)) q) hc
  rcases he (((c : Perm (Fin m))⁻¹) p) with h1 | h1
  · left
    rw [h1]
    exact perm_apply_inv_self _ _
  · right
    rw [h1, hcv, perm_apply_inv_self]

theorem mem_Epw_of_numMoved {v : alternatingGroup (Fin m)} (hv : v * v = 1)
    (hv8 : numMoved (v : Perm (Fin m)) = 8) {y : alternatingGroup (Fin m)} (hy2 : y * y = 1)
    (hyv : y * v = v * y) (hy4 : numMoved (y : Perm (Fin m)) = 4)
    (hyv4 : numMoved ((y * v : alternatingGroup (Fin m)) : Perm (Fin m)) = 4) : y ∈ Epw v hv := by
  by_contra hne
  rw [mem_Epw] at hne
  push Not at hne
  obtain ⟨p₀, hp₀1, hp₀2⟩ := hne
  have hyy : ∀ q, (y : Perm (Fin m)) ((y : Perm (Fin m)) q) = q := apply_apply_of_mul_self hy2
  have hyvq : ∀ q, (y : Perm (Fin m)) ((v : Perm (Fin m)) q) = (v : Perm (Fin m)) ((y : Perm (Fin m)) q) := by
    intro q
    exact congrArg (fun a : alternatingGroup (Fin m) => (a : Perm (Fin m)) q) hyv
  set Sy : Finset (Fin m) := Finset.univ.filter fun a => (y : Perm (Fin m)) a ≠ a with hSy
  set Syv : Finset (Fin m) :=
    Finset.univ.filter fun a => ((y * v : alternatingGroup (Fin m)) : Perm (Fin m)) a ≠ a with hSyv
  set Sv : Finset (Fin m) := Finset.univ.filter fun a => (v : Perm (Fin m)) a ≠ a with hSv
  have hcy : Sy.card = 4 := hy4
  have hcyv : Syv.card = 4 := hyv4
  have hcv : Sv.card = 8 := hv8
  have hsub : Sv ⊆ Sy ∪ Syv := by
    intro p hp
    rw [hSv, Finset.mem_filter] at hp
    rw [Finset.mem_union]
    by_cases hyp : (y : Perm (Fin m)) p = p
    · right
      rw [hSyv, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      show (y : Perm (Fin m)) ((v : Perm (Fin m)) p) ≠ p
      rw [hyvq, hyp]
      exact hp.2
    · left
      rw [hSy, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hyp⟩
  have hp₀mem : p₀ ∈ Sy ∩ Syv := by
    rw [Finset.mem_inter, hSy, hSyv, Finset.mem_filter, Finset.mem_filter]
    refine ⟨⟨Finset.mem_univ _, hp₀1⟩, Finset.mem_univ _, ?_⟩
    intro h
    have h' : (y : Perm (Fin m)) ((v : Perm (Fin m)) p₀) = p₀ := h
    have := congrArg (fun q => (y : Perm (Fin m)) q) h'
    simp only [hyy] at this
    exact hp₀2 this.symm
  have h1 := Finset.card_union_add_card_inter Sy Syv
  have h2 : 0 < (Sy ∩ Syv).card := Finset.card_pos.2 ⟨p₀, hp₀mem⟩
  have h3 := Finset.card_le_card hsub
  omega

theorem Epw_numMoved (hm : m ≤ 11) {v : alternatingGroup (Fin m)} (hv : v * v = 1)
    (hv8 : numMoved (v : Perm (Fin m)) = 8) {y : alternatingGroup (Fin m)} (hy : y ∈ Epw v hv)
    (hy1 : y ≠ 1) (hyv : y ≠ v) : numMoved (y : Perm (Fin m)) = 4 := by
  have hy2 := Epw_sq hy
  have hord : orderOf y = 2 := orderOf_eq_prime hy2 hy1
  rcases numMoved_eq_of_involution_alternating m hm y hord with h4 | h8
  · exact h4
  · exfalso
    apply hyv
    set Sy : Finset (Fin m) := Finset.univ.filter fun a => (y : Perm (Fin m)) a ≠ a with hSy
    set Sv : Finset (Fin m) := Finset.univ.filter fun a => (v : Perm (Fin m)) a ≠ a with hSv
    have hcy : Sy.card = 8 := h8
    have hcv : Sv.card = 8 := hv8
    have hsub : Sy ⊆ Sv := by
      intro p hp
      rw [hSy, Finset.mem_filter] at hp
      rw [hSv, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hy p with h1 | h1
      · exact absurd h1 hp.2
      · rw [← h1]
        exact hp.2
    have heq : Sy = Sv := Finset.eq_of_subset_of_card_le hsub (by rw [hcy, hcv])
    apply Subtype.ext
    apply Equiv.ext
    intro p
    by_cases hp : (v : Perm (Fin m)) p = p
    · have hpS : p ∉ Sy := by
        rw [heq, hSv, Finset.mem_filter]
        exact fun h => h.2 hp
      rw [hSy, Finset.mem_filter] at hpS
      push Not at hpS
      rw [hp]
      exact hpS (Finset.mem_univ _)
    · have hpS : p ∈ Sy := by
        rw [heq, hSv, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hp⟩
      rw [hSy, Finset.mem_filter] at hpS
      rcases hy p with h1 | h1
      · exact absurd h1 hpS.2
      · exact h1

theorem Epw_numMoved' (hm : m ≤ 11) {v : alternatingGroup (Fin m)} (hv : v * v = 1)
    (hv8 : numMoved (v : Perm (Fin m)) = 8) {y : alternatingGroup (Fin m)} (hy : y ∈ Epw v hv)
    (hy1 : y ≠ 1) (hyv : y ≠ v) :
    numMoved (y : Perm (Fin m)) = 4 ∧
      numMoved ((y * v : alternatingGroup (Fin m)) : Perm (Fin m)) = 4 := by
  refine ⟨Epw_numMoved hm hv hv8 hy hy1 hyv, ?_⟩
  have hyvE : y * v ∈ Epw v hv := (Epw v hv).mul_mem hy (v_mem_Epw hv)
  refine Epw_numMoved hm hv hv8 hyvE ?_ ?_
  · intro h
    apply hyv
    have : y = v⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact inv_eq_of_mul_eq_one_right hv
  · intro h
    apply hy1
    simpa using h

theorem mem_Epw_iff_conj {y₀ v k : alternatingGroup (Fin m)} (hy : y₀ * y₀ = 1) (hv : v * v = 1)
    (hvk : k * v * k⁻¹ = y₀) {x : alternatingGroup (Fin m)} :
    x ∈ Epw v hv ↔ k * x * k⁻¹ ∈ Epw y₀ hy := by
  have key : ∀ (a b : alternatingGroup (Fin m)) (q : Fin m),
      (((a * b * a⁻¹ : alternatingGroup (Fin m)) : Perm (Fin m))) q =
        (a : Perm (Fin m)) ((b : Perm (Fin m)) (((a : Perm (Fin m))⁻¹) q)) := fun a b q => rfl
  have hy₀ : ∀ q, (y₀ : Perm (Fin m)) q =
      (k : Perm (Fin m)) ((v : Perm (Fin m)) (((k : Perm (Fin m))⁻¹) q)) := by
    intro q
    rw [← hvk, key]
  constructor
  · intro hx p
    show (k : Perm (Fin m)) ((x : Perm (Fin m)) (((k : Perm (Fin m))⁻¹) p)) = p ∨
      (k : Perm (Fin m)) ((x : Perm (Fin m)) (((k : Perm (Fin m))⁻¹) p)) = (y₀ : Perm (Fin m)) p
    rw [hy₀]
    rcases hx (((k : Perm (Fin m))⁻¹) p) with h1 | h1
    · left
      rw [h1]
      exact perm_apply_inv_self _ _
    · right
      rw [h1]
  · intro hx p
    show (x : Perm (Fin m)) p = p ∨ (x : Perm (Fin m)) p = (v : Perm (Fin m)) p
    have h1 := hx ((k : Perm (Fin m)) p)
    have h2 : ((k * x * k⁻¹ : alternatingGroup (Fin m)) : Perm (Fin m)) ((k : Perm (Fin m)) p) =
        (k : Perm (Fin m)) ((x : Perm (Fin m)) p) := by
      rw [key, perm_inv_apply_self]
    rw [h2, hy₀, perm_inv_apply_self] at h1
    rcases h1 with h3 | h3
    · left
      exact (k : Perm (Fin m)).injective h3
    · right
      exact (k : Perm (Fin m)).injective h3

theorem Epw_map_conj {y₀ v k : alternatingGroup (Fin m)} (hy : y₀ * y₀ = 1) (hv : v * v = 1)
    (hvk : k * v * k⁻¹ = y₀) :
    (Epw v hv).map (MulAut.conj k).toMonoidHom = Epw y₀ hy := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_Epw_iff_conj hy hv hvk).1 hx
  · intro hz
    refine ⟨k⁻¹ * z * k, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    refine (mem_Epw_iff_conj hy hv hvk).2 ?_
    have h3 : k * (k⁻¹ * z * k) * k⁻¹ = z := by group
    rw [h3]
    exact hz

theorem Epw_le_of_sylow {v : alternatingGroup (Fin m)} (hv : v * v = 1)
    {S : Subgroup (alternatingGroup (Fin m))} (hS : IsSylowOf 2 S ⊤)
    (hvc : ∀ s ∈ S, s * v = v * s) : Epw v hv ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 ↥(Epw v hv) := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have := Epw_sq g.2
    simpa [sq] using this
  have hSnorm : S ≤ normalizer ((Epw v hv : Subgroup (alternatingGroup (Fin m))) : Set _) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro e
    constructor
    · intro he
      exact Epw_conj_mem (hvc s hs) he
    · intro he
      have hc : s⁻¹ * v = v * s⁻¹ := by
        have := hvc s hs
        calc s⁻¹ * v = s⁻¹ * (v * s) * s⁻¹ := by group
          _ = s⁻¹ * (s * v) * s⁻¹ := by rw [this]
          _ = v * s⁻¹ := by group
      have h2 := Epw_conj_mem (hv := hv) hc he
      have h3 : s⁻¹ * (s * e * s⁻¹) * s⁻¹⁻¹ = e := by group
      rwa [h3] at h2
  have hsup := hE2.to_sup_of_normal_left' hS.isPGroup hSnorm
  have heq := hS.eq_of_le le_sup_right le_top hsup
  exact le_sup_left.trans heq.le

theorem card_Epw_of_list {v : alternatingGroup (Fin m)} (hv : v * v = 1) (L : List (Perm (Fin m)))
    (hnd : L.Nodup) (hL : ∀ q ∈ L, sign q = 1)
    (hmem : ∀ g : alternatingGroup (Fin m), g ∈ Epw v hv ↔ (g : Perm (Fin m)) ∈ L) :
    Nat.card (Epw v hv) = L.length := by
  classical
  have e : Epw v hv ≃ {q : Perm (Fin m) // q ∈ L} :=
    { toFun := fun g => ⟨g.1.1, (hmem g.1).1 g.2⟩
      invFun := fun q => ⟨⟨q.1, mem_alternatingGroup.2 (hL q.1 q.2)⟩, (hmem _).2 q.2⟩
      left_inv := fun g => rfl
      right_inv := fun q => rfl }
  rw [Nat.card_congr e]
  have h2 : Nat.card {q : Perm (Fin m) // q ∈ L} = Nat.card (L.toFinset) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun q => by simp)
  rw [h2, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd]

theorem pair_cases {α : Type*} (g : Perm α) {a b : α} (hab : a ≠ b) (ha : g a = a ∨ g a = b)
    (hb : g b = b ∨ g b = a) : (g a = a ∧ g b = b) ∨ (g a = b ∧ g b = a) := by
  rcases ha with h1 | h1 <;> rcases hb with h2 | h2
  · exact Or.inl ⟨h1, h2⟩
  · exact absurd (g.injective (h1.trans h2.symm)) hab
  · exact absurd (g.injective (h1.trans h2.symm)) hab
  · exact Or.inr ⟨h1, h2⟩

end Epw


section Reduction

variable {m : ℕ}

theorem amodel_of_model (hm : m ≤ 11) (S₀ : Subgroup (alternatingGroup (Fin m)))
    (hS₀ : IsSylowOf 2 S₀ ⊤) (y₀ : alternatingGroup (Fin m)) (hy₀sq : y₀ * y₀ = 1)
    (hZ : ∀ s ∈ S₀, (∀ t ∈ S₀, s * t = t * s) → s * s = 1 → s ≠ 1 → s = y₀)
    (s₁ : alternatingGroup (Fin m)) (hs₁S : s₁ ∈ S₀) (hs₁sq : s₁ * s₁ = 1) (p₁ : Fin m)
    (hp₁ : (s₁ : Perm (Fin m)) p₁ ≠ p₁) (hp₁' : (s₁ : Perm (Fin m)) p₁ ≠ (y₀ : Perm (Fin m)) p₁)
    (hcard : Nat.card (Epw y₀ hy₀sq) = 8)
    (htrans : ∀ z₁ ∈ Epw y₀ hy₀sq, ∀ z₂ ∈ Epw y₀ hy₀sq, z₁ ≠ 1 → z₁ ≠ y₀ → z₂ ≠ 1 → z₂ ≠ y₀ →
      ∃ c : alternatingGroup (Fin m), c * y₀ = y₀ * c ∧ c * z₁ * c⁻¹ = z₂) :
    AModel m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S v hS hvS hvc hvord hvnm
  have hvsq : v * v = 1 := by
    have h1 := pow_orderOf_eq_one v
    rw [hvord, sq] at h1
    exact h1
  have hv1 : v ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hvord
    omega
  obtain ⟨k, -, hk⟩ := hS.exists_mem_conj hS₀
  have hSmem : ∀ s, s ∈ S ↔ k * s * k⁻¹ ∈ S₀ := by
    intro s
    have := hk (k * s * k⁻¹)
    have h2 : k⁻¹ * (k * s * k⁻¹) * k = s := by group
    rw [h2] at this
    exact this.symm
  have hcentre : ∀ s ∈ S, (∀ t ∈ S, s * t = t * s) → s * s = 1 → s ≠ 1 →
      k * s * k⁻¹ = y₀ := by
    intro s hs hsc hss hs1
    refine hZ (k * s * k⁻¹) ((hSmem s).1 hs) (fun t ht => ?_) ?_ ?_
    · have h1 := hsc (k⁻¹ * t * k) ((hk t).1 ht)
      calc k * s * k⁻¹ * t = k * (s * (k⁻¹ * t * k)) * k⁻¹ := by group
        _ = k * ((k⁻¹ * t * k) * s) * k⁻¹ := by rw [h1]
        _ = t * (k * s * k⁻¹) := by group
    · calc k * s * k⁻¹ * (k * s * k⁻¹) = k * (s * s) * k⁻¹ := by group
        _ = 1 := by rw [hss]; group
    · intro h1
      apply hs1
      have : s = k⁻¹ * (k * s * k⁻¹) * k := by group
      rw [this, h1]
      group
  have hvy : k * v * k⁻¹ = y₀ := hcentre v hvS (fun t ht => (hvc t ht).symm) hvsq hv1
  have hmem := fun x => mem_Epw_iff_conj (m := m) hy₀sq hvsq hvy (x := x)
  refine ⟨Epw v hvsq, Epw_le_of_sylow hvsq hS hvc, v_mem_Epw hvsq, ?_,
    fun a ha b hb => Epw_comm ha hb, fun a ha => Epw_sq ha,
    fun c hc e he => Epw_conj_mem hc he, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h1 := Epw_map_conj hy₀sq hvsq hvy
    have h2 : Nat.card ((Epw v hvsq).map (MulAut.conj k).toMonoidHom) = 8 := by
      rw [h1]
      exact hcard
    rwa [Subgroup.card_map_of_injective (MulAut.conj k).injective] at h2
  · intro y hy2 hy1 hyv hy4 hyv4
    exact mem_Epw_of_numMoved hvsq hvnm hy2 hyv hy4 hyv4
  · intro y hy hy1 hyv
    exact Epw_numMoved' hm hvsq hvnm hy hy1 hyv
  · intro y₁ hy₁ y₂ hy₂ h11 h1v h21 h2v
    have hne : ∀ y : alternatingGroup (Fin m), y ≠ 1 → y ≠ v →
        k * y * k⁻¹ ≠ 1 ∧ k * y * k⁻¹ ≠ y₀ := by
      intro y hy1 hyv
      refine ⟨fun h1 => hy1 ?_, fun h1 => hyv ?_⟩
      · have : y = k⁻¹ * (k * y * k⁻¹) * k := by group
        rw [this, h1]
        group
      · rw [← hvy] at h1
        exact mul_left_cancel (mul_right_cancel h1)
    obtain ⟨c, hc1, hc2⟩ := htrans _ ((hmem _).1 hy₁) _ ((hmem _).1 hy₂) (hne y₁ h11 h1v).1
      (hne y₁ h11 h1v).2 (hne y₂ h21 h2v).1 (hne y₂ h21 h2v).2
    refine ⟨k⁻¹ * c * k, ?_, ?_⟩
    · have hv' : v = k⁻¹ * y₀ * k := by rw [← hvy]; group
      rw [hv']
      calc k⁻¹ * c * k * (k⁻¹ * y₀ * k) = k⁻¹ * (c * y₀) * k := by group
        _ = k⁻¹ * (y₀ * c) * k := by rw [hc1]
        _ = k⁻¹ * y₀ * k * (k⁻¹ * c * k) := by group
    · have h3 : k⁻¹ * c * k * y₁ * (k⁻¹ * c * k)⁻¹ = k⁻¹ * (c * (k * y₁ * k⁻¹) * c⁻¹) * k := by
        group
      rw [h3, hc2]
      group
  · intro s hs hsc hss hs1
    have h1 := hcentre s hs hsc hss hs1
    rw [← hvy] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  · have h2 : k * (k⁻¹ * s₁ * k) * k⁻¹ = s₁ := by group
    refine ⟨k⁻¹ * s₁ * k, (hSmem _).2 (by rw [h2]; exact hs₁S), ?_, ?_⟩
    · calc k⁻¹ * s₁ * k * (k⁻¹ * s₁ * k) = k⁻¹ * (s₁ * s₁) * k := by group
        _ = 1 := by rw [hs₁sq]; group
    · intro hE
      have h1 := (hmem _).1 hE
      rw [h2] at h1
      rcases h1 p₁ with h3 | h3
      · exact hp₁ h3
      · exact hp₁' h3

end Reduction

end CFSG.GH74.GLS.C3.Layer1.Bk
