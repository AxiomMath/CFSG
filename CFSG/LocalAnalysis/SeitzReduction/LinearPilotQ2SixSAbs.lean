module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSOne

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup

variable {G : Type*} [Group G]

theorem card_inf_centralizer_conj_eq_sixS {W : Subgroup G} {g : G} (hg : g ∈ normalizer (W : Set G))
    (z : G) :
    Nat.card (W ⊓ centralizer ({g * z * g⁻¹} : Set G) : Subgroup G) =
      Nat.card (W ⊓ centralizer ({z} : Set G) : Subgroup G) := by
  have h : (W ⊓ centralizer ({z} : Set G)).map (MulAut.conj g).toMonoidHom =
      W ⊓ centralizer ({g * z * g⁻¹} : Set G) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨w, ⟨hw, hwz⟩, rfl⟩
      refine ⟨(mem_normalizer_iff.1 hg w).1 hw, ?_⟩
      calc g * w * g⁻¹ * (g * z * g⁻¹) = g * (w * z) * g⁻¹ := by group
        _ = g * (z * w) * g⁻¹ := by rw [hwz]
        _ = g * z * g⁻¹ * (g * w * g⁻¹) := by group
    · rintro ⟨hx, hxz⟩
      refine ⟨g⁻¹ * x * g, ⟨?_, ?_⟩, by group⟩
      · refine (mem_normalizer_iff.1 hg (g⁻¹ * x * g)).2 ?_
        rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
      · calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [hxz]
          _ = z * (g⁻¹ * x * g) := by group
  rw [← h, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem card_inf_centralizer_conj_mul_eq_sixS {W : Subgroup G} {g t : G}
    (hg : g ∈ normalizer (W : Set G)) (hgt : g * t = t * g) (h : G) :
    Nat.card (W ⊓ centralizer ({g * h * g⁻¹ * t} : Set G) : Subgroup G) =
      Nat.card (W ⊓ centralizer ({h * t} : Set G) : Subgroup G) := by
  have e : g * h * g⁻¹ * t = g * (h * t) * g⁻¹ := by
    have h1 : g⁻¹ * t = t * g⁻¹ := by
      calc g⁻¹ * t = g⁻¹ * (t * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * t) * g⁻¹ := by rw [hgt]
        _ = t * g⁻¹ := by group
    calc g * h * g⁻¹ * t = g * h * (g⁻¹ * t) := by group
      _ = g * h * (t * g⁻¹) := by rw [h1]
      _ = g * (h * t) * g⁻¹ := by group
  rw [e, card_inf_centralizer_conj_eq_sixS hg]

theorem exists_commutator_subgroup_card_le_sixS [Finite G] {W : Subgroup G}
    (hW : ∀ w ∈ W, w * w = 1)
    {x : G} (hxW : x ∈ normalizer (W : Set G)) {m : ℕ}
    (hroot : Nat.card W ≤ m * Nat.card (W ⊓ centralizer ({x} : Set G) : Subgroup G)) :
    ∃ M : Subgroup G, (∀ w ∈ W, x * w * x⁻¹ * w⁻¹ ∈ M) ∧ M ≤ W ∧ Nat.card M ≤ m := by
  have hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW hv hw
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
  refine ⟨M, fun w hw => ⟨φ ⟨w, hw⟩, ⟨_, rfl⟩, rfl⟩, map_subtype_le _, ?_⟩
  have hpos : 0 < Nat.card (W ⊓ centralizer ({x} : Set G) : Subgroup G) := Nat.card_pos
  rw [hMc]
  rw [hcard] at hroot
  exact Nat.le_of_mul_le_mul_right hroot hpos

theorem card_sup_le_mul_of_le_of_exponent_two_sixS [Finite G] {W M N : Subgroup G}
    (hW : ∀ w ∈ W, w * w = 1) (hMW : M ≤ W) (hNW : N ≤ W) :
    Nat.card (M ⊔ N : Subgroup G) ≤ Nat.card M * Nat.card N := by
  have hN : N ≤ normalizer (M : Set G) := by
    rw [le_normalizer_iff]
    intro b hb a ha
    rw [mul_comm_of_forall_mul_self_eq_one hW (hNW hb) (hMW ha), mul_inv_cancel_right]
    exact ha
  have h := card_sup_mul_card_inf_of_le_normalizer_sOne hN
  have hpos : 0 < Nat.card (M ⊓ N : Subgroup G) := Nat.card_pos
  calc Nat.card (M ⊔ N : Subgroup G) = Nat.card (M ⊔ N : Subgroup G) * 1 := (mul_one _).symm
    _ ≤ Nat.card (M ⊔ N : Subgroup G) * Nat.card (M ⊓ N : Subgroup G) :=
        Nat.mul_le_mul_left _ hpos
    _ = _ := h

theorem card_inf_centralizer_mul_mul_le_of_root_pair_sixS [Finite G] {W : Subgroup G} {t x y : G}
    (hW : ∀ w ∈ W, w * w = 1) (ht : t * t = 1) (htW : t ∈ normalizer (W : Set G))
    (hWV : Nat.card W = Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2)
    (hxW : x ∈ normalizer (W : Set G)) (hyW : y ∈ normalizer (W : Set G))
    (hxt : x * t = t * x) (hyt : y * t = t * y) (hxy : x * y = y * x)
    (hx2 : x * x = 1) (hy2 : y * y = 1)
    (hx : Nat.card W ≤ 4 * Nat.card (W ⊓ centralizer ({x} : Set G) : Subgroup G))
    (hy : Nat.card W ≤ 4 * Nat.card (W ⊓ centralizer ({y} : Set G) : Subgroup G))
    (hV : 4 * Nat.card (W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({x * y} : Set G) :
      Subgroup G) ≤ Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G)) :
    Nat.card (W ⊓ centralizer ({x * y * t} : Set G) : Subgroup G) ≤
      Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  have hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW hv hw
  set V : Subgroup G := W ⊓ centralizer ({t} : Set G) with hVdef
  have hhW : x * y ∈ normalizer (W : Set G) := mul_mem hxW hyW
  have hht : x * y * t = t * (x * y) := by
    rw [mul_assoc, hyt, ← mul_assoc, hxt, mul_assoc]
  have hh2 : x * y * (x * y) = 1 := by
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx2, hy2, one_mul]
  obtain ⟨Mx, hMx, hMxW, hMxc⟩ := exists_commutator_subgroup_card_le_sixS hW hxW hx
  obtain ⟨My, hMy, hMyW, hMyc⟩ := exists_commutator_subgroup_card_le_sixS hW hyW hy
  set B : Subgroup G := Mx ⊔ My with hB
  have hBW : B ≤ W := sup_le hMxW hMyW
  have hBc : Nat.card B ≤ 16 :=
    (card_sup_le_mul_of_le_of_exponent_two_sixS hW hMxW hMyW).trans (Nat.mul_le_mul hMxc hMyc)
  have hhB : ∀ w ∈ W, x * y * w * (x * y)⁻¹ * w⁻¹ ∈ B := by
    intro w hw
    have hxw : x * w * x⁻¹ ∈ W := (mem_normalizer_iff.1 hxW w).1 hw
    have hinv : x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hxy]
    have e : x * y * w * (x * y)⁻¹ * w⁻¹ =
        (y * (x * w * x⁻¹) * y⁻¹ * (x * w * x⁻¹)⁻¹) * (x * w * x⁻¹ * w⁻¹) := by
      calc x * y * w * (x * y)⁻¹ * w⁻¹ = (x * y) * w * (y⁻¹ * x⁻¹) * w⁻¹ := by group
        _ = (y * x) * w * (x⁻¹ * y⁻¹) * w⁻¹ := by rw [hxy, hinv]
        _ = _ := by group
    rw [e]
    exact mul_mem (mem_sup_right (hMy _ hxw)) (mem_sup_left (hMx w hw))
  have h1 := card_inf_centralizer_mul_le_card_mul hW ht htW hhW hh2 hhB
  have hABt : ∀ a ∈ B, t * a * t⁻¹ * a⁻¹ ∈ W := fun a ha => tcomm_mem htW (hBW ha)
  set ψ := tcommHom hWc htW hBW hABt with hψ
  have hkerψ : Nat.card ψ.ker = Nat.card (B ⊓ centralizer ({t} : Set G) : Subgroup G) :=
    card_ker_tcommHom hWc htW hBW hABt inf_le_left fun a ha =>
      ⟨fun h => (Subgroup.mem_inf.1 h).2, fun h => Subgroup.mem_inf.2 ⟨ha, h⟩⟩
  have hcardB := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hkerψ] at hcardB
  have hVW : V ≤ W := inf_le_left
  have hABh : ∀ a ∈ V, x * y * a * (x * y)⁻¹ * a⁻¹ ∈ W := fun a ha => tcomm_mem hhW (hVW ha)
  set χ := tcommHom (t := x * y) hWc hhW hVW hABh with hχ
  have hkerχ : Nat.card χ.ker =
      Nat.card (W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({x * y} : Set G) : Subgroup G) :=
    card_ker_tcommHom hWc hhW hVW hABh inf_le_left fun a ha =>
      ⟨fun h => (Subgroup.mem_inf.1 h).2, fun h => Subgroup.mem_inf.2 ⟨ha, h⟩⟩
  have hcardV := Subgroup.card_eq_card_quotient_mul_card_subgroup χ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv, hkerχ] at hcardV
  have hsurj := tcomm_surjective_of_card hW ht htW hWV
  have hrange : χ.range.map W.subtype ≤ ψ.range.map W.subtype := by
    rintro _ ⟨_, ⟨⟨v, hv⟩, rfl⟩, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hsurj v hv
    refine ⟨ψ ⟨x * y * w * (x * y)⁻¹ * w⁻¹, hhB w hw⟩, ⟨_, rfl⟩, ?_⟩
    change t * (x * y * w * (x * y)⁻¹ * w⁻¹) * t⁻¹ * (x * y * w * (x * y)⁻¹ * w⁻¹)⁻¹ =
      x * y * (t * w * t⁻¹ * w⁻¹) * (x * y)⁻¹ * (t * w * t⁻¹ * w⁻¹)⁻¹
    exact tcomm_commutator_eq hWc htW hhW hht hw
  have hrc : Nat.card χ.range ≤ Nat.card ψ.range := by
    have h2 := Subgroup.card_le_of_le hrange
    rwa [Subgroup.card_map_of_injective W.subtype_injective,
      Subgroup.card_map_of_injective W.subtype_injective] at h2
  have hle : Nat.card (W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({x * y} : Set G) ⊓ B :
      Subgroup G) ≤ Nat.card (B ⊓ centralizer ({t} : Set G) : Subgroup G) :=
    Subgroup.card_le_of_le fun z hz => Subgroup.mem_inf.2
      ⟨(Subgroup.mem_inf.1 hz).2,
        (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hz).1).1).2⟩
  set a := Nat.card (W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({x * y} : Set G) : Subgroup G)
  set b := Nat.card (B ⊓ centralizer ({t} : Set G) : Subgroup G)
  set v := Nat.card V
  set r := Nat.card ψ.range
  set s := Nat.card χ.range
  have hv : v = s * a := hcardV
  have hB16 : r * b ≤ 16 := hcardB ▸ hBc
  have hvpos : 0 < v := Nat.card_pos
  have hgoal : a * b * v ≤ v * v := by
    calc a * b * v = a * b * (s * a) := by rw [hv]
      _ ≤ a * b * (r * a) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hrc)
      _ = a * a * (r * b) := by ring
      _ ≤ a * a * 16 := Nat.mul_le_mul_left _ hB16
      _ = (4 * a) * (4 * a) := by ring
      _ ≤ v * v := Nat.mul_le_mul hV hV
  have hab : a * b ≤ v := Nat.le_of_mul_le_mul_right (by rwa [mul_comm v v] at hgoal) hvpos
  calc Nat.card (W ⊓ centralizer ({x * y * t} : Set G) : Subgroup G)
      ≤ a * Nat.card (W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({x * y} : Set G) ⊓ B :
          Subgroup G) := h1
    _ ≤ a * b := Nat.mul_le_mul_left _ hle
    _ ≤ v := hab

section Swap

variable {A : Subgroup G} {t : G}

theorem conj_mem_map_conj_sixS (x : A) :
    t * (x : G) * t⁻¹ ∈ A.map (MulAut.conj t).toMonoidHom :=
  ⟨x, x.2, rfl⟩

@[expose] def swapDiagHom (hc : ∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj t).toMonoidHom, a * b = b * a) :
    A →* G where
  toFun x := (x : G) * (t * x * t⁻¹)
  map_one' := by simp
  map_mul' x y := by
    have hy : (y : G) * (t * x * t⁻¹) = (t * x * t⁻¹) * y :=
      hc y y.2 _ (conj_mem_map_conj_sixS x)
    simp only [Subgroup.coe_mul]
    calc (x : G) * y * (t * (x * y) * t⁻¹) = x * (y * (t * x * t⁻¹)) * (t * y * t⁻¹) := by group
      _ = x * ((t * x * t⁻¹) * y) * (t * y * t⁻¹) := by rw [hy]
      _ = _ := by group

theorem swapDiagHom_apply (hc : ∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj t).toMonoidHom, a * b = b * a)
    (x : A) : swapDiagHom hc x = (x : G) * (t * x * t⁻¹) :=
  rfl

theorem swapDiagHom_injective (hinf : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥)
    (hc : ∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj t).toMonoidHom, a * b = b * a) :
    Function.Injective (swapDiagHom hc) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker, swapDiagHom_apply] at hx
  have h1 : (x : G) = (t * x * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hx
  have h2 : (x : G) ∈ A ⊓ A.map (MulAut.conj t).toMonoidHom :=
    Subgroup.mem_inf.2 ⟨x.2, h1 ▸ inv_mem (conj_mem_map_conj_sixS x)⟩
  rw [hinf, Subgroup.mem_bot] at h2
  exact Subgroup.mem_bot.2 (Subtype.ext h2)

theorem swapDiagHom_commute (ht : t * t = 1)
    (hc : ∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj t).toMonoidHom, a * b = b * a) (x : A) :
    swapDiagHom hc x * t = t * swapDiagHom hc x := by
  rw [swapDiagHom_apply]
  have h1 : (x : G) * (t * x * t⁻¹) = (t * x * t⁻¹) * x := hc x x.2 _ (conj_mem_map_conj_sixS x)
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  calc (x : G) * (t * x * t⁻¹) * t = (t * x * t⁻¹) * x * t := by rw [h1]
    _ = t * ((x : G) * (t * x * t⁻¹)) := by
        rw [hti, show t * x * t * x * t = t * x * (t * x * t) by group]
        rw [show t * ((x : G) * (t * x * t)) = t * x * (t * x * t) by group]

theorem swapDiagHom_mem_of_card_le [Finite G] (ht : t * t = 1)
    (hinf : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥)
    (hc : ∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj t).toMonoidHom, a * b = b * a) {D : Subgroup G}
    (hD : D ≤ A ⊔ A.map (MulAut.conj t).toMonoidHom) (hDt : D ≤ centralizer ({t} : Set G))
    (hcard : Nat.card A ≤ Nat.card D) (x : A) : swapDiagHom hc x ∈ D := by
  have hle : D ≤ (swapDiagHom hc).range := by
    intro d hd
    obtain ⟨y, hyA, hy⟩ := exists_eq_mul_conj_of_mem_sup ht hinf hc (hD hd)
      (mem_centralizer_singleton_iff.1 (hDt hd))
    exact ⟨⟨y, hyA⟩, hy.symm⟩
  have hrc : Nat.card (swapDiagHom hc).range = Nat.card A :=
    Nat.card_range_of_injective (swapDiagHom_injective hinf hc)
  have heq : D = (swapDiagHom hc).range :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hrc]; exact hcard)
  rw [heq]
  exact ⟨x, rfl⟩

end Swap

section Decomp

variable [Finite G] {A W₀ D : Subgroup G} {t : G}

open CFSG.ComponentClassification.M12Cover.CyclicKernel (exists_mul_of_mem_sup_of_commute)

omit [Finite G] in
theorem card_sup_eq_mul_sixS {M N : Subgroup G} (hc : ∀ a ∈ M, ∀ b ∈ N, a * b = b * a)
    (hinf : M ⊓ N = ⊥) : Nat.card (M ⊔ N : Subgroup G) = Nat.card M * Nat.card N := by
  have hN : N ≤ normalizer (M : Set G) := by
    rw [le_normalizer_iff]
    intro b hb a ha
    rw [← hc a ha b hb, mul_inv_cancel_right]
    exact ha
  have h := card_sup_mul_card_inf_of_le_normalizer_sOne hN
  rwa [hinf, Subgroup.card_bot, mul_one] at h

theorem eq_sup_and_card_le_of_swap_sixS (ht : t * t = 1)
    (hinf : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥)
    (hc : ∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj t).toMonoidHom, a * b = b * a)
    (hW₀ : W₀ ≤ A ⊔ A.map (MulAut.conj t).toMonoidHom) (hW₀2 : ∀ w ∈ W₀, w * w = 1)
    (htW₀ : t ∈ normalizer (W₀ : Set G)) (hδD : ∀ x : A, swapDiagHom hc x ∈ D)
    (hDV : D ⊓ centralizer ((W₀ ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) ≤ W₀)
    (hWV : Nat.card W₀ = Nat.card (W₀ ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2) :
    W₀ = (W₀ ⊓ A) ⊔ (W₀ ⊓ A.map (MulAut.conj t).toMonoidHom) ∧
      Nat.card (W₀ ⊓ centralizer ({t} : Set G) : Subgroup G) ≤
        Nat.card (W₀ ⊓ A : Subgroup G) := by
  set A' : Subgroup G := A.map (MulAut.conj t).toMonoidHom with hA'
  set V₀ : Subgroup G := W₀ ⊓ centralizer ({t} : Set G) with hV₀
  set E : Subgroup G := W₀ ⊓ A with hE
  set E' : Subgroup G := W₀ ⊓ A' with hE'
  have hWc : ∀ v ∈ W₀, ∀ w ∈ W₀, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW₀2 hv hw
  have htt : ∀ z : G, t * (t * z * t⁻¹) * t⁻¹ = z := conj_conj_of_mul_self ht
  have hcA' : ∀ b ∈ A', ∀ a ∈ A, b * a = a * b := fun b hb a ha => (hc a ha b hb).symm
  have hconjA : ∀ a ∈ A, t * a * t⁻¹ ∈ A' := fun a ha => ⟨a, ha, rfl⟩
  have hconjA' : ∀ b ∈ A', t * b * t⁻¹ ∈ A := fun b hb => (mem_map_conj_iff_of_mul_self ht).1 hb
  have huniq : ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b₁ ∈ A', ∀ b₂ ∈ A', a₁ * b₁ = a₂ * b₂ → a₁ = a₂ := by
    intro a₁ ha₁ a₂ ha₂ b₁ hb₁ b₂ hb₂ h
    have h1 : a₂⁻¹ * a₁ = b₂ * b₁⁻¹ := by
      calc a₂⁻¹ * a₁ = a₂⁻¹ * (a₁ * b₁) * b₁⁻¹ := by group
        _ = a₂⁻¹ * (a₂ * b₂) * b₁⁻¹ := by rw [h]
        _ = b₂ * b₁⁻¹ := by group
    have h2 : a₂⁻¹ * a₁ ∈ A ⊓ A' :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha₂) ha₁, h1 ▸ mul_mem hb₂ (inv_mem hb₁)⟩
    rw [hinf, Subgroup.mem_bot] at h2
    calc a₁ = a₂ * (a₂⁻¹ * a₁) := by group
      _ = a₂ := by rw [h2, mul_one]
  have hfac : ∀ w ∈ W₀, ∀ a ∈ A, ∀ b ∈ A', w = a * b → a * (t * a * t⁻¹) ∈ W₀ := by
    intro w hw a ha b hb hwab
    apply hDV
    refine Subgroup.mem_inf.2 ⟨hδD ⟨a, ha⟩, ?_⟩
    rw [mem_centralizer_iff]
    intro v hv
    obtain ⟨hvW, hvt⟩ := Subgroup.mem_inf.1 hv
    obtain ⟨x, hxA, hvx⟩ := exists_eq_mul_conj_of_mem_sup ht hinf hc (hW₀ hvW)
      (mem_centralizer_singleton_iff.1 hvt)
    have hx' : t * x * t⁻¹ ∈ A' := hconjA x hxA
    have hax : a * x = x * a := by
      refine huniq (a * x) (mul_mem ha hxA) (x * a) (mul_mem hxA ha) (b * (t * x * t⁻¹))
        (mul_mem hb hx') ((t * x * t⁻¹) * b) (mul_mem hx' hb) ?_
      have h1 : b * x = x * b := hcA' b hb x hxA
      have h2 : (t * x * t⁻¹) * a = a * (t * x * t⁻¹) := hcA' _ hx' a ha
      calc a * x * (b * (t * x * t⁻¹)) = a * (x * b) * (t * x * t⁻¹) := by group
        _ = a * (b * x) * (t * x * t⁻¹) := by rw [h1]
        _ = w * v := by rw [hwab, hvx]; group
        _ = v * w := hWc w hw v hvW
        _ = x * (t * x * t⁻¹) * (a * b) := by rw [hvx, hwab]
        _ = x * ((t * x * t⁻¹) * a) * b := by group
        _ = x * (a * (t * x * t⁻¹)) * b := by rw [h2]
        _ = x * a * ((t * x * t⁻¹) * b) := by group
    have hδ : swapDiagHom hc ⟨a, ha⟩ * swapDiagHom hc ⟨x, hxA⟩ =
        swapDiagHom hc ⟨x, hxA⟩ * swapDiagHom hc ⟨a, ha⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hax
    rw [hvx]
    exact hδ.symm
  have hEV : W₀ ≤ E ⊔ V₀ := by
    intro w hw
    obtain ⟨a, ha, b, hb, hwab⟩ := exists_mul_of_mem_sup_of_commute hc (hW₀ hw)
    have htw : t * w * t⁻¹ ∈ W₀ := (mem_normalizer_iff.1 htW₀ w).1 hw
    have h1 := hfac (t * w * t⁻¹) htw (t * b * t⁻¹) (hconjA' b hb) (t * a * t⁻¹) (hconjA a ha)
      (by rw [hwab, show t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) by group,
        hcA' _ (hconjA a ha) _ (hconjA' b hb)])
    rw [htt] at h1
    set u : G := t * b * t⁻¹ * b with hu
    have hut : u ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have h2 : b * (t * b * t⁻¹) = (t * b * t⁻¹) * b := hcA' b hb _ (hconjA' b hb)
      have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
      calc u * t = t * (b * (t * b * t⁻¹)) := by
            rw [hu, hti]
            calc t * b * t * b * t = t * b * t * b * t := rfl
              _ = t * (b * (t * b * t)) := by group
        _ = t * u := by rw [h2]
    have hev : w * u⁻¹ ∈ E := by
      refine Subgroup.mem_inf.2 ⟨mul_mem hw (inv_mem h1), ?_⟩
      have h3 : w * u⁻¹ = a * (t * b * t⁻¹)⁻¹ := by rw [hwab, hu]; group
      rw [h3]
      exact mul_mem ha (inv_mem (hconjA' b hb))
    have h4 : w = (w * u⁻¹) * u := by group
    rw [h4]
    exact mul_mem (mem_sup_left hev) (mem_sup_right (Subgroup.mem_inf.2 ⟨h1, hut⟩))
  have hcard1 : Nat.card W₀ ≤ Nat.card E * Nat.card V₀ :=
    (Subgroup.card_le_of_le hEV).trans
      (card_sup_le_mul_of_le_of_exponent_two_sixS hW₀2 inf_le_left inf_le_left)
  have hVE : Nat.card V₀ ≤ Nat.card E := by
    have hpos : 0 < Nat.card V₀ := Nat.card_pos
    rw [hWV, sq] at hcard1
    exact Nat.le_of_mul_le_mul_right hcard1 hpos
  have hEE' : E.map (MulAut.conj t).toMonoidHom = E' := map_conj_inf_eq ht htW₀
  have hE'c : Nat.card E' = Nat.card E := by
    rw [← hEE']
    exact Subgroup.card_map_of_injective (MulAut.conj t).injective
  have hinfE : E ⊓ E' = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : z ∈ A ⊓ A' := Subgroup.mem_inf.2 ⟨hz.1.2, hz.2.2⟩
    rwa [hinf] at h1
  have hcE : ∀ a ∈ E, ∀ b ∈ E', a * b = b * a := fun a ha b hb => hc a ha.2 b hb.2
  have hsup : E ⊔ E' ≤ W₀ := sup_le inf_le_left inf_le_left
  refine ⟨le_antisymm ?_ hsup, hVE⟩
  have hcard2 : Nat.card W₀ ≤ Nat.card (E ⊔ E' : Subgroup G) := by
    rw [card_sup_eq_mul_sixS hcE hinfE, hE'c, hWV, sq]
    exact Nat.mul_le_mul hVE hVE
  exact (Subgroup.eq_of_le_of_card_ge hsup hcard2).symm.le

omit [Finite G] in
theorem exists_faithful_factor_of_swap_sixS (ht : t * t = 1)
    (hinf : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥)
    (hc : ∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj t).toMonoidHom, a * b = b * a)
    (hW₀ : W₀ = (W₀ ⊓ A) ⊔ (W₀ ⊓ A.map (MulAut.conj t).toMonoidHom))
    (htW₀ : t ∈ normalizer (W₀ : Set G)) {F₀ : Subgroup G} (hF₀δ : F₀ ≤ (swapDiagHom hc).range)
    (hF₀W : F₀ ≤ normalizer (W₀ : Set G)) (hF₀2 : ∀ f ∈ F₀, f * f = 1)
    (hF₀V : F₀ ⊓ centralizer ((W₀ ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) = ⊥) :
    ∃ X : Subgroup G, IsPGroup 2 X ∧ X ≤ A ∧ X ≤ normalizer (W₀ : Set G) ∧
      X ⊓ centralizer ((W₀ ⊓ A : Subgroup G) : Set G) = ⊥ ∧ Nat.card X = Nat.card F₀ := by
  set A' : Subgroup G := A.map (MulAut.conj t).toMonoidHom with hA'
  set E : Subgroup G := W₀ ⊓ A with hE
  set E' : Subgroup G := W₀ ⊓ A' with hE'
  set δ := swapDiagHom hc with hδ
  have hδinj := swapDiagHom_injective hinf hc
  have hcE : ∀ a ∈ E, ∀ b ∈ E', a * b = b * a := fun a ha b hb => hc a ha.2 b hb.2
  have hEE' : E.map (MulAut.conj t).toMonoidHom = E' := map_conj_inf_eq ht htW₀
  set X : Subgroup G := (F₀.comap δ).map A.subtype with hX
  have hmemX : ∀ x ∈ X, ∃ y : A, (y : G) = x ∧ δ y ∈ F₀ := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, rfl, hy⟩
  have hact : ∀ y : A, ∀ e ∈ E, (y : G) * e * (y : G)⁻¹ = δ y * e * (δ y)⁻¹ := by
    intro y e he
    have h1 : e * (t * y * t⁻¹) = (t * y * t⁻¹) * e :=
      hc e he.2 _ (conj_mem_map_conj_sixS y)
    rw [hδ, swapDiagHom_apply]
    calc (y : G) * e * (y : G)⁻¹ = y * (e * (t * y * t⁻¹)) * (t * y * t⁻¹)⁻¹ * (y : G)⁻¹ := by
          group
      _ = y * ((t * y * t⁻¹) * e) * (t * y * t⁻¹)⁻¹ * (y : G)⁻¹ := by rw [h1]
      _ = _ := by group
  have hcent' : ∀ y : A, ∀ e ∈ E', (y : G) * e * (y : G)⁻¹ = e := by
    intro y e he
    rw [hc y y.2 e he.2, mul_inv_cancel_right]
  have hδE : ∀ y : A, δ y ∈ F₀ → δ y ∈ normalizer (E : Set G) := by
    intro y hy
    have hmem : δ y ∈ A ⊔ A' := by
      rw [hδ, swapDiagHom_apply]
      exact mul_mem (mem_sup_left y.2) (mem_sup_right (conj_mem_map_conj_sixS y))
    exact mem_normalizer_inf_of_mem (hF₀W hy) (sup_le_normalizer_of_commute hc hmem)
  have hy2 : ∀ y : A, δ y ∈ F₀ → (y : G) * y = 1 := by
    intro y hy
    have h1 : δ (y * y) = 1 := by rw [map_mul]; exact hF₀2 _ hy
    have h2 : y * y = 1 := hδinj (by rw [h1, map_one])
    exact congrArg Subtype.val h2
  refine ⟨X, ?_, map_subtype_le _, ?_, ?_, ?_⟩
  · refine isPGroup_of_forall_mul_self_eq_one fun x hx => ?_
    obtain ⟨y, rfl, hy⟩ := hmemX x hx
    exact hy2 y hy
  · intro x hx
    obtain ⟨y, rfl, hy⟩ := hmemX x hx
    refine mem_normalizer_of_mul_self_of_conj_mem (hy2 y hy) fun w hw => ?_
    rw [hW₀] at hw ⊢
    obtain ⟨e, he, e', he', rfl⟩ := exists_mul_of_mem_sup_of_commute hcE hw
    rw [show (y : G) * (e * e') * (y : G)⁻¹ = ((y : G) * e * (y : G)⁻¹) * ((y : G) * e' * (y : G)⁻¹)
      by group, hcent' y e' he', hact y e he]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.1 (hδE y hy) e).1 he)) (mem_sup_right he')
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨y, rfl, hy⟩ := hmemX x hxX
    have hδt : δ y * t = t * δ y := swapDiagHom_commute ht hc y
    have hcE1 : ∀ e ∈ E, δ y * e * (δ y)⁻¹ = e := fun e he => by
      rw [← hact y e he, ← (mem_centralizer_iff.1 hxC) e he, mul_inv_cancel_right]
    have hcE2 : ∀ e ∈ E', δ y * e * (δ y)⁻¹ = e := by
      intro e he
      rw [← hEE'] at he
      obtain ⟨e₀, he₀, rfl⟩ := he
      have hti : t⁻¹ * (δ y)⁻¹ = (δ y)⁻¹ * t⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, hδt]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc δ y * (t * e₀ * t⁻¹) * (δ y)⁻¹ = (δ y * t) * e₀ * (t⁻¹ * (δ y)⁻¹) := by group
        _ = (t * δ y) * e₀ * ((δ y)⁻¹ * t⁻¹) := by rw [hδt, hti]
        _ = t * (δ y * e₀ * (δ y)⁻¹) * t⁻¹ := by group
        _ = t * e₀ * t⁻¹ := by rw [hcE1 e₀ he₀]
    have hδC : δ y ∈ F₀ ⊓ centralizer ((W₀ ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) := by
      refine Subgroup.mem_inf.2 ⟨hy, mem_centralizer_iff.2 fun v hv => ?_⟩
      have hvW : v ∈ E ⊔ E' := hW₀ ▸ (Subgroup.mem_inf.1 hv).1
      obtain ⟨e, he, e', he', rfl⟩ := exists_mul_of_mem_sup_of_commute hcE hvW
      have h1 : δ y * (e * e') * (δ y)⁻¹ = e * e' := by
        rw [show δ y * (e * e') * (δ y)⁻¹ = (δ y * e * (δ y)⁻¹) * (δ y * e' * (δ y)⁻¹) by group,
          hcE1 e he, hcE2 e' he']
      calc e * e' * δ y = δ y * (e * e') * (δ y)⁻¹ * δ y := by rw [h1]
        _ = δ y * (e * e') := by group
    rw [hF₀V, Subgroup.mem_bot] at hδC
    have : y = 1 := hδinj (by rw [hδC, map_one])
    rw [this]
    exact one_mem _
  ·
    have h1 : Nat.card X = Nat.card (F₀.comap δ) :=
      Subgroup.card_map_of_injective A.subtype_injective
    have h2 : Nat.card ((F₀.comap δ).map δ) = Nat.card (F₀.comap δ) :=
      Subgroup.card_map_of_injective hδinj
    have h3 : (F₀.comap δ).map δ = F₀ := by
      rw [Subgroup.map_comap_eq, inf_eq_right.2 hF₀δ]
    rw [h1, ← h2, h3]

end Decomp

end CFSG.SeitzReduction.LinearPilot
