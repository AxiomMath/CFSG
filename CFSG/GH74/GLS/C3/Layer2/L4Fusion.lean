module

public import CFSG.GH74.GLS.C3.Layer2.ModelFusion

public section

namespace CFSG.GH74.GLS.C3.Layer2.L4

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.Model

section Generic

variable {X : Type*} [Group X]

theorem exists_conj_of_isSylowOf [Finite X] {P P' : Subgroup X} (hP : IsSylowOf 2 P ⊤)
    (hP' : IsSylowOf 2 P' ⊤) : ∃ k : X, ∀ w, w ∈ P' ↔ k * w * k⁻¹ ∈ P := by
  obtain ⟨k, -, hk⟩ := exists_mem_conj_le_of_isSylowOf hP' (le_top : P ≤ ⊤) hP.isPGroup
  let Pk : Subgroup X := P.map (MulAut.conj k⁻¹).toMonoidHom
  have hPk : Pk ≤ P' := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hk y hy
  have hcard : Nat.card P' ≤ Nat.card Pk := by
    rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hP.card_eq, hP'.card_eq]
  have hPk' : Pk = P' := Subgroup.eq_of_le_of_card_ge hPk hcard
  refine ⟨k, fun w => ?_⟩
  constructor
  · intro hw
    rw [← hPk'] at hw
    obtain ⟨y, hy, rfl⟩ := hw
    have e : k * (k⁻¹ * y * k) * k⁻¹ = y := by group
    simpa [MulAut.conj_apply, e] using hy
  · intro hw
    have := hk _ hw
    simpa [mul_assoc] using this

theorem card_centralizer_inf_of_conj {P P' : Subgroup X} (k z : X)
    (hk : ∀ w, w ∈ P' ↔ k * w * k⁻¹ ∈ P) :
    Nat.card ↥(centralizer ({k⁻¹ * z * k} : Set X) ⊓ P') =
      Nat.card ↥(centralizer ({z} : Set X) ⊓ P) := by
  refine Nat.card_congr ?_
  have key : ∀ w : X, w ∈ centralizer ({k⁻¹ * z * k} : Set X) ↔
      k * w * k⁻¹ ∈ centralizer ({z} : Set X) := by
    intro w
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro hw
      calc k * w * k⁻¹ * z = k * (w * (k⁻¹ * z * k)) * k⁻¹ := by group
        _ = k * ((k⁻¹ * z * k) * w) * k⁻¹ := by rw [hw]
        _ = z * (k * w * k⁻¹) := by group
    · intro hw
      calc w * (k⁻¹ * z * k) = k⁻¹ * ((k * w * k⁻¹) * z) * k := by group
        _ = k⁻¹ * (z * (k * w * k⁻¹)) * k := by rw [hw]
        _ = (k⁻¹ * z * k) * w := by group
  exact
    { toFun := fun w => ⟨k * (w : X) * k⁻¹, (key _).1 w.2.1, (hk _).1 w.2.2⟩
      invFun := fun w => ⟨k⁻¹ * (w : X) * k,
        (key _).2 (by
          have e : k * (k⁻¹ * (w : X) * k) * k⁻¹ = w := by group
          rw [e]; exact w.2.1),
        (hk _).2 (by
          have e : k * (k⁻¹ * (w : X) * k) * k⁻¹ = w := by group
          rw [e]; exact w.2.2)⟩
      left_inv := fun w => Subtype.ext (by simp [mul_assoc])
      right_inv := fun w => Subtype.ext (by simp [mul_assoc]) }

end Generic

section Main

variable {G : Type} [Group G] [Finite G] {n : ℕ} [NeZero n] {x : G} {K T Q S : Subgroup G} {a : G}

theorem fusion_facts
    (h : IsAConfig n x K T Q S a) (c : Coord h) (hn : n = 6 ∨ n = 7)
    (hG : IsSimpleGroup G) (hnab : ∃ u w : G, u * w ≠ w * u)
    (hM : ModelIso n c.alpha c.uElt c.XSet c.VSet) :
    Nat.card S = 128 ∧ S = T ⊔ zpowers a ∧ (∃ y ∈ S, y * y = 1 ∧ y ∉ T) ∧
      (∀ y ∈ S, orderOf y = 2 → y ∉ T → ¬ IsConj x y) := by
  obtain ⟨Sg, S', φg, hcl, hφg⟩ := fusion_of_modelIso h c hn hG hnab hM
  have hT : Nat.card T = 64 := c.card_T hn
  have hTS : T ≤ S := h.T_lt_S.le
  have hS128 : Nat.card S = 128 := by
    have h1 : Nat.card S = Nat.card Sg := by
      rw [h.sylowS.card_eq, Subgroup.card_top, Sg.card_eq_multiplicity]
    have h2 : Nat.card Sg = Nat.card S' := Nat.card_congr φg.toEquiv
    have h3 : Nat.card S' = 2 ^ 7 := by
      rw [S'.card_eq_multiplicity, card_alt_factorization n hn]
    rw [h1, h2, h3]; norm_num
  obtain ⟨φ, a₀, s, hφinj, hsum, ha₀2, ha₀r, hconj, hcls, hdiag, hη, hb, ha⟩ := hM.data
  obtain ⟨t₀, rfl⟩ := c.tau.surjective s
  set a₁ : G := (t₀ : G) * a with ha₁def
  have ha₁S : a₁ ∈ S := mul_mem (hTS t₀.2) h.a_mem.1
  have ha₁N : ∀ t ∈ T, a₁ * t * a₁⁻¹ ∈ T := by
    intro t ht
    have e : a₁ * t * a₁⁻¹ = (t₀ : G) * (a * t * a⁻¹) * (t₀ : G)⁻¹ := by
      rw [ha₁def]; group
    rw [e]
    exact mul_mem (mul_mem t₀.2 ((mem_normalizer_iff.1 h.a_mem.2.1 t).1 ht)) (inv_mem t₀.2)
  have ha₁T : a₁ ∉ T := fun hmem => h.a_mem.2.2.1 (by
    have : a = (t₀ : G)⁻¹ * a₁ := by rw [ha₁def]; group
    rw [this]; exact mul_mem (inv_mem t₀.2) hmem)
  have ha₁sq : a₁ ^ 2 = 1 := by
    have h1 : (t₀ * conjAutT h.a_mem.2.1 t₀ * ⟨a ^ 2, h.a_mem.2.2.2⟩ : ↥T) = 1 := by
      apply c.tau.injective
      rw [map_mul, map_mul, map_one, ← c.alpha_tau t₀]
      exact hsum
    have h2 := congrArg Subtype.val h1
    have h3 : (t₀ : G) * (a * t₀ * a⁻¹) * a ^ 2 = 1 := h2
    calc a₁ ^ 2 = (t₀ : G) * (a * t₀ * a⁻¹) * a ^ 2 := by rw [ha₁def, sq, sq]; group
      _ = 1 := h3
  have hS₁card : Nat.card ↥(T ⊔ zpowers a₁) = 128 := by
    rw [card_sup_zpowers ha₁N ha₁sq ha₁T, hT]
  have hS₁S : T ⊔ zpowers a₁ ≤ S := sup_le hTS (zpowers_le.2 ha₁S)
  have hS₁eq : T ⊔ zpowers a₁ = S :=
    Subgroup.eq_of_le_of_card_ge hS₁S (by rw [hS₁card, hS128])
  have hSeq : S = T ⊔ zpowers a := by
    apply le_antisymm
    · rw [← hS₁eq]
      refine sup_le le_sup_left (zpowers_le.2 ?_)
      exact mul_mem ((le_sup_left : T ≤ T ⊔ zpowers a) t₀.2)
        ((le_sup_right : zpowers a ≤ T ⊔ zpowers a) (mem_zpowers a))
    · exact sup_le hTS (zpowers_le.2 h.a_mem.1)
  refine ⟨hS128, hSeq, ⟨a₁, ha₁S, by rw [← sq]; exact ha₁sq, ha₁T⟩, ?_⟩
  intro y hyS hy2 hyT hyx
  have hCT : centralizer ({x} : Set G) ⊓ S = T :=
    h.sylowT.eq_of_le (le_inf h.T_le_C hTS) inf_le_left
      (IsPGroup.to_le h.sylowS.isPGroup inf_le_right)
  have hyx_nc : y * x ≠ x * y := by
    intro hc
    apply hyT
    have : y ∈ centralizer ({x} : Set G) ⊓ S := ⟨mem_centralizer_singleton_iff.2 hc, hyS⟩
    rwa [hCT] at this
  have hSgS : IsSylowOf 2 (Sg : Subgroup G) ⊤ := by
    rw [isSylowOf_iff]
    exact ⟨le_top, Sg.isPGroup', by rw [Subgroup.relIndex_top_right]; exact Sg.not_dvd_index⟩
  obtain ⟨m, hm⟩ := exists_conj_of_isSylowOf h.sylowS hSgS
  have hxS : x ∈ S := hTS h.x_mem_T
  have hxg : m⁻¹ * x * m ∈ (Sg : Subgroup G) := (hm _).2 (by
    have e : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
    rw [e]; exact hxS)
  have hyg : m⁻¹ * y * m ∈ (Sg : Subgroup G) := (hm _).2 (by
    have e : m * (m⁻¹ * y * m) * m⁻¹ = y := by group
    rw [e]; exact hyS)
  have hord_conj : ∀ (g z : G), orderOf (g⁻¹ * z * g) = orderOf z := fun g z => by
    have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) z
    simpa [MulAut.conj_apply] using this
  set ux : ↥(Sg : Subgroup G) := ⟨m⁻¹ * x * m, hxg⟩ with hux
  set uy : ↥(Sg : Subgroup G) := ⟨m⁻¹ * y * m, hyg⟩ with huy
  have hux2 : orderOf ux = 2 := by
    rw [← Subgroup.orderOf_coe]
    show orderOf (m⁻¹ * x * m) = 2
    rw [hord_conj, h.x_order]
  have huy2 : orderOf uy = 2 := by
    rw [← Subgroup.orderOf_coe]
    show orderOf (m⁻¹ * y * m) = 2
    rw [hord_conj, hy2]
  have hconj_x : IsConj (ux : G) x := isConj_iff.2 ⟨m, by simp [hux, mul_assoc]⟩
  have hconj_y : IsConj (uy : G) x :=
    (isConj_iff.2 ⟨m, by simp [huy, mul_assoc]⟩ : IsConj (uy : G) y).trans hyx.symm
  have hnx : numMoved (((φg ux : ↥S') : alternatingGroup (Fin (n + 4))) :
      Equiv.Perm (Fin (n + 4))) = 4 := (hφg ux hux2).1 hconj_x
  have hny : numMoved (((φg uy : ↥S') : alternatingGroup (Fin (n + 4))) :
      Equiv.Perm (Fin (n + 4))) = 4 := (hφg uy huy2).1 hconj_y
  set x'' : alternatingGroup (Fin (n + 4)) := ((φg ux : ↥S') : alternatingGroup (Fin (n + 4))) with hx''
  set y'' : alternatingGroup (Fin (n + 4)) := ((φg uy : ↥S') : alternatingGroup (Fin (n + 4))) with hy''
  have hcard64 : Nat.card ↥(centralizer ({x''} : Set (alternatingGroup (Fin (n + 4)))) ⊓
      (S' : Subgroup (alternatingGroup (Fin (n + 4))))) = 64 := by
    have h1 := card_centralizer_inf_equiv φg (g := (ux : G)) ux.2
    have h2 := card_centralizer_inf_of_conj (P := S) (P' := (Sg : Subgroup G)) m x hm
    rw [hCT, hT] at h2
    rw [← h1]
    exact h2
  have hx''2 : orderOf x'' = 2 := by
    rw [hx'', Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hux2]
  have hy''2 : orderOf y'' = 2 := by
    rw [hy'', Subgroup.orderOf_coe, MulEquiv.orderOf_eq, huy2]
  have hnc : y'' * x'' ≠ x'' * y'' := by
    intro hc
    apply hyx_nc
    have h1 : (φg uy) * (φg ux) = (φg ux) * (φg uy) := Subtype.ext hc
    have h2 : uy * ux = ux * uy := φg.injective (by rw [map_mul, map_mul]; exact h1)
    have h3 : m⁻¹ * y * m * (m⁻¹ * x * m) = m⁻¹ * x * m * (m⁻¹ * y * m) := congrArg Subtype.val h2
    have h4 : y * x = x * y := by
      have : m * (m⁻¹ * y * m * (m⁻¹ * x * m)) * m⁻¹ = y * x := by group
      rw [← this, h3]; group
    exact h4
  have ha₀N : ∀ t ∈ φ.range, a₀ * t * a₀⁻¹ ∈ φ.range := by
    rintro _ ⟨t', rfl⟩
    exact ⟨_, (hconj t').symm⟩
  have hcardS₁ : Nat.card ↥(φ.range ⊔ zpowers a₀) =
      2 ^ (Nat.card (alternatingGroup (Fin (n + 4)))).factorization 2 := by
    rw [card_alt_factorization n hn, card_sup_zpowers ha₀N ha₀2 ha₀r,
      Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv.symm, card_T0 n hn]
    norm_num
  have hS₁Syl : IsSylowOf 2 (φ.range ⊔ zpowers a₀) ⊤ :=
    isSylowOf_of_card le_top (by rw [Subgroup.card_top]; exact hcardS₁)
  have hS'Syl : IsSylowOf 2 (S' : Subgroup (alternatingGroup (Fin (n + 4)))) ⊤ := by
    rw [isSylowOf_iff]
    exact ⟨le_top, S'.isPGroup', by rw [Subgroup.relIndex_top_right]; exact S'.not_dvd_index⟩
  obtain ⟨k, hk⟩ := exists_conj_of_isSylowOf hS'Syl hS₁Syl
  set x₁ : alternatingGroup (Fin (n + 4)) := k⁻¹ * x'' * k with hx₁
  set y₁ : alternatingGroup (Fin (n + 4)) := k⁻¹ * y'' * k with hy₁
  have hx₁S : x₁ ∈ φ.range ⊔ zpowers a₀ := (hk _).2 (by
    have e : k * (k⁻¹ * x'' * k) * k⁻¹ = x'' := by group
    rw [e]; exact (φg ux).2)
  have hy₁S : y₁ ∈ φ.range ⊔ zpowers a₀ := (hk _).2 (by
    have e : k * (k⁻¹ * y'' * k) * k⁻¹ = y'' := by group
    rw [e]; exact (φg uy).2)
  have hord_conjA : ∀ z : alternatingGroup (Fin (n + 4)), orderOf (k⁻¹ * z * k) = orderOf z :=
    fun z => by
      have := MulEquiv.orderOf_eq (MulAut.conj k⁻¹) z
      simpa [MulAut.conj_apply] using this
  have hx₁2 : orderOf x₁ = 2 := by rw [hx₁, hord_conjA, hx''2]
  have hy₁2 : orderOf y₁ = 2 := by rw [hy₁, hord_conjA, hy''2]
  have hnm_conj : ∀ z : alternatingGroup (Fin (n + 4)),
      numMoved ((k⁻¹ * z * k : alternatingGroup (Fin (n + 4))) : Equiv.Perm (Fin (n + 4))) =
        numMoved (z : Equiv.Perm (Fin (n + 4))) := fun z => by
    have := numMoved_conj (z : Equiv.Perm (Fin (n + 4))) ((k : Equiv.Perm (Fin (n + 4)))⁻¹)
    simpa using this
  have hx₁card : Nat.card ↥(centralizer ({x₁} : Set (alternatingGroup (Fin (n + 4)))) ⊓
      (φ.range ⊔ zpowers a₀)) = 64 := by
    have := card_centralizer_inf_of_conj (P := (S' : Subgroup (alternatingGroup (Fin (n + 4)))))
      (P' := φ.range ⊔ zpowers a₀) k x'' hk
    rw [hcard64] at this
    exact this
  have hx₁cases := ha x₁ hx₁S hx₁2 hx₁card
  have hcommφ : ∀ t : T0 n, φ t * φ (x0T n) = φ (x0T n) * φ t := fun t => by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (x0_central n (T0_le_Fgrp n t.2))
  have hcomm_r : ∀ r ∈ φ.range, r * x₁ = x₁ * r := by
    intro r hr
    have hmain : ∀ r' ∈ φ.range, r' * φ (x0T n) = φ (x0T n) * r' := by
      rintro _ ⟨t, rfl⟩
      exact hcommφ t
    rcases hx₁cases with hx | hx
    · rw [hx]; exact hmain r hr
    · rw [hx]
      have ha₀inv : a₀⁻¹ = a₀ := by
        have : a₀ * a₀ = 1 := by rw [← sq]; exact ha₀2
        exact inv_eq_of_mul_eq_one_right this
      have hr' : a₀⁻¹ * r * a₀ ∈ φ.range := by
        rw [ha₀inv]
        have := ha₀N r hr
        rwa [ha₀inv] at this
      have h1 := hmain _ hr'
      calc r * (a₀ * φ (x0T n) * a₀⁻¹) = a₀ * ((a₀⁻¹ * r * a₀) * φ (x0T n)) * a₀⁻¹ := by group
        _ = a₀ * (φ (x0T n) * (a₀⁻¹ * r * a₀)) * a₀⁻¹ := by rw [h1]
        _ = (a₀ * φ (x0T n) * a₀⁻¹) * r := by group
  have hy₁nr : y₁ ∉ φ.range := by
    intro hr
    have h1 := hcomm_r y₁ hr
    apply hnc
    have h2 : k⁻¹ * (y'' * x'') * k = k⁻¹ * (x'' * y'') * k := by
      have e1 : k⁻¹ * (y'' * x'') * k = y₁ * x₁ := by rw [hy₁, hx₁]; group
      have e2 : k⁻¹ * (x'' * y'') * k = x₁ * y₁ := by rw [hy₁, hx₁]; group
      rw [e1, e2]; exact h1
    have := mul_left_cancel (mul_right_cancel h2)
    exact this
  obtain ⟨t, ht⟩ := hb y₁ hy₁S hy₁nr hy₁2
  have ha₀1 : a₀ ≠ 1 := fun h1 => ha₀r (h1 ▸ one_mem _)
  have ha₀ord : orderOf a₀ = 2 := orderOf_eq_prime ha₀2 ha₀1
  have h8 : numMoved ((a₀ : alternatingGroup (Fin (n + 4))) : Equiv.Perm (Fin (n + 4))) = 8 := by
    have := hdiag 1 (by rw [map_one, one_mul]; exact ha₀ord)
    rwa [map_one, one_mul] at this
  have hy₁nm : numMoved ((y₁ : alternatingGroup (Fin (n + 4))) : Equiv.Perm (Fin (n + 4))) = 8 := by
    rw [← ht]
    have := numMoved_conj (a₀ : Equiv.Perm (Fin (n + 4)))
      ((φ t : alternatingGroup (Fin (n + 4))) : Equiv.Perm (Fin (n + 4)))
    rw [← h8]
    simpa using this
  have hy₁nm4 : numMoved ((y₁ : alternatingGroup (Fin (n + 4))) : Equiv.Perm (Fin (n + 4))) = 4 := by
    rw [hy₁, hnm_conj]; exact hny
  omega

end Main

end CFSG.GH74.GLS.C3.Layer2.L4
