module

public import CFSG.GH74.Uniqueness.Section124A
public import CFSG.GH74.Uniqueness.Bender.FixedLinear

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

section ConjAut

omit [Finite X] in
@[expose] def A2.conjAut (L : Subgroup X) {u : X} (hu : u ∈ normalizer (L : Set X)) :
    MulAut ↥L where
  toFun y := ⟨u * y * u⁻¹, (mem_normalizer_iff.mp hu y).mp y.2⟩
  invFun y := ⟨u⁻¹ * y * u, by
    have h1 := (mem_normalizer_iff.mp (inv_mem hu) y).mp y.2
    rwa [inv_inv] at h1⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

omit [Finite X] in
theorem A2.conjAut_apply (L : Subgroup X) {u : X} (hu : u ∈ normalizer (L : Set X)) (y : ↥L) :
    ((A2.conjAut L hu y : ↥L) : X) = u * y * u⁻¹ := rfl

omit [Finite X] in
theorem A2.conjAut_mul_self (L : Subgroup X) {u : X} (hu : u ∈ normalizer (L : Set X))
    (huu : u * u = 1) : A2.conjAut L hu * A2.conjAut L hu = 1 := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  refine MulEquiv.ext fun x => Subtype.ext ?_
  change u * (u * (x : X) * u⁻¹) * u⁻¹ = (x : X)
  rw [hui]
  calc u * (u * (x : X) * u) * u = (u * u) * x * (u * u) := by group
    _ = x := by rw [huu]; group

omit [Finite X] in
@[expose] def A2.centralizerEquivAutFixed (L : Subgroup X) {u : X}
    (hu : u ∈ normalizer (L : Set X)) :
    ↥(L ⊓ centralizer ({u} : Set X)) ≃* ↥(Bender.autFixed (A2.conjAut L hu)) where
  toFun y := ⟨⟨y, (mem_inf.mp y.2).1⟩, by
    rw [Bender.mem_autFixed_iff]
    apply Subtype.ext
    have hyu : (y : X) * u = u * y := mem_centralizer_singleton_iff.mp (mem_inf.mp y.2).2
    change u * (y : X) * u⁻¹ = y
    rw [← hyu, mul_inv_cancel_right]⟩
  invFun x := ⟨x.1, mem_inf.mpr ⟨x.1.2, by
    have hx : A2.conjAut L hu x.1 = x.1 := Bender.mem_autFixed_iff.mp x.2
    have hx' := congrArg Subtype.val hx
    change u * ((x.1 : ↥L) : X) * u⁻¹ = x.1 at hx'
    rw [mem_centralizer_singleton_iff]
    calc ((x.1 : ↥L) : X) * u = (u * x.1 * u⁻¹) * u := by rw [hx']
      _ = u * x.1 := by group⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end ConjAut

section Arith

omit [Finite X] in
theorem A2.factorization_two_pow_mul {k o : ℕ} (ho : Odd o) : (2 ^ k * o).factorization 2 = k := by
  rw [Nat.factorization_mul (pow_ne_zero k two_ne_zero) ho.pos.ne', Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd
      (fun hd => (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hd))]
  simp

omit [Finite X] in
theorem A2.odd_sq_two_pow_sub_one {k : ℕ} (hk : k ≠ 0) : Odd ((2 ^ k) ^ 2 - 1) := by
  rw [← pow_mul]
  exact A2.odd_two_pow_sub_one (by omega)

end Arith

section Lemma124b

theorem A2.commute_of_inner {c : Ctx12 Z M} {n i : ℕ} (h : LData c n i) {u : X} (hu : u ∈ c.D)
    (hu2 : orderOf u = 2) (hN : u ∈ normalizer (c.L : Set X))
    (hinn : ∃ g : ↥c.L, ∀ x : ↥c.L, A2.conjAut c.L hN x = g * x * g⁻¹) :
    ∀ y ∈ c.L, y * u = u * y := by
  obtain ⟨g, hg⟩ := hinn
  have huu : u * u = 1 := mul_self_of_orderOf_eq_two hu2
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hg' : ∀ y ∈ c.L, u * y * u⁻¹ = (g : X) * y * (g : X)⁻¹ := by
    intro y hy
    have h1 := congrArg Subtype.val (hg ⟨y, hy⟩)
    exact h1
  have hcent : (g : X)⁻¹ * u ∈ centralizer (c.L : Set X) := by
    rw [mem_centralizer_iff]
    intro y hy
    calc y * ((g : X)⁻¹ * u) = (g : X)⁻¹ * ((g : X) * y * (g : X)⁻¹) * u := by group
      _ = (g : X)⁻¹ * (u * y * u⁻¹) * u := by rw [hg' y hy]
      _ = (g : X)⁻¹ * u * y := by group
  have hginvD : (g : X)⁻¹ ∈ c.D := by
    have h1 := c.D.mul_mem (h.centralizer_le hcent) (c.D.inv_mem hu)
    rwa [mul_inv_cancel_right] at h1
  have hgD : (g : X) ∈ c.D := by simpa using c.D.inv_mem hginvD
  have hgc : g * g ∈ center ↥c.L := by
    rw [mem_center_iff]
    intro x
    apply Subtype.ext
    have hxL : (x : X) ∈ c.L := x.2
    have hyL : u * (x : X) * u⁻¹ ∈ c.L := (mem_normalizer_iff.mp hN x).mp hxL
    have key : (x : X) = (g : X) * g * x * ((g : X) * g)⁻¹ := by
      calc (x : X) = u * (u * x * u⁻¹) * u⁻¹ := by
            rw [hui]
            calc (x : X) = (u * u) * x * (u * u) := by rw [huu]; group
              _ = u * (u * x * u) * u := by group
        _ = (g : X) * (u * x * u⁻¹) * (g : X)⁻¹ := hg' _ hyL
        _ = (g : X) * ((g : X) * x * (g : X)⁻¹) * (g : X)⁻¹ := by rw [hg' x hxL]
        _ = (g : X) * g * x * ((g : X) * g)⁻¹ := by group
    change (x : X) * ((g : X) * g) = (g : X) * g * x
    calc (x : X) * ((g : X) * g) = ((g : X) * g * x * ((g : X) * g)⁻¹) * ((g : X) * g) := by
          rw [← key]
      _ = (g : X) * g * x := by group
  rw [h.center_eq_bot, mem_bot] at hgc
  have hodd : Odd (Nat.card ↥(c.D ⊓ c.L)) := by
    rw [h.k_card]
    exact A2.odd_two_pow_sub_one (by have := h.hn; omega)
  have hgg : (g : X) * g = 1 := by
    have h1 := congrArg Subtype.val hgc
    exact h1
  have hg1 : (g : X) = 1 := eq_one_of_mem_of_sq_eq_one hodd (mem_inf.mpr ⟨hgD, g.2⟩) hgg
  intro y hy
  have e : u * y * u⁻¹ = y := by
    rw [hg' y hy, hg1, inv_one, one_mul, mul_one]
  calc y * u = (u * y * u⁻¹) * u := by rw [e]
    _ = u * y := by group

theorem A2.map_sylow_eq_of_linear
    (hZ : IsInvariantInvolutionSet Z) {c : Ctx12 Z M} {n : ℕ}
    (h : LData c n 1) {H A : Subgroup X} (hHL : H ≤ c.L) (hAH : A ≤ H) (hAM : A ≤ zHull Z M)
    (hA : A ≠ ⊥) (hAmax : ∀ x ∈ H, x ∈ zHull Z M → x ∈ A) (P : Sylow 2 ↥H)
    (hAP : A.subgroupOf H ≤ P) : (P : Subgroup ↥H).map H.subtype = A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := h.borel
  have hc := h.benderCore hZ hQ
  have hQR : Bender.rootCenter (Q : Subgroup c.L) = Q := by
    apply eq_of_le_of_card_ge (Bender.rootCenter_le _)
    rw [hc.card_center, hc.card_eq, pow_one]
  have hQM : (Q : Subgroup c.L).map c.L.subtype = zHull Z M := by
    rw [← hQR]
    exact h.map_subtype_rootCenter hZ hQ
  have hAP' : A ≤ (P : Subgroup ↥H).map H.subtype := fun x hx =>
    ⟨⟨x, hAH hx⟩, hAP (mem_subgroupOf.mpr hx), rfl⟩
  have hP'L : (P : Subgroup ↥H).map H.subtype ≤ c.L := (map_subtype_le _).trans hHL
  have hP2 : IsPGroup 2 ↥(((P : Subgroup ↥H).map H.subtype).subgroupOf c.L) :=
    (P.isPGroup'.map H.subtype).comap_of_injective c.L.subtype c.L.subtype_injective
  obtain ⟨Q₁, hQ₁⟩ := hP2.exists_le_sylow
  have hV : A.subgroupOf c.L ≠ ⊥ := by
    intro hbot
    apply hA
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hHL (hAH hx)⟩ : c.L) ∈ A.subgroupOf c.L := mem_subgroupOf.mpr hx
    rw [hbot, mem_bot] at hx'
    rw [mem_bot]
    have h1 := congrArg Subtype.val hx'
    exact h1
  have hVQ : A.subgroupOf c.L ≤ (Q : Subgroup c.L) := by
    intro y hy
    have hyM : (y : X) ∈ (Q : Subgroup c.L).map c.L.subtype := by
      rw [hQM]
      exact hAM (mem_subgroupOf.mp hy)
    obtain ⟨q, hq, hqy⟩ := hyM
    have hqy' : q = y := Subtype.ext hqy
    rw [← hqy']
    exact hq
  have hVQ₁ : A.subgroupOf c.L ≤ (Q₁ : Subgroup c.L) := fun y hy =>
    hQ₁ (mem_subgroupOf.mpr (hAP' (mem_subgroupOf.mp hy)))
  have hQQ : Q₁ = Q := hc.sylow_eq_of_ne_bot hV hVQ hVQ₁
  refine le_antisymm (fun x hx => ?_) hAP'
  have hxL : x ∈ c.L := hP'L hx
  have hxQ : (⟨x, hxL⟩ : c.L) ∈ (Q : Subgroup c.L) := by
    rw [← hQQ]
    exact hQ₁ (mem_subgroupOf.mpr hx)
  have hxM : x ∈ zHull Z M := by
    rw [← hQM]
    exact ⟨⟨x, hxL⟩, hxQ, rfl⟩
  exact hAmax x (map_subtype_le _ hx) hxM

theorem A2.lemma124b
    (S : ZDSetup X Z M) {c : Ctx12 Z M} {n i : ℕ} (h : LData c n i) {u : X}
    (hu : u ∈ c.D) (hu2 : orderOf u = 2) :
    (∀ y ∈ c.L, y * u = u * y) ∨
      (i = 1 ∧ ∃ k : ℕ, 2 ≤ k ∧ n = 2 * k ∧ qU Z M u = 2 ^ k ∧
        Bender.BenderType ↥(c.L ⊓ centralizer ({u} : Set X)) k 1 1) := by
  have hZ := S.invariant
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have huM : u ∈ M := (mem_inf.mp hu).1
  have huu : u * u = 1 := mul_self_of_orderOf_eq_two hu2
  have hN : u ∈ normalizer (c.L : Set X) :=
    IsProductDisconnected.le_normalizer_lSubgroup hZ S.prodDisc c.ht c.htM c.hz c.hzM hu
  have hα := A2.conjAut_mul_self c.L hN huu
  by_cases hinn : ∃ g : ↥c.L, ∀ x : ↥c.L, A2.conjAut c.L hN x = g * x * g⁻¹
  · exact Or.inl (A2.commute_of_inner h hu hu2 hN hinn)
  right
  have hi1 : i = 1 := by
    rcases h.hi with h1 | h2
    · exact h1
    · exfalso
      have hB2 : Bender.BenderType ↥c.L n 2 1 := h2 ▸ h.bender
      exact hinn (hB2.not_outer_involution_suzuki _ hα)
  subst hi1
  obtain ⟨k, hnk, ⟨φ⟩, -⟩ := h.bender.fixed_linear _ hα hinn
  let ψ := (A2.centralizerEquivAutFixed c.L hN).trans φ
  have hk0 : k ≠ 0 := by
    have := h.hn
    omega
  have hcardH : Nat.card ↥(c.L ⊓ centralizer ({u} : Set X)) = 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
    rw [Nat.card_congr ψ.toEquiv]
    exact CFSG.Walter.psl2_even_card hk0
  have h4 := A2.four_le_qU S h huM hu2
  have hAH : centralizer ({u} : Set X) ⊓ zHull Z M ≤ c.L ⊓ centralizer ({u} : Set X) :=
    fun x hx => mem_inf.mpr ⟨h.m_le (mem_inf.mp hx).2, (mem_inf.mp hx).1⟩
  have hAne : centralizer ({u} : Set X) ⊓ zHull Z M ≠ ⊥ := by
    intro hbot
    have h1 : qU Z M u = 1 := by
      change Nat.card ↥(centralizer ({u} : Set X) ⊓ zHull Z M) = 1
      rw [hbot, card_bot]
    omega
  have hA2 : IsPGroup 2 ↥((centralizer ({u} : Set X) ⊓ zHull Z M).subgroupOf
      (c.L ⊓ centralizer ({u} : Set X))) :=
    ((IsPGroup.of_card h.m_card).to_le inf_le_right).comap_of_injective _
      (c.L ⊓ centralizer ({u} : Set X)).subtype_injective
  obtain ⟨P, hP⟩ := hA2.exists_le_sylow
  have hPA := A2.map_sylow_eq_of_linear hZ h inf_le_left hAH inf_le_right hAne
    (fun x hx hxM => mem_inf.mpr ⟨(mem_inf.mp hx).2, hxM⟩) P hP
  have hqk : qU Z M u = 2 ^ k := by
    change Nat.card ↥(centralizer ({u} : Set X) ⊓ zHull Z M) = 2 ^ k
    rw [← hPA, card_map_of_injective (c.L ⊓ centralizer ({u} : Set X)).subtype_injective,
      P.card_eq_multiplicity, hcardH, A2.factorization_two_pow_mul (A2.odd_sq_two_pow_sub_one hk0)]
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hk1 : k = 1 := by omega
    rw [hqk, hk1] at h4
    norm_num at h4
  exact ⟨rfl, k, hk2, hnk, hqk, Bender.BenderType.linear k hk2 ψ⟩

end Lemma124b

end CFSG.GH74.Uniqueness
