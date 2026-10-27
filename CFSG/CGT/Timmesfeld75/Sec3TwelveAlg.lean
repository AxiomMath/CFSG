module

public import CFSG.CGT.Timmesfeld75.L2Aut
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.CGT.Timmesfeld75

open scoped MatrixGroups
open CFSG.Open

section Centralizer

variable {G : Type*} [Group G]

@[expose] def mulConjHom (A : Subgroup G) (hA : IsElemAbelian 2 A) (a : G)
    (haA : ∀ x ∈ A, a * x * a⁻¹ ∈ A) : A →* G :=
  MonoidHom.mk' (fun x : A => (x : G) * (a * x * a⁻¹)) fun x y => by
    have h : a * (x : G) * a⁻¹ * y = y * (a * (x : G) * a⁻¹) :=
      elemAbelian_mul_comm hA (haA x x.2) y.2
    show (x : G) * y * (a * ((x : G) * y) * a⁻¹) =
      (x : G) * (a * x * a⁻¹) * ((y : G) * (a * y * a⁻¹))
    calc (x : G) * y * (a * ((x : G) * y) * a⁻¹)
        = x * (y * (a * x * a⁻¹)) * (a * y * a⁻¹) := by group
      _ = x * ((a * x * a⁻¹) * y) * (a * y * a⁻¹) := by rw [h]
      _ = (x : G) * (a * x * a⁻¹) * ((y : G) * (a * y * a⁻¹)) := by group

theorem mulConjHom_apply (A : Subgroup G) (hA : IsElemAbelian 2 A) (a : G)
    (haA : ∀ x ∈ A, a * x * a⁻¹ ∈ A) (x : A) :
    mulConjHom A hA a haA x = (x : G) * (a * x * a⁻¹) := rfl

theorem mulConjHom_mem (A : Subgroup G) (hA : IsElemAbelian 2 A) (a : G)
    (haA : ∀ x ∈ A, a * x * a⁻¹ ∈ A) (x : A) : mulConjHom A hA a haA x ∈ A :=
  A.mul_mem x.2 (haA x x.2)

theorem mulConjHom_mem_centralizer (A : Subgroup G) (hA : IsElemAbelian 2 A) {a : G}
    (haa : a * a = 1) (haA : ∀ x ∈ A, a * x * a⁻¹ ∈ A) (x : A) :
    mulConjHom A hA a haA x ∈ Subgroup.centralizer ({a} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, mulConjHom_apply]
  have h : a * (x : G) * a⁻¹ * x = x * (a * (x : G) * a⁻¹) :=
    elemAbelian_mul_comm hA (haA x x.2) x.2
  have e : a * ((x : G) * (a * x * a⁻¹)) * a⁻¹ = (a * x * a⁻¹) * x := by
    calc a * ((x : G) * (a * x * a⁻¹)) * a⁻¹ = (a * x * a⁻¹) * ((a * a) * x * (a * a)⁻¹) := by
          group
      _ = (a * x * a⁻¹) * x := by rw [haa]; group
  have hy : a * ((x : G) * (a * x * a⁻¹)) * a⁻¹ = (x : G) * (a * x * a⁻¹) := e.trans h
  calc (x : G) * (a * x * a⁻¹) * a = (a * ((x : G) * (a * x * a⁻¹)) * a⁻¹) * a := by rw [hy]
    _ = a * ((x : G) * (a * x * a⁻¹)) := by group

theorem mulConjHom_eq_one_iff (A : Subgroup G) (hA : IsElemAbelian 2 A) {a : G}
    (haA : ∀ x ∈ A, a * x * a⁻¹ ∈ A) (x : A) :
    mulConjHom A hA a haA x = 1 ↔ a * (x : G) * a⁻¹ = x := by
  rw [mulConjHom_apply]
  constructor
  · intro h
    have h1 : a * (x : G) * a⁻¹ = (x : G)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h1, elemAbelian_inv hA x.2]
  · intro h
    rw [h]
    exact elemAbelian_mul_self hA x.2

theorem natCard_eq_natCard_centralizer_mul_natCard_range (A : Subgroup G)
    (hA : IsElemAbelian 2 A) {a : G} (haA : ∀ x ∈ A, a * x * a⁻¹ ∈ A) :
    Nat.card A = Nat.card ↥(A ⊓ Subgroup.centralizer ({a} : Set G)) *
      Nat.card (mulConjHom A hA a haA).range := by
  have h1 := Subgroup.card_mul_index (mulConjHom A hA a haA).ker
  rw [Subgroup.index_ker] at h1
  rw [← h1]
  congr 1
  refine Nat.card_congr
    { toFun := fun x => ⟨(x.1 : G), x.1.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      invFun := fun y => ⟨⟨(y : G), y.2.1⟩, (mulConjHom_eq_one_iff A hA haA _).2 ?_⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  · have h2 := (mulConjHom_eq_one_iff A hA haA x.1).1 x.2
    calc (x.1 : G) * a = (a * (x.1 : G) * a⁻¹) * a := by rw [h2]
      _ = a * x.1 := by group
  · have h2 := Subgroup.mem_centralizer_singleton_iff.1 y.2.2
    calc a * (y : G) * a⁻¹ = (y * a) * a⁻¹ := by rw [h2]
      _ = y := by group

theorem range_mulConjHom_le (A : Subgroup G) (hA : IsElemAbelian 2 A) {a : G} (haa : a * a = 1)
    (haA : ∀ x ∈ A, a * x * a⁻¹ ∈ A) :
    (mulConjHom A hA a haA).range ≤ A ⊓ Subgroup.centralizer ({a} : Set G) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨mulConjHom_mem A hA a haA x, mulConjHom_mem_centralizer A hA haa haA x⟩

theorem natCard_le_natCard_centralizer_sq [Finite G] (A : Subgroup G) (hA : IsElemAbelian 2 A)
    {a : G} (haa : a * a = 1) (haA : ∀ x ∈ A, a * x * a⁻¹ ∈ A) :
    Nat.card A ≤ Nat.card ↥(A ⊓ Subgroup.centralizer ({a} : Set G)) ^ 2 := by
  rw [natCard_eq_natCard_centralizer_mul_natCard_range A hA haA, sq]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le (range_mulConjHom_le A hA haa haA))

theorem exists_eq_mul_conj_of_natCard_eq_sq [Finite G] (A : Subgroup G) (hA : IsElemAbelian 2 A)
    {a : G} (haa : a * a = 1) (haA : ∀ x ∈ A, a * x * a⁻¹ ∈ A)
    (h : Nat.card A = Nat.card ↥(A ⊓ Subgroup.centralizer ({a} : Set G)) ^ 2) {w : G}
    (hw : w ∈ A ⊓ Subgroup.centralizer ({a} : Set G)) : ∃ l ∈ A, w = l * (a * l * a⁻¹) := by
  have h1 := natCard_eq_natCard_centralizer_mul_natCard_range A hA haA
  rw [h, sq] at h1
  have hpos : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer ({a} : Set G)) := Nat.card_pos
  have h2 : Nat.card (mulConjHom A hA a haA).range =
      Nat.card ↥(A ⊓ Subgroup.centralizer ({a} : Set G)) :=
    (Nat.eq_of_mul_eq_mul_left hpos h1).symm
  have h3 : (mulConjHom A hA a haA).range = A ⊓ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.eq_of_le_of_card_ge (range_mulConjHom_le A hA haa haA) h2.ge
  rw [← h3] at hw
  obtain ⟨x, hx⟩ := hw
  exact ⟨x, x.2, hx.symm⟩

theorem natCard_mul_natCard_le_of_inf_eq_bot [Finite G] {P Q M : Subgroup G} (hP : P ≤ M)
    (hQ : Q ≤ M) (h : P ⊓ Q = ⊥) : Nat.card P * Nat.card Q ≤ Nat.card M := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun pq : P × Q => (⟨(pq.1 : G) * pq.2, M.mul_mem (hP pq.1.2) (hQ pq.2.2)⟩ : M)) ?_
  rintro ⟨p, q⟩ ⟨p', q'⟩ hpq
  have h1 : (p : G) * q = p' * q' := congrArg Subtype.val hpq
  have h2 : (p' : G)⁻¹ * p = q' * (q : G)⁻¹ := by
    calc (p' : G)⁻¹ * p = (p' : G)⁻¹ * (p * q) * (q : G)⁻¹ := by group
      _ = q' * (q : G)⁻¹ := by rw [h1]; group
  have hmem : (p' : G)⁻¹ * p ∈ P ⊓ Q :=
    ⟨P.mul_mem (P.inv_mem p'.2) p.2, by rw [h2]; exact Q.mul_mem q'.2 (Q.inv_mem q.2)⟩
  rw [h, Subgroup.mem_bot] at hmem
  have hp : p' = p := Subtype.ext (inv_mul_eq_one.1 hmem)
  have hq : q' = q := Subtype.ext (mul_inv_eq_one.1 (h2 ▸ hmem))
  rw [hp, hq]

theorem isElemAbelian_subgroup_of_le {p : ℕ} {T K : Subgroup G} (hT : IsElemAbelian p T)
    (hK : K ≤ T) : IsElemAbelian p K := CFSG.Open.IsElemAbelian.mono hT hK

theorem exists_ne_one_ne_of_two_lt_natCard [Finite G] {H : Subgroup G} (h : 2 < Nat.card H) :
    ∃ x ∈ H, x ≠ 1 ∧ ∃ y ∈ H, y ≠ 1 ∧ x ≠ y := by
  by_contra hcon
  push Not at hcon
  by_cases hex : ∃ x : H, x ≠ 1
  · obtain ⟨x₀, hx₀⟩ := hex
    have hsub : (Set.univ : Set H) ⊆ {1, x₀} := by
      intro z _
      by_cases hz : z = 1
      · simp [hz]
      · have := hcon z z.2 (fun h => hz (Subtype.ext h)) x₀ x₀.2 (fun h => hx₀ (Subtype.ext h))
        simp [Subtype.ext this]
    have hle : Nat.card H ≤ 2 := by
      calc Nat.card H = (Set.univ : Set H).ncard := (Set.ncard_univ H).symm
        _ ≤ ({1, x₀} : Set H).ncard := Set.ncard_le_ncard hsub
        _ ≤ ({x₀} : Set H).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    omega
  · push Not at hex
    have hbot : H = ⊥ := (Subgroup.eq_bot_iff_forall H).2 fun x hx => by
      simpa using hex ⟨x, hx⟩
    rw [← Subgroup.card_eq_one] at hbot
    omega

end Centralizer

section Galois

theorem ringAut_eq_of_orderOf_eq_two {F : Type} [Field F] [Finite F] [CharP F 2]
    {τ τ' : F ≃+* F} (h : orderOf τ = 2) (h' : orderOf τ' = 2) : τ = τ' := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have : Fintype F := Fintype.ofFinite F
  let toGal : (F ≃+* F) →* (F ≃ₐ[ZMod 2] F) :=
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ) (fun x => by
        have := RingHom.congr_fun (RingHom.ext_zmod ((σ : F →+* F).comp (algebraMap (ZMod 2) F))
          (algebraMap (ZMod 2) F)) x
        simpa using this)
      map_one' := by ext; rfl
      map_mul' := fun σ ρ => by ext; rfl }
  have hinj : Function.Injective toGal := fun σ ρ hσρ => by
    ext x
    exact congrArg (fun g : F ≃ₐ[ZMod 2] F => g x) hσρ
  have hord : orderOf (toGal τ) = 2 := (orderOf_injective toGal hinj τ).trans h
  have hord' : orderOf (toGal τ') = 2 := (orderOf_injective toGal hinj τ').trans h'
  classical
  have : Fintype (F ≃ₐ[ZMod 2] F) := Fintype.ofFinite _
  have hdvd : 2 ∣ Fintype.card (F ≃ₐ[ZMod 2] F) := by
    have h0 : orderOf (toGal τ) ∣ Fintype.card (F ≃ₐ[ZMod 2] F) := orderOf_dvd_card
    rwa [hord] at h0
  have hcard := IsCyclic.card_orderOf_eq_totient hdvd
  rw [Nat.totient_two] at hcard
  have h1 : toGal τ = toGal τ' := by
    have hm : toGal τ ∈ Finset.univ.filter (fun a : F ≃ₐ[ZMod 2] F => orderOf a = 2) := by
      simp [hord]
    have hm' : toGal τ' ∈ Finset.univ.filter (fun a : F ≃ₐ[ZMod 2] F => orderOf a = 2) := by
      simp [hord']
    exact Finset.card_le_one.1 hcard.le _ hm _ hm'
  exact hinj h1

end Galois

section Gamma

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_data_of_involution (ρ : SL(2, F) ≃* SL(2, F))
    (hU : ∀ x, ρ x ∈ utri F ↔ x ∈ utri F) (hL : ∀ x, ρ x ∈ ltri F ↔ x ∈ ltri F)
    (hρρ : ∀ x, ρ (ρ x) = x) :
    ∃ (c : Fˣ) (σ : F ≃+* F), (c : F) * σ c = 1 ∧ (∀ s, σ (σ s) = s) ∧
      ∀ x, ρ x = torusElt c * sl2FieldAut σ x * (torusElt c)⁻¹ := by
  obtain ⟨c, σ, hc⟩ := exists_eq_torusElt_conj_sl2FieldAut ρ hU hL
  have hψu : ∀ s : F, ρ (utriElt s) = utriElt ((c : F) ^ 2 * σ s) := fun s => by
    rw [hc, sl2FieldAut_utriElt, torusElt_mul_utriElt_mul_inv]
  have hψψ : ∀ s : F, utriElt ((c : F) ^ 2 * σ ((c : F) ^ 2 * σ s)) = utriElt s := fun s => by
    rw [← hψu ((c : F) ^ 2 * σ s), ← hψu s, hρρ]
  have hnorm2 : ((c : F) * σ c) ^ 2 = 1 := by
    have h := utriElt_injective (hψψ 1)
    simpa [mul_pow] using h
  have hn : (c : F) * σ c = 1 := CharTwo.sq_injective (by simpa using hnorm2)
  refine ⟨c, σ, hn, fun s => ?_, hc⟩
  have h := utriElt_injective (hψψ s)
  rw [map_mul, map_pow] at h
  have h' : ((c : F) * σ c) ^ 2 * σ (σ s) = s := by rw [mul_pow]; linear_combination h
  rwa [hn, one_pow, one_mul] at h'

omit [Finite F] in
theorem eq_self_of_data_refl (c : Fˣ) (σ : F ≃+* F) (ρ : SL(2, F) ≃* SL(2, F))
    (hn : (c : F) * σ c = 1) (hσ : σ = RingEquiv.refl F)
    (hρ : ∀ x, ρ x = torusElt c * sl2FieldAut σ x * (torusElt c)⁻¹) (x : SL(2, F)) : ρ x = x := by
  have hc2 : (c : F) ^ 2 = 1 := by
    rw [sq]
    simpa [hσ] using hn
  have hc1 : c = 1 := Units.ext (CharTwo.sq_injective (by simpa using hc2))
  rw [hρ x, hc1, hσ, torusElt_one, sl2FieldAut_refl]
  simp

theorem eq_or_eq_one_of_commute_involutions (ρ₁ ρ₂ : SL(2, F) ≃* SL(2, F))
    (hU₁ : ∀ x, ρ₁ x ∈ utri F ↔ x ∈ utri F) (hL₁ : ∀ x, ρ₁ x ∈ ltri F ↔ x ∈ ltri F)
    (hU₂ : ∀ x, ρ₂ x ∈ utri F ↔ x ∈ utri F) (hL₂ : ∀ x, ρ₂ x ∈ ltri F ↔ x ∈ ltri F)
    (h₁ : ∀ x, ρ₁ (ρ₁ x) = x) (h₂ : ∀ x, ρ₂ (ρ₂ x) = x) (h₁₂ : ∀ x, ρ₁ (ρ₂ x) = ρ₂ (ρ₁ x)) :
    (∀ x, ρ₁ x = x) ∨ (∀ x, ρ₂ x = x) ∨ ∀ x, ρ₁ x = ρ₂ x := by
  obtain ⟨c₁, σ₁, hn₁, hσ₁, hρ₁⟩ := exists_data_of_involution ρ₁ hU₁ hL₁ h₁
  obtain ⟨c₂, σ₂, hn₂, hσ₂, hρ₂⟩ := exists_data_of_involution ρ₂ hU₂ hL₂ h₂
  by_cases hσ₁1 : σ₁ = RingEquiv.refl F
  · exact Or.inl (eq_self_of_data_refl c₁ σ₁ ρ₁ hn₁ hσ₁1 hρ₁)
  by_cases hσ₂1 : σ₂ = RingEquiv.refl F
  · exact Or.inr (Or.inl (eq_self_of_data_refl c₂ σ₂ ρ₂ hn₂ hσ₂1 hρ₂))
  right
  right
  have hord : ∀ σ : F ≃+* F, (∀ s, σ (σ s) = s) → σ ≠ RingEquiv.refl F → orderOf σ = 2 := by
    intro σ hσσ hσ1
    refine orderOf_eq_prime ?_ hσ1
    ext s
    exact hσσ s
  have hσ : σ₁ = σ₂ := ringAut_eq_of_orderOf_eq_two (hord σ₁ hσ₁ hσ₁1) (hord σ₂ hσ₂ hσ₂1)
  subst hσ
  have hsq : ∀ y, sl2FieldAut σ₁ (sl2FieldAut σ₁ y) = y := fun y => by
    apply sl2_ext <;> simp only [sl2FieldAut_apply_00, sl2FieldAut_apply_01,
      sl2FieldAut_apply_10, sl2FieldAut_apply_11, hσ₁]
  have hcomp : ∀ x, ρ₁ (ρ₂ x) = torusElt (c₁ * Units.map (σ₁ : F →* F) c₂) * x *
      (torusElt (c₁ * Units.map (σ₁ : F →* F) c₂))⁻¹ := fun x => by
    rw [hρ₂ x, hρ₁, map_mul, map_mul, map_inv, sl2FieldAut_torusElt, hsq x, torusElt_mul]
    group
  have hd2 : ∀ x, torusElt (c₁ * Units.map (σ₁ : F →* F) c₂) *
      (torusElt (c₁ * Units.map (σ₁ : F →* F) c₂) * x *
        (torusElt (c₁ * Units.map (σ₁ : F →* F) c₂))⁻¹) *
      (torusElt (c₁ * Units.map (σ₁ : F →* F) c₂))⁻¹ = x := fun x => by
    rw [← hcomp, ← hcomp, ← h₁₂ (ρ₂ x), h₂, h₁]
  have h := hd2 (utriElt 1)
  rw [torusElt_mul_utriElt_mul_inv, torusElt_mul_utriElt_mul_inv] at h
  have h' := utriElt_injective h
  have hd4 : (((c₁ * Units.map (σ₁ : F →* F) c₂ : Fˣ) : F) ^ 2) ^ 2 = 1 := by
    linear_combination h'
  have hd1 : ((c₁ * Units.map (σ₁ : F →* F) c₂ : Fˣ) : F) ^ 2 = 1 :=
    CharTwo.sq_injective (by simpa using hd4)
  have hd0 : c₁ * Units.map (σ₁ : F →* F) c₂ = 1 :=
    Units.ext (CharTwo.sq_injective (by simpa using hd1))
  intro x
  have h3 := hcomp (ρ₂ x)
  rw [h₂ x, hd0, torusElt_one] at h3
  simpa using h3

end Gamma

section QuotConj

variable {G : Type*} [Group G]

@[expose] def conjAutOfSubgroup (X : Subgroup G) (b : G) (hb : conjSubgroup b X = X) :
    ↥X ≃* ↥X :=
  ((MulAut.conj b).subgroupMap X).trans (MulEquiv.subgroupCongr hb)

theorem coe_conjAutOfSubgroup (X : Subgroup G) (b : G) (hb : conjSubgroup b X = X) (x : ↥X) :
    ((conjAutOfSubgroup X b hb x : ↥X) : G) = b * x * b⁻¹ := rfl

theorem mem_iff_conj_of_conjSubgroup_eq {X : Subgroup G} {b : G} (hb : conjSubgroup b X = X)
    (z : G) : z ∈ X ↔ b⁻¹ * z * b ∈ X := by
  conv_lhs => rw [← hb]
  exact mem_conjSubgroup

variable (X M : Subgroup G) [(M.subgroupOf X).Normal]

@[expose] noncomputable def quotConjAut (b : G) (hbX : conjSubgroup b X = X)
    (hbM : conjSubgroup b M = M) : ↥X ⧸ M.subgroupOf X ≃* ↥X ⧸ M.subgroupOf X :=
  QuotientGroup.congr (M.subgroupOf X) (M.subgroupOf X) (conjAutOfSubgroup X b hbX) (by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : (x : G) ∈ M := Subgroup.mem_subgroupOf.1 hx
      rw [Subgroup.mem_subgroupOf]
      show b * (x : G) * b⁻¹ ∈ M
      have : b * (x : G) * b⁻¹ ∈ conjSubgroup b M := ⟨x, hx', rfl⟩
      rwa [hbM] at this
    · intro hy
      have hy' : (y : G) ∈ M := Subgroup.mem_subgroupOf.1 hy
      refine ⟨(conjAutOfSubgroup X b hbX).symm y, ?_,
        (conjAutOfSubgroup X b hbX).apply_symm_apply y⟩
      have hψ : b * (((conjAutOfSubgroup X b hbX).symm y : ↥X) : G) * b⁻¹ = y :=
        congrArg Subtype.val ((conjAutOfSubgroup X b hbX).apply_symm_apply y)
      rw [Subgroup.mem_subgroupOf]
      have h1 := (mem_iff_conj_of_conjSubgroup_eq hbM (y : G)).1 hy'
      rwa [← hψ, show b⁻¹ * (b * (((conjAutOfSubgroup X b hbX).symm y : ↥X) : G) * b⁻¹) * b =
        (((conjAutOfSubgroup X b hbX).symm y : ↥X) : G) by group] at h1)

theorem quotConjAut_mk (b : G) (hbX : conjSubgroup b X = X) (hbM : conjSubgroup b M = M)
    (x : ↥X) : quotConjAut X M b hbX hbM (QuotientGroup.mk x) =
      QuotientGroup.mk ⟨b * (x : G) * b⁻¹, (conjAutOfSubgroup X b hbX x).2⟩ := rfl

theorem map_subgroupOf_conjSubgroup_eq (b : G) (hbX : conjSubgroup b X = X)
    (hbM : conjSubgroup b M = M) (A : Subgroup G) :
    ((conjSubgroup b A).subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X)) =
      ((A.subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X))).map
        (quotConjAut X M b hbX hbM).toMonoidHom := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : b⁻¹ * (x : G) * b ∈ A := mem_conjSubgroup.1 (Subgroup.mem_subgroupOf.1 hx)
    have hxb : b⁻¹ * (x : G) * b ∈ X := (mem_iff_conj_of_conjSubgroup_eq hbX x).1 x.2
    refine ⟨QuotientGroup.mk' _ ⟨b⁻¹ * x * b, hxb⟩,
      Subgroup.mem_map.2 ⟨⟨b⁻¹ * x * b, hxb⟩, Subgroup.mem_subgroupOf.2 hx', rfl⟩, ?_⟩
    show quotConjAut X M b hbX hbM (QuotientGroup.mk _) = QuotientGroup.mk' _ x
    rw [quotConjAut_mk]
    exact congrArg (QuotientGroup.mk' (M.subgroupOf X)) (Subtype.ext (by group))
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
    exact ⟨⟨b * x * b⁻¹, (conjAutOfSubgroup X b hbX x).2⟩,
      Subgroup.mem_subgroupOf.2 (conj_mem_conjSubgroup b (Subgroup.mem_subgroupOf.1 hx)), rfl⟩

theorem map_subgroupOf_conjSubgroup_of_mem (A : Subgroup G) {g : G} (hg : g ∈ X) :
    ((conjSubgroup g A).subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X)) =
      conjSubgroup (QuotientGroup.mk' (M.subgroupOf X) ⟨g, hg⟩)
        ((A.subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X))) := by
  rw [← map_conjSubgroup, ← conjSubgroup_subgroupOf X A ⟨g, hg⟩]

theorem quotConjAut_quotConjAut_of_mul_self (b : G) (hbX : conjSubgroup b X = X)
    (hbM : conjSubgroup b M = M) (hb : b * b = 1) (z : ↥X ⧸ M.subgroupOf X) :
    quotConjAut X M b hbX hbM (quotConjAut X M b hbX hbM z) = z := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  rw [quotConjAut_mk, quotConjAut_mk]
  refine congrArg QuotientGroup.mk (Subtype.ext ?_)
  show b * (b * (x : G) * b⁻¹) * b⁻¹ = x
  calc b * (b * (x : G) * b⁻¹) * b⁻¹ = (b * b) * x * (b * b)⁻¹ := by group
    _ = x := by rw [hb]; group

theorem quotConjAut_comm (b b' : G) (hbX : conjSubgroup b X = X) (hbM : conjSubgroup b M = M)
    (hbX' : conjSubgroup b' X = X) (hbM' : conjSubgroup b' M = M) (hcomm : b * b' = b' * b)
    (z : ↥X ⧸ M.subgroupOf X) :
    quotConjAut X M b hbX hbM (quotConjAut X M b' hbX' hbM' z) =
      quotConjAut X M b' hbX' hbM' (quotConjAut X M b hbX hbM z) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  rw [quotConjAut_mk, quotConjAut_mk, quotConjAut_mk, quotConjAut_mk]
  refine congrArg QuotientGroup.mk (Subtype.ext ?_)
  show b * (b' * (x : G) * b'⁻¹) * b⁻¹ = b' * (b * (x : G) * b⁻¹) * b'⁻¹
  calc b * (b' * (x : G) * b'⁻¹) * b⁻¹ = (b * b') * x * (b * b')⁻¹ := by group
    _ = (b' * b) * x * (b' * b)⁻¹ := by rw [hcomm]
    _ = b' * (b * (x : G) * b⁻¹) * b'⁻¹ := by group

theorem mem_of_quotConjAut_mk_eq (b : G) (hbX : conjSubgroup b X = X)
    (hbM : conjSubgroup b M = M) (x : ↥X)
    (h : quotConjAut X M b hbX hbM (QuotientGroup.mk x) = QuotientGroup.mk x) :
    (x : G)⁻¹ * (b * (x : G) * b⁻¹) ∈ M := by
  rw [quotConjAut_mk] at h
  have h1 := QuotientGroup.eq.1 h.symm
  exact Subgroup.mem_subgroupOf.1 h1

end QuotConj

section Transport

variable {F F' : Type} [Field F] [Field F']

@[expose] def sl2MulEquivOfRingEquiv (ρ : F ≃+* F') : SL(2, F) ≃* SL(2, F') where
  toFun g := Matrix.SpecialLinearGroup.map (ρ : F →+* F') g
  invFun g := Matrix.SpecialLinearGroup.map (ρ.symm : F' →+* F) g
  left_inv g := by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  right_inv g := by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  map_mul' g h := map_mul (Matrix.SpecialLinearGroup.map (ρ : F →+* F')) g h

theorem exists_mulEquiv_psl_of_mulEquiv_sl2 {X : Type*} [Group X] [Finite F] [CharP F 2]
    {f : ℕ} (hf : f ≠ 0) (hcard : Nat.card F = 2 ^ f) (e : X ≃* SL(2, F)) :
    Nonempty (X ≃* PSL(2, GaloisField 2 f)) := by
  have : Fintype F := Fintype.ofFinite F
  have : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hGF : Fintype.card F = Fintype.card (GaloisField 2 f) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard,
      GaloisField.card 2 f hf]
  exact ⟨(e.trans (sl2MulEquivOfRingEquiv (FiniteField.ringEquivOfCardEq hGF))).trans
    pslMulEquivSL.symm⟩

end Transport

end CFSG.CGT.Timmesfeld75
