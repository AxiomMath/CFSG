module

public import CFSG.Foundations.Basic
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup
open scoped commutatorElement Pointwise

variable {K : Type*} [Group K]

@[expose] def borel (P : Subgroup K) : Subgroup K := normalizer (P : Set K)

@[expose] def cartan (P : Subgroup K) (t : K) : Subgroup K := borel P ⊓ conjugate (borel P) t

@[expose] def rootCenter (P : Subgroup K) : Subgroup K := P ⊓ centralizer (P : Set K)

theorem mem_conjugate_iff_mul_inv {A : Subgroup K} {g x : K} :
    x ∈ conjugate A g ↔ g * x * g⁻¹ ∈ A := by
  simp only [conjugate, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [mul_assoc] using ha
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

theorem inv_eq_of_mul_self {t : K} (ht : t * t = 1) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right ht

theorem exists_sq_eq_of_odd_orderOf {a : K} (ha : Odd (orderOf a)) :
    ∃ k : ℕ, a ^ k * a ^ k = a := by
  obtain ⟨m, hm⟩ := ha
  refine ⟨m + 1, ?_⟩
  rw [← pow_add, show m + 1 + (m + 1) = orderOf a + 1 by omega, pow_succ, pow_orderOf_eq_one,
    one_mul]

structure BenderCore (q i e : ℕ) (P : Subgroup K) (t : K) : Prop where
  sq_eq_one : t * t = 1
  not_mem : t ∉ borel P
  strong : IsStronglyEmbedded (borel P)
  index_eq : (borel P).index = q ^ i + 1
  card_eq : Nat.card P = q ^ i
  sup_eq : P ⊔ cartan P t = borel P
  inf_eq : P ⊓ cartan P t = ⊥
  isCyclic : IsCyclic (cartan P t)
  card_cartan : Nat.card (cartan P t) = (q - 1) * e
  ncard_inv : {x : K | x ∈ cartan P t ∧ t * x * t = x⁻¹}.ncard = q - 1
  card_center : Nat.card (rootCenter P) = q
  center_sq : ∀ z ∈ rootCenter P, z * z = 1
  center_of_involution : ∀ g ∈ borel P, orderOf g = 2 → g ∈ rootCenter P

variable {q i e : ℕ} {P : Subgroup K} {t : K}

theorem le_borel (P : Subgroup K) : P ≤ borel P :=
  Subgroup.le_normalizer

theorem BenderCore.bruhat [Finite K] (h : BenderCore q i e P t) {g : K} (hg : g ∉ borel P) :
    ∃ p ∈ P, ∃ m ∈ borel P, g = p * t * m := by
  classical
  have hti : t⁻¹ = t := inv_eq_of_mul_self h.sq_eq_one
  let F : Option P → K ⧸ borel P := fun o =>
    o.elim (QuotientGroup.mk 1) (fun p => QuotientGroup.mk ((p : K) * t))
  have hinj : Function.Injective F := by
    rintro (_ | p) (_ | p') hpp
    · rfl
    · exfalso
      have h1 : ((1 : K))⁻¹ * ((p' : K) * t) ∈ borel P := QuotientGroup.eq.mp hpp
      rw [inv_one, one_mul] at h1
      exact h.not_mem (by
        have := (borel P).mul_mem ((borel P).inv_mem (le_borel P p'.2)) h1
        simpa using this)
    · exfalso
      have h1 : ((p : K) * t)⁻¹ * 1 ∈ borel P := QuotientGroup.eq.mp hpp
      rw [mul_one] at h1
      have h2 : (p : K) * t ∈ borel P := by simpa using (borel P).inv_mem h1
      exact h.not_mem (by
        have := (borel P).mul_mem ((borel P).inv_mem (le_borel P p.2)) h2
        simpa using this)
    · have h1 : ((p : K) * t)⁻¹ * ((p' : K) * t) ∈ borel P := QuotientGroup.eq.mp hpp
      have hx : (p : K)⁻¹ * p' ∈ cartan P t := by
        refine Subgroup.mem_inf.mpr ⟨le_borel P (P.mul_mem (P.inv_mem p.2) p'.2), ?_⟩
        rw [mem_conjugate_iff_mul_inv, hti]
        have : t * ((p : K)⁻¹ * p') * t = ((p : K) * t)⁻¹ * ((p' : K) * t) := by
          simp [mul_assoc, hti]
        rw [this]
        exact h1
      have hx' : (p : K)⁻¹ * p' ∈ P ⊓ cartan P t :=
        ⟨P.mul_mem (P.inv_mem p.2) p'.2, hx⟩
      rw [h.inf_eq, Subgroup.mem_bot] at hx'
      exact congrArg some (Subtype.ext (inv_mul_eq_one.mp hx'))
  have hcard : Nat.card (K ⧸ borel P) ≤ Nat.card (Option P) := by
    have : Nat.card (K ⧸ borel P) = q ^ i + 1 := h.index_eq
    rw [this]
    have h2 : Nat.card (Option P) = Nat.card P + 1 := by
      have : Finite P := inferInstance
      have : Fintype P := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_option]
    rw [h2, h.card_eq]
  have hbij : Function.Bijective F := hinj.bijective_of_nat_card_le hcard
  obtain ⟨o, ho⟩ := hbij.2 (QuotientGroup.mk g)
  rcases o with _ | p
  · exfalso
    have h1 : ((1 : K))⁻¹ * g ∈ borel P := QuotientGroup.eq.mp ho
    rw [inv_one, one_mul] at h1
    exact hg h1
  · have h1 : ((p : K) * t)⁻¹ * g ∈ borel P := QuotientGroup.eq.mp ho
    refine ⟨p, p.2, ((p : K) * t)⁻¹ * g, h1, ?_⟩
    simp [mul_assoc]

section Transport

variable {K' : Type*} [Group K']

theorem map_conjugate (φ : K ≃* K') (A : Subgroup K) (g : K) :
    (conjugate A g).map φ.toMonoidHom = conjugate (A.map φ.toMonoidHom) (φ g) := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_conjugate_iff_mul_inv, mem_conjugate_iff_mul_inv,
    Subgroup.mem_map_equiv]
  simp

theorem borel_map (φ : K ≃* K') (P : Subgroup K) :
    borel (P.map φ.toMonoidHom) = (borel P).map φ.toMonoidHom :=
  (Subgroup.map_equiv_normalizer_eq P φ).symm

theorem cartan_map (φ : K ≃* K') (P : Subgroup K) (t : K) :
    cartan (P.map φ.toMonoidHom) (φ t) = (cartan P t).map φ.toMonoidHom := by
  unfold cartan
  rw [borel_map, ← map_conjugate, Subgroup.map_inf _ _ _ φ.injective]

theorem rootCenter_map (φ : K ≃* K') (P : Subgroup K) :
    rootCenter (P.map φ.toMonoidHom) = (rootCenter P).map φ.toMonoidHom := by
  unfold rootCenter
  rw [Subgroup.map_inf _ _ _ φ.injective]
  congr 1
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx y hy
    have := hx (φ y) (Subgroup.mem_map_of_mem _ hy)
    have h2 := congrArg φ.symm this
    simpa using h2
  · intro hx y hy
    rw [SetLike.mem_coe, Subgroup.mem_map_equiv] at hy
    have := hx _ hy
    have h2 := congrArg φ this
    simpa using h2

theorem IsStronglyEmbedded.map {M : Subgroup K} (hM : IsStronglyEmbedded M) (φ : K ≃* K') :
    IsStronglyEmbedded (M.map φ.toMonoidHom) := by
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    apply hM.1
    apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
    rw [htop, Subgroup.map_top_of_surjective _ φ.surjective]
  · simpa only [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective] using hM.2.1
  · intro g hg
    have hpre : φ.symm g ∉ M := by
      intro hmem
      apply hg
      simpa using Subgroup.mem_map_of_mem φ.toMonoidHom hmem
    have h1 := hM.2.2 (φ.symm g) hpre
    have h2 : (M ⊓ conjugate M (φ.symm g)).map φ.toMonoidHom =
        M.map φ.toMonoidHom ⊓ conjugate (M.map φ.toMonoidHom) g := by
      rw [Subgroup.map_inf _ _ _ φ.injective, map_conjugate, MulEquiv.apply_symm_apply]
    rw [← h2, Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
    exact h1

theorem BenderCore.map (h : BenderCore q i e P t) (φ : K ≃* K') :
    BenderCore q i e (P.map φ.toMonoidHom) (φ t) where
  sq_eq_one := by rw [← map_mul, h.sq_eq_one, map_one]
  not_mem := by
    rw [borel_map]
    intro hmem
    exact h.not_mem (by simpa using Subgroup.mem_map_equiv.mp hmem)
  strong := by
    rw [borel_map]
    exact IsStronglyEmbedded.map h.strong φ
  index_eq := by
    rw [borel_map, Subgroup.index_map_of_bijective φ.bijective]
    exact h.index_eq
  card_eq := by
    rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
    exact h.card_eq
  sup_eq := by
    rw [cartan_map, borel_map, ← Subgroup.map_sup, h.sup_eq]
  inf_eq := by
    rw [cartan_map, ← Subgroup.map_inf _ _ _ φ.injective, h.inf_eq, Subgroup.map_bot]
  isCyclic := by
    rw [cartan_map]
    exact (MulEquiv.subgroupMap φ (cartan P t)).isCyclic.mp h.isCyclic
  card_cartan := by
    rw [cartan_map, Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
    exact h.card_cartan
  ncard_inv := by
    have hset : {x : K' | x ∈ cartan (P.map φ.toMonoidHom) (φ t) ∧ φ t * x * φ t = x⁻¹} =
        φ '' {x : K | x ∈ cartan P t ∧ t * x * t = x⁻¹} := by
      ext x
      rw [cartan_map]
      constructor
      · rintro ⟨hx1, hx2⟩
        refine ⟨φ.symm x, ⟨Subgroup.mem_map_equiv.mp hx1, ?_⟩, by simp⟩
        have := congrArg φ.symm hx2
        simpa using this
      · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
        refine ⟨Subgroup.mem_map_of_mem φ.toMonoidHom hy1, ?_⟩
        have := congrArg φ hy2
        simpa using this
    rw [hset, Set.ncard_image_of_injective _ φ.injective]
    exact h.ncard_inv
  card_center := by
    rw [rootCenter_map, Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
    exact h.card_center
  center_sq := by
    intro z hz
    rw [rootCenter_map] at hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, h.center_sq y hy, map_one]
  center_of_involution := by
    intro g hg hord
    rw [borel_map] at hg
    rw [rootCenter_map]
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
    simp only [MulEquiv.coe_toMonoidHom] at hord ⊢
    rw [MulEquiv.orderOf_eq] at hord
    exact Subgroup.mem_map_of_mem _ (h.center_of_involution y hy hord)

end Transport

section Conjugacy

theorem BenderCore.odd_card_cartan [Finite K] (h : BenderCore q i e P t) :
    Odd (Nat.card (cartan P t)) := h.strong.2.2 t h.not_mem

theorem BenderCore.exists_conj_eq [Finite K] (h : BenderCore q i e P t) {t' : K}
    (ht' : t' * t' = 1) (hmem : t' ∉ borel P) : ∃ m ∈ borel P, t' = m⁻¹ * t * m := by
  classical
  have hti : t⁻¹ = t := inv_eq_of_mul_self h.sq_eq_one
  obtain ⟨p, hp, m, hm, rfl⟩ := h.bruhat hmem
  have ha : m * p ∈ borel P := (borel P).mul_mem hm (le_borel P hp)
  have htm : t * (m * p) * t = (m * p)⁻¹ := by
    have h1 : p * t * m * (p * t * m) = 1 := ht'
    calc t * (m * p) * t = p⁻¹ * (p * t * m * (p * t * m)) * m⁻¹ := by group
      _ = (m * p)⁻¹ := by rw [h1]; group
  have hac : m * p ∈ cartan P t := by
    refine Subgroup.mem_inf.mpr ⟨ha, ?_⟩
    rw [mem_conjugate_iff_mul_inv, hti, htm]
    exact (borel P).inv_mem ha
  have hodd : Odd (orderOf (m * p)) :=
    Odd.of_dvd_nat h.odd_card_cartan (Subgroup.orderOf_dvd_natCard (cartan P t) hac)
  obtain ⟨k, hk⟩ := exists_sq_eq_of_odd_orderOf hodd
  set b := (m * p) ^ k with hbdef
  have htb : t * b * t = b⁻¹ := by
    have h1 : (t * (m * p) * t⁻¹) ^ k = t * (m * p) ^ k * t⁻¹ := conj_pow
    rw [hti, htm, inv_pow] at h1
    exact h1.symm
  have hbt : b⁻¹ * t * b = t * (m * p) := by
    calc b⁻¹ * t * b = (t * b * t) * t * b := by rw [← htb]
      _ = t * b * (t * t) * b := by group
      _ = t * (b * b) := by rw [h.sq_eq_one]; group
      _ = t * (m * p) := by rw [hk]
  have hbM : b ∈ borel P := (borel P).pow_mem ha k
  refine ⟨b * p⁻¹, (borel P).mul_mem hbM ((borel P).inv_mem (le_borel P hp)), ?_⟩
  calc p * t * m = p * (t * (m * p)) * p⁻¹ := by group
    _ = p * (b⁻¹ * t * b) * p⁻¹ := by rw [hbt]
    _ = (b * p⁻¹)⁻¹ * t * (b * p⁻¹) := by group

theorem map_conj_eq_of_mem_borel {m : K} (hm : m ∈ borel P) :
    P.map (MulAut.conj m⁻¹).toMonoidHom = P := by
  ext x
  rw [Subgroup.mem_map_equiv]
  have := (Subgroup.mem_normalizer_iff.mp hm x)
  simpa [MulAut.conj_symm_apply] using this.symm

theorem BenderCore.of_involution [Finite K] (h : BenderCore q i e P t) {t' : K}
    (ht' : t' * t' = 1) (hmem : t' ∉ borel P) : BenderCore q i e P t' := by
  obtain ⟨m, hm, rfl⟩ := h.exists_conj_eq ht' hmem
  have := h.map (MulAut.conj m⁻¹)
  rw [map_conj_eq_of_mem_borel hm] at this
  simpa using this

end Conjugacy

section Cartan

theorem cartan_le_borel (P : Subgroup K) (t : K) : cartan P t ≤ borel P := inf_le_left

theorem BenderCore.cartan_mul_mul (h : BenderCore q i e P t) {x : K} (hx : x ∈ cartan P t) :
    t * x * t ∈ cartan P t := by
  have hti : t⁻¹ = t := inv_eq_of_mul_self h.sq_eq_one
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  rw [mem_conjugate_iff_mul_inv, hti] at hx2
  refine Subgroup.mem_inf.mpr ⟨hx2, ?_⟩
  rw [mem_conjugate_iff_mul_inv, hti]
  have : t * (t * x * t) * t = x := by
    calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [h.sq_eq_one]; group
  rw [this]
  exact hx1

theorem BenderCore.cartan_comm (h : BenderCore q i e P t) {x y : K} (hx : x ∈ cartan P t)
    (hy : y ∈ cartan P t) : x * y = y * x := by
  have := h.isCyclic
  have := (IsMulCommutative.is_comm (M := ↥(cartan P t))).comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem eq_one_or_eq_of_mem_zpowers {t g : K} (ht : t * t = 1) (hg : g ∈ Subgroup.zpowers t) :
    g = 1 ∨ g = t := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hsq : t ^ 2 = 1 := by rw [sq]; exact ht
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, ← sq, hsq, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_one, zpow_two, ht, one_zpow, one_mul]

theorem BenderCore.mem_commutator_cartan_iff [Finite K] (h : BenderCore q i e P t) {x : K} :
    x ∈ ⁅cartan P t, Subgroup.zpowers t⁆ ↔ x ∈ cartan P t ∧ t * x * t = x⁻¹ := by
  have hti : t⁻¹ = t := inv_eq_of_mul_self h.sq_eq_one
  have key : ∀ a b : K, t * (a * b) * t = (t * a * t) * (t * b * t) := fun a b => by
    calc t * (a * b) * t = t * a * (t * t) * b * t := by rw [h.sq_eq_one]; group
      _ = (t * a * t) * (t * b * t) := by group
  have kk : ∀ a : K, t * (t * a * t) * t = a := fun a => by
    calc t * (t * a * t) * t = (t * t) * a * (t * t) := by group
      _ = a := by rw [h.sq_eq_one]; group
  constructor
  · intro hx
    rw [Subgroup.commutator_def] at hx
    refine Subgroup.closure_induction (p := fun x _ => x ∈ cartan P t ∧ t * x * t = x⁻¹)
      ?_ ?_ ?_ ?_ hx
    · rintro x ⟨d, hd, g, hg, rfl⟩
      rcases eq_one_or_eq_of_mem_zpowers h.sq_eq_one hg with hg1 | hg1
      · rw [hg1, commutatorElement_one_right]
        exact ⟨(cartan P t).one_mem, by simp [h.sq_eq_one]⟩
      · rw [hg1]
        have hd' : t * d⁻¹ * t ∈ cartan P t := h.cartan_mul_mul ((cartan P t).inv_mem hd)
        have hcomm : ⁅d, t⁆ = d * (t * d⁻¹ * t) := by
          simp [commutatorElement_def, hti, mul_assoc]
        rw [hcomm]
        refine ⟨(cartan P t).mul_mem hd hd', ?_⟩
        rw [key d (t * d⁻¹ * t), kk d⁻¹, mul_inv_rev]
        congr 2
        simp [hti, mul_assoc]
    · exact ⟨(cartan P t).one_mem, by simp [h.sq_eq_one]⟩
    · rintro x y _ _ ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
      refine ⟨(cartan P t).mul_mem hx1 hy1, ?_⟩
      rw [key, hx2, hy2, mul_inv_rev,
        h.cartan_comm ((cartan P t).inv_mem hx1) ((cartan P t).inv_mem hy1)]
    · rintro x _ ⟨hx1, hx2⟩
      refine ⟨(cartan P t).inv_mem hx1, ?_⟩
      have : t * x⁻¹ * t = (t * x * t)⁻¹ := by simp [hti, mul_assoc]
      rw [this, hx2]
  · rintro ⟨hx1, hx2⟩
    have hodd : Odd (orderOf x) :=
      Odd.of_dvd_nat h.odd_card_cartan (Subgroup.orderOf_dvd_natCard (cartan P t) hx1)
    obtain ⟨k, hk⟩ := exists_sq_eq_of_odd_orderOf hodd
    set y := x ^ k with hy
    have hyD : y ∈ cartan P t := (cartan P t).pow_mem hx1 k
    have hty : t * y * t = y⁻¹ := by
      have h1 : (t * x * t⁻¹) ^ k = t * x ^ k * t⁻¹ := conj_pow
      rw [hti, hx2, inv_pow] at h1
      exact h1.symm
    have : ⁅y, t⁆ = x := by
      calc ⁅y, t⁆ = y * (t * y⁻¹ * t) := by simp [commutatorElement_def, hti, mul_assoc]
        _ = y * (t * y * t)⁻¹ := by simp [hti, mul_assoc]
        _ = y * y := by rw [hty, inv_inv]
        _ = x := hk
    rw [← this]
    exact Subgroup.commutator_mem_commutator hyD (Subgroup.mem_zpowers t)

end Cartan

section Helpers

theorem le_normalizer_of_commute {A B : Subgroup K} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    B ≤ normalizer (A : Set K) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have h1 := hc a ha b hb
    have : b * a * b⁻¹ = a := by rw [← h1]; group
    rw [this]
    exact ha
  · intro ha'
    have h1 := hc _ ha' b⁻¹ (B.inv_mem hb)
    have : a = b * a * b⁻¹ := by
      calc a = b⁻¹ * (b * a * b⁻¹) * b := by group
        _ = (b * a * b⁻¹) * b⁻¹ * b := by rw [← h1]
        _ = b * a * b⁻¹ := by group
    rw [this]
    exact ha'

theorem card_sup_eq_mul_of_le_normalizer [Finite K] {A B : Subgroup K}
    (hB : B ≤ normalizer (A : Set K)) (hd : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left A B hB
  let f : A × B → ↥(A ⊔ B) := fun p => ⟨(p.1 : K) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨a1, ha1⟩, ⟨b1, hb1⟩⟩ ⟨⟨a2, ha2⟩, ⟨b2, hb2⟩⟩ heq
      have h1 : a1 * b1 = a2 * b2 := congrArg Subtype.val heq
      have h2 : a2⁻¹ * a1 = b2 * b1⁻¹ := by
        calc a2⁻¹ * a1 = a2⁻¹ * (a1 * b1) * b1⁻¹ := by group
          _ = a2⁻¹ * (a2 * b2) * b1⁻¹ := by rw [h1]
          _ = b2 * b1⁻¹ := by group
      have h3 : a2⁻¹ * a1 ∈ A ⊓ B :=
        ⟨A.mul_mem (A.inv_mem ha2) ha1, h2 ▸ B.mul_mem hb2 (B.inv_mem hb1)⟩
      rw [hd, Subgroup.mem_bot] at h3
      have ha : a2 = a1 := inv_mul_eq_one.mp h3
      subst ha
      have hb : b1 = b2 := mul_left_cancel h1
      subst hb
      rfl
    · rintro ⟨x, hx⟩
      have hx' : x ∈ (A : Set K) * (B : Set K) := by rw [← hset]; exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem card_sup_eq_mul_of_commute [Finite K] {A B : Subgroup K}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hd : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B :=
  card_sup_eq_mul_of_le_normalizer (le_normalizer_of_commute hc) hd

theorem exists_mul_of_mem_sup_of_commute {A B : Subgroup K}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : K} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left A B (le_normalizer_of_commute hc)
  have hx' : x ∈ (A : Set K) * (B : Set K) := by rw [← hset]; exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem eq_of_card_eq_of_cyclic [Finite K] {D A B : Subgroup K} (hD : IsCyclic D) (hA : A ≤ D)
    (hB : B ≤ D) (hcard : Nat.card A = Nat.card B) : A = B := by
  have h1 : A.subgroupOf D = B.subgroupOf D := by
    apply IsCyclic.subgroup_eq_iff_card_eq.mpr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv]
    exact hcard
  have h2 := Subgroup.subgroupOf_inj.mp h1
  rwa [inf_eq_left.mpr hA, inf_eq_left.mpr hB] at h2

end Helpers

section CartanDecomposition

@[expose] def fixCartan (P : Subgroup K) (t : K) : Subgroup K :=
  cartan P t ⊓ centralizer ({t} : Set K)

theorem BenderCore.mem_fixCartan_iff (h : BenderCore q i e P t) {x : K} :
    x ∈ fixCartan P t ↔ x ∈ cartan P t ∧ t * x * t = x := by
  have hti : t⁻¹ = t := inv_eq_of_mul_self h.sq_eq_one
  unfold fixCartan
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  apply and_congr_right
  intro _
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h1
    calc t * x * t = x * t * t := by rw [h1]
      _ = x := by rw [mul_assoc, h.sq_eq_one, mul_one]
  · intro h1
    calc t * x = t * x * t * t⁻¹ := by group
      _ = x * t := by rw [h1, hti]

theorem fixCartan_le_cartan (P : Subgroup K) (t : K) : fixCartan P t ≤ cartan P t := inf_le_left

theorem BenderCore.commutator_cartan_le [Finite K] (h : BenderCore q i e P t) :
    ⁅cartan P t, Subgroup.zpowers t⁆ ≤ cartan P t := fun _ hx =>
  (h.mem_commutator_cartan_iff.mp hx).1

theorem BenderCore.card_commutator_cartan [Finite K] (h : BenderCore q i e P t) :
    Nat.card ↥⁅cartan P t, Subgroup.zpowers t⁆ = q - 1 := by
  have hset : ((⁅cartan P t, Subgroup.zpowers t⁆ : Subgroup K) : Set K) =
      {x | x ∈ cartan P t ∧ t * x * t = x⁻¹} := by
    ext x
    exact h.mem_commutator_cartan_iff
  rw [← h.ncard_inv, ← hset, ← Nat.card_coe_set_eq]
  rfl

theorem BenderCore.inf_commutator_fixCartan [Finite K] (h : BenderCore q i e P t) :
    ⁅cartan P t, Subgroup.zpowers t⁆ ⊓ fixCartan P t = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxD, hinv⟩ := h.mem_commutator_cartan_iff.mp hx1
  obtain ⟨-, hfix⟩ := h.mem_fixCartan_iff.mp hx2
  have h0 : x = x⁻¹ := hfix.symm.trans hinv
  have hsq : x ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [h0]
    exact inv_mul_cancel x
  have hodd : Odd (orderOf x) :=
    Odd.of_dvd_nat h.odd_card_cartan (Subgroup.orderOf_dvd_natCard (cartan P t) hxD)
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have h1 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact h1
    · rw [h1] at hodd
      exact absurd hodd (by decide)
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)

theorem BenderCore.cartan_le_sup [Finite K] (h : BenderCore q i e P t) :
    cartan P t ≤ ⁅cartan P t, Subgroup.zpowers t⁆ ⊔ fixCartan P t := by
  intro x hx
  have hti : t⁻¹ = t := inv_eq_of_mul_self h.sq_eq_one
  have hφ : t * x * t ∈ cartan P t := h.cartan_mul_mul hx
  have hcomm := h.cartan_comm hx hφ
  have hy : x * (t * x * t) ∈ fixCartan P t := by
    rw [h.mem_fixCartan_iff]
    refine ⟨(cartan P t).mul_mem hx hφ, ?_⟩
    have hkey : t * (x * (t * x * t)) * t = (t * x * t) * (t * (t * x * t) * t) := by
      calc t * (x * (t * x * t)) * t = t * x * (t * t) * (t * x * t) * t := by
            rw [h.sq_eq_one]; group
        _ = (t * x * t) * (t * (t * x * t) * t) := by group
    have hkk : t * (t * x * t) * t = x := by
      calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
        _ = x := by rw [h.sq_eq_one]; group
    rw [hkey, hkk]
    exact hcomm.symm
  have hz : ⁅x, t⁆ ∈ ⁅cartan P t, Subgroup.zpowers t⁆ :=
    Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers t)
  have hzD : ⁅x, t⁆ ∈ cartan P t := h.commutator_cartan_le hz
  have hzeq : ⁅x, t⁆ = x * (t * x⁻¹ * t) := by
    simp [commutatorElement_def, hti, mul_assoc]
  have hφinv : t * x⁻¹ * t = (t * x * t)⁻¹ := by simp [hti, mul_assoc]
  have hyz : (x * (t * x * t)) * ⁅x, t⁆ = x ^ 2 := by
    rw [hzeq, hφinv]
    calc x * (t * x * t) * (x * (t * x * t)⁻¹)
        = x * ((t * x * t) * x) * (t * x * t)⁻¹ := by group
      _ = x * (x * (t * x * t)) * (t * x * t)⁻¹ := by rw [hcomm]
      _ = x * x := by group
      _ = x ^ 2 := (sq x).symm
  have hodd : Odd (orderOf x) :=
    Odd.of_dvd_nat h.odd_card_cartan (Subgroup.orderOf_dvd_natCard (cartan P t) hx)
  obtain ⟨k, hk⟩ := exists_sq_eq_of_odd_orderOf hodd
  have hyzc : Commute (x * (t * x * t)) ⁅x, t⁆ := h.cartan_comm ((cartan P t).mul_mem hx hφ) hzD
  have hxk : x = ⁅x, t⁆ ^ k * (x * (t * x * t)) ^ k := by
    calc x = x ^ k * x ^ k := hk.symm
      _ = (x ^ 2) ^ k := by rw [← pow_mul, ← pow_add, two_mul]
      _ = ((x * (t * x * t)) * ⁅x, t⁆) ^ k := by rw [hyz]
      _ = (x * (t * x * t)) ^ k * ⁅x, t⁆ ^ k := hyzc.mul_pow k
      _ = ⁅x, t⁆ ^ k * (x * (t * x * t)) ^ k :=
        ((hyzc.symm.pow_pow k k).eq).symm
  rw [hxk]
  exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ hz k) (Subgroup.pow_mem _ hy k)

theorem BenderCore.cartan_eq_sup [Finite K] (h : BenderCore q i e P t) :
    cartan P t = ⁅cartan P t, Subgroup.zpowers t⁆ ⊔ fixCartan P t :=
  le_antisymm h.cartan_le_sup (sup_le h.commutator_cartan_le (fixCartan_le_cartan P t))

theorem BenderCore.card_fixCartan [Finite K] (h : BenderCore q i e P t) :
    Nat.card (fixCartan P t) = e := by
  have hc : ∀ a ∈ ⁅cartan P t, Subgroup.zpowers t⁆, ∀ b ∈ fixCartan P t, a * b = b * a :=
    fun a ha b hb => h.cartan_comm (h.commutator_cartan_le ha) (fixCartan_le_cartan P t hb)
  have h1 := card_sup_eq_mul_of_commute hc h.inf_commutator_fixCartan
  rw [← h.cartan_eq_sup, h.card_cartan, h.card_commutator_cartan] at h1
  have hpos : 0 < q - 1 := by
    rw [← h.card_commutator_cartan]
    exact Nat.card_pos
  exact (Nat.eq_of_mul_eq_mul_left hpos h1).symm

end CartanDecomposition

section RootCenter

theorem rootCenter_le (P : Subgroup K) : rootCenter P ≤ P := inf_le_left

theorem mem_rootCenter_iff {P : Subgroup K} {z : K} :
    z ∈ rootCenter P ↔ z ∈ P ∧ ∀ p ∈ P, p * z = z * p := by
  unfold rootCenter
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  rfl

theorem conj_mem_rootCenter {P : Subgroup K} {d z : K} (hd : d ∈ borel P)
    (hz : z ∈ rootCenter P) : d * z * d⁻¹ ∈ rootCenter P := by
  rw [mem_rootCenter_iff] at hz ⊢
  obtain ⟨hzP, hzc⟩ := hz
  have hd' := Subgroup.mem_normalizer_iff.mp hd
  have hd'' := Subgroup.mem_normalizer_iff.mp ((borel P).inv_mem hd)
  refine ⟨(hd' z).mp hzP, fun p hp => ?_⟩
  have hp' : d⁻¹ * p * d ∈ P := by
    have := (hd'' p).mp hp
    simpa using this
  have h1 := hzc _ hp'
  calc p * (d * z * d⁻¹) = d * ((d⁻¹ * p * d) * z) * d⁻¹ := by group
    _ = d * (z * (d⁻¹ * p * d)) * d⁻¹ := by rw [h1]
    _ = d * z * d⁻¹ * p := by group

theorem BenderCore.involution_iff (h : BenderCore q i e P t) {g : K} :
    (g ∈ borel P ∧ orderOf g = 2) ↔ (g ∈ rootCenter P ∧ g ≠ 1) := by
  constructor
  · rintro ⟨hg, hord⟩
    refine ⟨h.center_of_involution g hg hord, ?_⟩
    rintro rfl
    simp at hord
  · rintro ⟨hg, hg1⟩
    refine ⟨le_borel P (rootCenter_le P hg), ?_⟩
    apply orderOf_eq_prime _ hg1
    rw [sq]
    exact h.center_sq g hg

theorem BenderCore.mem_borel_of_conj [Finite K] (h : BenderCore q i e P t) {z g : K}
    (hzM : z ∈ borel P) (hz2 : orderOf z = 2) (hzg : g⁻¹ * z * g ∈ borel P) : g ∈ borel P := by
  by_contra hg
  have hodd := h.strong.2.2 g hg
  have hmem : g⁻¹ * z * g ∈ borel P ⊓ conjugate (borel P) g := by
    refine Subgroup.mem_inf.mpr ⟨hzg, ?_⟩
    rw [mem_conjugate_iff_mul_inv]
    have : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
    rw [this]
    exact hzM
  have hord : orderOf (g⁻¹ * z * g) = 2 := by
    have := (MulAut.conj g⁻¹).orderOf_eq z
    simpa [MulAut.conj_apply] using this.trans hz2
  have hdvd := Subgroup.orderOf_dvd_natCard (borel P ⊓ conjugate (borel P) g) hmem
  rw [hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem BenderCore.exists_conj_t [Finite K] (h : BenderCore q i e P t) {z : K}
    (hz : z ∈ rootCenter P) (hz1 : z ≠ 1) : ∃ g : K, z = g⁻¹ * t * g := by
  have hti : t⁻¹ = t := inv_eq_of_mul_self h.sq_eq_one
  have hz2 : z * z = 1 := h.center_sq z hz
  have hzP : z ∈ borel P := le_borel P (rootCenter_le P hz)
  have hkk : t * (t * z * t) * t = z := by
    calc t * (t * z * t) * t = (t * t) * z * (t * t) := by group
      _ = z := by rw [h.sq_eq_one]; group
  have hw2 : t * z * t * (t * z * t) = 1 := by
    calc t * z * t * (t * z * t) = t * z * (t * t) * z * t := by group
      _ = t * (z * z) * t := by rw [h.sq_eq_one]; group
      _ = 1 := by rw [hz2, mul_one, h.sq_eq_one]
  have hw1 : t * z * t ≠ 1 := by
    intro h1
    apply hz1
    rw [← hkk, h1, mul_one, h.sq_eq_one]
  have hnot : t * z * t ∉ borel P := by
    intro hw
    have hD : t * z * t ∈ cartan P t := by
      refine Subgroup.mem_inf.mpr ⟨hw, ?_⟩
      rw [mem_conjugate_iff_mul_inv, hti, hkk]
      exact hzP
    have hord : orderOf (t * z * t) = 2 := by
      apply orderOf_eq_prime _ hw1
      rw [sq]
      exact hw2
    have hdvd := Subgroup.orderOf_dvd_natCard (cartan P t) hD
    rw [hord] at hdvd
    exact (Nat.not_even_iff_odd.mpr h.odd_card_cartan) (even_iff_two_dvd.mpr hdvd)
  obtain ⟨m, hm, hmw⟩ := h.exists_conj_eq hw2 hnot
  refine ⟨m * t, ?_⟩
  calc z = t * (t * z * t) * t := hkk.symm
    _ = t * (m⁻¹ * t * m) * t := by rw [hmw]
    _ = (m * t)⁻¹ * t * (m * t) := by rw [mul_inv_rev, hti]; group

theorem BenderCore.exists_cartan_conj [Finite K] (h : BenderCore q i e P t) {z z' : K}
    (hz : z ∈ rootCenter P) (hz1 : z ≠ 1) (hz' : z' ∈ rootCenter P) (hz1' : z' ≠ 1) :
    ∃ d ∈ cartan P t, z' = d⁻¹ * z * d := by
  obtain ⟨g, hg⟩ := h.exists_conj_t hz hz1
  obtain ⟨g', hg'⟩ := h.exists_conj_t hz' hz1'
  have hzc : z' = (g⁻¹ * g')⁻¹ * z * (g⁻¹ * g') := by
    rw [hg', hg]; group
  have hz2 : orderOf z = 2 := ((h.involution_iff).mpr ⟨hz, hz1⟩).2
  have hcM : g⁻¹ * g' ∈ borel P := by
    refine h.mem_borel_of_conj (le_borel P (rootCenter_le P hz)) hz2 ?_
    rw [← hzc]
    exact le_borel P (rootCenter_le P hz')
  have hcsup : g⁻¹ * g' ∈ P ⊔ cartan P t := by rw [h.sup_eq]; exact hcM
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left P (cartan P t)
    (cartan_le_borel P t)
  have hcsup' : g⁻¹ * g' ∈ (P : Set K) * (cartan P t : Set K) := by
    rw [← hmul]; exact hcsup
  obtain ⟨p, hp, d, hd, hpd⟩ := Set.mem_mul.mp hcsup'
  refine ⟨d, hd, ?_⟩
  have hzc' := (mem_rootCenter_iff.mp hz).2 p⁻¹ (P.inv_mem hp)
  rw [hzc, ← hpd]
  calc (p * d)⁻¹ * z * (p * d) = d⁻¹ * (p⁻¹ * z) * (p * d) := by group
    _ = d⁻¹ * (z * p⁻¹) * (p * d) := by rw [hzc']
    _ = d⁻¹ * z * d := by group

end RootCenter

section Regular

theorem BenderCore.ncard_rootCenter_ne_one [Finite K] (h : BenderCore q i e P t) :
    {z : K | z ∈ rootCenter P ∧ z ≠ 1}.ncard = q - 1 := by
  have hset : {z : K | z ∈ rootCenter P ∧ z ≠ 1} = (rootCenter P : Set K) \ {1} := by
    ext z
    simp
  rw [hset, Set.ncard_sdiff_singleton_of_mem (by exact (rootCenter P).one_mem),
    ← Nat.card_coe_set_eq]
  have : Nat.card ((rootCenter P : Set K)) = q := h.card_center
  rw [this]

theorem BenderCore.card_cartan_inf_centralizer [Finite K] (h : BenderCore q i e P t) {z : K}
    (hz : z ∈ rootCenter P) (hz1 : z ≠ 1) :
    Nat.card ↥(cartan P t ⊓ centralizer ({z} : Set K)) = e := by
  classical
  let D := cartan P t
  let _ : MulAction D K :=
    MulAction.compHom K ((ConjAct.toConjAct : K ≃* ConjAct K).toMonoidHom.comp D.subtype)
  have hsmul : ∀ (d : D) (x : K), d • x = d * x * (d : K)⁻¹ := fun d x => by
    change ConjAct.toConjAct (d : K) • x = _
    rw [ConjAct.smul_def]
    simp
  have horbit : MulAction.orbit D z = {z' : K | z' ∈ rootCenter P ∧ z' ≠ 1} := by
    ext z'
    constructor
    · rintro ⟨d, rfl⟩
      change d • z ∈ _
      rw [hsmul]
      refine ⟨conj_mem_rootCenter (cartan_le_borel P t d.2) hz, ?_⟩
      intro h1
      apply hz1
      have : (d : K)⁻¹ * ((d : K) * z * (d : K)⁻¹) * d = z := by group
      rw [h1] at this
      simpa using this.symm
    · rintro ⟨hz', hz1'⟩
      obtain ⟨d, hd, hzd⟩ := h.exists_cartan_conj hz hz1 hz' hz1'
      refine ⟨⟨d⁻¹, D.inv_mem hd⟩, ?_⟩
      change (⟨d⁻¹, D.inv_mem hd⟩ : D) • z = z'
      rw [hsmul]
      simp [hzd]
  have hstab : (MulAction.stabilizer D z).map D.subtype =
      cartan P t ⊓ centralizer ({z} : Set K) := by
    ext x
    constructor
    · rintro ⟨d, hd, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨d.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have h1 := MulAction.mem_stabilizer_iff.mp hd
      rw [hsmul] at h1
      change z * (d : K) = (d : K) * z
      calc z * (d : K) = ((d : K) * z * (d : K)⁻¹) * d := by rw [h1]
        _ = (d : K) * z := by group
    · intro hx
      obtain ⟨hxD, hxc⟩ := Subgroup.mem_inf.mp hx
      refine ⟨⟨x, hxD⟩, MulAction.mem_stabilizer_iff.mpr ?_, rfl⟩
      rw [hsmul]
      have h1 := Subgroup.mem_centralizer_iff.mp hxc z (Set.mem_singleton z)
      change z * x = x * z at h1
      calc x * z * x⁻¹ = (z * x) * x⁻¹ := by rw [← h1]
        _ = z := by group
  have hidx := MulAction.index_stabilizer (G := D) (x := z)
  have hcm := Subgroup.card_mul_index (MulAction.stabilizer D z)
  have hcard : Nat.card (cartan P t ⊓ centralizer ({z} : Set K) : Subgroup K) =
      Nat.card (MulAction.stabilizer D z) := by
    rw [← hstab, Subgroup.card_map_of_injective D.subtype_injective]
  rw [hidx, horbit, h.ncard_rootCenter_ne_one] at hcm
  have hDcard : Nat.card D = (q - 1) * e := h.card_cartan
  rw [hDcard] at hcm
  have hpos : 0 < q - 1 := by
    rw [← h.card_commutator_cartan]
    exact Nat.card_pos
  rw [hcard]
  have : (q - 1) * Nat.card (MulAction.stabilizer D z) = (q - 1) * e := by
    rw [mul_comm, hcm]
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem BenderCore.cartan_inf_centralizer_eq [Finite K] (h : BenderCore q i e P t) {z : K}
    (hz : z ∈ rootCenter P) (hz1 : z ≠ 1) :
    cartan P t ⊓ centralizer ({z} : Set K) = fixCartan P t :=
  eq_of_card_eq_of_cyclic h.isCyclic inf_le_left (fixCartan_le_cartan P t)
    (by rw [h.card_cartan_inf_centralizer hz hz1, h.card_fixCartan])

end Regular

section Final

theorem BenderCore.comm_commutator_fixCartan [Finite K] (h : BenderCore q i e P t) :
    ∀ a ∈ ⁅cartan P t, Subgroup.zpowers t⁆, ∀ b ∈ fixCartan P t, a * b = b * a :=
  fun _ ha _ hb => h.cartan_comm (h.commutator_cartan_le ha) (fixCartan_le_cartan P t hb)

theorem BenderCore.existsUnique_commutator_conj [Finite K] (h : BenderCore q i e P t) {z z' : K}
    (hz : z ∈ rootCenter P) (hz1 : z ≠ 1) (hz' : z' ∈ rootCenter P) (hz1' : z' ≠ 1) :
    ∃! d, d ∈ ⁅cartan P t, Subgroup.zpowers t⁆ ∧ z' = d⁻¹ * z * d := by
  obtain ⟨d, hd, hzd⟩ := h.exists_cartan_conj hz hz1 hz' hz1'
  have hsup : d ∈ ⁅cartan P t, Subgroup.zpowers t⁆ ⊔ fixCartan P t := h.cartan_eq_sup ▸ hd
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute h.comm_commutator_fixCartan hsup
  refine ⟨a, ⟨ha, ?_⟩, fun a2 ha2 => ?_⟩
  · have haD := h.commutator_cartan_le ha
    have haB : a⁻¹ ∈ borel P := cartan_le_borel P t ((cartan P t).inv_mem haD)
    have hz'' : a⁻¹ * z * a ∈ rootCenter P := by
      simpa using conj_mem_rootCenter haB hz
    have hz1'' : a⁻¹ * z * a ≠ 1 := by
      intro h1
      apply hz1
      have : a * (a⁻¹ * z * a) * a⁻¹ = z := by group
      rw [h1] at this
      simpa using this.symm
    have hb' : b ∈ cartan P t ⊓ centralizer ({a⁻¹ * z * a} : Set K) := by
      rw [h.cartan_inf_centralizer_eq hz'' hz1'']
      exact hb
    have hbc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb').2 (a⁻¹ * z * a)
      (Set.mem_singleton _)
    rw [hzd]
    calc (a * b)⁻¹ * z * (a * b) = b⁻¹ * (a⁻¹ * z * a) * b := by group
      _ = b⁻¹ * (b * (a⁻¹ * z * a)) := by rw [← hbc]; group
      _ = a⁻¹ * z * a := by group
  · obtain ⟨ha2, hza2⟩ := ha2
    have haD := h.commutator_cartan_le ha
    have hcinv : a * a2⁻¹ ∈ ⁅cartan P t, Subgroup.zpowers t⁆ :=
      Subgroup.mul_mem _ ha (Subgroup.inv_mem _ ha2)
    have hz'' : a⁻¹ * z * a ∈ rootCenter P := by
      have haB : a⁻¹ ∈ borel P := cartan_le_borel P t ((cartan P t).inv_mem haD)
      simpa using conj_mem_rootCenter haB hz
    have hb_fix : b ∈ fixCartan P t := hb
    have hz1'' : a⁻¹ * z * a ≠ 1 := by
      intro h1
      apply hz1
      have : a * (a⁻¹ * z * a) * a⁻¹ = z := by group
      rw [h1] at this
      simpa using this.symm
    have hb' : b ∈ cartan P t ⊓ centralizer ({a⁻¹ * z * a} : Set K) := by
      rw [h.cartan_inf_centralizer_eq hz'' hz1'']
      exact hb
    have hbc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb').2 (a⁻¹ * z * a)
      (Set.mem_singleton _)
    have hz'eq : z' = a⁻¹ * z * a := by
      rw [hzd]
      calc (a * b)⁻¹ * z * (a * b) = b⁻¹ * (a⁻¹ * z * a) * b := by group
        _ = b⁻¹ * (b * (a⁻¹ * z * a)) := by rw [← hbc]; group
        _ = a⁻¹ * z * a := by group
    have hcz : a * a2⁻¹ ∈ centralizer ({z} : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have h1 : a⁻¹ * z * a = a2⁻¹ * z * a2 := hz'eq.symm.trans hza2
      calc z * (a * a2⁻¹) = a * (a⁻¹ * z * a) * a2⁻¹ := by group
        _ = a * (a2⁻¹ * z * a2) * a2⁻¹ := by rw [h1]
        _ = a * a2⁻¹ * z := by group
    have hcD : a * a2⁻¹ ∈ cartan P t := h.commutator_cartan_le hcinv
    have hcfix : a * a2⁻¹ ∈ fixCartan P t := by
      rw [← h.cartan_inf_centralizer_eq hz hz1]
      exact Subgroup.mem_inf.mpr ⟨hcD, hcz⟩
    have : a * a2⁻¹ ∈ ⁅cartan P t, Subgroup.zpowers t⁆ ⊓ fixCartan P t :=
      Subgroup.mem_inf.mpr ⟨hcinv, hcfix⟩
    rw [h.inf_commutator_fixCartan, Subgroup.mem_bot] at this
    exact (mul_inv_eq_one.mp this).symm

end Final

section Centralizer

theorem BenderCore.centralizer_eq [Finite K] (h : BenderCore q i e P t) {z : K}
    (hz : z ∈ rootCenter P) (hz1 : z ≠ 1) :
    centralizer ({z} : Set K) = P ⊔ fixCartan P t := by
  have hz2 : orderOf z = 2 := ((h.involution_iff).mpr ⟨hz, hz1⟩).2
  have hzP : z ∈ borel P := le_borel P (rootCenter_le P hz)
  apply le_antisymm
  · intro x hx
    have hxc : z * x = x * z := Subgroup.mem_centralizer_iff.mp hx z (Set.mem_singleton z)
    have hxM : x ∈ borel P := by
      refine h.mem_borel_of_conj hzP hz2 ?_
      have : x⁻¹ * z * x = z := by
        calc x⁻¹ * z * x = x⁻¹ * (z * x) := by group
          _ = x⁻¹ * (x * z) := by rw [hxc]
          _ = z := by group
      rw [this]
      exact hzP
    have hxsup : x ∈ P ⊔ cartan P t := by rw [h.sup_eq]; exact hxM
    have hmul := Subgroup.coe_mul_of_right_le_normalizer_left P (cartan P t)
      (cartan_le_borel P t)
    have hx' : x ∈ (P : Set K) * (cartan P t : Set K) := by rw [← hmul]; exact hxsup
    obtain ⟨p, hp, d, hd, rfl⟩ := Set.mem_mul.mp hx'
    have hpz := (mem_rootCenter_iff.mp hz).2 p hp
    have hdz : z * d = d * z := by
      have h1 : p * (z * d) = p * (d * z) := by
        calc p * (z * d) = (p * z) * d := by group
          _ = (z * p) * d := by rw [hpz]
          _ = z * (p * d) := by group
          _ = (p * d) * z := hxc
          _ = p * (d * z) := by group
      exact mul_left_cancel h1
    have hdfix : d ∈ fixCartan P t := by
      rw [← h.cartan_inf_centralizer_eq hz hz1]
      refine Subgroup.mem_inf.mpr ⟨hd, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hdz
    exact Subgroup.mul_mem_sup hp hdfix
  · apply sup_le
    · intro p hp
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact ((mem_rootCenter_iff.mp hz).2 p hp).symm
    · intro d hd
      rw [← h.cartan_inf_centralizer_eq hz hz1] at hd
      exact (Subgroup.mem_inf.mp hd).2

theorem BenderCore.card_centralizer [Finite K] (h : BenderCore q i e P t) {z : K}
    (hz : z ∈ rootCenter P) (hz1 : z ≠ 1) :
    Nat.card ↥(centralizer ({z} : Set K)) = q ^ i * e := by
  rw [h.centralizer_eq hz hz1]
  have hd : P ⊓ fixCartan P t = ⊥ := by
    rw [eq_bot_iff, ← h.inf_eq]
    exact inf_le_inf_left _ (fixCartan_le_cartan P t)
  rw [card_sup_eq_mul_of_le_normalizer ((fixCartan_le_cartan P t).trans (cartan_le_borel P t)) hd,
    h.card_eq, h.card_fixCartan]

end Centralizer

section SylowTransport

theorem BenderCore.exists_of_sylow [Finite K] {S : Sylow 2 K} (h : BenderCore q i e (S : Subgroup K) t)
    (Q : Sylow 2 K) : ∃ t', BenderCore q i e (Q : Subgroup K) t' := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq K S Q
  refine ⟨MulAut.conj g t, ?_⟩
  have hU : (S : Subgroup K).map (MulAut.conj g).toMonoidHom = ((g • S : Sylow 2 K) : Subgroup K) := by
    ext x
    rw [Subgroup.mem_map_equiv, Sylow.coe_subgroup_smul,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  rw [← hU]
  exact h.map (MulAut.conj g)

end SylowTransport

section Consequences

theorem BenderCore.cartan_eq_commutator [Finite K] (h : BenderCore q i e P t) (he : e = 1) :
    cartan P t = ⁅cartan P t, Subgroup.zpowers t⁆ := by
  have hfix : fixCartan P t = ⊥ := by
    rw [← Subgroup.card_eq_one, h.card_fixCartan, he]
  calc cartan P t = ⁅cartan P t, Subgroup.zpowers t⁆ ⊔ fixCartan P t := h.cartan_eq_sup
    _ = ⁅cartan P t, Subgroup.zpowers t⁆ := by rw [hfix, sup_bot_eq]

theorem BenderCore.elemAbelian_le_rootCenter (h : BenderCore q i e P t) {A : Subgroup K}
    (hAP : A ≤ P) (hA : ∀ x ∈ A, x * x = 1) : A ≤ rootCenter P := by
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1]; exact (rootCenter P).one_mem
  · apply h.center_of_involution x (le_borel P (hAP hx))
    apply orderOf_eq_prime _ hx1
    rw [sq]
    exact hA x hx

end Consequences

section Generation

theorem conjugate_conjugate (A : Subgroup K) (g h : K) :
    conjugate (conjugate A g) h = conjugate A (g * h) := by
  ext x
  rw [mem_conjugate_iff_mul_inv, mem_conjugate_iff_mul_inv, mem_conjugate_iff_mul_inv]
  simp [mul_assoc]

theorem conjugate_borel (P : Subgroup K) (g : K) :
    conjugate (borel P) g = borel (conjugate P g) :=
  Subgroup.map_equiv_normalizer_eq P (MulAut.conj g⁻¹)

theorem conjugate_eq_of_mem_borel {m : K} {P : Subgroup K} (hm : m ∈ borel P) :
    conjugate P m = P := map_conj_eq_of_mem_borel hm

theorem BenderCore.ne_bot [Finite K] (h : BenderCore q i e P t) : P ≠ ⊥ := by
  intro hP
  apply h.not_mem
  have : (⊥ : Subgroup K).Normal := inferInstance
  have h1 := Subgroup.normalizer_eq_top_iff.mpr this
  rw [hP]
  unfold borel
  rw [h1]
  exact Subgroup.mem_top t

theorem BenderCore.normal_sup_conjugate [Finite K] (h : BenderCore q i e P t) :
    (P ⊔ conjugate P t).Normal := by
  have hti : t⁻¹ = t := inv_eq_of_mul_self h.sq_eq_one
  set H0 := P ⊔ conjugate P t with hH0
  have hD : cartan P t ≤ normalizer (H0 : Set K) := by
    have : cartan P t ≤ normalizer (P : Set K) ⊓ normalizer ((conjugate P t : Subgroup K) : Set K) := by
      refine le_inf (cartan_le_borel P t) ?_
      intro d hd
      have hd' := (Subgroup.mem_inf.mp hd).2
      rw [conjugate_borel] at hd'
      exact hd'
    exact this.trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hP' : P ≤ normalizer (H0 : Set K) := le_sup_left.trans Subgroup.le_normalizer
  have hkey : ∀ x ∈ H0, t * x * t⁻¹ ∈ H0 := by
    have hle : H0 ≤ H0.comap (MulAut.conj t).toMonoidHom := by
      apply sup_le
      · intro p hp
        change t * p * t⁻¹ ∈ H0
        refine le_sup_right (a := P) ?_
        rw [mem_conjugate_iff_mul_inv]
        have : t * (t * p * t⁻¹) * t⁻¹ = p := by
          rw [hti]
          calc t * (t * p * t) * t = (t * t) * p * (t * t) := by group
            _ = p := by rw [h.sq_eq_one]; group
        rw [this]
        exact hp
      · intro x hx
        change t * x * t⁻¹ ∈ H0
        refine le_sup_left (b := conjugate P t) ?_
        exact mem_conjugate_iff_mul_inv.mp hx
    exact fun x hx => hle hx
  have ht : t ∈ normalizer (H0 : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hkey x
    · intro hx
      have := hkey _ hx
      have e : t * (t * x * t⁻¹) * t⁻¹ = x := by
        rw [hti]
        calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
          _ = x := by rw [h.sq_eq_one]; group
      rwa [e] at this
  have hM : borel P ≤ normalizer (H0 : Set K) := by
    rw [← h.sup_eq]
    exact sup_le hP' hD
  have htop : normalizer (H0 : Set K) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    by_cases hg : g ∈ borel P
    · exact hM hg
    · obtain ⟨p, hp, m, hm, rfl⟩ := h.bruhat hg
      exact mul_mem (mul_mem (hP' hp) ht) (hM hm)
  exact Subgroup.normalizer_eq_top_iff.mp htop

theorem BenderCore.sup_conjugate_eq_top [Finite K] [IsSimpleGroup K] (h : BenderCore q i e P t) :
    P ⊔ conjugate P t = ⊤ := by
  have hnormal := h.normal_sup_conjugate
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P ⊔ conjugate P t) with hbot | htop
  · exact absurd (le_bot_iff.mp (hbot ▸ le_sup_left)) h.ne_bot
  · exact htop

theorem BenderCore.sup_zpowers_eq_top [Finite K] [IsSimpleGroup K] (h : BenderCore q i e P t)
    {x : K} (hx : x ∉ borel P) : P ⊔ Subgroup.zpowers x = ⊤ := by
  obtain ⟨p, hp, m, hm, hxeq⟩ := h.bruhat hx
  have hPp : conjugate P p = P := conjugate_eq_of_mem_borel (le_borel P hp)
  have hPm : conjugate P m = P := conjugate_eq_of_mem_borel hm
  have h1 : conjugate P x = conjugate (conjugate P t) m := by
    rw [hxeq, ← conjugate_conjugate, ← conjugate_conjugate, hPp]
  have h2 : P ⊔ conjugate P x = ⊤ := by
    rw [h1]
    calc P ⊔ conjugate (conjugate P t) m
        = conjugate P m ⊔ conjugate (conjugate P t) m := by rw [hPm]
      _ = conjugate (P ⊔ conjugate P t) m := by unfold conjugate; rw [Subgroup.map_sup]
      _ = ⊤ := by
        rw [h.sup_conjugate_eq_top]
        unfold conjugate
        exact Subgroup.map_top_of_surjective _ (MulAut.conj m⁻¹).surjective
  rw [eq_top_iff, ← h2]
  apply sup_le le_sup_left
  intro y hy
  rw [mem_conjugate_iff_mul_inv] at hy
  have hxz : x ∈ P ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have : y = x⁻¹ * (x * y * x⁻¹) * x := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ((P ⊔ Subgroup.zpowers x).inv_mem hxz)
    (Subgroup.mem_sup_left hy)) hxz

theorem BenderCore.le_borel_of_le [Finite K] [IsSimpleGroup K] (h : BenderCore q i e P t)
    {Y : Subgroup K} (hPY : P ≤ Y) (hY : Y ≠ ⊤) : Y ≤ borel P := by
  intro y hy
  by_contra hyM
  apply hY
  rw [eq_top_iff, ← h.sup_zpowers_eq_top hyM]
  exact sup_le hPY ((Subgroup.zpowers_le).mpr hy)

end Generation

section Orders

theorem BenderCore.card_borel [Finite K] (h : BenderCore q i e P t) :
    Nat.card (borel P) = q ^ i * ((q - 1) * e) := by
  rw [← h.sup_eq, card_sup_eq_mul_of_le_normalizer (cartan_le_borel P t) h.inf_eq, h.card_eq,
    h.card_cartan]

theorem BenderCore.card_group [Finite K] (h : BenderCore q i e P t) :
    Nat.card K = (q ^ i + 1) * (q ^ i * ((q - 1) * e)) := by
  have := Subgroup.card_mul_index (borel P)
  rw [h.card_borel, h.index_eq] at this
  rw [← this, mul_comm]

end Orders

section Lemma32Extras

theorem isCyclic_of_le_isCyclic {D A : Subgroup K} (hD : IsCyclic D) (hA : A ≤ D) :
    IsCyclic A := by
  have : IsCyclic (A.subgroupOf D) := inferInstance
  exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hA)).mp this

theorem BenderCore.isCyclic_commutator [Finite K] (h : BenderCore q i e P t) :
    IsCyclic ↥⁅cartan P t, Subgroup.zpowers t⁆ :=
  isCyclic_of_le_isCyclic h.isCyclic h.commutator_cartan_le

theorem BenderCore.isCyclic_fixCartan [Finite K] (h : BenderCore q i e P t) :
    IsCyclic (fixCartan P t) :=
  isCyclic_of_le_isCyclic h.isCyclic (fixCartan_le_cartan P t)

theorem BenderCore.closure_involutions [Finite K] (h : BenderCore q i e P t) :
    Subgroup.closure {g : K | g ∈ borel P ∧ orderOf g = 2} = rootCenter P := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    exact h.center_of_involution g hg.1 hg.2
  · intro g hg
    by_cases hg1 : g = 1
    · rw [hg1]; exact (Subgroup.closure _).one_mem
    · exact Subgroup.subset_closure ((h.involution_iff).mpr ⟨hg, hg1⟩)

theorem BenderCore.exists_involution [Finite K] (h : BenderCore q i e P t) :
    ∃ z : K, z ∈ rootCenter P ∧ z ≠ 1 := by
  have hdvd : 2 ∣ Nat.card (borel P) := even_iff_two_dvd.mp h.strong.2.1
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hg' : orderOf (g : K) = 2 := by rw [Subgroup.orderOf_coe]; exact hg
  exact h.involution_iff.mp ⟨g.2, hg'⟩ |> fun hh => ⟨g, hh⟩

theorem BenderCore.rootCenter_le_sup [Finite K] (h : BenderCore q i e P t) {z : K}
    (hz : z ∈ rootCenter P) (hz1 : z ≠ 1) :
    rootCenter P ≤ Subgroup.closure ({z, t} : Set K) ⊔ ⁅cartan P t, Subgroup.zpowers t⁆ := by
  intro z' hz'
  by_cases hz1' : z' = 1
  · rw [hz1']; exact Subgroup.one_mem _
  · obtain ⟨d, ⟨hd, hzd⟩, -⟩ := h.existsUnique_commutator_conj hz hz1 hz' hz1'
    have hzL : z ∈ Subgroup.closure ({z, t} : Set K) ⊔ ⁅cartan P t, Subgroup.zpowers t⁆ :=
      Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    have hdL : d ∈ Subgroup.closure ({z, t} : Set K) ⊔ ⁅cartan P t, Subgroup.zpowers t⁆ :=
      Subgroup.mem_sup_right hd
    rw [hzd]
    exact mul_mem (mul_mem (inv_mem hdL) hzL) hdL

theorem BenderCore.lemma32h_top_of_card_eq [Finite K] [IsSimpleGroup K] (h : BenderCore q i e P t)
    (hi : i = 1) {z : K} (hz : z ∈ rootCenter P) (hz1 : z ≠ 1) :
    Subgroup.closure ({z, t} : Set K) ⊔ ⁅cartan P t, Subgroup.zpowers t⁆ = ⊤ := by
  set L := Subgroup.closure ({z, t} : Set K) ⊔ ⁅cartan P t, Subgroup.zpowers t⁆ with hL
  have hPZ : rootCenter P = P := by
    apply Subgroup.eq_of_le_of_card_ge (rootCenter_le P)
    have h1 := h.card_center
    have h2 := h.card_eq
    rw [h1, h2, hi, pow_one]
  have hPL : P ≤ L := by
    have := h.rootCenter_le_sup hz hz1
    rwa [hPZ] at this
  have htL : t ∈ L := Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  by_contra hne
  exact h.not_mem (h.le_borel_of_le hPL hne htL)

theorem BenderCore.exists_conj_rootCenter [Finite K] (h : BenderCore q i e P t) {u : K}
    (hu : u * u = 1) (hu1 : u ≠ 1) :
    ∃ g : K, g⁻¹ * u * g ∈ rootCenter P ∧ g⁻¹ * u * g ≠ 1 := by
  have hord : orderOf u = 2 := by
    apply orderOf_eq_prime _ hu1
    rw [sq]; exact hu
  by_cases huM : u ∈ borel P
  · have := h.involution_iff.mp ⟨huM, hord⟩
    exact ⟨1, by simpa using this.1, by simpa using this.2⟩
  · obtain ⟨m, hm, hmu⟩ := h.exists_conj_eq hu huM
    obtain ⟨z, hz, hz1⟩ := h.exists_involution
    obtain ⟨g, hg⟩ := h.exists_conj_t hz hz1
    refine ⟨m⁻¹ * g, ?_, ?_⟩
    · have : (m⁻¹ * g)⁻¹ * u * (m⁻¹ * g) = z := by
        rw [hg, hmu]; group
      rw [this]; exact hz
    · have : (m⁻¹ * g)⁻¹ * u * (m⁻¹ * g) = z := by
        rw [hg, hmu]; group
      rw [this]; exact hz1

end Lemma32Extras

section Lemma32h

theorem BenderCore.lemma32h_ne_top [Finite K] [IsSimpleGroup K] (h : BenderCore q i e P t)
    (he : 1 < e) (hnc : ¬ ∀ x y : K, x * y = y * x) {z : K} (hz : z ∈ rootCenter P)
    (hz1 : z ≠ 1) :
    Subgroup.closure ({z, t} : Set K) ⊔ ⁅cartan P t, Subgroup.zpowers t⁆ ≠ ⊤ := by
  intro htop
  have hfix : fixCartan P t ≠ ⊥ := by
    intro hbot
    have := h.card_fixCartan
    rw [hbot, Subgroup.card_bot] at this
    omega
  obtain ⟨c, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hfix
  have hcfix : (c : K) ∈ fixCartan P t := c.2
  have hcz : z * c = c * z := by
    have hmem : (c : K) ∈ cartan P t ⊓ Subgroup.centralizer ({z} : Set K) := by
      rw [h.cartan_inf_centralizer_eq hz hz1]
      exact hcfix
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hmem).2 z (Set.mem_singleton z)
  have hct : t * c = c * t :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcfix).2 t (Set.mem_singleton t)
  have hcD : (c : K) ∈ cartan P t := fixCartan_le_cartan P t hcfix
  have hle : Subgroup.closure ({z, t} : Set K) ⊔ ⁅cartan P t, Subgroup.zpowers t⁆ ≤
      Subgroup.centralizer ({(c : K)} : Set K) := by
    apply sup_le
    · rw [Subgroup.closure_le]
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      rcases hx with rfl | rfl
      · exact hcz.symm
      · exact hct.symm
    · intro d hd
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact h.cartan_comm hcD (h.commutator_cartan_le hd)
  rw [htop, top_le_iff, Subgroup.centralizer_eq_top_iff_subset] at hle
  have hcc : (c : K) ∈ Subgroup.center K := hle (Set.mem_singleton _)
  have hcenter : Subgroup.center K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with hb | ht'
    · exact hb
    · exfalso
      apply hnc
      intro x y
      have : x ∈ Subgroup.center K := by rw [ht']; exact Subgroup.mem_top x
      exact (Subgroup.mem_center_iff.mp this y).symm
  rw [hcenter, Subgroup.mem_bot] at hcc
  exact hc1 (Subtype.ext hcc)

end Lemma32h

section Solvable

theorem BenderCore.isSolvable_borel [Finite K] {Q : Sylow 2 K}
    (h : BenderCore q i e (Q : Subgroup K) t) : Group.IsSolvable ↥(borel (Q : Subgroup K)) := by
  set P : Subgroup K := (Q : Subgroup K) with hP
  have hPM : P ≤ borel P := le_borel P
  have hnormal : (P.subgroupOf (borel P)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPM).mpr le_rfl
  have hsolP : Group.IsSolvable ↥(P.subgroupOf (borel P)) := by
    have : Group.IsNilpotent ↥P := IsPGroup.isNilpotent Q.isPGroup'
    have : Group.IsSolvable ↥P := inferInstance
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hPM).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPM).injective
  have hcyc : IsCyclic (↥(borel P) ⧸ P.subgroupOf (borel P)) := by
    have := h.isCyclic
    refine isCyclic_of_surjective
      ((QuotientGroup.mk' (P.subgroupOf (borel P))).comp
        (Subgroup.inclusion (cartan_le_borel P t))) ?_
    intro y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
    have hm : (m : K) ∈ P ⊔ cartan P t := by rw [h.sup_eq]; exact m.2
    have hmul := Subgroup.coe_mul_of_right_le_normalizer_left P (cartan P t)
      (cartan_le_borel P t)
    have hm' : (m : K) ∈ (P : Set K) * (cartan P t : Set K) := by rw [← hmul]; exact hm
    obtain ⟨p, hp, d, hd, hpd⟩ := Set.mem_mul.mp hm'
    refine ⟨⟨d, hd⟩, ?_⟩
    change QuotientGroup.mk (Subgroup.inclusion (cartan_le_borel P t) ⟨d, hd⟩) = QuotientGroup.mk m
    rw [QuotientGroup.eq]
    change (d : K)⁻¹ * (m : K) ∈ P
    have : (d : K)⁻¹ * (m : K) = d⁻¹ * p * d := by rw [← hpd]; group
    rw [this]
    have hdn := Subgroup.mem_normalizer_iff.mp (cartan_le_borel P t hd)
    have := (hdn (d⁻¹ * p * d)).mpr (by
      have e : d * (d⁻¹ * p * d) * d⁻¹ = p := by group
      rw [e]; exact hp)
    exact this
  have hsolq : Group.IsSolvable (↥(borel P) ⧸ P.subgroupOf (borel P)) := inferInstance
  exact Group.isSolvable_of_subgroup_quotient (P.subgroupOf (borel P))

theorem isSolvable_of_le_isSolvable {A B : Subgroup K} (hAB : A ≤ B) [Group.IsSolvable B] :
    Group.IsSolvable A :=
  Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hAB)
    (Subgroup.inclusion_injective hAB)

end Solvable

section Transitivity

theorem BenderCore.isMultiplyPretransitive [Finite K] (h : BenderCore q i e P t) :
    MulAction.IsMultiplyPretransitive K (K ⧸ borel P) 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective d
  have hz : x⁻¹ * y ∉ borel P := fun hm => hab (QuotientGroup.eq.mpr hm)
  have hz' : x'⁻¹ * y' ∉ borel P := fun hm => hcd (QuotientGroup.eq.mpr hm)
  obtain ⟨p, hp, m, hm, hzeq⟩ := h.bruhat hz
  obtain ⟨p', hp', m', hm', hzeq'⟩ := h.bruhat hz'
  refine ⟨x' * (p' * p⁻¹) * x⁻¹, ?_, ?_⟩
  · rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
    have : (x' * (p' * p⁻¹) * x⁻¹ * x)⁻¹ * x' = (p' * p⁻¹)⁻¹ := by group
    rw [this]
    exact (borel P).inv_mem ((borel P).mul_mem (le_borel P hp') ((borel P).inv_mem (le_borel P hp)))
  · rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
    have h1 : x⁻¹ * y = p * t * m := hzeq
    have h2 : x'⁻¹ * y' = p' * t * m' := hzeq'
    have : (x' * (p' * p⁻¹) * x⁻¹ * y)⁻¹ * y' = m⁻¹ * m' := by
      have e1 : x' * (p' * p⁻¹) * x⁻¹ * y = x' * (p' * p⁻¹) * (x⁻¹ * y) := by group
      have e2 : y' = x' * (x'⁻¹ * y') := by group
      rw [e1, h1, e2, h2]
      group
    rw [this]
    exact (borel P).mul_mem ((borel P).inv_mem hm) hm'

end Transitivity

section BruhatUnique

theorem BenderCore.eq_of_bruhat_eq [Finite K] (h : BenderCore q i e P t) {p p' m m' : K}
    (hp : p ∈ P) (hp' : p' ∈ P) (hm : m ∈ borel P) (hm' : m' ∈ borel P)
    (heq : p * t * m = p' * t * m') : p = p' := by
  have hti : t⁻¹ = t := inv_eq_of_mul_self h.sq_eq_one
  have h1 : (p * t)⁻¹ * (p' * t) ∈ borel P := by
    have : (p * t)⁻¹ * (p' * t) = m * m'⁻¹ := by
      have e1 : p' * t = p * t * m * m'⁻¹ := by
        calc p' * t = p' * t * m' * m'⁻¹ := by group
          _ = p * t * m * m'⁻¹ := by rw [← heq]
      rw [e1]; group
    rw [this]
    exact (borel P).mul_mem hm ((borel P).inv_mem hm')
  have hx : p⁻¹ * p' ∈ cartan P t := by
    refine Subgroup.mem_inf.mpr ⟨le_borel P (P.mul_mem (P.inv_mem hp) hp'), ?_⟩
    rw [mem_conjugate_iff_mul_inv, hti]
    have : t * (p⁻¹ * p') * t = (p * t)⁻¹ * (p' * t) := by
      simp [mul_assoc, hti]
    rw [this]
    exact h1
  have hx' : p⁻¹ * p' ∈ P ⊓ cartan P t := ⟨P.mul_mem (P.inv_mem hp) hp', hx⟩
  rw [h.inf_eq, Subgroup.mem_bot] at hx'
  exact inv_mul_eq_one.mp hx'

end BruhatUnique

section Extras

theorem BenderCore.isConj_of_involutions [Finite K] (h : BenderCore q i e P t) {u v : K}
    (hu : u * u = 1) (hu1 : u ≠ 1) (hv : v * v = 1) (hv1 : v ≠ 1) : IsConj u v := by
  obtain ⟨g, hg, hg1⟩ := h.exists_conj_rootCenter hu hu1
  obtain ⟨g', hg', hg1'⟩ := h.exists_conj_rootCenter hv hv1
  obtain ⟨d, hd, hdd⟩ := h.exists_cartan_conj hg hg1 hg' hg1'
  refine isConj_iff.mpr ⟨g' * d⁻¹ * g⁻¹, ?_⟩
  have h1 : g'⁻¹ * v * g' = d⁻¹ * (g⁻¹ * u * g) * d := hdd
  calc g' * d⁻¹ * g⁻¹ * u * (g' * d⁻¹ * g⁻¹)⁻¹
      = g' * (d⁻¹ * (g⁻¹ * u * g) * d) * g'⁻¹ := by group
    _ = g' * (g'⁻¹ * v * g') * g'⁻¹ := by rw [h1]
    _ = v := by group

theorem BenderCore.centralizer_rootCenter_eq [Finite K] (h : BenderCore q i e P t) :
    centralizer (rootCenter P : Set K) = P ⊔ fixCartan P t := by
  obtain ⟨z, hz, hz1⟩ := h.exists_involution
  apply le_antisymm
  · rw [← h.centralizer_eq hz hz1]
    exact Subgroup.centralizer_le (by simpa using hz)
  · apply sup_le
    · intro p hp
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact ((mem_rootCenter_iff.mp hy).2 p hp).symm
    · intro d hd
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      by_cases hy1 : y = 1
      · rw [hy1]; simp
      · have hd' : d ∈ cartan P t ⊓ centralizer ({y} : Set K) := by
          rw [h.cartan_inf_centralizer_eq hy hy1]; exact hd
        exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd').2 y
          (Set.mem_singleton y))

theorem BenderCore.mem_rootCenter_of_mul_self [Finite K] {q i e : ℕ} {P : Subgroup K} {t : K}
    (hc : BenderCore q i e P t) {y : K} (hyP : y ∈ P) (hy : y * y = 1) : y ∈ rootCenter P := by
  by_cases hy1 : y = 1
  · rw [hy1]; exact (rootCenter P).one_mem
  · apply hc.center_of_involution y (le_borel P hyP)
    apply orderOf_eq_prime _ hy1
    rw [sq]
    exact hy

theorem BenderCore.fixCartan_eq_bot [Finite K] {q i : ℕ} {P : Subgroup K} {t : K}
    (h : BenderCore q i 1 P t) : fixCartan P t = ⊥ :=
  Subgroup.card_eq_one.mp h.card_fixCartan

theorem BenderCore.centralizer_eq_of_e_one [Finite K] {q i : ℕ} {P : Subgroup K} {t : K}
    (h : BenderCore q i 1 P t) {z : K} (hz : z ∈ rootCenter P) (hz1 : z ≠ 1) :
    centralizer ({z} : Set K) = P := by
  rw [h.centralizer_eq hz hz1, h.fixCartan_eq_bot, sup_bot_eq]

end Extras

section StronglyEmbeddedLemmas

theorem IsStronglyEmbedded.mem_of_conj_mem [Finite K] {M : Subgroup K}
    (hM : IsStronglyEmbedded M) {V : Subgroup K} {g : K} (hVM : V ≤ M)
    (hVg : ∀ v ∈ V, g * v * g⁻¹ ∈ M) (hV2 : IsPGroup 2 V) (hV : V ≠ ⊥) : g ∈ M := by
  by_contra hgM
  have hodd := hM.2.2 g hgM
  have hle : V ≤ M ⊓ conjugate M g := by
    intro v hv
    exact Subgroup.mem_inf.mpr ⟨hVM hv, (mem_conjugate_iff_mul_inv).mpr (hVg v hv)⟩
  have hdvd : Nat.card V ∣ Nat.card ↥(M ⊓ conjugate M g) := Subgroup.card_dvd_of_le hle
  obtain ⟨k, hk⟩ := hV2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hV
    rw [pow_zero] at hk
    exact (Subgroup.card_eq_one).mp hk
  have h2 : 2 ∣ Nat.card ↥(M ⊓ conjugate M g) := by
    refine dvd_trans ?_ hdvd
    rw [hk]
    exact dvd_pow_self 2 hk0
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem mem_sylow_smul_iff (g : K) (S : Sylow 2 K) (x : K) :
    x ∈ ((g • S : Sylow 2 K) : Subgroup K) ↔ g⁻¹ * x * g ∈ (S : Subgroup K) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem BenderCore.sylow_eq_of_ne_bot [Finite K] {q i e : ℕ} {Q : Sylow 2 K} {t : K}
    (hc : BenderCore q i e (Q : Subgroup K) t) {Q₁ : Sylow 2 K} {V : Subgroup K} (hV : V ≠ ⊥)
    (hVQ : V ≤ (Q : Subgroup K)) (hVQ₁ : V ≤ (Q₁ : Subgroup K)) : Q₁ = Q := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq K Q Q₁
  have hV2 : IsPGroup 2 V := IsPGroup.to_le Q.isPGroup' hVQ
  have hg : g⁻¹ ∈ borel (Q : Subgroup K) := by
    refine IsStronglyEmbedded.mem_of_conj_mem hc.strong (V := V) (hVQ.trans (le_borel _))
      (fun v hv => ?_) hV2 hV
    have hv' := (mem_sylow_smul_iff g Q v).mp (hVQ₁ hv)
    simpa using le_borel _ hv'
  have hg' : g ∈ borel (Q : Subgroup K) := by simpa using (borel (Q : Subgroup K)).inv_mem hg
  exact Sylow.smul_eq_iff_mem_normalizer.mpr hg'

end StronglyEmbeddedLemmas

end CFSG.GH74.Uniqueness.Bender
