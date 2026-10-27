module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.T112MSylow
public import CFSG.HardMathSupport.Solomon.Coordinator.T112MOrder

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

namespace HatSevenFact

def permA : Equiv.Perm (Fin 7) := Equiv.swap 0 1 * Equiv.swap 1 2

def permB : Equiv.Perm (Fin 7) := Equiv.swap 3 4 * Equiv.swap 4 5

def permS : Equiv.Perm (Fin 7) := Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 2 5

theorem permA_sign : Equiv.Perm.sign permA = 1 := by decide

theorem permB_sign : Equiv.Perm.sign permB = 1 := by decide

theorem permS_sign : Equiv.Perm.sign permS = -1 := by decide

theorem perm_comm : permA * permB = permB * permA := by decide

theorem permS_inv_mul_B : permS⁻¹ * permB * permS = permA := by decide

theorem permS_inv_mul_A : permS⁻¹ * permA * permS = permB := by decide

def elA : alternatingGroup (Fin 7) :=
  ⟨permA, Equiv.Perm.mem_alternatingGroup.2 permA_sign⟩

def elB : alternatingGroup (Fin 7) :=
  ⟨permB, Equiv.Perm.mem_alternatingGroup.2 permB_sign⟩

theorem elA_comm_elB : elA * elB = elB * elA := Subtype.ext perm_comm

def mon (p : Fin 3 × Fin 3) : alternatingGroup (Fin 7) := elA ^ (p.1 : ℕ) * elB ^ (p.2 : ℕ)

theorem mon_mul : ∀ p q : Fin 3 × Fin 3, ∃ r : Fin 3 × Fin 3, mon r = mon p * mon q := by
  decide

theorem mon_inv : ∀ p : Fin 3 × Fin 3, ∃ r : Fin 3 × Fin 3, mon r = (mon p)⁻¹ := by decide

theorem mon_injective : Function.Injective mon := by
  have h : ∀ p q : Fin 3 × Fin 3, mon p = mon q → p = q := by decide
  exact fun p q hpq => h p q hpq

def sylowP : Subgroup (alternatingGroup (Fin 7)) where
  carrier := Set.range mon
  mul_mem' := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    exact mon_mul p q
  one_mem' := ⟨(0, 0), by decide⟩
  inv_mem' := by
    rintro _ ⟨p, rfl⟩
    exact mon_inv p

theorem card_sylowP : Nat.card sylowP = 9 := by
  have h : Nat.card sylowP = Nat.card (Fin 3 × Fin 3) := Nat.card_range_of_injective mon_injective
  simpa using h

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem index_sylowP : sylowP.index = 280 := by
  have h := sylowP.card_mul_index
  rw [card_sylowP, card_alt7] at h
  omega

section Comm

variable {Y : Type*} [Group Y]

theorem comm_central_mul_left {z : Y} (hz : z ∈ Subgroup.center Y) (u v : Y) :
    ⁅z * u, v⁆ = ⁅u, v⁆ := by
  have h1 : z * (u * v * u⁻¹) * z⁻¹ = u * v * u⁻¹ :=
    mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_center_iff.1 hz _).symm
  calc ⁅z * u, v⁆ = (z * (u * v * u⁻¹) * z⁻¹) * v⁻¹ := by
        rw [commutatorElement_def]; group
    _ = ⁅u, v⁆ := by rw [h1, commutatorElement_def]

theorem comm_central_mul_right {z : Y} (hz : z ∈ Subgroup.center Y) (u v : Y) :
    ⁅u, z * v⁆ = ⁅u, v⁆ := by
  rw [← commutatorElement_inv, comm_central_mul_left hz, commutatorElement_inv]

theorem comm_conj (g u v : Y) : ⁅g * u * g⁻¹, g * v * g⁻¹⁆ = g * ⁅u, v⁆ * g⁻¹ := by
  rw [commutatorElement_def, commutatorElement_def]; group

theorem aut_inv_commutator (φ : MulAut Y) {x z g z₁ z₂ : Y}
    (hz₁ : z₁ ∈ Subgroup.center Y) (hz₂ : z₂ ∈ Subgroup.center Y)
    (hx : φ x = z₁ * (g * z * g⁻¹)) (hz : φ z = z₂ * (g * x * g⁻¹))
    (hc : ⁅x, z⁆ ∈ Subgroup.center Y) : φ ⁅x, z⁆ = ⁅x, z⁆⁻¹ := by
  rw [map_commutatorElement, hx, hz, comm_central_mul_left hz₁, comm_central_mul_right hz₂,
    comm_conj, ← commutatorElement_inv]
  have h := Subgroup.mem_center_iff.1 ((Subgroup.center Y).inv_mem hc) g
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

theorem commute_mon {x z : Y} (hxz : Commute x z) {w w' : Y} (hw : w ∈ Subgroup.center Y)
    (hw' : w' ∈ Subgroup.center Y) (i j k l : ℕ) :
    Commute (x ^ i * z ^ j * w) (x ^ k * z ^ l * w') := by
  have hc : ∀ g : Y, Commute g w' := fun g => Subgroup.mem_center_iff.1 hw' g
  have hc' : ∀ g : Y, Commute g w := fun g => Subgroup.mem_center_iff.1 hw g
  have key : ∀ g : Y, Commute g (x ^ k) → Commute g (z ^ l) → Commute g (x ^ k * z ^ l * w') :=
    fun g h1 h2 => (h1.mul_right h2).mul_right (hc g)
  exact (((key _ ((Commute.refl x).pow_pow i k) (hxz.pow_pow i l)).mul_left
    (key _ (hxz.symm.pow_pow j k) ((Commute.refl z).pow_pow j l))).mul_left (hc' _).symm)

end Comm

section Cover

variable {Y : Type*} [Group Y] [Finite Y]

theorem lifts_not_commute (hperf : commutator Y = ⊤) (hZ : Nat.card (Subgroup.center Y) = 3)
    (hY : Nat.card Y = 7560) (ρ : Y →* alternatingGroup (Fin 7)) (hρ : Function.Surjective ρ)
    (hker : ∀ y, ρ y = 1 ↔ y ∈ Subgroup.center Y) {x y : Y} (hx : ρ x = elA) (hy : ρ y = elB) :
    ¬ Commute x y := by
  intro hxy
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R₀ : Subgroup Y := sylowP.comap ρ with hR₀
  have hidx : R₀.index = 280 := by
    rw [hR₀, Subgroup.index_comap_of_surjective sylowP hρ, index_sylowP]
  have hcardR : Nat.card R₀ = 27 := by
    have h := R₀.card_mul_index
    rw [hidx, hY] at h
    omega
  have hfac : (Nat.card Y).factorization 3 = 3 :=
    CFSG.HardMathSupport.Solomon.Coordinator.t112m_factorization_eq_three (m := 280)
      (by rw [hY]; norm_num) (by norm_num)
  let R : Sylow 3 Y := Sylow.ofCard R₀ (by rw [hcardR, hfac]; norm_num)
  obtain ⟨z₀, hz₀1⟩ : ∃ z₀ : Subgroup.center Y, z₀ ≠ 1 := by
    by_contra h
    push Not at h
    have : Subsingleton (Subgroup.center Y) := ⟨fun a b => (h a).trans (h b).symm⟩
    have := Nat.card_unique (α := Subgroup.center Y)
    omega
  have hz₀3 : (z₀ : Y) ^ 3 = 1 := by
    have : orderOf z₀ ∣ 3 := hZ ▸ orderOf_dvd_natCard z₀
    exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.1 this)
  obtain ⟨r, hr, s, hs, hrs⟩ := CFSG.HardMathSupport.Solomon.Coordinator.t112m_sylow_nonabelian
    hperf z₀.2 (fun h => hz₀1 (Subtype.ext h)) hz₀3 R
  have key : ∀ t ∈ R₀, ∃ i j : ℕ, ∃ w ∈ Subgroup.center Y, t = x ^ i * y ^ j * w := by
    intro t ht
    obtain ⟨⟨i, j⟩, hij⟩ := (Subgroup.mem_comap.1 ht : ρ t ∈ sylowP)
    refine ⟨(i : ℕ), (j : ℕ), (x ^ (i : ℕ) * y ^ (j : ℕ))⁻¹ * t, ?_,
      (mul_inv_cancel_left _ _).symm⟩
    rw [← hker, map_mul, map_inv, map_mul, map_pow, map_pow, hx, hy, ← hij]
    simp [mon]
  obtain ⟨i, j, w, hw, rfl⟩ := key r hr
  obtain ⟨k, l, w', hw', rfl⟩ := key s hs
  exact hrs (commute_mon hxy hw hw' i j k l)

end Cover

end HatSevenFact

open HatSevenFact in
theorem hatSevenOddInverts_holds : HatSevenOddInverts := by
  intro Y _ hY e φ σ hσ hind z hz
  obtain ⟨hperf, hZ, -⟩ := hY
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Subgroup.center Y) := Nat.finite_of_card_ne_zero (by omega)
  haveI : Finite (Y ⧸ Subgroup.center Y) := Finite.of_equiv _ e.toEquiv.symm
  haveI : Finite Y := Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := Subgroup.center Y)).symm
  have hY : Nat.card Y = 7560 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y)
    rw [hZ, Nat.card_congr e.toEquiv, card_alt7] at h
    omega
  let ρ : Y →* alternatingGroup (Fin 7) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))
  have hρ : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ∀ y, ρ y = 1 ↔ y ∈ Subgroup.center Y := fun y => by
    show e (QuotientGroup.mk y) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hφ : ∀ y, ρ (φ y) = MulAut.conjNormal (H := alternatingGroup (Fin 7)) σ (ρ y) :=
    fun y => hind y
  obtain ⟨x, hx⟩ := hρ elA
  obtain ⟨y, hy⟩ := hρ elB
  have hgσ : Equiv.Perm.sign (σ * permS⁻¹) = 1 := by
    rw [map_mul, map_inv, hσ, permS_sign]
    decide
  let gA : alternatingGroup (Fin 7) := ⟨σ * permS⁻¹, Equiv.Perm.mem_alternatingGroup.2 hgσ⟩
  have e1 : MulAut.conjNormal (H := alternatingGroup (Fin 7)) σ elA = gA * elB * gA⁻¹ := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    show σ * permA * σ⁻¹ = (σ * permS⁻¹) * permB * (σ * permS⁻¹)⁻¹
    rw [mul_inv_rev, inv_inv, ← permS_inv_mul_B]
    group
  have e2 : MulAut.conjNormal (H := alternatingGroup (Fin 7)) σ elB = gA * elA * gA⁻¹ := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    show σ * permB * σ⁻¹ = (σ * permS⁻¹) * permA * (σ * permS⁻¹)⁻¹
    rw [mul_inv_rev, inv_inv, ← permS_inv_mul_A]
    group
  obtain ⟨g, hg⟩ := hρ gA
  have hx1 : ρ (φ x) = ρ (g * y * g⁻¹) := by
    rw [hφ, hx, e1, map_mul, map_mul, map_inv, hg, hy]
  have hy1 : ρ (φ y) = ρ (g * x * g⁻¹) := by
    rw [hφ, hy, e2, map_mul, map_mul, map_inv, hg, hx]
  have hz₁ : φ x * (g * y * g⁻¹)⁻¹ ∈ Subgroup.center Y := by
    rw [← hker, map_mul, map_inv, hx1, mul_inv_cancel]
  have hz₂ : φ y * (g * x * g⁻¹)⁻¹ ∈ Subgroup.center Y := by
    rw [← hker, map_mul, map_inv, hy1, mul_inv_cancel]
  have hc : ⁅x, y⁆ ∈ Subgroup.center Y := by
    rw [← hker, map_commutatorElement, hx, hy]
    exact commutatorElement_eq_one_iff_mul_comm.2 elA_comm_elB
  have hinv : φ ⁅x, y⁆ = ⁅x, y⁆⁻¹ :=
    aut_inv_commutator φ hz₁ hz₂ (inv_mul_cancel_right _ _).symm (inv_mul_cancel_right _ _).symm hc
  have hc1 : ⁅x, y⁆ ≠ 1 := fun h =>
    lifts_not_commute hperf hZ hY ρ hρ hker hx hy (commutatorElement_eq_one_iff_mul_comm.1 h)
  have hc3 : ⁅x, y⁆ ^ 3 = 1 := by
    have : orderOf (⟨⁅x, y⁆, hc⟩ : Subgroup.center Y) ∣ 3 := hZ ▸ orderOf_dvd_natCard _
    exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.1 this)
  have hord : orderOf ⁅x, y⁆ = 3 := orderOf_eq_prime hc3 hc1
  have hzp : Subgroup.zpowers ⁅x, y⁆ = Subgroup.center Y :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hc) (by rw [Nat.card_zpowers, hord, hZ])
  have hzmem : z ∈ Subgroup.zpowers ⁅x, y⁆ := by rw [hzp]; exact hz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hzmem
  rw [← hk, map_zpow, hinv, inv_zpow]

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
