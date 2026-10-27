module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33Abstract
public import CFSG.GH74.KGroups.U33
public import Certificates.Certificate214020

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33Fin

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.LieType.ChevTwo.OppCl.U33Fin
  CFSG.LieType.BorelTits CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

theorem checkT0_eq : checkT0 () = true :=
  Certificates.certificate214020.1

theorem checkZ_eq : checkZ () = true :=
  Certificates.certificate214020.2.1

theorem checkC_eq : checkC () = true :=
  Certificates.certificate214020.2.2.1

theorem checkE1_eq : checkE1 () = true :=
  Certificates.certificate214020.2.2.2

section Facts


theorem T0L_facts :
    (T0L ()).length = 32 ∧ (T0L ()).Nodup ∧ (1 : Equiv.Perm (Fin 28)) ∈ T0L () ∧
      (∀ x ∈ T0L (), x⁻¹ ∈ T0L ()) ∧ (∀ x ∈ T0L (), x ∈ elems ()) ∧
      (∀ x ∈ T0L (), ∀ y ∈ T0L (), x * y ∈ T0L ()) := by
  have h := checkT0_eq
  simp only [checkT0, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨hlen, hnd⟩, h1⟩, hall⟩ := h
  exact ⟨hlen, hnd, h1, fun x hx => (hall x hx).1.1, fun x hx => (hall x hx).1.2,
    fun x hx => (hall x hx).2⟩

theorem Z_facts :
    z0 ∈ T0L () ∧ z0 ^ 4 = 1 ∧ z0 ^ 2 ≠ 1 ∧ (∀ x ∈ T0L (), x * z0 = z0 * x) ∧
      (∀ x ∈ T0L (), (∀ y ∈ T0L (), x * y = y * x) → x ∈ zL) := by
  have h := checkZ_eq
  simp only [checkZ, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
    List.all_eq_true, List.contains_iff_mem, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hz, h4⟩, h2⟩, hc⟩, hZ⟩ := h
  refine ⟨hz, h4, h2, hc, fun x hx hxc => ?_⟩
  rcases hZ x hx with h | h
  · exfalso
    rw [Bool.eq_false_iff] at h
    apply h
    simpa [List.all_eq_true] using hxc
  · exact h

theorem C_facts : ((elems ()).filter fun x => x * t0 == t0 * x).length = 96 := by
  have h := checkC_eq
  rw [checkC] at h
  exact beq_iff_eq.1 h

theorem E1_facts : ∀ g ∈ elems (), g ^ 3 = 1 → g ≠ 1 → g * t0 = t0 * g →
    ∀ x ∈ T0L (), x * g = g * x → x ∈ zL := by
  intro g hg h3 h1 hc x hx hxg
  have hcheck := checkE1_eq
  rw [checkE1] at hcheck
  have h2 := List.all_eq_true.1 hcheck g hg
  have hcond : (g ^ 3 == 1 && g != 1 && g * t0 == t0 * g) = true := by
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, beq_iff_eq]
    exact ⟨⟨h3, h1⟩, hc⟩
  rw [hcond, Bool.not_true, Bool.false_or] at h2
  have h4 := List.all_eq_true.1 h2 x hx
  have hxc : (x * g == g * x) = true := beq_iff_eq.2 hxg
  rw [hxc, Bool.not_true, Bool.false_or] at h4
  exact List.contains_iff_mem.1 h4

end Facts

section Model

variable {K : Type} [Group K]
  (e : K ≃* QP.originalSubgroup)

@[expose] def psi : K →* Equiv.Perm (Fin 28) := QP.originalSubgroup.subtype.comp e.toMonoidHom

theorem psi_injective : Function.Injective (psi e) := Subtype.val_injective.comp e.injective

theorem psi_mem (x : K) : psi e x ∈ elems () := (mem_elemsT QP QP_ok _).2 (e x).2

theorem psi_surj {y : Equiv.Perm (Fin 28)} (hy : y ∈ elems ()) : ∃ x : K, psi e x = y :=
  ⟨e.symm ⟨y, (mem_elemsT QP QP_ok y).1 hy⟩, by simp [psi]⟩

def Tk : Subgroup K where
  carrier := {x | psi e x ∈ T0L ()}
  mul_mem' := fun {a b} ha hb => by
    have ha' : psi e a ∈ T0L () := ha
    have hb' : psi e b ∈ T0L () := hb
    have h := T0L_facts.2.2.2.2.2 (psi e a) ha' (psi e b) hb'
    rw [← map_mul] at h
    exact h
  one_mem' := by
    have h := T0L_facts.2.2.1
    rw [← map_one (psi e)] at h
    exact h
  inv_mem' := fun {a} ha => by
    have ha' : psi e a ∈ T0L () := ha
    have h := T0L_facts.2.2.2.1 (psi e a) ha'
    rw [← map_inv] at h
    exact h

theorem mem_Tk {x : K} : x ∈ Tk e ↔ psi e x ∈ T0L () := Iff.rfl

theorem card_Tk : Nat.card (Tk e) = 32 := by
  have hnd := T0L_facts.2.1
  have hlen := T0L_facts.1
  have hbij : Function.Bijective
      (fun x : Tk e => (⟨psi e x, List.mem_toFinset.2 ((mem_Tk e).1 x.2)⟩ : ((T0L ()).toFinset))) := by
    constructor
    · intro a b hab
      have h1 : psi e (a : K) = psi e (b : K) :=
        congrArg (Subtype.val : {y // y ∈ (T0L ()).toFinset} → Equiv.Perm (Fin 28)) hab
      exact Subtype.ext (psi_injective e h1)
    · rintro ⟨y, hy⟩
      have hy' : y ∈ T0L () := List.mem_toFinset.1 hy
      obtain ⟨x, hx⟩ := psi_surj e (T0L_facts.2.2.2.2.1 y hy')
      exact ⟨⟨x, by rw [mem_Tk, hx]; exact hy'⟩, Subtype.ext hx⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup hnd, hlen]

theorem z0_mem_P : z0 ∈ QP.originalSubgroup :=
  (mem_elemsT QP QP_ok z0).1 (T0L_facts.2.2.2.2.1 z0 Z_facts.1)

def zk : K := e.symm ⟨z0, z0_mem_P⟩

theorem psi_zk : psi e (zk e) = z0 := by simp [zk, psi]

theorem zk_mem_Tk : zk e ∈ Tk e := by
  rw [mem_Tk, psi_zk]
  exact Z_facts.1

theorem orderOf_zk [Fact (Nat.Prime 2)] : orderOf (zk e) = 4 := by
  have h1 : orderOf z0 = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := z0)
      (by simpa using Z_facts.2.2.1) (by simpa using Z_facts.2.1)
    simpa using this
  rw [← orderOf_injective (psi e) (psi_injective e) (zk e), psi_zk]
  exact h1

theorem mem_zpowers_zk_of_mem_zL {x : K} (hx : psi e x ∈ zL) : x ∈ Subgroup.zpowers (zk e) := by
  simp only [zL, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h
  · have : x = 1 := psi_injective e (by rw [h, map_one])
    rw [this]
    exact one_mem _
  · have : x = zk e := psi_injective e (by rw [h, psi_zk])
    rw [this]
    exact Subgroup.mem_zpowers _
  · have : x = zk e ^ 2 := psi_injective e (by rw [h, map_pow, psi_zk])
    rw [this]
    exact pow_mem (Subgroup.mem_zpowers _) 2
  · have : x = zk e ^ 3 := psi_injective e (by rw [h, map_pow, psi_zk])
    rw [this]
    exact pow_mem (Subgroup.mem_zpowers _) 3

theorem zk_comm {x : K} (hx : x ∈ Tk e) : x * zk e = zk e * x := by
  apply psi_injective e
  rw [map_mul, map_mul, psi_zk]
  exact Z_facts.2.2.2.1 _ ((mem_Tk e).1 hx)

theorem zk_central {x : K} (hx : x ∈ Tk e) (hxc : ∀ y ∈ Tk e, x * y = y * x) :
    x ∈ Subgroup.zpowers (zk e) := by
  refine mem_zpowers_zk_of_mem_zL e (Z_facts.2.2.2.2 _ ((mem_Tk e).1 hx) fun y' hy' => ?_)
  obtain ⟨y, hy⟩ := psi_surj e (T0L_facts.2.2.2.2.1 y' hy')
  have hyT : y ∈ Tk e := by rw [mem_Tk, hy]; exact hy'
  rw [← hy, ← map_mul, ← map_mul, hxc y hyT]

theorem psi_zk_sq : psi e (zk e ^ 2) = t0 := by
  rw [map_pow, psi_zk]
  rfl

theorem card_centralizer_zk : Nat.card (Subgroup.centralizer ({zk e ^ 2} : Set K)) = 96 := by
  set L : List (Equiv.Perm (Fin 28)) := (elems ()).filter fun x => x * t0 == t0 * x with hL
  have hnd : L.Nodup := (nodup_elemsT QP QP_ok).filter _
  have hlen : L.length = 96 := C_facts
  have hmemL : ∀ y, y ∈ L ↔ y ∈ elems () ∧ y * t0 = t0 * y := by
    intro y
    rw [hL, List.mem_filter, beq_iff_eq]
  have hcent : ∀ x : K, x ∈ Subgroup.centralizer ({zk e ^ 2} : Set K) ↔
      psi e x * t0 = t0 * psi e x := by
    intro x
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      have := h (zk e ^ 2) rfl
      have h2 := congrArg (psi e) this
      rw [map_mul, map_mul, psi_zk_sq] at h2
      exact h2.symm
    · intro h y hy
      rw [Set.mem_singleton_iff.1 hy]
      apply psi_injective e
      rw [map_mul, map_mul, psi_zk_sq]
      exact h.symm
  have hbij : Function.Bijective
      (fun x : Subgroup.centralizer ({zk e ^ 2} : Set K) =>
        (⟨psi e x, List.mem_toFinset.2 ((hmemL _).2 ⟨psi_mem e x, (hcent x).1 x.2⟩)⟩ :
          L.toFinset)) := by
    constructor
    · intro a b hab
      have h1 : psi e (a : K) = psi e (b : K) :=
        congrArg (Subtype.val : {y // y ∈ L.toFinset} → Equiv.Perm (Fin 28)) hab
      exact Subtype.ext (psi_injective e h1)
    · rintro ⟨y, hy⟩
      have hy' := (hmemL y).1 (List.mem_toFinset.1 hy)
      obtain ⟨x, hx⟩ := psi_surj e hy'.1
      exact ⟨⟨x, (hcent x).2 (by rw [hx]; exact hy'.2)⟩, Subtype.ext hx⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup hnd, hlen]

theorem zk_E1 {g : K} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (hgt : g * zk e ^ 2 = zk e ^ 2 * g)
    {x : K} (hx : x ∈ Tk e) (hxg : x * g = g * x) : x ∈ Subgroup.zpowers (zk e) := by
  refine mem_zpowers_zk_of_mem_zL e (E1_facts (psi e g) (psi_mem e g) ?_ ?_ ?_ (psi e x)
    ((mem_Tk e).1 hx) ?_)
  · rw [← map_pow, hg3, map_one]
  · intro h
    exact hg1 (psi_injective e (by rw [h, map_one]))
  · have h2 := congrArg (psi e) hgt
    rw [map_mul, map_mul, psi_zk_sq] at h2
    exact h2
  · rw [← map_mul, ← map_mul, hxg]

end Model

section Main

variable {K : Type} [Group K]

theorem radRigidInner_of_model (e : K ≃* QP.originalSubgroup) (hBT : HoldsTits K 2) :
    RadRigidInner 2 K := by
  haveI : Finite K := Finite.of_equiv QP.originalSubgroup e.symm.toEquiv
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKcard : Nat.card K = 6048 := by
    rw [Nat.card_congr e.toEquiv, card_group QP QP_ok]
    exact QP_valid.2
  have hTcard := card_Tk e
  have hT2 : IsPGroup 2 (Tk e) := IsPGroup.of_card (n := 5) (by rw [hTcard]; norm_num)
  have hfact : (6048 : ℕ).factorization 2 = 5 := by
    have h : (6048 : ℕ) = 2 ^ 5 * 189 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 189 by norm_num)]
  have hsyl : Nat.card (Tk e) = 2 ^ (Nat.card K).factorization 2 := by
    rw [hTcard, hKcard, hfact]
    norm_num
  refine radRigidInner_of_sylow_core hBT (Sylow.ofCard (Tk e) hsyl) ?_
  intro R hR hRT hTN g hg hgo
  rw [Sylow.coe_ofCard] at hRT hTN
  exact u33_core (Tk e) (zk e) hT2 hTcard (zk_mem_Tk e) (orderOf_zk e) (fun x hx => zk_comm e hx)
    (fun x hx hxc => zk_central e hx hxc) (card_centralizer_zk e)
    (fun g hg3 hg1 hgt x hx hxg => zk_E1 e hg3 hg1 hgt hx hxg) R hR hRT hTN g hg hgo

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33Fin
