module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Base

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
  CFSG.Quasithin.BlueprintB2
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def actTriv (H Q U : Subgroup G) : Subgroup G where
  carrier := {h | h ∈ H ∧ h ∈ normalizer (Q : Set G) ∧ h ∈ normalizer (U : Set G) ∧
    ∀ x ∈ Q, x⁻¹ * (h * x * h⁻¹) ∈ U}
  one_mem' := ⟨H.one_mem, Subgroup.one_mem _, Subgroup.one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haH, haQ, haU, ha⟩ ⟨hbH, hbQ, hbU, hb⟩
    refine ⟨H.mul_mem haH hbH, Subgroup.mul_mem _ haQ hbQ, Subgroup.mul_mem _ haU hbU, ?_⟩
    intro x hx
    have hy : b * x * b⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hbQ x).mp hx
    have hu := hb x hx
    have h1 := ha x hx
    have h2 : a * (x⁻¹ * (b * x * b⁻¹)) * a⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp haU _).mp hu
    have e : x⁻¹ * (a * b * x * (a * b)⁻¹) =
        (x⁻¹ * (a * x * a⁻¹)) * (a * (x⁻¹ * (b * x * b⁻¹)) * a⁻¹) := by group
    rw [e]
    exact U.mul_mem h1 h2
  inv_mem' := by
    rintro a ⟨haH, haQ, haU, ha⟩
    refine ⟨H.inv_mem haH, Subgroup.inv_mem _ haQ, Subgroup.inv_mem _ haU, ?_⟩
    intro x hx
    have hx' : a⁻¹ * x * a ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haQ) x).mp hx
      simpa using this
    have h1 := ha _ hx'
    have e : x⁻¹ * (a⁻¹ * x * a⁻¹⁻¹) = (((a⁻¹ * x * a)⁻¹ * (a * (a⁻¹ * x * a) * a⁻¹)))⁻¹ := by
      group
    rw [e]
    exact U.inv_mem (by simpa using h1)

theorem actTriv_le {H Q U : Subgroup G} : actTriv H Q U ≤ H := fun _ h => h.1

theorem conj_mem_actTriv {H Q U : Subgroup G} (hQ : H ≤ normalizer (Q : Set G))
    (hU : H ≤ normalizer (U : Set G)) {g : G} (hg : g ∈ H) {k : G} (hk : k ∈ actTriv H Q U) :
    g * k * g⁻¹ ∈ actTriv H Q U := by
  obtain ⟨hkH, hkQ, hkU, hk⟩ := hk
  refine ⟨H.mul_mem (H.mul_mem hg hkH) (H.inv_mem hg),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hQ hg) hkQ) (Subgroup.inv_mem _ (hQ hg)),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hU hg) hkU) (Subgroup.inv_mem _ (hU hg)), ?_⟩
  intro x hx
  have hx' : g⁻¹ * x * g ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hQ hg)) x).mp hx
    simpa using this
  have h1 := hk _ hx'
  have h2 : g * ((g⁻¹ * x * g)⁻¹ * (k * (g⁻¹ * x * g) * k⁻¹)) * g⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp (hU hg) _).mp h1
  have e : x⁻¹ * (g * k * g⁻¹ * x * (g * k * g⁻¹)⁻¹) =
      g * ((g⁻¹ * x * g)⁻¹ * (k * (g⁻¹ * x * g) * k⁻¹)) * g⁻¹ := by group
  rw [e]
  exact h2

theorem le_normalizer_actTriv {H Q U : Subgroup G} (hQ : H ≤ normalizer (Q : Set G))
    (hU : H ≤ normalizer (U : Set G)) : H ≤ normalizer (actTriv H Q U : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · exact conj_mem_actTriv hQ hU hg
  · intro hk
    have := conj_mem_actTriv hQ hU (H.inv_mem hg) hk
    simpa [mul_assoc] using this

section Hyp

variable [Finite G]

structure A3LiftHyp (H Q : Subgroup G) {r : ℕ} (L : Fin r → Subgroup G) : Prop where
  Q_le : Q ≤ H
  Q_norm : H ≤ normalizer (Q : Set G)
  Q_two : IsPGroup 2 Q
  cent_le : H ⊓ Subgroup.centralizer (Q : Set G) ≤ Q
  inj : Function.Injective L
  short : ∀ i, IsShort2 (L i)
  L_le : ∀ i, L i ≤ H
  ord3 : ∀ i, Nat.card (↥(L i) ⧸ CFSG.pCore 2 ↥(L i)) = 3
  Q_norm_L : ∀ i, Q ≤ normalizer (L i : Set G)
  comm_eq : ∀ i, ⁅Q, L i⁆ = blockQ (L i)
  U_le_Z : ∀ i, blockQ (L i) ≤ centerTorsion 2 Q
  gen : H = Q ⊔ ⨆ i, L i
  three : ∀ h ∈ H, ∃ k : ℕ, h ^ 3 ^ k ∈ Q

namespace A3LiftHyp

variable {H Q : Subgroup G} {r : ℕ} {L : Fin r → Subgroup G} (h : A3LiftHyp H Q L)

include h

theorem block (i : Fin r) :
    blockQ (L i) = blockU (L i) ∧ Nat.card (blockU (L i)) = 4 ∧ blockZ (L i) = ⊥ ∧
      Nonempty (↥(L i) ≃* alternatingGroup (Fin 4)) ∧ IsAltType (L i) 3 :=
  short_order_three_is_alternating_four (h.short i) (h.ord3 i)

omit [Finite G] in
theorem U_le_Q (i : Fin r) : blockQ (L i) ≤ Q := (h.U_le_Z i).trans (centerTorsion_le 2 Q)

omit [Finite G] h in
theorem U_le_L (i : Fin r) : blockQ (L i) ≤ L i := C1.blockQ_le _

omit [Finite G] in
theorem Q_inf_L (i : Fin r) : Q ⊓ L i = blockQ (L i) := by
  refine le_antisymm ?_ (le_inf (h.U_le_Q i) (U_le_L i))
  have hnormal : ((Q ⊓ L i).subgroupOf (L i)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro y l hy hl
    refine ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (h.Q_norm (h.L_le i hl)) y).mp hy.1
      exact this
    · exact (L i).mul_mem ((L i).mul_mem hl hy.2) ((L i).inv_mem hl)
  exact CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 (Q ⊓ L i) (L i)
    inf_le_right hnormal ((h.Q_two).to_le inf_le_left)

omit [Finite G] in
theorem U_le_centerTorsion : (⨆ i, blockQ (L i) : Subgroup G) ≤ centerTorsion 2 Q :=
  iSup_le h.U_le_Z

omit [Finite G] in
theorem U_le_Q' : (⨆ i, blockQ (L i) : Subgroup G) ≤ Q :=
  h.U_le_centerTorsion.trans (centerTorsion_le 2 Q)

omit [Finite G] in
theorem U_elem : IsElemAbelian 2 (⨆ i, blockQ (L i) : Subgroup G) := by
  have hZ := h.U_le_centerTorsion
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => (mem_centerTorsion_iff.mp (hZ hx)).2.2⟩
  have hb := (mem_centerTorsion_iff.mp (hZ b.2)).2.1 (a : G) (h.U_le_Q' a.2)
  exact hb

omit [Finite G] in
theorem Q_comm_U {u : G} (hu : u ∈ (⨆ i, blockQ (L i) : Subgroup G)) {q : G} (hq : q ∈ Q) :
    q * u = u * q :=
  (mem_centerTorsion_iff.mp (h.U_le_centerTorsion hu)).2.1 q hq

omit [Finite G] in
theorem H_le_normalizer_U : H ≤ normalizer ((⨆ i, blockQ (L i) : Subgroup G) : Set G) := by
  set U : Subgroup G := ⨆ i, blockQ (L i) with hU
  have hQU : Q ≤ normalizer (U : Set G) := by
    intro q hq
    refine mem_normalizer_of_conj_mem (fun x hx => ?_) (fun x hx => ?_)
    · rw [show q * x * q⁻¹ = x by rw [h.Q_comm_U hx hq]; group]
      exact hx
    · rw [show q⁻¹ * x * q = x by rw [h.Q_comm_U hx (Q.inv_mem hq)]; group]
      exact hx
  have hLU : ∀ i, L i ≤ normalizer (U : Set G) := by
    intro i l hl
    have key : ∀ l ∈ L i, ∀ x ∈ U, l * x * l⁻¹ ∈ U := by
      intro l hl x hx
      refine Subgroup.iSup_induction (fun j => blockQ (L j)) (C := fun x => l * x * l⁻¹ ∈ U) hx
        ?_ ?_ ?_
      · intro j u hu
        have h1 : ⁅l, u⁆ ∈ ⁅L i, Q⁆ := Subgroup.commutator_mem_commutator hl (h.U_le_Q j hu)
        rw [Subgroup.commutator_comm, h.comm_eq i] at h1
        have h2 : l * u * l⁻¹ = ⁅l, u⁆ * u := by simp [commutatorElement_def]
        rw [h2]
        exact U.mul_mem (Subgroup.mem_iSup_of_mem i h1) (Subgroup.mem_iSup_of_mem j hu)
      · simp
      · intro x y hx hy
        have : l * (x * y) * l⁻¹ = (l * x * l⁻¹) * (l * y * l⁻¹) := by group
        rw [this]
        exact U.mul_mem hx hy
    exact mem_normalizer_of_conj_mem (key l hl)
      (fun x hx => by simpa using key l⁻¹ ((L i).inv_mem hl) x hx)
  rw [h.gen]
  exact sup_le hQU (iSup_le hLU)

omit [Finite G] in
theorem Q_le_normalizer_U : Q ≤ normalizer ((⨆ i, blockQ (L i) : Subgroup G) : Set G) :=
  fun _ hq => h.H_le_normalizer_U (h.Q_le hq)

omit [Finite G] in
theorem L_le_actTriv (i : Fin r) : L i ≤ actTriv H Q (⨆ j, blockQ (L j)) := by
  intro l hl
  refine ⟨h.L_le i hl, h.Q_norm (h.L_le i hl), h.H_le_normalizer_U (h.L_le i hl), fun x hx => ?_⟩
  have h1 : ⁅x⁻¹, l⁆ ∈ ⁅Q, L i⁆ := Subgroup.commutator_mem_commutator (Q.inv_mem hx) hl
  rw [h.comm_eq i] at h1
  have : x⁻¹ * (l * x * l⁻¹) = ⁅x⁻¹, l⁆ := by rw [commutatorElement_def]; group
  rw [this]
  exact Subgroup.mem_iSup_of_mem i h1

omit [Finite G] in
theorem actTriv_sup_eq : actTriv H Q (⨆ j, blockQ (L j)) ⊔ Q = H := by
  refine le_antisymm (sup_le actTriv_le h.Q_le) ?_
  calc H = Q ⊔ ⨆ i, L i := h.gen
    _ ≤ actTriv H Q (⨆ j, blockQ (L j)) ⊔ Q :=
      sup_le le_sup_right (iSup_le fun i => (h.L_le_actTriv i).trans le_sup_left)

omit [Finite G] in
theorem odd_mem_actTriv {c : G} (hc : c ∈ H) (hodd : Odd (orderOf c)) :
    c ∈ actTriv H Q (⨆ j, blockQ (L j)) :=
  mem_of_odd_of_sup_eq (le_normalizer_actTriv h.Q_norm h.H_le_normalizer_U) h.Q_le h.Q_two
    h.actTriv_sup_eq hc hodd

theorem eq_one_of_odd_centralizes {c : G} (hc : c ∈ H) (hodd : Odd (orderOf c))
    (hcU : ∀ u ∈ (⨆ i, blockQ (L i) : Subgroup G), c * u = u * c) : c = 1 := by
  obtain ⟨-, -, -, hdisp⟩ := h.odd_mem_actTriv hc hodd
  have hcent := centralizes_of_odd_trivial_factors h.Q_two h.U_le_Q' h.Q_le_normalizer_U
    (h.Q_norm hc) hodd hcU hdisp
  have hcQ : c ∈ Q := h.cent_le ⟨hc, Subgroup.mem_centralizer_iff.mpr fun x hx => (hcent x hx).symm⟩
  obtain ⟨k, hk⟩ := h.Q_two ⟨c, hcQ⟩
  have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (orderOf c) (2 ^ k) :=
    (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd))
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem cent_U_le_Q {c : G} (hc : c ∈ H)
    (hcU : ∀ u ∈ (⨆ i, blockQ (L i) : Subgroup G), c * u = u * c) : c ∈ Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hd : (c ^ 2 ^ a) ∈ H := H.pow_mem hc _
  have hdU : ∀ u ∈ (⨆ i, blockQ (L i) : Subgroup G), c ^ 2 ^ a * u = u * c ^ 2 ^ a :=
    fun u hu => ((show Commute c u from hcU u hu).pow_left (2 ^ a))
  have hdord : orderOf (c ^ 2 ^ a) = b := by
    have hdvd : 2 ^ a ∣ orderOf c := ⟨b, hab⟩
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hab]
    exact Nat.mul_div_cancel_left b (pow_pos two_pos a)
  have h1 : c ^ 2 ^ a = 1 := h.eq_one_of_odd_centralizes hd (by rw [hdord]; exact hb) hdU
  have hb1 : b = 1 := by rw [← hdord, h1, orderOf_one]
  have h3 : ¬ 3 ∣ orderOf c := by
    rw [hab, hb1, mul_one]
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  obtain ⟨k, hk⟩ := h.three c hc
  exact mem_of_not_dvd_orderOf_of_pow_mem h3 hk

end A3LiftHyp

end Hyp

end CFSG.QuasithinUnique.Setup.Wreath
