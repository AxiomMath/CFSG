module

public import CFSG.GH74.Generic.BProg.B2.T4PGVDefs
public import CFSG.GH74.Generic.BProg.B2.PumpupOutOrders

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.PGV

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint Subgroup
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (fixSub)
open scoped commutatorElement

@[expose] def Q3Empty (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (H : Subgroup N) (t : N) (K : Subgroup N),
    Q3Cent H t K → P ↥H → False

@[expose] def Q3EmptyIn (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (H : Subgroup N) (t : N) (K : Subgroup N),
    Q3Cent H t K → t ∈ H → P ↥H → False

@[expose] def Q3EmptyOut (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (H : Subgroup N) (t : N) (K : Subgroup N),
    Q3Cent H t K → t ∉ H → P ↥H → False

theorem Q3Empty.of_in_out {P : ∀ (X : Type) [Group X], Prop} (hi : Q3EmptyIn P)
    (ho : Q3EmptyOut P) : Q3Empty P := by
  intro N _ _ H t K hs hP
  by_cases ht : t ∈ H
  · exact hi N H t K hs ht hP
  · exact ho N H t K hs ht hP

namespace Q3Cent

variable {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N} {K : Subgroup N}

theorem le_cent (hs : Q3Cent H t K) : K ≤ H ⊓ centralizer ({t} : Set N) := hs.comp.1

theorem le (hs : Q3Cent H t K) : K ≤ H := hs.comp.1.trans inf_le_left

theorem mul_self (hs : Q3Cent H t K) : t * t = 1 := by
  have h := pow_orderOf_eq_one t
  rwa [hs.inv, sq] at h

theorem ne_one (hs : Q3Cent H t K) : t ≠ 1 := by
  intro h
  have := hs.inv
  rw [h, orderOf_one] at this
  omega

theorem card_K (hs : Q3Cent H t K) : Nat.card ↥K = 5616 :=
  (CFSG.GH74.card_of_lieModel_PSL (n := 3) (by norm_num) hs.type).trans (by decide)

theorem card_dvd_cent (hs : Q3Cent H t K) :
    Nat.card ↥K ∣ Nat.card ↥(H ⊓ centralizer ({t} : Set N)) :=
  Subgroup.card_dvd_of_le hs.le_cent

theorem cent_ne (hs : Q3Cent H t K) : H ⊓ centralizer ({t} : Set N) ≠ H := by
  intro heq
  apply hs.ne_one
  refine hs.faithful t fun h hh => ?_
  have hm : h ∈ H ⊓ centralizer ({t} : Set N) := by rw [heq]; exact hh
  exact (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hm).2).symm

theorem card_cent_lt (hs : Q3Cent H t K) :
    Nat.card ↥(H ⊓ centralizer ({t} : Set N)) < Nat.card ↥H := by
  have hle : H ⊓ centralizer ({t} : Set N) ≤ H := inf_le_left
  rcases lt_or_eq_of_le (Subgroup.card_le_of_le hle) with h | h
  · exact h
  · exact absurd (Subgroup.eq_of_le_of_card_ge hle h.ge) hs.cent_ne

theorem false_of_dvd (hs : Q3Cent H t K) {m : ℕ}
    (hm : Nat.card ↥(H ⊓ centralizer ({t} : Set N)) ∣ m) (h1 : ¬ 5616 ∣ m) : False :=
  h1 (hs.card_K ▸ hs.card_dvd_cent.trans hm)

theorem false_of_card (hs : Q3Cent H t K) {m : ℕ} (hm : Nat.card ↥H = m) (h1 : ¬ 5616 ∣ m) :
    False :=
  hs.false_of_dvd ((Subgroup.card_dvd_of_le inf_le_left).trans hm.dvd) h1

theorem sixteen_dvd (hs : Q3Cent H t K) : 16 ∣ Nat.card ↥K := by
  rw [hs.card_K]
  decide

theorem exists_q8 (hs : Q3Cent H t K) : ∃ ψ : QuaternionGroup 2 →* ↥K, Function.Injective ψ := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := PumpupTableBasic.stated_of_lieModel (Or.inl rfl) hs.type
  have hF2 : ringChar F ≠ 2 :=
    CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow Nat.prime_three (by norm_num) hF
  obtain ⟨ψ, hψ⟩ := PumpupTableBasic.exists_q8_statedProj_three hF2
  exact ⟨e.symm.toMonoidHom.comp ψ, e.symm.injective.comp hψ⟩

theorem exists_q8_H (hs : Q3Cent H t K) :
    ∃ ψ : QuaternionGroup 2 →* ↥H, Function.Injective ψ := by
  obtain ⟨ψ, hψ⟩ := hs.exists_q8
  exact ⟨(Subgroup.inclusion hs.le).comp ψ, (Subgroup.inclusion_injective hs.le).comp hψ⟩

theorem isQuasisimple (hs : Q3Cent H t K) : IsQuasisimple ↥K :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hs.comp.1) hs.comp.2.1

theorem isSimple (hs : Q3Cent H t K) : IsSimpleGroup ↥K :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity ↥K 3 3 1
    (PumpupTableBasic.stated_of_lieModel (Or.inl rfl) hs.type)).2

theorem center_eq_bot (hs : Q3Cent H t K) : center ↥K = ⊥ := by
  have := hs.isSimple
  have : Group.IsPerfect ↥K := hs.isQuasisimple.1
  exact PumpupTableTwoInv.center_eq_bot_of_perfect_of_simple

theorem exists_comp_fixSub (hs : Q3Cent H t K) [H.Normal] :
    ∃ K3 : Subgroup ↥H, IsCompIn (fixSub (MulAut.conjNormal t : MulAut ↥H)) K3 ∧
      Nonempty (↥K ≃* ↥K3) := by
  obtain ⟨Φ⟩ := PumpupOutOrders.exists_fixEquiv (H := H) (t := t)
  set F : Subgroup ↥H := fixSub (MulAut.conjNormal t : MulAut ↥H) with hFdef
  set X : Subgroup N := H ⊓ centralizer ({t} : Set N) with hXdef
  have hL1 : IsComponent (K.subgroupOf X) := hs.comp.2
  let eM : ↥(K.subgroupOf X) ≃* ↥((K.subgroupOf X).map Φ.toMonoidHom) :=
    (K.subgroupOf X).equivMapOfInjective Φ.toMonoidHom Φ.injective
  have hL2 : IsComponent ((K.subgroupOf X).map Φ.toMonoidHom) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eM hL1.1, hL1.2.map Φ.surjective⟩
  set L2 : Subgroup ↥F := (K.subgroupOf X).map Φ.toMonoidHom with hL2def
  set L3 : Subgroup ↥H := L2.map F.subtype with hL3def
  have hL3F : L3 ≤ F := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hsub : L3.subgroupOf F = L2 :=
    Subgroup.comap_map_eq_self_of_injective F.subtype_injective L2
  let eL : ↥K ≃* ↥L3 :=
    (Subgroup.subgroupOfEquivOfLe hs.comp.1).symm.trans
      (eM.trans ((MulEquiv.subgroupCongr hsub).symm.trans (Subgroup.subgroupOfEquivOfLe hL3F)))
  exact ⟨L3, ⟨hL3F, by rw [hsub]; exact hL2⟩, ⟨eL⟩⟩

theorem eq_of_simple_normal (hs : Q3Cent H t K) {L0 : Subgroup N}
    (hL0 : L0 ≤ H ⊓ centralizer ({t} : Set N))
    (hcomm : ∀ a ∈ H ⊓ centralizer ({t} : Set N), ∀ b ∈ H ⊓ centralizer ({t} : Set N),
      ⁅a, b⁆ ∈ L0)
    (hsimple : IsSimpleGroup ↥L0) : K = L0 := by
  set X : Subgroup N := H ⊓ centralizer ({t} : Set N) with hX
  have hLc : IsComponent (K.subgroupOf X) := hs.comp.2
  have hF0comm : ∀ a b : ↥X, ⁅a, b⁆ ∈ L0.subgroupOf X := by
    intro a b
    rw [Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using hcomm a a.2 b b.2
  have hF0 : IsSimpleGroup ↥(L0.subgroupOf X) :=
    ((Subgroup.subgroupOfEquivOfLe hL0).isSimpleGroup_congr).2 hsimple
  have h := PumpupOutOrders.comp_eq_of_simple_normal hLc hF0comm hF0
  rwa [Subgroup.subgroupOf_inj, inf_eq_left.2 hs.comp.1, inf_eq_left.2 hL0] at h

theorem card_eq_of_fixSub (hs : Q3Cent H t K) (L0 : Subgroup ↥H)
    (hL0 : ∀ x ∈ L0, (x : N) ∈ centralizer ({t} : Set N))
    (hcomm : ∀ a : ↥H, (a : N) ∈ centralizer ({t} : Set N) → ∀ b : ↥H,
      (b : N) ∈ centralizer ({t} : Set N) → ⁅a, b⁆ ∈ L0)
    (hsimple : IsSimpleGroup ↥L0) : Nat.card ↥K = Nat.card ↥L0 := by
  set L1 : Subgroup N := L0.map H.subtype with hL1
  have hle : L1 ≤ H ⊓ centralizer ({t} : Set N) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y.2, hL0 y hy⟩
  have hcomm1 : ∀ a ∈ H ⊓ centralizer ({t} : Set N), ∀ b ∈ H ⊓ centralizer ({t} : Set N),
      ⁅a, b⁆ ∈ L1 := by
    intro a ha b hb
    refine ⟨⁅(⟨a, ha.1⟩ : ↥H), ⟨b, hb.1⟩⁆, hcomm _ ha.2 _ hb.2, ?_⟩
    simp [commutatorElement_def]
  let eL : ↥L0 ≃* ↥L1 := L0.equivMapOfInjective H.subtype H.subtype_injective
  have hsimple1 : IsSimpleGroup ↥L1 := (MulEquiv.isSimpleGroup_congr eL).1 hsimple
  rw [hs.eq_of_simple_normal hle hcomm1 hsimple1]
  exact (Nat.card_congr eL.toEquiv).symm

theorem card_eq_of_fixSub_le (hs : Q3Cent H t K) [H.Normal] (L0 : Subgroup ↥H)
    (hL0 : L0 ≤ fixSub (MulAut.conjNormal t : MulAut ↥H))
    (hcomm : ∀ a ∈ fixSub (MulAut.conjNormal t : MulAut ↥H),
      ∀ b ∈ fixSub (MulAut.conjNormal t : MulAut ↥H), ⁅a, b⁆ ∈ L0)
    (hsimple : IsSimpleGroup ↥L0) : Nat.card ↥K = Nat.card ↥L0 :=
  hs.card_eq_of_fixSub L0 (fun _ hx => PumpupOutOrders.mem_fixSub_conjNormal.1 (hL0 hx))
    (fun a ha b hb => hcomm a (PumpupOutOrders.mem_fixSub_conjNormal.2 ha) b
      (PumpupOutOrders.mem_fixSub_conjNormal.2 hb)) hsimple

theorem card_eq_of_fixSub_simple (hs : Q3Cent H t K) [H.Normal]
    (hsimple : IsSimpleGroup ↥(fixSub (MulAut.conjNormal t : MulAut ↥H))) :
    Nat.card ↥K = Nat.card ↥(fixSub (MulAut.conjNormal t : MulAut ↥H)) :=
  hs.card_eq_of_fixSub_le _ le_rfl (fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) hsimple

end Q3Cent

theorem lt_ordG2 {q : ℕ} (hq : 3 ≤ q) : 5616 < CFSG.Open.ordG2 q := by
  unfold CFSG.Open.ordG2
  have h6 : 729 ≤ q ^ 6 := by
    calc 729 = 3 ^ 6 := by norm_num
      _ ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
  have h2 : 9 ≤ q ^ 2 := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  calc 5616 < 729 * 728 * 8 := by norm_num
    _ ≤ q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h6 (by omega)) (by omega)

theorem lt_ordTrialityD4 {q : ℕ} (hq : 3 ≤ q) : 5616 < CFSG.Open.ordTrialityD4 q := by
  unfold CFSG.Open.ordTrialityD4
  have h12 : 531441 ≤ q ^ 12 := by
    calc 531441 = 3 ^ 12 := by norm_num
      _ ≤ q ^ 12 := Nat.pow_le_pow_left hq 12
  have h6 : 729 ≤ q ^ 6 := by
    calc 729 = 3 ^ 6 := by norm_num
      _ ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
  have h2 : 9 ≤ q ^ 2 := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  calc 5616 < 531441 * 1 * 1 * 1 := by norm_num
    _ ≤ q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h12 (by omega)) (by omega)) (by omega)

theorem three_le_pow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) : 3 ≤ p ^ f := by
  have := hp.two_le
  calc 3 ≤ p := by omega
    _ ≤ p ^ f := Nat.le_self_pow (by omega) p

end CFSG.GH74.Generic.BProg.B2.T4.PGV
