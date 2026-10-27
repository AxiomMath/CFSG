module

public import CFSG.GH74.Generic.BProg.B3.Obs
public import CFSG.GH74.Generic.BProg.B1.PilotS5Facts
public import CFSG.Walter.J1Props.Aut

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.Blueprint CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution.Balance Subgroup
open CFSG.GH74.Generic.BProg.B1.PilotS5
open scoped commutatorElement

namespace LocBalJ1

section Abstract

variable {X : Type} [Group X]

theorem conj_injective_of_center (hZ : ∀ z : X, (∀ g : X, g * z = z * g) → z = 1) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  apply hZ t
  intro g
  have h2 := congrArg (fun f : MulAut X => f g) ht
  simp only [MulAut.conj_apply, MulAut.one_apply] at h2
  rw [mul_inv_eq_iff_eq_mul] at h2
  exact h2.symm

theorem nonempty_mulEquiv_of_inner (hZ : ∀ z : X, (∀ g : X, g * z = z * g) → z = 1)
    (hInn : ∀ φ : MulAut X, ∃ g : X, φ = MulAut.conj g) {H : Subgroup (MulAut X)}
    (hH : (MulAut.conj : X →* MulAut X).range ≤ H) : Nonempty (X ≃* ↥H) := by
  let φ : X →* ↥H := (MulAut.conj : X →* MulAut X).codRestrict H fun g => hH ⟨g, rfl⟩
  have hinj : Function.Injective φ := fun s t hst =>
    conj_injective_of_center hZ (congrArg Subtype.val hst)
  have hsurj : Function.Surjective φ := by
    intro h
    obtain ⟨g, hg⟩ := hInn h.1
    exact ⟨g, Subtype.ext hg.symm⟩
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

theorem involutionOddCore_eq_bot_of_inner (hZ : ∀ z : X, (∀ g : X, g * z = z * g) → z = 1)
    (hInn : ∀ φ : MulAut X, ∃ g : X, φ = MulAut.conj g)
    (hO : ∀ t : X, t * t = 1 → t ≠ 1 → involutionOddCore t = ⊥) {H : Subgroup (MulAut X)}
    (hH : (MulAut.conj : X →* MulAut X).range ≤ H) {b : ↥H} (hb2 : b * b = 1) (hb1 : b ≠ 1) :
    involutionOddCore b = ⊥ := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_inner hZ hInn hH
  obtain ⟨t, rfl⟩ := e.surjective b
  have ht2 : t * t = 1 := e.injective (by rw [map_mul, hb2, map_one])
  have ht1 : t ≠ 1 := fun h => hb1 (by rw [h, map_one])
  have h := involutionOddCore_map e t
  rw [hO t ht2 ht1, Subgroup.map_bot] at h
  exact h.symm

theorem deltaCore_eq_bot_of_inner (hZ : ∀ z : X, (∀ g : X, g * z = z * g) → z = 1)
    (hInn : ∀ φ : MulAut X, ∃ g : X, φ = MulAut.conj g)
    (hO : ∀ t : X, t * t = 1 → t ≠ 1 → involutionOddCore t = ⊥) {H : Subgroup (MulAut X)}
    (hH : (MulAut.conj : X →* MulAut X).range ≤ H) {D : Subgroup ↥H} (hcard : Nat.card ↥D = 4)
    (hsq : ∀ d ∈ D, d * d = 1) : deltaCore D = ⊥ := by
  have hne : D ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hcard
    omega
  obtain ⟨⟨d, hd⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  rw [eq_bot_iff]
  exact (deltaCore_le_involutionOddCore hd hd1').trans
    (involutionOddCore_eq_bot_of_inner hZ hInn hO hH (hsq d hd) hd1').le

theorem isLocBal32_of_inner (hZ : ∀ z : X, (∀ g : X, g * z = z * g) → z = 1)
    (hInn : ∀ φ : MulAut X, ∃ g : X, φ = MulAut.conj g)
    (hO : ∀ t : X, t * t = 1 → t ≠ 1 → involutionOddCore t = ⊥) (B : Subgroup (MulAut X))
    (hB : ∀ b ∈ B, b * b = 1) : IsLocBal32 X B := by
  intro H hH hBH
  refine ⟨fun b hb hb1 c hc b' _ => ?_, fun D _ hcard hsq => ?_⟩
  · have hb2 : b * b = 1 := Subtype.ext (by simpa using hB _ (Subgroup.mem_subgroupOf.mp hb))
    rw [involutionOddCore_eq_bot_of_inner hZ hInn hO hH hb2 hb1, Subgroup.mem_bot] at hc
    rw [hc]
    simp
  · exact deltaCore_eq_bot_of_inner hZ hInn hO hH hcard hsq

end Abstract

section J1

theorem involutionOddCore_eq_bot_walterJ1 {u : walterJ1}
    (hu2 : u * u = 1) (hu1 : u ≠ 1) : involutionOddCore u = ⊥ := by
  have hord : orderOf u = 2 := orderOf_eq_prime (by rwa [sq]) hu1
  obtain ⟨L, hle, hnm, heq, ⟨eL⟩⟩ := walterJ1_split u hord
  have hs : IsSplit 60 u L (centralizer ({u} : Set walterJ1)) :=
    IsSplit.of_equiv_alternating hord hle hnm heq eL
  unfold involutionOddCore
  rw [CFSG.Assembly.Dichotomy.oddCore_eq_pPrimeCore, hs.pPrimeCore_eq_bot, Subgroup.map_bot]

theorem involutionOddCore_eq_bot_of_equiv {X : Type} [Group X]
    (e : X ≃* walterJ1) {t : X} (ht2 : t * t = 1) (ht1 : t ≠ 1) : involutionOddCore t = ⊥ := by
  have h := involutionOddCore_map e t
  rw [involutionOddCore_eq_bot_walterJ1 (by rw [← map_mul, ht2, map_one])
    (fun h => ht1 (e.injective (by rw [h, map_one])))] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h

theorem forall_mulAut_inner_of_equiv {X : Type} [Group X]
    (e : X ≃* walterJ1) : ∀ φ : MulAut X, ∃ g : X, φ = MulAut.conj g := by
  intro φ
  obtain ⟨g, hg⟩ := CFSG.Walter.J1Props.J3_aut (MulAut.congr e φ)
  refine ⟨e.symm g, MulEquiv.ext fun x => e.injective ?_⟩
  have := congrArg (fun ψ : MulAut walterJ1 => ψ (e x)) hg
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply] at this
  rw [this, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

end J1

end LocBalJ1

section Main

variable {Kt : Type} [Group Kt]

theorem locBal32_J1 (hK : NativeSporadic.IsSporadic Kt .J1) (B : Subgroup (MulAut Kt))
    (hB : ∀ b ∈ B, b * b = 1) : IsLocBal32 Kt B := by
  obtain ⟨e⟩ := hK
  let e0 : Kt ≃* walterJ1 := e.trans CFSG.Walter.walterJ1EquivNative.symm
  exact LocBalJ1.isLocBal32_of_inner (center_of_equiv e0)
    (LocBalJ1.forall_mulAut_inner_of_equiv e0)
    (fun _ ht2 ht1 => LocBalJ1.involutionOddCore_eq_bot_of_equiv e0 ht2 ht1) B hB

end Main

end CFSG.GH74.Generic.BProg.B3
