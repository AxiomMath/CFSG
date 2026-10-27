module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Lift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.TransferComm
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35HLambda
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Data

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Closing
open scoped commutatorElement

theorem commutator_mul_of_commute {H : Type} [Group H] {ℓ ℓ' d d' : H} (h1 : Commute ℓ d)
    (h2 : Commute ℓ d') (h3 : Commute ℓ' d) (h4 : Commute ℓ' d') :
    ⁅ℓ * d, ℓ' * d'⁆ = ⁅ℓ, ℓ'⁆ * ⁅d, d'⁆ := by
  set X : H := d * d' * d⁻¹ with hX
  have hXℓ : Commute ℓ⁻¹ X := ((h1.inv_left.mul_right h2.inv_left).mul_right h1.inv_left.inv_right)
  have hY : Commute ℓ'⁻¹ (X * d'⁻¹) :=
    ((h3.inv_left.mul_right h4.inv_left).mul_right h3.inv_left.inv_right).mul_right
      h4.inv_left.inv_right
  have e1 : ℓ * d * (ℓ' * d') * (ℓ * d)⁻¹ * (ℓ' * d')⁻¹ =
      ℓ * ℓ' * X * ℓ⁻¹ * (d'⁻¹ * ℓ'⁻¹) := by
    rw [hX, mul_inv_rev, mul_inv_rev]
    have : d * ℓ' = ℓ' * d := h3.eq.symm
    calc ℓ * d * (ℓ' * d') * (d⁻¹ * ℓ⁻¹) * (d'⁻¹ * ℓ'⁻¹)
        = ℓ * (d * ℓ') * d' * d⁻¹ * ℓ⁻¹ * (d'⁻¹ * ℓ'⁻¹) := by simp only [mul_assoc]
      _ = ℓ * ℓ' * (d * d' * d⁻¹) * ℓ⁻¹ * (d'⁻¹ * ℓ'⁻¹) := by rw [this]; simp only [mul_assoc]
  have e2 : ℓ * ℓ' * X * ℓ⁻¹ * (d'⁻¹ * ℓ'⁻¹) = ℓ * ℓ' * ℓ⁻¹ * (X * d'⁻¹) * ℓ'⁻¹ := by
    calc ℓ * ℓ' * X * ℓ⁻¹ * (d'⁻¹ * ℓ'⁻¹) = ℓ * ℓ' * (X * ℓ⁻¹) * d'⁻¹ * ℓ'⁻¹ := by
          simp only [mul_assoc]
      _ = ℓ * ℓ' * (ℓ⁻¹ * X) * d'⁻¹ * ℓ'⁻¹ := by rw [hXℓ.eq]
      _ = ℓ * ℓ' * ℓ⁻¹ * (X * d'⁻¹) * ℓ'⁻¹ := by simp only [mul_assoc]
  have e3 : ℓ * ℓ' * ℓ⁻¹ * (X * d'⁻¹) * ℓ'⁻¹ = ℓ * ℓ' * ℓ⁻¹ * ℓ'⁻¹ * (X * d'⁻¹) := by
    calc ℓ * ℓ' * ℓ⁻¹ * (X * d'⁻¹) * ℓ'⁻¹ = ℓ * ℓ' * ℓ⁻¹ * ((X * d'⁻¹) * ℓ'⁻¹) := by
          simp only [mul_assoc]
      _ = ℓ * ℓ' * ℓ⁻¹ * (ℓ'⁻¹ * (X * d'⁻¹)) := by rw [hY.eq]
      _ = ℓ * ℓ' * ℓ⁻¹ * ℓ'⁻¹ * (X * d'⁻¹) := by simp only [mul_assoc]
  simp only [commutatorElement_def]
  rw [e1, e2, e3, hX]

theorem le_of_perfect_of_le_sup_solvable {H : Type} [Group H] {L C J : Subgroup H}
    (hC : C ≤ centralizer (L : Set H)) (hCs : Group.IsSolvable ↥C)
    (hJ : ⁅J, J⁆ = J) (hLperf : ⁅L, L⁆ = L) (hJLC : J ≤ L ⊔ C) : J ≤ L := by
  set D : ℕ → Subgroup H := fun n => (derivedSeries ↥C n).map C.subtype with hD
  have hDle : ∀ n, D n ≤ C := fun n x hx => by
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have hD0 : D 0 = C := by
    show (derivedSeries ↥C 0).map C.subtype = C
    rw [derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hDsucc : ∀ n, D (n + 1) = ⁅D n, D n⁆ := fun n => by
    simp only [hD, derivedSeries_succ, Subgroup.map_commutator]
  have key : ∀ n, J ≤ L ⊔ D n := by
    intro n
    induction n with
    | zero => rw [hD0]; exact hJLC
    | succ n ih =>
      rw [← hJ]
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      obtain ⟨ℓ, hℓ, d, hd, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
        ((hDle n).trans hC) (ih ha)
      obtain ⟨ℓ', hℓ', d', hd', rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
        ((hDle n).trans hC) (ih hb)
      have h1 : ⁅ℓ * d, ℓ' * d'⁆ = ⁅ℓ, ℓ'⁆ * ⁅d, d'⁆ := by
        refine commutator_mul_of_commute ?_ ?_ ?_ ?_
        · exact mem_centralizer_iff.1 ((hDle n).trans hC hd) ℓ hℓ
        · exact mem_centralizer_iff.1 ((hDle n).trans hC hd') ℓ hℓ
        · exact mem_centralizer_iff.1 ((hDle n).trans hC hd) ℓ' hℓ'
        · exact mem_centralizer_iff.1 ((hDle n).trans hC hd') ℓ' hℓ'
      rw [h1, hDsucc]
      exact mul_mem_sup (hLperf ▸ Subgroup.commutator_mem_commutator hℓ hℓ')
        (Subgroup.commutator_mem_commutator hd hd')
  obtain ⟨n, hn⟩ := (Group.isSolvable_def _).1 hCs
  have hDn : D n = ⊥ := by
    show (derivedSeries ↥C n).map C.subtype = ⊥
    rw [hn, Subgroup.map_bot]
  intro x hx
  have := key n hx
  rwa [hDn, sup_bot_eq] at this

theorem commutator_mul_central {X : Type} [Group X] (j j' z z' : X) (hz : ∀ w : X, z * w = w * z)
    (hz' : ∀ w : X, z' * w = w * z') : ⁅j * z, j' * z'⁆ = ⁅j, j'⁆ := by
  simp only [commutatorElement_def, mul_inv_rev]
  have hzz : z * z' * z⁻¹ = z' := by rw [hz z']; group
  calc j * z * (j' * z') * (z⁻¹ * j⁻¹) * (z'⁻¹ * j'⁻¹)
      = j * (z * j') * z' * z⁻¹ * j⁻¹ * (z'⁻¹ * j'⁻¹) := by simp only [mul_assoc]
    _ = j * (j' * z) * z' * z⁻¹ * j⁻¹ * (z'⁻¹ * j'⁻¹) := by rw [hz j']
    _ = j * j' * (z * z' * z⁻¹) * j⁻¹ * (z'⁻¹ * j'⁻¹) := by simp only [mul_assoc]
    _ = j * j' * (z' * j⁻¹) * z'⁻¹ * j'⁻¹ := by rw [hzz]; simp only [mul_assoc]
    _ = j * j' * (j⁻¹ * z') * z'⁻¹ * j'⁻¹ := by rw [hz' j⁻¹]
    _ = j * j' * j⁻¹ * j'⁻¹ := by group

@[expose] def ExcPerfect (p : ℕ) : ExcClass := fun Y _ ν =>
  ∃ J : Subgroup Y, J ≤ fixSubgroup ν ∧ Group.IsPerfect ↥J ∧ p ∣ Nat.card ↥J

@[expose] def PairClass.AvoidsPrimeCentralizer (Q : PairClass) (s : TauCeti.SporadicName) (p : ℕ) :
    Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L K : Subgroup H) (u : H), OddCover s L → Q H L K u →
    ¬ p ∣ Nat.card ↥(L ⊓ centralizer ({u} : Set H))

namespace Closing.ClosingSetup

variable {H : Type} [Group H] [Finite H] {N L : Subgroup H} {t u : H} (S : ClosingSetup H N L t u)
include S

theorem false_of_perfect_fixed {p : ℕ} (hout : OutTwo (↥L ⧸ center ↥L))
    (hcard : ¬ p ∣ Nat.card ↥(L ⊓ centralizer ({u} : Set H))) {u₁ : H}
    (hN : u₁ ∈ normalizer (L : Set H)) (hu₁₂ : u₁ * u₁ = 1) (hconj : IsConj u u₁)
    (hex : ∃ J : Subgroup (↥L ⧸ center ↥L), J ≤ fixSubgroup (normalizerAction L ⟨u₁, hN⟩) ∧
      Group.IsPerfect ↥J ∧ p ∣ Nat.card ↥J) : False := by
  classical
  obtain ⟨J, hJfix, hJperf, hpJ⟩ := hex
  obtain ⟨d, hd⟩ := isConj_iff.1 hconj
  let π : ↥L →* ↥L ⧸ center ↥L := QuotientGroup.mk' (center ↥L)
  let A : Subgroup ↥L := J.comap π ⊓ (centralizer ({u₁} : Set H)).comap L.subtype
  have hAmem : ∀ x : ↥L, x ∈ A ↔ π x ∈ J ∧ (x : H) ∈ centralizer ({u₁} : Set H) := fun x => Iff.rfl
  have hAsurj : ∀ j ∈ J, ∃ x ∈ A, π x = j := by
    intro j hj
    obtain ⟨y, hy, hyu⟩ := exists_fixed_lift S.centre_odd hN hu₁₂ (hJfix hj)
    refine ⟨y, (hAmem y).2 ⟨?_, ?_⟩, hy⟩
    · show (y : ↥L ⧸ center ↥L) ∈ J
      rw [hy]
      exact hj
    · rw [mem_centralizer_singleton_iff]
      calc (y : H) * u₁ = (u₁ * (y : H) * u₁⁻¹) * u₁ := by rw [hyu]
        _ = u₁ * y := by group
  have hAπ : A.map π = J := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact ((hAmem x).1 hx).1
    · intro j hj
      obtain ⟨x, hx, rfl⟩ := hAsurj j hj
      exact ⟨x, hx, rfl⟩
  have hJJ : ⁅J, J⁆ = J := isPerfect_iff.mp hJperf
  set Js : Subgroup ↥L := ⁅A, A⁆ with hJs
  have hJsA : Js ≤ A := Subgroup.commutator_le.2 fun a ha b hb =>
    A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)
  have hJsπ : Js.map π = J := by
    rw [hJs, Subgroup.map_commutator, hAπ, hJJ]
  have hmk : ∀ a ∈ A, ∃ j ∈ Js, ∃ z ∈ center ↥L, a = j * z := by
    intro a ha
    have : π a ∈ Js.map π := hJsπ ▸ ((hAmem a).1 ha).1
    obtain ⟨j, hj, hja⟩ := this
    refine ⟨j, hj, j⁻¹ * a, ?_, by group⟩
    exact QuotientGroup.eq.1 hja
  have hJsperf : ⁅Js, Js⁆ = Js := by
    refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb =>
      Js.mul_mem (Js.mul_mem (Js.mul_mem ha hb) (Js.inv_mem ha)) (Js.inv_mem hb)) ?_
    rw [hJs]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    obtain ⟨j, hj, z, hz, rfl⟩ := hmk a ha
    obtain ⟨j', hj', z', hz', rfl⟩ := hmk b hb
    rw [commutator_mul_central j j' z z' (fun w => (Subgroup.mem_center_iff.1 hz w).symm)
      (fun w => (Subgroup.mem_center_iff.1 hz' w).symm)]
    exact Subgroup.commutator_mem_commutator hj hj'
  have hpJs : p ∣ Nat.card ↥Js := by
    have h1 : Nat.card ↥(Js.map π) ∣ Nat.card ↥Js := Subgroup.card_map_dvd Js π
    rw [hJsπ] at h1
    exact hpJ.trans h1
  let f : ↥L →* H := (conjHom d⁻¹).comp L.subtype
  have hf : Function.Injective f := (conjHom_injective d⁻¹).comp L.subtype_injective
  set J₂ : Subgroup H := Js.map f with hJ₂
  have hJ₂C : J₂ ≤ centralizer ({u} : Set H) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxu₁ : (x : H) * u₁ = u₁ * (x : H) :=
      mem_centralizer_singleton_iff.1 ((hAmem x).1 (hJsA hx)).2
    rw [mem_centralizer_singleton_iff]
    show d⁻¹ * (x : H) * d⁻¹⁻¹ * u = u * (d⁻¹ * (x : H) * d⁻¹⁻¹)
    have hu₁ : u₁ = d * u * d⁻¹ := hd.symm
    rw [hu₁] at hxu₁
    calc d⁻¹ * (x : H) * d⁻¹⁻¹ * u = d⁻¹ * ((x : H) * (d * u * d⁻¹)) * d := by group
      _ = d⁻¹ * ((d * u * d⁻¹) * (x : H)) * d := by rw [hxu₁]
      _ = u * (d⁻¹ * (x : H) * d⁻¹⁻¹) := by group
  have hJ₂N : J₂ ≤ normalizer (L : Set H) := fun z hz => S.hyp38 (hJ₂C hz)
  have hJ₂perf : ⁅J₂, J₂⁆ = J₂ := by
    rw [hJ₂, ← Subgroup.map_commutator, hJsperf]
  have hLperf : ⁅L, L⁆ = L := isPerfect_iff.mp S.quasisimple.1
  have hLC : J₂ ≤ L ⊔ centralizer (L : Set H) := by
    rw [← hJ₂perf]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    exact comm_mem_sup (K₀ := centralizer (L : Set H)) S.perfect hout le_rfl
      (fun x hx y hy => ⟨fun _ => ⟨fun _ => hy, fun _ => hx⟩, fun _ => mul_mem hx hy⟩)
      (fun g hg x hx => conj_mem_centralizer hg hx) (hJ₂N ha) (hJ₂N hb)
  have hCsolv : Group.IsSolvable ↥(centralizer (L : Set H)) := by
    obtain ⟨S₀, hS₀⟩ := S.cyclicSylow
    exact isSolvable_of_cyclic_sylow_two fun P => (MulEquiv.isCyclic (Sylow.equiv P S₀)).mpr hS₀
  have hJ₂L : J₂ ≤ L := le_of_perfect_of_le_sup_solvable le_rfl hCsolv hJ₂perf hLperf hLC
  have hcard₂ : Nat.card ↥J₂ = Nat.card ↥Js := Subgroup.card_map_of_injective hf
  apply hcard
  have hdvd : Nat.card ↥J₂ ∣ Nat.card ↥(L ⊓ centralizer ({u} : Set H)) :=
    Subgroup.card_dvd_of_le (le_inf hJ₂L hJ₂C)
  rw [hcard₂] at hdvd
  exact hpJs.trans hdvd

end Closing.ClosingSetup

theorem excExcluded_of_perfect_fixed {s : TauCeti.SporadicName} {Q : PairClass} {p : ℕ}
    (hQ : Q.InL) (hA : Q.AvoidsPrimeCentralizer s p)
    (hout : ∀ (Y : Type) [Group Y], IsSporadic Y s → OutTwo Y) :
    ExcExcluded s (ExcPerfect p) Q := by
  intro H _ _ N L K t u hcov hhyp hQu u₁ hN hu₁₂ _ hconj hex
  have huL := hQ H L K u hQu
  have S := Closing.ClosingSetup.of_hypQ hhyp huL
  exact S.false_of_perfect_fixed (hout _ hcov.2.2) (hA H L K u hcov hQu) hN hu₁₂ hconj hex

end CFSG.EvenSporadicStandard.Induction
