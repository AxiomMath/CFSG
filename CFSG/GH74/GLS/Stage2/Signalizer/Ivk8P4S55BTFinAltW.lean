module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinAltW

open Equiv Equiv.Perm Subgroup CFSG

variable {α : Type*} [Fintype α] [DecidableEq α]

@[expose] def AltWit (r : ℕ) (σ : Perm α) : Prop :=
  ∃ E : Subgroup (Perm α), E ≤ alternatingGroup α ∧ IsPGroup r ↥E ∧
    (r = 2 → ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, σ * x * σ⁻¹ ∈ E) ∧
    ∃ x ∈ E, σ * x * σ⁻¹ ≠ x

theorem AltWit.conj {r : ℕ} {c : Perm α} (h : AltWit r c) (g : Perm α) :
    AltWit r (g * c * g⁻¹) := by
  obtain ⟨E, hEA, hEp, hEc, hEn, x, hxE, hx⟩ := h
  let φ : Perm α →* Perm α := (MulAut.conj g).toMonoidHom
  have hφ : ∀ y, φ y = g * y * g⁻¹ := fun y => rfl
  refine ⟨E.map φ, ?_, hEp.map φ, ?_, ?_, ⟨φ x, ⟨x, hxE, rfl⟩, ?_⟩⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [hφ]
    exact alternatingGroup.normal.conj_mem y (hEA hy) g
  · rintro hr _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, hEc hr y hy z hz]
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨c * y * c⁻¹, hEn y hy, ?_⟩
    rw [hφ, hφ]
    group
  · intro h'
    apply hx
    rw [hφ] at h'
    have : g * (c * x * c⁻¹) * g⁻¹ = g * x * g⁻¹ := by
      rw [← h']
      group
    exact mul_left_cancel (mul_right_cancel this)

theorem AltWit.extend {m n r : ℕ} (h : m ≤ n) {c : Perm (Fin m)} (hc : AltWit r c) :
    AltWit r (extendDomainHom (Fin.castLEquiv h) c) := by
  obtain ⟨E, hEA, hEp, hEc, hEn, x, hxE, hx⟩ := hc
  have hφ : Function.Injective (extendDomainHom (Fin.castLEquiv h)) :=
    extendDomainHom_injective _
  refine ⟨E.map (extendDomainHom (Fin.castLEquiv h)), ?_, hEp.map _, ?_, ?_,
    ⟨_, ⟨x, hxE, rfl⟩, ?_⟩⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [Perm.mem_alternatingGroup, extendDomainHom_apply, sign_extendDomain]
    exact Perm.mem_alternatingGroup.mp (hEA hy)
  · rintro hr _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, hEc hr y hy z hz]
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨c * y * c⁻¹, hEn y hy, by simp only [map_mul, map_inv]⟩
  · intro h'
    apply hx
    apply hφ
    simpa only [map_mul, map_inv] using h'

theorem AltWit.of_cycleType {m n r : ℕ} (h : m ≤ n) {c : Perm (Fin m)} (hc : AltWit r c)
    {σ : Perm (Fin n)} (hσ : σ.cycleType = c.cycleType) : AltWit r σ := by
  have hct : (extendDomainHom (Fin.castLEquiv h) c).cycleType = σ.cycleType := by
    rw [hσ, extendDomainHom_apply, cycleType_extendDomain]
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr hct)
  rw [← hg]
  exact (hc.extend h).conj g

theorem cycleType_eq_of_prime {β : Type*} [Fintype β] [DecidableEq β] {σ : Perm α}
    {τ : Perm β} {p : ℕ} (hp : p.Prime) (hσ : orderOf σ = p) (hτ : orderOf τ = p)
    (hs : σ.support.card = τ.support.card) : σ.cycleType = τ.cycleType := by
  obtain ⟨a, ha⟩ := cycleType_prime_order (σ := σ) (by rw [hσ]; exact hp)
  obtain ⟨b, hb⟩ := cycleType_prime_order (σ := τ) (by rw [hτ]; exact hp)
  rw [hσ] at ha
  rw [hτ] at hb
  have h1 : σ.support.card = (a + 1) * p := by
    rw [← sum_cycleType, ha, Multiset.sum_replicate, smul_eq_mul]
  have h2 : τ.support.card = (b + 1) * p := by
    rw [← sum_cycleType, hb, Multiset.sum_replicate, smul_eq_mul]
  have hab : a = b := by
    rw [h1, h2] at hs
    have := Nat.eq_of_mul_eq_mul_right hp.pos hs
    omega
  rw [ha, hb, hab]

theorem altWit_of_gens {c : Perm α} (S : List (Perm α)) (hA : ∀ s ∈ S, Perm.sign s = 1)
    (hinv : ∀ s ∈ S, s * s = 1) (hcomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s)
    (hc : ∀ s ∈ S, c * s * c⁻¹ ∈ closure {x | x ∈ S}) (hmove : ∃ s ∈ S, c * s * c⁻¹ ≠ s) :
    AltWit 2 c := by
  have hall : ∀ x ∈ closure {x | x ∈ S}, ∀ y ∈ closure {x | x ∈ S}, x * y = y * x := by
    intro x hx y hy
    have hpair : ({x | x ∈ S} : Set (Perm α)).Pairwise Commute :=
      fun a ha b hb _ => hcomm a ha b hb
    exact congrArg Subtype.val
      ((Subgroup.isMulCommutative_closure hpair).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq : ∀ x ∈ closure {x | x ∈ S}, x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hinv x hx
    | one => simp
    | mul x y hx hy hxx hyy =>
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [← hall x hx y hy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hxx, hyy, one_mul]
    | inv x hx hxx => rw [← mul_inv_rev, hxx, inv_one]
  refine ⟨closure {x | x ∈ S}, ?_, ?_, fun _ => hall, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    intro s hs
    exact Perm.mem_alternatingGroup.mpr (hA s hs)
  · refine IsPGroup.iff_orderOf.mpr fun g => ?_
    have hg2 : (g : Perm α) * g = 1 := hsq _ g.2
    have hg : orderOf g ∣ 2 ^ 1 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [pow_two] using hg2))
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hg
    exact ⟨k, hk⟩
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hc x hx
    | one => simp
    | mul x y _ _ hxx hyy =>
      have : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hxx hyy
    | inv x _ hxx =>
      have : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hxx
  · obtain ⟨s, hs, hsm⟩ := hmove
    exact ⟨s, subset_closure hs, hsm⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinAltW
