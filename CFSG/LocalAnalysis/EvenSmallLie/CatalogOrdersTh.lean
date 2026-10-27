module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersThCheck
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.EvenSmallLie.CatalogOrders

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native
open scoped Matrix

theorem dvd_card_units_of_pow_eq_one {M : Type*} [Monoid M] (S : Submonoid M) {X : M}
    (hX : X ∈ S) {q : ℕ} (hq : q.Prime) (hpow : X ^ q = 1) (hne : X ≠ 1) :
    q ∣ Nat.card Sˣ := by
  have : Fact q.Prime := ⟨hq⟩
  have h : (⟨X, hX⟩ : S) ^ q = 1 := Subtype.ext (by simpa using hpow)
  let u : Sˣ := Units.ofPowEqOne _ q h hq.ne_zero
  have hu : u ≠ 1 := fun h1 => hne (by simpa [u] using congrArg (fun v : Sˣ => ((v : S) : M)) h1)
  rw [← orderOf_eq_prime (Units.pow_ofPowEqOne _ _) hu]
  exact orderOf_dvd_natCard u

theorem dvd_card_of_prodOrderOK {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
    {sA sB : String} {q k : ℕ} (hq : q.Prime) (h : prodOrderOK O sA sB q k = true) :
    q ∣ Nat.card (NativeSporadic.seedMonoid p d 1 sA sB)ˣ := by
  simp only [prodOrderOK, Bool.and_eq_true] at h
  obtain ⟨hpow, hmove⟩ := h
  have hA := Sp.decode_wf sA
  have hB := Sp.decode_wf sB
  have hX := Sp.mul_wf hA hB
  have hXm : Sp.toMat (O.mul (O.decode sA) (O.decode sB)) =
      NativeSporadic.decode p d 1 sA * NativeSporadic.decode p d 1 sB := by
    rw [Sp.toMat_mul hA hB, Sp.toMat_decode, Sp.toMat_decode]
  obtain ⟨hP, hPm⟩ := Sp.pow_spec hX q
  have h1 := Sp.toMat_eq hP Sp.one_wf hpow
  rw [hPm, Sp.toMat_one, hXm] at h1
  have hmem : NativeSporadic.decode p d 1 sA * NativeSporadic.decode p d 1 sB ∈
      NativeSporadic.seedMonoid p d 1 sA sB :=
    Submonoid.mul_mem _ (Submonoid.subset_closure (Set.mem_insert _ _))
      (Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl))
  refine dvd_card_units_of_pow_eq_one _ hmem hq h1 fun hone => ?_
  apply Sp.toVec_ne hmove
  rw [Sp.toVec_vmul (Sp.unit_wf k) hX, hXm, hone, Matrix.vecMul_one]

theorem nineteen_dvd_card_Th
    : 19 ∣ Nat.card CFSG.Blueprint.NativeSporadic.Th :=
  dvd_card_of_prodOrderOK (spec2 248) (by norm_num) th_prodOrder_check

end CFSG.EvenSmallLie.CatalogOrders
