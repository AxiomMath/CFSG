module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseNearDef
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseMir
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseModelA

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG.OddStandard.AltStdSec.SylowSn

theorem model_mem_nearSet_iff {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {l : List ℕ}
    (ι : Gam l →* Equiv.Perm (Fin n)) (hι : Function.Injective ι)
    (hsg : ∀ γ, Equiv.Perm.sign (ι γ) = sgG l γ)
    (hfix : ∀ γ, Nat.card (Function.fixedPoints (ι γ)) = fixG l γ)
    (hP : ∀ x, x ∈ P ↔ ∃ γ, sgG l γ = 1 ∧ ι γ = x) (γ : Gam l) :
    ι γ ∈ nearSet n P ↔ γ ∈ nearModel l := by
  have hι1 : ι γ = 1 ↔ γ = 1 := by
    rw [← map_one ι]
    exact hι.eq_iff
  have hsq : ι γ * ι γ = 1 ↔ γ * γ = 1 := by
    rw [← map_mul, ← map_one ι]
    exact hι.eq_iff
  constructor
  · rintro (h | ⟨-, h2, h1, h3, h4⟩)
    · have h' : γ = 1 := hι1.1 (Set.mem_singleton_iff.1 h)
      subst h'
      exact ⟨map_one _, Or.inl rfl⟩
    · have h5 : sgG l γ = 1 := (hsg γ).symm.trans h4
      have h6 := hfix γ
      exact ⟨h5, Or.inr ⟨hsq.1 h2, fun h => h1 (hι1.2 h), by omega⟩⟩
  · rintro ⟨h5, h | ⟨h2, h1, h3⟩⟩
    · exact Or.inl (Set.mem_singleton_iff.2 (hι1.2 h))
    · have h6 := hfix γ
      exact Or.inr ⟨(hP _).2 ⟨γ, h5, rfl⟩, hsq.2 h2, fun h => h1 (hι1.1 h), by omega,
        (hsg γ).trans h5⟩

theorem nearTriple_model {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {l : List ℕ}
    (ι : Gam l →* Equiv.Perm (Fin n)) (hι : Function.Injective ι)
    (hsg : ∀ γ, Equiv.Perm.sign (ι γ) = sgG l γ)
    (hfix : ∀ γ, Nat.card (Function.fixedPoints (ι γ)) = fixG l γ)
    (hP : ∀ x, x ∈ P ↔ ∃ γ, sgG l γ = 1 ∧ ι γ = x) (γ : Gam l) :
    nearTriple n P (ι γ) = prodCnt (nearModel l) γ := by
  unfold nearTriple
  refine prodCnt_inj ι hι (fun h => model_mem_nearSet_iff ι hι hsg hfix hP h) (fun x hx => ?_) γ
  rcases hx with hx | hx
  · exact ⟨1, by rw [map_one]; exact (Set.mem_singleton_iff.1 hx).symm⟩
  · obtain ⟨δ, -, hδ⟩ := (hP x).1 hx.1
    exact ⟨δ, hδ⟩

theorem nearCount_model {l : List ℕ} (hl : l = [2, 3]) (P : Subgroup (Equiv.Perm (Fin 12)))
    (ι : Gam l →* Equiv.Perm (Fin 12)) (hι : Function.Injective ι)
    (hsg : ∀ γ, Equiv.Perm.sign (ι γ) = sgG l γ)
    (hfix : ∀ γ, Nat.card (Function.fixedPoints (ι γ)) = fixG l γ)
    (hP : ∀ x, x ∈ P ↔ ∃ γ, sgG l γ = 1 ∧ ι γ = x)
    (y : Equiv.Perm (Fin 12)) (hyP : y ∈ P) (hyN : y ∈ nearSet 12 P) (hy1 : y ≠ 1)
    (hyc : ∀ p ∈ P, p * y = y * p) : nearTriple 12 P 1 ≠ nearTriple 12 P y := by
  subst hl
  obtain ⟨γc, -, rfl⟩ := (hP y).1 hyP
  have hγcN : γc ∈ nearModel [2, 3] := (model_mem_nearSet_iff ι hι hsg hfix hP γc).1 hyN
  have hγc1 : γc ≠ 1 := by
    rintro rfl
    exact hy1 (map_one ι)
  have hcent : ∀ δ : Gam [2, 3], sgG [2, 3] δ = 1 → δ * γc = γc * δ := by
    intro δ hδ
    apply hι
    rw [map_mul, map_mul]
    exact hyc (ι δ) ((hP _).2 ⟨δ, hδ, rfl⟩)
  have h1 : nearTriple 12 P 1 = prodCnt (nearModel [2, 3]) 1 := by
    rw [← nearTriple_model ι hι hsg hfix hP 1, map_one]
  rw [h1, nearTriple_model ι hι hsg hfix hP γc]
  exact nearFinite γc hγcN hγc1 hcent

theorem nearCount12 : NearCount12 := by
  intro P hP hp hmax y hyP hyN hy1 hyc
  obtain ⟨ι, hι, hsg, hfix, hPm⟩ := exists_model 12 P hP hp hmax
  exact nearCount_model (by decide) P ι hι hsg hfix hPm y hyP hyN hy1 hyc

end CFSG.OddStandard.AltStdSec
