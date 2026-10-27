module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bRes2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescSuzuki

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA TauCeti

section Reduction

@[expose] def TD4Exc (p : ℕ) {Y : Type} [Group Y] (K B : Subgroup Y) : Prop :=
  p = 3 ∧ Nat.card B = 3 ^ 4 ∧ Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = 3 ∧
    catalogIs (↥K ⧸ Subgroup.center ↥K) (onLie isTrialityD4Big) ∧ ∃ b ∈ B, ¬ InducesInnerMod 3 K b

@[expose] def KDescFamRes (p : ℕ) (Q : CFSGIndex → Prop) : Prop :=
  p.Prime → p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y), KHyp p K B →
    catalogIs (↥K ⧸ Subgroup.center ↥K) Q → Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) < p ^ 3 →
    (fullCoverLevel p ↥K ≠ 4 ∨ TD4Exc p K B) → KConcl p K B ∨ ∃ D J : Subgroup Y, DescData p K B D J

theorem onLie_mono {P P' : LieTypeIndex → Prop} (h : ∀ d, P d → P' d) : ∀ i, onLie P i → onLie P' i := by
  intro i hi
  cases i with
  | lie dd => exact h _ hi
  | _ => exact hi.elim

theorem kDescFam_of_klie {p : ℕ} (hL : KD264KLie p) {Q : CFSGIndex → Prop}
    (hQ : ∀ i, Q i → onLie (fun _ => True) i) (hres : KDescFamRes p Q) : KDescFam p Q := by
  intro hp hp2 Y _ _ K B h hc hcB
  by_cases hlev : fullCoverLevel p ↥K = 4
  · have hK : CFSG.Open.IsKGroup ↥K := isKGroup_of_le h.kgroup K
    obtain ⟨i, hi, e⟩ := hc
    have hc' : catalogIs (↥K ⧸ Subgroup.center ↥K) (onLie fun _ => True) := ⟨i, hQ i hi, e⟩
    rcases hL Y K B h.normal h.qs hK hc' h.core hlev h.elem h.sup h.card h.maxrank h.cent with h1 | ⟨h3, h4, h5, h6, h7⟩
    · exact Or.inl h1
    · exact hres hp hp2 Y K B h ⟨i, hi, e⟩ hcB (Or.inr ⟨h3, h4, h5, h6, h7⟩)
  · exact hres hp hp2 Y K B h hc hcB (Or.inl hlev)

theorem kDescFam_of_klie' {p : ℕ} (hL : p.Prime → p ≠ 2 → KD264KLie p) {Q : CFSGIndex → Prop}
    (hQ : ∀ i, Q i → onLie (fun _ => True) i) (hres : KDescFamRes p Q) : KDescFam p Q :=
  fun hp hp2 => kDescFam_of_klie (hL hp hp2) hQ hres hp hp2

section Suzuki

theorem i264bResidual2_of_klie (hL : ∀ p : ℕ, p.Prime → p ≠ 2 → KD264KLie p)
    (td42_3 : KDescFam 3 fTD42) (td42_7 : TD42SevenRank) (u38_3 : KDescFam 3 fU38)
    (linear : ∀ p, KDescFamRes p fLinear) (unitary : ∀ p, KDescFamRes p fUnitary)
    (symplectic : ∀ p, KDescFamRes p fSymplectic) (omegaPlus : ∀ p, KDescFamRes p fOmegaPlus)
    (omegaMinus : ∀ p, KDescFamRes p fOmegaMinus) (e6 : ∀ p, KDescFamRes p fE6)
    (e7 : ∀ p, KDescFamRes p fE7) (e8 : ∀ p, KDescFamRes p fE8) (f4 : ∀ p, KDescFamRes p fF4)
    (g2 : ∀ p, KDescFamRes p fG2) (twE6 : ∀ p, KDescFamRes p fTwE6)
    (triD4 : ∀ p, KDescFamRes p fTriD4) (reeTits : ∀ p, KDescFamRes p fReeTits) :
    I264bResidual2 where
  td42_3 := td42_3
  td42_7 := td42_7
  u38_3 := u38_3
  linear p := kDescFam_of_klie' (hL p) (fun i hi => onLie_mono (fun _ _ => trivial) i hi) (linear p)
  unitary p := kDescFam_of_klie' (hL p) (fun i hi => onLie_mono (fun _ _ => trivial) i hi) (unitary p)
  symplectic p :=
    kDescFam_of_klie' (hL p) (fun i hi => onLie_mono (fun _ _ => trivial) i hi) (symplectic p)
  omegaPlus p :=
    kDescFam_of_klie' (hL p) (fun i hi => onLie_mono (fun _ _ => trivial) i hi) (omegaPlus p)
  omegaMinus p :=
    kDescFam_of_klie' (hL p) (fun i hi => onLie_mono (fun _ _ => trivial) i hi) (omegaMinus p)
  e6 p := kDescFam_of_klie' (hL p) (fun i hi => onLie_mono (fun _ _ => trivial) i hi) (e6 p)
  e7 p := kDescFam_of_klie' (hL p) (fun i hi => onLie_mono (fun _ _ => trivial) i hi) (e7 p)
  e8 p := kDescFam_of_klie' (hL p) (fun i hi => onLie_mono (fun _ _ => trivial) i hi) (e8 p)
  f4 p := kDescFam_of_klie' (hL p) (fun i hi => onLie_mono (fun _ _ => trivial) i hi) (f4 p)
  g2 p := kDescFam_of_klie' (hL p) (fun i hi => onLie_mono (fun _ _ => trivial) i hi) (g2 p)
  twE6 p := kDescFam_of_klie' (hL p) (fun i hi => onLie_mono (fun _ _ => trivial) i hi) (twE6 p)
  triD4 p := kDescFam_of_klie' (hL p) (fun i hi => onLie_mono (fun _ _ => trivial) i hi) (triD4 p)
  suzuki := kDescFam_suzuki_holds
  reeTits p :=
    kDescFam_of_klie' (hL p) (fun i hi => onLie_mono (fun _ _ => trivial) i hi) (reeTits p)

end Suzuki

end Reduction

end CFSG.LocalAnalysis.GLTheoremA.HDesc
