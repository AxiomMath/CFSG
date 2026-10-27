module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineWLevi
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Cover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.FieldIndexW

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP
open CFSG.RankThree.PartOne.OutStructure (OutPNice Inn)
open scoped commutatorElement

section Levi

variable {Y : Type} [Group Y]

@[expose] def LeviInnAtPW (p : ℕ) (P : Subgroup Y) : Prop :=
  ∀ l ∈ P, ∀ k : ℕ, (∀ w ∈ wPre P, ⁅l ^ (p ^ k), w⁆ = 1) →
    ∃ v ∈ wPre P, ∀ w ∈ wPre P, ⁅l * v, w⁆ ∈ pCoreOf 2 P

variable [Finite Y]

theorem actsInnerlyW_of_innP {p : ℕ} {L P : Subgroup Y} [L.Normal] (hCP : CompParab L P)
    (hLevi : LeviInnAtPW p P) {a : Y} (ha3 : IsPGroup p (Subgroup.zpowers a))
    (haN : a ∈ Subgroup.normalizer (P : Set Y))
    (hin : convAut L a ∈ Inn (↥L ⧸ Subgroup.center ↥L)) :
    ∃ v ∈ wPre P, ∀ w ∈ wPre P, ⁅a * v, w⁆ ∈ pCoreOf 2 P := by
  have hPL : P ≤ L := hCP.parab.1
  obtain ⟨l₀, hc⟩ := exists_mem_centralizer_of_convAut_mem_inn L hCP.comp.2.2.1 hin
  set c : Y := a * (l₀ : Y)⁻¹ with hcdef
  have hcL : ∀ x ∈ L, x * c = c * x := fun x hx => Subgroup.mem_centralizer_iff.1 hc x hx
  have hac : a = c * (l₀ : Y) := by rw [hcdef]; group
  have hconj : ∀ h : Y, h ∈ L → (l₀ : Y) * h * (l₀ : Y)⁻¹ = a * h * a⁻¹ := by
    intro h hh
    have hX : (l₀ : Y) * h * (l₀ : Y)⁻¹ ∈ L := L.mul_mem (L.mul_mem l₀.2 hh) (L.inv_mem l₀.2)
    have key : c * ((l₀ : Y) * h * (l₀ : Y)⁻¹) * c⁻¹ = (l₀ : Y) * h * (l₀ : Y)⁻¹ := by
      rw [← hcL _ hX]; group
    rw [hac]
    calc (l₀ : Y) * h * (l₀ : Y)⁻¹ = c * ((l₀ : Y) * h * (l₀ : Y)⁻¹) * c⁻¹ := key.symm
      _ = c * (l₀ : Y) * h * (c * (l₀ : Y))⁻¹ := by group
  have hl₀N : (l₀ : Y) ∈ Subgroup.normalizer (P : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hconj h (hPL hh)]
      exact (Subgroup.mem_normalizer_iff.1 haN h).1 hh
    · intro hh
      have hhL : h ∈ L := by
        have := L.mul_mem (L.mul_mem (L.inv_mem l₀.2) (hPL hh)) l₀.2
        simpa [mul_assoc] using this
      rw [hconj h hhL] at hh
      exact (Subgroup.mem_normalizer_iff.1 haN h).2 hh
  have hl₀P : (l₀ : Y) ∈ P :=
    CFSG.HardMathSupport.Curtis.UnitaryLevi.mem_of_mem_normalizer_of_isParabolicTwo hCP.parab
      l₀.2 hl₀N
  obtain ⟨k, hk⟩ := ha3 ⟨a, Subgroup.mem_zpowers a⟩
  have hak : a ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcomm : Commute c (l₀ : Y) := (hcL _ l₀.2).symm
  have hpow : (l₀ : Y) ^ (p ^ k) = (c ^ (p ^ k))⁻¹ := by
    rw [hac, hcomm.mul_pow] at hak
    exact eq_inv_of_mul_eq_one_right hak
  have hVL : wPre P ≤ L := (wPre_le P).trans hPL
  obtain ⟨v, hv, hvw⟩ := hLevi _ hl₀P k fun w hw => by
    have h1 : Commute (c ^ (p ^ k)) w := Commute.pow_left (hcL w (hVL hw)).symm _
    rw [commutatorElement_eq_one_iff_mul_comm, hpow]
    exact h1.inv_left.eq
  refine ⟨v, hv, fun w hw => ?_⟩
  have hvL : v ∈ L := hVL hv
  have hwL : w ∈ L := hVL hw
  have hX : (l₀ : Y) * v * w * v⁻¹ * (l₀ : Y)⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem (L.mul_mem (L.mul_mem l₀.2 hvL) hwL) (L.inv_mem hvL)) (L.inv_mem l₀.2)
  have hkey : c * ((l₀ : Y) * v * w * v⁻¹ * (l₀ : Y)⁻¹) * c⁻¹ =
      (l₀ : Y) * v * w * v⁻¹ * (l₀ : Y)⁻¹ := by
    rw [← hcL _ hX]; group
  have : ⁅a * v, w⁆ = ⁅(l₀ : Y) * v, w⁆ := by
    rw [commutatorElement_def, commutatorElement_def, hac]
    calc c * (l₀ : Y) * v * w * (c * (l₀ : Y) * v)⁻¹ * w⁻¹
        = (c * ((l₀ : Y) * v * w * v⁻¹ * (l₀ : Y)⁻¹) * c⁻¹) * w⁻¹ := by group
      _ = ((l₀ : Y) * v * w * v⁻¹ * (l₀ : Y)⁻¹) * w⁻¹ := by rw [hkey]
      _ = (l₀ : Y) * v * w * ((l₀ : Y) * v)⁻¹ * w⁻¹ := by group
  rw [this]
  exact hvw w hw

theorem fieldIndexW_coreP {p : ℕ} [Fact p.Prime] {L P : Subgroup Y} [L.Normal]
    {D : Subgroup (MulAut (↥L ⧸ Subgroup.center ↥L))} (hD : PCentral p D) {a : Y}
    (ha3 : IsPGroup p (Subgroup.zpowers a))
    (hout : ¬ ∃ v ∈ wPre P, ∀ w ∈ wPre P, ⁅a * v, w⁆ ∈ pCoreOf 2 P)
    (hLevi : convAut L a ∈ D → ∃ v ∈ wPre P, ∀ w ∈ wPre P, ⁅a * v, w⁆ ∈ pCoreOf 2 P) :
    ∃ N : Subgroup Y, N.Normal ∧ N.index = p := by
  have : Finite (↥L ⧸ Subgroup.center ↥L) := inferInstance
  by_cases h : convAut L a ∈ D
  · exact absurd (hLevi h) hout
  · exact exists_normal_index_prime (convAut L) hD ha3 h

theorem fieldIndexW_of_outPNiceP {p : ℕ} [Fact p.Prime] {L P : Subgroup Y} [L.Normal]
    (hCP : CompParab L P) (hO : OutPNice p (↥L ⧸ Subgroup.center ↥L))
    (hLevi : LeviInnAtPW p P) {a : Y}
    (ha3 : IsPGroup p (Subgroup.zpowers a)) (haN : a ∈ Subgroup.normalizer (P : Set Y))
    (hout : ¬ ∃ v ∈ wPre P, ∀ w ∈ wPre P, ⁅a * v, w⁆ ∈ pCoreOf 2 P) :
    ∃ N : Subgroup Y, N.Normal ∧ N.index = p := by
  obtain ⟨D, hD, hID, hD2⟩ := pCentral_of_outPNice hO
  refine fieldIndexW_coreP hD ha3 hout fun hmem => ?_
  obtain ⟨k, hk⟩ := ha3 ⟨a, Subgroup.mem_zpowers a⟩
  have hak : a ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine actsInnerlyW_of_innP hCP hLevi ha3 haN (hD2 _ hmem k ?_)
  rw [← map_pow, hak, map_one]
  exact Subgroup.one_mem _

end Levi

section Families

@[expose] def FieldIndexAtPW (p : ℕ) {Y : Type} [Group Y] [Finite Y] (L P : Subgroup Y) : Prop :=
  L.Normal → (∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q L ≤ 3) →
    p ∣ Nat.card (wPre P) → Open.pRank p (wPre P) ≤ 1 →
    ∀ a : Y, IsPGroup p (Subgroup.zpowers a) → a ∈ Subgroup.normalizer (P : Set Y) →
    (¬ ∃ v ∈ wPre P, ∀ w ∈ wPre P, ⁅a * v, w⁆ ∈ pCoreOf 2 P) →
    ∃ N : Subgroup Y, N.Normal ∧ N.index = p

@[expose] def FieldIndexOnPW (p : ℕ) (C : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    C (↥L ⧸ Subgroup.center ↥L) → FieldIndexAtPW p L P

@[expose] def LeviInnOnPW (p : ℕ) (C : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    C (↥L ⧸ Subgroup.center ↥L) → L.Normal → (∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q L ≤ 3) →
    p ∣ Nat.card (wPre P) → Open.pRank p (wPre P) ≤ 1 → LeviInnAtPW p P

theorem fieldIndexOnPW_of_outPNice {p : ℕ} [Fact p.Prime] {C : (X : Type) → [Group X] → Prop}
    (hT : ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
      C (↥L ⧸ Subgroup.center ↥L) → (∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q L ≤ 3) →
      OutPNice p (↥L ⧸ Subgroup.center ↥L))
    (hL : LeviInnOnPW p C) : FieldIndexOnPW p C := by
  intro Y _ _ L P hCP hC hLn hrank h3 hrk a ha3 haN hout
  haveI := hLn
  exact fieldIndexW_of_outPNiceP hCP (hT Y L P hCP hC hrank) (hL Y L P hCP hC hLn hrank h3 hrk)
    ha3 haN hout

end Families

theorem leviInnAtW_of_levi_dataP {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} [L.Normal] (hPL : P ≤ L)
    (hZL : Odd (Nat.card (Subgroup.center ↥L)))
    {K : Type} [Group K] [Finite K] (ρ : K →* ↥L) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center K) (hρo : Odd (Nat.card ρ.ker)) (Q : Subgroup K)
    (hQ : Q = coverSub ρ P) {k : ℕ} {G : Fin k → Type} [∀ j, Group (G j)] [∀ j, Finite (G j)]
    (S H : ∀ j, Subgroup (G j)) (β : ↥Q →* ∀ j, G j)
    (h2 : IsPGroup 2 β.ker) (hS : Subgroup.pi Set.univ S ≤ β.range)
    (hc : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (hodd : Odd ((Subgroup.pi Set.univ S).relIndex β.range))
    (hW : ∀ j, S j = ⊥ ∨ ParabCensus.IsWBlock ↥(S j))
    (hH : ∀ (x : ↥Q) (j : Fin k), β x j ∈ H j)
    (hblock : ∀ j, S j ≠ ⊥ → BlockOKP p (H j) (S j))
    (hZ : ∀ (j : Fin k) (E : Subgroup (G j)), E ≤ S j → IsElemAbelian p E → Nat.card E = p ^ 2 →
      ∀ x : ↥Q, ρ (x : K) = 1 → β x ∈ E.map (MonoidHom.mulSingle G j) → x = 1)
    (hZW : ∀ j, ¬ CFSG.Open.IsQuasisimple ↥(S j) → ∀ x : ↥Q, ρ (x : K) = 1 →
      β x ∈ (S j).map (MonoidHom.mulSingle G j) → β x = 1)
    (hrk : Open.pRank p (wPre P) ≤ 1) : LeviInnAtPW p P := by
  intro l hl m hcomm
  have hlL : l ∈ L := hPL hl
  obtain ⟨x, hx⟩ := hρ ⟨l, hlL⟩
  have hxQ : x ∈ Q := by
    rw [hQ]
    show ρ x ∈ P.subgroupOf L
    rw [hx]
    exact hl
  set x₀ : ↥Q := ⟨x, hxQ⟩ with hx₀
  have hn := ParabCensus.le_normalizer_of_commutator_le hS hc
  have hgN : ∀ j, ∀ s ∈ S j, β x₀ j * s * (β x₀ j)⁻¹ ∈ S j := by
    intro j s hs
    have hsp : Pi.mulSingle j s ∈ Subgroup.pi Set.univ S :=
      (Subgroup.mulSingle_mem_pi j s).mpr fun _ => hs
    have h1 := (Subgroup.mem_normalizer_iff.mp (hn ⟨x₀, rfl⟩) _).mp hsp
    have h2 := (Subgroup.mem_pi _).mp h1 j (Set.mem_univ j)
    simpa [Pi.mul_apply, Pi.inv_apply] using h2
  refine ParabCensus.actsInnerlyW_of_levi_dataP hp2 hPL hZL ρ hρ hker hρo Q hQ S H β h2 hS hc
    hodd hW hblock hZ hZW (MulAut.conj x₀) (β x₀) (fun j => hH x₀ j) (fun y => ?_) hgN (a := l)
    (Subgroup.le_normalizer hl) (fun y => ?_) ⟨m, fun w hw => ?_⟩ hrk
  · rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  · have h1 : (MulAut.conjNormal l : MulAut ↥L) (ρ (y : K)) = ρ x * ρ (y : K) * (ρ x)⁻¹ := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      have := congrArg Subtype.val hx
      simp only at this
      rw [← this]
      rfl
    have h2' : ρ (((MulAut.conj x₀ y : ↥Q) : K)) = ρ x * ρ (y : K) * (ρ x)⁻¹ := by
      rw [MulAut.conj_apply]
      simp [hx₀, map_mul, map_inv]
    rw [h1, h2', mul_inv_cancel]
    exact Subgroup.one_mem _
  · exact (commutatorElement_eq_one_iff_mul_comm.1 (hcomm w hw))

end CFSG.LocalAnalysis.RankThreeTheoremC.FieldIndexW
