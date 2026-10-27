module

public import CFSG.GH74.GLS.C3.Prop121.CentK
public import CFSG.GH74.GLS.C3.Prop121.L122Fin
public meta import CFSG.GH74.GLS.C3.Prop121.L122Fin
public meta import CFSG.GH74.GLS.C3.Prop121.MooreFinite7
public import Mathlib.GroupTheory.Perm.Cycle.Type
public meta import Mathlib.Algebra.Group.End
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.GroupTheory.Perm.Support
public meta import Mathlib.GroupTheory.Perm.Cycle.Basic
public meta import Mathlib.GroupTheory.Perm.Cycle.Type
public meta import Mathlib.Logic.Equiv.Fin.Basic
public meta import Mathlib.Logic.Equiv.Option
public meta import Mathlib.Data.List.FinRange
public import CFSG.GH74.GLS.C3.Prop121.CentK7Inputs
public meta import CFSG.GH74.GLS.C3.Prop121.CentK7Inputs
public import Certificates.Certificate5084
public import Certificates.Certificate5088
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.C3.Layer2.Final
public import CFSG.GH74.GLS.C3.Layer3.Main
public import CFSG.GH74.GLS.C3.Prop121.Recog
public import CFSG.GH74.GLS.Defs
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2.Model

theorem mem_even7 {s : Perm (Fin 7)} : s ∈ even7 ↔ sign s = 1 := by
  simp [even7, mem_allPerms]

theorem mem_centE7 {τ b : Perm (Fin 7)} :
    b ∈ centE7 τ ↔ sign b = 1 ∧ b * τ = τ * b ∧ b ≠ 1 ∧ b ≠ τ ∧ b ≠ τ⁻¹ := by
  simp [centE7, mem_even7]

theorem okSearch7_true : okSearch7 = true :=
  Certificates.certificate5084

theorem finite_cent_seven_rep
    {a1 a2 τ b : Perm (Fin 7)} (hrep : τ = tauA7 ∨ τ = tauB7)
    (ha1 : a1 * a1 = 1 ∧ a1 ≠ 1 ∧ sign a1 = 1) (ha2 : a2 * a2 = 1 ∧ a2 ≠ 1 ∧ sign a2 = 1)
    (ha12 : a1 * a2 = a2 * a1 ∧ a1 ≠ a2)
    (hτa : τ * a1 * τ⁻¹ = a2 ∨ τ * a1 * τ⁻¹ = a1 * a2)
    (hτb : τ * a2 * τ⁻¹ = a1 ∨ τ * a2 * τ⁻¹ = a2 ∨ τ * a2 * τ⁻¹ = a1 * a2)
    (hb : sign b = 1) (hbτ : b * τ = τ * b) (hb1 : b ≠ 1) (hbτ1 : b ≠ τ) (hbτ2 : b ≠ τ⁻¹) :
    goodW7 a1 a2 (b * a2 * b⁻¹ * a1 * a2 * b) = true ∨
      goodW7 a1 a2 (b * τ * a2 * (b * τ)⁻¹ * a1 * a2 * (b * τ)) = true ∨
      goodW7 a1 a2 (b * τ⁻¹ * a2 * (b * τ⁻¹)⁻¹ * a1 * a2 * (b * τ⁻¹)) = true := by
  have h1 : okTau7 τ = true := by
    have h := okSearch7_true
    simp only [okSearch7, Bool.and_eq_true] at h
    rcases hrep with rfl | rfl
    · exact h.1
    · exact h.2
  have hC0 : (a1 * a2 = a2 * a1 ∧ a1 ≠ a2) = True := eq_true ha12
  have h2 : okPair7 (centE7 τ) τ a1 a2 = true := by
    have h := List.all_eq_true.1 (List.all_eq_true.1 h1 a1 (mem_inv7.2 ha1)) a2 (mem_inv7.2 ha2)
    simp only [hC0, ite_true] at h
    exact h
  have hC1 : ((τ * a1 * τ⁻¹ = a2 ∨ τ * a1 * τ⁻¹ = a1 * a2) ∧
      (τ * a2 * τ⁻¹ = a1 ∨ τ * a2 * τ⁻¹ = a2 ∨ τ * a2 * τ⁻¹ = a1 * a2)) = True :=
    eq_true ⟨hτa, hτb⟩
  have h3 : (centE7 τ).all (okBeta7 a1 a2 τ) = true := by
    have h := h2
    simp only [okPair7, hC1, ite_true] at h
    exact h
  have h4 : okBeta7 a1 a2 τ b = true :=
    List.all_eq_true.1 h3 b (mem_centE7.2 ⟨hb, hbτ, hb1, hbτ1, hbτ2⟩)
  simpa only [okBeta7, wordW7, Bool.or_eq_true, or_assoc] using h4

theorem exists_conj_rep {τ : Perm (Fin 7)} (hτ : τ * τ * τ = 1 ∧ τ ≠ 1) :
    ∃ σ : Perm (Fin 7), σ * τ * σ⁻¹ = tauA7 ∨ σ * τ * σ⁻¹ = tauB7 := by
  have hpow : τ ^ 3 = 1 := by rw [pow_three']; exact hτ.1
  have hord : orderOf τ = 3 := orderOf_eq_prime hpow hτ.2
  obtain ⟨n, hn⟩ := cycleType_prime_order (σ := τ) (by rw [hord]; exact Nat.prime_three)
  rw [hord] at hn
  have hsum := sum_cycleType_le τ
  rw [hn, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hsum
  have h1 : tauA7.cycleType = {3} :=
    isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  have h1' : (swap (3 : Fin 7) 4 * swap 3 5).cycleType = {3} :=
    isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  have hd : Equiv.Perm.Disjoint tauA7 (swap (3 : Fin 7) 4 * swap 3 5) := by
    rw [Equiv.Perm.disjoint_iff_eq_or_eq]
    decide
  have h2 : tauB7.cycleType = {3, 3} := by
    rw [tauB7, hd.cycleType_mul, h1, h1']
    rfl
  have hn01 : n = 0 ∨ n = 1 := by omega
  rcases hn01 with rfl | rfl
  · obtain ⟨σ, hσ⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 (hn.trans h1.symm))
    exact ⟨σ, Or.inl hσ⟩
  · obtain ⟨σ, hσ⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 (hn.trans h2.symm))
    exact ⟨σ, Or.inr hσ⟩

theorem sign_conj7 (σ x : Perm (Fin 7)) : sign (σ * x * σ⁻¹) = sign x := by
  rw [map_mul, map_mul, sign_inv, mul_comm (sign σ) (sign x), mul_assoc, Int.units_mul_self,
    mul_one]

theorem goodW7_conj (c : Perm (Fin 7) ≃* Perm (Fin 7)) (a1 a2 w : Perm (Fin 7)) :
    goodW7 (c a1) (c a2) (c w) = goodW7 a1 a2 w := by
  have e : (c w * c a1 = c a1 * c w ∧ c w ≠ 1 ∧ c w ≠ c a1 ∧ c w ≠ c a2 ∧ c w ≠ c a1 * c a2) ↔
      (w * a1 = a1 * w ∧ w ≠ 1 ∧ w ≠ a1 ∧ w ≠ a2 ∧ w ≠ a1 * a2) := by
    simp only [ne_eq, ← map_mul c, EmbeddingLike.apply_eq_iff_eq, map_eq_one_iff c c.injective]
  unfold goodW7
  exact decide_eq_decide.2 e

theorem finite_cent_seven {a1 a2 τ b : Perm (Fin 7)}
    (ha1 : a1 * a1 = 1 ∧ a1 ≠ 1 ∧ sign a1 = 1) (ha2 : a2 * a2 = 1 ∧ a2 ≠ 1 ∧ sign a2 = 1)
    (ha12 : a1 * a2 = a2 * a1 ∧ a1 ≠ a2) (hτ : τ * τ * τ = 1 ∧ τ ≠ 1)
    (hτa : τ * a1 * τ⁻¹ = a2 ∨ τ * a1 * τ⁻¹ = a1 * a2)
    (hτb : τ * a2 * τ⁻¹ = a1 ∨ τ * a2 * τ⁻¹ = a2 ∨ τ * a2 * τ⁻¹ = a1 * a2)
    (hb : sign b = 1) (hbτ : b * τ = τ * b) (hb1 : b ≠ 1) (hbτ1 : b ≠ τ) (hbτ2 : b ≠ τ⁻¹) :
    goodW7 a1 a2 (b * a2 * b⁻¹ * a1 * a2 * b) = true ∨
      goodW7 a1 a2 (b * τ * a2 * (b * τ)⁻¹ * a1 * a2 * (b * τ)) = true ∨
      goodW7 a1 a2 (b * τ⁻¹ * a2 * (b * τ⁻¹)⁻¹ * a1 * a2 * (b * τ⁻¹)) = true := by
  obtain ⟨σ, hσ⟩ := exists_conj_rep hτ
  let c : Perm (Fin 7) ≃* Perm (Fin 7) := MulAut.conj σ
  have hcone : ∀ x : Perm (Fin 7), c x = 1 ↔ x = 1 := fun x => map_eq_one_iff c c.injective
  have hsign : ∀ x : Perm (Fin 7), sign (c x) = sign x := fun x => sign_conj7 σ x
  have key := finite_cent_seven_rep (a1 := c a1) (a2 := c a2) (τ := c τ) (b := c b) hσ
    ⟨by rw [← map_mul, ha1.1, map_one], fun h => ha1.2.1 ((hcone _).1 h),
      by rw [hsign]; exact ha1.2.2⟩
    ⟨by rw [← map_mul, ha2.1, map_one], fun h => ha2.2.1 ((hcone _).1 h),
      by rw [hsign]; exact ha2.2.2⟩
    ⟨by rw [← map_mul, ← map_mul, ha12.1], fun h => ha12.2 (c.injective h)⟩
    (by
      rcases hτa with h | h
      · left; simpa only [map_mul, map_inv] using congrArg c h
      · right; simpa only [map_mul, map_inv] using congrArg c h)
    (by
      rcases hτb with h | h | h
      · left; simpa only [map_mul, map_inv] using congrArg c h
      · right; left; simpa only [map_mul, map_inv] using congrArg c h
      · right; right; simpa only [map_mul, map_inv] using congrArg c h)
    (by rw [hsign]; exact hb)
    (by rw [← map_mul, ← map_mul, hbτ])
    (fun h => hb1 ((hcone _).1 h))
    (fun h => hbτ1 (c.injective h))
    (fun h => hbτ2 (c.injective (h.trans (map_inv c τ).symm)))
  rcases key with h | h | h
  · left
    rw [← goodW7_conj c a1 a2]
    simpa only [map_mul, map_inv] using h
  · right; left
    rw [← goodW7_conj c a1 a2]
    simpa only [map_mul, map_inv] using h
  · right; right
    rw [← goodW7_conj c a1 a2]
    simpa only [map_mul, map_inv] using h

section Config

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

theorem centralizer_K_inf_centralizer_t_seven
    (hC : pRank 2 G ≤ 4) (h : IsAConfig 7 x K T Q S a)
    {t u g : G} (hS : Stage3Loc 7 x K Q t u g) :
    ∀ r : G, (∀ k ∈ K, r * k = k * r) → r * t = t * r → r ∈ zpowers t := by
  classical
  have hn' : (7 : ℕ) = 5 ∨ (7 : ℕ) = 6 ∨ (7 : ℕ) = 7 := Or.inr (Or.inr rfl)
  have hG4 : pRank 2 G ≤ 4 := hC
  have hF := fnFacts 7 hn'
  obtain ⟨eK⟩ := hS.K_alt
  have hD := conj_mem_K_of_centralizer_K hn' hG4 h hF hS
  obtain ⟨φ, hφinj, hφsign⟩ := exists_psi eK hD
  intro r hr hrt
  have hrD : r ∈ centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.2 (fun k hk => (hr k hk).symm)
  have htD : t ∈ centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.2 (fun k hk => (hS.t_comm_K k hk).symm)
  obtain ⟨y₀, hy₀Q, hy₀1, hy₀x, hQall, hy2, hx2, hxy, ht3', ht1, hp, hs, htxx⟩ := Q_facts hS
  let R : ↥(centralizer (K : Set G)) := ⟨r, hrD⟩
  let T' : ↥(centralizer (K : Set G)) := ⟨t, htD⟩
  have hT3 : T' * T' * T' = 1 := Subtype.ext ht3'
  have hT1 : T' ≠ 1 := fun h1 => ht1 (congrArg Subtype.val h1)
  have hRT : R * T' = T' * R := Subtype.ext hrt
  have hφτ : φ T' * φ T' * φ T' = 1 ∧ φ T' ≠ 1 :=
    ⟨by rw [← map_mul, ← map_mul, hT3, map_one],
      fun h1 => hT1 (hφinj (h1.trans (map_one φ).symm))⟩
  have hφbτ : φ R * φ T' = φ T' * φ R := by rw [← map_mul, ← map_mul, hRT]
  by_contra hnot
  have hr1 : r ≠ 1 := fun h1 => hnot (by rw [h1]; exact one_mem _)
  have hrt1 : r ≠ t := fun h1 => hnot (by rw [h1]; exact mem_zpowers t)
  have hrt2 : r ≠ t⁻¹ := fun h1 => hnot (by rw [h1]; exact inv_mem (mem_zpowers t))
  have hxD : x ∈ centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.2 (fun k hk => hS.K_comm_Q k hk x hS.x_mem)
  have hyD : y₀ ∈ centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.2 (fun k hk => hS.K_comm_Q k hk y₀ hy₀Q)
  let X : ↥(centralizer (K : Set G)) := ⟨x, hxD⟩
  let Y : ↥(centralizer (K : Set G)) := ⟨y₀, hyD⟩
  have hXX : X * X = 1 := Subtype.ext hx2
  have hYY : Y * Y = 1 := Subtype.ext hy2
  have hXY : X * Y = Y * X := Subtype.ext hxy
  have hX1 : X ≠ 1 := fun h1 => hS.x_ne (congrArg Subtype.val h1)
  have hY1 : Y ≠ 1 := fun h1 => hy₀1 (congrArg Subtype.val h1)
  have hXYne : X ≠ Y := fun h1 => hy₀x (congrArg Subtype.val h1).symm
  have hφX : φ X * φ X = 1 ∧ φ X ≠ 1 ∧ sign (φ X) = 1 :=
    ⟨by rw [← map_mul, hXX, map_one],
      fun h1 => hX1 (hφinj (h1.trans (map_one φ).symm)), hφsign X⟩
  have hφY : φ Y * φ Y = 1 ∧ φ Y ≠ 1 ∧ sign (φ Y) = 1 :=
    ⟨by rw [← map_mul, hYY, map_one],
      fun h1 => hY1 (hφinj (h1.trans (map_one φ).symm)), hφsign Y⟩
  have hφXY : φ X * φ Y = φ Y * φ X ∧ φ X ≠ φ Y :=
    ⟨by rw [← map_mul, ← map_mul, hXY], fun h1 => hXYne (hφinj h1)⟩
  have hφa : φ T' * φ X * (φ T')⁻¹ = φ Y ∨ φ T' * φ X * (φ T')⁻¹ = φ X * φ Y := by
    have e : φ T' * φ X * (φ T')⁻¹ = φ (T' * X * T'⁻¹) := by rw [map_mul, map_mul, map_inv]
    rcases hp with h1 | h1
    · left; rw [e]; congr 1; exact Subtype.ext h1
    · right; rw [e, ← map_mul]; congr 1; exact Subtype.ext h1
  have hφb : φ T' * φ Y * (φ T')⁻¹ = φ X ∨ φ T' * φ Y * (φ T')⁻¹ = φ Y ∨
      φ T' * φ Y * (φ T')⁻¹ = φ X * φ Y := by
    have e : φ T' * φ Y * (φ T')⁻¹ = φ (T' * Y * T'⁻¹) := by rw [map_mul, map_mul, map_inv]
    rcases hs with h1 | h1 | h1
    · left; rw [e]; congr 1; exact Subtype.ext h1
    · right; left; rw [e]; congr 1; exact Subtype.ext h1
    · right; right; rw [e, ← map_mul]; congr 1; exact Subtype.ext h1
  have hRne : φ R ≠ 1 ∧ φ R ≠ φ T' ∧ φ R ≠ (φ T')⁻¹ :=
    ⟨fun h1 => hr1 (congrArg Subtype.val (hφinj (h1.trans (map_one φ).symm))),
      fun h1 => hrt1 (congrArg Subtype.val (hφinj h1)),
      fun h1 => hrt2 (congrArg Subtype.val (hφinj (h1.trans (map_inv φ T').symm)))⟩
  have key : ∀ C : ↥(centralizer (K : Set G)),
      goodW7 (φ X) (φ Y) (φ C) = true → False := by
    intro C hC'
    have hg := of_decide_eq_true hC'
    obtain ⟨hgc, hg1, hg2, hg3, hg4⟩ := hg
    have h1 : C * X = X * C := hφinj (by rw [map_mul, map_mul]; exact hgc)
    have hCx : (C : G) * x = x * (C : G) := congrArg Subtype.val h1
    have hCQ : (C : G) ∈ Q :=
      centralizer_K_inf_x hn' hG4 h (C : G) hCx
        (fun k hk => (Subgroup.mem_centralizer_iff.1 C.2 k hk).symm)
    rcases hQall (C : G) hCQ with h2 | h2 | h2 | h2
    · exact hg1 (by rw [show C = 1 from Subtype.ext h2, map_one])
    · exact hg2 (by rw [show C = X from Subtype.ext h2])
    · exact hg3 (by rw [show C = Y from Subtype.ext h2])
    · exact hg4 (by rw [show C = X * Y from Subtype.ext h2, map_mul])
  rcases finite_cent_seven hφX hφY hφXY hφτ hφa hφb (hφsign R) hφbτ hRne.1 hRne.2.1 hRne.2.2 with
    h1 | h1 | h1
  · apply key (R * Y * R⁻¹ * X * Y * R)
    simpa only [map_mul, map_inv] using h1
  · apply key (R * T' * Y * (R * T')⁻¹ * X * Y * (R * T'))
    simpa only [map_mul, map_inv] using h1
  · apply key (R * T'⁻¹ * Y * (R * T'⁻¹)⁻¹ * X * Y * (R * T'⁻¹))
    simpa only [map_mul, map_inv] using h1

end Config

end CFSG.GH74.GLS.C3.Prop121
