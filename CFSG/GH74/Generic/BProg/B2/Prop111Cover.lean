module

public import CFSG.GH74.Generic.BProg.B2.T1Basic
public import CFSG.GH74.Generic.BProg.B2.T1Sylow

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

namespace Prop111Cover

open C3.Layer1 C3.Layer1.PumpCalc C3.Layer1.PumpRigid C3.Layer1.Iv251

variable {G : Type} [Group G] [Finite G] {x : G} {K A M P Q : Subgroup G}

theorem pPrimeCoreOf_le_of_pCompIn {C J : Subgroup G} (hJ : IsPCompIn 2 C J) :
    pPrimeCoreOf 2 J ≤ pPrimeCoreOf 2 C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJC, K', -, hsub, -⟩ := hJ
  have h1 := CFSG.GH74.GLS.pPrimeCoreOf_le_of_subnormal (X := ↥C) 2 hsub
  rw [TwoThin.pPrimeCoreOf_eq_map_subgroupOf hJC]
  exact Subgroup.map_mono h1

theorem pumpup_cover_data (hs : Stage2Setup G x K A M P Q) {y : G} (hyQ : y ∈ Q) (hy : orderOf y = 2) :
    ∃ Hy Λ : Subgroup G, IsPCompIn 2 (centralizer ({y} : Set G)) Hy ∧ IsLam x y K Λ ∧ Λ ≤ K ⊓ Hy ∧
      (∀ k ∈ Hy, ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 Hy, k = l * o) ∧
      pPrimeCoreOf 2 Hy ≤ pPrimeCoreOf 2 (centralizer ({y} : Set G)) ∧
      Nonempty ((↥Hy ⧸ pPrimeCore 2 ↥Hy) ≃* (↥K ⧸ pPrimeCore 2 ↥K)) := by
  classical
  have hILo : IsILo 2 x K := hs.pair.1.1.1
  have hterm : IsTwoTerminal x K := hs.pair.1.2.2
  have hR3 : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)) := by
    have h3 : 3 ≤ pRank 2 G := by
      rw [pRank_two_eq_twoRank]
      exact hs.hyp.rank
    exact fun y hy => TwoThin.rankThreeCentralizers G hs.hyp.simple hs.hyp.nonab h3 y hy
  obtain ⟨Hy, hlt⟩ := PumpRigid.exists_pumpUpLT hILo hy (hs.sylowQ.le hyQ) (hR3 y hy)
  obtain ⟨hxHy, he⟩ := hterm.2.1 y Hy hlt
  obtain ⟨e⟩ := he
  have hle : TwoThin.hatCard Hy ≤ TwoThin.hatCard K := (Nat.card_congr e.toEquiv).le
  obtain ⟨Λ, hΛ, hΛHy, hcov⟩ := T1Sylow.exists_cover hlt hxHy hle
  have hHyc : IsPCompIn 2 (centralizer ({y} : Set G)) Hy := hlt.2.1.2.2
  exact ⟨Hy, Λ, hHyc, hΛ, le_inf (hΛ.le.trans inf_le_left) hΛHy, hcov,
    pPrimeCoreOf_le_of_pCompIn hHyc, ⟨e⟩⟩

theorem mem_centralizer_x_of_mem_Q (hs : Stage2Setup G x K A M P Q) {y : G} (hyQ : y ∈ Q) :
    y ∈ centralizer ({x} : Set G) :=
  (Subgroup.mem_inf.1 (hs.sylowQ.le hyQ)).1

theorem A_le_centralizer (hs : Stage2Setup G x K A M P Q) {y : G} (hyQ : y ∈ Q) :
    A ≤ centralizer ({y} : Set G) := by
  have hKA : ∀ a ∈ A ⊓ K, a ∈ centralizer ({y} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.2 (commute_Q_inf hs y hyQ a ha).symm
  have hxy : x ∈ centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_singleton_iff.1 (mem_centralizer_x_of_mem_Q hs hyQ)).symm
  obtain ⟨-, -, -, hcase⟩ := hs.src
  rcases hcase with ⟨hAK, -⟩ | ⟨E, hEK, hAE, -, -, -, -⟩
  · exact fun a ha => hKA a ⟨ha, hAK ha⟩
  · rw [hAE]
    refine sup_le (fun e he => hKA e ⟨?_, hEK he⟩) (Subgroup.zpowers_le.2 hxy)
    rw [hAE]
    exact Subgroup.mem_sup_left he

theorem inf_K_le_pumpup (hs : Stage2Setup G x K A M P Q) {y : G} (hyQ : y ∈ Q) {Hy Λ : Subgroup G}
    (hΛ : IsLam x y K Λ) (hΛHy : Λ ≤ Hy) : A ⊓ K ≤ Hy := by
  intro e he
  obtain ⟨n, hn⟩ := hs.sylowP.isPGroup (⟨e, hs.A_le he.1⟩ : ↥P)
  have hn' : e ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have heC : e ∈ centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (commute_Q_inf hs y hyQ e he).symm
  exact hΛHy (hΛ.twoElt e ⟨he.2, heC⟩ ⟨n, hn'⟩)

theorem comm_pumpup_x (hs : Stage2Setup G x K A M P Q) {y : G} (hyQ : y ∈ Q) {Hy Λ : Subgroup G}
    (hΛ : IsLam x y K Λ) (hcov : ∀ k ∈ Hy, ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 Hy, k = l * o)
    (hOle : pPrimeCoreOf 2 Hy ≤ pPrimeCoreOf 2 (centralizer ({y} : Set G))) :
    ∀ h ∈ Hy, ⁅h, x⁆ ∈ pPrimeCoreOf 2 (centralizer ({y} : Set G)) := by
  intro h hh
  obtain ⟨l, hl, o, ho, rfl⟩ := hcov h hh
  have hxC : x ∈ centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_singleton_iff.1 (mem_centralizer_x_of_mem_Q hs hyQ)).symm
  have hlK : l ∈ K := (hΛ.le hl).1
  have hlC : l ∈ centralizer ({y} : Set G) := (hΛ.le hl).2
  have hlx : l * x = x * l :=
    Subgroup.mem_centralizer_singleton_iff.1 (hs.pair.1.1.1.2.2.1 hlK)
  have hlx' : l⁻¹ * x⁻¹ = x⁻¹ * l⁻¹ := by
    have := congrArg (fun g => g⁻¹) hlx
    simpa [mul_inv_rev] using this.symm
  have ho' : o ∈ pPrimeCoreOf 2 (centralizer ({y} : Set G)) := hOle ho
  have e : ⁅l * o, x⁆ = l * (o * (x * o⁻¹ * x⁻¹)) * l⁻¹ := by
    calc ⁅l * o, x⁆ = l * o * x * o⁻¹ * (l⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
      _ = l * o * x * o⁻¹ * (x⁻¹ * l⁻¹) := by rw [hlx']
      _ = l * (o * (x * o⁻¹ * x⁻¹)) * l⁻¹ := by group
  rw [e]
  refine TwoThin.pPrimeCoreOf_normalized _ hlC (mul_mem ho' ?_)
  exact TwoThin.pPrimeCoreOf_normalized _ hxC (inv_mem ho')

end Prop111Cover

variable {G : Type} [Group G] [Finite G] {x : G} {K A M P Q : Subgroup G}

end CFSG.GH74.Generic.BProg.B2
