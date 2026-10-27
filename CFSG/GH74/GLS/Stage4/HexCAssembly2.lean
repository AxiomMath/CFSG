module

public import CFSG.GH74.GLS.Stage4.HexCAssembly
public import CFSG.GH74.GLS.Stage4.HexCD4Stmt
public import CFSG.GH74.GLS.Stage4.HexCStmt
public import CFSG.GH74.GLS.Stage4.RestOut

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Steinberg.TwistedD4 CFSG.Blueprint
  CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank
  CFSG.Timmesfeld.RankTwo CFSG.GH74.GLS.Stage4.Rest
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

@[expose] def Ch6OutPlusN2 (G : Type) [Group G] : Prop :=
  ∃ (p : ℕ) (H : Subgroup G) (r₁ r₂ : G) (U : Subgroup G) (root : ℤ → Subgroup G) (z : G)
    (S K₁ K₂ F P₀ : Subgroup G) (q : ℕ), Ch6PlusMatrix G p H r₁ r₂ U root z S K₁ K₂ F P₀ q ∧
      (5 ≤ q → RootOrdersG2 root q → NondegG2 root ∧ (p = 3 → NondegX15 root)) ∧
      (3 ≤ q → RootOrdersD4a root q → NondegG2 root ∧ NondegD4X13 root)

@[expose] def Ch6NondegLeaf2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ), IsTwoCentralG2TypeG2At G Gs q₁ q₂ →
      Ch6OutPlus G → Ch6OutPlusN2 G

@[expose] def Ch6LocalRGD2tN2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs], IsTwoCentralG2TypeG2 G Gs →
      ∃ (H : Subgroup G) (r₁ r₂ : G) (U : Subgroup G) (root : ℤ → Subgroup G)
        (R : RGD2 6 H r₁ r₂ U root), (H ⊔ U) ⊔ R.N = ⊤ ∧ ∃ p q : ℕ, p.Prime ∧ Odd q ∧
          PStruct p U root ∧ SL2At H R.N root 1 ∧ SL2At H R.N root 4 ∧ OrthPair root ∧
          SharedInv root ∧ LongA2 root ∧
          ((5 ≤ q ∧ RootOrdersG2 root q ∧ NondegG2 root ∧ (p = 3 → NondegX15 root)) ∨
            (3 ≤ q ∧ RootOrdersD4a root q ∧ NondegG2 root ∧ NondegD4X13 root))

theorem ch6LocalRGD2tN2_of_plusN2
    (h : ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
      ∀ (Gs : Type) [Group Gs], IsTwoCentralG2TypeG2 G Gs → Ch6OutPlusN2 G) :
    Ch6LocalRGD2tN2 := by
  intro G _ _ hStd hr Gs _ hG2
  have : IsSimpleGroup G := hStd.kps.1
  have hSE := no_stronglyEmbedded hStd hG2
  obtain ⟨p, H, r₁, r₂, U, root, z, S, K₁, K₂, F, P₀, q,
    ⟨D, E, hq, hcase, ⟨hK, hz1, hz2⟩, hE2, hA⟩, hN5, hN3⟩ := h G hStd hr Gs hG2
  refine ⟨H, r₁, r₂, U, root, D.toRGD2, Gen97.top D E hSE, p, q, D.prime, hq,
    ⟨Gen97.U_sylow D E hSE, ?_⟩, D.sl2At₁, D.sl2At₄, ?_, ⟨z, E.z_ord, ?_, ?_⟩, hA, ?_⟩
  · intro i h1 h6
    have hi : IsRoot 6 i := ⟨by omega, by omega⟩
    exact ⟨⟨⟨fun a b => Subtype.ext (D.root_comm i hi a.1 a.2 b.1 b.2)⟩⟩,
      fun x hx => D.root_exp i hi x hx⟩
  · intro a ha b hb
    rw [← E.K₁_eq] at ha
    rw [← E.K₂_eq] at hb
    exact hK a ha b hb
  · rw [← E.K₁_eq]; exact hz1
  · rw [← E.K₂_eq]; exact hz2
  · rcases hcase with ⟨h5, hD⟩ | ⟨h3, hD⟩
    · exact Or.inl ⟨h5, hD, hN5 h5 hD⟩
    · exact Or.inr ⟨h3, hD, hN3 h3 hD⟩

theorem s_ch6_Std_of_matchtN2
    (hA : Ch6LocalRGD2tN2) : S_ch6_Std := by
  intro G _ _ hStd hr hIn
  rcases hIn with hAsc | ⟨Gs, _, hT⟩
  · exact Or.inr (Or.inr (Or.inr hAsc))
  · have hG : IsTwoCentralG2TypeG2 G Gs := IsTwoCentralG2Type.g2 hStd.nonab hT
    obtain ⟨H, r₁, r₂, U, root, R, hgen, r, q, hr', hqodd, hP, hS1, hS4, hO, hZ, hL, hcase⟩ :=
      hA G hStd hr Gs hG
    have : IsSimpleGroup G := hStd.kps.1
    rcases hcase with ⟨h5, hD, hnd, hx⟩ | ⟨h3, hD, hnd, hnd13⟩
    · obtain ⟨F, _, _, hcard, ψ, hψ⟩ := hexCoordG2tN G H r₁ r₂ U root R hgen r q hr' hqodd h5 hD hP
        hS1 hS4 hO hZ hL hnd hx
      have hF : 3 ≤ Nat.card F := by omega
      obtain ⟨p, f, hp, hf, hpf, hL⟩ := lieModel_g2_of_match (R.toPre hgen).toSystemOfSimple
        (by omega) ⟨F, inferInstance, inferInstance, hF, hcard, Or.inl (uMatch_of_g2Coords hF hψ)⟩
      exact Or.inr (Or.inl ⟨p, f, hp, prime_ne_two_of_odd_pow hf hpf hqodd, hf, by omega, hL⟩)
    · obtain ⟨K, _, _, σ, hK, hσq, ψ, hψ⟩ := hexCoordD4tN G H r₁ r₂ U root R hgen r q h3 hr' hqodd
        hD hP hS1 hS4 hO hZ hL hnd hnd13
      obtain ⟨p, f, hp, hf, hpf, hL⟩ := lieModel_d4_of_match_or (R.toPre hgen).toSystemOfSimple
        (by omega) ⟨K, inferInstance, inferInstance, σ, hK, hσq,
          Or.inl (uMatch_of_d4Coords (by omega) hK hσq hψ)⟩
      exact Or.inr (Or.inr (Or.inl ⟨p, f, hp, prime_ne_two_of_odd_pow hf hpf hqodd, hf, hL⟩))

end CFSG.GH74.GLS.Stage4.Hex
