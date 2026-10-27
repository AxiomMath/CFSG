module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Wrapper
public import CFSG.HardMathSupport.Solomon.Coordinator.C25D44
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FIa

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns

structure Input25_4FactsNarrow : Prop where
  up34 : ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G), CFSG.IsKGroup ↥X →
    GLAPComponent 3 X K → ∀ b : G, b ∈ X → ∀ hbN : b ∈ Subgroup.normalizer (K : Set G),
    b ^ 3 = 1 → b ∉ dQ K → ∀ J : Subgroup G,
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set G)) J →
    IsLThreeFour (↥J ⧸ GLAPPrimeCore 3 ↥J) →
      (IsCatalogLieIso (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) IsL364Index ∧
        ¬ IsInnDiagThree (barAut 3 K ⟨b, hbN⟩)) ∨
      IsCatalogLieIso (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) Is3D44Index ∨
      (IsCatalogLieIso (barOf 3 K) IsD44Index ∧ Subgroup.center (barOf 3 K) = ⊥)
  heis : L364Rank3Heis
  gen3D4 : ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ →
    IsCatalogLieIso (Y ⧸ Subgroup.center Y) Is3D44Index →
    ∀ A : Subgroup (MulAut Y), IsElemAbelian 3 A →
      ⊤ ≤ ⨆ (S : Subgroup (MulAut Y)) (_ : S ≤ A ∧ Nat.card A ≤ 3 * Nat.card S), c25Fix S

theorem input25_4_of_narrow (F : Input25_4FactsNarrow) : Input25_4 := by
  intro G _ _ X K B hX hK hBel hBX hrank hC hBN hJ
  obtain ⟨b₁, hb₁, hb₁1⟩ := hC
  obtain ⟨b₀, hb₀B, hb₀1, J, hJ, hJ34⟩ := hJ
  have hb₀3 : b₀ ^ 3 = 1 := hBel.2 b₀ hb₀B
  by_cases hb₀d : b₀ ∈ dQ K
  ·
    left
    have hE : IsPGroup 3 ↥(Subgroup.zpowers b₀) := by
      intro g
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
      refine ⟨1, ?_⟩
      apply Subtype.ext
      show (g : G) ^ (3 ^ 1) = 1
      rw [← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb₀3,
        one_zpow]
    have hEd : Subgroup.zpowers b₀ ≤ dQ K := by
      rw [Subgroup.zpowers_le]
      exact hb₀d
    obtain ⟨J', hJ', -, huniq, -, -, ⟨e⟩⟩ := ia_cover coverStmt hK hE hEd
    have hcent : Subgroup.centralizer ((Subgroup.zpowers b₀ : Subgroup G) : Set G) =
        Subgroup.centralizer ({b₀} : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hcent] at hJ' huniq
    have hJJ : J = J' := huniq J hJ
    subst hJJ
    exact IsLThreeFour.of_mulEquiv e hJ34
  · right
    have hqs := isQuasisimple_quotient_of_glaPComponent Nat.prime_three hK
    have hcore0 : GLAPPrimeCore 3 (barOf 3 K) = ⊥ := glaPPrimeCore_quotient_eq_bot Nat.prime_three
    have hbN₀ : b₀ ∈ Subgroup.normalizer (K : Set G) := hBN hb₀B
    rcases F.up34 G X K hX hK b₀ (hBX hb₀B) hbN₀ hb₀3 hb₀d J hJ hJ34 with ⟨h, hdiag⟩ | h | ⟨hD4, hcen⟩
    · refine c25_transfer hBel hBN (fun X => X) (fun X => X) (fun X => le_rfl)
        (fun E _ => le_rfl) ?_
      have hα : ∃ α ∈ c25Img K B, α ≠ 1 ∧ ¬ IsInnDiagThree α := by
        refine ⟨barAut 3 K ⟨b₀, hbN₀⟩, ⟨⟨b₀, hbN₀⟩, ?_, rfl⟩, ?_, hdiag⟩
        · exact Subgroup.mem_subgroupOf.2 hb₀B
        · intro h1
          exact hb₀d ((LocalBalance.Lemma54Ns.mem_centralizerQuot_iff_barAut' 3 (J := K)
            ⟨b₀, hbN₀⟩).2 h1)
      exact genL364Narrow_of_rank3 (l364Rank3Gen_of_heis F.heis) _ hqs hcore0 h _
        (c25Img_isElemAbelian hBel) hα
    · exact c25_transfer hBel hBN (fun X => X) (fun X => X) (fun X => le_rfl)
        (fun E _ => le_rfl) (F.gen3D4 _ hqs hcore0 h _ (c25Img_isElemAbelian hBel))
    · exfalso
      obtain ⟨hb₁B, hb₁d⟩ := Subgroup.mem_inf.1 hb₁
      have h5 := c25_five_le_twoLocalRank hK.1 (hBX hb₁B) hb₁d (hBel.2 b₁ hb₁B) hb₁1 hcen
        (input25_4Facts_borel_holds _ hD4)
      omega


end CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3
