module

public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114Max
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Thm5114
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Stmt5_1_14_notf_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → ¬ quasithinIsFaithfulLocal T (oTwoUpper H)

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem isMaximalLocal_of_L34_F4
    (h510 : Stmt5_1_10_F4) (h5112 : Stmt5_1_12_F4)
    {T M L H B D : Subgroup G} {n : ℕ} (hyp : Hyp5_1_8 G T M L H n)
    (hN : IsNotation5_1_9 T M L H B D) (hK : LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2) :
    quasithinIsMaximalLocal T (oTwoUpper H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hH := hyp.hStar
  obtain ⟨k, hk⟩ := h510.exists_fieldParam_F4 hyp hN
  obtain ⟨-, K₁, hK₁, hKeq, -⟩ := id hk
  set K := oTwoUpper H with hKdef
  have hperf : ⁅K, K⁆ = K := by
    rw [hKeq]
    exact perfect_conjClosure hK₁.2.1
  have hs : IsSimpleGroup (O2Q K) := CFSG.Timmesfeld.isSimpleGroup_of_lieModel hK
  have hKH : K ≤ H := oTwoUpper_le H
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr (le_normalizer_oTwoUpper H)
  have hKC : quasithinIsCComponent K H := mem_cComp_of_normal_of_simple hKH hKn hperf hs
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hH.1.1.trans (le_normalizer_oTwoUpper H)
  have hKK : K = conjClosure K T := by
    apply le_antisymm (le_conjClosure K T)
    exact conjClosure_le fun t ht z hz => (Subgroup.mem_normalizer_iff.mp (hTK ht) z).mp hz
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hH.1.1
  have hHeq : H = K ⊔ T := eq_oTwoUpper_sup_of_isSylowTwoOf' hTH
  have hloc : quasithinIsLocal T K := by
    refine ⟨h.sylow.1, ?_, ?_, ?_⟩
    · rw [← hHeq]
      exact hKC
    · rw [← hHeq]
      exact hTH.2.2
    · rw [← hHeq]
      exact hH.1.2
  refine ⟨hloc, fun K' hK' hKK' => ?_⟩
  have hHX : InH H (K' ⊔ T) := ⟨hHeq.le.trans (sup_le_sup_right hKK' T), hK'.2.2.2⟩
  obtain ⟨Kh₁, hhat, -, hcases⟩ :=
    h5112 G T M L H B D K n k hyp hN hk hKC hKK (K' ⊔ T) hHX
  have hK'eq : K' = Kh₁ := hhat.2.2 K' hK'.2.1 hKK'
  rcases hcases with h1 | ⟨hlt, -⟩ | ⟨hsz, -⟩ | ⟨hl2, -⟩ | ⟨hl4, -⟩
  · apply le_antisymm _ hKK'
    rw [hK'eq, hKdef, h1]
    exact le_conjClosure Kh₁ T
  · exact absurd hlt (lt_irrefl K)
  · exact (not_suzukiModel_of_PSL34 hK hsz).elim
  · exact (not_lieModel_PSL2_of_PSL34 hK hl2).elim
  · exact (not_lieModel_PSL2_of_PSL34 hK hl4).elim

theorem stmt5_1_14_one_of_F4
    (h510 : Stmt5_1_10_F4) (h5112 : Stmt5_1_12_F4) (hnf : Stmt5_1_14_notf_F4) :
    Stmt5_1_14_one_F4 := fun G _ _ T M L V H B D n hyp hN hV hK =>
  ⟨isMaximalLocal_of_L34_F4 h510 h5112 hyp hN hK, hnf G T M L V H B D n hyp hN hV hK⟩

end CFSG.Quasithin.H13
