module

public import CFSG.Quasithin.H13.A5W1618f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W13616a

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Setting

variable {T L V : Subgroup G} (S : Setting G T L V)

theorem isChi0Block_of_minParabolic_F4 (h126 : TheoremC126)
    (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4)
    (h132fsu : Stmt13_3_2_three_fsu_F4) (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4)
    (h1327 : Stmt13_2_7_F4) (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) {K₀ M : Subgroup G}
    (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G)) (hK₀ : K₀ ∈ lFamily S.Tv)
    (hTK : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G))
    (hmp : MinParabolic (K₀ ⊔ S.Tv) S.Tv M) :
    IsChi0Block (K₀ ⊔ S.Tv) K₀ ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type K₀ n) ∨ IsAltType K₀ 5) := by
  have hsylTv := S.isSylowTwoOf_Tv_F4 h1222 h517
  have hHG : K₀ ⊔ S.Tv ≤ Subgroup.centralizer ({S.v12} : Set G) := sup_le hK₀G S.Tv_le_Gv
  have hHchar : CharTwo (K₀ ⊔ S.Tv) := C1GN.charTwo_of_le hF hsylTv le_sup_right hHG
  have hvT : S.v12 ∈ S.Tv :=
    ⟨S.V_le_T S.v12_mem_V, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

  have hvO : S.v12 ∈ pCoreOf 2 (K₀ ⊔ S.Tv) := by
    have hle : Subgroup.zpowers S.v12 ≤ K₀ ⊔ S.Tv :=
      (Subgroup.zpowers_le.mpr hvT).trans le_sup_right
    have hN : K₀ ⊔ S.Tv ≤ Subgroup.normalizer (Subgroup.zpowers S.v12 : Set G) := by
      intro g hg
      have hgG : g ∈ Subgroup.centralizer ({S.v12} : Set G) := hHG hg
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp hgG).symm k).eq)
    have h2 : IsPGroup 2 (Subgroup.zpowers S.v12) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (S.elemAbelian_V.2 _ S.v12_mem_V) S.v12_ne_one
    exact le_pCoreOf_of_normalizes hle hN h2 (Subgroup.mem_zpowers _)
  have hO : pCoreOf 2 (K₀ ⊔ S.Tv) ≠ ⊥ := fun h =>
    S.v12_ne_one (by rw [h, Subgroup.mem_bot] at hvO; exact hvO)
  have hSQ : IsSQTKTC (K₀ ⊔ S.Tv) :=
    isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian (T := S.Tv) ⟨le_sup_right, hO⟩

  obtain ⟨C₁, C₂, hC⟩ := exists_isGNChoice (G := G) theoremC118
  have hTv2 : IsPGroup 2 S.Tv := S.isPGroup_T.to_le inf_le_left
  have hTvne : S.Tv ≠ ⊥ := fun h =>
    S.v12_ne_one (by rw [h, Subgroup.mem_bot] at hvT; exact hvT)
  obtain ⟨h1ne, h1Z, h1char, h2ne, h2B, h2char, -⟩ := hC.pair S.Tv hTv2 hTvne
  obtain ⟨hmin, hTsyl, -⟩ := minParabolic_iff.mp hmp
  have hnot := fun {C : Subgroup G} (hCT : C ≤ S.Tv) (hC : C ≠ ⊥)
    (hch : (C.subgroupOf S.Tv).Characteristic) =>
    S.not_le_normalizer_of_characteristic_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h37 h39
      hK₀G hK₀ hTK hz hCT hC hch
  rcases h126 G C₁ C₂ hC (K₀ ⊔ S.Tv) S.Tv hSQ hTsyl hHchar hmin with
    h1 | h2 | ⟨r, B, hr, hB, -, hres, -, -⟩
  ·
    exfalso
    have hC1T : C₁ S.Tv ≤ S.Tv := h1Z.trans
      ((Subgroup.closure_le _).mpr fun x hx => hx.1.1)
    refine hnot hC1T h1ne h1char fun k hk => Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (Subgroup.mem_centralizer_iff.mp (h1 hc).2 k (Subgroup.mem_sup_left hk)).symm
  ·
    exfalso
    have hBT := C1GN.baum_le S.Tv
    have hch2 : ((C₂ S.Tv).subgroupOf S.Tv).Characteristic :=
      C1GN.characteristic_subgroupOf_trans hBT h2B (C1GN.characteristic_baum _) h2char
    exact hnot (h2B.trans hBT) h2ne hch2 (le_sup_left.trans h2)
  ·
    have hK₀p : ⁅K₀, K₀⁆ = K₀ := perfect_of_mem_cComp hK₀
    have hres_le : twoResidual (K₀ ⊔ S.Tv) ≤ K₀ :=
      twoResidual_le_of_isTwoQuotient le_sup_left (sup_le Subgroup.le_normalizer hTK)
        fun y hy => C1.exists_pow_mem_of_mem_sup hTv2 hTK hy
    have hres_eq : twoResidual (K₀ ⊔ S.Tv) = K₀ :=
      le_antisymm hres_le (le_twoResidual_of_perfect hK₀p le_sup_left)
    have hns : ¬ Group.IsSolvable ↥K₀ := not_isSolvable_of_mem_cComp hK₀
    have hsolvK : ∀ {X : Subgroup G}, X ≤ K₀ → X ≠ K₀ → IsSubnormal X K₀ →
        Group.IsSolvable ↥X := fun {X} hXK hne hsub => by
      have hle := le_solvRad_of_subnormal_lt hK₀ hsub (lt_of_le_of_ne hXK hne)
      have := solvRad_isSolvable K₀
      exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    obtain ⟨i, hi⟩ : ∃ i, ¬ Group.IsSolvable ↥(B i) := by
      by_contra hall
      push Not at hall
      have hle : (⨆ i, B i) ≤ solvRad (K₀ ⊔ S.Tv) :=
        iSup_le fun i => le_solvRad_of_subnormal (IsBlock2.isSubnormal (hB i).1.1) (hall i)
      rw [← hres, hres_eq] at hle
      have := solvRad_isSolvable (K₀ ⊔ S.Tv)
      exact hns (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle))
    have hBK : B i ≤ K₀ := by
      rw [← hres_eq, hres]
      exact le_iSup B i
    have hBsub : IsSubnormal (B i) K₀ :=
      A3.subnormal_of_le_of_le (IsBlock2.isSubnormal (hB i).1.1) hBK le_sup_left
    have hBeq : B i = K₀ := by
      by_contra hne
      exact hi (hsolvK hBK hne hBsub)
    obtain ⟨hblk, htype⟩ := (hB i).1
    rw [hBeq] at hblk htype
    refine ⟨⟨hblk, htype⟩, ?_⟩
    rcases htype with hlin | h3 | h5
    · exact Or.inl hlin
    · exact (hns (isSolvable_of_isAltType_three h3)).elim
    · exact Or.inr h5

end Setting

end CFSG.Quasithin.H13.A5
