module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.C134L32Corr
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W13616a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.EmptyFaithful.SBc11List
public import CFSG.Quasithin.H13.A5W1622p

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped Pointwise

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem isMSPair_of_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) {K₀ : Subgroup G}
    (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G)) (hK₀ : K₀ ∈ lFamily S.Tv)
    (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) (hchar : CharTwo (K₀ ⊔ S.Tv))
    (hRk : IsRankTwoLie2Derived
      ((↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ⧸ Subgroup.center (↥K₀ ⧸ CFSG.pCore 2 ↥K₀))) :
    IsMSPair (K₀ ⊔ S.Tv) S.Tv := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := K₀ ⊔ S.Tv with hHdef
  have hHG : H ≤ Subgroup.centralizer ({S.v12} : Set G) := sup_le hK₀G S.Tv_le_Gv
  have hsylH : IsSylowTwoOf S.Tv H :=
    C1GN.isSylowTwoOf_of_le (S.isSylowTwoOf_Tv_F4 h1222 h517) le_sup_right hHG

  have hvT : S.v12 ∈ S.Tv :=
    ⟨S.V_le_T S.v12_mem_V, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hO : pCoreOf 2 H ≠ ⊥ := by
    have hle : Subgroup.zpowers S.v12 ≤ H := (Subgroup.zpowers_le.mpr hvT).trans le_sup_right
    have hN : H ≤ Subgroup.normalizer (Subgroup.zpowers S.v12 : Set G) := by
      intro g hg
      have hgG : g ∈ Subgroup.centralizer ({S.v12} : Set G) := hHG hg
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp hgG).symm k).eq)
    have h2 : IsPGroup 2 (Subgroup.zpowers S.v12) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (S.elemAbelian_V.2 _ S.v12_mem_V) S.v12_ne_one
    intro h
    have hvO := le_pCoreOf_of_normalizes hle hN h2 (Subgroup.mem_zpowers _)
    rw [h, Subgroup.mem_bot] at hvO
    exact S.v12_ne_one hvO
  have hSQ : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hO
  have hset : (H : Set G) = (K₀ : Set G) * (S.Tv : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K₀ S.Tv hTK₀

  have hlt : S.Tv < H := by
    refine lt_of_le_of_ne le_sup_right fun h => ?_
    have hK₀T : K₀ ≤ S.Tv := h ▸ le_sup_left
    apply hz
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := S.conj_z_of_mem_T (hK₀T hk).1
    calc k * S.z = (k * S.z * k⁻¹) * k := by group
      _ = S.z * k := by rw [h1]
  refine ⟨⟨hSQ, hchar, K₀, hK₀, hset, hRk⟩, Or.inl ⟨S.Tv, hlt, hsylH.2.2, ?_⟩, ?_⟩
  · exact (F6.pCoreOf_eq_self_of_isPGroup hsylH.2.1).symm
  · intro C hCT hC hCc hHC
    exact S.not_le_normalizer_of_characteristic_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h37
      h39 hK₀G hK₀ hTK₀ hz hCT hC hCc (le_sup_left.trans hHC)

theorem c134_data_of_F4 (h132 : ASInputs.AS_C_1_32_F4) (h134 : C134L32Corr_F4) {K₀ : Subgroup G}
    (hK₀ : K₀ ∈ lFamily S.Tv) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hMS : IsMSPair (K₀ ⊔ S.Tv) S.Tv) (h168 : Nat.card (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) = 168) :
    (∃ (F : Type) (_ : Field F) (_ : Fintype F)
      (α : ↥K₀ →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)),
      Fintype.card F = 2 ∧ IsModO2Surj K₀ α) ∧
    ∃ i : ℕ, C134CorrLocal.IsC134CaseCorr i (K₀ ⊔ S.Tv) S.Tv K₀ := by
  have hset : ((K₀ ⊔ S.Tv : Subgroup G) : Set G) = (K₀ : Set G) * (S.Tv : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K₀ S.Tv hTK₀
  have h64 : ¬ 64 ∣ Nat.card (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) := by rw [h168]; norm_num
  rcases h132 G (K₀ ⊔ S.Tv) S.Tv K₀ hMS hK₀ hset with hG2 | hA6 | hSp4 | hHat |
    ⟨n, F, _, _, α, hFn, hα⟩
  ·
    exfalso
    have := SBc11.card_of_isPSU_three_three hG2.2.1
    omega
  ·
    exfalso
    obtain ⟨-, α, hα, hker, -⟩ := hA6
    have h1 : Nat.card (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) = 360 := by
      rw [← hker, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv]
      exact SBc11.card_of_isAlt_six ⟨MulEquiv.refl _⟩
    omega
  ·
    exfalso
    obtain ⟨-, F, _, _, hF4, α, hα, hker, -⟩ := hSp4
    apply h64
    have h1 : Nat.card (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) =
        Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) := by
      rw [← hker]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv
    rw [h1, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
      Nat.card_eq_fintype_card, hF4]
    exact Dvd.dvd.mul_right (by norm_num) _
  ·
    exfalso
    obtain ⟨-, ⟨-, hZ3, ⟨e6⟩⟩, -, -⟩ := hHat
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (↥K₀ ⧸ CFSG.pCore 2 ↥K₀))
    rw [Nat.card_congr e6.toEquiv, SBc11.card_of_isAlt_six ⟨MulEquiv.refl _⟩, hZ3, h168] at h1
    omega
  ·
    have hF2 := card_eq_two_of_not_dvd_64 hFn hα h64
    exact ⟨⟨F, inferInstance, inferInstance, α, hF2, hα⟩,
      h134 G (K₀ ⊔ S.Tv) S.Tv K₀ hMS hK₀ hset ⟨F, inferInstance, inferInstance, α, hF2, hα⟩⟩

end Setting

end CFSG.Quasithin.H13.A5
