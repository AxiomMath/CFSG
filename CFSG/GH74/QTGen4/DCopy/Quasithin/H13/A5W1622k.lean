module

public import CFSG.Quasithin.H13.A5W1622k
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622h

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Fischer
open scoped Matrix

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem false_of_hatA6Block_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4)
    (h39 : Vol2Native.A39ForSQTKCat) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀ : K₀ ∈ lFamily S.Tv) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) (hLvK₀ : S.Lv ≤ K₀)
    (hchar : CharTwo (K₀ ⊔ S.Tv)) (hblk : IsHatA6Block K₀) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hshort, hhat, hcardU, hCU⟩ := hblk
  let α : ↥K₀ →* ↥K₀ ⧸ CFSG.pCore 2 ↥K₀ := QuotientGroup.mk' _
  have hα : Function.Surjective α := QuotientGroup.mk'_surjective _
  have hker : α.ker = CFSG.pCore 2 ↥K₀ := QuotientGroup.ker_mk' _
  obtain ⟨P⟩ : Nonempty (Sylow 2 (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)) := inferInstance
  have hS₀ : IsSylowTwoOf (P : Subgroup (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)) ⊤ := by
    refine ⟨le_top, P.isPGroup', ?_⟩
    rw [show ((P : Subgroup (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)).subgroupOf ⊤).index =
      (P : Subgroup (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)).index from Subgroup.relIndex_top_right _]
    exact P.not_dvd_index
  refine S.false_of_blockModelU_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀
    hTK₀ hz hLvK₀ hchar hshort α hα hker hS₀ ?_
  have hinj : Function.Injective (blockLiftConj hshort α hα hker) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨ℓ, rfl⟩ := hα x
    rw [blockLiftConj_apply, A4.actionOn_eq_one_iff] at hx
    have hmem : (ℓ : G) ∈ pCoreOf 2 K₀ := by
      rw [← hCU]
      exact ⟨ℓ.2, hx⟩
    obtain ⟨q, hq, hqℓ⟩ := hmem
    have hqe : q = ℓ := Subtype.ext hqℓ
    subst hqe
    have hq' : q ∈ CFSG.pCore 2 ↥K₀ := by rw [CFSG.pCore_eq_open]; exact hq
    rw [← MonoidHom.mem_ker, hker]
    exact hq'
  have hN2 : ∀ n : ↥(blockU K₀), n ^ 2 = 1 := fun n =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact C1.blockU_sq hshort _ n.2)
  let _ : CommGroup ↥(blockU K₀) :=
    { (inferInstance : Group ↥(blockU K₀)) with
      mul_comm := fun a b => Subtype.ext
        (C1.blockU_comm hshort _ a.2 _ (C1.blockU_le_blockQ hshort b.2)) }
  exact modelFix_hatA6 hN2 hcardU hhat (blockLiftConj hshort α hα hker) hinj hS₀

end Setting

end CFSG.Quasithin.H13.A5
