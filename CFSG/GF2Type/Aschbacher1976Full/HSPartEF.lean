module

public import CFSG.GF2Type.Aschbacher1976Full.HSPartEC
public import CFSG.GF2Type.Aschbacher1976Full.HSAutSL

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.PartE

variable {G : Type} [Group G] [Finite G] {z : G} {T V : Subgroup G}

theorem pCoreOf_normalizer_eq (hset : HSSetting G z) (hV : HSV z T V) :
    CFSG.Open.pCoreOf 2 (Subgroup.normalizer (V : Set G)) = Subgroup.centralizer (V : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCN : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.centralizer_le_normalizer _
  obtain ⟨θ, hθs, hθk⟩ := hsAut_exists_SL gl3Stmt_holds hset hV
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
    haveI := CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
    exact CFSG.ComponentClassification.GHarris.SL32EquivGL32.isSimpleGroup
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    haveI hnormal : ((CFSG.pCore 2 ↥(Subgroup.normalizer (V : Set G))).map θ).Normal :=
      CFSG.pCore_normal.map θ hθs
    have h2 : IsPGroup 2 ↥((CFSG.pCore 2 ↥(Subgroup.normalizer (V : Set G))).map θ) :=
      CFSG.pCore_isPGroup.map θ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((CFSG.pCore 2 ↥(Subgroup.normalizer (V : Set G))).map θ) with hbot | htop
    · have hθy : θ y ∈ (CFSG.pCore 2 ↥(Subgroup.normalizer (V : Set G))).map θ := ⟨y, hy, rfl⟩
      rw [hbot] at hθy
      have hyker : y ∈ θ.ker := hθy
      rw [hθk, Subgroup.mem_subgroupOf] at hyker
      exact hyker
    · exfalso
      rw [htop] at h2
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
      rw [Subgroup.card_top,
        Nat.card_congr CFSG.ComponentClassification.GHarris.SL32EquivGL32.toEquiv,
        CFSG.ComponentClassification.GHarris.card_GL32_gh] at hn
      have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 168)
      have := Nat.prime_three.dvd_of_dvd_pow h3
      omega
  · intro c hc
    have hker : ((Subgroup.centralizer (V : Set G)).subgroupOf
        (Subgroup.normalizer (V : Set G))).Normal := by
      rw [← actV_ker]
      infer_instance
    have hp2 : IsPGroup 2 ↥((Subgroup.centralizer (V : Set G)).subgroupOf
        (Subgroup.normalizer (V : Set G))) :=
      (centralizer_isPGroup hset hV).of_equiv (Subgroup.subgroupOfEquivOfLe hCN).symm
    have hle : (Subgroup.centralizer (V : Set G)).subgroupOf (Subgroup.normalizer (V : Set G)) ≤
        CFSG.pCore 2 ↥(Subgroup.normalizer (V : Set G)) := le_sSup ⟨hker, hp2⟩
    exact ⟨⟨c, hCN hc⟩, hle (Subgroup.mem_subgroupOf.mpr hc), rfl⟩

theorem quasithinGenFitting_normalizer_eq (hset : HSSetting G z) (hV : HSV z T V) :
    CFSG.Open.quasithinGenFitting (Subgroup.normalizer (V : Set G)) =
      Subgroup.centralizer (V : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp := pCoreOf_normalizer_eq hset hV
  have key : CFSG.Open.quasithinGenFitting (Subgroup.normalizer (V : Set G)) =
      CFSG.Open.pCoreOf 2 (Subgroup.normalizer (V : Set G)) := by
    refine (CFSG.Quasithin.quasithinGenFitting_eq_pCoreOf_iff _ 2).mpr ?_
    rw [hp]
    rintro x ⟨-, hx⟩
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    exact (Subgroup.mem_centralizer_iff.mp hx) v
      (Subgroup.mem_centralizer_iff.mpr fun a ha => hsAut_mul_comm hV ha hv)
  rw [key, hp]

end CFSG.GF2Type.Aschbacher1976Full.HS.PartE
