module

public import CFSG.CGT.PushingUpLit.T2KR.TorusSzGrp
public import CFSG.CGT.Timmesfeld75.BenderInputsBasic
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFactsBasic
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
public import Certificates.Certificate113
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Walter.Defs

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG.Open CFSG.CGT.Timmesfeld75

section Zsharp

variable {K : Type*} [Group K] [Finite K]

theorem card_zsharp_eq (Q : Subgroup K) :
    Nat.card {w : K // IsZSharp Q w} = Nat.card (Subgroup.center ↥Q) - 1 := by
  classical
  have e : {w : K // IsZSharp Q w} ≃ {z : ↥(Subgroup.center ↥Q) // z ≠ 1} :=
    { toFun := fun w => ⟨⟨⟨w.1, w.2.1⟩, Subgroup.mem_center_iff.2 fun g =>
        Subtype.ext (w.2.2.1 g g.2)⟩, fun h => w.2.2.2 (by
          have := congrArg (fun z : ↥(Subgroup.center ↥Q) => ((z : ↥Q) : K)) h
          simpa using this)⟩
      invFun := fun z => ⟨((z.1 : ↥Q) : K), (z.1 : ↥Q).2, fun x hx => by
        have := Subgroup.mem_center_iff.1 z.1.2 ⟨x, hx⟩
        exact congrArg Subtype.val this, fun h => z.2 (Subtype.ext (Subtype.ext h))⟩
      left_inv := fun w => rfl
      right_inv := fun z => rfl }
  rw [Nat.card_congr e]
  have : Fintype ↥(Subgroup.center ↥Q) := Fintype.ofFinite _
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

end Zsharp

section Setting

variable {K : Type} [Group K] [Finite K]

theorem szSetting_of_equiv {a : ℕ} (ha : 1 ≤ a)
    (e : K ≃* Sz a) : SzSetting K (2 ^ (2 * a + 1)) := by
  have hK : CFSG.BenderSuzuki.IsBenderGroup K :=
    CFSG.ComponentClassification.Asc76X.isBenderGroup_of_mulEquiv_sz ha e
  have hB := CFSG.ComponentClassification.Asc76X.fusionBenderBorel_of_mulEquiv_sz ha e
  have h8 : 8 ≤ 2 ^ (2 * a + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine
    { three_le := by omega
      card := ?_
      syl_card := fun Q => (hB Q).2.2.2.2
      ne_top := fun Q =>
        (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isStronglyEmbeddedOrder_normalizer hK Q).1
      odd_inter := ?_
      inv_central := fun Q x hx hxx y hy =>
        (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hK Q hx hxx y hy).eq
      card_zsharp := ?_
      trans := ?_
      cent_le := fun Q t ht htt ht1 => centralizer_le_normalizer_of_isBenderGroup hK Q ht htt ht1 }
  · rw [Nat.card_congr e.toEquiv]
    exact CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz a
  · intro Q Q' hne
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq K Q Q'
    have hg : g ∉ Subgroup.normalizer (Q : Set K) := fun hg =>
      hne (Sylow.smul_eq_iff_mem_normalizer.2 hg).symm
    have hse := (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isStronglyEmbeddedOrder_normalizer
      hK Q).2.2 g hg
    have hN : Subgroup.normalizer ((g • Q : Sylow 2 K) : Set K) =
        (Subgroup.normalizer (Q : Set K)).map (MulAut.conj g).toMonoidHom := by
      ext x
      rw [Subgroup.mem_map]
      constructor
      · intro hx
        have hx' := Sylow.smul_eq_iff_mem_normalizer.2 hx
        refine ⟨g⁻¹ * x * g, ?_, ?_⟩
        · apply Sylow.smul_eq_iff_mem_normalizer.1
          calc (g⁻¹ * x * g) • Q = g⁻¹ • (x • (g • Q)) := by rw [mul_smul, mul_smul]
            _ = g⁻¹ • (g • Q) := by rw [hx']
            _ = Q := inv_smul_smul _ _
        · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
      · rintro ⟨y, hy, rfl⟩
        apply Sylow.smul_eq_iff_mem_normalizer.1
        have hy' := Sylow.smul_eq_iff_mem_normalizer.2 hy
        calc (MulAut.conj g).toMonoidHom y • (g • Q) = g • (y • (g⁻¹ • (g • Q))) := by
              simp [MulAut.conj_apply, mul_smul]
          _ = g • Q := by rw [inv_smul_smul, hy']
    rw [hN]
    exact hse
  · intro Q
    rw [card_zsharp_eq, (hB Q).2.2.2.1]
  · intro Q x y hx hy
    exact CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_normalizer_conj hK Q
      ⟨hx.1, fun q hq => hx.2.1 q hq⟩ hx.2.2 ⟨hy.1, fun q hq => hy.2.1 q hq⟩ hy.2.2

end Setting

end CFSG.CGT.PushingUpLit.T2KR
