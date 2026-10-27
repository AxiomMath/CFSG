module

public import CFSG.LocalAnalysis.SteinbergCENilpotentFrattiniActionCommutation
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65

open CFSG.LocalAnalysis.NilpotentFrattiniAction Subgroup
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] (Q : Subgroup G) [Q.Normal] [Fact (IsPGroup 2 Q)]

abbrev FV : Type := Additive (↥Q ⧸ frattini ↥Q)

noncomputable def rep : Representation (ZMod 2) G (FV Q) :=
  (Units.coeHom (FV Q →ₗ[ZMod 2] FV Q)).comp (frattiniRep 2 Q)

def piV (c : ↥Q) : FV Q := Additive.ofMul (c : ↥Q ⧸ frattini ↥Q)

theorem rep_apply (g : G) (c : ↥Q) : rep Q g (piV Q c) = piV Q (MulAut.conjNormal g c) := by
  change (frattiniRep 2 Q g : FV Q →ₗ[ZMod 2] FV Q) (Additive.ofMul (c : ↥Q ⧸ frattini ↥Q)) = _
  rw [frattiniRep_apply, frattiniConj_mk]
  rfl

theorem piV_one : piV Q 1 = 0 := by
  simp [piV]

theorem piV_mul_inv (a b : ↥Q) : piV Q (a * b⁻¹) = piV Q a - piV Q b := by
  simp only [piV, sub_eq_add_neg]
  rfl

theorem rep_sub_one_apply (g : G) (c : ↥Q) :
    (rep Q g - 1) (piV Q c) = piV Q (MulAut.conjNormal g c * c⁻¹) := by
  rw [piV_mul_inv, LinearMap.sub_apply, rep_apply]
  rfl

theorem piV_surjective : Function.Surjective (piV Q) := by
  intro v
  obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  exact ⟨c, by simpa [piV] using congrArg Additive.ofMul hc⟩

theorem exists_pow_mem_centralizer {g : G} (hg : rep Q g = 1) :
    ∃ k : ℕ, g ^ 2 ^ k ∈ centralizer (Q : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 ↥Q := Fact.out
  have hker := (CFSG.GroupTheory.frattini_automorphism_kernel hQ).2
  have hmem : (MulAut.conjNormal g : MulAut ↥Q) ∈
      (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥Q)).ker := by
    rw [CFSG.OrderReductions.FrattiniAutomorphisms.mem_quotientAutomorphism_kernel]
    intro c
    have h1 : rep Q g (piV Q c) = piV Q c := by
      rw [hg]
      rfl
    rw [rep_apply] at h1
    exact Additive.ofMul.injective h1
  obtain ⟨k, hk⟩ := hker ⟨_, hmem⟩
  refine ⟨k, ?_⟩
  have hk' : (MulAut.conjNormal g : MulAut ↥Q) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have h2 := congrArg (fun σ : MulAut ↥Q => ((σ ⟨q, hq⟩ : ↥Q) : G)) hk'
  simp only [← map_pow, MulAut.conjNormal_apply, MulAut.one_apply] at h2
  generalize g ^ 2 ^ k = h at h2 ⊢
  calc q * h = (h * q * h⁻¹) * h := by rw [h2]
    _ = h * q := by group

theorem isPGroup_ker_rep (hC : centralizer (Q : Set G) ≤ Q) : IsPGroup 2 (rep Q).ker := by
  intro g
  have hg : rep Q (g : G) = 1 := g.2
  obtain ⟨k, hk⟩ := exists_pow_mem_centralizer Q hg
  have hQ : IsPGroup 2 ↥Q := Fact.out
  obtain ⟨m, hm⟩ := hQ ⟨_, hC hk⟩
  refine ⟨k + m, Subtype.ext ?_⟩
  have h1 : (g : G) ^ 2 ^ (k + m) = ((g : G) ^ 2 ^ k) ^ 2 ^ m := by
    rw [pow_add, pow_mul]
  have h2 : ((g : G) ^ 2 ^ k) ^ 2 ^ m = 1 := congrArg Subtype.val hm
  simpa [h1] using h2

noncomputable def subEquiv : Subgroup (↥Q ⧸ frattini ↥Q) ≃o Submodule (ZMod 2) (FV Q) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)

noncomputable def subV (H : Subgroup ↥Q) : Submodule (ZMod 2) (FV Q) :=
  subEquiv Q (H.map (QuotientGroup.mk' (frattini ↥Q)))

theorem mem_subV {H : Subgroup ↥Q} {v : FV Q} : v ∈ subV Q H ↔ ∃ c ∈ H, piV Q c = v := by
  change Additive.toMul v ∈ H.map (QuotientGroup.mk' (frattini ↥Q)) ↔ _
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, by simpa [piV] using congrArg Additive.ofMul h⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩

theorem subV_mono {H K : Subgroup ↥Q} (h : H ≤ K) : subV Q H ≤ subV Q K := by
  intro v hv
  obtain ⟨c, hc, rfl⟩ := (mem_subV Q).1 hv
  exact (mem_subV Q).2 ⟨c, h hc, rfl⟩

theorem subV_iSup {ι : Sort*} (H : ι → Subgroup ↥Q) : subV Q (⨆ i, H i) = ⨆ i, subV Q (H i) := by
  unfold subV
  rw [Subgroup.map_iSup, OrderIso.map_iSup]

theorem subV_top : subV Q ⊤ = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨c, rfl⟩ := piV_surjective Q v
  exact (mem_subV Q).2 ⟨c, mem_top c, rfl⟩

theorem card_subV (H : Subgroup ↥Q) :
    Nat.card (subV Q H) = Nat.card (H.map (QuotientGroup.mk' (frattini ↥Q))) := by
  refine Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun v => ?_)
  exact Iff.rfl

theorem finrank_le_of_card_le {W : Submodule (ZMod 2) (FV Q)} {n : ℕ}
    (h : Nat.card W ≤ 2 ^ n) : Module.finrank (ZMod 2) W ≤ n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [h1] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65
