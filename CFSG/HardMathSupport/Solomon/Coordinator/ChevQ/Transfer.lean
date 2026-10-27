module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsBase
public import CFSG.LieType.Seitz.Defs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns CFSG.LieType.Seitz

section Action

variable {X : Type} [Group X] [Finite X]

@[expose] noncomputable def actK {K B : Subgroup X} (hBN : B ≤ Subgroup.normalizer (K : Set X)) :
    ↥B →* MulAut ↥K :=
  K.normalizerMonoidHom.comp (Subgroup.inclusion hBN)

theorem coe_actK {K B : Subgroup X} (hBN : B ≤ Subgroup.normalizer (K : Set X)) (b : ↥B)
    (x : ↥K) : ((actK hBN b x : ↥K) : X) = (b : X) * (x : X) * (b : X)⁻¹ := rfl

theorem ker_actK {K B : Subgroup X} (hBN : B ≤ Subgroup.normalizer (K : Set X)) :
    (actK hBN).ker = (Subgroup.centralizer (K : Set X)).subgroupOf B := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have h1 := Subgroup.normalizerMonoidHom_ker (H := K)
  have h2 : Subgroup.inclusion hBN b ∈ K.normalizerMonoidHom.ker ↔
      ((Subgroup.inclusion hBN b : ↥(Subgroup.normalizer (K : Set X))) : X) ∈
        Subgroup.centralizer (K : Set X) := by
    rw [h1, Subgroup.mem_subgroupOf]
  exact (MonoidHom.mem_ker (f := K.normalizerMonoidHom)
    (x := Subgroup.inclusion hBN b)).symm.trans h2

theorem isElemAbelian_range_actK {p : ℕ} {K B : Subgroup X} (hB : IsElemAbelian p B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) : IsElemAbelian p (actK hBN).range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : MulAut ↥K) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (congrArg Subtype.val (hB.1.is_comm.comm x z))
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [← map_pow]
    have : x ^ p = 1 := Subtype.ext (hB.2 x x.2)
    rw [this, map_one]

theorem card_range_actK {K B : Subgroup X} (hBN : B ≤ Subgroup.normalizer (K : Set X)) :
    Nat.card B = Nat.card (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) *
      Nat.card (actK hBN).range := by
  have h1 := Subgroup.card_ker_mul_card_range (actK hBN)
  rw [ker_actK hBN] at h1
  have h2 : Nat.card ((Subgroup.centralizer (K : Set X)).subgroupOf B) =
      Nat.card (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) := by
    rw [inf_comm, ← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [h2] at h1
  exact h1.symm

theorem card_ker_actK {K B : Subgroup X} (hBN : B ≤ Subgroup.normalizer (K : Set X)) :
    Nat.card (actK hBN).ker = Nat.card (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) := by
  rw [ker_actK hBN, inf_comm, ← Subgroup.inf_subgroupOf_right]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv

end Action

section Transfer

variable {X : Type} [Group X] [Finite X]

theorem isInGOne_of_gammaPrime_four {p : ℕ} {K B : Subgroup X}
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (h : K ≤ gammaPrimeIn p 4 B K) :
    IsInGOne p B K := by
  refine i271h_isInGOne_of_le hBN (h.trans ?_)
  unfold gammaPrimeIn
  exact iSup₂_le fun E hE => i271h_le_coreIn_of_le_centralizer hE.1 (by omega) le_rfl

end Transfer

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
