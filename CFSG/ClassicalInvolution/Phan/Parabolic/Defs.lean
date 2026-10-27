module

public import CFSG.ClassicalInvolution.Phan.Torus
public import CFSG.ClassicalInvolution.Phan.Parabolic.Generic

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

section Defs

variable (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]

@[expose] noncomputable def blockSup (n : ℕ) (J : Set (Fin n)) : Subgroup (Su K p f (n + 1)) :=
  ⨆ j ∈ J, (blockEmb2 K p f n j).range

@[expose] noncomputable def parabolic (n : ℕ) (J : Set (Fin n)) : Subgroup (Su K p f (n + 1)) :=
  torus (unitaryInvolution K p f) (n + 1) ⊔ blockSup K p f n J

end Defs

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem parabolic_def (J : Set (Fin n)) :
    parabolic K p f n J = torus (unitaryInvolution K p f) (n + 1) ⊔
      ⨆ j ∈ J, (blockEmb2 K p f n j).range :=
  rfl

theorem range_blockEmb2_le_blockSup {J : Set (Fin n)} {j : Fin n} (hj : j ∈ J) :
    (blockEmb2 K p f n j).range ≤ blockSup K p f n J :=
  le_iSup₂ (f := fun j _ => (blockEmb2 K p f n j).range) j hj

theorem blockEmb2_mem_blockSup {J : Set (Fin n)} {j : Fin n} (hj : j ∈ J) (A : Su K p f 2) :
    blockEmb2 K p f n j A ∈ blockSup K p f n J :=
  range_blockEmb2_le_blockSup hj ⟨A, rfl⟩

theorem torus_le_parabolic (J : Set (Fin n)) :
    torus (unitaryInvolution K p f) (n + 1) ≤ parabolic K p f n J :=
  le_sup_left

theorem blockSup_le_parabolic (J : Set (Fin n)) :
    blockSup K p f n J ≤ parabolic K p f n J :=
  le_sup_right

theorem range_blockEmb2_le_parabolic {J : Set (Fin n)} {j : Fin n} (hj : j ∈ J) :
    (blockEmb2 K p f n j).range ≤ parabolic K p f n J :=
  (range_blockEmb2_le_blockSup hj).trans (blockSup_le_parabolic J)

theorem blockEmb2_mem_parabolic {J : Set (Fin n)} {j : Fin n} (hj : j ∈ J) (A : Su K p f 2) :
    blockEmb2 K p f n j A ∈ parabolic K p f n J :=
  range_blockEmb2_le_parabolic hj ⟨A, rfl⟩

theorem blockSup_mono {J J' : Set (Fin n)} (h : J ⊆ J') :
    blockSup K p f n J ≤ blockSup K p f n J' :=
  iSup₂_le fun _ hj => range_blockEmb2_le_blockSup (h hj)

theorem parabolic_mono {J J' : Set (Fin n)} (h : J ⊆ J') :
    parabolic K p f n J ≤ parabolic K p f n J' :=
  sup_le_sup_left (blockSup_mono h) _

theorem blockSup_empty : blockSup K p f n (∅ : Set (Fin n)) = ⊥ :=
  iSup_emptyset

theorem blockSup_singleton (i : Fin n) :
    blockSup K p f n {i} = (blockEmb2 K p f n i).range :=
  iSup_singleton

theorem blockSup_pair (a b : Fin n) :
    blockSup K p f n {a, b} = (blockEmb2 K p f n a).range ⊔ (blockEmb2 K p f n b).range :=
  iSup_pair

theorem parabolic_empty : parabolic K p f n (∅ : Set (Fin n)) =
    torus (unitaryInvolution K p f) (n + 1) := by
  rw [parabolic, blockSup_empty, sup_bot_eq]

theorem torus_le_normalizer_blockSup (hK : Nat.card K = (p ^ f) ^ 2) (J : Set (Fin n)) :
    torus (unitaryInvolution K p f) (n + 1) ≤
      Subgroup.normalizer (blockSup K p f n J : Set (Su K p f (n + 1))) :=
  le_normalizer_iSup₂ _ J (fun j => (blockEmb2 K p f n j).range) fun j =>
    torus_le_normalizer_range_blockEmb hK (by omega)

theorem parabolic_le_closure (J : Set (Fin n)) :
    parabolic K p f n J ≤ Subgroup.closure
      ((torus (unitaryInvolution K p f) (n + 1) : Set (Su K p f (n + 1))) ∪
        ⋃ j ∈ J, ((blockEmb2 K p f n j).range : Set (Su K p f (n + 1)))) := by
  refine sup_le (fun x hx => Subgroup.subset_closure (Or.inl hx)) ?_
  refine iSup₂_le fun j hj x hx => ?_
  exact Subgroup.subset_closure (Or.inr (Set.mem_biUnion hj hx))

end CFSG.ClassicalInvolution.Phan
