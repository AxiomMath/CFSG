module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.GF2Type.Aschbacher1976Full.HSGL3
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

theorem y7c_index_dvd_168 {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] (hM : IsE 6 M)
    (ρ : Γ →* MulAut M) {N : Subgroup Γ} (hq : CFSG.IsQuasisimple ↥N) {V : Subgroup M}
    (hV8 : Nat.card ↥V = 8) (hVinv : ∀ n ∈ N, ∀ v ∈ V, ρ n v ∈ V)
    (hnt : ∃ n ∈ N, ∃ v ∈ V, ρ n v ≠ v) :
    Nat.card (↥N ⧸ Subgroup.center ↥N) ∣ 168 := by
  have hcommM : ∀ a b : M, a * b = b * a := fun a b =>
    congrArg Subtype.val
      (hM.1.1.is_comm.comm (⟨a, trivial⟩ : ↥(⊤ : Subgroup M)) ⟨b, trivial⟩)
  have hsqM : ∀ v : M, v * v = 1 := by
    intro v
    have h : v ^ 2 = 1 := hM.1.2 v trivial
    simpa [pow_two] using h
  have hVcomm : ∀ a b : ↥V, a * b = b * a := fun a b => Subtype.ext (hcommM a b)
  have hVsq : ∀ v : ↥V, v * v = 1 := fun v => Subtype.ext (hsqM v)
  have hmap : ∀ n : ↥N, V.map (ρ (n : Γ)) = V := by
    intro n
    refine Subgroup.eq_of_le_of_card_ge (H := V.map (ρ (n : Γ))) (K := V) ?_ ?_
    · rintro x ⟨v, hv, rfl⟩
      exact hVinv n n.2 v hv
    · rw [Subgroup.card_map_of_injective (ρ (n : Γ)).injective]
  let θfun : ↥N → MulAut ↥V := fun n =>
    (MulEquiv.subgroupMap (ρ (n : Γ)) V).trans (MulEquiv.subgroupCongr (hmap n))
  have hθmap : ∀ (n : ↥N) (v : ↥V), ((θfun n) v : M) = ρ (n : Γ) v := by
    intro n v
    simp [θfun]
  let θ : ↥N →* MulAut ↥V :=
    { toFun := θfun
      map_one' := by
        apply MulEquiv.ext
        intro v
        apply Subtype.ext
        rw [hθmap 1 v]
        simp
      map_mul' := by
        intro n₁ n₂
        apply MulEquiv.ext
        intro v
        apply Subtype.ext
        rw [MulAut.mul_apply, hθmap n₁ ((θfun n₂) v), hθmap n₂ v, hθmap (n₁ * n₂) v,
          show ((n₁ * n₂ : ↥N) : Γ) = (n₁ : Γ) * (n₂ : Γ) from rfl, map_mul,
          MulAut.mul_apply] }
  let N₁ : Subgroup ↥N := θ.ker
  have hN₁ne : N₁ ≠ ⊤ := by
    intro htop
    obtain ⟨n, hnN, v, hvV, hne⟩ := hnt
    have hmem : (⟨n, hnN⟩ : ↥N) ∈ N₁ := by rw [htop]; exact Subgroup.mem_top _
    have hker : θ ⟨n, hnN⟩ = 1 := MonoidHom.mem_ker.mp hmem
    have hcongr := congrArg (fun f : MulAut ↥V => ((f ⟨v, hvV⟩ : ↥V) : M)) hker
    have h1 : ((θ ⟨n, hnN⟩) ⟨v, hvV⟩ : M) = ρ n v := by
      change ((θfun ⟨n, hnN⟩) ⟨v, hvV⟩ : M) = ρ n v
      exact hθmap ⟨n, hnN⟩ ⟨v, hvV⟩
    exact hne (by simpa [h1] using hcongr)
  have hle : N₁ ≤ Subgroup.center ↥N := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups (Q := ↥N) hq (N := N₁)
        (inferInstance : N₁.Normal) with h | h
    · exact absurd h hN₁ne
    · exact h
  have hdvd : (Subgroup.center ↥N).index ∣ N₁.index := Subgroup.index_dvd_of_le hle
  have hN₁index : N₁.index = Nat.card θ.range := Subgroup.index_ker θ
  have hrange : Nat.card θ.range ∣ Nat.card (MulAut ↥V) :=
    Subgroup.card_subgroup_dvd_card θ.range
  have h168 : Nat.card (MulAut ↥V) = 168 :=
    CFSG.GF2Type.Aschbacher1976Full.HS.card_mulAut_eq_168 hV8 hVcomm hVsq
  have hcenter : Nat.card (↥N ⧸ Subgroup.center ↥N) = (Subgroup.center ↥N).index :=
    (Subgroup.index_eq_card (Subgroup.center ↥N)).symm
  rw [hcenter]
  calc (Subgroup.center ↥N).index ∣ N₁.index := hdvd
    _ = Nat.card θ.range := hN₁index
    _ ∣ Nat.card (MulAut ↥V) := hrange
    _ ∣ 168 := h168 ▸ dvd_rfl

end CFSG.OddStandard.HigherRank.YamadaG23
