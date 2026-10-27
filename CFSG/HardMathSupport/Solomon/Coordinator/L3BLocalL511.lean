module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BLocalModel
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BLocalHeis
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BLocalHeisMat

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma511Ns CFSG.RankThree.PartTwo.Sec4
  CFSG.LocalAnalysis.ComponentInitial Matrix

theorem l3b_core511 {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) {Y : Type} [Group Y] [Finite Y]
    (θ : Y ≃* CFSG.Assembly.LowTwoRank.StatedProj (slPi π 3 (p ^ f) K))
    (ŷ : ↥(slPi π 3 (p ^ f) K)) (hŷ : orderOf ŷ = 3) (y : Y) (hy : θ y = QuotientGroup.mk ŷ)
    (hy1 : y ≠ 1) :
    ∃ F : Subgroup Y, y ∈ F ∧ IsElemAbelian 3 F ∧ Nat.card F = 9 ∧
      (∃ f : QuaternionGroup 2 →* autizer (⊤ : Subgroup Y) F, Function.Injective f) ∧
      ∀ u ∈ F, ∀ v ∈ F, u ≠ 1 → v ≠ 1 →
        ∃ g ∈ (⊤ : Subgroup Y) ⊓ Subgroup.normalizer (F : Set Y), g * u * g⁻¹ = v := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  let ι : Y →* ProjGenLinGroup (Fin 3) K := (l3bProjHom (slPi π 3 (p ^ f) K)).comp θ.toMonoidHom
  have hι : Function.Injective ι := (l3bProjHom_injective (slPi π 3 (p ^ f) K)).comp θ.injective
  have hsurj : ∀ s ∈ slPi π 3 (p ^ f) K, ∃ m : Y, ι m = ProjGenLinGroup.mk s := fun s hs =>
    ⟨θ.symm (QuotientGroup.mk ⟨s, hs⟩), by
      show l3bProjHom (slPi π 3 (p ^ f) K) (θ (θ.symm _)) = _
      rw [MulEquiv.apply_symm_apply]; rfl⟩
  have hιy : ι y = ProjGenLinGroup.mk (ŷ : GL (Fin 3) K) := by
    show l3bProjHom (slPi π 3 (p ^ f) K) (θ y) = _
    rw [hy]; rfl
  have hx3 : orderOf (ŷ : GL (Fin 3) K) = 3 := by rw [Subgroup.orderOf_coe]; exact hŷ
  have hxZ : (ŷ : GL (Fin 3) K) ∉ zPi π 3 (p ^ f) K := by
    intro h
    have hs := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 h
    apply hy1
    apply θ.injective
    rw [hy, map_one]
    exact (QuotientGroup.eq_one_iff ŷ).2 hs
  obtain ⟨g, hg, hgx⟩ := rank3II_4_10_three hK hq hτ hτ1 ŷ.2 hxZ hx3
  have hxeq : (ŷ : GL (Fin 3) K) = g * diagTau hτ * g⁻¹ := eq_conj_of_inv_conj hgx
  have hc : g * cycThree * g⁻¹ ∈ slPi π 3 (p ^ f) K := conj_mem_slPi hπ hg (cycThree_mem_slPi hπ)
  obtain ⟨x₂, hx₂⟩ := hsurj _ hc
  obtain ⟨n₁, n₂, h12, h1, h2, hx1, hx2, hF1, hF2, hN1, hN2⟩ :=
    l3b_heis_pair (π := π) ι hι hsurj hK hq hτ hτ1 hg (x₁ := y) (x₂ := x₂)
      (by rw [hιy, hxeq]) hx₂
  obtain ⟨hE1, hE2, hE3, hE4⟩ := l3b_heis_q8_data (J := ⊤) (E := Subgroup.zpowers y ⊔
    Subgroup.zpowers x₂) rfl h12 h1 h2 hx1 hx2 hF1 hF2 hN1 hN2 trivial trivial
  exact ⟨_, Subgroup.mem_sup_left (Subgroup.mem_zpowers y), hE1, hE2, hE3, hE4⟩

theorem lemma511_input30_2_holds : Lemma511Ns.Input30_2 := by
  intro Y _ _ y hy1 hlift
  rcases hlift with ⟨K, _, _, θ, hK3, ŷ, hŷ, hθ⟩ | ⟨K, _, _, q, θ, hcard, hq3, ŷ, hŷ, hθ⟩
  · obtain ⟨p, f, hK, hq⟩ := l3b_exists_piField_true hK3
    exact l3b_core511 (π := true) hK hq θ ŷ hŷ y hθ hy1
  · obtain ⟨p, f, rfl, hK, hq⟩ := l3b_exists_piField_false hcard hq3
    exact l3b_core511 (π := false) hK hq θ ŷ hŷ y hθ hy1

end CFSG.HardMathSupport.Solomon.Coordinator
