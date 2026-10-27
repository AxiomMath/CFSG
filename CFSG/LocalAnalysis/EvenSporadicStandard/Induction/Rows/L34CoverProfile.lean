module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.L34Profile
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.QuatLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ElemAbelianFour

public section

namespace CFSG.EvenSporadicStandard.L34Q8

open CFSG.EvenSporadicStandard.Induction.CoverFix Subgroup CFSG.ComponentClassification.PSL3Four

@[expose] def NonabelianTwoIn {K : Type*} [Group K] (α : MulAut K) : Prop :=
  ∃ P : Subgroup K, (∀ p ∈ P, α p = p) ∧ IsPGroup 2 P ∧ ∃ p ∈ P, ∃ q ∈ P, p * q ≠ q * p

@[expose] def ElemFourIn {K : Type*} [Group K] (α : MulAut K) : Prop :=
  ∃ E : Subgroup K, (∀ e ∈ E, α e = e) ∧ (∀ e ∈ E, e * e = 1) ∧
    (∀ e ∈ E, ∀ f ∈ E, e * f = f * e) ∧ 4 ≤ Nat.card E

@[expose] def OrderEightIn {K : Type*} [Group K] (α : MulAut K) : Prop :=
  ∃ P : Subgroup K, (∀ p ∈ P, α p = p) ∧ IsPGroup 2 P ∧ Nat.card P = 8

theorem induced_conj_of_conj {K G : Type*} [Group K] [Group G] (π : K →* G)
    (hπ : Function.Surjective π) {α : MulAut K} {β : MulAut G} (h : ∀ x, π (α x) = β (π x))
    {k : K} (hα : α = MulAut.conj k) : β = MulAut.conj (π k) := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ := hπ y
  rw [← h x, hα]
  simp [MulAut.conj_apply]


theorem cover_profile {K : Type} [Group K] [Finite K] (hperf : Group.IsPerfect K)
    (π : K →* ↥S) (hπ : Function.Surjective π) (hker : π.ker = center K) {α : MulAut K}
    (h1 : α ≠ 1) (h2 : α * α = 1) :
    ¬ Group.IsSolvable ↥(fixed α) ∨
      (OrderEightIn α ∧
        ((∀ u ∈ fixed α, u ∈ π.ker → u * u = 1 → u = 1) → NonabelianTwoIn α) ∧
        ((∃ u ∈ fixed α, u ∈ π.ker ∧ u * u = 1 ∧ u ≠ 1) → ElemFourIn α) ∧
        ∀ k : K, α ≠ MulAut.conj k) ∨
      NonabelianTwoIn α := by
  have hZ : π.ker ≤ center K := hker.le
  obtain ⟨β, hβ⟩ := exists_induced π hπ hker α
  have hβ1 : β ≠ 1 := induced_ne_one hperf π hZ hβ h1
  have hβ2 : β * β = 1 := induced_sq π hπ hβ h2
  rcases l34_profile β hβ1 hβ2 with hns | ⟨x, y, hxy, hxf, hyf, hout⟩ | ⟨t, x, y, hβt, hxy, hxt⟩
  · exact Or.inl (not_isSolvable_fixed_of_induced π hπ hZ hβ hns)
  · refine Or.inr (Or.inl ?_)
    obtain ⟨P, hPf, hP2, hPc, hPna⟩ := exists_fixed_two_subgroup π hπ hZ hβ hxy hxf hyf
    obtain ⟨z, hzf, hzz, hzπ⟩ := exists_comm_involution π hπ hZ hβ hxy hxf hyf
    refine ⟨⟨P, hPf, hP2, hPc⟩, fun hno => ?_, fun ⟨u, huf, huk, hu2, hu1⟩ => ?_,
      fun k hk => hout (π k) (induced_conj_of_conj π hπ hβ hk)⟩
    · obtain ⟨p, hp, q, hq, hpq⟩ := hPna hno
      exact ⟨P, hPf, hP2, p, hp, q, hq, hpq⟩
    · have hπz : π z ≠ 1 := by
        rw [hzπ]
        exact hxy.sq_ne
      have hz1 : z ≠ 1 := fun h => hπz (by rw [h, map_one])
      have huz : u * z = z * u := (mem_center_iff.1 (hZ huk) z).symm
      have hne : u ≠ z := fun h => hπz (by
        rw [← h]
        exact MonoidHom.mem_ker.1 huk)
      obtain ⟨E, hEF, hEsq, hEc, hE4⟩ := exists_elemAbelian_four (F := fixed α) huf hzf hu2
        hzz huz hu1 hz1 hne
      exact ⟨E, fun e he => hEF he, hEsq, hEc, hE4⟩
  · refine Or.inr (Or.inr ?_)
    obtain ⟨g, hg⟩ := hπ t
    have hαg : α = MulAut.conj g := by
      refine eq_conj_of_induced_conj hperf π hZ fun x' => ?_
      rw [hβ x', hβt]
      simp [MulAut.conj_apply, hg]
    obtain ⟨P, hPc, hP2, hPna⟩ := exists_commuting_two_subgroup π hπ hZ hxy (g := g)
      (by rw [hg, hxt])
    refine ⟨P, fun p hp => ?_, hP2, hPna⟩
    rw [hαg, MulAut.conj_apply]
    have := hPc p hp
    rw [this]
    group

end CFSG.EvenSporadicStandard.L34Q8
