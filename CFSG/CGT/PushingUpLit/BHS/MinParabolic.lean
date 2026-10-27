module

public import CFSG.CGT.PushingUpLit.BHS.Prelim
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S9.Defs

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.QuasithinUnique

variable {Γ : Type*} [Group Γ]

theorem three_three_a [Finite Γ] {T P M N : Subgroup Γ} (hT : IsSylowOf 2 T P)
    (hMP : M < P) (hMu : ∀ X : Subgroup Γ, T ≤ X → X < P → X ≤ M) (hNP : N ≤ P)
    (hNn : P ≤ Subgroup.normalizer (N : Set Γ)) (hNM : N ≤ M) :
    P ≤ Subgroup.normalizer ((N ⊓ T : Subgroup Γ) : Set Γ) := by
  rw [inf_comm]
  have hT' : IsSylowTwoOf T P := hT
  have hS : IsSylowTwoOf (T ⊓ N) N := B6.isSylowTwoOf_inf_normal hT' hNP hNn
  have hfr := B6.frattini_two hNP hNn hS
  by_contra hnot
  set K : Subgroup Γ := P ⊓ Subgroup.normalizer ((T ⊓ N : Subgroup Γ) : Set Γ) with hK
  have hTK : T ≤ K := by
    refine le_inf hT.1 fun t ht => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxT, hxN⟩
      exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht), by
        have := (Subgroup.mem_normalizer_iff.mp (hNn (hT.1 ht)) x).mp hxN
        exact this⟩
    · rintro ⟨hxT, hxN⟩
      refine ⟨?_, ?_⟩
      · have := T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
        simpa [mul_assoc] using this
      · have := (Subgroup.mem_normalizer_iff.mp (hNn (hT.1 ht)) x).mpr hxN
        exact this
  have hKP : K < P := by
    exact lt_of_le_of_ne inf_le_left fun h => hnot (h.ge.trans inf_le_right)
  have hKM : K ≤ M := hMu K hTK hKP
  exact hMP.not_ge (hfr.trans (sup_le hNM hKM))

theorem three_three_b [Finite Γ] {T P M N : Subgroup Γ} (hT : IsSylowOf 2 T P)
    (hMu : ∀ X : Subgroup Γ, T ≤ X → X < P → X ≤ M) (hNP : N ≤ P)
    (hNn : P ≤ Subgroup.normalizer (N : Set Γ)) (hNM : ¬ N ≤ M) : opResidual 2 P ≤ N := by
  have hTn : T ≤ Subgroup.normalizer (N : Set Γ) := hT.1.trans hNn
  have hNT : N ⊔ T = P := by
    refine le_antisymm (sup_le hNP hT.1) ?_
    by_contra hlt
    have hlt' : N ⊔ T < P := lt_of_le_of_ne (sup_le hNP hT.1) fun h => hlt h.ge
    exact hNM (le_sup_left.trans (hMu _ le_sup_right hlt'))
  refine opResidual_le_of_pow_mem fun x hx => ?_
  rw [← hNT] at hx
  have hx' : x ∈ ((T ⊔ N : Subgroup Γ) : Set Γ) := by rwa [sup_comm]
  rw [Subgroup.coe_mul_of_left_le_normalizer_right T N hTn] at hx'
  obtain ⟨t, ht, n, hn, hxe⟩ := hx'
  have hxe' : t * n = x := hxe
  subst hxe'
  obtain ⟨k, hk⟩ := hT.2.1 ⟨t, ht⟩
  have hk' : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨y', hy', h⟩ := pow_mul_mem_of_mem_normalizer (hTn ht) hn (2 ^ k)
  exact ⟨k, by rw [h, hk', one_mul]; exact hy'⟩

end CFSG.CGT.PushingUpLit.BHS
