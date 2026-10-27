module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuPerm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeTrans
public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalogBase

public section

namespace CFSG.QuasithinUnique.Bridge.RuExcl

open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.RuSchreier
open CFSG.Blueprint

noncomputable def ruEquivC
    : NativeSporadic.Carrier .Ru ≃* ↥ruP := ruEquivP

noncomputable def ruAutEquiv
    : ↥ruP ≃* MulAut (NativeSporadic.Carrier .Ru) :=
  (MulEquiv.ofBijective (MulAut.conj : ↥ruP →* MulAut ↥ruP) conj_bijective).trans
    (MulAut.congr (G := ↥ruP) (H := NativeSporadic.Carrier .Ru) ruEquivC.symm)

theorem ruAutEquiv_apply
    (s : NativeSporadic.Carrier .Ru) :
    ruAutEquiv (ruEquivC s) = MulAut.conj s := by
  refine MulEquiv.ext fun s' => ?_
  simp only [ruAutEquiv, MulEquiv.trans_apply, MulEquiv.ofBijective_apply, MulAut.congr_apply,
    MulEquiv.symm_symm, MulAut.conj_apply, map_mul, map_inv, MulEquiv.symm_apply_apply]

theorem ru_rank
    : ∀ B : Subgroup (MulAut (NativeSporadic.Carrier .Ru)),
    (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 9 :=
  rank_of_equiv ruAutEquiv ru_rank_P

theorem ru_gen
    : ∀ ψ : MulAut (NativeSporadic.Carrier .Ru), ψ * ψ = 1 → ψ ≠ 1 →
    ∃ cs : List (MulAut (NativeSporadic.Carrier .Ru)), cs.length = 3 ∧
      (∀ c ∈ cs, c ∈ (MulAut.conj : NativeSporadic.Carrier .Ru →*
        MulAut (NativeSporadic.Carrier .Ru)).range) ∧
      ∀ s : NativeSporadic.Carrier .Ru, MulAut.conj s ∈ Subgroup.closure (conjSet cs {ψ}) :=
  gen_of_equiv (G := Equiv.Perm (Fin 4060)) (H := ruP) (A := ruP) le_rfl ruAutEquiv ruEquivC
    (fun s => ruAutEquiv_apply s) fun x hx hx2 hx1 => ru_gen_perm hx (by rw [sq]; exact hx2) hx1

theorem orderOf_two_zmod_29 : orderOf (2 : ZMod 29) = 28 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem ru_dim
    (V : Type) [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    (σ : NativeSporadic.Carrier .Ru →* MulAut V) (hσ : Function.Injective σ) :
    2 ^ 28 ≤ Nat.card V := by
  have h29 : 29 ∣ Nat.card (NativeSporadic.Carrier .Ru) := by
    rw [show Nat.card (NativeSporadic.Carrier .Ru) = 145926144000 from
      CFSG.Sporadic.Ru.card_Ru]
    norm_num
  have : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  have : Finite (NativeSporadic.Carrier .Ru) := CFSG.Sporadic.Ru.fam_ru_simplicity.1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 29 h29
  have hσx : orderOf (σ x) = 29 := by rw [orderOf_injective σ hσ x, hx]
  have h := two_pow_orderOf_le_index_fixV hV (p := 29) (by norm_num) hσx
  rw [orderOf_two_zmod_29] at h
  exact h.trans (index_fixV_le_card _)

theorem ru_cover
    (E : Type) [Group E] [Finite E] [Group.IsPerfect E]
    (π : E →* NativeSporadic.Carrier .Ru) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ :=
  CFSG.SectionRank.Ru_perfect_odd_cover_trivial π hπ hC hodd

theorem sporadicExclusion_Ru
    : X1.SporadicExclusion .Ru := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hE hEne hEel _
  have : Nontrivial (NativeSporadic.Carrier .Ru) := CFSG.Sporadic.Ru.fam_ru_simplicity.2.1
  exact weight_lt_of_three_conj hW hq.1 hirr hE hEne hEel e (r := 9) (k := 3) (ρ := 28)
    (by norm_num) (fun E _ _ _ π hπ hC hodd => ru_cover E π hπ hC hodd) ru_rank ru_gen ru_dim

end CFSG.QuasithinUnique.Bridge.RuExcl
