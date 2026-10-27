module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoTwoExGlue
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarFrame

public section

namespace CFSG.OddStandard.AltStdCycTwo.Two.Exact

open Subgroup Equiv Equiv.Perm AltStdBal AltStdSec

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} {z u : G}

theorem exists_untwisted (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {S₀ : Finset (Fin n)} (hk : S₀.card = 3 ∨ S₀.card = 4) (hkn : S₀.card + 7 ≤ n)
    (hII : CaseIIAt θ z S₀) :
    ∃ (u₀ : G) (T₀ : Shape G L Q n z u₀), ∀ τ : Perm (Fin n), τ.IsSwap →
      IsConj z (swapIota T₀ θ τ : G) ∧ ¬ IsConj z (z * (swapIota T₀ θ τ : G)) := by
  have hz2 : z * z = 1 := T.cyc.mul_self
  obtain ⟨c, hc, htw⟩ := caseII_twist T θ hk hkn hII
  rcases hc with hc | hc
  · rw [hc] at htw
    exact ⟨u, T, fun τ hτ => by simpa using htw τ hτ⟩
  · rw [hc] at htw
    refine ⟨u * z, T.mul_z, fun τ hτ => ?_⟩
    obtain ⟨h1, h2⟩ := htw τ hτ
    rw [hz2, one_mul] at h2
    rw [swapIota_mul_z_eq T θ hτ.sign_eq, ← mul_assoc, hz2, one_mul]
    exact ⟨h1, h2⟩

@[expose] noncomputable def permHom (B : Base G L Q n z) (θ : L ≃* alternatingGroup (Fin n)) :
    centralizer ({z} : Set G) →* Perm (Fin n) :=
  (rho θ B.hn).comp (Subgroup.inclusion (cent_le_normalizer B.std B.cyc))

@[expose] noncomputable def nearData_of_untwisted {u₀ : G} (T₀ : Shape G L Q n z u₀)
    (θ : L ≃* alternatingGroup (Fin n))
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q) {S₀ : Finset (Fin n)}
    (hS₀ : S₀.card = 3 ∨ S₀.card = 4) (hkn : S₀.card + 7 ≤ n) (hII : CaseIIAt θ z S₀)
    (htw : ∀ τ : Perm (Fin n), τ.IsSwap →
      IsConj z (swapIota T₀ θ τ : G) ∧ ¬ IsConj z (z * (swapIota T₀ θ τ : G))) :
    NearData z n where
  S := L ⊔ zpowers u₀
  ι := swapIota T₀ θ
  π := permHom T₀.toBase θ
  sq := T₀.cyc.mul_self
  ne_one := fun h1 => by
    have := T₀.cyc.order
    rw [h1, orderOf_one] at this
    omega
  le := T₀.le_centralizer
  π_ι σ := permOf_swapIota T₀ θ σ
  π_z := (permOf_eq_one_iff T₀.toBase θ (mem_centralizer_singleton_iff.2 rfl)).2
    (T₀.cyc.le T₀.cyc.mem)
  ker x hx := by
    have hK : (x : G) ∈ centralizer (L : Set G) := (permOf_eq_one_iff T₀.toBase θ x.2).1 hx
    have hQ : (x : G) ∈ Q := by
      rw [← hC]
      exact Subgroup.mem_inf.2 ⟨hK, x.2⟩
    exact eq_one_or_eq_of_card_eq_two T₀.cyc T₀.card hQ
  swap_mem τ hτ := by
    refine ⟨(htw τ hτ).1, fun h1 => ?_, ?_⟩
    · exact T₀.z_notMem (h1 ▸ (swapIota T₀ θ τ).2)
    · exact mem_centralizer_singleton_iff.1 (swapIota_mem_centralizer T₀ θ τ)
  near x hx hnear := by
    obtain ⟨g, hg⟩ := isConj_iff.1 hx.1
    have hsw : (permOf T₀.toBase θ x.2).IsSwap :=
      near_partner_swap T₀ θ hS₀ hkn hII x.2 hg hx.2.1 hnear
    refine ⟨hsw, ?_⟩
    rcases eq_swapIota_or_of_cent T₀ θ hC x.2 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hx.1) (htw _ hsw).2

end CFSG.OddStandard.AltStdCycTwo.Two.Exact
