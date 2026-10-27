module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoTwist
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarFrame

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdBal

section Near

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z u : G}

theorem exists_untwisted (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {S₀ : Finset (Fin n)} (hk : S₀.card = 3 ∨ S₀.card = 4)
    (hkn : S₀.card + 7 ≤ n) (hII : CaseIIAt e z S₀) :
    ∃ (u₀ : G) (T₀ : ShapeTwo L Q z u₀), ∀ τ : Perm (Fin n), τ.IsSwap →
      IsConj z (swapIota h d T₀ e τ : G) ∧ ¬ IsConj z (z * (swapIota h d T₀ e τ : G)) := by
  have hz2 : z * z = 1 := d.mul_self
  obtain ⟨c, hc, htw⟩ := caseII_twist h d T e hk hkn hII
  rcases hc with hc | hc
  · rw [hc] at htw
    exact ⟨u, T, fun τ hτ => by simpa using htw τ hτ⟩
  · rw [hc] at htw
    obtain ⟨hcent', hout', hsq'⟩ := shapeTwo_mul_z d T.cent T.outer T.sq
    have T' : ShapeTwo L Q z (u * z) := ⟨T.card, hcent', hout', hsq'⟩
    refine ⟨u * z, T', fun τ hτ => ?_⟩
    obtain ⟨h1, h2⟩ := htw τ hτ
    rw [hz2, one_mul] at h2
    have h3 := eq_swapIota_or h d T e (swapIota_mem_centralizer h d T' e τ)
    rw [permOf_swapIota h d T' e τ] at h3
    rcases h3 with h3 | h3
    · exact absurd h3 (swapIota_mul_z_ne h d T T' e hτ.sign_eq)
    · rw [h3, ← mul_assoc, hz2, one_mul]
      exact ⟨h1, h2⟩

@[expose] noncomputable def permHom (h : Setting G L n) (d : Cyc L Q z)
    (e : L ≃* alternatingGroup (Fin n)) : centralizer ({z} : Set G) →* Perm (Fin n) :=
  (rho e h.hn).comp (Subgroup.inclusion (AltStdBal.centralizer_le_normalizer h d))

theorem permHom_apply (h : Setting G L n) (d : Cyc L Q z) (e : L ≃* alternatingGroup (Fin n))
    (x : centralizer ({z} : Set G)) : permHom h d e x = permOf h d e x.2 := rfl

@[expose] noncomputable def nearData_of_untwisted (h : Setting G L n) (d : Cyc L Q z) {u₀ : G}
    (T₀ : ShapeTwo L Q z u₀) (e : L ≃* alternatingGroup (Fin n)) {S₀ : Finset (Fin n)}
    (hS₀ : S₀.card = 3 ∨ S₀.card = 4) (hkn : S₀.card + 7 ≤ n) (hII : CaseIIAt e z S₀)
    (htw : ∀ τ : Perm (Fin n), τ.IsSwap →
      IsConj z (swapIota h d T₀ e τ : G) ∧ ¬ IsConj z (z * (swapIota h d T₀ e τ : G))) :
    NearData z n where
  S := L ⊔ zpowers u₀
  ι := swapIota h d T₀ e
  π := permHom h d e
  sq := d.mul_self
  ne_one := fun h1 => by
    have := d.order
    rw [h1, orderOf_one] at this
    omega
  le := sup_le (le_centralizer_single h d) (zpowers_le.2 T₀.cent)
  π_ι σ := permOf_swapIota h d T₀ e σ
  π_z := permOf_self h d e (mem_centralizer_singleton_iff.2 rfl)
  ker x hx := by
    have hK : (x : G) ∈ centralizer (L : Set G) :=
      (rho_eq_one_iff e h.hn ⟨x, AltStdBal.centralizer_le_normalizer h d x.2⟩).1 hx
    have hQ : (x : G) ∈ Q := by
      rw [← cent_inf_eq h d]
      exact Subgroup.mem_inf.2 ⟨hK, x.2⟩
    exact eq_one_or_eq_of_card_eq_two d T₀.card hQ
  swap_mem τ hτ := by
    refine ⟨(htw τ hτ).1, fun h1 => ?_, ?_⟩
    · exact z_notMem_swapComplement h d T₀.cent T₀.outer T₀.sq (h1 ▸ (swapIota h d T₀ e τ).2)
    · exact mem_centralizer_singleton_iff.1 (swapIota_mem_centralizer h d T₀ e τ)
  near x hx hnear := by
    obtain ⟨g, hg⟩ := isConj_iff.1 hx.1
    have hsw : (permOf h d e x.2).IsSwap :=
      near_partner_swap h d T₀ e hS₀ hkn hII x.2 hg hx.2.1 hnear
    refine ⟨hsw, ?_⟩
    rcases eq_swapIota_or h d T₀ e x.2 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hx.1) (htw _ hsw).2

end Near

end CFSG.OddStandard.AltStdSec
