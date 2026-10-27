module

public import CFSG.Quasithin.Vol2.Ch3zBlocks
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.ASHypK
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltPair
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltPlumb

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank G6

namespace B69K

variable {V : Type} [CommGroup V] [Finite V]

theorem not_alt_odd_five {X T M A L : Subgroup (MulAut V)} (hH : B69.CompHypK X T M A L) {m : ℕ}
    (hm : 5 ≤ m) (hodd : Odd m) (hnp : ¬ ∃ j : ℕ, m = 2 ^ j + 1) :
    ¬ IsAlt m (↥L ⧸ Subgroup.center ↥L) := by
  rintro ⟨e₀⟩
  obtain ⟨Y, _, _, K, T', M', hAS, ⟨e'⟩⟩ := asHyp_of_compHypK hH
  exact false_of_alt_pair hAS (by obtain ⟨c, hc⟩ := hodd; omega) (e'.symm.trans e₀)
    fun T'' hT'' => alt_pair_odd hm hodd hnp T'' hT''

theorem exists_two_pow_of_altShape {X T M A L : Subgroup (MulAut V)} (hH : B69.CompHypK X T M A L)
    {W : Subgroup V} {k : ℕ} (hk : 1 ≤ k) {π : Equiv.Perm (Fin (2 * k + 1)) →* ↥(L ⊔ A)}
    (hreal : (FFModel.symDn (2 * k + 1)).RealizesVia (L ⊔ A) W ⊥ π)
    (hL : L = (alternatingGroup (Fin (2 * k + 1))).map ((L ⊔ A).subtype.comp π)) :
    ∃ j : ℕ, 2 * k + 1 = 2 ^ j + 1 := by
  have hLc : CFSG.Open.IsComponentOf L X := hH.2.2.2.2.2.2.1
  obtain ⟨θ, _, hθ, -, -, -⟩ := CFSG.Quasithin.Ch3z.isSymCore_of_realizes' hreal
  have hπinj : Function.Injective π := fun a b hab =>
    θ.symm.injective ((hθ a).trans (hab.trans (hθ b).symm))
  have hf : Function.Injective ((L ⊔ A).subtype.comp π) :=
    (Subgroup.subtype_injective (L ⊔ A)).comp hπinj
  have hodd : Odd (2 * k + 1) := odd_two_mul_add_one k
  have hLperf : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hLc.2.2.1
  have hLnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hLc.2.2
  have hn5 : 5 ≤ 2 * k + 1 := by
    by_contra hlt
    have hk1 : k = 1 := by omega
    subst hk1
    refine Group.IsPerfect.not_isMulCommutative ↥L
      (IsMulCommutative.of_setLike_mul_comm fun a ha b hb => ?_)
    rw [hL] at ha hb
    obtain ⟨σ₁, hσ₁, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨σ₂, hσ₂, rfl⟩ := Subgroup.mem_map.1 hb
    have hcomm : ∀ a b : alternatingGroup (Fin (2 * 1 + 1)), a * b = b * a := by decide
    have := congrArg (fun x : alternatingGroup (Fin (2 * 1 + 1)) =>
        ((L ⊔ A).subtype.comp π) (x : Equiv.Perm (Fin (2 * 1 + 1))))
      (hcomm ⟨σ₁, hσ₁⟩ ⟨σ₂, hσ₂⟩)
    simpa using this
  have hcard : 4 ≤ Nat.card (Fin (2 * k + 1)) := by
    rw [Nat.card_fin]
    omega
  have e : ↥L ≃* alternatingGroup (Fin (2 * k + 1)) :=
    (MulEquiv.subgroupCongr hL).trans
      (Subgroup.equivMapOfInjective (alternatingGroup (Fin (2 * k + 1)))
        ((L ⊔ A).subtype.comp π) hf).symm
  have hcenter : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ Subgroup.center ↥(alternatingGroup (Fin (2 * k + 1))) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := Subgroup.mem_center_iff.mp hz (e.symm g)
      have h2 : e (e.symm g * z) = e (z * e.symm g) := by rw [h1]
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
      exact h2
    rw [alternatingGroup.center_eq_bot hcard, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    exact e.injective (by rw [hz', map_one])
  have hiso : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin (2 * k + 1)) :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans (QuotientGroup.quotientBot.trans e)
  by_contra hnp
  exact (not_alt_odd_five hH hn5 hodd hnp) ⟨hiso⟩

end B69K

end CFSG.Quasithin
