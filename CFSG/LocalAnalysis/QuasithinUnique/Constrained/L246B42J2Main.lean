module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Dim
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalogBase

public section

namespace CFSG.QuasithinUnique.Bridge.J2Excl

open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Schreier CFSG.Blueprint CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

noncomputable def j2EquivC
    : NativeSporadic.Carrier .J2 ≃* ↥j2P := j2PermEquiv

theorem j2_aut_model
    : ∃ Φ : ↥j2R ≃* MulAut (NativeSporadic.Carrier .J2),
    ∀ s : NativeSporadic.Carrier .J2,
      Φ ⟨(j2EquivC s : Equiv.Perm (Fin 315)), j2P_le_R (j2EquivC s).2⟩ = MulAut.conj s := by
  obtain ⟨e, he, -⟩ := ctuc_j2_full_automorphism_permutation_model
  refine ⟨e.trans (MulAut.congr (G := ↥j2P) (H := NativeSporadic.Carrier .J2) j2EquivC.symm),
    fun s => ?_⟩
  refine MulEquiv.ext fun s' => ?_
  have h1 : e ⟨(j2EquivC s : Equiv.Perm (Fin 315)), j2P_le_R (j2EquivC s).2⟩ (j2EquivC s') =
      j2EquivC (s * s' * s⁻¹) := by
    apply Subtype.ext
    rw [he]
    simp [map_mul, map_inv]
  simp only [MulEquiv.trans_apply, MulAut.congr_apply, MulEquiv.symm_symm, MulAut.conj_apply, h1,
    MulEquiv.symm_apply_apply]

theorem j2_genSub
    : ∀ B : Subgroup (MulAut (NativeSporadic.Carrier .J2)),
    (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → B ≠ ⊥ →
    ∃ cs : List (MulAut (NativeSporadic.Carrier .J2)),
      (∀ c ∈ cs, c ∈ (MulAut.conj : NativeSporadic.Carrier .J2 →*
        MulAut (NativeSporadic.Carrier .J2)).range) ∧ Nat.card B ^ cs.length < 2 ^ 12 ∧
      ∀ s : NativeSporadic.Carrier .J2,
        MulAut.conj s ∈ Subgroup.closure {y | ∃ c ∈ cs, ∃ b ∈ B, y = c * b * c⁻¹} := by
  obtain ⟨Φ, hΦ⟩ := j2_aut_model
  exact genSub_of_equiv (G := Equiv.Perm (Fin 315)) (H := j2R) (A := j2P) j2P_le_R Φ j2EquivC hΦ
    (ρ := 12) j2_genSub_R

theorem j2_frob
    : ∃ x g : Equiv.Perm (Fin 315), x ∈ j2P ∧ g ∈ j2P ∧ x ^ 5 = 1 ∧ x ≠ 1 ∧
    x * (g * x * g⁻¹) = (g * x * g⁻¹) * x ∧
    g * (g * x * g⁻¹) * g⁻¹ = (x * (g * x * g⁻¹))⁻¹ := by
  obtain ⟨x, hxP, hx⟩ := regIn_j2P.word j2FrobXWord
  obtain ⟨g, hgP, hg⟩ := regIn_j2P.word j2FrobGWord
  have hy : PRep 315 j2FY (g * x * g⁻¹) := (hg.mul hx).mul hg.inv
  have hxy := hx.mul hy
  have hyx := hy.mul hx
  have hh := j2_frob_check
  simp only [j2FrobOK, Bool.and_eq_true, Bool.not_eq_true'] at hh
  obtain ⟨⟨⟨h5, h1⟩, hc⟩, hrel⟩ := hh
  refine ⟨x, g, hxP, hgP, ?_, ?_, ?_, ?_⟩
  · have h5' := (eqA_iff ((hx.mul hx).mul ((hx.mul hx).mul hx)).1 rep_idA).1 h5
    have e : x ^ 5 = x * x * (x * x * x) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e]
    exact h5'
  · intro h
    have : eqA 315 j2FX.1 (idA 315) = true := (eqA_iff hx.1 rep_idA).2 h
    rw [this] at h1
    exact absurd h1 (by simp)
  · exact (eqA_iff hxy.1 hyx.1).1 hc
  · have hr := (eqA_iff ((hg.mul hy).mul hg.inv).1 (hxy.inv).1).1 hrel
    exact hr

theorem j2_dim
    (V : Type) [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    (σ : NativeSporadic.Carrier .J2 →* MulAut V) (hσ : Function.Injective σ) :
    2 ^ 12 ≤ Nat.card V := by
  obtain ⟨x, g, hxP, hgP, hx5, hx1, hcomm, hrel⟩ := j2_frob
  let ψ : NativeSporadic.Carrier .J2 →* Equiv.Perm (Fin 315) :=
    j2P.subtype.comp j2EquivC.toMonoidHom
  have hψ : Function.Injective ψ := Subtype.val_injective.comp j2EquivC.injective
  set xS : NativeSporadic.Carrier .J2 := j2EquivC.symm ⟨x, hxP⟩ with hxS
  set gS : NativeSporadic.Carrier .J2 := j2EquivC.symm ⟨g, hgP⟩ with hgS
  have hψx : ψ xS = x := by simp [ψ, hxS]
  have hψg : ψ gS = g := by simp [ψ, hgS]
  have hx5S : xS ^ 5 = 1 := hψ (by rw [map_pow, hψx, hx5, map_one])
  have hx1S : xS ≠ 1 := fun h => hx1 (by rw [← hψx, h, map_one])
  have hcommS : xS * (gS * xS * gS⁻¹) = (gS * xS * gS⁻¹) * xS :=
    hψ (by simp only [map_mul, map_inv, hψx, hψg]; exact hcomm)
  have hrelS : gS * (gS * xS * gS⁻¹) * gS⁻¹ = (xS * (gS * xS * gS⁻¹))⁻¹ :=
    hψ (by simp only [map_mul, map_inv, hψx, hψg]; exact hrel)
  refine two_pow_twelve_le_card hV (x := σ xS) (g := σ gS) ?_ ?_ ?_ ?_
  · rw [← map_pow, hx5S, map_one]
  · have := congrArg σ hcommS
    simp only [map_mul, map_inv] at this
    exact this
  · have := congrArg σ hrelS
    simp only [map_mul, map_inv] at this
    exact this
  · intro h
    exact hx1S (hσ (h.trans (map_one σ).symm))

theorem j2_cover
    (E : Type) [Group E] [Finite E] [Group.IsPerfect E]
    (π : E →* NativeSporadic.Carrier .J2) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ :=
  CFSG.SectionRank.J2_perfect_odd_cover_trivial π hπ hC hodd

theorem sporadicExclusion_J2
    : X1.SporadicExclusion .J2 := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hE hEne hEel _
  have : Nontrivial (NativeSporadic.Carrier .J2) := CFSG.Sporadic.J2.fam_j2_simplicity.2.1
  exact weight_lt_of_genSub hW hq.1 hirr hE hEne hEel e (ρ := 12)
    (fun E _ _ _ π hπ hC hodd => j2_cover E π hπ hC hodd) j2_genSub j2_dim

end CFSG.QuasithinUnique.Bridge.J2Excl
