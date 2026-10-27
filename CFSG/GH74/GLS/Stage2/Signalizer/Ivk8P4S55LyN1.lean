module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55N1Core
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55PermStep
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55LyStar
public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.LyN1

open Subgroup CFSG CFSG.ABGLocalTools

theorem exists_conj_of_equiv {Y T : Type} [Group Y] [Group T] (e : Y ≃* T)
    (h : ∀ φ : MulAut T, ∃ g : T, φ = MulAut.conj g) (α : MulAut Y) :
    ∃ t : Y, α = MulAut.conj t := by
  obtain ⟨g, hg⟩ := h (MulAut.congr e α)
  refine ⟨e.symm g, ?_⟩
  ext y
  have h1 := congrArg (fun φ : MulAut T => φ (e y)) hg
  have h2 : (MulAut.congr e α) (e y) = e (α y) := by
    show e (α (e.symm (e y))) = e (α y)
    rw [MulEquiv.symm_apply_apply]
  simp only [h2, MulAut.conj_apply] at h1
  show α y = e.symm g * y * (e.symm g)⁻¹
  apply e.injective
  rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem center_eq_bot_of_simple_card {Y : Type*} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (hnp : ¬ (Nat.card Y).Prime) : Subgroup.center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · exfalso
    let _ : CommGroup Y := Group.commGroupOfCenterEqTop h
    exact hnp (IsSimpleGroup.prime_card (α := Y))

theorem ly_n1
    {Y : Type} [Group Y] [Finite Y] (hY : Blueprint.NativeSporadic.IsSporadic Y .Ly) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {b : MulAut Y} (hb : orderOf b = p) {R₀ : Subgroup Y}
    (hR₀ : IsSylowOf 2 R₀ ⊤)
    (hpg : IsPGroup p ↥(closure {c : MulAut Y | ∃ r ∈ R₀,
      c = MulAut.conj r * b * (MulAut.conj r)⁻¹})) :
    p = 3 ∧ ∃ τ y s : Y, b = MulAut.conj y ∧ orderOf τ = 2 ∧ orderOf y = 3 ∧ orderOf s = 7 ∧
      y * τ = τ * y ∧ s * τ = τ * s ∧ y * s = s * y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := id hY
  have hcard : Nat.card Y = 51765179004000000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Ly.card_Ly'
  have hfact : (Nat.card Y).factorization 2 = 8 := by
    rw [hcard, show (51765179004000000 : ℕ) = 2 ^ 8 * 202207730484375 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hs : IsSimpleGroup Y :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Ly.isSimpleGroup_Ly e
  have hZ : Subgroup.center Y = ⊥ :=
    center_eq_bot_of_simple_card hs (by rw [hcard]; norm_num)
  have hinj := N1Core.conj_injective hZ
  have hinnerT : ∀ φ : MulAut Blueprint.NativeSporadic.Ly, ∃ g : Blueprint.NativeSporadic.Ly,
      φ = MulAut.conj g := fun φ => by
    obtain ⟨g, hg⟩ := (Subgroup.eq_top_iff' _).mp
      CFSG.ComponentClassification.RestrictedStd.Spor.lyOuterTrivialInput φ
    exact ⟨g, hg.symm⟩
  obtain ⟨y, hy⟩ := exists_conj_of_equiv e hinnerT b
  obtain ⟨hy1, hyp, X, hXp, hyX, hN⟩ := N1Core.n1_core hb hpg hy hinj
  have hR₀card : Nat.card ↥R₀ = 2 ^ (7 + 1) := by
    have h1 := IsSylowOf.card_eq hR₀
    rw [Subgroup.card_top, hfact] at h1
    exact h1
  have hR₀ne : R₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hR₀card
    norm_num at hR₀card
  obtain ⟨τ, hτR, hτ2, hτc⟩ := Syl.exists_central_involution hR₀.isPGroup hR₀ne
  have hXC : X ≤ centralizer ({τ} : Set Y) :=
    WtP.ly_central hY hp2 hR₀card hτR hτ2 hτc hXp hN
  obtain ⟨-, hZc, ⟨E⟩⟩ :=
    CFSG.Sporadic.LySchreier.involution_centralizers_quasisimple ⟨e⟩ τ hτ2
  obtain ⟨-, hp3, s, hs7, hys, hsτ⟩ := PermStep.perm_step (n := 11) (e := 7) hp2
    (Or.inr ⟨rfl, rfl⟩) hR₀card hτR hτ2 hτc hZc E hXp hXC hN hyX hy1 hyp
  refine ⟨hp3, τ, y, s, hy, hτ2, ?_, hs7,
    Subgroup.mem_centralizer_singleton_iff.1 (hXC hyX), hsτ, hys⟩
  rw [← hp3]
  exact orderOf_eq_prime hyp hy1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.LyN1
