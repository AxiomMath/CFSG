module

public import CFSG.LieType.TitsSimplicity.LeviDatum

public section

namespace CFSG.LieType.TitsSimplicity.Levi

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem.Restrict

variable {G : Type*} [Group G] {D : UniversalRootDatum G} {m : ℕ} {e : Fin m → Fin D.rank}
  (he : Function.Injective e) {n : Fin D.rank → G} {H : Fin D.rank → Subgroup G}
  (hdiv : D.divisible = ∅)

set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType

variable (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)

include hct hdiv in
theorem restrict_bruhatExtras (hBU : BruhatExtras D H) :
    BruhatExtras (restrict D he) (HC D H e) := by
  have hroot : ∀ γ ∈ (restrict D he).roots, ext e γ ∈ D.roots :=
    fun γ hγ => (restrict_roots he hdiv γ).1 hγ
  have hht : ∀ γ : Fin m → ℤ, ht (ext e γ) = ht γ := fun γ => sum_ext he γ
  have hB : borel (restrict D he) (HC D H e) ≤ (borel D H).comap (leviC D e).subtype := by
    refine sup_le (iSup_le fun i x hx => ?_) (iSup₂_le fun γ hγ x hx => ?_)
    · exact iSup_le_borel (le_iSup H (e i) hx)
    · exact rootGroup_le_borel (hroot γ hγ.1) (lt_of_lt_of_eq hγ.2 (hht γ).symm) hx
  have hU : negUnipotent (restrict D he) ≤ (negUnipotent D).comap (leviC D e).subtype :=
    iSup₂_le fun γ hγ x hx =>
      rootGroup_le_negUnipotent (hroot γ hγ.1) (lt_of_eq_of_lt (hht γ) hγ.2) hx
  refine ⟨eq_bot_iff.2 fun x hx => ?_⟩
  have h1 : (x : G) ∈ borel D H ⊓ negUnipotent D := ⟨hB hx.1, hU hx.2⟩
  rw [hBU.borel_inf_negUnipotent, Subgroup.mem_bot] at h1
  exact Subtype.ext h1

include hct hdiv in
theorem restrict_rootGroupCommutators (hE : RootGroupCommutators D) :
    RootGroupCommutators (restrict D he) where
  commutator_le γ hγ h2 := absurd h2 (two_smul_notMem_roots (D := restrict D he) rfl hγ)
  commutator_eq_bot γ hγ _ := by
    have hγ' : ext e γ ∈ D.roots := (restrict_roots he hdiv γ).1 hγ
    have hE' := hE.commutator_eq_bot _ hγ' (two_smul_notMem_roots hdiv hγ')
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    have hx' : (x : G) ∈ D.rootGroup (ext e γ) := hx
    have hy' : (y : G) ∈ D.rootGroup (ext e γ) := hy
    have hc := Subgroup.commutator_mem_commutator hx' hy'
    rw [hE', Subgroup.mem_bot] at hc
    exact Subtype.ext hc
  commutator_two_smul_eq_bot γ hγ h2 :=
    absurd h2 (two_smul_notMem_roots (D := restrict D he) rfl hγ)

end CFSG.LieType.TitsSimplicity.Levi
