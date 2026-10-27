module

public import CFSG.Quasithin.H13.A5S1328
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem le_normalizer_of_cComp_F4 (h1222 : Stmt12_2_2_F4) {H K : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H) (hKc : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hZK : ⁅quasithinOmegaOneCenter T, K⁆ ≠ ⊥) : T ≤ Subgroup.normalizer (K : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hH.1.1

  have hKloc : quasithinIsLocal T K :=
    ⟨S.isPGroup_T, cComp_subset_lFamily hTH hKc,
      (isSylowTwoOf_of_le S.h13.sylow le_sup_right).2.2, by rw [← hHK]; exact hH.1.2⟩

  obtain ⟨K', hK'⟩ := (Set.toFinite {X : Subgroup G | quasithinIsLocal T X ∧ K ≤ X}).exists_maximal
    ⟨K, hKloc, le_rfl⟩
  have hKK' : K ≤ K' := hK'.1.2
  have hK'max : quasithinIsMaximalLocal T K' :=
    ⟨hK'.1.1, fun X hX hK'X => le_antisymm (hK'.2 ⟨hX, hKK'.trans hK'X⟩ hK'X) hK'X⟩

  have hZK' : ⁅quasithinOmegaOneCenter T, K'⁆ ≠ ⊥ := fun h =>
    hZK (le_bot_iff.mp (h ▸ Subgroup.commutator_mono le_rfl hKK'))
  have hK'f : quasithinIsFaithfulLocal T K' :=
    Vol2.Ch11.SecS.isFaithfulLocal_of_omegaOneCenter S.h13.qtke S.h13.sylow hK'max.1 hZK'
  obtain ⟨e⟩ := (quasithinO2QuotientIso_iff K' _).1 (S.h13.a5 S.a5 K' hK'f)
  have hq : CFSG.IsQuasisimple (↥K' ⧸ CFSG.pCore 2 ↥K') :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm isQuasisimple_alt_five
  have hTK' : T ≤ Subgroup.normalizer (K' : Set G) := by
    rcases h1222 G T S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow with h | h
    · exact absurd h S.not_alt12_2_2
    · exact (h K' hK'max hK'f hq).1

  by_contra hTK
  obtain ⟨t, htT, htN⟩ := Set.not_subset.mp hTK
  set Kt : Subgroup G := conjSub t K with hKtdef
  have hKt : Kt ∈ cComp H := conjSub_mem_cComp_of_mem hKc (hTH htT)
  have hne : K ≠ Kt := by
    intro h
    apply htN
    refine E1.LiftS5.mem_normalizer_of_conj_le fun k hk => ?_
    rw [h]
    exact Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
  have hKtK' : Kt ≤ K' := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    exact (Subgroup.mem_normalizer_iff.mp (hTK' htT) k).mp (hKK' hk)

  set Φ : ↥K' →* ↥(alternatingGroup (Fin 5)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K')) with hΦ
  have hΦker : Φ.ker = CFSG.pCore 2 ↥K' := by
    ext x
    simp [hΦ]
  have hsurj : ∀ X : Subgroup G, X ∈ cComp H → ∀ hX : X ≤ K', ∀ σ : alternatingGroup (Fin 5),
      ∃ x : ↥X, Φ (Subgroup.inclusion hX x) = σ := by
    intro X hXc hX σ
    have hker : Group.IsSolvable ↥(Φ.comp (Subgroup.inclusion hX)).ker := by
      rw [← MonoidHom.comap_ker, hΦker]
      have hp : IsPGroup 2 ↥((CFSG.pCore 2 ↥K').comap (Subgroup.inclusion hX)) :=
        (CFSG.pCore_isPGroup (p := 2) (G := ↥K')).comap_of_injective _
          (Subgroup.inclusion_injective hX)
      have := hp.isNilpotent
      infer_instance
    have htop := range_eq_top_of_not_isSolvable _ hker (not_isSolvable_of_mem_cComp hXc)
    have hσ : σ ∈ (Φ.comp (Subgroup.inclusion hX)).range := by rw [htop]; trivial
    obtain ⟨x, hx⟩ := hσ
    exact ⟨x, hx⟩

  have hcK' : ⁅K, Kt⁆ ≤ K' := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact K'.mul_mem (K'.mul_mem (K'.mul_mem (hKK' ha) (hKtK' hb)) (K'.inv_mem (hKK' ha)))
      (K'.inv_mem (hKtK' hb))
  have hcs : Group.IsSolvable ↥⁅K, Kt⁆ := by
    have hR : Group.IsSolvable ↥((CFSG.solvableRadical ↥H).map H.subtype) := by
      have : Group.IsSolvable ↥(CFSG.solvableRadical ↥H) := A3.solvableRadical_isSolvable
      have h1 : Group.IsSolvable ↥((H.subtype.comp (CFSG.solvableRadical ↥H).subtype).range) :=
        Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective _)
      rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h1
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (commutator_le_solvableRadical hKc hKt hne))
  set g : ↥⁅K, Kt⁆ →* ↥(alternatingGroup (Fin 5)) := Φ.comp (Subgroup.inclusion hcK') with hg
  have hgsurj : Function.Surjective g := by
    rw [← MonoidHom.range_eq_top, eq_top_iff,
      ← commutator_alternatingGroup_eq_top (α := Fin 5) (by simp),
      commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨x, rfl⟩ := hsurj K hKc hKK' a
    obtain ⟨y, rfl⟩ := hsurj Kt hKt hKtK' b
    refine ⟨⟨⁅(x : G), (y : G)⁆, Subgroup.commutator_mem_commutator x.2 y.2⟩, ?_⟩
    rw [hg, MonoidHom.comp_apply, ← map_commutatorElement]
    rfl
  exact E1.LiftS5.not_isSolvable_alt (Group.isSolvable_of_surjective hgsurj)

end Setting

@[expose] def Res1328a_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (_ : Setting G T L V)
    (H K : Subgroup G), IsHStar T (Subgroup.normalizer (L : Set G)) H →
    ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) → K ∈ cComp H →
    H = K ⊔ T → T ≤ Subgroup.normalizer (K : Set G) →
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) →
    E1.LiftS5.RootFourLiftQuot T K

end CFSG.Quasithin.H13.A5
