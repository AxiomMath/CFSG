module

public import CFSG.ClassicalInvolution.ModelFacts.ChevAutBasic
public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
public import CFSG.LieType.Steinberg.CentralExt.Split
public import CFSG.LieType.Steinberg.Isogeny.E6
public import CFSG.LieType.Steinberg.Isogeny.E7
public import CFSG.LieType.Steinberg.Minuscule.BruhatExtras
public import CFSG.LieType.Steinberg.Minuscule.ChevExtras
public import CFSG.LieType.TitsSimplicity.Core
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion

public section

namespace CFSG.ClassicalInvolution.ModelFacts.ChevAut

open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.CentralExt

theorem hasCentralPSplit_of_chevalleyExtras {K : Type} [Group K] {D : UniversalRootDatum K}
    {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    {x : (Fin D.rank → ℤ) → F → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D F x C O) (hB : HasBruhatDatum D) : HasCentralPSplit p K := by
  obtain ⟨n, H, hct, hext⟩ := hB
  intro E _ _ π hπ hker hC
  exact existsUnique_section_of_sl2_lift hct hext hE.param hE.rankOne hπ hker hC fun ρ => by
    obtain ⟨ρ', hρ', -⟩ := CFSG.SectionRank.EvenCover.sl2_existsUnique_lift hπ hker hC ρ
    exact ⟨ρ', fun g => congrArg (· g) hρ'⟩

section Datum

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem center_pow_eq_one
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) {m : ℕ}
    (hm : ∀ i, ∀ h ∈ H i, h ^ m = 1) : ∀ z ∈ Subgroup.center K, z ^ m = 1 := by
  intro z hz
  rw [CFSG.LieType.TitsSimplicity.center_eq_normalCore_borel hct hext hBU] at hz
  exact pow_eq_one_of_mem_iSup (fun i j h hh h' hh' => hext.torus_commute i j h hh h' hh') hm z
    (CFSG.LieType.TitsSimplicity.normalCore_borel_le_iSup hct hBU hz)

end Datum

section Param

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [CharP F p]
  {K : Type} [Group K] {D : UniversalRootDatum K} {x : (Fin D.rank → ℤ) → F → K}

theorem closure_of_isParametrization
    (hpar : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible)
      D.rootGroup x) (htop : ⨆ γ ∈ D.roots, D.rootGroup γ = ⊤) :
    Subgroup.closure {y : K | ∃ n : ℕ, orderOf y = p ^ n} = ⊤ :=
  closure_pElements_eq_top (S := D.roots) htop fun _ hγ => isPGroup_of_isParametrization hpar hγ

theorem simple_orderOf_of_isParametrization
    (hpar : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible)
      D.rootGroup x) (i : Fin D.rank) (c : F) :
    (∃ n : ℕ, orderOf (x (Pi.single i 1) c) = p ^ n) ∧
      ∃ n : ℕ, orderOf (x (-Pi.single i 1) c) = p ^ n := by
  have hΦ := isCTRootSystem D.isFiniteType D.divisible
  exact ⟨exists_orderOf_param hpar (hΦ.single_mem i) c,
    exists_orderOf_param hpar (CFSG.LieType.Steinberg.OfCartan.neg_mem_roots D.isFiniteType
      (hΦ.single_mem i)) c⟩

end Param

section Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (F : Type) [Field F]

theorem finite_minGroup [Finite F] : Finite ↥(hV.minGroup F) := by
  have : Finite (Module.End F (Fin D.d →₀ F)) := Module.finite_of_finite F
  infer_instance

theorem torus_pow_card_sub_one (i : Fin τ.rank) {h : hV.minGroup F} (hh : h ∈ hV.torus F i) :
    h ^ (Nat.card F - 1) = 1 := by
  obtain ⟨t, rfl⟩ := hh
  have ht : t ^ (Nat.card F - 1) = 1 := by
    have := pow_card_eq_one' (G := Fˣ) (x := t)
    rwa [Nat.card_units] at this
  change (hV.hHom F i t) ^ (Nat.card F - 1) = 1
  rw [← map_pow, ht, map_one]

end Minuscule

section E6

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny

variable (F : Type) [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]

theorem e6_hasCentralPSplit : HasCentralPSplit p ↥(e6Data_valid.minGroup F) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (e6Datum F).isFiniteType
    (Dv := (e6Datum F).divisible) rfl
  have hE := e6_chevalleyExtras F O _
    (e6Data_valid.commutatorFormula_commC F posDef_cartan_E6 _
      (roots_eq isFiniteType_cartan_E6) O)
  exact hasCentralPSplit_of_chevalleyExtras hE
    ⟨_, _, e6Datum_isCTGroupDatum F, e6Datum_steinbergExtras F⟩

theorem e6Isogeny_ker_le_center :
    (e6Isogeny F).ker ≤ Subgroup.center ↥(e6Data_valid.minGroup F) :=
  ker_le_center_of_isQuasisimple (isQuasisimple_e6 F) (e6Isogeny_ne_one F)

theorem e6Isogeny_not_dvd_card_ker : ¬ p ∣ Nat.card (e6Isogeny F).ker := by
  have := finite_minGroup e6Data_valid F
  refine not_dvd_card_of_forall_pow_card_sub_one (F := F) fun z hz => ?_
  exact center_pow_eq_one (e6Datum_isCTGroupDatum F) (e6Datum_steinbergExtras F)
    (e6Datum_bruhatExtras F) (fun i h hh => torus_pow_card_sub_one e6Data_valid F i hh) z
    (e6Isogeny_ker_le_center F hz)

end E6

section E7

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny

variable (F : Type) [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]

theorem e7_hasCentralPSplit : HasCentralPSplit p ↥(e7Data_valid.minGroup F) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (e7Datum F).isFiniteType
    (Dv := (e7Datum F).divisible) rfl
  have hE := e7_chevalleyExtras F O _
    (e7Data_valid.commutatorFormula_commC F posDef_cartan_E7 _
      (roots_eq isFiniteType_cartan_E7) O)
  exact hasCentralPSplit_of_chevalleyExtras hE
    ⟨_, _, e7Datum_isCTGroupDatum F, e7Datum_steinbergExtras F⟩

theorem e7Isogeny_ker_le_center :
    (e7Isogeny F).ker ≤ Subgroup.center ↥(e7Data_valid.minGroup F) :=
  ker_le_center_of_isQuasisimple (isQuasisimple_e7 F) (exists_e7Isogeny_ne_one F)

theorem e7Isogeny_not_dvd_card_ker : ¬ p ∣ Nat.card (e7Isogeny F).ker := by
  have := finite_minGroup e7Data_valid F
  refine not_dvd_card_of_forall_pow_card_sub_one (F := F) fun z hz => ?_
  exact center_pow_eq_one (e7Datum_isCTGroupDatum F) (e7Datum_steinbergExtras F)
    (e7Datum_bruhatExtras F) (fun i h hh => torus_pow_card_sub_one e7Data_valid F i hh) z
    (e7Isogeny_ker_le_center F hz)

end E7

end CFSG.ClassicalInvolution.ModelFacts.ChevAut
