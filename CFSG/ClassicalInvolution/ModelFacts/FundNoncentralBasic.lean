module

public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
public import CFSG.LieType.Steinberg.BruhatWeyl
public import CFSG.LieType.CurtisTits.Symplectic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
open scoped commutatorElement

section Quasisimple

theorem mem_center_of_commutators_mem_center {K : Type*} [Group K]
    (hK : CFSG.Open.IsQuasisimple K) {r : K}
    (hr : ∀ y : K, r * y * r⁻¹ * y⁻¹ ∈ Subgroup.center K) : r ∈ Subgroup.center K := by
  obtain ⟨hcomm, hsimple⟩ := hK
  have hC : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (K ⧸ Subgroup.center K))
      with h | h
    · exact h
    · exfalso
      have hle : commutator K ≤ Subgroup.center K := by
        rw [commutator_def]
        refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
        have hb : (b : K ⧸ Subgroup.center K) ∈ Subgroup.center (K ⧸ Subgroup.center K) := by
          rw [h]; trivial
        have h1 := Subgroup.mem_center_iff.mp hb (a : K ⧸ Subgroup.center K)
        rw [← QuotientGroup.eq_one_iff]
        have h3 : ((⁅a, b⁆ : K) : K ⧸ Subgroup.center K) =
            ⁅(a : K ⧸ Subgroup.center K), (b : K ⧸ Subgroup.center K)⁆ := by
          simp [commutatorElement_def]
        rw [h3, commutatorElement_eq_one_iff_mul_comm]
        exact h1
      rw [hcomm] at hle
      have htop : Subgroup.center K = ⊤ := top_le_iff.mp hle
      have hsub : Subsingleton (K ⧸ Subgroup.center K) := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
        rw [QuotientGroup.eq, htop]
        trivial
      exact not_subsingleton _ hsub
  have hmem : (r : K ⧸ Subgroup.center K) ∈ Subgroup.center (K ⧸ Subgroup.center K) := by
    rw [Subgroup.mem_center_iff]
    intro y'
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y'
    have h2 : ((⁅r, y⁆ : K) : K ⧸ Subgroup.center K) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hr y)
    have h3 : ((⁅r, y⁆ : K) : K ⧸ Subgroup.center K) =
        ⁅(r : K ⧸ Subgroup.center K), (y : K ⧸ Subgroup.center K)⁆ := by
      simp [commutatorElement_def]
    rw [h3, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2.symm
  rw [hC] at hmem
  exact (QuotientGroup.eq_one_iff r).mp hmem

end Quasisimple

section RankOne

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem mem_torus_of_mem_center_of_mem_rankOne
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {i : Fin D.rank} {r : K} (hr : r ∈ Subgroup.center K)
    (hri : r ∈ rankOne D.rootGroup i) : r ∈ H i := by
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := Or.inl ⟨1, i, by simp⟩
  have hα' : -(Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    OfCartan.neg_mem_roots D.isFiniteType hα
  have hc : ∀ x : K, r * x * r⁻¹ = x := fun x => by
    rw [← (Subgroup.mem_center_iff.mp hr x), mul_assoc, mul_inv_cancel, mul_one]
  rcases hext.rankOne_bruhat i r hri with ⟨h, hh, u, hu, e⟩ | ⟨u, hu, h, hh, v, hv, e⟩
  ·
    have hu1 : u = 1 := by
      refine hext.eq_one_of_mem_normalizer i u hu ?_
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have e2 : u * x * u⁻¹ = h⁻¹ * x * h := by
        have e1 : u = h⁻¹ * r := by rw [e]; group
        rw [e1]
        calc (h⁻¹ * r) * x * (h⁻¹ * r)⁻¹ = h⁻¹ * (r * x * r⁻¹) * h := by group
          _ = h⁻¹ * x * h := by rw [hc x]
      rw [e2]
      constructor
      · intro hx
        have := hct.H_conj_mem i _ hα' h⁻¹ (inv_mem hh) x hx
        simpa using this
      · intro hx
        have := hct.H_conj_mem i _ hα' h hh _ hx
        simpa [mul_assoc] using this
    rw [e, hu1, mul_one]
    exact hh
  ·
    exfalso
    have hbot : D.rootGroup (Pi.single i 1) = ⊥ := by
      refine eq_bot_iff.mpr fun x hx => ?_
      rw [Subgroup.mem_bot]
      have hvx : v * x * v⁻¹ ∈ D.rootGroup (Pi.single i 1) := mul_mem (mul_mem hv hx) (inv_mem hv)
      have hx' : h * (v * x * v⁻¹) * h⁻¹ ∈ D.rootGroup (Pi.single i 1) :=
        hct.H_conj_mem i _ hα h hh _ hvx
      have hy : n i * (h * (v * x * v⁻¹) * h⁻¹) * (n i)⁻¹ ∈
          D.rootGroup (-Pi.single i 1) := by
        have := hct.conj_mem i _ hα _ hx'
        rwa [weylAction_simple, reflection_single_self (D.isFiniteType.apply_self i)] at this
      have key : n i * (h * (v * x * v⁻¹) * h⁻¹) * (n i)⁻¹ = u⁻¹ * x * u := by
        have h1 : u * (n i * (h * (v * x * v⁻¹) * h⁻¹) * (n i)⁻¹) * u⁻¹ = x := by
          calc u * (n i * (h * (v * x * v⁻¹) * h⁻¹) * (n i)⁻¹) * u⁻¹ = r * x * r⁻¹ := by
                rw [e]; group
            _ = x := hc x
        calc n i * (h * (v * x * v⁻¹) * h⁻¹) * (n i)⁻¹
            = u⁻¹ * (u * (n i * (h * (v * x * v⁻¹) * h⁻¹) * (n i)⁻¹) * u⁻¹) * u := by group
          _ = u⁻¹ * x * u := by rw [h1]
      have hy' : n i * (h * (v * x * v⁻¹) * h⁻¹) * (n i)⁻¹ ∈ D.rootGroup (Pi.single i 1) := by
        rw [key]
        exact mul_mem (mul_mem (inv_mem hu) hx) hu
      have hy1 : n i * (h * (v * x * v⁻¹) * h⁻¹) * (n i)⁻¹ = 1 := by
        have hmem : n i * (h * (v * x * v⁻¹) * h⁻¹) * (n i)⁻¹ ∈
            posUnipotent D ⊓ negUnipotent D :=
          ⟨rootGroup_le_posUnipotent hα (ht_single_pos i) hy',
            rootGroup_le_negUnipotent hα' (by rw [ht_neg, ht_single]; norm_num) hy⟩
        rw [posUnipotent_inf_negUnipotent hext] at hmem
        exact hmem
      have h2 : h * (v * x * v⁻¹) * h⁻¹ = 1 := by
        have := congrArg (fun z => (n i)⁻¹ * z * n i) hy1
        simpa [mul_assoc] using this
      have h3 : v * x * v⁻¹ = 1 := by
        have := congrArg (fun z => h⁻¹ * z * h) h2
        simpa [mul_assoc] using this
      have h4 := congrArg (fun z => v⁻¹ * z * v) h3
      simpa [mul_assoc] using h4
    exact hext.ne_bot _ hα hbot

theorem eq_one_of_mem_center_of_mem_rankOne
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {i j : Fin D.rank} (hij : i ≠ j)
    (hconj : ∃ g : K, (rankOne D.rootGroup i).map (MulAut.conj g).toMonoidHom =
      rankOne D.rootGroup j)
    {r : K} (hr : r ∈ Subgroup.center K) (hri : r ∈ rankOne D.rootGroup i) : r = 1 := by
  obtain ⟨g, hg⟩ := hconj
  have hrj : r ∈ rankOne D.rootGroup j := by
    rw [← hg]
    refine ⟨r, hri, ?_⟩
    show g * r * g⁻¹ = r
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_center_iff.mp hr g
  have h1 := mem_torus_of_mem_center_of_mem_rankOne hct hext hr hri
  have h2 := mem_torus_of_mem_center_of_mem_rankOne hct hext hr hrj
  exact Subgroup.disjoint_def.mp (hext.torus_iSupIndep.pairwiseDisjoint hij) h1 h2

end RankOne

end CFSG.ClassicalInvolution.ModelFacts
