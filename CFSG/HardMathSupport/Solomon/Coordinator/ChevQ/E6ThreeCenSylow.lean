module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenHat
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadMonoCalc
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeToral

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar (e6Inndiag)
open CFSG.StandardType.TableBExc.E6Three (hatGroup hatAut monoHat psiHat psiHat_eq xHat mem_xHat
  mapsRootLines_rootDiagUnit finite_hatGroup not_three_dvd_index_xHat modelHomE6)

theorem cen_mulAut_congr_apply {G : Type*} [Group G] (φ X : MulAut G) :
    MulAut.congr φ X = φ * X * φ⁻¹ :=
  MulEquiv.ext fun _ => rfl

section Mono


theorem cen_bmMono_hatAut {K : Type} [Field K] {y : hatGroup .E6 K}
    (hym : (y : ModGL Tag.E6 K) ∈ monoHat .E6 K) :
    BmMono (hatAut .E6 K y) (psiHat .E6 K ⟨y, hym⟩) := by
  obtain ⟨n, hn, a, hna⟩ := id hym
  have hmaps : MapsRootLines n (weylQuotientHom Tag.E6 K ⟨n, hn⟩) :=
    mapsRootLines_weylQuotientHom ⟨n, hn⟩
  have hψ : psiHat .E6 K ⟨y, hym⟩ = weylQuotientHom Tag.E6 K ⟨n, hn⟩ := by
    refine psiHat_eq ?_
    have h := hmaps.mul (mapsRootLines_rootDiagUnit (K := K) a)
    rw [mul_one, ← hna] at h
    exact h
  rw [hψ]
  refine ⟨⟨n, monomialSubgroup_le_adjointGroup' hn⟩, a, hn, hmaps, ?_⟩
  refine MulEquiv.ext fun g => Subtype.ext ?_
  change (y : ModGL Tag.E6 K) * g * (y : ModGL Tag.E6 K)⁻¹ =
    n * (rootDiagUnit Tag.E6 a * g * (rootDiagUnit Tag.E6 a)⁻¹) * n⁻¹
  rw [hna]
  group

end Mono

section Sylow


theorem e6_exists_conj_bmMono_sylow {K : Type} [Field K] [Finite K] (hK : 3 ∣ Nat.card K - 1)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE3 : IsPGroup 3 E)
    (hED : E ≤ e6Inndiag K) :
    ∃ φ ∈ e6Inndiag K, ∀ X ∈ E.map (MulAut.congr φ).toMonoidHom,
      ∃ v ∈ modelHomE6.range, BmMono X v := by
  have := Fact.mk Nat.prime_three
  have : Finite (hatGroup .E6 K) := finite_hatGroup
  have hEκ : E ≤ (hatAut .E6 K).range := by
    rw [cen_range_hatAut]
    exact hED
  set Y : Subgroup (hatGroup .E6 K) := E.comap (hatAut .E6 K) with hY
  set f : Y →* E := ((hatAut .E6 K).comp Y.subtype).codRestrict E (fun y => y.2) with hf
  have hfs : Function.Surjective f := by
    rintro ⟨φ, hφ⟩
    obtain ⟨x, rfl⟩ := hEκ hφ
    exact ⟨⟨x, hφ⟩, rfl⟩
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow 3 Y))
  have hEp : IsPGroup 3 (⊤ : Subgroup E) := fun g => by
    obtain ⟨k, hk⟩ := hE3 g.1
    exact ⟨k, Subtype.ext hk⟩
  have hQ : (Q₀ : Subgroup Y).map f = ⊤ :=
    ((Q₀.mapSurjective hfs).is_maximal' hEp le_top).symm
  set P : Subgroup (hatGroup .E6 K) := (Q₀ : Subgroup Y).map Y.subtype with hP
  have hP3 : IsPGroup 3 P := Q₀.isPGroup'.map _
  have hPE : P.map (hatAut .E6 K) = E := by
    have hcomp : (hatAut .E6 K).comp Y.subtype = E.subtype.comp f := MonoidHom.ext fun _ => rfl
    rw [hP, Subgroup.map_map, hcomp, ← Subgroup.map_map, hQ, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  obtain ⟨c, hc⟩ := CFSG.StandardType.TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_three
    (not_three_dvd_index_xHat hK) hP3
  refine ⟨hatAut .E6 K c, (cen_range_hatAut (K := K)).le ⟨c, rfl⟩, ?_⟩
  rintro _ ⟨X₀, hX₀, rfl⟩
  rw [← hPE] at hX₀
  obtain ⟨p, hp, rfl⟩ := hX₀
  have hy : ((c * p * c⁻¹ : hatGroup .E6 K) : ModGL Tag.E6 K) ∈ xHat .E6 K modelHomE6.range :=
    Subgroup.mem_subgroupOf.mp (hc ⟨p, hp, rfl⟩)
  obtain ⟨hym, hyS⟩ := mem_xHat.mp hy
  refine ⟨psiHat .E6 K ⟨_, hym⟩, hyS, ?_⟩
  have hX : (MulAut.congr (hatAut .E6 K c)).toMonoidHom (hatAut .E6 K p) =
      hatAut .E6 K (c * p * c⁻¹) := by
    rw [map_mul, map_mul, map_inv]
    exact cen_mulAut_congr_apply _ _
  rw [hX]
  exact cen_bmMono_hatAut hym

end Sylow

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
