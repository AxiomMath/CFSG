module

public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
public import CFSG.LieType.CurtisTits.ExceptionalModel
public import CFSG.LieType.Steinberg.Exceptional.Universal
public import CFSG.LieType.Chevalley.NativeTorus
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
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123

public section

namespace CFSG.LieType.CurtisTits

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Minuscule

universe w

variable (p f : ℕ) [Fact p.Prime]

theorem exists_ne_one_adjointGroup (τ : Tag) (K : Type) [Field K] (hr : 0 < τ.rank) :
    ∃ x : ↥(adjointGroup τ K), x ≠ 1 := by
  let i : Fin τ.rank := ⟨0, hr⟩
  refine ⟨⟨xUnit τ K i 1, Subgroup.subset_closure ⟨i, 1, Or.inl rfl⟩⟩, fun h => ?_⟩
  have h1 : (xOp τ K i 1) (rootVec τ K (-Pi.single i 1)) = rootVec τ K (-Pi.single i 1) := by
    have := congrArg (fun g : ↥(adjointGroup τ K) =>
      ((g : ModGL τ K) : Module.End K (RootModule τ K)) (rootVec τ K (-Pi.single i 1))) h
    simpa [xUnit] using this
  rw [CFSG.LieType.Chevalley.xOp_rootVec_neg_single', one_smul, one_pow, one_smul] at h1
  have h2 := congrArg (fun v : RootModule τ K => v (Sum.inl i)) h1
  simp only [rootVec, hVec, dite_eq_left_of_eq_true (eq_true (isRoot_neg_single τ i)),
    dite_eq_left_of_eq_true (eq_true (IsRoot.basis (τ := τ) i)), Finsupp.add_apply,
    Finsupp.single_apply, reduceCtorEq, ite_false, ite_true] at h2
  simp at h2

theorem exists_ne_one_of_surjective_adjointGroup {G : Type*} [Group G] {τ : Tag} {K : Type}
    [Field K] (hr : 0 < τ.rank) {φ : G →* ↥(adjointGroup τ K)} (hφ : Function.Surjective φ) :
    ∃ x, φ x ≠ 1 := by
  obtain ⟨y, hy⟩ := exists_ne_one_adjointGroup τ K hr
  obtain ⟨x, rfl⟩ := hφ y
  exact ⟨x, hy⟩

theorem curtisTitsConclusion_e6_of_surjective (hadm : StatedLieAdmissible .E6 0 p f)
    (φ : ↥(e6Data_valid.minGroup (GaloisField p f)) →* ↥(adjointGroup .E6 (GaloisField p f)))
    (hφ : Function.Surjective φ) :
    CurtisTitsConclusion.{w} (e6Datum (GaloisField p f)) .E6 0 p f :=
  curtisTitsConclusion_of (e6Datum_isCTGroupDatum _) (e6Datum_steinbergExtras _)
    (by change 0 < 6; norm_num) (isQuasisimple_e6 _)
    (Or.inr (Or.inl ⟨rfl, by decide, hadm,
      untwistedChevalleyModel_of_surjective (isQuasisimple_e6 _)
        (GaloisField.card p f (by have := hadm.2.1; omega)) φ hφ
        (exists_ne_one_of_surjective_adjointGroup (by decide) hφ) (MulEquiv.refl _)⟩))

theorem curtisTitsConclusion_e7_of_surjective (hadm : StatedLieAdmissible .E7 0 p f)
    (φ : ↥(e7Data_valid.minGroup (GaloisField p f)) →* ↥(adjointGroup .E7 (GaloisField p f)))
    (hφ : Function.Surjective φ) :
    CurtisTitsConclusion.{w} (e7Datum (GaloisField p f)) .E7 0 p f :=
  curtisTitsConclusion_of (e7Datum_isCTGroupDatum _) (e7Datum_steinbergExtras _)
    (by change 0 < 7; norm_num) (isQuasisimple_e7 _)
    (Or.inr (Or.inl ⟨rfl, by decide, hadm,
      untwistedChevalleyModel_of_surjective (isQuasisimple_e7 _)
        (GaloisField.card p f (by have := hadm.2.1; omega)) φ hφ
        (exists_ne_one_of_surjective_adjointGroup (by decide) hφ) (MulEquiv.refl _)⟩))

end CFSG.LieType.CurtisTits
