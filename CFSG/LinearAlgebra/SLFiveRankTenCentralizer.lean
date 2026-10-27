module

public import CFSG.Quasithin.Background.JonesParshallCurtisClassify
public import CFSG.Quasithin.Background.Harris.Ln2.Wedge5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LinearAlgebra.SLFiveRankTen

open CFSG.Quasithin.G11
open CFSG.Quasithin.G11.Harris.Ln2
open CFSG.Quasithin.JonesParshall
open CFSG.Quasithin.JonesParshall.Curtis

variable
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {L : Subgroup (GLV V)}

theorem exists_actsAs_wedgeRep_of_finrank_ten
    (e : ↥L ≃* G5) (hirr : IsIrr L ⊤)
    (hdim : Module.finrank (ZMod 2) V = 10) :
    ∃ (θ : ↥L ≃* G5) (β : V ≃ₗ[ZMod 2] (Fin 10 → ZMod 2)),
      ActsAs L θ wedgeRep β := by
  have hρ : IsSimpleRep (repL L e) := isSimpleRep_repL e hirr
  rcases classify_ten hρ hdim with ⟨β, hβ⟩ | ⟨β, hβ⟩
  · refine ⟨e, β, fun l v => ?_⟩
    have h := hβ (e l) v
    rwa [repL_apply_self] at h
  · refine ⟨e.trans twistα, β, fun l v => ?_⟩
    have h := hβ (e l) v
    rw [repL_apply_self] at h
    simpa [MulEquiv.trans_apply] using h

theorem centralizer_eq_bot_of_finrank_ten
    (e : ↥L ≃* G5) (hirr : IsIrr L ⊤)
    (hdim : Module.finrank (ZMod 2) V = 10) :
    Subgroup.centralizer (L : Set (GLV V)) = ⊥ := by
  obtain ⟨θ, β, hact⟩ := exists_actsAs_wedgeRep_of_finrank_ten e hirr hdim
  refine (Subgroup.eq_bot_iff_forall _).2 ?_
  intro γ hγ
  have hcomm : ∀ l : ↥L, (l : GLV V) * γ = γ * (l : GLV V) := fun l =>
    Subgroup.mem_centralizer_iff.mp hγ (l : GLV V) l.2
  let M : (Fin 10 → ZMod 2) ≃ₗ[ZMod 2] (Fin 10 → ZMod 2) :=
    β.symm.trans (γ.trans β)
  have hM : ∀ x w, M (wedgeRep x w) = wedgeRep (1 * x * 1⁻¹) (M w) := by
    intro x w
    have hβsym : β.symm (wedgeRep x w) =
        ((θ.symm x : ↥L) : GLV V) (β.symm w) := by
      apply β.injective
      rw [LinearEquiv.apply_symm_apply]
      simpa using (hact (θ.symm x) (β.symm w)).symm
    have hMapply : ∀ y, M y = β (γ (β.symm y)) := fun y => by
      simp [M, LinearEquiv.trans_apply]
    have hcv : (θ.symm x : GLV V) (γ (β.symm w)) =
        γ ((θ.symm x : GLV V) (β.symm w)) := by
      have h := congrArg (fun f : GLV V => f (β.symm w)) (hcomm (θ.symm x))
      simpa [LinearEquiv.mul_apply] using h
    rw [hMapply (wedgeRep x w), hβsym, hMapply w]
    rw [show (1 : G5) * x * 1⁻¹ = x by simp]
    rw [← hcv]
    simpa using hact (θ.symm x) (γ (β.symm w))
  have hMid : ∀ w, M w = w := by
    intro w
    simpa using eq_wedgeRep_of_inner M 1 hM w
  ext v
  have h := hMid (β v)
  have h2 : β (γ v) = β v := by
    simpa [M, LinearEquiv.trans_apply] using h
  simpa using β.injective h2

theorem normalizer_eq_self_of_finrank_ten
    (e : ↥L ≃* G5) (hirr : IsIrr L ⊤)
    (hdim : Module.finrank (ZMod 2) V = 10) :
    Subgroup.normalizer (L : Set (GLV V)) = L := by
  obtain ⟨θ, β, hact⟩ := exists_actsAs_wedgeRep_of_finrank_ten e hirr hdim
  refine le_antisymm ?_ Subgroup.le_normalizer
  intro γ hγ
  exact mem_of_normalizes_wedge5 (Γ := Subgroup.normalizer (L : Set (GLV V)))
    (fun γ hγ l hl => (Subgroup.mem_normalizer_iff.mp hγ l).1 hl) hact γ hγ

end CFSG.LinearAlgebra.SLFiveRankTen
