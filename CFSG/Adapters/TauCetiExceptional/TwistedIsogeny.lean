module

public import CFSG.Adapters.TauCetiExceptional.TwistedEndgame
public import CFSG.Adapters.TauCetiExceptional.TwistedTransfer

public noncomputable section

namespace CFSG.TauCetiBridge.Twisted

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti BigCell

variable {t : TwistTag} {L : Type} [Field L] {n m : ℕ} (B : BlockCarrier t.tag L n m)

namespace BlockCarrier

@[expose] def rootSubgroup : Subgroup B.C :=
  Subgroup.closure (Set.range (fun ic : Fin t.tag.rank × L => B.u ic.1 ic.2) ∪
    Set.range (fun ic : Fin t.tag.rank × L => B.v ic.1 ic.2))

theorem adjointGroup_le_map_rootSubgroup :
    adjointGroup t.tag L ≤ B.rootSubgroup.map B.π := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨i, c, hx | hy⟩
  · refine ⟨B.u i c, Subgroup.subset_closure (Or.inl ⟨(i, c), rfl⟩), ?_⟩
    rw [B.π_u]
    exact Units.ext hx.symm
  · refine ⟨B.v i c, Subgroup.subset_closure (Or.inr ⟨(i, c), rfl⟩), ?_⟩
    rw [B.π_v]
    exact Units.ext hy.symm

theorem π_comp_eq_of_mem_rootSubgroup
    (F : B.C →* B.C) (Fr : L →+* L)
    (hFu : ∀ i c, F (B.u i c) = B.u (t.perm i) (Fr c))
    (hFv : ∀ i c, F (B.v i c) = B.v (t.perm i) (Fr c)) {e : B.C} (he : e ∈ B.rootSubgroup) :
    B.π (F e) = twistHom t L Fr (B.π e) := by
  induction he using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨⟨i, c⟩, rfl⟩ | ⟨⟨i, c⟩, rfl⟩
    · rw [hFu, B.π_u, B.π_u, twistHom_xUnit]
    · rw [hFv, B.π_v, B.π_v, twistHom_yUnit]
  | one => rw [map_one, map_one, map_one]
  | mul g h _ _ hg hh => rw [map_mul, map_mul, hg, hh, map_mul, map_mul]
  | inv g _ hg => rw [map_inv, map_inv, hg, map_inv, map_inv]

section Field

variable {p : ℕ} [Fact p.Prime] [IsAlgClosed L] [CharP L p] [Algebra (ZMod p) L]
  [Algebra.IsAlgebraic (ZMod p) L]

theorem π_comp_eq_twistHom
    (hτ : t.tag ≠ .G2) (hp2 : p ≠ 2)
    (hH : ∀ z : B.C, ∀ P, VanishesOnRat t.tag P →
      evalMat (natMat t.tag L (B.π z : Module.End L (RootModule t.tag L))) P = 0)
    (F : B.C →* B.C) (Fr : L →+* L)
    (hFu : ∀ i c, F (B.u i c) = B.u (t.perm i) (Fr c))
    (hFv : ∀ i c, F (B.v i c) = B.v (t.perm i) (Fr c))
    (hFker : ∀ k, B.π k = 1 → B.π (F k) = 1) (g : B.C) :
    B.π (F g) = twistHom t L Fr (B.π g) := by
  obtain ⟨e, he, hπe⟩ := B.adjointGroup_le_map_rootSubgroup (B.π_mem_adjointGroup hτ hp2 hH g)
  have hk : B.π (e⁻¹ * g) = 1 := by rw [map_mul, map_inv, hπe, inv_mul_cancel]
  have hg : g = e * (e⁻¹ * g) := by group
  rw [hg, map_mul, map_mul, hFker _ hk, mul_one, B.π_comp_eq_of_mem_rootSubgroup F Fr hFu hFv he,
    map_mul, hk, mul_one]

theorem isTwistedIsogeny
    (hτ : t.tag ≠ .G2) (hp2 : p ≠ 2)
    (hH : ∀ z : B.C, ∀ P, VanishesOnRat t.tag P →
      evalMat (natMat t.tag L (B.π z : Module.End L (RootModule t.tag L))) P = 0)
    (F : B.C →* B.C) (Fr : L →+* L)
    (hFu : ∀ i c, F (B.u i c) = B.u (t.perm i) (Fr c))
    (hFv : ∀ i c, F (B.v i c) = B.v (t.perm i) (Fr c))
    (hFker : ∀ k, B.π k = 1 → B.π (F k) = 1) :
    IsTwistedIsogeny t L Fr F B.π where
  mem := B.π_mem_adjointGroup hτ hp2 hH
  surj _ hx := B.adjointGroup_le_range hx
  ker g hg := B.ker_center g hg
  comm := B.π_comp_eq_twistHom hτ hp2 hH F Fr hFu hFv hFker

end Field

end BlockCarrier

end CFSG.TauCetiBridge.Twisted
