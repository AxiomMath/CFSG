module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem natCard_centralizer_singleton_mulEquiv {A B : Type} [Group A] [Group B] (Θ : A ≃* B)
    (a : A) :
    Nat.card (Subgroup.centralizer ({Θ a} : Set B)) =
      Nat.card (Subgroup.centralizer ({a} : Set A)) := by
  have key : ∀ b : B, b ∈ Subgroup.centralizer ({Θ a} : Set B) ↔
      Θ.symm b ∈ Subgroup.centralizer ({a} : Set A) := by
    intro b
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
      ← Θ.injective.eq_iff, map_mul, map_mul, Θ.apply_symm_apply]
  exact Nat.card_congr
    { toFun := fun b => ⟨Θ.symm b, (key b).mp b.2⟩
      invFun := fun c => ⟨Θ c, (key (Θ c)).mpr (by rw [Θ.symm_apply_apply]; exact c.2)⟩
      left_inv := fun b => Subtype.ext (Θ.apply_symm_apply b)
      right_inv := fun c => Subtype.ext (Θ.symm_apply_apply c) }

theorem sec4I_hasType_mulEquiv (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7)
    (hσ : quadSign Q = 1) (Θ : ProjOrth Q ≃* ProjOrth Sec4IQ) {x : ProjOrth Q} {r : ℕ} {α : ℤˣ}
    (hr : r = 2 ∨ r = 4 ∨ r = 6) (h : HasType x r α) : HasType (Θ x) r α := by
  have hxx : x * x = 1 := by
    obtain ⟨-, t, htt, -, rfl⟩ := h
    rw [← map_mul, htt, map_one]
  refine hasType_of_natCard_eq_seven hQ sec4IQ_nondegenerate hdim sec4IQ_finrank hσ
    sec4IQ_quadSign hxx h.1 ?_ ?_ ?_ hr h
  · rw [← map_mul, hxx, map_one]
  · exact fun h1 => h.1 (Θ.injective (by rw [h1, map_one]))
  · exact (natCard_centralizer_singleton_mulEquiv Θ x).symm

variable {G : Type} [Group G] {L : Subgroup G}

theorem sec4I_inducesTypeSome_iff (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {s : G} {r : ℕ}
    {α : ℤˣ} (hr : r = 2 ∨ r = 4 ∨ r = 6) :
    InducesTypeSome L s 7 1 r α ↔ ∃ y : ProjOrth Sec4IQ, Sec4IActs e s y ∧ HasType y r α := by
  constructor
  · rintro ⟨V, _, _, _, Q, hQ, e', x, hdim, hσ, ⟨hsN, hind⟩, y', rfl, hy'⟩
    obtain ⟨Θ, hΘ⟩ := sec4I_exists_theta hQ hdim hσ (e'.symm.trans e)
    refine ⟨Θ y', ⟨hsN, fun l l' hl' => ?_⟩, sec4I_hasType_mulEquiv hQ hdim hσ Θ hr hy'⟩
    have h1 := hind l l' hl'
    rw [projSimAct_projOrthToProjSim] at h1
    have h3 : (MulAut.conjNormal y' : MulAut (omegaProj hQ)) (e' (QuotientGroup.mk l)) =
        e' (QuotientGroup.mk l') :=
      Subtype.ext (by rw [MulAut.conjNormal_apply]; exact h1.symm)
    have h2 := hΘ y' (e' (QuotientGroup.mk l))
    rw [h3] at h2
    simpa using h2
  · rintro ⟨y, hy, hty⟩
    refine ⟨Sec4IV, inferInstance, inferInstance, inferInstance, Sec4IQ, sec4IQ_nondegenerate, e,
      projOrthToProjSim Sec4IQ y, sec4IQ_finrank, sec4IQ_quadSign, ⟨hy.1, fun l l' hl' => ?_⟩,
      y, rfl, hty⟩
    rw [projSimAct_projOrthToProjSim]
    exact hy.2 l l' hl'

theorem sec4I_inducesTypeSome_mem_iff (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {w : G}
    (hw : w ∈ L) {r : ℕ} {α : ℤˣ} (hr : r = 2 ∨ r = 4 ∨ r = 6) :
    InducesTypeSome L w 7 1 r α ↔
      HasType ((e (QuotientGroup.mk (⟨w, hw⟩ : ↥L)) : Sec4IOmega) : ProjOrth Sec4IQ) r α := by
  rw [sec4I_inducesTypeSome_iff e hr]
  constructor
  · rintro ⟨y, hy, hty⟩
    rw [hy.unique (Sec4IActs.of_mem e hw)] at hty
    exact hty
  · intro h
    exact ⟨_, Sec4IActs.of_mem e hw, h⟩

end CFSG.OddStandard.SmallF3.Omega
