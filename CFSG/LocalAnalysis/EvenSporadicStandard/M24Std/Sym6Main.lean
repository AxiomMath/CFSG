module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Sym6Ker

public section

namespace CFSG.EvenSporadicStandard.M24Std.Sym6

open Subgroup CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 CFSG.Blueprint

variable {G : Type} [Group G] {L A : Subgroup G}

@[expose] def nlE (e : L ≃* S24) : egNL L A →* S24 :=
  e.toMonoidHom.comp (Subgroup.inclusion (inf_le_right : egNL L A ≤ L))

theorem qdIota_nlE (e : L ≃* S24) (h : egNL L A) : qdIota e (nlE e h) = h := by
  show qdIota e (e (Subgroup.inclusion _ h)) = h
  rw [qdIota_apply]
  rfl

theorem nlE_injective (e : L ≃* S24) : Function.Injective (nlE (A := A) e) := fun h h' hh => by
  have h1 := congrArg (qdIota e) hh
  rw [qdIota_nlE, qdIota_nlE] at h1
  exact Subtype.ext h1

theorem nlE_mk (e : L ≃* S24) (s : S24) (hs : qdIota e s ∈ egNL L A) :
    nlE e (⟨qdIota e s, hs⟩ : egNL L A) = s :=
  qdIota_injective e (qdIota_nlE e _)

section Pinned

variable {e : L ≃* S24} (hA : ∀ x : L, (x : G) ∈ A ↔ e x ∈ m24E1l)
include hA

theorem nlE_norm (h : egNL L A) : QdNorm (nlE e h) := by
  obtain ⟨g, hg, hgh⟩ := qdExists_norm_of_mem_egNL e hA h.2
  have h1 : g = nlE e h := qdIota_injective e (by rw [hgh, qdIota_nlE])
  rw [← h1]
  exact hg

@[expose] def tetE : egNL L A →* Equiv.Perm (Fin 6) where
  toFun h := tetAct (nlE e h) (nlE_norm hA h)
  map_one' := by
    refine Equiv.ext fun i => ?_
    show tetIdx ((nlE e 1 : Equiv.Perm (Fin 24)) (tetRep i)) = i
    rw [map_one, Subgroup.coe_one, Equiv.Perm.one_apply, tetIdx_tetRep]
  map_mul' h h' := by
    refine Equiv.ext fun i => ?_
    show tetIdx ((nlE e (h * h') : Equiv.Perm (Fin 24)) (tetRep i)) =
      tetAct (nlE e h) (nlE_norm hA h) (tetIdx ((nlE e h' : Equiv.Perm (Fin 24)) (tetRep i)))
    rw [tetAct_tetIdx, map_mul, Subgroup.coe_mul, Equiv.Perm.mul_apply]

theorem tetE_apply (h : egNL L A) (i : Fin 6) :
    tetE hA h i = tetIdx ((nlE e h : Equiv.Perm (Fin 24)) (tetRep i)) := rfl

theorem tetE_eq_one_iff (h : egNL L A) :
    tetE hA h = 1 ↔ ∀ p : Fin 24, tetIdx ((nlE e h : Equiv.Perm (Fin 24)) p) = tetIdx p :=
  tetAct_eq_one_iff (nlE_norm hA h)

theorem le_ker_tetE : A.subgroupOf (egNL L A) ≤ (tetE hA).ker := by
  intro h hh
  rw [Subgroup.mem_subgroupOf] at hh
  rw [MonoidHom.mem_ker, tetE_eq_one_iff]
  exact tetIdx_of_mem ((hA (Subgroup.inclusion (inf_le_right : egNL L A ≤ L) h)).1 hh)

theorem tetE_surjective (hAL : A ≤ L) : Function.Surjective (tetE hA) := by
  have hS : tetE hA ⟨qdIota e sxS, qdIota_mem_egNL e hAL hA qdNorm_sxS⟩ = Equiv.swap 0 1 := by
    rw [← tetAct_sxS]
    refine Equiv.ext fun i => ?_
    rw [tetE_apply, nlE_mk, tetAct_apply]
  have hT : tetE hA ⟨qdIota e sxT, qdIota_mem_egNL e hAL hA qdNorm_sxT⟩ = finRotate 6 := by
    rw [← tetAct_sxT]
    refine Equiv.ext fun i => ?_
    rw [tetE_apply, nlE_mk, tetAct_apply]
  have htop : (tetE hA).range = ⊤ := by
    rw [eq_top_iff, ← closure_rot_swap, Subgroup.closure_le]
    rintro σ (rfl | rfl)
    exacts [⟨_, hT⟩, ⟨_, hS⟩]
  exact MonoidHom.range_eq_top.1 htop

theorem card_ker_tetE
    (hAL : A ≤ L) :
    Nat.card (tetE hA).ker = 192 := by
  rw [← length_sxK0]
  refine card_eq_length (· ∈ (tetE hA).ker) (nlE e) (nlE_injective e) sxK0 nodup_sxK0 fun b => ?_
  constructor
  · intro hb
    obtain ⟨hbn, hbfix⟩ := norm_of_mem_sxK0 hb
    refine ⟨⟨qdIota e b, qdIota_mem_egNL e hAL hA hbn⟩, ?_, nlE_mk _ _ _⟩
    rw [MonoidHom.mem_ker, tetE_eq_one_iff, nlE_mk]
    exact hbfix
  · rintro ⟨h, hh, rfl⟩
    rw [MonoidHom.mem_ker, tetE_eq_one_iff] at hh
    exact mem_sxK0_of_fix (nlE_norm hA h) hh

end Pinned

end CFSG.EvenSporadicStandard.M24Std.Sym6

namespace CFSG.EvenSporadicStandard.M24Std

open Sym6

variable {G : Type} [Group G]

theorem sym6Data_of_type
    {L A : Subgroup G} (h : SextetType L A) :
    ∃ φ : egNL L A →* Equiv.Perm (Fin 6),
      Function.Surjective φ ∧ A.subgroupOf (egNL L A) ≤ φ.ker ∧ Nat.card φ.ker = 192 := by
  obtain ⟨hAL, e, hA⟩ := h
  exact ⟨tetE hA, tetE_surjective hA hAL, le_ker_tetE hA, card_ker_tetE hA hAL⟩

end CFSG.EvenSporadicStandard.M24Std
