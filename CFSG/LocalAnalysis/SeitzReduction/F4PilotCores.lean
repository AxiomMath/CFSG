module

public import CFSG.Foundations.Basic
public import CFSG.Quasithin.Background.A3ComponentsBasic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect
  perfectCore_perfect)

variable {G : Type*} [Group G]

section General

theorem le_perfectCore_iff {X P : Subgroup G} (hP : ⁅P, P⁆ = P) : P ≤ perfectCore X ↔ P ≤ X :=
  ⟨fun h => h.trans (perfectCore_le X), fun h => le_perfectCore_of_perfect h hP⟩

theorem inSubgroup_layer_le_perfectCore (X : Subgroup G) : inSubgroup layer X ≤ perfectCore X :=
  le_perfectCore_of_perfect (map_subtype_le _)
    (by rw [inSubgroup, ← map_commutator, CFSG.LocalCores.layer_perfect])

private theorem centralizer_sup_eq_inf' (A B : Subgroup G) :
    centralizer ((A ⊔ B : Subgroup G) : Set G) =
      centralizer (A : Set G) ⊓ centralizer (B : Set G) := by
  rw [sup_eq_closure, centralizer_closure]
  ext x
  simp only [mem_centralizer_iff, Set.mem_union, SetLike.mem_coe, or_imp, forall_and, mem_inf]

private theorem map_centralizer_subgroupOf' {H J : Subgroup G} (hJH : J ≤ H) :
    (centralizer ((J.subgroupOf H : Subgroup H) : Set H)).map H.subtype =
      H ⊓ centralizer (J : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mem_inf.2 ⟨y.2, fun j hj =>
      congrArg Subtype.val (hy ⟨j, hJH hj⟩ (mem_subgroupOf.2 hj))⟩
  · intro hx
    exact ⟨⟨x, (mem_inf.1 hx).1⟩,
      fun h hh => Subtype.ext ((mem_inf.1 hx).2 h (mem_subgroupOf.1 hh)), rfl⟩

theorem map_centralizer_mulEquiv {G' : Type*} [Group G'] (e : G ≃* G') (J : Subgroup G) :
    (centralizer (J : Set G)).map e.toMonoidHom =
      centralizer ((J.map e.toMonoidHom : Subgroup G') : Set G') := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, hy h hh]
  · refine ⟨e.symm x, fun h hh => e.injective ?_, e.apply_symm_apply x⟩
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hx (e h) ⟨h, hh, rfl⟩

@[expose] def centralizerPerfectCore (J : Subgroup G) : Subgroup G :=
  perfectCore (centralizer (J : Set G))

theorem centralizerPerfectCore_def (J : Subgroup G) :
    centralizerPerfectCore J = perfectCore (centralizer (J : Set G)) :=
  rfl

theorem centralizerPerfectCore_le_centralizer (J : Subgroup G) :
    centralizerPerfectCore J ≤ centralizer (J : Set G) :=
  perfectCore_le _

theorem centralizerPerfectCore_anti {J₁ J₂ : Subgroup G} (h : J₁ ≤ J₂) :
    centralizerPerfectCore J₂ ≤ centralizerPerfectCore J₁ :=
  perfectCore_mono (centralizer_le h)

theorem antitone_centralizerPerfectCore : Antitone (centralizerPerfectCore (G := G)) :=
  fun _ _ h => centralizerPerfectCore_anti h

theorem centralizerPerfectCore_le_centralizer_of_le {X J : Subgroup G} (h : X ≤ J) :
    centralizerPerfectCore J ≤ centralizer (X : Set G) :=
  (centralizerPerfectCore_le_centralizer J).trans (centralizer_le h)

theorem le_centralizerPerfectCore {J P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hPJ : P ≤ centralizer (J : Set G)) : P ≤ centralizerPerfectCore J :=
  le_perfectCore_of_perfect hPJ hP

theorem le_centralizerPerfectCore_iff {J P : Subgroup G} (hP : ⁅P, P⁆ = P) :
    P ≤ centralizerPerfectCore J ↔ P ≤ centralizer (J : Set G) :=
  le_perfectCore_iff hP

theorem le_centralizerPerfectCore_sup {J₁ J₂ P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (h₁ : P ≤ centralizer (J₁ : Set G)) (h₂ : P ≤ centralizer (J₂ : Set G)) :
    P ≤ centralizerPerfectCore (J₁ ⊔ J₂) :=
  le_centralizerPerfectCore hP (by rw [centralizer_sup_eq_inf']; exact le_inf h₁ h₂)

theorem inSubgroup_layer_centralizer_le (J : Subgroup G) :
    inSubgroup layer (centralizer (J : Set G)) ≤ centralizerPerfectCore J :=
  inSubgroup_layer_le_perfectCore _

theorem normalizer_le_normalizer_centralizerPerfectCore (J : Subgroup G) :
    normalizer (J : Set G) ≤ normalizer (centralizerPerfectCore J : Set G) :=
  (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup J).trans
    (CFSG.Quasithin.normalizer_le_normalizer_perfectCore _)

theorem centralizerPerfectCore_normal (J : Subgroup G) :
    ((centralizerPerfectCore J).subgroupOf (centralizer (J : Set G))).Normal :=
  CFSG.Quasithin.perfectCore_normal _

end General

section Finite

variable [Finite G]

theorem perfectCore_eq_sSup (X : Subgroup G) :
    perfectCore X = sSup {P : Subgroup G | P ≤ X ∧ ⁅P, P⁆ = P} :=
  le_antisymm (le_sSup ⟨perfectCore_le X, perfectCore_perfect X⟩)
    (sSup_le fun _ hP => le_perfectCore_of_perfect hP.1 hP.2)

theorem perfectCore_eq_of_forall_le {X P : Subgroup G} (hPX : P ≤ X) (hP : ⁅P, P⁆ = P)
    (hmax : ∀ Q : Subgroup G, Q ≤ X → ⁅Q, Q⁆ = Q → Q ≤ P) : perfectCore X = P :=
  le_antisymm (hmax _ (perfectCore_le X) (perfectCore_perfect X))
    (le_perfectCore_of_perfect hPX hP)

theorem perfectCore_perfectCore (X : Subgroup G) :
    perfectCore (perfectCore X) = perfectCore X :=
  CFSG.Quasithin.perfectCore_eq_self_of_perfect (perfectCore_perfect X)

theorem perfectCore_perfectCore_inf (X Y : Subgroup G) :
    perfectCore (perfectCore X ⊓ Y) = perfectCore (X ⊓ Y) := by
  refine le_antisymm (perfectCore_mono (inf_le_inf_right Y (perfectCore_le X)))
    (le_perfectCore_of_perfect (le_inf ?_ ((perfectCore_le _).trans inf_le_right))
      (perfectCore_perfect _))
  exact le_perfectCore_of_perfect ((perfectCore_le _).trans inf_le_left) (perfectCore_perfect _)

theorem perfectCore_inf_perfectCore (X Y : Subgroup G) :
    perfectCore (X ⊓ perfectCore Y) = perfectCore (X ⊓ Y) := by
  rw [inf_comm, perfectCore_perfectCore_inf, inf_comm]

theorem perfectCore_centralizer_sup (A B : Subgroup G) :
    perfectCore (centralizer ((A ⊔ B : Subgroup G) : Set G)) =
      perfectCore (perfectCore (centralizer (A : Set G)) ⊓ centralizer (B : Set G)) := by
  rw [perfectCore_perfectCore_inf, centralizer_sup_eq_inf']

theorem perfectCore_inf_centralizer_eq_map {H J : Subgroup G} (hJH : J ≤ H) :
    perfectCore (H ⊓ centralizer (J : Set G)) =
      (perfectCore (centralizer ((J.subgroupOf H : Subgroup H) : Set H))).map H.subtype := by
  rw [CFSG.Quasithin.map_perfectCore, map_centralizer_subgroupOf' hJH]

theorem perfectCore_conjugate (X : Subgroup G) (g : G) :
    perfectCore (conjugate X g) = conjugate (perfectCore X) g :=
  (CFSG.Quasithin.map_perfectCore _ X).symm

theorem commutator_centralizerPerfectCore (J : Subgroup G) :
    ⁅centralizerPerfectCore J, centralizerPerfectCore J⁆ = centralizerPerfectCore J :=
  perfectCore_perfect _

theorem centralizerPerfectCore_eq_bot_iff (J : Subgroup G) :
    centralizerPerfectCore J = ⊥ ↔ Group.IsSolvable (centralizer (J : Set G)) :=
  (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot _).symm

theorem centralizerPerfectCore_sup (J₁ J₂ : Subgroup G) :
    centralizerPerfectCore (J₁ ⊔ J₂) =
      perfectCore (centralizerPerfectCore J₁ ⊓ centralizer (J₂ : Set G)) :=
  perfectCore_centralizer_sup J₁ J₂

theorem perfectCore_centralizerPerfectCore_inf_comm (J₁ J₂ : Subgroup G) :
    perfectCore (centralizerPerfectCore J₁ ⊓ centralizer (J₂ : Set G)) =
      perfectCore (centralizerPerfectCore J₂ ⊓ centralizer (J₁ : Set G)) := by
  rw [← centralizerPerfectCore_sup, ← centralizerPerfectCore_sup, sup_comm]

theorem centralizerPerfectCore_sup_eq (J₁ J₂ : Subgroup G) :
    centralizerPerfectCore (J₁ ⊔ J₂) =
      perfectCore (centralizerPerfectCore J₁ ⊓ centralizerPerfectCore J₂) := by
  rw [centralizerPerfectCore_def J₂, perfectCore_inf_perfectCore, ← centralizerPerfectCore_sup]

theorem centralizerPerfectCore_sup_eq_map {J₁ J₂ : Subgroup G}
    (h : J₂ ≤ centralizerPerfectCore J₁) :
    centralizerPerfectCore (J₁ ⊔ J₂) =
      (centralizerPerfectCore (J₂.subgroupOf (centralizerPerfectCore J₁))).map
        (centralizerPerfectCore J₁).subtype := by
  rw [centralizerPerfectCore_sup, perfectCore_inf_centralizer_eq_map h]
  rfl

theorem map_centralizerPerfectCore {G' : Type*} [Group G'] [Finite G'] (e : G ≃* G')
    (J : Subgroup G) :
    (centralizerPerfectCore J).map e.toMonoidHom =
      centralizerPerfectCore (J.map e.toMonoidHom) := by
  rw [centralizerPerfectCore, centralizerPerfectCore, CFSG.Quasithin.map_perfectCore,
    map_centralizer_mulEquiv]

theorem centralizerPerfectCore_conjugate (J : Subgroup G) (g : G) :
    centralizerPerfectCore (conjugate J g) = conjugate (centralizerPerfectCore J) g :=
  (map_centralizerPerfectCore (MulAut.conj g⁻¹) J).symm

end Finite

end CFSG.SeitzReduction.F4Pilot
