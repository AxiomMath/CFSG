module

public import CFSG.GroupTheory.SylowIntersectionControl.Selection
public import CFSG.Quasithin.Background.Equivariance
import CFSG.GroupTheory.CharacteristicNormalizer
import CFSG.GroupTheory.SylowIntersectionControl.Basic
import CFSG.GroupTheory.SylowIntersectionControl.Factor
import CFSG.GroupTheory.SylowIntersectionControl.Singular
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.Quasithin.Background.C1GNNotation
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.ABGLocalTools CFSG.Quasithin
open scoped Pointwise

variable {G : Type*} [Group G]

structure GNPairChoice (G : Type*) [Group G] where
  fst : Subgroup G → Subgroup G
  snd : Subgroup G → Subgroup G
  fst_le : ∀ T : Subgroup G, IsPGroup 2 T → baum T = T → fst T ≤ omegaOneCenterOf T
  snd_le : ∀ T : Subgroup G, IsPGroup 2 T → baum T = T → snd T ≤ T
  fst_ne_bot : ∀ T : Subgroup G, IsPGroup 2 T → baum T = T → T ≠ ⊥ → fst T ≠ ⊥
  snd_ne_bot : ∀ T : Subgroup G, IsPGroup 2 T → baum T = T → T ≠ ⊥ → snd T ≠ ⊥
  fst_map_conj : ∀ T : Subgroup G, IsPGroup 2 T → baum T = T → ∀ g : G,
    fst (T.map (MulAut.conj g).toMonoidHom) = (fst T).map (MulAut.conj g).toMonoidHom
  snd_map_conj : ∀ T : Subgroup G, IsPGroup 2 T → baum T = T → ∀ g : G,
    snd (T.map (MulAut.conj g).toMonoidHom) = (snd T).map (MulAut.conj g).toMonoidHom

namespace GNPairChoice

variable (c : GNPairChoice G)

@[expose] def C₁ (S : Subgroup G) : Subgroup G := c.fst (baum S)

@[expose] def C₂ (S : Subgroup G) : Subgroup G := c.snd (baum S)

section Basic

variable [Finite G] {P : Subgroup G}

theorem C₁_le_omegaOneCenterOf_baum (hP : IsPGroup 2 P) :
    c.C₁ P ≤ omegaOneCenterOf (baum P) :=
  c.fst_le (baum P) (hP.to_le (C1GN.baum_le P)) (C1GN.baum_baum P)

theorem C₂_le_baum (hP : IsPGroup 2 P) : c.C₂ P ≤ baum P :=
  c.snd_le (baum P) (hP.to_le (C1GN.baum_le P)) (C1GN.baum_baum P)

theorem C₁_ne_bot (hP : IsPGroup 2 P) (hne : P ≠ ⊥) : c.C₁ P ≠ ⊥ := by
  have hbP : IsPGroup 2 (baum P) := hP.to_le (C1GN.baum_le P)
  have hω : omegaOneCenterOf P ≠ ⊥ :=
    CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hP hne
  have hb : baum P ≠ ⊥ := fun h =>
    hω (le_bot_iff.mp (h ▸ C1GN.omegaOneCenterOf_le_baum P))
  exact c.fst_ne_bot (baum P) hbP (C1GN.baum_baum P) hb

theorem C₂_ne_bot (hP : IsPGroup 2 P) (hne : P ≠ ⊥) : c.C₂ P ≠ ⊥ := by
  have hbP : IsPGroup 2 (baum P) := hP.to_le (C1GN.baum_le P)
  have hω : omegaOneCenterOf P ≠ ⊥ :=
    CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hP hne
  have hb : baum P ≠ ⊥ := fun h =>
    hω (le_bot_iff.mp (h ▸ C1GN.omegaOneCenterOf_le_baum P))
  exact c.snd_ne_bot (baum P) hbP (C1GN.baum_baum P) hb

theorem C₁_map_conj (hP : IsPGroup 2 P) (g : G) :
    c.C₁ (P.map (MulAut.conj g).toMonoidHom) = (c.C₁ P).map (MulAut.conj g).toMonoidHom := by
  unfold C₁
  rw [← baum_map_mulEquiv (MulAut.conj g) P]
  exact c.fst_map_conj (baum P) (hP.to_le (C1GN.baum_le P)) (C1GN.baum_baum P) g

theorem C₂_map_conj (hP : IsPGroup 2 P) (g : G) :
    c.C₂ (P.map (MulAut.conj g).toMonoidHom) = (c.C₂ P).map (MulAut.conj g).toMonoidHom := by
  unfold C₂
  rw [← baum_map_mulEquiv (MulAut.conj g) P]
  exact c.snd_map_conj (baum P) (hP.to_le (C1GN.baum_le P)) (C1GN.baum_baum P) g

theorem normalizer_baum_le_normalizer_C₁ (hP : IsPGroup 2 P) :
    normalizer (baum P : Set G) ≤ normalizer (c.C₁ P : Set G) := by
  intro n hn
  have hbP : IsPGroup 2 (baum P) := hP.to_le (C1GN.baum_le P)
  have h := c.fst_map_conj (baum P) hbP (C1GN.baum_baum P) n
  rw [map_conj_eq_of_mem_normalizer hn] at h
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  unfold C₁
  exact h.symm

theorem normalizer_baum_le_normalizer_C₂ (hP : IsPGroup 2 P) :
    normalizer (baum P : Set G) ≤ normalizer (c.C₂ P : Set G) := by
  intro n hn
  have hbP : IsPGroup 2 (baum P) := hP.to_le (C1GN.baum_le P)
  have h := c.snd_map_conj (baum P) hbP (C1GN.baum_baum P) n
  rw [map_conj_eq_of_mem_normalizer hn] at h
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  unfold C₂
  exact h.symm

end Basic

@[expose] def selection [Finite G] : PSubgroupSelection 2 G where
  sets P := {c.C₁ P, c.C₂ P, omegaOneCenterOf P}
  le_of_mem := by
    intro P hP F hF
    change F ∈ ({c.C₁ P, c.C₂ P, omegaOneCenterOf P} : Set (Subgroup G)) at hF
    rcases Set.mem_insert_iff.mp hF with rfl | hF
    · exact (c.C₁_le_omegaOneCenterOf_baum hP).trans
        ((C1GN.omegaOneCenterOf_le_self (baum P)).trans (C1GN.baum_le P))
    · rcases Set.mem_insert_iff.mp hF with rfl | hF
      · exact (c.C₂_le_baum hP).trans (C1GN.baum_le P)
      · rw [Set.mem_singleton_iff] at hF
        rw [hF]
        exact C1GN.omegaOneCenterOf_le_self P
  normalizer_le := by
    intro P hP F hF
    change F ∈ ({c.C₁ P, c.C₂ P, omegaOneCenterOf P} : Set (Subgroup G)) at hF
    rcases Set.mem_insert_iff.mp hF with rfl | hF
    · exact (normalizer_le_normalizer_baum P).trans (c.normalizer_baum_le_normalizer_C₁ hP)
    · rcases Set.mem_insert_iff.mp hF with rfl | hF
      · exact (normalizer_le_normalizer_baum P).trans (c.normalizer_baum_le_normalizer_C₂ hP)
      · rw [Set.mem_singleton_iff] at hF
        rw [hF]
        exact normalizer_le_normalizer_of_map_mulEquiv omegaOneCenterOf_map_mulEquiv P
  sets_map_conj := by
    intro P hP g
    have h1 := c.C₁_map_conj hP g
    have h2 := c.C₂_map_conj hP g
    have h3 := omegaOneCenterOf_map_mulEquiv (MulAut.conj g) P
    simp only [Set.image_insert_eq, Set.image_singleton, h1, h2, ← h3]

@[expose] def gomiD : Set (Subgroup G) :=
  {X | ∃ S : Subgroup G, IsSylowOf 2 S ⊤ ∧
    (X = centralizer ((c.C₁ S ⊓ omegaOneCenterOf S : Subgroup G) : Set G) ∨
      X = normalizer ((c.C₂ S : Subgroup G) : Set G))}

private lemma map_conj_eq_of_forall_mem_iff {P Q : Subgroup G} {k : G}
    (h : ∀ x : G, x ∈ Q ↔ k⁻¹ * x * k ∈ P) : Q = P.map (MulAut.conj k).toMonoidHom := by
  ext x
  rw [h x, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

private lemma le_centralizer_of_le_centerOf {S A : Subgroup G} (hA : A ≤ centerOf S) :
    S ≤ Subgroup.centralizer (A : Set G) :=
  Subgroup.le_centralizer_iff.mpr
    (hA.trans (inf_le_right : centerOf S ≤ Subgroup.centralizer (S : Set G)))

private lemma two_not_dvd_relIndex_top [Finite G] {S X : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (hSX : S ≤ X) : ¬ 2 ∣ X.relIndex ⊤ := by
  have h := Subgroup.relIndex_mul_relIndex (H := S) (K := X) (L := ⊤) hSX le_top
  intro hdvd
  exact (isSylowOf_iff.mp hS).2.2 (h ▸ dvd_mul_of_dvd_right hdvd (S.relIndex X))

private lemma exists_mul_mem_normalizer [Finite G] {C E T : Subgroup G} (hCE : C ≤ E)
    (hE : E ≤ Subgroup.normalizer (C : Set G)) (hT : IsSylowOf 2 T C) {e : G} (he : e ∈ E) :
    ∃ k ∈ C, ∃ n ∈ Subgroup.normalizer (T : Set G) ⊓ E, e = k * n := by
  have hCe : C.map (MulAut.conj e).toMonoidHom = C := map_conj_eq_of_mem_normalizer (hE he)
  have hTe : IsSylowOf 2 (T.map (MulAut.conj e).toMonoidHom) C := by
    rw [← hCe]
    exact isSylowOf_map_conj hT e
  obtain ⟨k, hkC, hk⟩ := hT.exists_mem_conj hTe
  have hmap : T.map (MulAut.conj e).toMonoidHom = T.map (MulAut.conj k).toMonoidHom :=
    map_conj_eq_of_forall_mem_iff hk
  have hcomp : (MulAut.conj (k⁻¹ * e)).toMonoidHom =
      (MulAut.conj k⁻¹).toMonoidHom.comp (MulAut.conj e).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hid : (MulAut.conj k⁻¹).toMonoidHom.comp (MulAut.conj k).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  refine ⟨k, hkC, k⁻¹ * e, ⟨?_, E.mul_mem (E.inv_mem (hCE hkC)) he⟩, by group⟩
  refine (Subgroup.mem_normalizer_iff_map_conj_eq (H := T) (g := k⁻¹ * e)).mpr ?_
  change Subgroup.map (MulAut.conj (k⁻¹ * e)).toMonoidHom T = T
  rw [hcomp, ← Subgroup.map_map, hmap, Subgroup.map_map, hid, Subgroup.map_id]

private lemma mul_eq_of_frattini [Finite G] {C E T F₁ F₂ : Subgroup G} (hCE : C ≤ E)
    (hE : E ≤ Subgroup.normalizer (C : Set G)) (hT : IsSylowOf 2 T C) (hCF₁ : C ≤ F₁)
    (hNF₂ : Subgroup.normalizer (T : Set G) ≤ F₂) :
    ((F₁ ⊓ E : Subgroup G) : Set G) * ((F₂ ⊓ E : Subgroup G) : Set G) = E := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · intro x hx
    rw [Set.mem_mul] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact E.mul_mem ha.2 hb.2
  · intro x hx
    rw [Set.mem_mul]
    obtain ⟨k, hkC, n, hn, rfl⟩ := exists_mul_mem_normalizer hCE hE hT hx
    exact ⟨k, ⟨hCF₁ hkC, hCE hkC⟩, n, ⟨hNF₂ hn.1, hn.2⟩, rfl⟩

private lemma exists_sylow_members_mul_eq [Finite G] {S E : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) (hE : E ∈ sylowMembers 2 (c.selection.family ⊤) S) :
    ∃ F₁ ∈ sylowMembers 2 c.gomiD S, ∃ F₂ ∈ sylowMembers 2 c.gomiD S,
      ((F₁ ⊓ E : Subgroup G) : Set G) * ((F₂ ⊓ E : Subgroup G) : Set G) = E := by
  rw [c.selection.sylowMembers_family hS] at hE
  obtain ⟨F, hF, hFE⟩ := hE
  simp only [top_inf_eq] at hFE
  rw [← hFE]
  let F₁ : Subgroup G :=
    Subgroup.centralizer ((c.C₁ S ⊓ omegaOneCenterOf S : Subgroup G) : Set G)
  let F₂ : Subgroup G := Subgroup.normalizer ((c.C₂ S : Subgroup G) : Set G)
  have hSF₁ : S ≤ F₁ :=
    le_centralizer_of_le_centerOf (inf_le_right.trans (C1GN.omegaOneCenterOf_le_centerOf S))
  have hSF₂ : S ≤ F₂ :=
    Subgroup.le_normalizer.trans ((normalizer_le_normalizer_baum S).trans
      (c.normalizer_baum_le_normalizer_C₂ hS.isPGroup))
  have hF₁ : F₁ ∈ sylowMembers 2 c.gomiD S :=
    ⟨⟨S, hS, Or.inl rfl⟩, by rw [inf_eq_left.mpr hSF₁]; exact hS.of_le hSF₁ le_top⟩
  have hF₂ : F₂ ∈ sylowMembers 2 c.gomiD S :=
    ⟨⟨S, hS, Or.inr rfl⟩, by rw [inf_eq_left.mpr hSF₂]; exact hS.of_le hSF₂ le_top⟩
  have hFmem : F = c.C₁ S ∨ F = c.C₂ S ∨ F = omegaOneCenterOf S := by
    have h' : F ∈ ({c.C₁ S, c.C₂ S, omegaOneCenterOf S} : Set (Subgroup G)) := hF
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h'
  rcases hFmem with rfl | rfl | rfl
  · refine ⟨F₁, hF₁, F₂, hF₂, ?_⟩
    have hSE : S ≤ Subgroup.normalizer (c.C₁ S : Set G) :=
      Subgroup.le_normalizer.trans ((normalizer_le_normalizer_baum S).trans
        (c.normalizer_baum_le_normalizer_C₁ hS.isPGroup))
    have hC : Subgroup.centralizer (c.C₁ S : Set G) ≤
        Subgroup.normalizer (c.C₁ S : Set G) :=
      Subgroup.centralizer_le_normalizer _
    have hnorm : Subgroup.normalizer (c.C₁ S : Set G) ≤
        Subgroup.normalizer (Subgroup.centralizer (c.C₁ S : Set G) : Set G) :=
      CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup (c.C₁ S)
    have hbaum : baum (S ⊓ Subgroup.centralizer (c.C₁ S : Set G)) = baum S := by
      refine (baum_eq_of_le ?_ inf_le_left).symm
      refine le_inf (C1GN.baum_le S) ?_
      exact Subgroup.le_centralizer_iff.mpr
        ((c.C₁_le_omegaOneCenterOf_baum hS.isPGroup).trans
          ((C1GN.omegaOneCenterOf_le_centerOf (baum S)).trans inf_le_right))
    refine mul_eq_of_frattini (C := Subgroup.centralizer (c.C₁ S : Set G))
      (T := S ⊓ Subgroup.centralizer (c.C₁ S : Set G)) hC hnorm
      (IsSylowOf.inf_of_le_normalizer (hS.of_le hSE le_top) hC hnorm) ?_ ?_
    · exact Subgroup.centralizer_le Set.inter_subset_left
    · refine (normalizer_le_normalizer_baum _).trans ?_
      rw [hbaum]
      exact c.normalizer_baum_le_normalizer_C₂ hS.isPGroup
  · refine ⟨F₁, hF₁, F₂, hF₂, ?_⟩
    refine Set.eq_of_subset_of_subset ?_ ?_
    · intro x hx
      rw [Set.mem_mul] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact (Subgroup.normalizer (c.C₂ S : Set G)).mul_mem ha.2 hb.2
    · intro x hx
      rw [Set.mem_mul]
      exact ⟨1, ⟨F₁.one_mem, Subgroup.one_mem _⟩, x, ⟨hx, hx⟩, one_mul x⟩
  · refine ⟨F₁, hF₁, F₂, hF₂, ?_⟩
    refine mul_eq_of_frattini (C := Subgroup.centralizer (omegaOneCenterOf S : Set G))
      (T := S) (Subgroup.centralizer_le_normalizer _)
      (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup (omegaOneCenterOf S))
      (hS.of_le (le_centralizer_of_le_centerOf (C1GN.omegaOneCenterOf_le_centerOf S)) le_top)
      ?_ ?_
    · exact Subgroup.centralizer_le Set.inter_subset_right
    · exact (normalizer_le_normalizer_baum S).trans
        (c.normalizer_baum_le_normalizer_C₂ hS.isPGroup)

theorem controlsSylowIntersections_gomiD_union [Finite G] :
    ControlsSylowIntersections 2 (c.gomiD ∪ c.selection.singularMaxLocals) ⊤ := by
  have hf : ∀ P : Subgroup G, IsPGroup 2 P → P ≠ ⊥ →
      ∀ F ∈ c.selection.sets P, F ≠ ⊥ := by
    intro P hP hP0 F hF
    have h' : F ∈ ({c.C₁ P, c.C₂ P, omegaOneCenterOf P} : Set (Subgroup G)) := hF
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h'
    rcases h' with rfl | rfl | rfl
    · exact c.C₁_ne_bot hP hP0
    · exact c.C₂_ne_bot hP hP0
    · exact CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hP hP0
  have hfar : ControlsSylowIntersections 2
      (c.selection.family ⊤ ∪ c.selection.singularMaxLocals) ⊤ :=
    c.selection.controlsSylowIntersections_family_union hf
  refine ControlsSylowIntersections.of_factor (𝓔 := c.selection.family ⊤) (𝓕 := c.gomiD)
    (𝓓 := c.selection.singularMaxLocals) (K := ⊤) (fun _ _ => le_top) ?_ ?_ ?_ hfar
  · refine ⟨fun _ _ => le_top, ?_⟩
    rintro X ⟨S, hS, hX⟩ g -
    rcases hX with hX | hX
    · rw [hX]
      refine ⟨S.map (MulAut.conj g).toMonoidHom, ?_, Or.inl ?_⟩
      · have hm := isSylowOf_map_conj hS g
        rw [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at hm
        exact hm
      · rw [centralizer_map_mulEquiv, Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective,
          ← c.C₁_map_conj hS.isPGroup g, omegaOneCenterOf_map_mulEquiv]
    · rw [hX]
      refine ⟨S.map (MulAut.conj g).toMonoidHom, ?_, Or.inr ?_⟩
      · have hm := isSylowOf_map_conj hS g
        rw [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at hm
        exact hm
      · rw [Subgroup.map_equiv_normalizer_eq, ← c.C₂_map_conj hS.isPGroup g]
  · intro X hX
    rcases hX with hX | hX
    · rw [c.selection.family_top, Set.mem_setOf_eq] at hX
      obtain ⟨P, hP, F, hF, rfl⟩ := hX
      exact two_not_dvd_relIndex_top hP
        (Subgroup.le_normalizer.trans (c.selection.normalizer_le P hP.isPGroup F hF))
    · obtain ⟨S, hS, hX⟩ := hX
      rcases hX with hX | hX
      · rw [hX]
        exact two_not_dvd_relIndex_top hS (le_centralizer_of_le_centerOf
          (inf_le_right.trans (C1GN.omegaOneCenterOf_le_centerOf S)))
      · rw [hX]
        exact two_not_dvd_relIndex_top hS (Subgroup.le_normalizer.trans
          ((normalizer_le_normalizer_baum S).trans
            (c.normalizer_baum_le_normalizer_C₂ hS.isPGroup)))
  · exact fun S hS E hE => c.exists_sylow_members_mul_eq hS hE

private abbrev HasCharacteristicPair
    (P : Subgroup G → Subgroup G → Subgroup G → Prop) : Prop :=
  ∀ T : Subgroup G, IsPGroup 2 T → baum T = T → T ≠ ⊥ → ∃ T₁ T₂ : Subgroup G,
    T₁ ≠ ⊥ ∧ T₁ ≤ omegaOneCenterOf T ∧ (T₁.subgroupOf T).Characteristic ∧
      T₂ ≠ ⊥ ∧ T₂ ≤ T ∧ (T₂.subgroupOf T).Characteristic ∧ P T T₁ T₂

private def conjSetoid : Setoid (Subgroup G) where
  r T T' := ∃ g : G, T' = T.map (MulAut.conj g).toMonoidHom
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro T
      exact ⟨1, by simp [MulAut.one_def, MulEquiv.toMonoidHom_refl]⟩
    · rintro T T' ⟨g, rfl⟩
      refine ⟨g⁻¹, ?_⟩
      rw [Subgroup.map_conj_map_conj, inv_mul_cancel]
      simp [MulAut.one_def, MulEquiv.toMonoidHom_refl]
    · rintro T T' T'' ⟨g, rfl⟩ ⟨h, rfl⟩
      exact ⟨h * g, Subgroup.map_conj_map_conj T g h⟩

private noncomputable def rep (T : Subgroup G) : Subgroup G :=
  Quotient.out (Quotient.mk'' (s₁ := conjSetoid (G := G)) T)

private noncomputable def conjWitness (T : Subgroup G) : G :=
  Classical.choose (Quotient.mk_out (s := conjSetoid (G := G)) T)

private theorem conjWitness_spec (T : Subgroup G) :
    T = (rep T).map (MulAut.conj (conjWitness T)).toMonoidHom :=
  Classical.choose_spec (Quotient.mk_out (s := conjSetoid (G := G)) T)

private theorem rep_map_conj (T : Subgroup G) (g : G) :
    rep (T.map (MulAut.conj g).toMonoidHom) = rep T := by
  have h := (Quotient.sound' (s₁ := conjSetoid (G := G)) (a := T)
    (b := T.map (MulAut.conj g).toMonoidHom) ⟨g, rfl⟩).symm
  simpa [rep] using congrArg Quotient.out h

private theorem map_conj_inv_conjWitness (T : Subgroup G) :
    T.map (MulAut.conj (conjWitness T)⁻¹).toMonoidHom = rep T := by
  have hstep := congrArg (fun X : Subgroup G =>
    X.map (MulAut.conj (conjWitness T)⁻¹).toMonoidHom) (conjWitness_spec T)
  calc
    T.map (MulAut.conj (conjWitness T)⁻¹).toMonoidHom
        = ((rep T).map (MulAut.conj (conjWitness T)).toMonoidHom).map
            (MulAut.conj (conjWitness T)⁻¹).toMonoidHom := hstep
    _ = rep T := by
          rw [Subgroup.map_conj_map_conj, inv_mul_cancel]
          simp [MulAut.one_def, MulEquiv.toMonoidHom_refl]

private theorem rep_iff_of_invariant {Q : Subgroup G → Prop}
    (hQ : ∀ X : Subgroup G, Q X → ∀ g : G, Q (X.map (MulAut.conj g).toMonoidHom))
    (T : Subgroup G) : Q (rep T) ↔ Q T :=
  ⟨fun h => by
      rw [conjWitness_spec T]
      exact hQ (rep T) h (conjWitness T),
    fun h => by
      rw [← map_conj_inv_conjWitness T]
      exact hQ T h (conjWitness T)⁻¹⟩

private theorem rep_eq_bot_iff (T : Subgroup G) : rep T = ⊥ ↔ T = ⊥ :=
  rep_iff_of_invariant (Q := fun X => X = ⊥)
    (fun _ hX g => by rw [hX, Subgroup.map_bot]) T

private theorem isPGroup_rep_iff (T : Subgroup G) :
    IsPGroup 2 (rep T) ↔ IsPGroup 2 T :=
  rep_iff_of_invariant (Q := fun X => IsPGroup 2 X)
    (fun _ hX g => hX.map (MulAut.conj g).toMonoidHom) T

private theorem baum_rep_eq_iff (T : Subgroup G) :
    baum (rep T) = rep T ↔ baum T = T :=
  rep_iff_of_invariant (Q := fun X => baum X = X) (fun X hX g => by
    rw [← baum_map_mulEquiv (MulAut.conj g) X, hX]) T

private noncomputable def pairAt (P : Subgroup G → Subgroup G → Subgroup G → Prop)
    (hex : HasCharacteristicPair P) (R : Subgroup G) : Subgroup G × Subgroup G := by
  classical
  exact if h : IsPGroup 2 R ∧ baum R = R ∧ R ≠ ⊥ then
    (Classical.choose (hex R h.1 h.2.1 h.2.2),
      Classical.choose (Classical.choose_spec (hex R h.1 h.2.1 h.2.2)))
  else (⊥, ⊥)

private theorem pairAt_spec (P : Subgroup G → Subgroup G → Subgroup G → Prop)
    (hex : HasCharacteristicPair P) {R : Subgroup G} (hR : IsPGroup 2 R)
    (hb : baum R = R) (hne : R ≠ ⊥) :
    (pairAt P hex R).1 ≠ ⊥ ∧ (pairAt P hex R).1 ≤ omegaOneCenterOf R ∧
      ((pairAt P hex R).1.subgroupOf R).Characteristic ∧
      (pairAt P hex R).2 ≠ ⊥ ∧ (pairAt P hex R).2 ≤ R ∧
      ((pairAt P hex R).2.subgroupOf R).Characteristic ∧
      P R (pairAt P hex R).1 (pairAt P hex R).2 := by
  classical
  unfold pairAt
  rw [dif_pos (show IsPGroup 2 R ∧ baum R = R ∧ R ≠ ⊥ from ⟨hR, hb, hne⟩)]
  exact Classical.choose_spec (Classical.choose_spec (hex R hR hb hne))

private noncomputable def chosenPair (P : Subgroup G → Subgroup G → Subgroup G → Prop)
    (hex : HasCharacteristicPair P) (T : Subgroup G) : Subgroup G × Subgroup G :=
  let p := pairAt P hex (rep T)
  (p.1.map (MulAut.conj (conjWitness T)).toMonoidHom,
    p.2.map (MulAut.conj (conjWitness T)).toMonoidHom)

private theorem map_conjWitness_ne_bot {T C : Subgroup G} (hC : C ≠ ⊥) :
    C.map (MulAut.conj (conjWitness T)).toMonoidHom ≠ ⊥ :=
  fun h => hC ((Subgroup.map_eq_bot_iff_of_injective C
    (f := (MulAut.conj (conjWitness T)).toMonoidHom)
    (MulAut.conj (conjWitness T)).injective).mp h)

private theorem map_conjWitness_map_conj {T C : Subgroup G} (hC : C ≤ rep T)
    (hchar : (C.subgroupOf (rep T)).Characteristic) (g : G) :
    C.map (MulAut.conj (conjWitness (T.map (MulAut.conj g).toMonoidHom))).toMonoidHom =
      (C.map (MulAut.conj (conjWitness T)).toMonoidHom).map
        (MulAut.conj g).toMonoidHom := by
  have hTw := conjWitness_spec (T.map (MulAut.conj g).toMonoidHom)
  rw [rep_map_conj T g] at hTw
  have hT : T = (rep T).map (MulAut.conj (conjWitness T)).toMonoidHom := conjWitness_spec T
  have hEq : (rep T).map
        (MulAut.conj (conjWitness (T.map (MulAut.conj g).toMonoidHom))).toMonoidHom =
      (rep T).map (MulAut.conj (g * conjWitness T)).toMonoidHom := by
    rw [← hTw]
    conv_lhs => rw [hT]
    rw [Subgroup.map_conj_map_conj]
  calc
    C.map (MulAut.conj (conjWitness (T.map (MulAut.conj g).toMonoidHom))).toMonoidHom
        = C.map (MulAut.conj (g * conjWitness T)).toMonoidHom :=
          map_conj_eq_of_characteristic hC hchar hEq
    _ = (C.map (MulAut.conj (conjWitness T)).toMonoidHom).map
          (MulAut.conj g).toMonoidHom := by rw [Subgroup.map_conj_map_conj]

private theorem chosenPair_le (P : Subgroup G → Subgroup G → Subgroup G → Prop)
    (hex : HasCharacteristicPair P) (T : Subgroup G) (hT : IsPGroup 2 T)
    (hb : baum T = T) :
    (chosenPair P hex T).1 ≤ omegaOneCenterOf T ∧ (chosenPair P hex T).2 ≤ T := by
  by_cases hbot : T = ⊥
  · subst hbot
    simp [chosenPair, rep_eq_bot_iff, pairAt]
  · have hR : IsPGroup 2 (rep T) := (isPGroup_rep_iff T).mpr hT
    have hbR : baum (rep T) = rep T := (baum_rep_eq_iff T).mpr hb
    have hneR : rep T ≠ ⊥ := fun h => hbot ((rep_eq_bot_iff T).mp h)
    have hs := pairAt_spec P hex hR hbR hneR
    refine ⟨?_, ?_⟩
    · dsimp only [chosenPair]
      calc
        (pairAt P hex (rep T)).1.map (MulAut.conj (conjWitness T)).toMonoidHom ≤
            (omegaOneCenterOf (rep T)).map (MulAut.conj (conjWitness T)).toMonoidHom :=
          Subgroup.map_mono hs.2.1
        _ = omegaOneCenterOf ((rep T).map
              (MulAut.conj (conjWitness T)).toMonoidHom) :=
          omegaOneCenterOf_map_mulEquiv (MulAut.conj (conjWitness T)) (rep T)
        _ = omegaOneCenterOf T := congrArg omegaOneCenterOf (conjWitness_spec T).symm
    · dsimp only [chosenPair]
      calc
        (pairAt P hex (rep T)).2.map (MulAut.conj (conjWitness T)).toMonoidHom ≤
            (rep T).map (MulAut.conj (conjWitness T)).toMonoidHom :=
          Subgroup.map_mono hs.2.2.2.2.1
        _ = T := (conjWitness_spec T).symm

private theorem chosenPair_ne_bot (P : Subgroup G → Subgroup G → Subgroup G → Prop)
    (hex : HasCharacteristicPair P) (T : Subgroup G) (hT : IsPGroup 2 T)
    (hb : baum T = T) (hne : T ≠ ⊥) :
    (chosenPair P hex T).1 ≠ ⊥ ∧ (chosenPair P hex T).2 ≠ ⊥ := by
  have hR : IsPGroup 2 (rep T) := (isPGroup_rep_iff T).mpr hT
  have hbR : baum (rep T) = rep T := (baum_rep_eq_iff T).mpr hb
  have hneR : rep T ≠ ⊥ := fun h => hne ((rep_eq_bot_iff T).mp h)
  have hs := pairAt_spec P hex hR hbR hneR
  refine ⟨?_, ?_⟩
  · dsimp only [chosenPair]
    exact map_conjWitness_ne_bot hs.1
  · dsimp only [chosenPair]
    exact map_conjWitness_ne_bot hs.2.2.2.1

private theorem chosenPair_map_conj (P : Subgroup G → Subgroup G → Subgroup G → Prop)
    (hex : HasCharacteristicPair P) (T : Subgroup G) (hT : IsPGroup 2 T)
    (hb : baum T = T) (g : G) :
    (chosenPair P hex (T.map (MulAut.conj g).toMonoidHom)).1 =
        (chosenPair P hex T).1.map (MulAut.conj g).toMonoidHom ∧
      (chosenPair P hex (T.map (MulAut.conj g).toMonoidHom)).2 =
        (chosenPair P hex T).2.map (MulAut.conj g).toMonoidHom := by
  by_cases hbot : T = ⊥
  · subst hbot
    simp [Subgroup.map_bot, chosenPair, rep_eq_bot_iff, pairAt]
  · have hR : IsPGroup 2 (rep T) := (isPGroup_rep_iff T).mpr hT
    have hbR : baum (rep T) = rep T := (baum_rep_eq_iff T).mpr hb
    have hneR : rep T ≠ ⊥ := fun h => hbot ((rep_eq_bot_iff T).mp h)
    have hs := pairAt_spec P hex hR hbR hneR
    refine ⟨?_, ?_⟩
    · dsimp only [chosenPair]
      rw [rep_map_conj T g]
      exact map_conjWitness_map_conj
        (hs.2.1.trans (CFSG.Quasithin.C1GN.omegaOneCenterOf_le_self (rep T)))
        hs.2.2.1 g
    · dsimp only [chosenPair]
      rw [rep_map_conj T g]
      exact map_conjWitness_map_conj hs.2.2.2.2.1 hs.2.2.2.2.2.1 g

private theorem chosenPair_P (P : Subgroup G → Subgroup G → Subgroup G → Prop)
    (hP : ∀ T T₁ T₂ : Subgroup G, P T T₁ T₂ → ∀ g : G,
      P (T.map (MulAut.conj g).toMonoidHom) (T₁.map (MulAut.conj g).toMonoidHom)
        (T₂.map (MulAut.conj g).toMonoidHom))
    (hex : HasCharacteristicPair P) (T : Subgroup G)
    (hT : IsPGroup 2 T) (hb : baum T = T) (hne : T ≠ ⊥) :
    P T (chosenPair P hex T).1 (chosenPair P hex T).2 := by
  have hR : IsPGroup 2 (rep T) := (isPGroup_rep_iff T).mpr hT
  have hbR : baum (rep T) = rep T := (baum_rep_eq_iff T).mpr hb
  have hneR : rep T ≠ ⊥ := fun h => hne ((rep_eq_bot_iff T).mp h)
  have hp := (pairAt_spec P hex hR hbR hneR).2.2.2.2.2.2
  have htrans := hP (rep T) (pairAt P hex (rep T)).1 (pairAt P hex (rep T)).2 hp
    (conjWitness T)
  simpa only [chosenPair, ← conjWitness_spec T] using htrans

theorem exists_forall (P : Subgroup G → Subgroup G → Subgroup G → Prop)
    (hP : ∀ T T₁ T₂ : Subgroup G, P T T₁ T₂ → ∀ g : G,
      P (T.map (MulAut.conj g).toMonoidHom) (T₁.map (MulAut.conj g).toMonoidHom)
        (T₂.map (MulAut.conj g).toMonoidHom))
    (hex : ∀ T : Subgroup G, IsPGroup 2 T → baum T = T → T ≠ ⊥ → ∃ T₁ T₂ : Subgroup G,
      T₁ ≠ ⊥ ∧ T₁ ≤ omegaOneCenterOf T ∧ (T₁.subgroupOf T).Characteristic ∧
        T₂ ≠ ⊥ ∧ T₂ ≤ T ∧ (T₂.subgroupOf T).Characteristic ∧ P T T₁ T₂) :
    ∃ c : GNPairChoice G, ∀ T : Subgroup G, IsPGroup 2 T → baum T = T → T ≠ ⊥ →
      P T (c.fst T) (c.snd T) := by
  refine ⟨{
    fst := fun T => (chosenPair P hex T).1
    snd := fun T => (chosenPair P hex T).2
    fst_le := fun T hT hb => (chosenPair_le P hex T hT hb).1
    snd_le := fun T hT hb => (chosenPair_le P hex T hT hb).2
    fst_ne_bot := fun T hT hb hne => (chosenPair_ne_bot P hex T hT hb hne).1
    snd_ne_bot := fun T hT hb hne => (chosenPair_ne_bot P hex T hT hb hne).2
    fst_map_conj := fun T hT hb g => (chosenPair_map_conj P hex T hT hb g).1
    snd_map_conj := fun T hT hb g => (chosenPair_map_conj P hex T hT hb g).2 }, ?_⟩
  intro T hT hb hne
  exact chosenPair_P P hP hex T hT hb hne

end GNPairChoice

end CFSG.GroupTheory
