module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Aux
import TauCeti.GroupTheory.PGroup

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.SignalizerFunctorTheorem.McBride
  CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210

variable {G : Type*} [Group G]

private theorem map_conj_le_centralizer {L : Subgroup G}
    (hcomm : ∀ g : G, L.map (MulAut.conj g).toMonoidHom ≠ L →
      ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ = ⊥) {g k : G}
    (hne : L.map (MulAut.conj g).toMonoidHom ≠ L.map (MulAut.conj k).toMonoidHom) :
    L.map (MulAut.conj g).toMonoidHom ≤
      centralizer (L.map (MulAut.conj k).toMonoidHom : Set G) := by
  have h1 : L.map (MulAut.conj (g⁻¹ * k)).toMonoidHom ≠ L := fun h => hne (by
    conv_lhs => rw [← h]
    rw [Subgroup.map_conj_map_conj, mul_inv_cancel_left])
  have h2 := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) (hcomm _ h1)
  rw [map_commutator, Subgroup.map_conj_map_conj, mul_inv_cancel_left, Subgroup.map_bot] at h2
  exact commutator_eq_bot_iff_le_centralizer.mp h2

private theorem map_conj_inf_centralizer_eq_bot {L : Subgroup G}
    (hZ : L ⊓ centralizer (L : Set G) = ⊥) (g : G) :
    L.map (MulAut.conj g).toMonoidHom ⊓
      centralizer (L.map (MulAut.conj g).toMonoidHom : Set G) = ⊥ := by
  refine eq_bot_iff.mpr fun z hz => ?_
  obtain ⟨⟨y, hy, rfl⟩, hzc⟩ := mem_inf.mp hz
  have hyc : y ∈ L ⊓ centralizer (L : Set G) := by
    refine mem_inf.mpr ⟨hy, mem_centralizer_iff.mpr fun w hw => ?_⟩
    have h1 : g * w * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * w * g⁻¹) :=
      mem_centralizer_iff.mp hzc _ ⟨w, hw, rfl⟩
    calc w * y = g⁻¹ * (g * w * g⁻¹ * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹ * (g * w * g⁻¹)) * g := by rw [h1]
      _ = y * w := by group
  rw [hZ, mem_bot] at hyc
  simp [hyc]

theorem isDirectProduct_conj {L : Subgroup G}
    (hcomm : ∀ g : G, L.map (MulAut.conj g).toMonoidHom ≠ L →
      ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (hZ : L ⊓ centralizer (L : Set G) = ⊥) :
    IsDirectProduct (Set.range fun g : G => L.map (MulAut.conj g).toMonoidHom)
      (normalClosure (L : Set G)) where
  commute := by
    rintro _ ⟨g, rfl⟩ _ ⟨k, rfl⟩ hne x hx y hy
    exact (mem_centralizer_iff.mp (map_conj_le_centralizer hcomm hne hx) y hy).symm
  indep := by
    rintro _ ⟨g, rfl⟩
    refine disjoint_iff.mpr (le_bot_iff.mp ?_)
    refine le_trans (inf_le_inf_left _ (sSup_le ?_)) (map_conj_inf_centralizer_eq_bot hZ g).le
    rintro _ ⟨⟨k, rfl⟩, hk⟩
    exact map_conj_le_centralizer hcomm hk
  sSup_eq := by
    rw [sSup_range]
    have hn : (⨆ g : G, L.map (MulAut.conj g).toMonoidHom).Normal := ⟨fun x hx g => by
      have hle : (⨆ k : G, L.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom ≤
          ⨆ k : G, L.map (MulAut.conj k).toMonoidHom := by
        rw [Subgroup.map_iSup]
        exact iSup_le fun k => (Subgroup.map_conj_map_conj L k g).le.trans
          (le_iSup (fun k : G => L.map (MulAut.conj k).toMonoidHom) (g * k))
      exact hle ⟨x, hx, rfl⟩⟩
    refine le_antisymm (iSup_le fun g => ?_) (normalClosure_le_normal fun x hx => ?_)
    · rintro _ ⟨x, hx, rfl⟩
      exact normalClosure_normal.conj_mem _ (subset_normalClosure hx) g
    · exact le_iSup (fun g : G => L.map (MulAut.conj g).toMonoidHom) 1 ⟨x, hx, by simp⟩

section DirectProduct

variable [Finite G] {S : Set (Subgroup G)} {K : Subgroup G}

theorem isPGroup_of_forall_projIn {p : ℕ} (hK : IsDirectProduct S K) {X : Subgroup G}
    (hXK : X ≤ K) (h : ∀ J ∈ S, IsPGroup p (projIn S J X)) : IsPGroup p X := by
  have : Finite S := Set.toFinite S
  exact (IsPGroup.pi fun J : S => h J.1 J.2).of_injective _ (projInHom_injective_pi hK hXK)

theorem isPGroup_sSup_image {p : ℕ} (hK : IsDirectProduct S K) {T : Subgroup G → Subgroup G}
    (hT : ∀ J ∈ S, T J ≤ J) (hp : ∀ J ∈ S, IsPGroup p (T J)) :
    IsPGroup p (sSup {Y | ∃ J ∈ S, Y = T J} : Subgroup G) := by
  obtain ⟨hle, hproj⟩ := (le_sSup_image_iff hK hT).mp le_rfl
  exact isPGroup_of_forall_projIn hK hle fun J hJ => (hp J hJ).to_le (hproj J hJ)

theorem map_conj_projIn_le (hK : IsDirectProduct S K) {g : G}
    (hg : ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) {X : Subgroup G} {J : Subgroup G}
    (hJ : J ∈ S) :
    (projIn S J X).map (MulAut.conj g).toMonoidHom ≤
      projIn S (J.map (MulAut.conj g).toMonoidHom) (X.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨y, hyX, rfl⟩ := (hK.mem_projIn_iff hJ).mp hz
  exact (hK.mem_projIn_iff (hg J hJ)).mpr
    ⟨⟨g * y * g⁻¹, hK.conj_mem hg y.2⟩, ⟨y, hyX, rfl⟩, hK.coord_conj hg hJ y.2⟩

theorem projIn_le_of_forall_le {p : ℕ} (hK : IsDirectProduct S K) {H U X : Subgroup G}
    (hH : ∀ Y : Subgroup G, IsPGroup p Y → U ≤ normalizer (Y : Set G) → Y ≤ H)
    (hU : ∀ u ∈ U, ∀ J ∈ S, J.map (MulAut.conj u).toMonoidHom ∈ S) (hXK : X ≤ K)
    (hX : IsPGroup p X) (hUX : U ≤ normalizer (X : Set G)) {J : Subgroup G} (hJ : J ∈ S) :
    projIn S J X ≤ H := by
  have hP : IsPGroup p (sSup {Y | ∃ J ∈ S, Y = projIn S J X} : Subgroup G) :=
    isPGroup_sSup_image hK (fun J _ => projIn_le J X)
      fun J hJ => hX.of_surjective (projInHom hK hJ hXK) (projInHom_surjective hK hJ hXK)
  have hmem : projIn S J X ∈ {Y | ∃ J ∈ S, Y = projIn S J X} := ⟨J, hJ, rfl⟩
  refine (le_sSup hmem).trans (hH _ hP (le_normalizer_iff.mpr fun u hu y hy => ?_))
  have hXu : X.map (MulAut.conj u).toMonoidHom ≤ X := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp (hUX hu) x).mp hx
  have hle : (sSup {Y | ∃ J ∈ S, Y = projIn S J X}).map (MulAut.conj u).toMonoidHom ≤
      sSup {Y | ∃ J ∈ S, Y = projIn S J X} := by
    rw [map_le_iff_le_comap]
    refine sSup_le ?_
    rintro _ ⟨J', hJ', rfl⟩
    rw [← map_le_iff_le_comap]
    exact ((map_conj_projIn_le hK (hU u hu) hJ').trans (proj_mono hXu)).trans
      (le_sSup ⟨_, hU u hu J' hJ', rfl⟩)
  exact hle ⟨y, hy, rfl⟩

theorem eq_sSup_inf (hK : IsDirectProduct S K) {X : Subgroup G} (hXK : X ≤ K)
    (h : ∀ J ∈ S, projIn S J X ≤ X) : X = sSup {Y | ∃ J ∈ S, Y = X ⊓ J} :=
  le_antisymm ((le_sSup_image_iff hK (T := fun J => X ⊓ J) fun _ _ => inf_le_right).mpr
      ⟨hXK, fun J hJ => le_inf (h J hJ) (projIn_le J X)⟩)
    (sSup_le fun _ ⟨_, _, hY⟩ => hY ▸ inf_le_left)

theorem inf_centralizer_le (hK : IsDirectProduct S K) {X : Subgroup G}
    (hX : ∀ J ∈ S, J ⊓ centralizer ((X ⊓ J : Subgroup G) : Set G) ≤ X) :
    K ⊓ centralizer (X : Set G) ≤ X := by
  rintro c ⟨hcK, hcX⟩
  refine hK.mem_of_coord_mem hcK fun J hJ => hX J hJ ⟨(hK.coord hJ ⟨c, hcK⟩).2, ?_⟩
  refine mem_centralizer_iff.mpr fun a ha => ?_
  have haK : a ∈ K := hK.le hJ ha.2
  have hca : (⟨c, hcK⟩ * ⟨a, haK⟩ * (⟨c, hcK⟩ : K)⁻¹ : K) = ⟨a, haK⟩ := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← mem_centralizer_iff.mp hcX a ha.1]
    group
  have h := congrArg (fun y : K => ((hK.coord hJ y : J) : G)) hca
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hK.coord_of_mem hJ ha.2] at h
  calc a * ((hK.coord hJ ⟨c, hcK⟩ : J) : G)
      = (((hK.coord hJ ⟨c, hcK⟩ : J) : G) * a * ((hK.coord hJ ⟨c, hcK⟩ : J) : G)⁻¹) *
        ((hK.coord hJ ⟨c, hcK⟩ : J) : G) := by rw [h]
    _ = ((hK.coord hJ ⟨c, hcK⟩ : J) : G) * a := by group

end DirectProduct

end CFSG.GroupTheory
