module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigFourConn
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup

@[expose] def SylowFourJoined (Q : Type) [Group Q] : Prop :=
  ∀ S : Sylow 2 Q, ∀ E F : Subgroup Q, IsKleinFour E → E ≤ S → IsKleinFour F → F ≤ S →
    Relation.ReflTransGen (CommFourAdj Q) E F

variable {Q : Type} [Group Q]

private theorem gsy02_isKleinFour_map {Q' : Type} [Group Q'] {f : Q →* Q'}
    (hf : Function.Injective f) {E : Subgroup Q} (hE : IsKleinFour E) :
    IsKleinFour (E.map f) := by
  refine FooteLit.isKleinFour_of_card_eq_four ?_ fun x hx => ?_
  · rw [Subgroup.card_map_of_injective hf, hE.card_four]
  · obtain ⟨v, hv, rfl⟩ := hx
    rw [← map_pow, FooteLit.sq_eq_one_of_isKleinFour hE hv, map_one]

private theorem gsy02_map_comap_of_le {Q' : Type} [Group Q'] {f : Q →* Q'} {E : Subgroup Q'}
    (hEf : E ≤ f.range) : (E.comap f).map f = E := by
  rw [Subgroup.map_comap_eq]
  exact inf_eq_right.mpr hEf

private theorem gsy02_isKleinFour_comap {Q' : Type} [Group Q'] {f : Q →* Q'}
    (hf : Function.Injective f) {E : Subgroup Q'} (hE : IsKleinFour E) (hEf : E ≤ f.range) :
    IsKleinFour (E.comap f) := by
  refine FooteLit.isKleinFour_of_card_eq_four ?_ fun x hx => ?_
  · rw [← Subgroup.card_map_of_injective hf, gsy02_map_comap_of_le hEf, hE.card_four]
  · apply hf
    rw [map_pow, map_one]
    exact FooteLit.sq_eq_one_of_isKleinFour hE (Subgroup.mem_comap.mp hx)

private theorem gsy02_map_conj_map_conj (E : Subgroup Q) (g h : Q) :
    (E.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      E.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  group

private theorem gsy02_map_conj_one (E : Subgroup Q) :
    E.map (MulAut.conj (1 : Q)).toMonoidHom = E := by
  ext x
  simp

theorem sylowFourJoined_of_sylow [Finite Q] (S₀ : Sylow 2 Q)
    (h : ∀ E F : Subgroup Q, IsKleinFour E → E ≤ S₀ → IsKleinFour F → F ≤ S₀ →
      Relation.ReflTransGen (CommFourAdj Q) E F) : SylowFourJoined Q := by
  intro S E F hE hES hF hFS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q S S₀
  have hgS : ((g • S : Sylow 2 Q) : Subgroup Q) =
      (S : Subgroup Q).map (MulAut.conj g).toMonoidHom := rfl
  have hle : ∀ D : Subgroup Q, D ≤ S → D.map (MulAut.conj g).toMonoidHom ≤ S₀ := fun D hD => by
    rw [← hg, hgS]
    exact Subgroup.map_mono hD
  have h1 := h _ _ (gsy02_isKleinFour_map (MulAut.conj g).injective hE) (hle E hES)
    (gsy02_isKleinFour_map (MulAut.conj g).injective hF) (hle F hFS)
  have h2 := reflTransGen_commFourAdj_map_conj h1 g⁻¹
  rwa [gsy02_map_conj_map_conj, gsy02_map_conj_map_conj, inv_mul_cancel, gsy02_map_conj_one,
    gsy02_map_conj_one] at h2

theorem reflTransGen_commFourAdj_map_injective {Q' : Type} [Group Q'] {f : Q →* Q'}
    (hf : Function.Injective f) {E F : Subgroup Q}
    (h : Relation.ReflTransGen (CommFourAdj Q) E F) :
    Relation.ReflTransGen (CommFourAdj Q') (E.map f) (F.map f) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    refine ih.tail ⟨gsy02_isKleinFour_map hf hbc.1, gsy02_isKleinFour_map hf hbc.2.1, ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨c, hc, rfl⟩
    have hcb : c * b = b * c := mem_centralizer_iff.mp (hbc.2.2 hb) c hc
    rw [← map_mul, ← map_mul, hcb]

theorem SylowFourJoined.of_mulEquiv {Q' : Type} [Group Q'] [Finite Q] (e : Q ≃* Q')
    (h : SylowFourJoined Q) : SylowFourJoined Q' := by
  intro S' E F hE hES hF hFS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrange : e.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
  let S : Sylow 2 Q := S'.comapOfKerIsPGroup e.toMonoidHom
    (IsPGroup.ker_isPGroup_of_injective e.injective) (by rw [hrange]; exact le_top)
  have hS : (S : Subgroup Q) = (S' : Subgroup Q').comap e.toMonoidHom := rfl
  have h1 := h S _ _ (gsy02_isKleinFour_comap e.injective hE (by rw [hrange]; exact le_top))
    (by rw [hS]; exact Subgroup.comap_mono hES)
    (gsy02_isKleinFour_comap e.injective hF (by rw [hrange]; exact le_top))
    (by rw [hS]; exact Subgroup.comap_mono hFS)
  have h2 := reflTransGen_commFourAdj_map_injective (f := e.toMonoidHom) e.injective h1
  rwa [gsy02_map_comap_of_le (by rw [hrange]; exact le_top),
    gsy02_map_comap_of_le (by rw [hrange]; exact le_top)] at h2

theorem sylowFourJoined_of_le [Finite Q] (H : Subgroup Q) (P : Sylow 2 H) (S : Sylow 2 Q)
    (hPS : (P : Subgroup H).map H.subtype = S) (h : SylowFourJoined H) : SylowFourJoined Q := by
  refine sylowFourJoined_of_sylow S fun E F hE hES hF hFS => ?_
  have hSH : (S : Subgroup Q) ≤ H.subtype.range := by
    rw [← hPS, Subgroup.range_subtype]
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hle : ∀ D : Subgroup Q, D ≤ S → D.comap H.subtype ≤ P := fun D hD => by
    rw [← Subgroup.comap_map_eq_self_of_injective H.subtype_injective (P : Subgroup H), hPS]
    exact Subgroup.comap_mono hD
  have h1 := h P _ _ (gsy02_isKleinFour_comap H.subtype_injective hE (hES.trans hSH))
    (hle E hES) (gsy02_isKleinFour_comap H.subtype_injective hF (hFS.trans hSH)) (hle F hFS)
  have h2 := reflTransGen_commFourAdj_map_injective H.subtype_injective h1
  rwa [gsy02_map_comap_of_le (hES.trans hSH), gsy02_map_comap_of_le (hFS.trans hSH)] at h2

theorem sylowFourJoined_of_normal_elemAbelian [Finite Q] (S : Sylow 2 Q) {A : Subgroup Q}
    (hSA : (S : Subgroup Q) ≤ normalizer (A : Set Q)) (hA2 : ∀ a ∈ A, a * a = 1)
    (hA8 : 8 ≤ Nat.card A) : SylowFourJoined Q :=
  sylowFourJoined_of_sylow S fun _ _ hE hES hF hFS =>
    reflTransGen_commFourAdj_of_normal_elemAbelian hSA hA2 hA8 hE hES hF hFS

theorem reflTransGen_conj_of_closure_eq_top [Finite Q] {V₀ : Subgroup Q}
    {X : Set Q} (hX : Subgroup.closure X = ⊤)
    (hgen : ∀ x ∈ X, ∃ F : Subgroup Q, Relation.ReflTransGen (CommFourAdj Q) V₀ F ∧
      x ∈ normalizer (F : Set Q)) (g : Q) :
    Relation.ReflTransGen (CommFourAdj Q) V₀ (V₀.map (MulAut.conj g).toMonoidHom) := by
  let H : Subgroup Q :=
    { carrier := {g | Relation.ReflTransGen (CommFourAdj Q) V₀
        (V₀.map (MulAut.conj g).toMonoidHom)}
      one_mem' := by
        show Relation.ReflTransGen _ V₀ (V₀.map (MulAut.conj (1 : Q)).toMonoidHom)
        rw [gsy02_map_conj_one]
      mul_mem' := fun {g h} hg hh => by
        show Relation.ReflTransGen _ V₀ (V₀.map (MulAut.conj (g * h)).toMonoidHom)
        rw [← gsy02_map_conj_map_conj V₀ g h]
        exact hg.trans (reflTransGen_commFourAdj_map_conj hh g)
      inv_mem' := fun {g} hg => by
        show Relation.ReflTransGen _ V₀ (V₀.map (MulAut.conj g⁻¹).toMonoidHom)
        have h := reflTransGen_commFourAdj_map_conj hg g⁻¹
        rw [gsy02_map_conj_map_conj V₀ g⁻¹ g, inv_mul_cancel, gsy02_map_conj_one] at h
        exact reflTransGen_commFourAdj_symm h }
  have hXH : X ⊆ H := fun x hx => by
    obtain ⟨F, hVF, hxF⟩ := hgen x hx
    have h1 := reflTransGen_commFourAdj_map_conj hVF x
    have hFx : F.map (MulAut.conj x).toMonoidHom = F := mem_normalizer_iff_map_conj_eq.mp hxF
    rw [hFx] at h1
    exact hVF.trans (reflTransGen_commFourAdj_symm h1)
  have hle : Subgroup.closure X ≤ H := (Subgroup.closure_le H).mpr hXH
  rw [hX] at hle
  have hg : g ∈ H := top_le_iff.mp hle ▸ mem_top g
  exact hg

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
