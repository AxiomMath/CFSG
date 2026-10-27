module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2A
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2B
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2C
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1CenCheck
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicMovedPerfect
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicEndgame
public import CFSG.Sporadic.Schreier.Co1OddInner
public import CFSG.Sporadic.Co2Schreier.FullAut

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co1

open Subgroup CFSG.Open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block

@[expose] noncomputable def co1ι :
    Blueprint.NativeSporadic.Co1 →* GL24 where
  toFun a := ((co1MatEquiv a : GA) : GL24)
  map_one' := by rw [map_one]; rfl
  map_mul' a b := by rw [map_mul]; rfl

theorem co1ι_apply (u : Blueprint.NativeSporadic.Co1) :
    co1ι u = ((co1MatEquiv u : GA) : GL24) := rfl

theorem co1ι_injective : Function.Injective co1ι :=
  fun _ _ h => co1MatEquiv.injective (Subtype.ext h)

theorem map_top_co1ι :
    (⊤ : Subgroup Blueprint.NativeSporadic.Co1).map co1ι = GA := by
  ext g
  constructor
  · rintro ⟨u, -, rfl⟩
    exact (co1MatEquiv u).2
  · intro hg
    exact ⟨co1MatEquiv.symm ⟨g, hg⟩, mem_top _, by rw [co1ι_apply, MulEquiv.apply_symm_apply]⟩

theorem co1ι_symm (g : GA) :
    co1ι (co1MatEquiv.symm g) = (g : GL24) := by
  rw [co1ι_apply, MulEquiv.apply_symm_apply]

theorem center_co1 :
    center Blueprint.NativeSporadic.Co1 = ⊥ := by
  have := CFSG.Sporadic.Co1.isSimpleGroup_Co1
  refine Endgame.center_eq_bot_of_not_prime ?_
  rw [CFSG.Sporadic.Co1.card_Co1]
  norm_num

theorem co1AutModel :
    AutModel (Blueprint.NativeSporadic.Carrier .Co1) Blueprint.NativeSporadic.Co1 ⊤ :=
  autModel_top center_co1 (full_automorphisms_inner_of_inputs
      Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner)

noncomputable irreducible_def co1E1 :
    Blueprint.NativeSporadic.Co1 := co1MatEquiv.symm a₁

noncomputable irreducible_def co1E2 :
    Blueprint.NativeSporadic.Co1 :=
  co1MatEquiv.symm (co1E2C : GA)

theorem co1ι_co1E1 : co1ι co1E1 = A₁ := by
  rw [co1E1_def, co1ι_symm]

theorem co1ι_co1E2 :
    co1ι co1E2 = co1E2G := by
  rw [co1E2_def, co1ι_symm, co1E2G_eq]

@[expose] noncomputable def co1R :
    Subgroup Blueprint.NativeSporadic.Co1 :=
  closure {co1E1, co1E2}

@[expose] noncomputable def co1RGL :
    Subgroup GL24 :=
  closure {A₁, co1E2G}

theorem map_co1R :
    co1R.map co1ι = co1RGL := by
  rw [co1R, co1RGL, MonoidHom.map_closure, Set.image_pair, co1ι_co1E1, co1ι_co1E2]

@[expose] def co1Exc
    (E : Subgroup Blueprint.NativeSporadic.Co1) : Prop :=
  ∃ w : Blueprint.NativeSporadic.Co1, E = co1R.map (MulAut.conj w).toMonoidHom

section Census

variable {U V : Type*} [Group U] [Group V]

theorem map_map_conj (f : U →* V) (H : Subgroup U) (w : U) :
    (H.map (MulAut.conj w).toMonoidHom).map f = (H.map f).map (MulAut.conj (f w)).toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem exists_ne_one_of_two_le {E : Subgroup U} (h : 2 ≤ Nat.card E) : ∃ t ∈ E, t ≠ 1 := by
  by_contra hne
  push Not at hne
  have hbot : E = ⊥ := (eq_bot_iff_forall E).mpr hne
  rw [hbot, card_bot] at h
  omega

theorem ncard_fourSet_le (a b : U) : (fourSet a b).ncard ≤ 4 := by
  unfold fourSet
  calc ({1, a, b, a * b} : Set U).ncard ≤ ({a, b, a * b} : Set U).ncard + 1 :=
        Set.ncard_insert_le _ _
    _ ≤ ({b, a * b} : Set U).ncard + 1 + 1 := by gcongr; exact Set.ncard_insert_le _ _
    _ ≤ ({a * b} : Set U).ncard + 1 + 1 + 1 := by gcongr; exact Set.ncard_insert_le _ _
    _ = 4 := by rw [Set.ncard_singleton]

theorem orderOf_mk_eq_two {H : Subgroup U} {t : U} (htH : t ∈ H) (ht1 : t ≠ 1)
    (ht2 : t ^ 2 = 1) : orderOf (⟨t, htH⟩ : H) = 2 :=
  orderOf_eq_prime (Subtype.ext (by simp [ht2])) fun h => ht1 (congrArg Subtype.val h)

theorem coe_conj_eq {H : Subgroup U} {c x y : H} (h : c * x * c⁻¹ = y) :
    (c : U) * x * (c : U)⁻¹ = y := by
  have := congrArg Subtype.val h
  simpa using this

theorem conj_reduce {H E' : Subgroup U} (hE'H : E' ≤ H) (hE' : IsElemAbelian 2 E')
    (h4 : 4 ≤ Nat.card E') {c : U} (hc : c ∈ H) :
    E'.map (MulAut.conj c).toMonoidHom ≤ H ∧ IsElemAbelian 2 (E'.map (MulAut.conj c).toMonoidHom) ∧
      4 ≤ Nat.card (E'.map (MulAut.conj c).toMonoidHom) ∧
      (PWitness H (E'.map (MulAut.conj c).toMonoidHom) → PWitness H E') := by
  have hHc : H.map (MulAut.conj c).toMonoidHom = H :=
    (mem_normalizer_iff_map_conj_eq).mp (le_normalizer hc)
  refine ⟨?_, isElemAbelian_map hE' _, ?_, fun h => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem hc (hE'H hx)) (H.inv_mem hc)
  · rw [card_map_of_injective (MulAut.conj c).injective]
    exact h4
  · rw [← hHc] at h
    exact (pWitness_map_iff (MulAut.conj c).toMonoidHom (MulAut.conj c).injective H E').mp h

theorem conj_mem_map_conj {E' : Subgroup U} {t : U} (ht : t ∈ E') (c : U) {r : U}
    (hr : c * t * c⁻¹ = r) : r ∈ E'.map (MulAut.conj c).toMonoidHom :=
  ⟨t, ht, by rw [← hr]; rfl⟩

theorem map_conj_inv_map_conj (E' : Subgroup U) (c : U) :
    (E'.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = E' := by
  rw [map_map]
  conv_rhs => rw [← map_id E']
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem yCensus17_of_map {W : Type*} [Group W] (ι : W →* U) (hι : Function.Injective ι)
    {H : Subgroup U} (hH : (⊤ : Subgroup W).map ι = H) {Exc : Subgroup W → Prop}
    (h : ∀ E : Subgroup W, E.map ι ≤ H → IsElemAbelian 2 (E.map ι) → 4 ≤ Nat.card (E.map ι) →
      ¬ Exc E → PWitness H (E.map ι)) :
    YCensus17 (⊤ : Subgroup W) Exc := by
  intro E hE hE4 hExc
  right
  rw [← pWitness_map_iff ι hι, hH]
  refine h E (hH ▸ map_mono le_top) (isElemAbelian_map hE ι) ?_ hExc
  rw [card_map_of_injective hι]
  exact hE4

theorem eq_map_conj_of_subset {W : Type*} [Group W] (ι : W →* U) (hι : Function.Injective ι)
    {R₀ : Subgroup W} {a b : U} (hR : R₀.map ι = closure {a, b}) (E : Subgroup W) {c : U}
    {w : W} (hw : ι w = c⁻¹)
    (hsub : (((E.map ι).map (MulAut.conj c).toMonoidHom : Subgroup U) : Set U) ⊆ fourSet a b)
    (h4 : 4 ≤ Nat.card ((E.map ι).map (MulAut.conj c).toMonoidHom)) :
    E = R₀.map (MulAut.conj w).toMonoidHom := by
  set E'' := (E.map ι).map (MulAut.conj c).toMonoidHom with hE''
  have hcard : (fourSet a b).ncard ≤ (E'' : Set U).ncard := by
    rw [← Nat.card_coe_set_eq (E'' : Set U)]
    exact (ncard_fourSet_le a b).trans h4
  have hset : (E'' : Set U) = fourSet a b :=
    Set.eq_of_subset_of_ncard_le hsub hcard (by unfold fourSet; exact Set.toFinite _)
  have hab : a ∈ E'' ∧ b ∈ E'' := by
    rw [← SetLike.mem_coe, ← SetLike.mem_coe, hset]
    exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl))⟩
  have hER : E'' = closure {a, b} := by
    refine le_antisymm (fun x hx => ?_) ((closure_le _).mpr ?_)
    · have hx' : x ∈ fourSet a b := hset ▸ hx
      rcases mem_four hx' with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact subset_closure (Set.mem_insert _ _)
      · exact subset_closure (Set.mem_insert_of_mem _ rfl)
      · exact mul_mem (subset_closure (Set.mem_insert _ _))
          (subset_closure (Set.mem_insert_of_mem _ rfl))
    · intro x hx
      rcases hx with rfl | hx
      · exact hab.1
      · rw [Set.mem_singleton_iff.mp hx]
        exact hab.2
  apply map_injective hι
  rw [map_map_conj, hR, hw, ← hER, hE'', map_conj_inv_map_conj]

end Census

theorem co1_yCensus17 :
    YCensus17 (⊤ : Subgroup Blueprint.NativeSporadic.Co1) co1Exc := by
  refine yCensus17_of_map co1ι co1ι_injective map_top_co1ι fun E hE'G hE'ab hE'4 hExc => ?_
  obtain ⟨t, htE, ht1⟩ := exists_ne_one_of_two_le (E := E.map co1ι) (by omega)
  have htG : t ∈ GA := hE'G htE
  have hord := orderOf_mk_eq_two htG ht1 (hE'ab.2 t htE)
  rcases involution_classes.1 _ hord with h | h | h
  · obtain ⟨c, hc⟩ := isConj_iff.mp h
    obtain ⟨hG, hab, h4, himp⟩ := conj_reduce hE'G hE'ab hE'4 c.2
    have e1 : (c : GL24) * t * (c : GL24)⁻¹ = aG := (coe_conj_eq hc).trans coe_aC
    exact himp (co1_pWitness_aG co1_cen2ACheck hG hab h4 (conj_mem_map_conj htE (c : GL24) e1))
  · obtain ⟨c, hc⟩ := isConj_iff.mp h
    obtain ⟨hG, hab, h4, himp⟩ := conj_reduce hE'G hE'ab hE'4 c.2
    have e1 : (c : GL24) * t * (c : GL24)⁻¹ = cG := (coe_conj_eq hc).trans coe_cC
    exact himp (co1_pWitness_cG co1_cen2CCheck hG hab h4 (conj_mem_map_conj htE (c : GL24) e1))
  · obtain ⟨c, hc⟩ := isConj_iff.mp h
    obtain ⟨hG, hab, h4, himp⟩ := conj_reduce hE'G hE'ab hE'4 c.2
    have hA : A₁ ∈ (E.map co1ι).map (MulAut.conj (c : GL24)).toMonoidHom :=
      conj_mem_map_conj htE (c : GL24) ((coe_conj_eq hc).trans coe_a₁)
    refine himp (co1_pWitness_a₁ co1_cen2BCheck hG hab hA fun hsub => hExc ?_)
    exact ⟨co1MatEquiv.symm c⁻¹, eq_map_conj_of_subset co1ι co1ι_injective map_co1R E
      (co1ι_symm c⁻¹) hsub h4⟩
