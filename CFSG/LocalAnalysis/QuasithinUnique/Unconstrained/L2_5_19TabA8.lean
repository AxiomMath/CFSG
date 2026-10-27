module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabA8Basic
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction
public import CFSG.Permutation.AlternatingAutomorphism.Conjugation
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs

public section

namespace CFSG.QuasithinUnique.Id2519.Tab.A8

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open Equiv Equiv.Perm Subgroup
open scoped commutatorElement

theorem isPerfect_of_simple {Y : Type*} [Group Y] [IsSimpleGroup Y]
    (hnc : ¬ IsMulCommutative Y) : Group.IsPerfect Y := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Y) with h | h
  · exfalso
    apply hnc
    refine ⟨⟨fun x y => ?_⟩⟩
    have h1 : ⁅x, y⁆ ∈ commutator Y := Subgroup.commutator_mem_commutator (Subgroup.mem_top x)
      (Subgroup.mem_top y)
    rw [h, Subgroup.mem_bot] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1)
  · exact h

theorem commute_swap_of_fix {a b : Fin 8} (w : Perm (Fin 8)) (hwa : w a = a) (hwb : w b = b) :
    w * swap a b = swap a b * w := by
  ext x
  simp only [Perm.mul_apply]
  by_cases hxa : x = a
  · subst hxa
    rw [swap_apply_left, hwa, swap_apply_left, hwb]
  · by_cases hxb : x = b
    · subst hxb
      rw [swap_apply_right, hwb, swap_apply_right, hwa]
    · rw [swap_apply_of_ne_of_ne hxa hxb]
      have hwx : w x ≠ a := fun h => hxa (w.injective (h.trans hwa.symm))
      have hwx' : w x ≠ b := fun h => hxb (w.injective (h.trans hwb.symm))
      rw [swap_apply_of_ne_of_ne hwx hwx']

theorem tabAutCent_patA8
    (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G)
    (hK : K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)))
    (hpat : PatA8 X K t) (Y : Subgroup G) (hYn : Y ≤ Subgroup.normalizer (X : Set G))
    (hYc : Y ≤ Subgroup.centralizer (K : Set G)) :
    (Y ⊓ Subgroup.centralizer (X : Set G)).relIndex Y ≤ 2 := by
  obtain ⟨-, φ, a, b, hab, hind⟩ := hpat
  have hcent : ∀ y : ↥X, (φ y : Perm (Fin 8)) * swap a b = swap a b * (φ y : Perm (Fin 8)) →
      (y : G) ∈ Subgroup.centralizer ({t} : Set G) := by
    intro y hc
    obtain ⟨hN, hφ⟩ := hind
    have hy' : t⁻¹ * (y : G) * t ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (X : Set G)).inv_mem hN) y).mp y.2
      simpa using this
    have key := hφ y ⟨t⁻¹ * (y : G) * t, hy'⟩ rfl
    have hcoe : ((φ ⟨t⁻¹ * (y : G) * t, hy'⟩ : ↥(alternatingGroup (Fin 8))) : Perm (Fin 8)) =
        swap a b * (φ y : Perm (Fin 8)) * (swap a b)⁻¹ := by
      rw [key]
      simp
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : swap a b * (φ y : Perm (Fin 8)) * (swap a b)⁻¹ = (φ y : Perm (Fin 8)) := by
      calc swap a b * (φ y : Perm (Fin 8)) * (swap a b)⁻¹
          = ((φ y : Perm (Fin 8)) * swap a b) * (swap a b)⁻¹ := by rw [hc]
        _ = (φ y : Perm (Fin 8)) := by group
    have h3 : φ ⟨t⁻¹ * (y : G) * t, hy'⟩ = φ y := by
      apply Subtype.ext
      rw [hcoe, h2]
    have h4 : (⟨t⁻¹ * (y : G) * t, hy'⟩ : ↥X) = y := φ.injective h3
    have h5 : t⁻¹ * (y : G) * t = y := congrArg Subtype.val h4
    calc (y : G) * t = t * (t⁻¹ * (y : G) * t) := by group
      _ = t * y := by rw [h5]
  have hfixC : ∀ w : ↥(alternatingGroup (Fin 8)), (w : Perm (Fin 8)) a = a →
      (w : Perm (Fin 8)) b = b → ((φ.symm w : ↥X) : G) ∈ Subgroup.centralizer ({t} : Set G) := by
    intro w hwa hwb
    apply hcent
    rw [MulEquiv.apply_symm_apply]
    exact commute_swap_of_fix _ hwa hwb
  set s : Finset (Fin 8) := Finset.univ \ {a, b} with hs
  have hscard : Nat.card ↥s = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact card_sdiff_pair a b hab
  have hsimple : IsSimpleGroup ↥(alternatingGroup ↥s) :=
    alternatingGroup.isSimpleGroup (by rw [hscard]; norm_num)
  have hnc : ¬ IsMulCommutative ↥(alternatingGroup ↥s) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three, hscard]
    norm_num
  have hperfS : Group.IsPerfect ↥(alternatingGroup ↥s) := isPerfect_of_simple hnc
  let ψ : ↥(alternatingGroup ↥s) →* G :=
    X.subtype.comp (φ.symm.toMonoidHom.comp (alternatingGroup.ofSubtype s))
  have hperf : Group.IsPerfect ↥ψ.range := Group.IsPerfect.range ψ
  have hrange : ∀ w : ↥(alternatingGroup (Fin 8)), (w : Perm (Fin 8)) a = a →
      (w : Perm (Fin 8)) b = b → ((φ.symm w : ↥X) : G) ∈ ψ.range := by
    intro w hwa hwb
    have hsupp : (w : Perm (Fin 8)).support ⊆ s := by
      intro x hx
      rw [Equiv.Perm.mem_support] at hx
      rw [hs, Finset.mem_sdiff]
      refine ⟨Finset.mem_univ x, ?_⟩
      intro hxab
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxab
      rcases hxab with rfl | rfl
      · exact hx hwa
      · exact hx hwb
    obtain ⟨u, hu⟩ := (alternatingGroup.mem_range_ofSubtype_iff s w).mpr hsupp
    exact ⟨u, by simp only [ψ, MonoidHom.comp_apply, hu]; rfl⟩
  have hYX : ψ.range ≤ X ⊓ Subgroup.centralizer ({t} : Set G) := by
    rintro _ ⟨u, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨(φ.symm (alternatingGroup.ofSubtype s u)).2, ?_⟩
    have h := (alternatingGroup.mem_range_ofSubtype_iff s _).mp ⟨u, rfl⟩
    refine hfixC _ ?_ ?_
    · by_contra hne
      have := h (Equiv.Perm.mem_support.mpr hne)
      rw [hs, Finset.mem_sdiff] at this
      exact this.2 (by simp)
    · by_contra hne
      have := h (Equiv.Perm.mem_support.mpr hne)
      rw [hs, Finset.mem_sdiff] at this
      exact this.2 (by simp)
  have hYK : ψ.range ≤ K := by
    rw [hK]
    exact CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf _ _ hperf hYX
  let θ : ↥Y →* MulAut ↥(alternatingGroup (Fin 8)) :=
    (MulAut.congr φ).toMonoidHom.comp ((X.normalizerMonoidHom).comp (Subgroup.inclusion hYn))
  have hθ : ∀ (y : ↥Y) (x : ↥X),
      θ y (φ x) = φ ((X.normalizerMonoidHom (Subgroup.inclusion hYn y)) x) := by
    intro y x
    show φ ((X.normalizerMonoidHom (Subgroup.inclusion hYn y)) (φ.symm (φ x))) = _
    rw [φ.symm_apply_apply]
  have hconjy : ∀ (y : ↥Y) (x : ↥X),
      (((X.normalizerMonoidHom (Subgroup.inclusion hYn y)) x : ↥X) : G) =
        (y : G) * (x : G) * (y : G)⁻¹ := by
    intro y x
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hfixA : ∀ (y : ↥Y) (w : ↥(alternatingGroup (Fin 8))), (w : Perm (Fin 8)) a = a →
      (w : Perm (Fin 8)) b = b → θ y w = w := by
    intro y w hwa hwb
    have hmem : ((φ.symm w : ↥X) : G) ∈ K := hYK (hrange w hwa hwb)
    have hxy : ((φ.symm w : ↥X) : G) * (y : G) = (y : G) * ((φ.symm w : ↥X) : G) :=
      Subgroup.mem_centralizer_iff.mp (hYc y.2) _ hmem
    have h1 := hθ y (φ.symm w)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [h1]
    have hfix : (X.normalizerMonoidHom (Subgroup.inclusion hYn y)) (φ.symm w) = φ.symm w := by
      apply Subtype.ext
      rw [hconjy]
      calc (y : G) * ((φ.symm w : ↥X) : G) * (y : G)⁻¹
          = (((φ.symm w : ↥X) : G) * (y : G)) * (y : G)⁻¹ := by rw [hxy]
        _ = ((φ.symm w : ↥X) : G) := by group
    rw [hfix, MulEquiv.apply_symm_apply]
  have hrangeθ : (θ.range : Set (MulAut ↥(alternatingGroup (Fin 8)))) ⊆
      {1, MulAut.conjNormal (swap a b)} := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨σy, hσy⟩ :=
      CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
        (Or.inr (by norm_num : 7 ≤ 8)) (θ y)
    have hcommg : ∀ w : ↥(alternatingGroup (Fin 8)), (w : Perm (Fin 8)) a = a →
        (w : Perm (Fin 8)) b = b → σy * (w : Perm (Fin 8)) = (w : Perm (Fin 8)) * σy := by
      intro w hwa hwb
      have h1 := hfixA y w hwa hwb
      have h2 := hσy w
      rw [h1] at h2
      calc σy * (w : Perm (Fin 8)) = (σy * (w : Perm (Fin 8)) * σy⁻¹) * σy := by group
        _ = (w : Perm (Fin 8)) * σy := by rw [← h2]
    have hc5 : σy * g5 a b = g5 a b * σy :=
      hcommg ⟨g5 a b, mem_alternatingGroup.2 (g5_sign a b hab)⟩ (g5_fix a b hab).1
        (g5_fix a b hab).2
    have hc3 : σy * g3 a b = g3 a b * σy :=
      hcommg ⟨g3 a b, mem_alternatingGroup.2 (g3_sign a b hab)⟩ (g3_fix a b hab).1
        (g3_fix a b hab).2
    rcases cent_g a b hab σy hc5 hc3 with h | h
    · refine Set.mem_insert_iff.2 (Or.inl ?_)
      refine MulEquiv.ext fun g => Subtype.ext ?_
      rw [hσy g, h]
      simp
    · refine Set.mem_insert_iff.2 (Or.inr (Set.mem_singleton_iff.2 ?_))
      refine MulEquiv.ext fun g => Subtype.ext ?_
      rw [hσy g, h, MulAut.conjNormal_apply]
  have hcard : Nat.card θ.range ≤ 2 := by
    calc Nat.card θ.range = (θ.range : Set (MulAut ↥(alternatingGroup (Fin 8)))).ncard :=
          Nat.card_coe_set_eq _
      _ ≤ ({1, MulAut.conjNormal (swap a b)} : Set (MulAut ↥(alternatingGroup (Fin 8)))).ncard :=
          Set.ncard_le_ncard hrangeθ (Set.toFinite _)
      _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
  have hker : θ.ker = (Y ⊓ Subgroup.centralizer (X : Set G)).subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      have h1 := hθ y ⟨x, hx⟩
      rw [h, MulAut.one_apply] at h1
      have h3 := congrArg Subtype.val (φ.injective h1)
      rw [hconjy] at h3
      calc x * (y : G) = ((y : G) * x * (y : G)⁻¹) * y := by rw [← h3]
        _ = y * x := by group
    · rintro ⟨-, h⟩
      refine MulEquiv.ext fun g => ?_
      obtain ⟨x, rfl⟩ := φ.surjective g
      rw [hθ, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [hconjy]
      have hxy : (x : G) * (y : G) = (y : G) * (x : G) := Subgroup.mem_centralizer_iff.mp h x x.2
      calc (y : G) * (x : G) * (y : G)⁻¹ = ((x : G) * (y : G)) * (y : G)⁻¹ := by rw [hxy]
        _ = x := by group
  have hrel : (Y ⊓ Subgroup.centralizer (X : Set G)).relIndex Y = Nat.card θ.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  rw [hrel]
  exact hcard

end CFSG.QuasithinUnique.Id2519.Tab.A8
