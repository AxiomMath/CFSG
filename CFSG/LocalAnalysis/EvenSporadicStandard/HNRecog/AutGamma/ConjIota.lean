module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Unique

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G] {a z : G}

theorem conj_gammaConj (hF : IsF5Type a z) (hL : F5Local G a z) (hlines : LinesThrough a z)
    (hperp : PerpThreeA a) (σ : Gamma a ≃g Gamma a) {x : G} (hx : IsConj a x) :
    σ * gammaConj a x * σ⁻¹ = gammaConj a (act σ x) := by
  obtain ⟨u, hu⟩ := isConj_iff.1 hx
  obtain ⟨v, hv⟩ := isConj_iff.1 (isConj_act σ hx)
  have hσ' : act ((gammaConj a v)⁻¹ * σ * gammaConj a u) a = a := by
    rw [act_mul _ _ (IsConj.refl a), act_mul _ _ (isConj_act _ (IsConj.refl a)),
      act_gammaConj u (IsConj.refl a), hu, ← map_inv,
      act_gammaConj v⁻¹ (isConj_act σ hx), ← hv]
    group
  have key := conj_gammaConj_base hF hL hlines hperp _ hσ'
  have h1 : gammaConj a x = gammaConj a u * gammaConj a a * (gammaConj a u)⁻¹ := by
    rw [← hu, map_mul, map_mul, map_inv]
  have h2 : gammaConj a (act σ x) = gammaConj a v * gammaConj a a * (gammaConj a v)⁻¹ := by
    rw [← hv, map_mul, map_mul, map_inv]
  rw [h1, h2]
  calc σ * (gammaConj a u * gammaConj a a * (gammaConj a u)⁻¹) * σ⁻¹
      = gammaConj a v * (((gammaConj a v)⁻¹ * σ * gammaConj a u) * gammaConj a a *
          ((gammaConj a v)⁻¹ * σ * gammaConj a u)⁻¹) * (gammaConj a v)⁻¹ := by group
    _ = gammaConj a v * gammaConj a a * (gammaConj a v)⁻¹ := by rw [key]

theorem normalClosure_eq_top [IsSimpleGroup G] (hF : IsF5Type a z) :
    Subgroup.normalClosure {a} = ⊤ := by
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure {a})).resolve_left ?_
  intro h
  have ha : a ∈ Subgroup.normalClosure ({a} : Set G) := Subgroup.subset_normalClosure rfl
  rw [h, Subgroup.mem_bot] at ha
  exact ne_one_of_isConj hF (IsConj.refl a) ha

theorem normal_range_gammaConj [IsSimpleGroup G] (hF : IsF5Type a z) (hL : F5Local G a z)
    (hlines : LinesThrough a z) (hperp : PerpThreeA a) : (gammaConj a).range.Normal := by
  refine ⟨fun n hn σ => ?_⟩
  obtain ⟨g, rfl⟩ := hn
  let φ : G →* (Gamma a ≃g Gamma a) := (MulAut.conj σ).toMonoidHom.comp (gammaConj a)
  have hle : Subgroup.normalClosure {a} ≤ (gammaConj a).range.comap φ := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro x hx
    obtain ⟨a', ha', hx'⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    rw [Set.mem_singleton_iff] at ha'
    subst ha'
    refine ⟨act σ x, ?_⟩
    rw [← conj_gammaConj hF hL hlines hperp σ hx']
    rfl
  have hg : g ∈ (gammaConj a).range.comap φ := by
    apply hle
    rw [normalClosure_eq_top hF]
    exact Subgroup.mem_top g
  exact hg

theorem gammaConj_ne_one (hF : IsF5Type a z) (hL : F5Local G a z) : gammaConj a a ≠ 1 := by
  intro h
  obtain ⟨x, hx⟩ := (isConjOrbit_orb3A hL).nonempty
  have h2 := act_gammaConj a hx.1
  rw [h, act_one] at h2
  apply not_comm_of_mem_orb3A hF hx
  calc a * x = a * x * a⁻¹ * a := by group
    _ = x * a := by rw [← h2]

theorem gammaConj_injective [IsSimpleGroup G] (hF : IsF5Type a z) (hL : F5Local G a z) :
    Function.Injective (gammaConj a) := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (gammaConj a).ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).1 h
  · exfalso
    have ha : a ∈ (gammaConj a).ker := h ▸ Subgroup.mem_top a
    exact gammaConj_ne_one hF hL ha

theorem commutator_eq_top [IsSimpleGroup G] (hF : IsF5Type a z) (hL : F5Local G a z) :
    commutator G = ⊤ := by
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G)).resolve_left ?_
  intro h
  rw [commutator_eq_bot_iff] at h
  obtain ⟨x, hx⟩ := (isConjOrbit_orb3A hL).nonempty
  exact not_comm_of_mem_orb3A hF hx (h.is_comm.comm a x)

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
