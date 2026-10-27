module

public import CFSG.LargeExtraspecial.S12TriD2
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.LargeExtraspecial.S12TriB
public import CFSG.LargeExtraspecial.S12TriD

public section

namespace CFSG.LargeExtraspecial.S12Tri

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Subgroup Matrix QuadraticMap CFSG.Open CFSG.Blueprint.Fischer CFSG.Fischer
open CFSG.Fischer.Classification CFSG.Timmesfeld.Transvection.QTwo

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)}

variable (Q) in
@[expose] def DO : Set (OG Q) :=
  {g | (g : GL ι (ZMod 2)) ∈ fischerTransvections (polar Q) fun v => Q v = 1}

theorem mem_DO_iff {g : OG Q} : g ∈ DO Q ↔ ∃ v, ∃ hv : Q v = 1, g = tvO Q hv := by
  constructor
  · intro hg
    obtain ⟨v, hv, hgv⟩ := eq_tv_of_mem hg
    exact ⟨v, hv, Subtype.ext hgv⟩
  · rintro ⟨v, hv, rfl⟩
    exact tv_mem hv

theorem tvO_mem_DO {v : ι → ZMod 2} (hv : Q v = 1) : tvO Q hv ∈ DO Q := tv_mem hv

theorem mem_localClass_DO (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0) {v : ι → ZMod 2}
    (hv : Q v = 1) {g : OG Q} :
    g ∈ LocalClass (DO Q) (tvO Q hv) ↔
      ∃ w, ∃ hw : Q w = 1, polar Q w v = 0 ∧ w ≠ v ∧ g = tvO Q hw := by
  constructor
  · rintro ⟨hg, hne, hc⟩
    obtain ⟨w, hw, rfl⟩ := mem_DO_iff.1 hg
    exact ⟨w, hw, (tvO_commute_iff hnd hw hv).1 hc, fun h => hne (by subst h; rfl), rfl⟩
  · rintro ⟨w, hw, hwv, hne, rfl⟩
    exact ⟨tvO_mem_DO hw, fun h => hne ((tvO_eq_iff hnd hw hv).1 h),
      (tvO_commute_iff hnd hw hv).2 hwv⟩

theorem triGood_OG (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0) (h6 : 6 ≤ Fintype.card ι)
    (hH : Hyp (OG Q) (DO Q)) (hna : ∃ a b : commutator (OG Q), a * b ≠ b * a)
    {v : ι → ZMod 2} (hv : Q v = 1) (hX : tvO Q hv ∉ commutator (OG Q)) :
    TriGood (OG Q) (tvO Q hv) := by
  refine triGood_of_local hH hna (tvO_mem_DO hv) hX ?_ ?_ ?_
  · intro y hyt hyD
    exact eq_one_or_eq_of_centralizes_tv hnd hv hyt fun w hw hwv hne =>
      hyD _ ((mem_localClass_DO hnd hv).2 ⟨w, hw, hwv, hne, rfl⟩)
  · obtain ⟨a, b, ha, hb, hav, hbv, hab, hne, hanv, hbnv⟩ := exists_pair_perp hnd h6 hv
    exact ⟨tvO Q ha, (mem_localClass_DO hnd hv).2 ⟨a, ha, hav, hanv, rfl⟩, tvO Q hb,
      (mem_localClass_DO hnd hv).2 ⟨b, hb, hbv, hbnv, rfl⟩,
      fun h => hne ((tvO_eq_iff hnd ha hb).1 h), (tvO_commute_iff hnd ha hb).2 hab⟩
  · intro x hx y hy hxy _
    obtain ⟨a, ha, hav, hanv, rfl⟩ := (mem_localClass_DO hnd hv).1 hx
    obtain ⟨b, hb, hbv, hbnv, rfl⟩ := (mem_localClass_DO hnd hv).1 hy
    have hne : a ≠ b := fun h => hxy (by subst h; rfl)
    obtain ⟨c, hc1, hcv, hcb, hca⟩ := exists_cond hnd hv ha hb hav hbv hne hanv hbnv
    have hcnv : c ≠ v := by
      rintro rfl
      rw [polar_comm, hav] at hca
      exact zero_ne_one hca
    refine ⟨tvO Q hc1, (mem_localClass_DO hnd hv).2 ⟨c, hc1, hcv, hcnv, rfl⟩,
      (tvO_commute_iff hnd hc1 hb).2 hcb, fun h => ?_⟩
    rw [tvO_commute_iff hnd hc1 ha, hca] at h
    exact one_ne_zero h

theorem natCard_OG (Q : QuadraticForm (ZMod 2) (ι → ZMod 2)) :
    Nat.card (OG Q) = Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have hH : (OG Q).map (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2)).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [OG, fischerMatrixGroup_isometry_eq_comap]
    exact Subgroup.map_comap_eq_self_of_surjective
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2)).surjective _
  exact Nat.card_congr ((((CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι
    (ZMod 2)).subgroupMap (OG Q)).trans (MulEquiv.subgroupCongr hH)).toEquiv)

theorem natCard_OG_minus_four {Q : QuadraticForm (ZMod 2) (Fin (2 * 2) → ZMod 2)}
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hplus : ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * 2) → ZMod 2),
      Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    Nat.card (OG Q) = 120 := by
  rw [natCard_OG]
  have hnd' : (polarBilin Q).Nondegenerate :=
    ⟨fun x hx => hnd x fun y => by simpa using hx y,
      fun y hy => hnd y fun x => by rw [polar_comm]; simpa using hy x⟩
  have hdim : Module.finrank (ZMod 2) (Fin (2 * 2) → ZMod 2) = 2 * (1 + 1) := by simp
  have hε : ((-1 : ℤ) = 1 ∧ CFSG.GroupTheory.WeirSylow.IsPlusType Q) ∨
      ((-1 : ℤ) = -1 ∧ ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) := by
    refine Or.inr ⟨rfl, fun ⟨W, hW, hWs⟩ => hplus ⟨W, ?_, hWs⟩⟩
    rw [hdim] at hW
    omega
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hnd' hdim hε
  rw [Nat.card_zmod, Finset.Icc_self, Finset.prod_singleton] at h
  have e : (2 : ℤ) * ((2 : ℕ) : ℤ) ^ (1 * (1 + 1)) * (((2 : ℕ) : ℤ) ^ (1 + 1) - -1) *
      ((((2 : ℕ) : ℤ) ^ 2) ^ 1 - 1) = 120 := by norm_num
  rw [e] at h
  exact_mod_cast h

theorem triResult_orth {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hna : ∃ a b : commutator G, a * b ≠ b * a) {t : G} (ht : t ∈ D) (htG : t ∉ commutator G)
    (h3 : ∃ m : ℕ, 2 ≤ m ∧ ∃ Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2),
      (∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) ∧
      (m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
        Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) ∧
      fischerLinearModel D (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
        (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) :
    TriResult G t := by
  obtain ⟨m, hm, Q, hnd, hplus, φ, hφ⟩ := h3
  rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
  · right; left
    have h2 := index_commutator_eq_two hH.pair htG
    have hcard : Nat.card G = 120 :=
      (Nat.card_congr φ.toEquiv).trans (natCard_OG_minus_four hnd (hplus rfl))
    have := Subgroup.card_mul_index (commutator G)
    rw [h2, hcard] at this
    omega
  · left
    have hD : φ '' D = DO Q := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (hφ x).1 hx
      · intro hg
        exact ⟨φ.symm g, (hφ _).2 (by rw [MulEquiv.apply_symm_apply]; exact hg),
          MulEquiv.apply_symm_apply _ _⟩
    have hH' : Hyp (OG Q) (DO Q) := hD ▸ hyp_map hH φ
    obtain ⟨v, hv, hvt⟩ := mem_DO_iff.1 (show φ t ∈ DO Q from (hφ t).1 ht)
    refine TriGood.of_mulEquiv φ ?_
    rw [hvt]
    refine triGood_OG hnd (by simp only [Fintype.card_fin]; omega) hH' (nonabelian_map φ hna)
      hv ?_
    rw [← hvt, apply_mem_commutator_iff]
    exact htG

end CFSG.LargeExtraspecial.S12Tri
