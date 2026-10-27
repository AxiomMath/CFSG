module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizerFour

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap Module

variable {F V : Type*} [Field F] [CharP F 2] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

omit [FiniteDimensional F V] in
theorem eq_eichler_of_sub_mem_span (hF : ∀ a : F, a = 0 ∨ a = 1)
    (hQ : (polarBilin Q).Nondegenerate) {z y : V} (hz0 : z ≠ 0) (hz : Q z = 0)
    (hzy : polar Q z y = 0) (hyz : y ∉ F ∙ z) {g : V ≃ₗ[F] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hspan : ∀ v, g v - v ∈ Submodule.span F {z, y}) (h₁ : ∃ v, g v - v = z)
    (h₂ : ∃ v, g v - v = y) : g = eichler Q z y := by
  classical
  have hnegv : ∀ x : V, -x = x := CFSG.RankThree.OrthogonalInvolutions.neg_vec_eq F
  have hsubv : ∀ x y : V, x - y = x + y :=
    CFSG.RankThree.OrthogonalInvolutions.sub_eq_add_vec F
  have hnegF : ∀ a : F, -a = a := fun a => CharTwo.neg_eq a
  have hzz : polar Q z z = 0 := polar_self_eq_zero hz
  have hzy' : polar Q y z = 0 := by rw [polar_comm, hzy]
  have hyy : polar Q y y = 0 := by
    rw [polar_self_eq_two_mul, two_mul, CharTwo.add_self_eq_zero]
  choose a b hab using fun v => Submodule.mem_span_pair.mp (hspan v)
  have hgv : ∀ v, g v = v + a v • z + b v • y := by
    intro v
    have h : g v = (a v • z + b v • y) + v := by
      rw [hab v]
      abel
    rw [h]
    abel
  have hli : LinearIndependent F ![z, y] := by
    rw [LinearIndependent.pair_iff' hz0]
    intro c hc
    exact hyz (hc ▸ Submodule.mem_span_singleton.mpr ⟨c, rfl⟩)
  have huniq := LinearIndependent.pair_iffₛ.mp hli
  obtain ⟨v₁, hv₁⟩ := h₁
  have h1' : a v₁ • z + b v₁ • y = (1 : F) • z + (0 : F) • y := by
    rw [hab v₁, hv₁]
    simp
  obtain ⟨ha1, hb1⟩ := huniq (a v₁) (b v₁) 1 0 h1'
  obtain ⟨v₂, hv₂⟩ := h₂
  have h2' : a v₂ • z + b v₂ • y = (0 : F) • z + (1 : F) • y := by
    rw [hab v₂, hv₂]
    simp
  obtain ⟨ha2, hb2⟩ := huniq (a v₂) (b v₂) 0 1 h2'
  have hQid : ∀ v, b v * b v * Q y + a v * polar Q v z + b v * polar Q v y = 0 := by
    intro v
    have h := map_of_mem hg v
    rw [hgv v] at h
    have hexp : Q (v + a v • z + b v • y) =
        Q v + (b v * b v * Q y + a v * polar Q v z + b v * polar Q v y) := by
      rw [QuadraticMap.map_add Q (v + a v • z) (b v • y),
        QuadraticMap.map_add Q v (a v • z)]
      simp only [map_smul_eq_sq, hz, polar_add_left, polar_smul_right_eq, polar_smul_left_eq,
        hzy, mul_zero, add_zero]
      ring
    rw [hexp] at h
    linear_combination h
  have hBid : ∀ u v, a v * polar Q u z + b v * polar Q u y + a u * polar Q z v
      + b u * polar Q y v = 0 := by
    intro u v
    have h := polar_map_of_mem hg u v
    have hexp : polar Q (g u) (g v) =
        polar Q u v + (a v * polar Q u z + b v * polar Q u y + a u * polar Q z v
          + b u * polar Q y v) := by
      rw [hgv u, hgv v]
      simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq,
        hzz, hyy, hzy, hzy', mul_zero, add_zero]
      ring
    rw [hexp] at h
    linear_combination h
  have hBv1z : polar Q v₁ z = 0 := by
    have h := hQid v₁
    rw [ha1, hb1] at h
    simpa using h
  have hBv2y : polar Q v₂ y = Q y := by
    have h := hQid v₂
    rw [ha2, hb2] at h
    have h' : Q y + polar Q v₂ y = 0 := by simpa using h
    have := eq_neg_of_add_eq_zero_right h'
    rwa [hnegF] at this
  have hb : ∀ v, b v = polar Q z v := by
    have hv1y_ne : polar Q v₁ y ≠ 0 := by
      intro h0
      obtain ⟨v₀, hv₀⟩ := exists_polar_ne_zero hQ hz0
      have h := hBid v₁ v₀
      rw [ha1, hb1, hBv1z, h0] at h
      exact hv₀ (by simpa using h)
    have hv1y : polar Q v₁ y = 1 := (hF _).resolve_left hv1y_ne
    intro v
    have h := hBid v₁ v
    rw [ha1, hb1, hBv1z, hv1y] at h
    have h' : b v + polar Q z v = 0 := by simpa using h
    have := eq_neg_of_add_eq_zero_left h'
    rwa [hnegF] at this
  have ha : ∀ v, a v = Q y * polar Q z v + polar Q v y := by
    have hcoef : ∀ v, a v * polar Q v₂ z = Q y * polar Q z v + polar Q v y := by
      intro v
      have h := hBid v₂ v
      rw [ha2, hb2, hBv2y, hb v] at h
      have h' : a v * polar Q v₂ z + (Q y * polar Q z v + polar Q v y) = 0 := by
        rw [mul_comm (polar Q z v) (Q y), polar_comm Q y v] at h
        simpa only [mul_zero, zero_mul, add_zero, zero_add, one_mul, mul_one,
          add_assoc] using h
      have := eq_neg_of_add_eq_zero_left h'
      rwa [hnegF] at this
    have hne : Q y • z + y ≠ 0 := by
      intro h
      apply hyz
      rw [Submodule.mem_span_singleton]
      refine ⟨Q y, ?_⟩
      have h2 : y = Q y • z := by
        have h3 := eq_neg_of_add_eq_zero_right h
        rwa [hnegv] at h3
      exact h2.symm
    have hBv2z : polar Q v₂ z = 1 := by
      obtain ⟨v₀, hv₀⟩ := exists_polar_ne_zero hQ hne
      have hv₀' : Q y * polar Q z v₀ + polar Q v₀ y ≠ 0 := by
        rwa [polar_add_left, polar_smul_left_eq, polar_comm Q y v₀] at hv₀
      have hneB : polar Q v₂ z ≠ 0 := by
        intro h0
        apply hv₀'
        have h := hcoef v₀
        rw [h0, mul_zero] at h
        exact h.symm
      exact (hF _).resolve_left hneB
    intro v
    have := hcoef v
    rwa [hBv2z, mul_one] at this
  refine LinearEquiv.ext fun v => ?_
  rw [hgv v, eichler_apply hz hzy, ha v, hb v]
  rw [polar_comm Q z v, hsubv]
  rw [add_comm (polar Q v y) (Q y * polar Q v z)]
  abel

theorem exists_eq_eichler_of_mul_self_block (hF : ∀ a : F, a = 0 ∨ a = 1)
    (hQ : (polarBilin Q).Nondegenerate) {W E : Submodule F V} (hWE : IsCompl W E)
    (hW : finrank F W = 6) {g : V ≃ₗ[F] V} (hgE : g ∈ elementaryGroup Q) (hg2 : g * g = 1)
    (hg1 : g ≠ 1) (hgW : ∀ w ∈ W, g w ∈ W) (hgE' : ∀ e ∈ E, g e = e) :
    ∃ z y : V, z ∈ W ∧ y ∈ W ∧ z ≠ 0 ∧ Q z = 0 ∧ polar Q z y = 0 ∧ y ∉ F ∙ z ∧
      g = eichler Q z y := by
  classical
  have hO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q hgE
  have hΩ : g ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ :=
    elementaryGroup_le_omegaGroup hQ hgE
  rw [CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup] at hΩ
  have heven : Even (finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace g)) := hΩ.2
  have hnegv : ∀ x : V, -x = x := CFSG.RankThree.OrthogonalInvolutions.neg_vec_eq F
  have hsubv : ∀ x y : V, x - y = x + y :=
    CFSG.RankThree.OrthogonalInvolutions.sub_eq_add_vec F
  have hLW : CFSG.RankThree.OrthogonalInvolutions.commSpace g ≤ W := by
    intro x hx
    obtain ⟨v, rfl⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hx
    obtain ⟨w, hw, e, he, rfl⟩ : ∃ w ∈ W, ∃ e ∈ E, w + e = v := by
      have hv : v ∈ W ⊔ E := by
        rw [hWE.sup_eq_top]
        exact Submodule.mem_top
      exact Submodule.mem_sup.mp hv
    have hcancel : g (w + e) - (w + e) = g w - w := by
      rw [map_add, hgE' e he]
      abel
    rw [hcancel]
    exact Submodule.sub_mem W (hgW w hw) hw
  have hEfix : E ≤ CFSG.RankThree.OrthogonalInvolutions.fixSpace g := by
    intro e he
    rw [CFSG.RankThree.OrthogonalInvolutions.mem_fixSpace]
    exact hgE' e he
  have hsup : E ⊔ CFSG.RankThree.OrthogonalInvolutions.commSpace g ≤
      CFSG.RankThree.OrthogonalInvolutions.fixSpace g :=
    sup_le hEfix (CFSG.RankThree.OrthogonalInvolutions.commSpace_le_fixSpace hg2)
  have hEdisj : E ⊓ CFSG.RankThree.OrthogonalInvolutions.commSpace g = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE, hxL⟩ := Submodule.mem_inf.mp hx
    exact (Submodule.disjoint_def.mp hWE.disjoint) x (hLW hxL) hxE
  have hLrank_le : finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace g) ≤ 3 := by
    have h6 : (6 : ℕ) + finrank F E = finrank F V := by
      have h := Submodule.finrank_add_eq_of_isCompl hWE
      omega
    have hLfix := CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_add_finrank_fixSpace g
    have hsup' : finrank F ↥(E ⊔ CFSG.RankThree.OrthogonalInvolutions.commSpace g) =
        finrank F E + finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace g) := by
      have h : finrank F ↥(E ⊔ CFSG.RankThree.OrthogonalInvolutions.commSpace g) +
          finrank F ↥(E ⊓ CFSG.RankThree.OrthogonalInvolutions.commSpace g) =
          finrank F E + finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace g) :=
        Submodule.finrank_sup_add_finrank_inf_eq E
          (CFSG.RankThree.OrthogonalInvolutions.commSpace g)
      rw [hEdisj, finrank_bot, add_zero] at h
      exact h
    have hEL : finrank F E + finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace g) ≤
        finrank F (CFSG.RankThree.OrthogonalInvolutions.fixSpace g) := by
      rw [← hsup']
      exact Submodule.finrank_mono hsup
    omega
  have hone : 1 ≤ finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace g) :=
    CFSG.RankThree.OrthogonalInvolutions.one_le_finrank_commSpace hg1
  have hLrank : finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace g) = 2 := by
    obtain ⟨k, hk⟩ := heven
    omega
  have hLtot : ∀ x, x ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace g → ∀ y,
      y ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace g → polar Q x y = 0 := by
    intro x hx y hy
    exact CFSG.RankThree.OrthogonalInvolutions.polar_commSpace_eq_zero hO hg2 hx hy
  have hLne : CFSG.RankThree.OrthogonalInvolutions.commSpace g ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hLrank
    omega
  obtain ⟨u₁, hu₁L, hu₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hLne
  have hnotle : ¬ CFSG.RankThree.OrthogonalInvolutions.commSpace g ≤ F ∙ u₁ := by
    intro hle
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hu₁0] at h1
    omega
  have hu₂ : ∃ u₂ ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace g, u₂ ∉ F ∙ u₁ := by
    by_contra h
    apply hnotle
    intro x hx
    by_contra hx'
    exact h ⟨x, hx, hx'⟩
  obtain ⟨u₂, hu₂L, hu₂not⟩ := hu₂
  have hu₂0 : u₂ ≠ 0 := by
    intro h
    exact (h ▸ hu₂not) (Submodule.zero_mem (F ∙ u₁))
  have hu₁not₂ : u₁ ∉ F ∙ u₂ := by
    intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hc
      exact hu₁0 hc.symm
    apply hu₂not
    rw [Submodule.mem_span_singleton]
    refine ⟨c⁻¹, ?_⟩
    rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hsum0 : u₁ + u₂ ≠ 0 := by
    intro h
    have h2 : u₂ = u₁ := by
      have := eq_neg_of_add_eq_zero_right h
      rwa [hnegv] at this
    refine hu₂not ?_
    rw [h2]
    exact Submodule.mem_span_singleton_self u₁
  have hu₁not_sum : u₁ ∉ F ∙ (u₁ + u₂) := by
    intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    rcases hF c with hc0 | hc1
    · rw [hc0, zero_smul] at hc
      exact hu₁0 hc.symm
    · rw [hc1, one_smul] at hc
      have h0 : u₂ = 0 := by
        have hc' : u₁ + u₂ = u₁ + 0 := by simpa using hc
        exact add_left_cancel hc'
      exact hu₂0 h0
  have span_le_commSpace : ∀ z y : V,
      z ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace g →
      y ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace g → z ≠ 0 → y ∉ F ∙ z →
      CFSG.RankThree.OrthogonalInvolutions.commSpace g ≤ Submodule.span F {z, y} := by
    intro z y hzL hyL hz0 hyz
    have hli : LinearIndependent F ![z, y] := by
      rw [LinearIndependent.pair_iff' hz0]
      intro c hc
      exact hyz (hc ▸ Submodule.mem_span_singleton.mpr ⟨c, rfl⟩)
    have hfr : finrank F (Submodule.span F {z, y}) = 2 := by
      have h := finrank_span_eq_card hli
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Fintype.card_fin] at h
      exact h
    have hle : Submodule.span F {z, y} ≤ CFSG.RankThree.OrthogonalInvolutions.commSpace g := by
      rw [Submodule.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hzL
      · exact hyL
    have heq : Submodule.span F {z, y} = CFSG.RankThree.OrthogonalInvolutions.commSpace g :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr, hLrank])
    exact le_of_eq heq.symm
  have key : ∀ z y : V, z ≠ 0 → Q z = 0 → polar Q z y = 0 → y ∉ F ∙ z →
      CFSG.RankThree.OrthogonalInvolutions.commSpace g ≤ Submodule.span F {z, y} →
      z ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace g →
      y ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace g → g = eichler Q z y := by
    intro z y hz0 hz hzy hyz hle hzL hyL
    exact eq_eichler_of_sub_mem_span hF hQ hz0 hz hzy hyz hO
      (fun v => hle (CFSG.RankThree.OrthogonalInvolutions.sub_mem_commSpace g v))
      (CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hzL)
      (CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hyL)
  rcases hF (Q u₁) with hq1 | hq1
  · refine ⟨u₁, u₂, hLW hu₁L, hLW hu₂L, hu₁0, hq1, hLtot u₁ hu₁L u₂ hu₂L, hu₂not, ?_⟩
    exact key u₁ u₂ hu₁0 hq1 (hLtot u₁ hu₁L u₂ hu₂L) hu₂not
      (span_le_commSpace u₁ u₂ hu₁L hu₂L hu₁0 hu₂not) hu₁L hu₂L
  rcases hF (Q u₂) with hq2 | hq2
  · refine ⟨u₂, u₁, hLW hu₂L, hLW hu₁L, hu₂0, hq2, hLtot u₂ hu₂L u₁ hu₁L, hu₁not₂, ?_⟩
    exact key u₂ u₁ hu₂0 hq2 (hLtot u₂ hu₂L u₁ hu₁L) hu₁not₂
      (span_le_commSpace u₂ u₁ hu₂L hu₁L hu₂0 hu₁not₂) hu₂L hu₁L
  · have hQsum : Q (u₁ + u₂) = 0 := by
      rw [QuadraticMap.map_add Q u₁ u₂, hLtot u₁ hu₁L u₂ hu₂L, hq1, hq2]
      simpa using CharTwo.add_self_eq_zero (1 : F)
    have hpol : polar Q (u₁ + u₂) u₁ = 0 := by
      rw [polar_add_left, hLtot u₁ hu₁L u₁ hu₁L, hLtot u₂ hu₂L u₁ hu₁L, add_zero]
    have hzL : u₁ + u₂ ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace g :=
      Submodule.add_mem (CFSG.RankThree.OrthogonalInvolutions.commSpace g) hu₁L hu₂L
    refine ⟨u₁ + u₂, u₁, Submodule.add_mem W (hLW hu₁L) (hLW hu₂L), hLW hu₁L, hsum0, hQsum,
      hpol, hu₁not_sum, ?_⟩
    exact key (u₁ + u₂) u₁ hsum0 hQsum hpol hu₁not_sum
      (span_le_commSpace (u₁ + u₂) u₁ hzL hu₁L hsum0 hu₁not_sum) hzL hu₁L

end CFSG.ClassicalGroups.Orthogonal
