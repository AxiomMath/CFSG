module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46Asch
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGenerationM
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46Cent

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

structure Thm46Data (L M₁ M₂ : Subgroup G) : Prop extends Thm46Pair L M₁ M₂ where
  hN : normalizer (M₁ : Set G) = normalizer (M₂ : Set G)
  hfour₁ : ∀ W : Subgroup G, IsKleinFour W → W ≤ M₂ →
    ∃ F : Subgroup G, (∀ x ∈ F, x ^ 2 = 1) ∧ Nat.card F = 8 ∧ W ≤ F ∧ F ≤ coreActionKernel M₁
  hfour₂ : ∀ W : Subgroup G, IsKleinFour W → W ≤ M₁ →
    ∃ F : Subgroup G, (∀ x ∈ F, x ^ 2 = 1) ∧ Nat.card F = 8 ∧ W ≤ F ∧ F ≤ coreActionKernel M₂
  hnab : ∀ P : Sylow 2 (L ⧸ Open.fusionZStar L),
    ∃ x ∈ (P : Subgroup (L ⧸ Open.fusionZStar L)),
      ∃ y ∈ (P : Subgroup (L ⧸ Open.fusionZStar L)), x * y ≠ y * x

namespace Thm46Pair

variable {M₁ M₂ : Subgroup G}

theorem eq_or_eq_of_le_normalizer (h : FooteSec4 G L) (hp : Thm46Pair L M₁ M₂)
    {M' : Subgroup G} (hM' : IsFooteM L M')
    (h1 : M' ≤ normalizer (M₁ : Set G)) (h2 : M' ≤ normalizer (M₂ : Set G))
    (h1' : M₁ ≤ normalizer (M' : Set G)) (h2' : M₂ ≤ normalizer (M' : Set G)) :
    M' = M₁ ∨ M' = M₂ := by
  rcases foote_thm46_pair h hM' hp.hM₁ (commutator_le_inf_of_le_normalizer h1 h1') with
    e1 | ⟨-, c1, -⟩
  · exact Or.inl e1
  rcases foote_thm46_pair h hM' hp.hM₂ (commutator_le_inf_of_le_normalizer h2 h2') with
    e2 | ⟨-, c2, -⟩
  · exact Or.inr e2
  exfalso
  exact hM'.not_odd h (Odd.of_dvd_nat (hp.odd h) (card_dvd_of_le (le_inf c1 c2)))

end Thm46Pair

omit [Finite G] in
theorem map_conj_inv_map_conj (X : Subgroup G) (g : G) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = X := by
  rw [← Thm46Pair.map_conj_mul, inv_mul_cancel]
  ext x
  simp

omit [Finite G] in
theorem map_conj_map_conj_inv (X : Subgroup G) (g : G) :
    (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = X := by
  have h1 := map_conj_inv_map_conj X g⁻¹
  rwa [inv_inv] at h1

omit [Finite G] in
theorem centralizer_le_map_conj {t g : G} {H : Subgroup G}
    (hH : centralizer ({g⁻¹ * t * g} : Set G) ≤ H) :
    centralizer ({t} : Set G) ≤ H.map (MulAut.conj g).toMonoidHom := by
  intro y hy
  refine ⟨g⁻¹ * y * g, hH (mem_centralizer_singleton_iff.mpr ?_), ?_⟩
  · have h1 := mem_centralizer_singleton_iff.mp hy
    calc g⁻¹ * y * g * (g⁻¹ * t * g) = g⁻¹ * (y * t) * g := by group
      _ = g⁻¹ * (t * y) * g := by rw [h1]
      _ = g⁻¹ * t * g * (g⁻¹ * y * g) := by group
  · show (MulAut.conj g) (g⁻¹ * y * g) = y
    rw [MulAut.conj_apply]
    group

namespace Thm46Data

variable {M₁ M₂ : Subgroup G}

theorem le_map_normalizer (h : FooteSec4 G L)
    (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts) (hcalc : FooteSmallCentralizers)
    (hd : Thm46Data L M₁ M₂) {M X : Subgroup G} (hM : M = M₁ ∨ M = M₂) (hXM : X ≤ M)
    (hXp : ⁅X, X⁆ = X) (hcov : M ≤ X ⊔ oddCoreIn M) {g : G}
    (hXg : X.map (MulAut.conj g).toMonoidHom ≤ normalizer ((M₁ ⊔ M₂ : Subgroup G) : Set G)) :
    M₁ ⊔ M₂ ≤ (normalizer ((M₁ ⊔ M₂ : Subgroup G) : Set G)).map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := M₁ ⊔ M₂ with hD
  set H := normalizer (D : Set G) with hH
  have hMF : IsFooteM L M := by rcases hM with rfl | rfl; exacts [hd.hM₁, hd.hM₂]
  set Y := X.map (MulAut.conj g).toMonoidHom with hY
  have hYp : ⁅Y, Y⁆ = Y := by rw [hY, ← Subgroup.map_commutator, hXp]
  have hYN := hd.toThm46Pair.le_normalizer_of_perfect h hXg hYp
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 Y
  have hT' : IsSylowOf 2 (T.map (MulAut.conj g⁻¹).toMonoidHom) X := by
    have h1 := isSylowOf_map_conj hT g⁻¹
    rwa [hY, map_conj_inv_map_conj] at h1
  have hT'M : IsSylowOf 2 (T.map (MulAut.conj g⁻¹).toMonoidHom) M := isSylowOf_of_cover hXM hcov hT'
  have hTiso : ∃ P : Sylow 2 (L ⧸ Open.fusionZStar L),
      Nonempty ((P : Subgroup (L ⧸ Open.fusionZStar L)) ≃* T) := by
    obtain ⟨Q, ⟨eQ⟩⟩ := exists_sylow_mulEquiv_of_isSylowOf h hMF hT'M
    exact ⟨Q, ⟨eQ.trans (T.equivMapOfInjective _ (MulAut.conj g⁻¹).injective).symm⟩⟩
  obtain ⟨W₀, hW₀, hW₀M⟩ := hMF.exists_isKleinFour h
  obtain ⟨W, hW, hWT'⟩ := exists_isKleinFour_le_of_isSylowOf hT'M hW₀ hW₀M
  have hV : IsKleinFour (W.map (MulAut.conj g).toMonoidHom) := by
    refine isKleinFour_of_card_eq_four (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hW.card_four]) ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_pow, sq_eq_one_of_isKleinFour hW hw, map_one]
  have hVT : W.map (MulAut.conj g).toMonoidHom ≤ T := by
    have h1 := map_mono (f := (MulAut.conj g).toMonoidHom) hWT'
    rwa [← Thm46Pair.map_conj_mul, mul_inv_cancel, show (MulAut.conj (1 : G)).toMonoidHom =
      MonoidHom.id G by ext; simp, Subgroup.map_id] at h1
  have hNH : normalizer (M₁ : Set G) ≤ H := fun x hx =>
    mem_normalizer_sup hx (hd.hN ▸ hx)
  have hC : ∀ t ∈ T, orderOf t = 2 →
      centralizer ({t} : Set G) ≤ H.map (MulAut.conj g).toMonoidHom := by
    intro t htT ht
    apply centralizer_le_map_conj
    have ht' : g⁻¹ * t * g ∈ M := by
      have h1 : g⁻¹ * t * g ∈ T.map (MulAut.conj g⁻¹).toMonoidHom :=
        ⟨t, htT, by simp⟩
      exact hXM (hT'.le h1)
    have ht'2 : orderOf (g⁻¹ * t * g) = 2 := by
      rw [show g⁻¹ * t * g = MulAut.conj g⁻¹ t by simp, MulEquiv.orderOf_eq, ht]
    rcases hM with rfl | rfl
    · exact (centralizer_le_normalizer_of_mem h hd.hM₂ hd.hM₁ hd.hN.symm
        (by rw [inf_comm]; exact hd.odd h) hd.hfour₁ ht'2 (hd.h12 ht')).1.trans
        (hd.hN ▸ hNH)
    · exact (centralizer_le_normalizer_of_mem h hd.hM₁ hd.hM₂ hd.hN (hd.odd h) hd.hfour₂ ht'2
        (hd.h21 ht')).1.trans hNH
  exact sup_le
    (le_of_forall_centralizer_le h hK hcalc hd.hM₁ hd.hnab (fun x hx => (hYN (hT.le hx)).1)
      hT.isPGroup hTiso hV hVT hC)
    (le_of_forall_centralizer_le h hK hcalc hd.hM₂ hd.hnab (fun x hx => (hYN (hT.le hx)).2)
      hT.isPGroup hTiso hV hVT hC)

theorem commutator_sup_eq (h : FooteSec4 G L) (hd : Thm46Data L M₁ M₂) :
    ⁅M₁ ⊔ M₂, M₁ ⊔ M₂⁆ = M₁ ⊔ M₂ := by
  refine le_antisymm (commutator_le.mpr fun a ha b hb => ?_) (sup_le ?_ ?_)
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · conv_lhs => rw [← hd.hM₁.commutator_eq h]
    exact commutator_mono le_sup_left le_sup_left
  · conv_lhs => rw [← hd.hM₂.commutator_eq h]
    exact commutator_mono le_sup_right le_sup_right

theorem mem_normalizer_of_cover (h : FooteSec4 G L)
    (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts) (hcalc : FooteSmallCentralizers)
    (hd : Thm46Data L M₁ M₂) {M X : Subgroup G} (hM : M = M₁ ∨ M = M₂) (hXM : X ≤ M)
    (hXp : ⁅X, X⁆ = X) (hcov : M ≤ X ⊔ oddCoreIn M) {g : G}
    (hXg : X.map (MulAut.conj g).toMonoidHom ≤ normalizer ((M₁ ⊔ M₂ : Subgroup G) : Set G)) :
    g ∈ normalizer ((M₁ ⊔ M₂ : Subgroup G) : Set G) := by
  set D := M₁ ⊔ M₂ with hD
  set H := normalizer (D : Set G) with hH
  have hmapN : ∀ x : G, H.map (MulAut.conj x).toMonoidHom =
      normalizer ((D.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) :=
    fun x => Subgroup.map_equiv_normalizer_eq D (MulAut.conj x)
  have h1 := hd.le_map_normalizer h hK hcalc hM hXM hXp hcov hXg
  have hM₁g : M₁.map (MulAut.conj g⁻¹).toMonoidHom ≤ H := by
    have h2 := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (le_sup_left.trans h1)
    rwa [map_conj_inv_map_conj] at h2
  have h2 := hd.le_map_normalizer h hK hcalc (Or.inl rfl) le_rfl (hd.hM₁.commutator_eq h)
    le_sup_left hM₁g
  set D' := D.map (MulAut.conj g).toMonoidHom with hD'
  have hD'N : D' ≤ H := by
    have h3 := map_mono (f := (MulAut.conj g).toMonoidHom) h2
    rwa [map_conj_map_conj_inv] at h3
  have hD''N : D.map (MulAut.conj g⁻¹).toMonoidHom ≤ H := by
    have h3 := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h1
    rwa [map_conj_inv_map_conj] at h3
  have hDp := commutator_sup_eq h hd
  have hD'p : ⁅D', D'⁆ = D' := by rw [hD', ← Subgroup.map_commutator, hDp]
  have hD''p : ⁅D.map (MulAut.conj g⁻¹).toMonoidHom, D.map (MulAut.conj g⁻¹).toMonoidHom⁆ =
      D.map (MulAut.conj g⁻¹).toMonoidHom := by rw [← Subgroup.map_commutator, hDp]
  have hN' := hd.toThm46Pair.le_normalizer_of_perfect h hD'N hD'p
  have hN'' := hd.toThm46Pair.le_normalizer_of_perfect h hD''N hD''p
  have hconj : ∀ N : Subgroup G, N = M₁ ∨ N = M₂ →
      N.map (MulAut.conj g).toMonoidHom = M₁ ∨ N.map (MulAut.conj g).toMonoidHom = M₂ := by
    intro N hN
    have hNF : IsFooteM L N := by rcases hN with rfl | rfl; exacts [hd.hM₁, hd.hM₂]
    have hND : N ≤ D := by rcases hN with rfl | rfl; exacts [le_sup_left, le_sup_right]
    have hN'F : IsFooteM L (N.map (MulAut.conj g).toMonoidHom) := by
      have h3 := isFooteM_conjugate h hNF g⁻¹
      unfold conjugate at h3
      rwa [inv_inv] at h3
    have hN'D : N.map (MulAut.conj g).toMonoidHom ≤ D' := map_mono hND
    have hnorm : ∀ x ∈ D, x ∈ normalizer ((N.map (MulAut.conj g).toMonoidHom : Subgroup G) :
        Set G) := by
      intro x hx
      have hx' : g⁻¹ * x * g ∈ D.map (MulAut.conj g⁻¹).toMonoidHom := ⟨x, hx, by simp⟩
      have hxN : g⁻¹ * x * g ∈ normalizer (N : Set G) := by
        rcases hN with rfl | rfl
        · exact (hN'' hx').1
        · exact (hN'' hx').2
      apply mem_normalizer_of_map_conj_eq
      rw [← Thm46Pair.map_conj_mul, show x * g = g * (g⁻¹ * x * g) by group,
        Thm46Pair.map_conj_mul, map_conj_eq_of_mem_normalizer hxN]
    exact hd.toThm46Pair.eq_or_eq_of_le_normalizer h hN'F
      (fun y hy => (hN' (hN'D hy)).1) (fun y hy => (hN' (hN'D hy)).2)
      (fun y hy => hnorm y ((le_sup_left : M₁ ≤ D) hy))
      (fun y hy => hnorm y ((le_sup_right : M₂ ≤ D) hy))
  have hD'D : D' ≤ D := by
    rw [hD', hD, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rcases hconj M₁ (Or.inl rfl) with e | e <;> rw [e]
      exacts [le_sup_left, le_sup_right]
    · rcases hconj M₂ (Or.inr rfl) with e | e <;> rw [e]
      exacts [le_sup_left, le_sup_right]
  have hD'eq : D' = D := Subgroup.eq_of_le_of_card_ge hD'D
    (by rw [hD', Subgroup.card_map_of_injective (MulAut.conj g).injective])
  exact mem_normalizer_of_map_conj_eq hD'eq

end Thm46Data

end CFSG.ComponentClassification.FooteLit
