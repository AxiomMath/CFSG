module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLargeTorusCore

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix Matrix.ProjGenLinGroup CFSG.Open

variable {G : Type*} [Group G] {Γ : Type*} [Group Γ] {K : Type*} [Field K] {p : ℕ}

noncomputable abbrev frameTorus (L : Γ →* G) (τ : Γ →* GL (Fin p) K)
    (hker : ∀ x, L x = 1 ↔ ∃ u : Kˣ, τ x = GeneralLinearGroup.scalar (Fin p) u)
    (P : GL (Fin p) K) : Subgroup G :=
  ((omegaTorus P).subgroupOf (projHom τ).range).map (rangeLift L τ hker)

variable [Finite G] [Finite K]

omit [Finite G] in
theorem exists_plane_frame (hp : p.Prime) (hp2 : p ≠ 2) (L : Γ →* G)
    (τ : Γ →* GL (Fin p) K) (hτ : Function.Injective τ)
    (hker : ∀ x, L x = 1 ↔ ∃ u : Kˣ, τ x = GeneralLinearGroup.scalar (Fin p) u)
    (D : Subgroup G) (hDL : D ≤ L.range) (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hDp : ∀ x ∈ D, x ^ p = 1) (hcard : Nat.card D = p ^ 2)
    (hna : ¬ ∀ x ∈ D.comap L, ∀ y ∈ D.comap L, x * y = y * x)
    {d : G} (hdD : d ∈ D) (hd1 : d ≠ 1) {A : Γ} (hAd : L A = d)
    (hAdet : (τ A : Matrix (Fin p) (Fin p) K).det = 1) :
    ∃ (ζ : K) (B : Γ) (P : GL (Fin p) K), IsPrimitiveRoot ζ p ∧
      (τ A : Matrix (Fin p) (Fin p) K) * τ B = ζ • ((τ B : Matrix (Fin p) (Fin p) K) * τ A) ∧
      (τ A : Matrix (Fin p) (Fin p) K) = (P : Matrix (Fin p) (Fin p) K) *
        diagonal (fun i : Fin p => ζ ^ (i : ℕ)) *
          ((P⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) := by
  obtain ⟨e, heD, hde⟩ := exists_closure_pair_of_mem hp hDp hcard hdD hd1
  obtain ⟨B, hBe⟩ := hDL heD
  obtain ⟨-, -, hroot⟩ := plane_transport hp L τ hτ hker D hDL hDab hDp hcard hna
  obtain ⟨ζ, hζ, hAB⟩ := hroot A B (by rw [hAd, hBe]; exact hde)
  obtain ⟨P, hP⟩ := exists_eigenbasis hp hp2 hζ (τ B).isUnit hAB hAdet
  exact ⟨ζ, B, P, hζ, hAB, hP⟩

omit [Finite K] in
theorem large_torus_of_given_frame (hp : p.Prime) (hp5 : 5 ≤ p) (L : Γ →* G)
    (τ : Γ →* GL (Fin p) K)
    (hker : ∀ x, L x = 1 ↔ ∃ u : Kˣ, τ x = GeneralLinearGroup.scalar (Fin p) u)
    (Inn : Subgroup G) (hInn : Inn.Normal) (hIN : L.range.Normal)
    (D : Subgroup G) {d : G} (hdD : d ∈ D) (hd1 : d ≠ 1) {A : Γ} (hAd : L A = d)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (P : GL (Fin p) K)
    (hP : (τ A : Matrix (Fin p) (Fin p) K) = (P : Matrix (Fin p) (Fin p) K) *
      diagonal (fun i : Fin p => ζ ^ (i : ℕ)) * ((P⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K))
    (hUJ : omegaTorus P ≤ (projHom τ).range)
    (hWinn : ∀ y ∈ detOneTorus P, ∀ hy : y ∈ (projHom τ).range,
      rangeLift L τ hker ⟨y, hy⟩ ∈ Inn) :
    frameTorus L τ hker P ≤ L.range ⊓ Subgroup.centralizer {d} ∧
      (∀ x ∈ frameTorus L τ hker P, ∀ y ∈ frameTorus L τ hker P, x * y = y * x) ∧
      (∀ x ∈ frameTorus L τ hker P, x ^ p = 1) ∧ Nat.card (frameTorus L τ hker P) = p ^ (p - 1) ∧
      ((frameTorus L τ hker P).subgroupOf (L.range ⊓ Subgroup.centralizer {d})).Characteristic ∧
      ((frameTorus L τ hker P).subgroupOf (Subgroup.centralizer {d})).Normal ∧
      d ∈ frameTorus L τ hker P ∧
      (∃ k, p - 2 ≤ k ∧ Nat.card (frameTorus L τ hker P ⊓ Inn : Subgroup G) = p ^ k) ∧
      (∀ y ∈ detOneTorus P, ∀ hy : y ∈ (projHom τ).range,
        rangeLift L τ hker ⟨y, hy⟩ ∈ frameTorus L τ hker P ⊓ Inn) ∧
      (∀ x ∈ localDelta p ⊤ D, ∀ u ∈ frameTorus L τ hker P, x * u = u * x) ∧
      ∀ H : Subgroup G, Inn ≤ H → D ≤ H →
        ∀ x ∈ localDelta p H D, ∀ v ∈ (frameTorus L τ hker P ⊓ Inn : Subgroup G),
          x * v = v * x := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  set ζu : Kˣ := Units.mk0 ζ (hζ.ne_zero hp.ne_zero)
  have hζu : ζu ^ p = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, hζ.pow_eq_one, Units.val_one])
  set J := (projHom τ).range
  set ι := rangeLift L τ hker
  have hιinj := rangeLift_injective L τ hker
  have hιrange := range_rangeLift L τ hker
  have hAP : τ A = P * TauCeti.diagGL (rootVec ζu) * P⁻¹ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, TauCeti.diagGL_coe, hP]
    rfl
  have hd'J : frameElt P ζu ∈ J := ⟨A, by rw [MonoidHom.comp_apply, hAP]; rfl⟩
  set d' : J := ⟨frameElt P ζu, hd'J⟩
  have hιd' : ι d' = d := by
    rw [← hAd, ← rangeLift_apply L τ hker A]
    congr 1
    exact Subtype.ext (by rw [MonoidHom.coe_rangeRestrict, MonoidHom.comp_apply, hAP]; rfl)
  set U := frameTorus L τ hker P with hUdef
  have hUmem : ∀ {y : J}, (y : ProjGenLinGroup (Fin p) K) ∈ omegaTorus P → ι y ∈ U :=
    fun hy => ⟨_, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  have hUI : U ≤ L.range := by
    rw [← hιrange]
    exact Subgroup.map_le_range ι _
  have hUd : U ≤ Subgroup.centralizer {d} := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg, ← hιd', ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact omegaTorus_comm P _ (torusHom_mem_omegaTorus P (rootVec_mem_powEqSubgroup hζu)) _
      (Subgroup.mem_subgroupOf.1 hy)
  have hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ι (Subtype.ext (omegaTorus_comm P _ (Subgroup.mem_subgroupOf.1 ha) _
      (Subgroup.mem_subgroupOf.1 hb)))
  have hUp : ∀ x ∈ U, x ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, ← map_one ι]
    exact congrArg ι (Subtype.ext (by
      rw [SubmonoidClass.coe_pow]; exact omegaTorus_pow P _ (Subgroup.mem_subgroupOf.1 ha)))
  have hUcard : Nat.card U = p ^ (p - 1) := by
    rw [Subgroup.card_map_of_injective hιinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUJ).toEquiv, card_omegaTorus P hζ]
  have hdU : d ∈ U := by
    rw [← hιd']
    exact hUmem (torusHom_mem_omegaTorus P (rootVec_mem_powEqSubgroup hζu))
  have hp2lt : p ^ 2 < Nat.card U := by
    rw [hUcard]
    exact Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hmax : ∀ E : Subgroup G, E ≤ L.range ⊓ Subgroup.centralizer {d} →
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ p = 1) → p ^ 2 < Nat.card E →
        E ≤ U := by
    intro E hE hEab hEp hEcard
    refine le_map_of_elementary ι hιinj d' (fun E' hE' hE'ab hE'p hE'c =>
      le_omegaTorus_of_elementary hp hζ hE' hE'ab hE'p hE'c) ?_ ?_ hEab hEp hEcard
    · rw [hιrange]
      exact fun x hx => (hE hx).1
    · rw [hιd']
      exact fun x hx => (hE hx).2
  have hUC : U ≤ L.range ⊓ Subgroup.centralizer {d} := le_inf hUI hUd
  have hchar := characteristic_of_max hUC hUab hUp hp2lt hmax
  have hconj : ∀ g : G, g * d = d * g → ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
    intro g hg
    refine conj_mem_of_max hUC hUab hUp hp2lt hmax fun c hc =>
      Subgroup.mem_inf.2 ⟨hIN.conj_mem c (Subgroup.mem_inf.1 hc).1 g, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.1 hx]
    have hcd : Commute d c := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 d rfl
    have hdg : Commute d g := hg.symm
    exact ((hdg.mul_right hcd).mul_right hdg.inv_right).eq
  have hnormal : (U.subgroupOf (Subgroup.centralizer {d})).Normal := by
    refine ⟨fun u hu g => Subgroup.mem_subgroupOf.2 ?_⟩
    have hg : (g : G) * d = d * g := (Subgroup.mem_centralizer_iff.1 g.2 d rfl).symm
    exact hconj g hg u (Subgroup.mem_subgroupOf.1 hu)
  have hWU : ∀ y ∈ detOneTorus P, ∀ hy : y ∈ J, ι ⟨y, hy⟩ ∈ U ⊓ Inn := fun y hy hyJ =>
    ⟨hUmem (detOneTorus_le P hy), hWinn y hy hyJ⟩
  have hW : ((detOneTorus P).subgroupOf J).map ι ≤ U ⊓ Inn := by
    rintro _ ⟨y, hy, rfl⟩
    exact hWU _ (Subgroup.mem_subgroupOf.1 hy) y.2
  have hWcard : Nat.card (((detOneTorus P).subgroupOf J).map ι) = p ^ (p - 2) := by
    rw [Subgroup.card_map_of_injective hιinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe ((detOneTorus_le P).trans hUJ)).toEquiv,
      card_detOneTorus P hζ (by omega)]
  have hVrank : ∃ k, p - 2 ≤ k ∧ Nat.card (U ⊓ Inn : Subgroup G) = p ^ k := by
    have := Fact.mk hp
    have hpg : IsPGroup p (U ⊓ Inn : Subgroup G) := fun x => ⟨1, by
      rw [pow_one]
      exact Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hUp x x.2.1)⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hpg
    refine ⟨k, ?_, hk⟩
    have hle := Subgroup.card_le_of_le hW
    rw [hWcard, hk] at hle
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
  refine ⟨hUC, hUab, hUp, hUcard, hchar, hnormal, hdU, hVrank, hWU, ?_, ?_⟩
  · intro x hx u hu
    exact localDelta_commute hp hdD hd1 le_top le_top hUd (fun g _ hg v hv => hconj g hg v hv)
      hUp hx hu
  · intro H hInnH hDH x hx v hv
    refine localDelta_commute hp hdD hd1 hDH (fun w hw => hInnH (Subgroup.mem_inf.1 hw).2)
      (fun w hw => hUd (Subgroup.mem_inf.1 hw).1)
      (fun g _ hg w hw => Subgroup.mem_inf.2 ⟨hconj g hg w (Subgroup.mem_inf.1 hw).1,
        hInn.conj_mem w (Subgroup.mem_inf.1 hw).2 g⟩)
      (fun w hw => hUp w (Subgroup.mem_inf.1 hw).1) hx hv

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
