module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RY0

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

section Realization

variable {M : Type*} [Group M] {P R : Subgroup M}

theorem real_conj (hPR : P ≤ R) (e : ↥R ≃* MulAut ↥P)
    (he : ∀ (x : ↥R) (p : ↥P), (((e x) p : ↥P) : M) = (x : M) * (p : M) * (x : M)⁻¹)
    {y : M} (hy : y ∈ P) : e ⟨y, hPR hy⟩ = MulAut.conj (⟨y, hy⟩ : ↥P) := by
  ext p
  rw [he]
  simp [MulAut.conj_apply]

end Realization

theorem S16Model.of_realization {M : Type*} [Group M] [Finite M] {P R : Subgroup M} (hPR : P ≤ R)
    (e : ↥R ≃* MulAut ↥P)
    (he : ∀ (x : ↥R) (p : ↥P), (((e x) p : ↥P) : M) = (x : M) * (p : M) * (x : M)⁻¹)
    {t b r v x : M} (ht : t ∈ P) (hb : b ∈ P) (hr : r ∈ R) (hrP : r ∉ P) (hv : v ∈ P)
    (hx : x ∈ P)
    (r_sq : r * r = 1) (r_t : r * t * r⁻¹ = t) (r_b : r * b * r⁻¹ = b⁻¹)
    (v_t : v * t = t * v) (x_t : x * t = t * x) (v4 : v ^ 4 = t) (v8 : v ^ 8 = 1)
    (x_sq : x * x = 1) (x_ne_one : x ≠ 1) (x_ne_t : x ≠ t) (x_v : x * v * x⁻¹ = v⁻¹)
    (r_v : r * v * r⁻¹ = v * t) (r_x : r * x * r⁻¹ = x * t) (v_b : v * b * v⁻¹ = b⁻¹)
    (x_b : x * b * x⁻¹ = b⁻¹)
    (roots : Set M) (hroots : ∀ y ∈ roots, y ∈ P ∧ y * y = t)
    (hrootcard : Nat.card ↥(rootGroup ↥P ⟨t, ht⟩) = 32)
    (hE1card : Nat.card ↥(closure roots) = 32)
    (hCEcard : Nat.card ↥(closure roots ⊓ centralizer ({r} : Set M)) = 8)
    (hCE : closure ({v * v, v * x} : Set M) = closure roots ⊓ centralizer ({r} : Set M))
    (hY : Nat.card ↥(closure ({v, x, r} : Set M)) = 32)
    (cs : Set M) (hcsR : ∀ c ∈ cs, c ∈ R)
    (hcsΘ : ∀ c ∈ cs, (c ∈ P ∧ c * t = t * c) ∨ (∃ y, y ∈ P ∧ y * t = t * y ∧ c = y * r))
    (hcsx : ∀ c ∈ cs, c * x = x * c) (hC : Nat.card ↥(closure cs) = 32)
    (htC : t ∈ closure cs) (hxC : x ∈ closure cs)
    (hquad : ∀ c ∈ closure cs, c * c = 1 ∨ c * c = t ∨ c * c = x ∨ c * c = t * x)
    (hcomm : ∀ c ∈ closure cs, ∀ d ∈ closure cs, c * d * c⁻¹ * d⁻¹ = 1 ∨
      c * d * c⁻¹ * d⁻¹ = t ∨ c * d * c⁻¹ * d⁻¹ = x ∨ c * d * c⁻¹ * d⁻¹ = t * x) :
    S16Model ↥P ⟨t, ht⟩ ⟨b, hb⟩ := by
  classical
  have hconj := fun {y : M} (hy : y ∈ P) => real_conj hPR e he hy
  set t' : ↥P := ⟨t, ht⟩ with ht'
  set b' : ↥P := ⟨b, hb⟩ with hb'
  set v' : ↥P := ⟨v, hv⟩ with hv'
  set x' : ↥P := ⟨x, hx⟩ with hx'
  set r' : MulAut ↥P := e ⟨r, hr⟩ with hr'
  have hr'app : ∀ p : ↥P, ((r' p : ↥P) : M) = r * p * r⁻¹ := fun p => he ⟨r, hr⟩ p
  refine ⟨r', v', x', ?_⟩
  have hcsle : closure cs ≤ R := (Subgroup.closure_le R).2 hcsR
  have hE1P : closure roots ≤ P := (Subgroup.closure_le P).2 fun y hy => (hroots y hy).1
  have hRoot : (rootGroup ↥P t').map P.subtype = closure roots := by
    have hle : closure roots ≤ (rootGroup ↥P t').map P.subtype := by
      rw [Subgroup.closure_le]
      intro y hy
      refine ⟨⟨y, (hroots y hy).1⟩, subset_closure ?_, rfl⟩
      exact Subtype.ext (hroots y hy).2
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [Subgroup.card_map_of_injective P.subtype_injective, hrootcard, hE1card]
  have hfix : (fixedSub r').map P.subtype = P ⊓ centralizer ({r} : Set M) := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p.2, ?_⟩
      show (p : M) ∈ centralizer ({r} : Set M)
      rw [mem_centralizer_singleton_iff]
      have h1 : r * (p : M) * r⁻¹ = p := by
        rw [← hr'app]
        exact congrArg Subtype.val hp
      calc (p : M) * r = (r * p * r⁻¹) * r := by rw [h1]
        _ = r * p := by group
    · rintro ⟨hyP, hyc⟩
      refine ⟨⟨y, hyP⟩, ?_, rfl⟩
      show r' ⟨y, hyP⟩ = ⟨y, hyP⟩
      apply Subtype.ext
      rw [hr'app]
      have := mem_centralizer_singleton_iff.1 hyc
      calc r * y * r⁻¹ = (y * r) * r⁻¹ := by rw [this]
        _ = y := by group
  have hmapE : (rootGroup ↥P t' ⊓ fixedSub r').map P.subtype =
      closure roots ⊓ centralizer ({r} : Set M) := by
    rw [Subgroup.map_inf _ _ _ P.subtype_injective, hRoot, hfix]
    ext y
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hE1P h1, h2⟩
  have hcomm' : ∀ c ∈ closure cs, c * x = x * c := by
    intro c hc
    have : closure cs ≤ centralizer ({x} : Set M) := by
      rw [Subgroup.closure_le]
      intro c hc'
      exact mem_centralizer_singleton_iff.2 (hcsx c hc')
    exact mem_centralizer_singleton_iff.1 (this hc)
  refine
  { r_sq := ?_, r_outer := ?_, r_t := ?_, r_β := ?_, v_t := ?_, ξ_t := ?_, v4 := ?_, v8 := ?_,
    ξ_sq := ?_, ξ_ne_one := ?_, ξ_ne_t := ?_, ξ_v := ?_, r_v := ?_, r_ξ := ?_, v_β := ?_,
    ξ_β := ?_, card_CE := ?_, CE_eq := ?_, card_Y := ?_, rank5 := ?_ }
  · have h : (⟨r, hr⟩ : ↥R) * ⟨r, hr⟩ = 1 := Subtype.ext r_sq
    rw [hr', ← map_mul, h, map_one]
  · rintro ⟨y, hy⟩
    apply hrP
    have h1 : e ⟨r, hr⟩ = e ⟨(y : M), hPR y.2⟩ := by
      rw [hconj y.2]
      exact hy
    have h2 := e.injective h1
    have h3 : r = (y : M) := congrArg Subtype.val h2
    rw [h3]
    exact y.2
  · apply Subtype.ext
    rw [hr'app]
    exact r_t
  · apply Subtype.ext
    rw [hr'app]
    exact r_b
  · exact Subtype.ext v_t
  · exact Subtype.ext x_t
  · apply Subtype.ext
    simpa using v4
  · apply Subtype.ext
    simpa using v8
  · exact Subtype.ext x_sq
  · exact fun h => x_ne_one (congrArg Subtype.val h)
  · exact fun h => x_ne_t (congrArg Subtype.val h)
  · exact Subtype.ext x_v
  · apply Subtype.ext
    rw [hr'app]
    exact r_v
  · apply Subtype.ext
    rw [hr'app]
    exact r_x
  · exact Subtype.ext v_b
  · exact Subtype.ext x_b
  · calc Nat.card ↥(rootGroup ↥P t' ⊓ fixedSub r') =
        Nat.card ↥((rootGroup ↥P t' ⊓ fixedSub r').map P.subtype) :=
          (Subgroup.card_map_of_injective P.subtype_injective).symm
      _ = 8 := by rw [hmapE]; exact hCEcard
  · apply Subgroup.map_injective P.subtype_injective
    rw [hmapE, MonoidHom.map_closure, ← hCE]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, (rfl | rfl), rfl⟩
      · left; rfl
      · right; rfl
    · rintro (rfl | rfl)
      · exact ⟨v' * v', Or.inl rfl, rfl⟩
      · exact ⟨v' * x', Or.inr rfl, rfl⟩
  · have hYeq : closure ({MulAut.conj v', MulAut.conj x', r'} : Set (MulAut ↥P)) =
        (closure ({(⟨v, hPR hv⟩ : ↥R), ⟨x, hPR hx⟩, ⟨r, hr⟩} : Set ↥R)).map e.toMonoidHom := by
      rw [MonoidHom.map_closure]
      congr 1
      ext y
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (rfl | rfl | rfl)
        · exact ⟨_, Or.inl rfl, hconj hv⟩
        · exact ⟨_, Or.inr (Or.inl rfl), hconj hx⟩
        · exact ⟨_, Or.inr (Or.inr rfl), rfl⟩
      · rintro ⟨z, (rfl | rfl | rfl), rfl⟩
        · left; exact hconj hv
        · right; left; exact hconj hx
        · right; right; rfl
    have hYmap : (closure ({(⟨v, hPR hv⟩ : ↥R), ⟨x, hPR hx⟩, ⟨r, hr⟩} : Set ↥R)).map
        R.subtype = closure ({v, x, r} : Set M) := by
      rw [MonoidHom.map_closure]
      congr 1
      ext y
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨z, (rfl | rfl | rfl), rfl⟩
        · left; rfl
        · right; left; rfl
        · right; right; rfl
      · rintro (rfl | rfl | rfl)
        · exact ⟨⟨_, hPR hv⟩, Or.inl rfl, rfl⟩
        · exact ⟨⟨_, hPR hx⟩, Or.inr (Or.inl rfl), rfl⟩
        · exact ⟨⟨_, hr⟩, Or.inr (Or.inr rfl), rfl⟩
    rw [hYeq, Subgroup.card_map_of_injective e.injective,
      ← Subgroup.card_map_of_injective R.subtype_injective, hYmap]
    exact hY
  · set C0 : Subgroup M := closure cs with hC0
    have hΘ : ∀ c ∈ C0, ∃ hc : c ∈ R, e ⟨c, hc⟩ ∈ thetaSub t' r' := by
      have hle : C0 ≤ ((thetaSub t' r').comap e.toMonoidHom).map R.subtype := by
        rw [hC0, Subgroup.closure_le]
        intro c hc
        have hcR := hcsR c hc
        refine ⟨⟨c, hcR⟩, ?_, rfl⟩
        show e ⟨c, hcR⟩ ∈ thetaSub t' r'
        rcases hcsΘ c hc with ⟨hcP, hct⟩ | ⟨y, hyP, hyt, rfl⟩
        · rw [hconj hcP]
          apply mem_sup_left
          refine ⟨⟨c, hcP⟩, ?_, rfl⟩
          rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
          exact Subtype.ext hct
        · have h1 : (⟨y * r, hcR⟩ : ↥R) = ⟨y, hPR hyP⟩ * ⟨r, hr⟩ := rfl
          rw [h1, map_mul, hconj hyP]
          apply mul_mem
          · apply mem_sup_left
            refine ⟨⟨y, hyP⟩, ?_, rfl⟩
            rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
            exact Subtype.ext hyt
          · exact mem_sup_right (mem_zpowers _)
      intro c hc
      obtain ⟨z, hz, rfl⟩ := hle hc
      exact ⟨z.2, hz⟩
    have hqS : ∀ w : ↥R, ((w : M) = 1 ∨ (w : M) = t ∨ (w : M) = x ∨ (w : M) = t * x) →
        e w ∈ quadSet t' x' := by
      intro w h
      rcases h with h | h | h | h
      · have : w = 1 := Subtype.ext h
        rw [this, map_one]
        exact Or.inl rfl
      · have : w = ⟨t, hPR ht⟩ := Subtype.ext h
        rw [this, hconj ht]
        exact Or.inr (Or.inl rfl)
      · have : w = ⟨x, hPR hx⟩ := Subtype.ext h
        rw [this, hconj hx]
        exact Or.inr (Or.inr (Or.inl rfl))
      · have : w = ⟨t, hPR ht⟩ * ⟨x, hPR hx⟩ := Subtype.ext h
        rw [this, map_mul, hconj ht, hconj hx]
        exact Or.inr (Or.inr (Or.inr rfl))
    refine ⟨(C0.subgroupOf R).map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨c, hc, rfl⟩
      obtain ⟨hc', hmem⟩ := hΘ (c : M) (Subgroup.mem_subgroupOf.1 hc)
      exact hmem
    · exact ⟨⟨t, hPR ht⟩, Subgroup.mem_subgroupOf.2 htC, hconj ht⟩
    · exact ⟨⟨x, hPR hx⟩, Subgroup.mem_subgroupOf.2 hxC, hconj hx⟩
    · rintro _ ⟨c, hc, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have hcx := hcomm' (c : M) (Subgroup.mem_subgroupOf.1 hc)
      show e c * MulAut.conj x' = MulAut.conj x' * e c
      rw [← hconj hx, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hcx
    · rw [Subgroup.card_map_of_injective e.injective]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcsle).toEquiv]
      exact hC
    · rintro _ ⟨c, hc, rfl⟩
      show e c * e c ∈ quadSet t' x'
      rw [← map_mul]
      exact hqS _ (hquad _ (Subgroup.mem_subgroupOf.1 hc))
    · rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
      show e c * e d * (e c)⁻¹ * (e d)⁻¹ ∈ quadSet t' x'
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact hqS _ (hcomm _ (Subgroup.mem_subgroupOf.1 hc) _ (Subgroup.mem_subgroupOf.1 hd))

end CFSG.EvenSporadicStandard.Fin76b
