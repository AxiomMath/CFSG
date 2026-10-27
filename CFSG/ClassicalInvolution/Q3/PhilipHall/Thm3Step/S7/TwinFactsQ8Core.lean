module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.CertQ8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Twin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Cert Certificates.S5Rows

section Wit

variable {G : Type*} [Group G]

@[expose] def PairWit (x₀ y₀ r y c : G) : Prop :=
  (∀ t ∈ q8Span r y, c * t * c⁻¹ ∈ q8Span x₀ y₀) ∨
  ((∃ t ∈ q8Span r y, c * t * c⁻¹ ∉ q8Span r y) ∧
    ∃ a ∈ q8Span r y, a * a ≠ 1 ∧ ∃ t ∈ q8Span r y, c * t * c⁻¹ = a) ∨
  ((∃ t ∈ q8Span r y, c * t * c⁻¹ = r * r) ∧
    (∀ a ∈ q8Span r y, a * a ≠ 1 → ∀ t ∈ q8Span r y, c * t * c⁻¹ ≠ a) ∧
    ∃ k ∈ q8Span r y, ∃ t ∈ q8Span r y, k * (c * t * c⁻¹) ≠ c * t * c⁻¹ * k)

variable {N : Type*} [Group N] {f : G →* N}

theorem exists_eq_of_mem_q8Span_map {i j : G} {y : N} (hy : y ∈ q8Span (f i) (f j)) :
    ∃ x ∈ q8Span i j, f x = y :=
  exists_of_mem_q8Span_map f hy

theorem mem_of_map_mem_q8Span (hf : Function.Injective f) {i j x : G}
    (h : f x ∈ q8Span (f i) (f j)) : x ∈ q8Span i j := by
  obtain ⟨u, hu, hux⟩ := exists_of_mem_q8Span_map f h
  rwa [← hf hux]

theorem map_conj (c t : G) : f (c * t * c⁻¹) = f c * f t * (f c)⁻¹ := by
  rw [map_mul, map_mul, map_inv]

theorem PairWit.of_map (hf : Function.Injective f) {x₀ y₀ r y c : G}
    (h : PairWit (f x₀) (f y₀) (f r) (f y) (f c)) : PairWit x₀ y₀ r y c := by
  rcases h with h | ⟨⟨t', ht', hJ⟩, a', ha', ha2, t'', ht'', hta⟩ |
    ⟨⟨t', ht', hz⟩, hno, k', hk', t'', ht'', hkt⟩
  · refine Or.inl fun t ht => mem_of_map_mem_q8Span hf ?_
    rw [map_conj]
    exact h _ (mem_q8Span_map f ht)
  · obtain ⟨t, ht, rfl⟩ := exists_eq_of_mem_q8Span_map ht'
    obtain ⟨a, ha, rfl⟩ := exists_eq_of_mem_q8Span_map ha'
    obtain ⟨u, hu, rfl⟩ := exists_eq_of_mem_q8Span_map ht''
    refine Or.inr (Or.inl ⟨⟨t, ht, fun hm => hJ ?_⟩, a, ha, fun h1 => ha2 ?_, u, hu, ?_⟩)
    · rw [← map_conj]
      exact mem_q8Span_map f hm
    · rw [← map_mul, h1, map_one]
    · apply hf
      rw [map_conj]
      exact hta
  · obtain ⟨t, ht, rfl⟩ := exists_eq_of_mem_q8Span_map ht'
    obtain ⟨k, hk, rfl⟩ := exists_eq_of_mem_q8Span_map hk'
    obtain ⟨u, hu, rfl⟩ := exists_eq_of_mem_q8Span_map ht''
    refine Or.inr (Or.inr ⟨⟨t, ht, hf ?_⟩, fun a ha ha2 s hs he => ?_, k, hk, u, hu, fun he => ?_⟩)
    · rw [map_conj, map_mul]
      exact hz
    · refine hno (f a) (mem_q8Span_map f ha) (fun h1 => ha2 (hf ?_)) (f s) (mem_q8Span_map f hs) ?_
      · rw [map_mul, h1, map_one]
      · rw [← map_conj, he]
    · apply hkt
      rw [← map_conj, ← map_mul, ← map_mul, he]

end Wit

section Omega

variable {G : Type} [Group G] [Finite G] [DecidableEq G]

theorem classicalInvolutionOddCore_eq_bot_of_isPGroup {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) : classicalInvolutionOddCore P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (classicalInvolutionOddCore P)) :=
    CFSG.ComponentClassification.OddCore.odd_card P
  obtain ⟨k, hk⟩ := (hP.to_subgroup (classicalInvolutionOddCore P)).exists_card_eq
  apply Subgroup.eq_bot_of_card_eq
  rw [hk] at hodd ⊢
  rcases k with _ | k
  · rfl
  · exact absurd hodd (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, by omega⟩))

theorem oddCoreOf_eq_bot_of_twoGroup {T : Subgroup G} (hT : IsPGroup 2 T) : oddCoreOf T = ⊥ := by
  rw [oddCoreOf, classicalInvolutionOddCore_eq_bot_of_isPGroup hT, Subgroup.map_bot]

theorem four_dvd_orderOf {T : Subgroup G} (hT : Nat.card T = 8) {a : G} (ha : a ∈ T)
    (ha2 : a * a ≠ 1) : 4 ∣ orderOf a := by
  have h8 : orderOf a ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hT]
    exact Subgroup.orderOf_dvd_natCard T ha
  obtain ⟨m, hm, hmo⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h8
  rw [hmo]
  by_cases h2 : 2 ≤ m
  · exact (by norm_num : (4 : ℕ) = 2 ^ 2) ▸ pow_dvd_pow 2 h2
  · exfalso
    apply ha2
    have h1 : orderOf a ∣ 2 := by
      rw [hmo]
      exact (pow_dvd_pow 2 (by omega : m ≤ 1)).trans (by norm_num)
    rw [← sq]
    exact orderOf_dvd_iff_pow_eq_one.mp h1

theorem mem_conjClass_or_not_hypOmegaGen {x₀ y₀ r y c : G} (h0 : Q8Rel x₀ y₀) (h : Q8Rel r y)
    (hw : PairWit x₀ y₀ r y c) :
    Subgroup.closure ({r, y} : Set G) ∈
        CoreAssembly.conjClass (Subgroup.closure ({x₀, y₀} : Set G)) ∨
      ¬ HypOmegaGen (CoreAssembly.conjClass (Subgroup.closure ({r, y} : Set G))) := by
  set T := Subgroup.closure ({r, y} : Set G) with hTdef
  set J := conjSub c T with hJdef
  have hT : ∀ {x : G}, x ∈ T ↔ x ∈ q8Span r y := fun {x} => mem_closure_pair_iff h
  have hJ : ∀ {x : G}, x ∈ J ↔ c⁻¹ * x * c ∈ T := fun {x} => mem_conjSub_iff
  have hJc : ∀ {t : G}, t ∈ q8Span r y → c * t * c⁻¹ ∈ J := fun ht =>
    conj_mem_conjSub (hT.mpr ht)
  have hcardT : Nat.card T = 8 := card_closure_pair h
  have hcardJ : Nat.card J = 8 := by
    rw [hJdef, conjSub, Subgroup.card_map_of_injective (MulAut.conj c).injective, hcardT]
  have hJm : J ∈ CoreAssembly.conjClass T := ⟨c, rfl⟩
  have hTm : T ∈ CoreAssembly.conjClass T := CoreAssembly.mem_conjClass_self T
  rcases hw with hg | ⟨⟨t, ht, hJT⟩, a, ha, ha2, s, hs, hsa⟩ | ⟨⟨t, ht, hz⟩, hno, k, hk, s, hs, hks⟩
  ·
    left
    have hle : J ≤ Subgroup.closure ({x₀, y₀} : Set G) := by
      intro x hx
      have hx' := hT.mp (hJ.mp hx)
      have := hg _ hx'
      rw [show c * (c⁻¹ * x * c) * c⁻¹ = x by group] at this
      exact (mem_closure_pair_iff h0).mpr this
    have heq : J = Subgroup.closure ({x₀, y₀} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [card_closure_pair h0, hcardJ])
    refine ⟨c⁻¹, ?_⟩
    show conjSub c⁻¹ (Subgroup.closure ({x₀, y₀} : Set G)) = T
    rw [← heq, hJdef, conjSub_inv_conjSub]
  ·
    right
    intro hΩ
    have hne : T ≠ J := by
      intro he
      exact hJT (hT.mp (he ▸ hJc ht))
    have h4 := (hΩ.omega4 T hTm J hJm hne).1
    have haT : a ∈ T := hT.mpr ha
    have haJ : a ∈ J := hsa ▸ hJc hs
    have hdvd : 2 ^ 2 ∣ Nat.card ↥(T ⊓ J) := by
      have h1 : orderOf a ∣ Nat.card ↥(T ⊓ J) :=
        Subgroup.orderOf_dvd_natCard (T ⊓ J) (Subgroup.mem_inf.mpr ⟨haT, haJ⟩)
      exact (four_dvd_orderOf hcardT haT ha2).trans h1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 := (padicValNat_dvd_iff_le (p := 2) Nat.card_pos.ne').mp hdvd
    omega
  ·
    right
    intro hΩ
    have hz2 : r * r ≠ 1 := by rw [← sq]; exact h.2.1
    have hinter : ((T ⊓ J : Subgroup G) : Set G) = {1, r * r} := by
      ext x
      simp only [SetLike.mem_coe, Subgroup.mem_inf, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hxT, hxJ⟩
        have hxx : x * x = 1 := by
          by_contra hxx
          exact hno x (hT.mp hxT) hxx _ (hT.mp (hJ.mp hxJ)) (by group)
        exact (isUniqueInvolution_closure_pair h).unique x hxT hxx
      · rintro (rfl | rfl)
        · exact ⟨T.one_mem, J.one_mem⟩
        · exact ⟨(isUniqueInvolution_closure_pair h).mem, hz ▸ hJc ht⟩
    have hcard2 : Nat.card ↥(T ⊓ J) = 2 := by
      rw [show Nat.card ↥(T ⊓ J) = Nat.card ((T ⊓ J : Subgroup G) : Set G) from rfl,
        Nat.card_coe_set_eq, hinter, Set.ncard_pair (Ne.symm hz2)]
    have hne : T ≠ J := by
      intro he
      rw [← he, inf_idem, hcardT] at hcard2
      omega
    have h4 := (hΩ.omega4 T hTm J hJm hne).2 (by rw [hcard2]; exact padicValNat.self (by norm_num))
    have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 3) (by rw [hcardT]; norm_num)
    have hJ2 : IsPGroup 2 J := IsPGroup.of_card (n := 3) (by rw [hcardJ]; norm_num)
    rw [oddCoreOf_eq_bot_of_twoGroup hT2, oddCoreOf_eq_bot_of_twoGroup hJ2, inf_idem,
      le_bot_iff] at h4
    have hmem := Subgroup.commutator_mem_commutator (hT.mpr hk) (hJc hs)
    rw [h4, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hks hmem

end Omega

section Model

variable {n : ℕ}

theorem mem_conjClass_of_model (H S : Subgroup (Equiv.Perm (Fin n))) (hSH : S ≤ H)
    (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ (S.subgroupOf H).index) (reps : List (Equiv.Perm (Fin n)))
    (hcov : ∀ u ∈ S, orderOf u = 4 → ∃ r ∈ reps, ∃ s ∈ S, u = s * r * s⁻¹)
    {x₀ y₀ : Equiv.Perm (Fin n)} (hx₀ : x₀ ∈ H) (hy₀ : y₀ ∈ H) (h0 : Q8Rel x₀ y₀)
    (hwit : ∀ r ∈ reps, ∀ y ∈ S, Q8Rel r y → ∃ c ∈ H, PairWit x₀ y₀ r y c)
    (T : Subgroup ↥H) (hT : Nonempty (↥T ≃* QuaternionGroup 2))
    (hΩ : HypOmegaGen (CoreAssembly.conjClass T)) :
    T ∈ CoreAssembly.conjClass
      (Subgroup.closure ({⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩} : Set ↥H)) := by
  have hinj : Function.Injective H.subtype := H.subtype_injective
  set SH := S.subgroupOf H with hSHdef
  have hSH2 : IsPGroup 2 SH :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  obtain ⟨g, hg⟩ := exists_conj_mem_of_isPGroup hSH2 hSi (isPGroup_of_q8 hT)
  set T₂ := conjSub g⁻¹ T with hT₂def
  have hT₂S : ∀ x ∈ T₂, x ∈ SH := by
    intro x hx
    have := hg _ (mem_conjSub_iff.mp hx)
    rwa [inv_inv, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
  obtain ⟨e₂⟩ := nonempty_conjSub_mulEquiv hT g⁻¹
  obtain ⟨i, hi, j, hj, hij, -⟩ := exists_q8Pair e₂
  have hT₂ : T₂ = Subgroup.closure ({i, j} : Set ↥H) :=
    (Subgroup.eq_of_le_of_card_ge (closure_pair_le hi hj)
      (by rw [card_closure_pair hij, card_eq_eight ⟨e₂⟩])).symm
  have hiS : (i : Equiv.Perm (Fin n)) ∈ S := Subgroup.mem_subgroupOf.mp (hT₂S i hi)
  have hjS : (j : Equiv.Perm (Fin n)) ∈ S := Subgroup.mem_subgroupOf.mp (hT₂S j hj)
  have hi4 : orderOf (i : Equiv.Perm (Fin n)) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_four_of_q8Rel hij]
  obtain ⟨r, hr, s, hs, his⟩ := hcov _ hiS hi4
  set s' : ↥H := ⟨s, hSH hs⟩ with hs'def
  set r' : ↥H := s'⁻¹ * i * s' with hr'def
  set y' : ↥H := s'⁻¹ * j * s' with hy'def
  have hr' : (r' : Equiv.Perm (Fin n)) = r := by
    simp only [hr'def, hs'def, Subgroup.coe_mul, Subgroup.coe_inv, his]
    group
  have hry : Q8Rel r' y' := by
    have := q8Rel_conj hij s'⁻¹
    rwa [inv_inv] at this
  have hyS : (y' : Equiv.Perm (Fin n)) ∈ S := by
    simp only [hy'def, Subgroup.coe_mul, Subgroup.coe_inv]
    exact S.mul_mem (S.mul_mem (S.inv_mem hs) hjS) hs
  have hry' : Q8Rel r (y' : Equiv.Perm (Fin n)) := by
    have := Q8Rel.map H.subtype hry (fun h1 => hry.2.1 (hinj (by rw [h1, map_one])))
    rwa [Subgroup.coe_subtype, hr'] at this
  obtain ⟨c, hc, hw⟩ := hwit r hr _ hyS hry'
  have hw' : PairWit (⟨x₀, hx₀⟩ : ↥H) ⟨y₀, hy₀⟩ r' y' ⟨c, hc⟩ := by
    refine PairWit.of_map (f := H.subtype) hinj ?_
    simp only [Subgroup.coe_subtype]
    rw [hr']
    exact hw
  have h0' : Q8Rel (⟨x₀, hx₀⟩ : ↥H) ⟨y₀, hy₀⟩ := by
    refine ⟨Subtype.ext ?_, fun h1 => h0.2.1 (congrArg Subtype.val h1), Subtype.ext ?_,
      Subtype.ext ?_⟩
    · simpa using h0.1
    · simpa using h0.2.2.1
    · simpa using h0.2.2.2
  have hT₃ : Subgroup.closure ({r', y'} : Set ↥H) = conjSub s'⁻¹ T₂ := by
    rw [hT₂, conjSub_closure_pair, inv_inv]
  have hcls : CoreAssembly.conjClass (Subgroup.closure ({r', y'} : Set ↥H)) =
      CoreAssembly.conjClass T := by
    rw [hT₃, conjClass_conjSub, hT₂def, conjClass_conjSub]
  rcases mem_conjClass_or_not_hypOmegaGen h0' hry hw' with ⟨h', hh'⟩ | hno
  · have hh' : conjSub h' (Subgroup.closure ({⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩} : Set ↥H)) =
        Subgroup.closure ({r', y'} : Set ↥H) := hh'
    refine ⟨g * s' * h', ?_⟩
    show conjSub (g * s' * h') _ = T
    rw [conjSub_mul, conjSub_mul, hh', hT₃, conjSub_conjSub_inv, hT₂def, conjSub_conjSub_inv]
  · exact absurd (hcls ▸ hΩ) hno

end Model

section Transport

variable {X M : Type} [Group X] [Group M] [Finite X] [Finite M]

theorem image_conjClass (θ : X ≃* M) (T : Subgroup X) :
    (fun K : Subgroup X => K.map θ.toMonoidHom) '' CoreAssembly.conjClass T =
      CoreAssembly.conjClass (T.map θ.toMonoidHom) := by
  ext K
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨θ g, (AscQuot.map_conjSub θ.toMonoidHom g T).symm⟩
  · rintro ⟨m, rfl⟩
    refine ⟨conjSub (θ.symm m) T, ⟨θ.symm m, rfl⟩, ?_⟩
    show (conjSub (θ.symm m) T).map θ.toMonoidHom = _
    rw [AscQuot.map_conjSub]
    simp

theorem hypOmegaGen_map (θ : X ≃* M) {T : Subgroup X} (hT : Nonempty (↥T ≃* QuaternionGroup 2))
    (hΩ : HypOmegaGen (CoreAssembly.conjClass T)) :
    HypOmegaGen (CoreAssembly.conjClass (T.map θ.toMonoidHom)) := by
  have h2 : ∀ K ∈ CoreAssembly.conjClass T,
      Subgroup.closure {x : X | x ∈ K ∧ IsPGroup 2 (Subgroup.zpowers x)} = K := by
    rintro _ ⟨g, rfl⟩
    have hp : IsPGroup 2 (conjSub g T) := isPGroup_of_q8 (nonempty_conjSub_mulEquiv hT g)
    apply le_antisymm
    · rw [Subgroup.closure_le]
      exact fun x hx => hx.1
    · intro x hx
      exact Subgroup.subset_closure ⟨hx, hp.to_le ((Subgroup.zpowers_le).mpr hx)⟩
  have hinv : ConjInvariant ((fun K : Subgroup X => K.map θ.toMonoidHom) ''
      CoreAssembly.conjClass T) := by
    rw [image_conjClass]
    exact TL4.conjInvariant_conjClass _
  have h := TL4.Vtx.hypOmegaGen_map_of_inj θ.toMonoidHom θ.injective hΩ h2 hinv
  rwa [image_conjClass] at h

theorem mem_conjClass_of_mulEquiv (θ : X ≃* M) (K₀ : Subgroup M)
    (hM : ∀ T : Subgroup M, Nonempty (↥T ≃* QuaternionGroup 2) →
      HypOmegaGen (CoreAssembly.conjClass T) → T ∈ CoreAssembly.conjClass K₀)
    {T₁ T₂ : Subgroup X} (h₁ : Nonempty (↥T₁ ≃* QuaternionGroup 2))
    (h₂ : Nonempty (↥T₂ ≃* QuaternionGroup 2)) (hΩ₁ : HypOmegaGen (CoreAssembly.conjClass T₁))
    (hΩ₂ : HypOmegaGen (CoreAssembly.conjClass T₂)) : T₂ ∈ CoreAssembly.conjClass T₁ := by
  have hmap : ∀ {T : Subgroup X}, Nonempty (↥T ≃* QuaternionGroup 2) →
      Nonempty (↥(T.map θ.toMonoidHom) ≃* QuaternionGroup 2) := by
    rintro T ⟨e⟩
    exact ⟨(T.equivMapOfInjective θ.toMonoidHom θ.injective).symm.trans e⟩
  obtain ⟨a, ha⟩ := hM _ (hmap h₁) (hypOmegaGen_map θ h₁ hΩ₁)
  obtain ⟨b, hb⟩ := hM _ (hmap h₂) (hypOmegaGen_map θ h₂ hΩ₂)
  have ha : conjSub a K₀ = T₁.map θ.toMonoidHom := ha
  have hb : conjSub b K₀ = T₂.map θ.toMonoidHom := hb
  refine ⟨θ.symm (b * a⁻¹), Subgroup.map_injective (f := θ.toMonoidHom) θ.injective ?_⟩
  show (conjSub (θ.symm (b * a⁻¹)) T₁).map θ.toMonoidHom = T₂.map θ.toMonoidHom
  rw [AscQuot.map_conjSub, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, ← ha, ← hb,
    ← conjSub_mul, inv_mul_cancel_right]

end Transport

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Twin
