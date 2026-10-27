module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HeldLift

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem mem_normalizer_sup_of {A B : Subgroup G} {x : G}
    (hA : x ∈ normalizer (A : Set G)) (hB : x ∈ normalizer (B : Set G)) :
    x ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

omit [Finite G] in
theorem eq_one_of_card_lt {P Q R : Type*} [Group P] [Finite P] [Group Q] [IsSimpleGroup Q]
    [Group R] [Finite R] (hP : Group.IsPerfect P) (ψ : P →* Q) (hψ : Function.Surjective ψ)
    (hodd : Odd (Nat.card ψ.ker)) (F : P →* R) (hlt : Nat.card R < Nat.card Q) (p : P) :
    F p = 1 := by
  have hn : ((F.ker ⊔ ψ.ker).map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((F.ker ⊔ ψ.ker).map ψ) with h | h
  · exfalso
    have hle : F.ker ≤ ψ.ker := le_sup_left.trans ((Subgroup.map_eq_bot_iff _).mp h)
    have h1 := card_eq_card_quotient_mul_card_subgroup F.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange F).toEquiv] at h1
    have h2 := card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv] at h2
    have h3 : Nat.card F.ker ≤ Nat.card ψ.ker := Subgroup.card_le_of_le hle
    have h4 : Nat.card F.range ≤ Nat.card R := Subgroup.card_le_card_group F.range
    have hpos : 0 < Nat.card F.ker := Nat.card_pos
    have h5 : Nat.card Q * Nat.card F.ker ≤ Nat.card F.range * Nat.card F.ker :=
      calc Nat.card Q * Nat.card F.ker ≤ Nat.card Q * Nat.card ψ.ker := Nat.mul_le_mul_left _ h3
        _ = Nat.card F.range * Nat.card F.ker := by rw [← h2, h1]
    have h6 := Nat.le_of_mul_le_mul_right h5 hpos
    omega
  · have htop : F.ker ⊔ ψ.ker = ⊤ := by
      have h1 := Subgroup.comap_map_eq ψ (F.ker ⊔ ψ.ker)
      rw [h, comap_top, sup_assoc, sup_idem] at h1
      exact h1.symm
    have hrange : F.range = ψ.ker.map F := by
      rw [MonoidHom.range_eq_map, ← htop, Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr le_rfl,
        bot_sup_eq]
    have hodd' : Odd (Nat.card F.range) := by
      rw [hrange]
      exact hodd.of_dvd_nat (card_map_dvd _ _)
    have hsol : Group.IsSolvable F.range := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'
    have := hP
    have hperf : Group.IsPerfect F.range := Group.IsPerfect.range F
    by_contra hne
    have : Nontrivial F.range :=
      ⟨⟨⟨F p, p, rfl⟩, 1, fun h => hne (congrArg Subtype.val h)⟩⟩
    exact Group.IsPerfect.not_isSolvable _ hsol

theorem exists_perfect_cover
    {K Λ T : Subgroup G} {t : G}
    (e : ↥K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He) (htt : t * t = 1)
    (htK : t ∈ coreActionKernel K)
    (hΛ : centralizer ({t} : Set G) ≤ normalizer (Λ : Set G)) (hTK : T ≤ K)
    (hTt : T ≤ centralizer ({t} : Set G)) (hTΛ : T ≤ Λ) (hT : ⁅T, T⁆ = T)
    (hT2 : Even (Nat.card T)) :
    ∃ P : Subgroup G, T ≤ P ∧ P ≤ centralizer ({t} : Set G) ∧ P ≤ Λ ∧ ⁅P, P⁆ = P ∧
      ∀ {R : Type} [Group R] [Finite R], Nat.card R < 4030387200 →
        ∀ (F : ↥P →* R) (p : ↥P), F p = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup heP := heP_simple
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  set C : Subgroup G := centralizer ({t} : Set G) with hC
  set H : Subgroup G := K ⊓ C with hH
  let ψ : ↥H →* ↥heP := (heModelL e).comp (Subgroup.inclusion inf_le_left)
  have hψs : Function.Surjective ψ := by
    intro p
    obtain ⟨k, hk⟩ := heModelL_surjective e p
    have h1 : (k : G)⁻¹ * (t * k * t⁻¹) ∈ (pPrimeCore 2 ↥K).map K.subtype := by
      have h2 := (mem_coreActionKernel.mp htK).2 k k.2
      rw [hti] at h2 ⊢
      simpa only [mul_assoc] using h2
    obtain ⟨o, ho, hko⟩ := exists_commute_mul_mem (odd_card_map_pPrimeCore K) htt h1
    obtain ⟨o', ho', rfl⟩ := mem_map.mp ho
    refine ⟨⟨k * o', mem_inf.mpr ⟨mul_mem k.2 o'.2,
      mem_centralizer_singleton_iff.mpr hko.symm⟩⟩, ?_⟩
    change heModelL e (k * o') = p
    rw [map_mul, (heModelL_eq_one_iff e o').mpr ho', mul_one, hk]
  have hodd : Odd (Nat.card ψ.ker) := by
    have hle : ψ.ker.map H.subtype ≤ oddIn K := by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨_, (heModelL_eq_one_iff e _).mp (MonoidHom.mem_ker.mp hy), rfl⟩
    rw [← Subgroup.card_map_of_injective H.subtype_injective]
    exact (odd_card_map_pPrimeCore K).of_dvd_nat (Subgroup.card_dvd_of_le hle)
  have hTH : T ≤ H := le_inf hTK hTt
  set TH : Subgroup ↥H := T.subgroupOf H with hTHdef
  have hTHmap : TH.map H.subtype = T := by rw [hTHdef, subgroupOf_map_subtype, inf_eq_left.mpr hTH]
  have hTHperf : ⁅TH, TH⁆ = TH := by
    apply map_injective H.subtype_injective
    rw [map_commutator, hTHmap, hT]
  set Pc : Subgroup ↥H := normalClosure (TH : Set ↥H) with hPc
  have hTPc : TH ≤ Pc := le_normalClosure
  have hPcperf : ⁅Pc, Pc⁆ = Pc := by
    refine le_antisymm (commutator_le_self _) (normalClosure_le_normal ?_)
    rw [← hTHperf]
    exact commutator_mono hTPc hTPc
  set P : Subgroup G := Pc.map H.subtype with hP
  have hPH : P ≤ H := map_subtype_le _
  have hPperf : ⁅P, P⁆ = P := by rw [hP, ← map_commutator, hPcperf]
  have hΛH : (Λ.subgroupOf H).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    have hg : (g : G) ∈ normalizer (Λ : Set G) := hΛ (mem_inf.mp g.2).2
    exact (mem_normalizer_iff.mp hg x).mp hx
  have hPcΛ : Pc ≤ Λ.subgroupOf H := normalClosure_le_normal fun x hx => hTΛ hx
  refine ⟨P, ?_, hPH.trans inf_le_right, ?_, hPperf, ?_⟩
  · rw [← hTHmap]
    exact map_mono hTPc
  · rintro _ ⟨x, hx, rfl⟩
    exact hPcΛ hx
  · intro R _ _ hR F p
    set ι : ↥P →* ↥H := Pc.subtype.comp
      (Pc.equivMapOfInjective H.subtype H.subtype_injective).symm.toMonoidHom with hι
    have hιi : Function.Injective ι := Pc.subtype_injective.comp (MulEquiv.injective _)
    have hιr : ι.range = Pc := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact ((Pc.equivMapOfInjective H.subtype H.subtype_injective).symm z).2
      · intro hy
        refine ⟨Pc.equivMapOfInjective H.subtype H.subtype_injective ⟨y, hy⟩, ?_⟩
        simp only [hι, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.symm_apply_apply, Subgroup.coe_subtype]
    set ψP : ↥P →* ↥heP := ψ.comp ι with hψP
    have hψPs : Function.Surjective ψP := by
      have hn : (Pc.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψs
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Pc.map ψ) with h | h
      · exfalso
        obtain ⟨j, hjT, hj2⟩ : ∃ j ∈ T, orderOf j = 2 := by
          obtain ⟨j, hj⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 2 (even_iff_two_dvd.mp hT2)
          exact ⟨j, j.2, by rw [← hj, Subgroup.orderOf_coe]⟩
        have hjPc : (⟨j, hTH hjT⟩ : ↥H) ∈ Pc := hTPc hjT
        have hψj : ψ ⟨j, hTH hjT⟩ = 1 := by
          have : ψ ⟨j, hTH hjT⟩ ∈ Pc.map ψ := mem_map_of_mem _ hjPc
          rwa [h, mem_bot] at this
        have hjO : (⟨j, hTK hjT⟩ : ↥K) ∈ pPrimeCore 2 ↥K := (heModelL_eq_one_iff e _).mp hψj
        have h1 : orderOf (⟨⟨j, hTK hjT⟩, hjO⟩ : ↥(pPrimeCore 2 ↥K)) ∣
            Nat.card ↥(pPrimeCore 2 ↥K) := orderOf_dvd_natCard _
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hj2] at h1
        exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
          (even_iff_two_dvd.mpr h1)
      · intro y
        have hy : y ∈ Pc.map ψ := h ▸ mem_top y
        obtain ⟨z, hz, rfl⟩ := mem_map.mp hy
        obtain ⟨w, hw⟩ : z ∈ ι.range := hιr ▸ hz
        exact ⟨w, by rw [hψP, MonoidHom.comp_apply, hw]⟩
    have hψPodd : Odd (Nat.card ψP.ker) := by
      have hle : ψP.ker.map ι ≤ ψ.ker := by
        rintro _ ⟨y, hy, rfl⟩
        exact hy
      rw [← Subgroup.card_map_of_injective hιi]
      exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le hle)
    have hPfin : Finite ↥P := inferInstance
    exact eq_one_of_card_lt (isPerfect_iff.mpr hPperf) ψP hψPs hψPodd F
      (by rw [card_heP]; exact hR) p

omit [Finite G] in
theorem le_coreActionKernel_of_small {N P : Subgroup G}
    (hN : ⁅N, N⁆ = N) (hNt : IsL34Type (↥N ⧸ Open.fusionZStar ↥N))
    (hPN : P ≤ normalizer (N : Set G))
    (hsmall : ∀ {R : Type} [Group R] [Finite R], Nat.card R < 4030387200 →
      ∀ (F : ↥P →* R) (p : ↥P), F p = 1) :
    P ≤ coreActionKernel N := by
  set Nb := ↥N ⧸ pPrimeCore 2 ↥N with hNb
  have hNperf : Group.IsPerfect ↥N := isPerfect_iff.mpr hN
  have hNbperf : Group.IsPerfect Nb :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (pPrimeCore 2 ↥N))
      (QuotientGroup.mk'_surjective _)
  obtain ⟨eS⟩ := CatFactsSmall.nonempty_equiv_psl34_of_lieModel hNt
  obtain ⟨eR, -, -⟩ := PSL3Four.full_automorphism_action
  have hcardA : Nat.card (MulAut (Nb ⧸ center Nb)) = 241920 := by
    rw [Nat.card_congr (MulAut.congr ((Sol78.coreQuotientCenterEquiv ↥N).trans eS)).toEquiv,
      ← Nat.card_congr eR.toEquiv, PSL3Four.card_R]
  have : Finite (MulAut (Nb ⧸ center Nb)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardA]; norm_num)
  let F : ↥P →* MulAut (Nb ⧸ center Nb) :=
    GH74.KGroups.inducedHom.comp ((heldQuotConj N).comp (Subgroup.inclusion hPN))
  intro p hp
  have hpi : p⁻¹ ∈ P := inv_mem hp
  have hF : F ⟨p⁻¹, hpi⟩ = 1 := hsmall (by rw [hcardA]; norm_num) F _
  have h1 : heldQuotConj N ⟨p⁻¹, hPN hpi⟩ = 1 := by
    apply GH74.KGroups.inducedHom_injective hNbperf
    rw [map_one]
    exact hF
  refine ⟨hPN hp, fun j hj => ?_⟩
  have h2 : heldQuotConj N ⟨p⁻¹, hPN hpi⟩ (QuotientGroup.mk ⟨j, hj⟩) =
      QuotientGroup.mk ⟨j, hj⟩ := by
    rw [h1]
    rfl
  have h3 := QuotientGroup.eq.mp h2.symm
  refine ⟨_, h3, ?_⟩
  change (j : G)⁻¹ * (p⁻¹ * j * p⁻¹⁻¹) = j⁻¹ * p⁻¹ * j * p
  group

theorem false_of_le_coreActionKernel {N N' T : Subgroup G}
    (hN'N : N' ≤ normalizer (N : Set G)) (hNN' : N ≤ normalizer (N' : Set G))
    (hT : ⁅T, T⁆ = T) (hT2 : Even (Nat.card T)) (hTN : T ≤ N ⊔ N')
    (hTk : T ≤ coreActionKernel N) (hTk' : T ≤ coreActionKernel N') : False := by
  set Q : Subgroup G := oddIn N ⊔ oddIn N' with hQ
  have hON : ∀ {A B : Subgroup G}, B ≤ normalizer (A : Set G) →
      B ≤ normalizer (oddIn A : Set G) := fun {A B} hBA =>
    hBA.trans (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic A (pPrimeCore 2 ↥A))
  have hOO : oddIn N' ≤ normalizer (oddIn N : Set G) :=
    hON ((map_subtype_le (pPrimeCore 2 ↥N')).trans hN'N)
  have hQodd : Odd (Nat.card Q) :=
    odd_card_sup_held hOO (odd_card_map_pPrimeCore N) (odd_card_map_pPrimeCore N')
  have hNQ : ∀ {A : Subgroup G}, A ≤ normalizer (N : Set G) → A ≤ normalizer (N' : Set G) →
      A ≤ normalizer (Q : Set G) := fun {A} h1 h2 x hx =>
    mem_normalizer_sup_of (hON h1 hx) (hON h2 hx)
  have hsupQ : N ⊔ N' ≤ normalizer (Q : Set G) :=
    sup_le (hNQ le_normalizer hNN') (hNQ hN'N le_normalizer)
  have hsup : N ⊔ N' = closure ((N : Set G) ∪ N') := by
    rw [Subgroup.closure_union, closure_eq, closure_eq]
  have hcomm : ∀ {A : Subgroup G} {x y : G}, x ∈ coreActionKernel A → y ∈ A →
      ⁅x, y⁆ ∈ oddIn A := by
    intro A x y hx hy
    have h1 := (mem_coreActionKernel.mp (inv_mem hx)).2 y⁻¹ (inv_mem hy)
    have h2 : ⁅x, y⁆ = (y⁻¹⁻¹ * x⁻¹⁻¹ * y⁻¹ * x⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact inv_mem h1
  have key : ∀ y ∈ N ⊔ N', y ∈ normalizer (Q : Set G) ∧ ∀ x ∈ T, ⁅x, y⁆ ∈ Q := by
    intro y hy
    rw [hsup] at hy
    induction hy using closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact ⟨hsupQ (mem_sup_left hy), fun x hx => mem_sup_left (hcomm (hTk hx) hy)⟩
      · exact ⟨hsupQ (mem_sup_right hy), fun x hx => mem_sup_right (hcomm (hTk' hx) hy)⟩
    | one =>
      exact ⟨one_mem _, fun x _ => by rw [commutatorElement_one_right]; exact one_mem _⟩
    | mul y z _ _ hy hz =>
      refine ⟨mul_mem hy.1 hz.1, fun x hx => ?_⟩
      have heq : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [heq]
      exact mul_mem (hy.2 x hx) ((mem_normalizer_iff.mp hy.1 _).mp (hz.2 x hx))
    | inv y _ hy =>
      refine ⟨inv_mem hy.1, fun x hx => ?_⟩
      have heq : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [heq]
      exact (mem_normalizer_iff.mp (inv_mem hy.1) _).mp (inv_mem (hy.2 x hx))
  have hTQ : T ≤ Q := by
    rw [← hT]
    refine (commutator_mono le_rfl hTN).trans ?_
    rw [commutator_le]
    intro x hx y hy
    exact (key y hy).2 x hx
  exact (Nat.not_even_iff_odd.mpr (hQodd.of_dvd_nat (Subgroup.card_dvd_of_le hTQ))) hT2

end CFSG.ComponentClassification.GrSLit.GrS4
