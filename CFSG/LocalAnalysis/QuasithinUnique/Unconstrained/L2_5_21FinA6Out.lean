module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinA6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinAut

public section

namespace CFSG.QuasithinUnique.Out21

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.A6Facts

section Index

theorem eq_of_index_two_simple {B : Type*} [Group B] [Finite B] {M₀ I : Subgroup B}
    (hM : M₀.index = 2) (hcard : Nat.card ↥I = Nat.card ↥M₀) (hI : IsSimpleGroup ↥I)
    (h2 : 2 < Nat.card ↥I) : I = M₀ := by
  by_contra hne
  have hnle : ¬ I ≤ M₀ := fun hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle (hcard ▸ le_rfl))
  have hMn : M₀.Normal := Subgroup.normal_of_index_eq_two hM
  have hrel : M₀.relIndex I = 2 := by
    have hdvd := Subgroup.relIndex_dvd_index_of_normal M₀ I
    rw [hM] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd (Subgroup.relIndex_eq_one.mp h1) hnle
    · exact h1
  have hN : (M₀.subgroupOf I).index = 2 := hrel
  have hNn : (M₀.subgroupOf I).Normal := Subgroup.normal_of_index_eq_two hN
  have := hI
  have := hNn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M₀.subgroupOf I) with h1 | h1
  · rw [h1, Subgroup.index_bot] at hN
    omega
  · rw [h1, Subgroup.index_top] at hN
    omega

end Index

section Group10

theorem le_normalizer_map_subtype {X : Type*} [Group X] (E : Subgroup X) (K' : Subgroup E)
    [K'.Normal] : E ≤ Subgroup.normalizer ((K'.map E.subtype : Subgroup X) : Set X) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨h, hh⟩ * k * ⟨h, hh⟩⁻¹, Subgroup.Normal.conj_mem inferInstance k hk ⟨h, hh⟩, rfl⟩
  · rintro ⟨k, hk, hkg⟩
    refine ⟨⟨h, hh⟩⁻¹ * k * ⟨h, hh⟩, ?_, ?_⟩
    · have := Subgroup.Normal.conj_mem (inferInstance : K'.Normal) k hk ⟨h, hh⟩⁻¹
      simpa using this
    · simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hkg ⊢
      rw [hkg]
      group

theorem oddNormalFix_of_card_ten {X : Type*} [Group X] [Finite X] {α : MulAut X}
    (h : Nat.card ↥(fixSub α) = 10) : OddNormalFix α := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set E : Subgroup X := fixSub α with hE
  have : Finite ↥E := inferInstance
  have hfac : (Nat.card ↥E).factorization 5 = 1 := by
    rw [h]; norm_num [Nat.factorization]
  have hsy : Finite (Sylow 5 ↥E) := inferInstance
  obtain ⟨S5⟩ : Nonempty (Sylow 5 ↥E) := inferInstance
  have hS5 : Nat.card ↥(S5 : Subgroup ↥E) = 5 := by
    rw [Sylow.card_eq_multiplicity S5, hfac]; norm_num
  have hidx : (S5 : Subgroup ↥E).index = 2 := by
    have h1 := Subgroup.card_mul_index (S5 : Subgroup ↥E)
    rw [hS5, Nat.card_congr (Equiv.refl ↥E)] at h1
    have : Nat.card ↥E = 10 := h
    omega
  have hdvd := Sylow.card_dvd_index S5
  have hmod := card_sylow_modEq_one 5 ↥E
  rw [hidx] at hdvd
  have hn : Nat.card (Sylow 5 ↥E) = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card (Sylow 5 ↥E) := Nat.card_pos
    unfold Nat.ModEq at hmod
    omega
  have hsub : Subsingleton (Sylow 5 ↥E) := (Nat.card_eq_one_iff_unique.mp hn).1
  have hnormal : (S5 : Subgroup ↥E).Normal := Sylow.normal_of_subsingleton S5
  refine ⟨(S5 : Subgroup ↥E).map E.subtype, ?_, ?_, Subgroup.map_subtype_le _,
    le_normalizer_map_subtype E _⟩
  · intro hbot
    have h1 : Nat.card ↥((S5 : Subgroup ↥E).map E.subtype) = 1 := by
      rw [hbot]; simp
    rw [Subgroup.card_map_of_injective E.subtype_injective, hS5] at h1
    omega
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hS5]
    exact ⟨2, by norm_num⟩

end Group10

section Outer

variable {G : Type} [Group G] [Finite G] {K H S : Subgroup G}

@[expose] noncomputable def innerHom (h : OutSetting K H S) : ↥K →* ↥(autOn H K) :=
  (MulAut.conj : ↥K →* MulAut ↥K).codRestrict (autOn H K) fun x => innerAut_le_autOn h ⟨x, rfl⟩

theorem innerHom_injective
    (h : OutSetting K H S) : Function.Injective (innerHom h) :=
  fun _ _ hab => conj_injective h (congrArg Subtype.val hab)

@[expose] noncomputable def cHom (h : OutSetting K H S) {M : Type*} [Group M] (φ : ↥(autOn H K) ≃* M) :
    ↥K →* M :=
  φ.toMonoidHom.comp (innerHom h)

theorem cHom_injective
    (h : OutSetting K H S) {M : Type*} [Group M] (φ : ↥(autOn H K) ≃* M) :
    Function.Injective (cHom h φ) :=
  φ.injective.comp (innerHom_injective h)

@[expose] noncomputable def actElem (h : OutSetting K H S) {u : G} (hu : u ∈ H) : ↥(autOn H K) :=
  ⟨actOf h u hu, actOf_mem_autOn h hu⟩

theorem actElem_mul_self (h : OutSetting K H S) {u : G} (hu : u ∈ H) (hu2 : u * u = 1) :
    actElem h hu * actElem h hu = 1 :=
  Subtype.ext (actOf_mul_self h hu hu2)

theorem actElem_ne_innerHom (h : OutSetting K H S) {u : G} (hu : u ∈ H)
    (hout : u ∉ K ⊔ (H ⊓ Subgroup.centralizer (K : Set G))) (x : ↥K) :
    actElem h hu ≠ innerHom h x := by
  intro heq
  apply actOf_not_mem_innerAut h hu hout
  exact ⟨x, (congrArg Subtype.val heq).symm⟩

theorem conj_mul_comm_iff
    (h : OutSetting K H S) (α : MulAut ↥K) (x : ↥K) :
    MulAut.conj x * α = α * MulAut.conj x ↔ α x = x := by
  have key : α * MulAut.conj x = MulAut.conj (α x) * α := by
    ext v
    simp [MulAut.conj_apply, map_mul, map_inv]
  constructor
  · intro hc
    have h1 : MulAut.conj x * α = MulAut.conj (α x) * α := by rw [hc, key]
    have h2 : MulAut.conj x = MulAut.conj (α x) := mul_right_cancel h1
    exact (conj_injective h h2).symm
  · intro hx
    rw [key, hx]

theorem false_of_outer_m10
    (h : OutSetting K H S) (e6 : ↥K ≃* alternatingGroup (Fin 6))
    (φ : ↥(autOn H K) ≃* ↥A6Models.m10) {u : G} (hu : u ∈ H) (hu2 : u * u = 1)
    (hout : u ∉ K ⊔ (H ⊓ Subgroup.centralizer (K : Set G))) : False := by
  have hK : Nat.card ↥K = 360 := card_K_of_a6 e6
  have hinj := cHom_injective h φ
  set IB : Subgroup ↥A6Models.m10 := (cHom h φ).range with hIBdef
  have hIB : Nat.card ↥IB = 360 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hK]
  have hsimple : IsSimpleGroup ↥IB := by
    have := h.simple
    exact (MonoidHom.ofInjective hinj).symm.isSimpleGroup
  set M₀ : Subgroup ↥A6Models.m10 := A6Models.psl29.subgroupOf A6Models.m10 with hM₀
  have hM₀card : Nat.card ↥M₀ = 360 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe A6.psl29_le_m10).toEquiv, card_psl29]
  have hM₀idx : M₀.index = 2 := by
    have h1 := Subgroup.card_mul_index M₀
    rw [hM₀card, A6.card_m10] at h1
    omega
  have hEq : IB = M₀ :=
    eq_of_index_two_simple hM₀idx (by rw [hIB, hM₀card]) hsimple (by omega)
  set y : ↥A6Models.m10 := φ (actElem h hu) with hy
  have hyIB : y ∉ IB := by
    rintro ⟨x, hx⟩
    apply actElem_ne_innerHom h hu hout x
    apply φ.injective
    exact hx.symm
  have hy2 : y * y = 1 := by
    rw [hy, ← map_mul, actElem_mul_self h hu hu2, map_one]
  have hyM₀ : y ∈ M₀ := by
    refine Subgroup.mem_subgroupOf.mpr (A6.m10_involution_mem_psl29 y.2 ?_)
    exact congrArg Subtype.val hy2
  exact hyIB (hEq ▸ hyM₀)

theorem oddNormalFix_of_outer_pgl29
    (h : OutSetting K H S) (e6 : ↥K ≃* alternatingGroup (Fin 6))
    (φ : ↥(autOn H K) ≃* ↥A6Models.pgl29) {u : G} (hu : u ∈ H) (hu2 : u * u = 1)
    (hout : u ∉ K ⊔ (H ⊓ Subgroup.centralizer (K : Set G))) :
    OddNormalFix (actOf h u hu) := by
  have hK : Nat.card ↥K = 360 := card_K_of_a6 e6
  have hinj := cHom_injective h φ
  set c := cHom h φ with hc
  set IB : Subgroup ↥A6Models.pgl29 := c.range with hIBdef
  have hIB : Nat.card ↥IB = 360 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hK]
  have hsimple : IsSimpleGroup ↥IB := by
    have := h.simple
    exact (MonoidHom.ofInjective hinj).symm.isSimpleGroup
  set M₀ : Subgroup ↥A6Models.pgl29 := A6Models.psl29.subgroupOf A6Models.pgl29 with hM₀
  have hM₀card : Nat.card ↥M₀ = 360 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe A6.psl29_le_pgl29).toEquiv, card_psl29]
  have hM₀idx : M₀.index = 2 := by
    have h1 := Subgroup.card_mul_index M₀
    rw [hM₀card, A6.card_pgl29] at h1
    omega
  have hEq : IB = M₀ :=
    eq_of_index_two_simple hM₀idx (by rw [hIB, hM₀card]) hsimple (by omega)
  set y : ↥A6Models.pgl29 := φ (actElem h hu) with hy
  have hyIB : y ∉ IB := by
    rintro ⟨x, hx⟩
    apply actElem_ne_innerHom h hu hout x
    apply φ.injective
    exact hx.symm
  have hy2 : y * y = 1 := by
    rw [hy, ← map_mul, actElem_mul_self h hu hu2, map_one]
  have hyps : (y : P10) ∉ A6Models.psl29 := fun hmem =>
    hyIB (hEq ▸ Subgroup.mem_subgroupOf.mpr hmem)
  have hcard10 : Nat.card ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({(y : P10)} : Set P10)) = 10 :=
    A6.card_psl29_centralizer_pgl29 y.2 (congrArg Subtype.val hy2) hyps
  have hcomm : ∀ x : ↥K, c x * y = y * c x ↔ actOf h u hu x = x := by
    intro x
    have e1 : c x = φ (innerHom h x) := rfl
    rw [e1, hy, ← map_mul, ← map_mul, φ.injective.eq_iff]
    have h1 : innerHom h x * actElem h hu = actElem h hu * innerHom h x ↔
        MulAut.conj x * actOf h u hu = actOf h u hu * MulAut.conj x := by
      constructor
      · intro hh
        exact congrArg Subtype.val hh
      · intro hh
        exact Subtype.ext hh
    rw [h1]
    exact conj_mul_comm_iff h _ x
  have hfix : Nat.card ↥(fixSub (actOf h u hu)) = 10 := by
    rw [← hcard10]
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨((c x.1 : ↥A6Models.pgl29) : P10), ?_, ?_⟩) ⟨?_, ?_⟩)
    · have : c x.1 ∈ M₀ := hEq ▸ ⟨x.1, rfl⟩
      exact Subgroup.mem_subgroupOf.mp this
    · show ((c x.1 : ↥A6Models.pgl29) : P10) ∈ Subgroup.centralizer ({(y : P10)} : Set P10)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := (hcomm x.1).mpr x.2
      exact congrArg Subtype.val this
    · intro a b hab
      apply Subtype.ext
      apply hinj
      apply Subtype.ext
      exact congrArg (fun z : ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({(y : P10)} : Set P10)) =>
        (z : P10)) hab
    · rintro ⟨z, hzp, hzc⟩
      have hz' : (⟨z, A6.psl29_le_pgl29 hzp⟩ : ↥A6Models.pgl29) ∈ M₀ :=
        Subgroup.mem_subgroupOf.mpr hzp
      rw [← hEq] at hz'
      obtain ⟨x, hx⟩ := hz'
      refine ⟨⟨x, ?_⟩, Subtype.ext ?_⟩
      · rw [mem_fixSub]
        refine (hcomm x).mp ?_
        rw [hx]
        apply Subtype.ext
        have := Subgroup.mem_centralizer_singleton_iff.mp hzc
        exact this
      · show ((c x : ↥A6Models.pgl29) : P10) = z
        rw [hx]
  exact oddNormalFix_of_card_ten hfix

end Outer

end CFSG.QuasithinUnique.Out21
