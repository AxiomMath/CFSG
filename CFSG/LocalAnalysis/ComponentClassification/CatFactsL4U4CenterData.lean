module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OuterData

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OutInv

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

theorem commutator_sup_center_le {G : Type*} [Group G] (X : Subgroup G) :
    ⁅X ⊔ center G, X ⊔ center G⁆ ≤ X := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  obtain ⟨b, hb, d, hd, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  have hc' := Subgroup.mem_center_iff.mp hc
  have hd' := Subgroup.mem_center_iff.mp hd
  have e : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹
        = a * (c * b) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by group
      _ = a * (b * c) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by rw [hc' b]
      _ = a * b * (c * (d * c⁻¹)) * a⁻¹ * d⁻¹ * b⁻¹ := by group
      _ = a * b * (c * (c⁻¹ * d)) * a⁻¹ * d⁻¹ * b⁻¹ := by
          rw [(Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hc) d).symm]
      _ = a * b * (d * a⁻¹) * d⁻¹ * b⁻¹ := by group
      _ = a * b * (a⁻¹ * d) * d⁻¹ * b⁻¹ := by rw [hd' a⁻¹]
      _ = a * b * a⁻¹ * b⁻¹ := by group
  rw [e, commutatorElement_def]
  exact X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb)

theorem nonempty_quotient_center_equiv' {X Q Y : Type*} [Group X] [Group Q] [Group Y]
    [Finite Q] (hQ : IsQuasisimple Q) (θ : X →* Q) (hθ : Function.Surjective θ)
    (O : Subgroup X) [O.Normal] (hO : Odd (Nat.card (O.map θ))) (e : X ⧸ O ≃* Y)
    (hY : IsQuasisimple Y) : Nonempty (Q ⧸ center Q ≃* Y ⧸ center Y) := by
  set M : Subgroup X := (center Q).comap θ with hM
  have hOM : O ≤ M := by
    have hn : (O.map θ).Normal := Subgroup.Normal.map inferInstance θ hθ
    rcases LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hQ (O.map θ) with hc | ht
    · intro x hx
      exact hc (mem_map_of_mem θ hx)
    · exfalso
      have hodd : Odd (Nat.card Q) := by
        rw [ht, Subgroup.card_top] at hO
        exact hO
      exact false_of_isSolvable hQ (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
  set ε : X →* Y := e.toMonoidHom.comp (QuotientGroup.mk' O) with hε
  have hεs : Function.Surjective ε := e.surjective.comp (QuotientGroup.mk'_surjective O)
  set M' : Subgroup X := (center Y).comap ε with hM'
  have hMM' : M ≤ M' := by
    have hMn : M.Normal := Subgroup.Normal.comap inferInstance θ
    have hMbn : (M.map ε).Normal := hMn.map _ hεs
    rcases LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hY (M.map ε) with hc | ht
    · intro x hx
      exact hc (mem_map_of_mem ε hx)
    · exfalso
      have hall : ∀ x : X, x ∈ M := by
        intro x
        have h1 : ε x ∈ M.map ε := by
          rw [ht]
          exact mem_top _
        obtain ⟨m, hm, hme⟩ := h1
        have h2 : QuotientGroup.mk' O m = QuotientGroup.mk' O x := e.injective hme
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h2
        have := mul_mem hm (hOM h2)
        rwa [mul_inv_cancel_left] at this
      obtain ⟨-, -, a, b, hab⟩ := hQ
      apply hab
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      obtain ⟨x', rfl⟩ := hθ x
      obtain ⟨y', rfl⟩ := hθ y
      have hx : θ x' ∈ center Q := hall x'
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hx (θ y')]
  have hM'M : M' ≤ M := by
    intro x hx
    have hx' : ε x ∈ center Y := hx
    have hcen : (QuotientGroup.mk (θ x) : Q ⧸ center Q) ∈ center (Q ⧸ center Q) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective g
      obtain ⟨y, rfl⟩ := hθ q
      have h1 : ε (x⁻¹ * y⁻¹ * x * y) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        calc (ε x)⁻¹ * (ε y)⁻¹ * ε x * ε y = (ε x)⁻¹ * ((ε y)⁻¹ * ε x) * ε y := by group
          _ = (ε x)⁻¹ * (ε x * (ε y)⁻¹) * ε y := by rw [mem_center_iff.mp hx' (ε y)⁻¹]
          _ = 1 := by group
      have h2 : x⁻¹ * y⁻¹ * x * y ∈ O := by
        have := e.injective (h1.trans (map_one e).symm)
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      have h3 : θ (x⁻¹ * y⁻¹ * x * y) ∈ center Q := hOM h2
      have h4 : (QuotientGroup.mk (θ (x⁻¹ * y⁻¹ * x * y)) : Q ⧸ center Q) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr h3
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv] at h4
      calc (QuotientGroup.mk (θ y) : Q ⧸ center Q) * QuotientGroup.mk (θ x) =
          QuotientGroup.mk (θ y) * QuotientGroup.mk (θ x) *
            ((QuotientGroup.mk (θ x))⁻¹ * (QuotientGroup.mk (θ y))⁻¹ *
              QuotientGroup.mk (θ x) * QuotientGroup.mk (θ y)) := by rw [h4, mul_one]
        _ = QuotientGroup.mk (θ x) * QuotientGroup.mk (θ y) := by group
    rw [LieType.CurtisTits.center_quotient_center_eq_bot_of_isQuasisimple hQ, mem_bot,
      QuotientGroup.eq_one_iff] at hcen
    exact hcen
  have hMeq : M = M' := le_antisymm hMM' hM'M
  set ψ : X →* Q ⧸ center Q := (QuotientGroup.mk' (center Q)).comp θ with hψ
  have hψs : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hθ
  have hker : ψ.ker = M := by
    rw [hM, hψ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  set ψ' : X →* Y ⧸ center Y := (QuotientGroup.mk' (center Y)).comp ε with hψ'
  have hψ's : Function.Surjective ψ' := (QuotientGroup.mk'_surjective _).comp hεs
  have hker' : ψ'.ker = M' := by
    rw [hM', hψ', ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (hker.trans (hMeq.trans hker'.symm))).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ' hψ's))⟩

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

theorem orderOf_phi_abar' : orderOf (phi hKa (abar h)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [sq, ← map_mul, abar_mul_self, map_one]
  · intro h1
    apply oddBarConj_a_ne_one h hKa
    have h2 : rhoL hKa ⟨h.a, h.a_mem_normalizer⟩ = 1 := by
      have := congrArg (fun g : ↥(GAut hKa) => (g : MulAut (LK h))) h1
      rw [← rhoBar_mk]
      exact this
    exact oddBarConj_eq_one_of_mem_kernel ((rhoL_eq_one_iff hKa _).mp h2)

theorem phi_abar_mem_NL (hin : h.a ∈ h.K ⊔ coreActionKernel h.K) : phi hKa (abar h) ∈ NL hKa := by
  obtain ⟨l, hl⟩ := exists_oddBarConj_a_eq_conj h hKa hin
  rw [mem_subgroupOf]
  refine ⟨(l : LK h), ?_⟩
  show _ = rhoBar hKa (abar h)
  rw [rhoBar_mk, rhoL, MonoidHom.comp_apply]
  rw [show actW h hKa ⟨h.a, h.a_mem_normalizer⟩ = oddBarConj h.K ⟨h.a, a_mem_normalizer_K h hKa⟩
    from rfl, hl, inducedHom_conj]

theorem nonempty_Jhat_equiv' :
    Nonempty (↥(Jhat hKa) ⧸ center ↥(Jhat hKa) ≃* OddBar h.J ⧸ center (OddBar h.J)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set JB := GSLit.fixedLayer h.J h.B with hJB
  have hJBW : JB ≤ h.W := (fixedLayer_le_K h hKa).trans (K_le_W h)
  set JB' : Subgroup h.W := JB.subgroupOf h.W with hJB'
  set χ : h.W →* ↥(GAut hKa) := (phi hKa).comp (wbarMk h.B) with hχ
  have heq : Jhat hKa = JB'.map χ := Subgroup.map_map _ _ _
  have hBJ : h.B ≤ coreActionKernel h.J := h.B_le.trans inf_le_right
  have hB2 : IsPGroup 2 h.B := h.isPGroup_S.to_le (h.B_le.trans inf_le_left)
  have hsup := (GSLit.fixedLayer_sup_pPrimeCore (B5a.isQuasisimple_J h) hBJ hB2).1
  have hJBJ : JB ≤ h.J := (GSLit.fixedLayer_le_inf h.J h.B).trans inf_le_left
  obtain ⟨-, e1, -⟩ := restriction_quotient_mulEquiv hJBJ hsup
  let e2 : JB ≃* JB' := (subgroupOfEquivOfLe hJBW).symm
  let e3 : JB ⧸ pPrimeCore 2 JB ≃* JB' ⧸ pPrimeCore 2 JB' :=
    QuotientGroup.congr (pPrimeCore 2 JB) (pPrimeCore 2 JB') e2 (pPrimeCore_map_iso 2 e2)
  have hQ : IsQuasisimple ↥(JB'.map χ) := by
    rw [← heq]
    exact (Jhat_standard hKa).1
  have hO : Odd (Nat.card ((pPrimeCore 2 JB').map (χ.subgroupMap JB'))) := by
    have h1 := Subgroup.card_map_dvd (H := pPrimeCore 2 JB') (χ.subgroupMap JB')
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card) h1
  obtain ⟨eQ⟩ := nonempty_quotient_center_equiv' hQ (χ.subgroupMap JB')
    (χ.subgroupMap_surjective JB') (pPrimeCore 2 JB') hO (e3.symm.trans e1) h.isQuasisimple_J
  rw [heq]
  exact ⟨eQ⟩

abbrev X9 (h : Hyp52 H) : Subgroup H :=
  layerIn h.W ⊓ normalizer ((GSLit.fixedLayer h.J h.B ⊔ oddCoreIn h.W : Subgroup H) : Set H)

include hKa in
theorem X9_le_K : X9 h ≤ h.K := inf_le_left.trans (h.V_eq_K hKa).le

noncomputable abbrev M9 : Subgroup ↥(GAut hKa) :=
  NL hKa ⊓ normalizer ((Jhat hKa : Subgroup ↥(GAut hKa)) : Set ↥(GAut hKa))

noncomputable abbrev psi9 : ↥(X9 h) →* ↥(GAut hKa) :=
  (phi hKa).comp ((wbarMk h.B).comp (inclusion ((X9_le_K hKa).trans (K_le_W h))))

include hKa in
theorem wbarImage_sup_oddCoreIn :
    wbarImage h.B (GSLit.fixedLayer h.J h.B ⊔ oddCoreIn h.W) =
      wbarImage h.B (GSLit.fixedLayer h.J h.B) := by
  have hJBW : GSLit.fixedLayer h.J h.B ≤ h.W := (fixedLayer_le_K h hKa).trans (K_le_W h)
  have hOW : oddCoreIn h.W ≤ h.W := by
    rintro _ ⟨o, -, rfl⟩
    exact o.2
  have hOb : ((oddCoreIn h.W).subgroupOf h.W).map (wbarMk h.B) = ⊥ := by
    have e1 : (oddCoreIn h.W).subgroupOf h.W = pPrimeCore 2 h.W :=
      comap_map_eq_self_of_injective h.W.subtype_injective _
    rw [e1, Subgroup.map_eq_bot_iff, wbarMk, QuotientGroup.ker_mk']
    exact Hyp52.pPrimeCore_le_oddTwoCore _
  rw [wbarImage, wbarImage, subgroupOf_sup hJBW hOW, Subgroup.map_sup, hOb, sup_bot_eq]

theorem psi9_mem (x : ↥(X9 h)) : psi9 hKa x ∈ M9 hKa := by
  have hxK : (x : H) ∈ h.K := X9_le_K hKa x.2
  refine mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_subgroupOf]
    refine ⟨(((⟨x, hxK⟩ : ↥h.K) : OddBar h.K) : LK h), ?_⟩
    show _ = rhoBar hKa (wbarMk h.B ⟨(⟨x, hxK⟩ : ↥h.K), K_le_W h hxK⟩)
    rw [rhoBar_mk, rhoL_of_mem_K]
  · apply B5a.map_mem_normalizer
    rw [← wbarImage_sup_oddCoreIn hKa]
    apply B5a.map_mem_normalizer
    rw [← subgroupOf_normalizer_eq ?_, mem_subgroupOf]
    · exact (mem_inf.mp x.2).2
    · refine sup_le ((fixedLayer_le_K h hKa).trans (K_le_W h)) ?_
      rintro _ ⟨o, -, rfl⟩
      exact o.2

include hKa in
theorem mem_normalizer_of_wbar {k : H} (hk : k ∈ h.K)
    (hkn : wbarMk h.B ⟨k, K_le_W h hk⟩ ∈ normalizer ((wbarImage h.B
      (GSLit.fixedLayer h.J h.B) : Subgroup (Wbar h.B)) : Set (Wbar h.B))) :
    k ∈ normalizer ((GSLit.fixedLayer h.J h.B ⊔ oddCoreIn h.W : Subgroup H) : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set JB := GSLit.fixedLayer h.J h.B with hJB
  have hJBK : JB ≤ h.K := fixedLayer_le_K h hKa
  set πK : ↥h.K →* OddBar h.K := QuotientGroup.mk' (pPrimeCore 2 h.K) with hπK
  set JK : Subgroup (OddBar h.K) := (JB.subgroupOf h.K).map πK with hJK
  have hJKp : ⁅JK, JK⁆ = JK := by
    have h1 : ⁅JB.subgroupOf h.K, JB.subgroupOf h.K⁆ = JB.subgroupOf h.K := by
      apply map_injective h.K.subtype_injective
      rw [map_commutator, map_subgroupOf_eq_of_le hJBK, fixedLayer_commutator_eq]
    rw [hJK, ← map_commutator, h1]
  set kK : ↥h.K := ⟨k, hk⟩ with hkK
  have hstep1 : ∀ j : ↥h.K, (j : H) ∈ JB →
      πK (kK * j * kK⁻¹) ∈ JK ⊔ center (OddBar h.K) := by
    intro j hj
    have hjW : (j : H) ∈ h.W := K_le_W h j.2
    have h1 : wbarMk h.B ⟨k, K_le_W h hk⟩ * wbarMk h.B ⟨j, hjW⟩ *
        (wbarMk h.B ⟨k, K_le_W h hk⟩)⁻¹ ∈ wbarImage h.B JB :=
      (mem_normalizer_iff.mp hkn _).mp ⟨⟨j, hjW⟩, hj, rfl⟩
    obtain ⟨j', hj', hj'e⟩ := h1
    rw [← map_inv, ← map_mul, ← map_mul] at hj'e
    have hc := QuotientGroup.eq.mp hj'e
    rw [SetLike.mem_coe, mem_subgroupOf] at hj'
    have hj'K : (j' : H) ∈ h.K := hJBK hj'
    set c : ↥h.K := (⟨j', hj'K⟩ : ↥h.K)⁻¹ * (kK * j * kK⁻¹) with hcdef
    have hcO : (⟨c, K_le_W h c.2⟩ : h.W) ∈ oddTwoCore h.W := by
      convert hc using 1
    have hcZ := mem_center_of_mem_oddTwoCore hcO
    have e : kK * j * kK⁻¹ = ⟨j', hj'K⟩ * c := by rw [hcdef, mul_inv_cancel_left]
    rw [e, map_mul]
    refine mul_mem (mem_sup_left ⟨⟨j', hj'K⟩, ?_, rfl⟩) (mem_sup_right hcZ)
    rw [SetLike.mem_coe, mem_subgroupOf]
    exact hj'
  have hconj : ∀ j : ↥h.K, MulAut.conj (πK kK) (πK j) = πK (kK * j * kK⁻¹) := by
    intro j
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hle : JK.map (MulAut.conj (πK kK)).toMonoidHom ≤ JK := by
    have h1 : JK.map (MulAut.conj (πK kK)).toMonoidHom ≤ JK ⊔ center (OddBar h.K) := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨j, hj, rfl⟩ := hy
      rw [SetLike.mem_coe, mem_subgroupOf] at hj
      rw [MulEquiv.coe_toMonoidHom, hconj]
      exact hstep1 j hj
    have h2 : ⁅JK.map (MulAut.conj (πK kK)).toMonoidHom,
        JK.map (MulAut.conj (πK kK)).toMonoidHom⁆ = JK.map (MulAut.conj (πK kK)).toMonoidHom := by
      rw [← map_commutator, hJKp]
    rw [← h2]
    exact (commutator_mono h1 h1).trans (commutator_sup_center_le JK)
  have hstep2 : ∀ j : ↥h.K, (j : H) ∈ JB → πK (kK * j * kK⁻¹) ∈ JK := by
    intro j hj
    have h1 := hle ⟨πK j, ⟨j, by rw [SetLike.mem_coe, mem_subgroupOf]; exact hj, rfl⟩, rfl⟩
    rwa [MulEquiv.coe_toMonoidHom, hconj] at h1
  have hstep3 : ∀ j ∈ JB, k * j * k⁻¹ ∈ JB ⊔ oddCoreIn h.W := by
    intro j hj
    have hjK := hJBK hj
    obtain ⟨j'', hj'', hj''e⟩ := hstep2 ⟨j, hjK⟩ hj
    rw [SetLike.mem_coe, mem_subgroupOf] at hj''
    have hO := QuotientGroup.eq.mp hj''e
    have hOW := mem_pPrimeCore_W_of_mem_pPrimeCore hKa hO
    have e : k * j * k⁻¹ = (j'' : H) * ((j''⁻¹ * (kK * ⟨j, hjK⟩ * kK⁻¹) : ↥h.K) : H) := by
      simp [hkK]
    rw [e]
    exact mul_mem (mem_sup_left hj'') (mem_sup_right ⟨_, hOW, rfl⟩)
  apply mem_normalizer_of_conj_mem
  have hle' : (JB ⊔ oddCoreIn h.W).map (MulAut.conj k).toMonoidHom ≤ JB ⊔ oddCoreIn h.W := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨j, hj, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hstep3 j hj
    · rintro _ ⟨o, ho, rfl⟩
      obtain ⟨o', ho', rfl⟩ := ho
      have hkW := K_le_W h hk
      refine mem_sup_right ⟨⟨k, hkW⟩ * o' * (⟨k, hkW⟩ : h.W)⁻¹,
        (pPrimeCore_normal (p := 2) (G := h.W)).conj_mem _ ho' _, ?_⟩
      simp [MulAut.conj_apply]
  intro y hy
  exact hle' ⟨y, hy, rfl⟩

theorem psi9_surj (m : ↥(GAut hKa)) (hm : m ∈ M9 hKa) : ∃ x, psi9 hKa x = m := by
  obtain ⟨hmN, hmJ⟩ := mem_inf.mp hm
  rw [mem_subgroupOf] at hmN
  obtain ⟨l, hl⟩ := hmN
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective l
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  have hkW := K_le_W h k.2
  set kb : Wbar h.B := wbarMk h.B ⟨k, hkW⟩ with hkb
  have hm' : phi hKa kb = m := by
    apply Subtype.ext
    show rhoBar hKa (wbarMk h.B ⟨k, K_le_W h k.2⟩) = (m : MulAut (LK h))
    rw [rhoBar_mk, rhoL_of_mem_K, hl]
  have hkn : kb ∈ normalizer ((wbarImage h.B (GSLit.fixedLayer h.J h.B) : Subgroup (Wbar h.B)) :
      Set (Wbar h.B)) := by
    apply mem_normalizer_of_conj_mem
    intro u hu
    have hu' : phi hKa (kb * u * kb⁻¹) ∈ Jhat hKa := by
      rw [map_mul, map_mul, map_inv, hm']
      exact (mem_normalizer_iff.mp hmJ (phi hKa u)).mp ⟨u, hu, rfl⟩
    obtain ⟨u', hu'J, hu'e⟩ := hu'
    have hkhat : kb ∈ Khat h := ⟨⟨k, hkW⟩, k.2, rfl⟩
    have h1 : kb * u * kb⁻¹ ∈ Khat h := (Khat_normal hKa).conj_mem u (JBbar_le_Khat hKa hu) kb
    have h2 := eq_of_rhoBar_eq hKa (JBbar_le_Khat hKa hu'J) h1 (congrArg Subtype.val hu'e)
    rw [← h2]
    exact hu'J
  have hkX : (k : H) ∈ X9 h := by
    refine mem_inf.mpr ⟨?_, mem_normalizer_of_wbar hKa k.2 hkn⟩
    rw [show layerIn h.W = h.K from h.V_eq_K hKa]
    exact k.2
  exact ⟨⟨k, hkX⟩, hm'⟩

theorem exists_sylow_image : ∃ R : Subgroup ↥(GAut hKa), R ≤ M9 hKa ∧
    (∃ R' : Sylow 2 ↥(M9 hKa), (R' : Subgroup _) = R.subgroupOf (M9 hKa)) ∧
    ∀ r ∈ R, ∃ q ∈ h.Q, ∃ hq : q ∈ h.W, r = phi hKa (wbarMk h.B ⟨q, hq⟩) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hRQ, hRX, R', hR'⟩ := h.sylow_layer
  set ψM : ↥(X9 h) →* ↥(M9 hKa) := (psi9 hKa).codRestrict (M9 hKa) (psi9_mem hKa) with hψM
  have hψMs : Function.Surjective ψM := by
    rintro ⟨m, hm⟩
    obtain ⟨x, hx⟩ := psi9_surj hKa m hm
    exact ⟨x, Subtype.ext hx⟩
  set R'' : Sylow 2 ↥(M9 hKa) := R'.mapSurjective hψMs with hR''
  refine ⟨(R'' : Subgroup ↥(M9 hKa)).map (M9 hKa).subtype, map_subtype_le _, ⟨R'', ?_⟩, ?_⟩
  · exact (comap_map_eq_self_of_injective (M9 hKa).subtype_injective _).symm
  · rintro _ ⟨y, hy, rfl⟩
    rw [hR'', Sylow.coe_mapSurjective] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hR', SetLike.mem_coe, mem_subgroupOf] at hx
    exact ⟨x, (hRQ hx), (X9_le_K hKa).trans (K_le_W h) x.2, rfl⟩

end OutInv

end CFSG.ComponentClassification.CatFactsL4U4
