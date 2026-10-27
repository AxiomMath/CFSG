module

public import CFSG.LieType.Chevalley.ChevalleyLargeRootCentralizerFaithful
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiTwoAAutomorphisms

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Ree

theorem F4_conj_entrywise_eq_id
    {f : ℕ} (hf : 1 ≤ f) {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2 ^ f) (y : adjointGroup ReeTag.F4.tag k) (σ : k ≃+* k)
    (h : ∀ x : adjointGroup ReeTag.F4.tag k, (y : ModGL ReeTag.F4.tag k) *
      Units.map (entrywiseHom σ.toRingHom) (x : ModGL ReeTag.F4.tag k) *
        (y : ModGL ReeTag.F4.tag k)⁻¹ = x) :
    y = 1 ∧ σ = RingEquiv.refl k := by
  have : CharP k 2 :=
    finite_field_prime_power_characteristic Nat.prime_two hf hk
  have : CharP k ReeTag.F4.prime := this
  obtain ⟨s, hs, hσ, -⟩ := exists_frobenius_pow_eq hf hk σ
  have h1 : exactNormalAut ReeTag.F4.tag k 1 σ 0 = ReeTag.F4.finiteFrobeniusAut k ^ s :=
    exactNormalAut_one_eq_finiteFrobeniusAut_pow ReeTag.F4 hσ
  have h2 : MulAut.conj y * ReeTag.F4.finiteExceptionalAut k ^ ((⟨2 * s, by omega⟩ :
      Fin (2 * f)) : ℕ) = 1 := by
    change MulAut.conj y * ReeTag.F4.finiteExceptionalAut k ^ (2 * s) = 1
    rw [finiteExceptionalAut_pow_two_mul ReeTag.F4, ← h1]
    have hQ : exactQ ReeTag.F4.tag k 0 = (1 : ModGL ReeTag.F4.tag k) := rfl
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply, Subgroup.coe_mul,
      Subgroup.coe_mul, coe_exactNormalAut, Subgroup.coe_inv, hQ, rootDiagUnit_one]
    simp only [one_mul, mul_one, inv_one]
    exact h x
  obtain ⟨-, huniq, -⟩ := even_F4_exact_automorphism_normal_form hf k hk
  obtain ⟨gk, -, hgk⟩ := huniq 1
  have e1 := hgk (y, ⟨2 * s, by omega⟩) h2.symm
  have e2 := hgk (1, ⟨0, by omega⟩) (by simp)
  have e := e1.trans e2.symm
  have hy : y = 1 := congrArg Prod.fst e
  have hs0 : 2 * s = 0 := congrArg (fun p : adjointGroup ReeTag.F4.tag k × Fin (2 * f) =>
    (p.2 : ℕ)) e
  refine ⟨hy, RingEquiv.ext fun c => ?_⟩
  rw [hσ, show s = 0 by omega, pow_zero, pow_one]
  rfl

theorem coe_diagramConjAut_pow
    {K : Type} [Field K] (n : ℕ) (h : adjointGroup TwistTag.E6.tag K) :
    ((diagramConjAut TwistTag.E6 K ^ n) h : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K ^ n * h * (diagramMap TwistTag.E6 K ^ n)⁻¹ := by
  induction n generalizing h with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, coe_diagramConjAut, ih, pow_succ', mul_inv_rev]
    group

theorem even_E6_canonical_graph_full_pointwise_centralizer
    {f : ℕ} (hf : 1 ≤ f) (k : Type)
    [Field k] (hk : Nat.card k = 2 ^ f) :
    Subgroup.centralizer {diagramConjAut TwistTag.E6 k} ⊓
        Subgroup.centralizer ((((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).subgroupOf
          (adjointGroup TwistTag.E6.tag k)).map MulAut.conj :
            Subgroup (MulAut (adjointGroup TwistTag.E6.tag k))) :
              Set (MulAut (adjointGroup TwistTag.E6.tag k))) =
      Subgroup.zpowers (diagramConjAut TwistTag.E6 k) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : CharP k 2 := finite_field_prime_power_characteristic Nat.prime_two hf hk
  have hk2 : ringChar k = 2 := ringChar.eq k 2
  have h2 : (2 : k) = 0 := two_eq_zero_of_ringChar hk2
  set C := adjointGroup TwistTag.E6.tag k
  set P := diagramMap TwistTag.E6 k
  set η := diagramConjAut TwistTag.E6 k
  set Γ := twistedFixedGroup TwistTag.E6 k (RingHom.id k)
  have hZ : Subgroup.center C = ⊥ := center_adjointGroup_eq_bot
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have hη : ∀ g : C, (η g : ModGL TwistTag.E6.tag k) = P * g * P⁻¹ :=
    coe_diagramConjAut TwistTag.E6 k
  have hP2 : P * P = 1 := diagramMap_E6_mul_self
  have hPinv : P⁻¹ = P := (eq_inv_of_mul_eq_one_left hP2).symm
  have hΓfix : ∀ g : C, (g : ModGL TwistTag.E6.tag k) ∈ Γ → η g = g := fun g hg =>
    Subtype.ext (by rw [hη, (mem_twistedFixedGroup_id_iff.1 hg).2, mul_inv_cancel_right])
  have hηN : ∀ n ∈ ((Γ.subgroupOf C).map MulAut.conj : Subgroup (MulAut C)), n * η = η * n := by
    rintro _ ⟨j, hj, rfl⟩
    have h1 : η * MulAut.conj j * η⁻¹ = MulAut.conj j := by
      rw [mulAut_mul_conj_mul_inv, hΓfix j (Subgroup.mem_subgroupOf.1 hj)]
    calc MulAut.conj j * η = η * MulAut.conj j * η⁻¹ * η := by rw [h1]
      _ = η * MulAut.conj j := by group
  refine le_antisymm (fun β hβ => ?_) (Subgroup.zpowers_le.2 (Subgroup.mem_inf.2
    ⟨Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh],
      Subgroup.mem_centralizer_iff.2 fun n hn => hηN n hn⟩))
  obtain ⟨hβη, hβN⟩ := Subgroup.mem_inf.1 hβ
  have hβη' : η * β = β * η := Subgroup.mem_centralizer_iff.1 hβη η (Set.mem_singleton η)
  have hfixJ : ∀ j : C, (j : ModGL TwistTag.E6.tag k) ∈ Γ → β j = j := fun j hj => by
    have hn : MulAut.conj j ∈ ((Γ.subgroupOf C).map MulAut.conj : Subgroup (MulAut C)) :=
      ⟨j, Subgroup.mem_subgroupOf.2 hj, rfl⟩
    have h1 : MulAut.conj j * β = β * MulAut.conj j := Subgroup.mem_centralizer_iff.1 hβN _ hn
    have h2 : MulAut.conj (β j) = MulAut.conj j := by
      rw [← mulAut_mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
    exact hinj h2
  obtain ⟨-, hNF2, hNF3⟩ :=
    ordinary_E_exact_automorphism_normal_form TwistTag.E6.tag (Or.inl rfl) k
  obtain ⟨g, a, φ, ε, hβ⟩ := hNF3 β
  set Q : ModGL TwistTag.E6.tag k := exactQ TwistTag.E6.tag k ε with hQdef
  have hQ : Q = P ^ (ε : ℕ) := rfl
  set x : ModGL TwistTag.E6.tag k := (g : ModGL TwistTag.E6.tag k) * rootDiagUnit TwistTag.E6.tag a
    with hx
  have hβx : ∀ h : C, (β h : ModGL TwistTag.E6.tag k) =
      x * (Q * Units.map (entrywiseHom φ.toRingHom) (h : ModGL TwistTag.E6.tag k) * Q⁻¹) * x⁻¹ :=
    fun h => by
      rw [hβ h, hx, mul_inv_rev]
      simp only [mul_assoc]
  clear_value x Q
  have hPφ : Units.map (entrywiseHom φ.toRingHom) P = P :=
    units_map_entrywiseHom_diagramMap φ.toRingHom
  have hQP : Commute P Q := by
    rw [hQ]
    exact (Commute.refl P).pow_right _
  obtain ⟨ψ, -, hψ⟩ := hNF2 1 φ ε
  have hψ' : ∀ h : C, (ψ h : ModGL TwistTag.E6.tag k) =
      Q * Units.map (entrywiseHom φ.toRingHom) (h : ModGL TwistTag.E6.tag k) * Q⁻¹ := fun h => by
    rw [hψ h, rootDiagUnit_one, one_mul, inv_one, mul_one, ← hQdef]
  set z : ModGL TwistTag.E6.tag k := (P * x)⁻¹ * (x * P) with hz
  have hzC : ∀ w : C, z * (w : ModGL TwistTag.E6.tag k) = w * z := by
    intro w
    obtain ⟨h, rfl⟩ := ψ.surjective w
    have e := congrArg (fun φ' : MulAut C => ((φ' h : C) : ModGL TwistTag.E6.tag k)) hβη'
    simp only [MulAut.mul_apply] at e
    rw [hη, hβx, hβx, hη, map_mul, map_mul, map_inv, hPφ] at e
    rw [hψ' h]
    set w := Q * Units.map (entrywiseHom φ.toRingHom) (h : ModGL TwistTag.E6.tag k) * Q⁻¹
    have hw : Q * (P * Units.map (entrywiseHom φ.toRingHom) (h : ModGL TwistTag.E6.tag k) * P⁻¹) *
        Q⁻¹ = P * w * P⁻¹ := by
      have h1 : P * Q⁻¹ = Q⁻¹ * P := (hQP.inv_right).eq
      calc Q * (P * Units.map (entrywiseHom φ.toRingHom) (h : ModGL TwistTag.E6.tag k) * P⁻¹) *
            Q⁻¹ = (Q * P) * Units.map (entrywiseHom φ.toRingHom) (h : ModGL TwistTag.E6.tag k) *
              (P⁻¹ * Q⁻¹) := by group
        _ = (P * Q) * Units.map (entrywiseHom φ.toRingHom) (h : ModGL TwistTag.E6.tag k) *
              (Q⁻¹ * P⁻¹) := by
            rw [hQP.eq, ← mul_inv_rev, ← mul_inv_rev, hQP.eq]
        _ = P * w * P⁻¹ := by
            simp only [w]
            group
    rw [hw] at e
    have e2 : (x * P) * w * (x * P)⁻¹ = (P * x) * w * (P * x)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev]
      calc x * P * w * (P⁻¹ * x⁻¹) = x * (P * w * P⁻¹) * x⁻¹ := by group
        _ = P * (x * w * x⁻¹) * P⁻¹ := e.symm
        _ = P * x * w * (x⁻¹ * P⁻¹) := by group
    calc z * w = (P * x)⁻¹ * ((x * P) * w * (x * P)⁻¹) * (x * P) := by
          rw [hz]
          group
      _ = (P * x)⁻¹ * ((P * x) * w * (P * x)⁻¹) * (x * P) := by rw [e2]
      _ = w * z := by
          rw [hz]
          group
  clear_value z
  set L := AlgebraicClosure k
  set ι : k →+* L := algebraMap k L
  have hxL : baseChangeGL ι x ∈ adjointGroup TwistTag.E6.tag L := by
    rw [hx, map_mul, baseChangeGL_rootDiagUnit]
    exact mul_mem (baseChangeGL_mem_adjointGroup ι g.2)
      (exceptional_Lang_adjoint_diagonal_lift _ L _).1
  have hz1 : z = 1 := by
    rcases Nat.lt_or_ge f 2 with hf1 | hf2
    ·
      have hk2' : Nat.card k = 2 := by rw [hk, show f = 1 by omega, pow_one]
      have hunit : ∀ u : kˣ, u = 1 := by
        classical
        have : Fintype k := Fintype.ofFinite k
        have hcard : Fintype.card kˣ = 1 := by
          rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hk2']
        have : Subsingleton kˣ := Fintype.card_le_one_iff_subsingleton.mp hcard.le
        exact fun u => Subsingleton.elim u 1
      have ha : rootDiagUnit TwistTag.E6.tag a = 1 := by
        rw [show a = 1 from funext fun i => hunit (a i), rootDiagUnit_one]
      have hzC' : z ∈ C := by
        have h1 := (η g).2
        rw [hη] at h1
        have e : z = (g : ModGL TwistTag.E6.tag k)⁻¹ *
            (P * (g : ModGL TwistTag.E6.tag k) * P⁻¹) := by
          rw [hz, hx, ha, mul_one, mul_inv_rev, hPinv]
          group
        rw [e]
        exact mul_mem (inv_mem g.2) h1
      have hzZ : (⟨z, hzC'⟩ : C) ∈ Subgroup.center C :=
        Subgroup.mem_center_iff.2 fun w => Subtype.ext (hzC w).symm
      rw [hZ, Subgroup.mem_bot] at hzZ
      exact congrArg Subtype.val hzZ
    ·
      have h4 : 4 ≤ Nat.card k := by
        rw [hk]
        calc 4 = 2 ^ 2 := rfl
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      obtain ⟨hιinj, -, hfaith, -⟩ :=
        Chevalley_large_finite_root_centralizer_faithfulness_of_four_le TwistTag.E6.tag k h4 L ι
      have hPL : baseChangeGL ι P = diagramMap TwistTag.E6 L := baseChangeGL_diagramMap ι _
      have hPLinv : (diagramMap TwistTag.E6 L)⁻¹ = diagramMap TwistTag.E6 L :=
        (eq_inv_of_mul_eq_one_left diagramMap_E6_mul_self).symm
      have hzL : baseChangeGL ι z ∈ adjointGroup TwistTag.E6.tag L := by
        have hconj := (diagramConjAut TwistTag.E6 L ⟨_, hxL⟩).2
        rw [coe_diagramConjAut] at hconj
        have hzk : z = x⁻¹ * (P * x * P⁻¹) := by
          rw [hz, mul_inv_rev, hPinv]
          group
        have e : baseChangeGL ι z = (baseChangeGL ι x)⁻¹ * (diagramMap TwistTag.E6 L *
            baseChangeGL ι x * (diagramMap TwistTag.E6 L)⁻¹) := by
          rw [hzk, map_mul, map_inv, map_mul, map_mul, map_inv, hPL]
        rw [e]
        exact mul_mem (inv_mem hxL) hconj
      have hcomm : ∀ h ∈ (adjointGroup TwistTag.E6.tag k).map (baseChangeGL ι),
          baseChangeGL ι z * h = h * baseChangeGL ι z := by
        rintro _ ⟨h0, hh0, rfl⟩
        rw [← map_mul, ← map_mul, hzC ⟨h0, hh0⟩]
      exact hιinj ((hfaith _ hzL hcomm).trans (map_one _).symm)
  have hxP : P * x = x * P := by
    rw [hz] at hz1
    exact inv_mul_eq_one.1 hz1
  have hxΓ : x ∈ Γ := by
    obtain ⟨Fr, hFr⟩ := exists_frobenius_of_ringChar k L hk2
    have h1 : baseChangeGL ι x ∈ twistedFixedGroup TwistTag.E6 L (RingHom.id L) ⊓
        (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
      refine ⟨mem_twistedFixedGroup_id_iff.2 ⟨hxL, ?_⟩,
        units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr x⟩
      rw [← baseChangeGL_diagramMap ι, ← map_mul, hxP, map_mul]
    rw [e6_frobenius_fixed_eq_map hk2 Fr hFr] at h1
    obtain ⟨x', hx', hx'x⟩ := h1
    rw [← baseChangeGL_injective ι hx'x]
    exact hx'
  have hφΓ : ∀ {j : ModGL TwistTag.E6.tag k}, j ∈ Γ →
      Units.map (entrywiseHom φ.toRingHom) j ∈ Γ := fun {j} hj => by
    obtain ⟨hjC, hjP⟩ := mem_twistedFixedGroup_id_iff.1 hj
    refine mem_twistedFixedGroup_id_iff.2 ⟨(entrywiseAdjointAut TwistTag.E6.tag φ ⟨j, hjC⟩).2, ?_⟩
    have h1 : Units.map (entrywiseHom φ.toRingHom) (diagramMap TwistTag.E6 k * j) =
        Units.map (entrywiseHom φ.toRingHom) (j * diagramMap TwistTag.E6 k) := by rw [hjP]
    rwa [map_mul, map_mul, units_map_entrywiseHom_diagramMap] at h1
  have hJid : ∀ j ∈ Γ, x * Units.map (entrywiseHom φ.toRingHom) j * x⁻¹ = j := by
    intro j hj
    have h1 := hβx ⟨j, hj.1⟩
    rw [hfixJ ⟨j, hj.1⟩ hj] at h1
    have hc : Commute P (Units.map (entrywiseHom φ.toRingHom) j) :=
      (mem_twistedFixedGroup_id_iff.1 (hφΓ hj)).2
    rw [hQ, (hc.pow_left _).eq, mul_inv_cancel_right] at h1
    exact h1.symm
  set e := e6FixedF4Equiv k h2
  have hnat : ∀ jΓ : Γ, (e ⟨Units.map (entrywiseHom φ.toRingHom) jΓ, hφΓ jΓ.2⟩ :
      ModGL Tag.F4 k) = Units.map (entrywiseHom φ.toRingHom) (e jΓ : ModGL Tag.F4 k) := fun jΓ => by
    rw [coe_e6FixedF4Equiv, coe_e6FixedF4Equiv]
    exact e6FixedToF4_baseChangeGL φ.toRingHom jΓ
  obtain ⟨hy1, hφ1⟩ := F4_conj_entrywise_eq_id hf hk (e ⟨x, hxΓ⟩) φ fun F => by
    obtain ⟨jΓ, rfl⟩ := e.surjective F
    have h3 : (⟨x, hxΓ⟩ : Γ) * ⟨Units.map (entrywiseHom φ.toRingHom) jΓ, hφΓ jΓ.2⟩ *
        (⟨x, hxΓ⟩ : Γ)⁻¹ = jΓ := Subtype.ext (hJid jΓ jΓ.2)
    have h4 : e ⟨x, hxΓ⟩ * e ⟨Units.map (entrywiseHom φ.toRingHom) jΓ, hφΓ jΓ.2⟩ *
        (e ⟨x, hxΓ⟩)⁻¹ = e jΓ := by
      rw [← map_inv, ← map_mul, ← map_mul, h3]
    have h5 := congrArg (fun y : adjointGroup Tag.F4 k => (y : ModGL Tag.F4 k)) h4
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h5
    rw [hnat] at h5
    exact h5
  have hx1 : x = 1 := congrArg Subtype.val (e.injective (hy1.trans (map_one e).symm))
  subst hφ1
  have hβε : β = η ^ (ε : ℕ) := MulEquiv.ext fun h => Subtype.ext (by
    rw [hβx h, hx1, coe_diagramConjAut_pow, hQ, inv_one, one_mul, mul_one]
    congr 2
    exact Units.ext (entrywise_id _))
  rw [hβε]
  exact Subgroup.npow_mem_zpowers η _

end CFSG.LieType.Chevalley
