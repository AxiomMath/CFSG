module

public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadic

public section

open scoped commutatorElement

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def OPrimeCoreTrivialAt (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∀ s : K, orderOf s = p → GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set K)) = ⊥

@[expose] def NoOuterFixesCentralizer (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∀ σ : MulAut K, σ ^ 2 = 1 → σ ∉ innerAut K → ∀ s : K, orderOf s = p →
    ∃ t : K, s * t = t * s ∧ σ t ≠ t

section General

variable {p : ℕ} {K : Type*} [Group K]

theorem eq_of_ne_one_of_card_le_two {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 2)
    {a b : G} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  by_contra hab
  have hinj : Function.Injective (![1, a, b] : Fin 3 → G) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_fin] at this
  omega

theorem conj_injective_of_center_eq_bot (hcen : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have : g ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h := congrArg (fun φ : MulAut K => φ y) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  rw [hcen] at this
  exact this

theorem mulAut_mul_conj_mul_inv (σ : MulAut K) (t : K) :
    σ * MulAut.conj t * σ⁻¹ = MulAut.conj (σ t) := by
  ext z
  simp [MulAut.conj_apply]

theorem isLocallyOneBalancedAbs_of_parts [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center K = ⊥) (hout : Nat.card (Outer K) ≤ 2)
    (h1 : OPrimeCoreTrivialAt p K) (h2 : NoOuterFixesCentralizer p K) :
    IsLocallyOneBalancedAbs p K := by
  intro x hx H hH _
  have hψ : Function.Injective (MulAut.conj : K →* MulAut K) :=
    conj_injective_of_center_eq_bot hcen
  let q : MulAut K →* Outer K := QuotientGroup.mk' (inner K)
  have hqker : ∀ y : MulAut K, q y = 1 ↔ y ∈ innerAut K := fun y =>
    QuotientGroup.eq_one_iff y
  have hsq : ∀ y : MulAut K, (q y) ^ 2 = 1 := by
    intro y
    have hc : (q y) ^ Nat.card (Outer K) = 1 := pow_card_eq_one'
    have hpos : 0 < Nat.card (Outer K) := Nat.card_pos
    interval_cases hn : Nat.card (Outer K)
    · have : q y = 1 := by simpa using hc
      rw [this, one_pow]
    · exact hc
  have hxi : x ∈ innerAut K := by
    refine (hqker x).1 ?_
    have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have h3 : (q x) ^ p = 1 := by
      rw [← map_pow, hxp, map_one]
    have h4 : orderOf (q x) ∣ Nat.gcd p 2 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one (hsq x))
    have hg : Nat.gcd p 2 = 1 := by
      rw [Nat.gcd_comm]
      exact (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at h4
    exact h4
  obtain ⟨s, rfl⟩ := hxi
  have hs : orderOf s = p := by
    rw [← hx, orderOf_injective _ hψ s]
  set A : Subgroup (MulAut K) := H ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut K))
    with hA
  set N := GLAPPrimeCoreOf p A with hN
  have hNA : N ≤ A := GLAPPrimeCoreOf_le A
  have hNinn : N ⊓ innerAut K = ⊥ := by
    set B : Subgroup (MulAut K) :=
      innerAut K ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut K)) with hB
    have hBA : B ≤ A := inf_le_inf hH le_rfl
    have hOB : GLAPPrimeCoreOf p B = ⊥ := by
      have hmap := map_glaPPrimeCoreOf_of_injective p (MulAut.conj : K →* MulAut K) hψ
        (Subgroup.centralizer ({s} : Set K))
      have hc := map_inf_centralizer_of_injective (MulAut.conj : K →* MulAut K) hψ ⊤ s
      rw [top_inf_eq] at hc
      have hrange : (⊤ : Subgroup K).map (MulAut.conj : K →* MulAut K) = innerAut K :=
        MonoidHom.range_eq_map _ |>.symm
      rw [hrange] at hc
      rw [h1 s hs, Subgroup.map_bot, hc] at hmap
      exact hmap.symm
    rw [eq_bot_iff, ← hOB]
    refine le_GLAPPrimeCoreOf_of_normal (fun y hy => ⟨hy.2, (hNA hy.1).2⟩) ?_ ?_
    · intro g hg y hy
      have hgA := hBA hg
      refine ⟨GLAPPrimeCoreOf_conj_mem g hgA y hy.1, ?_⟩
      exact (inner_normal K).conj_mem y hy.2 g
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (coprime_card_GLAPPrimeCoreOf hp A)
  rw [eq_bot_iff]
  intro σ hσ
  by_contra hσ1
  have hσ1' : σ ≠ 1 := by simpa using hσ1
  have hσinn : σ ∉ innerAut K := fun hi => hσ1 (by
    have : σ ∈ N ⊓ innerAut K := ⟨hσ, hi⟩
    rw [hNinn] at this
    exact this)
  have hqσ : q σ ≠ 1 := fun e => hσinn ((hqker σ).1 e)
  have hσ2 : σ ^ 2 = 1 := by
    have hmem : σ ^ 2 ∈ N ⊓ innerAut K := by
      refine ⟨N.pow_mem hσ 2, (hqker _).1 ?_⟩
      rw [map_pow]
      exact hsq σ
    rw [hNinn] at hmem
    exact hmem
  obtain ⟨t, hts, hσt⟩ := h2 σ hσ2 hσinn s hs
  have hcomm_out : ∀ a : MulAut K, q a * q σ = q σ * q a := by
    intro a
    by_cases ha : q a = 1
    · rw [ha, one_mul, mul_one]
    · rw [eq_of_ne_one_of_card_le_two hout ha hqσ]
  have ht : MulAut.conj t ∈ A := by
    refine Subgroup.mem_inf.2 ⟨hH ⟨t, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh, ← map_mul, ← map_mul, hts]
  have hcent : MulAut.conj t * σ * (MulAut.conj t)⁻¹ = σ := by
    have hmem : MulAut.conj t * σ * (MulAut.conj t)⁻¹ * σ⁻¹ ∈ N ⊓ innerAut K := by
      refine ⟨N.mul_mem (GLAPPrimeCoreOf_conj_mem _ ht σ hσ) (N.inv_mem hσ), (hqker _).1 ?_⟩
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      have := hcomm_out (MulAut.conj t)
      calc q (MulAut.conj t) * q σ * (q (MulAut.conj t))⁻¹ * (q σ)⁻¹
          = (q σ * q (MulAut.conj t)) * (q (MulAut.conj t))⁻¹ * (q σ)⁻¹ := by rw [this]
        _ = 1 := by group
    rw [hNinn] at hmem
    have h1' : MulAut.conj t * σ * (MulAut.conj t)⁻¹ * σ⁻¹ = 1 := hmem
    exact mul_inv_eq_one.1 h1'
  have hc2 : σ * MulAut.conj t * σ⁻¹ = MulAut.conj t := by
    have h3 : MulAut.conj t * σ = σ * MulAut.conj t := by
      have := congrArg (fun y => y * MulAut.conj t) hcent
      simpa [mul_assoc] using this
    rw [← h3]
    group
  rw [mulAut_mul_conj_mul_inv] at hc2
  exact hσt (hψ hc2)

theorem inf_eq_bot_of_coprime_isPGroup {G : Type*} [Group G] [Finite G] (hp : p.Prime)
    {R Q : Subgroup G} (hR : Nat.Coprime p (Nat.card R)) (hQ : IsPGroup p Q) : R ⊓ Q = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hc : Nat.Coprime (Nat.card R) (Nat.card Q) := by
    rw [hn]
    exact Nat.Coprime.pow_right n hR.symm
  exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hc)

theorem gLAPPrimeCoreOf_eq_bot_of_pConstrained {G : Type*} [Group G] [Finite G] (hp : p.Prime)
    {C Q : Subgroup G} (hQC : Q ≤ C) (hQn : ∀ g ∈ C, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hQp : IsPGroup p Q) (hcQ : C ⊓ Subgroup.centralizer (Q : Set G) ≤ Q) :
    GLAPPrimeCoreOf p C = ⊥ := by
  set R := GLAPPrimeCoreOf p C with hR
  have hRQ : R ⊓ Q = ⊥ := inf_eq_bot_of_coprime_isPGroup hp (coprime_card_GLAPPrimeCoreOf hp C) hQp
  rw [eq_bot_iff]
  intro y hy
  have hyC : y ∈ C := GLAPPrimeCoreOf_le C hy
  have hcent : y ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h1 : y * q * y⁻¹ * q⁻¹ ∈ Q := Q.mul_mem (hQn y hyC q hq) (Q.inv_mem hq)
    have h2 : y * q * y⁻¹ * q⁻¹ ∈ R := by
      have := R.mul_mem hy (GLAPPrimeCoreOf_conj_mem q (hQC hq) y⁻¹ (R.inv_mem hy))
      simpa [mul_assoc] using this
    have h3 : y * q * y⁻¹ * q⁻¹ ∈ R ⊓ Q := ⟨h2, h1⟩
    rw [hRQ] at h3
    have h4 : y * q * y⁻¹ * q⁻¹ = 1 := h3
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h4
    exact h4.symm
  have hyQ : y ∈ Q := hcQ ⟨hyC, hcent⟩
  have : y ∈ R ⊓ Q := ⟨hy, hyQ⟩
  rw [hRQ] at this
  exact this

theorem commute_of_mem_gLAPPrimeCoreOf_of_perfect {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) {C L : Subgroup G} (hLC : L ≤ C)
    (hLn : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hperf : ⁅L, L⁆ = L)
    (hZ : ∀ M : Subgroup G, M ≤ L → (∀ g ∈ L, ∀ m ∈ M, g * m * g⁻¹ ∈ M) →
      Nat.Coprime p (Nat.card M) → ∀ m ∈ M, ∀ l ∈ L, l * m = m * l)
    {r : G} (hr : r ∈ GLAPPrimeCoreOf p C) : ∀ l ∈ L, r * l = l * r := by
  set R := GLAPPrimeCoreOf p C with hR
  have hrC : r ∈ C := GLAPPrimeCoreOf_le C hr
  have hcomm : ∀ a ∈ L, ∀ g ∈ L, g * (r * a * r⁻¹ * a⁻¹) = (r * a * r⁻¹ * a⁻¹) * g := by
    intro a ha g hg
    set M : Subgroup G := R ⊓ L with hM
    have hMmem : r * a * r⁻¹ * a⁻¹ ∈ M := by
      refine ⟨?_, ?_⟩
      · have := R.mul_mem hr (GLAPPrimeCoreOf_conj_mem a (hLC ha) r⁻¹ (R.inv_mem hr))
        simpa [mul_assoc] using this
      · exact L.mul_mem (hLn r hrC a ha) (L.inv_mem ha)
    exact hZ M inf_le_right (fun g hg m hm => ⟨GLAPPrimeCoreOf_conj_mem g (hLC hg) m hm.1,
        L.mul_mem (L.mul_mem hg hm.2) (L.inv_mem hg)⟩)
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (coprime_card_GLAPPrimeCoreOf hp C)) _ hMmem g hg
  have hle : ⁅L, L⁆ ≤ Subgroup.centralizer ({r} : Set G) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.1 hx]
    set za := r * a * r⁻¹ * a⁻¹ with hza
    set zb := r * b * r⁻¹ * b⁻¹ with hzb
    have hza' := hcomm a ha
    have hzb' := hcomm b hb
    have hra : r * a * r⁻¹ = za * a := by rw [hza]; group
    have hrb : r * b * r⁻¹ = zb * b := by rw [hzb]; group
    have hza_L : za ∈ L := L.mul_mem (hLn r hrC a ha) (L.inv_mem ha)
    have hzb_L : zb ∈ L := L.mul_mem (hLn r hrC b hb) (L.inv_mem hb)
    have key : r * ⁅a, b⁆ * r⁻¹ = ⁅a, b⁆ := by
      have e1 : r * ⁅a, b⁆ * r⁻¹ = ⁅r * a * r⁻¹, r * b * r⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e1, hra, hrb]
      have c1 : za * a * (zb * b) * (za * a)⁻¹ * (zb * b)⁻¹ = ⁅a, b⁆ := by
        have ha1 : a * zb = zb * a := hzb' a ha
        have hX : za * (a * zb * b * a⁻¹) * za⁻¹ = a * zb * b * a⁻¹ := by
          have hXL : a * zb * b * a⁻¹ ∈ L :=
            L.mul_mem (L.mul_mem (L.mul_mem ha hzb_L) hb) (L.inv_mem ha)
          have := hza' _ hXL
          calc za * (a * zb * b * a⁻¹) * za⁻¹ = (a * zb * b * a⁻¹) * za * za⁻¹ := by rw [← this]
            _ = a * zb * b * a⁻¹ := by group
        have hY : zb * (a * b * a⁻¹ * b⁻¹) * zb⁻¹ = a * b * a⁻¹ * b⁻¹ := by
          have hYL : a * b * a⁻¹ * b⁻¹ ∈ L :=
            L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)
          have := hzb' _ hYL
          calc zb * (a * b * a⁻¹ * b⁻¹) * zb⁻¹ = (a * b * a⁻¹ * b⁻¹) * zb * zb⁻¹ := by
                rw [← this]
            _ = a * b * a⁻¹ * b⁻¹ := by group
        calc za * a * (zb * b) * (za * a)⁻¹ * (zb * b)⁻¹
            = za * (a * zb * b * a⁻¹) * za⁻¹ * (b⁻¹ * zb⁻¹) := by group
          _ = (a * zb * b * a⁻¹) * (b⁻¹ * zb⁻¹) := by rw [hX]
          _ = (zb * a) * b * a⁻¹ * (b⁻¹ * zb⁻¹) := by rw [ha1]
          _ = zb * (a * b * a⁻¹ * b⁻¹) * zb⁻¹ := by group
          _ = ⁅a, b⁆ := by rw [hY, commutatorElement_def]
      rw [commutatorElement_def]
      exact c1
    have := congrArg (· * r) key
    simp only [inv_mul_cancel_right] at this
    exact this
  intro l hl
  have hl' : l ∈ ⁅L, L⁆ := by rw [hperf]; exact hl
  exact (Subgroup.mem_centralizer_iff.1 (hle hl') r (Set.mem_singleton r))

theorem gLAPPrimeCoreOf_eq_bot_of_perfect {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) {C L : Subgroup G} (hLC : L ≤ C)
    (hLn : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hperf : ⁅L, L⁆ = L)
    (hZ : ∀ M : Subgroup G, M ≤ L → (∀ g ∈ L, ∀ m ∈ M, g * m * g⁻¹ ∈ M) →
      Nat.Coprime p (Nat.card M) → ∀ m ∈ M, ∀ l ∈ L, l * m = m * l)
    (hCL : IsPGroup p ↥(C ⊓ Subgroup.centralizer (L : Set G))) :
    GLAPPrimeCoreOf p C = ⊥ := by
  have hle : GLAPPrimeCoreOf p C ≤ C ⊓ Subgroup.centralizer (L : Set G) := by
    intro r hr
    refine Subgroup.mem_inf.2 ⟨GLAPPrimeCoreOf_le C hr, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (commute_of_mem_gLAPPrimeCoreOf_of_perfect hp hLC hLn hperf hZ hr l hl).symm
  have h1 := inf_eq_bot_of_coprime_isPGroup hp (coprime_card_GLAPPrimeCoreOf hp C) hCL
  rw [eq_bot_iff, ← h1]
  exact le_inf le_rfl hle

theorem noOuterFixesCentralizer_of_elemAbelian {k : ℕ}
    (hE : ∀ s : K, orderOf s = p → ∃ E : Subgroup K, IsElemAbelian p E ∧ Nat.card E = p ^ k ∧
      ∀ e ∈ E, s * e = e * s)
    (hK : ∀ σ : MulAut K, σ ^ 2 = 1 → σ ∉ innerAut K → ∀ E : Subgroup K, IsElemAbelian p E →
      Nat.card E = p ^ k → ∃ x ∈ E, σ x ≠ x) :
    NoOuterFixesCentralizer p K := by
  intro σ hσ hσi s hs
  obtain ⟨E, hE1, hE2, hE3⟩ := hE s hs
  obtain ⟨x, hx, hσx⟩ := hK σ hσ hσi E hE1 hE2
  exact ⟨x, hE3 x hx, hσx⟩

theorem OPrimeCoreTrivialAt.of_mulEquiv {K' : Type*} [Group K'] (e : K ≃* K')
    (h : OPrimeCoreTrivialAt p K') : OPrimeCoreTrivialAt p K := by
  intro s hs
  have hmap := map_glaPPrimeCoreOf_of_injective p e.toMonoidHom e.injective
    (Subgroup.centralizer ({s} : Set K))
  have hc := map_inf_centralizer_of_injective e.toMonoidHom e.injective ⊤ s
  rw [top_inf_eq, Subgroup.map_top_of_surjective _ e.surjective, top_inf_eq] at hc
  rw [hc] at hmap
  have h' := h (e s) (by rw [← hs]; exact orderOf_injective e.toMonoidHom e.injective s)
  have h'' : (GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set K))).map e.toMonoidHom = ⊥ := by
    rw [hmap]
    exact h'
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h''

theorem NoOuterFixesCentralizer.of_mulEquiv {K' : Type*} [Group K'] (e : K ≃* K')
    (h : NoOuterFixesCentralizer p K') : NoOuterFixesCentralizer p K := by
  intro σ hσ hσi s hs
  have hσ' : (MulAut.congr e σ) ^ 2 = 1 := by rw [← map_pow, hσ, map_one]
  have hσi' : MulAut.congr e σ ∉ innerAut K' := by
    rintro ⟨y, hy⟩
    apply hσi
    refine ⟨e.symm y, ?_⟩
    apply (MulAut.congr e).injective
    rw [← hy]
    ext z
    simp [MulAut.congr_apply, MulAut.conj_apply]
  obtain ⟨t', ht1, ht2⟩ := h (MulAut.congr e σ) hσ' hσi' (e s)
    (by rw [← hs]; exact orderOf_injective e.toMonoidHom e.injective s)
  refine ⟨e.symm t', ?_, ?_⟩
  · apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ht1]
  · intro hc
    apply ht2
    have : MulAut.congr e σ t' = e (σ (e.symm t')) := by simp [MulAut.congr_apply]
    rw [this, hc, MulEquiv.apply_symm_apply]

theorem isLocallyOneBalancedAbs_of_parts_mulEquiv {K' : Type*} [Group K'] [Finite K]
    (e : K ≃* K') (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center K = ⊥)
    (hout : Nat.card (Outer K) ≤ 2) (h1 : OPrimeCoreTrivialAt p K')
    (h2 : NoOuterFixesCentralizer p K') : IsLocallyOneBalancedAbs p K :=
  isLocallyOneBalancedAbs_of_parts hp hp2 hcen hout (OPrimeCoreTrivialAt.of_mulEquiv e h1)
    (h2.of_mulEquiv e)

end General

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
