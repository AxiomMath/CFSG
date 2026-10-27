module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneData

public section

namespace CFSG.AGLEmbedding.KFactProofs.NonUnitary

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

structure OneLieBase (p : ℕ) (K : Type) [Group K] [Finite K] (T : Sylow p K) : Prop where
  dvd : p ∣ Nat.card (T : Subgroup K)
  center : Subgroup.center K = ⊥
  maximal : IsCoatom (Subgroup.normalizer ((T : Subgroup K) : Set K))
  solvable : Group.IsSolvable (Subgroup.normalizer ((T : Subgroup K) : Set K))
  inner : ∀ f : MulAut K, (∀ t ∈ (T : Subgroup K), f t = t) →
    ∃ u ∈ (T : Subgroup K), f = MulAut.conj u
  pLe : ∀ Y : Subgroup (MulAut K), IsPGroup p Y →
    (∀ b ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ α ∈ Y,
      MulAut.conj b * α * (MulAut.conj b)⁻¹ ∈ Y) →
    ∀ α ∈ Y, ∃ u ∈ (T : Subgroup K), α = MulAut.conj u
  outer : Group.IsSolvable (Outer K)
  torus : ∃ T₀ : Subgroup K, T₀ ≤ Subgroup.normalizer ((T : Subgroup K) : Set K) ∧
    p.Coprime (Nat.card T₀) ∧ (T : Subgroup K) ⊓ Subgroup.centralizer (T₀ : Set K) = ⊥
  cent : ∀ V : Subgroup K, V ≤ (T : Subgroup K) → V ≠ ⊥ →
    Subgroup.normalizer ((T : Subgroup K) : Set K) ≤ Subgroup.normalizer (V : Set K) →
    ∀ f : MulAut K, (∀ v ∈ V, f v = v) → ∃ t ∈ (T : Subgroup K), f = MulAut.conj t

section Transport

theorem OneLieBase.of_equiv {K K' : Type} [Group K] [Finite K] [Group K'] [Finite K']
    {p : ℕ} (e : K ≃* K') {T : Sylow p K} {T' : Sylow p K'}
    (hT : (T : Subgroup K).map e.toMonoidHom = (T' : Subgroup K'))
    (D : OneLieBase p K' T') : OneLieBase p K T := by
  have hTmem : ∀ x : K, x ∈ (T : Subgroup K) ↔ e x ∈ (T' : Subgroup K') := by
    intro x
    rw [← hT, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hN : (Subgroup.normalizer ((T : Subgroup K) : Set K)).map e.toMonoidHom =
      Subgroup.normalizer ((T' : Subgroup K') : Set K') := by
    rw [Subgroup.map_equiv_normalizer_eq, hT]
  have hNmem : ∀ x : K, x ∈ Subgroup.normalizer ((T : Subgroup K) : Set K) ↔
      e x ∈ Subgroup.normalizer ((T' : Subgroup K') : Set K') := by
    intro x
    rw [← hN, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hconj : ∀ x : K, MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := fun x =>
    CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e x
  have hcongr : ∀ (f : MulAut K) (x : K), (MulAut.congr e f) (e x) = e (f x) := by
    intro f x
    simp [MulAut.congr_apply]
  have hinner : ∀ (f : MulAut K) (u' : K'), MulAut.congr e f = MulAut.conj u' →
      f = MulAut.conj (e.symm u') := by
    intro f u' hf
    apply MulEquiv.ext
    intro x
    have h1 := congrArg (fun φ : MulAut K' => φ (e x)) hf
    simp only [hcongr, MulAut.conj_apply] at h1
    apply e.injective
    rw [h1, MulAut.conj_apply]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : Nat.card (T' : Subgroup K') = Nat.card (T : Subgroup K) := by
      rw [← hT, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    rw [← h]
    exact D.dvd
  · rw [eq_bot_iff]
    intro x hx
    have : e x ∈ Subgroup.center K' := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx z]
    rw [D.center] at this
    exact Subgroup.mem_bot.2 (e.injective (by rw [map_one]; exact Subgroup.mem_bot.1 this))
  · have h := D.maximal
    rw [← hN] at h
    exact (OrderIso.isCoatom_iff e.mapSubgroup _).mp h
  · have := D.solvable
    exact Group.isSolvable_of_isSolvable_injective
      (f := ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hN)).toMonoidHom)
      ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hN)).injective
  · intro f hf
    obtain ⟨u', hu', hfu'⟩ := D.inner (MulAut.congr e f) fun t' ht' => by
      obtain ⟨t, rfl⟩ := e.surjective t'
      rw [hcongr]
      exact congrArg e (hf t ((hTmem t).2 ht'))
    exact ⟨e.symm u', (hTmem _).2 (by simpa using hu'), hinner f u' hfu'⟩
  · intro Y hY hYN α hα
    let Y' : Subgroup (MulAut K') := Y.map (MulAut.congr e).toMonoidHom
    have hY' : IsPGroup p Y' := by
      rintro ⟨_, ⟨a, ha, rfl⟩⟩
      obtain ⟨k, hk⟩ := hY ⟨a, ha⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : a ^ p ^ k = 1 := congrArg Subtype.val hk
      show (MulAut.congr e).toMonoidHom a ^ p ^ k = 1
      rw [← map_pow, h1, map_one]
    have hyp : ∀ b' ∈ Subgroup.normalizer ((T' : Subgroup K') : Set K'), ∀ β' ∈ Y',
        MulAut.conj b' * β' * (MulAut.conj b')⁻¹ ∈ Y' := by
      intro b' hb' β' hβ'
      obtain ⟨β, hβ, rfl⟩ := hβ'
      have hb : e.symm b' ∈ Subgroup.normalizer ((T : Subgroup K) : Set K) :=
        (hNmem _).2 (by simpa using hb')
      refine ⟨_, hYN (e.symm b') hb β hβ, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, hconj, MulEquiv.apply_symm_apply]
    obtain ⟨u', hu', hαu'⟩ := D.pLe Y' hY' hyp (MulAut.congr e α) ⟨α, hα, rfl⟩
    exact ⟨e.symm u', (hTmem _).2 (by simpa using hu'), hinner α u' hαu'⟩
  · have := D.outer
    exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e.symm
  · obtain ⟨T₀', hT₀N, hcop, hT₀⟩ := D.torus
    refine ⟨T₀'.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      rw [hNmem]
      simpa using hT₀N hy
    · rwa [Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective]
    · rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxT, hxC⟩ := hx
      have : e x ∈ (T' : Subgroup K') ⊓ Subgroup.centralizer (T₀' : Set K') := by
        refine ⟨(hTmem x).1 hxT, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
        have h1 := Subgroup.mem_centralizer_iff.1 hxC (e.symm y) ⟨y, hy, rfl⟩
        have h2 := congrArg e h1
        simpa using h2
      rw [hT₀] at this
      exact Subgroup.mem_bot.2 (e.injective (by rw [map_one]; exact Subgroup.mem_bot.1 this))
  · intro V hVT hV hVN f hf
    have hVmap : V.map e.toMonoidHom ≤ (T' : Subgroup K') := by
      rw [← hT]
      exact Subgroup.map_mono hVT
    have hV' : V.map e.toMonoidHom ≠ ⊥ := fun h =>
      hV (Subgroup.map_injective e.injective (h.trans (Subgroup.map_bot _).symm))
    have hVN' : Subgroup.normalizer ((T' : Subgroup K') : Set K') ≤
        Subgroup.normalizer ((V.map e.toMonoidHom : Subgroup K') : Set K') := by
      intro b' hb'
      have hb : e.symm b' ∈ Subgroup.normalizer ((T : Subgroup K) : Set K) :=
        (hNmem _).2 (by simpa using hb')
      have h1 : e (e.symm b') ∈ (Subgroup.normalizer (V : Set K)).map e.toMonoidHom :=
        ⟨_, hVN hb, rfl⟩
      rw [Subgroup.map_equiv_normalizer_eq] at h1
      simpa using h1
    obtain ⟨u', hu', hfu'⟩ := D.cent _ hVmap hV' hVN' (MulAut.congr e f) fun v' hv' => by
      obtain ⟨v, hv, rfl⟩ := hv'
      rw [MulEquiv.coe_toMonoidHom, hcongr]
      exact congrArg e (hf v hv)
    exact ⟨e.symm u', (hTmem _).2 (by simpa using hu'), hinner f u' hfu'⟩

end Transport

section Assembly

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem OneLieBase.centralizer_le {T : Sylow p K} (D : OneLieBase p K T) {g : K}
    (hg : ∀ t ∈ (T : Subgroup K), g * t = t * g) : g ∈ (T : Subgroup K) := by
  obtain ⟨u, hu, hgu⟩ := D.inner (MulAut.conj g) fun t ht => by
    rw [MulAut.conj_apply, hg t ht]
    group
  have := conj_injective_of_center_trivial D.center hgu
  rwa [this]

theorem OneLieBase.glbCore_eq (hp : p.Prime) {T : Sylow p K} (D : OneLieBase p K T)
    (hΓ : GLBCore p 1 (T : Subgroup K) ≠ ⊤) :
    GLBCore p 1 (T : Subgroup K) = Subgroup.normalizer ((T : Subgroup K) : Set K) := by
  have hle : Subgroup.normalizer ((T : Subgroup K) : Set K) ≤ GLBCore p 1 (T : Subgroup K) :=
    le_sSup ⟨T, le_rfl, KFactProofs.GLBCoreNormalizer.one_le_pRank_of_dvd hp D.dvd, rfl⟩
  rcases D.maximal.le_iff.1 hle with h | h
  · exact absurd h hΓ
  · exact h

theorem kFactUPrime_of_base (hp : p.Prime) (hD : ∀ T : Sylow p K, OneLieBase p K T) :
    KFactUPrime p K := by
  intro T hΓ
  have : Fact p.Prime := ⟨hp⟩
  have D := hD T
  rw [D.glbCore_eq hp hΓ]
  refine ⟨fun Y hY => ?_, fun N hNB hNnorm hcop => ?_, fun f hf => ?_⟩
  · rcases D.maximal.le_iff.1 hY with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨k, hk⟩ := (T.2).exists_card_eq
    have hNT : ∀ y ∈ N, y ∈ (T : Subgroup K) → y = 1 := by
      intro y hyN hyT
      have h1 : orderOf y ∣ Nat.card N := by
        have := orderOf_dvd_natCard (⟨y, hyN⟩ : N)
        rwa [← Subgroup.orderOf_coe] at this
      have h2 : orderOf y ∣ Nat.card (T : Subgroup K) := by
        have := orderOf_dvd_natCard (⟨y, hyT⟩ : (T : Subgroup K))
        rwa [← Subgroup.orderOf_coe] at this
      rw [hk] at h2
      have h3 : Nat.Coprime (orderOf y) (Nat.card N) := by
        have h4 : Nat.Coprime (p ^ k) (Nat.card N) := Nat.Coprime.pow_left k hcop
        exact Nat.Coprime.coprime_dvd_left h2 h4
      exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h3 h1)
    have hcomm : ∀ t ∈ (T : Subgroup K), x * t = t * x := by
      intro t ht
      have htB : t ∈ Subgroup.normalizer ((T : Subgroup K) : Set K) :=
        Subgroup.le_normalizer ht
      have hxB : x ∈ Subgroup.normalizer ((T : Subgroup K) : Set K) := hNB hx
      have h1 : x * t * x⁻¹ * t⁻¹ ∈ (T : Subgroup K) := by
        refine Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.1 hxB t).1 ht)
          (Subgroup.inv_mem _ ht)
      have h2 : x * t * x⁻¹ * t⁻¹ ∈ N := by
        have hn : (⟨t, htB⟩ : Subgroup.normalizer ((T : Subgroup K) : Set K)) *
            ⟨x⁻¹, Subgroup.inv_mem _ hxB⟩ * (⟨t, htB⟩ : Subgroup.normalizer
              ((T : Subgroup K) : Set K))⁻¹ ∈ N.subgroupOf _ :=
          hNnorm.conj_mem ⟨x⁻¹, Subgroup.inv_mem _ hxB⟩
            (Subgroup.mem_subgroupOf.2 (Subgroup.inv_mem _ hx)) ⟨t, htB⟩
        have hn' : t * x⁻¹ * t⁻¹ ∈ N := Subgroup.mem_subgroupOf.1 hn
        have := Subgroup.mul_mem _ hx hn'
        simpa [mul_assoc] using this
      have h3 := hNT _ h2 h1
      calc x * t = (x * t * x⁻¹ * t⁻¹) * (t * x) := by group
        _ = t * x := by rw [h3, one_mul]
    exact (Subgroup.mem_bot).2 (hNT x hx (D.centralizer_le hcomm))
  · obtain ⟨u, hu, hfu⟩ := D.inner f fun t ht => hf t (Subgroup.le_normalizer ht)
    obtain ⟨T₀, hT₀N, -, hT₀⟩ := D.torus
    have hu1 : u = 1 := by
      have : u ∈ (T : Subgroup K) ⊓ Subgroup.centralizer (T₀ : Set K) := by
        refine ⟨hu, Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
        have := hf s (hT₀N hs)
        rw [hfu, MulAut.conj_apply] at this
        calc s * u = (u * s * u⁻¹) * u := by rw [this]
          _ = u * s := by group
      rw [hT₀] at this
      exact Subgroup.mem_bot.1 this
    rw [hfu, hu1, map_one]

theorem oneLieFacts_of_base (hp : p.Prime) (hD : ∀ T : Sylow p K, OneLieBase p K T)
    (T : Sylow p K) : OneLieFacts p K T := by
  have D := hD T
  refine ⟨kFactUPrime_of_base hp hD, D.outer, ?_, D.torus, ?_⟩
  · intro Y hY _ hYN α hα
    obtain ⟨u, hu, hαu⟩ := D.pLe Y hY (fun b hb β hβ =>
      (Subgroup.mem_normalizer_iff.1 (hYN ⟨b, hb, rfl⟩) β).1 hβ) α hα
    exact ⟨u, hu, hαu.symm⟩
  · intro V hVT hV hVN
    exact Or.inl (D.cent V hVT hV hVN)

end Assembly

end CFSG.AGLEmbedding.KFactProofs.NonUnitary
