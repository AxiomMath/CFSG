module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallNoTwoGen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOut
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKFacts

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

structure SporCore (p : ℕ) (K : Type) [Group K] [Finite K] (T : Sylow p K) : Prop where
  dvd : p ∣ Nat.card (T : Subgroup K)
  center : Subgroup.center K = ⊥
  centralizer_le : ∀ g : K, (∀ t ∈ (T : Subgroup K), g * t = t * g) → g ∈ (T : Subgroup K)
  maximal : IsCoatom (Subgroup.normalizer ((T : Subgroup K) : Set K))
  solvable : Group.IsSolvable (Subgroup.normalizer ((T : Subgroup K) : Set K))
  torus : ∃ T₀ : Subgroup K, T₀ ≤ Subgroup.normalizer ((T : Subgroup K) : Set K) ∧
    p.Coprime (Nat.card T₀) ∧ (T : Subgroup K) ⊓ Subgroup.centralizer (T₀ : Set K) = ⊥
  invariant : ∀ V : Subgroup K, V ≤ (T : Subgroup K) → V ≠ ⊥ →
    Subgroup.normalizer ((T : Subgroup K) : Set K) ≤ Subgroup.normalizer (V : Set K) →
    V = (T : Subgroup K) ∨ (V = centerOf (T : Subgroup K) ∧ centerOf (T : Subgroup K) ≠ T)

@[expose] def AutFixInner (p : ℕ) (K : Type) [Group K] (T : Sylow p K) : Prop :=
  ∀ f : MulAut K, (∀ t ∈ (T : Subgroup K), f t = t) → f ∈ (MulAut.conj : K →* MulAut K).range

section Transport

variable {K K' : Type} [Group K] [Finite K] [Group K'] [Finite K'] {p : ℕ}

theorem SporCore.of_equiv (e : K ≃* K') {T : Sylow p K} {T' : Sylow p K'}
    (hT : (T : Subgroup K).map e.toMonoidHom = (T' : Subgroup K')) (D : SporCore p K' T') :
    SporCore p K T := by
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro g hg
    refine (hTmem g).2 (D.centralizer_le (e g) fun t' ht' => ?_)
    obtain ⟨t, rfl⟩ := e.surjective t'
    have := hg t ((hTmem t).2 ht')
    rw [← map_mul, ← map_mul, this]
  · have h := D.maximal
    rw [← hN] at h
    exact (OrderIso.isCoatom_iff e.mapSubgroup _).mp h
  · have := D.solvable
    exact Group.isSolvable_of_isSolvable_injective
      (f := ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hN)).toMonoidHom)
      ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hN)).injective
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
  · intro V hVT hV hVN
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
    have hcenter : ∀ x : K, x ∈ centerOf (T : Subgroup K) ↔ e x ∈ centerOf (T' : Subgroup K') := by
      intro x
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨(hTmem x).1 h1, Subgroup.mem_centralizer_iff.2 fun t' ht' => ?_⟩
        obtain ⟨t, rfl⟩ := e.surjective t'
        have h3 := Subgroup.mem_centralizer_iff.1 h2 t ((hTmem t).2 ht')
        simpa using congrArg e h3
      · rintro ⟨h1, h2⟩
        refine ⟨(hTmem x).2 h1, Subgroup.mem_centralizer_iff.2 fun t ht => ?_⟩
        have h3 := Subgroup.mem_centralizer_iff.1 h2 (e t) ((hTmem t).1 ht)
        exact e.injective (by simpa using h3)
    rcases D.invariant _ hVmap hV' hVN' with h | ⟨h, hne⟩
    · exact Or.inl (Subgroup.map_injective e.injective (h.trans hT.symm))
    · refine Or.inr ⟨?_, ?_⟩
      · ext x
        have hx : x ∈ V ↔ e x ∈ V.map e.toMonoidHom := by
          rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
        rw [hx, h]
        exact (hcenter x).symm
      · intro hc
        apply hne
        ext x'
        obtain ⟨x, rfl⟩ := e.surjective x'
        rw [← hcenter x, hc, hTmem x]
end Transport

section Consequences

variable {K : Type} [Group K] [Finite K] {p : ℕ}

omit [Finite K] in
theorem coe_smul_sylow_eq_map (T : Sylow p K) (g : K) :
    ((g • T : Sylow p K) : Subgroup K) = (T : Subgroup K).map (MulAut.conj g).toMonoidHom := by
  rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
  rfl

theorem SporCore.of_sylow (hp : p.Prime) {T₀ : Sylow p K} (D : SporCore p K T₀)
    (T : Sylow p K) : SporCore p K T := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K T₀ T
  refine SporCore.of_equiv (MulAut.conj g⁻¹) (T' := T₀) ?_ D
  have h1 : (T : Subgroup K) = (T₀ : Subgroup K).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact coe_smul_sylow_eq_map T₀ g
  rw [h1, Subgroup.map_map]
  conv_rhs => rw [← Subgroup.map_id (T₀ : Subgroup K)]
  congr 1
  ext x
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.id_apply]
  group

theorem SporCore.of_equiv_all {K' : Type} [Group K'] [Finite K'] (hp : p.Prime) (e : K ≃* K')
    (hD : ∃ T₀ : Sylow p K', SporCore p K' T₀) (T : Sylow p K) : SporCore p K T := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T₀, D⟩ := hD
  have hf : Function.Surjective e.toMonoidHom := e.surjective
  have D' := D.of_sylow hp (Sylow.mapSurjective hf T)
  exact SporCore.of_equiv e (T' := Sylow.mapSurjective hf T) rfl D'

theorem SporCore.glbCore_eq (hp : p.Prime) {T : Sylow p K} (D : SporCore p K T)
    (hΓ : GLBCore p 1 (T : Subgroup K) ≠ ⊤) :
    GLBCore p 1 (T : Subgroup K) = Subgroup.normalizer ((T : Subgroup K) : Set K) := by
  have hle : Subgroup.normalizer ((T : Subgroup K) : Set K) ≤ GLBCore p 1 (T : Subgroup K) :=
    le_sSup ⟨T, le_rfl, KFactProofs.GLBCoreNormalizer.one_le_pRank_of_dvd hp D.dvd, rfl⟩
  rcases D.maximal.le_iff.1 hle with h | h
  · exact absurd h hΓ
  · exact h

theorem SporCore.isSolvable_glbCore (hp : p.Prime) {T : Sylow p K} (D : SporCore p K T)
    (hΓ : GLBCore p 1 (T : Subgroup K) ≠ ⊤) : Group.IsSolvable (GLBCore p 1 (T : Subgroup K)) := by
  rw [D.glbCore_eq hp hΓ]
  exact D.solvable

theorem SporCore.noTwo (hp : p.Prime) (hp2 : p ≠ 2) {S : Sylow p K} (D : SporCore p K S)
    (hΓ : GLBCore p 1 (S : Subgroup K) ≠ ⊤) (hdvd : p ^ 2 ∣ Nat.card S)
    (hexp : ∀ s ∈ (S : Subgroup K), s ^ p = 1) (U : Subgroup K) (hU : IsPGroup 2 U)
    (hSU : (S : Subgroup K) ≤ Subgroup.normalizer (U : Set K)) : U = ⊥ :=
  noTwo_of_gamma_le_normalizer hp hp2 S hdvd hexp (D.glbCore_eq hp hΓ).le D.centralizer_le U hU hSU

end Consequences

section Assembly

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem SporCore.mem_of_conj_fix {T : Sylow p K} (D : SporCore p K T) {g : K}
    (hg : ∀ t ∈ (T : Subgroup K), MulAut.conj g t = t) : g ∈ (T : Subgroup K) := by
  refine D.centralizer_le g fun t ht => ?_
  have := hg t ht
  rw [MulAut.conj_apply] at this
  calc g * t = (g * t * g⁻¹) * g := by group
    _ = t * g := by rw [this]

theorem kFactUPrime_of_sporCore (hp : p.Prime) (hD : ∀ T : Sylow p K, SporCore p K T)
    (hA : ∀ T : Sylow p K, AutFixInner p K T) : KFactUPrime p K := by
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
    exact (Subgroup.mem_bot).2 (hNT x hx (D.centralizer_le x hcomm))
  · obtain ⟨g, hg⟩ := hA T f fun t ht => hf t (Subgroup.le_normalizer ht)
    obtain ⟨T₀, hT₀N, -, hT₀⟩ := D.torus
    have hgT : g ∈ (T : Subgroup K) :=
      D.mem_of_conj_fix fun t ht => by rw [hg]; exact hf t (Subgroup.le_normalizer ht)
    have hg1 : g = 1 := by
      have : g ∈ (T : Subgroup K) ⊓ Subgroup.centralizer (T₀ : Set K) := by
        refine ⟨hgT, Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
        have := hf s (hT₀N hs)
        rw [← hg, MulAut.conj_apply] at this
        calc s * g = (g * s * g⁻¹) * g := by rw [this]
          _ = g * s := by group
      rw [hT₀] at this
      exact Subgroup.mem_bot.1 this
    rw [← hg, hg1, map_one]

theorem oneSmallFacts_of_sporCore (hp : p.Prime) {T : Sylow p K} (D : SporCore p K T)
    (hA : AutFixInner p K T) (hPin : AutPInner p K) : OneSmallFacts p K T := by
  refine ⟨?_, D.torus, ?_⟩
  · intro Y hY _ hYN α hα
    have hin : ∀ Y : Subgroup (MulAut K), IsPGroup p Y →
        Y ≤ (MulAut.conj : K →* MulAut K).range :=
      fun Y hY α hα => hPin α (by
        obtain ⟨k, hk⟩ := hY ⟨α, hα⟩
        exact ⟨k, congrArg Subtype.val hk⟩)
    obtain ⟨u, hu, hαu⟩ := pLe_of_pInner hp T D.center hin Y hY (fun b hb β hβ =>
      (Subgroup.mem_normalizer_iff.1 (hYN ⟨b, hb, rfl⟩) β).1 hβ) α hα
    exact ⟨u, hu, hαu.symm⟩
  · intro V hVT hV hVN
    rcases D.invariant V hVT hV hVN with h | h
    · left
      intro f hf
      obtain ⟨g, hg⟩ := hA f fun t ht => hf t (h ▸ ht)
      exact ⟨g, D.mem_of_conj_fix fun t ht => by rw [hg]; exact hf t (h ▸ ht), hg.symm⟩
    · exact Or.inr h

end Assembly

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
