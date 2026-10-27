module

public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.LocalAnalysis.OddStandard.ThmCO2Pre

public section

namespace CFSG.OddStandard.ThmC.O2.Gor

open CFSG Subgroup

section Local

variable {Q : Type} [Group Q] [Finite Q]

theorem exists_sylow_subgroupOf (R : Sylow 2 Q) (K : Subgroup Q)
    (hRK : (R : Subgroup Q) ≤ normalizer (K : Set Q)) :
    ∃ T : Sylow 2 K, (T : Subgroup K) = (R : Subgroup Q).subgroupOf K := by
  have : (K.subgroupOf (normalizer (K : Set Q))).Normal := Subgroup.normal_in_normalizer
  have h1 := sylow_inf_normal_relIndex_odd (R.subtype hRK)
    (K.subgroupOf (normalizer (K : Set Q)))
  have h2 : ((R.subtype hRK : Subgroup (normalizer (K : Set Q))) : Subgroup _) =
      (R : Subgroup Q).subgroupOf (normalizer (K : Set Q)) := rfl
  rw [Subgroup.inf_relIndex_right, h2,
    Subgroup.relIndex_subgroupOf (Subgroup.le_normalizer (H := K))] at h1
  exact ⟨(R.isPGroup'.comap_subtype (K := K)).toSylow h1, rfl⟩

theorem exists_odd_complement (R : Sylow 2 Q)
    (habel : ∀ r ∈ (R : Subgroup Q), ∀ s ∈ (R : Subgroup Q), r * s = s * r)
    (K : Subgroup Q) (hRK : (R : Subgroup Q) ≤ normalizer (K : Set Q))
    (hNC : ∀ y ∈ K, y ∈ normalizer (((R : Subgroup Q) ⊓ K : Subgroup Q) : Set Q) →
      y ∈ centralizer (((R : Subgroup Q) ⊓ K : Subgroup Q) : Set Q)) :
    ∃ O : Subgroup Q, O ≤ K ∧ Odd (Nat.card O) ∧
      normalizer (K : Set Q) ≤ normalizer (O : Set Q) ∧ K ≤ O ⊔ (R : Subgroup Q) := by
  have _ := habel
  obtain ⟨T, hT⟩ := exists_sylow_subgroupOf R K hRK
  have hTmem : ∀ x : K, x ∈ (T : Subgroup K) ↔ (x : Q) ∈ (R : Subgroup Q) := by
    intro x
    rw [hT]
    exact Subgroup.mem_subgroupOf
  have hNC' : normalizer ((T : Subgroup K) : Set K) ≤ centralizer ((T : Subgroup K) : Set K) := by
    intro y hy
    have hy' := Subgroup.mem_normalizer_iff.1 hy
    have hyN : (y : Q) ∈ normalizer (((R : Subgroup Q) ⊓ K : Subgroup Q) : Set Q) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨hxR, hxK⟩
        have := (hy' ⟨x, hxK⟩).1 ((hTmem _).2 hxR)
        exact ⟨(hTmem _).1 this, K.mul_mem (K.mul_mem y.2 hxK) (K.inv_mem y.2)⟩
      · rintro ⟨hxR, hxK⟩
        have hxK' : x ∈ K := by
          have := K.mul_mem (K.mul_mem (K.inv_mem y.2) hxK) y.2
          simpa [mul_assoc] using this
        have := (hy' ⟨x, hxK'⟩).2 ((hTmem (y * ⟨x, hxK'⟩ * y⁻¹)).2 hxR)
        exact ⟨(hTmem _).1 this, hxK'⟩
    have hyC := hNC y y.2 hyN
    rw [Subgroup.mem_centralizer_iff] at hyC ⊢
    intro h hh
    exact Subtype.ext (hyC h ⟨(hTmem h).1 hh, h.2⟩)
  obtain ⟨O', hO'n, hO'odd, -, -, hO'char, -, hO'sup, -, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement T hNC'
  refine ⟨O'.map K.subtype, Subgroup.map_subtype_le O', ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hO'odd)
  · intro g hg
    have hgK : ∀ x : Q, x ∈ K ↔ g * x * g⁻¹ ∈ K := Subgroup.mem_normalizer_iff.1 hg
    let φ : MulAut K := Subgroup.normalizerMonoidHom K ⟨g, hg⟩
    have hφ : ∀ x : K, (φ x : Q) = g * x * g⁻¹ := fun x => rfl
    have hfix := hO'char.fixed φ
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : x ∈ O'.comap φ.toMonoidHom := by
        rw [hfix]
        exact hx
      exact ⟨φ x, this, hφ x⟩
    · rintro ⟨y, hy, hyh⟩
      have hhK : h ∈ K := (hgK h).2 (by rw [← hyh]; exact y.2)
      refine ⟨⟨h, hhK⟩, ?_, rfl⟩
      have hφy : φ ⟨h, hhK⟩ = y := Subtype.ext (by rw [hφ]; exact hyh.symm)
      have : (⟨h, hhK⟩ : K) ∈ O'.comap φ.toMonoidHom := by
        show φ ⟨h, hhK⟩ ∈ O'
        rw [hφy]
        exact hy
      rwa [hfix] at this
  · intro k hk
    have hk' : (⟨k, hk⟩ : K) ∈ O' ⊔ (T : Subgroup K) := by
      rw [hO'sup]
      exact Subgroup.mem_top _
    have hkm : k ∈ (O' ⊔ (T : Subgroup K)).map K.subtype := ⟨⟨k, hk⟩, hk', rfl⟩
    rw [Subgroup.map_sup] at hkm
    have hTR : (T : Subgroup K).map K.subtype ≤ (R : Subgroup Q) := by
      rintro _ ⟨t, ht, rfl⟩
      exact (hTmem t).1 ht
    exact sup_le_sup_left hTR _ hkm

omit [Finite Q] in
theorem gl_exists_prod_subgroup (K R : Subgroup Q) (hRK : R ≤ normalizer (K : Set Q)) :
    ∃ P : Subgroup Q, K ≤ P ∧ R ≤ P ∧ ∀ g ∈ P, ∃ k ∈ K, ∃ r ∈ R, g = k * r := by
  have hconj : ∀ r ∈ R, ∀ k ∈ K, r * k * r⁻¹ ∈ K := fun r hr k hk =>
    (Subgroup.mem_normalizer_iff.1 (hRK hr) k).1 hk
  refine ⟨{ carrier := {x | ∃ k ∈ K, ∃ r ∈ R, x = k * r}
            one_mem' := ⟨1, K.one_mem, 1, R.one_mem, by simp⟩
            mul_mem' := ?_
            inv_mem' := ?_ }, ?_, ?_, fun g hg => hg⟩
  · rintro _ _ ⟨k, hk, r, hr, rfl⟩ ⟨k', hk', r', hr', rfl⟩
    refine ⟨k * (r * k' * r⁻¹), K.mul_mem hk (hconj r hr k' hk'), r * r', R.mul_mem hr hr', ?_⟩
    group
  · rintro _ ⟨k, hk, r, hr, rfl⟩
    refine ⟨r⁻¹ * k⁻¹ * r, ?_, r⁻¹, R.inv_mem hr, ?_⟩
    · simpa using hconj r⁻¹ (R.inv_mem hr) k⁻¹ (K.inv_mem hk)
    · group
  · intro k hk
    exact ⟨k, hk, 1, R.one_mem, by simp⟩
  · intro r hr
    exact ⟨1, K.one_mem, r, hr, by simp⟩

omit [Finite Q] in
theorem gl_mem_smul (R : Sylow 2 Q) (y x : Q) :
    x ∈ ((y • R : Sylow 2 Q) : Subgroup Q) ↔ ∃ s ∈ (R : Subgroup Q), y * s * y⁻¹ = x := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  simp [MulAut.conj_apply]

omit [Finite Q] in
theorem gl_le_of_fixed_point_free (R K : Subgroup Q) [Finite R]
    (habel : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r)
    (hRK : R ≤ normalizer (K : Set Q)) {g k r : Q} (hgN : g ∈ normalizer (R : Set Q))
    (hk : k ∈ K) (hr : r ∈ R) (hg : g = k * r)
    (hfix : ∀ s ∈ R, g * s * g⁻¹ = s → s = 1) : R ≤ K := by
  have hgR : ∀ s ∈ R, g * s * g⁻¹ ∈ R := fun s hs => (Subgroup.mem_normalizer_iff.1 hgN s).1 hs
  let f : R → R := fun s => ⟨g * s * g⁻¹ * (s : Q)⁻¹, R.mul_mem (hgR s s.2) (R.inv_mem s.2)⟩
  have hinj : Function.Injective f := by
    intro s s' h
    have h' : g * s * g⁻¹ * (s : Q)⁻¹ = g * s' * g⁻¹ * (s' : Q)⁻¹ := congrArg Subtype.val h
    have hs : (s : Q) ∈ R := s.2
    have hs' : (s' : Q) ∈ R := s'.2
    have ha' : g * s' * g⁻¹ ∈ R := hgR s' hs'
    have h1 : g * s * g⁻¹ = (g * s' * g⁻¹) * ((s' : Q)⁻¹ * s) := by
      calc g * s * g⁻¹ = g * s * g⁻¹ * (s : Q)⁻¹ * s := by group
        _ = g * s' * g⁻¹ * (s' : Q)⁻¹ * s := by rw [h']
        _ = (g * s' * g⁻¹) * ((s' : Q)⁻¹ * s) := by group
    have h2 := habel _ ha' _ (R.mul_mem (R.inv_mem hs') hs)
    have h3 : (s' : Q)⁻¹ * s = s * (s' : Q)⁻¹ := habel _ (R.inv_mem hs') _ hs
    have hcomm : g * (s * (s' : Q)⁻¹) * g⁻¹ = s * (s' : Q)⁻¹ := by
      calc g * (s * (s' : Q)⁻¹) * g⁻¹ = (g * s * g⁻¹) * (g * s' * g⁻¹)⁻¹ := by group
        _ = ((g * s' * g⁻¹) * ((s' : Q)⁻¹ * s)) * (g * s' * g⁻¹)⁻¹ := by rw [← h1]
        _ = ((s' : Q)⁻¹ * s) * (g * s' * g⁻¹) * (g * s' * g⁻¹)⁻¹ := by rw [h2]
        _ = (s' : Q)⁻¹ * s := by group
        _ = s * (s' : Q)⁻¹ := h3
    exact Subtype.ext (mul_inv_eq_one.1 (hfix _ (R.mul_mem hs (R.inv_mem hs')) hcomm))
  intro x hx
  obtain ⟨s, hs⟩ := Finite.surjective_of_injective hinj ⟨x, hx⟩
  have hs' : g * s * g⁻¹ * (s : Q)⁻¹ = x := congrArg Subtype.val hs
  have hrs : r * s * r⁻¹ = s := by rw [habel r hr s s.2]; exact mul_inv_cancel_right _ _
  have hconj : (s : Q) * k⁻¹ * (s : Q)⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.1 (hRK s.2) k⁻¹).1 (K.inv_mem hk)
  have hx' : x = k * ((s : Q) * k⁻¹ * (s : Q)⁻¹) := by
    rw [← hs', hg]
    calc k * r * s * (k * r)⁻¹ * (s : Q)⁻¹ = k * (r * s * r⁻¹) * k⁻¹ * (s : Q)⁻¹ := by group
      _ = k * ((s : Q) * k⁻¹ * (s : Q)⁻¹) := by rw [hrs]; group
  rw [hx']
  exact K.mul_mem hk hconj

theorem le_of_moves (R : Sylow 2 Q)
    (habel : ∀ r ∈ (R : Subgroup Q), ∀ s ∈ (R : Subgroup Q), r * s = s * r)
    (hfpf : ∀ g ∈ normalizer ((R : Subgroup Q) : Set Q),
      (∀ r ∈ (R : Subgroup Q), g * r * g⁻¹ = r) ∨
        (∀ r ∈ (R : Subgroup Q), g * r * g⁻¹ = r → r = 1))
    (K : Subgroup Q) (hRK : (R : Subgroup Q) ≤ normalizer (K : Set Q)) {y : Q} (hyK : y ∈ K)
    (hyN : y ∈ normalizer (((R : Subgroup Q) ⊓ K : Subgroup Q) : Set Q))
    (hyC : y ∉ centralizer (((R : Subgroup Q) ⊓ K : Subgroup Q) : Set Q)) :
    (R : Subgroup Q) ≤ K := by
  obtain ⟨P, hKP, hRP, hPprod⟩ := gl_exists_prod_subgroup K (R : Subgroup Q) hRK
  obtain ⟨T, hTdef⟩ : ∃ T : Subgroup Q, T = (R : Subgroup Q) ⊓ K := ⟨_, rfl⟩
  rw [← hTdef] at hyN hyC
  have hTR : T ≤ (R : Subgroup Q) := hTdef ▸ inf_le_left
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup Q, C = centralizer (T : Set Q) ⊓ P := ⟨_, rfl⟩
  have hCmem : ∀ x, x ∈ C ↔ x ∈ centralizer (T : Set Q) ∧ x ∈ P := fun x => by
    rw [hCdef]; exact Subgroup.mem_inf
  have hyT : ∀ t ∈ T, y⁻¹ * t * y ∈ T := fun t ht =>
    (Subgroup.mem_normalizer_iff.1 hyN (y⁻¹ * t * y)).2 (by rwa [show y * (y⁻¹ * t * y) * y⁻¹ = t
      by group])
  have hRC : (R : Subgroup Q) ≤ C := fun r hr =>
    (hCmem r).2 ⟨mem_centralizer_iff.2 fun t ht => habel t (hTR ht) r hr, hRP hr⟩
  have hR'C : ((y • R : Sylow 2 Q) : Subgroup Q) ≤ C := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := (gl_mem_smul R y x).1 hx
    refine (hCmem _).2 ⟨mem_centralizer_iff.2 fun t ht => ?_, ?_⟩
    · have h1 : y⁻¹ * t * y ∈ (R : Subgroup Q) := hTR (hyT t ht)
      have h2 := habel _ h1 s hs
      calc t * (y * s * y⁻¹) = y * ((y⁻¹ * t * y) * s) * y⁻¹ := by group
        _ = y * (s * (y⁻¹ * t * y)) * y⁻¹ := by rw [h2]
        _ = y * s * y⁻¹ * t := by group
    · have h1 : s * y⁻¹ * s⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hRK hs) y⁻¹).1 (K.inv_mem hyK)
      have : y * s * y⁻¹ = (y * (s * y⁻¹ * s⁻¹)) * s := by group
      rw [this]
      exact P.mul_mem (P.mul_mem (hKP hyK) (hKP h1)) (hRP hs)
  obtain ⟨c, hc⟩ : ∃ c : C, (c : Q) • R = y • R := by
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C (R.subtype hRC) ((y • R).subtype hR'C)
    refine ⟨c, ?_⟩
    rw [Sylow.smul_subtype hRC c] at hc
    exact Sylow.subtype_injective hc
  have hc1 : (c : Q) ∈ centralizer (T : Set Q) := ((hCmem c).1 c.2).1
  have hc2 : (c : Q) ∈ P := ((hCmem c).1 c.2).2
  have hgN : (c : Q)⁻¹ * y ∈ normalizer ((R : Subgroup Q) : Set Q) := by
    refine Sylow.smul_eq_iff_mem_normalizer.1 ?_
    rw [mul_smul, ← hc, inv_smul_smul]
  have hgT : ∀ t ∈ T, ((c : Q)⁻¹ * y) * t * ((c : Q)⁻¹ * y)⁻¹ = y * t * y⁻¹ := by
    intro t ht
    have h1 : y * t * y⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hyN t).1 ht
    have h2 := mem_centralizer_iff.1 hc1 _ h1
    calc ((c : Q)⁻¹ * y) * t * ((c : Q)⁻¹ * y)⁻¹ = (c : Q)⁻¹ * ((y * t * y⁻¹) * (c : Q)) := by
          group
      _ = (c : Q)⁻¹ * ((c : Q) * (y * t * y⁻¹)) := by rw [h2]
      _ = y * t * y⁻¹ := by group
  obtain ⟨t, htT, htne⟩ : ∃ t ∈ T, t * y ≠ y * t := by
    by_contra hcon
    apply hyC
    rw [mem_centralizer_iff]
    intro t ht
    by_contra hne
    exact hcon ⟨t, ht, hne⟩
  have hfix : ∀ s ∈ (R : Subgroup Q),
      ((c : Q)⁻¹ * y) * s * ((c : Q)⁻¹ * y)⁻¹ = s → s = 1 := by
    rcases hfpf _ hgN with h | h
    · exfalso
      have h1 := h t (hTR htT)
      rw [hgT t htT] at h1
      apply htne
      calc t * y = (y * t * y⁻¹) * y := by rw [h1]
        _ = y * t := by group
    · exact h
  obtain ⟨k, hk, r, hr, hg⟩ := hPprod ((c : Q)⁻¹ * y) (P.mul_mem (P.inv_mem hc2) (hKP hyK))
  exact gl_le_of_fixed_point_free (R : Subgroup Q) K habel hRK hgN hk hr hg hfix

end Local

end CFSG.OddStandard.ThmC.O2.Gor
