module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsRu

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.RuSz

open Subgroup CFSG.Blueprint CFSG.Sporadic.RuSchreier CFSG.EvenSporadicStandard.RuStd
  CFSG.Blueprint.NativeSporadic

section Pair


theorem card_centralizer_of_pair {Y : Type} [Group Y] (hY : IsSporadic Y .Ru) {u : Y}
    (hu : orderOf u = 2) {Kl : Subgroup Y} (hKu : ∀ k ∈ Kl, k * u = u * k)
    (hKcard : Nat.card Kl = 29120) : Nat.card (centralizer ({u} : Set Y)) = 116480 := by
  have hF := ruFacts_of_isSporadic hY
  have hdvd : Nat.card Kl ∣ Nat.card (centralizer ({u} : Set Y)) :=
    Subgroup.card_dvd_of_le fun k hk => Subgroup.mem_centralizer_singleton_iff.2 (hKu k hk)
  rw [hKcard] at hdvd
  rcases hF.card_centralizer u hu with h | h
  · exfalso
    rw [h] at hdvd
    omega
  · exact h

theorem exists_std_equiv {Y : Type} [Group Y] (hY : IsSporadic Y .Ru) {u : Y}
    (hu : orderOf u = 2) (hcu : Nat.card (centralizer ({u} : Set Y)) = 116480) :
    ∃ e : Y ≃* ruP, e u = ruA0' := by
  obtain ⟨e₀⟩ := CFSG.EvenSporadicStandard.TwoRu.nonempty_mulEquiv_ruP_of_isSporadic hY
  have hv : orderOf (e₀ u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
  have hcv : Nat.card (centralizer ({e₀ u} : Set ruP)) = 116480 := by
    rw [card_centralizer_equiv]
    exact hcu
  have ha : orderOf ruA0' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_ruA0
  obtain ⟨c, hc⟩ := isConj_iff.1 (ruP_isConj_B (e₀ u) ruA0' hv ha hcv card_centralizer_ruA0')
  refine ⟨e₀.trans (MulAut.conj c), ?_⟩
  simpa [MulAut.conj_apply] using hc

@[expose] def emb {Y : Type} [Group Y] (e : Y ≃* ruP) : Y →* Equiv.Perm (Fin 4060) :=
  ruP.subtype.comp e.toMonoidHom

theorem emb_injective {Y : Type} [Group Y] (e : Y ≃* ruP) : Function.Injective (emb e) :=
  Subtype.val_injective.comp e.injective

theorem emb_mem {Y : Type} [Group Y] (e : Y ≃* ruP) (y : Y) : emb e y ∈ ruP := (e y).2

theorem emb_surj {Y : Type} [Group Y] (e : Y ≃* ruP) {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP) :
    ∃ y, emb e y = g := by
  obtain ⟨y, hy⟩ := e.surjective ⟨g, hg⟩
  exact ⟨y, congrArg Subtype.val hy⟩

theorem map_eq_K0 {Y : Type} [Group Y] {e : Y ≃* ruP} {u : Y} (he : e u = ruA0')
    {Kl : Subgroup Y} (hKu : ∀ k ∈ Kl, k * u = u * k) (hKcard : Nat.card Kl = 29120) :
    Kl.map (emb e) = K0 := by
  have hX : Kl.map (emb e) ≤ ruL := by
    rintro _ ⟨k, hk, rfl⟩
    rw [← ruCentralizer_a]
    refine ⟨emb_mem e k, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : emb e k * emb e u = emb e u * emb e k := by rw [← map_mul, ← map_mul, hKu k hk]
    have h2 : emb e u = ruA0 := by simp [emb, he]
    rw [h2] at h1
    exact h1
  refine eq_K0_of_card hX ?_
  rw [Subgroup.card_map_of_injective (emb_injective e), hKcard]

theorem emb_conj_mem {Y : Type} [Group Y] {e : Y ≃* ruP} {u : Y} (he : e u = ruA0') {c : Y}
    (hc : c * u = u * c) : emb e c ∈ ruL := by
  rw [← ruCentralizer_a]
  refine ⟨emb_mem e c, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have h1 : emb e c * emb e u = emb e u * emb e c := by rw [← map_mul, ← map_mul, hc]
  have h2 : emb e u = ruA0 := by simp [emb, he]
  rw [h2] at h1
  exact h1

theorem pair_analysis {Y : Type} [Group Y] (hY : IsSporadic Y .Ru) {u : Y} (hu : orderOf u = 2)
    {Kl : Subgroup Y} (hKu : ∀ k ∈ Kl, k * u = u * k) (hKcard : Nat.card Kl = 29120) :
    IsSimpleGroup Kl ∧ SuzukiModel Kl 2 3 ∧
      (∀ c : Y, c * u = u * c → ∀ k ∈ Kl, c * k * c⁻¹ ∈ Kl) ∧
      Nat.card (centralizer (Kl : Set Y)) = 4 := by
  obtain ⟨e, he⟩ := exists_std_equiv hY hu (card_centralizer_of_pair hY hu hKu hKcard)
  have hmap := map_eq_K0 he hKu hKcard
  have eK : Kl ≃* K0 :=
    (Kl.equivMapOfInjective (emb e) (emb_injective e)).trans (MulEquiv.subgroupCongr hmap)
  refine ⟨?_, suzukiModel_of_equiv eK K0_suzukiModel, ?_, ?_⟩
  · exact (MulEquiv.isSimpleGroup_congr eK).2 K0_simple
  · intro c hc k hk
    have hcL := emb_conj_mem he hc
    have hkK0 : emb e k ∈ K0 := hmap ▸ Subgroup.mem_map_of_mem _ hk
    have hnorm := Subgroup.mem_normalizer_iff.1 (ruL_le_normalizer hcL) (emb e k)
    have h1 : emb e (c * k * c⁻¹) ∈ K0 := by
      rw [map_mul, map_mul, map_inv]
      exact hnorm.1 hkK0
    rw [← hmap] at h1
    obtain ⟨k', hk', hkk⟩ := h1
    have := emb_injective e hkk
    exact this ▸ hk'
  · have hcent : (centralizer (Kl : Set Y)).map (emb e) = DK := by
      ext g
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine mem_DK.2 ⟨emb_mem e y, fun k' hk' => ?_⟩
        rw [← hmap] at hk'
        obtain ⟨k, hk, rfl⟩ := hk'
        rw [← map_mul, ← map_mul]
        exact congrArg _ (Subgroup.mem_centralizer_iff.1 hy k hk)
      · intro hg
        obtain ⟨hgP, hcomm⟩ := mem_DK.1 hg
        obtain ⟨y, rfl⟩ := emb_surj e hgP
        refine ⟨y, Subgroup.mem_centralizer_iff.2 fun k hk => ?_, rfl⟩
        have hkK0 : emb e k ∈ K0 := hmap ▸ Subgroup.mem_map_of_mem _ hk
        apply emb_injective e
        rw [map_mul, map_mul]
        exact hcomm _ hkK0
    rw [← Subgroup.card_map_of_injective (emb_injective e), hcent, card_DK]

theorem exists_pair_Y {Y : Type} [Group Y] (hY : IsSporadic Y .Ru) :
    ∃ (u : Y) (Kl : Subgroup Y), orderOf u = 2 ∧ (∀ k ∈ Kl, k * u = u * k) ∧
      Nat.card Kl = 29120 := by
  obtain ⟨e₀⟩ := CFSG.EvenSporadicStandard.TwoRu.nonempty_mulEquiv_ruP_of_isSporadic hY
  have hK0P : K0 ≤ ruP := K0_le_L.trans ruL_le
  refine ⟨e₀.symm ruA0', (K0.subgroupOf ruP).comap e₀.toMonoidHom, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact orderOf_ruA0
  · intro k hk
    apply e₀.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    have hk' : (e₀ k : Equiv.Perm (Fin 4060)) ∈ K0 := hk
    exact Subtype.ext (ruA0_comm_K0 _ hk').symm
  · have h0 : (K0.subgroupOf ruP).comap e₀.toMonoidHom =
        (K0.subgroupOf ruP).map e₀.symm.toMonoidHom := by
      ext x
      constructor
      · intro hx
        exact ⟨e₀ x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    have h1 : Nat.card ↥((K0.subgroupOf ruP).comap e₀.toMonoidHom) =
        Nat.card (K0.subgroupOf ruP) := by
      rw [h0]
      exact Subgroup.card_map_of_injective e₀.symm.injective
    rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK0P).toEquiv, card_K0]

end Pair

end CFSG.EvenSporadicStandard.Induction.RuSz
