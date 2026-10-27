module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHub
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrTwo

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
open scoped commutatorElement

section Family

variable {K : Type*} [Group K] {D : UniversalRootDatum K}

theorem TwoLevi.leviIdx {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    {exc : Fin D.rank → Fin D.rank → Prop} (hL : TwoLevi D exc) (hext : SteinbergExtras D n H)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hidx : ∀ i j, exc i j → ∃ V : Subgroup K,
      V ≤ rankOne D.rootGroup i ⊔ rankOne D.rootGroup j ∧ ⁅V, V⁆ = V ∧
        Nat.card ↥(rankOne D.rootGroup i ⊔ rankOne D.rootGroup j) ∣ 2 * Nat.card V) :
    LeviIdx (fun i => rankOne D.rootGroup i) p (fun i j => D.cartan i j ≠ 0) exc where
  adj_symm _ _ h1 h2 := h1 (D.isFiniteType.apply_eq_zero_iff.2 h2)
  comm _ _ hij hadj := commutes_rankOne_of_cartan_eq_zero hext hij (not_not.1 hadj)
  node i := (hL.node i).imp_right fun h => h p hp hp5
  pair := hL.pair
  exc_symm := hL.exc_symm
  exc_unique := hL.exc_unique
  exc_idx := hidx

end Family

section Quotient

variable {K : Type*} {Y : Type} [Group K] [Group Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {M : ℕ} {π : K →* Y}

theorem borelQuotient_twoHub [Finite K] [Finite Y] {exc : Fin D.rank → Fin D.rank → Prop}
    (h : BorelQuotient D n H π M) (hM : M ∣ 3) (hL : TwoLevi D exc)
    (hidx : ∀ i j, exc i j → ∃ V : Subgroup K,
      V ≤ rankOne D.rootGroup i ⊔ rankOne D.rootGroup j ∧ ⁅V, V⁆ = V ∧
        Nat.card ↥(rankOne D.rootGroup i ⊔ rankOne D.rootGroup j) ∣ 2 * Nat.card V) :
    TwoHub Y := by
  classical
  intro T J hNJ r hr hr5 g hgJ hga
  obtain ⟨ar, hga⟩ := hga
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : (borel D H).map π' ≤ J := by
    rw [← hNπ]
    exact hNJ
  have hBA : borel D H ≤ J.comap π' := fun b hb => hBJ ⟨b, hb, rfl⟩
  have hJeq := eq_map_borel_sup_of_le h.ct h.extras hπ' hBJ
  have hpB : ¬ r ∣ Nat.card ((borel D H).map π') := fun hpB => by
    have := dvd_of_dvd_card_map_borel h.ct h.extras h.pGroup π'
      (fun t ht => hQ.pow_eq_one_of_mem_iSup ht) hr (by omega) hpB
    have := Nat.le_of_dvd (by norm_num) (this.trans hM)
    omega
  set I : Finset (Fin D.rank) := Finset.univ.filter (fun i => i ∈ negIndices D (J.comap π'))
    with hI
  set Λ : Subgroup Y := ⨆ i ∈ I, (rankOne D.rootGroup i).map π' with hΛ
  have hmemI : ∀ i ∈ I, i ∈ negIndices D (J.comap π') := fun i hi => (Finset.mem_filter.1 hi).2
  have hLJ' : ∀ i ∈ I, rankOne D.rootGroup i ≤ J.comap π' := fun i hi =>
    rankOne_le_of_mem_negIndices hBA (hmemI i hi)
  have hLJ : ∀ i ∈ I, (rankOne D.rootGroup i).map π' ≤ J := fun i hi =>
    Subgroup.map_le_iff_le_comap.2 (hLJ' i hi)
  have hswap : ∀ x ∈ Λ, ∀ b ∈ (borel D H).map π', ∃ x' ∈ Λ, ∃ b' ∈ (borel D H).map π',
      b * x = x' * b' := by
    intro x hx
    refine iSup₂_induction (C := fun x => ∀ b ∈ (borel D H).map π', ∃ x' ∈ Λ,
      ∃ b' ∈ (borel D H).map π', b * x = x' * b') hx ?_ ?_ ?_
    · rintro i hi _ ⟨l, hl, rfl⟩ _ ⟨b, hb, rfl⟩
      obtain ⟨l', hl', b', hb', e⟩ := exists_mul_rankOne_eq h.ct h.extras i hb hl
      have hLΛ : (rankOne D.rootGroup i).map π' ≤ Λ := le_iSup₂_of_le i hi le_rfl
      exact ⟨π' l', hLΛ ⟨l', hl', rfl⟩, π' b', ⟨b', hb', rfl⟩, by
        rw [← map_mul, ← map_mul, e]⟩
    · intro b hb
      exact ⟨1, one_mem _, b, hb, by rw [one_mul, mul_one]⟩
    · intro y z hy hz b hb
      obtain ⟨y', hy', b₁, hb₁, e₁⟩ := hy b hb
      obtain ⟨z', hz', b₂, hb₂, e₂⟩ := hz b₁ hb₁
      exact ⟨y' * z', mul_mem hy' hz', b₂, hb₂, by rw [← mul_assoc, e₁, mul_assoc, e₂, mul_assoc]⟩
  let T' : Subgroup Y :=
    { carrier := {x | ∃ x' ∈ Λ, ∃ b ∈ (borel D H).map π', x = x' * b}
      mul_mem' := by
        rintro _ _ ⟨g₁, hg₁, b₁, hb₁, rfl⟩ ⟨g₂, hg₂, b₂, hb₂, rfl⟩
        obtain ⟨g', hg', b', hb', e⟩ := hswap g₂ hg₂ b₁ hb₁
        exact ⟨g₁ * g', mul_mem hg₁ hg', b' * b₂, mul_mem hb' hb₂, by
          rw [mul_assoc, ← mul_assoc b₁, e]; group⟩
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨g, hg, b, hb, rfl⟩
        obtain ⟨g', hg', b', hb', e⟩ := hswap g⁻¹ (inv_mem hg) b⁻¹ (inv_mem hb)
        exact ⟨g', hg', b', hb', by rw [mul_inv_rev, e]⟩ }
  have hJT : J ≤ T' := by
    rw [hJeq]
    refine sup_le (fun b hb => ⟨1, one_mem _, b, hb, by rw [one_mul]⟩) ?_
    refine iSup₂_le fun i hi => ?_
    have hiI : i ∈ I := Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩
    have hLΛ : (rankOne D.rootGroup i).map π' ≤ Λ := le_iSup₂_of_le i hiI le_rfl
    exact fun x hx => ⟨x, hLΛ hx, 1, one_mem _, by rw [mul_one]⟩
  have hdec : ∀ x ∈ J, ∃ a ∈ ⨆ i ∈ I, rankOne D.rootGroup i, ∃ b ∈ borel D H,
      x = π' (a * b) := by
    intro x hx
    obtain ⟨x', hx', b, hb, rfl⟩ := hJT hx
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    have hlift : ∃ a ∈ ⨆ i ∈ I, rankOne D.rootGroup i, π' a = x' := by
      refine iSup₂_induction (C := fun x => ∃ a ∈ ⨆ i ∈ I, rankOne D.rootGroup i, π' a = x) hx'
        ?_ ?_ ?_
      · rintro i hi _ ⟨l, hl, rfl⟩
        exact ⟨l, (le_iSup₂_of_le i hi le_rfl :
          rankOne D.rootGroup i ≤ ⨆ i ∈ I, rankOne D.rootGroup i) hl, rfl⟩
      · exact ⟨1, one_mem _, map_one π'⟩
      · rintro y z ⟨a₁, ha₁, rfl⟩ ⟨a₂, ha₂, rfl⟩
        exact ⟨a₁ * a₂, mul_mem ha₁ ha₂, map_mul π' a₁ a₂⟩
    obtain ⟨a, ha, rfl⟩ := hlift
    exact ⟨a, ha, b₀, hb₀, (map_mul π' a b₀).symm⟩
  exact mem_perfectJoin_of_leviIdx π' hr hr5 (TwoLevi.leviIdx hL h.extras hr hr5 hidx) I hLJ' hBA
    hpB hdec hgJ hga

end Quotient

end CFSG.AGLEmbedding.ParabAutIrr
