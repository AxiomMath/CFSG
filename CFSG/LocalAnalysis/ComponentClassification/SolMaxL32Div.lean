module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig32F

public section

namespace CFSG.ComponentClassification.SolMax.L32

open CFSG Subgroup Equiv

theorem not_dvd_card_quot_pPrimeCore {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : ¬ p ∣ Nat.card (K ⧸ Open.fusionZStar K)) :
    ¬ p ∣ Nat.card (K ⧸ pPrimeCore 2 K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  intro hdvd
  have hO : Open.fusionOddCore K = pPrimeCore 2 K := GSLit.oddCore_eq_pPrimeCore_two K
  set Q := K ⧸ Open.fusionOddCore K with hQdef
  let eQ : Q ≃* K ⧸ pPrimeCore 2 K := QuotientGroup.quotientMulEquivOfEq hO
  have hcardQ : Nat.card Q = Nat.card (K ⧸ pPrimeCore 2 K) := Nat.card_congr eQ.toEquiv
  have hidx : Nat.card (K ⧸ Open.fusionZStar K) = (center Q).index := by
    change (Open.fusionZStar K).index = _
    unfold Open.fusionZStar
    exact Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hmul := (center Q).card_mul_index
  rw [hcardQ] at hmul
  rw [← hmul] at hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with hZ | hZ
  ·
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center Q) p hZ
    have hzQ : orderOf (z : Q) = p := by rw [Subgroup.orderOf_coe]; exact hz
    have hn : (zpowers (z : Q)).Normal := ⟨fun x hx g => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
      have hc : g * (z : Q) = (z : Q) * g := (Subgroup.mem_center_iff.mp z.2 g)
      have hc' : g * (z : Q) ^ k = (z : Q) ^ k * g := ((Commute.zpow_right hc k)).eq
      rw [hc', mul_inv_cancel_right]
      exact zpow_mem (mem_zpowers _) k⟩
    have hcop : Nat.Coprime 2 (Nat.card (zpowers (z : Q))) := by
      rw [Nat.card_zpowers, hzQ]
      exact (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
    have hle : zpowers (z : Q) ≤ pPrimeCore 2 Q := le_sSup ⟨hn, hcop⟩
    have hbot : pPrimeCore 2 Q = ⊥ := by
      have h1 := pPrimeCore_map_iso 2 eQ
      rw [CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2,
        map_eq_bot_iff_of_injective _ (MulEquiv.injective _)] at h1
      exact h1
    rw [hbot, le_bot_iff, zpowers_eq_bot] at hle
    rw [hle, orderOf_one] at hzQ
    exact hp.one_lt.ne hzQ
  · exact h (hidx ▸ hZ)

variable {X : Type} [Group X]

theorem card_map_mk_eq_index {Y H : Subgroup X} :
    Nat.card ((H.subgroupOf Y).map (QuotientGroup.mk' (pPrimeCore 2 ↥Y))) =
      ((pPrimeCore 2 ↥Y).subgroupOf (H.subgroupOf Y)).index := by
  rw [← MonoidHom.domRestrict_range, ← Subgroup.index_ker, MonoidHom.ker_domRestrict,
    QuotientGroup.ker_mk']

theorem dvd_or_dvd_of_le_sup [Finite X] {Y A B L : Subgroup X} (hA : A ≤ Y)
    (hAp : IsPComponent 2 (A.subgroupOf Y)) (hB : B ≤ Y) (hBp : IsPComponent 2 (B.subgroupOf Y))
    (hLAB : L ≤ A ⊔ B) {p : ℕ} (hp : p.Prime) (hpL : p ∣ Nat.card (↥L ⧸ pPrimeCore 2 ↥L)) :
    p ∣ Nat.card (↥A ⧸ pPrimeCore 2 ↥A) ∨ p ∣ Nat.card (↥B ⧸ pPrimeCore 2 ↥B) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥Y) with hπ
  have hLY : L ≤ Y := hLAB.trans (sup_le hA hB)
  have hcomp : ∀ P : Subgroup X, P ≤ Y → IsPComponent 2 (P.subgroupOf Y) →
      Nat.card ((P.subgroupOf Y).map π) = Nat.card (↥P ⧸ pPrimeCore 2 ↥P) := by
    intro P hP hPp
    obtain ⟨-, -, hs, -, -⟩ := id hPp
    rw [hπ, card_map_mk_eq_index]
    have h1 : (pPrimeCore 2 ↥Y).subgroupOf (P.subgroupOf Y) = pPrimeCore 2 ↥(P.subgroupOf Y) := by
      have h2 := UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hs
      calc (pPrimeCore 2 ↥Y).subgroupOf (P.subgroupOf Y) =
          (P.subgroupOf Y ⊓ pPrimeCore 2 ↥Y).subgroupOf (P.subgroupOf Y) :=
            (inf_subgroupOf_left _ _).symm
        _ = ((pPrimeCore 2 ↥(P.subgroupOf Y)).map (P.subgroupOf Y).subtype).subgroupOf
            (P.subgroupOf Y) := by rw [h2]
        _ = pPrimeCore 2 ↥(P.subgroupOf Y) :=
            comap_map_eq_self_of_injective (P.subgroupOf Y).subtype_injective _
    rw [h1]
    change Nat.card (↥(P.subgroupOf Y) ⧸ pPrimeCore 2 ↥(P.subgroupOf Y)) = _
    exact Nat.card_congr (Sol78.coreQuotCongr (subgroupOfEquivOfLe hP)).toEquiv
  have hLimg : p ∣ Nat.card ((L.subgroupOf Y).map π) := by
    rw [hπ, card_map_mk_eq_index]
    have hle : (pPrimeCore 2 ↥Y).subgroupOf (L.subgroupOf Y) ≤ pPrimeCore 2 ↥(L.subgroupOf Y) := by
      have : (pPrimeCore 2 ↥Y).Normal := pPrimeCore_normal
      refine le_sSup ⟨inferInstance, ?_⟩
      have h1 : Nat.card ↥((pPrimeCore 2 ↥Y).subgroupOf (L.subgroupOf Y)) ∣
          Nat.card ↥(pPrimeCore 2 ↥Y) := by
        rw [← card_map_of_injective (L.subgroupOf Y).subtype_injective, subgroupOf_map_subtype]
        exact card_dvd_of_le inf_le_left
      exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
    refine dvd_trans ?_ (Subgroup.index_dvd_of_le hle)
    change p ∣ Nat.card (↥(L.subgroupOf Y) ⧸ pPrimeCore 2 ↥(L.subgroupOf Y))
    rw [Nat.card_congr (Sol78.coreQuotCongr (subgroupOfEquivOfLe hLY)).toEquiv]
    exact hpL
  have hLle : (L.subgroupOf Y).map π ≤ (A.subgroupOf Y).map π ⊔ (B.subgroupOf Y).map π := by
    rw [← Subgroup.map_sup, ← subgroupOf_sup hA hB]
    exact map_mono fun y hy => mem_subgroupOf.mpr (hLAB (mem_subgroupOf.mp hy))
  by_cases hAB : A = B
  · subst hAB
    left
    rw [sup_idem] at hLle
    rw [← hcomp A hA hAp]
    exact dvd_trans hLimg (card_dvd_of_le hLle)
  have hne : A.subgroupOf Y ≠ B.subgroupOf Y := fun h => by
    rw [subgroupOf_inj, inf_of_le_left hA, inf_of_le_left hB] at h
    exact hAB h
  obtain ⟨-, -, hc, -⟩ :=
    (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _ hAp hBp).2 hne
  have hcomm : (A.subgroupOf Y).map π ≤ centralizer ((B.subgroupOf Y).map π : Set _) := by
    rw [← commutator_eq_bot_iff_le_centralizer, ← map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
    obtain ⟨-, -, hs, -, -⟩ := id hAp
    refine hc.trans (inf_le_left.trans ?_)
    rw [UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hs]
    exact inf_le_right
  set Ab := (A.subgroupOf Y).map π with hAbdef
  set Bb := (B.subgroupOf Y).map π with hBbdef
  have hc' : ∀ (a : ↥Ab) (b : ↥Bb), Commute (Ab.subtype a) (Bb.subtype b) := fun a b =>
    (mem_centralizer_iff.mp (hcomm a.2) b b.2).symm
  have hrange : (MonoidHom.noncommCoprod Ab.subtype Bb.subtype hc').range = Ab ⊔ Bb := by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  have hdvd : Nat.card ↥(Ab ⊔ Bb) ∣ Nat.card ↥Ab * Nat.card ↥Bb := by
    rw [← hrange, ← Nat.card_prod]
    exact Subgroup.card_range_dvd _
  have h1 : p ∣ Nat.card ↥Ab * Nat.card ↥Bb :=
    dvd_trans (dvd_trans hLimg (card_dvd_of_le hLle)) hdvd
  rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
  · left
    rw [← hcomp A hA hAp]
    exact h
  · right
    rw [← hcomp B hB hBp]
    exact h

theorem exists_location_in [Finite X] {Y : Subgroup X} {x : X} (hxY : x ∈ Y)
    (hx : orderOf x = 2) {T : Subgroup X} (hTY : T ≤ Y ⊓ centralizer ({x} : Set X))
    (hTpc : IsPComponent 2 (T.subgroupOf (Y ⊓ centralizer ({x} : Set X)))) :
    ∃ M : Subgroup X, M ≤ Y ∧ IsPComponent 2 (M.subgroupOf Y) ∧
      T ≤ M ⊔ M.map (MulAut.conj x).toMonoidHom := by
  classical
  have hx2 : x⁻¹ = x := by
    have h1 : x * x = 1 := by rw [← sq, ← hx, pow_orderOf_eq_one]
    exact inv_eq_of_mul_eq_one_right h1
  set x' : ↥Y := ⟨x, hxY⟩ with hx'def
  have hx' : orderOf x' = 2 := by rw [hx'def, Subgroup.orderOf_mk]; exact hx
  have hTYY : T ≤ Y := hTY.trans inf_le_left
  set T' := T.subgroupOf Y with hT'def
  have hcent : centralizer ({x'} : Set ↥Y) = (Y ⊓ centralizer ({x} : Set X)).subgroupOf Y := by
    rw [centralizer_mk_eq hxY, inf_comm]
  have hT'C : T' ≤ centralizer ({x'} : Set ↥Y) := by
    rw [hcent]
    intro y hy
    exact hTY hy
  have hT'pc : IsPComponent 2 (T'.subgroupOf (centralizer ({x'} : Set ↥Y))) := by
    rw [hcent, hT'def, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
      Nat.prime_two]
    exact hTpc
  have hTE := FooteLit.le_pLayer_of_isPComponent_centralizer_singleton hx' hT'C hT'pc
  obtain ⟨M₀, hM₀pc, hTM₀, -⟩ :=
    UnbalancedLayer.two_layer_fixed_component_orbit_location hx' hT'C hT'pc hTE
  set M := M₀.map Y.subtype with hMdef
  have hMY : M ≤ Y := map_subtype_le _
  have hMsub : M.subgroupOf Y = M₀ := by
    change (M₀.map Y.subtype).comap Y.subtype = M₀
    exact comap_map_eq_self_of_injective Y.subtype_injective M₀
  have hconj := map_conjugate_subtype hxY hx2 M₀
  rw [← hx'def] at hconj
  have hsup : (M₀ ⊔ conjugate M₀ x').map Y.subtype =
      M ⊔ M.map (MulAut.conj x).toMonoidHom := by
    rw [Subgroup.map_sup, hconj]
  refine ⟨M, hMY, by rw [hMsub]; exact hM₀pc, ?_⟩
  rw [← hsup]
  intro y hy
  exact ⟨⟨y, hTYY hy⟩, hTM₀ hy, rfl⟩

end CFSG.ComponentClassification.SolMax.L32
