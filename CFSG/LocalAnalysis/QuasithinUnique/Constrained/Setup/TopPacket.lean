module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.TopDefs

public section

namespace CFSG.QuasithinUnique.Setup.Top

open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Family
  CFSG.QuasithinUnique.Setup.Lift
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem exists_elemAbelian_of_independent {p : ℕ} {H : Subgroup G} {r : ℕ}
    (K : Fin r → Subgroup G) (hKH : ∀ i, K i ≤ H) (hcomm : ∀ i j, i ≠ j → ⁅K i, K j⁆ = ⊥)
    (hind : ∀ i, K i ⊓ (⨆ j, ⨆ (_ : j ≠ i), K j) = ⊥) (hord : ∀ i, ∃ x ∈ K i, orderOf x = p) :
    ∃ (A : Type) (_ : Group A) (f : A →* G), (∀ a b : A, a * b = b * a) ∧ (∀ a : A, a ^ p = 1) ∧
      Nat.card A = p ^ r ∧ Function.Injective f ∧ f.range ≤ H := by
  choose x hxK hxo using hord
  let Z : Fin r → Subgroup G := fun i => Subgroup.zpowers (x i)
  have hZK : ∀ i, Z i ≤ K i := fun i => (Subgroup.zpowers_le).2 (hxK i)
  have hcommK : ∀ i j, i ≠ j → ∀ a ∈ K i, ∀ b ∈ K j, Commute a b := by
    intro i j hij a ha b hb
    have : ⁅a, b⁆ ∈ (⁅K i, K j⁆ : Subgroup G) := Subgroup.commutator_mem_commutator ha hb
    rw [hcomm i j hij, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_commute.mp this
  have hcommZ : Pairwise fun i j => ∀ a b : G, a ∈ Z i → b ∈ Z j → Commute a b :=
    fun i j hij a b ha hb => hcommK i j hij a (hZK i ha) b (hZK j hb)
  have hindK : iSupIndep K := fun i => disjoint_iff.mpr (hind i)
  have hindZ : iSupIndep Z := hindK.mono hZK
  let f := Subgroup.noncommPiCoprod hcommZ
  refine ⟨∀ i, ↥(Z i), inferInstance, f, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    funext i
    apply Subtype.ext
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (a i).2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (b i).2
    simp only [Pi.mul_apply, Subgroup.coe_mul]
    rw [← hm, ← hn]
    exact (Commute.zpow_zpow_self (x i) m n).eq
  · intro a
    funext i
    apply Subtype.ext
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (a i).2
    simp only [Pi.pow_apply, Subgroup.coe_pow, Pi.one_apply, Subgroup.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hxo i,
      pow_orderOf_eq_one, one_zpow]
  · rw [Nat.card_pi]
    simp only [Z, Nat.card_zpowers, hxo, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · exact Subgroup.injective_noncommPiCoprod_of_iSupIndep hindZ
  · rw [Subgroup.noncommPiCoprod_range]
    exact iSup_le fun i => (hZK i).trans (hKH i)

theorem le_pRank_of_independent [Finite G] {p : ℕ} (hp : p.Prime) {H : Subgroup G} {r : ℕ}
    (K : Fin r → Subgroup G) (hKH : ∀ i, K i ≤ H) (hcomm : ∀ i j, i ≠ j → ⁅K i, K j⁆ = ⊥)
    (hind : ∀ i, K i ⊓ (⨆ j, ⨆ (_ : j ≠ i), K j) = ⊥) (hord : ∀ i, ∃ x ∈ K i, orderOf x = p) :
    r ≤ CFSG.Open.pRank p H := by
  obtain ⟨A, _, f, hc, hpow, hA, hf, hH⟩ := exists_elemAbelian_of_independent K hKH hcomm hind hord
  exact CFSG.SectionRank.le_pRank_of_injective hp.one_lt hc hpow hA f hf hH

theorem card_sq_le_card_sl2 (F : Type) [Field F] [Fintype F] :
    Fintype.card F ^ 2 ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
  classical
  let g : F × F → Matrix.SpecialLinearGroup (Fin 2) F := fun ab =>
    ⟨!![1 + ab.1 * ab.2, ab.1; ab.2, 1], by
      rw [Matrix.det_fin_two_of]; ring⟩
  have hg : Function.Injective g := by
    intro x y h
    have h1 := congrArg
      (fun M : Matrix.SpecialLinearGroup (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 0 1) h
    have h2 := congrArg
      (fun M : Matrix.SpecialLinearGroup (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 1 0) h
    simp [g] at h1 h2
    exact Prod.ext h1 h2
  have := Nat.card_le_card_of_injective g hg
  rw [Nat.card_prod, Nat.card_eq_fintype_card] at this
  simpa [sq] using this

theorem isAltType_three_of_alt4 {P K : Subgroup G} (hK : IsChi0Block P K)
    (e : Nonempty (↥K ≃* alternatingGroup (Fin 4))) : IsAltType K 3 := by
  obtain ⟨e⟩ := e
  have hcard : Nat.card ↥K = 12 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hfin : Finite ↥K := Nat.finite_of_card_ne_zero (by omega)
  rcases hK.2 with ⟨n, hn, F, hF, hFin, hc, α, hα, -⟩ | h3 | ⟨α, hα, -⟩
  · exfalso
    have h1 := Nat.card_le_card_of_surjective α hα
    have h2 := card_sq_le_card_sl2 F
    have h3 : 4 ≤ Fintype.card F := by
      rw [hc]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h4 : 16 ≤ Fintype.card F ^ 2 := by nlinarith
    omega
  · exact h3
  · exfalso
    have h1 := Nat.card_le_card_of_surjective α hα
    have h2 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    omega

theorem le_normalizer_of_commutator_eq_bot {A B : Subgroup G} (h : ⁅A, B⁆ = ⊥) :
    A ≤ Subgroup.normalizer (B : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  have hc : ∀ b ∈ B, Commute a b := by
    intro b hb
    have : ⁅a, b⁆ ∈ (⁅A, B⁆ : Subgroup G) := Subgroup.commutator_mem_commutator ha hb
    rw [h, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_commute.mp this
  constructor
  · intro hb
    rw [show a * b * a⁻¹ = b from by rw [(hc b hb).eq]; group]
    exact hb
  · intro hb
    have hcomm := hc _ hb
    have h2 : a⁻¹ * (a * b * a⁻¹) * a = a * b * a⁻¹ := by
      rw [mul_assoc, ← hcomm.eq, ← mul_assoc, inv_mul_cancel, one_mul]
    have hb2 : b = a * b * a⁻¹ := by
      calc b = a⁻¹ * (a * b * a⁻¹) * a := by group
        _ = a * b * a⁻¹ := h2
    rw [hb2]
    exact hb

theorem coe_iSup_eq_prod_of_le_two {r : ℕ} (hr : 1 ≤ r) (hr2 : r ≤ 2) (K : Fin r → Subgroup G)
    (h : ∀ i j, i ≠ j → ⁅K i, K j⁆ = ⊥) :
    ((⨆ i, K i : Subgroup G) : Set G) = (List.ofFn fun i => (K i : Set G)).prod := by
  obtain rfl | rfl : r = 1 ∨ r = 2 := by omega
  · simp [List.ofFn_succ]
  · have h01 := h 0 1 (by decide)
    have hsup : (⨆ i : Fin 2, K i) = K 0 ⊔ K 1 := by
      apply le_antisymm
      · exact iSup_le fun i => by fin_cases i <;> simp
      · exact sup_le (le_iSup K 0) (le_iSup K 1)
    rw [hsup, Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (le_normalizer_of_commutator_eq_bot h01)]
    simp [List.ofFn_succ]

theorem blockPacket_of_prePacket [Finite G] {S P : Subgroup G} (h : PushUpObstruction S P)
    {r : ℕ} {L : Fin r → Subgroup G} (hpre : PrePacket S P r L) (hle : r ≤ 2) :
    BlockPacket S P r L := by
  have hr : 1 ≤ r := by
    obtain ⟨k, hk⟩ := hpre.pow_two
    rw [hk]
    exact Nat.one_le_two_pow
  obtain ⟨hSI, hIP, -⟩ := uniqueMaxOver_spec h.minParabolic
  refine ⟨hpre, hr, hle, fun i hi => ?_, ?_⟩
  · have : P ≤ uniqueMaxOver S P := (hpre.gen i).le.trans (sup_le hi hSI)
    exact absurd (lt_of_le_of_lt this hIP) (lt_irrefl _)
  · have hN : oddOrderSubgroup P ≤ P := oddOrderSubgroup_le P
    have hI : uniqueMaxOver S P ≤ Subgroup.normalizer (oddOrderSubgroup P : Set G) :=
      hIP.le.trans (Subgroup.le_normalizer.trans
        (normalizer_le_normalizer_oddOrderSubgroup P))
    have hPeq : P = uniqueMaxOver S P ⊔ oddOrderSubgroup P := by
      apply le_antisymm
      · exact (hpre.gen ⟨0, by omega⟩).le.trans
          (sup_le ((hpre.le_odd ⟨0, by omega⟩).trans le_sup_right) (hSI.trans le_sup_left))
      · exact sup_le hIP.le hN
    calc (P : Set G) = ((uniqueMaxOver S P ⊔ oddOrderSubgroup P : Subgroup G) : Set G) :=
          congrArg SetLike.coe hPeq
      _ = (uniqueMaxOver S P : Set G) * (oddOrderSubgroup P : Set G) :=
          Subgroup.coe_mul_of_left_le_normalizer_right _ _ hI
      _ = (uniqueMaxOver S P : Set G) * (List.ofFn fun i => (L i : Set G)).prod := by
          rw [hpre.odd_eq, coe_iSup_eq_prod_of_le_two hr hle L hpre.commute]

theorem minParabolicBlocks_of_blockPacket
    (hpacket : ∀ (G : Type) [Group G] [Finite G] (S P : Subgroup G), PushUpObstruction S P →
      ∃ (r : ℕ) (L : Fin r → Subgroup G), BlockPacket S P r L) : MinParabolicBlocks := by
  intro G _ _ S P h
  obtain ⟨r, L, hL⟩ := hpacket G S P h
  have hr1 := hL.one_le
  have hr2 := hL.le_two
  have hSP : S ≤ P := h.sylow.1
  have hL0P : ∀ i, L i ≤ P := fun i => (hL.le_odd i).trans (oddOrderSubgroup_le P)
  have hconjP : ∀ (s : S) (i : Fin r), (L i).map (MulAut.conj (s : G)).toMonoidHom ≤ P := by
    intro s i
    rintro _ ⟨x, hx, rfl⟩
    exact P.mul_mem (P.mul_mem (hSP s.2) (hL0P i hx)) (P.inv_mem (hSP s.2))
  have hself : ∀ i, L i ≤ conjJoin S (L i) := fun i =>
    le_iSup_of_le (⟨1, S.one_mem⟩ : S) (fun x hx => ⟨x, hx, by simp⟩)
  have hjoinP : ∀ i, conjJoin S (L i) ≤ P := fun i => iSup_le fun s => hconjP s i
  have hPeq : ∀ i, P = conjJoin S (L i) ⊔ S := fun i =>
    le_antisymm ((hL.gen i).le.trans (sup_le_sup_right (hself i) S)) (sup_le (hjoinP i) hSP)
  obtain rfl | rfl : r = 1 ∨ r = 2 := by omega
  · refine ⟨L 0, hL.chi0 0, hL.perfect 0, hPeq 0, Or.inl ?_⟩
    refine le_antisymm (iSup_le fun s => ?_) (hself 0)
    obtain ⟨j, hj⟩ := hL.permuted s s.2 0
    obtain rfl : j = 0 := Subsingleton.elim j 0
    exact hj.le
  · obtain ⟨t, ht, hts⟩ := hL.transitive 0 1
    refine ⟨L 0, hL.chi0 0, hL.perfect 0, hPeq 0, Or.inr ⟨t, ht, ?_, ?_, ?_⟩⟩
    · rw [hts]
      exact fun h01 => absurd (hL.injective h01) (by decide)
    · rw [hts]
      apply le_antisymm
      · refine iSup_le fun s => ?_
        obtain ⟨j, hj⟩ := hL.permuted s s.2 0
        rw [hj]
        fin_cases j
        · exact le_sup_left
        · exact le_sup_right
      · refine sup_le (hself 0) ?_
        rw [← hts]
        exact le_iSup_of_le (⟨t, ht⟩ : S) le_rfl
    · rw [hts]
      exact hL.commute 0 1 (by decide)

end CFSG.QuasithinUnique.Setup.Top
