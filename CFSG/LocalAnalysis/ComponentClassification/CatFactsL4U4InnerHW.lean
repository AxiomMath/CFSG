module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerCase
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OutU
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aConjFixHWA
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTypesHW

public section

namespace CFSG.ComponentClassification.CatFactsL4U4HW

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.CatFactsL4U4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Hyp

variable {H : Type} [Group H] [Finite H] (h : Hyp52W H)

theorem mem_fixedLayer_of_mem_D {z : H} (hzD : z ∈ h.D) (hzS : ∀ s ∈ h.S, s * z = z * s)
    (hz2 : orderOf z = 2) : z ∈ GSLit.fixedLayer h.J h.B := by
  rw [GSLit.fixedLayer_eq_closure h.isQuasisimple_J h.B_le_coreActionKernel h.isPGroup_B]
  refine subset_closure ⟨mem_inf.2 ⟨h.D_le_J hzD, ?_⟩, 1, by rw [hz2, pow_one]⟩
  rw [mem_centralizer_iff]
  intro b hb
  exact hzS b (h.B_le_S hb)

theorem fixedLayer_le_K (hKa : conjugate h.K h.a = h.K) : GSLit.fixedLayer h.J h.B ≤ h.K :=
  (B5aHW.fixedLayer_le_V h).trans (h.V_eq_K hKa).le

theorem fixedLayer_le_centralizer_a : GSLit.fixedLayer h.J h.B ≤ centralizer ({h.a} : Set H) :=
  (GSLit.fixedLayer_le_inf h.J h.B).trans (inf_le_left.trans h.J_le)

@[expose] noncomputable def imJB : Subgroup (OddBar h.K) :=
  ((GSLit.fixedLayer h.J h.B).subgroupOf h.K).map (QuotientGroup.mk' (pPrimeCore 2 h.K))

theorem imJB_commutator_eq (hKa : conjugate h.K h.a = h.K) : ⁅imJB h, imJB h⁆ = imJB h := by
  have hle := fixedLayer_le_K h hKa
  have h1 : ⁅(GSLit.fixedLayer h.J h.B).subgroupOf h.K,
      (GSLit.fixedLayer h.J h.B).subgroupOf h.K⁆ =
      (GSLit.fixedLayer h.J h.B).subgroupOf h.K := by
    apply map_injective h.K.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hle, fixedLayer_commutator_eq]
  rw [imJB, ← map_commutator, h1]

theorem a_mem_normalizer_K (hKa : conjugate h.K h.a = h.K) :
    h.a ∈ normalizer (h.K : Set H) :=
  mem_normalizer_of_conjugate_eq hKa

theorem oddBarConj_a_apply_of_mem_imJB (hKa : conjugate h.K h.a = h.K) {x : OddBar h.K}
    (hx : x ∈ imJB h) : oddBarConj h.K ⟨h.a, a_mem_normalizer_K h hKa⟩ x = x := by
  obtain ⟨j, hj, rfl⟩ := hx
  have hja : (j : H) * h.a = h.a * j :=
    mem_centralizer_singleton_iff.mp (fixedLayer_le_centralizer_a h (mem_subgroupOf.mp hj))
  rw [QuotientGroup.mk'_apply, oddBarConj_apply_mk]
  congr 1
  apply Subtype.ext
  show h.a * (j : H) * h.a⁻¹ = j
  rw [← hja, mul_inv_cancel_right]

theorem oddBarConj_a_ne_one (hKa : conjugate h.K h.a = h.K) :
    oddBarConj h.K ⟨h.a, a_mem_normalizer_K h hKa⟩ ≠ 1 := by
  intro h1
  have haK : h.a ∈ coreActionKernel h.K := mem_coreActionKernel_of_oddBarConj_eq_one h1
  have hle : ⁅h.K, zpowers h.a⁆ ≤ (pPrimeCore 2 h.K).map h.K.subtype := by
    rw [commutator_le]
    intro k hk g hg
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
    exact commutatorElement_mem_oddCoreIn hk (zpow_mem haK n)
  have hcomm := h.commutator_eq
  have hV : layerIn (normalizer (h.B : Set H)) = h.K := h.V_eq_K hKa
  rw [hV] at hcomm
  rw [hcomm] at hle
  have htop : pPrimeCore 2 h.K = ⊤ := by
    rw [eq_top_iff]
    intro k _
    obtain ⟨o, ho, hoe⟩ := mem_map.mp (hle k.2)
    rwa [show o = k from Subtype.ext hoe] at ho
  obtain ⟨-, hsimp, -⟩ := h.isQuasisimple_K
  have hsub : Subsingleton (OddBar h.K) := by
    rw [subsingleton_iff]
    intro x y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [QuotientGroup.eq, htop]
    exact mem_top _
  have : Nontrivial (OddBar h.K ⧸ center (OddBar h.K)) := IsSimpleGroup.toNontrivial
  obtain ⟨u, v, huv⟩ := exists_pair_ne (OddBar h.K ⧸ center (OddBar h.K))
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
  exact huv (by rw [Subsingleton.elim u v])

theorem exists_oddBarConj_a_eq_conj (hKa : conjugate h.K h.a = h.K)
    (hin : h.a ∈ h.K ⊔ coreActionKernel h.K) :
    ∃ l : OddBar h.K, oddBarConj h.K ⟨h.a, a_mem_normalizer_K h hKa⟩ = MulAut.conj l := by
  obtain ⟨k, hk, c, hc, hkc⟩ := exists_mul_of_mem_sup_coreActionKernel' hin
  have hkN : k ∈ normalizer (h.K : Set H) := le_normalizer hk
  have hcN : c ∈ normalizer (h.K : Set H) := (mem_coreActionKernel.mp hc).1
  refine ⟨QuotientGroup.mk ⟨k, hk⟩, ?_⟩
  have e1 : (⟨h.a, a_mem_normalizer_K h hKa⟩ : ↥(normalizer (h.K : Set H))) =
      ⟨k, hkN⟩ * ⟨c, hcN⟩ := Subtype.ext hkc.symm
  rw [e1, map_mul, oddBarConj_eq_one_of_mem_coreActionKernel' (g := ⟨c, hcN⟩) hc, mul_one,
    oddBarConj_mk_eq_conj h.K hk]

@[expose] noncomputable def jbToK (hKa : conjugate h.K h.a = h.K) :
    ↥(GSLit.fixedLayer h.J h.B) →* OddBar h.K :=
  (QuotientGroup.mk' (pPrimeCore 2 h.K)).comp (Subgroup.inclusion (fixedLayer_le_K h hKa))

theorem jbToK_apply (hKa : conjugate h.K h.a = h.K) (j : ↥(GSLit.fixedLayer h.J h.B)) :
    jbToK h hKa j = QuotientGroup.mk ⟨(j : H), fixedLayer_le_K h hKa j.2⟩ := rfl

theorem range_jbToK (hKa : conjugate h.K h.a = h.K) : (jbToK h hKa).range = imJB h := by
  apply le_antisymm
  · rintro _ ⟨j, rfl⟩
    exact ⟨⟨j, fixedLayer_le_K h hKa j.2⟩, mem_subgroupOf.mpr j.2, rfl⟩
  · rintro _ ⟨k, hk, rfl⟩
    exact ⟨⟨k, mem_subgroupOf.mp hk⟩, rfl⟩

theorem ker_jbToK_le (hKa : conjugate h.K h.a = h.K) :
    (jbToK h hKa).ker ≤ pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_pPrimeCore_of_normal
  set φ := jbToK h hKa
  let f : φ.ker →* pPrimeCore 2 h.K :=
    ((Subgroup.inclusion (fixedLayer_le_K h hKa)).comp φ.ker.subtype).codRestrict _ (by
      intro j
      have hj := j.2
      rw [MonoidHom.mem_ker, jbToK_apply, QuotientGroup.eq_one_iff] at hj
      exact hj)
  have hf : Function.Injective f := by
    intro x y hxy
    have := congrArg (fun z : pPrimeCore 2 h.K => ((z : h.K) : H)) hxy
    exact Subtype.ext (Subtype.ext this)
  exact Nat.Coprime.coprime_dvd_right (card_dvd_of_injective f hf) pPrimeCore_coprime_card

theorem exists_oddBar_JB_equiv :
    ∃ e : ↥(GSLit.fixedLayer h.J h.B) ⧸ pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B) ≃* OddBar h.J,
      ∀ (t : ↥(GSLit.fixedLayer h.J h.B)) (ht : (t : H) ∈ h.J),
        e t = ((⟨(t : H), ht⟩ : h.J) : OddBar h.J) := by
  have hle : GSLit.fixedLayer h.J h.B ≤ h.J := (GSLit.fixedLayer_le_inf h.J h.B).trans inf_le_left
  have hsup := (GSLit.fixedLayer_sup_pPrimeCore h.isQuasisimple_J h.B_le_coreActionKernel
    h.isPGroup_B).1
  exact (restriction_quotient_mulEquiv hle hsup).2

theorem card_oddBar_J_dvd (hKa : conjugate h.K h.a = h.K) :
    Nat.card (OddBar h.J) ∣ Nat.card (imJB h) := by
  obtain ⟨e, -⟩ := exists_oddBar_JB_equiv h
  rw [← Nat.card_congr e.toEquiv, ← range_jbToK h hKa,
    ← Nat.card_congr (QuotientGroup.quotientKerEquivRange (jbToK h hKa)).toEquiv]
  refine card_dvd_of_surjective (QuotientGroup.map _ _ (MonoidHom.id _) (ker_jbToK_le h hKa))
    fun y => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨QuotientGroup.mk x, rfl⟩

theorem eq_one_of_central_sq (hKa : conjugate h.K h.a = h.K)
    (hZJ : center (OddBar h.J) = ⊥) {x : OddBar h.K} (hx : x ∈ imJB h)
    (hc : ∀ y ∈ imJB h, x * y = y * x) (h2 : x * x = 1) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← range_jbToK h hKa] at hx hc
  obtain ⟨j, rfl⟩ := hx
  obtain ⟨e, he⟩ := exists_oddBar_JB_equiv h
  set φ := jbToK h hKa with hφ
  have hcen : (QuotientGroup.mk j : ↥(GSLit.fixedLayer h.J h.B) ⧸
      pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B)) ∈ center _ := by
    rw [mem_center_iff]
    intro w
    obtain ⟨j', rfl⟩ := QuotientGroup.mk_surjective w
    have h1 : φ ((j' * j)⁻¹ * (j * j')) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hc (φ j') ⟨j', rfl⟩, inv_mul_cancel]
    have h3 := ker_jbToK_le h hKa (MonoidHom.mem_ker.mpr h1)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    exact h3
  have hcen' : e (QuotientGroup.mk j) ∈ center (OddBar h.J) := by
    rw [mem_center_iff]
    intro w
    obtain ⟨w', rfl⟩ := e.surjective w
    rw [← map_mul, ← map_mul, (mem_center_iff.mp hcen) w']
  rw [hZJ, mem_bot, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at hcen'
  have hodd : Odd (orderOf j) := by
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B))) :=
      pPrimeCore_coprime_card
    have h1 : orderOf j = orderOf (⟨j, hcen'⟩ : pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B)) :=
      Subgroup.orderOf_coe (⟨j, hcen'⟩ : pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B))
    rw [h1]
    refine Odd.of_dvd_nat ?_ (orderOf_dvd_natCard _)
    rcases Nat.even_or_odd (Nat.card (pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B))) with he | ho
    · exact absurd (Nat.Coprime.coprime_dvd_right (even_iff_two_dvd.1 he) hcop) (by norm_num)
    · exact ho
  have hdvd : orderOf (φ j) ∣ orderOf j := orderOf_map_dvd φ j
  have h2' : orderOf (φ j) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  have hodd' : Odd (orderOf (φ j)) := Odd.of_dvd_nat hodd hdvd
  rcases (Nat.dvd_prime Nat.prime_two).1 h2' with h1 | h1
  · exact orderOf_eq_one_iff.1 h1
  · rw [h1] at hodd'
    exact absurd hodd' (by decide)

theorem inner_data {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hJ : Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f)) (hKa : conjugate h.K h.a = h.K)
    (hin : h.a ∈ h.K ⊔ coreActionKernel h.K) :
    ∃ ℓ : OddBar h.K, oddBarConj h.K ⟨h.a, a_mem_normalizer_K h hKa⟩ = MulAut.conj ℓ ∧
      ℓ ∉ center (OddBar h.K) ∧ ℓ ^ 2 ∈ center (OddBar h.K) ∧
      imJB h ≤ centralizer {ℓ} ∧ ⁅imJB h, imJB h⁆ = imJB h ∧
      (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) ≤ 2 * Nat.card (imJB h) ∧
      (∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ s ∣ (p ^ f) ^ 2 + 1 ∧ s ∣ Nat.card (OddBar h.J) ∧
        s ∣ Nat.card (imJB h)) ∧
      ∀ x ∈ imJB h, (∀ w ∈ imJB h, x * w = w * x) → x * x = 1 → x = 1 := by
  obtain ⟨ℓ, hℓ⟩ := exists_oddBarConj_a_eq_conj h hKa hin
  have hconj1 : ∀ u : OddBar h.K, MulAut.conj u = 1 → u ∈ center (OddBar h.K) := by
    intro u hu
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut (OddBar h.K) => φ g) hu
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  have hℓZ : ℓ ∉ center (OddBar h.K) := by
    intro hc
    apply oddBarConj_a_ne_one h hKa
    rw [hℓ]
    ext g
    rw [MulAut.conj_apply, MulAut.one_apply, ← (Subgroup.mem_center_iff.mp hc g),
      mul_inv_cancel_right]
  have ha2 : (⟨h.a, a_mem_normalizer_K h hKa⟩ : normalizer (h.K : Set H)) ^ 2 = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← h.orderOf_a, pow_orderOf_eq_one]
    rfl
  have hℓ2 : ℓ ^ 2 ∈ center (OddBar h.K) := by
    apply hconj1
    rw [map_pow, ← hℓ, ← map_pow, ha2, map_one]
  have hJC : imJB h ≤ centralizer {ℓ} := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := oddBarConj_a_apply_of_mem_imJB h hKa hx
    rw [hℓ, MulAut.conj_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hQ : Odd (p ^ (2 * f)) := (hp.odd_of_ne_two hp2).pow
  have hpf : p ^ (2 * f) = (p ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
  have h2J : 2 * Nat.card (OddBar h.J) = (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) := by
    rw [card_of_lieModel_psl_two hp2 hJ, two_mul_ordA_one hQ, hpf, ← pow_mul (p ^ f) 2 2]
  have hdvd := card_oddBar_J_dvd h hKa
  have hle : Nat.card (OddBar h.J) ≤ Nat.card (imJB h) := Nat.le_of_dvd Nat.card_pos hdvd
  refine ⟨ℓ, hℓ, hℓZ, hℓ2, hJC, imJB_commutator_eq h hKa, by omega, ?_, ?_⟩
  · have h3 : 3 ≤ p ^ f := by
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hf1 : 1 ≤ f := by
        by_contra hf0
        have hf0' : f = 0 := by omega
        have := card_of_lieModel_psl_two hp2 hJ
        obtain ⟨⟨-, hf', -⟩, -⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hJ
        omega
      calc 3 ≤ p := hp3
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf1
    obtain ⟨s, hs, hs2, hsq⟩ := exists_odd_prime_dvd_sq_add_one hq h3
    suffices hsJ : s ∣ Nat.card (OddBar h.J) from ⟨s, hs, hs2, hsq, hsJ, dvd_trans hsJ hdvd⟩
    have h4 : s ∣ 2 * Nat.card (OddBar h.J) := by
      rw [h2J]
      apply Dvd.dvd.mul_left
      obtain ⟨Q, hQ1⟩ : ∃ Q, (p ^ f) ^ 2 = Q + 1 :=
        ⟨(p ^ f) ^ 2 - 1, by have : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
      have h5 : (p ^ f) ^ 4 - 1 = ((p ^ f) ^ 2 + 1) * ((p ^ f) ^ 2 - 1) := by
        rw [show (p ^ f) ^ 4 = ((p ^ f) ^ 2) ^ 2 by ring, hQ1,
          show (Q + 1) ^ 2 = (Q ^ 2 + 2 * Q) + 1 by ring, Nat.add_sub_cancel, Nat.add_sub_cancel]
        ring
      rw [h5]
      exact Dvd.dvd.mul_right hsq _
    exact (Nat.Coprime.dvd_of_dvd_mul_left
      ((Nat.coprime_primes hs Nat.prime_two).2 hs2) h4)
  · have : IsSimpleGroup (OddBar h.J) := isSimpleGroup_of_lieModel_psl_two hJ
    have hZJ : center (OddBar h.J) = ⊥ :=
      center_eq_bot_of_isSimpleGroup_of_isQuasisimple h.isQuasisimple_J
    intro x hx hc h2
    exact eq_one_of_central_sq h hKa hZJ hx hc h2

theorem inner_structure (hrow : h.Row516) (hin : h.a ∈ h.K ⊔ coreActionKernel h.K) :
    center (OddBar h.K) = ⊥ ∧ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f) ∧
      ((p ^ f % 4 = 3 ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F),
          Fintype.card F = p ^ f ∧ Nonempty (OddBar h.K ≃* StatedProj (StatedSL 4 F))) ∨
        (p ^ f % 4 = 1 ∧ ∃ (K' : Type) (_ : Field K'), UnitaryFieldData p f K' ∧
          Nonempty (OddBar h.K ≃* StatedProj (StatedSU 4 (p ^ f) K')))) := by
  classical
  obtain ⟨p, f, hp, hp2, hf, hJ, hKa, hK⟩ := hrow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect (OddBar h.K) := h.isQuasisimple_K.1
  have hZ2 : IsPGroup 2 (center (OddBar h.K)) :=
    isPGroup_two_center_of_pPrimeCore_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  obtain ⟨ℓ, -, hℓZ, hℓ2, hJC, hJp, hJc, ⟨s, hs, hs2, hsq, -, hsJ⟩, hnc⟩ :=
    inner_data h hp hp2 hJ hKa hin
  have := Fact.mk hs
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := imJB h) s hsJ
  set y : OddBar h.K := (y' : OddBar h.K) with hydef
  have hy : orderOf y = s := by rw [hydef, Subgroup.orderOf_coe, hy']
  have hyℓ : y * ℓ = ℓ * y := Subgroup.mem_centralizer_singleton_iff.mp (hJC y'.2)
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hiso : ∀ {M : Type} [Group M], center (OddBar h.K) = ⊥ → (ZStarBar h.K ≃* M) →
      Nonempty (OddBar h.K ≃* M) := fun hZ eM =>
    ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans
      (eZ.trans eM)⟩
  rcases hK with hL | hU | ⟨e', rfl, hO8⟩
  · obtain ⟨-, F, _, _, hF, ⟨eL⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hL
    let : Fintype F := Fintype.ofFinite F
    have hFq : Fintype.card F = p ^ f := by rw [Fintype.card_eq_nat_card, hF]
    have hqF : Odd (Fintype.card F) := hFq ▸ hq
    have hZ := center_eq_bot_of_inner_L4 hZ2 hqF (eZ.trans eL) hℓZ hℓ2 hJC hJp
      (by rw [hFq]; exact hJc) hs hs2 (by rw [hFq]; exact hsq) hsJ hnc
    refine ⟨hZ, p, f, hp, hp2, hf, hJ, Or.inl ⟨?_, F, inferInstance, inferInstance, hFq,
      hiso hZ eL⟩⟩
    have := card_mod_four_of_inner_L4 hZ2 hqF (eZ.trans eL) hℓZ hℓ2 hs hs2
      (by rw [hFq]; exact hsq) hy hyℓ
    rwa [hFq] at this
  · obtain ⟨-, K', _, _, hK', ⟨eU⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hU
    have hUF : UnitaryFieldData p f K' := ⟨hp, hf, by rw [hK', ← pow_mul, mul_comm]⟩
    have hZ := center_eq_bot_of_inner_U4 hUF hZ2 hp2 (eZ.trans eU) hℓZ hℓ2 hJC hJp hJc hs hs2
      hsq hsJ hnc
    refine ⟨hZ, p, f, hp, hp2, hf, hJ, Or.inr ⟨?_, K', inferInstance, hUF, hiso hZ eU⟩⟩
    exact card_mod_four_of_inner_U4 hUF hZ2 hp2 (eZ.trans eU) hℓZ hℓ2 hs hs2 hsq hy hyℓ
  · exfalso
    obtain ⟨-, K', _, _, hK', b, c, hbc, ⟨eO⟩⟩ :=
      statedClassicalModel_of_lieModel_ne_zero (by norm_num) hO8
    let : Fintype K' := Fintype.ofFinite K'
    have hKq : Fintype.card K' = p ^ e' := by rw [Fintype.card_eq_nat_card, hK']
    have h4 : (p ^ e') ^ 4 = (p ^ (2 * e')) ^ 2 := by rw [← pow_mul, ← pow_mul]; ring_nf
    set E := eZ.trans eO with hE
    apply false_of_omegaMinus_eight (K := K') (hKq ▸ (hp.odd_of_ne_two hp2).pow) hbc hs hs2
      (by rw [hKq, h4]; exact hsq) (E (QuotientGroup.mk ℓ)) (E (QuotientGroup.mk y))
    · rw [Ne, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
      exact hℓZ
    · rw [← map_pow, ← QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff _).2 hℓ2, map_one]
    · rw [← map_pow, ← QuotientGroup.mk_pow, ← hy, pow_orderOf_eq_one, QuotientGroup.mk_one,
        map_one]
    · rw [Ne, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
      exact not_mem_of_isPGroup_two hZ2 hs hs2 hy
    · rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hyℓ]

end Hyp

theorem cfRow516InnerCenterHW : CFRow516InnerCenterHW :=
  fun _ _ _ h hrow hin => (inner_structure h hrow hin).1

theorem cfRow516InnerOutHW : CFRow516InnerOutHW := by
  intro H _ _ h hrow hin u v
  obtain ⟨-, p, f, hp, hp2, hf, -, hL | hU⟩ := inner_structure h hrow hin
  · obtain ⟨hq, F, _, _, hF, ⟨e⟩⟩ := hL
    set e' : OddBar h.K ≃* LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 4 F :=
      e.trans ((projectiveSpecialLinearGroupEquivStatedProj 4 F).symm.trans
        (QuotientGroup.quotientMulEquivOfEq
          (LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 4 F).symm))
    exact commutator_mem_range_conj_of_mulEquiv e'
      (fun u v => LinearOut.out_comm_projectiveSL_four (by rw [hF]; exact hq) u v) u v
  · obtain ⟨hq, K', _, hUF, ⟨e⟩⟩ := hU
    exact commutator_mem_range_conj_of_mulEquiv e
      (fun u v => UnitaryOut.out_comm_statedSU_four hUF hp2 hq u v) u v

end CFSG.ComponentClassification.CatFactsL4U4HW
