module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516Tools
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma515
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma514
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Hyp59

variable {H : Type} [Group H] [Finite H] (h : Hyp59 H)

theorem false_of_row516_outer (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hB7 : EmbedsTQuotStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hST : SuzukiTausskyInput) (hFus : CFProp23Row516)
    (hStab : CFAutL2Stab) (hCent : CF516Cent)
    (hT : Nat.card (↥h.T ⧸ h.B.subgroupOf h.T) = 2) (hrow : h.Row516)
    (hout : h.a ∉ h.K ⊔ coreActionKernel h.K) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p, f, hp, hp2, hf, hJlie, hKa, hKlie⟩ := id hrow
  have hZJ := h.toHyp52.center_eq_bot hB1 hB6 hCF23 hCF24
  have hDP := h.toHyp52.D_inf_P_eq_bot hZJ
  have hCaN := h.toHyp52.centralizer_le_normalizer_J hB1 hB6 hCF23 hCF24 hCFc
  obtain ⟨b, hBb, hb, -, hTab, -⟩ := h.index_two_structure hB7 hT
  have hbB : b ∈ h.B := hBb ▸ mem_zpowers b
  have hbP : b ∈ h.P := h.toHyp52.B_le_P hbB
  have hB2 : Nat.card h.B = 2 := by rw [hBb, Nat.card_zpowers, hb]
  have hb2 : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
  have ha2 : h.a * h.a = 1 := by rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
  have hxb := h.conj_x_b hBb hb hTab
  have hCN := h.centralizer_b_le hBb hb hKa
  have hKB : ∀ {k : H}, k ∈ h.K → k * b = b * k := fun hk =>
    (mem_centralizer_iff.mp ((h.toHyp52.K_le_layer_W.trans h.toHyp52.V_le_centralizer_B) hk) b
      hbB).symm
  obtain ⟨z, hzD, hzS, hz2⟩ := h.toHyp52.exists_involution_D_center
  have hzJ : z ∈ h.J := h.toHyp52.D_le_J hzD
  have hza : z * h.a = h.a * z := h.toHyp52.comm_a (h.toHyp52.D_le_S hzD)
  obtain ⟨g, hgW, y, hyBZ, hgy⟩ := hFus H h.toHyp52 hrow hout z hzD hzS hz2
  have hgb : g * b = b * g := by
    have hgW' : g ∈ normalizer ((zpowers b : Subgroup H) : Set H) := hBb ▸ hgW
    exact comm_of_mem_normalizer_zpowers hb hgW'
  obtain ⟨hyB, hyZ⟩ := mem_inf.mp hyBZ
  have hy1 : y ≠ 1 := by
    intro hy1
    rw [hy1, mul_one] at hgy
    have hmem : g⁻¹ * h.a * g ∈ h.J ⊔ zpowers h.a := by
      rw [hgy]
      exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left hzJ)
    have hnot : g⁻¹ * h.a * g ∉ zpowers h.a := by
      rw [hgy]
      intro hm
      have hz : z ∈ zpowers h.a := by
        have := mul_mem (inv_mem (mem_zpowers h.a)) hm
        rwa [inv_mul_cancel_left] at this
      have hzP : z ∈ h.D ⊓ h.P := mem_inf.mpr ⟨hzD, zpowers_le.mpr h.toHyp52.a_mem_P hz⟩
      rw [hDP, mem_bot] at hzP
      rw [hzP, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
    have hPP := h.toHyp52.inf_conjugate_P_eq_bot hB1 hB6 hCF23 hCF24 hCFc cfSmallInv hmem hnot
    have hbg : b ∈ conjugate h.P g := by
      rw [mem_conjugate_iff, hgb, mul_inv_cancel_right]
      exact hbP
    have := hPP ▸ mem_inf.mpr ⟨hbP, hbg⟩
    have hb1 : b = 1 := mem_bot.mp this
    rw [hb1, orderOf_one] at hb
    exact absurd hb (by norm_num)
  have hyb : y = b := eq_of_mem_zpowers_of_orderOf_eq_two hb (hBb ▸ hyB) hy1
  rw [hyb] at hgy hyZ
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥h.K) with hπ
  obtain ⟨bK, hbKZ, hbKe⟩ := mem_map.mp hyZ
  have hbKe' : (bK : H) = b := hbKe
  have hbKc : π bK ∈ center (OddBar h.K) := by
    have h1 : bK ∈ (center (↥h.K ⧸ Open.fusionOddCore ↥h.K)).comap
        (QuotientGroup.mk' (Open.fusionOddCore ↥h.K)) := hbKZ
    rw [comap_center_congr (fusionOddCore_eq_pPrimeCore ↥h.K)] at h1
    exact h1
  have hbK1 : π bK ≠ 1 := by
    intro he
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at he
    have hdvd : orderOf bK ∣ Nat.card (pPrimeCore 2 ↥h.K) := by
      have := orderOf_dvd_natCard (⟨bK, he⟩ : pPrimeCore 2 ↥h.K)
      rwa [Subgroup.orderOf_mk] at this
    have hob : orderOf bK = 2 := by rw [← Subgroup.orderOf_coe, hbKe', hb]
    rw [hob] at hdvd
    exact absurd (Nat.Coprime.coprime_dvd_right hdvd (CFSG.pPrimeCore_coprime_card (p := 2)))
      (by norm_num)
  have hZK : center (OddBar h.K) ≠ ⊥ := fun he => hbK1 (by
    rw [he] at hbKc
    exact mem_bot.mp hbKc)
  have hZ2 := h.card_center_oddBar_K hB6 hKa hB2 hZK
  set c := h.x * g with hc
  have hcb : c⁻¹ * b * c = h.a * z := by
    have hgb' : g⁻¹ * b * g = b := by rw [mul_assoc, ← hgb, ← mul_assoc, inv_mul_cancel, one_mul]
    calc c⁻¹ * b * c = g⁻¹ * (h.x⁻¹ * b * h.x) * g := by rw [hc]; group
      _ = (g⁻¹ * h.a * g) * (g⁻¹ * b * g) := by rw [hxb]; group
      _ = h.a * z := by rw [hgy, hgb', mul_assoc (h.a * z), hb2, mul_one]
  have hconj : ∀ {u v : H}, u * v = v * u →
      (c⁻¹ * u * c) * (c⁻¹ * v * c) = (c⁻¹ * v * c) * (c⁻¹ * u * c) := fun {u v} huv => by
    calc (c⁻¹ * u * c) * (c⁻¹ * v * c) = c⁻¹ * (u * v) * c := by group
      _ = c⁻¹ * (v * u) * c := by rw [huv]
      _ = (c⁻¹ * v * c) * (c⁻¹ * u * c) := by group
  set a' := c * h.a * c⁻¹ with ha'
  have hca' : c⁻¹ * a' * c = h.a := by rw [ha']; group
  have ha'b : a' * b = b * a' := by
    have h1 : h.a * (h.a * z) = (h.a * z) * h.a := by rw [mul_assoc h.a z h.a, hza]
    calc a' * b = c * ((c⁻¹ * a' * c) * (c⁻¹ * b * c)) * c⁻¹ := by group
      _ = c * (h.a * (h.a * z)) * c⁻¹ := by rw [hca', hcb]
      _ = c * ((h.a * z) * h.a) * c⁻¹ := by rw [h1]
      _ = c * ((c⁻¹ * b * c) * (c⁻¹ * a' * c)) * c⁻¹ := by rw [hca', hcb]
      _ = b * a' := by group
  have ha'N : a' ∈ normalizer (h.K : Set H) := hCN (mem_centralizer_singleton_iff.mpr ha'b)
  set t : ↥(normalizer (h.K : Set H)) := ⟨a', ha'N⟩ with ht
  have ht2 : (t : H) * t = 1 := by
    show c * h.a * c⁻¹ * (c * h.a * c⁻¹) = 1
    calc c * h.a * c⁻¹ * (c * h.a * c⁻¹) = c * (h.a * h.a) * c⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  set α := oddBarConj h.K t with hα
  have hα2 : α ^ 2 = 1 := by
    rw [hα, ← map_pow, pow_two, show t * t = 1 from Subtype.ext ht2, map_one]
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  have hLie : Blueprint.LieModel ((OddBar h.K) ⧸ center (OddBar h.K)) .PSL 4 p f ∨
      Blueprint.LieModel ((OddBar h.K) ⧸ center (OddBar h.K)) .PSU 4 p f ∨
      ∃ e : ℕ, f = 2 * e ∧
        Blueprint.LieModel ((OddBar h.K) ⧸ center (OddBar h.K)) .POmegaMinus 4 p e := by
    rcases hKlie with hL | hL | ⟨e, he, hL⟩
    · exact Or.inl (lieModel_of_mulEquiv_ne_zero eZ.symm (by norm_num) hL)
    · exact Or.inr (Or.inl (lieModel_of_mulEquiv_ne_zero eZ.symm (by norm_num) hL))
    · exact Or.inr (Or.inr ⟨e, he, lieModel_of_mulEquiv_ne_zero eZ.symm (by norm_num) hL⟩)
  obtain ⟨N, hNfix, hNtype, hNalt⟩ :=
    hCent (OddBar h.K) h.toHyp52.isQuasisimple_K hZ2 p f hp hp2 hf hLie α hα2
  set CK : Subgroup ↥h.K := (centralizer ({a'} : Set H)).subgroupOf h.K with hCK
  have hfixlift : ∀ w : OddBar h.K, α w = w → ∃ k ∈ CK, π k = w := by
    intro w hw
    obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨y', hy', hyt⟩ := exists_fixed_lift ht2 hw
    exact ⟨y', mem_subgroupOf.mpr (mem_centralizer_singleton_iff.mpr hyt.symm), hy'⟩
  have hτa : ∀ k ∈ CK, (c⁻¹ * (k : H) * c) * h.a = h.a * (c⁻¹ * (k : H) * c) := by
    intro k hk
    have h1 : (k : H) * a' = a' * k := mem_centralizer_singleton_iff.mp (mem_subgroupOf.mp hk)
    have := hconj h1
    rwa [hca'] at this
  have hτz : ∀ k ∈ CK, (c⁻¹ * (k : H) * c) * z = z * (c⁻¹ * (k : H) * c) := by
    intro k hk
    have h1 := hconj (hKB k.2)
    rw [hcb] at h1
    have h2 := hτa k hk
    set w := c⁻¹ * (k : H) * c
    have hz' : z = h.a * (h.a * z) := by rw [← mul_assoc, ha2, one_mul]
    calc w * z = w * h.a * (h.a * z) := by rw [mul_assoc w, ← hz']
      _ = h.a * (w * (h.a * z)) := by rw [h2, mul_assoc]
      _ = h.a * ((h.a * z) * w) := by rw [h1]
      _ = z * w := by rw [← mul_assoc, ← hz']
  have hτN : ∀ k ∈ CK, c⁻¹ * (k : H) * c ∈ normalizer (h.J : Set H) := fun k hk =>
    hCaN (mem_centralizer_singleton_iff.mpr (hτa k hk))
  set zbar : OddBar h.J := ((⟨z, hzJ⟩ : h.J) : OddBar h.J) with hzbar
  have hzbar2 : orderOf zbar = 2 := by
    apply orderOf_eq_prime
    · rw [hzbar, ← QuotientGroup.mk_pow]
      have : (⟨z, hzJ⟩ : h.J) ^ 2 = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hz2, pow_orderOf_eq_one])
      rw [this, QuotientGroup.mk_one]
    · intro he
      rw [hzbar, QuotientGroup.eq_one_iff] at he
      have hdvd : orderOf (⟨z, hzJ⟩ : h.J) ∣ Nat.card (pPrimeCore 2 ↥h.J) := by
        have := orderOf_dvd_natCard (⟨⟨z, hzJ⟩, he⟩ : pPrimeCore 2 ↥h.J)
        rwa [Subgroup.orderOf_mk] at this
      rw [Subgroup.orderOf_mk, hz2] at hdvd
      exact absurd (Nat.Coprime.coprime_dvd_right hdvd (CFSG.pPrimeCore_coprime_card (p := 2)))
        (by norm_num)
  obtain ⟨hsolv, h2grp⟩ := hStab (OddBar h.J) p f hp hp2 hf hJlie zbar hzbar2
  obtain ⟨Ñ, hÑC, hNÑ, hÑJ⟩ : ∃ Ñ : Subgroup ↥h.K, Ñ ≤ CK ∧ N ≤ Ñ.map π ∧
      ∀ k ∈ Ñ, c⁻¹ * (k : H) * c ∈ coreActionKernel h.J := by
    rcases hNtype with hperf | ⟨hq3, hNodd⟩
    · set M : Subgroup ↥h.K := CK ⊓ N.comap π with hM
      have hMmap : M.map π = N := by
        apply le_antisymm
        · rintro _ ⟨m, hm, rfl⟩
          exact (mem_inf.mp hm).2
        · intro w hw
          obtain ⟨k, hk, hke⟩ := hfixlift w (hNfix w hw)
          exact ⟨k, mem_inf.mpr ⟨hk, show π k ∈ N from hke ▸ hw⟩, hke⟩
      refine ⟨Quasithin.perfectCore M, (Quasithin.perfectCore_le M).trans inf_le_left, ?_, ?_⟩
      · rw [Quasithin.map_perfectCore, hMmap, Quasithin.perfectCore_eq_self_of_perfect hperf]
      · set X : Subgroup H := ((Quasithin.perfectCore M).map h.K.subtype).map
          (MulAut.conj c⁻¹).toMonoidHom with hX
        have hmemX : ∀ {k : ↥h.K}, k ∈ Quasithin.perfectCore M → c⁻¹ * (k : H) * c ∈ X :=
          fun {k} hk => ⟨k, ⟨k, hk, rfl⟩, by
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
        have hXC : ∀ x ∈ X, ∃ k ∈ CK, x = c⁻¹ * (k : H) * c := by
          rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
          refine ⟨k, (Quasithin.perfectCore_le M).trans inf_le_left hk, ?_⟩
          simp only [subtype_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        have hXN : X ≤ normalizer (h.J : Set H) := fun x hx => by
          obtain ⟨k, hk, rfl⟩ := hXC x hx
          exact hτN k hk
        have hXz : ∀ x ∈ X, x * z = z * x := fun x hx => by
          obtain ⟨k, hk, rfl⟩ := hXC x hx
          exact hτz k hk
        have hXperf : ⁅X, X⁆ = X := by
          rw [hX, ← map_commutator, ← map_commutator, Quasithin.perfectCore_perfect]
        have hXle := le_coreActionKernel_of_perfect hzJ hXN hXz hsolv hXperf
        exact fun k hk => hXle (hmemX hk)
    · set Ñ : Subgroup ↥h.K := closure {k : ↥h.K | k ∈ CK ∧ Odd (orderOf k)} with hÑ
      refine ⟨Ñ, (closure_le _).mpr fun k hk => hk.1, ?_, ?_⟩
      · refine hNodd.trans ?_
        rw [hÑ, MonoidHom.map_closure]
        apply Subgroup.closure_mono
        rintro w ⟨hwfix, hwodd⟩
        obtain ⟨k, hk, hke⟩ := hfixlift w hwfix
        obtain ⟨n, hnodd, hne⟩ := exists_pow_odd_orderOf_map_eq π k (by rw [hke]; exact hwodd)
        exact ⟨k ^ n, ⟨pow_mem hk n, hnodd⟩, hne.trans hke⟩
      · set S' : Subgroup ↥h.K := ((coreActionKernel h.J).comap
          (MulAut.conj c⁻¹).toMonoidHom).comap h.K.subtype with hS'
        have hmemS' : ∀ {k : ↥h.K}, k ∈ S' ↔ c⁻¹ * (k : H) * c ∈ coreActionKernel h.J := by
          intro k
          simp only [hS', mem_comap, subtype_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            inv_inv]
        have hle : Ñ ≤ S' := by
          rw [hÑ, closure_le]
          rintro k ⟨hk, hkodd⟩
          rw [SetLike.mem_coe, hmemS']
          have hodd' : Odd (orderOf (c⁻¹ * (k : H) * c)) := by
            have h1 : c⁻¹ * (k : H) * c = (MulAut.conj c⁻¹).toMonoidHom (k : H) := by
              simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
            rw [h1, orderOf_injective _ (MulAut.conj c⁻¹).injective, Subgroup.orderOf_coe]
            exact hkodd
          exact mem_coreActionKernel_of_odd hzJ (hτN k hk) (hτz k hk) (h2grp hq3) hodd'
        exact fun k hk => hmemS'.mp (hle hk)
  have haK : h.a ∈ coreActionKernel h.J := h.toHyp52.a_mem_coreActionKernel
  have haC : h.a ∈ centralizer ({h.a} : Set H) := mem_centralizer_singleton_iff.mpr rfl
  have hτCK : ∀ k ∈ Ñ, c⁻¹ * (k : H) * c ∈ centralizer ({h.a} : Set H) := fun k hk =>
    mem_centralizer_singleton_iff.mpr (hτa k (hÑC hk))
  rcases hNalt with hZN | ⟨A, hAN, hAc, hA8, u, huA, v, hvA, huv, hu2, hv2⟩ | ⟨hninn, h4⟩
  ·
    obtain ⟨n, hnÑ, hne⟩ := mem_map.mp (hNÑ (hZN hbKc))
    have ho : n⁻¹ * bK ∈ pPrimeCore 2 ↥h.K := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hne
      exact hne
    set o : ↥h.K := n⁻¹ * bK with hodef
    have hbno : b = (n : H) * (o : H) := by
      rw [hodef, coe_mul, coe_inv, ← hbKe']
      group
    set w₁ := c⁻¹ * (n : H) * c with hw₁
    set w₂ := c⁻¹ * (o : H) * c with hw₂
    have hw₁K : w₁ ∈ coreActionKernel h.J := hÑJ n hnÑ
    have hw₁N : w₁ ∈ normalizer (h.J : Set H) := hτN n (hÑC hnÑ)
    have hoCK : o ∈ CK := by
      have hbCK : bK ∈ CK := mem_subgroupOf.mpr (mem_centralizer_singleton_iff.mpr (by
        rw [hbKe']
        exact ha'b.symm))
      exact mul_mem (inv_mem (hÑC hnÑ)) hbCK
    have hw₂N : w₂ ∈ normalizer (h.J : Set H) := hτN o hoCK
    have haN : h.a ∈ normalizer (h.J : Set H) := hCaN haC
    have hzN : z ∈ normalizer (h.J : Set H) := le_normalizer hzJ
    have hw₂eq : (⟨w₂, hw₂N⟩ : ↥(normalizer (h.J : Set H))) =
        (⟨w₁, hw₁N⟩ : ↥(normalizer (h.J : Set H)))⁻¹ * ⟨h.a, haN⟩ * ⟨z, hzN⟩ := by
      apply Subtype.ext
      show w₂ = w₁⁻¹ * h.a * z
      have h1 : c⁻¹ * b * c = w₁ * w₂ := by rw [hbno, hw₁, hw₂]; group
      rw [hcb] at h1
      calc w₂ = w₁⁻¹ * (w₁ * w₂) := by group
        _ = w₁⁻¹ * (h.a * z) := by rw [h1]
        _ = w₁⁻¹ * h.a * z := by group
    set ρ := oddBarConj h.J with hρ
    have hρ1 : ρ ⟨w₁, hw₁N⟩ = 1 := oddBarConj_eq_one_of_mem_coreActionKernel hw₁K
    have hρa : ρ ⟨h.a, haN⟩ = 1 := oddBarConj_eq_one_of_mem_coreActionKernel haK
    have hρw₂ : ρ ⟨w₂, hw₂N⟩ = ρ ⟨z, hzN⟩ := by
      rw [hw₂eq, map_mul, map_mul, map_inv, hρ1, hρa, inv_one, one_mul, one_mul]
    have hρz1 : ρ ⟨z, hzN⟩ ≠ 1 := by
      intro he
      have hzK := mem_coreActionKernel_of_oddBarConj_eq_one he
      have hzP : z ∈ h.D ⊓ h.P :=
        mem_inf.mpr ⟨hzD, mem_inf.mpr ⟨h.toHyp52.D_le_S hzD, hzK⟩⟩
      rw [hDP, mem_bot] at hzP
      rw [hzP, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
    have hρz2 : orderOf (ρ ⟨z, hzN⟩) = 2 := by
      apply orderOf_eq_prime _ hρz1
      rw [← map_pow]
      have : (⟨z, hzN⟩ : ↥(normalizer (h.J : Set H))) ^ 2 = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hz2, pow_orderOf_eq_one])
      rw [this, map_one]
    have hoodd : Odd (orderOf w₂) := by
      have h1 : w₂ = (MulAut.conj c⁻¹).toMonoidHom (o : H) := by
        simp only [hw₂, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [h1, orderOf_injective _ (MulAut.conj c⁻¹).injective, Subgroup.orderOf_coe]
      have hdvd : orderOf o ∣ Nat.card (pPrimeCore 2 ↥h.K) := by
        have := orderOf_dvd_natCard (⟨o, ho⟩ : pPrimeCore 2 ↥h.K)
        rwa [Subgroup.orderOf_mk] at this
      have hcop := Nat.Coprime.coprime_dvd_right hdvd (CFSG.pPrimeCore_coprime_card (p := 2))
      exact Nat.coprime_two_left.mp hcop
    have hdvd : orderOf (ρ ⟨w₂, hw₂N⟩) ∣ orderOf w₂ := by
      have := orderOf_map_dvd ρ (⟨w₂, hw₂N⟩ : ↥(normalizer (h.J : Set H)))
      rwa [Subgroup.orderOf_mk] at this
    rw [hρw₂, hρz2] at hdvd
    exact (Nat.not_even_iff_odd.mpr hoodd) (even_iff_two_dvd.mpr hdvd)
  ·
    have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 3) (by rw [hA8]; norm_num)
    obtain ⟨R, hRÑ, hRA, hRinj⟩ := exists_twoSubgroup_lift hA2 (hAN.trans hNÑ)
    have hlift : ∀ {w : OddBar h.K}, w ∈ A → orderOf w = 2 →
        ∃ r ∈ R, π r = w ∧ r ^ 2 = 1 ∧ r ≠ 1 := by
      intro w hw hw2
      rw [← hRA] at hw
      obtain ⟨r, hr, rfl⟩ := mem_map.mp hw
      refine ⟨r, hr, rfl, ?_, ?_⟩
      · apply hRinj _ (pow_mem hr 2) _ (one_mem _)
        rw [map_pow, map_one]
        have h1 := pow_orderOf_eq_one (π r)
        rwa [hw2] at h1
      · rintro rfl
        rw [map_one, orderOf_one] at hw2
        exact absurd hw2 (by norm_num)
    obtain ⟨u₀, hu₀R, hu₀e, hu₀2, hu₀1⟩ := hlift huA hu2
    obtain ⟨v₀, hv₀R, hv₀e, hv₀2, hv₀1⟩ := hlift hvA hv2
    have hu₀v₀ : u₀ ≠ v₀ := fun he => huv (by rw [← hu₀e, ← hv₀e, he])
    set E : Subgroup H := (R.map h.K.subtype).map (MulAut.conj c⁻¹).toMonoidHom with hE
    have hEdesc : ∀ x ∈ E, ∃ r ∈ R, x = c⁻¹ * (r : H) * c := by
      rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      exact ⟨r, hr, by simp only [subtype_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        inv_inv]⟩
    have hmemE : ∀ {r : ↥h.K}, r ∈ R → c⁻¹ * (r : H) * c ∈ E := fun {r} hr =>
      ⟨r, ⟨r, hr, rfl⟩, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
    have hEC : E ≤ centralizer ({h.a} : Set H) := fun x hx => by
      obtain ⟨r, hr, rfl⟩ := hEdesc x hx
      exact hτCK r (hRÑ hr)
    have hEK : E ≤ coreActionKernel h.J := fun x hx => by
      obtain ⟨r, hr, rfl⟩ := hEdesc x hx
      exact hÑJ r (hRÑ hr)
    have hRc : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r := by
      intro r hr s hs
      apply hRinj _ (mul_mem hr hs) _ (mul_mem hs hr)
      rw [map_mul, map_mul]
      exact hAc _ (hRA ▸ mem_map_of_mem π hr) _ (hRA ▸ mem_map_of_mem π hs)
    have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
      intro x hx y hy
      obtain ⟨r, hr, rfl⟩ := hEdesc x hx
      obtain ⟨s, hs, rfl⟩ := hEdesc y hy
      have h1 : (r : H) * s = s * r := by rw [← coe_mul, ← coe_mul, hRc r hr s hs]
      exact hconj h1
    have hRcard : Nat.card R = 8 := by
      have hinj : Function.Injective (π.comp R.subtype) := fun r s hrs =>
        Subtype.ext (hRinj r r.2 s s.2 hrs)
      have hrange : (π.comp R.subtype).range = A := by
        rw [MonoidHom.range_comp, range_subtype, hRA]
      rw [← hA8, ← hrange]
      exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    have hEcard : Nat.card E = 8 := by
      rw [hE, card_map_of_injective (MulAut.conj c⁻¹).injective,
        card_map_of_injective h.K.subtype_injective, hRcard]
    have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hEcard]; norm_num)
    have horder : ∀ {r : ↥h.K}, r ^ 2 = 1 → r ≠ 1 → orderOf (c⁻¹ * (r : H) * c) = 2 := by
      intro r hr2 hr1
      have h1 : c⁻¹ * (r : H) * c = (MulAut.conj c⁻¹).toMonoidHom (r : H) := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [h1, orderOf_injective _ (MulAut.conj c⁻¹).injective, Subgroup.orderOf_coe]
      exact orderOf_eq_prime hr2 hr1
    have heq := h.eq_of_involutions hB1 hB6 hB7 hCF23 hCF24 hCFc hST hT hEC hEK hE2 hEc
      hEcard.ge (hmemE hu₀R) (hmemE hv₀R) (horder hu₀2 hu₀1) (horder hv₀2 hv₀1)
    apply hu₀v₀
    apply Subtype.ext
    calc (u₀ : H) = c * (c⁻¹ * (u₀ : H) * c) * c⁻¹ := by group
      _ = c * (c⁻¹ * (v₀ : H) * c) * c⁻¹ := by rw [heq]
      _ = v₀ := by group
  ·
    have h4Ñ : 2 ^ 2 ∣ Nat.card Ñ := by
      have h1 : Nat.card N ∣ Nat.card (Ñ.map π) := Subgroup.card_dvd_of_le hNÑ
      have h2 : Nat.card (Ñ.map π) ∣ Nat.card Ñ := Subgroup.card_map_dvd Ñ π
      have h3 : 4 ∣ Nat.card Ñ := h4.trans (h1.trans h2)
      norm_num
      exact h3
    obtain ⟨A₀, hA₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4Ñ
    set E₀ : Subgroup H := ((A₀.map Ñ.subtype).map h.K.subtype).map
      (MulAut.conj c⁻¹).toMonoidHom with hE₀
    have hE₀desc : ∀ x ∈ E₀, ∃ k ∈ Ñ, x = c⁻¹ * (k : H) * c := by
      rintro _ ⟨_, ⟨_, ⟨k, -, rfl⟩, rfl⟩, rfl⟩
      exact ⟨k, k.2, by simp only [subtype_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        inv_inv]⟩
    have hE₀C : E₀ ≤ centralizer ({h.a} : Set H) := fun x hx => by
      obtain ⟨k, hk, rfl⟩ := hE₀desc x hx
      exact hτCK k hk
    have hE₀K : E₀ ≤ coreActionKernel h.J := fun x hx => by
      obtain ⟨k, hk, rfl⟩ := hE₀desc x hx
      exact hÑJ k hk
    have hE₀card : Nat.card E₀ = 4 := by
      rw [hE₀, card_map_of_injective (MulAut.conj c⁻¹).injective,
        card_map_of_injective h.K.subtype_injective, card_map_of_injective Ñ.subtype_injective,
        hA₀]
      norm_num
    have hE₀c : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := by
      intro x hx y hy
      have hc4 : Nat.card E₀ = 2 ^ 2 := by rw [hE₀card]; norm_num
      exact congrArg Subtype.val
        ((IsPGroup.isMulCommutative_of_card_eq_prime_sq hc4).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have haE₀ : h.a ∉ E₀ := by
      intro haE
      obtain ⟨k, -, hk⟩ := hE₀desc _ haE
      have ha'k : a' = (k : H) := by
        rw [ha', hk]
        group
      apply hninn (k : OddBar h.K)
      rw [hα, ht]
      have : (⟨a', ha'N⟩ : ↥(normalizer (h.K : Set H))) = ⟨(k : H), ha'k ▸ ha'N⟩ :=
        Subtype.ext ha'k
      rw [this]
      exact oddBarConj_eq_conj k _
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := E₀) 2 (by rw [hE₀card]; norm_num)
    set F : Subgroup H := E₀ ⊔ zpowers h.a with hF
    have hFC : F ≤ centralizer ({h.a} : Set H) := sup_le hE₀C (zpowers_le.mpr haC)
    have hFK : F ≤ coreActionKernel h.J := sup_le hE₀K (zpowers_le.mpr haK)
    have hFcent : F ≤ centralizer (E₀ : Set H) ⊓ centralizer ({h.a} : Set H) := by
      refine sup_le (le_inf (fun x hx => mem_centralizer_iff.mpr fun y hy => hE₀c y hy x hx)
        hE₀C) (zpowers_le.mpr (mem_inf.mpr ⟨mem_centralizer_iff.mpr fun y hy =>
          mem_centralizer_singleton_iff.mp (hE₀C hy), haC⟩))
    have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := by
      intro x hx y hy
      obtain ⟨hxE, hxa⟩ := mem_inf.mp (hFcent hx)
      have hle : F ≤ centralizer ({x} : Set H) := by
        refine sup_le (fun e he => ?_) (zpowers_le.mpr ?_)
        · rw [mem_centralizer_singleton_iff]
          exact (mem_centralizer_iff.mp hxE e he)
        · rw [mem_centralizer_singleton_iff]
          exact (mem_centralizer_singleton_iff.mp hxa).symm
      exact (mem_centralizer_singleton_iff.mp (hle hy)).symm
    have hinf : E₀ ⊓ zpowers h.a = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxE, hxa⟩ := mem_inf.mp hx
      rw [mem_bot]
      by_contra hx1
      exact haE₀ (eq_of_mem_zpowers_of_orderOf_eq_two h.orderOf_a hxa hx1 ▸ hxE)
    have hF8 : 8 ≤ Nat.card F := by
      have := card_mul_le_card_sup hinf
      rw [hE₀card, Nat.card_zpowers, h.orderOf_a] at this
      omega
    have hF2 : IsPGroup 2 F := by
      have hE₀2 : IsPGroup 2 E₀ := IsPGroup.of_card (n := 2) (by rw [hE₀card]; norm_num)
      have ha2' : IsPGroup 2 (zpowers h.a) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.orderOf_a]; norm_num)
      exact hE₀2.to_sup_of_normal_right' ha2' fun x hx =>
        mem_normalizer_zpowers_of_comm (mem_centralizer_singleton_iff.mp (hE₀C hx))
    have heq := h.eq_of_involutions hB1 hB6 hB7 hCF23 hCF24 hCFc hST hT hFC hFK hF2 hFc hF8
      (mem_sup_left u.2) (mem_sup_right (mem_zpowers h.a))
      (by rw [Subgroup.orderOf_coe]; exact hu) h.orderOf_a
    exact haE₀ (heq ▸ u.2)

end Hyp59

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem mem_of_row516 (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hB7 : EmbedsTQuotStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hCFi : CFProp23IndexElim) (hST : SuzukiTausskyInput)
    (hFus : CFProp23Row516) (hStab : CFAutL2Stab) (hCent : CF516Cent) (hsec : h.SectionData)
    (hrow : h.Row516) : h.a ∈ h.K ⊔ coreActionKernel h.K := by
  by_contra hout
  obtain ⟨p, f, hp, hp2, hf, hJ, hKa, hK⟩ := hrow
  have hT := h.card_T_quot_eq_two
    (hCFi H h (Or.inr (Or.inr ⟨⟨p, f, hp, hp2, hf, hJ, hKa, hK⟩, hout⟩)))
  obtain ⟨H', _, _, h', ⟨eT⟩, ⟨eK⟩, -, -, hJ', hKa', hout', -⟩ := hsec
  have hT' : Nat.card (↥h'.T ⧸ h'.B.subgroupOf h'.T) = 2 := (Nat.card_congr eT.toEquiv).trans hT
  have hJs : IsSimpleGroup (OddBar h.J) := isSimpleGroup_of_lieModel_psl_two hJ
  obtain ⟨eJ⟩ := hJ' (center_eq_bot_of_isSimpleGroup_of_isQuasisimple h.isQuasisimple_J)
  have hJ'' : Blueprint.LieModel (OddBar h'.J) .PSL 2 p (2 * f) :=
    lieModel_of_mulEquiv_ne_zero eJ.symm (by norm_num) hJ
  have hK'' : Blueprint.LieModel (ZStarBar h'.K) .PSL 4 p f ∨
      Blueprint.LieModel (ZStarBar h'.K) .PSU 4 p f ∨
      ∃ e : ℕ, f = 2 * e ∧ Blueprint.LieModel (ZStarBar h'.K) .POmegaMinus 4 p e := by
    rcases hK with hL | hL | ⟨e, he, hL⟩
    · exact Or.inl (lieModel_of_mulEquiv_ne_zero eK.symm (by norm_num) hL)
    · exact Or.inr (Or.inl (lieModel_of_mulEquiv_ne_zero eK.symm (by norm_num) hL))
    · exact Or.inr (Or.inr ⟨e, he, lieModel_of_mulEquiv_ne_zero eK.symm (by norm_num) hL⟩)
  exact h'.false_of_row516_outer hB1 hB6 hB7 hCF23 hCF24 hCFc hST hFus hStab hCent hT'
    ⟨p, f, hp, hp2, hf, hJ'', hKa'.mpr hKa, hK''⟩ fun ha => hout (hout'.mp ha)

end Hyp52

end CFSG.ComponentClassification.GSThmB
