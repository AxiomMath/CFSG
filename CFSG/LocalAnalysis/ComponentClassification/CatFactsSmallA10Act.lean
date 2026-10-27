module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallS10
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallSAct
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5A10
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuot
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBSharedCore
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bOrbit

public section

namespace CFSG.ComponentClassification.CatFactsSmall.A10

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.UnbalancedLayer
open Equiv

section Cores

variable {A : Type*} [Group A] [Finite A]

omit [Finite A] in
theorem exists_pow_mem_of_mem_oddTwoCore {x : A} (hx : x ∈ oddTwoCore A) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ pPrimeCore 2 A := by
  obtain ⟨k, hk⟩ := pCore_isPGroup (p := 2) (G := A ⧸ pPrimeCore 2 A)
    ⟨QuotientGroup.mk' (pPrimeCore 2 A) x, hx⟩
  refine ⟨k, ?_⟩
  have h1 : (QuotientGroup.mk' (pPrimeCore 2 A) x) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

omit [Finite A] in
theorem le_oddTwoCore_of_isPGroup {M : Subgroup A} (hM : M.Normal) (h2 : IsPGroup 2 M) :
    M ≤ oddTwoCore A := by
  intro m hm
  have hn : (M.map (QuotientGroup.mk' (pPrimeCore 2 A))).Normal :=
    hM.map _ (QuotientGroup.mk'_surjective _)
  have hle : M.map (QuotientGroup.mk' (pPrimeCore 2 A)) ≤ pCore 2 (A ⧸ pPrimeCore 2 A) :=
    le_sSup ⟨hn, h2.map _⟩
  exact hle ⟨m, hm, rfl⟩

omit [Finite A] in
theorem le_pPrimeCore_of_coprime {M : Subgroup A} (hM : M.Normal)
    (hc : Nat.Coprime 2 (Nat.card M)) : M ≤ pPrimeCore 2 A :=
  le_sSup ⟨hM, hc⟩

omit [Finite A] in
theorem pPrimeCore_le_oddTwoCore' : pPrimeCore 2 A ≤ oddTwoCore A := by
  intro x hx
  show QuotientGroup.mk' (pPrimeCore 2 A) x ∈ pCore 2 (A ⧸ pPrimeCore 2 A)
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
  exact one_mem _

end Cores

@[expose] noncomputable def autA10 : Perm (Fin 10) ≃* MulAut (alternatingGroup (Fin 10)) :=
  MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 10)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 10 (by norm_num)
      (by norm_num))

theorem autA10_symm_conj (y : alternatingGroup (Fin 10)) :
    autA10.symm (MulAut.conj y) = (y : Perm (Fin 10)) := by
  rw [MulEquiv.symm_apply_eq]
  ext x
  simp [autA10, MulAut.conjNormal_apply, MulAut.conj_apply]

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem K_le_W : h.K ≤ h.W := h.isPComponent_K.1

theorem W_le_normalizer_K (hKa : conjugate h.K h.a = h.K) : h.W ≤ normalizer (h.K : Set H) := by
  have h1 := OddQuot.le_normalizer_layerIn h.W
  rw [← h.V_eq_K hKa]
  exact h1

section Cores

variable {h}

theorem mem_pPrimeCore_of_mem_pPrimeCore_W {k : h.K}
    (hk : (⟨k, K_le_W h k.2⟩ : h.W) ∈ pPrimeCore 2 h.W) : k ∈ pPrimeCore 2 h.K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup h.K := (pPrimeCore 2 h.W).comap (inclusion (K_le_W h)) with hM
  have hMn : M.Normal := (pPrimeCore_normal (p := 2) (G := h.W)).comap _
  have hMc : Nat.Coprime 2 (Nat.card M) := by
    have hle : M.map (inclusion (K_le_W h)) ≤ pPrimeCore 2 h.W := map_comap_le _ _
    have h1 := card_dvd_of_le hle
    rw [card_map_of_injective (inclusion_injective _)] at h1
    exact (pPrimeCore_coprime_card (p := 2) (G := h.W)).coprime_dvd_right h1
  exact le_pPrimeCore_of_coprime hMn hMc hk

theorem mem_pPrimeCore_of_mem_oddTwoCore (eK : OddBar h.K ≃* alternatingGroup (Fin 10)) {k : h.K}
    (hk : (⟨k, K_le_W h k.2⟩ : h.W) ∈ oddTwoCore h.W) : k ∈ pPrimeCore 2 h.K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup h.K := (oddTwoCore h.W).comap (inclusion (K_le_W h)) with hN
  have hNn : N.Normal := (oddTwoCore_normal h.W).comap _
  have hNb : (N.map (QuotientGroup.mk' (pPrimeCore 2 h.K))).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective _)
  have hsimp : IsSimpleGroup (OddBar h.K) :=
    (MulEquiv.isSimpleGroup_congr eK).2 (alternatingGroup.isSimpleGroup (by simp))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (N.map (QuotientGroup.mk' (pPrimeCore 2 h.K))) with hb | ht
  · have : QuotientGroup.mk' (pPrimeCore 2 h.K) k ∈
        N.map (QuotientGroup.mk' (pPrimeCore 2 h.K)) := ⟨k, hk, rfl⟩
    rw [hb, mem_bot] at this
    exact (QuotientGroup.eq_one_iff k).1 this
  exfalso
  have h2 : ∀ y : OddBar h.K, ∃ e : ℕ, y ^ 2 ^ e = 1 := by
    intro y
    have hy : y ∈ N.map (QuotientGroup.mk' (pPrimeCore 2 h.K)) := by
      rw [ht]
      exact mem_top y
    obtain ⟨n, hn, rfl⟩ := hy
    obtain ⟨e, he⟩ := exists_pow_mem_of_mem_oddTwoCore hn
    refine ⟨e, ?_⟩
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).2
    have : inclusion (K_le_W h) (n ^ 2 ^ e) ∈ pPrimeCore 2 h.W := by
      rw [map_pow]
      exact he
    exact mem_pPrimeCore_of_mem_pPrimeCore_W this
  have hcard : 3 ∣ Nat.card (OddBar h.K) := by
    rw [Nat.card_congr eK.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 hcard
  obtain ⟨e, he⟩ := h2 y
  have h3 := orderOf_dvd_of_pow_eq_one he
  rw [hy] at h3
  exact absurd ((Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)) (by decide)

theorem mem_oddTwoCore_of_mem_pPrimeCore (hKN : h.W ≤ normalizer (h.K : Set H)) {k : h.K}
    (hk : k ∈ pPrimeCore 2 h.K) : (⟨k, K_le_W h k.2⟩ : h.W) ∈ oddTwoCore h.W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply pPrimeCore_le_oddTwoCore'
  set M : Subgroup h.W := (pPrimeCore 2 h.K).map (inclusion (K_le_W h)) with hM
  have hMn : M.Normal := ⟨fun m hm w => by
    obtain ⟨o, ho, rfl⟩ := hm
    have hw := UnbalancedGS.normalizer_le_normalizer_map_of_characteristic h.K
      (pPrimeCore 2 h.K) (hKN w.2)
    obtain ⟨o', ho', hoe⟩ := mem_map.1 ((mem_normalizer_iff.1 hw (o : H)).1 ⟨o, ho, rfl⟩)
    refine ⟨o', ho', Subtype.ext ?_⟩
    rw [subtype_apply] at hoe
    simp only [coe_inclusion, coe_mul, coe_inv, hoe]⟩
  have hMc : Nat.Coprime 2 (Nat.card M) := by
    rw [hM, card_map_of_injective (inclusion_injective _)]
    exact pPrimeCore_coprime_card
  exact le_pPrimeCore_of_coprime hMn hMc ⟨k, hk, rfl⟩

end Cores

@[expose] noncomputable def rhoW (hKa : conjugate h.K h.a = h.K)
    (eK : OddBar h.K ≃* alternatingGroup (Fin 10)) : h.W →* Perm (Fin 10) :=
  autA10.symm.toMonoidHom.comp ((MulAut.congr eK).toMonoidHom.comp
    ((oddBarConj h.K).comp (inclusion (W_le_normalizer_K h hKa))))

variable {h} (hKa : conjugate h.K h.a = h.K) (eK : OddBar h.K ≃* alternatingGroup (Fin 10))

theorem rhoW_eq_one_iff (w : h.W) :
    rhoW h hKa eK w = 1 ↔ (w : H) ∈ coreActionKernel h.K := by
  have : rhoW h hKa eK w = 1 ↔ oddBarConj h.K (inclusion (W_le_normalizer_K h hKa) w) = 1 := by
    simp only [rhoW, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.map_eq_one_iff]
  rw [this]
  exact ⟨fun h1 => mem_coreActionKernel_of_oddBarConj_eq_one h1,
    fun h1 => oddBarConj_one_of_mem_kernel h1⟩

theorem rhoW_of_mem_K (k : h.K) :
    rhoW h hKa eK ⟨k, K_le_W h k.2⟩ = (eK (k : OddBar h.K) : Perm (Fin 10)) := by
  simp only [rhoW, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
  have h1 : oddBarConj h.K (inclusion (W_le_normalizer_K h hKa) ⟨k, K_le_W h k.2⟩) =
      MulAut.conj (k : OddBar h.K) := oddBarConj_of_mem k _
  rw [h1]
  have h2 : MulAut.congr eK (MulAut.conj (k : OddBar h.K)) = MulAut.conj (eK k) := by
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  rw [h2, autA10_symm_conj]

theorem oddTwoCore_le_ker : oddTwoCore h.W ≤ (rhoW h hKa eK).ker := by
  intro o ho
  rw [MonoidHom.mem_ker, rhoW_eq_one_iff, mem_coreActionKernel]
  refine ⟨W_le_normalizer_K h hKa o.2, fun j hj => ?_⟩
  have hjW : j ∈ h.W := K_le_W h hj
  have hcK : j⁻¹ * (o : H)⁻¹ * j * o ∈ h.K := by
    have h1 : (o : H)⁻¹ * j * (o : H)⁻¹⁻¹ ∈ h.K :=
      (mem_normalizer_iff.1 (W_le_normalizer_K h hKa (inv_mem o.2)) j).1 hj
    rw [inv_inv] at h1
    have := mul_mem (inv_mem hj) h1
    rwa [← mul_assoc, ← mul_assoc] at this
  have hcO : (⟨j⁻¹ * (o : H)⁻¹ * j * o, K_le_W h hcK⟩ : h.W) ∈ oddTwoCore h.W := by
    have h1 : (⟨j, hjW⟩ : h.W)⁻¹ * o⁻¹ * (⟨j, hjW⟩ : h.W)⁻¹⁻¹ ∈ oddTwoCore h.W :=
      (oddTwoCore_normal h.W).conj_mem _ (inv_mem ho) _
    rw [inv_inv] at h1
    have h2 := mul_mem h1 ho
    convert h2 using 1
  exact ⟨_, mem_pPrimeCore_of_mem_oddTwoCore eK (k := ⟨_, hcK⟩) hcO, rfl⟩

@[expose] noncomputable def rhoBar : Wbar h.B →* Perm (Fin 10) :=
  QuotientGroup.lift (oddTwoCore h.W) (rhoW h hKa eK) (oddTwoCore_le_ker hKa eK)

theorem rhoBar_mk (w : h.W) : rhoBar hKa eK (wbarMk h.B w) = rhoW h hKa eK w :=
  QuotientGroup.lift_mk _ _ _

theorem wbarMk_eq_of_rhoW_eq {k₁ k₂ : h.K}
    (heq : rhoW h hKa eK ⟨k₁, K_le_W h k₁.2⟩ = rhoW h hKa eK ⟨k₂, K_le_W h k₂.2⟩) :
    wbarMk h.B ⟨k₁, K_le_W h k₁.2⟩ = wbarMk h.B ⟨k₂, K_le_W h k₂.2⟩ := by
  rw [rhoW_of_mem_K, rhoW_of_mem_K] at heq
  have h1 : (k₁ : OddBar h.K) = k₂ := eK.injective (Subtype.ext heq)
  rw [QuotientGroup.eq] at h1
  have h2 := mem_oddTwoCore_of_mem_pPrimeCore (W_le_normalizer_K h hKa) h1
  simp only [wbarMk, QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq]
  convert h2 using 1

theorem eq_one_of_rhoBar_eq_one {y : Wbar h.B} (hy : rhoBar hKa eK y = 1) (hy2 : y * y = 1) :
    y = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (oddTwoCore h.W) y
  change rhoBar hKa eK (wbarMk h.B w) = 1 at hy
  rw [rhoBar_mk] at hy
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos w).ne'
  set w' := w ^ m with hw'
  have hw'2 : w' ^ 2 ^ a = 1 := by
    rw [hw', ← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  have hw'K : (w' : H) ∈ coreActionKernel h.K := by
    rw [← rhoW_eq_one_iff hKa eK, hw', map_pow, hy, one_pow]
  have hV : layerIn h.W = h.K := h.V_eq_K hKa
  set X := normalizer (h.B : Set H) ⊓ coreActionKernel (layerIn h.W) with hX
  obtain ⟨R, hR⟩ : ∃ R : Sylow 2 X, (R : Subgroup X) = h.B.subgroupOf X := h.B_sylow_kernel
  have hw'X : (w' : H) ∈ X := ⟨w'.2, by rw [hV]; exact hw'K⟩
  set x : X := ⟨w', hw'X⟩ with hx
  have hw'2H : (w' : H) ^ 2 ^ a = 1 := by
    have := congrArg Subtype.val hw'2
    simpa using this
  have hx2 : IsPGroup 2 (zpowers x) := IsPGroup.of_card_dvd_pow (n := a) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [hx] using hw'2H)))
  have hRn : x ∈ normalizer ((R : Subgroup X) : Set X) := by
    rw [hR, mem_normalizer_iff]
    intro b
    simp only [mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.1 w'.2 b
  have hxR : x ∈ (R : Subgroup X) := by
    have hsup : IsPGroup 2 ↥((R : Subgroup X) ⊔ zpowers x) :=
      IsPGroup.to_sup_of_normal_left' R.isPGroup' hx2 (zpowers_le.2 hRn)
    rw [← R.is_maximal' hsup le_sup_left]
    exact mem_sup_right (mem_zpowers x)
  rw [hR, mem_subgroupOf] at hxR
  have hB2 : IsPGroup 2 h.B := (isPGroup_S h).to_le (h.B_le.trans inf_le_left)
  have hBO : h.B.subgroupOf h.W ≤ oddTwoCore h.W :=
    le_oddTwoCore_of_isPGroup (Subgroup.normal_in_normalizer) hB2.comap_subtype
  have hw'O : w' ∈ oddTwoCore h.W := hBO (mem_subgroupOf.2 hxR)
  have h1 : wbarMk h.B w' = 1 := (QuotientGroup.eq_one_iff _).2 hw'O
  have h2 : wbarMk h.B w' = wbarMk h.B w := by
    rw [hw', map_pow]
    obtain ⟨m', rfl⟩ := hm
    rw [pow_succ, pow_mul, sq]
    change (QuotientGroup.mk' (oddTwoCore h.W) w * QuotientGroup.mk' (oddTwoCore h.W) w) ^ m' *
      _ = _
    rw [hy2, one_pow, one_mul]
  rw [← h2, h1]

end CFSG.ComponentClassification.CatFactsSmall.A10
