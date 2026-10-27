module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51Cal
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Pick

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem exists_twoElt_centralizer_of_comm_mem_pgroup {K T : Subgroup X} {y : X}
    (hT : IsPGroup 2 ↥T) (hO : T ≤ normalizer (pPrimeCoreOf 2 K : Set X)) (hyK : y ∈ K)
    (hyt : ∀ t ∈ T, ⁅y, t⁆ ∈ pPrimeCoreOf 2 K) {j : ℕ} (hyj : y ^ (2 ^ j) = 1) :
    ∃ c ∈ K ⊓ centralizer (T : Set X), c ^ (2 ^ j) = 1 ∧ c⁻¹ * y ∈ pPrimeCoreOf 2 K := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCoreOf 2 K with hOdef
  set N := normalizer (O : Set X)
  have hOK : O ≤ K := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hON : O ≤ N := le_normalizer
  have hKN : K ≤ N := by
    have h : (O.subgroupOf K).Normal := by
      rw [hOdef, pPrimeCoreOf, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
      infer_instance
    exact (normal_subgroupOf_iff_le_normalizer hOK).1 h
  have hMn : (O.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hON).2 le_rfl
  let yN : ↥N := ⟨y, hKN hyK⟩
  let T' : Subgroup ↥N := T.subgroupOf N
  have hT2 : Fact (IsPGroup 2 ↥T') :=
    ⟨IsPGroup.of_equiv hT (Subgroup.subgroupOfEquivOfLe hO).symm⟩
  have hμ : Nat.Coprime 2 (Nat.card O) := by
    rw [hOdef, pPrimeCoreOf, Subgroup.card_map_of_injective K.subtype_injective]
    exact pPrimeCore_coprime_card
  have hcop : Nat.Coprime 2 (Nat.card (O.subgroupOf N)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hON).toEquiv]
  set M := O.subgroupOf N with hMdef
  have hcent : centralizer (((T'.map (QuotientGroup.mk' M) : Subgroup (↥N ⧸ M))) :
      Set (↥N ⧸ M)) = (centralizer ((T' : Subgroup ↥N) : Set ↥N)).map
        (QuotientGroup.mk' M) :=
    centralizer_map_quotient_eq_map_centralizer 2 T' M hMn hcop
  have hmem : QuotientGroup.mk' M yN ∈
      centralizer (((T'.map (QuotientGroup.mk' M) : Subgroup (↥N ⧸ M))) :
        Set (↥N ⧸ M)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨tN, htN, rfl⟩
    have htT : (tN : X) ∈ T := Subgroup.mem_subgroupOf.1 htN
    have hcommM : ⁅yN, tN⁆ ∈ M := by
      rw [hMdef, Subgroup.mem_subgroupOf]
      exact hyt _ htT
    have hq1 : ⁅QuotientGroup.mk' M yN, QuotientGroup.mk' M tN⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).2 hcommM
    exact (commutatorElement_eq_one_iff_mul_comm.1 hq1).symm
  rw [hcent] at hmem
  obtain ⟨a, ha, haq⟩ := Subgroup.mem_map.1 hmem
  have hay : ((a : ↥N) : X)⁻¹ * y ∈ O := by
    have h1 : a⁻¹ * yN ∈ M := QuotientGroup.eq.1 haq
    rw [hMdef, Subgroup.mem_subgroupOf] at h1
    exact h1
  have haC : ((a : ↥N) : X) ∈ centralizer (T : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have htN : (⟨t, hO ht⟩ : ↥N) ∈ T' := Subgroup.mem_subgroupOf.2 ht
    have h1 : (⟨t, hO ht⟩ : ↥N) * a = a * ⟨t, hO ht⟩ :=
      (Subgroup.mem_centralizer_iff.1 ha) _ htN
    exact congrArg Subtype.val h1
  have haK : ((a : ↥N) : X) ∈ K := by
    have h1 : y * (((a : ↥N) : X)⁻¹ * y)⁻¹ ∈ K := K.mul_mem hyK (K.inv_mem (hOK hay))
    have h2 : y * (((a : ↥N) : X)⁻¹ * y)⁻¹ = ((a : ↥N) : X) := by group
    rwa [h2] at h1
  have hab : ((a : ↥N) : X) ^ (2 ^ j) ∈ O := by
    have hy1 : yN ^ (2 ^ j) = 1 := Subtype.ext hyj
    have e : QuotientGroup.mk' M (a ^ (2 ^ j)) = 1 := by
      rw [map_pow, haq, ← map_pow, hy1, map_one]
    have h1 : a ^ (2 ^ j) ∈ M := (QuotientGroup.eq_one_iff _).1 e
    rw [hMdef, Subgroup.mem_subgroupOf] at h1
    exact h1
  obtain ⟨n, hn1, hn2⟩ := exists_zpow_twoElt_of_pow_mem hμ hab
  refine ⟨((a : ↥N) : X) ^ n, ⟨zpow_mem haK n, zpow_mem haC n⟩, hn1, ?_⟩
  have e : (((a : ↥N) : X) ^ n)⁻¹ * y
      = (((a : ↥N) : X)⁻¹ * ((a : ↥N) : X) ^ n)⁻¹ * (((a : ↥N) : X)⁻¹ * y) := by group
  rw [e]
  exact O.mul_mem (O.inv_mem hn2) hay

theorem oTwoPrimeOf_inf_centralizer_covers_pgroup {K T : Subgroup X} (hT : IsPGroup 2 ↥T)
    (hK : primeResidual 2 ↥K = ⊤) (hO : T ≤ normalizer (pPrimeCoreOf 2 K : Set X))
    (hcomm : ∀ k ∈ K, ∀ t ∈ T, ⁅k, t⁆ ∈ pPrimeCoreOf 2 K) :
    (oTwoPrimeOf (K ⊓ centralizer (T : Set X))).subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤ := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_top_iff, ← hK, primeResidual_eq_closure, Subgroup.closure_le]
  rintro x ⟨j, hj⟩
  have hxj : (x : X) ^ (2 ^ j) = 1 := by
    have := pow_orderOf_eq_one x
    rw [hj] at this
    exact congrArg Subtype.val this
  obtain ⟨c, hc, hcj, hcy⟩ := exists_twoElt_centralizer_of_comm_mem_pgroup hT hO x.2
    (fun t ht => hcomm _ x.2 t ht) hxj
  have hcK : c ∈ K := hc.1
  have hcF : c ∈ oTwoPrimeOf (K ⊓ centralizer (T : Set X)) := mem_oTwoPrimeOf hc j hcj
  have h1 : (⟨c, hcK⟩ : ↥K) ∈ (oTwoPrimeOf (K ⊓ centralizer (T : Set X))).subgroupOf K := hcF
  have h2 : (⟨c, hcK⟩ : ↥K)⁻¹ * x ∈ pPrimeCore 2 ↥K := by
    obtain ⟨w, hw, hwe⟩ := hcy
    have : w = (⟨c, hcK⟩ : ↥K)⁻¹ * x := Subtype.ext hwe
    rwa [← this]
  have : x = ⟨c, hcK⟩ * ((⟨c, hcK⟩ : ↥K)⁻¹ * x) := by group
  rw [this]
  exact Subgroup.mul_mem_sup h1 h2

theorem exists_conj_twoElt_of_mem_sup_odd_X {A N : Subgroup X}
    (hAN : A ≤ normalizer (N : Set X)) (hN : Odd (Nat.card N)) {x : X} (hx : x ∈ A ⊔ N) {j : ℕ}
    (hxj : x ^ (2 ^ j) = 1) : ∃ o ∈ N, ∃ a ∈ A, a ^ (2 ^ j) = 1 ∧ x = o * a * o⁻¹ := by
  set D : Subgroup X := normalizer (N : Set X) with hD
  have hND : N ≤ D := Subgroup.le_normalizer
  have hMn : (N.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hND).2 le_rfl
  have hxD : x ∈ D := (sup_le hAN hND) hx
  have hxAN : (⟨x, hxD⟩ : D) ∈ A.subgroupOf D ⊔ N.subgroupOf D := by
    rw [← Subgroup.subgroupOf_sup hAN hND]
    exact hx
  have hN' : Odd (Nat.card (N.subgroupOf D)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hND).toEquiv]
    exact hN
  obtain ⟨o, ho, a, ha, hak, hxa⟩ :=
    exists_conj_twoElt_of_mem_sup_odd (A := A.subgroupOf D) (N := N.subgroupOf D) hN' hxAN
      (j := j) (Subtype.ext hxj)
  exact ⟨(o : X), Subgroup.mem_subgroupOf.1 ho, (a : X), Subgroup.mem_subgroupOf.1 ha,
    congrArg Subtype.val hak, congrArg Subtype.val hxa⟩

theorem le_of_le_sup_pPrimeCoreOf {D M E : Subgroup X} (hM : IsPCompIn 2 D M)
    (hED : E ≤ D) (hgen : primeResidual 2 ↥E = ⊤) (h : E ≤ M ⊔ pPrimeCoreOf 2 D) : E ≤ M := by
  obtain ⟨hMD, hMc⟩ := hM
  have hgen' : primeResidual 2 ↥(E.subgroupOf D) = ⊤ :=
    primeResidual_eq_top_of_equiv 2 (Subgroup.subgroupOfEquivOfLe hED).symm hgen
  have h' : E.subgroupOf D ≤ M.subgroupOf D ⊔ pPrimeCore 2 ↥D := by
    intro y hy
    have hy1 : (y : X) ∈ M ⊔ pPrimeCoreOf 2 D := h hy
    have hmap : M ⊔ pPrimeCoreOf 2 D = (M.subgroupOf D ⊔ pPrimeCore 2 ↥D).map D.subtype := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hMD]
      rfl
    rw [hmap] at hy1
    obtain ⟨y', hy', hyy'⟩ := Subgroup.mem_map.1 hy1
    have hyy : y' = y := Subtype.ext hyy'
    exact hyy ▸ hy'
  have hle : E.subgroupOf D ≤ M.subgroupOf D := le_of_le_sup_pPrimeCore hMc hgen' h'
  intro y hy
  exact Subgroup.mem_subgroupOf.1
    (hle (Subgroup.mem_subgroupOf.2 (show (⟨y, hED hy⟩ : D).1 ∈ E from hy)))

theorem inf_pPrimeCoreOf_le_pPrimeCoreOf {A L : Subgroup X} (hAL : A ≤ L) :
    A ⊓ pPrimeCoreOf 2 L ≤ pPrimeCoreOf 2 A := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup ↥A := (A ⊓ pPrimeCoreOf 2 L).subgroupOf A with hM
  have hMnormal : M.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hM, Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨A.mul_mem (A.mul_mem g.2 hn.1) (A.inv_mem g.2), ?_⟩
    exact (Subgroup.mem_normalizer_iff.1 (mem_normalizer_pPrimeCoreOf_of_mem (hAL g.2))
      (n : X)).1 hn.2
  have hMcard : Nat.Coprime 2 (Nat.card M) := by
    have h1 : Nat.card M = Nat.card ↥(A ⊓ pPrimeCoreOf 2 L) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have h2 : Nat.card ↥(A ⊓ pPrimeCoreOf 2 L) ∣ Nat.card ↥(pPrimeCoreOf 2 L) :=
      Subgroup.card_dvd_of_le inf_le_right
    have h3 : Nat.card ↥(pPrimeCoreOf 2 L) = Nat.card (pPrimeCore 2 ↥L) :=
      Subgroup.card_map_of_injective L.subtype_injective
    rw [h1]
    exact Nat.Coprime.coprime_dvd_right (h3 ▸ h2) pPrimeCore_coprime_card
  have hMle : M ≤ pPrimeCore 2 ↥A := le_sSup ⟨hMnormal, hMcard⟩
  intro x hx
  have hxM : (⟨x, hx.1⟩ : ↥A) ∈ M := hx
  exact ⟨⟨x, hx.1⟩, hMle hxM, rfl⟩

omit [Finite X] in
theorem normalizer_le_normalizer_pPrimeCoreOf (A : Subgroup X) :
    normalizer (A : Set X) ≤ normalizer (pPrimeCoreOf 2 A : Set X) := by
  intro c hc
  have hP : (pPrimeCoreOf 2 A).map (MulAut.conj c).toMonoidHom = pPrimeCoreOf 2 A := by
    rw [← pPrimeCoreOf_map_mulEquiv, map_conj_eq_of_mem_normalizer hc]
  exact mem_normalizer_of_map_conj_eq hP

theorem pPrimeCoreOf_le_normalizer_of_isPCompIn {D M : Subgroup X} (hM : IsPCompIn 2 D M) :
    pPrimeCoreOf 2 D ≤ normalizer (M : Set X) := by
  obtain ⟨hMD, hMpc⟩ := hM
  rintro _ ⟨o', ho', rfl⟩
  have h := pPrimeCore_le_normalizer_of_isPComponent hMpc ho'
  rw [← Subgroup.subgroupOf_normalizer_eq hMD] at h
  exact h

theorem normalizes_isPCompIn_of_comm_mem {D L : Subgroup X} {a : X} (hL : IsPCompIn 2 D L)
    (haD : a ∈ normalizer (D : Set X)) (hcomm : ∀ l ∈ L, ⁅l, a⁆ ∈ pPrimeCoreOf 2 D) :
    a ∈ centralizerSection L (pPrimeCoreOf 2 L) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : X ≃* X := MulAut.conj a with hφ
  have hLD : L ≤ D := hL.1
  have hDφ : D.map φ.toMonoidHom = D := map_conj_eq_of_mem_normalizer haD
  have hL'D : L.map φ.toMonoidHom ≤ D := by
    rw [← hDφ]; exact Subgroup.map_mono hLD
  have hL' : IsPCompIn 2 D (L.map φ.toMonoidHom) := by
    refine ⟨hL'D, ?_⟩
    have := (isPComponent_subgroupOf_map_iff 2 φ.toMonoidHom φ.injective hLD).2 hL.2
    rwa [hDφ] at this
  have hgen : primeResidual 2 ↥(L.map φ.toMonoidHom) = ⊤ :=
    ((isTwoGenQuasi_subgroupOf_iff hL'D).1 (isPComponent_two_iff.1 hL'.2).2).1
  have hle : L.map φ.toMonoidHom ≤ L ⊔ pPrimeCoreOf 2 D := by
    rintro _ ⟨l, hl, rfl⟩
    have h1 : φ.toMonoidHom l = ⁅a, l⁆ * l := by
      simp [hφ, MulAut.conj_apply, commutatorElement_def]
    rw [h1]
    have h2 : ⁅a, l⁆ ∈ pPrimeCoreOf 2 D := by
      have : ⁅a, l⁆ = (⁅l, a⁆)⁻¹ := (commutatorElement_inv l a).symm
      rw [this]
      exact (pPrimeCoreOf 2 D).inv_mem (hcomm l hl)
    rw [sup_comm]
    exact Subgroup.mul_mem_sup h2 hl
  have hL'L : L.map φ.toMonoidHom ≤ L := le_of_le_sup_pPrimeCoreOf hL hL'D hgen hle
  have hcard : Nat.card (L.map φ.toMonoidHom) = Nat.card L :=
    Subgroup.card_map_of_injective φ.injective
  have hL'eq : L.map φ.toMonoidHom = L := Subgroup.eq_of_le_of_card_ge hL'L hcard.ge
  have haL : a ∈ normalizer (L : Set X) := mem_normalizer_of_map_conj_eq hL'eq
  have haO : a ∈ normalizer (pPrimeCoreOf 2 L : Set X) :=
    normalizer_le_normalizer_pPrimeCoreOf L haL
  refine ⟨haL, haO, fun l hl => ?_⟩
  have h1 : ⁅l, a⁆ ∈ L := by
    have : ⁅l, a⁆ = l * (a * l⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact L.mul_mem hl ((Subgroup.mem_normalizer_iff.1 haL l⁻¹).1 (L.inv_mem hl))
  exact inf_pPrimeCoreOf_le_pPrimeCoreOf hLD ⟨h1, hcomm l hl⟩

end CFSG.OddStandard.Solomon75
