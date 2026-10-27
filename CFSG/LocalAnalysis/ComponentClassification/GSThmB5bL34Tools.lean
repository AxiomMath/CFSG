module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bAction
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma512c
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankProjectiveAction

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

theorem card_le_four_of_sq_eq_one {G : Type*} [Group G] [Finite G] {P C E : Subgroup G}
    (hCP : C ≤ P) (hC : IsCyclic C) (hPC : Nat.card P ≤ 2 * Nat.card C) (hEP : E ≤ P)
    (hE2 : ∀ e ∈ E, e ^ 2 = 1) : Nat.card E ≤ 4 := by
  classical
  have : Fintype C := Fintype.ofFinite C
  have h1 : Nat.card ↥(C ⊓ E) ≤ 2 := by
    have hle := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
    set S₁ := E.subgroupOf C with hS₁
    have hcS : Nat.card ↥(C ⊓ E) = Nat.card S₁ := by
      rw [← Subgroup.card_map_of_injective C.subtype_injective, hS₁, subgroupOf_map_subtype,
        inf_comm]
    rw [hcS, Nat.card_eq_fintype_card, Fintype.card_subtype]
    refine le_trans (Finset.card_le_card fun y hy => ?_) hle
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hE2 _ (mem_subgroupOf.mp hy)
  have hPfin : C.relIndex P ≠ 0 := by
    rw [relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have h2 : C.relIndex E ≤ C.relIndex P := relIndex_le_of_le_right hEP hPfin
  have h3 : C.relIndex P ≤ 2 := by
    have hc := Subgroup.card_mul_index (C.subgroupOf P)
    have hcC : Nat.card (C.subgroupOf P) = Nat.card C := by
      rw [← Subgroup.card_map_of_injective P.subtype_injective, subgroupOf_map_subtype,
        inf_of_le_left hCP]
    rw [hcC] at hc
    have hC0 : 0 < Nat.card C := Nat.card_pos
    rw [relIndex]
    by_contra hlt
    push Not at hlt
    have : 3 * Nat.card C ≤ Nat.card P := by
      calc 3 * Nat.card C ≤ (C.subgroupOf P).index * Nat.card C := Nat.mul_le_mul_right _ hlt
        _ = Nat.card P := by rw [← hc, mul_comm]
    omega
  have hcE := Subgroup.card_mul_index (C.subgroupOf E)
  have hcE' : Nat.card (C.subgroupOf E) = Nat.card ↥(C ⊓ E) := by
    rw [← Subgroup.card_map_of_injective E.subtype_injective, subgroupOf_map_subtype]
  rw [hcE'] at hcE
  calc Nat.card E = Nat.card ↥(C ⊓ E) * C.relIndex E := hcE.symm
    _ ≤ 2 * 2 := Nat.mul_le_mul h1 (h2.trans h3)
    _ = 4 := by norm_num

theorem mem_normalizer_layerIn {G : Type*} [Group G] [Finite G] {Y : Subgroup G} {y : G}
    (hy : y ∈ Y) : y ∈ normalizer (layerIn Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (pLayer ↥Y 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
  have hN : (pLayer ↥Y 2).Normal := inferInstance
  have key : ∀ c ∈ Y, ∀ x ∈ layerIn Y, c * x * c⁻¹ ∈ layerIn Y := by
    intro c hc x hx
    obtain ⟨x', hx', rfl⟩ := mem_map.mp hx
    exact ⟨⟨c, hc⟩ * x' * ⟨c, hc⟩⁻¹, hN.conj_mem _ hx' _, rfl⟩
  apply mem_normalizer_of_conj_mem (key y hy)
  intro x hx
  have := key y⁻¹ (inv_mem hy) x hx
  rwa [inv_inv] at this

namespace Hyp59

variable {H : Type} [Group H] [Finite H] (h : Hyp59 H)

theorem x_mem_normalizer_T : h.x ∈ normalizer (h.T : Set H) := by
  rcases h.x_cond with hx | ⟨hPQ, -⟩
  · obtain ⟨-, hxQ⟩ := mem_inf.mp hx
    have key : ∀ c : H, c ∈ h.S → c ∈ normalizer (h.Q : Set H) →
        ∀ y ∈ h.T, c * y * c⁻¹ ∈ h.T := by
      intro c hcS hcQ y hy
      obtain ⟨hyQ, hyP⟩ := mem_inf.mp hy
      exact mem_inf.mpr ⟨(mem_normalizer_iff.mp hcQ y).mp hyQ, h.toHyp52.conj_mem_P hcS hyP⟩
    apply mem_normalizer_of_conj_mem (key _ h.x_mem hxQ)
    intro y hy
    have := key _ (inv_mem h.x_mem) (inv_mem hxQ) y hy
    rwa [inv_inv] at this
  · have hTP : h.T = h.P := le_antisymm inf_le_right (fun y hy => mem_inf.mpr ⟨hPQ hy, hy⟩)
    rw [hTP]
    apply mem_normalizer_of_conj_mem (fun y hy => h.toHyp52.conj_mem_P h.x_mem hy)
    intro y hy
    have := h.toHyp52.conj_mem_P (inv_mem h.x_mem) hy
    rwa [inv_inv] at this

theorem conj_x_b {b : H} (hBb : h.B = zpowers b) (hb : orderOf b = 2)
    (hTab : h.T = zpowers h.a ⊔ zpowers b) : h.x⁻¹ * b * h.x = h.a * b := by
  have hbB : b ∈ h.B := hBb ▸ mem_zpowers b
  have hbT : b ∈ h.T := h.toHyp52.B_le_T hbB
  have hbS : b ∈ h.S := h.toHyp52.B_le_S hbB
  have hab : h.a * b = b * h.a := (h.toHyp52.comm_a hbS).symm
  have hb1 : b ≠ 1 := fun he => by rw [he, orderOf_one] at hb; exact absurd hb (by norm_num)
  have hxb : h.x⁻¹ * b * h.x ∈ h.T := by
    have := (mem_normalizer_iff.mp (inv_mem h.x_mem_normalizer_T) b).mp hbT
    rwa [inv_inv] at this
  rcases h.mem_T_cases hb hTab hab hxb with h1 | h1 | h1 | h1
  · exfalso; apply hb1
    calc b = h.x * (h.x⁻¹ * b * h.x) * h.x⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · exfalso; apply h.toHyp52.a_not_mem_B
    have : b = h.a := by
      calc b = h.x * (h.x⁻¹ * b * h.x) * h.x⁻¹ := by group
        _ = h.x * h.a * h.x⁻¹ := by rw [h1]
        _ = h.a := by rw [h.toHyp52.x_comm_a, mul_inv_cancel_right]
    rw [← this]; exact hbB
  · exfalso; apply hb1
    have hbx : b ∈ conjugate h.B h.x := by
      rw [mem_conjugate_iff]
      have : h.x * b * h.x⁻¹ = b := by
        calc h.x * b * h.x⁻¹ = h.x * (h.x⁻¹ * b * h.x) * h.x⁻¹ := by rw [h1]
          _ = b := by group
      rw [this]; exact hbB
    exact mem_bot.mp (h.inf_conjugate_x ▸ mem_inf.mpr ⟨hbB, hbx⟩)
  · exact h1

theorem centralizer_b_le {b : H} (hBb : h.B = zpowers b) (hb : orderOf b = 2)
    (hKa : conjugate h.K h.a = h.K) : centralizer ({b} : Set H) ≤ normalizer (h.K : Set H) := by
  have hWC : normalizer (h.B : Set H) = centralizer ({b} : Set H) := by
    ext y
    rw [hBb, mem_centralizer_singleton_iff]
    exact ⟨comm_of_mem_normalizer_zpowers hb, mem_normalizer_zpowers_of_comm⟩
  have hK : h.K = layerIn (centralizer ({b} : Set H)) := by
    rw [← h.toHyp52.V_eq_K hKa]
    show layerIn (normalizer (h.B : Set H)) = _
    rw [hWC]
  intro y hy
  rw [hK]
  exact mem_normalizer_layerIn hy

theorem card_center_oddBar_K (hB6 : SylowKernelStatement) (hKa : conjugate h.K h.a = h.K)
    (hB2 : Nat.card h.B = 2) (hZ : center (OddBar h.K) ≠ ⊥) :
    Nat.card (center (OddBar h.K)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := center (OddBar h.K) with hZdef
  have hO : pPrimeCore 2 (OddBar h.K) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hZ2 : IsPGroup 2 Z := by
    intro z
    obtain ⟨i, m, hm, him⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
    refine ⟨i, ?_⟩
    set w := z ^ 2 ^ i with hw
    have hwo : orderOf w = m := by
      rw [hw, orderOf_pow_of_dvd (by positivity) (by rw [him]; exact dvd_mul_right _ _), him,
        Nat.mul_div_cancel_left _ (by positivity)]
    have hwN : (zpowers ((w : Z) : OddBar h.K)).Normal := by
      constructor
      intro n hn g
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
      have hc := Subgroup.mem_center_iff.mp (zpow_mem w.2 k) g
      rw [hc, mul_inv_cancel_right]
      exact zpow_mem (mem_zpowers _) k
    have hcop : Nat.Coprime 2 (Nat.card (zpowers ((w : Z) : OddBar h.K))) := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hwo, Nat.coprime_two_left]
      exact hm
    have hle := LocalAnalysis.ComponentInitial.le_pPrimeCore hwN hcop
    rw [hO] at hle
    have hw1 : ((w : Z) : OddBar h.K) = 1 := mem_bot.mp (hle (mem_zpowers _))
    exact Subtype.ext hw1
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hZ2
  set π := QuotientGroup.mk' (pPrimeCore 2 h.K) with hπ
  set Zs : Subgroup h.K := Z.comap π with hZs
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hcardZs : Nat.card Zs = Nat.card Z * Nat.card (pPrimeCore 2 h.K) := by
    set f : Zs →* OddBar h.K := π.comp Zs.subtype with hf
    have hrange : f.range = Z := by
      apply le_antisymm
      · rintro _ ⟨k, rfl⟩
        exact k.2
      · intro z hz
        obtain ⟨y, rfl⟩ := hπsurj z
        exact ⟨⟨y, hz⟩, rfl⟩
    have hker : Nat.card f.ker = Nat.card (pPrimeCore 2 h.K) := by
      have hOZs : pPrimeCore 2 h.K ≤ Zs := by
        intro y hy
        show π y ∈ Z
        rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff y).mpr hy]
        exact one_mem _
      have hkeq : f.ker.map Zs.subtype = pPrimeCore 2 h.K := by
        ext y
        constructor
        · rintro ⟨k, hk, rfl⟩
          have hk' : k ∈ f.ker := hk
          rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
            QuotientGroup.eq_one_iff] at hk'
          exact hk'
        · intro hy
          refine ⟨⟨y, hOZs hy⟩, ?_, rfl⟩
          show (⟨y, hOZs hy⟩ : Zs) ∈ f.ker
          rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply]
          exact (QuotientGroup.eq_one_iff y).mpr hy
      calc Nat.card f.ker = Nat.card (f.ker.map Zs.subtype) :=
            (Subgroup.card_map_of_injective Zs.subtype_injective).symm
        _ = Nat.card (pPrimeCore 2 h.K) := by rw [hkeq]
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker]
  obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow 2 Zs))
  have hRcard : Nat.card R = Nat.card Z := by
    rw [Sylow.card_eq_multiplicity, hcardZs, hj]
    have hk0 : Nat.card (pPrimeCore 2 h.K) ≠ 0 := Nat.card_pos.ne'
    have hodd : ¬ 2 ∣ Nat.card (pPrimeCore 2 h.K) := fun h2 =>
      absurd (Nat.Coprime.coprime_dvd_right h2 (CFSG.pPrimeCore_coprime_card (p := 2)))
        (by norm_num)
    rw [Nat.factorization_mul (by positivity) hk0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hodd, add_zero]
  set R' : Subgroup H := ((R : Subgroup Zs).map Zs.subtype).map h.K.subtype with hR'
  have hR'card : Nat.card R' = Nat.card R := by
    rw [hR', Subgroup.card_map_of_injective h.K.subtype_injective,
      Subgroup.card_map_of_injective Zs.subtype_injective]
  have hR'C : R' ≤ coreActionKernel h.K := by
    rintro _ ⟨_, ⟨r, -, rfl⟩, rfl⟩
    have hrZ : π (r : h.K) ∈ Z := r.2
    rw [mem_coreActionKernel]
    refine ⟨le_normalizer (r : h.K).2, fun j hj => ?_⟩
    have hc := (Subgroup.mem_center_iff.mp hrZ (π ⟨j, hj⟩)).symm
    rw [← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at hc
    refine ⟨((r : h.K) * ⟨j, hj⟩)⁻¹ * (⟨j, hj⟩ * (r : h.K)), hc, ?_⟩
    simp only [subtype_apply, coe_mul, coe_inv]
    group
  have hR'2 : IsPGroup 2 R' :=
    (R.isPGroup'.map Zs.subtype).map h.K.subtype
  have h6 := hB6 H h.toHyp52
  rw [h.toHyp52.V_eq_K hKa] at h6
  obtain ⟨hBC, R₀, hR₀⟩ := h6
  have hcardB : Nat.card R' ≤ 2 := by
    obtain ⟨Q, hQ⟩ := (hR'2.comap_subtype (K := coreActionKernel h.K)).exists_le_sylow
    have hQcard : Nat.card (Q : Subgroup ↥(coreActionKernel h.K)) = 2 := by
      rw [Sylow.card_eq_multiplicity Q, ← Sylow.card_eq_multiplicity R₀, hR₀,
        ← Subgroup.card_map_of_injective (coreActionKernel h.K).subtype_injective,
        subgroupOf_map_subtype, inf_of_le_left hBC, hB2]
    have h3 : Nat.card (R'.subgroupOf (coreActionKernel h.K)) = Nat.card R' := by
      rw [← Subgroup.card_map_of_injective (coreActionKernel h.K).subtype_injective,
        subgroupOf_map_subtype, inf_of_le_left hR'C]
    rw [← h3, ← hQcard]
    exact Subgroup.card_le_of_le hQ
  have hZ1 : 1 < Nat.card Z := (Subgroup.one_lt_card_iff_ne_bot Z).mpr hZ
  rw [← hRcard, ← hR'card]
  rw [← hRcard, ← hR'card] at hZ1
  omega

theorem exists_cyclic_index_two (hB7 : EmbedsTQuotStatement) (hST : SuzukiTausskyInput)
    (hT : Nat.card (↥h.T ⧸ h.B.subgroupOf h.T) = 2) :
    ∃ C : Subgroup H, C ≤ h.P ∧ IsCyclic C ∧ Nat.card h.P ≤ 2 * Nat.card C := by
  rcases Nat.lt_or_ge (Nat.card h.P) 8 with h8 | h8
  · have hPT := h.P_eq_T_of_card_lt hB7 hT h8
    obtain ⟨b, -, -, hT4, -, -⟩ := h.index_two_structure hB7 hT
    refine ⟨zpowers h.a, zpowers_le.mpr h.toHyp52.a_mem_P, inferInstance, ?_⟩
    rw [Nat.card_zpowers, h.orderOf_a, hPT, hT4]
  · obtain ⟨p, -, hp, -, -, hc, -⟩ := h.presentation_of_index_two hB7 hST hT h8
    exact ⟨zpowers p, zpowers_le.mpr hp, inferInstance, by rw [Nat.card_zpowers, hc]⟩

theorem card_le_sixteen (hB7 : EmbedsTQuotStatement) (hST : SuzukiTausskyInput)
    (hT : Nat.card (↥h.T ⧸ h.B.subgroupOf h.T) = 2)
    (hAutJ : ∀ E : Subgroup (MulAut (OddBar h.J)), (∀ e ∈ E, e ^ 2 = 1) → Nat.card E ≤ 4)
    {A : Subgroup H} (hAS : A ≤ h.S) (hA2 : ∀ e ∈ A, e ^ 2 = 1) : Nat.card A ≤ 16 := by
  obtain ⟨C, hCP, hCc, hPC⟩ := h.exists_cyclic_index_two hB7 hST hT
  have hAP : Nat.card ↥(A ⊓ h.P) ≤ 4 :=
    card_le_four_of_sq_eq_one hCP hCc hPC inf_le_right (fun e he => hA2 e (mem_inf.mp he).1)
  have hAN : A ≤ normalizer (h.J : Set H) := hAS.trans h.toHyp52.S_le_normalizer
  set f : ↥A →* MulAut (OddBar h.J) := (oddBarConj h.J).comp (inclusion hAN) with hf
  have hrange : Nat.card f.range ≤ 4 := by
    apply hAutJ
    rintro _ ⟨y, rfl⟩
    rw [← map_pow]
    have : y ^ 2 = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hA2 _ y.2)
    rw [this, map_one]
  have hker : Nat.card f.ker ≤ Nat.card ↥(A ⊓ h.P) := by
    have hle : f.ker ≤ (A ⊓ h.P).subgroupOf A := by
      intro y hy
      rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply] at hy
      have hyC := mem_coreActionKernel_of_oddBarConj_eq_one hy
      rw [mem_subgroupOf]
      exact mem_inf.mpr ⟨y.2, mem_inf.mpr ⟨hAS y.2, hyC⟩⟩
    calc Nat.card f.ker ≤ Nat.card ((A ⊓ h.P).subgroupOf A) := Subgroup.card_le_of_le hle
      _ = Nat.card ↥(A ⊓ h.P) := by
        rw [← Subgroup.card_map_of_injective A.subtype_injective, subgroupOf_map_subtype,
          inf_of_le_left inf_le_left]
  have hcardA : Nat.card A = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  calc Nat.card A = Nat.card f.range * Nat.card f.ker := hcardA
    _ ≤ 4 * 4 := Nat.mul_le_mul hrange (hker.trans hAP)
    _ = 16 := by norm_num

end Hyp59

end CFSG.ComponentClassification.GSThmB
