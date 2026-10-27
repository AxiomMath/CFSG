module

public import CFSG.GH74.Generic.BProg.B1.Lift0
public import CFSG.GH74.GLS.TwoThin.Equivariance
public import CFSG.GH74.GLS.TwoThin.PumpData

public section

namespace CFSG.GH74.Generic.BProg.B2.SD.TwoA7Term

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.Generic CFSG.GH74.Generic.BProg
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isKGroupNative_barQ_centralizer (hG : IsKProperSimple G) {y : G} (hy : y ≠ 1) :
    IsKGroupNative (barQ ↥(centralizer ({y} : Set G))) := by
  have : IsSimpleGroup G := hG.1
  have hcen : center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hG.2.1
      have : a ∈ center G := h ▸ mem_top a
      exact hab (Subgroup.mem_center_iff.mp this b).symm
  have hne : centralizer ({y} : Set G) ≠ ⊤ := by
    intro htop
    apply hy
    have hyc : y ∈ center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ centralizer ({y} : Set G) := htop ▸ mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp this
    rw [hcen] at hyc
    exact Subgroup.mem_bot.mp hyc
  have h1 := hG.isKGroupNative_of_ne_top hne
  exact SectionRank.IsKGroupCat.quotient h1 _

theorem eq_one_of_two_pow_of_mem_pPrimeCore {X : Type*} [Group X] [Finite X] {z : X}
    (hz : z ∈ pPrimeCore 2 X) {n : ℕ} (hzn : z ^ (2 ^ n) = 1) : z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : orderOf z ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hzn
  have h2 : orderOf z ∣ Nat.card (pPrimeCore 2 X) := Subgroup.orderOf_dvd_natCard _ hz
  have h3 : orderOf z = 1 :=
    Nat.eq_one_of_dvd_coprimes ((pPrimeCore_coprime_card (p := 2) (G := X)).pow_left n) h1 h2
  exact orderOf_eq_one_iff.mp h3

omit [Finite G] in
theorem mem_of_isSylowOf_of_central {C Q : Subgroup G} (hQ : IsSylowOf 2 Q C) {z : G}
    (hzC : z ∈ C) (hz2 : orderOf z = 2) (hcen : ∀ c ∈ C, c * z = z * c) : z ∈ Q := by
  obtain ⟨S, hS⟩ := hQ
  have hzc : (⟨z, hzC⟩ : ↥C) ∈ Subgroup.center ↥C := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcen g g.2)
  have hN : (zpowers (⟨z, hzC⟩ : ↥C)).Normal := normal_of_le_center (zpowers_le.2 hzc)
  have hz2' : orderOf (⟨z, hzC⟩ : ↥C) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hz2
  have hp : IsPGroup 2 (zpowers (⟨z, hzC⟩ : ↥C)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2', pow_one])
  have hle := IsPGroup.le_sylow_of_normal hp S
  rw [← hS]
  exact ⟨⟨z, hzC⟩, hle (mem_zpowers _), rfl⟩

theorem barMk_eq_one_of_mem_pPrimeCoreOf {Y' K' : Subgroup G}
    (hK'Y : K' ≤ Y') (hsub : (K'.subgroupOf Y').IsSubnormal) {o : G}
    (ho : o ∈ pPrimeCoreOf 2 K') (hoY : o ∈ Y') : barMk ↥Y' ⟨o, hoY⟩ = 1 := by
  have h1 : o ∈ (pPrimeCoreOf 2 (K'.subgroupOf Y')).map Y'.subtype := by
    rw [← pPrimeCoreOf_eq_map_subgroupOf hK'Y]
    exact ho
  obtain ⟨o', ho', rfl⟩ := h1
  have h2 : o' ∈ pPrimeCore 2 ↥Y' := pPrimeCoreOf_le_of_subnormal 2 hsub ho'
  exact (QuotientGroup.eq_one_iff _).mpr h2

theorem barMk_restrict_eq_one {W Y' : Subgroup G} (hWY : W ≤ Y') {z : G} (hz : z ∈ W)
    (h : barMk ↥Y' ⟨z, hWY hz⟩ = 1) : barMk ↥W ⟨z, hz⟩ = 1 := by
  have hmem : (⟨z, hWY hz⟩ : ↥Y') ∈ pPrimeCore 2 ↥Y' := (QuotientGroup.eq_one_iff _).mp h
  let N : Subgroup ↥W := (pPrimeCore 2 ↥Y').comap (Subgroup.inclusion hWY)
  have hNn : N.Normal := (inferInstance : (pPrimeCore 2 ↥Y').Normal).comap _
  have hNc : Nat.Coprime 2 (Nat.card N) :=
    Nat.Coprime.coprime_dvd_right
      (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hWY))
      (pPrimeCore_coprime_card (p := 2) (G := ↥Y'))
  have hNle : N ≤ pPrimeCore 2 ↥W := le_sSup ⟨hNn, hNc⟩
  exact (QuotientGroup.eq_one_iff _).mpr (hNle hmem)

structure PumpTrivial (u y : G) (I K' : Subgroup G) : Prop where
  le : K' ≤ centralizer ({y} : Set G)
  normalizes : u ∈ normalizer (K' : Set G)
  hat : Nonempty ((↥K' ⧸ pPrimeCore 2 ↥K') ≃* (↥I ⧸ pPrimeCore 2 ↥I))
  equivariant : ∀ q ∈ CxK u I, y * q = q * y → q ∈ CxK y K'
  data : ∃ Λ : Subgroup G,
    IsPCompIn 2 (centralizer ({u} : Set G) ⊓ centralizer ({y} : Set G)) Λ ∧ Λ ≤ I ∧
      (∀ k ∈ I, ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 I, k = l * o) ∧
      (∀ z ∈ I ⊓ centralizer ({y} : Set G), (∃ n : ℕ, z ^ 2 ^ n = 1) → z ∈ Λ) ∧
      TwoComponents.IsTwoComponent (K'.subgroupOf (centralizer ({y} : Set G))) ∧
      (Λ.subgroupOf (centralizer ({y} : Set G))).map (barMk ↥(centralizer ({y} : Set G))) =
        (K'.subgroupOf (centralizer ({y} : Set G))).map (barMk ↥(centralizer ({y} : Set G)))

theorem conj_barMk_eq_of_mem_CxK {y : G} {K' : Subgroup G} (hK'Y : K' ≤ centralizer ({y} : Set G))
    (hsub : (K'.subgroupOf (centralizer ({y} : Set G))).IsSubnormal) {q : G}
    (hq : q ∈ CxK y K') :
    ∀ m ∈ K'.subgroupOf (centralizer ({y} : Set G)),
      barMk ↥(centralizer ({y} : Set G)) (⟨q, hq.1⟩ * m * ⟨q, hq.1⟩⁻¹) =
        barMk ↥(centralizer ({y} : Set G)) m := by
  intro m hm
  have hk : (m : G) ∈ K' := Subgroup.mem_subgroupOf.mp hm
  have hqs : q ∈ centralizerSection K' (pPrimeCoreOf 2 K') := hq.2
  have hqm : q * (m : G) * q⁻¹ * (m : G)⁻¹ ∈ pPrimeCoreOf 2 K' := by
    have := inv_mem (hqs.2.2 (m : G) hk)
    simpa [commutatorElement_def, mul_assoc] using this
  have hY : q * (m : G) * q⁻¹ * (m : G)⁻¹ ∈ centralizer ({y} : Set G) :=
    mul_mem (mul_mem (mul_mem hq.1 m.2) (inv_mem hq.1)) (inv_mem m.2)
  have h1 := barMk_eq_one_of_mem_pPrimeCoreOf hK'Y hsub hqm hY
  have h2 : (⟨q * (m : G) * q⁻¹ * (m : G)⁻¹, hY⟩ : ↥(centralizer ({y} : Set G))) =
      (⟨q, hq.1⟩ * m * ⟨q, hq.1⟩⁻¹) * m⁻¹ := rfl
  rw [h2, map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

theorem sylow_clause {u y : G} {I K' : Subgroup G} (hu2 : orderOf u = 2)
    (hIc : IsPCompIn 2 (centralizer ({u} : Set G)) I) (huI : u ∈ I)
    (hyu : y ∈ centralizer ({u} : Set G)) (htr : PumpTrivial u y I K')
    {Q : Subgroup G} (hQ : IsSylowOf 2 Q (CxK u I))
    (hyc : ∀ q ∈ Q, y * q = q * y) : IsSylowOf 2 Q (CxK y K') := by
  obtain ⟨Λ, hΛW, hΛI, hcovΛ, h2el, hK'2, hΛK'⟩ := htr.data
  set Y' := centralizer ({y} : Set G) with hY'
  have huY : u ∈ Y' := mem_centralizer_symm hyu
  have hK'Y : K' ≤ Y' := htr.le
  have hΛW1 := hΛW.1
  have hΛY : Λ ≤ Y' := hΛW1.trans inf_le_right
  have hK'sub : (K'.subgroupOf Y').IsSubnormal :=
    Components.mathlib_subnormal_of_chain hK'2.1 Subgroup.IsSubnormal.top
  have hIu : I ≤ centralizer ({u} : Set G) := hIc.1
  have hIc2 := (isPCompIn_two_iff.mp hIc).2
  have hIsub : (I.subgroupOf (centralizer ({u} : Set G))).IsSubnormal :=
    B1.isSubnormal_of_isPCompIn hIc
  have huC₁ : u ∈ CxK u I := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, ?_⟩
    refine ⟨Subgroup.le_normalizer huI, mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer huI), ?_⟩
    intro k hk
    have : k * u = u * k := Subgroup.mem_centralizer_singleton_iff.mp (hIu hk)
    rw [commutatorElement_eq_one_iff_mul_comm.mpr this]
    exact one_mem _
  have huQ : u ∈ Q := by
    refine mem_of_isSylowOf_of_central hQ huC₁ hu2 fun c hc => ?_
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).1
  have hQC₂ : Q ≤ CxK y K' := fun q hq => htr.equivariant q (hQ.le hq) (hyc q hq)
  have hQ2 : IsPGroup 2 ↥(Q.subgroupOf (CxK y K')) := hQ.isPGroup.comap_subtype
  obtain ⟨S, hS⟩ := hQ2.exists_le_sylow
  set Qs : Subgroup G := (S : Subgroup ↥(CxK y K')).map (CxK y K').subtype with hQs
  have hQsS : IsSylowOf 2 Qs (CxK y K') := ⟨S, rfl⟩
  have hQQs : Q ≤ Qs := fun q hq => ⟨⟨q, hQC₂ hq⟩, hS (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
  have key : Qs ≤ CxK u I := by
    intro q hq
    have hqC₂ : q ∈ CxK y K' := hQsS.le hq
    have hqY : q ∈ Y' := hqC₂.1
    have huQs : u ∈ Qs := hQQs huQ
    have hπK : ∀ z : ↥Y', barMk ↥Y' z ∈ (K'.subgroupOf Y').map (barMk ↥Y') →
        barMk ↥Y' (⟨q, hqY⟩ * z * ⟨q, hqY⟩⁻¹) = barMk ↥Y' z := by
      intro z hz
      obtain ⟨k, hk, hkz⟩ := hz
      have h1 := conj_barMk_eq_of_mem_CxK hK'Y hK'sub hqC₂ k hk
      rw [map_mul, map_mul, map_inv] at h1 ⊢
      rw [← hkz]
      exact h1
    have hu2' : u ^ (2 ^ 1) = 1 := by
      have := pow_orderOf_eq_one u
      rwa [hu2, ← pow_one 2] at this
    have huΛ : u ∈ Λ := h2el u (Subgroup.mem_inf.mpr ⟨huI, huY⟩) ⟨1, hu2'⟩
    have hu_in : barMk ↥Y' ⟨u, huY⟩ ∈ (K'.subgroupOf Y').map (barMk ↥Y') := by
      rw [← hΛK']
      exact ⟨⟨u, huY⟩, Subgroup.mem_subgroupOf.mpr huΛ, rfl⟩
    have hqU : q ∈ centralizer ({u} : Set G) := by
      have hcY : q * u * q⁻¹ * u⁻¹ ∈ Y' :=
        mul_mem (mul_mem (mul_mem hqY huY) (inv_mem hqY)) (inv_mem huY)
      have hc1 : barMk ↥Y' ⟨q * u * q⁻¹ * u⁻¹, hcY⟩ = 1 := by
        have h2 : (⟨q * u * q⁻¹ * u⁻¹, hcY⟩ : ↥Y') =
            (⟨q, hqY⟩ * ⟨u, huY⟩ * ⟨q, hqY⟩⁻¹) * ⟨u, huY⟩⁻¹ := rfl
        rw [h2, map_mul, map_inv, hπK _ hu_in, mul_inv_cancel]
      have hmem : (⟨q * u * q⁻¹ * u⁻¹, hcY⟩ : ↥Y') ∈ pPrimeCore 2 ↥Y' :=
        (QuotientGroup.eq_one_iff _).mp hc1
      have hcQs : q * u * q⁻¹ * u⁻¹ ∈ Qs :=
        mul_mem (mul_mem (mul_mem hq huQs) (inv_mem hq)) (inv_mem huQs)
      obtain ⟨n, hn⟩ := hQsS.isPGroup ⟨q * u * q⁻¹ * u⁻¹, hcQs⟩
      have hn' : (q * u * q⁻¹ * u⁻¹) ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
      have h1 := eq_one_of_two_pow_of_mem_pPrimeCore hmem (n := n) (Subtype.ext (by simpa using hn'))
      have h1' : q * u * q⁻¹ * u⁻¹ = 1 := congrArg Subtype.val h1
      have hqu : q * u = u * q := by
        calc q * u = (q * u * q⁻¹ * u⁻¹) * (u * q) := by group
          _ = u * q := by rw [h1', one_mul]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hqu
    set W := centralizer ({u} : Set G) ⊓ Y' with hW
    have hqW : q ∈ W := Subgroup.mem_inf.mpr ⟨hqU, hqY⟩
    have hWY : W ≤ Y' := inf_le_right
    have hπW : ∀ m ∈ Λ.subgroupOf W,
        barMk ↥W (⟨q, hqW⟩ * m * ⟨q, hqW⟩⁻¹) = barMk ↥W m := by
      intro m hm
      have hmΛ : (m : G) ∈ Λ := Subgroup.mem_subgroupOf.mp hm
      have hmY : (m : G) ∈ Y' := hWY m.2
      have hz : barMk ↥Y' ⟨m, hmY⟩ ∈ (K'.subgroupOf Y').map (barMk ↥Y') := by
        rw [← hΛK']
        exact ⟨⟨m, hmY⟩, Subgroup.mem_subgroupOf.mpr hmΛ, rfl⟩
      have h1 := hπK _ hz
      have hcW : q * (m : G) * q⁻¹ * (m : G)⁻¹ ∈ W :=
        mul_mem (mul_mem (mul_mem hqW m.2) (inv_mem hqW)) (inv_mem m.2)
      have h2 : barMk ↥Y' ⟨q * (m : G) * q⁻¹ * (m : G)⁻¹, hWY hcW⟩ = 1 := by
        have h3 : (⟨q * (m : G) * q⁻¹ * (m : G)⁻¹, hWY hcW⟩ : ↥Y') =
            (⟨q, hqY⟩ * ⟨m, hmY⟩ * ⟨q, hqY⟩⁻¹) * ⟨m, hmY⟩⁻¹ := rfl
        rw [h3, map_mul, map_inv, h1, mul_inv_cancel]
      have h4 := barMk_restrict_eq_one hWY hcW h2
      have h5 : (⟨q * (m : G) * q⁻¹ * (m : G)⁻¹, hcW⟩ : ↥W) =
          (⟨q, hqW⟩ * m * ⟨q, hqW⟩⁻¹) * m⁻¹ := rfl
      rw [h5, map_mul, map_inv, mul_inv_eq_one] at h4
      exact h4
    have hqΛ : q ∈ centralizerSection Λ (pPrimeCoreOf 2 Λ) :=
      mem_centralizerSection_of_map_eq hΛW1 (isPCompIn_two_iff.mp hΛW).2 hqW hπW
    have hker := ker_hatMap_eq_pPrimeCore hΛI hcovΛ
    have hlq : ∀ l ∈ Λ, q * l * q⁻¹ * l⁻¹ ∈ pPrimeCoreOf 2 I := by
      intro l hl
      have h1 : q * l * q⁻¹ * l⁻¹ ∈ pPrimeCoreOf 2 Λ := by
        have := inv_mem (hqΛ.2.2 l hl)
        simpa [commutatorElement_def, mul_assoc] using this
      obtain ⟨a, ha, haeq⟩ := h1
      have h2 : a ∈ (hatMap hΛI).ker := by rw [hker]; exact ha
      have h3 := (hatMap_eq_one_iff hΛI (a : ↥Λ)).mp (MonoidHom.mem_ker.mp h2)
      have haeq' : ((a : ↥Λ) : G) = q * l * q⁻¹ * l⁻¹ := haeq
      rw [haeq'] at h3
      exact h3
    have hπI : ∀ m ∈ I.subgroupOf (centralizer ({u} : Set G)),
        barMk ↥(centralizer ({u} : Set G)) (⟨q, hqU⟩ * m * ⟨q, hqU⟩⁻¹) =
          barMk ↥(centralizer ({u} : Set G)) m := by
      intro m hm
      have hmI : (m : G) ∈ I := Subgroup.mem_subgroupOf.mp hm
      obtain ⟨l, hl, o, ho, hmlo⟩ := hcovΛ m hmI
      have hlU : l ∈ centralizer ({u} : Set G) := hIu (hΛI hl)
      have hoU : o ∈ centralizer ({u} : Set G) := hIu (pPrimeCoreOf_le I ho)
      have hπo : barMk ↥(centralizer ({u} : Set G)) ⟨o, hoU⟩ = 1 :=
        barMk_eq_one_of_mem_pPrimeCoreOf hIu hIsub ho hoU
      have hcl : q * l * q⁻¹ * l⁻¹ ∈ pPrimeCoreOf 2 I := hlq l hl
      have hclU : q * l * q⁻¹ * l⁻¹ ∈ centralizer ({u} : Set G) :=
        mul_mem (mul_mem (mul_mem hqU hlU) (inv_mem hqU)) (inv_mem hlU)
      have hπc : barMk ↥(centralizer ({u} : Set G)) ⟨q * l * q⁻¹ * l⁻¹, hclU⟩ = 1 :=
        barMk_eq_one_of_mem_pPrimeCoreOf hIu hIsub hcl hclU
      have hm' : m = ⟨l, hlU⟩ * ⟨o, hoU⟩ := Subtype.ext hmlo
      have h3 : (⟨q * l * q⁻¹ * l⁻¹, hclU⟩ : ↥(centralizer ({u} : Set G))) =
          (⟨q, hqU⟩ * ⟨l, hlU⟩ * ⟨q, hqU⟩⁻¹) * ⟨l, hlU⟩⁻¹ := rfl
      rw [h3, map_mul, map_inv, mul_inv_eq_one] at hπc
      rw [hm']
      simp only [map_mul, map_inv, hπo, mul_one]
      simp only [map_mul, map_inv] at hπc
      exact hπc
    have hqI : q ∈ centralizerSection I (pPrimeCoreOf 2 I) :=
      mem_centralizerSection_of_map_eq hIu hIc2 hqU hπI
    exact Subgroup.mem_inf.mpr ⟨hqU, hqI⟩
  have hEq : Qs = Q := hQ.eq_of_le hQQs key hQsS.isPGroup
  rw [hEq] at hQsS
  exact hQsS

end CFSG.GH74.Generic.BProg.B2.SD.TwoA7Term
