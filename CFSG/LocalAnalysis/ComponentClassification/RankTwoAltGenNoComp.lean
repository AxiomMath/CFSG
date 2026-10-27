module

public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQ
import CFSG.Adapters.WholeGroupLayer

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalCores

section Transfer

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem eq_one_of_pow_odd {g : X} (hg : g * g = 1) {m : ℕ} (hm : Odd m) (h : g ^ m = 1) :
    g = 1 := by
  obtain ⟨k, rfl⟩ := hm
  have h2 : g ^ 2 = 1 := by rw [sq, hg]
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at h
  exact h

open scoped IsMulCommutative in
theorem notMem_commutator_of_mem_center {H : Subgroup X} (hH : IsMulCommutative H)
    (hodd : Odd H.index) {z : X} (hzc : z ∈ center X) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) : z ∉ commutator X := by
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite
  intro hzX
  set ϕ : H →* H := MonoidHom.id H
  have htr := MonoidHom.transfer_eq_pow ϕ z fun k g₀ _ => by
    rw [mul_assoc, ← (Subgroup.mem_center_iff.mp (pow_mem hzc k) g₀), ← mul_assoc,
      inv_mul_cancel, one_mul]
  have hker : z ∈ (MonoidHom.transfer ϕ).ker :=
    Abelianization.commutator_subset_ker (MonoidHom.transfer ϕ) hzX
  rw [MonoidHom.mem_ker, htr] at hker
  exact hz1 (eq_one_of_pow_odd hz2 hodd (congrArg Subtype.val hker))

open scoped IsMulCommutative in
omit [Finite X] in
theorem transfer_eq_pow_of_conj {A : Type*} [CommGroup A] {H : Subgroup X} [H.FiniteIndex]
    (ϕ : H →* A) {g : X} (hg : g ∈ H)
    (key : ∀ (k : ℕ) (g₀ : X) (h : g₀⁻¹ * g ^ k * g₀ ∈ H),
      ϕ ⟨g₀⁻¹ * g ^ k * g₀, h⟩ = ϕ ⟨g, hg⟩ ^ k) :
    ϕ.transfer g = ϕ ⟨g, hg⟩ ^ H.index := by
  classical
  let := H.fintypeQuotientOfFiniteIndex
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  simp only [key]
  rw [Finset.prod_pow_eq_pow_sum, ← Subgroup.index_eq_sum_minimalPeriod]

open scoped IsMulCommutative in
theorem le_of_index_two_of_perfect (hX : commutator X = ⊤) {H W : Subgroup X} (hWH : W ≤ H)
    (hodd : Odd H.index) (hW : ∀ h ∈ H, h * h = 1 ↔ h ∈ W)
    (h2 : ∀ a ∈ H, ∀ b ∈ H, a ∉ W → b ∉ W → a * b ∈ W) : H ≤ W := by
  classical
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite
  set W' : Subgroup H := W.subgroupOf H with hW'
  have hmemW' : ∀ a : H, a ∈ W' ↔ (a : X) ∈ W := fun a => mem_subgroupOf
  have hcos : ∀ a b : H, a⁻¹ * b ∈ W' ↔ ((a : X) ∈ W ↔ (b : X) ∈ W) := by
    intro a b
    rw [hmemW']
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · intro hab
      constructor
      · intro ha
        simpa using W.mul_mem ha hab
      · intro hb
        simpa using W.mul_mem hb (W.inv_mem hab)
    · intro hab
      by_cases ha : (a : X) ∈ W
      · exact W.mul_mem (W.inv_mem ha) (hab.mp ha)
      · have hb : (b : X) ∉ W := fun hb => ha (hab.mpr hb)
        exact h2 _ (inv_mem a.2) _ b.2 (fun h => ha (by simpa using W.inv_mem h)) hb
  have hW'n : W'.Normal := by
    refine ⟨fun w hw h => ?_⟩
    rw [hmemW'] at hw ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    by_cases hh : (h : X) ∈ W
    · exact W.mul_mem (W.mul_mem hh hw) (W.inv_mem hh)
    · have h1 : (h : X) * w ∉ W := fun h' => hh (by simpa using W.mul_mem h' (W.inv_mem hw))
      have h3 : (h : X)⁻¹ ∉ W := fun h' => hh (by simpa using W.inv_mem h')
      exact h2 _ (mul_mem h.2 (hWH hw)) _ (inv_mem h.2) h1 h3
  have hsq : ∀ a : H, (a : X) * a ∈ W := by
    intro a
    by_cases ha : (a : X) ∈ W
    · exact W.mul_mem ha ha
    · exact h2 _ a.2 _ a.2 ha ha
  have hex : ∀ u : H ⧸ W', u * u = 1 := by
    intro u
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective u
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, hmemW']
    exact hsq c
  have hcomm : IsMulCommutative (H ⧸ W') := by
    refine ⟨⟨fun u v => ?_⟩⟩
    have h1 := inv_eq_of_mul_eq_one_right (hex u)
    have h3 := inv_eq_of_mul_eq_one_right (hex v)
    have h4 := inv_eq_of_mul_eq_one_right (hex (u * v))
    calc u * v = (u * v)⁻¹ := h4.symm
      _ = v⁻¹ * u⁻¹ := mul_inv_rev _ _
      _ = v * u := by rw [h1, h3]
  set ϕ : H →* H ⧸ W' := QuotientGroup.mk' W' with hϕ
  have hϕeq : ∀ a b : H, ϕ a = ϕ b ↔ ((a : X) ∈ W ↔ (b : X) ∈ W) := fun a b => by
    rw [hϕ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hcos]
  intro h hh
  have htr := transfer_eq_pow_of_conj ϕ hh fun k g₀ hk => by
    rw [← map_pow, hϕeq]
    simp only [SubgroupClass.coe_pow]
    rw [← hW _ hk, ← hW _ (pow_mem hh k)]
    constructor
    · intro h1
      calc h ^ k * h ^ k = g₀ * (g₀⁻¹ * h ^ k * g₀ * (g₀⁻¹ * h ^ k * g₀)) * g₀⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · intro h1
      calc g₀⁻¹ * h ^ k * g₀ * (g₀⁻¹ * h ^ k * g₀) = g₀⁻¹ * (h ^ k * h ^ k) * g₀ := by group
        _ = 1 := by rw [h1]; group
  have hle := Abelianization.commutator_subset_ker (MonoidHom.transfer ϕ)
  rw [hX] at hle
  have hker := hle (mem_top h)
  rw [MonoidHom.mem_ker, htr, ← map_pow, hϕ, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, hmemW'] at hker
  have hpow : (h : X) ^ H.index ∈ W := by simpa using hker
  obtain ⟨m, hm⟩ := hodd
  rw [hm, pow_succ, pow_mul] at hpow
  have hm2 : ((h : X) ^ 2) ^ m ∈ W := pow_mem (by rw [sq]; exact hsq ⟨h, hh⟩) m
  simpa using W.mul_mem (W.inv_mem hm2) hpow

omit [Finite X] in
theorem eq_one_of_mem_odd_of_isPGroup {O P : Subgroup X} (hO : Odd (Nat.card O))
    (hP : IsPGroup 2 P) {x : X} (hxO : x ∈ O) (hxP : x ∈ P) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : Odd (orderOf x) := hO.of_dvd_nat (Subgroup.orderOf_dvd_natCard O hxO)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rcases j with _ | j
  · exact orderOf_eq_one_iff.mp (by simpa using hj)
  · rw [hj, pow_succ] at h2
    exact absurd (Nat.even_mul.mpr (Or.inr even_two)) (Nat.not_even_iff_odd.mpr h2)

end Transfer

theorem mem_zpowers_iff_of_mul_self {X : Type*} [Group X] {e x : X} (he : e * e = 1) :
    x ∈ zpowers e ↔ x = 1 ∨ x = e := by
  constructor
  · rintro ⟨k, rfl⟩
    have h2 : e ^ (2 : ℤ) = 1 := by rw [zpow_two, he]
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · left
      show e ^ k = 1
      rw [hm, zpow_mul, h2, one_zpow]
    · right
      show e ^ k = e
      rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

variable {G : Type} [Group G] [Finite G]

open scoped commutatorElement in
theorem qbarNoComponent_of (hGA : Asc76X.GoldschmidtTheoremA) {z : G} {S Q : Subgroup G}
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hS : IsSylowOf 2 S (centralizer ({z} : Set G)))
    (hQS : Q ≤ S) (hzQ : z ∈ Q) (hQ2 : ∀ x ∈ Q, x * x = 1)
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) (hQz : ∃ q ∈ Q, q ∉ zpowers z)
    (hcl : ∀ x ∈ Q, ∀ h ∈ centralizer ({z} : Set G), h⁻¹ * x * h ∈ S → h⁻¹ * x * h ∈ Q)
    (htrans : ∀ x ∈ Q, ∀ y ∈ Q, x ∉ zpowers z → y ∉ zpowers z →
      ∃ c ∈ centralizer ({z} : Set G), c ∈ normalizer (Q : Set G) ∧ c * x * c⁻¹ = y)
    (hP : ∀ P : Subgroup G, Q ≤ P → P ≤ S → (∀ x ∈ P, x * x ∈ zpowers z → x ∈ Q) →
      ∀ x ∈ P, ∀ y ∈ P, x ∉ Q → y ∉ Q → x * y ∈ Q) :
    AS81.QbarNoComponent z Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({z} : Set G) with hCdef
  obtain ⟨SC, hSC⟩ := hS
  have hSCle : S ≤ C := hSC ▸ map_subtype_le _
  have hQC : Q ≤ C := hQS.trans hSCle
  set zH : ↥C := AS81.zC z with hzH
  set N : Subgroup ↥C := zpowers zH with hNdef
  set π₀ := QuotientGroup.mk' N with hπ₀def
  have hπ₀ : Function.Surjective π₀ := QuotientGroup.mk'_surjective N
  have hker : π₀.ker = N := QuotientGroup.ker_mk' N
  set QH : Subgroup ↥C := Q.subgroupOf C with hQHdef
  have hNQ : N ≤ QH := zpowers_le.mpr (mem_subgroupOf.mpr hzQ)
  have hQHS : QH ≤ (SC : Subgroup ↥C) := by
    intro x hx
    have hxS : (x : G) ∈ S := hQS (mem_subgroupOf.mp hx)
    rw [← hSC] at hxS
    obtain ⟨y, hy, hyx⟩ := hxS
    rwa [← Subtype.ext hyx]
  have hNS : N ≤ (SC : Subgroup ↥C) := hNQ.trans hQHS
  have hmemN : ∀ x : ↥C, x ∈ N ↔ (x : G) ∈ zpowers z := fun x => AS81.mem_zpowers_zC
  let Sb : Sylow 2 (↥C ⧸ N) := SC.mapSurjective hπ₀
  have hSb : (Sb : Subgroup (↥C ⧸ N)) = (SC : Subgroup ↥C).map π₀ := Sylow.coe_mapSurjective _ _
  set Qb : Subgroup (↥C ⧸ N) := QH.map π₀ with hQbdef
  have hQbS : Qb ≤ Sb := by
    rw [hSb]
    exact map_mono hQHS
  have hQbab : IsMulCommutative Qb := by
    refine isMulCommutative_iff_of_setLike.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hQab _ (mem_subgroupOf.mp ha) _ (mem_subgroupOf.mp hb))
  have hclb : ∀ a ∈ Qb, ∀ g : ↥C ⧸ N, g⁻¹ * a * g ∈ (Sb : Subgroup (↥C ⧸ N)) →
      g⁻¹ * a * g ∈ Qb := by
    rintro _ ⟨a, ha, rfl⟩ g hg
    obtain ⟨h, rfl⟩ := hπ₀ g
    rw [← map_inv, ← map_mul, ← map_mul] at hg ⊢
    rw [hSb] at hg
    obtain ⟨s, hs, hse⟩ := hg
    have hmem : h⁻¹ * a * h ∈ (SC : Subgroup ↥C) := by
      have h1 : s⁻¹ * (h⁻¹ * a * h) ∈ N := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hse, inv_mul_cancel]
      have h2 := (SC : Subgroup ↥C).mul_mem hs (hNS h1)
      simpa [mul_assoc] using h2
    have hmemS : ((h⁻¹ * a * h : ↥C) : G) ∈ S := by
      rw [← hSC]
      exact ⟨_, hmem, rfl⟩
    refine ⟨h⁻¹ * a * h, mem_subgroupOf.mpr ?_, rfl⟩
    exact hcl _ (mem_subgroupOf.mp ha) _ h.2 hmemS
  obtain ⟨ha, hb, hc⟩ := hGA (↥C ⧸ N) Sb Qb hQbS hQbab hclb
  set M : Subgroup (↥C ⧸ N) := normalClosure (Qb : Set (↥C ⧸ N)) with hMdef
  change goldschmidtLayer (↥M ⧸ goldschmidtOddCore ↥M) = ⊥
  have hMn : M.Normal := normalClosure_normal
  have hQbM : Qb ≤ M := subset_normalClosure
  set π := QuotientGroup.mk' (goldschmidtOddCore ↥M) with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Yb : Subgroup (↥M ⧸ goldschmidtOddCore ↥M) := (Qb.subgroupOf M).map π with hYbdef
  set O2 := CFSG.Open.pCore 2 (↥M ⧸ goldschmidtOddCore ↥M) with hO2def
  have hO2Y : O2 ≤ Yb := by
    rw [hb]
    exact le_sup_left
  have hYbab : ∀ a ∈ Yb, ∀ b ∈ Yb, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (isMulCommutative_iff_of_setLike.mp hQbab _ ha _ hb')
  have hYb : ∀ y ∈ Yb, ∃ q ∈ Q, ∃ hqC : q ∈ C, ∃ hqM : π₀ ⟨q, hqC⟩ ∈ M,
      π ⟨π₀ ⟨q, hqC⟩, hqM⟩ = y := by
    rintro _ ⟨⟨_, hqM⟩, ⟨⟨q, hqC⟩, hq, rfl⟩, rfl⟩
    exact ⟨q, mem_subgroupOf.mp hq, hqC, hqM, rfl⟩
  have hconj : ∀ (c : G) (hcC : c ∈ C) (q : G) (hqC : q ∈ C) (hqM : π₀ ⟨q, hqC⟩ ∈ M)
      (hcqC : c * q * c⁻¹ ∈ C) (hcqM : π₀ ⟨c * q * c⁻¹, hcqC⟩ ∈ M),
      Asc76X.conjQuot hMn (π₀ ⟨c, hcC⟩) (π ⟨π₀ ⟨q, hqC⟩, hqM⟩) =
        π ⟨π₀ ⟨c * q * c⁻¹, hcqC⟩, hcqM⟩ := by
    intro c hcC q hqC hqM hcqC hcqM
    rw [hπdef, Asc76X.conjQuot_mk]
    congr 2
  have hO2 : O2 = ⊥ ∨ O2 = Yb := by
    by_cases hO : O2 = ⊥
    · exact Or.inl hO
    right
    refine le_antisymm hO2Y ?_
    obtain ⟨t, ht, ht1⟩ := (Subgroup.bot_or_exists_ne_one O2).resolve_left hO
    obtain ⟨q, hq, hqC, hqM, rfl⟩ := hYb t (hO2Y ht)
    have hqz : q ∉ zpowers z := by
      intro hqz
      apply ht1
      have h1 : π₀ ⟨q, hqC⟩ = 1 := by
        rw [← MonoidHom.mem_ker, hker, hmemN]
        exact hqz
      have h2 : (⟨π₀ ⟨q, hqC⟩, hqM⟩ : ↥M) = 1 := Subtype.ext h1
      rw [h2, map_one]
    intro y hy
    obtain ⟨q', hq', hq'C, hq'M, rfl⟩ := hYb y hy
    by_cases hq'z : q' ∈ zpowers z
    · have h1 : π₀ ⟨q', hq'C⟩ = 1 := by
        rw [← MonoidHom.mem_ker, hker, hmemN]
        exact hq'z
      have h2 : (⟨π₀ ⟨q', hq'C⟩, hq'M⟩ : ↥M) = 1 := Subtype.ext h1
      rw [h2, map_one]
      exact one_mem _
    obtain ⟨c, hcC, -, hcq⟩ := htrans q hq q' hq' hqz hq'z
    have hcqC : c * q * c⁻¹ ∈ C := by rw [hcq]; exact hq'C
    have hcqM : π₀ ⟨c * q * c⁻¹, hcqC⟩ ∈ M := by
      have : (⟨c * q * c⁻¹, hcqC⟩ : ↥C) = ⟨q', hq'C⟩ := Subtype.ext hcq
      rw [this]
      exact hq'M
    have h1 := hconj c hcC q hqC hqM hcqC hcqM
    have h2 : π ⟨π₀ ⟨c * q * c⁻¹, hcqC⟩, hcqM⟩ = π ⟨π₀ ⟨q', hq'C⟩, hq'M⟩ := by
      congr 3
      exact Subtype.ext hcq
    rw [← h2, ← h1, hO2def, ← Asc76X.openPCore_map_eq 2 (Asc76X.conjQuot hMn (π₀ ⟨c, hcC⟩))]
    exact ⟨_, ht, rfl⟩
  have hlayer : CFSG.Open.goldschmidtLayer (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) =
      CFSG.layer (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) :=
    CFSG.Adapters.goldschmidtLayer_eq_foundations _
  have hab_layer : (∀ a b : ↥M ⧸ goldschmidtOddCore ↥M, a * b = b * a) →
      CFSG.layer (↥M ⧸ goldschmidtOddCore ↥M) = ⊥ := by
    intro habE
    rw [← layer_perfect, eq_bot_iff]
    refine (commutator_le).mpr fun a _ b _ => ?_
    rw [commutatorElement_def, habE a b, mul_inv_cancel_right, mul_inv_cancel, mem_bot]
  rcases hO2 with hO | hO
  ·
    rw [hlayer]
    apply hab_layer
    have hLtop : goldschmidtLayer (↥M ⧸ goldschmidtOddCore ↥M) = ⊤ := by
      have h1 := ha
      rw [hO, bot_sup_eq] at h1
      exact h1
    have hperf : commutator (↥M ⧸ goldschmidtOddCore ↥M) = ⊤ := by
      have h1 := layer_perfect (G := ↥M ⧸ goldschmidtOddCore ↥M)
      rw [← hlayer, hLtop] at h1
      rw [commutator_def]
      exact h1
    have hSbtop : IsSylowOf 2 (Sb : Subgroup (↥C ⧸ N)) ⊤ := by
      rw [isSylowOf_iff]
      refine ⟨le_top, Sb.isPGroup', ?_⟩
      rw [relIndex_top_right]
      exact Sb.not_dvd_index
    obtain ⟨QM, hQM⟩ := hSbtop.inf_of_le_normalizer (le_top : M ≤ ⊤)
      (by rw [normalizer_eq_top_iff.mpr hMn])
    have hmemQM : ∀ m : ↥M, m ∈ (QM : Subgroup ↥M) ↔ (m : ↥C ⧸ N) ∈ (Sb : Subgroup _) := by
      intro m
      constructor
      · intro hm
        have h1 : (m : ↥C ⧸ N) ∈ (QM : Subgroup ↥M).map M.subtype := ⟨m, hm, rfl⟩
        rw [hQM] at h1
        exact h1.1
      · intro hm
        have h1 : (m : ↥C ⧸ N) ∈ (Sb : Subgroup _) ⊓ M := ⟨hm, m.2⟩
        rw [← hQM] at h1
        obtain ⟨m', hm', hmm'⟩ := h1
        rw [show m = m' from Subtype.ext hmm'.symm]
        exact hm'
    let Qbar : Sylow 2 (↥M ⧸ goldschmidtOddCore ↥M) := QM.mapSurjective hπs
    have hQbar : (Qbar : Subgroup _) = (QM : Subgroup ↥M).map π := Sylow.coe_mapSurjective _ _
    have hTQ : ((Sb : Subgroup (↥C ⧸ N)).subgroupOf M).map π = (Qbar : Subgroup _) := by
      rw [hQbar]
      congr 1
      ext m
      exact (hmemQM m).symm
    have hYbT : Yb = Subgroup.closure {t : ↥M ⧸ goldschmidtOddCore ↥M |
        t ∈ (Qbar : Subgroup _) ∧ t ^ 2 = 1} := by
      have h1 := hb
      rw [hO, bot_sup_eq, hLtop, inf_top_eq, hTQ] at h1
      exact h1
    have hYbsq : ∀ t ∈ Yb, t * t = 1 := by
      intro t ht
      obtain ⟨q, hq, hqC, hqM, rfl⟩ := hYb t ht
      rw [← map_mul]
      have h1 : (⟨π₀ ⟨q, hqC⟩, hqM⟩ : ↥M) * ⟨π₀ ⟨q, hqC⟩, hqM⟩ = 1 := by
        apply Subtype.ext
        show π₀ ⟨q, hqC⟩ * π₀ ⟨q, hqC⟩ = 1
        rw [← map_mul]
        have h2 : (⟨q, hqC⟩ : ↥C) * ⟨q, hqC⟩ = 1 := Subtype.ext (hQ2 q hq)
        rw [h2, map_one]
      rw [h1, map_one]
    have hW : ∀ t ∈ (Qbar : Subgroup _), t * t = 1 ↔ t ∈ Yb := by
      intro t ht
      refine ⟨fun h => ?_, hYbsq t⟩
      rw [hYbT]
      exact subset_closure ⟨ht, by rw [sq]; exact h⟩
    have hYbQ : Yb ≤ (Qbar : Subgroup _) := by
      rintro _ ⟨m, hm, rfl⟩
      rw [hQbar]
      exact ⟨m, (hmemQM m).mpr (hQbS hm), rfl⟩
    have hinjQM : ∀ m ∈ (QM : Subgroup ↥M), ∀ m' ∈ (QM : Subgroup ↥M), π m = π m' → m = m' := by
      intro m hm m' hm' hmm'
      have hk : m'⁻¹ * m ∈ goldschmidtOddCore ↥M := by
        rw [← QuotientGroup.ker_mk' (goldschmidtOddCore ↥M), MonoidHom.mem_ker, map_mul, map_inv,
          ← hπdef, hmm', inv_mul_cancel]
      have h1 : m'⁻¹ * m = 1 := eq_one_of_mem_odd_of_isPGroup
        (CFSG.ComponentClassification.OddCore.odd_card ↥M) QM.isPGroup' hk
        (mul_mem (inv_mem hm') hm)
      exact (inv_mul_eq_one.mp h1).symm
    set P : Subgroup G := ((SC : Subgroup ↥C) ⊓ M.comap π₀).map C.subtype with hPdef
    have hQP : Q ≤ P := fun q hq => ⟨⟨q, hQC hq⟩, ⟨hQHS (mem_subgroupOf.mpr hq),
      hQbM ⟨⟨q, hQC hq⟩, mem_subgroupOf.mpr hq, rfl⟩⟩, rfl⟩
    have hPS : P ≤ S := by
      rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
      rw [← hSC]
      exact ⟨x, hx, rfl⟩
    have hmemQM' : ∀ x : ↥C, x ∈ (SC : Subgroup ↥C) → ∀ hxM : π₀ x ∈ M,
        (⟨π₀ x, hxM⟩ : ↥M) ∈ (QM : Subgroup ↥M) :=
      fun x hx hxM => (hmemQM _).mpr (by rw [hSb]; exact ⟨x, hx, rfl⟩)
    have hQofQb : ∀ x : ↥C, π₀ x ∈ Qb → (x : G) ∈ Q := by
      intro x ⟨q, hq, hqx⟩
      have hqx' : q⁻¹ * x ∈ N := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hqx, inv_mul_cancel]
      have h1 := QH.mul_mem hq (hNQ hqx')
      rw [mul_inv_cancel_left] at h1
      exact mem_subgroupOf.mp h1
    have hPΩ : ∀ x ∈ P, x * x ∈ zpowers z → x ∈ Q := by
      rintro _ ⟨x, ⟨hxS, hxM⟩, rfl⟩ hxx
      have hmQ := hmemQM' x hxS hxM
      have hmm : (⟨π₀ x, hxM⟩ : ↥M) * ⟨π₀ x, hxM⟩ = 1 := by
        apply Subtype.ext
        show π₀ x * π₀ x = 1
        rw [← map_mul, ← MonoidHom.mem_ker, hker, hmemN]
        exact hxx
      have hπQ : π ⟨π₀ x, hxM⟩ ∈ (Qbar : Subgroup _) := by
        rw [hQbar]
        exact ⟨_, hmQ, rfl⟩
      have hπm : π ⟨π₀ x, hxM⟩ ∈ Yb := (hW _ hπQ).mp (by rw [← map_mul, hmm, map_one])
      obtain ⟨m', hm', hmm'⟩ := hπm
      have hm'Q : m' ∈ (QM : Subgroup ↥M) := (hmemQM m').mpr (hQbS hm')
      have heq := hinjQM _ hmQ _ hm'Q hmm'.symm
      apply hQofQb x
      have : ((⟨π₀ x, hxM⟩ : ↥M) : ↥C ⧸ N) ∈ Qb := by rw [heq]; exact hm'
      exact this
    have hidx := hP P hQP hPS hPΩ
    have h2 : ∀ a ∈ (Qbar : Subgroup _), ∀ b ∈ (Qbar : Subgroup _), a ∉ Yb → b ∉ Yb →
        a * b ∈ Yb := by
      intro a ha b hb' haY hbY
      rw [hQbar] at ha hb'
      obtain ⟨m, hm, rfl⟩ := ha
      obtain ⟨m', hm', rfl⟩ := hb'
      have hmS : (m : ↥C ⧸ N) ∈ (SC : Subgroup ↥C).map π₀ := by rw [← hSb]; exact (hmemQM m).mp hm
      have hm'S : (m' : ↥C ⧸ N) ∈ (SC : Subgroup ↥C).map π₀ := by
        rw [← hSb]; exact (hmemQM m').mp hm'
      obtain ⟨x, hx, hxm⟩ := hmS
      obtain ⟨x', hx', hxm'⟩ := hm'S
      have hxP : (x : G) ∈ P := ⟨x, ⟨hx, by show π₀ x ∈ M; rw [hxm]; exact m.2⟩, rfl⟩
      have hx'P : (x' : G) ∈ P := ⟨x', ⟨hx', by show π₀ x' ∈ M; rw [hxm']; exact m'.2⟩, rfl⟩
      have hxQ : (x : G) ∉ Q := fun h => haY ⟨m, by
        show (m : ↥C ⧸ N) ∈ Qb
        rw [← hxm]; exact ⟨x, mem_subgroupOf.mpr h, rfl⟩, rfl⟩
      have hx'Q : (x' : G) ∉ Q := fun h => hbY ⟨m', by
        show (m' : ↥C ⧸ N) ∈ Qb
        rw [← hxm']; exact ⟨x', mem_subgroupOf.mpr h, rfl⟩, rfl⟩
      have hxx' := hidx _ hxP _ hx'P hxQ hx'Q
      refine ⟨m * m', ?_, map_mul _ _ _⟩
      show (m : ↥C ⧸ N) * m' ∈ Qb
      rw [← hxm, ← hxm', ← map_mul]
      exact ⟨x * x', mem_subgroupOf.mpr hxx', rfl⟩
    have hQY : (Qbar : Subgroup _) ≤ Yb := le_of_index_two_of_perfect hperf hYbQ
      (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp Qbar.not_dvd_index)) hW h2
    have hQMQ : ∀ m ∈ (QM : Subgroup ↥M), (m : ↥C ⧸ N) ∈ Qb := by
      intro m hm
      obtain ⟨m', hm', hmm'⟩ := hQY (by rw [hQbar]; exact ⟨m, hm, rfl⟩ : π m ∈ (Qbar : Subgroup _))
      have hm'Q : m' ∈ (QM : Subgroup ↥M) := (hmemQM m').mpr (hQbS hm')
      rw [hinjQM _ hm _ hm'Q hmm'.symm]
      exact hm'
    have hQbodd : Odd (Qb.relIndex M) := by
      have heq : Qb.subgroupOf M = (QM : Subgroup ↥M) :=
        le_antisymm (fun m hm => (hmemQM m).mpr (hQbS hm)) (fun m hm => hQMQ m hm)
      show Odd (Qb.subgroupOf M).index
      rw [heq]
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp QM.not_dvd_index)
    set M₀ : Subgroup ↥C := M.comap π₀ with hM₀
    have hM₀n : M₀.Normal := hMn.comap π₀
    have hQHM₀ : QH ≤ M₀ := fun q hq => hQbM ⟨q, hq, rfl⟩
    have hzM₀ : zH ∈ M₀ := hQHM₀ (hNQ (mem_zpowers _))
    have hQHeq : QH = Qb.comap π₀ := by
      rw [hQbdef, comap_map_eq, hker, sup_eq_left.mpr hNQ]
    have hrel : Odd (QH.relIndex M₀) := by
      rw [hQHeq, hM₀, relIndex_comap, map_comap_eq_self_of_surjective hπ₀]
      exact hQbodd
    have hzc : ∀ h : ↥C, h * zH = zH * h := fun h =>
      Subtype.ext (mem_centralizer_singleton_iff.mp h.2)
    set zM : ↥M₀ := ⟨zH, hzM₀⟩ with hzM
    have hzMc : zM ∈ center ↥M₀ :=
      Subgroup.mem_center_iff.mpr fun h => Subtype.ext (hzc h)
    have hzM2 : zM * zM = 1 := Subtype.ext (Subtype.ext hz2)
    have hzM1 : zM ≠ 1 := fun h => hz1 (congrArg (fun x : ↥M₀ => ((x : ↥C) : G)) h)
    have hH₀ab : IsMulCommutative (QH.subgroupOf M₀) := by
      refine ⟨⟨fun a b => Subtype.ext (Subtype.ext (Subtype.ext ?_))⟩⟩
      exact hQab _ (mem_subgroupOf.mp (mem_subgroupOf.mp a.2)) _
        (mem_subgroupOf.mp (mem_subgroupOf.mp b.2))
    have hzK := notMem_commutator_of_mem_center hH₀ab hrel hzMc hzM2 hzM1
    set K₁ : Subgroup ↥C := ⁅M₀, M₀⁆ with hK₁
    have hK₁n : K₁.Normal := Subgroup.commutator_normal M₀ M₀
    have hK₁eq : (commutator ↥M₀).map M₀.subtype = K₁ := M₀.map_subtype_commutator
    have hzK₁ : zH ∉ K₁ := by
      rw [← hK₁eq]
      rintro ⟨k, hk, hkz⟩
      have : k = zM := Subtype.ext hkz
      exact hzK (this ▸ hk)
    have hK₁Q : ∀ q ∈ Q, ∀ hqC : q ∈ C, (⟨q, hqC⟩ : ↥C) ∈ K₁ → q = 1 := by
      intro q hq hqC hqK
      by_contra hq1
      have hqz : q ∉ zpowers z := by
        rw [mem_zpowers_iff_of_mul_self hz2]
        rintro (h | h)
        · exact hq1 h
        · subst h
          exact hzK₁ hqK
      have hyQ : q * z ∈ Q := mul_mem hq hzQ
      have hyz : q * z ∉ zpowers z := by
        rw [mem_zpowers_iff_of_mul_self hz2]
        rintro (h | h)
        · apply hqz
          rw [mem_zpowers_iff_of_mul_self hz2]
          right
          calc q = q * z * z := by rw [mul_assoc, hz2, mul_one]
            _ = z := by rw [h, one_mul]
        · apply hq1
          calc q = q * z * z⁻¹ := by group
            _ = 1 := by rw [h, mul_inv_cancel]
      obtain ⟨c, hcC, -, hcq⟩ := htrans q hq (q * z) hyQ hqz hyz
      have h1 : (⟨c, hcC⟩ : ↥C) * ⟨q, hqC⟩ * (⟨c, hcC⟩ : ↥C)⁻¹ ∈ K₁ :=
        hK₁n.conj_mem _ hqK _
      have h2 : (⟨q, hqC⟩ : ↥C)⁻¹ * ((⟨c, hcC⟩ : ↥C) * ⟨q, hqC⟩ * (⟨c, hcC⟩ : ↥C)⁻¹) = zH := by
        apply Subtype.ext
        show q⁻¹ * (c * q * c⁻¹) = z
        rw [hcq]
        group
      exact hzK₁ (h2 ▸ mul_mem (inv_mem hqK) h1)
    have hQH2 : IsPGroup 2 QH := fun x => ⟨1, by
      apply Subtype.ext
      apply Subtype.ext
      simp only [pow_one, sq, Subgroup.coe_mul, OneMemClass.coe_one]
      exact hQ2 _ (mem_subgroupOf.mp x.2)⟩
    have hQHsyl : IsSylowOf 2 QH M₀ := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [isSylowOf_iff]
      exact ⟨hQHM₀, hQH2, fun h => (Nat.not_even_iff_odd.mpr hrel) (even_iff_two_dvd.mpr h)⟩
    have hK₁M₀ : K₁ ≤ M₀ := Subgroup.commutator_le_left M₀ M₀
    have hsylK := hQHsyl.inf_of_le_normalizer hK₁M₀
      (by rw [normalizer_eq_top_iff.mpr hK₁n]; exact le_top)
    have hbot : QH ⊓ K₁ = ⊥ := by
      rw [eq_bot_iff]
      intro x ⟨hxQ, hxK⟩
      rw [mem_bot]
      exact Subtype.ext (hK₁Q _ (mem_subgroupOf.mp hxQ) x.2 hxK)
    have hK₁odd : Odd (Nat.card K₁) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h1 := hsylK.card_eq
      rw [hbot, card_bot] at h1
      have h2 : (Nat.card K₁).factorization 2 = 0 := by
        have := (Nat.pow_eq_one.mp h1.symm)
        rcases this with h | h
        · exact absurd h (by norm_num)
        · exact h
      rw [Nat.factorization_eq_zero_iff] at h2
      rcases h2 with h | h | h
      · exact absurd Nat.prime_two h
      · exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)
      · exact absurd h Nat.card_pos.ne'
    set ψ : ↥M₀ →* ↥M ⧸ goldschmidtOddCore ↥M :=
      π.comp ((π₀.comp M₀.subtype).codRestrict M fun x => x.2) with hψ
    have hψs : Function.Surjective ψ := by
      intro a
      obtain ⟨m, rfl⟩ := hπs a
      obtain ⟨c, hc⟩ := hπ₀ (m : ↥C ⧸ N)
      refine ⟨⟨c, show π₀ c ∈ M by rw [hc]; exact m.2⟩, ?_⟩
      show π _ = π m
      congr 1
      exact Subtype.ext hc
    set L := (commutator ↥M₀).map ψ with hL
    have hLn : L.Normal := (commutator_normal ⊤ ⊤).map ψ hψs
    have hLodd : Odd (Nat.card L) := by
      have h1 := card_map_dvd (H := commutator ↥M₀) ψ
      have h2 : Nat.card (commutator ↥M₀) = Nat.card K₁ := by
        rw [← hK₁eq, card_map_of_injective M₀.subtype_injective]
      rw [h2] at h1
      exact hK₁odd.of_dvd_nat h1
    have hLbot : L = ⊥ := by
      rw [eq_bot_iff]
      calc L ≤ CFSG.oddCore (↥M ⧸ goldschmidtOddCore ↥M) := le_sSup ⟨hLn, hLodd⟩
        _ = ⊥ := Asc76X.oddCore_quotient_oddCore ↥M
    intro a b
    obtain ⟨x, rfl⟩ := hψs a
    obtain ⟨y, rfl⟩ := hψs b
    have h1 : ψ ⁅x, y⁆ ∈ L := ⟨_, commutator_mem_commutator (mem_top x) (mem_top y), rfl⟩
    rw [hLbot, mem_bot, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  ·
    rw [hlayer]
    apply hab_layer
    set X : Subgroup (↥C ⧸ N) := (O2.comap π).map M.subtype with hXdef
    have hXn : X.Normal := by
      refine ⟨fun x hx g => ?_⟩
      obtain ⟨m, hm, rfl⟩ := hx
      have h1 : (Asc76X.conjQuot hMn g) (π m) ∈ O2 := by
        rw [hO2def, ← Asc76X.openPCore_map_eq 2 (Asc76X.conjQuot hMn g)]
        exact ⟨π m, hm, rfl⟩
      rw [hπdef, Asc76X.conjQuot_mk] at h1
      exact ⟨⟨g * m * g⁻¹, hMn.conj_mem m m.2 g⟩, h1, rfl⟩
    have hQbX : Qb ≤ X := by
      intro q hq
      refine ⟨⟨q, hQbM hq⟩, ?_, rfl⟩
      show π ⟨q, hQbM hq⟩ ∈ O2
      rw [hO]
      exact ⟨⟨q, hQbM hq⟩, hq, rfl⟩
    have hMX : M ≤ X := normalClosure_le_normal hQbX
    have hO2top : ∀ e : ↥M ⧸ goldschmidtOddCore ↥M, e ∈ O2 := by
      intro e
      obtain ⟨m, rfl⟩ := hπs e
      obtain ⟨m', hm', hmm'⟩ := hMX m.2
      have : m' = m := Subtype.ext hmm'
      rw [← this]
      exact hm'
    intro a b
    have ha' : a ∈ Yb := hO ▸ hO2top a
    have hb' : b ∈ Yb := hO ▸ hO2top b
    exact hYbab a ha' b hb'

end CFSG.ComponentClassification.RankTwoAlt
