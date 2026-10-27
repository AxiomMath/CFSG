module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitQuotientChain
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTypeRank

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_coreActionKernel {K : Subgroup G} {g x : G} (hg : g ∈ normalizer (K : Set G))
    (hx : x ∈ coreActionKernel K) : g * x * g⁻¹ ∈ coreActionKernel K := by
  refine ⟨mul_mem (mul_mem hg hx.1) (inv_mem hg), fun j hj => ?_⟩
  have hj' : g⁻¹ * j * g ∈ K := by
    have h := (mem_normalizer_iff.mp (inv_mem hg) j).mp hj
    rwa [inv_inv] at h
  have h1 := hx.2 _ hj'
  have h2 := (mem_normalizer_iff.mp (mem_normalizer_oddCoreIn hg) _).mp h1
  rw [show g * ((g⁻¹ * j * g)⁻¹ * x⁻¹ * (g⁻¹ * j * g) * x) * g⁻¹ =
    j⁻¹ * (g * x * g⁻¹)⁻¹ * j * (g * x * g⁻¹) by group] at h2
  exact h2

omit [Finite G] in
theorem mem_normalizer_coreActionKernel {K : Subgroup G} {g : G}
    (hg : g ∈ normalizer (K : Set G)) :
    g ∈ normalizer ((coreActionKernel K : Subgroup G) : Set G) :=
  mem_normalizer_iff.mpr fun x => ⟨fun hx => conj_mem_coreActionKernel hg hx, fun hx => by
    have h := conj_mem_coreActionKernel (inv_mem hg) hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h⟩

omit [Finite G] in
theorem mem_coreActionKernel_conjugate {J : Subgroup G} {g x : G}
    (hx : g * x * g⁻¹ ∈ coreActionKernel J) : x ∈ coreActionKernel (conjugate J g) := by
  refine ⟨mem_normalizer_iff.mpr fun y => ?_, fun j hj => ?_⟩
  · rw [mem_conjugate_iff, mem_conjugate_iff]
    have h := mem_normalizer_iff.mp hx.1 (g * y * g⁻¹)
    rw [show g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * (x * y * x⁻¹) * g⁻¹ by group]
      at h
    exact h
  · rw [mem_conjugate_iff] at hj
    have h := hx.2 _ hj
    rw [show (g * j * g⁻¹)⁻¹ * (g * x * g⁻¹)⁻¹ * (g * j * g⁻¹) * (g * x * g⁻¹) =
      g * (j⁻¹ * x⁻¹ * j * x) * g⁻¹ by group] at h
    show _ ∈ (pPrimeCore 2 ↥(J.map (MulAut.conj g⁻¹).toMonoidHom)).map
      (J.map (MulAut.conj g⁻¹).toMonoidHom).subtype
    rw [← GSLit.map_map_pPrimeCore]
    refine ⟨g * (j⁻¹ * x⁻¹ * j * x) * g⁻¹, h, ?_⟩
    change g⁻¹ * (g * (j⁻¹ * x⁻¹ * j * x) * g⁻¹) * g⁻¹⁻¹ = _
    group

theorem mem_coreActionKernel_of_le {J T : Subgroup G} {d : G} (hTJ : T ≤ J)
    (hdT : d ∈ normalizer (T : Set G)) (hd : d ∈ coreActionKernel J) :
    d ∈ coreActionKernel T := by
  refine ⟨hdT, fun t ht => ?_⟩
  have hle : T ⊓ oddCoreIn J ≤ oddCoreIn T :=
    le_oddCoreIn inf_le_left (fun x hx => mem_normalizer_inf' (le_normalizer hx)
      (mem_normalizer_oddCoreIn (le_normalizer (hTJ hx))))
      (Odd.of_dvd_nat (odd_card_oddCoreIn J) (card_dvd_of_le inf_le_right))
  refine hle (mem_inf.mpr ⟨?_, hd.2 t (hTJ ht)⟩)
  have h1 : d⁻¹ * t * d ∈ T := by
    have h := (mem_normalizer_iff.mp (inv_mem hdT) t).mp ht
    rwa [inv_inv] at h
  rw [show t⁻¹ * d⁻¹ * t * d = t⁻¹ * (d⁻¹ * t * d) by group]
  exact mul_mem (inv_mem ht) h1

theorem oddCoreIn_le_of_sup {T K : Subgroup G} (hTK : T ≤ K) (hsup : T ⊔ oddCoreIn K = K) :
    oddCoreIn T ≤ oddCoreIn K := by
  set N := oddCoreIn T ⊔ oddCoreIn K with hN
  have hOTK : oddCoreIn T ≤ normalizer ((oddCoreIn K : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_oddCoreIn (le_normalizer (hTK (map_subtype_le _ hx)))
  have hNodd : Odd (Nat.card N) :=
    odd_card_sup_of_le_normalizer hOTK (odd_card_oddCoreIn T) (odd_card_oddCoreIn K)
  have hNK : N ≤ K := sup_le ((map_subtype_le _).trans hTK) (map_subtype_le _)
  have hTN : T ≤ normalizer (N : Set G) := fun x hx =>
    mem_normalizer_sup (mem_normalizer_oddCoreIn (le_normalizer hx))
      (mem_normalizer_oddCoreIn (le_normalizer (hTK hx)))
  have hON : oddCoreIn K ≤ normalizer (N : Set G) := le_normalizer_sup_of_le_normalizer hOTK
  have hKN : K ≤ normalizer (N : Set G) := by
    rw [← hsup]
    exact sup_le hTN hON
  exact le_sup_left.trans (le_oddCoreIn hNK hKN hNodd)

theorem mem_coreActionKernel_of_sup {T K : Subgroup G} {d : G} (hTK : T ≤ K)
    (hsup : T ⊔ oddCoreIn K = K) (hdK : d ∈ normalizer (K : Set G))
    (hd : d ∈ coreActionKernel T) : d ∈ coreActionKernel K := by
  refine ⟨hdK, fun x hx => ?_⟩
  have hTO : T ≤ normalizer ((oddCoreIn K : Subgroup G) : Set G) := fun y hy =>
    mem_normalizer_oddCoreIn (le_normalizer (hTK hy))
  rw [← hsup, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right T (oddCoreIn K) hTO]
    at hx
  obtain ⟨t, ht, o, ho, rfl⟩ := hx
  have h1 : t⁻¹ * d⁻¹ * t * d ∈ oddCoreIn K := oddCoreIn_le_of_sup hTK hsup (hd.2 t ht)
  have h2 : d⁻¹ * o * d ∈ oddCoreIn K := by
    have h := (mem_normalizer_iff.mp (mem_normalizer_oddCoreIn (inv_mem hdK)) o).mp ho
    rwa [inv_inv] at h
  rw [show (t * o)⁻¹ * d⁻¹ * (t * o) * d = o⁻¹ * (t⁻¹ * d⁻¹ * t * d) * (d⁻¹ * o * d) by group]
  exact mul_mem (mul_mem (inv_mem ho) h1) h2

theorem mem_coreActionKernel_iff_of_common_odd_cover {D L K : Subgroup G} {d : G}
    (hDL : D ≤ L) (hDK : D ≤ K) (hsupL : D ⊔ oddCoreIn L = L)
    (hsupK : D ⊔ oddCoreIn K = K) (hdL : d ∈ normalizer (L : Set G))
    (hdK : d ∈ normalizer (K : Set G)) (hdD : d ∈ normalizer (D : Set G)) :
    d ∈ coreActionKernel L ↔ d ∈ coreActionKernel K :=
  ⟨fun hd => mem_coreActionKernel_of_sup hDK hsupK hdK
      (mem_coreActionKernel_of_le hDL hdD hd),
    fun hd => mem_coreActionKernel_of_sup hDL hsupL hdL
      (mem_coreActionKernel_of_le hDK hdD hd)⟩

theorem mem_coreActionKernel_of_sup_conjugate {J J' T : Subgroup G} {d : G}
    (hJ'J : J' ≤ normalizer (J : Set G)) (hJJ' : J ≤ normalizer (J' : Set G))
    (hT : T ≤ J ⊔ J') (hdT : d ∈ normalizer (T : Set G)) (hdJ : d ∈ coreActionKernel J)
    (hdJ' : d ∈ coreActionKernel J') : d ∈ coreActionKernel T := by
  set N := oddCoreIn J ⊔ oddCoreIn J' with hN
  have hNodd : Odd (Nat.card N) :=
    odd_card_sup_of_le_normalizer
      (fun x hx => mem_normalizer_oddCoreIn (hJJ' (map_subtype_le _ hx)))
      (odd_card_oddCoreIn J) (odd_card_oddCoreIn J')
  have hJN : J ≤ normalizer (N : Set G) := fun x hx =>
    mem_normalizer_sup (mem_normalizer_oddCoreIn (le_normalizer hx))
      (mem_normalizer_oddCoreIn (hJJ' hx))
  have hJ'N : J' ≤ normalizer (N : Set G) := fun x hx =>
    mem_normalizer_sup (mem_normalizer_oddCoreIn (hJ'J hx))
      (mem_normalizer_oddCoreIn (le_normalizer hx))
  have hTN : T ≤ normalizer ((T ⊓ N : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_inf' (le_normalizer hx) (sup_le hJN hJ'N (hT hx))
  have hle : T ⊓ N ≤ oddCoreIn T :=
    le_oddCoreIn inf_le_left hTN (Odd.of_dvd_nat hNodd (card_dvd_of_le inf_le_right))
  refine ⟨hdT, fun t ht => hle (mem_inf.mpr ⟨?_, ?_⟩)⟩
  · have h1 : d⁻¹ * t * d ∈ T := by
      have h := (mem_normalizer_iff.mp (inv_mem hdT) t).mp ht
      rwa [inv_inv] at h
    rw [show t⁻¹ * d⁻¹ * t * d = t⁻¹ * (d⁻¹ * t * d) by group]
    exact mul_mem (inv_mem ht) h1
  · have ht' := hT ht
    rw [sup_comm, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right J' J hJ'J] at ht'
    obtain ⟨j', hj', j, hj, rfl⟩ := ht'
    have h1 : j'⁻¹ * d⁻¹ * j' * d ∈ oddCoreIn J' := hdJ'.2 j' hj'
    have h2 : j⁻¹ * (j'⁻¹ * d⁻¹ * j' * d) * j ∈ oddCoreIn J' := by
      have h := (mem_normalizer_iff.mp (mem_normalizer_oddCoreIn (inv_mem (hJJ' hj))) _).mp h1
      rwa [inv_inv] at h
    have h3 : j⁻¹ * d⁻¹ * j * d ∈ oddCoreIn J := hdJ.2 j hj
    rw [show (j' * j)⁻¹ * d⁻¹ * (j' * j) * d =
      (j⁻¹ * (j'⁻¹ * d⁻¹ * j' * d) * j) * (j⁻¹ * d⁻¹ * j * d) by group]
    exact mul_mem (mem_sup_right h2) (mem_sup_left h3)

theorem le_coreActionKernel_of_commutator_le {H K : Subgroup G} {b : G}
    (hHK : H ≤ normalizer (K : Set G)) (hKb : K ≤ centralizer ({b} : Set G))
    (h : ⁅H, K⁆ ≤ oddCoreOfCentralizer b) : H ≤ coreActionKernel K := by
  have hle : K ⊓ oddCoreOfCentralizer b ≤ oddCoreIn K :=
    le_oddCoreIn inf_le_left (fun x hx => mem_normalizer_inf' (le_normalizer hx)
      (mem_normalizer_oddCoreOfCentralizer (hKb hx)))
      (Odd.of_dvd_nat (odd_card_oddCoreOfCentralizer b) (card_dvd_of_le inf_le_right))
  intro x hx
  refine ⟨hHK hx, fun j hj => hle (mem_inf.mpr ⟨?_, ?_⟩)⟩
  · have h1 : x⁻¹ * j * x ∈ K := by
      have h := (mem_normalizer_iff.mp (inv_mem (hHK hx)) j).mp hj
      rwa [inv_inv] at h
    rw [show j⁻¹ * x⁻¹ * j * x = j⁻¹ * (x⁻¹ * j * x) by group]
    exact mul_mem (inv_mem hj) h1
  · have h1 : ⁅j⁻¹, x⁻¹⁆ ∈ ⁅K, H⁆ := commutator_mem_commutator (inv_mem hj) (inv_mem hx)
    rw [commutator_comm] at h1
    have h2 := h h1
    rwa [commutatorElement_def, inv_inv, inv_inv] at h2

theorem le_coreActionKernel_of_balance (hLB : FooteLBalanceInput) {a b : G}
    (ha : orderOf a = 2) (hab : a * b = b * a) {Y : Subgroup G}
    (hYb : Y ≤ centralizer ({b} : Set G))
    (hY : IsPComponent 2 (Y.subgroupOf (centralizer ({b} : Set G))))
    (h : conjugate Y a ≠ Y ∨ a ∈ coreActionKernel Y) :
    oddCoreOfCentralizer a ⊓ centralizer ({b} : Set G) ≤ coreActionKernel Y := by
  set C := centralizer ({b} : Set G) with hC
  have haC : a ∈ C := mem_centralizer_singleton_iff.mpr hab
  set a' : C := ⟨a, haC⟩ with ha'def
  have ha' : orderOf a' = 2 := by rw [Subgroup.orderOf_mk]; exact ha
  obtain ⟨hN, hcent⟩ := hLB _ a' ha' _ hY
  have hcond : conjugate (Y.subgroupOf C) a' ≠ Y.subgroupOf C ∨
      ∀ x ∈ Y.subgroupOf C, x⁻¹ * a'⁻¹ * x * a' ∈
        (pPrimeCore 2 (Y.subgroupOf C)).map (Y.subgroupOf C).subtype := by
    rcases h with h | h
    · left
      intro h'
      apply h
      rw [conjugate_subgroupOf_eq] at h'
      have hle : conjugate Y a ≤ C := conjugate_le_of_mem hYb haC
      have h'' := (Subgroup.subgroupOf_inj).mp h'
      rwa [inf_of_le_left hle, inf_of_le_left hYb] at h''
    · right
      exact ((mem_coreActionKernel_subgroupOf_iff hYb a').mpr h).2
  have hW := hcent hcond
  intro x hx
  obtain ⟨x', hx', rfl⟩ := mem_map.mp (oddCoreOfCentralizer_inf_le C a' hx)
  refine (mem_coreActionKernel_subgroupOf_iff hYb x').mp ⟨hN hx', fun j hj => ?_⟩
  have h1 : ⁅j⁻¹, x'⁻¹⁆ ∈ ⁅Y.subgroupOf C, oddCoreOfCentralizer a'⁆ :=
    commutator_mem_commutator (inv_mem hj) (inv_mem hx')
  rw [commutator_comm] at h1
  have h2 := hW h1
  rwa [commutatorElement_def, inv_inv, inv_inv] at h2

theorem commutator_le_coreActionKernel_of_inf_centralizer {Y K : Subgroup G} {k : G}
    (hY : Odd (Nat.card Y)) (hYK : Y ≤ normalizer (K : Set G))
    (hkY : k ∈ normalizer (Y : Set G)) (hk : orderOf k = 2) (hkK : k ∈ coreActionKernel K)
    (h : ⁅Y ⊓ centralizer ({k} : Set G), Y ⊓ centralizer ({k} : Set G)⁆ ≤ coreActionKernel K) :
    ⁅Y, Y⁆ ≤ coreActionKernel K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Y ⊓ coreActionKernel K with hN
  have hNodd : ¬ 2 ∣ Nat.card N := fun h2 =>
    (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hY (card_dvd_of_le inf_le_left)))
      (even_iff_two_dvd.mpr h2)
  have hkp : IsPGroup 2 (zpowers k) := isPGroup_zpowers_of_orderOf hk
  have hkN : zpowers k ≤ normalizer (N : Set G) := (zpowers_le).mpr
    (mem_normalizer_inf' hkY (mem_normalizer_coreActionKernel hkK.1))
  have hcov : ∀ y ∈ Y, ∃ c ∈ Y ⊓ centralizer ({k} : Set G), c⁻¹ * y ∈ coreActionKernel K := by
    intro y hy
    obtain ⟨n, hn, hyn⟩ := exists_mul_mem_centralizer hkp hNodd hkN (y := y) (fun u hu => by
      have huK : u ∈ coreActionKernel K := (zpowers_le.mpr hkK) hu
      have huY : u ∈ normalizer (Y : Set G) := (zpowers_le.mpr hkY) hu
      refine mem_inf.mpr ⟨mul_mem (inv_mem hy) ((mem_normalizer_iff.mp huY y).mp hy), ?_⟩
      have h1 : y⁻¹ * u * y ∈ coreActionKernel K := by
        have h := conj_mem_coreActionKernel (inv_mem (hYK hy)) huK
        rwa [inv_inv] at h
      rw [show y⁻¹ * (u * y * u⁻¹) = (y⁻¹ * u * y) * u⁻¹ by group]
      exact mul_mem h1 (inv_mem huK))
    refine ⟨y * n, mem_inf.mpr ⟨mul_mem hy (mem_inf.mp hn).1, ?_⟩, ?_⟩
    · rw [← centralizer_zpowers_eq]; exact hyn
    · rw [show (y * n)⁻¹ * y = n⁻¹ by group]; exact inv_mem (mem_inf.mp hn).2
  rw [commutator_le]
  intro y₁ hy₁ y₂ hy₂
  obtain ⟨c₁, hc₁, hm₁⟩ := hcov y₁ hy₁
  obtain ⟨c₂, hc₂, hm₂⟩ := hcov y₂ hy₂
  have hcc : ⁅c₁, c₂⁆ ∈ coreActionKernel K := h (commutator_mem_commutator hc₁ hc₂)
  have hc₁K : c₁ ∈ normalizer (K : Set G) := hYK (mem_inf.mp hc₁).1
  have hc₂K : c₂ ∈ normalizer (K : Set G) := hYK (mem_inf.mp hc₂).1
  set m₁ := c₁⁻¹ * y₁ with hm₁def
  set m₂ := c₂⁻¹ * y₂ with hm₂def
  have e₁ : y₁ = c₁ * m₁ := by rw [hm₁def]; group
  have e₂ : y₂ = c₂ * m₂ := by rw [hm₂def]; group
  have hA : c₁ * m₁ * c₁⁻¹ ∈ coreActionKernel K := conj_mem_coreActionKernel hc₁K hm₁
  have hB : c₂ * m₂ * c₂⁻¹ ∈ coreActionKernel K := conj_mem_coreActionKernel hc₂K hm₂
  have hg : c₁ * c₂ * c₁⁻¹ ∈ normalizer (K : Set G) :=
    mul_mem (mul_mem hc₁K hc₂K) (inv_mem hc₁K)
  rw [e₁, e₂, show ⁅c₁ * m₁, c₂ * m₂⁆ = (c₁ * m₁ * c₁⁻¹) * (c₁ * (c₂ * m₂ * c₂⁻¹) * c₁⁻¹) *
      ((c₁ * c₂ * c₁⁻¹) * (c₁ * m₁ * c₁⁻¹)⁻¹ * (c₁ * c₂ * c₁⁻¹)⁻¹) * ⁅c₁, c₂⁆ *
      (c₂ * m₂ * c₂⁻¹)⁻¹ by rw [commutatorElement_def, commutatorElement_def]; group]
  exact mul_mem (mul_mem (mul_mem (mul_mem hA (conj_mem_coreActionKernel hc₁K hB))
    (conj_mem_coreActionKernel hg (inv_mem hA))) hcc) (inv_mem hB)

theorem exists_involution_central_of_le_normalizer {S N : Subgroup G} (hS : IsPGroup 2 S)
    (hSN : S ≤ normalizer (N : Set G)) (hne : S ⊓ N ≠ ⊥) :
    ∃ u : G, u ∈ S ∧ u ∈ N ∧ orderOf u = 2 ∧ ∀ s ∈ S, s * u = u * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent S := hS.isNilpotent
  have hSSN : S ≤ normalizer ((S ⊓ N : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_inf' (le_normalizer hx) (hSN hx)
  have : ((S ⊓ N).subgroupOf S).Normal :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hSSN
  have hM : (S ⊓ N).subgroupOf S ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hmem : (⟨x, (mem_inf.mp hx).1⟩ : S) ∈ (S ⊓ N).subgroupOf S := mem_subgroupOf.mpr hx
    rw [h, mem_bot] at hmem
    rw [mem_bot]
    exact congrArg Subtype.val hmem
  have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hM
  have hZp : IsPGroup 2 ↥((S ⊓ N).subgroupOf S ⊓ center S) := hS.to_subgroup _
  rcases hZp.card_eq_or_dvd with h1 | h2
  · exact absurd (Subgroup.card_eq_one.mp h1) h
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hyN := mem_subgroupOf.mp (mem_inf.mp y.2).1
  refine ⟨((y : S) : G), (y : S).2, (mem_inf.mp hyN).2, ?_, fun s hs => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
  · exact congrArg Subtype.val (mem_center_iff.mp (mem_inf.mp y.2).2 ⟨s, hs⟩)

theorem exists_involution_commute {N : Subgroup G} {a : G} (ha : orderOf a = 2)
    (haN : a ∈ normalizer (N : Set G)) (h2 : 2 ∣ Nat.card N) :
    ∃ u ∈ N, orderOf u = 2 ∧ a * u = u * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := N ⊔ zpowers a with hH
  have haH : a ∈ H := mem_sup_right (mem_zpowers a)
  have hHN : H ≤ normalizer (N : Set G) := sup_le le_normalizer ((zpowers_le).mpr haN)
  have hP0 : IsPGroup 2 ((zpowers a).subgroupOf H) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_congr (subgroupOfEquivOfLe ((zpowers_le).mpr haH)).toEquiv, Nat.card_zpowers,
      ha, pow_one]
  obtain ⟨P, hP⟩ := hP0.exists_le_sylow
  set S := (P : Subgroup H).map H.subtype with hS
  have hSp : IsPGroup 2 S := by
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := k)
      (by rw [Subgroup.card_map_of_injective H.subtype_injective, hk])
  have haS : a ∈ S := ⟨⟨a, haH⟩, hP (mem_subgroupOf.mpr (mem_zpowers a)), rfl⟩
  have hSN : S ≤ normalizer (N : Set G) := (map_subtype_le _).trans hHN
  have hne : S ⊓ N ≠ ⊥ := by
    have : (N.subgroupOf H).Normal :=
      (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hHN
    obtain ⟨Q, hQ⟩ := Glauberman.sylow_inf_normal P (N := N.subgroupOf H)
    have hQne : (Q : Subgroup (N.subgroupOf H)) ≠ ⊥ := Q.ne_bot_of_dvd_card (by
      rw [Nat.card_congr (subgroupOfEquivOfLe (le_sup_left : N ≤ H)).toEquiv]
      exact h2)
    intro hbot
    apply hQne
    rw [hQ, eq_bot_iff]
    intro x hx
    rw [mem_subgroupOf] at hx
    obtain ⟨hxP, hxN⟩ := mem_inf.mp hx
    have hx1 : (((x : N.subgroupOf H) : H) : G) ∈ S ⊓ N :=
      mem_inf.mpr ⟨⟨_, hxP, rfl⟩, mem_subgroupOf.mp hxN⟩
    rw [hbot, mem_bot] at hx1
    rw [mem_bot]
    exact Subtype.ext (Subtype.ext hx1)
  obtain ⟨u, -, huN, hu, hcomm⟩ := exists_involution_central_of_le_normalizer hSp hSN hne
  exact ⟨u, huN, hu, hcomm a haS⟩

theorem two_dvd_card_inf_coreActionKernel {K : Subgroup G}
    (hZ : center (K ⧸ pPrimeCore 2 K) ≠ ⊥) : 2 ∣ Nat.card ↥(K ⊓ coreActionKernel K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZp := isPGroup_center_quotient_pPrimeCore ↥K
  rcases hZp.card_eq_or_dvd with h1 | h2
  · exact absurd (Subgroup.card_eq_one.mp h1) hZ
  obtain ⟨⟨zq, hzq⟩, hzo⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective zq
  have hzK : (z : G) ∈ K ⊓ coreActionKernel K := by
    refine mem_inf.mpr ⟨z.2, le_normalizer z.2, fun j hj => ?_⟩
    have hc := mem_center_iff.mp hzq (QuotientGroup.mk (⟨j, hj⟩ : K))
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hc
    have h1 := (mem_pPrimeCore_iff_mem_oddCoreIn _).mp (inv_mem hc)
    rw [show ((((⟨j, hj⟩ : K) * z)⁻¹ * (z * ⟨j, hj⟩))⁻¹ : K) =
      (⟨j, hj⟩ : K)⁻¹ * z⁻¹ * ⟨j, hj⟩ * z by group] at h1
    exact h1
  have hord : 2 ∣ orderOf (⟨(z : G), hzK⟩ : ↥(K ⊓ coreActionKernel K)) := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
    have h1 := orderOf_map_dvd (QuotientGroup.mk' (pPrimeCore 2 K)) z
    rw [Subgroup.orderOf_mk] at hzo
    rw [QuotientGroup.mk'_apply, hzo] at h1
    exact h1
  exact hord.trans (orderOf_dvd_natCard _)

omit [Finite G] in
theorem footeFamilyType_of_lieModel {B : Subgroup G} {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (h : Blueprint.LieModel (B ⧸ Open.fusionZStar B) .PSL 2 p f) :
    FooteFamilyType B := by
  obtain ⟨⟨-, -, -, -, h23⟩, -⟩ := statedClassicalModel_of_lieModel_psl_two h
  refine Or.inr ⟨p, f, hp, hp2, hf, ?_, h⟩
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h3 : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow (by omega) p)
  have hne3 : p ^ f ≠ 3 := fun h' => h23 (by rw [h'])
  obtain ⟨m, hm⟩ := hodd
  omega

omit [Finite G] in
theorem mem_oddCoreIn_of_mem_coreActionKernel {J : Subgroup G}
    (hZ : center (J ⧸ pPrimeCore 2 J) = ⊥) {x : G} (hxJ : x ∈ J) (hx : x ∈ coreActionKernel J) :
    x ∈ oddCoreIn J := by
  have hmem : (QuotientGroup.mk (⟨x, hxJ⟩ : J) : J ⧸ pPrimeCore 2 J) ∈
      center (J ⧸ pPrimeCore 2 J) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    set y' : J := ⟨y, hy⟩
    set x' : J := ⟨x, hxJ⟩
    have h1 : y'⁻¹ * x'⁻¹ * y' * x' ∈ pPrimeCore 2 ↥J :=
      (mem_pPrimeCore_iff_mem_oddCoreIn (y'⁻¹ * x'⁻¹ * y' * x')).mpr (hx.2 y hy)
    have h2 := inv_mem h1
    rwa [show (y'⁻¹ * x'⁻¹ * y' * x')⁻¹ = (y' * x')⁻¹ * (x' * y') by group] at h2
  rw [hZ, mem_bot, QuotientGroup.eq_one_iff] at hmem
  exact (mem_pPrimeCore_iff_mem_oddCoreIn _).mp hmem

omit [Finite G] in
theorem center_quotient_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : center (X ⧸ pPrimeCore 2 X) = ⊥) : center (Y ⧸ pPrimeCore 2 Y) = ⊥ := by
  set e' := UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e
  rw [eq_bot_iff]
  intro z hz
  have h1 : e'.symm z ∈ center (X ⧸ pPrimeCore 2 X) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e'.symm.surjective g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hz g']
  rw [h, mem_bot] at h1
  rw [mem_bot]
  have h2 := congrArg e' h1
  rwa [MulEquiv.apply_symm_apply, map_one] at h2

theorem center_ne_bot_of_mem_sup {k : G} (hk : orderOf k = 2) {J J' : Subgroup G}
    (hJ : IsTwoComponentAt k J) (hJ' : IsTwoComponentAt k J') (hne : J ≠ J')
    (hZ' : center (J ⧸ pPrimeCore 2 J) = ⊥ → center (J' ⧸ pPrimeCore 2 J') = ⊥)
    (hkJJ : k ∈ J ⊔ J') : center (J ⧸ pPrimeCore 2 J) ≠ ⊥ := by
  intro hZ
  have hZ'' := hZ' hZ
  have hJ'J : J' ≤ coreActionKernel J :=
    GSThmB.B5a.le_coreActionKernel_of_ne hJ.2.1 hJ'.2.1 hJ.2.2 hJ'.2.2 hne
  have hJJ' : J ≤ coreActionKernel J' :=
    GSThmB.B5a.le_coreActionKernel_of_ne hJ'.2.1 hJ.2.1 hJ'.2.2 hJ.2.2 (Ne.symm hne)
  have hkC : k ∈ coreActionKernel J := GSLit.mem_coreActionKernel_of_le_centralizer hJ.2.1
  have hkC' : k ∈ coreActionKernel J' := GSLit.mem_coreActionKernel_of_le_centralizer hJ'.2.1
  rw [sup_comm, ← SetLike.mem_coe,
    coe_mul_of_left_le_normalizer_right J' J (fun x hx => (hJ'J hx).1)] at hkJJ
  obtain ⟨j', hj', j, hj, hkjj⟩ := hkJJ
  have hj'C : j' ∈ coreActionKernel J' := by
    rw [show j' = k * j⁻¹ by rw [← hkjj]; group]
    exact mul_mem hkC' (inv_mem (hJJ' hj))
  have hjC : j ∈ coreActionKernel J := by
    rw [show j = j'⁻¹ * k by rw [← hkjj]; group]
    exact mul_mem (inv_mem (hJ'J hj')) hkC
  have hj'O := mem_oddCoreIn_of_mem_coreActionKernel hZ'' hj' hj'C
  have hjO := mem_oddCoreIn_of_mem_coreActionKernel hZ hj hjC
  have hodd : Odd (Nat.card ↥(oddCoreIn J' ⊔ oddCoreIn J)) :=
    odd_card_sup_of_le_normalizer
      (fun x hx => mem_normalizer_oddCoreIn ((hJ'J (map_subtype_le _ hx)).1))
      (odd_card_oddCoreIn J') (odd_card_oddCoreIn J)
  have hkmem : k ∈ oddCoreIn J' ⊔ oddCoreIn J := by
    rw [← hkjj]
    exact mul_mem (mem_sup_left hj'O) (mem_sup_right hjO)
  have h1 := odd_orderOf_of_mem_of_odd hodd hkmem
  rw [hk] at h1
  exact absurd h1 (by decide)

end CFSG.ComponentClassification.FooteLit
