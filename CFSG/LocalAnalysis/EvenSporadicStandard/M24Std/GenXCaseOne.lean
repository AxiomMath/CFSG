module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CaseOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.GenXLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.GenXTransfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Input

public section

namespace CFSG.EvenSporadicStandard.M24Std.GenX

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}

namespace LS

variable (hs : LS G L z) {U : Subgroup G}

include hs in
theorem z_le_centralizer_U (hUL : U ≤ L) : zpowers z ≤ centralizer (U : Set G) :=
  hs.z_central.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hUL))

include hs in
theorem card_T (hUL : U ≤ L) : Nat.card (U ⊔ zpowers z : Subgroup G) = Nat.card U * 2 := by
  have e := mulEquivProdSup (hs.z_le_centralizer_U hUL) (hs.disjoint.mono_left hUL)
  rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zpowers, hs.order_z]

include hs in
theorem isPGroup_T (hUL : U ≤ L) (hUp : IsPGroup 2 U) :
    IsPGroup 2 (U ⊔ zpowers z : Subgroup G) := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hUp
  exact IsPGroup.of_card (n := k + 1) (by rw [hs.card_T hUL, hk, pow_succ])

include hs in
theorem mem_T (hUL : U ≤ L) {t : G} (ht : t ∈ U ⊔ zpowers z) :
    ∃ u ∈ U, t = u ∨ t = u * z := by
  obtain ⟨u, hu, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (hs.z_le_centralizer_U hUL) ht
  rcases hs.eq_one_or_eq_z hb with rfl | rfl
  · exact ⟨u, hu, Or.inl (mul_one u)⟩
  · exact ⟨u, hu, Or.inr rfl⟩

include hs in
theorem mem_of_mem_T_of_mem_L (hUL : U ≤ L) {t : G} (ht : t ∈ U ⊔ zpowers z) (htL : t ∈ L) :
    t ∈ U := by
  obtain ⟨u, hu, h | h⟩ := hs.mem_T hUL ht
  · rw [h]
    exact hu
  · exfalso
    apply hs.z_not_mem
    have : z = u⁻¹ * t := by rw [h]; group
    rw [this]
    exact L.mul_mem (L.inv_mem (hUL hu)) htL

include hs in
theorem T_le_centralizer (hUL : U ≤ L) : U ⊔ zpowers z ≤ centralizer ({z} : Set G) := by
  rw [hs.centralizer_eq]
  exact sup_le_sup_right hUL _

include hs in
theorem two_dvd_index_T (hUL : U ≤ L) : 2 ∣ (U ⊔ zpowers z : Subgroup G).index := by
  by_contra h
  have hrel : U.relIndex (U ⊔ zpowers z) = 2 := by
    have h1 := Subgroup.card_mul_index (U.subgroupOf (U ⊔ zpowers z))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : U ≤ U ⊔ zpowers z)).toEquiv,
      hs.card_T hUL] at h1
    have hpos : 0 < Nat.card U := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  obtain ⟨ψ, hψ⟩ := exists_hom_neg hs.mul_self_z h hrel fun g hg => by
    apply hs.conj_not_mem g⁻¹
    rw [inv_inv]
    exact hUL hg
  rw [hs.hom_z ψ] at hψ
  exact absurd hψ (by decide)

include hs in
theorem exists_normalizer_not_mem (hUL : U ≤ L) (hUp : IsPGroup 2 U) :
    ∃ n : G, n ∈ normalizer ((U ⊔ zpowers z : Subgroup G) : Set G) ∧
      n ∉ (U ⊔ zpowers z : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := U ⊔ zpowers z with hT
  have hTp := hs.isPGroup_T hUL hUp
  obtain ⟨S, hTS⟩ := hTp.exists_le_sylow
  have hne : T ≠ (S : Subgroup G) := by
    intro h
    have h1 := hs.two_dvd_index_T hUL
    rw [← hT, h] at h1
    exact Sylow.not_dvd_index S h1
  have hlt : T.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    exact hne (le_antisymm hTS (Subgroup.subgroupOf_eq_top.1 h))
  have : Group.IsNilpotent S := (S.isPGroup').isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥S)
  obtain ⟨x, hx, hxn⟩ := IsConcreteLE.exists_of_lt (hnc _ hlt)
  refine ⟨(x : G), ?_, ?_⟩
  · refine Subgroup.mem_normalizer_iff.2 fun h => ?_
    by_cases hhS : h ∈ (S : Subgroup G)
    · have := Subgroup.mem_normalizer_iff.1 hx ⟨h, hhS⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at this
      exact this
    · constructor
      · intro hhT
        exact absurd (hTS hhT) hhS
      · intro hh
        have h1 : (x : G) * h * (x : G)⁻¹ ∈ (S : Subgroup G) := hTS hh
        have h2 := S.mul_mem (S.mul_mem (S.inv_mem x.2) h1) x.2
        have e : (x : G)⁻¹ * ((x : G) * h * (x : G)⁻¹) * x = h := by group
        rw [e] at h2
        exact absurd h2 hhS
  · rwa [Subgroup.mem_subgroupOf] at hxn

include hs in
theorem mem_of_mem_L_normalizer_T
    (hUL : U ≤ L) (hUp : IsPGroup 2 U) (hUi : ¬ 2 ∣ (U.subgroupOf L).index) {m : G} (hmL : m ∈ L)
    (hmN : m ∈ normalizer ((U ⊔ zpowers z : Subgroup G) : Set G)) : m ∈ U := by
  have key : ∀ m : G, m ∈ L → m ∈ normalizer ((U ⊔ zpowers z : Subgroup G) : Set G) →
      ∀ u ∈ U, m * u * m⁻¹ ∈ U := by
    intro m hmL hmN u hu
    have h1 : m * u * m⁻¹ ∈ U ⊔ zpowers z :=
      (Subgroup.mem_normalizer_iff.1 hmN u).1 (Subgroup.mem_sup_left hu)
    exact hs.mem_of_mem_T_of_mem_L hUL h1 (L.mul_mem (L.mul_mem hmL (hUL hu)) (L.inv_mem hmL))
  refine mem_of_mem_normalizer_sylow hs.sporadic hUL hUp hUi hmL ?_
  refine Subgroup.mem_normalizer_iff.2 fun u => ⟨key m hmL hmN u, fun hu => ?_⟩
  have := key m⁻¹ (L.inv_mem hmL) (Subgroup.inv_mem _ hmN) _ hu
  simpa [mul_assoc] using this

include hs in
theorem mem_T_of_centralizer
    (hUL : U ≤ L) (hUp : IsPGroup 2 U) (hUi : ¬ 2 ∣ (U.subgroupOf L).index) {n : G}
    (hnN : n ∈ normalizer ((U ⊔ zpowers z : Subgroup G) : Set G))
    (hnc : n ∈ centralizer ({z} : Set G)) : n ∈ U ⊔ zpowers z := by
  obtain ⟨m, hmL, hm | hm⟩ := hs.exists_mem_L hnc
  · have : m ∈ U := hs.mem_of_mem_L_normalizer_T hUL hUp hUi hmL (hm ▸ hnN)
    rw [hm]
    exact Subgroup.mem_sup_left this
  · have hmN : m ∈ normalizer ((U ⊔ zpowers z : Subgroup G) : Set G) := by
      have hz : z⁻¹ ∈ normalizer ((U ⊔ zpowers z : Subgroup G) : Set G) :=
        Subgroup.inv_mem _ ((le_normalizer (H := U ⊔ zpowers z))
          (Subgroup.mem_sup_right (mem_zpowers z)))
      have := Subgroup.mul_mem _ hnN hz
      have hz2 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hs.mul_self_z
      have e : m = n * z⁻¹ := by
        rw [hm, hz2, mul_assoc, hs.mul_self_z, mul_one]
      rw [e]
      exact this
    have : m ∈ U := hs.mem_of_mem_L_normalizer_T hUL hUp hUi hmL hmN
    rw [hm]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left this) (Subgroup.mem_sup_right (mem_zpowers z))

include hs in
theorem exists_involution_of_normalizer
    (hUL : U ≤ L) (hUp : IsPGroup 2 U) (hUi : ¬ 2 ∣ (U.subgroupOf L).index) {n : G}
    (hnN : n ∈ normalizer ((U ⊔ zpowers z : Subgroup G) : Set G))
    (hnT : n ∉ (U ⊔ zpowers z : Subgroup G)) :
    ∃ l ∈ L, orderOf l = 2 ∧ (∀ u ∈ U, l * u = u * l) ∧ n * z * n⁻¹ = l * z := by
  have hz2 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hs.mul_self_z
  have hzT : z ∈ U ⊔ zpowers z := Subgroup.mem_sup_right (mem_zpowers z)
  have hz'T : n * z * n⁻¹ ∈ U ⊔ zpowers z := (Subgroup.mem_normalizer_iff.1 hnN z).1 hzT
  have hz'Q := hs.T_le_centralizer hUL hz'T
  have hz'ne : n * z * n⁻¹ ≠ z := by
    intro h
    apply hnT
    refine hs.mem_T_of_centralizer hUL hUp hUi hnN ?_
    rw [mem_centralizer_singleton_iff]
    calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [h]
  have hz'sq : (n * z * n⁻¹) * (n * z * n⁻¹) = 1 := by
    calc (n * z * n⁻¹) * (n * z * n⁻¹) = n * (z * z) * n⁻¹ := by group
      _ = 1 := by rw [hs.mul_self_z]; group
  obtain ⟨l, hlL, h | h⟩ := hs.exists_mem_L hz'Q
  · exact absurd (h ▸ hlL) (hs.conj_not_mem n)
  · have hl1 : l ≠ 1 := by
      rintro rfl
      exact hz'ne (by rw [h, one_mul])
    have hll : l * l = 1 := by
      have : (l * z) * (l * z) = l * l * (z * z) := by
        rw [mul_assoc, ← mul_assoc z l z, ← hs.comm_z hlL]
        group
      rw [h, this, hs.mul_self_z, mul_one] at hz'sq
      exact hz'sq
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨l, hlL, orderOf_eq_prime (by rw [pow_two]; exact hll) hl1, fun u hu => ?_, h⟩
    have hzu : u * z = z * u := hs.comm_z (hUL hu)
    have hu' : n⁻¹ * u * n ∈ U ⊔ zpowers z := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hnN) u).1
        (Subgroup.mem_sup_left hu)
      simpa using this
    have hcomm : z * (n⁻¹ * u * n) = (n⁻¹ * u * n) * z := by
      have := mem_centralizer_singleton_iff.1 (hs.T_le_centralizer hUL hu')
      exact this.symm
    have hz'u : (n * z * n⁻¹) * u = u * (n * z * n⁻¹) := by
      calc (n * z * n⁻¹) * u = n * (z * (n⁻¹ * u * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * u * n) * z) * n⁻¹ := by rw [hcomm]
        _ = u * (n * z * n⁻¹) := by group
    rw [h] at hz'u
    have h3 : l * (z * u) = u * l * z := by
      calc l * (z * u) = (l * z) * u := by group
        _ = u * (l * z) := hz'u
        _ = u * l * z := by group
    have h4 : l * (u * z) = u * l * z := by rw [← hzu] at h3; exact h3
    have h5 : l * u * z = u * l * z := by rw [mul_assoc]; exact h4
    exact mul_right_cancel h5


include hs in
theorem mem_of_commute
    {A : Subgroup G} (hAL : A ≤ L) (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hsq : ∀ x ∈ A, x * x = 1) (hA : Nat.card A = 64) {l : G} (hlL : l ∈ L) (hll : l * l = 1)
    (hcomm : ∀ a ∈ A, l * a = a * l) : l ∈ A := by
  obtain ⟨hcB, hsB⟩ := elemAbelian_sup_zpowers hc hsq hll hcomm
  have hBL : A ⊔ zpowers l ≤ L := sup_le hAL (zpowers_le.2 hlL)
  have h64 := card_le_of_elemAbelian_le hs.sporadic hBL hcB hsB
  have : A = A ⊔ zpowers l := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hA]; exact h64)
  rw [this]
  exact Subgroup.mem_sup_right (mem_zpowers l)


include hs in
theorem not_normalizer_le_centralizer
    {A : Subgroup G} (hAL : A ≤ L) (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hsq : ∀ x ∈ A, x * x = 1) (hA : Nat.card A = 64) :
    ¬ normalizer ((A ⊔ zpowers z : Subgroup G) : Set G) ≤ centralizer ({z} : Set G) := by
  intro H1
  have hz2 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hs.mul_self_z
  have hAp : IsPGroup 2 A := IsPGroup.of_card (n := 6) (by rw [hA]; norm_num)
  obtain ⟨U, hAU, hUL, hUp, hUi⟩ := exists_sylow_ge hAL hAp
  obtain ⟨n, hnN, hnT⟩ := hs.exists_normalizer_not_mem hUL hUp
  obtain ⟨l₁, hl₁L, hl₁2, -, hn1⟩ := hs.exists_involution_of_normalizer hUL hUp hUi hnN hnT
  have hnN' : n⁻¹ ∈ normalizer ((U ⊔ zpowers z : Subgroup G) : Set G) :=
    Subgroup.inv_mem _ hnN
  have hnT' : n⁻¹ ∉ (U ⊔ zpowers z : Subgroup G) := fun h =>
    hnT (by simpa using Subgroup.inv_mem _ h)
  obtain ⟨l₀, hl₀L, hl₀2, hl₀c, hn0⟩ :=
    hs.exists_involution_of_normalizer hUL hUp hUi hnN' hnT'
  have hn0' : n⁻¹ * z * n = l₀ * z := by simpa using hn0
  have hl₀ll : l₀ * l₀ = 1 := by
    rw [← pow_two, ← hl₀2]
    exact pow_orderOf_eq_one l₀
  have hl₀A : l₀ ∈ A :=
    hs.mem_of_commute hAL hc hsq hA hl₀L hl₀ll (fun a ha => hl₀c a (hAU ha))
  have hzA : ∀ a ∈ A, z * a = a * z := fun a ha => (hs.comm_z (hAL ha)).symm
  obtain ⟨hWc, hWs⟩ := elemAbelian_sup_zpowers hc hsq hs.mul_self_z hzA
  set W : Subgroup G := A ⊔ zpowers z with hW
  have hzcA : zpowers z ≤ centralizer (A : Set G) := hs.z_le_centralizer_U hAL
  have hWcard : Nat.card W = 128 := by
    have e := mulEquivProdSup hzcA (hs.disjoint.mono_left hAL)
    rw [hW, ← Nat.card_congr e.toEquiv, Nat.card_prod, hA, Nat.card_zpowers, hs.order_z]
  have hWT : W ≤ U ⊔ zpowers z := sup_le_sup hAU le_rfl
  set W₂ : Subgroup G := W.map (MulAut.conj n).toMonoidHom with hW₂
  have hmemW₂ : ∀ x, x ∈ W₂ ↔ n⁻¹ * x * n ∈ W := by
    intro x
    constructor
    · rintro ⟨w, hw, rfl⟩
      show n⁻¹ * (n * w * n⁻¹) * n ∈ W
      have e : n⁻¹ * (n * w * n⁻¹) * n = w := by group
      rw [e]
      exact hw
    · intro hx
      refine ⟨n⁻¹ * x * n, hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hzW₂ : z ∈ W₂ := by
    rw [hmemW₂, hn0']
    exact W.mul_mem (Subgroup.mem_sup_left hl₀A) (Subgroup.mem_sup_right (mem_zpowers z))
  have hW₂T : W₂ ≤ U ⊔ zpowers z := by
    rintro _ ⟨w, hw, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hnN w).1 (hWT hw)
  have hW₂c : ∀ x ∈ W₂, ∀ y ∈ W₂, x * y = y * x := by
    intro x hx y hy
    have := hWc _ ((hmemW₂ x).1 hx) _ ((hmemW₂ y).1 hy)
    calc x * y = n * ((n⁻¹ * x * n) * (n⁻¹ * y * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * y * n) * (n⁻¹ * x * n)) * n⁻¹ := by rw [this]
      _ = y * x := by group
  have hW₂s : ∀ x ∈ W₂, x * x = 1 := by
    intro x hx
    have := hWs _ ((hmemW₂ x).1 hx)
    calc x * x = n * ((n⁻¹ * x * n) * (n⁻¹ * x * n)) * n⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hdecomp : W₂ = (W₂ ⊓ L) ⊔ zpowers z := by
    refine le_antisymm (fun w hw => ?_) (sup_le inf_le_left (zpowers_le.2 hzW₂))
    obtain ⟨l, hlL, h | h⟩ := hs.exists_mem_L (hs.T_le_centralizer hUL (hW₂T hw))
    · exact Subgroup.mem_sup_left ⟨h ▸ hw, h ▸ hlL⟩
    · have hl : l ∈ W₂ := by
        have : l = w * z⁻¹ := by rw [h, hz2, mul_assoc, hs.mul_self_z, mul_one]
        rw [this]
        exact W₂.mul_mem hw (W₂.inv_mem hzW₂)
      rw [h]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hl, hlL⟩)
        (Subgroup.mem_sup_right (mem_zpowers z))
  have hzc₂ : zpowers z ≤ centralizer ((W₂ ⊓ L : Subgroup G) : Set G) :=
    hs.z_le_centralizer_U inf_le_right
  have hA₂card : Nat.card (W₂ ⊓ L : Subgroup G) = 64 := by
    have e := mulEquivProdSup hzc₂ (hs.disjoint.mono_left (inf_le_right : W₂ ⊓ L ≤ L))
    have h1 : Nat.card W₂ = 128 := by
      rw [hW₂, Subgroup.card_map_of_injective (MulAut.conj n).injective]
      exact hWcard
    have h2 : Nat.card ((W₂ ⊓ L) ⊔ zpowers z : Subgroup G) =
        Nat.card (W₂ ⊓ L : Subgroup G) * 2 := by
      rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zpowers, hs.order_z]
    rw [← hdecomp] at h2
    omega
  have h9 := nine_dvd_card_normalizer_inf hs.sporadic (A := W₂ ⊓ L) inf_le_right
    (fun x hx y hy => hW₂c x hx.1 y hy.1) (fun x hx => hW₂s x hx.1) hA₂card
  have hle : normalizer ((W₂ ⊓ L : Subgroup G) : Set G) ⊓ L ≤ centralizer ({l₁} : Set G) ⊓ L := by
    rintro g ⟨hgN, hgL⟩
    refine ⟨?_, hgL⟩
    have hgz : g * z = z * g := hs.comm_z hgL
    have hgW₂ : g ∈ normalizer (W₂ : Set G) := by
      refine mem_normalizer_fintype fun x hx => ?_
      have hx' : x ∈ (W₂ ⊓ L) ⊔ zpowers z := by
        rw [← hdecomp]
        exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hzc₂ hx'
      have hga : g * a * g⁻¹ ∈ W₂ ⊓ L := (Subgroup.mem_normalizer_iff.1 hgN a).1 ha
      have hgb : g * b * g⁻¹ = b := by
        rcases eq_one_or_eq_of_mul_self hs.mul_self_z hb with rfl | rfl
        · group
        · rw [hgz]; group
      have hbW : b ∈ W₂ := (zpowers_le.2 hzW₂) hb
      show g * (a * b) * g⁻¹ ∈ W₂
      rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group, hgb]
      exact W₂.mul_mem hga.1 hbW
    have hgW : n⁻¹ * g * n ∈ normalizer (W : Set G) := by
      refine Subgroup.mem_normalizer_iff.2 fun w => ?_
      have h1 := Subgroup.mem_normalizer_iff.1 hgW₂ (n * w * n⁻¹)
      rw [hmemW₂, hmemW₂] at h1
      have e1 : n⁻¹ * (n * w * n⁻¹) * n = w := by group
      have e2 : n⁻¹ * (g * (n * w * n⁻¹) * g⁻¹) * n =
          (n⁻¹ * g * n) * w * (n⁻¹ * g * n)⁻¹ := by group
      rw [e1, e2] at h1
      exact h1
    have hgc : n⁻¹ * g * n ∈ centralizer ({z} : Set G) := H1 hgW
    rw [mem_centralizer_singleton_iff] at hgc
    have hgz1 : g * (n * z * n⁻¹) = (n * z * n⁻¹) * g := by
      calc g * (n * z * n⁻¹) = n * ((n⁻¹ * g * n) * z) * n⁻¹ := by group
        _ = n * (z * (n⁻¹ * g * n)) * n⁻¹ := by rw [hgc]
        _ = (n * z * n⁻¹) * g := by group
    rw [hn1] at hgz1
    refine mem_centralizer_singleton_iff.2 (mul_right_cancel (b := z) ?_)
    calc g * l₁ * z = g * (l₁ * z) := by group
      _ = l₁ * z * g := hgz1
      _ = l₁ * (z * g) := by group
      _ = l₁ * (g * z) := by rw [hgz]
      _ = l₁ * g * z := by group
  have h9' : 9 ∣ Nat.card (centralizer ({l₁} : Set G) ⊓ L : Subgroup G) :=
    h9.trans (Subgroup.card_dvd_of_le hle)
  exact not_nine_dvd_card_centralizer_inf hs.sporadic hl₁L hl₁2 h9'


include hs in
theorem caseTwo :
    CaseTwo L z := fun _ hBL hBc hBs hB64 =>
  hs.not_normalizer_le_centralizer hBL hBc hBs hB64

end LS

end CFSG.EvenSporadicStandard.M24Std.GenX
