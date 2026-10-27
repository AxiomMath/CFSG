module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TE
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerCase

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OutInv

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

theorem false_of_isSolvable {Q : Type*} [Group Q] (hQ : IsQuasisimple Q)
    (hs : Group.IsSolvable Q) : False := by
  obtain ⟨hperf, -, a, b, hab⟩ := hQ
  have : Nontrivial Q := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [Subsingleton.elim x y]
  exact Group.IsPerfect.not_isSolvable Q hs

theorem eq_top_of_sup_center {X : Type*} [Group X] [Group.IsPerfect X] {M : Subgroup X}
    (h : M ⊔ center X = ⊤) : M = ⊤ := by
  rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := X), commutator_def,
    Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top x)
  obtain ⟨b, hb, d, hd, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top y)
  have hc' := Subgroup.mem_center_iff.mp hc
  have hd' := Subgroup.mem_center_iff.mp hd
  have e : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹
        = a * (c * b) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by group
      _ = a * (b * c) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by rw [hc' b]
      _ = a * b * (c * (d * c⁻¹)) * a⁻¹ * d⁻¹ * b⁻¹ := by group
      _ = a * b * (c * (c⁻¹ * d)) * a⁻¹ * d⁻¹ * b⁻¹ := by
          rw [(Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hc) d).symm]
      _ = a * b * (d * a⁻¹) * d⁻¹ * b⁻¹ := by group
      _ = a * b * (a⁻¹ * d) * d⁻¹ * b⁻¹ := by rw [hd' a⁻¹]
      _ = a * b * a⁻¹ * b⁻¹ := by group
  rw [e, commutatorElement_def]
  exact M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)

theorem oddBarConj_eq_one_of_mem_kernel {G : Type*} [Group G] {L : Subgroup G}
    {g : ↥(normalizer (L : Set G))} (hg : (g : G) ∈ coreActionKernel L) : oddBarConj L g = 1 := by
  obtain ⟨-, hc⟩ := mem_coreActionKernel.mp hg
  ext y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  rw [oddBarConj_apply_mk, MulAut.one_apply, QuotientGroup.eq]
  have hj : (g : G) * y * (g : G)⁻¹ ∈ L := (mem_normalizer_iff.mp g.2 y).mp y.2
  obtain ⟨o, ho, hoe⟩ := mem_map.mp (hc _ hj)
  convert ho using 1
  apply Subtype.ext
  rw [subtype_apply] at hoe
  rw [hoe]
  simp only [coe_mul, coe_inv]
  group

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

abbrev LK (h : Hyp52 H) : Type := OddBar h.K ⧸ center (OddBar h.K)

@[expose] noncomputable def rhoL : h.W →* MulAut (LK h) :=
  GH74.KGroups.inducedHom.comp (actW h hKa)

theorem rhoL_eq_one_iff (w : h.W) : rhoL hKa w = 1 ↔ (w : H) ∈ coreActionKernel h.K := by
  have hinj := GH74.KGroups.inducedHom_injective (K := OddBar h.K) h.isQuasisimple_K.1
  have e1 : rhoL hKa w = 1 ↔ actW h hKa w = 1 := by
    rw [rhoL, MonoidHom.comp_apply]
    constructor
    · intro h1
      apply hinj
      rw [h1, map_one]
    · intro h1
      rw [h1, map_one]
  rw [e1]
  show oddBarConj h.K (inclusion (W_le_normalizer_K h hKa) w) = 1 ↔ _
  exact ⟨fun h1 => mem_coreActionKernel_of_oddBarConj_eq_one h1,
    fun h1 => oddBarConj_eq_one_of_mem_kernel h1⟩

theorem rhoL_of_mem_K (k : h.K) :
    rhoL hKa ⟨k, K_le_W h k.2⟩ = MulAut.conj ((k : OddBar h.K) : LK h) := by
  rw [rhoL, MonoidHom.comp_apply, actW_of_mem_K, inducedHom_conj]

include hKa in
theorem mem_center_of_mem_kernel {k : h.K} (hk : (k : H) ∈ coreActionKernel h.K) :
    (k : OddBar h.K) ∈ center (OddBar h.K) := by
  have h1 : actW h hKa ⟨k, K_le_W h k.2⟩ = 1 :=
    oddBarConj_eq_one_of_mem_kernel (L := h.K)
      (g := inclusion (W_le_normalizer_K h hKa) ⟨k, K_le_W h k.2⟩) hk
  rw [actW_of_mem_K] at h1
  set y : OddBar h.K := (k : OddBar h.K) with hy
  rw [mem_center_iff]
  intro x
  have h2 := congrArg (fun φ : MulAut (OddBar h.K) => φ x) h1
  simp only [MulAut.conj_apply, MulAut.one_apply] at h2
  calc x * y = (y * x * y⁻¹) * y := by rw [h2]
    _ = y * x := by group

theorem mem_center_of_mem_oddTwoCore {k : h.K}
    (hk : (⟨k, K_le_W h k.2⟩ : h.W) ∈ oddTwoCore h.W) :
    (k : OddBar h.K) ∈ center (OddBar h.K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup h.K := (oddTwoCore h.W).comap (inclusion (K_le_W h)) with hN
  have hNn : N.Normal := (oddTwoCore_normal h.W).comap _
  set Nb : Subgroup (OddBar h.K) := N.map (QuotientGroup.mk' (pPrimeCore 2 h.K)) with hNb
  have hNbn : Nb.Normal := hNn.map _ (QuotientGroup.mk'_surjective _)
  have hkN : (k : OddBar h.K) ∈ Nb := ⟨k, hk, rfl⟩
  rcases LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple h.isQuasisimple_K Nb with
    hc | ht
  · exact hc hkN
  exfalso
  have h2 : IsPGroup 2 (OddBar h.K) := by
    intro y
    have hy : y ∈ Nb := by
      rw [ht]
      exact mem_top y
    obtain ⟨n, hn, rfl⟩ := hy
    obtain ⟨e, he⟩ := B5a.exists_pow_mem_of_mem_oddTwoCore hn
    refine ⟨e, ?_⟩
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).2
    have : inclusion (K_le_W h) (n ^ 2 ^ e) ∈ pPrimeCore 2 h.W := by
      rw [map_pow]
      exact he
    exact mem_pPrimeCore_of_mem_pPrimeCore_W this
  have := h2.isNilpotent
  exact false_of_isSolvable h.isQuasisimple_K inferInstance

theorem oddTwoCore_le_ker : oddTwoCore h.W ≤ (rhoL hKa).ker := by
  intro o ho
  rw [MonoidHom.mem_ker]
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  show (QuotientGroup.mk (actW h hKa o (k : OddBar h.K)) : LK h) =
    QuotientGroup.mk (k : OddBar h.K)
  rw [actW_apply_mk, QuotientGroup.eq]
  set k₁ : h.K := ⟨(o : H) * k * (o : H)⁻¹, (mem_normalizer_iff.mp
    (W_le_normalizer_K h hKa o.2) k).mp k.2⟩ with hk₁
  have hmk : ((k₁ : OddBar h.K))⁻¹ * (k : OddBar h.K) = ((k₁⁻¹ * k : h.K) : OddBar h.K) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hmk]
  apply mem_center_of_mem_oddTwoCore
  have hkW : (k : H) ∈ h.W := K_le_W h k.2
  have h1 : (⟨(k₁⁻¹ * k : h.K), K_le_W h (k₁⁻¹ * k).2⟩ : h.W) =
      o * ((⟨k, hkW⟩ : h.W)⁻¹ * o * (⟨k, hkW⟩ : h.W)⁻¹⁻¹)⁻¹ := by
    apply Subtype.ext
    simp only [hk₁, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
    group
  rw [h1]
  exact mul_mem ho (inv_mem ((oddTwoCore_normal h.W).conj_mem o ho _))

@[expose] noncomputable def rhoBar : Wbar h.B →* MulAut (LK h) :=
  QuotientGroup.lift (oddTwoCore h.W) (rhoL hKa) (oddTwoCore_le_ker hKa)

theorem rhoBar_mk (w : h.W) : rhoBar hKa (wbarMk h.B w) = rhoL hKa w :=
  QuotientGroup.lift_mk _ _ _

include hKa in
theorem mem_pPrimeCore_W_of_mem_pPrimeCore {k : h.K} (hk : k ∈ pPrimeCore 2 h.K) :
    (⟨k, K_le_W h k.2⟩ : h.W) ∈ pPrimeCore 2 h.W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKN := W_le_normalizer_K h hKa
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
  exact (le_sSup ⟨hMn, hMc⟩ : M ≤ pPrimeCore 2 h.W) ⟨k, hk, rfl⟩

include hKa in
theorem mem_oddTwoCore_of_mem_kernel {k : h.K} (hk : (k : H) ∈ coreActionKernel h.K) :
    (⟨k, K_le_W h k.2⟩ : h.W) ∈ oddTwoCore h.W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup h.W := ((coreActionKernel h.K).subgroupOf h.K).map (inclusion (K_le_W h))
    with hM
  have hMn : M.Normal := ⟨fun m hm w => by
    obtain ⟨k', hk', rfl⟩ := hm
    rw [SetLike.mem_coe, mem_subgroupOf] at hk'
    have hwN := W_le_normalizer_K h hKa w.2
    have hk'N : (k' : H) ∈ normalizer (h.K : Set H) := (mem_coreActionKernel.mp hk').1
    have hg1 : oddBarConj h.K ⟨(w : H) * k' * (w : H)⁻¹,
        mul_mem (mul_mem hwN hk'N) (inv_mem hwN)⟩ = 1 := by
      have e : (⟨(w : H) * k' * (w : H)⁻¹, mul_mem (mul_mem hwN hk'N) (inv_mem hwN)⟩ :
          ↥(normalizer (h.K : Set H))) = ⟨w, hwN⟩ * ⟨k', hk'N⟩ * (⟨w, hwN⟩)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv,
        oddBarConj_eq_one_of_mem_kernel (g := ⟨(k' : H), hk'N⟩) hk', mul_one,
        mul_inv_cancel]
    have hgK : (w : H) * k' * (w : H)⁻¹ ∈ h.K := (mem_normalizer_iff.mp hwN k').mp k'.2
    refine ⟨⟨_, hgK⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_subgroupOf]
      exact mem_coreActionKernel_of_oddBarConj_eq_one hg1
    · apply Subtype.ext
      simp⟩
  refine B5a.le_oddTwoCore hMn ?_ ⟨k, by rw [SetLike.mem_coe, mem_subgroupOf]; exact hk, rfl⟩
  rintro _ ⟨m, hm, rfl⟩
  rw [SetLike.mem_coe, mem_subgroupOf] at hm
  have hZ := mem_center_of_mem_kernel hKa hm
  obtain ⟨e, he⟩ := (isPGroup_two_center_of_pPrimeCore_eq_bot
    (pPrimeCore_quotient_pPrimeCore_eq_bot 2) : IsPGroup 2 (center (OddBar h.K))) ⟨_, hZ⟩
  have h1 : ((m ^ 2 ^ e : h.K) : OddBar h.K) = 1 := by
    have := congrArg Subtype.val he
    simpa using this
  rw [QuotientGroup.eq_one_iff] at h1
  refine ⟨e, ?_⟩
  rw [← map_pow]
  exact mem_pPrimeCore_W_of_mem_pPrimeCore hKa h1

abbrev Khat (h : Hyp52 H) : Subgroup (Wbar h.B) := wbarImage h.B h.K

include hKa in
theorem Khat_normal : (Khat h).Normal := by
  have : (h.K.subgroupOf h.W).Normal :=
    (normal_subgroupOf_iff_le_normalizer (K_le_W h)).2 (W_le_normalizer_K h hKa)
  exact this.map _ (QuotientGroup.mk'_surjective _)

theorem eq_of_rhoBar_eq {u v : Wbar h.B} (hu : u ∈ Khat h) (hv : v ∈ Khat h)
    (huv : rhoBar hKa u = rhoBar hKa v) : u = v := by
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨v', hv', rfl⟩ := hv
  rw [rhoBar_mk, rhoBar_mk] at huv
  rw [SetLike.mem_coe, mem_subgroupOf] at hu' hv'
  have h1 : rhoL hKa (u'⁻¹ * v') = 1 := by rw [map_mul, map_inv, huv, inv_mul_cancel]
  rw [rhoL_eq_one_iff] at h1
  have hk : ((u'⁻¹ * v' : h.W) : H) ∈ h.K := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem (inv_mem hu') hv'
  have h2 := mem_oddTwoCore_of_mem_kernel hKa (k := ⟨_, hk⟩) h1
  simp only [wbarMk, QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq]
  convert h2 using 1

theorem ker_le_centralizer {X : Subgroup (Wbar h.B)} (hX : X ≤ Khat h) :
    (rhoBar hKa).ker ≤ centralizer (X : Set (Wbar h.B)) := by
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  rw [mem_centralizer_iff]
  intro x hx
  have hyx : y * x * y⁻¹ ∈ Khat h := (Khat_normal hKa).conj_mem x (hX hx) y
  have h2 : rhoBar hKa (y * x * y⁻¹) = rhoBar hKa x := by
    rw [map_mul, map_mul, map_inv, hy, one_mul, inv_one, mul_one]
  have h3 := eq_of_rhoBar_eq hKa hyx (hX hx) h2
  calc x * y = (y * x * y⁻¹) * y := by rw [h3]
    _ = y * x := by group

theorem eq_one_of_rhoBar_eq_one {y : Wbar h.B} (hy : rhoBar hKa y = 1) (hy2 : y * y = 1) :
    y = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (oddTwoCore h.W) y
  change rhoBar hKa (wbarMk h.B w) = 1 at hy
  rw [rhoBar_mk] at hy
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos w).ne'
  set w' := w ^ m with hw'
  have hw'2 : w' ^ 2 ^ a = 1 := by
    rw [hw', ← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  have hw'K : (w' : H) ∈ coreActionKernel h.K := by
    rw [← rhoL_eq_one_iff hKa, hw', map_pow, hy, one_pow]
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
  have hB2 : IsPGroup 2 h.B := h.isPGroup_S.to_le (h.B_le.trans inf_le_left)
  have hBO : h.B.subgroupOf h.W ≤ oddTwoCore h.W := by
    refine B5a.le_oddTwoCore Subgroup.normal_in_normalizer fun m hm => ?_
    have hB2' : IsPGroup 2 ↥(h.B.subgroupOf h.W) := hB2.comap_subtype
    obtain ⟨k, hk⟩ := hB2' ⟨m, hm⟩
    refine ⟨k, ?_⟩
    have hmk : m ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [hmk]
    exact one_mem _
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

theorem odd_card_ker : Odd (Nat.card (rhoBar hKa).ker) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := (rhoBar hKa).ker) 2
    (even_iff_two_dvd.mp hev)
  have hy2 : (y : Wbar h.B) * y = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy, sq] at this
    exact congrArg Subtype.val this
  have h1 := eq_one_of_rhoBar_eq_one hKa (MonoidHom.mem_ker.mp y.2) hy2
  have : y = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hy
  exact absurd hy (by norm_num)

end OutInv

end CFSG.ComponentClassification.CatFactsL4U4
