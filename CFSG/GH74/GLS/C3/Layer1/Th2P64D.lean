module

public import CFSG.GH74.GLS.C3.Layer1.Th2P64Cop
public import CFSG.GH74.GLS.C3.Layer1.Th2P64Perm
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.GLS.C3.Layer1.Th2P617
public import CFSG.GH74.GLS.C3.Layer1.Th2P64A

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem Obstr52.centralizer_le_normalizer {B : Subgroup G} {b : G} {J : Subgroup G}
    (h : Obstr52 B b J) (hG4 : pRank 2 G ≤ 4) (hB : CFSG.IsElementaryAbelian 2 ↥B) :
    centralizer ({b} : Set G) ≤ normalizer (J : Set G) :=
  fun g hg => h.normalizes_centralizer hG4 hB g hg

@[expose] noncomputable def actOn {J : Subgroup G} (e : kBar J ≃* alternatingGroup (Fin 7))
    {V : Subgroup G} (hV : V ≤ normalizer (J : Set G)) : ↥V →* Perm (Fin 7) :=
  (a7Act J e).comp (Subgroup.inclusion hV)

omit [Finite G] in
theorem actOn_apply {J : Subgroup G} (e : kBar J ≃* alternatingGroup (Fin 7)) {V : Subgroup G}
    (hV : V ≤ normalizer (J : Set G)) {g : G} (hg : g ∈ V) :
    actOn e hV ⟨g, hg⟩ = a7Act J e ⟨g, hV hg⟩ := rfl

omit [Finite G] in
theorem actOn_eq_one_iff {J : Subgroup G} (e : kBar J ≃* alternatingGroup (Fin 7)) {V : Subgroup G}
    (hV : V ≤ normalizer (J : Set G)) {g : G} (hg : g ∈ V) :
    actOn e hV ⟨g, hg⟩ = 1 ↔ g ∈ centralizerSection J (pPrimeCoreOf 2 J) := by
  rw [actOn_apply, a7Act_eq_one_iff, barAct_eq_one_iff]

theorem eq_of_mem_CxK_of_orderOf_two {b : G} {J : Subgroup G}
    (hJ : IsPCompIn 2 (centralizer ({b} : Set G)) J) (hb2 : orderOf b = 2)
    (hN2 : twoPartCard (CxK b J) = 2) {n : G} (hn : n ∈ CxK b J) (hn2 : orderOf n = 2) : n = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hnb : n * b = b * n := mem_centralizer_singleton_iff.1 hn.1
  have hbN : b ∈ CxK b J := mem_CxK_self' hJ.1
  have h2 := C3.Layer1.U1a.two_le_pRank_of_commute hn hbN hn2 hb2 hnb hne
  obtain ⟨E, hEN, hEel, hErk⟩ := exists_elemAbelian_pRank (CxK b J)
  have hcard := C3.Layer1.Back.card_eq_two_pow_pRank hEel
  have hle := Th2.L627.card_le_twoPartCard (CFSG.IsElementaryAbelian.isPGroup 2 ↥E) hEN
  rw [hN2, hcard, hErk] at hle
  have h4 : 2 ^ 2 ≤ 2 ^ pRank 2 ↥(CxK b J) := Nat.pow_le_pow_right (by norm_num) h2
  omega

theorem Obstr52.card_le_32 {B : Subgroup G} {b : G} {J : Subgroup G} (h : Obstr52 B b J)
    (hG4 : pRank 2 G ≤ 4) (hB : CFSG.IsElementaryAbelian 2 ↥B) (hA : Nonempty (kBar J ≃* alternatingGroup (Fin 7)))
    (hN2 : twoPartCard (CxK b J) = 2) {V : Subgroup G} (hV : V ≤ centralizer ({b} : Set G))
    (hV2 : IsPGroup 2 ↥V) : Nat.card ↥V ≤ 32 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hA
  have hVN : V ≤ normalizer (J : Set G) := hV.trans (h.centralizer_le_normalizer hG4 hB)
  set φ := actOn e hVN with hφ
  have h1 := Subgroup.card_ker_mul_card_range φ
  have hker : Nat.card φ.ker ≤ 2 := by
    have hk2 : IsPGroup 2 ↥(φ.ker.map V.subtype) := (hV2.to_subgroup φ.ker).map V.subtype
    have hkle : φ.ker.map V.subtype ≤ CxK b J := by
      rintro g ⟨⟨g', hg'⟩, hgk, rfl⟩
      exact ⟨hV hg', (actOn_eq_one_iff e hVN hg').1 hgk⟩
    have := Th2.L627.card_le_twoPartCard hk2 hkle
    rw [hN2, Subgroup.card_map_of_injective V.subtype_injective] at this
    exact this
  have hrange : Nat.card φ.range ≤ 16 := by
    have hR : IsPGroup 2 ↥φ.range := IsPGroup.of_surjective hV2 φ.rangeRestrict φ.rangeRestrict_surjective
    have := Th2.L627.card_le_twoPartCard hR (le_top : φ.range ≤ ⊤)
    have h5 : twoPartCard (⊤ : Subgroup (Perm (Fin 7))) = 16 := by
      unfold twoPartCard
      rw [Subgroup.card_top, show (Nat.card (Perm (Fin 7))).factorization 2 = 4 from
        A7.factorization_S7]
      norm_num
    omega
  calc Nat.card ↥V = Nat.card φ.ker * Nat.card φ.range := h1.symm
    _ ≤ 2 * 16 := Nat.mul_le_mul hker hrange
    _ = 32 := by norm_num

theorem Obstr52.exists_image_B {B : Subgroup G} {b : G} {J : Subgroup G} (h : Obstr52 B b J)
    (hG4 : pRank 2 G ≤ 4) (hB : CFSG.IsElementaryAbelian 2 ↥B)
    (e : kBar J ≃* alternatingGroup (Fin 7)) {V : Subgroup G} (hBV : B ≤ V)
    (hVN : V ≤ normalizer (J : Set G)) :
    ∃ (F : Subgroup (Perm (Fin 7))) (t : Perm (Fin 7)), IsRootFour F ∧ t.IsSwap ∧
      (∀ i, (∃ f ∈ F, f i ≠ i) → t i = i) ∧
      (actOn e (hBV.trans hVN)).range = F ⊔ zpowers t := by
  obtain ⟨D, hD⟩ := h.exists_D
  obtain ⟨-, hBinv⟩ := hD.B_inv (h.normalizes hG4 hB)
  obtain ⟨t, ht, hdis, hBt⟩ := hBinv e
  refine ⟨_, t, hD.D_root e, ht, hdis, ?_⟩
  rw [← hBt]
  ext y
  simp only [MonoidHom.mem_range, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact ⟨⟨g, hVN (hBV hg)⟩, hg, rfl⟩
  · rintro ⟨⟨g, hgN⟩, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

theorem Obstr52.V_structure {B : Subgroup G} {b : G} {J : Subgroup G} (h : Obstr52 B b J)
    (hG4 : pRank 2 G ≤ 4) (hB : CFSG.IsElementaryAbelian 2 ↥B)
    (hA : Nonempty (kBar J ≃* alternatingGroup (Fin 7))) (hN2 : twoPartCard (CxK b J) = 2)
    {V : Subgroup G} (hV : V ≤ centralizer ({b} : Set G)) (hV2 : IsPGroup 2 ↥V) (hBV : B ≤ V)
    (hne : B ≠ V) : Nat.card (center ↥V) ≤ 8 ∧ ∃ u ∈ V, ∃ v ∈ V, u * v ≠ v * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hA
  have hb2 : orderOf b = 2 := by
    obtain ⟨-, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
    exact orderOf_eq_prime (by rw [sq]; exact hBsq b h.mem) h.ne_one
  have hVN : V ≤ normalizer (J : Set G) := hV.trans (h.centralizer_le_normalizer hG4 hB)
  have hBN : B ≤ normalizer (J : Set G) := hBV.trans hVN
  obtain ⟨F, t, hF, ht, hdis, hrange⟩ := h.exists_image_B hG4 hB e hBV hVN
  set φ := actOn e hVN with hφ
  have KC : ∀ (v : G) (hv : v ∈ V), (∀ y ∈ F ⊔ zpowers t, φ ⟨v, hv⟩ * y = y * φ ⟨v, hv⟩) →
      v ∈ B := by
    intro v hv hcomm
    have hmem : φ ⟨v, hv⟩ ∈ F ⊔ zpowers t :=
      centralizer_rootFour_sup_swap hF ht hdis (fun y hy => hcomm y hy)
    rw [← hrange] at hmem
    obtain ⟨⟨β, hβ⟩, hβeq⟩ := hmem
    have hβφ : actOn e (hBV.trans hVN) ⟨β, hβ⟩ = φ ⟨β, hBV hβ⟩ := rfl
    rw [hβφ] at hβeq
    set n : G := β⁻¹ * v with hn
    have hnV : n ∈ V := V.mul_mem (V.inv_mem (hBV hβ)) hv
    have hnφ : φ ⟨n, hnV⟩ = 1 := by
      have : (⟨n, hnV⟩ : ↥V) = (⟨β, hBV hβ⟩ : ↥V)⁻¹ * ⟨v, hv⟩ := rfl
      rw [this, map_mul, map_inv, hβeq]
      simp
    have hnCx : n ∈ CxK b J := ⟨hV hnV, (actOn_eq_one_iff e hVN hnV).1 hnφ⟩
    have hnb : n = 1 ∨ n = b := by
      by_cases hn1 : n = 1
      · exact Or.inl hn1
      · right
        have hle : Nat.card (zpowers n) ≤ 2 := by
          have := Th2.L627.card_le_twoPartCard (A := zpowers n) (X := CxK b J)
            (hV2.to_le (zpowers_le.2 hnV)) (zpowers_le.2 hnCx)
          rwa [hN2] at this
        rw [Nat.card_zpowers] at hle
        have hpos : 0 < orderOf n := orderOf_pos n
        have h1 : orderOf n ≠ 1 := fun h1 => hn1 (orderOf_eq_one_iff.1 h1)
        exact eq_of_mem_CxK_of_orderOf_two h.comp hb2 hN2 hnCx (by omega)
    have hv' : v = β * n := by rw [hn]; group
    rw [hv']
    refine B.mul_mem hβ ?_
    rcases hnb with h1 | h1
    · rw [h1]; exact B.one_mem
    · rw [h1]; exact h.mem
  have hcommB : ∀ (v : G) (hv : v ∈ V), (∀ β ∈ B, v * β = β * v) →
      ∀ y ∈ F ⊔ zpowers t, φ ⟨v, hv⟩ * y = y * φ ⟨v, hv⟩ := by
    intro v hv hvB y hy
    rw [← hrange] at hy
    obtain ⟨⟨β, hβ⟩, rfl⟩ := hy
    have hβφ : actOn e (hBV.trans hVN) ⟨β, hβ⟩ = φ ⟨β, hBV hβ⟩ := rfl
    rw [hβφ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hvB β hβ)
  constructor
  ·
    set Z : Subgroup ↥V := center ↥V with hZ
    have hZ2 : IsPGroup 2 ↥Z := hV2.to_subgroup Z
    set ψZ : ↥Z →* Perm (Fin 7) := φ.comp Z.subtype with hψZ
    have h1 := Subgroup.card_ker_mul_card_range ψZ
    have hker : Nat.card ψZ.ker ≤ 2 := by
      let ι : ↥Z →* G := V.subtype.comp Z.subtype
      have hι : Function.Injective ι := V.subtype_injective.comp Z.subtype_injective
      have hk2 : IsPGroup 2 ↥(ψZ.ker.map ι) := (hZ2.to_subgroup ψZ.ker).map ι
      have hkle : ψZ.ker.map ι ≤ CxK b J := by
        rintro g ⟨⟨⟨g', hg'⟩, hZg⟩, hgk, rfl⟩
        have : φ ⟨g', hg'⟩ = 1 := hgk
        exact ⟨hV hg', (actOn_eq_one_iff e hVN hg').1 this⟩
      have := Th2.L627.card_le_twoPartCard hk2 hkle
      rw [hN2, Subgroup.card_map_of_injective hι] at this
      exact this
    have hΨ8 : Nat.card (F ⊔ zpowers t : Subgroup (Perm (Fin 7))) ≤ 8 := by
      set φB := actOn e (hBV.trans hVN) with hφB
      have h2 := Subgroup.card_ker_mul_card_range φB
      have hBcard : Nat.card ↥B ≤ 16 := by
        rw [C3.Layer1.Back.card_eq_two_pow_pRank hB]
        have : pRank 2 ↥B ≤ 4 := (pRank_le_top' B).trans hG4
        calc 2 ^ pRank 2 ↥B ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) this
          _ = 16 := by norm_num
      have hbk : (⟨b, h.mem⟩ : ↥B) ∈ φB.ker := by
        show φB ⟨b, h.mem⟩ = 1
        exact (actOn_eq_one_iff e (hBV.trans hVN) h.mem).2 (mem_CxK_self' h.comp.1).2
      have hker2 : 2 ≤ Nat.card φB.ker := by
        have hb1 : (⟨b, h.mem⟩ : ↥B) ≠ 1 := fun h1 => h.ne_one (congrArg Subtype.val h1)
        have : φB.ker ≠ ⊥ := fun hbot => hb1 (by simpa [hbot] using hbk)
        have := (Subgroup.one_lt_card_iff_ne_bot φB.ker).2 this
        omega
      rw [← hrange]
      by_contra hlt
      push Not at hlt
      have : 2 * 9 ≤ Nat.card φB.ker * Nat.card φB.range := Nat.mul_le_mul hker2 hlt
      omega
    have hrange : Nat.card ψZ.range ≤ 4 := by
      have hψr : ψZ.range = Z.map φ := by
        ext y
        simp only [MonoidHom.mem_range, Subgroup.mem_map]
        constructor
        · rintro ⟨z, rfl⟩
          exact ⟨z.1, z.2, rfl⟩
        · rintro ⟨z, hz, rfl⟩
          exact ⟨⟨z, hz⟩, rfl⟩
      rw [hψr]
      set R := Z.map φ with hR
      have hRle : R ≤ F ⊔ zpowers t := by
        rintro _ ⟨⟨z, hz⟩, hzZ, rfl⟩
        refine centralizer_rootFour_sup_swap hF ht hdis (fun y hy => ?_)
        rw [← hrange] at hy
        obtain ⟨⟨β, hβ⟩, rfl⟩ := hy
        have hβφ : actOn e (hBV.trans hVN) ⟨β, hβ⟩ = φ ⟨β, hBV hβ⟩ := rfl
        rw [hβφ, ← map_mul, ← map_mul]
        congr 1
        have := Subgroup.mem_center_iff.1 hzZ ⟨β, hBV hβ⟩
        exact (this).symm
      have hRne : R ≠ F ⊔ zpowers t := by
        intro hReq
        apply hne
        refine le_antisymm hBV (fun g hg => KC g hg (fun y hy => ?_))
        rw [← hReq] at hy
        obtain ⟨⟨z, hz⟩, hzZ, rfl⟩ := hy
        rw [← map_mul, ← map_mul]
        congr 1
        exact (Subgroup.mem_center_iff.1 hzZ ⟨g, hg⟩)
      have hdvd : Nat.card R ∣ Nat.card (F ⊔ zpowers t : Subgroup (Perm (Fin 7))) :=
        Subgroup.card_dvd_of_le hRle
      have hlt : Nat.card R < Nat.card (F ⊔ zpowers t : Subgroup (Perm (Fin 7))) := by
        by_contra hge
        push Not at hge
        exact hRne (Subgroup.eq_of_le_of_card_ge hRle hge)
      obtain ⟨k', hk'⟩ := hdvd
      have hRpos : 0 < Nat.card R := Nat.card_pos
      have hk2 : 2 ≤ k' := by
        by_contra hk2
        push Not at hk2
        interval_cases k'
        · simp at hk'; exact absurd hk' (Nat.card_pos (α := ↥(F ⊔ zpowers t)) |>.ne')
        · simp at hk'; omega
      have h5 : Nat.card R * 2 ≤ Nat.card (F ⊔ zpowers t : Subgroup (Perm (Fin 7))) := by
        rw [hk']; exact Nat.mul_le_mul_left _ hk2
      omega
    calc Nat.card (center ↥V) = Nat.card ψZ.ker * Nat.card ψZ.range := h1.symm
      _ ≤ 2 * 4 := Nat.mul_le_mul hker hrange
      _ = 8 := by norm_num
  · by_contra hab
    push Not at hab
    apply hne
    refine le_antisymm hBV (fun g hg => ?_)
    exact KC g hg (hcommB g hg (fun β hβ => hab g hg β (hBV hβ)))

theorem sixteen_dvd_card_centralizer {s : Perm (Fin 7)} (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    16 ∣ Nat.card (centralizer ({s} : Set (Perm (Fin 7)))) := by
  have hsq : s ^ 2 = 1 := by rw [sq]; exact hs2
  rcases A7.involution_cycleType s hsq hs1 with h | h | h
  · rw [A7.card_centralizer_S7_two h]; norm_num
  · rw [A7.card_centralizer_S7_two_two h]; norm_num
  · rw [A7.card_centralizer_S7_two_two_two h]; norm_num

theorem Obstr52.thirtyTwo_dvd_card {B : Subgroup G} {b : G} {J : Subgroup G} (h : Obstr52 B b J)
    (hG4 : pRank 2 G ≤ 4) (hB : CFSG.IsElementaryAbelian 2 ↥B)
    (hA : Nonempty (kBar J ≃* alternatingGroup (Fin 7))) (hN2 : twoPartCard (CxK b J) = 2)
    {x : G} (hx2 : x * x = 1) (hx1 : x ≠ 1) (hxb : x ≠ b) (hxcomm : x * b = b * x)
    (hBx : B ≤ centralizer ({x} : Set G)) : 32 ∣ Nat.card (centralizer ({x, b} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hA
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq b h.mem) h.ne_one
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  set D := centralizer ({x, b} : Set G) with hD
  have hDb : D ≤ centralizer ({b} : Set G) := Subgroup.centralizer_le (by simp)
  have hDN : D ≤ normalizer (J : Set G) := hDb.trans (h.centralizer_le_normalizer hG4 hB)
  have hxD : x ∈ D := by
    rw [hD, Subgroup.mem_centralizer_iff]
    intro g hg
    rcases hg with rfl | rfl
    · rfl
    · exact hxcomm.symm
  have hbD : b ∈ D := by
    rw [hD, Subgroup.mem_centralizer_iff]
    intro g hg
    rcases hg with rfl | rfl
    · exact hxcomm
    · rfl
  have hBD : B ≤ D := by
    intro β hβ
    rw [hD, Subgroup.mem_centralizer_iff]
    intro g hg
    rcases hg with rfl | rfl
    · exact (mem_centralizer_singleton_iff.1 (hBx hβ)).symm
    · exact hBc _ h.mem β hβ
  obtain ⟨F, t, hF, ht, hdis, hrange⟩ := h.exists_image_B hG4 hB e hBD hDN
  have htt : t * t = 1 := by
    obtain ⟨a₁, a₂, -, rfl⟩ := ht
    exact Equiv.swap_mul_self a₁ a₂
  have hsign_t : Equiv.Perm.sign t = -1 := by
    obtain ⟨a₁, a₂, hne, rfl⟩ := ht
    exact Equiv.Perm.sign_swap hne
  have htmem : t ∈ F ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  rw [← hrange] at htmem
  obtain ⟨⟨f, hfB⟩, hft⟩ := htmem
  have hfD : f ∈ D := hBD hfB
  set φ := actOn e hDN with hφ
  have hφf : φ ⟨f, hfD⟩ = t := hft
  have hφt : t ∈ φ.range := ⟨⟨f, hfD⟩, hφf⟩
  have hxfcomm : x * f = f * x := (mem_centralizer_singleton_iff.1 (hBx hfB)).symm
  set s : Perm (Fin 7) := φ ⟨x, hxD⟩ with hs
  have hs2 : s * s = 1 := by
    rw [hs, ← map_mul]
    have : (⟨x, hxD⟩ * ⟨x, hxD⟩ : ↥D) = 1 := Subtype.ext hx2
    rw [this, map_one]
  have hs1 : s ≠ 1 := by
    intro h1
    have h2 := (actOn_eq_one_iff e hDN hxD).1 h1
    exact hxb (eq_of_mem_CxK_of_orderOf_two h.comp hb2 hN2 ⟨hDb hxD, h2⟩ hxo)
  have hst : s * t = t * s := by
    rw [hs, ← hφf, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxfcomm
  have hcent : centralizer ({s} : Set (Perm (Fin 7))) ≤ φ.range := by
    have key : ∀ y₀ ∈ alternatingGroup (Fin 7), y₀ * s = s * y₀ → y₀ ∈ φ.range := by
      intro y₀ hy₀A hy₀s
      obtain ⟨kb, hkb⟩ := e.surjective ⟨y₀, hy₀A⟩
      induction kb using QuotientGroup.induction_on with | H j => ?_
      have hjJ : (j : G) ∈ J := j.2
      have hJj : a7Act J e ⟨(j : G), Subgroup.le_normalizer hjJ⟩ = y₀ :=
        (a7Act_of_mem e hjJ).trans (congrArg Subtype.val hkb)
      have hxN : x ∈ normalizer (J : Set G) := hDN hxD
      have hcJ : x⁻¹ * ((j : G) * x * (j : G)⁻¹) ∈ J := by
        have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hxN) (j : G)).1 hjJ
        have : x⁻¹ * ((j : G) * x * (j : G)⁻¹) = (x⁻¹ * (j : G) * x⁻¹⁻¹) * (j : G)⁻¹ := by group
        rw [this]
        exact J.mul_mem h1 (J.inv_mem hjJ)
      have hcact : a7Act J e ⟨x⁻¹ * ((j : G) * x * (j : G)⁻¹), Subgroup.le_normalizer hcJ⟩ = 1 := by
        have : (⟨x⁻¹ * ((j : G) * x * (j : G)⁻¹), Subgroup.le_normalizer hcJ⟩ : ↥(normalizer (J : Set G))) =
            (⟨x, hxN⟩ : ↥(normalizer (J : Set G)))⁻¹ *
              (⟨(j : G), Subgroup.le_normalizer hjJ⟩ * ⟨x, hxN⟩ * ⟨(j : G), Subgroup.le_normalizer hjJ⟩⁻¹) :=
          rfl
        rw [this, map_mul, map_inv, map_mul, map_mul, map_inv, hJj]
        have hsx : a7Act J e ⟨x, hxN⟩ = s := rfl
        rw [hsx]
        have : y₀ * s * y₀⁻¹ = s := by
          calc y₀ * s * y₀⁻¹ = (s * y₀) * y₀⁻¹ := by rw [hy₀s]
            _ = s := by group
        rw [this]; group
      have hcO : x⁻¹ * ((j : G) * x * (j : G)⁻¹) ∈ pPrimeCoreOf 2 J := by
        rw [a7Act_of_mem e hcJ] at hcact
        have h1 : e (QuotientGroup.mk (⟨x⁻¹ * ((j : G) * x * (j : G)⁻¹), hcJ⟩ : ↥J)) = 1 :=
          Subtype.ext hcact
        have h2 : QuotientGroup.mk (⟨x⁻¹ * ((j : G) * x * (j : G)⁻¹), hcJ⟩ : ↥J) = (1 : kBar J) :=
          e.injective (by rw [h1, map_one])
        exact ⟨_, (QuotientGroup.eq_one_iff _).1 h2, rfl⟩
      obtain ⟨y', hy'J, hy'x, hy'O⟩ := exists_centralizer_lift hxN hx2 hx1 hjJ hcO
      have hmk : (QuotientGroup.mk (⟨y', hy'J⟩ : ↥J) : kBar J) = QuotientGroup.mk j := by
        rw [QuotientGroup.eq]
        obtain ⟨o, ho, hoeq⟩ := hy'O
        have hO2 : y'⁻¹ * ((j : G) * y'⁻¹) * y' ∈ pPrimeCoreOf 2 J := by
          have := TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer (J.inv_mem hy'J))
          have h5 := (Subgroup.mem_normalizer_iff.1 this ((j : G) * y'⁻¹)).1 ⟨o, ho, hoeq⟩
          simpa using h5
        obtain ⟨o2, ho2, hoeq2⟩ := hO2
        have : (⟨y', hy'J⟩ : ↥J)⁻¹ * j = o2 := by
          apply Subtype.ext
          have : ((⟨y', hy'J⟩ : ↥J)⁻¹ * j : ↥J).1 = y'⁻¹ * (j : G) := rfl
          rw [this]
          have h6 : (o2 : G) = y'⁻¹ * ((j : G) * y'⁻¹) * y' := hoeq2
          rw [h6]; group
        rw [this]; exact ho2
      have hy'D : y' ∈ D := by
        rw [hD, Subgroup.mem_centralizer_iff]
        intro g hg
        rcases hg with rfl | rfl
        · exact hy'x
        · exact (mem_centralizer_singleton_iff.1 (h.comp.1 hy'J)).symm
      refine ⟨⟨y', hy'D⟩, ?_⟩
      have h1 : actOn e hDN ⟨y', hy'D⟩ = a7Act J e ⟨y', Subgroup.le_normalizer hy'J⟩ := rfl
      rw [h1, a7Act_of_mem e hy'J, hmk, ← a7Act_of_mem e hjJ]
      exact hJj
    intro y hy
    have hysc : y * s = s * y := mem_centralizer_singleton_iff.1 hy
    by_cases hyA : y ∈ alternatingGroup (Fin 7)
    · exact key y hyA hysc
    · have hsy : Equiv.Perm.sign y = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign y) with h1 | h1
        · exact absurd (Equiv.Perm.mem_alternatingGroup.2 h1) hyA
        · exact h1
      have hytA : y * t ∈ alternatingGroup (Fin 7) := by
        rw [Equiv.Perm.mem_alternatingGroup, map_mul, hsy, hsign_t]; norm_num
      have hyts : y * t * s = s * (y * t) := by
        calc y * t * s = y * (t * s) := by rw [mul_assoc]
          _ = y * (s * t) := by rw [hst]
          _ = (y * s) * t := by rw [mul_assoc]
          _ = (s * y) * t := by rw [hysc]
          _ = s * (y * t) := by rw [mul_assoc]
      have h1 := key (y * t) hytA hyts
      have : y = (y * t) * t := by rw [mul_assoc, htt, mul_one]
      rw [this]
      exact φ.range.mul_mem h1 hφt
  have hdvd16 : 16 ∣ Nat.card φ.range :=
    (sixteen_dvd_card_centralizer hs2 hs1).trans (Subgroup.card_dvd_of_le hcent)
  have hbk : (⟨b, hbD⟩ : ↥D) ∈ φ.ker := by
    show φ ⟨b, hbD⟩ = 1
    exact (actOn_eq_one_iff e hDN hbD).2 (mem_CxK_self' h.comp.1).2
  have hdvd2 : 2 ∣ Nat.card φ.ker := by
    have := Subgroup.orderOf_dvd_natCard φ.ker hbk
    rwa [Subgroup.orderOf_mk, hb2] at this
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [← h1]
  exact Nat.mul_dvd_mul hdvd2 hdvd16 |> fun h2 => by simpa using h2

end CFSG.GH74.GLS.Th2.Obs
