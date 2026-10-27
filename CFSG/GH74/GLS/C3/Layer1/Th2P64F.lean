module

public import CFSG.GH74.GLS.C3.Layer1.Th2P64D
public import CFSG.GH74.GLS.C3.Layer1.Th2P64E
public import CFSG.GH74.GLS.C3.Layer1.Th2P64B

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_inf_CxK {x : G} {K W : Subgroup G} (hcen : CenterlessBar K)
    (hW : IsPGroup 2 ↥W) {g : G} (hgW : g ∈ W) (hgK : g ∈ K) (hgC : g ∈ CxK x K) : g = 1 := by
  have hsec : g ∈ centralizerSection K (pPrimeCoreOf 2 K) := hgC.2
  exact card_inf_pPrimeCoreOf_eq hW hgW
    (mem_pPrimeCoreOf_of_commutators hcen hgK (fun k hk => hsec.2.2 k hk))

omit [Finite G] in
theorem x_mem_CxK {x : G} {K : Subgroup G} (hK : K ≤ centralizer ({x} : Set G)) : x ∈ CxK x K := by
  refine ⟨mem_centralizer_singleton_iff.2 rfl,
    C3.Layer1.Back.mem_centralizerSection_of_centralizes ?_ ?_⟩
  · intro k hk
    exact (mem_centralizer_singleton_iff.1 (hK hk)).symm
  · unfold pPrimeCoreOf
    intro z hz
    obtain ⟨z', -, rfl⟩ := hz
    exact z'.2

theorem mem_of_isSylowOf_of_central {D V : Subgroup G} (hV : IsSylowOf 2 V D) {z : G}
    (hz2 : orderOf z = 2) (hzD : z ∈ D) (hzc : ∀ d ∈ D, z * d = d * z) : z ∈ V := by
  have hzel : CFSG.IsElementaryAbelian 2 ↥(zpowers z) := isElementaryAbelian_zpowers_of_orderOf_two hz2
  have hzp : IsPGroup 2 ↥(zpowers z) := CFSG.IsElementaryAbelian.isPGroup 2 _
  obtain ⟨g, hgD, hg⟩ := Th2.exists_cj_le_of_isSylowOf hV (zpowers_le.2 hzD) hzp
  have : g⁻¹ * z * g = z := by
    calc g⁻¹ * z * g = g⁻¹ * (z * g) := by group
      _ = g⁻¹ * (g * z) := by rw [hzc g hgD]
      _ = z := by group
  exact hg ((Th2.mem_cj_iff g _ z).2 (by rw [this]; exact mem_zpowers z))


theorem prop64_false_of_lemma66
    (hG : C3Hyp G) {x : G} {K : Subgroup G} {B : Subgroup G} {b : G} {J : Subgroup G}
    (hxo : orderOf x = 2) (hKM : K ≤ centralizer ({x} : Set G))
    (hKn : ∀ m ∈ centralizer ({x} : Set G), ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hcen : CenterlessBar K) (hL2 : HasL2Model (kBar K) Odd)
    (hB : CFSG.IsElementaryAbelian 2 ↥B) (h : Obstr52 B b J)
    (hA : Nonempty (kBar J ≃* alternatingGroup (Fin 7))) (hN2 : twoPartCard (CxK b J) = 2)
    (hBx : B ≤ centralizer ({x} : Set G)) (hxb : x ≠ b) (hbC : b ∉ CxK x K)
    (hbdec : ∃ a ∈ K, ∃ e ∈ CxK x K, a ∈ B ∧ e ∈ B ∧ a * e = b)
    (h66 : ∀ V : Subgroup G, IsSylowOf 2 V (centralizer ({x, b} : Set G)) → B ≤ V →
      ∀ u ∈ V, ∀ v ∈ V, ⁅u, v⁆ ∈ CxK x K) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG4 : pRank 2 G ≤ 4 := hG.pRank_eq_four.le
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  have hb2' : b * b = 1 := hBsq b h.mem
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hb2') h.ne_one
  have hx1 : x ≠ 1 := fun h1 => by rw [h1] at hxo; simp at hxo
  have hx2' : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hxo, sq] at this
  have hbx : b * x = x * b := mem_centralizer_singleton_iff.1 (hBx h.mem)
  have hxcomm : x * b = b * x := hbx.symm
  set D := centralizer ({x, b} : Set G) with hD
  have hDb : D ≤ centralizer ({b} : Set G) := Subgroup.centralizer_le (by simp)
  have hDx : D ≤ centralizer ({x} : Set G) := Subgroup.centralizer_le (by simp)
  have hxDc : ∀ d ∈ D, x * d = d * x := fun d hd =>
    Subgroup.mem_centralizer_iff.1 hd x (by simp)
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
  obtain ⟨V, hV, hBV⟩ := Th2.L627.exists_isSylowOf_ge (CFSG.IsElementaryAbelian.isPGroup 2 ↥B) hBD
  have hVD : V ≤ D := hV.le
  have hV2 : IsPGroup 2 ↥V := hV.isPGroup
  have hVb : V ≤ centralizer ({b} : Set G) := hVD.trans hDb
  have hVx : V ≤ centralizer ({x} : Set G) := hVD.trans hDx
  have hbV : b ∈ V := hBV h.mem
  have hV32 : Nat.card ↥V = 32 := by
    have hle := h.card_le_32 hG4 hB hA hN2 hVb hV2
    have hdvd := h.thirtyTwo_dvd_card hG4 hB hA hN2 hx2' hx1 hxb hxcomm hBx
    have h5 : 5 ≤ (Nat.card D).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 (by simpa using hdvd)
    have hge : 32 ≤ Nat.card ↥V := by
      rw [hV.card_eq]
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ (Nat.card D).factorization 2 := Nat.pow_le_pow_right (by norm_num) h5
    omega
  have hBne : B ≠ V := by
    intro hBV'
    have hBcard : Nat.card ↥B ≤ 16 := by
      rw [C3.Layer1.Back.card_eq_two_pow_pRank hB]
      have : pRank 2 ↥B ≤ 4 := (pRank_le_top' B).trans hG4
      calc 2 ^ pRank 2 ↥B ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) this
        _ = 16 := by norm_num
    rw [← hBV'] at hV32
    omega
  obtain ⟨hZ8, hVnab⟩ := h.V_structure hG4 hB hA hN2 hVb hV2 hBV hBne
  have hL66 := h66 V hV hBV
  have hxV : x ∈ V := mem_of_isSylowOf_of_central hV hxo hxD hxDc
  have hxCx : x ∈ CxK x K := x_mem_CxK hKM
  have hxK : x ∉ K := fun hxK => hx1 (eq_one_of_mem_inf_CxK hcen hV2 hxV hxK hxCx)
  have hP₀c : ∀ p ∈ V ⊓ K, ∀ v ∈ V, v * p = p * v := by
    intro p hp v hv
    have hc : ⁅v, p⁆ = 1 := by
      refine eq_one_of_mem_inf_CxK hcen hV2 (g := ⁅v, p⁆) ?_ ?_ (hL66 v hv p hp.1)
      · rw [commutatorElement_def]
        exact V.mul_mem (V.mul_mem (V.mul_mem hv hp.1) (V.inv_mem hv)) (V.inv_mem hp.1)
      · rw [commutatorElement_def]
        exact K.mul_mem (hKn v (hVx hv) p hp.2) (K.inv_mem hp.2)
    exact commutatorElement_eq_one_iff_mul_comm.1 hc
  obtain ⟨a, haK, e, heC, haB, heB, hae⟩ := hbdec
  have ha2 : a * a = 1 := hBsq a haB
  have ha1 : a ≠ 1 := by
    intro ha1
    rw [ha1, one_mul] at hae
    exact hbC (hae ▸ heC)
  have haV : a ∈ V := hBV haB
  have hbK : b ∈ normalizer (K : Set G) := C3.Layer1.U1a.mem_normalizer_of_norm hKn (hBx h.mem)
  have hact : ∀ k ∈ K, (b * k * b⁻¹) * (a * k * a⁻¹)⁻¹ ∈ pPrimeCoreOf 2 K := by
    intro k hk
    have hesec : e ∈ centralizerSection K (pPrimeCoreOf 2 K) := heC.2
    have h1 : ⁅k, e⁆ ∈ pPrimeCoreOf 2 K := hesec.2.2 k hk
    have h2 : (e * k * e⁻¹ * k⁻¹) ∈ pPrimeCoreOf 2 K := by
      have h1' : (k * e * k⁻¹ * e⁻¹) ∈ pPrimeCoreOf 2 K := by
        simpa [commutatorElement_def] using h1
      have := (pPrimeCoreOf 2 K).inv_mem h1'
      have h3 : (k * e * k⁻¹ * e⁻¹)⁻¹ = e * k * e⁻¹ * k⁻¹ := by group
      rwa [h3] at this
    have h3 : (b * k * b⁻¹) * (a * k * a⁻¹)⁻¹ = a * (e * k * e⁻¹ * k⁻¹) * a⁻¹ := by
      rw [← hae]; group
    rw [h3]
    have hanorm := TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer haK)
    exact (Subgroup.mem_normalizer_iff.1 hanorm _).1 h2
  have hclass := isConj_of_hasL2Model_odd hL2
  have hK1 := twoPartCard_le_inf_centralizer hbK hb2' h.ne_one haK ha2 ha1 hact hclass
  have hDnorm : D ≤ normalizer ((K ⊓ D : Subgroup G) : Set G) := fun d hd =>
    C3.Layer1.U1a.mem_normalizer_of_norm (M := D) (L := K ⊓ D)
      (fun c hc k hk => ⟨hKn c (hDx hc) k hk.1, D.mul_mem (D.mul_mem hc hk.2) (D.inv_mem hc)⟩) hd
  have hP₀S : IsSylowOf 2 (V ⊓ (K ⊓ D)) (K ⊓ D) := hV.inf_of_le_normalizer inf_le_right hDnorm
  have hKD_eq : K ⊓ D = K ⊓ centralizer ({b} : Set G) := by
    ext g
    constructor
    · rintro ⟨hgK, hgD⟩
      exact ⟨hgK, hDb hgD⟩
    · rintro ⟨hgK, hgb⟩
      refine ⟨hgK, ?_⟩
      show g ∈ centralizer ({x, b} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases hy with rfl | rfl
      · exact (mem_centralizer_singleton_iff.1 (hKM hgK)).symm
      · exact (mem_centralizer_singleton_iff.1 hgb).symm
  have hVKD : V ⊓ (K ⊓ D) = V ⊓ K := by
    ext g
    constructor
    · rintro ⟨hgV, hgK, -⟩
      exact ⟨hgV, hgK⟩
    · rintro ⟨hgV, hgK⟩
      exact ⟨hgV, hgK, hVD hgV⟩
  have hP₀card : Nat.card ↥(V ⊓ (K ⊓ D)) = twoPartCard (K ⊓ D) := hP₀S.card_eq
  have hP₀le : Nat.card ↥(V ⊓ K) ≤ twoPartCard K :=
    Th2.L627.card_le_twoPartCard (hV2.to_le inf_le_left) inf_le_right
  have hP₀eq : Nat.card ↥(V ⊓ K) = twoPartCard K := by
    refine le_antisymm hP₀le ?_
    rw [← hVKD, hP₀card, hKD_eq]
    exact hK1
  have hP₀4 : 4 ≤ Nat.card ↥(V ⊓ K) := by
    have hrk : 2 ≤ pRank 2 ↥K := C3.Layer1.Thm1.two_le_pRank_of_shape (Or.inl hL2)
    obtain ⟨E, hEK, hEel, hErk⟩ := exists_elemAbelian_pRank K
    have hEc := C3.Layer1.Back.card_eq_two_pow_pRank hEel
    have hle := Th2.L627.card_le_twoPartCard (CFSG.IsElementaryAbelian.isPGroup 2 ↥E) hEK
    rw [hEc, hErk] at hle
    have h4 : 2 ^ 2 ≤ 2 ^ pRank 2 ↥K := Nat.pow_le_pow_right (by norm_num) hrk
    omega
  set Zc : Subgroup G := V ⊓ centralizer (V : Set G) with hZc
  have hZcle : Zc ≤ (center ↥V).map V.subtype := by
    intro g hg
    refine ⟨⟨g, hg.1⟩, ?_, rfl⟩
    show (⟨g, hg.1⟩ : ↥V) ∈ center ↥V
    rw [Subgroup.mem_center_iff]
    intro v
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hg.2 v v.2)
  have hZcard : Nat.card Zc ≤ 8 := by
    have := Subgroup.card_le_of_le hZcle
    rw [Subgroup.card_map_of_injective V.subtype_injective] at this
    omega
  have hPle : V ⊓ K ≤ Zc := fun p hp => ⟨hp.1, Subgroup.mem_centralizer_iff.2 (fun v hv => hP₀c p hp v hv)⟩
  have hxZ : zpowers x ≤ Zc := by
    rw [zpowers_le]
    exact ⟨hxV, Subgroup.mem_centralizer_iff.2 (fun v hv => (hxDc v (hVD hv)).symm)⟩
  have hPx : CommDisj (V ⊓ K) (zpowers x) := by
    refine ⟨fun p hp q hq => ?_, ?_⟩
    · obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hq
      have hpx : p * x = x * p := (hxDc p (hVD hp.1)).symm
      exact ((Commute.zpow_right (show Commute p x from hpx) n)).eq
    · refine eq_bot_iff.2 fun g hg => ?_
      rcases mem_zpowers_two hxo hg.2 with h0 | h0
      · rw [h0]; exact Subgroup.one_mem _
      · exact absurd (h0 ▸ hg.1.2) hxK
  have hsupcard : Nat.card ↥((V ⊓ K) ⊔ zpowers x) = Nat.card ↥(V ⊓ K) * 2 := by
    rw [hPx.card_sup le_rfl le_rfl, Nat.card_zpowers, hxo]
  have hsupZ : (V ⊓ K) ⊔ zpowers x ≤ Zc := sup_le hPle hxZ
  have hZc8 : Nat.card Zc = 8 := by
    have := Subgroup.card_le_of_le hsupZ
    omega
  have hZeq : (V ⊓ K) ⊔ zpowers x = Zc :=
    Subgroup.eq_of_le_of_card_ge hsupZ (by omega)
  have hZCx : ∀ g ∈ Zc, g ∈ CxK x K → g = 1 ∨ g = x := by
    intro g hgZ hgC
    rw [← hZeq] at hgZ
    obtain ⟨p, hp, q, hq, hpq⟩ := Th2.exists_mul_of_mem_sup_of_commute hPx.comm hgZ
    rcases mem_zpowers_two hxo hq with h0 | h0
    · left
      rw [h0, mul_one] at hpq
      rw [hpq]
      exact eq_one_of_mem_inf_CxK (x := x) hcen hV2 hp.1 hp.2 (hpq ▸ hgC)
    · right
      have hp1 : p = 1 := by
        refine eq_one_of_mem_inf_CxK (x := x) hcen hV2 hp.1 hp.2 ?_
        have : p = g * x⁻¹ := by rw [hpq, h0]; group
        rw [this]
        exact (CxK x K).mul_mem hgC ((CxK x K).inv_mem hxCx)
      rw [hpq, hp1, h0, one_mul]
  have hbZ : b ∈ Zc := ⟨hbV, Subgroup.mem_centralizer_iff.2 (fun v hv =>
    mem_centralizer_singleton_iff.1 (hVb hv))⟩
  have haZ : a ∈ Zc := hPle ⟨haV, haK⟩
  have heZ : e ∈ Zc := by
    have : e = a⁻¹ * b := by rw [← hae]; group
    rw [this]
    exact Zc.mul_mem (Zc.inv_mem haZ) hbZ
  have he1x : e = 1 ∨ e = x := hZCx e heZ heC
  have hex : ∀ m ∈ centralizer ({x} : Set G), m * e = e * m := by
    intro m hm
    rcases he1x with h0 | h0
    · rw [h0]; simp
    · rw [h0]; exact mem_centralizer_singleton_iff.1 hm
  have hMKD : ∀ m ∈ centralizer ({x} : Set G), ∃ k ∈ K, ∃ d ∈ D, m = k * d := by
    intro m hm
    set a' := m * a * m⁻¹ with ha'
    have ha'K : a' ∈ K := hKn m hm a haK
    have ha'2 : a' * a' = 1 := by
      calc m * a * m⁻¹ * (m * a * m⁻¹) = m * (a * a) * m⁻¹ := by group
        _ = 1 := by rw [ha2]; group
    have ha'1 : a' ≠ 1 := by
      intro h1
      apply ha1
      calc a = m⁻¹ * (m * a * m⁻¹) * m := by group
        _ = 1 := by rw [← ha', h1]; group
    obtain ⟨k, hkK, hk⟩ := exists_conj_of_isConj_kBar haK ha'K ha2 ha1 ha'2 ha'1
      (hclass _ _ (orderOf_mk_eq_two haK ha2 ha1) (orderOf_mk_eq_two ha'K ha'2 ha'1))
    have hmb : m * b * m⁻¹ = k * b * k⁻¹ := by
      have e1 : m * b * m⁻¹ = a' * e := by
        have := hex m hm
        rw [← hae, ha']
        calc m * (a * e) * m⁻¹ = m * a * m⁻¹ * (m * e * m⁻¹) := by group
          _ = m * a * m⁻¹ * e := by rw [this]; group
      have e2 : k * b * k⁻¹ = a' * e := by
        have := hex k (hKM hkK)
        rw [← hae, hk]
        calc k * (a * e) * k⁻¹ = k * a * k⁻¹ * (k * e * k⁻¹) := by group
          _ = k * a * k⁻¹ * e := by rw [this]; group
      rw [e1, e2]
    refine ⟨k, hkK, k⁻¹ * m, ?_, by group⟩
    rw [hD, Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with h0 | h0
    · rw [h0]
      have hk' : k * x = x * k := mem_centralizer_singleton_iff.1 (hKM hkK)
      have hm' : m * x = x * m := mem_centralizer_singleton_iff.1 hm
      have hkx : k⁻¹ * x = x * k⁻¹ := by
        calc k⁻¹ * x = k⁻¹ * (x * k) * k⁻¹ := by group
          _ = k⁻¹ * (k * x) * k⁻¹ := by rw [hk']
          _ = x * k⁻¹ := by group
      calc x * (k⁻¹ * m) = (x * k⁻¹) * m := by group
        _ = (k⁻¹ * x) * m := by rw [hkx]
        _ = k⁻¹ * (x * m) := by group
        _ = k⁻¹ * (m * x) := by rw [hm']
        _ = k⁻¹ * m * x := by group
    · rw [h0]
      have : k * b * k⁻¹ = m * b * m⁻¹ := hmb.symm
      calc b * (k⁻¹ * m) = k⁻¹ * (k * b * k⁻¹) * m := by group
        _ = k⁻¹ * (m * b * m⁻¹) * m := by rw [this]
        _ = (k⁻¹ * m) * b := by group
  have hSylM : IsSylowOf 2 V (centralizer ({x} : Set G)) := by
    refine isSylowOf_of_factor hKM hDx hKn hMKD hV ?_
    rw [← hP₀eq, ← hVKD, hP₀card]
  have hcard_center : Nat.card (center ↥V) = 8 := by
    have := Subgroup.card_le_of_le hZcle
    rw [Subgroup.card_map_of_injective V.subtype_injective] at this
    omega
  have hcommV : ∀ u ∈ V, ∀ v ∈ V, ⁅u, v⁆ = 1 ∨ ⁅u, v⁆ = x := by
    intro u hu v hv
    have hq : Nat.card (↥V ⧸ center ↥V) = 2 ^ 2 := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥V)
      rw [hV32, hcard_center] at this
      omega
    have hcq : IsMulCommutative (↥V ⧸ center ↥V) := IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
    have hqq : (QuotientGroup.mk (⟨u, hu⟩ : ↥V) : ↥V ⧸ center ↥V) * QuotientGroup.mk ⟨v, hv⟩ =
        QuotientGroup.mk ⟨v, hv⟩ * QuotientGroup.mk ⟨u, hu⟩ := hcq.is_comm.comm _ _
    have hc : (⁅(⟨u, hu⟩ : ↥V), ⟨v, hv⟩⁆ : ↥V) ∈ center ↥V := by
      have h1 : (QuotientGroup.mk' (center ↥V)) ⁅(⟨u, hu⟩ : ↥V), ⟨v, hv⟩⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 hqq
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hcV : ⁅u, v⁆ ∈ V := by
      rw [commutatorElement_def]
      exact V.mul_mem (V.mul_mem (V.mul_mem hu hv) (V.inv_mem hu)) (V.inv_mem hv)
    have hcZ : ⁅u, v⁆ ∈ Zc := by
      refine ⟨hcV, Subgroup.mem_centralizer_iff.2 (fun w hw => ?_)⟩
      have := Subgroup.mem_center_iff.1 hc ⟨w, hw⟩
      exact congrArg Subtype.val this
    exact hZCx _ hcZ (hL66 u hu v hv)
  obtain ⟨u₀, hu₀, v₀, hv₀, hne⟩ := hVnab
  have hxcomm' : ⁅u₀, v₀⁆ = x := by
    rcases hcommV u₀ hu₀ v₀ hv₀ with h1 | h1
    · exact absurd (commutatorElement_eq_one_iff_mul_comm.1 h1) hne
    · exact h1
  have hnormM : ∀ n ∈ normalizer (V : Set G), n ∈ centralizer ({x} : Set G) := by
    intro n hn
    have h1 := (Subgroup.mem_normalizer_iff.1 hn u₀).1 hu₀
    have h2 := (Subgroup.mem_normalizer_iff.1 hn v₀).1 hv₀
    have h3 : ⁅n * u₀ * n⁻¹, n * v₀ * n⁻¹⁆ = n * x * n⁻¹ := by
      rw [← hxcomm']
      simp only [commutatorElement_def]
      group
    rcases hcommV _ h1 _ h2 with h4 | h4
    · exfalso
      rw [h3] at h4
      apply hx1
      calc x = n⁻¹ * (n * x * n⁻¹) * n := by group
        _ = 1 := by rw [h4]; group
    · rw [h3] at h4
      rw [mem_centralizer_singleton_iff]
      calc n * x = (n * x * n⁻¹) * n := by group
        _ = x * n := by rw [h4]
  obtain ⟨S, hS, hVS⟩ := Th2.L627.exists_isSylowOf_ge hV2 (le_top : V ≤ ⊤)
  have hVeq : V = S := by
    by_contra hne'
    obtain ⟨a', ha'S, ha'N, ha'V, -⟩ := Th2.L627.exists_normalizer_sq_mem hS.isPGroup hVS hne'
    have ha'M : a' ∈ centralizer ({x} : Set G) := hnormM a' ha'N
    have hWS : V ⊔ zpowers a' ≤ S := sup_le hVS (zpowers_le.2 ha'S)
    have hWM : V ⊔ zpowers a' ≤ centralizer ({x} : Set G) :=
      sup_le hVx (zpowers_le.2 ha'M)
    have hW2 : IsPGroup 2 ↥(V ⊔ zpowers a') := hS.isPGroup.to_le hWS
    have hWeq : V ⊔ zpowers a' = V := hSylM.eq_of_le le_sup_left hWM hW2
    exact ha'V (hWeq ▸ mem_sup_right (mem_zpowers a'))
  have hcardV : Nat.card ↥V = 2 ^ (Nat.card G).factorization 2 := by
    rw [hVeq, hS.card_eq, Subgroup.card_top]
  have hcent : IsCentralInvolution b := by
    refine ⟨hb2, Sylow.ofCard V hcardV, ?_, fun s hs => ?_⟩
    · rw [Sylow.coe_ofCard]; exact hbV
    · rw [Sylow.coe_ofCard] at hs
      exact mem_centralizer_singleton_iff.1 (hVb hs)
  exact h.not_isCentralInvolution hG hB hA hN2 hcent

end CFSG.GH74.GLS.Th2.Obs
