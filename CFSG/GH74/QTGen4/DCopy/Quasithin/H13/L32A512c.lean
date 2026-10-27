module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A512b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A512P
public import CFSG.Quasithin.H13.L32A511Gold
import CFSG.Quasithin.H13.L32A512c
public import CFSG.Quasithin.H13.L32A512a
public import CFSG.Quasithin.H13.L32A513a

public section

namespace CFSG.Quasithin.H13.L32A.T53

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

theorem lemma14_5_12CaseOne_holds_F4 : Lemma14_5_12CaseOne_F4 := by
  intro G _ _ T L V V₂ Y C hXS3 _ hQ hsolv _ hX1 h311 hGA hO
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsMulCommutative ↥V := C.isMulCommutative_V_F4
  have S := C.set14_F4
  set H := hY T L V₂ Y with hHdef
  set W := vH T L V V₂ Y with hWdef
  have hWe : IsElemAbelian 2 W := (C.vH_le_center_F4 hQ).2
  have hHW : H ≤ Subgroup.normalizer (W : Set G) := le_normalizer_conjClosure _ _
  have hXH : xL L V₂ ⊔ T ≤ H := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hYH : Y ⊔ T ≤ H := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hTH : T ≤ H := le_sup_right
  have hV1W : fsuV1 T V ≤ W := le_conjClosure _ _
  have hV2W : V₂ ≤ W := by
    rw [← C.conjClosure_V1_X_F4]
    exact conjClosure_mono le_rfl (le_sup_left.trans le_sup_left)
  have : Finite (MulAut (IntMod W hWe)) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := MulAut (IntMod W hWe)))
  set ψ : ↥H →* MulAut (IntMod W hWe) := (convI hWe).comp (Subgroup.inclusion hHW) with hψ
  have hψ1 : ∀ h : ↥H, ψ h = 1 ↔ (h : G) ∈ Subgroup.centralizer (W : Set G) := fun h =>
    convI_eq_one_iff hWe _
  have hψval : ∀ (h : ↥H) (u : IntMod W hWe), ((ψ h) u).val = (h : G) * u.val * (h : G)⁻¹ :=
    fun h u => convI_apply_val hWe _ u
  have hψv : ∀ (h : ↥H) (w : G) (hw : w ∈ W),
      ((ψ h) (IntMod.mk hWe ⟨w, hw⟩)).val = (h : G) * w * (h : G)⁻¹ := fun h w hw =>
    hψval h _
  have hψS : ∀ h : ↥H, ψ h ∈ autI hWe H := fun h => convI_mem_autI hWe h.2 (hHW h.2)
  have hψS' : ∀ P ∈ autI hWe H, ∃ h : ↥H, ψ h = P := by
    intro P hP
    obtain ⟨g, hg, rfl⟩ := (mem_autI hWe).1 hP
    exact ⟨⟨g, hg⟩, rfl⟩
  have hcomm : ∀ h k : ↥H, ψ h * ψ k = ψ k * ψ h →
      ⁅(h : G), (k : G)⁆ ∈ Subgroup.centralizer (W : Set G) := fun h k hhk => by
    have : ψ ⁅h, k⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hhk
    rw [hψ1] at this
    exact this
  have hNψ : CFSG.pPrimeCore 3 ↥H ≤ ψ.ker := by
    intro h hh
    rw [MonoidHom.mem_ker, hψ1]
    exact h311 ⟨h, hh, rfl⟩
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) with hπ
  set ψ' := QuotientGroup.lift (CFSG.pPrimeCore 3 ↥H) ψ hNψ with hψ'
  have hQX : pCoreOf 2 (xL L V₂ ⊔ T) = pCoreOf 2 H := C.pCoreOf_xT_eq_F4 hO
  have hQY : pCoreOf 2 (Y ⊔ T) = pCoreOf 2 H := hO.symm.trans hQX
  have hTC : T ⊓ Subgroup.centralizer (W : Set G) = pCoreOf 2 H := C.inf_T_eq_F4 hXS3 hQ hX1 hO
  have hQC : pCoreOf 2 H ≤ Subgroup.centralizer (W : Set G) := by
    rw [← hTC]
    exact inf_le_right
  have hkerX : ∀ g (hg : g ∈ pCoreOf 2 (xL L V₂ ⊔ T)),
      ψ ⟨g, hXH (pCoreOf_le 2 _ hg)⟩ = 1 := fun g hg =>
    (hψ1 _).mpr (hQC (by rw [← hQX]; exact hg))
  have hkerY : ∀ g (hg : g ∈ pCoreOf 2 (Y ⊔ T)),
      ψ ⟨g, hYH (pCoreOf_le 2 _ hg)⟩ = 1 := fun g hg =>
    (hψ1 _).mpr (hQC (by rw [← hQY]; exact hg))
  have hT2 : Nat.card (autI hWe T) = 2 := by
    rw [card_autI_eq hWe (hTH.trans hHW), hTC, ← hQX]
    exact C.relIndex_pCoreOf_xT_F4 hXS3
  obtain ⟨A, hAT, hA, hmax, hAC⟩ := C.exists_J1_F4 hXS3 hX1
  have hAN : A ≤ Subgroup.normalizer (W : Set G) := (hAT.trans hTH).trans hHW
  have hA2 : (A ⊓ Subgroup.centralizer (W : Set G)).relIndex A = 2 := by
    rw [← card_autI_eq hWe hAN]
    have hdvd : Nat.card (autI hWe A) ∣ 2 := by
      rw [← hT2]
      exact Subgroup.card_dvd_of_le (autI_mono hWe hAT)
    have hne : Nat.card (autI hWe A) ≠ 1 := by
      intro h1
      apply hAC
      rw [← autI_eq_bot_iff hWe hAN]
      exact Subgroup.card_eq_one.mp h1
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  have hcard4 : Nat.card W ≤ 4 * Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) :=
    C.card_le_four_mul_F4 hQ hAT hA hmax hA2
  obtain ⟨t₀, ht₀A, ht₀C⟩ := IsConcreteLE.not_le_iff_exists.mp hAC
  have ht₀2 : t₀ ^ 2 = 1 := hA.2 t₀ ht₀A
  have ht₀T : t₀ ∈ T := hAT ht₀A
  set σt := ψ ⟨t₀, hTH ht₀T⟩ with hσt
  have hσt1 : σt ≠ 1 := fun h => ht₀C ((hψ1 _).mp h)
  have hσt2 : σt ^ 2 = 1 := by
    rw [hσt, ← map_pow]
    have : (⟨t₀, hTH ht₀T⟩ : ↥H) ^ 2 = 1 := Subtype.ext (by simpa using ht₀2)
    rw [this, map_one]
  have hσtA : σt ∈ autI hWe A := convI_mem_autI hWe ht₀A (hAN ht₀A)
  have hσtT : σt ∈ autI hWe T := convI_mem_autI hWe ht₀T (hAN ht₀A)
  have hrk : rk (commV (Subgroup.zpowers σt)) ≤ 2 := by
    have hz : Subgroup.zpowers σt = autI hWe A := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hσtA) ?_
      rw [card_autI_eq hWe hAN, hA2, Nat.card_zpowers, orderOf_eq_prime hσt2 hσt1]
    rw [← rkIdx_fixV_zpowers, hz]
    unfold rkIdx
    have e1 := (fixV (autI hWe A)).index_mul_card
    rw [card_fixV_autI hWe hAN] at e1
    have e2 : Nat.card (IntMod W hWe) = Nat.card W := rfl
    rw [e2] at e1
    have hpos : 0 < Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) := Nat.card_pos
    have hidx : (fixV (autI hWe A)).index ≤ 4 :=
      Nat.le_of_mul_le_mul_right (e1.le.trans hcard4) hpos
    have hidx0 : (fixV (autI hWe A)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    by_contra h
    have h8 : 2 ^ 3 ∣ (fixV (autI hWe A)).index :=
      (Nat.pow_dvd_pow 2 (by omega)).trans pow_padicValNat_dvd
    have h8' := Nat.le_of_dvd (Nat.pos_of_ne_zero hidx0) h8
    norm_num at h8'
    omega
  obtain ⟨x₀, hx₀, hx₀o, y, hy, hyo, hb₀⟩ := C.exists_comm_not_mem_F4
  obtain ⟨z, a, x, hz, hz1, ha, haV, hx, hx3, hxz, hxa⟩ := C.exists_rot_X_F4
  have hxXT : x ∈ xL L V₂ ⊔ T := Subgroup.mem_sup_left hx
  have hxo : Odd (orderOf x) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hx3)
  have hzW : z ∈ W := hV1W hz
  have haW : a ∈ W := hV2W ha
  have hyY : y ∈ Y := by
    rw [← C.oTwoUpper_yT_F4]
    exact Subgroup.subset_closure ⟨hy, hyo⟩
  have hyz : y * z * y⁻¹ = z := by
    rw [← Subgroup.mem_centralizer_iff.mp (C.le_centralizer_V1_F4 hyY) z hz, mul_inv_cancel_right]
  set hx' : ↥H := ⟨x, hXH hxXT⟩ with hhx'
  set hy' : ↥H := ⟨y, hYH hy⟩ with hhy'
  set hx₀' : ↥H := ⟨x₀, hXH hx₀⟩ with hhx₀'
  set σx := ψ hx' with hσx
  set σy := ψ hy' with hσy
  have hσx1 : σx ≠ 1 := by
    intro h
    rw [hσx, hψ1] at h
    apply haV
    have h2 : x * z = z * x := (Subgroup.mem_centralizer_iff.mp h z hzW).symm
    rw [← hxz, h2, mul_inv_cancel_right]
    exact hz
  obtain ⟨j, hj⟩ := exists_eq_pow_of_odd' hXH hXS3 ψ hkerX hxXT hx₀ hxo hx₀o hσx1
  have hψx₀ : ψ hx₀' = σx ^ j := hj
  have hσy1 : σy ≠ 1 := by
    intro h
    apply hb₀
    refine hcomm hx₀' hy' ?_
    rw [← hσy, h, one_mul, mul_one]
  have hσx3 : σx ^ 3 = 1 := by
    rw [hσx, ← map_pow]
    have : hx' ^ 3 = 1 := Subtype.ext (by simpa [hhx'] using hx3)
    rw [this, map_one]
  have hσy3 : σy ^ 3 = 1 := by
    rw [hσy, ← map_pow]
    have : hy' ^ 3 = 1 := Subtype.ext (by simpa [hhy'] using cube_of_odd C.hS3 hy hyo)
    rw [this, map_one]
  have ht₀Q : t₀ ∉ pCoreOf 2 (xL L V₂ ⊔ T) := fun h => ht₀C (hQC (by rw [← hQX]; exact h))
  have ht₀Q' : t₀ ∉ pCoreOf 2 (Y ⊔ T) := fun h => ht₀C (hQC (by rw [← hQY]; exact h))
  have htx : σt * σx * σt⁻¹ = σx⁻¹ :=
    inv_of_involution' hXH hXS3 ψ hkerX (Subgroup.mem_sup_right ht₀T) hxXT ht₀2 ht₀Q hxo
  have hty : σt * σy * σt⁻¹ = σy⁻¹ :=
    inv_of_involution' hYH C.hS3 ψ hkerY (Subgroup.mem_sup_right ht₀T) hy ht₀2 ht₀Q' hyo
  have hTsyl : IsSylowTwoOf T H := C.isSylowTwoOf_T_F4 le_sup_right
  have hSyl := B2F.isSylowTwoOf_autI hWe hHW hTsyl
  have hTS : ∀ u ∈ autI hWe H, ∀ w ∈ autI hWe H, u ^ 2 = 1 → w ^ 2 = 1 → u ≠ 1 → w ≠ 1 →
      u * w = w * u → u = w := by
    intro u hu w hw hu2 hw2 hu1 hw1 huw
    have hKe : IsElemAbelian 2 (Subgroup.closure ({u, w} : Set (MulAut (IntMod W hWe)))) := by
      refine B2F.isElemAbelian_closure ?_ ?_
      · rintro p (rfl | rfl) q (rfl | rfl)
        · rfl
        · exact huw
        · exact huw.symm
        · rfl
      · rintro p (rfl | rfl)
        · exact hu2
        · exact hw2
    have hKH : Subgroup.closure ({u, w} : Set (MulAut (IntMod W hWe))) ≤ autI hWe H := by
      rw [Subgroup.closure_le]
      rintro p (rfl | rfl)
      · exact hu
      · exact hw
    obtain ⟨g, -, hg⟩ :=
      exists_conj_le_of_isSylowTwoOf hSyl hKH (B2F.isPGroup_of_isElemAbelian hKe)
    have hmem : ∀ p ∈ ({u, w} : Set (MulAut (IntMod W hWe))), g * p * g⁻¹ ∈ autI hWe T := by
      intro p hp
      refine hg (mem_cjSub.mpr ?_)
      rw [show g⁻¹ * (g * p * g⁻¹) * g = p by group]
      exact Subgroup.subset_closure hp
    have hne : ∀ p : MulAut (IntMod W hWe), p ≠ 1 → g * p * g⁻¹ ≠ 1 := by
      intro p hp h
      apply hp
      calc p = g⁻¹ * (g * p * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have := eq_of_mem_of_card_eq_two hT2 (hmem u (Set.mem_insert u _))
      (hmem w (Set.mem_insert_of_mem u rfl)) (hne u hu1) (hne w hw1)
    exact mul_left_cancel (mul_right_cancel this)
  have hr : Open.pRank 3 (⊤ : Subgroup ↥H) ≤ 2 :=
    stronglyQuasithin_of_pCoreOf_ne_bot C.hyp.fsu.qtke hQ 3 Nat.prime_three (by norm_num)
  have hsolvD : Group.IsSolvable (↥H ⧸ CFSG.pPrimeCore 3 ↥H) := by
    have := hsolv
    infer_instance
  have hL : twoResidual (((xL L V₂ ⊔ T).subgroupOf H).map π) ≤
      Subgroup.centralizer (opResidual 3 (genFittingFitting (↥H ⧸ CFSG.pPrimeCore 3 ↥H)) :
        Set (↥H ⧸ CFSG.pPrimeCore 3 ↥H)) := by
    refine le_centralizer_opResidual F6.pCore_quotient_pPrimeCore ?_
    intro p hp hp5 e he k _
    rw [pCore_quotient_pPrimeCore_eq_bot hp (by omega), Subgroup.mem_bot] at he
    rw [he, mul_one, one_mul]
  have h23 : ∀ q : ℕ, q.Prime → q ∣ Nat.card (↥H ⧸ CFSG.pPrimeCore 3 ↥H) → q = 2 ∨ q = 3 :=
    fun q hq hqd => F6.prime_eq_two_or_three_of_pRank_le_two hGA.toIsGoldschmidtTriple hsolvD
      π (QuotientGroup.mk'_surjective _) hr (Or.inl hL) hq hqd
  have h5 : ∀ P ∈ autI hWe H, orderOf P ≠ 5 := by
    intro P hP hP5
    obtain ⟨h, rfl⟩ := hψS' P hP
    have h1 : orderOf (ψ h) ∣ Nat.card (↥H ⧸ CFSG.pPrimeCore 3 ↥H) :=
      (orderOf_map_dvd ψ' (π h)).trans (orderOf_dvd_natCard _)
    rw [hP5] at h1
    rcases h23 5 (by norm_num) h1 with he | he <;> omega
  have hV : ∀ w : IntMod W hWe, w ^ 2 = 1 := fun w => IntMod.sq_eq_one (hV := hWe) w
  have hσtS : σt ∈ autI hWe H := hψS _
  have hxy3 : (σx * σy) ^ 3 = 1 :=
    mul_cube_of_inverts hV hTS h5 (hψS hx') (hψS hy') hσtS hσx3 hσy3 hσt2 hσt1 htx hty hrk
  have hxy'3 : (σx * σy⁻¹) ^ 3 = 1 := by
    refine mul_cube_of_inverts hV hTS h5 (hψS hx') ((autI hWe H).inv_mem (hψS hy')) hσtS hσx3
      (by rw [inv_pow, hσy3, inv_one]) hσt2 hσt1 htx ?_ hrk
    rw [inv_inv, show σt * σy⁻¹ * σt⁻¹ = (σt * σy * σt⁻¹)⁻¹ by group, hty, inv_inv]
  set c := ψ ⁅hx', hy'⁆ with hc
  have hc' : c = ⁅σx, σy⁆ := map_commutatorElement ψ hx' hy'
  have hcx : c * σx = σx * c := by
    rw [hc']
    exact (b23_comm_left hσx3 hσy3 hxy3 hxy'3).symm
  have hcy : c * σy = σy * c := by
    rw [hc']
    exact (b23_comm_right hσx3 hσy3 hxy3 hxy'3).symm
  have hc3 : c ^ 3 = 1 := by
    rw [hc']
    exact b23_cube hσx3 hσy3 hxy3 hxy'3
  have hct : c * σt = σt * c := by
    have h1 : σt * c * σt⁻¹ = c := by
      rw [hc', show σt * ⁅σx, σy⁆ * σt⁻¹ = ⁅σt * σx * σt⁻¹, σt * σy * σt⁻¹⁆ by
        simp only [commutatorElement_def]; group, htx, hty, b23_inv_comm hσx3 hσy3 hxy'3]
    calc c * σt = σt * c * σt⁻¹ * σt := by rw [h1]
      _ = σt * c := by group
  set Zc : Subgroup G :=
    ((Subgroup.centralizer ({c} : Set (MulAut (IntMod W hWe)))).comap ψ).map H.subtype with hZc
  have hXZ : xL L V₂ ≤ Zc := by
    rw [← C.oTwoUpper_xT_F4]
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨hg, hgo⟩
    refine ⟨⟨g, hXH hg⟩, ?_, rfl⟩
    obtain ⟨i, hi⟩ := exists_eq_pow_of_odd' hXH hXS3 ψ hkerX hxXT hg hxo hgo hσx1
    show ψ ⟨g, hXH hg⟩ ∈ Subgroup.centralizer ({c} : Set (MulAut (IntMod W hWe)))
    rw [hi, Subgroup.mem_centralizer_singleton_iff]
    exact (Commute.pow_left (hcx.symm : Commute σx c) i).eq
  have hYZ : Y ≤ Zc := by
    rw [← C.oTwoUpper_yT_F4]
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨hg, hgo⟩
    refine ⟨⟨g, hYH hg⟩, ?_, rfl⟩
    obtain ⟨i, hi⟩ := exists_eq_pow_of_odd' hYH C.hS3 ψ hkerY hy hg hyo hgo hσy1
    show ψ ⟨g, hYH hg⟩ ∈ Subgroup.centralizer ({c} : Set (MulAut (IntMod W hWe)))
    rw [hi, Subgroup.mem_centralizer_singleton_iff]
    exact (Commute.pow_left (hcy.symm : Commute σy c) i).eq
  have hTZ : T ≤ Zc := by
    intro t' ht'
    refine ⟨⟨t', hTH ht'⟩, ?_, rfl⟩
    show ψ ⟨t', hTH ht'⟩ ∈ Subgroup.centralizer ({c} : Set (MulAut (IntMod W hWe)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases h1 : ψ ⟨t', hTH ht'⟩ = 1
    · rw [h1, one_mul, mul_one]
    · have hmemT : ψ ⟨t', hTH ht'⟩ ∈ autI hWe T := convI_mem_autI hWe ht' (hHW (hTH ht'))
      rw [eq_of_mem_of_card_eq_two hT2 hmemT hσtT h1 hσt1]
      exact hct.symm
  have hHZ : H ≤ Zc := sup_le (sup_le hXZ hYZ) hTZ
  have hcent : ∀ h : ↥H, c * ψ h = ψ h * c := by
    intro h
    obtain ⟨h', hh', he⟩ := hHZ h.2
    obtain rfl : h' = h := Subtype.ext he
    have hh'' : ψ h' ∈ Subgroup.centralizer ({c} : Set (MulAut (IntMod W hWe))) := hh'
    exact (Subgroup.mem_centralizer_singleton_iff.mp hh'').symm
  set v : IntMod W hWe := IntMod.mk hWe ⟨z, hzW⟩ with hv
  have hyv : σy v = v := by
    apply IntMod.val_injective
    rw [hσy, hv, hψv]
    exact hyz
  have hxv : v * σx v * σx (σx v) = 1 := by
    have h1 : σx v = IntMod.mk hWe ⟨a, haW⟩ := by
      apply IntMod.val_injective
      rw [hσx, hv, hψv]
      exact hxz
    have h2 : σx (σx v) = IntMod.mk hWe ⟨z * a, W.mul_mem hzW haW⟩ := by
      apply IntMod.val_injective
      rw [h1, hσx, hψv]
      exact hxa
    rw [h2, h1]
    apply IntMod.val_injective
    simp only [IntMod.val_mul, IntMod.val_one]
    show z * a * (z * a) = 1
    have hza : z * a = a * z := S.comm_V_F4 (Subgroup.mem_inf.mp hz).1 (S.hV2.2.1 ha)
    have hz2 : z * z = 1 := S.mul_self_V_F4 (Subgroup.mem_inf.mp hz).1
    have ha2 : a * a = 1 := S.mul_self_V_F4 (S.hV2.2.1 ha)
    calc z * a * (z * a) = z * (a * z) * a := by group
      _ = z * (z * a) * a := by rw [← hza]
      _ = (z * z) * (a * a) := by group
      _ = 1 := by rw [hz2, ha2, one_mul]
  have hcdef : c = σx * σy * σx⁻¹ * σy⁻¹ := by rw [hc', commutatorElement_def]
  have hcv : c v = v := fix_of_comm_triple hV hcdef hcx hcy hc3 hyv hxv
  have hbz : ∀ h : ↥H, c (ψ h v) = ψ h v := by
    intro h
    rw [← MulAut.mul_apply, hcent h, MulAut.mul_apply, hcv]
  have hWC : W ≤ Subgroup.centralizer ({⁅x, y⁆} : Set G) := by
    refine conjClosure_le fun h hh w hw => ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    rcases S.eq_of_mem_V1_F4 hz hz1 hw with hw1 | hw1
    · rw [hw1]
      simp
    · rw [hw1]
      have h1 := congrArg IntMod.val (hbz ⟨h, hh⟩)
      rw [hc, hψval, hψval] at h1
      have h2 : ⁅x, y⁆ * (h * z * h⁻¹) * ⁅x, y⁆⁻¹ = h * z * h⁻¹ := h1
      calc ⁅x, y⁆ * (h * z * h⁻¹) = ⁅x, y⁆ * (h * z * h⁻¹) * ⁅x, y⁆⁻¹ * ⁅x, y⁆ := by group
        _ = h * z * h⁻¹ * ⁅x, y⁆ := by rw [h2]
  have hxyC : ⁅x, y⁆ ∈ Subgroup.centralizer (W : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hWC hw) _ rfl).symm
  apply hb₀
  have h1 : ψ ⁅hx', hy'⁆ = 1 := (hψ1 _).mpr hxyC
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  refine hcomm hx₀' hy' ?_
  rw [hψx₀]
  exact (Commute.pow_left h1 j).eq

end CFSG.Quasithin.H13.L32A.T53

end
