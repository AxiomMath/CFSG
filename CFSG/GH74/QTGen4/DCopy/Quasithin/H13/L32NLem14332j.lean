module

public import CFSG.Quasithin.H13.L32NLem14332j
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems143b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneTwelve

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement

namespace L14332

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} {g a : G}
  {D : HatModelU (fsuU T V)} {K : Subgroup G}

theorem conj_W_inf_eq_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    (C : Ctx14332 G T L V V₂ g a D) :
    CFSG.conjugate (l32nW T V V₂) g ⊓ centralizerMod (fsuV1 T V) (l32nH T V) (fsuU T V) =
      l32nE T V V₂ g := by
  have S := L128P.setting128A_F4 h1222 h12213 C.setting
  obtain ⟨k, hk, hkN, hkY⟩ := L128P.exists_conjugate_eq C.setting.hyp C.setting.v1 C.gP C.gN
  obtain ⟨hTW, -⟩ := L128P.T_le_normalizer_w128_F4 h1222 h12213 C.setting
  have hWk : CFSG.conjugate (l32nW T V V₂) g = CFSG.conjugate (l32nW T V V₂) k := hkY _ hTW
  have h95 := (S.nine_five ⟨hk, hkN⟩).2
  have hU : L128A.uA V₂ (fsuV1 T V) = fsuU T V := L128P.uA_eq_F4 h1222 C.setting
  rw [L128A.wA, hU] at h95
  have hWkH : CFSG.conjugate (l32nW T V V₂) k ≤ l32nH T V := hWk ▸ C.Wg_le
  rw [l32nE, hWk, inf_centralizerMod hWkH]
  exact h95

theorem comm_Q_Wg_mem_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    (C : Ctx14332 G T L V V₂ g a D) (hQT : pCoreOf 2 (l32nH T V) ≤ T) {q x : G}
    (hq : q ∈ pCoreOf 2 (l32nH T V)) (hx : x ∈ CFSG.conjugate (l32nW T V V₂) g) :
    q * x * q⁻¹ * x⁻¹ ∈ fsuU T V := by
  have hQH : pCoreOf 2 (l32nH T V) ≤ l32nH T V :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 (l32nH T V)
  have hqH : q ∈ l32nH T V := hQH hq
  have hqN : q ∈ Subgroup.normalizer (V₂ : Set G) := (Subgroup.mem_inf.mp (C.T_le (hQT hq))).2
  obtain ⟨u, hu, k, hkH, hkC, rfl⟩ :=
    C.exists_mul_centralizer (Subgroup.mem_inf.mpr ⟨hqH, hqN⟩)
  have hkQ : k ∈ pCoreOf 2 (l32nH T V) := by
    have := (pCoreOf 2 (l32nH T V)).mul_mem
      ((pCoreOf 2 (l32nH T V)).inv_mem (fsuU_le_pCoreOf C hu)) hq
    simpa using this
  have hxH : x ∈ l32nH T V := C.Wg_le hx
  have hgN : g ∈ Subgroup.normalizer (V₂ : Set G) :=
    Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp C.gP.2 V₂) ⟨2, le_rfl, C.plane.1⟩
  have hkx := conj_mem_conj_l32nW C.plane.2 hgN hkC hx

  have hkxE : k * x * k⁻¹ * x⁻¹ ∈ l32nE T V V₂ g := by
    rw [← conj_W_inf_eq_F4 h1222 h12213 C]
    refine Subgroup.mem_inf.mpr ⟨mul_mem hkx (inv_mem hx), ?_⟩
    rw [C.q_tilde]
    have hxk : x * k⁻¹ * x⁻¹ ∈ pCoreOf 2 (l32nH T V) :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (l32nH T V) hxH) _).mp (inv_mem hkQ)
    have e : k * x * k⁻¹ * x⁻¹ = k * (x * k⁻¹ * x⁻¹) := by group
    rw [e]
    exact mul_mem hkQ hxk
  have hEU : l32nE T V V₂ g ≤ fsuU T V := inf_le_left.trans inf_le_left
  have e : u * k * x * (u * k)⁻¹ * x⁻¹ = u * (k * x * k⁻¹ * x⁻¹) * (x * u⁻¹ * x⁻¹) := by group
  rw [e]
  exact mul_mem (mul_mem hu (hEU hkxE)) (conj_mem_fsuU hxH (inv_mem hu))

theorem card_img_conj_W_F4 (h14323 : Lemma14323Rest_F4) (C : Ctx14332 G T L V V₂ g a D)
    (hii : Case14323ii T V g D) (hd : Module.finrank (ZMod 2) D.V = 4) :
    Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) = 4 := by
  obtain ⟨-, -, ⟨hrel, -⟩, -⟩ := h14323 G T L V C.hyp V₂ g C.plane C.gP C.gN D hd
  have hmul := Subgroup.relIndex_mul_card (H := D.img (CFSG.conjugate (centerOf (fsuU T V)) g))
    (K := D.img (CFSG.conjugate (l32nW T V V₂) g))
  rw [inf_eq_left.mpr (img_zU_le C), hrel, hii.card_zU] at hmul
  omega

theorem commutator_K_Q_le_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h14323 : Lemma14323Rest_F4)
    (C : Ctx14332 G T L V V₂ g a D) (hii : Case14323ii T V g D)
    (hd : Module.finrank (ZMod 2) D.V = 4) (hQ : pCoreOf 2 (l32nH T V) = l32nCHat T V)
    (hQT : pCoreOf 2 (l32nH T V) ≤ T) (hK : K ∈ cComp (l32nH T V)) :
    ⁅K, pCoreOf 2 (l32nH T V)⁆ ≤ fsuU T V := by
  have := finite_linearEquiv D
  have hKH : K ≤ l32nH T V := le_of_mem_cComp hK
  have hKn := le_normalizer_cComp hii hQ hK
  set Q := pCoreOf 2 (l32nH T V) with hQdef
  set Cm := centralizerMod (fsuU T V) (l32nH T V) Q with hCm
  have hHCm : l32nH T V ≤ Subgroup.normalizer (Cm : Set G) :=
    le_normalizer_centralizerMod (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (l32nH T V))
      (l32nH_le_normalizer_fsuU T V)

  have hWCm : CFSG.conjugate (l32nW T V V₂) g ≤ Cm := fun x hx =>
    ⟨C.Wg_le hx, l32nH_le_normalizer_fsuU T V (C.Wg_le hx), fun q hq => by
      have h1 := comm_Q_Wg_mem_F4 h1222 h12213 C hQT hq hx
      have e : x * q * x⁻¹ * q⁻¹ = (q * x * q⁻¹ * x⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem h1⟩

  set P : Subgroup ↥K := (K ⊓ Cm).subgroupOf K with hP
  have hPn : P.Normal := by
    constructor
    intro n hn k
    rw [hP, Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnK, hnC⟩ := Subgroup.mem_inf.mp hn
    exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem k.2 hnK) (inv_mem k.2),
      (Subgroup.mem_normalizer_iff.mp (hHCm (hKH k.2)) _).mp hnC⟩
  rcases normal_eq_top_or_map_le_solvRad hK P with hPtop | hPle
  · refine Subgroup.commutator_le.mpr fun k hk q hq => ?_
    have hkP : (⟨k, hk⟩ : ↥K) ∈ P := hPtop ▸ Subgroup.mem_top _
    rw [hP, Subgroup.mem_subgroupOf] at hkP
    obtain ⟨-, -, -, hkc⟩ := Subgroup.mem_inf.mp hkP
    rw [commutatorElement_def]
    exact hkc q hq
  · exfalso
    set Kd := (K.subgroupOf (l32nH T V)).map (imgHom D) with hKd

    set Xd := (D.img (CFSG.conjugate (l32nW T V V₂) g)).subgroupOf (D.img (l32nH T V)) with hXd
    have hXC : Xd ≤ Subgroup.centralizer (Kd : Set ↥(D.img (l32nH T V))) := by
      intro ξ hξ
      obtain ⟨x, hx, hxN, hξx⟩ := (L128A.HatU.mem_img D).mp (Subgroup.mem_subgroupOf.mp hξ)
      have hxH : x ∈ l32nH T V := C.Wg_le hx
      have eξ : ξ = imgHom D ⟨x, hxH⟩ := Subtype.ext (by rw [imgHom_apply]; exact hξx.symm)
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨⟨k, hkH⟩, hk, rfl⟩
      have hkK : k ∈ K := Subgroup.mem_subgroupOf.mp hk

      have hcK : k * x * k⁻¹ * x⁻¹ ∈ K := by
        have : x * k⁻¹ * x⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (hKn hxH) _).mp (inv_mem hkK)
        have e : k * x * k⁻¹ * x⁻¹ = k * (x * k⁻¹ * x⁻¹) := by group
        rw [e]
        exact mul_mem hkK this
      have hcC : k * x * k⁻¹ * x⁻¹ ∈ Cm :=
        mul_mem ((Subgroup.mem_normalizer_iff.mp (hHCm hkH) x).mp (hWCm hx)) (inv_mem (hWCm hx))
      have hcR : k * x * k⁻¹ * x⁻¹ ∈ solvRad K :=
        hPle ⟨⟨_, hcK⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hcK, hcC⟩), rfl⟩
      have h1 := imgHom_solvRad hii hQ hK hcR
      have e : (⟨k * x * k⁻¹ * x⁻¹, le_of_mem_cComp hK (solvRad_le K hcR)⟩ :
          ↥(l32nH T V)) = ⟨k, hkH⟩ * ⟨x, hxH⟩ * (⟨k, hkH⟩)⁻¹ * (⟨x, hxH⟩)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      rw [eξ]
      calc imgHom D ⟨k, hkH⟩ * imgHom D ⟨x, hxH⟩ =
          (imgHom D ⟨k, hkH⟩ * imgHom D ⟨x, hxH⟩ * (imgHom D ⟨k, hkH⟩)⁻¹ *
            (imgHom D ⟨x, hxH⟩)⁻¹) * imgHom D ⟨x, hxH⟩ * imgHom D ⟨k, hkH⟩ := by group
        _ = imgHom D ⟨x, hxH⟩ * imgHom D ⟨k, hkH⟩ := by rw [h1, one_mul]
    have hXle : D.img (CFSG.conjugate (l32nW T V V₂) g) ≤ D.img (l32nH T V) := by
      intro γ hγ
      obtain ⟨y, hy, hyN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
      exact L128A.HatU.rho_mem_img D (C.Wg_le hy) hyN
    have hXc : Nat.card ↥Xd = 4 := by
      rw [hXd, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXle).toEquiv]
      exact card_img_conj_W_F4 h14323 C hii hd
    have h2 := (Subgroup.card_le_of_le hXC).trans (card_centralizer_kd_le hii hQ hK)
    omega

end L14332

end CFSG.Quasithin.H13
