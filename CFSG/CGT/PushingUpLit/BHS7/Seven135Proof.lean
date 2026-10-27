module

public import CFSG.CGT.PushingUpLit.BHS7.SevenThirteenG
public import CFSG.CGT.PushingUpLit.BHS7.Seven135Mod

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem s135_omegaOneCenter_thompsonJ_le_zSub (T : Subgroup Γ) :
    omegaOneCenterOf (thompsonJ T) ≤ zSub T := by
  refine Subgroup.closure_mono ?_
  rintro x ⟨hxZ, hx2⟩
  refine ⟨?_, hx2⟩
  have hxJ : x ∈ thompsonJ T := hxZ.1
  have hxB : x ∈ baum T := (B6.thompsonJ_le_baum T) hxJ
  refine ⟨hxB, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
  have hxY : x ∈ omegaOneCenterOf (thompsonJ T) := Subgroup.subset_closure ⟨hxZ, hx2⟩
  exact (Subgroup.mem_centralizer_iff.mp hb.2 x hxY).symm

theorem s135_isMaximal_conjSub {G H : Subgroup Γ} (hH : IsMaximalSubgroup G H) {g : Γ}
    (hg : g ∈ G) : IsMaximalSubgroup G (A1b.conjSub g H) := by
  have hG : A1b.conjSub g G = G := BHS.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hg)
  have hG' : A1b.conjSub g⁻¹ G = G :=
    BHS.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer (G.inv_mem hg))
  refine ⟨?_, fun K hHK hKG => ?_⟩
  · refine lt_of_le_of_ne (hG ▸ A1b.conjSub_mono g hH.1.le) fun h => hH.1.ne ?_
    exact (conjSub_inj g).mp (h.trans hG.symm)
  · have h1 : H ≤ A1b.conjSub g⁻¹ K := by
      have := A1b.conjSub_mono g⁻¹ hHK
      rwa [conjSub_inv_conjSub_self] at this
    have h2 : A1b.conjSub g⁻¹ K < G := by
      refine lt_of_le_of_ne (hG' ▸ A1b.conjSub_mono g⁻¹ hKG.le) fun h => hKG.ne ?_
      have := congrArg (A1b.conjSub g) (h.trans hG'.symm)
      rwa [conjSub_conjSub_inv_self, conjSub_conjSub_inv_self] at this
    have h3 := hH.2 _ h1 h2
    calc K = A1b.conjSub g (A1b.conjSub g⁻¹ K) := (conjSub_conjSub_inv_self g K).symm
      _ = A1b.conjSub g H := by rw [h3]


theorem s135_conj_key (b v z d c : Γ) (hd : d = b * v * b⁻¹ * v⁻¹) (hc : c = v * z * v⁻¹ * z⁻¹)
    (hbz : b * z = z * b) (hdz : d * z = z * d) (hdc : d * c = c * d) : b * c * b⁻¹ = c := by
  have e1 : b * v * b⁻¹ = d * v := by rw [hd]; group
  have e2 : b * z * b⁻¹ = z := by
    calc b * z * b⁻¹ = (z * b) * b⁻¹ := by rw [hbz]
      _ = z := by group
  calc b * c * b⁻¹ = (b * v * b⁻¹) * (b * z * b⁻¹) * (b * v * b⁻¹)⁻¹ * (b * z * b⁻¹)⁻¹ := by
        rw [hc]; group
    _ = (d * v) * z * (d * v)⁻¹ * z⁻¹ := by rw [e1, e2]
    _ = d * (v * z * v⁻¹ * z⁻¹) * z * d⁻¹ * z⁻¹ := by group
    _ = d * c * z * d⁻¹ * z⁻¹ := by rw [← hc]
    _ = (c * d) * z * d⁻¹ * z⁻¹ := by rw [hdc]
    _ = c * (d * z) * d⁻¹ * z⁻¹ := by group
    _ = c * (z * d) * d⁻¹ * z⁻¹ := by rw [hdz]
    _ = c := by group


section Finite

variable [Finite Γ] {G T E : Subgroup Γ}

theorem s135_commutator_vSub_zSub_le (h : MinCex G T) : ⁅vSub G T, zSub T⁆ ≤ zSub T := by
  have hT2 : IsSylowTwoOf T G := h.sylow
  have hV : IsElemAbelian 2 (vSub G T) := isElemAbelian_vSub h.charTwo hT2
  have hVT : vSub G T ≤ T := (vSub_le_pCoreOf h.charTwo hT2).trans hT2.pCoreOf_le
  have hGV : G ≤ Subgroup.normalizer (vSub G T : Set Γ) := le_normalizer_vSub G T
  have hBG : baum T ≤ G := (C1GN.baum_le T).trans hT2.1
  have hTB : T ≤ Subgroup.normalizer (baum T : Set Γ) := le_normalizer_baum T
  rw [Subgroup.commutator_le]
  intro v hv z hz
  have hzc : z ∈ centerOf (baum T) := C1GN.omegaOneCenterOf_le_centerOf (baum T) hz
  have hzB : z ∈ baum T := hzc.1
  have hzC : ∀ b ∈ baum T, b * z = z * b := fun b hb =>
    Subgroup.mem_centralizer_iff.mp hzc.2 b hb
  have hvT : v ∈ T := hVT hv
  have hvz : v * z * v⁻¹ ∈ baum T :=
    (Subgroup.mem_normalizer_iff.mp (hTB hvT) z).mp hzB
  have hcB : ⁅v, z⁆ ∈ baum T := by
    have : ⁅v, z⁆ = (v * z * v⁻¹) * z⁻¹ := rfl
    rw [this]
    exact (baum T).mul_mem hvz ((baum T).inv_mem hzB)
  have hcV : ⁅v, z⁆ ∈ vSub G T := by
    have : ⁅v, z⁆ = v * (z * v⁻¹ * z⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact (vSub G T).mul_mem hv ((Subgroup.mem_normalizer_iff.mp (hGV (hBG hzB)) v⁻¹).mp
      ((vSub G T).inv_mem hv))
  have hc2 : ⁅v, z⁆ ^ 2 = 1 := hV.2 _ hcV
  have hcC : ⁅v, z⁆ ∈ Subgroup.centralizer (baum T : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbG : b ∈ G := hBG hb
    have hdB : ⁅b, v⁆ ∈ baum T := by
      have : ⁅b, v⁆ = b * (v * b⁻¹ * v⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      have h1 : v * b⁻¹ * v⁻¹ ∈ baum T :=
        (Subgroup.mem_normalizer_iff.mp (hTB hvT) b⁻¹).mp ((baum T).inv_mem hb)
      exact (baum T).mul_mem hb h1
    have hdV : ⁅b, v⁆ ∈ vSub G T := by
      have : ⁅b, v⁆ = (b * v * b⁻¹) * v⁻¹ := rfl
      rw [this]
      exact (vSub G T).mul_mem ((Subgroup.mem_normalizer_iff.mp (hGV hbG) v).mp hv)
        ((vSub G T).inv_mem hv)
    have hdz : ⁅b, v⁆ * z = z * ⁅b, v⁆ := hzC _ hdB
    have hdc : ⁅b, v⁆ * ⁅v, z⁆ = ⁅v, z⁆ * ⁅b, v⁆ := isElemAbelian_comm' hV hdV hcV
    have hbz : b * z = z * b := hzC b hb
    have key := s135_conj_key b v z ⁅b, v⁆ ⁅v, z⁆ rfl rfl hbz hdz hdc
    calc b * ⁅v, z⁆ = (b * ⁅v, z⁆ * b⁻¹) * b := by group
      _ = ⁅v, z⁆ * b := by rw [key]
  exact Subgroup.subset_closure ⟨⟨hcB, hcC⟩, hc2⟩


theorem s135_mem_of_proper (h : MinCex G T) {E H : Subgroup Γ} (hE : E ∈ bStarT G T)
    (hZ : ⁅vSub G T, zSub T⁆ ≠ ⊥) (hH : IsMaximalSubgroup G H) (hEH : E ⊔ baum T ≤ H)
    (huniq : ∀ H' : Subgroup Γ, IsMaximalSubgroup G H' → E ⊔ baum T ≤ H' → H' = H)
    (hTH : T ≤ H) {y : Γ} (hyG : y ∈ G)
    (hK : baum T ⊔ A1b.conjSub y (baum T) ⊔ A1b.conjSub y E < G) : y ∈ H := by
  classical
  have hT : IsSylowTwoOf T G := h.sylow
  have hVn : G ≤ Subgroup.normalizer (vSub G T : Set Γ) := le_normalizer_vSub G T
  have hGc : A1b.conjSub y G = G := BHS.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hyG)
  obtain ⟨M, hM, hKM⟩ := exists_maximalSubgroup_ge hK
  have hM' : IsMaximalSubgroup G (A1b.conjSub y⁻¹ M) := s135_isMaximal_conjSub hM (G.inv_mem hyG)
  have hBM : baum T ≤ M := (le_sup_left.trans le_sup_left).trans hKM
  have hEM : E ⊔ baum T ≤ A1b.conjSub y⁻¹ M := by
    refine sup_le ?_ ?_
    · have h1 : A1b.conjSub y E ≤ M := le_sup_right.trans hKM
      have := A1b.conjSub_mono y⁻¹ h1
      rwa [conjSub_inv_conjSub_self] at this
    · have h1 : A1b.conjSub y (baum T) ≤ M := (le_sup_right.trans le_sup_left).trans hKM
      have := A1b.conjSub_mono y⁻¹ h1
      rwa [conjSub_inv_conjSub_self] at this
  have hMH : A1b.conjSub y⁻¹ M = H := huniq _ hM' hEM
  have hMy : M = A1b.conjSub y H := by rw [← hMH, conjSub_conjSub_inv_self]
  have hBH : baum T ≤ A1b.conjSub y H := hMy ▸ hBM
  have hTH' : IsSylowTwoOf T H := B6.isSylowTwoOf_mono hT hTH hH.1.le
  have hS1 : IsSylowTwoOf (A1b.conjSub y T) (A1b.conjSub y H) := B6.isSylowTwoOf_conjSub hTH' y
  obtain ⟨S₁, hS₁, hBS₁⟩ := B6.exists_isSylowTwoOf_ge (hT.2.1.to_le (C1GN.baum_le T)) hBH
  obtain ⟨z, hz, hzS⟩ := B6.isSylowTwoOf_exists_conj hS1 hS₁
  have hHyG : A1b.conjSub y H ≤ G := hGc ▸ A1b.conjSub_mono y hH.1.le
  have hzG : z ∈ G := hHyG hz
  have hzy : z * y ∈ G := G.mul_mem hzG hyG
  have hS₁eq : S₁ = A1b.conjSub (z * y) T := by rw [hzS, b6_conjSub_eq, conjSub_mul]
  have hS₁G : S₁ ≤ G := hS₁.1.trans hHyG
  have hbS : baum S₁ = baum T := baum_eq_of_isPGroup_of_baum_le hT hS₁.2.1 hS₁G hBS₁
  have hbc : baum (A1b.conjSub (z * y) T) = baum T := hS₁eq ▸ hbS
  have hZc : A1b.conjSub (z * y) (zSub T) = zSub T := by
    have h1 : zSub (A1b.conjSub (z * y) T) = A1b.conjSub (z * y) (zSub T) := by
      unfold zSub
      rw [baum_conjSub, omegaOneCenterOf_conjSub]
    rw [← h1]
    unfold zSub
    rw [hbc]
  have hcomm := seven_twelve_of_ne h hE hH hEH hZ
  have hne : ¬ tZero G T ≤ Subgroup.centralizer (vSub G T : Set Γ) := by
    rw [tZero_of_ne hZ]
    intro hle
    apply hZ
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro v hv z' hz'
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp (hle hz') v hv
  obtain ⟨hK1, -, -, -⟩ := seven_thirteen_one h hE hcomm hne huniq
  have hCn : z * y ∈ Subgroup.normalizer ((G ⊓ Subgroup.centralizer (vSub G T : Set Γ) :
      Subgroup Γ) : Set Γ) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hzy,
      B6.le_normalizer_centralizer hVn hzy⟩
  have hnorm : z * y ∈ Subgroup.normalizer ((tZero G T ⊔
      (G ⊓ Subgroup.centralizer (vSub G T : Set Γ)) : Subgroup Γ) : Set Γ) := by
    refine BHS.mem_normalizer_of_conjSub_eq ?_
    rw [conjSub_sup_eq, tZero_of_ne hZ, hZc, BHS.conjSub_eq_of_mem_normalizer hCn]
  have hzyH : z * y ∈ H := hK1 ⟨hzy, hnorm⟩
  have hh1 : y⁻¹ * z * y ∈ H := A1b.mem_conjSub_iff.mp hz
  have : y = (z * y) * (y⁻¹ * z * y)⁻¹ := by group
  rw [this]
  exact H.mul_mem hzyH (H.inv_mem hh1)

theorem s135_comm_of_mem (h : MinCex G T) {E H : Subgroup Γ} (hE : E ∈ bStarT G T)
    (hZ : ⁅vSub G T, zSub T⁆ ≠ ⊥) (hH : IsMaximalSubgroup G H) (hEH : E ⊔ baum T ≤ H)
    (hsub : IsSubnormal E H) {y : Γ} (hy : y ∈ H) {A : Subgroup Γ} (hAZ : A ≤ zSub T) :
    ⁅blockW E, A1b.conjSub y A⁆ = ⊥ := by
  classical
  have hT : IsSylowTwoOf T G := h.sylow
  have hyG : y ∈ G := hH.1.le hy
  have hEG : E ≤ G := hE.1.2.le
  have hVQ : vSub G T ≤ pCoreOf 2 G := vSub_le_pCoreOf h.charTwo hT
  have hGV : G ≤ Subgroup.normalizer (vSub G T : Set Γ) := le_normalizer_vSub G T
  have hne : ⁅E, vSub G T⁆ ≠ ⊥ := commutator_vSub_ne_bot hEG hE.2
  have hE'mem : A1b.conjSub y⁻¹ E ∈ sigmaSet G E H :=
    ⟨⟨y⁻¹, G.inv_mem hyG, rfl⟩, isSubnormal_conjSub (H.inv_mem hy) hsub⟩
  have hE'H : A1b.conjSub y⁻¹ E ≤ H := sigmaSet_le hE'mem
  have hE' : A1b.conjSub y⁻¹ E ∈ bStarT G T :=
    sigma_mem_bStarT h hE hH.1 (le_sup_right.trans hEH) (le_sup_left.trans hEH)
      hE'mem.1 hE'mem.2
  have hcomm := seven_twelve_of_ne h hE' hH (sup_le hE'H (le_sup_right.trans hEH)) hZ
  rw [tZero_of_ne hZ] at hcomm
  have hyN : y ∈ Subgroup.normalizer (Subgroup.centralizer (vSub G T : Set Γ) : Set Γ) :=
    B6.le_normalizer_centralizer hGV hyG
  have hX : ∀ x ∈ A1b.conjSub y A, ∀ f ∈ E, ⁅x, f⁆ ∈ Subgroup.centralizer (vSub G T : Set Γ) := by
    intro x hx f hf
    have hxa : y⁻¹ * x * y ∈ A := A1b.mem_conjSub_iff.mp hx
    have hf' : y⁻¹ * f * y ∈ A1b.conjSub y⁻¹ E := by
      rw [A1b.mem_conjSub_iff]
      have e : y * (y⁻¹ * f * y) * y⁻¹ = f := by group
      simpa only [inv_inv, e] using hf
    have h1 := hcomm _ (hAZ hxa) _ hf'
    have h2 : y * ⁅y⁻¹ * x * y, y⁻¹ * f * y⁆ * y⁻¹ = ⁅x, f⁆ := by
      simp only [commutatorElement_def]; group
    rw [← h2]
    exact (Subgroup.mem_normalizer_iff.mp hyN _).mp h1
  have hAT : A ≤ T := hAZ.trans ((C1GN.omegaOneCenterOf_le_self _).trans (C1GN.baum_le T))
  have hTy : IsSylowTwoOf (A1b.conjSub y T) G := isSylowTwoOf_conjSub_of_mem hT hyG
  have hX2 : IsPGroup 2 ↥(A1b.conjSub y A) := hTy.2.1.to_le (A1b.conjSub_mono y hAT)
  have hXG : A1b.conjSub y A ≤ G := (A1b.conjSub_mono y hAT).trans hTy.1
  exact commutator_blockW_eq_bot_of_comm_mod h.charTwo h.sylow hE.1.2 hVQ hGV hne hX2 hXG hX


theorem s135_step_one (h : MinCex G T) {E P : Subgroup Γ} (hE : E ∈ bStarT G T) (hTP : T ≤ P)
    (hPG : P ≤ G) (hPE : P ⊔ E = G) {A : Subgroup Γ} (hAQ : A ≤ pCoreOf 2 P)
    (hall : ∀ y ∈ P, ⁅blockW E, A1b.conjSub y A⁆ = ⊥) :
    A ≤ Subgroup.centralizer (vSub G T : Set Γ) := by
  classical
  have hT : IsSylowTwoOf T G := h.sylow
  have hEG : E ≤ G := hE.1.2.le
  have hVQ : vSub G T ≤ pCoreOf 2 G := vSub_le_pCoreOf h.charTwo hT
  have hGV : G ≤ Subgroup.normalizer (vSub G T : Set Γ) := le_normalizer_vSub G T
  have hne : ⁅E, vSub G T⁆ ≠ ⊥ := commutator_vSub_ne_bot hEG hE.2
  have hWE : ⁅E, vSub G T⁆ = blockW E :=
    commutator_eq_blockW h.charTwo h.sylow hE.1.2 hVQ (hEG.trans hGV) hne
  have hTP' : IsSylowTwoOf T P := B6.isSylowTwoOf_mono hT hTP hPG
  have hQT : pCoreOf 2 P ≤ T := hTP'.pCoreOf_le
  have hPQ : P ≤ Subgroup.normalizer (pCoreOf 2 P : Set Γ) := le_normalizer_pCoreOf_self P
  set S : Subgroup Γ := ⨆ y : P, A1b.conjSub (y : Γ) A with hS
  have hconjQ : ∀ y : P, A1b.conjSub (y : Γ) A ≤ pCoreOf 2 P := by
    intro y x hx
    have h1 : (y : Γ)⁻¹ * x * y ∈ A := A1b.mem_conjSub_iff.mp hx
    have h2 : (y : Γ) * ((y : Γ)⁻¹ * x * y) * (y : Γ)⁻¹ ∈ pCoreOf 2 P :=
      (Subgroup.mem_normalizer_iff.mp (hPQ y.2) _).mp (hAQ h1)
    have e : (y : Γ) * ((y : Γ)⁻¹ * x * y) * (y : Γ)⁻¹ = x := by group
    rwa [e] at h2
  have hSQ : S ≤ pCoreOf 2 P := iSup_le hconjQ
  have hST : S ≤ T := hSQ.trans hQT
  have hSP : P ≤ Subgroup.normalizer (S : Set Γ) := by
    intro p hp
    have key : ∀ q ∈ P, A1b.conjSub q S ≤ S := by
      intro q hq
      rw [hS, BHS.conjSub_iSup]
      refine iSup_le fun y => ?_
      rw [← A1b.conjSub_mul]
      exact le_iSup (fun y : P => A1b.conjSub (y : Γ) A) ⟨q * y, P.mul_mem hq y.2⟩
    exact BHS.mem_normalizer_of_conjSub_le (key p hp) (key p⁻¹ (P.inv_mem hp))
  have hWS : ∀ w ∈ blockW E, ∀ s ∈ S, s * w = w * s := by
    have hle : S ≤ Subgroup.centralizer (blockW E : Set Γ) := by
      refine iSup_le fun y => ?_
      intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h1 : ⁅w, s⁆ ∈ (⁅blockW E, A1b.conjSub (y : Γ) A⁆ : Subgroup Γ) :=
        Subgroup.commutator_mem_commutator hw hs
      rw [hall y y.2, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    intro w hw s hs
    exact (Subgroup.mem_centralizer_iff.mp (hle hs) w hw).symm
  set C : Subgroup Γ := vSub G T ⊓ Subgroup.centralizer (S : Set Γ) with hC
  have hCP : P ≤ Subgroup.normalizer (C : Set Γ) := by
    intro p hp
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hGV (hPG hp),
      B6.le_normalizer_centralizer hSP hp⟩
  have hCE : E ≤ Subgroup.normalizer (C : Set Γ) := by
    have key : ∀ e ∈ E, ∀ v ∈ C, e * v * e⁻¹ ∈ C := by
      intro e he v hv
      have hvV : v ∈ vSub G T := hv.1
      have hevV : e * v * e⁻¹ ∈ vSub G T :=
        (Subgroup.mem_normalizer_iff.mp (hGV (hEG he)) v).mp hvV
      have hcomm : ⁅e, v⁆ ∈ blockW E := hWE ▸ Subgroup.commutator_mem_commutator he hvV
      have e1 : e * v * e⁻¹ = ⁅e, v⁆ * v := by simp only [commutatorElement_def]; group
      refine ⟨hevV, ?_⟩
      rw [e1]
      refine Subgroup.mul_mem _ ?_ hv.2
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact hWS _ hcomm s hs
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨fun hv => key e he v hv, fun hv => ?_⟩
    have := key e⁻¹ (E.inv_mem he) _ hv
    simpa [mul_assoc] using this
  have hGC : G ≤ Subgroup.normalizer (C : Set Γ) := hPE ▸ sup_le hCP hCE
  have hΩC : omegaOneCenterOf T ≤ C := by
    intro u hu
    refine ⟨?_, ?_⟩
    · have : u ∈ A1b.conjSub (1 : Γ) (omegaOneCenterOf T) := by rw [A1b.conjSub_one]; exact hu
      exact le_iSup (fun g : G => A1b.conjSub (g : Γ) (omegaOneCenterOf T)) ⟨1, G.one_mem⟩ this
    · refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
      exact Subgroup.mem_centralizer_iff.mp (C1GN.omegaOneCenterOf_le_centerOf T hu).2 s (hST hs)
  have hVC : vSub G T ≤ C := by
    refine iSup_le fun g => ?_
    have hgC : A1b.conjSub (g : Γ) C = C := BHS.conjSub_eq_of_mem_normalizer (hGC g.2)
    calc A1b.conjSub (g : Γ) (omegaOneCenterOf T) ≤ A1b.conjSub (g : Γ) C := A1b.conjSub_mono _ hΩC
      _ = C := hgC
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvC : v ∈ C := hVC hv
  have haS : a ∈ S := by
    have : a ∈ A1b.conjSub (1 : Γ) A := by rw [A1b.conjSub_one]; exact ha
    exact le_iSup (fun y : P => A1b.conjSub (y : Γ) A) ⟨1, P.one_mem⟩ this
  exact (Subgroup.mem_centralizer_iff.mp hvC.2 a haS).symm



omit [Finite Γ] in
theorem s135_conjSub_le_pCoreOf {P A : Subgroup Γ} (hAQ : A ≤ pCoreOf 2 P) {y : Γ} (hy : y ∈ P) :
    A1b.conjSub y A ≤ pCoreOf 2 P := by
  intro x hx
  have h1 : y⁻¹ * x * y ∈ A := A1b.mem_conjSub_iff.mp hx
  have h2 : y * (y⁻¹ * x * y) * y⁻¹ ∈ pCoreOf 2 P :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf_self P hy) _).mp (hAQ h1)
  have e : y * (y⁻¹ * x * y) * y⁻¹ = x := by group
  rwa [e] at h2

theorem s135_case_two (h : MinCex G T) {E H : Subgroup Γ} (hE : E ∈ bStarT G T)
    (hH : IsMaximalSubgroup G H) (hEH : E ⊔ baum T ≤ H) (hsub : IsSubnormal E H) (hTH : T ≤ H)
    {y' : Γ} (hy'T : y' ∈ T) (hy'E : y' ∉ Subgroup.normalizer (E : Set Γ)) :
    ∃ w ∈ pCoreOf 2 E, ⁅y', w⁆ ∈ Subgroup.centralizer (baum T : Set Γ) ∧
      ⁅y', w⁆ ∉ Subgroup.centralizer (E : Set Γ) := by
  classical
  have hT : IsSylowTwoOf T G := h.sylow
  have hTS : IsSylowOf 2 T G := h.sylow
  have hy'G : y' ∈ G := hT.1 hy'T
  have hy'H : y' ∈ H := hTH hy'T
  have hE'mem : A1b.conjSub y' E ∈ sigmaSet G E H :=
    ⟨⟨y', hy'G, rfl⟩, isSubnormal_conjSub hy'H hsub⟩
  have hEmem : E ∈ sigmaSet G E H := mem_sigmaSet_self hsub
  have hne : A1b.conjSub y' E ≠ E := fun heq => hy'E (BHS.mem_normalizer_of_conjSub_eq heq)
  have hcomm : ⁅A1b.conjSub y' E, E⁆ = ⊥ := sigma_comm h hE hH.1 hEH hE'mem hEmem hne
  have hJN : thompsonJ T ≤ Subgroup.normalizer (E : Set Γ) :=
    (B6.thompsonJ_le_baum T).trans (baum_le_normalizer_of_isBTBlock hE.1.2)
  obtain ⟨w, hwW, hwE, hwΩ⟩ := exists_fixed_noncentral h.charTwo hTS hE.1.2 hTS hJN
  have hwZ : w ∈ zSub T := s135_omegaOneCenter_thompsonJ_le_zSub T hwΩ
  have hwE' : w ∈ E := blockW_le E (by rw [blockW_eq_pCoreOf hE.1.2]; exact hwW)
  have hTB : T ≤ Subgroup.normalizer (baum T : Set Γ) := le_normalizer_baum T
  have hZy : A1b.conjSub y' (zSub T) = zSub T := by
    unfold zSub
    rw [← omegaOneCenterOf_conjSub, BHS.conjSub_eq_of_mem_normalizer (hTB hy'T)]
  have hu : y' * w * y'⁻¹ ∈ zSub T := by
    have := A1b.mem_conjSub_of_mem (g := y') hwZ
    rwa [hZy] at this
  have hr : ⁅y', w⁆ ∈ zSub T := by
    have : ⁅y', w⁆ = (y' * w * y'⁻¹) * w⁻¹ := rfl
    rw [this]
    exact (zSub T).mul_mem hu ((zSub T).inv_mem hwZ)
  refine ⟨w, hwW, (C1GN.omegaOneCenterOf_le_centerOf (baum T) hr).2, ?_⟩
  intro hrE
  apply hwE
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have h1 : e * (y' * w * y'⁻¹ * w⁻¹) = (y' * w * y'⁻¹ * w⁻¹) * e :=
    Subgroup.mem_centralizer_iff.mp hrE e he
  have hu' : y' * w * y'⁻¹ ∈ A1b.conjSub y' E := A1b.mem_conjSub_of_mem hwE'
  have h2 : ⁅y' * w * y'⁻¹, e⁆ ∈ (⁅A1b.conjSub y' E, E⁆ : Subgroup Γ) :=
    Subgroup.commutator_mem_commutator hu' he
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
  have h3 : e * (y' * w * y'⁻¹) = (y' * w * y'⁻¹) * e := h2.symm
  have h4 : e * w⁻¹ = w⁻¹ * e := by
    apply mul_left_cancel (a := y' * w * y'⁻¹)
    calc (y' * w * y'⁻¹) * (e * w⁻¹) = ((y' * w * y'⁻¹) * e) * w⁻¹ := by group
      _ = (e * (y' * w * y'⁻¹)) * w⁻¹ := by rw [h3]
      _ = e * (y' * w * y'⁻¹ * w⁻¹) := by group
      _ = (y' * w * y'⁻¹ * w⁻¹) * e := h1
      _ = (y' * w * y'⁻¹) * (w⁻¹ * e) := by group
  calc e * w = w * (w⁻¹ * e) * w := by group
    _ = w * (e * w⁻¹) * w := by rw [h4]
    _ = w * e := by group

theorem seven_135 (h : MinCex G T) : Seven135 G T := by
  intro E H P hE hZ hH hEH hsub huniq hTH hNH hCH hTP hPG hPH hmin hPE
  classical
  by_contra hA
  have hT : IsSylowTwoOf T G := h.sylow
  have hEG : E ≤ G := hE.1.2.le
  have hPG' : P ≤ G := hPG.le
  have hVQ : vSub G T ≤ pCoreOf 2 G := vSub_le_pCoreOf h.charTwo hT
  have hGV : G ≤ Subgroup.normalizer (vSub G T : Set Γ) := le_normalizer_vSub G T
  have hne : ⁅E, vSub G T⁆ ≠ ⊥ := commutator_vSub_ne_bot hEG hE.2
  set A : Subgroup Γ := zSub T ⊓ pCoreOf 2 P with hAdef
  have hAZ : A ≤ zSub T := inf_le_left
  have hAQ : A ≤ pCoreOf 2 P := inf_le_right
  have hAT : A ≤ T := hAZ.trans ((C1GN.omegaOneCenterOf_le_self _).trans (C1GN.baum_le T))
  obtain ⟨y, hyP, hWy⟩ : ∃ y ∈ P, ⁅blockW E, A1b.conjSub y A⁆ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    exact hA (s135_step_one h hE hTP hPG' hPE hAQ hcon)
  have hyG : y ∈ G := hPG' hyP
  have hyH : y ∉ H := fun hyH => hWy (s135_comm_of_mem h hE hZ hH hEH hsub hyH hAZ)
  have hTP' : IsSylowTwoOf T P := B6.isSylowTwoOf_mono hT hTP hPG'
  have hYT : ∀ y' ∈ A1b.conjSub y A, y' ∈ T := fun y' hy' =>
    hTP'.pCoreOf_le (s135_conjSub_le_pCoreOf hAQ hyP hy')
  obtain ⟨y', hy'Y, w, hwW, hrB, hrE⟩ : ∃ y' ∈ A1b.conjSub y A, ∃ w ∈ pCoreOf 2 E,
      ⁅y', w⁆ ∈ Subgroup.centralizer (baum T : Set Γ) ∧
        ⁅y', w⁆ ∉ Subgroup.centralizer (E : Set Γ) := by
    by_cases hN : ∀ y' ∈ A1b.conjSub y A, y' ∈ Subgroup.normalizer (E : Set Γ)
    ·
      by_contra hcon
      push Not at hcon
      apply hWy
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro w hw y' hy'
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      by_contra hne'
      have hwW' : w ∈ pCoreOf 2 E := by rw [← blockW_eq_pCoreOf hE.1.2]; exact hw
      have hmove : y' * w * y'⁻¹ ≠ w := fun heq => hne' (by
        calc w * y' = (y' * w * y'⁻¹) * y' := by rw [heq]
          _ = y' * w := by group)
      obtain ⟨w', hw'W, hw'B, hw'E⟩ := s135_exists_commutator h.charTwo h.sylow hE.1.2
        (hYT y' hy') (hN y' hy') ⟨w, hwW', hmove⟩
      exact hw'E (hcon y' hy' w' hw'W hw'B)
    · push Not at hN
      obtain ⟨y', hy'Y, hy'N⟩ := hN
      obtain ⟨w, hwW, hwB, hwE⟩ := s135_case_two h hE hH hEH hsub hTH (hYT y' hy'Y) hy'N
      exact ⟨y', hy'Y, w, hwW, hwB, hwE⟩
  have hwV : w ∈ vSub G T := by
    have hWV : blockW E ≤ vSub G T := by
      rw [← commutator_eq_blockW h.charTwo h.sylow hE.1.2 hVQ (hEG.trans hGV) hne]
      exact commutator_le_of_le_normalizer (hEG.trans hGV)
    exact hWV (by rw [blockW_eq_pCoreOf hE.1.2]; exact hwW)
  have ha : y⁻¹ * y' * y ∈ A := A1b.mem_conjSub_iff.mp hy'Y
  have hv' : y⁻¹ * w * y ∈ vSub G T := by
    have := (Subgroup.mem_normalizer_iff.mp (hGV (G.inv_mem hyG)) w).mp hwV
    simpa using this
  have hc : ⁅y⁻¹ * y' * y, y⁻¹ * w * y⁆ ∈ (⁅vSub G T, A⁆ : Subgroup Γ) := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator ha hv'
  have hr : ⁅y', w⁆ = y * ⁅y⁻¹ * y' * y, y⁻¹ * w * y⁆ * y⁻¹ := by
    simp only [commutatorElement_def]; group
  generalize hcdef : ⁅y⁻¹ * y' * y, y⁻¹ * w * y⁆ = c at hc hr
  have hVAZ : (⁅vSub G T, A⁆ : Subgroup Γ) ≤ zSub T :=
    (Subgroup.commutator_mono le_rfl hAZ).trans (s135_commutator_vSub_zSub_le h)
  have hcB : ∀ b ∈ baum T, b * c = c * b := fun b hb =>
    Subgroup.mem_centralizer_iff.mp (C1GN.omegaOneCenterOf_le_centerOf (baum T) (hVAZ hc)).2 b hb
  have hcomm_ZE := seven_twelve_of_ne h hE hH hEH hZ
  rw [tZero_of_ne hZ] at hcomm_ZE
  have hX2 : IsPGroup 2 ↥A := hT.2.1.to_le hAT
  have hAG : A ≤ G := hAT.trans hT.1
  have hAEV : ∀ x ∈ A, ∀ f ∈ E, ⁅x, f⁆ ∈ Subgroup.centralizer (vSub G T : Set Γ) :=
    fun x hx f hf => hcomm_ZE x (hAZ hx) f hf
  have hVAE : ⁅⁅vSub G T, A⁆, E⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_comm_mod h.charTwo h.sylow hE.1.2 hVQ hGV hne hX2 hAG hAEV
  have hcE : ∀ e ∈ E, e * c = c * e := by
    intro e he
    have h1 : ⁅c, e⁆ ∈ (⁅⁅vSub G T, A⁆, E⁆ : Subgroup Γ) :=
      Subgroup.commutator_mem_commutator hc he
    rw [hVAE, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hKr : baum T ⊔ A1b.conjSub y (baum T) ⊔ A1b.conjSub y E ≤
      Subgroup.centralizer ({⁅y', w⁆} : Set Γ) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro b hb
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hrB b hb
    · intro b' hb'
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hcB _ (A1b.mem_conjSub_iff.mp hb')
      calc b' * ⁅y', w⁆ = y * ((y⁻¹ * b' * y) * c) * y⁻¹ := by rw [hr]; group
        _ = y * (c * (y⁻¹ * b' * y)) * y⁻¹ := by rw [h1]
        _ = ⁅y', w⁆ * b' := by rw [hr]; group
    · intro e' he'
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hcE _ (A1b.mem_conjSub_iff.mp he')
      calc e' * ⁅y', w⁆ = y * ((y⁻¹ * e' * y) * c) * y⁻¹ := by rw [hr]; group
        _ = y * (c * (y⁻¹ * e' * y)) * y⁻¹ := by rw [h1]
        _ = ⁅y', w⁆ * e' := by rw [hr]; group
  have hKG : ¬ (baum T ⊔ A1b.conjSub y (baum T) ⊔ A1b.conjSub y E < G) := fun hlt =>
    hyH (s135_mem_of_proper h hE hZ hH hEH huniq hTH hyG hlt)
  have hGc : A1b.conjSub y G = G := BHS.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hyG)
  have hBG : baum T ≤ G := (C1GN.baum_le T).trans hT.1
  have hKleG : baum T ⊔ A1b.conjSub y (baum T) ⊔ A1b.conjSub y E ≤ G := by
    refine sup_le (sup_le hBG ?_) ?_
    · calc A1b.conjSub y (baum T) ≤ A1b.conjSub y G := A1b.conjSub_mono y hBG
        _ = G := hGc
    · calc A1b.conjSub y E ≤ A1b.conjSub y G := A1b.conjSub_mono y hEG
        _ = G := hGc
  have hKeq : baum T ⊔ A1b.conjSub y (baum T) ⊔ A1b.conjSub y E = G := by
    by_contra hne'
    exact hKG (lt_of_le_of_ne hKleG hne')
  rw [Subgroup.mem_centralizer_iff] at hrE
  push Not at hrE
  obtain ⟨e, he, hne''⟩ := hrE
  have heK : e ∈ baum T ⊔ A1b.conjSub y (baum T) ⊔ A1b.conjSub y E := hKeq ▸ hEG he
  exact hne'' (Subgroup.mem_centralizer_singleton_iff.mp (hKr heK))

end Finite

end CFSG.CGT.PushingUpLit.BHS7
