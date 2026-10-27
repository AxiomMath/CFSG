module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofEightE1

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups
open scoped commutatorElement

section ModelU

open CFSG.RankThree.PartOne.U5K.Hyp

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem sec38v_bar_entry {z : hypSU h 2 1} (hz : z ∈ ZPsub h) :
    h.bar (mat z ιe₁ ιf₁) = mat z ιe₁ ιf₁ := by
  have := h.charP
  obtain ⟨hzU, a2, -, a4, -, -, -, a8, -, -⟩ := mem_ZPsub.1 hz
  have e := (U_rel hzU).2.2.2.2.2
  rw [a2, a4, a8] at e
  simp only [map_zero, zero_mul, mul_zero, add_zero] at e
  have h2 := CharTwo.add_self_eq_zero (mat z ιe₁ ιf₁)
  linear_combination e - h2

theorem sec38v_act_mem_ZPsub (hZ : center (hypPSU h 2 1) = ⊥)
    {T : Subgroup (MulAut (hypPSU h 2 1))} (hTU : T ⊓ Pi h = Uh h) {x : Gam h}
    (hxT : Phi h x ∈ T) {z : hypSU h 2 1} (hz : z ∈ ZPsub h) : act h x z ∈ ZPsub h := by
  obtain ⟨z', hz', hze⟩ := conj_mem_Zh hZ hTU hxT hz
  rw [Phi_mul_innM_mul_inv] at hze
  have hsq : act h x z * act h x z = 1 := by
    rw [← act_mul, Vsub_sq (ZPsub_le_Vsub hz), act_one]
  have e := eq_of_innM_eq_of_sq hZ hze (Vsub_sq (ZPsub_le_Vsub hz')) hsq
  rw [← e]
  exact hz'

theorem sec38v_entry_rel {x : Gam h} (hbar : ∀ c, x.1.right c = h.bar c) {z : hypSU h 2 1}
    (hz : z ∈ ZPsub h) (hz' : act h x z ∈ ZPsub h) :
    lmat x ιe₁ ιe₁ * mat z ιe₁ ιf₁ = mat (act h x z) ιe₁ ιf₁ * lmat x ιf₁ ιf₁ := by
  have hm := lmat_mul_map x z
  have e1 := congrFun (congrFun hm ιe₁) ιf₁
  obtain ⟨hzU, -, k2, -, k4, -, -, -, k8, -⟩ := mem_ZPsub.1 hz
  obtain ⟨hz'U, l2, -, l4, -, -, -, l8, -, -⟩ := mem_ZPsub.1 hz'
  obtain ⟨⟨-, -, -, u44, -⟩, -⟩ := U_entries hzU
  obtain ⟨⟨v11, -, -, -, -⟩, -⟩ := U_entries hz'U
  have hb := sec38v_bar_entry hz
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_one,
    Matrix.map_apply] at e1
  simp only [hbar, k2, k4, k8, u44, v11, l2, l4, l8, map_zero, map_one, mul_zero, zero_mul,
    mul_one, one_mul, add_zero, zero_add, hb] at e1
  linear_combination e1

theorem sec38v_lmat_e₁e₁_ne_zero (hZ : center (hypPSU h 2 1) = ⊥)
    {T : Subgroup (MulAut (hypPSU h 2 1))} (hTU : T ⊓ Pi h = Uh h) {x : Gam h}
    (hxT : Phi h x ∈ T) : lmat x ιe₁ ιe₁ ≠ 0 := by
  have hρN := mem_normalizer_Vh hZ hTU hxT
  have hP := isParaW_of_act_mem fun v hv => act_mem_Vsub hZ hρN hv
  have hdet := det_blkEE_ne_zero hP
  rw [Matrix.det_fin_two] at hdet
  have h21 := lmat_e₂e₁_eq_zero hZ hTU hxT
  have hdet' : lmat x ιe₁ ιe₁ * lmat x ιe₂ ιe₂ - lmat x ιe₁ ιe₂ * lmat x ιe₂ ιe₁ ≠ 0 := hdet
  intro h0
  apply hdet'
  rw [h0, h21]
  ring

theorem sec38v_centralizes_Zh (hZ : center (hypPSU h 2 1) = ⊥)
    {T : Subgroup (MulAut (hypPSU h 2 1))} (hT2 : IsPGroup 2 T) (hTU : T ⊓ Pi h = Uh h)
    {ρ : MulAut (hypPSU h 2 1)} (hρT : ρ ∈ T) (hρ2 : ρ * ρ ∈ Pi h) {z : hypSU h 2 1}
    (hz : z ∈ ZPsub h) : ρ * innM h z * ρ⁻¹ = innM h z := by
  classical
  obtain ⟨j, hj⟩ := hT2 ⟨ρ, hρT⟩
  have hj' : ρ ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  by_cases hρP : ρ ∈ Pi h
  · have hmem : ρ ∈ Uh h := by
      rw [← hTU]
      exact ⟨hρT, hρP⟩
    obtain ⟨u, hu, rfl⟩ := hmem
    have hzc : u * z = z * u := by
      have : z ∈ CFSG.centerIn (hypUnitriangular h 2 1) := by
        rw [centerIn_U]
        exact hz
      exact mem_centralizer_iff.1 this.2 u hu
    rw [← map_inv, ← map_mul, ← map_mul, mul_inv_eq_iff_eq_mul.2 hzc]
  · obtain ⟨x, hx⟩ := Phi_surjective h ρ
    have hbar : ∀ c, x.1.right c = h.bar c :=
      (right_eq_of_sq_mem_Pi hρ2 hx).resolve_left fun e =>
        hρP (Dlin_two_mem_Pi ((mem_Dlin_iff hx).2 e) hj')
    have hxT : Phi h x ∈ T := by
      rw [hx]
      exact hρT
    have hz1 : z₁SU h ∈ ZPsub h := z₁SU_mem_ZPsub
    have hz1' := sec38v_act_mem_ZPsub hZ hTU hxT hz1
    obtain ⟨ν, hν⟩ : ∃ ν : K, mat (act h x (z₁SU h)) ιe₁ ιf₁ = ν := ⟨_, rfl⟩
    have hrel1 := sec38v_entry_rel hbar hz1 hz1'
    rw [mat_z₁SU_e₁f₁, mul_one, hν] at hrel1
    have hA11 := sec38v_lmat_e₁e₁_ne_zero hZ hTU hxT
    have hd : lmat x ιf₁ ιf₁ ≠ 0 := fun h0 => hA11 (by rw [hrel1, h0, mul_zero])
    have hν0 : ν ≠ 0 := fun h0 => hA11 (by rw [hrel1, h0, zero_mul])
    have hgen : ∀ z ∈ ZPsub h, act h x z ∈ ZPsub h ∧
        mat (act h x z) ιe₁ ιf₁ = ν * mat z ιe₁ ιf₁ := by
      intro z hz
      have hz' := sec38v_act_mem_ZPsub hZ hTU hxT hz
      refine ⟨hz', ?_⟩
      have := sec38v_entry_rel hbar hz hz'
      apply mul_right_cancel₀ hd
      linear_combination (-1 : K) * this + (mat z ιe₁ ιf₁) * hrel1
    have hpow : ∀ n : ℕ, ∀ z ∈ ZPsub h, ∃ z'' ∈ ZPsub h,
        innM h z'' = ρ ^ n * innM h z * (ρ ^ n)⁻¹ ∧
          mat z'' ιe₁ ιf₁ = ν ^ n * mat z ιe₁ ιf₁ := by
      intro n
      induction n with
      | zero => intro z hz; exact ⟨z, hz, by simp, by simp⟩
      | succ n ih =>
        intro z hz
        obtain ⟨z1, hz1, e1, e2⟩ := ih z hz
        obtain ⟨hz2, e3⟩ := hgen z1 hz1
        refine ⟨act h x z1, hz2, ?_, ?_⟩
        · rw [← Phi_mul_innM_mul_inv, hx, e1, pow_succ']
          group
        · rw [e3, e2, pow_succ]
          ring
    obtain ⟨z'', hz'', e1, e2⟩ := hpow (2 ^ j) _ hz1
    rw [hj', one_mul, inv_one, mul_one] at e1
    have e3 : z'' = z₁SU h := innM_injOn hZ (ZPsub_le_U hz'') (ZPsub_le_U hz1) e1
    rw [e3, mat_z₁SU_e₁f₁, mul_one] at e2
    have hνbar : h.bar ν = ν := by
      have := sec38v_bar_entry hz1'
      rwa [hν] at this
    rw [h.bar_apply] at hνbar
    have hfpos : 1 ≤ f := h.one_le
    have hν1 : ν ^ (2 ^ f - 1) = 1 := by
      have h2f : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      apply mul_right_cancel₀ hν0
      rw [← pow_succ, Nat.sub_add_cancel h2f, hνbar, one_mul]
    have hodd : Odd (2 ^ f - 1) := by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      have h2 : 2 ^ (g + 1) = 2 * 2 ^ g := by ring
      have hpos : 1 ≤ 2 ^ g := Nat.one_le_two_pow
      exact ⟨2 ^ g - 1, by omega⟩
    have hcop : Nat.Coprime (2 ^ j) (2 ^ f - 1) :=
      Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hodd)
    have hν : ν = 1 := by
      have h1 : orderOf ν ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one e2.symm
      have h2 : orderOf ν ∣ 2 ^ f - 1 := orderOf_dvd_of_pow_eq_one hν1
      have h3 : orderOf ν ∣ Nat.gcd (2 ^ j) (2 ^ f - 1) := Nat.dvd_gcd h1 h2
      rw [Nat.Coprime.gcd_eq_one hcop] at h3
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
    have hact : act h x z = z := by
      obtain ⟨hz', e⟩ := hgen z hz
      rw [hν, one_mul] at e
      exact eq_of_mem_ZPsub hz' hz e
    rw [← hx, Phi_mul_innM_mul_inv, hact]

end ModelU

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem Hyp.sec38v_eq_of_act_eq (hd : d.Hyp) {a b : G} (ha : a ∈ d.L) (hb : b ∈ d.L)
    (e : d.act ⟨a, le_normalizer ha⟩ = d.act ⟨b, le_normalizer hb⟩) : a = b := by
  have hN : ∀ x ∈ d.L, x ∈ normalizer (d.L : Set G) := fun x hx => le_normalizer hx
  have hc : a⁻¹ * b ∈ centralizer (d.L : Set G) := by
    refine (d.act_eq_one_iff ⟨a⁻¹ * b, mul_mem (inv_mem (hN a ha)) (hN b hb)⟩).1 ?_
    have e' : (⟨a⁻¹ * b, mul_mem (inv_mem (hN a ha)) (hN b hb)⟩ : normalizer (d.L : Set G)) =
        (⟨a, hN a ha⟩ : normalizer (d.L : Set G))⁻¹ * ⟨b, hN b hb⟩ := rfl
    rw [e', map_mul, map_inv, e, inv_mul_cancel]
  have hL : a⁻¹ * b ∈ d.L := mul_mem (inv_mem ha) hb
  have h1 : a⁻¹ * b ∈ d.L ⊓ centralizer (d.L : Set G) := ⟨hL, hc⟩
  rw [hd.inf_centralizer_eq_bot, mem_bot] at h1
  exact inv_mul_eq_one.1 h1

theorem Hyp.sec38v_comm_of_act (hd : d.Hyp) {s : G} (hsN : s ∈ normalizer (d.L : Set G))
    {g : hypSU h 2 1}
    (hg : d.act ⟨s, hsN⟩ * CFSG.RankThree.PartOne.U5K.Hyp.innM h g * (d.act ⟨s, hsN⟩)⁻¹ =
      CFSG.RankThree.PartOne.U5K.Hyp.innM h g) :
    s * d.η g * s⁻¹ = d.η g := by
  have haL : d.η g ∈ d.L := d.η_mem g
  have hbL : s * d.η g * s⁻¹ ∈ d.L := (mem_normalizer_iff.1 hsN _).1 haL
  refine hd.sec38v_eq_of_act_eq hbL haL ?_
  have e1 : (⟨s * d.η g * s⁻¹, le_normalizer hbL⟩ : normalizer (d.L : Set G)) =
      ⟨s, hsN⟩ * ⟨d.η g, le_normalizer haL⟩ * ⟨s, hsN⟩⁻¹ := rfl
  rw [e1, map_mul, map_mul, map_inv, d.act_η, hg]

theorem Hyp.sec38v_centralizes_Zp (hd : d.Hyp) {s : G} (hs : s ∈ d.T) (hs2 : s * s ∈ d.P)
    {z : G} (hz : z ∈ d.Zp) : s * z * s⁻¹ = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsN : s ∈ normalizer (d.L : Set G) := hd.T_le_normalizer hs
  by_cases hst : s ∈ d.tP
  · have hzc : z ∈ CFSG.centerIn d.P := by
      rw [d.sec2_2_three.2.2.2.2]
      exact hz
    obtain ⟨p, hp, hsp | hsp⟩ := hd.exists_of_mem_zpowers_sup d.P_le_L hst
    · rw [hsp]
      exact mul_inv_eq_iff_eq_mul.2 (mem_centralizer_iff.1 hzc.2 p hp)
    · have hzt : z * d.t = d.t * z := hd.comm_t (d.Zp_le_L hz)
      have hpz : p * z = z * p := mem_centralizer_iff.1 hzc.2 p hp
      rw [hsp]
      calc d.t * p * z * (d.t * p)⁻¹ = d.t * (p * z) * p⁻¹ * d.t⁻¹ := by group
        _ = d.t * (z * p) * p⁻¹ * d.t⁻¹ := by rw [hpz]
        _ = d.t * z * d.t⁻¹ := by group
        _ = z := mul_inv_eq_iff_eq_mul.2 hzt.symm
  · have hout : d.act ⟨s, hsN⟩ ∉ CFSG.RankThree.PartOne.U5K.Hyp.Pi h := fun e =>
      hst (hd.mem_tP_of_act_mem_Pi hs hsN e)
    have hT2 : IsPGroup 2 (d.actImage d.T) :=
      (hd.isPGroup_T.comap_subtype (K := normalizer (d.L : Set G))).map _
    have hs2' : d.act ⟨s, hsN⟩ * d.act ⟨s, hsN⟩ ∈ CFSG.RankThree.PartOne.U5K.Hyp.Pi h := by
      rw [← map_mul]
      have hP : d.act (⟨s, hsN⟩ * ⟨s, hsN⟩) ∈ d.actImage d.P :=
        d.mem_actImage.2 ⟨s * s, hs2, _, rfl⟩
      rw [d.actImage_P] at hP
      exact CFSG.RankThree.PartOne.U5K.Hyp.Uh_le_Pi hP
    obtain ⟨z0, hz0, rfl⟩ := hz
    have h1 := sec38v_centralizes_Zh hd.center_hypPSU hT2 hd.inf_Pi_actImage_T
      (d.mem_actImage.2 ⟨s, hs, hsN, rfl⟩) hs2' hz0
    exact hd.sec38v_comm_of_act hsN h1

@[expose] def sec38vOm (d : Data G h) : Subgroup G :=
  closure {x | x ∈ d.E ⊔ d.T ∧ x * x = 1}

theorem sec38vOm_le (d : Data G h) : d.sec38vOm ≤ d.E ⊔ d.T :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

theorem mem_sec38vOm {x : G} (hx : x ∈ d.E ⊔ d.T) (hx2 : x * x = 1) : x ∈ d.sec38vOm :=
  subset_closure ⟨hx, hx2⟩

theorem sec38v_exists_mul (hp : d.CaseHyp) {x : G} (hx : x ∈ d.E ⊔ d.T) :
    ∃ e ∈ d.E, ∃ s ∈ d.T, x = e * s :=
  exists_mul_of_mem_sup_of_le_normalizer (hp.hyp.T_le_normalizer_E hp.gms) hx

theorem Hyp.sec38v_T_le_normalizer_V (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) : d.T ≤ normalizer (d.V : Set G) := fun _ hs =>
  hd.normalizer_ZtP_le_normalizer_V hGMS
    (d.normalizer_tP_le_normalizer_ZtP (hd.normalizer_T_le (le_normalizer hs)))

theorem Hyp.sec38v_E_le_Om (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.E ≤ d.sec38vOm := by
  refine d.E_le fun n hn w hw => ?_
  refine mem_sec38vOm (mem_sup_left (d.conj_mem_E hn hw)) ?_
  have hw2 := hd.mul_self_eq_one_of_mem_F hGMS (hd.W_le_F hGMS hw)
  calc n * w * n⁻¹ * (n * w * n⁻¹) = n * (w * w) * n⁻¹ := by group
    _ = 1 := by rw [hw2]; group

theorem Hyp.sec38v_t_mem_Om (hd : d.Hyp) : d.t ∈ d.sec38vOm :=
  mem_sec38vOm (mem_sup_right hd.t_mem_T) hd.t_mul_t

theorem sec38v_conj_mem_Om {y : G} (hy : y ∈ normalizer ((d.E ⊔ d.T : Subgroup G) : Set G))
    {x : G} (hx : x ∈ d.sec38vOm) : y * x * y⁻¹ ∈ d.sec38vOm := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    refine mem_sec38vOm ((mem_normalizer_iff.1 hy x).1 hx.1) ?_
    calc y * x * y⁻¹ * (y * x * y⁻¹) = y * (x * x) * y⁻¹ := by group
      _ = 1 := by rw [hx.2]; group
  | one => simpa using one_mem _
  | mul a b _ _ ha hb =>
    have : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
    rw [this]
    exact mul_mem ha hb
  | inv a _ ha =>
    have : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem ha

theorem sec38v_mem_normalizer_of_centralizes {S : Subgroup G} {s : G}
    (hs : ∀ z ∈ S, s * z * s⁻¹ = z) : s ∈ normalizer (S : Set G) := by
  rw [mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    rwa [hs z hz]
  · intro hz
    have e := hs _ hz
    have e2 : s * z * s⁻¹ = z := by
      calc s * z * s⁻¹ = s⁻¹ * (s * (s * z * s⁻¹) * s⁻¹) * s := by group
        _ = s⁻¹ * (s * z * s⁻¹) * s := by rw [e]
        _ = z := by group
    rwa [e2] at hz

theorem sec38v_comm_V_T (hp : d.CaseHyp) {s : G} (hs : s ∈ d.T)
    (hsZ : ∀ z ∈ d.Zp, s * z * s⁻¹ = z) {v : G} (hv : v ∈ d.V) : ⁅v, s⁆ ∈ d.Zp := by
  obtain ⟨-, -, -, -, -, -, -, -, ψ, -, hker, -, hequi⟩ := hp.hyp.sec3_3_one hp.gms
  have hsC : s ∈ normalizer (d.Zp : Set G) ⊓ centralizer ({d.t} : Set G) :=
    ⟨sec38v_mem_normalizer_of_centralizes hsZ, hp.hyp.T_le_centralizer hs⟩
  obtain ⟨hvs, hψ⟩ := hequi s hsC ⟨v, hv⟩
  have h1 : (ψ ⟨s * v * s⁻¹, hvs⟩ : G) = ψ ⟨v, hv⟩ := by
    rw [hψ]
    exact hsZ _ (ψ ⟨v, hv⟩).2
  have h2 : ψ ⟨s * v * s⁻¹, hvs⟩ = ψ ⟨v, hv⟩ := Subtype.ext h1
  have h3 : (⟨s * v * s⁻¹, hvs⟩ : d.V) * (⟨v, hv⟩ : d.V)⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h2, mul_inv_cancel]
  rw [hker] at h3
  have h4 : s * v * s⁻¹ * v⁻¹ ∈ d.Zp := h3
  have e : ⁅v, s⁆ = (s * v * s⁻¹ * v⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact inv_mem h4

theorem sec38v_sq_mem_A₂ (hp : d.CaseHyp) {e s : G} (he : e ∈ d.E) (hs : s ∈ d.T)
    (hx : e * s * (e * s) = 1) : s * s ∈ d.A₂ := by
  have hsN := hp.hyp.T_le_normalizer_E hp.gms hs
  have hse : s * e * s⁻¹ ∈ d.E := (mem_normalizer_iff.1 hsN e).1 he
  have h0 : e * (s * e * s⁻¹) * (s * s) = 1 := by
    rw [← hx]
    group
  have h1 : s * s = (e * (s * e * s⁻¹))⁻¹ := eq_inv_of_mul_eq_one_right h0
  have h2 : s * s ∈ d.E := by
    rw [h1]
    exact inv_mem (mul_mem he hse)
  exact hp.hyp.E_inf_T_le_A₂ hp.gms ⟨h2, mul_mem hs hs⟩

theorem sec38v_invol (hp : d.CaseHyp) {x : G} (hx : x ∈ d.E ⊔ d.T) (hx2 : x * x = 1) :
    (∀ z ∈ d.Zp, x * z * x⁻¹ = z) ∧ ∀ v ∈ d.V, ⁅v, x⁆ ∈ d.Zp := by
  obtain ⟨e, he, s, hs, rfl⟩ := sec38v_exists_mul hp hx
  have hsq := sec38v_sq_mem_A₂ hp he hs hx2
  have hsZ : ∀ z ∈ d.Zp, s * z * s⁻¹ = z := fun z hz =>
    hp.hyp.sec38v_centralizes_Zp hs (d.A₂_le_P hsq) hz
  have hEV : ∀ v ∈ d.V, e * v * e⁻¹ = v := fun v hv =>
    mul_inv_eq_iff_eq_mul.2 (hp.hyp.sec38a1_V_comm hp.gms hv he)
  refine ⟨fun z hz => ?_, fun v hv => ?_⟩
  · calc e * s * z * (e * s)⁻¹ = e * (s * z * s⁻¹) * e⁻¹ := by group
      _ = e * z * e⁻¹ := by rw [hsZ z hz]
      _ = z := hEV z (hp.hyp.Zp_le_V hz)
  · have hsv : s * v⁻¹ * s⁻¹ ∈ d.V :=
      (mem_normalizer_iff.1 (hp.hyp.sec38v_T_le_normalizer_V hp.gms hs) v⁻¹).1 (inv_mem hv)
    have e1 : ⁅v, e * s⁆ = ⁅v, s⁆ := by
      calc ⁅v, e * s⁆ = v * (e * (s * v⁻¹ * s⁻¹) * e⁻¹) := by
            simp only [commutatorElement_def]; group
        _ = ⁅v, s⁆ := by rw [hEV _ hsv]; simp only [commutatorElement_def]; group
    rw [e1]
    exact sec38v_comm_V_T hp hs hsZ hv

theorem sec38v_Q_mul {x y : G} (hx : ∀ z ∈ d.Zp, x * z * x⁻¹ = z)
    (hy : ∀ z ∈ d.Zp, y * z * y⁻¹ = z) (hxV : ∀ v ∈ d.V, ⁅v, x⁆ ∈ d.Zp)
    (hyV : ∀ v ∈ d.V, ⁅v, y⁆ ∈ d.Zp) :
    (∀ z ∈ d.Zp, x * y * z * (x * y)⁻¹ = z) ∧ ∀ v ∈ d.V, ⁅v, x * y⁆ ∈ d.Zp := by
  refine ⟨fun z hz => ?_, fun v hv => ?_⟩
  · calc x * y * z * (x * y)⁻¹ = x * (y * z * y⁻¹) * x⁻¹ := by group
      _ = z := by rw [hy z hz, hx z hz]
  · have e : ⁅v, x * y⁆ = ⁅v, x⁆ * (x * ⁅v, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e, hx _ (hyV v hv)]
    exact mul_mem (hxV v hv) (hyV v hv)

theorem sec38v_Q_inv {x : G} (hx : ∀ z ∈ d.Zp, x * z * x⁻¹ = z)
    (hxV : ∀ v ∈ d.V, ⁅v, x⁆ ∈ d.Zp) :
    (∀ z ∈ d.Zp, x⁻¹ * z * x⁻¹⁻¹ = z) ∧ ∀ v ∈ d.V, ⁅v, x⁻¹⁆ ∈ d.Zp := by
  have hinv : ∀ z ∈ d.Zp, x⁻¹ * z * x⁻¹⁻¹ = z := by
    intro z hz
    have e := hx z hz
    calc x⁻¹ * z * x⁻¹⁻¹ = x⁻¹ * (x * z * x⁻¹) * x := by rw [e]; group
      _ = z := by group
  refine ⟨hinv, fun v hv => ?_⟩
  have hw := hxV v hv
  have e : ⁅v, x⁻¹⁆ = x⁻¹ * (⁅v, x⁆)⁻¹ * x⁻¹⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e, hinv _ (inv_mem hw)]
  exact inv_mem hw

theorem sec38v_Om_prop (hp : d.CaseHyp) {x : G} (hx : x ∈ d.sec38vOm) :
    (∀ z ∈ d.Zp, x * z * x⁻¹ = z) ∧ ∀ v ∈ d.V, ⁅v, x⁆ ∈ d.Zp := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact sec38v_invol hp hx.1 hx.2
  | one =>
    refine ⟨fun z _ => by simp, fun v _ => ?_⟩
    rw [commutatorElement_one_right]
    exact one_mem _
  | mul a b _ _ ha hb => exact sec38v_Q_mul ha.1 hb.1 ha.2 hb.2
  | inv a _ ha => exact sec38v_Q_inv ha.1 ha.2

theorem sec38v_s_mem_A₂ (hp : d.CaseHyp)
    (hCTE : ∀ x ∈ d.T, (∀ e ∈ d.E, ⁅e, x⁆ ∈ d.V) → x ∈ d.A₂) {e0 s : G} (he0 : e0 ∈ d.E)
    (hs : s ∈ d.T) (hc : ∀ e ∈ d.E, ⁅e0 * s, e⁆ ∈ d.V) : s ∈ d.A₂ := by
  refine hCTE s hs fun e he => ?_
  have hE := hp.hyp.elemAbMod_V_E hp.gms
  have h1 : ⁅e0, e⁆ ∈ d.V := hE.2 e0 he0 e he
  have hwV : e0 * ⁅s, e⁆ * e0⁻¹ ∈ d.V := by
    have e1 : ⁅e0 * s, e⁆ * ⁅e0, e⁆⁻¹ = e0 * ⁅s, e⁆ * e0⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [← e1]
    exact mul_mem (hc e he) (inv_mem h1)
  have hcomm : e0 * (e0 * ⁅s, e⁆ * e0⁻¹) = (e0 * ⁅s, e⁆ * e0⁻¹) * e0 :=
    hp.hyp.sec38a1_V_comm hp.gms hwV he0
  have e2 : ⁅s, e⁆ = e0 * ⁅s, e⁆ * e0⁻¹ := by
    calc ⁅s, e⁆ = e0⁻¹ * (e0 * ⁅s, e⁆ * e0⁻¹) * e0 := by group
      _ = e0⁻¹ * ((e0 * ⁅s, e⁆ * e0⁻¹) * e0) := by group
      _ = e0⁻¹ * (e0 * (e0 * ⁅s, e⁆ * e0⁻¹)) := by rw [← hcomm]
      _ = e0 * ⁅s, e⁆ * e0⁻¹ := by group
  have hsV : ⁅s, e⁆ ∈ d.V := by
    rw [e2]
    exact hwV
  have := inv_mem hsV
  rwa [commutatorElement_inv] at this

theorem sec38v_center_Om (hp : d.CaseHyp)
    (hCTE : ∀ x ∈ d.T, (∀ e ∈ d.E, ⁅e, x⁆ ∈ d.V) → x ∈ d.A₂) {z : G} :
    z ∈ d.Zp ↔ z ∈ d.sec38vOm ∧ ∀ w ∈ d.sec38vOm, z * w = w * z := by
  have hd := hp.hyp
  have hG := hp.gms
  constructor
  · intro hz
    refine ⟨hd.sec38v_E_le_Om hG (d.V_le_E (hd.Zp_le_V hz)), fun w hw => ?_⟩
    exact (mul_inv_eq_iff_eq_mul.1 ((sec38v_Om_prop hp hw).1 z hz)).symm
  · rintro ⟨hzΩ, hzc⟩
    obtain ⟨e0, he0, s, hs, hzeq⟩ := sec38v_exists_mul hp (sec38vOm_le d hzΩ)
    have hEΩ := hd.sec38v_E_le_Om hG
    have hsA : s ∈ d.A₂ := by
      refine sec38v_s_mem_A₂ hp hCTE he0 hs fun e he => ?_
      have h1 : ⁅e0 * s, e⁆ = 1 := by
        rw [← hzeq]
        exact commutatorElement_eq_one_iff_mul_comm.2 (hzc e (hEΩ he))
      rw [h1]
      exact one_mem _
    have hzE : z ∈ d.E := by
      rw [hzeq]
      exact mul_mem he0 (hd.A₂_le_E hG hsA)
    have hzV : z ∈ d.V := by
      rw [← hd.centerIn_E hG]
      exact ⟨hzE, mem_centralizer_iff.2 fun y hy => (hzc y (hEΩ hy)).symm⟩
    have hzt : z ∈ d.V ⊓ centralizer ({d.t} : Set G) :=
      ⟨hzV, mem_centralizer_singleton_iff.2 (hzc d.t hd.sec38v_t_mem_Om)⟩
    rwa [hd.V_inf_centralizer_t] at hzt

theorem sec38v_Z₂_le (hp : d.CaseHyp)
    (hCTE : ∀ x ∈ d.T, (∀ e ∈ d.E, ⁅e, x⁆ ∈ d.V) → x ∈ d.A₂) {x : G} (hx : x ∈ d.sec38vOm)
    (hxc : ∀ w ∈ d.sec38vOm, ⁅x, w⁆ ∈ d.Zp) : x ∈ d.V := by
  have hd := hp.hyp
  have hG := hp.gms
  have hEΩ := hd.sec38v_E_le_Om hG
  obtain ⟨e0, he0, s, hs, hxeq⟩ := sec38v_exists_mul hp (sec38vOm_le d hx)
  have hsA : s ∈ d.A₂ := by
    refine sec38v_s_mem_A₂ hp hCTE he0 hs fun e he => ?_
    rw [← hxeq]
    exact hd.Zp_le_V (hxc e (hEΩ he))
  have hxE : x ∈ d.E := by
    rw [hxeq]
    exact mul_mem he0 (hd.A₂_le_E hG hsA)
  have hxVA : x ∈ d.V ⊔ d.A₂ := by
    have h1 := hd.Zp_le_V (hxc d.t hd.sec38v_t_mem_Om)
    have h2 : (x⁻¹)⁻¹ * d.t * x⁻¹ * d.t ∈ d.V := by
      have e1 : (x⁻¹)⁻¹ * d.t * x⁻¹ * d.t = ⁅x, d.t⁆ := by
        rw [commutatorElement_def, hd.sec38a1_inv_t]
        group
      rw [e1]
      exact h1
    have := inv_mem (hd.sec38a1_mem_VA hG (inv_mem hxE) h2)
    rwa [inv_inv] at this
  obtain ⟨v, hv, a, ha, hva⟩ := hd.exists_mul_of_mem_VA hxVA
  have haE : a ∈ d.E := hd.A₂_le_E hG ha
  have haZ : a ∈ d.Zp := by
    refine sec38e1_A2E hp ha fun e he => ?_
    have e1 : ⁅v * a, e⁆ = ⁅a, e⁆ := by
      have hc : v * (a * e * a⁻¹) = (a * e * a⁻¹) * v := by
        have := hd.sec38a1_V_comm hG hv (mul_mem (mul_mem haE he) (inv_mem haE))
        exact this.symm
      simp only [commutatorElement_def]
      calc v * a * e * (v * a)⁻¹ * e⁻¹ = (v * (a * e * a⁻¹) * v⁻¹) * e⁻¹ := by group
        _ = a * e * a⁻¹ * e⁻¹ := by rw [hc]; group
    rw [← e1, ← hva]
    exact hxc e (hEΩ he)
  rw [hva]
  exact mul_mem hv (hd.Zp_le_V haZ)

theorem sec38v_conj_mem_Zp (hp : d.CaseHyp)
    (hCTE : ∀ x ∈ d.T, (∀ e ∈ d.E, ⁅e, x⁆ ∈ d.V) → x ∈ d.A₂) {y : G}
    (hy : y ∈ normalizer ((d.E ⊔ d.T : Subgroup G) : Set G)) {z : G} (hz : z ∈ d.Zp) :
    y * z * y⁻¹ ∈ d.Zp := by
  have hz' := (sec38v_center_Om hp hCTE).1 hz
  rw [sec38v_center_Om hp hCTE]
  refine ⟨sec38v_conj_mem_Om hy hz'.1, fun w hw => ?_⟩
  have hw' : y⁻¹ * w * y⁻¹⁻¹ ∈ d.sec38vOm := sec38v_conj_mem_Om (inv_mem hy) hw
  have hc := hz'.2 _ hw'
  calc y * z * y⁻¹ * w = y * (z * (y⁻¹ * w * y⁻¹⁻¹)) * y⁻¹ := by group
    _ = y * ((y⁻¹ * w * y⁻¹⁻¹) * z) * y⁻¹ := by rw [hc]
    _ = w * (y * z * y⁻¹) := by group

theorem sec38a3_of_facts (hp : d.CaseHyp)
    (hCTE : ∀ x ∈ d.T, (∀ e ∈ d.E, ⁅e, x⁆ ∈ d.V) → x ∈ d.A₂) :
    ∀ y ∈ normalizer ((d.E ⊔ d.T : Subgroup G) : Set G), y ∈ normalizer (d.V : Set G) := by
  have hd := hp.hyp
  have hG := hp.gms
  have key : ∀ y ∈ normalizer ((d.E ⊔ d.T : Subgroup G) : Set G), ∀ v ∈ d.V,
      y * v * y⁻¹ ∈ d.V := by
    intro y hy v hv
    have hvΩ : v ∈ d.sec38vOm := hd.sec38v_E_le_Om hG (d.V_le_E hv)
    refine sec38v_Z₂_le hp hCTE (sec38v_conj_mem_Om hy hvΩ) fun w hw => ?_
    have hw' : y⁻¹ * w * y⁻¹⁻¹ ∈ d.sec38vOm := sec38v_conj_mem_Om (inv_mem hy) hw
    have h1 := (sec38v_Om_prop hp hw').2 v hv
    have e : ⁅y * v * y⁻¹, w⁆ = y * ⁅v, y⁻¹ * w * y⁻¹⁻¹⁆ * y⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact sec38v_conj_mem_Zp hp hCTE hy h1
  intro y hy
  rw [mem_normalizer_iff]
  intro v
  refine ⟨key y hy v, fun hv => ?_⟩
  have := key y⁻¹ (inv_mem hy) _ hv
  have e : y⁻¹ * (y * v * y⁻¹) * y⁻¹⁻¹ = v := by group
  rwa [e] at this

theorem sec38a3 (hp : d.CaseHyp) :
    ∀ y ∈ normalizer ((d.E ⊔ d.T : Subgroup G) : Set G), y ∈ normalizer (d.V : Set G) :=
  sec38a3_of_facts hp fun _ hx h => sec38e1_CTE hp hx h

end Data

end CFSG.LocalAnalysis.EvenBN.U5
