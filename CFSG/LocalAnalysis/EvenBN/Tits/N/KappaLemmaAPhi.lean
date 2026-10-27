module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.KappaLemmaACrd
public import CFSG.LocalAnalysis.EvenBN.Tits.S56V1

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.KappaA

open Matrix Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits
  CFSG.LocalAnalysis.EvenBN.Tits.Model

variable {G : Type} [Group G] [Finite G] {d : Data G}


@[expose] noncomputable def zc (u : G) : ZMod 2 := open Classical in if u = 1 then 0 else 1

theorem zc_one : zc (1 : G) = 0 := by
  simp [zc]

theorem zc_z (hd : d.Hyp) : zc d.z = 1 := by
  simp [zc, hd.s56_z_ne_one]

theorem zpow_zc (hd : d.Hyp) {u : G} (hu : u ∈ zpowers d.z) : u = d.z ^ (zc u).val := by
  rcases hd.s56_mem_zpowers_z hu with rfl | rfl
  · simp [zc_one]
  · rw [zc_z hd, ZMod.val_one 2, pow_one]

theorem zc_mul (hd : d.Hyp) {u u' : G} (hu : u ∈ zpowers d.z) (hu' : u' ∈ zpowers d.z) :
    zc (u * u') = zc u + zc u' := by
  rcases hd.s56_mem_zpowers_z hu with rfl | rfl <;>
    rcases hd.s56_mem_zpowers_z hu' with rfl | rfl
  · simp [zc_one]
  · simp [zc_one]
  · simp [zc_one]
  · rw [hd.s56_z_sq, zc_one, zc_z hd]
    decide

theorem zc_conj (hd : d.Hyp) {g : G} (hg : g * d.z = d.z * g) {u : G} (hu : u ∈ zpowers d.z) :
    zc (g * u * g⁻¹) = zc u := by
  rcases hd.s56_mem_zpowers_z hu with rfl | rfl
  · simp
  · have h : g * d.z * g⁻¹ = d.z := by rw [hg]; group
    rw [h]

@[expose] noncomputable def phi (_d : Data G) (q e : G) : ZMod 2 := zc (q * e * q⁻¹ * e⁻¹)

theorem phi_mem (hd : d.Hyp) {q e : G} (hq : q ∈ d.s56J) (he : e ∈ d.E) :
    q * e * q⁻¹ * e⁻¹ = d.z ^ (phi d q e).val :=
  zpow_zc hd (hd.s56_J_comm_E hq he)

theorem phi_mul_left (hd : d.Hyp) {q q' e : G} (hq : q ∈ d.s56J) (hq' : q' ∈ d.s56J)
    (he : e ∈ d.E) : phi d (q * q') e = phi d q e + phi d q' e := by
  have hc := hd.s56_J_comm_E hq he
  have hc' := hd.s56_J_comm_E hq' he
  have hcomm : q * (q' * e * q'⁻¹ * e⁻¹) * q⁻¹ = q' * e * q'⁻¹ * e⁻¹ := by
    rw [hd.s56_M_comm_zpowers (hd.s56_J_le_M hq) hc']
    group
  have key : q * q' * e * (q * q')⁻¹ * e⁻¹ =
      (q * (q' * e * q'⁻¹ * e⁻¹) * q⁻¹) * (q * e * q⁻¹ * e⁻¹) := by
    group
  unfold phi
  rw [key, hcomm, zc_mul hd hc' hc]
  exact add_comm _ _

theorem phi_mul_right (hd : d.Hyp) {q e e' : G} (hq : q ∈ d.s56J) (he : e ∈ d.E)
    (he' : e' ∈ d.E) : phi d q (e * e') = phi d q e + phi d q e' := by
  have hc := hd.s56_J_comm_E hq he
  have hc' := hd.s56_J_comm_E hq he'
  have hEc' : e * (q * e' * q⁻¹ * e'⁻¹) = (q * e' * q⁻¹ * e'⁻¹) * e :=
    hd.s56_E_comm he (hd.s56_zpowers_le_E hc')
  have key : q * (e * e') * q⁻¹ * (e * e')⁻¹ =
      (q * e * q⁻¹ * e⁻¹) * (q * e' * q⁻¹ * e'⁻¹) := by
    calc q * (e * e') * q⁻¹ * (e * e')⁻¹
        = (q * e * q⁻¹ * e⁻¹) * (e * (q * e' * q⁻¹ * e'⁻¹) * e⁻¹) := by group
      _ = (q * e * q⁻¹ * e⁻¹) * (q * e' * q⁻¹ * e'⁻¹) := by rw [hEc']; group
  unfold phi
  rw [key, zc_mul hd hc hc']

theorem phi_z (hd : d.Hyp) {q : G} (hq : q ∈ d.s56J) : phi d q d.z = 0 := by
  have h : q * d.z * q⁻¹ * d.z⁻¹ = 1 := by
    rw [hd.s56_M_comm_z (hd.s56_J_le_M hq)]
    group
  unfold phi
  rw [h, zc_one]

theorem phi_eq_zero_iff (hd : d.Hyp) {q e : G} (hq : q ∈ d.s56J) (he : e ∈ d.E) :
    phi d q e = 0 ↔ q * e = e * q := by
  constructor
  · intro h
    have h1 : q * e * q⁻¹ * e⁻¹ = 1 := by
      have h2 := phi_mem hd hq he
      rw [h] at h2
      simpa using h2
    calc q * e = (q * e * q⁻¹ * e⁻¹) * (e * q) := by group
      _ = e * q := by rw [h1, one_mul]
  · intro h
    have h1 : q * e * q⁻¹ * e⁻¹ = 1 := by
      rw [h]
      group
    unfold phi
    rw [h1, zc_one]

theorem phi_conj (hd : d.Hyp) {g q e : G} (hg : g * d.z = d.z * g) (hq : q ∈ d.s56J)
    (he : e ∈ d.E) : phi d (g * q * g⁻¹) (g * e * g⁻¹) = phi d q e := by
  have h : g * q * g⁻¹ * (g * e * g⁻¹) * (g * q * g⁻¹)⁻¹ * (g * e * g⁻¹)⁻¹ =
      g * (q * e * q⁻¹ * e⁻¹) * g⁻¹ := by
    group
  unfold phi
  rw [h]
  exact zc_conj hd hg (hd.s56_J_comm_E hq he)

theorem phi_pv_mem_E (hd : d.Hyp) {i : ℕ} (hi8 : 8 ≤ i) (hi12 : i ≤ 12) : d.pv i ∈ d.E := by
  have h := crdE_mem hd (Pi.single (⟨12 - i, by omega⟩ : Fin 5) 1)
  have e : basisV (⟨12 - i, by omega⟩ : Fin 5) = i := by
    show 12 - (12 - i) = i
    omega
  rwa [crdE_single, e] at h

theorem phi_pv_mem_E_fin (hd : d.Hyp) (i : Fin 4) : d.pv (11 - i.val) ∈ d.E := by
  have := i.isLt
  exact phi_pv_mem_E hd (by omega) (by omega)

theorem phi_pv12 (d : Data G) : d.pv 12 = d.z := by
  rw [Data.pv, Model.parrottV_twelve, d.lift_titsZ]

theorem phi_pv_mem_F (d : Data G) {i : ℕ} (hi : i ∈ ({7, 9, 10, 11, 12} : Set ℕ)) :
    d.pv i ∈ d.F :=
  (Data.mem_liftSub (d := d)).2 ⟨_, Model.parrottV_mem_parrottF hi,
    Model.parrottF_le_titsD (Model.parrottV_mem_parrottF hi), rfl⟩

theorem phi_pow_val {q x : G} (n : ZMod 2) : phi d q (x ^ n.val) = n * phi d q x := by
  have hn : n = 0 ∨ n = 1 := by
    revert n
    decide
  rcases hn with rfl | rfl
  · simp [phi, zc_one]
  · simp [ZMod.val_one 2]

@[expose] noncomputable def fb (d : Data G) (q : G) : W4 := fun i => phi d q (d.pv (11 - i.val))

theorem phi_crdE (hd : d.Hyp) {q : G} (hq : q ∈ d.s56J) (c : Fin 5 → ZMod 2) :
    phi d q (crdE d c) = ∑ i : Fin 4, fb d q i * c i.succ := by
  have m0 : d.pv 12 ^ (c 0).val ∈ d.E := pow_mem (phi_pv_mem_E hd (by norm_num) (by norm_num)) _
  have m1 : d.pv 11 ^ (c 1).val ∈ d.E := pow_mem (phi_pv_mem_E hd (by norm_num) (by norm_num)) _
  have m2 : d.pv 10 ^ (c 2).val ∈ d.E := pow_mem (phi_pv_mem_E hd (by norm_num) (by norm_num)) _
  have m3 : d.pv 9 ^ (c 3).val ∈ d.E := pow_mem (phi_pv_mem_E hd (by norm_num) (by norm_num)) _
  have m4 : d.pv 8 ^ (c 4).val ∈ d.E := pow_mem (phi_pv_mem_E hd (by norm_num) (by norm_num)) _
  have p12 : phi d q (d.pv 12) = 0 := by
    rw [phi_pv12, phi_z hd hq]
  unfold crdE
  rw [phi_mul_right hd hq (mul_mem (mul_mem (mul_mem m0 m1) m2) m3) m4,
    phi_mul_right hd hq (mul_mem (mul_mem m0 m1) m2) m3, phi_mul_right hd hq (mul_mem m0 m1) m2,
    phi_mul_right hd hq m0 m1, phi_pow_val, phi_pow_val, phi_pow_val, phi_pow_val, phi_pow_val, p12,
    Fin.sum_univ_four]
  have f0 : fb d q 0 = phi d q (d.pv 11) := rfl
  have f1 : fb d q 1 = phi d q (d.pv 10) := rfl
  have f2 : fb d q 2 = phi d q (d.pv 9) := rfl
  have f3 : fb d q 3 = phi d q (d.pv 8) := rfl
  rw [f0, f1, f2, f3]
  show _ = _ * c 1 + _ * c 2 + _ * c 3 + _ * c 4
  ring

theorem phi_dot (hd : d.Hyp) {q u : G} (hq : q ∈ d.s56J) (hu : u ∈ d.E) :
    phi d q u = fb d q ⬝ᵥ wcoord d u := by
  obtain ⟨c, rfl⟩ := exists_crdE hd hu
  rw [phi_crdE hd hq c, wcoord_crdE hd c]
  rfl

theorem fb_mul (hd : d.Hyp) {q q' : G} (hq : q ∈ d.s56J) (hq' : q' ∈ d.s56J) :
    fb d (q * q') = fb d q + fb d q' := by
  funext i
  exact phi_mul_left hd hq hq' (phi_pv_mem_E_fin hd i)

theorem fb_eq_zero_iff (hd : d.Hyp) {q : G} (hq : q ∈ d.s56J) : fb d q = 0 ↔ q ∈ d.E := by
  constructor
  · intro h
    have hQ2 : q ∈ d.s56Q2 := by
      refine (Data.s56_mem_Q2_iff).2 ⟨hd.s56_J_le_M hq, fun e he => ?_⟩
      have h0 : phi d q e = 0 := by
        rw [phi_dot hd hq he, h]
        simp
      exact ((phi_eq_zero_iff hd hq he).1 h0).symm
    have h2 : q ∈ d.s56J ⊓ d.s56Q2 := mem_inf.2 ⟨hq, hQ2⟩
    rwa [hd.s56_J_inf_Q2] at h2
  · intro hqE
    funext i
    have hi := phi_pv_mem_E_fin hd i
    exact (phi_eq_zero_iff hd hq hi).2 (hd.s56_E_comm hqE hi)

theorem fb_surj (hd : d.Hyp) (b : W4) : ∃ q ∈ d.s56J, fb d q = b := by
  let f : d.s56J →* Multiplicative W4 :=
    MonoidHom.mk' (fun q => Multiplicative.ofAdd (fb d q.1)) (fun q q' => by
      show Multiplicative.ofAdd (fb d ((q * q' : d.s56J) : G)) = _
      rw [Subgroup.coe_mul, fb_mul hd q.2 q'.2]
      rfl)
  have hker : f.ker = d.E.subgroupOf d.s56J := by
    ext q
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show Multiplicative.ofAdd (fb d q.1) = 1 ↔ _
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
    exact fb_eq_zero_iff hd q.2
  have hcard := Subgroup.card_ker_mul_card_range f
  have hE : Nat.card (d.E.subgroupOf d.s56J) = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.s56_E_le_J).toEquiv]
    exact hd.A_facts.1
  rw [hker, hE, hd.s56_card_J] at hcard
  have hW : Nat.card (Multiplicative W4) = 16 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  have hrange : f.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hW]
    omega
  have hb : Multiplicative.ofAdd b ∈ f.range := by
    rw [hrange]
    exact Subgroup.mem_top _
  obtain ⟨q, hq⟩ := hb
  exact ⟨q.1, q.2, Multiplicative.ofAdd.injective hq⟩

theorem fb_conj (hd : d.Hyp) {g : G} (hgL : g ∈ d.L) (hgM : g ∈ d.M)
    (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) (hz : ∀ i, A i 0 = if i = 0 then 1 else 0)
    (hA : ∀ j : Fin 5, g * d.pv (basisV j) * g⁻¹ = crdE d (fun i => A i j)) {q : G}
    (hq : q ∈ d.s56J) :
    g * q * g⁻¹ ∈ d.s56J ∧
      (Matrix.of fun i j : Fin 4 => A i.succ j.succ)ᵀ *ᵥ fb d (g * q * g⁻¹) = fb d q := by
  have hq' : g * q * g⁻¹ ∈ d.s56J :=
    (mem_normalizer_iff.1 (hd.s56_L_inf_M_normalizes_J hgL hgM) q).1 hq
  refine ⟨hq', ?_⟩
  have key : ∀ w : W4,
      ((Matrix.of fun i j : Fin 4 => A i.succ j.succ)ᵀ *ᵥ fb d (g * q * g⁻¹)) ⬝ᵥ w =
        fb d q ⬝ᵥ w := by
    intro w
    obtain ⟨u, hu, rfl⟩ := wcoord_surj hd w
    obtain ⟨hgu, hw⟩ := wcoord_conj hd A hz hA hu
    rw [← phi_dot hd hq hu, ← phi_conj hd (hd.s56_M_comm_z hgM) hq hu, phi_dot hd hq' hgu, hw,
      Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
  funext k
  simpa using key (Pi.single k 1)

theorem fb_pv7 (hd : d.Hyp) : fb d (d.pv 7) = b0 := by
  have h7 : d.pv 7 ∈ d.s56J := d.s56_pv_mem_J (by simp)
  have hc : ∀ i : ℕ, 9 ≤ i → i ≤ 11 → phi d (d.pv 7) (d.pv i) = 0 := fun i h9 h11 => by
    have hE := phi_pv_mem_E hd (by omega) (by omega : i ≤ 12)
    refine (phi_eq_zero_iff hd h7 hE).2 ((hd.s56_pv7_comm_iff hE).2 (phi_pv_mem_F d ?_))
    have : i = 9 ∨ i = 10 ∨ i = 11 := by omega
    rcases this with rfl | rfl | rfl <;> simp
  have h8 : phi d (d.pv 7) (d.pv 8) = 1 := by
    have hE8 : d.pv 8 ∈ d.E := d.s56_pv8_mem_E
    have e : d.pv 7 * d.pv 8 * (d.pv 7)⁻¹ * (d.pv 8)⁻¹ = d.z := by
      rw [Data.s56_pv7_conj_pv8 d, hd.s56_E_comm hE8 hd.s56_z_mem_E]
      group
    unfold phi
    rw [e, zc_z hd]
  funext i
  fin_cases i
  · exact hc 11 (by norm_num) (by norm_num)
  · exact hc 10 (by norm_num) (by norm_num)
  · exact hc 9 (by norm_num) (by norm_num)
  · exact h8

@[expose] noncomputable def eb (d : Data G) (x : G) : W4 := wcoord d (d.s56Eps x)

theorem eb_mul (hd : d.Hyp) {x x' : G} (hx : x ∈ d.s56V) (hx' : x' ∈ d.s56V) :
    eb d (x * x') = eb d x + eb d x' := by
  unfold eb
  rw [hd.s56_eps_mul_Q2' (d.s56_V_le_Q2 hx) (d.s56_V_le_Q2 hx')]
  exact wcoord_mul hd (hd.s56_V_eps_mem_E hx) (hd.s56_V_eps_mem_E hx')

theorem eb_eq_zero_iff (hd : d.Hyp) {x : G} (hx : x ∈ d.s56V) :
    eb d x = 0 ↔ d.s56Eps x ∈ zpowers d.z :=
  wcoord_eq_zero_iff hd (hd.s56_V_eps_mem_E hx)

theorem eb_surj (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) (a : W4) :
    ∃ x ∈ d.s56V, eb d x = a := by
  obtain ⟨u, hu, rfl⟩ := wcoord_surj hd a
  obtain ⟨x, hx, hxu⟩ := hd.s56_V_eps_surj h49 hz u hu
  exact ⟨x, hx, by unfold eb; rw [hxu]⟩

theorem eb_conj (hd : d.Hyp) {g : G} (hgM : g ∈ d.M) (hgt : g * d.t = d.t * g)
    (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) (hz : ∀ i, A i 0 = if i = 0 then 1 else 0)
    (hA : ∀ j : Fin 5, g * d.pv (basisV j) * g⁻¹ = crdE d (fun i => A i j)) {x : G}
    (h49 : d.Thm49Statement) (hx : x ∈ d.s56V) :
    g * x * g⁻¹ ∈ d.s56V ∧
      eb d (g * x * g⁻¹) = (Matrix.of fun i j : Fin 4 => A i.succ j.succ) *ᵥ eb d x := by
  refine ⟨hd.s56_V_conj_mem h49 hgM hx, ?_⟩
  unfold eb
  rw [hd.s56_eps_conj hgt x]
  exact (wcoord_conj hd A hz hA (hd.s56_V_eps_mem_E hx)).2

theorem phi_eps (hd : d.Hyp) {q x : G} (hq : q ∈ d.s56J) (hx : x ∈ d.s56V) :
    phi d q (d.s56Eps x) = fb d q ⬝ᵥ eb d x :=
  phi_dot hd hq (hd.s56_V_eps_mem_E hx)

end CFSG.LocalAnalysis.EvenBN.Tits.N.KappaA
