module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadMonoCalc
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadMonoWeyl

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.ComponentClassification.CatLeafProof (weylWordElt)

set_option linter.unusedSectionVars false

theorem bm_forall_six {P : Fin Tag.E6.rank → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3)
    (h4 : P 4) (h5 : P 5) : ∀ j, P j := by
  intro j
  fin_cases j
  exacts [h0, h1, h2, h3, h4, h5]

theorem bm_inner_exp (y : Fin Tag.E6.rank → ℤ) (hL : (y 0 + 2 * y 2 + y 4 + 2 * y 5) % 3 = 0) :
    ∃ z : Fin Tag.E6.rank → ℤ, ∀ j, ∑ i, z i * Tag.E6.cartan i j = y j := by
  have key : ∀ y : Fin 6 → ℤ, (y 0 + 2 * y 2 + y 4 + 2 * y 5) % 3 = 0 →
      ∃ z : Fin 6 → ℤ, ∀ j, ∑ i, z i * Tag.cartanE 6 i j = y j := by
    intro y hL
    obtain ⟨a0, ha0⟩ : (3 : ℤ) ∣ 4 * y 0 + 3 * y 1 + 5 * y 2 + 6 * y 3 + 4 * y 4 + 2 * y 5 := by
      omega
    obtain ⟨a1, ha1⟩ : (3 : ℤ) ∣ 3 * y 0 + 6 * y 1 + 6 * y 2 + 9 * y 3 + 6 * y 4 + 3 * y 5 := by
      omega
    obtain ⟨a2, ha2⟩ : (3 : ℤ) ∣ 5 * y 0 + 6 * y 1 + 10 * y 2 + 12 * y 3 + 8 * y 4 + 4 * y 5 := by
      omega
    obtain ⟨a3, ha3⟩ : (3 : ℤ) ∣ 6 * y 0 + 9 * y 1 + 12 * y 2 + 18 * y 3 + 12 * y 4 + 6 * y 5 := by
      omega
    obtain ⟨a4, ha4⟩ : (3 : ℤ) ∣ 4 * y 0 + 6 * y 1 + 8 * y 2 + 12 * y 3 + 10 * y 4 + 5 * y 5 := by
      omega
    obtain ⟨a5, ha5⟩ : (3 : ℤ) ∣ 2 * y 0 + 3 * y 1 + 4 * y 2 + 6 * y 3 + 5 * y 4 + 4 * y 5 := by
      omega
    refine ⟨![a0, a1, a2, a3, a4, a5], fun j => ?_⟩
    fin_cases j <;> simp [Fin.sum_univ_six, Tag.cartanE] <;> omega
  exact key y hL

theorem bm_parab_exp (y : Fin Tag.E6.rank → ℤ) (h0 : (2 * y 0 + y 2) % 3 = 0) :
    ∃ x : Fin Tag.E6.rank → ℤ, y 0 + (∑ k, x k * bmTw 0 k - x 0) = 0 ∧
      y 2 + (∑ k, x k * bmTw 2 k - x 2) = 0 := by
  obtain ⟨a, ha⟩ : (3 : ℤ) ∣ y 0 - y 2 := by omega
  refine ⟨![a, 0, y 2 + a, 0, 0, 0], ?_, ?_⟩ <;> simp [bm_sum_six, bmTw] <;> omega

theorem bm_final_exp (y : Fin Tag.E6.rank → ℤ) (hl1 : (2 * y 4 + y 5) % 3 = 0)
    (hl3 : (y 1 + y 2 + 2 * y 5 - (2 * y 0 + y 2)) % 3 = 0) :
    ∃ x : Fin Tag.E6.rank → ℤ, ∀ j, y j + (∑ k, x k * bmTw j k - x j) =
      (![0, 0, 2 * y 0 + y 2, 0, 0, 0] : Fin Tag.E6.rank → ℤ) j := by
  obtain ⟨a, ha⟩ : (3 : ℤ) ∣ 2 * y 4 + y 5 := by omega
  obtain ⟨c, hc⟩ : (3 : ℤ) ∣ y 1 - 2 * y 0 + y 4 + y 5 := by omega
  obtain ⟨d, hd⟩ : (3 : ℤ) ∣ y 4 - y 5 := by omega
  obtain ⟨e, he⟩ : (3 : ℤ) ∣ y 4 + 2 * y 5 := by omega
  refine ⟨![y 0, y 0 - y 3 - a, -y 0, y 3 + c, d, e], bm_forall_six ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
    simp [bm_sum_six, bmTw] <;> omega

theorem bm_res {a : ℤ} (h : a % 3 ≠ 0) : a % 3 = 1 ∨ a % 3 = 2 := by
  omega

@[expose] def bmKhExp : Fin Tag.E6.rank → ℤ := ![0, 0, 0, 1, 0, 0]

theorem bm_moves_char : ∀ j : Fin Tag.E6.rank,
    (∑ k, bmKhExp k * bmInvA j k - bmKhExp j) % 3 = 0 ∧
    (∑ k, bmKhExp k * bmInvB j k - bmKhExp j) % 3 = 0 ∧
    (∑ k, bmKhExp k * bmInvC j k + bmKhExp j) % 3 = 0 ∧
    (∑ k, bmD0Exp k * bmInvA j k - bmD0Exp j) % 3 = 0 ∧
    (∑ k, bmD0Exp k * bmInvB j k - bmD0Exp j) % 3 = 0 ∧
    (∑ k, bmD0Exp k * bmInvC j k - bmD0Exp j) % 3 = 0 := by
  decide +kernel

@[expose] def bmStab {G : Type*} [Group G] (R : Subgroup G) : Subgroup (MulAut G) where
  carrier := {ε | R.map ε.toMonoidHom = R}
  mul_mem' {a b} ha hb := by
    change R.map a.toMonoidHom = R at ha
    change R.map b.toMonoidHom = R at hb
    change R.map (a * b).toMonoidHom = R
    rw [show (a * b).toMonoidHom = a.toMonoidHom.comp b.toMonoidHom from
      MonoidHom.ext fun _ => rfl, ← Subgroup.map_map, hb, ha]
  one_mem' := by
    change R.map (1 : MulAut G).toMonoidHom = R
    rw [show (1 : MulAut G).toMonoidHom = MonoidHom.id G from MonoidHom.ext fun _ => rfl,
      Subgroup.map_id]
  inv_mem' {a} ha := by
    change R.map a.toMonoidHom = R at ha
    change R.map a⁻¹.toMonoidHom = R
    conv_lhs => rw [← ha]
    rw [Subgroup.map_map, show a⁻¹.toMonoidHom.comp a.toMonoidHom = MonoidHom.id G from
      MonoidHom.ext fun x => MulAut.inv_apply_self G a x, Subgroup.map_id]

section Normal

variable
  {K : Type} [Field K]

@[expose] def bmX (K : Type) [Field K] (b : Fin Tag.E6.rank → Kˣ) :
    MulAut (adjointGroup Tag.E6 K) :=
  MulAut.conj (weylWordElt .E6 K e6BadWord) * rootDiagAutHom Tag.E6 K b

theorem e6BadX_eq_bmX (c : Kˣ) : e6BadX K c = bmX K ![1, 1, c, 1, 1, 1] :=
  rfl

theorem bm_weylTuple_pow {u : WeylGroup Tag.E6} {T : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ}
    (hT : ∀ j, u⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = T j) (g : Kˣ)
    (x : Fin Tag.E6.rank → ℤ) :
    weylTuple u (fun j => g ^ x j) = fun j => g ^ ∑ k, x k * T j k := by
  funext j
  simp only [weylTuple]
  rw [hT j, rootChar_zpow]

theorem bm_zpow_eq_of_emod {ω : Kˣ} (h3 : ω ^ 3 = 1) {a b : ℤ} (h : (a - b) % 3 = 0) :
    ω ^ a = ω ^ b := by
  have h3' : ω ^ (3 : ℤ) = 1 := by exact_mod_cast h3
  rw [zpow_eq_zpow_emod a h3', zpow_eq_zpow_emod b h3', show a % 3 = b % 3 by omega]

theorem bm_weylTuple_char {u : WeylGroup Tag.E6} {T : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ}
    (hT : ∀ j, u⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = T j) {ω : Kˣ} (h3 : ω ^ 3 = 1)
    {f e : Fin Tag.E6.rank → ℤ} (h : ∀ j, (∑ k, f k * T j k - e j) % 3 = 0) :
    weylTuple u (fun j => ω ^ f j) = fun j => ω ^ e j := by
  rw [bm_weylTuple_pow hT]
  funext j
  exact bm_zpow_eq_of_emod h3 (h j)

theorem bm_e6LineChar_eq (ω : Kˣ) : e6LineChar ω = fun j => ω ^ bmKhExp j := by
  have h0 : ω ^ (0 : ℤ) = 1 := zpow_zero ω
  have h1 : ω ^ (1 : ℤ) = ω := zpow_one ω
  funext j
  fin_cases j
  exacts [h0.symm, h0.symm, h0.symm, h1.symm, h0.symm, h0.symm]

theorem bm_e6D0Char_zpow (ω : Kˣ) : e6D0Char ω = fun j => ω ^ bmD0Exp j :=
  e6D0Char_eq ω

theorem bm_moveA_kh {ω : Kˣ} (h3 : ω ^ 3 = 1) :
    weylTuple ((coxeterSystem Tag.E6).wordProd bmMoveA) (e6LineChar ω) = e6LineChar ω := by
  rw [bm_e6LineChar_eq]
  exact bm_weylTuple_char bm_inv_moveA h3 fun j => (bm_moves_char j).1

theorem bm_moveB_kh {ω : Kˣ} (h3 : ω ^ 3 = 1) :
    weylTuple ((coxeterSystem Tag.E6).wordProd bmMoveB) (e6LineChar ω) = e6LineChar ω := by
  rw [bm_e6LineChar_eq]
  exact bm_weylTuple_char bm_inv_moveB h3 fun j => (bm_moves_char j).2.1

theorem bm_moveC_kh {ω : Kˣ} (h3 : ω ^ 3 = 1) :
    weylTuple ((coxeterSystem Tag.E6).wordProd bmMoveC) (e6LineChar ω) = (e6LineChar ω)⁻¹ := by
  have e : (e6LineChar ω)⁻¹ = fun j => ω ^ (-bmKhExp j) := by
    rw [bm_e6LineChar_eq]
    funext j
    rw [Pi.inv_apply, zpow_neg]
  rw [e, bm_e6LineChar_eq]
  exact bm_weylTuple_char (e := fun j => -bmKhExp j) bm_inv_moveC h3 fun j => by
    simpa only [sub_neg_eq_add] using (bm_moves_char j).2.2.1

theorem bm_moveA_kd {ω : Kˣ} (h3 : ω ^ 3 = 1) :
    weylTuple ((coxeterSystem Tag.E6).wordProd bmMoveA) (e6D0Char ω) = e6D0Char ω := by
  rw [bm_e6D0Char_zpow]
  exact bm_weylTuple_char bm_inv_moveA h3 fun j => (bm_moves_char j).2.2.2.1

theorem bm_moveB_kd {ω : Kˣ} (h3 : ω ^ 3 = 1) :
    weylTuple ((coxeterSystem Tag.E6).wordProd bmMoveB) (e6D0Char ω) = e6D0Char ω := by
  rw [bm_e6D0Char_zpow]
  exact bm_weylTuple_char bm_inv_moveB h3 fun j => (bm_moves_char j).2.2.2.2.1

theorem bm_moveC_kd {ω : Kˣ} (h3 : ω ^ 3 = 1) :
    weylTuple ((coxeterSystem Tag.E6).wordProd bmMoveC) (e6D0Char ω) = e6D0Char ω := by
  rw [bm_e6D0Char_zpow]
  exact bm_weylTuple_char bm_inv_moveC h3 fun j => (bm_moves_char j).2.2.2.2.2

theorem bm_bmX_conj_rootDiag (t b : Fin Tag.E6.rank → Kˣ) :
    rootDiagAutHom Tag.E6 K t * bmX K b * (rootDiagAutHom Tag.E6 K t)⁻¹ =
      bmX K (weylTuple ((coxeterSystem Tag.E6).wordProd e6BadWord)⁻¹ t * b * t⁻¹) := by
  have h := bm_rootDiag_mul_conj (bm_weylWordElt_mem_monomial (K := K) e6BadWord)
    (bm_mapsRootLines_weylWordElt e6BadWord) t
  simp only [bmX]
  rw [← mul_assoc, h, map_mul, map_mul, ← map_inv]
  group

theorem bm_bmX_mem_innerAut {g : Kˣ} {y : Fin Tag.E6.rank → ℤ}
    (hL : (y 0 + 2 * y 2 + y 4 + 2 * y 5) % 3 = 0) :
    bmX K (fun j => g ^ y j) ∈ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) := by
  obtain ⟨z, hz⟩ := bm_inner_exp y hL
  have hb : (fun j => g ^ y j) = fun j => g ^ ∑ i, z i * Tag.E6.cartan i j :=
    funext fun j => by rw [hz j]
  rw [bmX, hb]
  exact mul_mem ⟨weylWordElt .E6 K e6BadWord, rfl⟩
    ⟨⟨_, bm_rootDiagUnit_cartan_mem g z⟩, bm_conj_eq_rootDiagAutHom rfl⟩

@[expose] def BmParabolic (K : Type) [Field K] (ω : Kˣ) : Prop :=
  ∀ b : Fin Tag.E6.rank → Kˣ, b 0 = 1 → b 2 = 1 →
    ∃ R : Subgroup (adjointGroup Tag.E6 K), R ≠ ⊥ ∧ IsPGroup (ringChar K) R ∧
      R.map (MulAut.conj (e6LineElt ω)).toMonoidHom = R ∧
      R.map (rootDiagAutHom Tag.E6 K (e6D0Char ω)).toMonoidHom = R ∧
      R.map (MulAut.conj (weylWordElt .E6 K e6BadWord) * rootDiagAutHom Tag.E6 K b).toMonoidHom = R

variable [Finite K]

theorem bm_e6NormalizesR_of_closure {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    {S : Set (MulAut (adjointGroup Tag.E6 K))} (hE : Subgroup.closure S = E)
    {R : Subgroup (adjointGroup Tag.E6 K)} (hR1 : R ≠ ⊥) (hRp : IsPGroup (ringChar K) R)
    (hS : ∀ ε ∈ S, R.map ε.toMonoidHom = R) : E6NormalizesR K E := by
  refine ⟨R, hR1, hRp, fun ε hε => ?_⟩
  rw [← hE] at hε
  exact (Subgroup.closure_le (bmStab R)).2 hS hε

theorem bm_torus {ω : Kˣ} {g : Kˣ} {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    {y : Fin Tag.E6.rank → ℤ} (h : BmGood ω E (bmX K fun i => g ^ y i)) (x : Fin Tag.E6.rank → ℤ) :
    BmGood ω (E.map (MulAut.congr (rootDiagAutHom Tag.E6 K fun i => g ^ x i)).toMonoidHom)
      (bmX K fun j => g ^ (y j + (∑ k, x k * bmTw j k - x j))) := by
  have hc : ∀ s : Fin Tag.E6.rank → Kˣ, rootDiagAutHom Tag.E6 K (fun i => g ^ x i) *
      rootDiagAutHom Tag.E6 K s * (rootDiagAutHom Tag.E6 K fun i => g ^ x i)⁻¹ =
        rootDiagAutHom Tag.E6 K s := fun s => by
    rw [← map_inv, ← map_mul, ← map_mul, mul_comm (fun i => g ^ x i) s, mul_assoc,
      mul_inv_cancel, mul_one]
  have hh := bm_mem_map_congr (rootDiagAutHom Tag.E6 K fun i => g ^ x i) h.2.2.2.1
  rw [bm_conj_e6LineElt, hc, ← bm_conj_e6LineElt] at hh
  have hd := bm_mem_map_congr (rootDiagAutHom Tag.E6 K fun i => g ^ x i) h.2.2.2.2.1
  rw [hc] at hd
  have hw : ∀ j, ((coxeterSystem Tag.E6).wordProd e6BadWord)⁻¹⁻¹ •
      (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = bmTw j := fun j => by rw [inv_inv, bm_smul_Tw]
  have h' := h.map _ hh hd
  rw [bm_bmX_conj_rootDiag, bm_weylTuple_pow hw g x] at h'
  have e : ((fun j => g ^ ∑ k, x k * bmTw j k) * (fun i => g ^ y i) * (fun i => g ^ x i)⁻¹) =
      fun j => g ^ (y j + (∑ k, x k * bmTw j k - x j)) := by
    funext j
    simp only [Pi.mul_apply, Pi.inv_apply]
    rw [← zpow_neg, ← zpow_add, ← zpow_add]
    congr 1
    ring
  rwa [e] at h'

theorem BmGood.conj_word {ω : Kˣ} {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    {X : MulAut (adjointGroup Tag.E6 K)} (h : BmGood ω E X) {u : List (Fin Tag.E6.rank)}
    (hkh : weylTuple ((coxeterSystem Tag.E6).wordProd u) (e6LineChar ω) = e6LineChar ω ∨
      weylTuple ((coxeterSystem Tag.E6).wordProd u) (e6LineChar ω) = (e6LineChar ω)⁻¹)
    (hkd : weylTuple ((coxeterSystem Tag.E6).wordProd u) (e6D0Char ω) = e6D0Char ω) :
    BmGood ω (E.map (MulAut.congr (MulAut.conj (weylWordElt .E6 K u))).toMonoidHom)
      (MulAut.conj (weylWordElt .E6 K u) * X * (MulAut.conj (weylWordElt .E6 K u))⁻¹) := by
  have hum := bm_weylWordElt_mem_monomial (K := K) u
  have hur := bm_mapsRootLines_weylWordElt (K := K) u
  have hc : ∀ s : Fin Tag.E6.rank → Kˣ, MulAut.conj (weylWordElt .E6 K u) *
      rootDiagAutHom Tag.E6 K s * (MulAut.conj (weylWordElt .E6 K u))⁻¹ =
        rootDiagAutHom Tag.E6 K (weylTuple ((coxeterSystem Tag.E6).wordProd u) s) := fun s => by
    rw [bm_conj_mul_rootDiag hum hur s, mul_inv_cancel_right]
  have hh : MulAut.conj (e6LineElt ω) ∈
      E.map (MulAut.congr (MulAut.conj (weylWordElt .E6 K u))).toMonoidHom := by
    have h0 := bm_mem_map_congr (MulAut.conj (weylWordElt .E6 K u)) h.2.2.2.1
    rw [bm_conj_e6LineElt, hc] at h0
    rw [bm_conj_e6LineElt]
    rcases hkh with hkh | hkh
    · rwa [hkh] at h0
    · rw [hkh, map_inv] at h0
      rw [← inv_inv (rootDiagAutHom Tag.E6 K (e6LineChar ω))]
      exact inv_mem h0
  have hd : rootDiagAutHom Tag.E6 K (e6D0Char ω) ∈
      E.map (MulAut.congr (MulAut.conj (weylWordElt .E6 K u))).toMonoidHom := by
    have h0 := bm_mem_map_congr (MulAut.conj (weylWordElt .E6 K u)) h.2.2.2.2.1
    rwa [hc, hkd] at h0
  exact h.map _ hh hd

theorem bm_move {ω : Kˣ} {g : Kˣ} (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g)
    {u : List (Fin Tag.E6.rank)} {T : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ}
    (hu : (coxeterSystem Tag.E6).wordProd u * (coxeterSystem Tag.E6).wordProd e6BadWord =
      (coxeterSystem Tag.E6).wordProd e6BadWord * (coxeterSystem Tag.E6).wordProd u)
    (hT : ∀ j, ((coxeterSystem Tag.E6).wordProd u)⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = T j)
    (hkh : weylTuple ((coxeterSystem Tag.E6).wordProd u) (e6LineChar ω) = e6LineChar ω ∨
      weylTuple ((coxeterSystem Tag.E6).wordProd u) (e6LineChar ω) = (e6LineChar ω)⁻¹)
    (hkd : weylTuple ((coxeterSystem Tag.E6).wordProd u) (e6D0Char ω) = e6D0Char ω)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} {y : Fin Tag.E6.rank → ℤ}
    (h : BmGood ω E (bmX K fun i => g ^ y i)) :
    ∃ (φ : MulAut (adjointGroup Tag.E6 K)) (m : Fin Tag.E6.rank → ℤ),
      BmGood ω (E.map (MulAut.congr φ).toMonoidHom)
        (bmX K fun j => g ^ (3 * m j + ∑ k, y k * T j k)) := by
  obtain ⟨s, hs, hsX⟩ := bm_conj_word_bmX (K := K) e6BadWord hu fun i => g ^ y i
  have h' := h.conj_word hkh hkd
  have hsX' : MulAut.conj (weylWordElt .E6 K u) * bmX K (fun i => g ^ y i) *
      (MulAut.conj (weylWordElt .E6 K u))⁻¹ =
        bmX K (s * weylTuple ((coxeterSystem Tag.E6).wordProd u) fun i => g ^ y i) := hsX
  rw [hsX', bm_weylTuple_pow hT g y] at h'
  have hm : ∀ j, ∃ m : ℤ, s j = g ^ (3 * m) := fun j => by
    obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.1 (hg (s j))
    refine ⟨e, ?_⟩
    rw [mul_comm, zpow_mul, he, zpow_ofNat, pow_succ, hs j, one_mul]
  choose m hm using hm
  have e : (s * fun j => g ^ ∑ k, y k * T j k) =
      fun j => g ^ (3 * m j + ∑ k, y k * T j k) := by
    funext j
    simp only [Pi.mul_apply]
    rw [hm j, ← zpow_add]
  rw [e] at h'
  exact ⟨_, m, h'⟩

theorem bm_false_of_parabolic {ω : Kˣ} (hpar : BmParabolic K ω) (h1 : ω ≠ 1) {g : Kˣ}
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} {y : Fin Tag.E6.rank → ℤ}
    (h : BmGood ω E (bmX K fun j => g ^ y j)) (h0 : (2 * y 0 + y 2) % 3 = 0) : False := by
  obtain ⟨x, hx0, hx2⟩ := bm_parab_exp y h0
  have h' := bm_torus h x
  obtain ⟨R, hR1, hRp, hRh, hRd, hRX⟩ := hpar (fun j => g ^ (y j + (∑ k, x k * bmTw j k - x j)))
    (by simp only [hx0, zpow_zero]) (by simp only [hx2, zpow_zero])
  exact h'.2.2.1 (bm_e6NormalizesR_of_closure (h'.closure_eq h1) hR1 hRp
    (by rintro ε (rfl | rfl | rfl); exacts [hRh, hRd, hRX]))

theorem bmGoal_of_final {ω : Kˣ} (h1 : ω ≠ 1) {g : Kˣ}
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} {y : Fin Tag.E6.rank → ℤ}
    (h : BmGood ω E (bmX K fun j => g ^ y j)) (hl1 : (2 * y 4 + y 5) % 3 = 0)
    (hl3 : (y 1 + y 2 + 2 * y 5 - (2 * y 0 + y 2)) % 3 = 0) : BmGoal ω E := by
  obtain ⟨x, hx⟩ := bm_final_exp y hl1 hl3
  have h' := bm_torus h x
  have e : (fun j => g ^ (y j + (∑ k, x k * bmTw j k - x j))) =
      ![1, 1, g ^ (2 * y 0 + y 2), 1, 1, 1] := by
    funext j
    rw [hx j]
    fin_cases j
    exacts [zpow_zero g, zpow_zero g, rfl, zpow_zero g, zpow_zero g, zpow_zero g]
  rw [e, ← e6BadX_eq_bmX] at h'
  exact bmGoal_of_map _ (bmGoal_of_bmX h1 h')

theorem bmGoal_of_l1 {ω : Kˣ} (hpar : BmParabolic K ω) (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) {g : Kˣ}
    (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    {y : Fin Tag.E6.rank → ℤ} (h : BmGood ω E (bmX K fun j => g ^ y j))
    (hl1 : (2 * y 4 + y 5) % 3 = 0) : BmGoal ω E := by
  by_cases h0 : (2 * y 0 + y 2) % 3 = 0
  · exact (bm_false_of_parabolic hpar h1 h h0).elim
  by_cases hl3 : (y 1 + y 2 + 2 * y 5 - (2 * y 0 + y 2)) % 3 = 0
  · exact bmGoal_of_final h1 h hl1 hl3
  by_cases hA : (y 1 + y 2 + 2 * y 5 + (2 * y 0 + y 2)) % 3 = 0
  · obtain ⟨φ, m, h'⟩ := bm_move hg bm_comm_moveA bm_inv_moveA (Or.inl (bm_moveA_kh h3))
      (bm_moveA_kd h3) h
    refine bmGoal_of_map φ (bmGoal_of_final h1 h' ?_ ?_) <;> simp [bm_sum_six, bmInvA] <;> omega
  · obtain ⟨φ, m, h'⟩ := bm_move hg bm_comm_moveB bm_inv_moveB (Or.inl (bm_moveB_kh h3))
      (bm_moveB_kd h3) h
    refine bmGoal_of_map φ (bmGoal_of_final h1 h' ?_ ?_) <;> simp [bm_sum_six, bmInvB] <;>
      rcases bm_res h0 with h0' | h0' <;> rcases bm_res hl3 with h3' | h3' <;> omega

theorem bmGoal_of_bmX_pow {ω : Kˣ} (hpar : BmParabolic K ω) (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    {g : Kˣ} (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} {y : Fin Tag.E6.rank → ℤ}
    (h : BmGood ω E (bmX K fun j => g ^ y j)) : BmGoal ω E := by
  by_cases h0 : (2 * y 0 + y 2) % 3 = 0
  · exact (bm_false_of_parabolic hpar h1 h h0).elim
  by_cases hl1 : (2 * y 4 + y 5) % 3 = 0
  · exact bmGoal_of_l1 hpar h3 h1 hg h hl1
  have hL : (y 0 + 2 * y 2 + y 4 + 2 * y 5) % 3 ≠ 0 := fun hL =>
    h.2.2.2.2.2.2 (bm_bmX_mem_innerAut hL)
  obtain ⟨φ, m, h'⟩ := bm_move hg bm_comm_moveC bm_inv_moveC (Or.inr (bm_moveC_kh h3))
    (bm_moveC_kd h3) h
  refine bmGoal_of_map φ (bmGoal_of_l1 hpar h3 h1 hg h' ?_)
  simp [bm_sum_six, bmInvC]
  rcases bm_res h0 with h0' | h0' <;> rcases bm_res hl1 with h1' | h1' <;> omega

theorem bmGoal_of_bmX_any {ω : Kˣ} (hpar : BmParabolic K ω) (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} {b : Fin Tag.E6.rank → Kˣ}
    (h : BmGood ω E (bmX K b)) : BmGoal ω E := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hy : ∀ j, ∃ e : ℤ, g ^ e = b j := fun j => Subgroup.mem_zpowers_iff.1 (hg (b j))
  choose y hy using hy
  have hb : b = fun j => g ^ y j := funext fun j => (hy j).symm
  rw [hb] at h
  exact bmGoal_of_bmX_pow hpar h3 h1 hg h

end Normal

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
