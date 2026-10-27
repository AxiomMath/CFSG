module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadMonoNormal
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeModel

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.ComponentClassification.CatLeafProof (weylWordElt)
open CFSG.HardMathSupport.Malle.SeitzCube (wordProd_smul_E6)
open CFSG.StandardType.TableBExc.E6Three (gE6 cE6 gE6_pow_three gE6_comm cE6_pow_three wordE6G0
  wordE6G1 wordE6G2 wordE6C)

set_option linter.unusedSectionVars false

theorem cen_wordProd_pow_three {μ : List (Fin Tag.E6.rank)}
    (h : ∀ i : Fin Tag.E6.rank,
      (μ ++ μ ++ μ).foldr (reflect .E6) (Pi.single i 1) = Pi.single i 1) :
    (coxeterSystem Tag.E6).wordProd μ ^ 3 = 1 := by
  refine ext_single fun i => ?_
  rw [pow_three, ← CoxeterSystem.wordProd_append, ← CoxeterSystem.wordProd_append, one_smul,
    wordProd_smul_E6, ← List.append_assoc, h i]

@[expose] def cenTg0 : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![0, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![-1, 0, -1, 0, 0, 0], ![1, 0, 1, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]

@[expose] def cenTg1 : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 0, -1, -1], ![0, 0, 0, 0, 1, 0]]

@[expose] def cenTg2 : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![1, 0, 0, 0, 0, 0], ![1, 1, 2, 3, 2, 1], ![0, 0, 1, 0, 0, 0], ![-1, -1, -2, -2, -2, -1],
    ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]

@[expose] def cenTc : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 1, 0, 0],
    ![0, 1, 0, 0, 0, 0], ![-1, -2, -2, -3, -2, -1]]

@[expose] def cenTg12 : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![1, 0, 0, 0, 0, 0], ![1, 1, 2, 3, 2, 1], ![0, 0, 1, 0, 0, 0], ![-1, -1, -2, -2, -1, 0],
    ![0, 0, 0, 0, -1, -1], ![0, 0, 0, 0, 1, 0]]

@[expose] def cenTw1 : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![0, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![-1, 0, -1, 0, 0, 0], ![1, 0, 1, 1, 1, 0],
    ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, -1, -1]]

@[expose] def cenTw2 : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![1, 0, 0, 0, 0, 0], ![-1, -2, -2, -3, -2, -1], ![0, 0, 1, 0, 0, 0], ![0, 1, 0, 1, 1, 1],
    ![0, 0, 0, 0, -1, -1], ![0, 0, 0, 0, 1, 0]]

@[expose] def cenTw2sq : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![1, 0, 0, 0, 0, 0], ![1, 1, 2, 3, 2, 1], ![0, 0, 1, 0, 0, 0], ![-1, -1, -2, -2, -1, -1],
    ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, -1, -1]]

@[expose] def cenTz : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![0, 0, 1, 0, 0, 0], ![1, 1, 2, 3, 2, 1], ![-1, 0, -1, 0, 0, 0], ![0, -1, -1, -2, -1, 0],
    ![0, 0, 0, 0, -1, -1], ![0, 0, 0, 0, 1, 0]]

theorem cen_smul_g0 (j : Fin Tag.E6.rank) :
    (coxeterSystem Tag.E6).wordProd wordE6G0 • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
      cenTg0 j := by
  rw [wordProd_smul_E6]
  revert j
  decide +kernel

theorem cen_smul_g1 (j : Fin Tag.E6.rank) :
    (coxeterSystem Tag.E6).wordProd wordE6G1 • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
      cenTg1 j := by
  rw [wordProd_smul_E6]
  revert j
  decide +kernel

theorem cen_smul_g2 (j : Fin Tag.E6.rank) :
    (coxeterSystem Tag.E6).wordProd wordE6G2 • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
      cenTg2 j := by
  rw [wordProd_smul_E6]
  revert j
  decide +kernel

theorem cen_smul_c (j : Fin Tag.E6.rank) :
    (coxeterSystem Tag.E6).wordProd wordE6C • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
      cenTc j := by
  rw [wordProd_smul_E6]
  revert j
  decide +kernel

theorem cen_smul_g12 (j : Fin Tag.E6.rank) :
    (coxeterSystem Tag.E6).wordProd (wordE6G1 ++ wordE6G2) •
      (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = cenTg12 j := by
  rw [wordProd_smul_E6]
  revert j
  decide +kernel

theorem cen_smul_w1 (j : Fin Tag.E6.rank) :
    (coxeterSystem Tag.E6).wordProd (wordE6G0 ++ (wordE6G1 ++ wordE6G1)) •
      (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = cenTw1 j := by
  rw [wordProd_smul_E6]
  revert j
  decide +kernel

theorem cen_smul_w2 (j : Fin Tag.E6.rank) :
    (coxeterSystem Tag.E6).wordProd (wordE6G1 ++ (wordE6G2 ++ wordE6G2)) •
      (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = cenTw2 j := by
  rw [wordProd_smul_E6]
  revert j
  decide +kernel

theorem cen_smul_w2sq (j : Fin Tag.E6.rank) :
    (coxeterSystem Tag.E6).wordProd
        (wordE6G1 ++ (wordE6G2 ++ wordE6G2) ++ (wordE6G1 ++ (wordE6G2 ++ wordE6G2))) •
      (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = cenTw2sq j := by
  rw [wordProd_smul_E6]
  revert j
  decide +kernel

theorem cen_smul_z (j : Fin Tag.E6.rank) :
    (coxeterSystem Tag.E6).wordProd (wordE6G0 ++ wordE6G1 ++ wordE6G2) •
      (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = cenTz j := by
  rw [wordProd_smul_E6]
  revert j
  decide +kernel

theorem cen_pow_three_g12 : (coxeterSystem Tag.E6).wordProd (wordE6G1 ++ wordE6G2) ^ 3 = 1 :=
  cen_wordProd_pow_three (by decide +kernel)

theorem cen_pow_three_w1 :
    (coxeterSystem Tag.E6).wordProd (wordE6G0 ++ (wordE6G1 ++ wordE6G1)) ^ 3 = 1 :=
  cen_wordProd_pow_three (by decide +kernel)

theorem cen_pow_three_w2 :
    (coxeterSystem Tag.E6).wordProd (wordE6G1 ++ (wordE6G2 ++ wordE6G2)) ^ 3 = 1 :=
  cen_wordProd_pow_three (by decide +kernel)

theorem cen_pow_three_z :
    (coxeterSystem Tag.E6).wordProd (wordE6G0 ++ wordE6G1 ++ wordE6G2) ^ 3 = 1 :=
  cen_wordProd_pow_three (by decide +kernel)

theorem cen_comm_OA : (coxeterSystem Tag.E6).wordProd wordE6G0 *
    (coxeterSystem Tag.E6).wordProd (wordE6G1 ++ wordE6G2) =
      (coxeterSystem Tag.E6).wordProd (wordE6G1 ++ wordE6G2) *
        (coxeterSystem Tag.E6).wordProd wordE6G0 :=
  bm_wordProd_comm (by decide +kernel)

theorem cen_comm_OB : (coxeterSystem Tag.E6).wordProd (wordE6G0 ++ (wordE6G1 ++ wordE6G1)) *
    (coxeterSystem Tag.E6).wordProd (wordE6G1 ++ (wordE6G2 ++ wordE6G2)) =
      (coxeterSystem Tag.E6).wordProd (wordE6G1 ++ (wordE6G2 ++ wordE6G2)) *
        (coxeterSystem Tag.E6).wordProd (wordE6G0 ++ (wordE6G1 ++ wordE6G1)) :=
  bm_wordProd_comm (by decide +kernel)

theorem cen_comm_OT : (coxeterSystem Tag.E6).wordProd wordE6C *
    (coxeterSystem Tag.E6).wordProd (wordE6G0 ++ wordE6G1 ++ wordE6G2) =
      (coxeterSystem Tag.E6).wordProd (wordE6G0 ++ wordE6G1 ++ wordE6G2) *
        (coxeterSystem Tag.E6).wordProd wordE6C :=
  bm_wordProd_comm (by decide +kernel)

theorem cen_three_dvd_of_gen {K : Type} [Field K] [Finite K] (hK : 3 ∣ Nat.card K - 1) {g : Kˣ}
    (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) {m : ℤ} (h : g ^ m = 1) : (3 : ℤ) ∣ m := by
  have h1 : ((orderOf g : ℕ) : ℤ) ∣ m := orderOf_dvd_iff_zpow_eq_one.mpr h
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units K] at h1
  obtain ⟨c, hc⟩ := hK
  obtain ⟨d, hd⟩ := h1
  exact ⟨c * d, by rw [hd, hc]; push_cast; ring⟩

section Exp


theorem cen_exists_exp {K : Type} [Field K] {X : MulAut (adjointGroup Tag.E6 K)}
    {μ : List (Fin Tag.E6.rank)} (hX : BmMono X ((coxeterSystem Tag.E6).wordProd μ)) {g : Kˣ}
    (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) :
    ∃ y : Fin Tag.E6.rank → ℤ,
      X = MulAut.conj (weylWordElt .E6 K μ) * rootDiagAutHom Tag.E6 K (fun j => g ^ y j) := by
  obtain ⟨b, rfl⟩ := hX.exists_eq_word
  have hy : ∀ j, ∃ e : ℤ, g ^ e = b j := fun j => Subgroup.mem_zpowers_iff.1 (hg (b j))
  choose y hy using hy
  exact ⟨y, by rw [show b = fun j => g ^ y j from funext fun j => (hy j).symm]⟩

theorem cen_word_mul_exp {K : Type} [Field K] (μ μ' : List (Fin Tag.E6.rank))
    {T : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ}
    (hT : ∀ j, (coxeterSystem Tag.E6).wordProd μ' • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = T j)
    (g : Kˣ) (y z : Fin Tag.E6.rank → ℤ) :
    MulAut.conj (weylWordElt .E6 K μ) * rootDiagAutHom Tag.E6 K (fun j => g ^ y j) *
        (MulAut.conj (weylWordElt .E6 K μ') * rootDiagAutHom Tag.E6 K (fun j => g ^ z j)) =
      MulAut.conj (weylWordElt .E6 K (μ ++ μ')) *
        rootDiagAutHom Tag.E6 K (fun j => g ^ (∑ k, y k * T j k + z j)) := by
  have hT' : ∀ j, ((coxeterSystem Tag.E6).wordProd μ')⁻¹⁻¹ •
      (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = T j := fun j => by rw [inv_inv, hT j]
  have e : ((fun j => g ^ ∑ k, y k * T j k) * fun j => g ^ z j) =
      fun j => g ^ (∑ k, y k * T j k + z j) := funext fun j => (zpow_add g _ _).symm
  rw [bm_word_mul, bm_weylTuple_pow hT', e]

theorem cen_three_dvd_of_word_eq {K : Type} [Field K] [Finite K] (hK : 3 ∣ Nat.card K - 1)
    {g : Kˣ} (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) {μ μ' : List (Fin Tag.E6.rank)}
    (hμ : (coxeterSystem Tag.E6).wordProd μ = (coxeterSystem Tag.E6).wordProd μ')
    {p q : Fin Tag.E6.rank → ℤ}
    (h : MulAut.conj (weylWordElt .E6 K μ) * rootDiagAutHom Tag.E6 K (fun j => g ^ p j) =
      MulAut.conj (weylWordElt .E6 K μ') * rootDiagAutHom Tag.E6 K (fun j => g ^ q j)) :
    ∀ j, (3 : ℤ) ∣ p j - q j := by
  obtain ⟨s, hs, he⟩ := bm_weylWordElt_eq_mul_sign (K := K) hμ
  have hd : (((weylWordElt .E6 K μ')⁻¹ * weylWordElt .E6 K μ : adjointGroup Tag.E6 K) :
      ModGL Tag.E6 K) = rootDiagUnit Tag.E6 s := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, he, inv_mul_cancel_left]
  have hc : MulAut.conj (weylWordElt .E6 K μ) =
      MulAut.conj (weylWordElt .E6 K μ') * rootDiagAutHom Tag.E6 K s := by
    rw [← bm_conj_eq_rootDiagAutHom hd, ← map_mul, mul_inv_cancel_left]
  rw [hc, mul_assoc, ← map_mul (rootDiagAutHom Tag.E6 K)] at h
  have h2 := rootDiagAutHom_injective (τ := Tag.E6) (K := K) (mul_left_cancel h)
  intro j
  have hj : s j * g ^ p j = g ^ q j := congrFun h2 j
  have hsj : s j = g ^ (q j - p j) := by
    rw [zpow_sub, ← hj, mul_inv_cancel_right]
  have h1 : g ^ (2 * (q j - p j)) = 1 := by
    rw [mul_comm, zpow_mul, ← hsj, zpow_two, ← sq, hs j]
  have h3 := cen_three_dvd_of_gen hK hg h1
  omega

theorem cen_cube_exp {K : Type} [Field K] [Finite K] (hK : 3 ∣ Nat.card K - 1) {g : Kˣ}
    (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) {μ : List (Fin Tag.E6.rank)}
    {T : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ}
    (hT : ∀ j, (coxeterSystem Tag.E6).wordProd μ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = T j)
    (hμ : (coxeterSystem Tag.E6).wordProd μ ^ 3 = 1) {y : Fin Tag.E6.rank → ℤ}
    (h : (MulAut.conj (weylWordElt .E6 K μ) * rootDiagAutHom Tag.E6 K (fun j => g ^ y j)) ^ 3 =
      1) :
    ∀ j, (3 : ℤ) ∣ ∑ k, (∑ l, y l * T k l + y k) * T j k + y j := by
  rw [pow_three', cen_word_mul_exp μ μ hT, cen_word_mul_exp (μ ++ μ) μ hT] at h
  have h1 : (1 : MulAut (adjointGroup Tag.E6 K)) = MulAut.conj (weylWordElt .E6 K []) *
      rootDiagAutHom Tag.E6 K (fun _ : Fin Tag.E6.rank => g ^ (0 : ℤ)) := by
    rw [show (fun _ : Fin Tag.E6.rank => g ^ (0 : ℤ)) = 1 from funext fun _ => zpow_zero g,
      show weylWordElt .E6 K [] = 1 from rfl, map_one, map_one, one_mul]
  have hμ' : (coxeterSystem Tag.E6).wordProd (μ ++ μ ++ μ) =
      (coxeterSystem Tag.E6).wordProd [] := by
    rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_nil,
      ← hμ, pow_three']
  intro j
  have h3 := cen_three_dvd_of_word_eq hK hg hμ' (h.trans h1) j
  rwa [sub_zero] at h3

theorem cen_comm_exp {K : Type} [Field K] [Finite K] (hK : 3 ∣ Nat.card K - 1) {g : Kˣ}
    (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) {μ ν : List (Fin Tag.E6.rank)}
    {T U : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ}
    (hT : ∀ j, (coxeterSystem Tag.E6).wordProd μ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = T j)
    (hU : ∀ j, (coxeterSystem Tag.E6).wordProd ν • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = U j)
    (hμν : (coxeterSystem Tag.E6).wordProd μ * (coxeterSystem Tag.E6).wordProd ν =
      (coxeterSystem Tag.E6).wordProd ν * (coxeterSystem Tag.E6).wordProd μ)
    {y z : Fin Tag.E6.rank → ℤ}
    (h : MulAut.conj (weylWordElt .E6 K μ) * rootDiagAutHom Tag.E6 K (fun j => g ^ y j) *
        (MulAut.conj (weylWordElt .E6 K ν) * rootDiagAutHom Tag.E6 K (fun j => g ^ z j)) =
      MulAut.conj (weylWordElt .E6 K ν) * rootDiagAutHom Tag.E6 K (fun j => g ^ z j) *
        (MulAut.conj (weylWordElt .E6 K μ) * rootDiagAutHom Tag.E6 K (fun j => g ^ y j))) :
    ∀ j, (3 : ℤ) ∣ (∑ k, y k * U j k + z j) - (∑ k, z k * T j k + y j) := by
  rw [cen_word_mul_exp μ ν hU, cen_word_mul_exp ν μ hT] at h
  exact cen_three_dvd_of_word_eq hK hg (by
    rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append, hμν]) h

theorem cen_word_mem_innerAut {K : Type} [Field K] (μ : List (Fin Tag.E6.rank)) {g : Kˣ}
    {y : Fin Tag.E6.rank → ℤ} (hL : (y 0 + 2 * y 2 + y 4 + 2 * y 5) % 3 = 0) :
    MulAut.conj (weylWordElt .E6 K μ) * rootDiagAutHom Tag.E6 K (fun j => g ^ y j) ∈
      CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) := by
  obtain ⟨z, hz⟩ := bm_inner_exp y hL
  have hb : (fun j => g ^ y j) = fun j => g ^ ∑ i, z i * Tag.E6.cartan i j :=
    funext fun j => by rw [hz j]
  rw [hb]
  exact mul_mem ⟨weylWordElt .E6 K μ, rfl⟩
    ⟨⟨_, bm_rootDiagUnit_cartan_mem g z⟩, bm_conj_eq_rootDiagAutHom rfl⟩

theorem e6Cen_inner_OA {K : Type} [Field K] [Finite K] (hK : 3 ∣ Nat.card K - 1)
    {X Y : MulAut (adjointGroup Tag.E6 K)} (hX : BmMono X (gE6 0))
    (hY : BmMono Y (gE6 1 * gE6 2)) (hX3 : X ^ 3 = 1) (hY3 : Y ^ 3 = 1) (hXY : X * Y = Y * X) :
    X ∈ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hY' : BmMono Y ((coxeterSystem Tag.E6).wordProd (wordE6G1 ++ wordE6G2)) := by
    rw [CoxeterSystem.wordProd_append]
    exact hY
  obtain ⟨y, rfl⟩ := cen_exists_exp (μ := wordE6G0) hX hg
  obtain ⟨z, rfl⟩ := cen_exists_exp hY' hg
  have hcX := cen_cube_exp hK hg cen_smul_g0 (gE6_pow_three 0) hX3 3
  have hcY := cen_cube_exp hK hg cen_smul_g12 cen_pow_three_g12 hY3 3
  have hm := cen_comm_exp hK hg cen_smul_g0 cen_smul_g12 cen_comm_OA hXY 1
  refine cen_word_mem_innerAut _ ?_
  simp [bm_sum_six, cenTg0, cenTg12] at hcX hcY hm
  omega

theorem e6Cen_inner_OB {K : Type} [Field K] [Finite K] (hK : 3 ∣ Nat.card K - 1)
    {X Y : MulAut (adjointGroup Tag.E6 K)} (hX : BmMono X (gE6 0 * gE6 1 ^ 2))
    (hY : BmMono Y (gE6 1 * gE6 2 ^ 2)) (hX3 : X ^ 3 = 1) (hY3 : Y ^ 3 = 1)
    (hXY : X * Y = Y * X) :
    X * Y ^ 2 ∈ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  rw [pow_two] at hX hY
  have hX' : BmMono X
      ((coxeterSystem Tag.E6).wordProd (wordE6G0 ++ (wordE6G1 ++ wordE6G1))) := by
    rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append]
    exact hX
  have hY' : BmMono Y
      ((coxeterSystem Tag.E6).wordProd (wordE6G1 ++ (wordE6G2 ++ wordE6G2))) := by
    rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append]
    exact hY
  obtain ⟨y, rfl⟩ := cen_exists_exp hX' hg
  obtain ⟨z, rfl⟩ := cen_exists_exp hY' hg
  have hcX := cen_cube_exp hK hg cen_smul_w1 cen_pow_three_w1 hX3 3
  have hcY := cen_cube_exp hK hg cen_smul_w2 cen_pow_three_w2 hY3 3
  have hm := cen_comm_exp hK hg cen_smul_w1 cen_smul_w2 cen_comm_OB hXY 4
  rw [pow_two, cen_word_mul_exp _ _ cen_smul_w2, cen_word_mul_exp _ _ cen_smul_w2sq]
  refine cen_word_mem_innerAut _ ?_
  simp [bm_sum_six, cenTw1, cenTw2, cenTw2sq] at hcX hcY hm ⊢
  omega

theorem e6Cen_inner_OT {K : Type} [Field K] [Finite K] (hK : 3 ∣ Nat.card K - 1)
    {X Y : MulAut (adjointGroup Tag.E6 K)} (hX : BmMono X cE6)
    (hY : BmMono Y (gE6 0 * gE6 1 * gE6 2)) (hX3 : X ^ 3 = 1) (hY3 : Y ^ 3 = 1)
    (hXY : X * Y = Y * X) :
    Y ∈ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hY' : BmMono Y ((coxeterSystem Tag.E6).wordProd (wordE6G0 ++ wordE6G1 ++ wordE6G2)) := by
    rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append]
    exact hY
  obtain ⟨y, rfl⟩ := cen_exists_exp (μ := wordE6C) hX hg
  obtain ⟨z, rfl⟩ := cen_exists_exp hY' hg
  have hcX := cen_cube_exp hK hg cen_smul_c cE6_pow_three hX3 0
  have hcY := cen_cube_exp hK hg cen_smul_z cen_pow_three_z hY3 0
  have hm0 := cen_comm_exp hK hg cen_smul_c cen_smul_z cen_comm_OT hXY 0
  have hm2 := cen_comm_exp hK hg cen_smul_c cen_smul_z cen_comm_OT hXY 2
  refine cen_word_mem_innerAut _ ?_
  simp [bm_sum_six, cenTc, cenTz] at hcX hcY hm0 hm2
  omega

theorem e6Cen_inner_O3 {K : Type} [Field K] [Finite K] (hK : 3 ∣ Nat.card K - 1)
    {X : Fin 3 → MulAut (adjointGroup Tag.E6 K)} (hX : ∀ i, BmMono (X i) (gE6 i))
    (hX3 : ∀ i, X i ^ 3 = 1) (hXY : ∀ i j, X i * X j = X j * X i) :
    ∀ i, X i ∈ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨y₀, h₀⟩ := cen_exists_exp (μ := wordE6G0) (hX 0) hg
  obtain ⟨y₁, h₁⟩ := cen_exists_exp (μ := wordE6G1) (hX 1) hg
  obtain ⟨y₂, h₂⟩ := cen_exists_exp (μ := wordE6G2) (hX 2) hg
  have e₀ := hX3 0
  have e₁ := hX3 1
  have e₂ := hX3 2
  have e₀₁ := hXY 0 1
  have e₀₂ := hXY 0 2
  rw [h₀] at e₀ e₀₁ e₀₂
  rw [h₁] at e₁ e₀₁
  rw [h₂] at e₂ e₀₂
  have hc₀ := cen_cube_exp hK hg cen_smul_g0 (gE6_pow_three 0) e₀ 3
  have hc₁ := cen_cube_exp hK hg cen_smul_g1 (gE6_pow_three 1) e₁ 3
  have hc₂ := cen_cube_exp hK hg cen_smul_g2 (gE6_pow_three 2) e₂ 3
  have hm₀₁ := cen_comm_exp hK hg cen_smul_g0 cen_smul_g1 (gE6_comm 0 1) e₀₁
  have hm₀₂ := cen_comm_exp hK hg cen_smul_g0 cen_smul_g2 (gE6_comm 0 2) e₀₂
  have i₀ : X 0 ∈ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) := by
    rw [h₀]
    refine cen_word_mem_innerAut _ ?_
    have hm := hm₀₁ 4
    simp [bm_sum_six, cenTg0, cenTg1] at hc₀ hm
    omega
  have i₁ : X 1 ∈ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) := by
    rw [h₁]
    refine cen_word_mem_innerAut _ ?_
    have hm := hm₀₁ 0
    simp [bm_sum_six, cenTg0, cenTg1] at hc₁ hm
    omega
  have i₂ : X 2 ∈ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) := by
    rw [h₂]
    refine cen_word_mem_innerAut _ ?_
    have hm := hm₀₂ 0
    simp [bm_sum_six, cenTg0, cenTg2] at hc₂ hm
    omega
  intro i
  fin_cases i
  exacts [i₀, i₁, i₂]

end Exp

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
