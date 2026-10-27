module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213CaseA
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Comp212Diag
import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Lemma213

open CFSG CFSG.LocalCores CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {K : Type} [Group K] [Finite K] {n p : ℕ} {P : Sylow p K} {z : K} {D : Subgroup K}

theorem smul_eq_self_iff (g : K) (C : ComponentIndex K) :
    g • C = C ↔ g ∈ normalizer (C.1 : Set K) := by
  rw [mem_normalizer_iff_map_conj_eq]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

namespace Red

theorem eq_zpowers_of_ne (R : Red n p K P z D) {T : Subgroup K} (hTD : T ≤ D) (hzT : z ∈ T)
    (hne : T ≠ D) : T = zpowers z := by
  haveI := R.fact
  have hp := R.prime
  have hcardz : Nat.card (zpowers z) = p := by rw [Nat.card_zpowers, R.conf.ord]
  have hdvd : Nat.card T ∣ p ^ 2 := R.conf.card ▸ card_dvd_of_le hTD
  obtain ⟨i, hi, hTi⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hlt : i < 2 := by
    by_contra hi2
    have h2 : i = 2 := by omega
    exact hne (eq_of_le_of_card_ge hTD (by rw [R.conf.card, hTi, h2]))
  have hle : Nat.card T ≤ Nat.card (zpowers z) := by
    rw [hTi, hcardz]
    calc p ^ i ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
      _ = p := pow_one p
  exact (eq_of_le_of_card_ge (zpowers_le.2 hzT) hle).symm

theorem z_mem_normalizer (R : Red n p K P z D) (C : ComponentIndex K) :
    z ∈ normalizer (C.1 : Set K) :=
  layer_le_normalizer C.2 R.hzL

theorem inf_normalizer_eq_zpowers (R : Red n p K P z D) {w : K} (hw : w ∈ D)
    {C : ComponentIndex K} (hmove : w • C ≠ C) :
    D ⊓ normalizer (C.1 : Set K) = zpowers z := by
  refine R.eq_zpowers_of_ne inf_le_left ⟨R.conf.mem, R.z_mem_normalizer C⟩ fun h => ?_
  have hwD : w ∈ D ⊓ normalizer (C.1 : Set K) := by rw [h]; exact hw
  exact hmove ((smul_eq_self_iff w C).2 hwD.2)

theorem not_mem_zpowers (R : Red n p K P z D) {w : K} (hw : w ∈ D) {C : ComponentIndex K}
    (hmove : w • C ≠ C) : w ∉ zpowers z := fun h =>
  hmove ((smul_eq_self_iff w C).2 (zpowers_le.2 (R.z_mem_normalizer C) h))

theorem pow_smul_eq (R : Red n p K P z D) {w : K} (hw : w ∈ D) {C : ComponentIndex K}
    (hmove : w • C ≠ C) {i j : ℕ} (h : w ^ i • C = w ^ j • C) : i ≡ j [MOD p] := by
  haveI := R.fact
  have hwp : w ^ p = 1 := R.conf.elem.2 w hw
  have hnorm : w ^ ((i : ℤ) - j) ∈ normalizer (C.1 : Set K) := by
    rw [← smul_eq_self_iff]
    have : w ^ ((i : ℤ) - j) • C = (w ^ (j : ℤ))⁻¹ • (w ^ (i : ℤ) • C) := by
      rw [← mul_smul, ← zpow_neg, ← zpow_add]
      congr 2
      ring
    rw [this, zpow_natCast, zpow_natCast, h, inv_smul_smul]
  by_contra hmod
  have hnd : ¬ (p : ℤ) ∣ ((i : ℤ) - j) := by
    intro hd
    apply hmod
    exact (Nat.modEq_iff_dvd.2 hd).symm
  exact zpow_notMem_normalizer_of_not_dvd R.prime hwp
    (fun hmem => hmove ((smul_eq_self_iff w C).2 hmem)) hnd hnorm

theorem exists_diag (R : Red n p K P z D) {w : K} (hw : w ∈ D) {C₁ : ComponentIndex K}
    (hmove : w • C₁ ≠ C₁) {x : K} (hx : x ∈ C₁.1) :
    ∃ (y : K) (hy : y ∈ layer K), w * y * w⁻¹ = y ∧
      (∀ j : ℕ, π R.hZ (w ^ j • C₁) y hy = w ^ j * x * (w ^ j)⁻¹) ∧
      (∀ C' : ComponentIndex K, (∀ j : ℕ, w ^ j • C₁ ≠ C') → π R.hZ C' y hy = 1) ∧
      (∀ N : ℕ, x ^ N = 1 → y ^ N = 1) := by
  classical
  haveI := R.fact
  have hwp : w ^ p = 1 := R.conf.elem.2 w hw
  set Cs : ℕ → ComponentIndex K := fun i => w ^ i • C₁ with hCs
  set c : ℕ → K := fun i => w ^ i * x * (w ^ i)⁻¹ with hc
  have hcmem : ∀ i, c i ∈ (Cs i).1 := fun i => mem_cjComp_of_mem (w ^ i) C₁ hx
  have hCsne : ∀ i j, i < p → j < p → i ≠ j → Cs i ≠ Cs j := by
    intro i j hi hj hij h
    have := R.pow_smul_eq hw hmove h
    rw [Nat.ModEq, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
    exact hij this
  have hcomm : ((Finset.range p : Finset ℕ) : Set ℕ).Pairwise (Function.onFun Commute c) := by
    intro i hi j hj hij
    have hi' := Finset.mem_range.1 hi
    have hj' := Finset.mem_range.1 hj
    exact (mem_centralizer_iff.1
      (comp_le_centralizer_of_ne (hCsne i j hi' hj' hij) (hcmem i)) (c j) (hcmem j)).symm
  have hcL : ∀ i, c i ∈ layer K := fun i => component_le_layer (Cs i).2 (hcmem i)
  set y : K := (Finset.range p).noncommProd c hcomm with hy
  have hyL : y ∈ layer K :=
    Subgroup.noncommProd_mem (layer K) hcomm (fun i _ => hcL i)
  have hcoord0 : ∀ k, k < p → π R.hZ (Cs k) y hyL = c k := by
    intro k hk
    have hkmem : k ∈ Finset.range p := Finset.mem_range.2 hk
    obtain ⟨u, huL, huC, hyeq⟩ : ∃ u : K, u ∈ layer K ∧ u ∈ centralizer ((Cs k).1 : Set K) ∧
        y = c k * u := by
      refine ⟨_, ?_, ?_, (Finset.mul_noncommProd_erase (Finset.range p) hkmem c hcomm).symm⟩
      · exact Subgroup.noncommProd_mem (layer K) _ (fun i _ => hcL i)
      · refine Subgroup.noncommProd_mem (centralizer ((Cs k).1 : Set K)) _ (fun i hi => ?_)
        have hik : i ≠ k := Finset.ne_of_mem_erase hi
        have hip : i < p := Finset.mem_range.1 (Finset.mem_of_mem_erase hi)
        exact comp_le_centralizer_of_ne (hCsne i k hip hk hik) (hcmem i)
    rw [π_congr (Cs k) hyeq hyL (mul_mem (hcL k) huL), π_mul _ (hcL k) huL,
      π_of_mem _ (hcmem k), (π_eq_one_iff (hZ := R.hZ) (Cs k) huL).2 huC, mul_one]
  have hcoord : ∀ j : ℕ, π R.hZ (Cs j) y hyL = c j := by
    intro j
    have h1 : Cs j = Cs (j % p) := by
      simp only [hCs]
      rw [pow_eq_pow_mod j hwp]
    have h2 : c j = c (j % p) := by
      simp only [hc]
      rw [pow_eq_pow_mod j hwp]
    rw [h2, ← hcoord0 (j % p) (Nat.mod_lt _ R.prime.pos)]
    exact congrArg (fun C => π R.hZ C y hyL) h1
  have hcoord1 : ∀ C' : ComponentIndex K, (∀ j : ℕ, Cs j ≠ C') → π R.hZ C' y hyL = 1 := by
    intro C' hC'
    rw [π_eq_one_iff (hZ := R.hZ) C' hyL]
    exact Subgroup.noncommProd_mem (centralizer (C'.1 : Set K)) hcomm
      (fun i _ => comp_le_centralizer_of_ne (hC' i) (hcmem i))
  have hinv : w⁻¹ = w ^ (p - 1) := by
    refine eq_inv_of_mul_eq_one_left ?_ |>.symm
    rw [← pow_succ, Nat.sub_add_cancel R.prime.one_lt.le]
    exact hwp
  have hwy : w * y * w⁻¹ = y := by
    refine π_ext (hZ := R.hZ) (conj_mem_layer w hyL) hyL fun C' => ?_
    obtain ⟨C'', rfl⟩ : ∃ C'', w • C'' = C' := ⟨w⁻¹ • C', smul_inv_smul w C'⟩
    have h1 : π R.hZ (cjComp w C'') (w * y * w⁻¹) (conj_mem_layer w hyL) =
        w * π R.hZ C'' y hyL * w⁻¹ := π_conj w C'' hyL
    show π R.hZ (cjComp w C'') (w * y * w⁻¹) _ = π R.hZ (cjComp w C'') y hyL
    rw [h1]
    by_cases horb : ∃ j, Cs j = C''
    · obtain ⟨j, rfl⟩ := horb
      have e : cjComp w (Cs j) = Cs (j + 1) := by
        show w • (w ^ j • C₁) = w ^ (j + 1) • C₁
        rw [← mul_smul, pow_succ']
      rw [e, hcoord j, hcoord (j + 1)]
      simp only [hc]
      group
    · push Not at horb
      have hn : ∀ j, Cs j ≠ cjComp w C'' := by
        intro j hj
        apply horb (p - 1 + j)
        have : w⁻¹ • (w • C'') = w⁻¹ • Cs j := by
          show w⁻¹ • cjComp w C'' = _
          rw [hj]
        rw [inv_smul_smul, hinv, ← mul_smul, ← pow_add] at this
        exact this.symm
      rw [hcoord1 C'' horb, hcoord1 _ hn]
      simp
  have hpow : ∀ N : ℕ, x ^ N = 1 → y ^ N = 1 := by
    intro N hN
    refine eq_one_of_π_eq_one (hZ := R.hZ) (pow_mem hyL N) fun C' => ?_
    rw [π_pow C' hyL N]
    by_cases horb : ∃ j, Cs j = C'
    · obtain ⟨j, rfl⟩ := horb
      rw [hcoord j]
      simp only [hc]
      rw [conj_pow, hN]
      simp
    · push Not at horb
      rw [hcoord1 C' horb]
      simp
  exact ⟨y, hyL, hwy, hcoord, hcoord1, hpow⟩

theorem zc_smul (R : Red n p K P z D) {g : K} (hg : g ∈ (P : Subgroup K))
    (C : ComponentIndex K) : R.zc (g • C) = g * R.zc C * g⁻¹ := by
  have h2 := π_conj (hZ := R.hZ) g C R.hzL
  have h3 : π R.hZ (cjComp g C) (g * z * g⁻¹) (conj_mem_layer g R.hzL) =
      π R.hZ (cjComp g C) z R.hzL := π_congr _ (R.g_z hg) _ _
  rw [h3] at h2
  exact h2

theorem π_z_zpow (R : Red n p K P z D) (C : ComponentIndex K) (m : ℤ) :
    π R.hZ C (z ^ m) (zpow_mem R.hzL m) = R.zc C ^ m :=
  π_zpow C R.hzL m

theorem exists_diag_zpowers (R : Red n p K P z D) {w : K} (hw : w ∈ D) {C₁ : ComponentIndex K}
    (hmove : w • C₁ ≠ C₁) {x : K} (hx : x ∈ C₁.1) (hxz : x * R.zc C₁ = R.zc C₁ * x) {k : ℕ}
    (hk : x ^ (p ^ k) = 1) :
    ∃ (y : K) (hy : y ∈ layer K) (m : ℤ), y = z ^ m ∧ π R.hZ C₁ y hy = x ∧
      ∀ C' : ComponentIndex K, (∀ j : ℕ, w ^ j • C₁ ≠ C') → π R.hZ C' y hy = 1 := by
  haveI := R.fact
  obtain ⟨y, hy, hwy, hcoord, hcoord1, hpow⟩ := R.exists_diag hw hmove hx
  have hwP : ∀ j : ℕ, w ^ j ∈ (P : Subgroup K) := fun j => pow_mem (R.conf.le hw) j
  have hzy : z * y * z⁻¹ = y := by
    refine π_ext (hZ := R.hZ) (conj_mem_layer z hy) hy fun C'' => ?_
    rw [π_mul _ (mul_mem R.hzL hy) (inv_mem R.hzL), π_mul _ R.hzL hy, π_inv _ R.hzL]
    by_cases horb : ∃ j : ℕ, w ^ j • C₁ = C''
    · obtain ⟨j, rfl⟩ := horb
      have hzj : R.zc (w ^ j • C₁) = w ^ j * R.zc C₁ * (w ^ j)⁻¹ := R.zc_smul (hwP j) C₁
      have hcz : π R.hZ (w ^ j • C₁) z R.hzL = R.zc (w ^ j • C₁) := rfl
      rw [hcz, hcoord j, hzj]
      have hc : (w ^ j * R.zc C₁ * (w ^ j)⁻¹) * (w ^ j * x * (w ^ j)⁻¹) =
          (w ^ j * x * (w ^ j)⁻¹) * (w ^ j * R.zc C₁ * (w ^ j)⁻¹) := by
        calc (w ^ j * R.zc C₁ * (w ^ j)⁻¹) * (w ^ j * x * (w ^ j)⁻¹)
            = w ^ j * (R.zc C₁ * x) * (w ^ j)⁻¹ := by group
          _ = w ^ j * (x * R.zc C₁) * (w ^ j)⁻¹ := by rw [hxz]
          _ = (w ^ j * x * (w ^ j)⁻¹) * (w ^ j * R.zc C₁ * (w ^ j)⁻¹) := by group
      rw [hc]
      group
    · push Not at horb
      rw [hcoord1 C'' horb]
      simp
  have hcen : y ∈ centralizer (D : Set K) := by
    rw [mem_centralizer_iff]
    intro d hd
    obtain ⟨s, t, rfl⟩ := exists_pow_mul_pow_of_mem_plane R.conf.elem R.conf.card R.conf.mem
      R.z_ne_one hw (R.not_mem_zpowers hw hmove) hd
    have hyw : Commute w y := mul_inv_eq_iff_eq_mul.1 hwy
    have hyz : Commute z y := mul_inv_eq_iff_eq_mul.1 hzy
    exact ((hyw.pow_left s).mul_left (hyz.pow_left t)).eq
  have hyD : y ∈ D := R.conf.mem_of_pElement_mem_centralizer R.prime hcen ⟨k, hpow (p ^ k) hk⟩
  have hyN : y ∈ normalizer (C₁.1 : Set K) := layer_le_normalizer C₁.2 hy
  have hyZ : y ∈ zpowers z := by
    rw [← R.inf_normalizer_eq_zpowers hw hmove]
    exact ⟨hyD, hyN⟩
  obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hyZ
  refine ⟨y, hy, m, hm.symm, ?_, hcoord1⟩
  simpa using hcoord 0

theorem orbit_eq (R : Red n p K P z D) {w : K} (hw : w ∈ D) {C₀ : ComponentIndex K}
    (hmove : w • C₀ ≠ C₀) (C : ComponentIndex K) : ∃ j : ℕ, w ^ j • C₀ = C := by
  haveI := R.fact
  by_contra hno
  push Not at hno
  obtain ⟨y, hy, m, hym, hy0, hy1⟩ := R.exists_diag_zpowers hw hmove (R.zc_mem C₀)
    (Commute.refl (R.zc C₀)).eq (k := 1) (by rw [pow_one]; exact R.zc_pow C₀)
  have hy0' : R.zc C₀ ^ m = R.zc C₀ := by
    have h1 : π R.hZ C₀ y hy = π R.hZ C₀ (z ^ m) (zpow_mem R.hzL m) := π_congr _ hym _ _
    rw [R.π_z_zpow] at h1
    exact h1.symm.trans hy0
  have hy1' : R.zc C ^ m = 1 := by
    have h1 : π R.hZ C y hy = π R.hZ C (z ^ m) (zpow_mem R.hzL m) := π_congr _ hym _ _
    rw [R.π_z_zpow] at h1
    exact h1.symm.trans (hy1 C hno)
  have hord0 : orderOf (R.zc C₀) = p := orderOf_eq_prime (R.zc_pow C₀) (R.zc_ne_one C₀)
  have hordC : orderOf (R.zc C) = p := orderOf_eq_prime (R.zc_pow C) (R.zc_ne_one C)
  have hdvd : (p : ℤ) ∣ m - 1 := by
    rw [← hord0, orderOf_dvd_iff_zpow_eq_one, zpow_sub, hy0', zpow_one, mul_inv_cancel]
  have hC1 : R.zc C ^ (m - 1) = 1 := by
    rw [← orderOf_dvd_iff_zpow_eq_one, hordC]
    exact hdvd
  apply R.zc_ne_one C
  have : R.zc C ^ m = R.zc C ^ (m - 1) * R.zc C := by
    rw [← zpow_add_one]
    congr 1
    ring
  rw [hy1', hC1, one_mul] at this
  exact this.symm

theorem pElement_mem_zpowers_zc (R : Red n p K P z D) {w : K} (hw : w ∈ D)
    {C : ComponentIndex K} (hmove : w • C ≠ C) {x : K} (hx : x ∈ C.1)
    (hxz : x * R.zc C = R.zc C * x) {k : ℕ} (hk : x ^ (p ^ k) = 1) : x ∈ zpowers (R.zc C) := by
  obtain ⟨y, hy, m, hym, hy0, -⟩ := R.exists_diag_zpowers hw hmove hx hxz hk
  have h1 : π R.hZ C y hy = π R.hZ C (z ^ m) (zpow_mem R.hzL m) := π_congr _ hym _ _
  rw [R.π_z_zpow, hy0] at h1
  exact mem_zpowers_iff.2 ⟨m, h1.symm⟩

end Red

end CFSG.LocalAnalysis.RankFourTheoremC.Lemma213
