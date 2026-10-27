module

public import CFSG.Fischer.Classification.PartIII.U.Large
public import CFSG.Fischer.Classification.PartIII.U.Linear3
import all CFSG.Fischer.F4

public section

namespace CFSG.Fischer.Classification.LocalU

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
  CFSG.Fischer.Classification.Unitary CFSG.Fischer.Classification.LocalR3
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

@[expose] noncomputable def suOfF4 (M₀ : Matrix (Fin 5) (Fin 5) F4) (h1 : M₀.det = 1)
    (h2 : M₀.transpose.map (fun c => c ^ 2) * M₀ = 1) : SUid frob 5 :=
  mkSU frob (M₀.map eF4)
    (by
      have h := RingHom.map_det (eF4 : F4 →+* K) M₀
      rw [RingHom.mapMatrix_apply, h1, map_one] at h
      exact h.symm)
    (fun x y => by
      have hc : conjTr frob (M₀.map eF4) * M₀.map eF4 = 1 := by
        have e1 : conjTr frob (M₀.map eF4) = (M₀.transpose.map (fun c => c ^ 2)).map eF4 := by
          ext i j
          simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply, frob_eF4]
        rw [e1, ← Matrix.map_mul, h2, Matrix.map_one _ (map_zero eF4) (map_one eF4)]
      rw [herm_mulVec, hc, Matrix.one_mulVec])

theorem suOfF4_smul (M₀ : Matrix (Fin 5) (Fin 5) F4) (h1 : M₀.det = 1)
    (h2 : M₀.transpose.map (fun c => c ^ 2) * M₀ = 1) (v : Fin 5 → K) :
    suOfF4 M₀ h1 h2 • v = Matrix.mulVec (M₀.map eF4) v := rfl

@[expose] def kMat : Matrix (Fin 5) (Fin 5) F4 :=
  Matrix.diagonal ![F4.ω, F4.ω, F4.ω, F4.ω, F4.ω + 1]

@[expose] def gMat : Matrix (Fin 5) (Fin 5) F4 :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, F4.ω + 1, F4.ω, 1; 0, 0, F4.ω, F4.ω + 1, 1;
    0, 0, 1, 1, 1]

set_option maxRecDepth 100000 in
theorem det_kMat : kMat.det = 1 := by decide

theorem unitary_kMat : kMat.transpose.map (fun c => c ^ 2) * kMat = 1 := by decide

set_option maxRecDepth 100000 in
theorem det_gMat : gMat.det = 1 := by decide

theorem unitary_gMat : gMat.transpose.map (fun c => c ^ 2) * gMat = 1 := by decide

@[expose] noncomputable def kSU : SUid frob 5 := suOfF4 kMat det_kMat unitary_kMat

@[expose] noncomputable def gSU : SUid frob 5 := suOfF4 gMat det_gMat unitary_gMat

theorem eF4_omega_add_one : eF4 (F4.ω + 1) = ω + 1 := by rw [map_add, map_one]; rfl

theorem kSU_smul (w : Fin 5 → K) :
    kSU • w = ![ω * w 0, ω * w 1, ω * w 2, ω * w 3, (ω + 1) * w 4] := by
  rw [kSU, suOfF4_smul]
  funext i
  fin_cases i <;> simp [kMat, Matrix.mulVec, dotProduct, Fin.sum_univ_five, Matrix.diagonal,
    eF4_omega_add_one, omega_eq]

theorem gSU_smul (w : Fin 5 → K) :
    gSU • w = ![w 0, w 1, (ω + 1) * w 2 + ω * w 3 + w 4, ω * w 2 + (ω + 1) * w 3 + w 4,
      w 2 + w 3 + w 4] := by
  rw [gSU, suOfF4_smul]
  funext i
  fin_cases i <;> simp [gMat, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
    eF4_omega_add_one, omega_eq]

theorem kSU_smul_of_π {w : Fin 5 → K} (hw : π 3 w = 0) : kSU • w = ω • w := by
  have h2 : w 2 = 0 := congrFun hw 0
  have h3 : w 3 = 0 := congrFun hw 1
  have h4 : w 4 = 0 := congrFun hw 2
  rw [kSU_smul]
  funext i
  fin_cases i <;> simp [h2, h3, h4]

theorem gSU_smul_of_π {w : Fin 5 → K} (hw : π 3 w = 0) : gSU • w = (1 : K) • w := by
  have h2 : w 2 = 0 := congrFun hw 0
  have h3 : w 3 = 0 := congrFun hw 1
  have h4 : w 4 = 0 := congrFun hw 2
  rw [gSU_smul]
  funext i
  fin_cases i <;> simp [h2, h3, h4]

noncomputable abbrev w5 (a c e : K) : Fin 5 → K := ![a, 0, c, c, e]

theorem w5_apply_zero (a c e : K) : w5 a c e 0 = a := rfl

theorem w5_apply_two (a c e : K) : w5 a c e 2 = c := rfl

theorem w5_apply_three (a c e : K) : w5 a c e 3 = c := rfl

theorem w5_apply_four (a c e : K) : w5 a c e 4 = e := rfl

theorem herm_w5_left (a c e : K) (T : Fin 5 → K) :
    herm frob (w5 a c e) T = frob a * T 0 + frob c * T 2 + frob c * T 3 + frob e * T 4 := by
  simp [herm_def, Fin.sum_univ_five]

theorem herm_self_five (T : Fin 5 → K) :
    herm frob T T = frob (T 0) * T 0 + frob (T 1) * T 1 + frob (T 2) * T 2 +
      frob (T 3) * T 3 + frob (T 4) * T 4 := by
  simp [herm_def, Fin.sum_univ_five]

theorem herm_w5 (a c e a' c' e' : K) :
    herm frob (w5 a c e) (w5 a' c' e') = frob a * a' + frob e * e' := by
  rw [herm_w5_left, w5_apply_zero, w5_apply_two, w5_apply_three, w5_apply_four]
  linear_combination (frob c * c') * two_eq_zero

theorem smul_w5 (t a c e : K) : t • w5 a c e = w5 (t * a) (t * c) (t * e) := by
  funext i
  fin_cases i <;> simp

theorem w5_add (a c e a' c' e' : K) :
    w5 a c e + w5 a' c' e' = w5 (a + a') (c + c') (e + e') := by
  funext i
  fin_cases i <;> simp

theorem w5_ne_zero_of_left {a : K} (ha : a ≠ 0) (c e : K) : w5 a c e ≠ 0 := fun h =>
  ha (by simpa using congrFun h 0)

theorem w5_ne_zero_of_mid {c : K} (hc : c ≠ 0) (a e : K) : w5 a c e ≠ 0 := fun h =>
  hc (by simpa using congrFun h 2)

theorem isotropic_w5 (a c : K) : herm frob (w5 a c a) (w5 a c a) = 0 := by
  rw [herm_w5, add_self_K]

theorem kSU_w5 (a c e : K) : kSU • w5 a c e = w5 (ω * a) (ω * c) ((ω + 1) * e) := by
  rw [kSU_smul]
  funext i
  fin_cases i <;> simp

theorem gSU_w5 (a c e : K) : gSU • w5 a c e = w5 a (c + e) e := by
  rw [gSU_smul]
  have h1 : (ω + 1) * c + ω * c + e = c + e := by linear_combination (ω * c) * two_eq_zero
  have h2 : ω * c + (ω + 1) * c + e = c + e := by linear_combination (ω * c) * two_eq_zero
  have h3 : c + c + e = e := by linear_combination c * two_eq_zero
  funext i
  fin_cases i <;> simp [h1, h2, h3]

theorem kgkk_w5 (h : K) : kSU • gSU • kSU • kSU • w5 1 h 1 = w5 1 (h + ω + 1) 1 := by
  rw [kSU_w5, kSU_w5, gSU_w5, kSU_w5]
  have e1 : ω * (ω * (ω * 1)) = 1 := by
    linear_combination (ω + 1) * omega_mul_omega + ω * two_eq_zero
  have e2 : ω * (ω * (ω * h) + (ω + 1) * ((ω + 1) * 1)) = h + ω + 1 := by
    linear_combination (h + 1) * (ω + 1) * omega_mul_omega + (h * ω + ω + ω * ω) * two_eq_zero
  have e3 : (ω + 1) * ((ω + 1) * ((ω + 1) * 1)) = 1 := by
    linear_combination (ω + 4) * omega_mul_omega + (4 * ω + 2) * two_eq_zero
  rw [e1, e2, e3]

theorem eq_smul_w5 {T : Fin 5 → K} (hT : herm frob T T = 0)
    (hST : herm frob (w5 0 1 0) T = 0) (hQT : herm frob (w5 1 0 1) T = 0)
    (hne : ∀ c : K, T ≠ c • w5 0 1 0) : ∃ a h : K, a ≠ 0 ∧ T = a • w5 1 h 1 := by
  rw [herm_w5_left, map_zero, map_one, zero_mul, zero_mul, zero_add, one_mul, one_mul,
    add_zero] at hST
  rw [herm_w5_left, map_zero, map_one, zero_mul, zero_mul, add_zero, add_zero, one_mul,
    one_mul] at hQT
  rw [herm_self_five] at hT
  have h3 : T 3 = T 2 := (eq_of_add_eq_zero_K hST).symm
  have h4 : T 4 = T 0 := (eq_of_add_eq_zero_K hQT).symm
  rw [h3, h4] at hT
  have h1 : T 1 = 0 := by
    have h : frob (T 1) * T 1 = 0 := by
      linear_combination hT - (frob (T 0) * T 0 + frob (T 2) * T 2) * two_eq_zero
    rcases mul_eq_zero.1 h with h | h
    · exact frob_eq_zero_iff.1 h
    · exact h
  obtain ⟨a, c, rfl⟩ : ∃ a c : K, T = w5 a c a := ⟨T 0, T 2, by
    funext i
    fin_cases i <;> simp [h1, h3, h4]⟩
  have ha : a ≠ 0 := fun h0 => hne c (by rw [h0, smul_w5, mul_zero, mul_one])
  exact ⟨a, a⁻¹ * c, ha, by rw [smul_w5, mul_one, mul_inv_cancel_left₀ ha]⟩

theorem localClass_DG_nonempty {m : ℕ} (hm : 4 ≤ m) {p : PG m} (hp : p ∈ DG m) :
    (LocalClass (DG m) p).Nonempty := by
  obtain ⟨v, hv0, hv, rfl⟩ := hp
  obtain ⟨w, hw0, hw, hvw, hwv⟩ := exists_isotropic_perp hm hv0 hv
  exact ⟨tq w, (tq_mem_localClass_iff (by omega) hv0 hv hw0 hw).2 ⟨hvw, hwv⟩⟩

theorem tq_smul_eq {m : ℕ} {v : Fin m → K} (hv : herm frob v v = 0) {c : K} (hc : c ≠ 0) :
    tq (c • v) = tq v :=
  congrArg QuotientGroup.mk (tvU_smul_vec hv hc)

theorem omega_add_one_ne_zero : ω + 1 ≠ 0 := fun h =>
  omega_ne_one (by linear_combination h - one_add_one_K)

theorem false_of_flag_muY_zero {G : Type} [Group G] {D : Set G} (hP : Pair G D)
    (hZ : Subgroup.center G = ⊥) (hS : IsSimpleGroup (commutator G)) {d : G} (hd : d ∈ D)
    (φ : LocalQuotient D d ≃* PG 5) (hφ : φ '' LocalImages D d = DG 5) {x : G} (hx : x ∈ D)
    (hxd : x * d ≠ d * x) {f₀ : G} (hf₀ : f₀ ∈ muSet D d x)
    (hιf₀ : (φ ∘ lqMap D d) f₀ = tq (v₀ 3))
    (hS₀ : (φ ∘ lqMap D d) '' muSet D d x ∩ LocalClass (DG 5) (tq (v₀ 3)) = muY 0) :
    False := by
  have hPG : Pair (PG 5) (DG 5) := pair_DG (by norm_num)
  have hF : MuSections (DG 5) := muSections_DG (n := 3) (by norm_num)
  have hinv : ∀ (g : SUid frob 5) (c : K), c ≠ 0 →
      (∀ w : Fin 5 → K, π 3 w = 0 → g • w = c • w) → ∀ v : Fin 5 → K, herm frob v v = 0 →
        tq v ∈ (φ ∘ lqMap D d) '' muSet D d x → tq (g • v) ∈ (φ ∘ lqMap D d) '' muSet D d x := by
    intro g c hc hg v hv hvM
    have hfix : ∀ w : Fin 5 → K, herm frob w w = 0 → π 3 w = 0 →
        (QuotientGroup.mk g : PG 5) * tq w * (QuotientGroup.mk g)⁻¹ = tq w :=
      fun w hw hπ => by rw [conj_tq g hw, hg w hπ, tq_smul_eq hw hc]
    have hμ : (fun s => (QuotientGroup.mk g : PG 5) * s * (QuotientGroup.mk g)⁻¹) ''
        muY (0 : Fin 3 → K) = muY 0 := by
      rw [muY, Pair.image_conj_muSet hPG, hfix _ herm_v₀_v₀ π_v₀,
        hfix _ (herm_uy_uy 0) (π_uy 0)]
    have key := image_conj_eq_of_fix hP hZ hS hd φ hφ hPG
      (tripleProperty_DG (n := 3) (by norm_num))
      (fun p hp => localClass_DG_nonempty (by norm_num) hp) hx hxd hf₀ (QuotientGroup.mk g)
      (by rw [hιf₀]; exact hfix _ herm_v₀_v₀ π_v₀) (by rw [hιf₀, hS₀]; exact hμ)
    rw [← key]
    exact ⟨tq v, hvM, conj_tq g hv⟩
  have hk := hinv kSU ω omega_ne_zero fun w hw => kSU_smul_of_π hw
  have hg := hinv gSU 1 one_ne_zero fun w hw => gSU_smul_of_π hw
  have hs : tq (w5 0 1 0) ∈ (φ ∘ lqMap D d) '' muSet D d x ∩ LocalClass (DG 5) (tq (v₀ 3)) := by
    rw [hS₀, muY_eq (by norm_num)]
    refine ⟨v3 1 1 0, v3_ne_zero_of_left one_ne_zero _ _, isotropic_v3_left one_ne_zero, ?_⟩
    rw [herm_zero_left, sv, zero_smul, zero_add]
    rfl
  obtain ⟨⟨f₁, hf₁, hf₁s⟩, -⟩ := hs
  have hMe := meetsTwins_inter hP hZ hS hd φ hφ hF hx hxd hf₁
  rw [hf₁s] at hMe
  have hS0 : w5 0 1 0 ≠ 0 := w5_ne_zero_of_mid one_ne_zero _ _
  have hSi : herm frob (w5 0 1 0) (w5 0 1 0) = 0 := isotropic_w5 0 1
  have hQ0 : w5 1 0 1 ≠ 0 := w5_ne_zero_of_left one_ne_zero _ _
  have hq₀ : tq (w5 1 0 1) ∈ LocalClass (DG 5) (tq (w5 0 1 0)) :=
    (tq_mem_localClass_iff (by norm_num) hS0 hSi hQ0 (isotropic_w5 1 0)).2
      ⟨by rw [herm_w5, map_zero, zero_mul, add_zero], fun c h => by
        have h0 : (1 : K) = c * 0 := congrFun h 0
        exact one_ne_zero (h0.trans (mul_zero c))⟩
  obtain ⟨_, ⟨htM, htS⟩, htw⟩ := hMe _ hq₀
  obtain ⟨T, hT0, hT, rfl⟩ := htS.1
  have hST := (tq_mem_localClass_iff (by norm_num) hS0 hSi hT0 hT).1 htS
  have hQT := (tq_commute_iff (by norm_num) hQ0 (isotropic_w5 1 0) hT0 hT).1 htw.2.2.1
  obtain ⟨a, h, ha, rfl⟩ := eq_smul_w5 hT hST.1 hQT hST.2
  rw [tq_smul_eq (isotropic_w5 1 h) ha] at htM
  have hA : tq (w5 1 (h + 1) 1) ∈ (φ ∘ lqMap D d) '' muSet D d x := by
    have h1 := hg _ (isotropic_w5 1 h) htM
    rwa [gSU_w5] at h1
  have hB : tq (w5 1 (h + ω + 1) 1) ∈ (φ ∘ lqMap D d) '' muSet D d x := by
    have h1 := hk _ (isotropic_w5 1 h) htM
    have h2 := hk _ (by rw [herm_smul_smul]; exact isotropic_w5 1 h) h1
    have h3 := hg _ (by rw [herm_smul_smul, herm_smul_smul]; exact isotropic_w5 1 h) h2
    have h4 := hk _ (by
      rw [herm_smul_smul, herm_smul_smul, herm_smul_smul]
      exact isotropic_w5 1 h) h3
    rwa [kgkk_w5] at h4
  have htw' := isTwin_add_smul (m := 5) (by norm_num) (w5_ne_zero_of_left one_ne_zero h 1)
    (isotropic_w5 1 h) (w5_ne_zero_of_left one_ne_zero (h + 1) 1) (isotropic_w5 1 (h + 1))
    (by rw [herm_w5, map_one, one_mul, add_self_K]) (fun c hc => by
      rw [smul_w5] at hc
      have h0 : (1 : K) = c * 1 := congrFun hc 0
      have h2 : h + 1 = c * h := congrFun hc 2
      rw [mul_one] at h0
      rw [← h0, one_mul] at h2
      exact one_ne_zero (by linear_combination h2)) (ω + 1)
  have hX : w5 1 (h + 1) 1 + (ω + 1) • w5 1 h 1 = w5 ω (ω * h + 1) ω := by
    rw [smul_w5, w5_add]
    have e1 : 1 + (ω + 1) * 1 = ω := by linear_combination one_add_one_K
    have e2 : h + 1 + (ω + 1) * h = ω * h + 1 := by linear_combination h * two_eq_zero
    rw [e1, e2]
  have hR : tq (w5 1 (h + 1) 1 + (ω + 1) • w5 1 h 1) = tq (w5 1 (h + ω + 1) 1) := by
    rw [hX, ← tq_smul_eq (isotropic_w5 ω (ω * h + 1)) omega_add_one_ne_zero, smul_w5]
    have e3 : (ω + 1) * ω = 1 := by linear_combination omega_mul_omega + ω * two_eq_zero
    have e4 : (ω + 1) * (ω * h + 1) = h + ω + 1 := by
      linear_combination h * omega_mul_omega + (ω * h) * two_eq_zero
    rw [e3, e4]
  rw [hR] at htw'
  obtain ⟨f₂, hf₂, hf₂t⟩ := htM
  have hT₂ := twinFree_inter hP hZ hS hd φ hφ hF hx hxd hf₂
  rw [hf₂t] at hT₂
  have heq := hT₂ _ ⟨hA, htw'.1⟩ _ ⟨hB, htw'.2.1⟩ htw'
  obtain ⟨c, hc⟩ := (tq_eq_tq_iff (by norm_num) (w5_ne_zero_of_left one_ne_zero (h + 1) 1)
    (isotropic_w5 1 (h + 1)) (w5_ne_zero_of_left one_ne_zero (h + ω + 1) 1)
    (isotropic_w5 1 (h + ω + 1))).1 heq
  rw [smul_w5] at hc
  have h0 : (1 : K) = c * 1 := congrFun hc 0
  have h2 : h + ω + 1 = c * (h + 1) := congrFun hc 2
  rw [mul_one] at h0
  rw [← h0, one_mul] at h2
  exact omega_ne_zero (by linear_combination h2)

theorem false_of_localPG_five {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hnab : NonabelianCommutator G) {d : G} (hd : d ∈ D) (φ : LocalQuotient D d ≃* PG 5)
    (hφ : φ '' LocalImages D d = DG 5) : False := by
  obtain ⟨hP, hZ, hS⟩ := hH
  have hna : ∃ a b : commutator G, a * b ≠ b * a := hnab
  have hPG : Pair (PG 5) (DG 5) := pair_DG (by norm_num)
  obtain ⟨x, hx, hxd⟩ : ∃ x ∈ D, x * d ≠ d * x := by
    by_contra! h
    have hdZ : d ∈ Subgroup.center G := (Pair.mem_center_iff hP).2 h
    rw [hZ, Subgroup.mem_bot] at hdZ
    exact Pair.ne_one hP hd hdZ
  obtain ⟨f₀, hf₀⟩ := Pair.muSet_nonempty hP (Pair.connected_of_nonabelian hP hS hna) hd hx hxd
  have hι₁ := isChart_of_localQuotientEquiv hP (Pair.starImage_injective_of_simple hP hZ hS hd)
    φ hφ
  obtain ⟨ψ, hψD, hψ⟩ := Pair.exists_mulEquiv hPG (hι₁.mem hf₀.1)
    (tq_mem_DG v₀_ne_zero herm_v₀_v₀)
  set φ' := φ.trans ψ with hφ'def
  have hφ' : φ' '' LocalImages D d = DG 5 := by
    rw [hφ'def, MulEquiv.coe_trans, Set.image_comp, hφ, hψD]
  have hιf₀ : (φ' ∘ lqMap D d) f₀ = tq (v₀ 3) := hψ
  have hF : MuSections (DG 5) := muSections_DG (n := 3) (by norm_num)
  have hT := twinFree_inter hP hZ hS hd φ' hφ' hF hx hxd hf₀
  have hMe := meetsTwins_inter hP hZ hS hd φ' hφ' hF hx hxd hf₀
  rw [hιf₀] at hT hMe
  have hτ : ∀ a ∈ (φ' ∘ lqMap D d) '' muSet D d x ∩ LocalClass (DG 5) (tq (v₀ 3)),
      ∀ b ∈ (φ' ∘ lqMap D d) '' muSet D d x ∩ LocalClass (DG 5) (tq (v₀ 3)),
        a * b * a ∈ (φ' ∘ lqMap D d) '' muSet D d x ∩ LocalClass (DG 5) (tq (v₀ 3)) := by
    rintro _ ⟨⟨a, ha, rfl⟩, ha'⟩ _ ⟨⟨b, hb, rfl⟩, hb'⟩
    exact ⟨mul_mul_mem_image_muSet hP φ' ha hb, Pair.mul_mul_mem_localClass_of_mem hPG ha' hb'⟩
  obtain ⟨γs, hγS, h1, h2⟩ := exists_section_fun (n := 3) (by norm_num) Set.inter_subset_right
    hτ hT hMe
  obtain ⟨y, hy⟩ := exists_eq_herm_of_section ⟨h1, h2⟩
  have hSy : (φ' ∘ lqMap D d) '' muSet D d x ∩ LocalClass (DG 5) (tq (v₀ 3)) = muY y := by
    rw [muY_eq (by norm_num)]
    ext q
    constructor
    · intro hq
      obtain ⟨α, z, hz0, hz, rfl⟩ := exists_sv_of_mem_localClass (n := 3) (by norm_num) hq.2
      have hmem := hγS z hz0 hz
      rw [hy z hz0 hz] at hmem
      exact ⟨z, hz0, hz, hT _ hq _ hmem
        ((isTwin_sv_iff (by norm_num) hz0 hz hz0 hz).2 ⟨1, (one_smul K z).symm⟩)⟩
    · rintro ⟨z, hz0, hz, rfl⟩
      have hmem := hγS z hz0 hz
      rwa [hy z hz0 hz] at hmem
  obtain ⟨g, hgv, hgu⟩ := exists_smul_eq_hyp (n := 3) (by norm_num) v₀_ne_zero herm_v₀_v₀
    (herm_uy_uy y) (herm_v₀_uy y)
  set c : PG 5 := QuotientGroup.mk g with hcdef
  have hcv : c * tq (v₀ 3) * c⁻¹ = tq (v₀ 3) := by rw [hcdef, conj_tq g herm_v₀_v₀, hgv]
  set φ'' := φ'.trans (MulAut.conj c) with hφ''def
  have hφ'' : φ'' '' LocalImages D d = DG 5 := by
    rw [hφ''def, MulEquiv.coe_trans, Set.image_comp, hφ', Pair.image_conj hPG]
  have hfun : ∀ s, (φ'' ∘ lqMap D d) s = c * (φ' ∘ lqMap D d) s * c⁻¹ := fun s => rfl
  have hιf₀' : (φ'' ∘ lqMap D d) f₀ = tq (v₀ 3) := by rw [hfun, hιf₀, hcv]
  have hS₀ : (φ'' ∘ lqMap D d) '' muSet D d x ∩ LocalClass (DG 5) (tq (v₀ 3)) = muY 0 := by
    have e1 : (φ'' ∘ lqMap D d) '' muSet D d x =
        (fun s => c * s * c⁻¹) '' ((φ' ∘ lqMap D d) '' muSet D d x) := by
      rw [Set.image_image]
      rfl
    have e2 : LocalClass (DG 5) (tq (v₀ 3)) =
        (fun s => c * s * c⁻¹) '' LocalClass (DG 5) (tq (v₀ 3)) := by
      rw [Pair.image_conj_localClass hPG, hcv]
    rw [e1, e2, ← Set.image_inter (conj_injective c), hSy, muY, Pair.image_conj_muSet hPG, hcv,
      hcdef, conj_tq g (herm_uy_uy y), hgu, muSet_eq_muY (by norm_num) herm_u₀_u₀ herm_v₀_u₀,
      π_u₀]
  exact false_of_flag_muY_zero hP hZ hS hd φ'' hφ'' hx hxd hf₀ hιf₀' hS₀

end CFSG.Fischer.Classification.LocalU

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification.Unitary
  CFSG.Fischer.Classification.LocalU

theorem false_of_localU2_five {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hnab : NonabelianCommutator G) {d : G} (hd : d ∈ D) (φ : LocalQuotient D d ≃* U2 5)
    (hφ : φ '' LocalImages D d = DU 5) : False := by
  refine false_of_localPG_five hH hnab hd (φ.trans (u2Equiv 5)) ?_
  rw [MulEquiv.coe_trans, Set.image_comp, hφ, image_DU]

theorem false_of_local_case4_five {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hnab : NonabelianCommutator G) {d : G} (hd : d ∈ D)
    (h : CFSG.Open.fischerCentralQuotientModel (LocalImages D d) (SUm 5) (TU 5)) : False := by
  obtain ⟨φ, hφ⟩ := fischerCentralQuotientModel_iff_U2.1 h
  exact false_of_localU2_five hH hnab hd φ hφ

end CFSG.Fischer.Classification
