module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutTorus
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FCoord

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three


section Diag

variable {K : Type} [Field K] [Finite K]

@[expose] def diagAut (b : Fin Tag.D4.rank → Kˣ) : MulAut (adjointGroup Tag.D4 K) :=
  exactNormalAut Tag.D4 K b 1 0

theorem diagAut_mul (b b' : Fin Tag.D4.rank → Kˣ) :
    diagAut b * diagAut b' = diagAut (b * b') :=
  exactNormalAut_diag_mul b b' 1 0

theorem diagAut_one : diagAut (1 : Fin Tag.D4.rank → Kˣ) = (1 : MulAut (adjointGroup Tag.D4 K)) := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  change (exactNormalAut Tag.D4 K 1 1 0 x : ModGL Tag.D4 K) = x
  rw [coe_exactNormalAut, rootDiagUnit_one]
  change (1 : ModGL Tag.D4 K) * 1 * Units.map (entrywiseHom (RingEquiv.refl K).toRingHom) (x : ModGL Tag.D4 K) *
    (1 : ModGL Tag.D4 K)⁻¹ * (1 : ModGL Tag.D4 K)⁻¹ = _
  have : Units.map (entrywiseHom (RingEquiv.refl K).toRingHom) (x : ModGL Tag.D4 K) = x :=
    Units.ext (entrywise_id _)
  rw [this]; simp

theorem diagAut_inv (b : Fin Tag.D4.rank → Kˣ) : (diagAut b)⁻¹ = diagAut b⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right]
  rw [diagAut_mul, mul_inv_cancel, diagAut_one]

theorem exactPerm_D4 (ε : ℕ) : exactPerm Tag.D4 ε = 1 := rfl

theorem normal_mul_diag (a b : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) :
    exactNormalAut Tag.D4 K a σ 0 * diagAut b =
      diagAut (fun j => Units.map σ.toRingHom.toMonoidHom (b j)) * exactNormalAut Tag.D4 K a σ 0 := by
  rw [diagAut, exactNormalAut_mul, diagAut, exactNormalAut_diag_mul]
  have h1 : (fun j => a j * (Units.map σ.toRingHom.toMonoidHom) (b ((exactPerm Tag.D4 0).symm j))) =
      (fun j => (Units.map σ.toRingHom.toMonoidHom) (b j)) * a := by
    funext j
    rw [exactPerm_D4]
    simp [mul_comm]
    rfl
  rw [h1]
  simp

theorem graph_mul_diag (ε : ℕ) (b : Fin Tag.D4.rank → Kˣ) :
    d4Graph K ε * diagAut b = diagAut (fun j => b ((d4Rho ^ ε).symm j)) * d4Graph K ε := by
  refine mulAut_ext_adjX_adjY (fun i c => ?_) fun i c => ?_
  · rw [MulAut.mul_apply, MulAut.mul_apply, d4Graph_adjX]
    change d4Graph K ε (exactNormalAut Tag.D4 K b 1 0 (adjX Tag.D4 K i c)) = _
    rw [exactNormalAut_adjX, d4Graph_adjX]
    change _ = exactNormalAut Tag.D4 K _ 1 0 (adjX Tag.D4 K ((d4Rho ^ ε) i) c)
    rw [exactNormalAut_adjX]
    simp [exactPerm_D4]
  · rw [MulAut.mul_apply, MulAut.mul_apply, d4Graph_adjY]
    change d4Graph K ε (exactNormalAut Tag.D4 K b 1 0 (adjY Tag.D4 K i c)) = _
    rw [exactNormalAut_adjY, d4Graph_adjY]
    change _ = exactNormalAut Tag.D4 K _ 1 0 (adjY Tag.D4 K ((d4Rho ^ ε) i) c)
    rw [exactNormalAut_adjY]
    simp [exactPerm_D4]

theorem diagAut_adjX (b : Fin Tag.D4.rank → Kˣ) (i : Fin Tag.D4.rank) (c : K) :
    diagAut b (adjX Tag.D4 K i c) = adjX Tag.D4 K i ((b i : K) * c) := by
  rw [diagAut, exactNormalAut_adjX]
  simp [exactPerm_D4]

theorem diagAut_injective {b b' : Fin Tag.D4.rank → Kˣ} (h : diagAut b = diagAut (K := K) b') :
    b = b' := by
  funext i
  have h1 := congrArg (fun m => m (adjX Tag.D4 K i 1)) h
  simp only [diagAut_adjX, mul_one] at h1
  exact Units.ext (by simpa using adjX_injective (τ := Tag.D4) (K := K) i h1)

theorem mem_torusGroup_of_conj_mem {x : adjointGroup Tag.D4 K}
    (hA : MulAut.conj x ∈ unipotentPairAut Tag.D4 K) : (x : ModGL Tag.D4 K) ∈ torusGroup Tag.D4 K := by
  obtain ⟨hU, hV⟩ := hA
  have hNU := mem_normalizer_of_map_conj_subgroupOf posUnipotent_le_adjointGroup hU
  have hNV := mem_normalizer_of_map_conj_subgroupOf negUnipotent_le_adjointGroup hV
  have hB : (x : ModGL Tag.D4 K) ∈ borelGroup Tag.D4 K := by
    rw [← (borel_self_normalizers Tag.D4 K).1]
    exact Subgroup.mem_inf.2 ⟨x.2, hNU⟩
  have hB' : (x : ModGL Tag.D4 K) ∈ oppositeBorel Tag.D4 K := by
    rw [← oppositeBorel_normalizer Tag.D4 K]
    exact Subgroup.mem_inf.2 ⟨x.2, hNV⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  rw [← (opposite_Borel_intersection Tag.D4 K w₀ hw₀).2.2.1]
  exact Subgroup.mem_inf.2 ⟨hB, hB'⟩

theorem conj_rootDiagUnit_eq_diagAut (b : Fin Tag.D4.rank → Kˣ)
    (hb : rootDiagUnit Tag.D4 b ∈ adjointGroup Tag.D4 K) :
    MulAut.conj (⟨rootDiagUnit Tag.D4 b, hb⟩ : adjointGroup Tag.D4 K) = diagAut b := by
  refine MulEquiv.ext fun y => Subtype.ext ?_
  change _ = (exactNormalAut Tag.D4 K b 1 0 y : ModGL Tag.D4 K)
  rw [coe_exactNormalAut]
  have : Units.map (entrywiseHom (RingEquiv.refl K).toRingHom) (y : ModGL Tag.D4 K) = y :=
    Units.ext (entrywise_id _)
  change _ = rootDiagUnit Tag.D4 b * (1 : ModGL Tag.D4 K) *
    Units.map (entrywiseHom (RingEquiv.refl K).toRingHom) (y : ModGL Tag.D4 K) *
      (1 : ModGL Tag.D4 K)⁻¹ * (rootDiagUnit Tag.D4 b)⁻¹
  rw [this]
  simp [MulAut.conj_apply]

theorem diagAut_inner_iff (b : Fin Tag.D4.rank → Kˣ) :
    (∃ x : adjointGroup Tag.D4 K, MulAut.conj x = diagAut b) ↔ ∃ cc, b = cartanChar cc := by
  constructor
  · rintro ⟨x, hx⟩
    have hA : MulAut.conj x ∈ unipotentPairAut Tag.D4 K := by
      rw [hx]; exact exactNormalAut_mem b 1 0
    obtain ⟨cc, hcc⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.mem_torusGroup_iff_cartanChar.1
      (mem_torusGroup_of_conj_mem hA)
    refine ⟨cc, ?_⟩
    have hmem : rootDiagUnit Tag.D4 (cartanChar cc) ∈ adjointGroup Tag.D4 K := hcc ▸ x.2
    have h1 : MulAut.conj x = diagAut (cartanChar cc) := by
      have : x = ⟨rootDiagUnit Tag.D4 (cartanChar cc), hmem⟩ := Subtype.ext hcc
      rw [this]
      exact conj_rootDiagUnit_eq_diagAut _ hmem
    exact diagAut_injective (hx.symm.trans h1)
  · rintro ⟨cc, rfl⟩
    have hmem : rootDiagUnit Tag.D4 (cartanChar cc) ∈ adjointGroup Tag.D4 K := by
      rw [← list_prod_torusElt_eq_rootDiagUnit]
      refine Subgroup.list_prod_mem _ fun g hg => ?_
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
      exact torusElt_mem_adjointGroup i _
    exact ⟨⟨_, hmem⟩, conj_rootDiagUnit_eq_diagAut _ hmem⟩

theorem cartanD4_apply' (i j : Fin Tag.D4.rank) :
    Tag.D4.cartan i j = (![![2, 0, -1, 0], ![0, 2, -1, 0], ![-1, -1, 2, -1], ![0, 0, -1, 2]] :
      Fin 4 → Fin 4 → ℤ) i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem cartanChar_D4_apply (cc : Fin Tag.D4.rank → Kˣ) :
    cartanChar cc 0 = cc 0 ^ 2 * (cc 2)⁻¹ ∧ cartanChar cc 1 = cc 1 ^ 2 * (cc 2)⁻¹ ∧
    cartanChar cc 2 = (cc 0)⁻¹ * (cc 1)⁻¹ * cc 2 ^ 2 * (cc 3)⁻¹ ∧
    cartanChar cc 3 = cc 3 ^ 2 * (cc 2)⁻¹ := by
  have key : ∀ l : Fin Tag.D4.rank, cartanChar (τ := Tag.D4) cc l =
      cc 0 ^ Tag.D4.cartan 0 l * cc 1 ^ Tag.D4.cartan 1 l * cc 2 ^ Tag.D4.cartan 2 l *
        cc 3 ^ Tag.D4.cartan 3 l := fun l => by
    unfold cartanChar
    exact Fin.prod_univ_four _
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [key] <;> simp only [cartanD4_apply'] <;> simp <;> exact mul_comm _ _

theorem squares_of_cartan {a : Fin Tag.D4.rank → Kˣ} (h : ∃ cc, a = cartanChar cc) :
    IsSquare ((a 0 : K) * a 1) ∧ IsSquare ((a 0 : K) * a 3) := by
  obtain ⟨cc, rfl⟩ := h
  obtain ⟨h0, h1, -, h3⟩ := cartanChar_D4_apply cc
  have e0 : ((cartanChar cc 0 : Kˣ) : K) = (cc 0 : K) ^ 2 * ((cc 2 : K))⁻¹ := by
    rw [h0]; simp
  have e1 : ((cartanChar cc 1 : Kˣ) : K) = (cc 1 : K) ^ 2 * ((cc 2 : K))⁻¹ := by
    rw [h1]; simp
  have e3 : ((cartanChar cc 3 : Kˣ) : K) = (cc 3 : K) ^ 2 * ((cc 2 : K))⁻¹ := by
    rw [h3]; simp
  have h2 : (cc 2 : K) ≠ 0 := Units.ne_zero _
  constructor
  · refine ⟨(cc 0 : K) * cc 1 * ((cc 2 : K))⁻¹, ?_⟩
    rw [e0, e1]; field_simp
  · refine ⟨(cc 0 : K) * cc 3 * ((cc 2 : K))⁻¹, ?_⟩
    rw [e0, e3]; field_simp

theorem cartan_of_squares {a : Fin Tag.D4.rank → Kˣ} (h01 : IsSquare ((a 0 : K) * a 1))
    (h03 : IsSquare ((a 0 : K) * a 3)) : ∃ cc, a = cartanChar cc := by
  obtain ⟨s, hs⟩ := h01
  obtain ⟨r, hr⟩ := h03
  have ha0 : (a 0 : K) ≠ 0 := Units.ne_zero _
  have ha1 : (a 1 : K) ≠ 0 := Units.ne_zero _
  have ha2 : (a 2 : K) ≠ 0 := Units.ne_zero _
  have ha3 : (a 3 : K) ≠ 0 := Units.ne_zero _
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact mul_ne_zero ha0 ha1 (by simpa using hs)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact mul_ne_zero ha0 ha3 (by simpa using hr)
  let su : Kˣ := Units.mk0 s hs0
  let ru : Kˣ := Units.mk0 r hr0
  let w : Kˣ := a 2 * su * ru * (a 0)⁻¹
  have hw : (w : K) = (a 2 : K) * s * r * ((a 0 : K))⁻¹ := by simp [w, su, ru]
  have hw0 : (w : K) ≠ 0 := Units.ne_zero _
  let cc : Fin Tag.D4.rank → Kˣ := ![a 0 * w, su * w, a 0 * w ^ 2, ru * w]
  have hc0 : cc 0 = a 0 * w := rfl
  have hc1 : cc 1 = su * w := rfl
  have hc2 : cc 2 = a 0 * w ^ 2 := rfl
  have hc3 : cc 3 = ru * w := rfl
  obtain ⟨c0, c1, c2, c3⟩ := cartanChar_D4_apply cc
  have e0 : a 0 = cartanChar cc 0 := by
    refine Units.ext ?_
    have := congrArg Units.val c0
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hc0, hc2] at this
    rw [this]; field_simp
  have e1 : a 1 = cartanChar cc 1 := by
    refine Units.ext ?_
    have := congrArg Units.val c1
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hc1, hc2] at this
    rw [this]
    simp only [su, Units.val_mk0]
    field_simp
    linear_combination hs
  have e2 : a 2 = cartanChar cc 2 := by
    refine Units.ext ?_
    have := congrArg Units.val c2
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hc0, hc1, hc2,
      hc3] at this
    rw [this]
    simp only [su, ru, Units.val_mk0]
    rw [hw]
    field_simp
  have e3 : a 3 = cartanChar cc 3 := by
    refine Units.ext ?_
    have := congrArg Units.val c3
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hc2, hc3] at this
    rw [this]
    simp only [ru, Units.val_mk0]
    field_simp
    linear_combination hr
  refine ⟨cc, funext fun j => ?_⟩
  fin_cases j
  exacts [e0, e1, e2, e3]

section Squares

variable {K : Type} [Field K] [Finite K]

theorem isSquare_mul_map (hK2 : ringChar K ≠ 2) (σ : K ≃+* K) {x : K} (hx : x ≠ 0) :
    IsSquare (x * σ x) := by
  haveI := Fintype.ofFinite K
  have hσx : σ x ≠ 0 := by simpa using hx
  have hq : Fintype.card K % 2 = 1 := FiniteField.odd_card_of_char_ne_two hK2
  have hsq : ∀ y : K, y ≠ 0 → (y ^ (Fintype.card K / 2)) ^ 2 = 1 := by
    intro y hy
    rw [← pow_mul]
    have : Fintype.card K / 2 * 2 = Fintype.card K - 1 := by omega
    rw [this]
    exact FiniteField.pow_card_sub_one_eq_one y hy
  have hpm : ∀ y : K, y ≠ 0 → (y ^ (Fintype.card K / 2) = 1 ∨ y ^ (Fintype.card K / 2) = -1) :=
    fun y hy => sq_eq_one_iff.1 (hsq y hy)
  have hσpm : (σ x) ^ (Fintype.card K / 2) = x ^ (Fintype.card K / 2) := by
    rw [← map_pow]
    rcases hpm x hx with h | h
    · rw [h]; simp
    · rw [h]; simp
  rw [FiniteField.isSquare_iff hK2 (mul_ne_zero hx hσx), mul_pow, hσpm, ← sq]
  exact hsq x hx

theorem isSquare_of_mul_sq {x y : K} (hy : y ≠ 0) (h : IsSquare (x * y ^ 2)) : IsSquare x := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r * y⁻¹, ?_⟩
  have : x = (x * y ^ 2) * (y⁻¹) ^ 2 := by field_simp
  rw [this, hr]; ring

theorem isSquare_twist (hK2 : ringChar K ≠ 2) (σ : K ≃+* K) {u v : K} (hv : v ≠ 0)
    (h : IsSquare (u * (σ v)⁻¹)) : IsSquare (u * v) := by
  have hσv : σ v ≠ 0 := by simpa using hv
  have h1 := isSquare_mul_map hK2 σ hv
  have h2 := h.mul h1
  have e : u * (σ v)⁻¹ * (v * σ v) = u * v := by field_simp
  rwa [e] at h2

theorem d4Rho_symm_values_one : (d4Rho ^ 1).symm 0 = 3 ∧ (d4Rho ^ 1).symm 1 = 0 ∧
    (d4Rho ^ 1).symm 3 = 1 := by
  unfold d4Rho TwistTag.perm
  decide +kernel

theorem d4Rho_symm_values_two : (d4Rho ^ 2).symm 0 = 1 ∧ (d4Rho ^ 2).symm 1 = 3 ∧
    (d4Rho ^ 2).symm 3 = 0 := by
  unfold d4Rho TwistTag.perm
  decide +kernel

theorem cartan_of_twist (hK2 : ringChar K ≠ 2) (σ : K ≃+* K) (ε : ℕ) (hε : ε = 1 ∨ ε = 2)
    (a : Fin Tag.D4.rank → Kˣ)
    (h : ∃ cc, (fun j => a j * (Units.map σ.toRingHom.toMonoidHom (a ((d4Rho ^ ε).symm j)))⁻¹) =
      cartanChar cc) : ∃ cc, a = cartanChar cc := by
  obtain ⟨hw01, hw03⟩ := squares_of_cartan h
  have ha0 : (a 0 : K) ≠ 0 := Units.ne_zero _
  have ha1 : (a 1 : K) ≠ 0 := Units.ne_zero _
  have ha2 : (a 2 : K) ≠ 0 := Units.ne_zero _
  have ha3 : (a 3 : K) ≠ 0 := Units.ne_zero _
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, RingEquiv.toRingHom_eq_coe,
    MonoidHom.coe_coe, RingHom.coe_coe] at hw01 hw03
  rcases hε with rfl | rfl
  · obtain ⟨e0, e1, e3⟩ := d4Rho_symm_values_one
    rw [e0, e1] at hw01
    rw [e0, e3] at hw03
    have h1 : IsSquare ((a 1 : K) * a 3) := by
      have := isSquare_twist hK2 σ (u := (a 0 : K) * a 1) (v := (a 3 : K) * a 0)
        (mul_ne_zero ha3 ha0) (by
          rw [map_mul]
          convert hw01 using 1
          field_simp
          rfl)
      have e : (a 0 : K) * a 1 * ((a 3 : K) * a 0) = (a 0) ^ 2 * ((a 1 : K) * a 3) := by ring
      rw [e] at this
      exact isSquare_of_mul_sq ha0 (by simpa [mul_comm] using this)
    have h2 : IsSquare ((a 0 : K) * a 1) := by
      have := isSquare_twist hK2 σ (u := (a 0 : K) * a 3) (v := (a 3 : K) * a 1)
        (mul_ne_zero ha3 ha1) (by
          rw [map_mul]
          convert hw03 using 1
          field_simp
          rfl)
      have e : (a 0 : K) * a 3 * ((a 3 : K) * a 1) = (a 3) ^ 2 * ((a 0 : K) * a 1) := by ring
      rw [e] at this
      exact isSquare_of_mul_sq ha3 (by simpa [mul_comm] using this)
    refine cartan_of_squares h2 ?_
    have e : (a 0 : K) * a 3 = ((a 0 : K) * a 1) * ((a 1 : K) * a 3) * ((a 1 : K)⁻¹) ^ 2 := by
      field_simp
    rw [e]
    exact (h2.mul h1).mul (by
      refine ⟨(a 1 : K)⁻¹, by ring⟩)
  · obtain ⟨e0, e1, e3⟩ := d4Rho_symm_values_two
    rw [e0, e1] at hw01
    rw [e0, e3] at hw03
    have h1 : IsSquare ((a 0 : K) * a 3) := by
      have := isSquare_twist hK2 σ (u := (a 0 : K) * a 1) (v := (a 1 : K) * a 3)
        (mul_ne_zero ha1 ha3) (by
          rw [map_mul]
          convert hw01 using 1
          field_simp
          rfl)
      have e : (a 0 : K) * a 1 * ((a 1 : K) * a 3) = (a 1) ^ 2 * ((a 0 : K) * a 3) := by ring
      rw [e] at this
      exact isSquare_of_mul_sq ha1 (by simpa [mul_comm] using this)
    have h2 : IsSquare ((a 3 : K) * a 1) := by
      have := isSquare_twist hK2 σ (u := (a 0 : K) * a 3) (v := (a 1 : K) * a 0)
        (mul_ne_zero ha1 ha0) (by
          rw [map_mul]
          convert hw03 using 1
          field_simp
          rfl)
      have e : (a 0 : K) * a 3 * ((a 1 : K) * a 0) = (a 0) ^ 2 * ((a 3 : K) * a 1) := by ring
      rw [e] at this
      exact isSquare_of_mul_sq ha0 (by simpa [mul_comm] using this)
    refine cartan_of_squares ?_ h1
    have e : (a 0 : K) * a 1 = ((a 0 : K) * a 3) * ((a 3 : K) * a 1) * ((a 3 : K)⁻¹) ^ 2 := by
      field_simp
    rw [e]
    exact (h1.mul h2).mul (by
      refine ⟨(a 3 : K)⁻¹, by ring⟩)

end Squares

theorem diag_case_inner (hK2 : ringChar K ≠ 2) (t z : MulAut (adjointGroup Tag.D4 K))
    (g c : adjointGroup Tag.D4 K) (a a_z : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ)
    (hε : ε = 1 ∨ ε = 2)
    (ht : t = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε))
    (hz : z = MulAut.conj c * diagAut a_z) (hzt : z * t = t * z) :
    ∃ y : adjointGroup Tag.D4 K, z = MulAut.conj y := by
  set N : MulAut (adjointGroup Tag.D4 K) := exactNormalAut Tag.D4 K a σ 0 with hN
  set Γ : MulAut (adjointGroup Tag.D4 K) := d4Graph K ε with hΓ
  set Δ : MulAut (adjointGroup Tag.D4 K) := diagAut a_z with hΔ
  set a1 : Fin Tag.D4.rank → Kˣ := fun j => a_z ((d4Rho ^ ε).symm j) with ha1
  set a2 : Fin Tag.D4.rank → Kˣ := fun j => Units.map σ.toRingHom.toMonoidHom (a1 j) with ha2
  have hΓΔ : Γ * Δ = diagAut a1 * Γ := graph_mul_diag ε a_z
  have hNΔ : N * diagAut a1 = diagAut a2 * N := normal_mul_diag a a1 σ
  have e1 : z * t = MulAut.conj (c * Δ g) * (Δ * (N * Γ)) := by
    rw [hz, ht]
    calc MulAut.conj c * Δ * (MulAut.conj g * (N * Γ))
        = MulAut.conj c * (Δ * MulAut.conj g) * (N * Γ) := by group
      _ = MulAut.conj c * (MulAut.conj (Δ g) * Δ) * (N * Γ) := by rw [mul_conj_eq]
      _ = MulAut.conj (c * Δ g) * (Δ * (N * Γ)) := by rw [map_mul]; group
  have e2 : t * z = MulAut.conj (g * N (Γ c)) * (diagAut a2 * (N * Γ)) := by
    rw [hz, ht]
    calc MulAut.conj g * (N * Γ) * (MulAut.conj c * Δ)
        = MulAut.conj g * (N * (Γ * MulAut.conj c)) * Δ := by group
      _ = MulAut.conj g * (N * (MulAut.conj (Γ c) * Γ)) * Δ := by rw [mul_conj_eq]
      _ = MulAut.conj g * ((N * MulAut.conj (Γ c)) * Γ) * Δ := by group
      _ = MulAut.conj g * ((MulAut.conj (N (Γ c)) * N) * Γ) * Δ := by rw [mul_conj_eq]
      _ = MulAut.conj (g * N (Γ c)) * (N * (Γ * Δ)) := by rw [map_mul]; group
      _ = MulAut.conj (g * N (Γ c)) * (N * (diagAut a1 * Γ)) := by rw [hΓΔ]
      _ = MulAut.conj (g * N (Γ c)) * ((N * diagAut a1) * Γ) := by group
      _ = MulAut.conj (g * N (Γ c)) * ((diagAut a2 * N) * Γ) := by rw [hNΔ]
      _ = MulAut.conj (g * N (Γ c)) * (diagAut a2 * (N * Γ)) := by group
  have h3 : MulAut.conj (c * Δ g) * Δ = MulAut.conj (g * N (Γ c)) * diagAut a2 := by
    have h := hzt
    rw [e1, e2] at h
    have h' : (MulAut.conj (c * Δ g) * Δ) * (N * Γ) =
        (MulAut.conj (g * N (Γ c)) * diagAut a2) * (N * Γ) := by
      simpa only [mul_assoc] using h
    exact mul_right_cancel h'
  have hconj : MulAut.conj ((c * Δ g)⁻¹ * (g * N (Γ c))) = diagAut (a_z * a2⁻¹) := by
    rw [← diagAut_mul, ← diagAut_inv]
    have : Δ = MulAut.conj ((c * Δ g)⁻¹ * (g * N (Γ c))) * diagAut a2 := by
      rw [map_mul, map_inv]
      calc Δ = (MulAut.conj (c * Δ g))⁻¹ * (MulAut.conj (c * Δ g) * Δ) := by group
        _ = (MulAut.conj (c * Δ g))⁻¹ * (MulAut.conj (g * N (Γ c)) * diagAut a2) := by rw [h3]
        _ = _ := by group
    exact eq_mul_inv_iff_mul_eq.2 this.symm
  obtain ⟨cc, hcc⟩ := (diagAut_inner_iff _).1 ⟨_, hconj⟩
  obtain ⟨cc', hcc'⟩ := cartan_of_twist hK2 σ ε hε a_z ⟨cc, by
    funext j
    exact congrFun hcc j⟩
  obtain ⟨y', hy'⟩ := (diagAut_inner_iff a_z).2 ⟨cc', hcc'⟩
  exact ⟨c * y', by rw [hz, hΔ, ← hy', map_mul]⟩

end Diag

end CFSG.LocalAnalysis.GLTheoremA
