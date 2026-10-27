module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeSL2Sections
public import CFSG.CharacterTheory.Semidihedral.CentralKernelTorusSplitSupport
public import CFSG.LocalAnalysis.ABGTheoremB.R1NFacts
public import CFSG.CharacterTheory.Semidihedral.AllPrimeLayerFacts
public import CFSG.CharacterTheory.Semidihedral.CentralKernelTorusSplitModel
public import CFSG.CharacterTheory.Semidihedral.FixedTorusDerived
public import CFSG.LocalAnalysis.ABGTheoremB.V4Defs

public noncomputable section

namespace CFSG.Semidihedral.AllPrime

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups
open CFSG.ABGTheoremB CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open scoped Pointwise

section Elementary

private theorem r1n_matrix_aux {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {a b c x e f g h : F}
    (e00 : e * e + f * g = -1) (e11 : g * f + h * h = -1) (hdet : e * h - f * g = 1)
    (c00 : a * e + b * g = e * a + f * c) (c01 : a * f + b * h = e * b + f * x)
    (c10 : c * e + x * g = g * a + h * c)
    (htr : a - 1 + (x - 1) = 0) (hnd : (a - 1) * (x - 1) - b * c = 0) :
    a = 1 ∧ b = 0 ∧ c = 0 ∧ x = 1 := by
  have heh : e + h = 0 := by
    have h' : (e + h) ^ 2 = 0 := by linear_combination e00 + e11 + 2 * hdet
    exact pow_eq_zero_iff two_ne_zero |>.mp h'
  have hh : h = -e := by linear_combination heh
  have hx : x = 2 - a := by linear_combination htr
  subst hh hx
  have h3 : f * (a - 1) = b * e := by
    have h' : 2 * (f * (a - 1) - b * e) = 0 := by linear_combination c01
    have := (mul_eq_zero.mp h').resolve_left h2
    linear_combination this
  have h4 : g * (a - 1) = c * e := by
    have h' : 2 * (g * (a - 1) - c * e) = 0 := by linear_combination -c10
    have := (mul_eq_zero.mp h').resolve_left h2
    linear_combination this
  have h5 : b * g = f * c := by linear_combination c00
  have h6 : (a - 1) ^ 2 + b * c = 0 := by linear_combination -hnd
  have hα : a - 1 = 0 := by
    have h' : (a - 1) ^ 2 * (e * e + f * g) = e ^ 2 * ((a - 1) ^ 2 + b * c) := by
      linear_combination (g * (a - 1)) * h3 + (b * e) * h4
    rw [e00, h6, mul_zero] at h'
    have h'' : (a - 1) ^ 2 = 0 := by linear_combination -h'
    exact pow_eq_zero_iff two_ne_zero |>.mp h''
  have hbc : b * c = 0 := by rw [hα] at h6; linear_combination h6
  have hbe : b * e = 0 := by rw [← h3, hα, mul_zero]
  have hce : c * e = 0 := by rw [← h4, hα, mul_zero]
  have hb : b = 0 := by
    have h' : b * b * (e * e + f * g) = e * (b * e) * b + f * f * (b * c) := by
      linear_combination (f * b) * h5
    rw [e00, hbe, hbc] at h'
    have h'' : b ^ 2 = 0 := by linear_combination -h'
    exact pow_eq_zero_iff two_ne_zero |>.mp h''
  have hc : c = 0 := by
    have h' : c * c * (e * e + f * g) = e * (c * e) * c + g * g * (b * c) := by
      linear_combination (g * c) * h5.symm
    rw [e00, hce, hbc] at h'
    have h'' : c ^ 2 = 0 := by linear_combination -h'
    exact pow_eq_zero_iff two_ne_zero |>.mp h''
  exact ⟨by linear_combination hα, hb, hc, by linear_combination -hα⟩

private theorem sl2_pElement_eq_one_of_commute_sq_neg_one {F : Type} [Field F] {p : ℕ}
    [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) {X d : Matrix.SpecialLinearGroup (Fin 2) F} {k : ℕ}
    (hX : X ^ p ^ k = 1) (hd : d * d = -1) (hXd : X * d = d * X) : X = 1 := by
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff F p 2).mp (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp this)
  set M : Matrix (Fin 2) (Fin 2) F := (X : Matrix (Fin 2) (Fin 2) F) - 1 with hMdef
  have hM : M ^ p ^ k = 0 := by
    rw [hMdef, sub_pow_char_pow_of_commute p k (Commute.one_right _),
      one_pow, ← Matrix.SpecialLinearGroup.coe_pow, hX, Matrix.SpecialLinearGroup.coe_one,
      sub_self]
  have htr : Matrix.trace M = 0 := (Matrix.isNilpotent_trace_of_isNilpotent ⟨_, hM⟩).eq_zero
  have hdet : Matrix.det M = 0 := by
    have h := congrArg Matrix.det hM
    rw [Matrix.det_pow, Matrix.det_zero] at h
    exact pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) |>.mp h
  have hddet := d.2
  rw [Matrix.det_fin_two] at hddet hdet
  rw [Matrix.trace_fin_two] at htr
  have hdd := congrArg (fun Y : Matrix.SpecialLinearGroup (Fin 2) F =>
    (Y : Matrix (Fin 2) (Fin 2) F)) hd
  have hXd' := congrArg (fun Y : Matrix.SpecialLinearGroup (Fin 2) F =>
    (Y : Matrix (Fin 2) (Fin 2) F)) hXd
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one] at hdd hXd'
  have e00 := congrFun (congrFun hdd 0) 0
  have e11 := congrFun (congrFun hdd 1) 1
  have c00 := congrFun (congrFun hXd' 0) 0
  have c01 := congrFun (congrFun hXd' 0) 1
  have c10 := congrFun (congrFun hXd' 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, hMdef] at e00 e11 c00 c01 c10 htr hdet
  obtain ⟨h00, h01, h10, h11⟩ := r1n_matrix_aux h2 e00 e11 hddet c00 c01 c10 htr hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

private theorem conj_eq_inv_of_fixedPointFree {H₀ : Type*} [Group H₀] {U : Subgroup H₀}
    [Finite U] (g : H₀) (hgU : ∀ y ∈ U, g * y * g⁻¹ ∈ U)
    (hg2 : ∀ y ∈ U, g * (g * y * g⁻¹) * g⁻¹ = y)
    (hfree : ∀ y ∈ U, g * y * g⁻¹ = y → y = 1) :
    ∀ y ∈ U, g * y * g⁻¹ = y⁻¹ := by
  let α : U → U := fun y => ⟨g * y * g⁻¹, hgU y y.2⟩
  have hαmul : ∀ x y : U, α (x * y) = α x * α y := fun x y => Subtype.ext (by
    change g * ((x : H₀) * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹)
    group)
  have hαinv : ∀ x : U, α x⁻¹ = (α x)⁻¹ := fun x => Subtype.ext (by
    change g * (x : H₀)⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹
    group)
  have hαα : ∀ x : U, α (α x) = x := fun x => Subtype.ext (hg2 x x.2)
  let φ : U → U := fun x => x⁻¹ * α x
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : α (y * x⁻¹) = y * x⁻¹ := by
      have h : x⁻¹ * α x = y⁻¹ * α y := hxy
      rw [hαmul, hαinv]
      calc α y * (α x)⁻¹ = y * (y⁻¹ * α y) * (α x)⁻¹ := by group
        _ = y * (x⁻¹ * α x) * (α x)⁻¹ := by rw [h]
        _ = y * x⁻¹ := by group
    have h2 := hfree _ (y * x⁻¹).2 (congrArg Subtype.val h1)
    have h3 : y * x⁻¹ = 1 := Subtype.ext h2
    exact (mul_inv_eq_one.mp h3).symm
  have hφs : Function.Surjective φ := Finite.injective_iff_surjective.mp hφ
  intro y hy
  obtain ⟨x, hx⟩ := hφs ⟨y, hy⟩
  have h : α (φ x) = (φ x)⁻¹ := by
    change α (x⁻¹ * α x) = (x⁻¹ * α x)⁻¹
    rw [hαmul, hαinv, hαα]
    group
  rw [hx] at h
  exact congrArg Subtype.val h

end Elementary

section Semidirect

variable {N Q : Type*} [Group N] [Group Q] [Finite N] [Finite Q] {φ : Q →* MulAut N}
  {r : ℕ} [Fact r.Prime]

private theorem r1n_finite_semidirect : Finite (N ⋊[φ] Q) :=
  Finite.of_equiv _ SemidirectProduct.equivProd.symm

private theorem r1n_exists_sylow_comap_inl (P : Sylow r (N ⋊[φ] Q)) :
    ∃ S : Sylow r N, ∀ n : N, n ∈ (S : Subgroup N) ↔
      (SemidirectProduct.inl n : N ⋊[φ] Q) ∈ (P : Subgroup (N ⋊[φ] Q)) := by
  have := r1n_finite_semidirect (N := N) (Q := Q) (φ := φ)
  let W' : Subgroup (N ⋊[φ] Q) := (SemidirectProduct.inl : N →* N ⋊[φ] Q).range
  have hW' : W'.Normal := by
    have h : W' = (SemidirectProduct.rightHom : N ⋊[φ] Q →* Q).ker :=
      SemidirectProduct.range_inl_eq_ker_rightHom
    rw [h]
    infer_instance
  have hPsyl : IsSylowOf r (P : Subgroup (N ⋊[φ] Q)) ⊤ := by
    rw [isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, P.isPGroup', P.not_dvd_index⟩
  have hPW := hPsyl.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top_iff.mpr hW').ge
  have hcardW : Nat.card W' = Nat.card N := by
    change Nat.card (SemidirectProduct.inl : N →* N ⋊[φ] Q).range = _
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective SemidirectProduct.inl_injective,
      Subgroup.card_top]
  have hmap : ((P : Subgroup (N ⋊[φ] Q)).comap SemidirectProduct.inl).map
      (SemidirectProduct.inl : N →* N ⋊[φ] Q) = (P : Subgroup (N ⋊[φ] Q)) ⊓ W' := by
    rw [Subgroup.map_comap_eq, inf_comm]
  have hcard : Nat.card ((P : Subgroup (N ⋊[φ] Q)).comap SemidirectProduct.inl) =
      r ^ (Nat.card N).factorization r := by
    rw [← Subgroup.card_map_of_injective (f := (SemidirectProduct.inl : N →* N ⋊[φ] Q))
      SemidirectProduct.inl_injective, hmap, hPW.card_eq, hcardW]
  exact ⟨Sylow.ofCard _ hcard, fun n => Iff.rfl⟩

omit [Finite N] [Finite Q] in
private theorem r1n_pgroup_inf_inl (hN : ¬ r ∣ Nat.card N) {P : Subgroup (N ⋊[φ] Q)}
    (hP : IsPGroup r P) : ∀ y ∈ P, y.right = 1 → y = 1 := by
  intro y hy hyr
  obtain ⟨k, hk⟩ := hP ⟨y, hy⟩
  have hyl : SemidirectProduct.inl y.left = y := by
    apply SemidirectProduct.ext
    · rfl
    · rw [SemidirectProduct.right_inl, hyr]
  have hk' : y.left ^ r ^ k = 1 := by
    apply SemidirectProduct.inl_injective (φ := φ)
    rw [map_pow, hyl, map_one]
    exact congrArg Subtype.val hk
  have hcop : Nat.Coprime (r ^ k) (Nat.card N) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hN)
  have h1 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk')
    (orderOf_dvd_natCard _)
  rw [← hyl, orderOf_eq_one_iff.mp h1, map_one]

private theorem r1n_semidirect_sylow_conj (P : Sylow r (N ⋊[φ] Q))
    (hP : ∀ y ∈ (P : Subgroup (N ⋊[φ] Q)), y.right = 1 → y = 1) :
    ∃ (k : N ⋊[φ] Q) (Qr : Sylow r Q),
      (P : Subgroup (N ⋊[φ] Q)) =
        ((Qr : Subgroup Q).map SemidirectProduct.inr).map (MulAut.conj k).toMonoidHom := by
  have := r1n_finite_semidirect (N := N) (Q := Q) (φ := φ)
  obtain ⟨SN, hSN⟩ := r1n_exists_sylow_comap_inl P
  have hSN1 : (SN : Subgroup N) = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    have h := hP _ ((hSN n).mp hn) rfl
    rw [Subgroup.mem_bot]
    exact SemidirectProduct.inl_injective (h.trans (map_one _).symm)
  have hN0 : (Nat.card N).factorization r = 0 := by
    have h := SN.card_eq_multiplicity
    rw [hSN1, Subgroup.card_bot] at h
    exact (Nat.pow_eq_one.mp h.symm).resolve_left (Fact.out : r.Prime).one_lt.ne'
  obtain ⟨Qr⟩ : Nonempty (Sylow r Q) := inferInstance
  have hcardK : Nat.card (N ⋊[φ] Q) = Nat.card N * Nat.card Q := SemidirectProduct.card
  have hcard : Nat.card ((Qr : Subgroup Q).map (SemidirectProduct.inr : Q →* N ⋊[φ] Q)) =
      r ^ (Nat.card (N ⋊[φ] Q)).factorization r := by
    rw [Subgroup.card_map_of_injective SemidirectProduct.inr_injective, Qr.card_eq_multiplicity,
      hcardK, Nat.factorization_mul (Nat.card_pos (α := N)).ne' (Nat.card_pos (α := Q)).ne',
      Finsupp.add_apply, hN0, zero_add]
  let P₀ : Sylow r (N ⋊[φ] Q) := Sylow.ofCard _ hcard
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (N ⋊[φ] Q) P₀ P
  refine ⟨k, Qr, ?_⟩
  rw [← hk, Sylow.coe_subgroup_smul]
  rfl

end Semidirect

section Quotient

variable {G : Type} [Group G]

private theorem r1n_sup_N_eq (t : G) {K : Subgroup G} (hK : K ≤ C t) :
    K ⊔ (N t).map (C t).subtype =
      (((K.subgroupOf (C t)).map (nu t)).comap (nu t)).map (C t).subtype := by
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
    map_subgroupOf_C_subtype t hK]

private theorem r1n_mem_sup_N_iff (t : G) {K : Subgroup G} (hK : K ≤ C t) (c : C t) :
    (c : G) ∈ K ⊔ (N t).map (C t).subtype ↔ nu t c ∈ (K.subgroupOf (C t)).map (nu t) := by
  rw [r1n_sup_N_eq t hK]
  exact Subgroup.mem_map_iff_mem (C t).subtype_injective

private theorem r1n_mem_normalizer_sup_N (t : G) {K : Subgroup G} (hK : K ≤ C t) (c : C t)
    (hc : nu t c ∈ Subgroup.normalizer
      (((K.subgroupOf (C t)).map (nu t) : Subgroup (H t)) : Set (H t))) :
    (c : G) ∈ Subgroup.normalizer ((K ⊔ (N t).map (C t).subtype : Subgroup G) : Set G) := by
  rw [r1n_sup_N_eq t hK]
  exact Subgroup.le_normalizer_map _ ⟨c, Subgroup.le_normalizer_comap _ hc, rfl⟩

private theorem r1n_conj_mem_bar (t : G) {K : Subgroup G} (d : C t)
    (hd : (d : G) ∈ Subgroup.normalizer (K : Set G)) {y : H t}
    (hy : y ∈ (K.subgroupOf (C t)).map (nu t)) :
    nu t d * y * (nu t d)⁻¹ ∈ (K.subgroupOf (C t)).map (nu t) := by
  obtain ⟨c, hc, rfl⟩ := hy
  refine ⟨d * c * d⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  exact (Subgroup.mem_normalizer_iff.mp hd (c : G)).mp hc

private theorem r1n_mem_of_bar (t : G) {K : Subgroup G} (hK : K ≤ C t)
    (hNK : (N t).map (C t).subtype ≤ K) (c : C t)
    (hc : nu t c ∈ (K.subgroupOf (C t)).map (nu t)) : (c : G) ∈ K := by
  have h := (r1n_mem_sup_N_iff t hK c).mpr hc
  rwa [sup_eq_left.mpr hNK] at h

end Quotient

section Sylow

variable {G : Type} [Group G]

private theorem r1n_sd_facts {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (p f : ℕ) :
    orderOf (fS (r n ^ 2 ^ (n - 3)) : G) = 4 ∧
    (fS (r n ^ 2 ^ (n - 3)) : G) ^ 2 = t ∧
    (fS (r n ^ 2 ^ (n - 3)) : G) ∈ (frontierSetting S fS t p f).D ∧
    (fS (s n) : G) ∈ (frontierSetting S fS t p f).D ∧
    orderOf ((fS (s n) : G) * fS (r n ^ 2 ^ (n - 3))) = 2 ∧
    (fS (s n) : G) * fS (r n ^ 2 ^ (n - 3)) ≠ t := by
  obtain ⟨hz, -, -, -, -, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have := sdFourSubgroup_isKleinFour hn
  obtain ⟨-, -, hvN, -⟩ := sd_kleinFour_facts hn (sdFourSubgroup n)
  have hinj := FocalFusion.ambientHom_injective n (S : Subgroup G) fS
  have hamb : ∀ x, FocalFusion.ambientHom n (S : Subgroup G) fS x = (fS x : G) := fun _ => rfl
  have hv4 := orderOf_sdV hn
  set v := r n ^ 2 ^ (n - 3) with hv
  have hv2 : v ^ 2 = r n ^ 2 ^ (n - 2) := by
    rw [hv, ← pow_mul, ← pow_succ, show n - 3 + 1 = n - 2 by omega]
  have hs2 : s n * s n = 1 := by
    have h := pow_orderOf_eq_one (s n)
    rwa [orderOf_s n (by omega), sq] at h
  have hsinv : (s n)⁻¹ = s n := inv_eq_of_mul_eq_one_right hs2
  have hsv : s n * v * s n = v⁻¹ := by
    have h := sd_s_conj_quarter hn
    rwa [hsinv] at h
  have hsv2 : (s n * v) ^ 2 = 1 := by
    rw [sq, show s n * v * (s n * v) = s n * v * s n * v by group, hsv, inv_mul_cancel]
  have hsv1 : s n * v ≠ 1 := by
    intro h
    have hv' : v = (s n)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [hv', orderOf_inv, orderOf_s n (by omega)] at hv4
    omega
  have hsvo : orderOf (s n * v) = 2 := orderOf_eq_prime hsv2 hsv1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hamb, orderOf_injective _ hinj, hv4]
  · rw [← hamb, ← map_pow, hv2, ht, ← hamb, ← map_pow]
  · rw [frontierSetting_D hn S fS t ht p f]
    exact ⟨v, hvN, rfl⟩
  · rw [frontierSetting_D hn S fS t ht p f]
    exact ⟨s n, Subgroup.le_normalizer
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)), rfl⟩
  · rw [← hamb, ← hamb, ← map_mul, orderOf_injective _ hinj, hsvo]
  · intro h
    rw [← hz, ← hamb, ← hamb, ← hamb, ← map_mul] at h
    have h' := hinj h
    have hc := Subgroup.mem_center_iff.mp (z_mem_center n hn) v
    rw [← h'] at hc
    have hcomm : v * s n = s n * v := by
      have h3 : v * s n * v = s n * v * v := by rw [mul_assoc]; exact hc
      exact mul_right_cancel h3
    apply sd_quarter_ne_inv hn
    rw [← sd_s_conj_quarter hn, ← hcomm, mul_inv_cancel_right]

private theorem r1n_C_eq {n : ℕ} (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G) (p f : ℕ) (sC : C t)
    (hsC : (sC : G) = (fS (s n) : G)) :
    (frontierSetting S fS t p f).C =
      (Subgroup.centralizer ({sC} : Set (C t))).map (C t).subtype := by
  ext g
  change g ∈ Subgroup.centralizer (Subgroup.closure ({t, (fS (s n) : G)} : Set G) : Set G) ↔ _
  rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    have hgt : g ∈ C t :=
      Subgroup.mem_centralizer_singleton_iff.mpr (h t (Set.mem_insert _ _)).symm
    refine ⟨⟨g, hgt⟩, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_), rfl⟩
    change g * (sC : G) = (sC : G) * g
    rw [hsC]
    exact (h _ (Set.mem_insert_of_mem _ rfl)).symm
  · rintro ⟨c, hc, rfl⟩ x hx
    rcases hx with rfl | rfl
    · exact (Subgroup.mem_centralizer_singleton_iff.mp c.2).symm
    · rw [← hsC]
      exact (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)).symm

end Sylow

section Model

variable {G : Type} [Group G]

private theorem r1n_model [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (sC : C t) (hsC : (sC : G) = (fS (s n) : G)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (A : Subgroup (F ≃+* F)) (b : Fˣ)
      (hfix : ∀ σ : A, (σ : F ≃+* F) (b : F) = b)
      (Psi : MatrixTorus.OriginalH F b A hfix ≃* H t),
      Nat.card F = p ^ f ∧ Odd (Nat.card A) ∧ ¬IsSquare b ∧ (∀ σ τ : A, σ * τ = τ * σ) ∧
      Psi (MatrixTorus.originalZ F b A hfix) = nu t (tInC t) ∧
      Psi (MatrixTorus.originalU F b A hfix) = nu t sC ∧
      (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) =
        (MatrixTorus.originalSlInH F b A hfix).range.map Psi.toMonoidHom ∧
      (∀ w, Psi (ActualFourGroupCentralizer.originalOddInclusion F A b hfix w) * nu t sC =
        nu t sC * Psi (ActualFourGroupCentralizer.originalOddInclusion F A b hfix w)) ∧
      (∀ h : H t, h * nu t sC = nu t sC * h → Odd (orderOf h) →
        ∃ w, Psi (ActualFourGroupCentralizer.originalOddInclusion F A b hfix w) = h) ∧
      (∀ c : C t, c * sC = sC * c → Odd (orderOf c) →
        (c : G) ∈ oddCoreIn (frontierSetting S fS t p f).C) ∧
      Function.Injective (ActualFourGroupCentralizer.originalWAction F A b hfix) := by
  obtain ⟨-, ht2, -, -, hs2, hst⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hG := CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  have hsC2 : orderOf sC = 2 := by rw [← Subgroup.orderOf_coe, hsC]; exact hs2
  have hsCt : sC ≠ tInC t := fun h => hst (by rw [← hsC, h]; rfl)
  obtain ⟨-, F, hF, hFfin, A, a, hFcard, hAodd, -, -, -, -, -, haF, -, -, -, hall⟩ :=
    ActualFourGroupCentralizer.actual_simple_layer_four_group_centralizer_odd_core n hn S fS hG t
      ht2 hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨Psi, hPsiZ, hPsiU, hdata, -, -, -, -⟩ := hall sC hsC2 hsCt
  set b := MatrixCover.fixedUnit F A a with hbdef
  have hfix : ∀ σ : A, (σ : F ≃+* F) (b : F) = b :=
    ActualFourGroupCentralizer.fixed_coefficient_action F A a
  obtain ⟨-, -, -, hAutcyc, -, -⟩ :=
    SemilinearOuterQuotient.odd_field_projective_semilinear_exact_outer_quotient F hp hpodd hf
      hFcard
  have : IsCyclic (F ≃+* F) := hAutcyc
  have hAcyc : IsCyclic A := Subgroup.isCyclic A
  have hAcomm : ∀ σ τ : A, σ * τ = τ * σ := by
    obtain ⟨g, hg⟩ := hAcyc.exists_generator
    intro σ τ
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg σ)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg τ)
    exact (Commute.zpow_zpow_self g i j).eq
  obtain ⟨e, he⟩ := hdata.quotient_original_direct
  have hK := hdata.lifted.klein_four
  refine ⟨F, hF, hFfin, A, b, hfix, Psi, hFcard, hAodd, haF, hAcomm, hPsiZ, hPsiU, ?_, ?_, ?_,
    ?_, ?_⟩
  ·
    obtain ⟨F', hF', hF'fin, _A', _rho', data'⟩ :=
      actual_simple_layer_matrix_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf
        hmodel
    obtain ⟨eta', -, -, -⟩ := data'.compatible_layer
    set T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) with hT₀def
    have hT₀perf : Group.IsPerfect T₀ := by
      have : Fintype F' := Fintype.ofFinite F'
      have h4 : ∃ u : Finset F', u.card = 4 := by
        obtain ⟨u, -, hu⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F'))
          (n := 4) (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, data'.field_card]; omega)
        exact ⟨u, hu⟩
      have := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
      exact Group.IsPerfect.ofSurjective (f := eta'.symm.toMonoidHom) eta'.symm.surjective
    have hcommH : commutator (H t) =
        (commutator (MatrixTorus.OriginalH F b A hfix)).map Psi.toMonoidHom := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ Psi.surjective]
    have hT₀le : T₀ ≤ (MatrixTorus.originalSlInH F b A hfix).range.map Psi.toMonoidHom :=
      calc T₀ = ⁅T₀, T₀⁆ := (Subgroup.isPerfect_iff.mp hT₀perf).symm
        _ ≤ commutator (H t) := Subgroup.commutator_mono le_top le_top
        _ = (commutator (MatrixTorus.OriginalH F b A hfix)).map Psi.toMonoidHom := hcommH
        _ ≤ (MatrixTorus.originalSlInH F b A hfix).range.map Psi.toMonoidHom :=
          Subgroup.map_mono
            (CentralKernelTorusSplit.commutator_le_originalSlInH_range F b A hfix hAcomm)
    have hcardT₀ : Nat.card ((MatrixTorus.originalSlInH F b A hfix).range.map
        Psi.toMonoidHom) ≤ Nat.card T₀ := by
      rw [Subgroup.card_map_of_injective Psi.injective, Nat.card_congr eta'.toEquiv,
        ← Nat.card_congr (MonoidHom.ofInjective
          (MatrixFourGroupNormalizer.originalSlInH_injective F b A hfix)).toEquiv]
      exact (CentralKernelTorusSplit.card_SL_two_congr
        (hFcard.trans data'.field_card.symm)).le
    exact Subgroup.eq_of_le_of_card_ge hT₀le hcardT₀
  ·
    intro w
    have h1 := (e (1, w)).2
    rw [he, OneMemClass.coe_one, one_mul] at h1
    exact Subgroup.mem_centralizer_singleton_iff.mp h1
  ·
    intro h hh hodd
    have hhC : h ∈ Subgroup.centralizer {nu t sC} := Subgroup.mem_centralizer_singleton_iff.mpr hh
    set y := e.symm ⟨h, hhC⟩ with hydef
    have hord : orderOf y = orderOf h := by
      rw [hydef, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    have hpow : y.1 ^ orderOf h = 1 := by
      have h' := congrArg Prod.fst (pow_orderOf_eq_one y)
      rwa [Prod.pow_fst, hord, Prod.fst_one] at h'
    have hv2 : y.1 ^ 2 = 1 := by
      obtain ⟨u, hu, hyu⟩ := y.1.2
      have hu2 : (⟨u, hu⟩ : KleinFourOddKernel.fourSubgroup (tInC t) sC) ^ 2 = 1 := by
        rw [← hK.exponent_two]
        exact Monoid.pow_exponent_eq_one _
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, ← hyu, ← map_pow]
      have hu2' : u ^ 2 = 1 := congrArg Subtype.val hu2
      rw [hu2', map_one]
      rfl
    have hv1 : y.1 = 1 := by
      have h' := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpow) (orderOf_dvd_of_pow_eq_one hv2)
      rw [Nat.Coprime.gcd_eq_one hodd.coprime_two_right] at h'
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h')
    refine ⟨y.2, ?_⟩
    have h' := he y.1 y.2
    rw [Prod.mk.eta, hydef, MulEquiv.apply_symm_apply, hv1, OneMemClass.coe_one, one_mul] at h'
    exact h'.symm
  ·
    intro c hc hodd
    have hCeq := r1n_C_eq S fS t p f sC hsC
    have hcD : c ∈ KleinFourOddKernel.centralizer sC :=
      Subgroup.mem_centralizer_singleton_iff.mpr hc
    obtain ⟨e', he'⟩ := hdata.lifted.direct_equiv
    set c' : KleinFourOddKernel.centralizer sC := ⟨c, hcD⟩ with hc'def
    set y := e'.symm c' with hydef
    have hord : orderOf y = orderOf c := by
      rw [hydef, MulEquiv.orderOf_eq, hc'def, Subgroup.orderOf_mk]
    have hpow : y.1 ^ orderOf c = 1 := by
      have h := congrArg Prod.fst (pow_orderOf_eq_one y)
      rwa [Prod.pow_fst, hord, Prod.fst_one] at h
    have hv2 : y.1 ^ 2 = 1 := by
      rw [← hK.exponent_two]
      exact Monoid.pow_exponent_eq_one _
    have hv1 : y.1 = 1 := by
      have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpow) (orderOf_dvd_of_pow_eq_one hv2)
      rw [Nat.Coprime.gcd_eq_one hodd.coprime_two_right] at h
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)
    have hcval : c = ((y.2 : KleinFourOddKernel.centralizer sC) : C t) := by
      have h := he' y.1 y.2
      rw [Prod.mk.eta, hydef, MulEquiv.apply_symm_apply, hv1, OneMemClass.coe_one,
        one_mul] at h
      exact h
    set R' := (KleinFourOddKernel.oddKernel sC).map (KleinFourOddKernel.centralizer sC).subtype
      with hR'def
    have hcR : c ∈ R' := ⟨y.2, y.2.2, hcval.symm⟩
    have hRle : R'.map (C t).subtype ≤ oddCoreIn (frontierSetting S fS t p f).C := by
      apply CFSG.ABGTheoremB.le_oddCoreIn
      · rw [hCeq]
        exact Subgroup.map_mono (Subgroup.map_subtype_le _)
      · rw [hCeq]
        have := hdata.lifted.odd_core_normal
        have h1 := CFSG.ABGTheoremB.le_normalizer_map_subtype
          (KleinFourOddKernel.centralizer sC) (KleinFourOddKernel.oddKernel sC)
        exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map _)
      · rw [Subgroup.card_map_of_injective (C t).subtype_injective,
          Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
        exact hdata.lifted.odd_core_odd
    exact hRle ⟨c, hcR, rfl⟩
  ·
    have hodd : Odd (Nat.card F) := hFcard ▸ hpodd.pow
    obtain ⟨-, -, -, -, -, -, -, -, -, hinj, -⟩ :=
      FixedTorusDerived.odd_field_fixed_torus_derived_subgroup_has_exact_torus_centralizer F hp
        hpodd hf hFcard A hAodd b haF hfix
    exact hinj

private theorem r1n_bar_inf_layer [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (X : Subgroup G) (hXp : IsPGroup p X)
    (hXD : (frontierSetting S fS t p f).D ≤ Subgroup.normalizer (X : Set G)) :
    (X.subgroupOf (C t)).map (nu t) ⊓ (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) =
      ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hpodd) even_two
  obtain ⟨-, ht2, -, hsCmem, hs2, hst⟩ :=
    CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hG := CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  obtain ⟨hv4, hvt, hvD, hsD, hsv2, hsvt⟩ := r1n_sd_facts hn S fS t ht p f
  set sC : C t := ⟨(fS (s n) : G), hsCmem⟩ with hsCdef
  have hvC : (fS (r n ^ 2 ^ (n - 3)) : G) ∈ C t := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hvt]
    exact (Commute.self_pow _ 2).eq
  set vC : C t := ⟨_, hvC⟩ with hvCdef
  obtain ⟨F, hF, hFfin, A, b, hfix, Psi, hFcard, hAodd, hb, -, hPsiZ, hPsiU, hlayer, -, -, -,
    -⟩ := r1n_model hGnonab hn S fS t ht hnonab hcentral hnc hp hpodd hf hq hmodel sC rfl
  set Y := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) with hYdef
  have hYn : Y.Normal := by
    have := SemilinearLayerModel.generalizedFitting_normal (Gamma t)
    exact Subgroup.Normal.comap inferInstance _
  set Xbar := (X.subgroupOf (C t)).map (nu t) with hXbardef
  have hXbarp : IsPGroup p Xbar := (hXp.comap_subtype (K := C t)).map (nu t)
  have hodd : Odd (Nat.card F) := hFcard ▸ hpodd.pow
  have hzc : ∀ y : H t, nu t (tInC t) * y = y * nu t (tInC t) := by
    intro y
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (N t) y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (tInC_central t) c]
  obtain ⟨F', hF', hF'fin, A', rho', data'⟩ :=
    actual_simple_layer_matrix_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf
      hmodel
  have hvC4 : orderOf vC = 4 := by rw [← Subgroup.orderOf_coe]; exact hv4
  have hvY : nu t vC ∈ Y :=
    actual_order_four_image_mem_layer n hn S fS hG t ht2 F' A' p f rho' data' vC hvC4
  have hvC2 : vC ^ 2 = tInC t := Subtype.ext hvt
  rw [hlayer] at hvY
  obtain ⟨_, ⟨Dv, rfl⟩, hDv⟩ := hvY
  have hDv' : Psi (MatrixTorus.originalSlInH F b A hfix Dv) = nu t vC := hDv
  have hDv2 : Dv * Dv = -1 := by
    apply MatrixFourGroupNormalizer.originalSlInH_injective F b A hfix
    apply Psi.injective
    rw [map_mul, map_mul, hDv', ← map_mul, ← sq, hvC2, ← hPsiZ]
    rfl
  have hslpow : ∀ (X : MatrixCoverData.SL F) (k : ℕ),
      Psi (MatrixTorus.originalSlInH F b A hfix X) ^ k = 1 → X ^ k = 1 := by
    intro X k hX
    apply MatrixFourGroupNormalizer.originalSlInH_injective F b A hfix
    apply Psi.injective
    rw [map_pow, map_pow, hX, map_one, map_one]
  have hA' : ∀ y ∈ Y, ∀ k : ℕ, y ^ p ^ k = 1 → y * nu t sC = nu t sC * y → y = 1 := by
    intro y hy k hyk hys
    rw [hlayer] at hy
    obtain ⟨_, ⟨X, rfl⟩, rfl⟩ := hy
    rw [MulEquiv.coe_toMonoidHom] at hyk hys ⊢
    have hXT : X ∈ MatrixTorus.Torus F b := by
      rw [← CentralKernelTorusSplit.originalSlInH_commute_originalU_iff F b A hfix X]
      apply Psi.injective
      rw [map_mul, map_mul, hPsiU]
      exact hys
    have hXk := hslpow X _ hyk
    have hcard := MatrixTorus.torus_card F b hodd hb
    have hdvd1 : orderOf (⟨X, hXT⟩ : MatrixTorus.Torus F b) ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext hXk)
    have hdvd2 : orderOf (⟨X, hXT⟩ : MatrixTorus.Torus F b) ∣
        MatrixTorus.torusSize (p ^ f) := by
      rw [← hFcard, ← hcard]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (p ^ k) (MatrixTorus.torusSize (p ^ f)) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr
        (ActualFourGroupCentralizer.prime_not_dvd_torusSize p f hp hf))
    have h1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2)
    have hX1 : X = 1 := congrArg Subtype.val h1
    rw [hX1, map_one, map_one]
  have : Fintype F := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hFcard)
  have hB' : ∀ y ∈ Y, ∀ k : ℕ, y ^ p ^ k = 1 → y * nu t vC = nu t vC * y → y = 1 := by
    intro y hy k hyk hyv
    rw [hlayer] at hy
    obtain ⟨_, ⟨X, rfl⟩, rfl⟩ := hy
    rw [MulEquiv.coe_toMonoidHom] at hyk hyv ⊢
    have hXk := hslpow X _ hyk
    have hXD : X * Dv = Dv * X := by
      apply MatrixFourGroupNormalizer.originalSlInH_injective F b A hfix
      apply Psi.injective
      rw [map_mul, map_mul, map_mul, map_mul, hDv']
      exact hyv
    rw [sl2_pElement_eq_one_of_commute_sq_neg_one hp2 hXk hDv2 hXD, map_one, map_one]
  set U := Xbar ⊓ Y with hUdef
  have hUp : ∀ y ∈ U, ∃ k : ℕ, y ^ p ^ k = 1 := by
    intro y hy
    obtain ⟨k, hk⟩ := hXbarp ⟨y, (Subgroup.mem_inf.mp hy).1⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hconjU : ∀ d : C t, (d : G) ∈ (frontierSetting S fS t p f).D →
      ∀ y ∈ U, nu t d * y * (nu t d)⁻¹ ∈ U := by
    intro d hd y hy
    exact Subgroup.mem_inf.mpr ⟨r1n_conj_mem_bar t d (hXD hd) (Subgroup.mem_inf.mp hy).1,
      hYn.conj_mem y (Subgroup.mem_inf.mp hy).2 _⟩
  have hsC2 : orderOf sC = 2 := by rw [← Subgroup.orderOf_coe]; exact hs2
  have hs1 : nu t sC * nu t sC = 1 := by
    have h := pow_orderOf_eq_one sC
    rw [hsC2, sq] at h
    rw [← map_mul, h, map_one]
  have hv1 : nu t vC * nu t vC = nu t (tInC t) := by
    rw [← map_mul, ← sq, hvC2]
  have hs_inv : ∀ y ∈ U, nu t sC * y * (nu t sC)⁻¹ = y⁻¹ :=
    conj_eq_inv_of_fixedPointFree (nu t sC) (hconjU sC hsD)
      (fun y _ => by
        calc nu t sC * (nu t sC * y * (nu t sC)⁻¹) * (nu t sC)⁻¹
            = (nu t sC * nu t sC) * y * (nu t sC * nu t sC)⁻¹ := by group
          _ = y := by rw [hs1]; group)
      (fun y hy hfx => by
        obtain ⟨k, hk⟩ := hUp y hy
        exact hA' y (Subgroup.mem_inf.mp hy).2 k hk (mul_inv_eq_iff_eq_mul.mp hfx).symm)
  have hv_inv : ∀ y ∈ U, nu t vC * y * (nu t vC)⁻¹ = y⁻¹ :=
    conj_eq_inv_of_fixedPointFree (nu t vC) (hconjU vC hvD)
      (fun y _ => by
        calc nu t vC * (nu t vC * y * (nu t vC)⁻¹) * (nu t vC)⁻¹
            = (nu t vC * nu t vC) * y * (nu t vC * nu t vC)⁻¹ := by group
          _ = nu t (tInC t) * y * (nu t (tInC t))⁻¹ := by rw [hv1]
          _ = y := by rw [hzc y, mul_inv_cancel_right])
      (fun y hy hfx => by
        obtain ⟨k, hk⟩ := hUp y hy
        exact hB' y (Subgroup.mem_inf.mp hy).2 k hk (mul_inv_eq_iff_eq_mul.mp hfx).symm)
  have hsv_comm : ∀ y ∈ U, nu t (sC * vC) * y = y * nu t (sC * vC) := by
    intro y hy
    rw [map_mul]
    calc nu t sC * nu t vC * y = nu t sC * (nu t vC * y * (nu t vC)⁻¹) * nu t vC := by group
      _ = nu t sC * y⁻¹ * nu t vC := by rw [hv_inv y hy]
      _ = (nu t sC * y * (nu t sC)⁻¹)⁻¹ * nu t sC * nu t vC := by group
      _ = y * (nu t sC * nu t vC) := by rw [hs_inv y hy, inv_inv, mul_assoc]
  have hsvC2 : orderOf (sC * vC) = 2 := by rw [← Subgroup.orderOf_coe]; exact hsv2
  have hsCt : sC ≠ ActualFourGroupAlignment.actualInvolution t :=
    fun h => hst (congrArg Subtype.val h)
  have hsvCt : sC * vC ≠ ActualFourGroupAlignment.actualInvolution t :=
    fun h => hsvt (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := ActualFourGroupAlignment.exists_actual_noncentral_involution_conjugator n hn
    S fS hG t ht2 (sC * vC) sC hsvC2 hsC2 hsvCt hsCt
  have hc' : nu t c * nu t (sC * vC) * (nu t c)⁻¹ = nu t sC := by
    rw [← map_mul, ← map_inv, ← map_mul, hc]
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := hUp y hy
  have hy' : nu t c * y * (nu t c)⁻¹ = 1 := by
    apply hA' _ (hYn.conj_mem y (Subgroup.mem_inf.mp hy).2 _) k
    · rw [conj_pow, hk, mul_one, mul_inv_cancel]
    · rw [← hc']
      calc nu t c * y * (nu t c)⁻¹ * (nu t c * nu t (sC * vC) * (nu t c)⁻¹)
          = nu t c * (y * nu t (sC * vC)) * (nu t c)⁻¹ := by group
        _ = nu t c * (nu t (sC * vC) * y) * (nu t c)⁻¹ := by rw [← hsv_comm y hy]
        _ = nu t c * nu t (sC * vC) * (nu t c)⁻¹ * (nu t c * y * (nu t c)⁻¹) := by group
  calc y = (nu t c)⁻¹ * (nu t c * y * (nu t c)⁻¹) * nu t c := by group
    _ = 1 := by rw [hy', mul_one, inv_mul_cancel]

end Model

section FieldAction

private theorem r1n_inr_conj_originalSlInH (F : Type) [Field F] (A : Subgroup (F ≃+* F))
    (b : Fˣ) (hfix : ∀ σ : A, (σ : F ≃+* F) (b : F) = b) (q : A) (X : MatrixCoverData.SL F) :
    (SemidirectProduct.inr q : MatrixTorus.OriginalH F b A hfix) *
        MatrixTorus.originalSlInH F b A hfix X * (SemidirectProduct.inr q)⁻¹ =
      MatrixTorus.originalSlInH F b A hfix
        (Matrix.SpecialLinearGroup.map (q : F ≃+* F).toRingHom X) := by
  change (SemidirectProduct.inr q : MatrixTorus.OriginalH F b A hfix) *
      SemidirectProduct.inl (MatrixCoverData.inclusion F b X) * (SemidirectProduct.inr q)⁻¹ =
    SemidirectProduct.inl (MatrixCoverData.inclusion F b
      (Matrix.SpecialLinearGroup.map (q : F ≃+* F).toRingHom X))
  rw [← map_inv, ← SemidirectProduct.inl_aut]
  rfl

private theorem r1n_originalSlInH_commute_inr_iff (F : Type) [Field F] (A : Subgroup (F ≃+* F))
    (b : Fˣ) (hfix : ∀ σ : A, (σ : F ≃+* F) (b : F) = b) (q : A) (X : MatrixCoverData.SL F) :
    MatrixTorus.originalSlInH F b A hfix X * SemidirectProduct.inr q =
        SemidirectProduct.inr q * MatrixTorus.originalSlInH F b A hfix X ↔
      Matrix.SpecialLinearGroup.map (q : F ≃+* F).toRingHom X = X := by
  rw [← (MatrixFourGroupNormalizer.originalSlInH_injective F b A hfix).eq_iff,
    ← r1n_inr_conj_originalSlInH, mul_inv_eq_iff_eq_mul, eq_comm]

end FieldAction

section Dickson

open CFSG.BenderSuzuki.MatrixGroups

private theorem sl2_W_sup_fixedEntry_eq_top
    {F : Type} [Field F] [Finite F] {p f : ℕ}
    [Fact p.Prime] (hpodd : Odd p) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) (hq : 5 < p ^ f)
    (b : Fˣ) (hb : ¬IsSquare b) (A₀ : Subgroup (F ≃+* F)) (hA₀ : Odd (Nat.card A₀))
    (hA₀1 : 1 < Nat.card A₀) :
    (MatrixTorus.W F b).map (MatrixTorus.Torus F b).subtype ⊔
      OddFieldLift.fixedEntrySL2 F A₀ = ⊤ := by
  have hp : p.Prime := Fact.out
  have hodd : Odd (Nat.card F) := hF ▸ hpodd.pow
  have hneg1 : (-1 : F) ≠ 1 := SL2Sections.neg_one_ne_one_of_odd_card hodd
  set Z := Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) with hZ
  set π : Matrix.SpecialLinearGroup (Fin 2) F →* PSL2MatrixGroup F := QuotientGroup.mk' Z
    with hπ
  set Fix := OddFieldLift.fixedEntrySL2 F A₀ with hFix
  set K₀ := (MatrixTorus.W F b).map (MatrixTorus.Torus F b).subtype ⊔ Fix with hK₀
  have hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) F) ∈ Fix := by
    rw [hFix, OddFieldLift.mem_fixedEntrySL2]
    intro a
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  obtain ⟨-, -, hq03, hq0odd, -, hF0card, hpow, -⟩ :=
    FixedFieldData.odd_fixed_field_data p f hp hpodd hf F hF A₀ hA₀
  have hA₀3 : 3 ≤ Nat.card A₀ := by
    have := Nat.odd_iff.mp hA₀
    omega
  have hq27 : 27 ≤ p ^ f := by
    rw [← hF, hpow]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ (p ^ (f / Nat.card A₀)) ^ 3 := Nat.pow_le_pow_left hq03 3
      _ ≤ (p ^ (f / Nat.card A₀)) ^ Nat.card A₀ := Nat.pow_le_pow_right (by omega) hA₀3
  set w := MatrixTorus.torusSize (p ^ f) / 2 with hw
  have hwq : (p ^ f % 4 = 1 ∧ 2 * w = p ^ f + 1) ∨ (p ^ f % 4 = 3 ∧ 2 * w = p ^ f - 1) := by
    have hT := MatrixTorus.torusSize_mod_four (hpodd.pow (n := f))
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp (hpodd.pow (n := f))) with h | h
    · have ht : MatrixTorus.torusSize (p ^ f) = p ^ f + 1 := by
        rw [MatrixTorus.torusSize, ite_eq_left h]
      left
      omega
    · have ht : MatrixTorus.torusSize (p ^ f) = p ^ f - 1 := by
        rw [MatrixTorus.torusSize, ite_eq_right (by omega)]
      right
      omega
  have hw13 : 13 ≤ w := by
    rcases hwq with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hwodd : Odd w := MatrixTorus.torusSize_half_odd (hpodd.pow (n := f))
  have h4fix : 4 ∣ Nat.card (Fix.map π) := by
    set ψ := π.comp (OddFieldLift.fixedSL2Inclusion F A₀) with hψ
    have hrange : ψ.range = Fix.map π := by
      rw [hψ, MonoidHom.range_comp]
      rfl
    have hcard := SL2Sections.card_ker_mul_card_range ψ
    rw [hrange, CFSG.BenderSuzuki.External.huppert614_card_specialLinearGroup, hF0card]
      at hcard
    have hker : Nat.card ψ.ker ∣ 2 := by
      have hle : ψ.ker.map (OddFieldLift.fixedSL2Inclusion F A₀) ≤ Z := by
        rintro _ ⟨x, hx, rfl⟩
        exact (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hx)
      have h := Subgroup.card_dvd_of_le hle
      rwa [Subgroup.card_map_of_injective (OddFieldLift.fixedSL2Inclusion_injective F A₀),
        CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_ne_one hneg1] at h
    obtain ⟨k, hk⟩ := Nat.eight_dvd_sq_sub_one_of_odd hq0odd
    rw [hk] at hcard
    rcases (Nat.dvd_prime Nat.prime_two).mp hker with h1 | h2
    · rw [h1, one_mul] at hcard
      rw [hcard]
      exact ⟨p ^ (f / Nat.card A₀) * (2 * k), by ring⟩
    · rw [h2, show p ^ (f / Nat.card A₀) * (8 * k) = 2 * (4 * (p ^ (f / Nat.card A₀) * k))
        by ring] at hcard
      exact ⟨_, Nat.eq_of_mul_eq_mul_left (by norm_num) hcard⟩
  have hWcyc := MatrixTorus.W_cyclic F b hodd hb
  have hWcard := MatrixTorus.W_card F b hodd hb
  obtain ⟨g, hg⟩ := hWcyc.exists_generator
  have hgo : orderOf g = w := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hWcard, hF]
  set G0 : Matrix.SpecialLinearGroup (Fin 2) F :=
    ((g : MatrixTorus.Torus F b) : Matrix.SpecialLinearGroup (Fin 2) F) with hG0
  have hG0o : orderOf G0 = w := by
    rw [hG0, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hgo]
  have hπG0 : orderOf (π G0) = w := by
    apply Nat.dvd_antisymm
    · rw [← hG0o]
      exact orderOf_map_dvd π G0
    · rw [← hG0o]
      apply orderOf_dvd_of_pow_eq_one
      have h1 : π (G0 ^ orderOf (π G0)) = 1 := by rw [map_pow, pow_orderOf_eq_one]
      have h2 : G0 ^ orderOf (π G0) ∈ Z := (QuotientGroup.eq_one_iff _).mp h1
      rcases (SL2Sections.mem_center_sl2_iff hodd _).mp h2 with h | h
      · exact h
      · exfalso
        have hw' : (G0 ^ orderOf (π G0)) ^ w = 1 := by
          rw [← pow_mul, mul_comm, pow_mul, ← hG0o, pow_orderOf_eq_one, one_pow]
        rw [h, hwodd.neg_one_pow] at hw'
        apply hneg1
        have h3 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F =>
          (M : Matrix (Fin 2) (Fin 2) F) 0 0) hw'
        simpa using h3
  have hX : K₀.map π = ⊤ := by
    have h4 : 4 ∣ Nat.card (K₀.map π) :=
      h4fix.trans (Subgroup.card_dvd_of_le (Subgroup.map_mono le_sup_right))
    have hG0K : G0 ∈ K₀ := Subgroup.mem_sup_left ⟨g, g.2, rfl⟩
    rcases SL2Sections.psl2_subgroup_eq_top_or_small hpodd hF hq hwq (K₀.map π) h4
        ⟨π G0, Subgroup.mem_map_of_mem π hG0K⟩ (by rw [Subgroup.orderOf_mk]; exact hπG0) with
      h | ⟨h3, -⟩ | ⟨h5, -⟩
    · exact h
    · omega
    · omega
  rw [eq_top_iff]
  intro x _
  have hx : π x ∈ K₀.map π := by
    rw [hX]
    exact Subgroup.mem_top _
  obtain ⟨k, hk, hkx⟩ := hx
  have hz : k⁻¹ * x ∈ Z := by
    have h1 : π (k⁻¹ * x) = 1 := by rw [map_mul, map_inv, hkx, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hzK : k⁻¹ * x ∈ K₀ := by
    rcases (SL2Sections.mem_center_sl2_iff hodd _).mp hz with h | h
    · rw [h]
      exact K₀.one_mem
    · rw [h]
      exact Subgroup.mem_sup_right hneg
  have h := K₀.mul_mem hk hzK
  rwa [mul_inv_cancel_left] at h

end Dickson

theorem frontier_R1NFacts
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ J : Subgroup G, (frontierSetting S fS t p f).IsV21Layer J →
      (frontierSetting S fS t p f).R1NFacts J := by
  intro J hJ
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, ht2, -, hsCmem, hs2, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hG := CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  obtain ⟨-, -, -, hsD, -, -⟩ := r1n_sd_facts hn S fS t ht p f
  set sC : C t := ⟨(fS (s n) : G), hsCmem⟩ with hsCdef
  have hsC2 : orderOf sC = 2 := by rw [← Subgroup.orderOf_coe]; exact hs2
  have hsC1 : sC * sC = 1 := by
    have h := pow_orderOf_eq_one sC
    rwa [hsC2, sq] at h
  obtain ⟨F, hF, hFfin, A, b, hfix, Psi, hFcard, hAodd, hb, hAcomm, -, hPsiU, hlayer, hBcent,
    hBodd, hOC, hfaith⟩ :=
    r1n_model hGnonab hn S fS t ht hnonab hcentral hnc hp hpodd hf hq hmodel sC rfl
  set Y := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) with hYdef
  have hYn : Y.Normal := by
    have := SemilinearLayerModel.generalizedFitting_normal (Gamma t)
    exact Subgroup.Normal.comap inferInstance _
  set ι := Psi.toMonoidHom.comp (ActualFourGroupCentralizer.originalOddInclusion F A b hfix)
    with hιdef
  have hι : Function.Injective ι :=
    Psi.injective.comp (ActualFourGroupCentralizer.originalOddInclusion_injective F A b hfix)
  have hlay : ∀ x, ι x ∈ Y ↔ x.right = 1 := by
    intro x
    rw [hlayer]
    exact (Subgroup.mem_map_iff_mem (f := Psi.toMonoidHom) Psi.injective).trans
      (CentralKernelTorusSplit.originalOddInclusion_mem_range_iff F b A hfix x)
  have hodd : Odd (Nat.card F) := hFcard ▸ hpodd.pow
  have hWPodd : Odd (Nat.card (ActualFourGroupCentralizer.OriginalWProduct F A b hfix)) := by
    rw [SemidirectProduct.card, MatrixTorus.W_card F b hodd hb]
    exact (MatrixTorus.torusSize_half_odd hodd).mul hAodd
  have hιodd : ∀ x, Odd (orderOf (ι x)) := fun x => by
    rw [orderOf_injective ι hι]
    exact hWPodd.of_dvd_nat (orderOf_dvd_natCard x)
  have hNodd : Odd (Nat.card (N t)) := Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hON : (frontierSetting S fS t p f).ON = (N t).map (C t).subtype :=
    frontierSetting_ON S fS t p f
  obtain ⟨F', hF', hF'fin, A', rho', data'⟩ :=
    actual_simple_layer_matrix_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf
      hmodel
  obtain ⟨-, -, hcommC⟩ :=
    LocalLayerAbelianQuotients.actual_matrix_layer_preimage_has_abelian_quotient t n p f hp
      hpodd hf F' A' rho' data'
  rw [commutator_def] at hcommC
  have hF2 : ∀ X : Subgroup G, X ≤ C t → IsPGroup p X →
      (frontierSetting S fS t p f).D ≤ Subgroup.normalizer (X : Set G) →
      ∀ y ∈ (X.subgroupOf (C t)).map (nu t), y ∈ ι.range := by
    intro X hXC hXp hXD y hy
    have hinf := r1n_bar_inf_layer hGnonab hn S fS t ht hnonab hcentral hnc hp hpodd hf hq
      hmodel X hXp hXD
    obtain ⟨x, hx, rfl⟩ := hy
    have hcX : x * sC * x⁻¹ * sC⁻¹ ∈ X.subgroupOf (C t) := by
      have hx' : (x : G) ∈ X := hx
      have h1 : (sC : G) * (x : G)⁻¹ * (sC : G)⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hXD hsD) _).mp (X.inv_mem hx')
      have h2 := X.mul_mem hx' h1
      rw [Subgroup.mem_subgroupOf]
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using h2
    have hcL : nu t (x * sC * x⁻¹ * sC⁻¹) ∈ Y := by
      have h := hcommC (Subgroup.commutator_mem_commutator (Subgroup.mem_top x)
        (Subgroup.mem_top sC))
      rw [commutatorElement_def] at h
      exact h
    have h1 : nu t (x * sC * x⁻¹ * sC⁻¹) = 1 := by
      have hmem : nu t (x * sC * x⁻¹ * sC⁻¹) ∈ (X.subgroupOf (C t)).map (nu t) ⊓ Y :=
        Subgroup.mem_inf.mpr ⟨⟨_, hcX, rfl⟩, hcL⟩
      rw [hinf] at hmem
      exact hmem
    have hcomm : nu t x * nu t sC = nu t sC * nu t x := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
    have hxodd : Odd (orderOf (nu t x)) := by
      have hXbarp : IsPGroup p ((X.subgroupOf (C t)).map (nu t)) :=
        (hXp.comap_subtype (K := C t)).map (nu t)
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hXbarp ⟨nu t x, ⟨x, hx, rfl⟩⟩
      have hk' : orderOf (nu t x) = p ^ k := (Subgroup.orderOf_coe _).trans hk
      rw [hk']
      exact hpodd.pow
    exact hBodd (nu t x) hcomm hxodd
  have hJL₀ : J ≤ (localLayerPreimage t).map (C t).subtype := hJ.le
  have hJC : J ≤ C t := hJL₀.trans (Subgroup.map_subtype_le _)
  have hpON : pCoreIn (frontierSetting S fS t p f).p (frontierSetting S fS t p f).N ≤
      (N t).map (C t).subtype := by
    rw [← hON, ← hJ.inf_eq]
    exact inf_le_right
  have hF3 : ∀ W ∈ (frontierSetting S fS t p f).familyW J,
      (W.subgroupOf (C t)).map (nu t) = Y ⊓ ι.range := by
    intro W hW
    obtain ⟨hWJ, -, -, hWeq⟩ := hW
    have hWC : W ≤ C t := hWJ.trans hJC
    apply le_antisymm
    ·
      have hle : oddCoreIn (frontierSetting S fS t p f).C ⊓ J ⊔
          pCoreIn (frontierSetting S fS t p f).p (frontierSetting S fS t p f).N ≤
          (ι.range.comap (nu t)).map (C t).subtype := by
        apply sup_le
        · intro g hg
          have hgO := (Subgroup.mem_inf.mp hg).1
          have hgC := CFSG.ABGTheoremB.oddCoreIn_le _ hgO
          rw [r1n_C_eq S fS t p f sC rfl] at hgC
          obtain ⟨d, hd, rfl⟩ := hgC
          refine ⟨d, ?_, rfl⟩
          have hdodd : Odd (orderOf d) := by
            have h1 : orderOf (d : G) ∣ _ := Subgroup.orderOf_dvd_natCard _ hgO
            rw [Subgroup.orderOf_coe] at h1
            exact (CFSG.ABGTheoremB.odd_card_oddCoreIn _).of_dvd_nat h1
          have hdc : d * sC = sC * d := Subgroup.mem_centralizer_singleton_iff.mp hd
          exact hBodd (nu t d) (by rw [← map_mul, ← map_mul, hdc])
            (hdodd.of_dvd_nat (orderOf_map_dvd _ _))
        · intro g hg
          obtain ⟨c, hc, rfl⟩ := hpON hg
          refine ⟨c, ?_, rfl⟩
          have h1 : nu t c = 1 := (QuotientGroup.eq_one_iff c).mpr hc
          change nu t c ∈ ι.range
          rw [h1]
          exact ι.range.one_mem
      rintro _ ⟨w, hw, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (Subgroup.mem_map_iff_mem (C t).subtype_injective).mp (hJL₀ (hWJ hw))
      · have hwK : (w : G) ∈ oddCoreIn (frontierSetting S fS t p f).C ⊓ J ⊔
            pCoreIn (frontierSetting S fS t p f).p (frontierSetting S fS t p f).N := by
          rw [← hWeq]
          exact Subgroup.mem_sup_left hw
        exact (Subgroup.mem_map_iff_mem (C t).subtype_injective).mp (hle hwK)
    ·
      intro y hy
      obtain ⟨hyY, hyB⟩ := Subgroup.mem_inf.mp hy
      obtain ⟨wy, hwy⟩ := hyB
      set J' := J.subgroupOf (C t) with hJ'def
      have hJ'n : J'.Normal := by
        constructor
        intro j hj c
        exact (Subgroup.mem_normalizer_iff.mp (hJ.normal c.2) _).mp hj
      have hJ'Y : ∀ j : J', nu t (j : C t) ∈ Y := fun j =>
        (Subgroup.mem_map_iff_mem (C t).subtype_injective).mp (hJL₀ j.2)
      have hJ'sup : J' ⊔ N t = localLayerPreimage t := by
        apply Subgroup.map_injective (C t).subtype_injective
        rw [Subgroup.map_sup, map_subgroupOf_C_subtype t hJC, ← hON, ← hJ.sup_eq]
        rfl
      have hJ'map : J'.map (nu t) = Y := by
        have h := congrArg (Subgroup.map (nu t)) hJ'sup
        rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] at h
        rw [h]
        exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
      have hyJ : y ∈ J'.map (nu t) := by rw [hJ'map]; exact hyY
      obtain ⟨j₀, hj₀, hj₀y⟩ := hyJ
      have hEodd : Odd (Nat.card (J' ⊓ N t : Subgroup (C t))) :=
        hNodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
      have hys' : nu t sC * y = y * nu t sC := by rw [← hwy]; exact (hBcent wy).symm
      have hys : nu t sC * y * (nu t sC)⁻¹ * y⁻¹ = 1 := by
        rw [mul_inv_eq_of_eq_mul hys', mul_inv_cancel]
      have hjs₀ : sC * j₀ * sC⁻¹ * j₀⁻¹ ∈ J' ⊓ N t := by
        refine Subgroup.mem_inf.mpr ⟨J'.mul_mem (hJ'n.conj_mem j₀ hj₀ sC) (J'.inv_mem hj₀), ?_⟩
        apply (QuotientGroup.eq_one_iff _).mp
        change nu t (sC * j₀ * sC⁻¹ * j₀⁻¹) = 1
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hj₀y]
        exact hys
      obtain ⟨j, hjJ, hjs, hjj₀⟩ :=
        CentralKernelTorusSplit.exists_fixed_lift inf_le_left hEodd hsC2 hj₀ hjs₀
      have hjy : nu t j = y := by
        have h1 : nu t (j⁻¹ * j₀) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_inf.mp hjj₀).2
        rw [map_mul, map_inv, hj₀y, inv_mul_eq_one] at h1
        exact h1
      have hjodd : Odd (orderOf j) := by
        have hyodd : Odd (orderOf y) := by rw [← hwy]; exact hιodd wy
        have hjm : j ^ orderOf y ∈ N t := by
          apply (QuotientGroup.eq_one_iff _).mp
          change nu t (j ^ orderOf y) = 1
          rw [map_pow, hjy, pow_orderOf_eq_one]
        have h1 : j ^ (orderOf y * Nat.card (N t)) = 1 := by
          rw [pow_mul]
          have h2 : (⟨_, hjm⟩ : N t) ^ Nat.card (N t) = 1 := pow_card_eq_one'
          exact congrArg Subtype.val h2
        exact (hyodd.mul hNodd).of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
      have hjW : (j : G) ∈ W ⊔ (N t).map (C t).subtype := by
        have h : (j : G) ∈ oddCoreIn (frontierSetting S fS t p f).C ⊓ J ⊔
            pCoreIn (frontierSetting S fS t p f).p (frontierSetting S fS t p f).N :=
          Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hOC j hjs hjodd, hjJ⟩)
        rw [← hWeq] at h
        exact sup_le_sup_left hpON W h
      rw [← hjy]
      exact (r1n_mem_sup_N_iff t hWC j).mp hjW
  refine ⟨?_, ?_, ?_⟩
  ·
    intro W hW X hXN hXp hXD x hx
    have hXp' : IsPGroup p X := hXp
    have hWJ : W ≤ J := by
      obtain ⟨h, -⟩ := hW
      exact h
    have hWC : W ≤ C t := hWJ.trans hJC
    have hxC : x ∈ C t := hXN hx
    set xb := nu t ⟨x, hxC⟩ with hxb
    have hxB : xb ∈ ι.range := hF2 X hXN hXp' hXD xb ⟨⟨x, hxC⟩, hx, rfl⟩
    rw [hON]
    apply r1n_mem_normalizer_sup_N t hWC ⟨x, hxC⟩
    rw [hF3 W hW, Subgroup.mem_normalizer_iff]
    intro h
    have hconj : xb⁻¹ * (xb * h * xb⁻¹) * xb = h := by group
    constructor
    · intro hh
      obtain ⟨hhY, hhB⟩ := Subgroup.mem_inf.mp hh
      exact Subgroup.mem_inf.mpr ⟨hYn.conj_mem h hhY _,
        ι.range.mul_mem (ι.range.mul_mem hxB hhB) (ι.range.inv_mem hxB)⟩
    · intro hh
      obtain ⟨hhY, hhB⟩ := Subgroup.mem_inf.mp hh
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h1 := hYn.conj_mem _ hhY xb⁻¹
        rwa [inv_inv, hconj] at h1
      · have h1 := ι.range.mul_mem (ι.range.mul_mem (ι.range.inv_mem hxB) hhB) hxB
        rwa [hconj] at h1
  ·
    intro W hW X hXN hXp hXD y hy hyW
    have hXp' : IsPGroup p X := hXp
    have hyC : y ∈ C t := hXN hy
    set yb := nu t ⟨y, hyC⟩ with hyb
    have hinf := r1n_bar_inf_layer hGnonab hn S fS t ht hnonab hcentral hnc hp hpodd hf hq
      hmodel X hXp' hXD
    obtain ⟨x, hx⟩ := hF2 X hXN hXp' hXD yb ⟨⟨y, hyC⟩, hy, rfl⟩
    have hcommW : ∀ w0 : MatrixTorus.W F b,
        x * SemidirectProduct.inl w0 = SemidirectProduct.inl w0 * x := by
      intro w0
      apply hι
      have hw0 : ι (SemidirectProduct.inl w0) ∈ (W.subgroupOf (C t)).map (nu t) := by
        rw [hF3 W hW]
        exact Subgroup.mem_inf.mpr ⟨(hlay _).mpr rfl, ⟨_, rfl⟩⟩
      obtain ⟨w, hw, hwe⟩ := hw0
      have h1 := hyW (w : G) hw
      rw [hON] at h1
      have h2 : ⟨y, hyC⟩ * w * ⟨y, hyC⟩⁻¹ * w⁻¹ ∈ N t :=
        (Subgroup.mem_map_iff_mem (x := ⟨y, hyC⟩ * w * ⟨y, hyC⟩⁻¹ * w⁻¹)
          (C t).subtype_injective).mp h1
      have h3 : nu t (⟨y, hyC⟩ * w * ⟨y, hyC⟩⁻¹ * w⁻¹) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr h2
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
      have h4 : yb * nu t w = nu t w * yb := mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h3)
      rw [map_mul, map_mul, hx, ← hwe]
      exact h4
    have hfixW : ∀ w0, ActualFourGroupCentralizer.originalWAction F A b hfix x.right w0 = w0 := by
      intro w0
      have hl := congrArg SemidirectProduct.left (hcommW w0)
      simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
        SemidirectProduct.right_inl, map_one, MulAut.one_apply] at hl
      rw [FixedTorusDerived.W_mul_comm F b w0 x.left] at hl
      exact mul_left_cancel hl
    have hxr : x.right = 1 := by
      apply hfaith
      rw [map_one]
      apply MulEquiv.ext
      intro w0
      rw [MulAut.one_apply]
      exact hfixW w0
    have hybY : yb ∈ Y := by
      rw [← hx]
      exact (hlay x).mpr hxr
    have hyb1 : yb = 1 := by
      have hmem : yb ∈ (X.subgroupOf (C t)).map (nu t) ⊓ Y :=
        Subgroup.mem_inf.mpr ⟨⟨⟨y, hyC⟩, hy, rfl⟩, hybY⟩
      rw [hinf] at hmem
      exact hmem
    rw [hON]
    exact ⟨⟨y, hyC⟩, (QuotientGroup.eq_one_iff _).mp hyb1, rfl⟩
  ·
    intro W hW X hXN hXp hXD M hLM hMN
    have hXp' : IsPGroup p X := hXp
    have hWJ : W ≤ J := by
      obtain ⟨h, -⟩ := hW
      exact h
    have hWC : W ≤ C t := hWJ.trans hJC
    have hXC : X ≤ C t := hXN
    have hMC : M ≤ C t := hMN
    have hDC : (frontierSetting S fS t p f).D ≤ C t :=
      inf_le_left.trans (frontier_S_le_C hn S fS t ht p f)
    have hONC : (frontierSetting S fS t p f).ON ≤ C t := by
      rw [hON]
      exact Subgroup.map_subtype_le _
    set K := W ⊔ (frontierSetting S fS t p f).D ⊔ (M ⊓ Subgroup.normalizer
      (((frontierSetting S fS t p f).ON ⊔ X : Subgroup G) : Set G)) ⊔
      (frontierSetting S fS t p f).ON with hKdef
    have hKC : K ≤ C t := sup_le (sup_le (sup_le hWC hDC) (inf_le_left.trans hMC)) hONC
    have hONK : (N t).map (C t).subtype ≤ K := by
      rw [← hON]
      exact le_sup_right
    set Kbar := (K.subgroupOf (C t)).map (nu t) with hKbar
    set Mbar := (M.subgroupOf (C t)).map (nu t) with hMbar
    set Xbar := (X.subgroupOf (C t)).map (nu t) with hXbar
    have hKmem : ∀ c : C t, (c : G) ∈ K → nu t c ∈ Kbar := fun c hc => ⟨c, hc, rfl⟩
    have hMmem : ∀ c : C t, (c : G) ∈ M → nu t c ∈ Mbar := fun c hc => ⟨c, hc, rfl⟩
    have hnorm : ∀ h ∈ Mbar, h ∈ Subgroup.normalizer (Xbar : Set (H t)) → h ∈ Kbar := by
      rintro _ ⟨c, hc, rfl⟩ hh
      apply hKmem
      have h1 := r1n_mem_normalizer_sup_N t hXC c hh
      rw [sup_comm, ← hON] at h1
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hc, h1⟩))
    have hLL : (frontierSetting S fS t p f).L₀ ≤ M := le_sup_left.trans hLM
    have hSM : ((frontierSetting S fS t p f).S : Subgroup G) ≤ M := le_sup_right.trans hLM
    have hYM : Y ≤ Mbar := by
      intro y hy
      obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (N t) y
      exact hMmem c (hLL ⟨c, hy, rfl⟩)
    have hsM : nu t sC ∈ Mbar := hMmem sC (hSM (fS (s n)).2)
    have hsK : nu t sC ∈ Kbar :=
      hKmem sC (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right hsD)))
    have hWbarK : ∀ c : C t, (c : G) ∈ W → nu t c ∈ Kbar := fun c hc =>
      hKmem c (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left hc)))
    have hWbarM : ∀ c : C t, (c : G) ∈ W → nu t c ∈ Mbar := fun c hc =>
      hMmem c (hLL (hJL₀ (hWJ hc)))
    have hWB : ∀ w0 : MatrixTorus.W F b,
        ι (SemidirectProduct.inl w0) ∈ Kbar ∧ ι (SemidirectProduct.inl w0) ∈ Mbar := by
      intro w0
      have hw0 : ι (SemidirectProduct.inl w0) ∈ (W.subgroupOf (C t)).map (nu t) := by
        rw [hF3 W hW]
        exact Subgroup.mem_inf.mpr ⟨(hlay _).mpr rfl, ⟨_, rfl⟩⟩
      obtain ⟨c, hc, hce⟩ := hw0
      rw [← hce]
      exact ⟨hWbarK c hc, hWbarM c hc⟩
    intro m hm
    have hmC := hMC hm
    apply r1n_mem_of_bar t hKC hONK ⟨m, hmC⟩
    by_cases hX1 : Xbar = ⊥
    · apply hnorm _ (hMmem _ hm)
      have hbot : (⊥ : Subgroup (H t)).Normal := inferInstance
      rw [hX1, Subgroup.normalizer_eq_top_iff.mpr hbot]
      exact Subgroup.mem_top _
    have hXB : Xbar ≤ ι.range := fun y hy => hF2 X hXC hXp' hXD y hy
    have hXbarp : IsPGroup p Xbar := (hXp'.comap_subtype (K := C t)).map (nu t)
    have hXtp : IsPGroup p (Xbar.comap ι) := hXbarp.comap_of_injective ι hι
    obtain ⟨Qp, hQp⟩ := hXtp.exists_le_sylow
    have hWp : ¬ p ∣ Nat.card (MatrixTorus.W F b) := by
      rw [MatrixTorus.W_card F b hodd hb, hFcard]
      intro hd
      apply ActualFourGroupCentralizer.prime_not_dvd_torusSize p f hp hf
      exact hd.trans (Nat.div_dvd_of_dvd
        ⟨_, MatrixTorus.torusSize_two_mul_half (hpodd.pow (n := f))⟩)
    have hQpW := r1n_pgroup_inf_inl hWp Qp.isPGroup'
    obtain ⟨k, Qr, hQr⟩ := r1n_semidirect_sylow_conj Qp hQpW
    set c₀ := ι k with hc₀
    have hXdesc : ∀ y ∈ Xbar, ∃ a ∈ (Qr : Subgroup A),
        y = c₀ * Psi (SemidirectProduct.inr a) * c₀⁻¹ := by
      intro y hy
      obtain ⟨x, rfl⟩ := hXB hy
      have hxQ : x ∈ (Qp : Subgroup _) := hQp hy
      rw [hQr] at hxQ
      obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := hxQ
      refine ⟨a, ha, ?_⟩
      change ι (k * SemidirectProduct.inr a * k⁻¹) = _
      rw [map_mul, map_mul, map_inv]
      rfl
    set Qr₀ : Subgroup (F ≃+* F) := (Qr : Subgroup A).map A.subtype with hQr₀def
    have hmodd : Odd (Nat.card Qr₀) :=
      hAodd.of_dvd_nat (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _))
    have hm1 : 1 < Nat.card Qr₀ := by
      by_contra hle
      apply hX1
      have hc1 : Nat.card Qr₀ = 1 := by
        have := Nat.card_pos (α := Qr₀)
        omega
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨a, ha, rfl⟩ := hXdesc y hy
      have ha1 : a = 1 := by
        have ha0 : (a : F ≃+* F) ∈ Qr₀ := ⟨a, ha, rfl⟩
        rw [Subgroup.card_eq_one.mp hc1, Subgroup.mem_bot] at ha0
        exact Subtype.ext ha0
      rw [ha1, map_one, map_one, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    have hgen := sl2_W_sup_fixedEntry_eq_top hpodd hf hFcard hq b hb Qr₀ hmodd hm1
    have hYK : Y ≤ Kbar := by
      intro y hy
      have hy' : c₀⁻¹ * y * c₀ ∈ Y := by
        have h := hYn.conj_mem y hy c₀⁻¹
        rwa [inv_inv] at h
      rw [hlayer] at hy'
      obtain ⟨_, ⟨X0, rfl⟩, hX0⟩ := hy'
      have hX0' : Psi (MatrixTorus.originalSlInH F b A hfix X0) = c₀⁻¹ * y * c₀ := hX0
      have hyΘ : y = c₀ * Psi (MatrixTorus.originalSlInH F b A hfix X0) * c₀⁻¹ := by
        rw [hX0']
        group
      set Θ : MatrixCoverData.SL F →* H t := (MulAut.conj c₀).toMonoidHom.comp
        (Psi.toMonoidHom.comp (MatrixTorus.originalSlInH F b A hfix)) with hΘ
      have hle : (MatrixTorus.W F b).map (MatrixTorus.Torus F b).subtype ⊔
          OddFieldLift.fixedEntrySL2 F Qr₀ ≤ Kbar.comap Θ := by
        apply sup_le
        · rintro _ ⟨w0, hw0, rfl⟩
          have h1 : ι (SemidirectProduct.inl ⟨w0, hw0⟩) =
              Psi (MatrixTorus.originalSlInH F b A hfix (w0 : MatrixCoverData.SL F)) := rfl
          have hmem : Θ (w0 : MatrixCoverData.SL F) ∈ Y ⊓ ι.range := by
            change c₀ * Psi (MatrixTorus.originalSlInH F b A hfix (w0 : MatrixCoverData.SL F)) *
              c₀⁻¹ ∈ Y ⊓ ι.range
            rw [← h1]
            exact Subgroup.mem_inf.mpr ⟨hYn.conj_mem _ ((hlay _).mpr rfl) _,
              ι.range.mul_mem (ι.range.mul_mem ⟨k, rfl⟩ ⟨_, rfl⟩) (ι.range.inv_mem ⟨k, rfl⟩)⟩
          rw [← hF3 W hW] at hmem
          obtain ⟨c, hc, hce⟩ := hmem
          change Θ (w0 : MatrixCoverData.SL F) ∈ Kbar
          rw [← hce]
          exact hWbarK c hc
        · intro X1 hX1
          have hXfix : ∀ a ∈ (Qr : Subgroup A),
              Matrix.SpecialLinearGroup.map (a : F ≃+* F).toRingHom X1 = X1 := fun a ha =>
            (OddFieldLift.mem_fixedEntrySL2 F Qr₀ X1).mp hX1 ⟨a, ⟨a, ha, rfl⟩⟩
          change c₀ * Psi (MatrixTorus.originalSlInH F b A hfix X1) * c₀⁻¹ ∈ Kbar
          set g := c₀ * Psi (MatrixTorus.originalSlInH F b A hfix X1) * c₀⁻¹ with hg
          have hgY : g ∈ Y :=
            hYn.conj_mem _ (by rw [hlayer]; exact ⟨_, ⟨X1, rfl⟩, rfl⟩) _
          have hcent : ∀ z ∈ Xbar, g * z = z * g := by
            intro z hz
            obtain ⟨a, ha, rfl⟩ := hXdesc z hz
            have h := (r1n_originalSlInH_commute_inr_iff F A b hfix a X1).mpr (hXfix a ha)
            have h' : Psi (MatrixTorus.originalSlInH F b A hfix X1) *
                Psi (SemidirectProduct.inr a) = Psi (SemidirectProduct.inr a) *
                Psi (MatrixTorus.originalSlInH F b A hfix X1) := by
              rw [← map_mul, ← map_mul, h]
            calc g * (c₀ * Psi (SemidirectProduct.inr a) * c₀⁻¹)
                = c₀ * (Psi (MatrixTorus.originalSlInH F b A hfix X1) *
                    Psi (SemidirectProduct.inr a)) * c₀⁻¹ := by rw [hg]; group
              _ = c₀ * (Psi (SemidirectProduct.inr a) *
                    Psi (MatrixTorus.originalSlInH F b A hfix X1)) * c₀⁻¹ := by rw [h']
              _ = c₀ * Psi (SemidirectProduct.inr a) * c₀⁻¹ * g := by rw [hg]; group
          apply hnorm g (hYM hgY)
          exact Subgroup.centralizer_le_normalizer _
            (Subgroup.mem_centralizer_iff.mpr fun z hz => (hcent z hz).symm)
      rw [hyΘ]
      exact hle (by rw [hgen]; exact Subgroup.mem_top _)
    have hmM : nu t ⟨m, hmC⟩ ∈ Mbar := hMmem _ hm
    obtain ⟨z, hz⟩ := Psi.surjective (nu t ⟨m, hmC⟩)
    have hzdec : z = MatrixTorus.originalSlInH F b A hfix z.left.left *
        SemidirectProduct.inl (SemidirectProduct.inr z.left.right) *
        SemidirectProduct.inr z.right := by
      change z = SemidirectProduct.inl (SemidirectProduct.inl z.left.left) *
        SemidirectProduct.inl (SemidirectProduct.inr z.left.right) * SemidirectProduct.inr z.right
      rw [← map_mul, SemidirectProduct.inl_left_mul_inr_right,
        SemidirectProduct.inl_left_mul_inr_right]
    have hm3 : nu t ⟨m, hmC⟩ = Psi (MatrixTorus.originalSlInH F b A hfix z.left.left) *
        Psi (SemidirectProduct.inl (SemidirectProduct.inr z.left.right)) *
        Psi (SemidirectProduct.inr z.right) := by
      rw [← hz, ← map_mul, ← map_mul, ← hzdec]
    have he₁ : Psi (MatrixTorus.originalSlInH F b A hfix z.left.left) ∈ Y := by
      rw [hlayer]
      exact ⟨_, ⟨z.left.left, rfl⟩, rfl⟩
    have he₂ : Psi (SemidirectProduct.inl (SemidirectProduct.inr z.left.right) :
          MatrixTorus.OriginalH F b A hfix) ∈ Kbar ∧
        Psi (SemidirectProduct.inl (SemidirectProduct.inr z.left.right) :
          MatrixTorus.OriginalH F b A hfix) ∈ Mbar := by
      rcases MatrixTorus.C2_cases z.left.right with h | h
      · rw [h, map_one, map_one, map_one]
        exact ⟨Kbar.one_mem, Mbar.one_mem⟩
      · have h' : Psi (SemidirectProduct.inl (SemidirectProduct.inr z.left.right) :
            MatrixTorus.OriginalH F b A hfix) = nu t sC := by
          rw [h, ← hPsiU]
          rfl
        rw [h']
        exact ⟨hsK, hsM⟩
    set e₃ := Psi (SemidirectProduct.inr z.right : MatrixTorus.OriginalH F b A hfix) with he₃def
    have he₃M : e₃ ∈ Mbar := by
      have h : e₃ = (Psi (MatrixTorus.originalSlInH F b A hfix z.left.left) *
          Psi (SemidirectProduct.inl (SemidirectProduct.inr z.left.right)))⁻¹ *
          nu t ⟨m, hmC⟩ := by
        rw [hm3]
        group
      rw [h]
      exact Mbar.mul_mem (Mbar.inv_mem (Mbar.mul_mem (hYM he₁) he₂.2)) hmM
    set w₀ := ι (SemidirectProduct.inl k.left) with hw₀
    set a₀ := Psi (SemidirectProduct.inr k.right : MatrixTorus.OriginalH F b A hfix) with ha₀
    have hc₀dec : c₀ = w₀ * a₀ := by
      have h : ι k = ι (SemidirectProduct.inl k.left) * ι (SemidirectProduct.inr k.right) := by
        rw [← map_mul, SemidirectProduct.inl_left_mul_inr_right]
      rw [hc₀, h]
      rfl
    have hcomm3 : a₀ * e₃ = e₃ * a₀ := by
      rw [ha₀, he₃def, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hAcomm k.right z.right]
    have he : c₀ * e₃ * c₀⁻¹ = w₀ * e₃ * w₀⁻¹ := by
      rw [hc₀dec]
      calc w₀ * a₀ * e₃ * (w₀ * a₀)⁻¹ = w₀ * (a₀ * e₃) * a₀⁻¹ * w₀⁻¹ := by group
        _ = w₀ * (e₃ * a₀) * a₀⁻¹ * w₀⁻¹ := by rw [hcomm3]
        _ = w₀ * e₃ * w₀⁻¹ := by group
    have heK : c₀ * e₃ * c₀⁻¹ ∈ Kbar := by
      apply hnorm
      · rw [he]
        exact Mbar.mul_mem (Mbar.mul_mem (hWB k.left).2 he₃M) (Mbar.inv_mem (hWB k.left).2)
      · apply Subgroup.centralizer_le_normalizer
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        obtain ⟨a, ha, rfl⟩ := hXdesc x hx
        have h : Psi (SemidirectProduct.inr a : MatrixTorus.OriginalH F b A hfix) * e₃ =
            e₃ * Psi (SemidirectProduct.inr a) := by
          rw [he₃def, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hAcomm a z.right]
        calc c₀ * Psi (SemidirectProduct.inr a) * c₀⁻¹ * (c₀ * e₃ * c₀⁻¹)
            = c₀ * (Psi (SemidirectProduct.inr a) * e₃) * c₀⁻¹ := by group
          _ = c₀ * (e₃ * Psi (SemidirectProduct.inr a)) * c₀⁻¹ := by rw [h]
          _ = c₀ * e₃ * c₀⁻¹ * (c₀ * Psi (SemidirectProduct.inr a) * c₀⁻¹) := by group
    have he₃K : e₃ ∈ Kbar := by
      have h : e₃ = w₀⁻¹ * (c₀ * e₃ * c₀⁻¹) * w₀ := by
        rw [he]
        group
      rw [h]
      exact Kbar.mul_mem (Kbar.mul_mem (Kbar.inv_mem (hWB k.left).1) heK) (hWB k.left).1
    rw [hm3]
    exact Kbar.mul_mem (Kbar.mul_mem (hYK he₁) he₂.1) he₃K

theorem frontier_x₂_commutator_mem_ON {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ X : Subgroup G, X ≤ (frontierSetting S fS t p f).N → IsPGroup p X →
      (frontierSetting S fS t p f).D ≤ Subgroup.normalizer (X : Set G) → ∀ y ∈ X,
        (frontierSetting S fS t p f).x₂ * y * (frontierSetting S fS t p f).x₂⁻¹ * y⁻¹ ∈
          (frontierSetting S fS t p f).ON := by
  intro X hXN hXp hXD y hy
  obtain ⟨-, ht2, -, hsCmem, -, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hG := CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  obtain ⟨-, -, -, hsD, -, -⟩ := r1n_sd_facts hn S fS t ht p f
  set sC : C t := ⟨(fS (s n) : G), hsCmem⟩ with hsCdef
  obtain ⟨F', hF', hF'fin, A', rho', data'⟩ :=
    actual_simple_layer_matrix_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf
      hmodel
  obtain ⟨-, -, hcommC⟩ :=
    LocalLayerAbelianQuotients.actual_matrix_layer_preimage_has_abelian_quotient t n p f hp
      hpodd hf F' A' rho' data'
  rw [commutator_def] at hcommC
  have hinf := r1n_bar_inf_layer hGnonab hn S fS t ht hnonab hcentral hnc hp hpodd hf hq
    hmodel X hXp hXD
  set x : C t := ⟨y, hXN hy⟩ with hxdef
  have hcX : x * sC * x⁻¹ * sC⁻¹ ∈ X.subgroupOf (C t) := by
    have h1 : (sC : G) * (x : G)⁻¹ * (sC : G)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hXD hsD) _).mp (X.inv_mem hy)
    have h2 := X.mul_mem hy h1
    rw [Subgroup.mem_subgroupOf]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using h2
  have hcL : nu t (x * sC * x⁻¹ * sC⁻¹) ∈
      (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := by
    have h := hcommC (Subgroup.commutator_mem_commutator (Subgroup.mem_top x)
      (Subgroup.mem_top sC))
    rw [commutatorElement_def] at h
    exact h
  have h1 : nu t (x * sC * x⁻¹ * sC⁻¹) = 1 := by
    have hmem : nu t (x * sC * x⁻¹ * sC⁻¹) ∈ (X.subgroupOf (C t)).map (nu t) ⊓
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) :=
      Subgroup.mem_inf.mpr ⟨⟨_, hcX, rfl⟩, hcL⟩
    rw [hinf] at hmem
    exact hmem
  have hmemN : (x * sC * x⁻¹ * sC⁻¹)⁻¹ ∈ N t :=
    (N t).inv_mem ((QuotientGroup.eq_one_iff _).mp h1)
  rw [frontierSetting_ON]
  refine ⟨_, hmemN, ?_⟩
  change ((x * sC * x⁻¹ * sC⁻¹)⁻¹ : C t).1 = (fS (s n) : G) * y * (fS (s n) : G)⁻¹ * y⁻¹
  simp only [hxdef, hsCdef, mul_inv_rev, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]

end CFSG.Semidihedral.AllPrime
