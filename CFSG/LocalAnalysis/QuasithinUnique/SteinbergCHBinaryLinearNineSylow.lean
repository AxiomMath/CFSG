module

public import CFSG.LocalAnalysis.QuasithinUnique.SteinbergCHBinaryLinearParabolic
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer

public section

namespace CFSG.QuasithinUnique

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  Subgroup
open scoped Pointwise

namespace SteinbergCH

section GL2

variable (K : Type*) [Field K]

@[expose] noncomputable def glUpper : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 1; 0, 1] (by simp)

@[expose] noncomputable def glThree : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 1] (by simp)

variable {K}

theorem coe_glUpper : ((glUpper K : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 0, 1] :=
  rfl

theorem coe_glThree : ((glThree K : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 1] :=
  rfl

theorem orderOf_glUpper [Finite K] (hK : Nat.card K = 2) : orderOf (glUpper K) = 2 := by
  have : CharP K 2 := charP_two_of_card_two hK
  have h11 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (Units.ext ?_) fun h => ?_
  · rw [Units.val_pow_eq_pow_val, coe_glUpper, Units.val_one, sq, Matrix.mul_fin_two,
      Matrix.one_fin_two]
    simp [h11]
  · have := congrArg (fun x : GL (Fin 2) K => (x : Matrix (Fin 2) (Fin 2) K) 0 1) h
    simp [coe_glUpper] at this

theorem orderOf_glThree [Finite K] (hK : Nat.card K = 2) : orderOf (glThree K) = 3 := by
  have : CharP K 2 := charP_two_of_card_two hK
  have h11 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (Units.ext ?_) fun h => ?_
  · rw [Units.val_pow_eq_pow_val, coe_glThree, Units.val_one, pow_succ, sq, Matrix.mul_fin_two,
      Matrix.mul_fin_two, Matrix.one_fin_two]
    simp [h11]
  · have := congrArg (fun x : GL (Fin 2) K => (x : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp [coe_glThree] at this

theorem exists_unique_card_three_GL2 [Finite K] (hK : Nat.card K = 2) :
    ∃ T : Subgroup (GL (Fin 2) K), Nat.card T = 3 ∧
      (∀ T' : Subgroup (GL (Fin 2) K), Nat.card T' = 3 → T' = T) ∧ glThree K ∈ T := by
  have h6 := card_GL_two_of_card_two hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT3 : Nat.card (zpowers (glThree K)) = 3 := by rw [Nat.card_zpowers, orderOf_glThree hK]
  refine ⟨zpowers (glThree K), hT3, fun T' hT' => ?_, mem_zpowers _⟩
  have hidx : ∀ H : Subgroup (GL (Fin 2) K), Nat.card H = 3 → H.index = 2 := by
    intro H hH
    have := H.card_mul_index
    rw [hH, h6] at this
    omega
  have hsyl : ∀ H : Subgroup (GL (Fin 2) K), Nat.card H = 3 → IsPGroup 3 H ∧ ¬ 3 ∣ H.index :=
    fun H hH => ⟨IsPGroup.of_card (n := 1) (by rw [hH, pow_one]), by rw [hidx H hH]; norm_num⟩
  obtain ⟨h1, h2⟩ := hsyl T' hT'
  obtain ⟨h3, h4⟩ := hsyl _ hT3
  have hcard : Nat.card (Sylow 3 (GL (Fin 2) K)) = 1 := by
    have hmod := card_sylow_modEq_one 3 (GL (Fin 2) K)
    have hdvd := (h1.toSylow h2).card_dvd_index
    change Nat.card (Sylow 3 (GL (Fin 2) K)) ∣ T'.index at hdvd
    rw [hidx T' hT'] at hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card (Sylow 3 (GL (Fin 2) K))
    · simp at hdvd
    · rfl
    · exact absurd hmod (by decide)
  have := (Nat.card_eq_one_iff_unique.mp hcard).1
  exact congrArg (fun P : Sylow 3 (GL (Fin 2) K) => (P : Subgroup (GL (Fin 2) K)))
    (Subsingleton.elim (h1.toSylow h2) (h3.toSylow h4))

theorem eq_zero_of_commute_glThree {ε : K}
    (h : !![1, ε; 0, 1] * !![(0 : K), 1; 1, 1] = !![0, 1; 1, 1] * !![1, ε; 0, 1]) : ε = 0 := by
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two] at h
  have := congrFun (congrFun h 0) 0
  simpa using this

end GL2

theorem mem_map_conj_iff {G : Type*} [Group G] (g : G) (H : Subgroup G) (x : G) :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem map_conj_map_conj_inv {G : Type*} [Group G] (g : G) (H : Subgroup G) :
    (H.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = H := by
  ext x
  rw [mem_map_conj_iff, mem_map_conj_iff, inv_inv]
  constructor <;> intro h
  · simpa [mul_assoc] using h
  · simpa [mul_assoc] using h

@[expose] noncomputable def restrictionAction {G : Type*} [Group G] (D B : Subgroup G) :
    ↥(normalizer (D : Set G) ⊓ normalizer (B : Set G)) →* MulAut D :=
  D.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_left)

variable {K : Type*} [Field K] {n : ℕ}

theorem pair_not_succ {p₁ p₂ : ℕ} (hp : p₁ + 2 ≤ p₂) :
    ∀ x ∈ ({p₁ + 1, p₂ + 1} : Set ℕ), x + 1 ∉ ({p₁ + 1, p₂ + 1} : Set ℕ) := by
  intro x hx hx1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hx1
  omega

theorem pair_bounds {p₁ p₂ : ℕ} (hp : p₁ + 2 ≤ p₂) (hpn : p₂ + 2 ≤ n) :
    ∀ x ∈ ({p₁ + 1, p₂ + 1} : Set ℕ), 1 ≤ x ∧ x < n := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  omega

variable (K) in
@[expose] noncomputable def pairBlockHom {p₁ p₂ : ℕ} (hp : p₁ + 2 ≤ p₂) (hpn : p₂ + 2 ≤ n) :
    flagStabilizer n K (joinCuts n {p₁ + 1, p₂ + 1}) →* GL (Fin 2) K × GL (Fin 2) K :=
  (blockHom K (pair_not_succ hp) (Set.mem_insert _ _) (by omega)).prod
    (blockHom K (pair_not_succ hp) (Set.mem_insert_of_mem _ rfl) hpn)

theorem ker_pairBlockHom [Finite K] (hK : Nat.card K = 2) {p₁ p₂ : ℕ} (hp : p₁ + 2 ≤ p₂)
    (hpn : p₂ + 2 ≤ n) :
    (pairBlockHom K hp hpn).ker = (blockRadical n K (joinCuts n {p₁ + 1, p₂ + 1})).subgroupOf
      (flagStabilizer n K (joinCuts n {p₁ + 1, p₂ + 1})) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
    mem_blockRadical_joinCuts_iff hK (pair_not_succ hp) (pair_bounds hp hpn) x.2]
  simp only [pairBlockHom, MonoidHom.prod_apply, Prod.mk_eq_one, Units.ext_iff, coe_blockHom,
    Units.val_one]
  constructor
  · rintro ⟨h1, h2⟩ p hpJ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpJ
    rcases hpJ with h | h
    · obtain rfl : p = p₁ := by omega
      exact h1
    · obtain rfl : p = p₂ := by omega
      exact h2
  · intro h
    exact ⟨h p₁ (Set.mem_insert _ _), h p₂ (Set.mem_insert_of_mem _ rfl)⟩

theorem blockMat_of_mem_unitriangular {p : ℕ} (hp : p + 2 ≤ n)
    {u : SpecialLinearGroup (Fin n) K} (hu : u ∈ unitriangular n K) :
    blockMat p hp (u : Matrix (Fin n) (Fin n) K) =
      !![1, (u : Matrix (Fin n) (Fin n) K) ⟨p, by omega⟩ ⟨p + 1, by omega⟩; 0, 1] := by
  have hlt : (⟨p, by omega⟩ : Fin n) < ⟨p + 1, by omega⟩ := Fin.lt_def.mpr (by simp)
  ext a b
  fin_cases a <;> fin_cases b
  · rw [blockMat_apply_of_eq (i := ⟨p, by omega⟩) (j := ⟨p, by omega⟩) (by simp) (by simp),
      hu.2]
    rfl
  · rw [blockMat_apply_of_eq (i := ⟨p, by omega⟩) (j := ⟨p + 1, by omega⟩) (by simp) (by simp)]
    rfl
  · rw [blockMat_apply_of_eq (i := ⟨p + 1, by omega⟩) (j := ⟨p, by omega⟩) (by simp) (by simp),
      hu.1 _ _ hlt]
    rfl
  · rw [blockMat_apply_of_eq (i := ⟨p + 1, by omega⟩) (j := ⟨p + 1, by omega⟩) (by simp)
      (by simp), hu.2]
    rfl

theorem pair_structure [Finite K] (hK : Nat.card K = 2) {p₁ p₂ : ℕ} (hp : p₁ + 2 ≤ p₂)
    (hpn : p₂ + 2 ≤ n) {D : Subgroup (SpecialLinearGroup (Fin n) K)} (hD : Nat.card D = 9)
    (hDU : D ⊓ unitriangular n K = ⊥)
    (hDQ : D ≤ flagStabilizer n K (joinCuts n {p₁ + 1, p₂ + 1})) :
    Function.Injective ((pairBlockHom K hp hpn).comp (Subgroup.inclusion hDQ)) ∧
      (∃ T : Subgroup (GL (Fin 2) K), Nat.card T = 3 ∧
        (∀ T' : Subgroup (GL (Fin 2) K), Nat.card T' = 3 → T' = T) ∧
        ((pairBlockHom K hp hpn).comp (Subgroup.inclusion hDQ)).range = T.prod T) ∧
      Function.Surjective (pairBlockHom K hp hpn) ∧
      ∀ u ∈ unitriangular n K, u ∈ normalizer (D : Set (SpecialLinearGroup (Fin n) K)) →
        ((∀ d ∈ D, u * d * u⁻¹ = d) ↔
          (u : Matrix (Fin n) (Fin n) K) ⟨p₁, by omega⟩ ⟨p₁ + 1, by omega⟩ = 0 ∧
            (u : Matrix (Fin n) (Fin n) K) ⟨p₂, by omega⟩ ⟨p₂ + 1, by omega⟩ = 0) := by
  set Q := flagStabilizer n K (joinCuts n {p₁ + 1, p₂ + 1}) with hQ
  set π := pairBlockHom K hp hpn with hπ
  have hUQ : unitriangular n K ≤ Q :=
    (unitriangular_le_upperTriangular n K).trans (upperTriangular_le_flagStabilizer _)
  have hker := ker_pairBlockHom hK hp hpn
  have hkerU : ∀ x : Q, π x = 1 → (x : SpecialLinearGroup (Fin n) K) ∈ unitriangular n K := by
    intro x hx
    have hx' : x ∈ π.ker := hx
    rw [hker, Subgroup.mem_subgroupOf] at hx'
    exact blockRadical_le_unitriangular _ hx'
  have hinj : Function.Injective (π.comp (Subgroup.inclusion hDQ)) := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have hmem : (d : SpecialLinearGroup (Fin n) K) ∈ D ⊓ unitriangular n K := ⟨d.2, hkerU _ hd⟩
    rw [hDU, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  obtain ⟨T, hT3, hTu, hcT⟩ := exists_unique_card_three_GL2 hK
  have h6 := card_GL_two_of_card_two hK
  set φD := π.comp (Subgroup.inclusion hDQ) with hφD
  have hrange_card : Nat.card φD.range = 9 := by
    rw [← hD]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hle_T : ∀ ψ : D →* GL (Fin 2) K, ψ.range ≤ T := by
    intro ψ
    have h1 : Nat.card ψ.range ∣ 9 := by
      rw [← hD, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
      exact Subgroup.card_quotient_dvd_card _
    have h2 : Nat.card ψ.range ∣ 6 := h6 ▸ Subgroup.card_subgroup_dvd_card _
    have h3 : Nat.card ψ.range ∣ 3 := by
      have := Nat.dvd_gcd h1 h2
      rwa [show Nat.gcd 9 6 = 3 by norm_num] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
    · rw [Subgroup.card_eq_one.mp h]
      exact bot_le
    · exact (hTu _ h).le
  have hrangeT : φD.range = T.prod T := by
    have hle : φD.range ≤ T.prod T := by
      rintro _ ⟨d, rfl⟩
      exact ⟨hle_T ((MonoidHom.fst _ _).comp φD) ⟨d, rfl⟩,
        hle_T ((MonoidHom.snd _ _).comp φD) ⟨d, rfl⟩⟩
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hrange_card, Nat.card_congr (Subgroup.prodEquiv T T).toEquiv, Nat.card_prod, hT3]
  have hp₁ : p₁ + 1 < n := by omega
  have hp₂ : p₂ + 1 < n := by omega
  have hlt₁ : (⟨p₁, by omega⟩ : Fin n) < ⟨p₁ + 1, hp₁⟩ := Fin.lt_def.mpr (by simp)
  have hlt₂ : (⟨p₂, by omega⟩ : Fin n) < ⟨p₂ + 1, hp₂⟩ := Fin.lt_def.mpr (by simp)
  set x₁ : SpecialLinearGroup (Fin n) K := SpecialLinearGroup.transvection hlt₁.ne (1 : K)
  set x₂ : SpecialLinearGroup (Fin n) K := SpecialLinearGroup.transvection hlt₂.ne (1 : K)
  have hx₁U : x₁ ∈ unitriangular n K := transvection_mem_unitriangular hlt₁ 1
  have hx₂U : x₂ ∈ unitriangular n K := transvection_mem_unitriangular hlt₂ 1
  have hblock : ∀ (p : ℕ) (hpJ : p + 1 ∈ ({p₁ + 1, p₂ + 1} : Set ℕ)) (hpn' : p + 2 ≤ n)
      (u : SpecialLinearGroup (Fin n) K) (hu : u ∈ unitriangular n K),
      ((blockHom K (pair_not_succ hp) hpJ hpn' ⟨u, hUQ hu⟩ : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) =
        !![1, (u : Matrix (Fin n) (Fin n) K) ⟨p, by omega⟩ ⟨p + 1, by omega⟩; 0, 1] :=
    fun p hpJ hpn' u hu => by rw [coe_blockHom]; exact blockMat_of_mem_unitriangular hpn' hu
  have hπx₁ : π ⟨x₁, hUQ hx₁U⟩ = (glUpper K, 1) := by
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · rw [hπ, pairBlockHom, MonoidHom.prod_apply, hblock _ _ _ _ hx₁U, coe_glUpper]
      simp [x₁, SpecialLinearGroup.transvection_coe]
    · rw [hπ, pairBlockHom, MonoidHom.prod_apply, hblock _ _ _ _ hx₁U, Units.val_one,
        Matrix.one_fin_two]
      simp [x₁, SpecialLinearGroup.transvection_coe, single_apply]
      omega
  have hπx₂ : π ⟨x₂, hUQ hx₂U⟩ = (1, glUpper K) := by
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · rw [hπ, pairBlockHom, MonoidHom.prod_apply, hblock _ _ _ _ hx₂U, Units.val_one,
        Matrix.one_fin_two]
      simp [x₂, SpecialLinearGroup.transvection_coe, single_apply]
      omega
    · rw [hπ, pairBlockHom, MonoidHom.prod_apply, hblock _ _ _ _ hx₂U, coe_glUpper]
      simp [x₂, SpecialLinearGroup.transvection_coe]
  have hsurj : Function.Surjective π := by
    have hTT : T.prod T ≤ π.range := by
      rw [← hrangeT]
      rintro _ ⟨d, rfl⟩
      exact ⟨_, rfl⟩
    have hV : (zpowers (glUpper K)).prod (zpowers (glUpper K)) ≤ π.range := by
      rw [Subgroup.prod_le_iff, MonoidHom.map_zpowers, MonoidHom.map_zpowers, Subgroup.zpowers_le,
        Subgroup.zpowers_le, MonoidHom.inl_apply, MonoidHom.inr_apply]
      exact ⟨⟨_, hπx₁⟩, ⟨_, hπx₂⟩⟩
    have h9 : 9 ∣ Nat.card π.range := by
      have := Subgroup.card_dvd_of_le hTT
      rwa [Nat.card_congr (Subgroup.prodEquiv T T).toEquiv, Nat.card_prod, hT3] at this
    have h4 : 4 ∣ Nat.card π.range := by
      have := Subgroup.card_dvd_of_le hV
      rwa [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Nat.card_zpowers,
        orderOf_glUpper hK] at this
    have h36 : Nat.card (GL (Fin 2) K × GL (Fin 2) K) = 36 := by rw [Nat.card_prod, h6]
    have hle36 : Nat.card π.range ≤ 36 := h36 ▸ Subgroup.card_le_card_group _
    have hpos : 0 < Nat.card π.range := Nat.card_pos
    have h36' : Nat.card π.range = 36 := by
      have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 9 4) h9 h4
      have := Nat.le_of_dvd hpos this
      omega
    rw [← MonoidHom.range_eq_top, ← Subgroup.card_eq_iff_eq_top, h36', h36]
  refine ⟨hinj, ⟨T, hT3, hTu, hrangeT⟩, hsurj, fun u hu hun => ?_⟩
  have huQ : u ∈ Q := hUQ hu
  have hblk₁ := hblock p₁ (Set.mem_insert _ _) (by omega) u hu
  have hblk₂ := hblock p₂ (Set.mem_insert_of_mem _ rfl) hpn u hu
  constructor
  · intro hc
    have hcc : (glThree K, glThree K) ∈ φD.range := by
      rw [hrangeT]
      exact ⟨hcT, hcT⟩
    obtain ⟨d, hd⟩ := hcc
    have hdu : (⟨u, huQ⟩ : Q) * ⟨d, hDQ d.2⟩ = ⟨d, hDQ d.2⟩ * ⟨u, huQ⟩ := by
      apply Subtype.ext
      have := hc d d.2
      simp only [Subgroup.coe_mul]
      calc u * d = u * d * u⁻¹ * u := by group
        _ = d * u := by rw [this]
    have hπdu := congrArg π hdu
    rw [map_mul, map_mul] at hπdu
    have hd' : π ⟨d, hDQ d.2⟩ = (glThree K, glThree K) := hd
    rw [hd'] at hπdu
    have e₁ := congrArg (fun z : GL (Fin 2) K × GL (Fin 2) K =>
      ((z.1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hπdu
    have e₂ := congrArg (fun z : GL (Fin 2) K × GL (Fin 2) K =>
      ((z.2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hπdu
    simp only [Prod.fst_mul, Prod.snd_mul, Units.val_mul, coe_glThree] at e₁ e₂
    rw [hπ, pairBlockHom, MonoidHom.prod_apply, hblk₁] at e₁
    rw [hπ, pairBlockHom, MonoidHom.prod_apply, hblk₂] at e₂
    exact ⟨eq_zero_of_commute_glThree e₁, eq_zero_of_commute_glThree e₂⟩
  · rintro ⟨h₁, h₂⟩ d hd
    have hπu : π ⟨u, huQ⟩ = 1 := by
      refine Prod.ext (Units.ext ?_) (Units.ext ?_)
      · rw [hπ, pairBlockHom, MonoidHom.prod_apply, hblk₁, h₁, Prod.fst_one, Units.val_one,
          Matrix.one_fin_two]
      · rw [hπ, pairBlockHom, MonoidHom.prod_apply, hblk₂, h₂, Prod.snd_one, Units.val_one,
          Matrix.one_fin_two]
    set dq : Q := ⟨d, hDQ hd⟩
    have hcomm1 : π (dq * ⟨u, huQ⟩ * dq⁻¹ * (⟨u, huQ⟩ : Q)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hπu]
      group
    have hcU := hkerU _ hcomm1
    have hcD : d * u * d⁻¹ * u⁻¹ ∈ D := by
      have := (mem_normalizer_iff.mp hun d⁻¹).mp (D.inv_mem hd)
      have h' := D.mul_mem hd this
      simpa [mul_assoc] using h'
    have hmem : d * u * d⁻¹ * u⁻¹ ∈ D ⊓ unitriangular n K := ⟨hcD, hcU⟩
    rw [hDU, Subgroup.mem_bot] at hmem
    calc u * d * u⁻¹ = (d * u * d⁻¹ * u⁻¹)⁻¹ * d := by group
      _ = d := by rw [hmem, inv_one, one_mul]

end SteinbergCH

open SteinbergCH

theorem binary_linear_four_five_nine_Sylow_products_have_abelian_inner_common_action
    {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (B₂ : Sylow 2 (SpecialLinearGroup (Fin n) K)) :
    normalizer ((B₂ : Subgroup (SpecialLinearGroup (Fin n) K)) :
        Set (SpecialLinearGroup (Fin n) K)) = B₂ ∧
      Nat.card (Subgroup.center (B₂ : Subgroup (SpecialLinearGroup (Fin n) K))) = 2 ∧
      ∀ D : Subgroup (SpecialLinearGroup (Fin n) K), Nat.card D = 9 →
        (D : Set (SpecialLinearGroup (Fin n) K)) *
            ((B₂ : Subgroup (SpecialLinearGroup (Fin n) K)) : Set (SpecialLinearGroup (Fin n) K)) =
          ((B₂ : Subgroup (SpecialLinearGroup (Fin n) K)) : Set (SpecialLinearGroup (Fin n) K)) *
            (D : Set (SpecialLinearGroup (Fin n) K)) →
        ((D ⊔ (B₂ : Subgroup (SpecialLinearGroup (Fin n) K)) : Subgroup _) :
            Set (SpecialLinearGroup (Fin n) K)) =
          (D : Set (SpecialLinearGroup (Fin n) K)) *
            ((B₂ : Subgroup (SpecialLinearGroup (Fin n) K)) : Set (SpecialLinearGroup (Fin n) K)) ∧
        (∃ (g : SpecialLinearGroup (Fin n) K) (a : List ℕ),
          a.sum = n ∧ (∀ x ∈ a, x = 1 ∨ x = 2) ∧ a.count 2 = 2 ∧
          D ⊔ B₂ = (flagStabilizer n K (compositionCuts a)).map (MulAut.conj g).toMonoidHom ∧
          (B₂ : Subgroup (SpecialLinearGroup (Fin n) K)) =
            (unitriangular n K).map (MulAut.conj g).toMonoidHom ∧
          (blockRadical n K (compositionCuts a)).map (MulAut.conj g).toMonoidHom ≤ D ⊔ B₂ ∧
          (((blockRadical n K (compositionCuts a)).map (MulAut.conj g).toMonoidHom).subgroupOf
            (D ⊔ B₂)).Normal ∧
          IsPGroup 2 ((blockRadical n K (compositionCuts a)).map (MulAut.conj g).toMonoidHom) ∧
          ∃ φ : ↥(D ⊔ (B₂ : Subgroup (SpecialLinearGroup (Fin n) K))) →*
              GL (Fin 2) K × GL (Fin 2) K,
            Function.Surjective φ ∧
            φ.ker = ((blockRadical n K (compositionCuts a)).map
              (MulAut.conj g).toMonoidHom).subgroupOf (D ⊔ B₂) ∧
            Nonempty ((↥(D ⊔ (B₂ : Subgroup (SpecialLinearGroup (Fin n) K))) ⧸ φ.ker) ≃*
              GL (Fin 2) K × GL (Fin 2) K) ∧
            Function.Injective (φ.comp (Subgroup.inclusion le_sup_left)) ∧
            ∃ T : Subgroup (GL (Fin 2) K), Nat.card T = 3 ∧
              (∀ T' : Subgroup (GL (Fin 2) K), Nat.card T' = 3 → T' = T) ∧
              (φ.comp (Subgroup.inclusion le_sup_left)).range = T.prod T) ∧
        (∃ f : (restrictionAction D B₂).range →*
            Multiplicative (ZMod 2) × Multiplicative (ZMod 2), Function.Injective f) ∧
          Nat.card (restrictionAction D B₂).range ≤ 4 ∧
          ∀ x y : (restrictionAction D B₂).range, x * y = y * x := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have : CharP K 2 := charP_two_of_card_two hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U₀, hU₀⟩ := exists_sylow_unitriangular (K := K) 2 hn1
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin n) K) U₀ B₂
  have hB : (B₂ : Subgroup (SpecialLinearGroup (Fin n) K)) =
      (unitriangular n K).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, coe_sylow_smul, hU₀]
    rfl
  have hNB : normalizer ((B₂ : Subgroup (SpecialLinearGroup (Fin n) K)) :
      Set (SpecialLinearGroup (Fin n) K)) = B₂ := by
    rw [hB, ← Subgroup.map_equiv_normalizer_eq, normalizer_unitriangular,
      upperTriangular_eq_unitriangular_of_card_two hK]
  have hZ : Nat.card (Subgroup.center (B₂ : Subgroup (SpecialLinearGroup (Fin n) K))) = 2 := by
    rw [hB, ← Nat.card_congr (Subgroup.centerCongr (Subgroup.equivMapOfInjective
      (unitriangular n K) (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)).toEquiv]
    exact card_center_unitriangular hK hn2
  refine ⟨hNB, hZ, fun D hD hDB => ?_⟩
  set D' := D.map (MulAut.conj g⁻¹).toMonoidHom with hD'
  have hD'card : Nat.card D' = 9 := by
    rw [hD', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hD]
  have hconjB : (B₂ : Subgroup (SpecialLinearGroup (Fin n) K)).map
      (MulAut.conj g⁻¹).toMonoidHom = unitriangular n K := by
    have := map_conj_map_conj_inv g⁻¹ (unitriangular n K)
    rwa [inv_inv, ← hB] at this
  have hD'U : (D' : Set (SpecialLinearGroup (Fin n) K)) * (unitriangular n K) =
      (unitriangular n K) * (D' : Set (SpecialLinearGroup (Fin n) K)) := by
    rw [← hconjB, hD', Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, ← Set.image_mul, hDB]
  have hD'mem : ∀ x : SpecialLinearGroup (Fin n) K, x ∈ D' ↔ g * x * g⁻¹ ∈ D := by
    intro x
    rw [hD', mem_map_conj_iff, inv_inv]
  obtain ⟨hinf', p₁, p₂, a, hp, hpn, hY', ha_sum, ha12, ha2, hcuts⟩ :=
    exists_joinCuts_of_card_nine hK hn hD'card hD'U
  set Q := flagStabilizer n K (joinCuts n {p₁ + 1, p₂ + 1}) with hQ
  have hD'Q : D' ≤ Q := hY' ▸ le_sup_left
  obtain ⟨hinj', ⟨T, hT3, hTu, hTrange⟩, hsurj', hcent⟩ :=
    pair_structure hK hp hpn hD'card hinf' hD'Q
  set π := pairBlockHom K hp hpn with hπ
  have hY : D ⊔ (B₂ : Subgroup (SpecialLinearGroup (Fin n) K)) =
      Q.map (MulAut.conj g).toMonoidHom := by
    rw [← hY', Subgroup.map_sup, hD', map_conj_map_conj_inv, hB]
  have hYQ' : D ⊔ (B₂ : Subgroup (SpecialLinearGroup (Fin n) K)) =
      (flagStabilizer n K (compositionCuts a)).map (MulAut.conj g).toMonoidHom := by
    rw [hcuts]
    exact hY
  set R := (blockRadical n K (compositionCuts a)).map (MulAut.conj g).toMonoidHom with hR
  have hR' : R = (blockRadical n K (joinCuts n {p₁ + 1, p₂ + 1})).map
      (MulAut.conj g).toMonoidHom := by
    rw [hR, hcuts]
  have hmemQ : ∀ y : ↥(D ⊔ (B₂ : Subgroup (SpecialLinearGroup (Fin n) K))),
      g⁻¹ * (y : SpecialLinearGroup (Fin n) K) * g ∈ Q :=
    fun y => (mem_map_conj_iff g Q y).mp (hY ▸ y.2)
  let ψY : ↥(D ⊔ (B₂ : Subgroup (SpecialLinearGroup (Fin n) K))) →* Q :=
    { toFun := fun y => ⟨g⁻¹ * y * g, hmemQ y⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let φ := π.comp ψY
  have hφsurj : Function.Surjective φ := by
    intro z
    obtain ⟨q, rfl⟩ := hsurj' z
    have hq : g * (q : SpecialLinearGroup (Fin n) K) * g⁻¹ ∈
        D ⊔ (B₂ : Subgroup (SpecialLinearGroup (Fin n) K)) := by
      rw [hY, mem_map_conj_iff]
      simp [mul_assoc]
    refine ⟨⟨_, hq⟩, ?_⟩
    show π (ψY ⟨_, hq⟩) = π q
    congr 1
    apply Subtype.ext
    show g⁻¹ * (g * q * g⁻¹) * g = q
    group
  have hφker : φ.ker = R.subgroupOf (D ⊔ (B₂ : Subgroup (SpecialLinearGroup (Fin n) K))) := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hR', mem_map_conj_iff]
    change π (ψY y) = 1 ↔ _
    rw [← MonoidHom.mem_ker, ker_pairBlockHom hK hp hpn, Subgroup.mem_subgroupOf]
    rfl
  have hdmem : ∀ d : D, g⁻¹ * (d : SpecialLinearGroup (Fin n) K) * g ∈ D' := fun d => by
    rw [hD'mem]
    simp [mul_assoc]
  have hφD : ∀ d : D, φ (Subgroup.inclusion le_sup_left d) =
      (π.comp (Subgroup.inclusion hD'Q)) ⟨_, hdmem d⟩ := fun d => rfl
  have hφinj : Function.Injective (φ.comp (Subgroup.inclusion le_sup_left)) := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have h1 : (π.comp (Subgroup.inclusion hD'Q)) ⟨_, hdmem d⟩ = 1 := (hφD d).symm.trans hd
    have h2 := (injective_iff_map_eq_one _).mp hinj' _ h1
    have h3 : g⁻¹ * (d : SpecialLinearGroup (Fin n) K) * g = 1 := congrArg Subtype.val h2
    apply Subtype.ext
    calc (d : SpecialLinearGroup (Fin n) K) = g * (g⁻¹ * d * g) * g⁻¹ := by group
      _ = 1 := by rw [h3]; group
  have hφrange : (φ.comp (Subgroup.inclusion le_sup_left)).range = T.prod T := by
    rw [← hTrange]
    ext z
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨⟨_, hdmem d⟩, (hφD d).symm⟩
    · rintro ⟨d', rfl⟩
      have hd : g * (d' : SpecialLinearGroup (Fin n) K) * g⁻¹ ∈ D := (hD'mem _).mp d'.2
      refine ⟨⟨_, hd⟩, ?_⟩
      show π (ψY _) = π (Subgroup.inclusion hD'Q d')
      congr 1
      apply Subtype.ext
      show g⁻¹ * (g * d' * g⁻¹) * g = d'
      group
  have hRle : R ≤ D ⊔ (B₂ : Subgroup (SpecialLinearGroup (Fin n) K)) := by
    rw [hR', hY]
    exact Subgroup.map_mono (blockRadical_le_flagStabilizer _)
  have hRnormal : (R.subgroupOf (D ⊔ (B₂ : Subgroup (SpecialLinearGroup (Fin n) K)))).Normal :=
    hφker ▸ φ.normal_ker
  have hRp : IsPGroup 2 R := by
    refine IsPGroup.to_le B₂.isPGroup' ?_
    rw [hR', hB]
    exact Subgroup.map_mono (blockRadical_le_unitriangular _)
  refine ⟨coe_sup_eq_mul_of_permute D _ hDB, ⟨g, a, ha_sum, ha12, ha2, hYQ', hB, hRle, hRnormal,
    hRp, φ, hφsurj, hφker, ⟨QuotientGroup.quotientKerEquivOfSurjective φ hφsurj⟩, hφinj, T, hT3,
    hTu, hφrange⟩, ?_⟩
  have hNU : ∀ x : ↥(normalizer (D : Set (SpecialLinearGroup (Fin n) K)) ⊓
      normalizer ((B₂ : Subgroup (SpecialLinearGroup (Fin n) K)) :
        Set (SpecialLinearGroup (Fin n) K))),
      g⁻¹ * (x : SpecialLinearGroup (Fin n) K) * g ∈ unitriangular n K := by
    have hy : ∀ y : SpecialLinearGroup (Fin n) K,
        y ∈ normalizer ((B₂ : Subgroup (SpecialLinearGroup (Fin n) K)) :
          Set (SpecialLinearGroup (Fin n) K)) → g⁻¹ * y * g ∈ unitriangular n K := by
      intro y hy
      rw [hNB, hB, mem_map_conj_iff] at hy
      exact hy
    exact fun x => hy _ x.2.2
  have hp₁ : p₁ + 1 < n := by omega
  have hp₂ : p₂ + 1 < n := by omega
  let ψ : ↥(normalizer (D : Set (SpecialLinearGroup (Fin n) K)) ⊓
      normalizer ((B₂ : Subgroup (SpecialLinearGroup (Fin n) K)) :
        Set (SpecialLinearGroup (Fin n) K))) →* Multiplicative K × Multiplicative K :=
    { toFun := fun x =>
        (Multiplicative.ofAdd (((g⁻¹ * (x : SpecialLinearGroup (Fin n) K) * g :
            SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨p₁, by omega⟩ ⟨p₁ + 1, hp₁⟩),
          Multiplicative.ofAdd (((g⁻¹ * (x : SpecialLinearGroup (Fin n) K) * g :
            SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨p₂, by omega⟩ ⟨p₂ + 1, hp₂⟩))
      map_one' := by
        have h₁ : (⟨p₁, by omega⟩ : Fin n) ≠ ⟨p₁ + 1, hp₁⟩ := fun h => by
          simpa using congrArg Fin.val h
        have h₂ : (⟨p₂, by omega⟩ : Fin n) ≠ ⟨p₂ + 1, hp₂⟩ := fun h => by
          simpa using congrArg Fin.val h
        simp only [OneMemClass.coe_one, mul_one, inv_mul_cancel, SpecialLinearGroup.coe_one,
          one_apply_ne h₁, one_apply_ne h₂, ofAdd_zero, Prod.mk_one_one]
      map_mul' := fun x y => by
        have hxy : g⁻¹ * ((x * y : ↥(normalizer (D : Set (SpecialLinearGroup (Fin n) K)) ⊓
            normalizer ((B₂ : Subgroup (SpecialLinearGroup (Fin n) K)) :
              Set (SpecialLinearGroup (Fin n) K)))) : SpecialLinearGroup (Fin n) K) * g =
            (g⁻¹ * x * g) * (g⁻¹ * y * g) := by
          simp only [Subgroup.coe_mul]
          group
        rw [hxy, mul_apply_superdiag (hNU x) (hNU y) p₁ hp₁,
          mul_apply_superdiag (hNU x) (hNU y) p₂ hp₂]
        rfl }
  have hρ : ∀ x, restrictionAction D B₂ x = 1 ↔
      ∀ d ∈ D, (x : SpecialLinearGroup (Fin n) K) * d * (x : SpecialLinearGroup (Fin n) K)⁻¹ =
        d := by
    intro x
    rw [MulEquiv.ext_iff]
    constructor
    · intro h d hd
      have := congrArg Subtype.val (h ⟨d, hd⟩)
      simpa [restrictionAction, Subgroup.normalizerMonoidHom_apply_apply_coe] using this
    · intro h d
      apply Subtype.ext
      simp [restrictionAction, Subgroup.normalizerMonoidHom_apply_apply_coe, h d d.2]
  have hψ : ∀ x, ψ x = 1 ↔
      ∀ d ∈ D, (x : SpecialLinearGroup (Fin n) K) * d * (x : SpecialLinearGroup (Fin n) K)⁻¹ =
        d := by
    intro x
    have hu := hNU x
    have hun : g⁻¹ * (x : SpecialLinearGroup (Fin n) K) * g ∈
        normalizer (D' : Set (SpecialLinearGroup (Fin n) K)) := by
      rw [mem_normalizer_iff]
      intro h
      rw [hD'mem, hD'mem, mem_normalizer_iff.mp x.2.1 (g * h * g⁻¹)]
      constructor <;> intro hh <;> simpa [mul_assoc] using hh
    have hψx : ψ x = 1 ↔ ((g⁻¹ * (x : SpecialLinearGroup (Fin n) K) * g :
        SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨p₁, by omega⟩ ⟨p₁ + 1, hp₁⟩ =
          0 ∧ ((g⁻¹ * (x : SpecialLinearGroup (Fin n) K) * g :
        SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨p₂, by omega⟩ ⟨p₂ + 1, hp₂⟩ =
          0 :=
      Prod.mk_eq_one.trans (and_congr ofAdd_eq_one ofAdd_eq_one)
    rw [hψx, ← hcent _ hu hun]
    constructor
    · intro h d hd
      have := h (g⁻¹ * d * g) ((hD'mem _).mpr (by simpa [mul_assoc] using hd))
      have h' : g⁻¹ * ((x : SpecialLinearGroup (Fin n) K) * d *
          (x : SpecialLinearGroup (Fin n) K)⁻¹) * g = g⁻¹ * d * g := by
        rw [← this]
        group
      simpa using h'
    · intro h d' hd'
      have := h _ ((hD'mem _).mp hd')
      calc (g⁻¹ * (x : SpecialLinearGroup (Fin n) K) * g) * d' *
            (g⁻¹ * (x : SpecialLinearGroup (Fin n) K) * g)⁻¹ =
            g⁻¹ * ((x : SpecialLinearGroup (Fin n) K) * (g * d' * g⁻¹) *
              (x : SpecialLinearGroup (Fin n) K)⁻¹) * g := by group
        _ = g⁻¹ * (g * d' * g⁻¹) * g := by rw [this]
        _ = d' := by group
  have hker : (restrictionAction D B₂).ker = ψ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hρ, hψ]
  have hK' : Nat.card (Multiplicative K) = 2 := by rw [Nat.card_congr Multiplicative.toAdd, hK]
  have hZ2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  let e₂ : Multiplicative K ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hK' hZ2
  let ψbar := QuotientGroup.lift (restrictionAction D B₂).ker ψ hker.le
  let f := ((MulEquiv.prodCongr e₂ e₂).toMonoidHom.comp ψbar).comp
    (QuotientGroup.quotientKerEquivRange (restrictionAction D B₂)).symm.toMonoidHom
  have hψbar : Function.Injective ψbar := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [QuotientGroup.lift_mk] at hq
    rw [QuotientGroup.eq_one_iff, hker]
    exact hq
  have hf : Function.Injective f :=
    (MulEquiv.prodCongr e₂ e₂).injective.comp
      (hψbar.comp (QuotientGroup.quotientKerEquivRange _).symm.injective)
  refine ⟨⟨f, hf⟩, ?_, fun x y => hf ?_⟩
  · have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, hZ2] at this
    omega
  · rw [map_mul, map_mul, mul_comm]

end CFSG.QuasithinUnique
