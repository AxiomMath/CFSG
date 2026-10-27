module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsLift
public import CFSG.LocalAnalysis.ComponentClassification.Sol76R12Sp4

public section

namespace CFSG.ComponentClassification.Sol76T13.R12.Pcls

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank

section Linear

variable {n : ℕ} {K : Type} [Field K]

@[expose] def slSign (ε : Fin n → K) (hε : ∏ i, ε i = 1) : Matrix.SpecialLinearGroup (Fin n) K :=
  ⟨diagonal ε, by rw [det_diagonal, hε]⟩

theorem slSign_mul (ε δ : Fin n → K) (hε : ∏ i, ε i = 1) (hδ : ∏ i, δ i = 1) :
    slSign ε hε * slSign δ hδ =
      slSign (ε * δ) (by simp only [Pi.mul_apply]; rw [Finset.prod_mul_distrib, hε, hδ, one_mul]) :=
  Subtype.ext (by
    change diagonal ε * diagonal δ = diagonal (ε * δ)
    rw [diagonal_mul_diagonal]
    rfl)

theorem slSign_mul_self {ε : Fin n → K} (hε : ∏ i, ε i = 1) (h2 : ∀ i, ε i * ε i = 1) :
    slSign ε hε * slSign ε hε = 1 := by
  rw [slSign_mul]
  apply Subtype.ext
  change diagonal (ε * ε) = 1
  rw [← diagonal_one]
  congr 1
  funext i
  exact h2 i

theorem slSign_comm (ε δ : Fin n → K) (hε : ∏ i, ε i = 1) (hδ : ∏ i, δ i = 1) :
    slSign ε hε * slSign δ hδ = slSign δ hδ * slSign ε hε := by
  rw [slSign_mul, slSign_mul]
  congr 1
  exact mul_comm ε δ

theorem slSign_not_mem_center {ε : Fin n → K} (hε : ∏ i, ε i = 1) {i j : Fin n}
    (hij : ε i ≠ ε j) : slSign ε hε ∉ center (Matrix.SpecialLinearGroup (Fin n) K) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  rintro ⟨r, -, hr⟩
  have hi := congrFun (congrFun hr i) i
  have hj := congrFun (congrFun hr j) j
  simp only [scalar_apply, diagonal_apply_eq] at hi hj
  change r = (diagonal ε) i i at hi
  change r = (diagonal ε) j j at hj
  rw [diagonal_apply_eq] at hi hj
  exact hij (hi.symm.trans hj)

theorem eq_one_or_neg_one_of_mul_self_sl2 (h2 : (2 : K) ≠ 0)
    {A : Matrix.SpecialLinearGroup (Fin 2) K} (hA : A * A = 1) : A = 1 ∨ A = -1 := by
  have hdet := A.prop
  rw [det_fin_two] at hdet
  have hm := congrArg
    (fun B : Matrix.SpecialLinearGroup (Fin 2) K => (B : Matrix (Fin 2) (Fin 2) K)) hA
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at hm
  have h00 := congrFun (congrFun hm 0) 0
  have h01 := congrFun (congrFun hm 0) 1
  have h10 := congrFun (congrFun hm 1) 0
  have h11 := congrFun (congrFun hm 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  set a := (A : Matrix (Fin 2) (Fin 2) K) 0 0
  set b := (A : Matrix (Fin 2) (Fin 2) K) 0 1
  set c := (A : Matrix (Fin 2) (Fin 2) K) 1 0
  set d := (A : Matrix (Fin 2) (Fin 2) K) 1 1
  have htr : a + d ≠ 0 := by
    intro htr
    have hd : d = -a := by linear_combination htr
    rw [hd] at hdet
    apply h2
    linear_combination -h00 - hdet
  have hb : b = 0 := by
    have : b * (a + d) = 0 := by linear_combination h01
    exact (mul_eq_zero.mp this).resolve_right htr
  have hc : c = 0 := by
    have : c * (a + d) = 0 := by linear_combination h10
    exact (mul_eq_zero.mp this).resolve_right htr
  rw [hb, hc] at hdet h00 h11
  have had : a = d := by
    have h1 : a * a = 1 := by linear_combination h00
    have h2' : a * d = 1 := by linear_combination hdet
    have : a * (a - d) = 0 := by linear_combination h1 - h2'
    have ha0 : a ≠ 0 := fun h => by rw [h, zero_mul] at h1; exact zero_ne_one h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha0)
  have ha2 : a * a = 1 := by linear_combination h00
  rcases mul_self_eq_one_iff.mp ha2 with ha | ha
  · left
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a, b, c, d, ← had, ha, hb, hc] at *
  · right
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a, b, c, d, ← had, ha, hb, hc] at *

theorem prod_update_neg_one (i : Fin n) :
    ∏ j, (Function.update (1 : Fin n → K) i (-1)) j = -1 := by
  rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

theorem exists_sign_pair (hn : 3 ≤ n) (hn1 : (-1 : K) ≠ 1) :
    ∃ (ε δ : Fin n → K) (_ : ∏ i, ε i = 1) (_ : ∏ i, δ i = 1),
      (∀ i, ε i * ε i = 1) ∧ (∀ i, δ i * δ i = 1) ∧
      (∃ i j, ε i ≠ ε j) ∧ (∃ i j, δ i ≠ δ j) ∧ ∃ i j, (ε * δ) i ≠ (ε * δ) j := by
  set s : Fin n → (Fin n → K) := fun i => Function.update 1 i (-1) with hs
  have hs2 : ∀ i j, s i j * s i j = 1 := fun i j => by
    simp only [hs, Function.update_apply]
    split_ifs <;> simp
  have hval : ∀ i l, s i l = if l = i then -1 else 1 := fun i l => by
    simp only [hs, Function.update_apply, Pi.one_apply]
  have hpair : ∀ i j, ∏ l, (s i * s j) l = 1 := fun i j => by
    simp only [Pi.mul_apply]
    rw [Finset.prod_mul_distrib, prod_update_neg_one, prod_update_neg_one]
    ring
  have hsq : ∀ i j l, (s i * s j) l * (s i * s j) l = 1 := fun i j l => by
    simp only [Pi.mul_apply]
    calc s i l * s j l * (s i l * s j l) = (s i l * s i l) * (s j l * s j l) := by ring
      _ = 1 := by rw [hs2, hs2, one_mul]
  have hnc : ∀ {i j l : Fin n}, i ≠ j → l ≠ i → l ≠ j → (s i * s j) i ≠ (s i * s j) l := by
    intro i j l hij hli hlj
    have hi' : (s i * s j) i = -1 := by simp [hval, hij]
    have hl' : (s i * s j) l = 1 := by simp [hval, hli, hlj]
    rw [hi', hl']
    exact hn1
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  set i2 : Fin n := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  have hprod : s i0 * s i1 * (s i0 * s i2) = s i1 * s i2 := by
    funext l
    simp only [Pi.mul_apply]
    calc s i0 l * s i1 l * (s i0 l * s i2 l) = (s i0 l * s i0 l) * (s i1 l * s i2 l) := by ring
      _ = s i1 l * s i2 l := by rw [hs2, one_mul]
  refine ⟨s i0 * s i1, s i0 * s i2, hpair i0 i1, hpair i0 i2, hsq i0 i1, hsq i0 i2,
    ⟨i0, i2, hnc h01 h02.symm h12.symm⟩, ⟨i0, i1, hnc h02 h01.symm h12⟩, ?_⟩
  rw [hprod]
  exact ⟨i1, i0, hnc h12 h01 h02⟩

end Linear

section Symplectic

variable {r : ℕ} {K : Type} [Field K]

@[expose] noncomputable def spSign (ε : Fin r → K) (hε : ∏ i, ε i = 1) : StatedSp r K :=
  LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.leviSp
    (Matrix.SpecialLinearGroup.toGL (slSign ε hε))

theorem spSign_mul (ε δ : Fin r → K) (hε : ∏ i, ε i = 1) (hδ : ∏ i, δ i = 1) :
    spSign ε hε * spSign δ hδ =
      spSign (ε * δ) (by simp only [Pi.mul_apply]; rw [Finset.prod_mul_distrib, hε, hδ, one_mul]) :=
  by rw [spSign, spSign, spSign, ← map_mul, ← map_mul, slSign_mul]

theorem spSign_mul_self {ε : Fin r → K} (hε : ∏ i, ε i = 1) (h2 : ∀ i, ε i * ε i = 1) :
    spSign ε hε * spSign ε hε = 1 := by
  rw [spSign, ← map_mul, ← map_mul, slSign_mul_self hε h2, map_one, map_one]

theorem spSign_comm (ε δ : Fin r → K) (hε : ∏ i, ε i = 1) (hδ : ∏ i, δ i = 1) :
    spSign ε hε * spSign δ hδ = spSign δ hδ * spSign ε hε := by
  rw [spSign, spSign, ← map_mul, ← map_mul, slSign_comm, map_mul, map_mul]

theorem spSign_not_mem_scalars {ε : Fin r → K} (hε : ∏ i, ε i = 1) {i j : Fin r}
    (hij : ε i ≠ ε j) :
    spSign ε hε ∉ (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K) := by
  rw [Subgroup.mem_subgroupOf]
  rintro ⟨c, hc⟩
  have hm := congrArg (fun g : GL (Fin r ⊕ Fin r) K => (g : Matrix (Fin r ⊕ Fin r)
    (Fin r ⊕ Fin r) K)) hc
  have hi := congrFun (congrFun hm (.inl i)) (.inl i)
  have hj := congrFun (congrFun hm (.inl j)) (.inl j)
  simp only [spSign, LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.coe_leviSp,
    fromBlocks_apply₁₁] at hi hj
  change _ = (diagonal ε) i i at hi
  change _ = (diagonal ε) j j at hj
  simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map] at hi hj
  change Matrix.scalar (Fin r ⊕ Fin r) (c : K) (.inl i) (.inl i) = diagonal ε i i at hi
  change Matrix.scalar (Fin r ⊕ Fin r) (c : K) (.inl j) (.inl j) = diagonal ε j j at hj
  simp only [scalar_apply, diagonal_apply_eq] at hi hj
  exact hij (hi.symm.trans hj)

end Symplectic

section Covers

variable {Q : Type} [Group Q]

theorem ker_quotientMap {S : Type*} [Group S] (e : Q ⧸ center Q ≃* S) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (center Q))).ker = center Q := by
  ext y
  rw [MonoidHom.mem_ker]
  change e (QuotientGroup.mk y) = 1 ↔ _
  rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]

theorem surjective_of_lift {G S : Type*} [Group G] [Group S] (hperf : Group.IsPerfect Q)
    {πG : G →* S} {πQ : Q →* S} (hπG : Function.Surjective πG) (hkerQ : πQ.ker ≤ center Q)
    {τ : G →* Q} (hτ : ∀ g, πQ (τ g) = πG g) : Function.Surjective τ := by
  have hτZ : ∀ y : Q, ∃ x : G, ∃ c ∈ center Q, y = τ x * c := by
    intro y
    obtain ⟨x, hx⟩ := hπG (πQ y)
    refine ⟨x, (τ x)⁻¹ * y, hkerQ (MonoidHom.mem_ker.mpr ?_), by group⟩
    rw [map_mul, map_inv, hτ, hx, inv_mul_cancel]
  have hle : commutator Q ≤ τ.range := by
    refine commutator_le.mpr fun y₁ _ y₂ _ => ?_
    obtain ⟨x₁, c₁, hc₁, rfl⟩ := hτZ y₁
    obtain ⟨x₂, c₂, hc₂, rfl⟩ := hτZ y₂
    rw [commutatorElement_mul_central hc₁ hc₂, ← map_commutatorElement]
    exact ⟨_, rfl⟩
  rw [Group.IsPerfect.commutator_eq_top, top_le_iff] at hle
  exact MonoidHom.range_eq_top.mp hle

theorem three_le_pRank_of_PSL [Finite Q] (hO : pPrimeCore 2 Q = ⊥) {z : Q} (hzZ : z ∈ center Q)
    (hz2 : orderOf z = 2) {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (e : Q ⧸ center Q ≃* StatedProj (StatedSL n K)) :
    3 ≤ CFSG.pRank 2 Q := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set πQ := e.toMonoidHom.comp (QuotientGroup.mk' (center Q)) with hπQ
  have hπQs : Function.Surjective πQ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerQ := ker_quotientMap e
  have h2 : IsPGroup 2 πQ.ker := hkerQ ▸ isPGroup_center_of_pPrimeCore_eq_bot hO
  set πG : Matrix.SpecialLinearGroup (Fin (m + 1)) K →* StatedProj (StatedSL (m + 1) K) :=
    (projectiveSpecialLinearGroupEquivStatedProj (m + 1) K).toMonoidHom.comp
      (QuotientGroup.mk' (center _)) with hπG
  have hπG1 : ∀ x, πG x = 1 ↔ x ∈ center (Matrix.SpecialLinearGroup (Fin (m + 1)) K) := by
    intro x
    rw [hπG, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨σ, hσ, -, -⟩ := LieType.Steinberg.sl_central_two_extension_splitting m hK
    (pullbackFst_surjective (πG := πG) hπQs) (pullbackFst_ker_le_center hkerQ.le)
    (isPGroup_pullbackFst_ker h2)
  obtain ⟨τ, hτ⟩ := exists_lift_of_section hσ
  obtain ⟨ε, δ, hε, hδ, hε2, hδ2, ⟨i, j, hij⟩, ⟨i', j', hij'⟩, ⟨i'', j'', hij''⟩⟩ :=
    exists_sign_pair hn (Ring.neg_one_ne_one_of_char_ne_two hK)
  have hz1 : z ≠ 1 := by rintro rfl; rw [orderOf_one] at hz2; omega
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  refine three_le_pRank_of_four_group hτ (slSign_mul_self hε hε2) (slSign_mul_self hδ hδ2)
    (slSign_comm _ _ _ _) ?_ ?_ ?_ hzZ hzz hz1 (by rw [← MonoidHom.mem_ker, hkerQ]; exact hzZ)
  · rw [Ne, hπG1]; exact slSign_not_mem_center hε hij
  · rw [Ne, hπG1]; exact slSign_not_mem_center hδ hij'
  · rw [slSign_mul, Ne, hπG1]; exact slSign_not_mem_center _ hij''

theorem three_le_pRank_of_PSp [Finite Q] (hO : pPrimeCore 2 Q = ⊥) {z : Q} (hzZ : z ∈ center Q)
    (hz2 : orderOf z = 2) {r : ℕ} (hr : 3 ≤ r) {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (e : Q ⧸ center Q ≃* StatedProj (StatedSp r K)) :
    3 ≤ CFSG.pRank 2 Q := by
  set πQ := e.toMonoidHom.comp (QuotientGroup.mk' (center Q)) with hπQ
  have hπQs : Function.Surjective πQ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerQ := ker_quotientMap e
  have h2 : IsPGroup 2 πQ.ker := hkerQ ▸ isPGroup_center_of_pPrimeCore_eq_bot hO
  set πG : StatedSp r K →* StatedProj (StatedSp r K) := QuotientGroup.mk' _ with hπG
  have hπG1 : ∀ x, πG x = 1 ↔ x ∈ (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K) :=
    fun x => by rw [hπG, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨σ, hσ, -, -⟩ := LieType.Steinberg.odd_symplectic_central_two_extension_splitting hK r
    (pullbackFst_surjective (πG := πG) hπQs) (pullbackFst_ker_le_center hkerQ.le)
    (isPGroup_pullbackFst_ker h2)
  obtain ⟨τ, hτ⟩ := exists_lift_of_section hσ
  obtain ⟨ε, δ, hε, hδ, hε2, hδ2, ⟨i, j, hij⟩, ⟨i', j', hij'⟩, ⟨i'', j'', hij''⟩⟩ :=
    exists_sign_pair hr (Ring.neg_one_ne_one_of_char_ne_two hK)
  have hz1 : z ≠ 1 := by rintro rfl; rw [orderOf_one] at hz2; omega
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  refine three_le_pRank_of_four_group hτ (spSign_mul_self hε hε2) (spSign_mul_self hδ hδ2)
    (spSign_comm _ _ _ _) ?_ ?_ ?_ hzZ hzz hz1 (by rw [← MonoidHom.mem_ker, hkerQ]; exact hzZ)
  · rw [Ne, hπG1]; exact spSign_not_mem_scalars hε hij
  · rw [Ne, hπG1]; exact spSign_not_mem_scalars hδ hij'
  · rw [spSign_mul, Ne, hπG1]; exact spSign_not_mem_scalars _ hij''

theorem pRank_le_one_of_PSL_two [Finite Q] (hQ : IsQuasisimple Q) (hO : pPrimeCore 2 Q = ⊥) {z : Q}
    (hzZ : z ∈ center Q) (hz2 : orderOf z = 2) {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (e : Q ⧸ center Q ≃* StatedProj (StatedSL 2 K)) :
    CFSG.pRank 2 Q ≤ 1 := by
  set πQ := e.toMonoidHom.comp (QuotientGroup.mk' (center Q)) with hπQ
  have hπQs : Function.Surjective πQ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerQ := ker_quotientMap e
  have h2 : IsPGroup 2 πQ.ker := hkerQ ▸ isPGroup_center_of_pPrimeCore_eq_bot hO
  set πG : Matrix.SpecialLinearGroup (Fin 2) K →* StatedProj (StatedSL 2 K) :=
    (projectiveSpecialLinearGroupEquivStatedProj 2 K).toMonoidHom.comp
      (QuotientGroup.mk' (center _)) with hπG
  have hπGs : Function.Surjective πG :=
    (projectiveSpecialLinearGroupEquivStatedProj 2 K).surjective.comp
      (QuotientGroup.mk'_surjective _)
  have hπG1 : ∀ x, πG x = 1 ↔ x ∈ center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    intro x
    rw [hπG, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨σ, hσ, -, -⟩ := LieType.Steinberg.sl_central_two_extension_splitting 1 hK
    (pullbackFst_surjective (πG := πG) hπQs) (pullbackFst_ker_le_center hkerQ.le)
    (isPGroup_pullbackFst_ker h2)
  obtain ⟨τ, hτ⟩ : ∃ τ : Matrix.SpecialLinearGroup (Fin 2) K →* Q, ∀ g, πQ (τ g) = πG g :=
    exists_lift_of_section hσ
  have hτs : Function.Surjective τ := surjective_of_lift hQ.1 hπGs hkerQ.le hτ
  have h2K : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hcen : ∀ x ∈ center (Matrix.SpecialLinearGroup (Fin 2) K), x = 1 ∨ x = -1 := by
    intro x hx
    rw [Matrix.SpecialLinearGroup.mem_center_iff] at hx
    obtain ⟨r, hr, hrx⟩ := hx
    rw [Fintype.card_fin] at hr
    have hr' : r * r = 1 := by rw [← pow_two]; exact hr
    rcases mul_self_eq_one_iff.mp hr' with rfl | rfl
    · left; exact Subtype.ext (by rw [← hrx]; simp)
    · right
      refine Subtype.ext ?_
      rw [← hrx, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
      ext i j
      by_cases h : i = j <;> simp [h]
  have hτinj : Function.Injective τ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxc : x ∈ center _ := (hπG1 x).mp (by rw [← hτ, MonoidHom.mem_ker.mp hx, map_one])
    rcases hcen x hxc with rfl | rfl
    · exact one_mem _
    · exfalso
      have hτm : τ (-1) = 1 := hx
      have hZ : ∀ y ∈ center Q, y = 1 := by
        intro y hy
        obtain ⟨w, rfl⟩ := hτs y
        have hw : w ∈ center _ := (hπG1 w).mp (by
          rw [← hτ]; exact MonoidHom.mem_ker.mp (hkerQ ▸ hy))
        rcases hcen w hw with rfl | rfl
        · exact map_one τ
        · exact hτm
      exact (show z ≠ 1 by rintro rfl; rw [orderOf_one] at hz2; omega) (hZ z hzZ)
  refine pRank_le_one_of_sq_eq_one_mem (H := zpowers (τ (-1))) ?_ ?_
  · rw [Nat.card_zpowers]
    refine orderOf_le_of_pow_eq_one (by norm_num) ?_
    rw [← map_pow, pow_two, neg_mul_neg, mul_one, map_one]
  · intro y hy
    obtain ⟨x, rfl⟩ := hτs y
    have hx2 : x * x = 1 := hτinj (by rw [map_mul, ← pow_two, hy, map_one])
    rcases eq_one_or_neg_one_of_mul_self_sl2 h2K hx2 with rfl | rfl
    · rw [map_one]; exact one_mem _
    · exact mem_zpowers _

end Covers

end CFSG.ComponentClassification.Sol76T13.R12.Pcls
