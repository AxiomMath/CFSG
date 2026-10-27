module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PSp4Lin
public import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSplitSp4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PSp4Core

open CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PSp4Lin
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof
open CFSG.Open
open Matrix

theorem comm_of_isElemAbelian {G : Type} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) {x y : G} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x :=
  congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem isElemAbelian_map {G H : Type} [Group G] [Group H] (f : G →* H) {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  refine ⟨IsMulCommutative.of_setLike_mul_comm ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, comm_of_isElemAbelian hE ha hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]

theorem isElemAbelian_of_map_injective {G H : Type} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p (E.map f)) :
    IsElemAbelian p E := by
  refine ⟨IsMulCommutative.of_setLike_mul_comm ?_, ?_⟩
  · intro a ha b hb
    apply hf
    rw [map_mul, map_mul]
    exact comm_of_isElemAbelian hE ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  · intro x hx
    apply hf
    rw [map_pow, map_one]
    exact hE.2 _ ⟨x, hx, rfl⟩

theorem no_quadratic_of_card_eight {K : Type} [Field K] [Finite K] [CharP K 2] (hcard : Nat.card K = 8)
    (z : K) : z ^ 2 + z + 1 ≠ 0 := by
  intro h
  haveI := Fintype.ofFinite K
  have h8 : z ^ 8 = z := by
    have := FiniteField.pow_card z
    rwa [← Nat.card_eq_fintype_card, hcard] at this
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hz3 : z ^ 3 = 1 := by linear_combination (z - 1) * h
  have hsq : z ^ 2 = z := by
    have : z ^ 8 = z ^ 2 := by
      calc z ^ 8 = (z ^ 3) ^ 2 * z ^ 2 := by ring
        _ = z ^ 2 := by rw [hz3]; ring
    rw [← this, h8]
  have hz : z * (z - 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.1 hz with h0 | h1
  · rw [h0] at h
    norm_num at h
  · have hz1 : z = 1 := sub_eq_zero.1 h1
    rw [hz1] at h
    have : (1 : K) = 0 := by linear_combination h - h2
    exact one_ne_zero this

theorem quad_entries {K : Type} [Field K] {X : Matrix (Fin 2) (Fin 2) K} (hX : X * X + X + 1 = 0) :
    X 0 0 * X 0 0 + X 0 1 * X 1 0 + X 0 0 + 1 = 0 ∧ X 0 0 * X 0 1 + X 0 1 * X 1 1 + X 0 1 = 0 ∧
      X 1 0 * X 0 0 + X 1 1 * X 1 0 + X 1 0 = 0 ∧ X 1 0 * X 0 1 + X 1 1 * X 1 1 + X 1 1 + 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using congrFun (congrFun hX 0) 0
  · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using congrFun (congrFun hX 0) 1
  · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using congrFun (congrFun hX 1) 0
  · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using congrFun (congrFun hX 1) 1

theorem plane_proj_onPlane {K : Type} [Field K] {i : Fin 2} {X : Matrix (Fin 2) (Fin 2) K}
    (h2 : (2 : K) = 0) (v : Fin 2 ⊕ Fin 2 → K) :
    CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PSp4Lin.OnPlane i
      (pairMat (Sum.inl i) (Sum.inr i) X *ᵥ (pairMat (Sum.inl i) (Sum.inr i) X *ᵥ v) +
      pairMat (Sum.inl i) (Sum.inr i) X *ᵥ v) := by
  intro k h1 h2'
  rw [Pi.add_apply, mulVec_pairMat_other X _ h1 h2', mulVec_pairMat_other X v h1 h2']
  linear_combination (v k) * h2

theorem plane_proj_coord {K : Type} [Field K] {i : Fin 2} {X : Matrix (Fin 2) (Fin 2) K}
    (hX : X * X + X + 1 = 0) (h2 : (2 : K) = 0) (v : Fin 2 ⊕ Fin 2 → K) (k : Fin 2 ⊕ Fin 2)
    (hk : k = Sum.inl i ∨ k = Sum.inr i) :
    (pairMat (Sum.inl i) (Sum.inr i) X *ᵥ (pairMat (Sum.inl i) (Sum.inr i) X *ᵥ v) +
      pairMat (Sum.inl i) (Sum.inr i) X *ᵥ v) k = v k := by
  obtain ⟨e00, e01, e10, e11⟩ := quad_entries hX
  rcases hk with rfl | rfl
  · simp only [Pi.add_apply, mulVec_pairMat_inl, mulVec_pairMat_inr]
    linear_combination (v (Sum.inl i)) * e00 + (v (Sum.inr i)) * e01 - (v (Sum.inl i)) * h2
  · simp only [Pi.add_apply, mulVec_pairMat_inl, mulVec_pairMat_inr]
    linear_combination (v (Sum.inl i)) * e10 + (v (Sum.inr i)) * e11 - (v (Sum.inr i)) * h2

theorem mem_planes {i j : Fin 2} (hij : i ≠ j) (m : Fin 2) : m = i ∨ m = j := by
  fin_cases i <;> fin_cases j <;> fin_cases m <;> simp_all

theorem sum_split {K : Type} [Field K] {i j : Fin 2} (hij : i ≠ j) (v : Fin 2 ⊕ Fin 2 → K) :
    v = (fun k => if k = Sum.inl i ∨ k = Sum.inr i then v k else 0) +
      (fun k => if k = Sum.inl j ∨ k = Sum.inr j then v k else 0) := by
  funext k
  rw [Pi.add_apply]
  by_cases hk : k = Sum.inl i ∨ k = Sum.inr i
  · have hk' : ¬ (k = Sum.inl j ∨ k = Sum.inr j) := by
      rintro (h | h) <;> rcases hk with h' | h' <;> subst h' <;>
        simp_all [Sum.inl_injective.eq_iff, Sum.inr_injective.eq_iff]
    simp [hk, hk']
  · have hk' : k = Sum.inl j ∨ k = Sum.inr j := by
      rcases k with m | m
      · rcases mem_planes hij m with h | h
        · exact absurd (Or.inl (by rw [h])) hk
        · exact Or.inl (by rw [h])
      · rcases mem_planes hij m with h | h
        · exact absurd (Or.inr (by rw [h])) hk
        · exact Or.inr (by rw [h])
    simp [hk, hk']

theorem false_of_plane {K : Type} [Field K] [Finite K] (hK : ∀ z : K, z ^ 2 + z + 1 ≠ 0)
    (hev : Even (Nat.card K)) (T : Subgroup (StatedSp 2 K)) (hT : IsPGroup 2 T) (hT0 : T ≠ ⊥)
    {i j : Fin 2} (hij : i ≠ j) {Xj : Matrix (Fin 2) (Fin 2) K}
    (hXj : Xj * Xj + Xj + 1 = 0)
    (hCj : ∀ v ∈ fixSub T, pairMat (Sum.inl j) (Sum.inr j) Xj *ᵥ v ∈ fixSub T)
    (hi : ∀ v, OnPlane i v → v ∈ fixSub T) : False := by
  have hfix : ∀ t ∈ T, ∀ v, OnPlane i v → mat t *ᵥ v = v := fun t ht v hv => hi v hv t ht
  have hpl : ∀ t ∈ T, ∀ v, OnPlane j v → OnPlane j (mat t *ᵥ v) :=
    fun t ht v hv => onPlane_of_fixes hij (fun v' hv' => hfix t ht v' hv') hv
  letI := planeMulAction T j hpl
  have hevj : Even (Nat.card {v : Fin 2 ⊕ Fin 2 → K // OnPlane j v}) := by
    rw [natCard_onPlane j]
    exact Nat.even_pow.2 ⟨hev, two_ne_zero⟩
  obtain ⟨u, hune, hufix⟩ := exists_fixed_ne hT hevj ⟨0, onPlane_zero j⟩
    (fun g => Subtype.ext (by show mat g.1 *ᵥ (0 : Fin 2 ⊕ Fin 2 → K) = 0; simp))
  have hu_mem : u.1 ∈ fixSub T := fun t ht => congrArg Subtype.val (hufix ⟨t, ht⟩)
  have hu0 : u.1 ≠ 0 := fun h => hune (Subtype.ext h)
  have hjall := plane_mem_of_ne_zero j hXj hK (fixSub T) hCj hu_mem u.2 hu0
  have hall : ∀ t ∈ T, ∀ v : Fin 2 ⊕ Fin 2 → K, mat t *ᵥ v = v := by
    intro t ht v
    have hA : OnPlane i (fun k => if k = Sum.inl i ∨ k = Sum.inr i then v k else 0) := by
      intro k h1 h2
      simp [h1, h2]
    have hB : OnPlane j (fun k => if k = Sum.inl j ∨ k = Sum.inr j then v k else 0) := by
      intro k h1 h2
      simp [h1, h2]
    have hsplit := sum_split hij v
    have hmul : mat t *ᵥ v = mat t *ᵥ (fun k => if k = Sum.inl i ∨ k = Sum.inr i then v k else 0) +
        mat t *ᵥ (fun k => if k = Sum.inl j ∨ k = Sum.inr j then v k else 0) := by
      rw [← Matrix.mulVec_add, ← hsplit]
    rw [hmul, hi _ hA t ht, hjall _ hB t ht, ← hsplit]
  apply hT0
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_bot]
  exact mat_eq_one_of_forall (fun v => hall t ht v)

theorem card_le_three_of_normalizes {K : Type} [Field K] [Finite K] [CharP K 2]
    (hcard : Nat.card K = 8)
    {E T : Subgroup (StatedSp 2 K)} (hE : IsElemAbelian 3 E) (hT : IsPGroup 2 T) (hT0 : T ≠ ⊥)
    (hN : ∀ g ∈ E, ∀ t ∈ T, g * t * g⁻¹ ∈ T) : Nat.card E ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : ∀ z : K, z ^ 2 + z + 1 ≠ 0 := no_quadratic_of_card_eight hcard
  have hev : Even (Nat.card K) := ⟨4, by rw [hcard]⟩
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  by_contra hlt
  push Not at hlt
  obtain ⟨S, hS⟩ := exists_sylow_le_range_slPair (K := K)
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨c, hc⟩ := exists_conj_map_le_sylow' S hEp
  obtain ⟨E', hE'def⟩ : ∃ E' : Subgroup (StatedSp 2 K),
      E' = E.map (MulAut.conj c).toMonoidHom := ⟨_, rfl⟩
  obtain ⟨T', hT'def⟩ : ∃ T' : Subgroup (StatedSp 2 K),
      T' = T.map (MulAut.conj c).toMonoidHom := ⟨_, rfl⟩
  have hinj : Function.Injective (MulAut.conj c).toMonoidHom := (MulAut.conj c).injective
  have hE' : IsElemAbelian 3 E' := by rw [hE'def]; exact isElemAbelian_map _ hE
  have hcardE' : Nat.card E' = Nat.card E := by
    rw [hE'def]; exact Subgroup.card_map_of_injective hinj
  have hE'le : E' ≤ (slPair K).range := by rw [hE'def]; exact hc.trans hS
  have hT'0 : T' ≠ ⊥ := by
    intro h
    apply hT0
    rw [eq_bot_iff]
    intro t ht
    have hmem : (MulAut.conj c).toMonoidHom t ∈ T' := by
      rw [hT'def]; exact Subgroup.mem_map_of_mem _ ht
    rw [h, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.2 (hinj (hmem.trans (map_one _).symm))
  have hT'2 : IsPGroup 2 T' := by
    rw [hT'def]
    rintro ⟨x, hx⟩
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨n, hn⟩ := hT ⟨t, ht⟩
    refine ⟨n, Subtype.ext ?_⟩
    show (MulAut.conj c).toMonoidHom t ^ 2 ^ n = 1
    have hn' : t ^ 2 ^ n = 1 := congrArg Subtype.val hn
    rw [← map_pow, hn', map_one]
  have hN' : ∀ g ∈ E', ∀ t ∈ T', g * t * g⁻¹ ∈ T' := by
    intro g hg t ht
    rw [hE'def, Subgroup.mem_map] at hg
    rw [hT'def, Subgroup.mem_map] at ht ⊢
    obtain ⟨g0, hg0, rfl⟩ := hg
    obtain ⟨t0, ht0, rfl⟩ := ht
    exact ⟨g0 * t0 * g0⁻¹, hN g0 hg0 t0 ht0, by simp [map_mul, map_inv]⟩
  obtain ⟨Ê, hÊdef⟩ : ∃ Ê : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K ×
      Matrix.SpecialLinearGroup (Fin 2) K), Ê = E'.comap (slPair K) := ⟨_, rfl⟩
  have hÊmap : Ê.map (slPair K) = E' := by
    rw [hÊdef]; exact Subgroup.map_comap_eq_self hE'le
  have hÊab : IsElemAbelian 3 Ê := by
    apply isElemAbelian_of_map_injective (slPair K) slPair_injective
    rw [hÊmap]; exact hE'
  have hÊcard : Nat.card Ê = Nat.card E' := by
    rw [← hÊmap]; exact (Subgroup.card_map_of_injective slPair_injective).symm
  have hXex : ∃ x : Matrix.SpecialLinearGroup (Fin 2) K, x ≠ 1 ∧
      (x, (1 : Matrix.SpecialLinearGroup (Fin 2) K)) ∈ Ê := by
    by_contra hno
    push Not at hno
    have hmem : ∀ u : Ê, u.1.2 ∈ Ê.map (MonoidHom.snd _ _) := fun u =>
      Subgroup.mem_map.2 ⟨u.1, u.2, rfl⟩
    have hinj : Function.Injective (fun u : Ê => (⟨u.1.2, hmem u⟩ :
          (Ê.map (MonoidHom.snd _ _)))) := by
      intro u v huv
      have huv' : u.1.2 = v.1.2 := congrArg Subtype.val huv
      apply Subtype.ext
      have hw : u.1 * (v.1)⁻¹ ∈ Ê := Ê.mul_mem u.2 (Ê.inv_mem v.2)
      have hq : (u.1 * (v.1)⁻¹).2 = 1 := by
        rw [Prod.snd_mul, Prod.snd_inv, huv', mul_inv_cancel]
      have hp : (u.1 * (v.1)⁻¹).1 = 1 := by
        by_contra hne
        apply hno _ hne
        have hEq : u.1 * (v.1)⁻¹ =
            ((u.1 * (v.1)⁻¹).1, 1) := Prod.ext rfl hq
        rw [← hEq]
        exact hw
      exact mul_inv_eq_one.1 (Prod.ext hp hq)
    have h1 : Nat.card Ê ≤ Nat.card (Ê.map (MonoidHom.snd _ _)) :=
      Nat.card_le_card_of_injective _ hinj
    have h2' := card_le_three_of_elemAbelian_sl2 (isElemAbelian_map (MonoidHom.snd _ _) hÊab)
    omega
  have hYex : ∃ y : Matrix.SpecialLinearGroup (Fin 2) K, y ≠ 1 ∧
      ((1 : Matrix.SpecialLinearGroup (Fin 2) K), y) ∈ Ê := by
    by_contra hno
    push Not at hno
    have hmem : ∀ u : Ê, u.1.1 ∈ Ê.map (MonoidHom.fst _ _) := fun u =>
      Subgroup.mem_map.2 ⟨u.1, u.2, rfl⟩
    have hinj : Function.Injective (fun u : Ê => (⟨u.1.1, hmem u⟩ :
          (Ê.map (MonoidHom.fst _ _)))) := by
      intro u v huv
      have huv' : u.1.1 = v.1.1 := congrArg Subtype.val huv
      apply Subtype.ext
      have hw : u.1 * (v.1)⁻¹ ∈ Ê := Ê.mul_mem u.2 (Ê.inv_mem v.2)
      have hp : (u.1 * (v.1)⁻¹).1 = 1 := by
        rw [Prod.fst_mul, Prod.fst_inv, huv', mul_inv_cancel]
      have hq : (u.1 * (v.1)⁻¹).2 = 1 := by
        by_contra hne
        apply hno _ hne
        have hEq : u.1 * (v.1)⁻¹ =
            (1, (u.1 * (v.1)⁻¹).2) := Prod.ext hp rfl
        rw [← hEq]
        exact hw
      exact mul_inv_eq_one.1 (Prod.ext hp hq)
    have h1 : Nat.card Ê ≤ Nat.card (Ê.map (MonoidHom.fst _ _)) :=
      Nat.card_le_card_of_injective _ hinj
    have h2' := card_le_three_of_elemAbelian_sl2 (isElemAbelian_map (MonoidHom.fst _ _) hÊab)
    omega
  obtain ⟨x, hx1, hxmem⟩ := hXex
  obtain ⟨y, hy1, hymem⟩ := hYex
  have hga : lam (0 : Fin 2) x ∈ E' := by
    have h := Subgroup.mem_map_of_mem (slPair K) hxmem
    rw [hÊmap, slPair_apply, map_one, mul_one] at h
    exact h
  have hgb : lam (1 : Fin 2) y ∈ E' := by
    have h := Subgroup.mem_map_of_mem (slPair K) hymem
    rw [hÊmap, slPair_apply, map_one, one_mul] at h
    exact h
  have hx3 : x ^ 3 = 1 := by
    have h := hE'.2 _ hga
    rw [← map_pow] at h
    exact (lam_eq_one_iff' (0 : Fin 2) (x ^ 3)).1 h
  have hy3 : y ^ 3 = 1 := by
    have h := hE'.2 _ hgb
    rw [← map_pow] at h
    exact (lam_eq_one_iff' (1 : Fin 2) (y ^ 3)).1 h
  have hquad : ∀ z : Matrix.SpecialLinearGroup (Fin 2) K, z ^ 3 = 1 → z ≠ 1 →
      (z : Matrix (Fin 2) (Fin 2) K) * z + z + 1 = 0 := by
    intro z hz3 hz1
    apply quadratic_of_cube (Matrix.SpecialLinearGroup.det_coe z) _
      (fun h => hz1 (Subtype.ext (by simpa using h)))
    have h3 : (z : Matrix (Fin 2) (Fin 2) K) ^ 3 = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, hz3, Matrix.SpecialLinearGroup.coe_one]
    rw [← pow_three']
    exact h3
  have hXa := hquad x hx3 hx1
  have hXb := hquad y hy3 hy1
  have hinv : ∀ g ∈ E', ∀ v ∈ fixSub T', mat g *ᵥ v ∈ fixSub T' := by
    intro g hg v hv
    rw [mem_fixSub] at hv ⊢
    intro t ht
    have h1 : g⁻¹ * t * g⁻¹⁻¹ ∈ T' := hN' g⁻¹ (E'.inv_mem hg) t ht
    have h2'' := hv _ h1
    have hgt : t * g = g * (g⁻¹ * t * g⁻¹⁻¹) := by group
    calc mat t *ᵥ (mat g *ᵥ v) = mat (t * g) *ᵥ v := by rw [mat_mul, Matrix.mulVec_mulVec]
      _ = mat (g * (g⁻¹ * t * g⁻¹⁻¹)) *ᵥ v := by rw [hgt]
      _ = mat g *ᵥ (mat (g⁻¹ * t * g⁻¹⁻¹) *ᵥ v) := by rw [mat_mul, Matrix.mulVec_mulVec]
      _ = mat g *ᵥ v := by rw [h2'']
  have hCa : ∀ v ∈ fixSub T', pairMat (Sum.inl (0 : Fin 2)) (Sum.inr (0 : Fin 2))
      (x : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈ fixSub T' := fun v hv => hinv _ hga v hv
  have hCb : ∀ v ∈ fixSub T', pairMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2))
      (y : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈ fixSub T' := fun v hv => hinv _ hgb v hv
  have hevV : Even (Nat.card (Fin 2 ⊕ Fin 2 → K)) := by
    rw [natCard_vec, hcard]; exact ⟨2048, by norm_num⟩
  obtain ⟨w, hwC, hw0⟩ : ∃ w ∈ fixSub T', w ≠ 0 := by
    letI := vecMulAction T'
    obtain ⟨w, hw0, hwfix⟩ := exists_fixed_ne hT'2 hevV 0
      (fun g => by show mat g.1 *ᵥ (0 : Fin 2 ⊕ Fin 2 → K) = 0; simp)
    exact ⟨w, mem_fixSub.2 (fun t ht => hwfix ⟨t, ht⟩), hw0⟩
  have hu0mem : pairMat (Sum.inl (0 : Fin 2)) (Sum.inr (0 : Fin 2)) (x : Matrix (Fin 2) (Fin 2) K) *ᵥ
      (pairMat (Sum.inl (0 : Fin 2)) (Sum.inr (0 : Fin 2)) (x : Matrix (Fin 2) (Fin 2) K) *ᵥ w) +
        pairMat (Sum.inl (0 : Fin 2)) (Sum.inr (0 : Fin 2)) (x : Matrix (Fin 2) (Fin 2) K) *ᵥ w ∈
          fixSub T' :=
    (fixSub T').add_mem (hCa _ (hCa w hwC)) (hCa w hwC)
  have hu1mem : pairMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2)) (y : Matrix (Fin 2) (Fin 2) K) *ᵥ
      (pairMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2)) (y : Matrix (Fin 2) (Fin 2) K) *ᵥ w) +
        pairMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2)) (y : Matrix (Fin 2) (Fin 2) K) *ᵥ w ∈
          fixSub T' :=
    (fixSub T').add_mem (hCb _ (hCb w hwC)) (hCb w hwC)
  have h2fin : (2 : K) = 0 := h2
  have hu0supp := plane_proj_onPlane (i := (0 : Fin 2)) (X := (x : Matrix (Fin 2) (Fin 2) K)) h2fin w
  have hu1supp := plane_proj_onPlane (i := (1 : Fin 2)) (X := (y : Matrix (Fin 2) (Fin 2) K)) h2fin w
  have hsplit : ∀ k : Fin 2 ⊕ Fin 2, w k = (pairMat (Sum.inl (0 : Fin 2)) (Sum.inr (0 : Fin 2))
        (x : Matrix (Fin 2) (Fin 2) K) *ᵥ (pairMat (Sum.inl (0 : Fin 2)) (Sum.inr (0 : Fin 2))
          (x : Matrix (Fin 2) (Fin 2) K) *ᵥ w) + pairMat (Sum.inl (0 : Fin 2)) (Sum.inr (0 : Fin 2))
          (x : Matrix (Fin 2) (Fin 2) K) *ᵥ w) k + (pairMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2))
          (y : Matrix (Fin 2) (Fin 2) K) *ᵥ (pairMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2))
          (y : Matrix (Fin 2) (Fin 2) K) *ᵥ w) + pairMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2))
          (y : Matrix (Fin 2) (Fin 2) K) *ᵥ w) k := by
    intro k
    have hm : ∀ m : Fin 2, m = 0 ∨ m = 1 := by decide
    by_cases hk : k = Sum.inl 0 ∨ k = Sum.inr 0
    · have hk1 := not_or.1 (show ¬ (k = Sum.inl 1 ∨ k = Sum.inr 1) by
        rcases hk with rfl | rfl <;> simp)
      rw [plane_proj_coord (i := 0) hXa h2fin w k hk, hu1supp k hk1.1 hk1.2, add_zero]
    · have hk' : k = Sum.inl 1 ∨ k = Sum.inr 1 := by
        rcases k with m | m
        · rcases hm m with rfl | rfl
          · exact absurd (Or.inl rfl) hk
          · exact Or.inl rfl
        · rcases hm m with rfl | rfl
          · exact absurd (Or.inr rfl) hk
          · exact Or.inr rfl
      have hk0 := not_or.1 hk
      rw [plane_proj_coord (i := 1) hXb h2fin w k hk', hu0supp k hk0.1 hk0.2, zero_add]
  by_cases hu0 : (pairMat (Sum.inl (0 : Fin 2)) (Sum.inr (0 : Fin 2)) (x : Matrix (Fin 2) (Fin 2) K) *ᵥ
      (pairMat (Sum.inl (0 : Fin 2)) (Sum.inr (0 : Fin 2)) (x : Matrix (Fin 2) (Fin 2) K) *ᵥ w) +
        pairMat (Sum.inl (0 : Fin 2)) (Sum.inr (0 : Fin 2)) (x : Matrix (Fin 2) (Fin 2) K) *ᵥ w) = 0
  · have hu1 : (pairMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2)) (y : Matrix (Fin 2) (Fin 2) K) *ᵥ
        (pairMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2)) (y : Matrix (Fin 2) (Fin 2) K) *ᵥ w) +
          pairMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2)) (y : Matrix (Fin 2) (Fin 2) K) *ᵥ w) ≠ 0 := by
      intro h1
      apply hw0
      funext k
      show w k = 0
      rw [hsplit k, congrFun hu0 k, congrFun h1 k]
      simp
    have hi1 := plane_mem_of_ne_zero (i := 1) hXb hK (fixSub T') hCb hu1mem hu1supp hu1
    exact false_of_plane hK hev T' hT'2 hT'0 (i := 1) (j := 0) (by decide) hXa hCa hi1
  · have hi0 := plane_mem_of_ne_zero (i := 0) hXa hK (fixSub T') hCa hu0mem hu0supp hu0
    exact false_of_plane hK hev T' hT'2 hT'0 (i := 0) (j := 1) (by decide) hXb hCb hi0

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PSp4Core
