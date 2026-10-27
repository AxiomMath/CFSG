module

public import CFSG.LocalAnalysis.SectionRank.OddCover.UnitaryThree

public section

namespace CFSG.SectionRank.OddCover

open scoped commutatorElement Pointwise

section Products

variable {G : Type*} [Group G]

theorem card_sup_le_of_le_normalizer [Finite G] {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ B) ≤ Nat.card A * Nat.card B := by
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left A B h
  let f : A × B → ↥(A ⊔ B) := fun q => ⟨q.1 * q.2,
    Subgroup.mul_mem _ (Subgroup.mem_sup_left q.1.2) (Subgroup.mem_sup_right q.2.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨g, hg⟩
    have hg' : g ∈ ((A : Set G) * (B : Set G)) := by rw [← hset]; exact hg
    obtain ⟨a, ha, b, hb, rfl⟩ := hg'
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  calc Nat.card ↥(A ⊔ B) ≤ Nat.card (A × B) := Nat.card_le_card_of_surjective f hf
    _ = Nat.card A * Nat.card B := Nat.card_prod _ _

theorem mem_normalizer_of_involution {A : Subgroup G} {u : G} (hu : u * u = 1)
    (h : ∀ g ∈ A, u * g * u⁻¹ ∈ A) : u ∈ Subgroup.normalizer (A : Set G) := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨h g, fun hg => ?_⟩
  have := h _ hg
  rwa [huinv, show u * (u * g * u) * u = (u * u) * g * (u * u) by group, hu, one_mul,
    mul_one] at this

theorem card_closure_pair_le_of_commute [Finite G] {x y : G} (hxy : x * y = y * x) {e : ℕ}
    (he : 0 < e) (hx : x ^ e = 1) (hy : y ^ e = 1) :
    Nat.card (Subgroup.closure ({x, y} : Set G)) ≤ e ^ 2 := by
  have hcl : Subgroup.closure ({x, y} : Set G) = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure,
      Subgroup.zpowers_eq_closure]
  have hn : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      simp only
      rw [← conj_zpow, show y * x * y⁻¹ = x by rw [← hxy]; group]
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      simp only at hk ⊢
      have h1 : y * x ^ k * y⁻¹ = x ^ k := by
        rw [← conj_zpow, show y * x * y⁻¹ = x by rw [← hxy]; group]
      rw [← h1] at hk
      exact mul_left_cancel (mul_right_cancel hk)
  rw [hcl]
  calc Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y)
      ≤ Nat.card (Subgroup.zpowers x) * Nat.card (Subgroup.zpowers y) :=
        card_sup_le_of_le_normalizer hn
    _ ≤ e * e := by
        rw [Nat.card_zpowers, Nat.card_zpowers]
        exact Nat.mul_le_mul (orderOf_le_of_pow_eq_one he hx) (orderOf_le_of_pow_eq_one he hy)
    _ = e ^ 2 := (sq e).symm

theorem card_closure_involutions_le_six [Finite G] {u v : G} (hu : u * u = 1) (hv : v * v = 1)
    (huv : (u * v) ^ 3 = 1) : Nat.card (Subgroup.closure ({u, v} : Set G)) ≤ 6 := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  set w := u * v with hwdef
  have hle : Subgroup.closure ({u, v} : Set G) ≤ Subgroup.zpowers w ⊔ Subgroup.zpowers u := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers _), ?_⟩
    have : v = u * w := by rw [hwdef, ← mul_assoc, hu, one_mul]
    rw [SetLike.mem_coe, this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have huw : u * w * u⁻¹ = w⁻¹ := by
    rw [huinv, hwdef, mul_inv_rev, inv_eq_of_mul_eq_one_right hv, huinv,
      show u * (u * v) * u = (u * u) * v * u by group, hu, one_mul]
  have hn : Subgroup.zpowers u ≤ Subgroup.normalizer (Subgroup.zpowers w : Set G) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_involution hu fun g hg => ?_
    obtain ⟨k, rfl⟩ := hg
    simp only
    rw [← conj_zpow, huw, inv_zpow']
    exact Subgroup.zpow_mem_zpowers _ _
  calc Nat.card (Subgroup.closure ({u, v} : Set G))
      ≤ Nat.card ↥(Subgroup.zpowers w ⊔ Subgroup.zpowers u) := Subgroup.card_le_of_le hle
    _ ≤ Nat.card (Subgroup.zpowers w) * Nat.card (Subgroup.zpowers u) :=
        card_sup_le_of_le_normalizer hn
    _ ≤ 3 * 2 := by
        rw [Nat.card_zpowers, Nat.card_zpowers]
        exact Nat.mul_le_mul (orderOf_le_of_pow_eq_one (by norm_num) huv)
          (orderOf_le_of_pow_eq_one (by norm_num) (by rw [sq, hu]))
    _ = 6 := by norm_num

end Products

section Lift

variable {E G : Type*} [Group E] [Group G] {π : E →* G}

theorem exists_monomial_lift [Finite E] (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) {a b s₀₁ s₀₂ s₁₂ : G}
    (h01 : s₀₁ ^ 2 = 1) (h02 : s₀₂ ^ 2 = 1) (h12 : s₁₂ ^ 2 = 1) (hab : a * b = b * a)
    (ha : s₀₂ * a * s₀₂⁻¹ = a⁻¹) (hb : s₁₂ * b * s₁₂⁻¹ = b⁻¹) (hab' : s₀₁ * a * s₀₁⁻¹ = b)
    (ha12 : s₁₂ * a * s₁₂⁻¹ = a * b⁻¹) (h0102 : s₀₁ * s₀₂ * s₀₁⁻¹ = s₁₂)
    (h1202 : s₁₂ * s₀₂ * s₁₂⁻¹ = s₀₁) (hw : (s₀₁ * s₁₂) ^ 3 = 1) {e : ℕ} (he : 0 < e)
    (hae : a ^ e = 1) (hbe : b ^ e = 1) :
    ∃ N : Subgroup E, N.map π =
        Subgroup.closure ({a, b} : Set G) ⊔ Subgroup.closure ({s₀₁, s₁₂} : Set G) ∧
      Nat.card N ≤ 6 * e ^ 2 := by
  classical
  obtain ⟨u, ⟨hu2, hu⟩, -⟩ := existsUnique_involution_lift hπ hC hodd h01
  obtain ⟨v, ⟨hv2, hv⟩, -⟩ := existsUnique_involution_lift hπ hC hodd h12
  obtain ⟨s, ⟨hs2, hs⟩, -⟩ := existsUnique_involution_lift hπ hC hodd h02
  have hsa : π s * a * (π s)⁻¹ = a⁻¹ := by rw [hs]; exact ha
  have hvb : π v * b * (π v)⁻¹ = b⁻¹ := by rw [hv]; exact hb
  obtain ⟨x, ⟨hx, hxs⟩, -⟩ := existsUnique_inverted_lift hπ hC hodd s hsa
  obtain ⟨y, ⟨hy, hyv⟩, -⟩ := existsUnique_inverted_lift hπ hC hodd v hvb
  have hu' : u * u = 1 := by rw [← sq, hu2]
  have hv' : v * v = 1 := by rw [← sq, hv2]
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu'
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv'
  have hcsq : ∀ t g : E, g ^ 2 = 1 → (t * g * t⁻¹) ^ 2 = 1 := fun t g hg => by
    rw [conj_pow, hg, mul_one, mul_inv_cancel]
  have hA : u * s * u⁻¹ = v :=
    (existsUnique_involution_lift hπ hC hodd h12).unique
      ⟨hcsq u s hs2, by rw [map_mul, map_mul, map_inv, hu, hs, h0102]⟩ ⟨hv2, hv⟩
  have hF : v * s * v⁻¹ = u :=
    (existsUnique_involution_lift hπ hC hodd h01).unique
      ⟨hcsq v s hs2, by rw [map_mul, map_mul, map_inv, hv, hs, h1202]⟩ ⟨hu2, hu⟩
  have hB : u * x * u⁻¹ = y := by
    refine (existsUnique_inverted_lift hπ hC hodd v hvb).unique ⟨?_, ?_⟩ ⟨hy, hyv⟩
    · rw [map_mul, map_mul, map_inv, hu, hx, hab']
    · rw [← hA]
      calc u * s * u⁻¹ * (u * x * u⁻¹) * (u * s * u⁻¹)⁻¹ = u * (s * x * s⁻¹) * u⁻¹ := by group
        _ = (u * x * u⁻¹)⁻¹ := by rw [hxs]; group
  have hB' : u * y * u⁻¹ = x := by
    rw [← hB, show u * (u * x * u⁻¹) * u⁻¹ = (u * u) * x * (u * u)⁻¹ by group, hu', one_mul,
      inv_one, mul_one]
  have hxy : x * y = y * x := by
    have hzk : ⁅x, y⁆ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, hx, hy,
        commutatorElement_eq_one_iff_mul_comm]
      exact hab
    have hz : u * ⁅x, y⁆ * u⁻¹ = ⁅x, y⁆⁻¹ := by
      rw [commutatorElement_inv]
      calc u * ⁅x, y⁆ * u⁻¹ = ⁅u * x * u⁻¹, u * y * u⁻¹⁆ := by
            simp only [commutatorElement_def]; group
        _ = ⁅y, x⁆ := by rw [hB, hB']
    have h1 := eq_one_of_sq_eq_one_of_odd (sq_eq_one_of_conj_eq_inv (hC hzk) hz)
      (odd_orderOf_of_mem hodd hzk)
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have h1s : π s * 1 * (π s)⁻¹ = (1 : G)⁻¹ := by simp
  have hxe : x ^ e = 1 :=
    (existsUnique_inverted_lift hπ hC hodd s h1s).unique
      ⟨by rw [map_pow, hx, hae], by rw [← conj_pow, hxs, inv_pow]⟩ ⟨map_one π, by simp⟩
  have h1v : π v * 1 * (π v)⁻¹ = (1 : G)⁻¹ := by simp
  have hye : y ^ e = 1 :=
    (existsUnique_inverted_lift hπ hC hodd v h1v).unique
      ⟨by rw [map_pow, hy, hbe], by rw [← conj_pow, hyv, inv_pow]⟩ ⟨map_one π, by simp⟩
  have hba : s₀₁ * b * s₀₁⁻¹ = a := by
    rw [← hab', show s₀₁ * (s₀₁ * a * s₀₁⁻¹) * s₀₁⁻¹ = (s₀₁ * s₀₁) * a * (s₀₁ * s₀₁)⁻¹ by group,
      ← sq, h01, one_mul, inv_one, mul_one]
  have hua : π u * (a * b⁻¹) * (π u)⁻¹ = (a * b⁻¹)⁻¹ := by
    rw [hu]
    calc s₀₁ * (a * b⁻¹) * s₀₁⁻¹ = (s₀₁ * a * s₀₁⁻¹) * (s₀₁ * b * s₀₁⁻¹)⁻¹ := by group
      _ = (a * b⁻¹)⁻¹ := by rw [hab', hba]; group
  have hG : v * x * v⁻¹ = x * y⁻¹ := by
    refine (existsUnique_inverted_lift hπ hC hodd u hua).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · rw [map_mul, map_mul, map_inv, hv, hx, ha12]
    · rw [← hF]
      calc v * s * v⁻¹ * (v * x * v⁻¹) * (v * s * v⁻¹)⁻¹ = v * (s * x * s⁻¹) * v⁻¹ := by group
        _ = (v * x * v⁻¹)⁻¹ := by rw [hxs]; group
    · rw [map_mul, map_inv, hx, hy]
    · calc u * (x * y⁻¹) * u⁻¹ = (u * x * u⁻¹) * (u * y * u⁻¹)⁻¹ := by group
        _ = (x * y⁻¹)⁻¹ := by rw [hB, hB']; group
  have hI : (u * v) ^ 3 = 1 := by
    have hck : (u * v) ^ 3 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, map_mul, hu, hv, hw]
    have h1 : u * (u * v) * u⁻¹ = (u * v)⁻¹ := by
      rw [huinv, mul_inv_rev, huinv, hvinv, show u * (u * v) * u = (u * u) * v * u by group, hu',
        one_mul]
    have hc : u * (u * v) ^ 3 * u⁻¹ = ((u * v) ^ 3)⁻¹ := by rw [← conj_pow, h1, inv_pow]
    exact eq_one_of_sq_eq_one_of_odd (sq_eq_one_of_conj_eq_inv (hC hck) hc)
      (odd_orderOf_of_mem hodd hck)
  set T := Subgroup.closure ({x, y} : Set E) with hTdef
  set W := Subgroup.closure ({u, v} : Set E) with hWdef
  have hxT : x ∈ T := Subgroup.subset_closure (by simp)
  have hyT : y ∈ T := Subgroup.subset_closure (by simp)
  have huT : u ∈ Subgroup.normalizer (T : Set E) :=
    mem_normalizer_of_involution hu' fun g hg =>
      conj_mem_closure_pair (by rw [hB]; exact hyT) (by rw [hB']; exact hxT) hg
  have hvT : v ∈ Subgroup.normalizer (T : Set E) :=
    mem_normalizer_of_involution hv' fun g hg =>
      conj_mem_closure_pair (by rw [hG]; exact T.mul_mem hxT (T.inv_mem hyT))
        (by rw [hyv]; exact T.inv_mem hyT) hg
  have hWT : W ≤ Subgroup.normalizer (T : Set E) := by
    rw [hWdef, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨huT, hvT⟩
  refine ⟨T ⊔ W, ?_, ?_⟩
  · rw [Subgroup.map_sup, hTdef, hWdef, MonoidHom.map_closure, MonoidHom.map_closure,
      Set.image_pair, Set.image_pair, hx, hy, hu, hv]
  · calc Nat.card ↥(T ⊔ W) ≤ Nat.card T * Nat.card W := card_sup_le_of_le_normalizer hWT
      _ ≤ e ^ 2 * 6 := Nat.mul_le_mul (card_closure_pair_le_of_commute hxy he hxe hye)
          (card_closure_involutions_le_six hu' hv' hI)
      _ = 6 * e ^ 2 := mul_comm _ _

end Lift

section Monomial

open Matrix CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

theorem s01GL_conj_s02GL : (s01GL : GL (Fin 3) K) * s02GL * s01GL⁻¹ = s12GL := by
  apply Units.ext
  rw [s01GL_inv, Units.val_mul, Units.val_mul, coe_s01GL, coe_s02GL, coe_s12GL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s01Mat, s02Mat, s12Mat, Matrix.mul_apply, Fin.sum_univ_three]

theorem s12GL_conj_s02GL : (s12GL : GL (Fin 3) K) * s02GL * s12GL⁻¹ = s01GL := by
  apply Units.ext
  rw [s12GL_inv, Units.val_mul, Units.val_mul, coe_s01GL, coe_s02GL, coe_s12GL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s01Mat, s02Mat, s12Mat, Matrix.mul_apply, Fin.sum_univ_three]

theorem s01GL_not_mem_torus3_sup_cyc [Finite K] (M : Subgroup Kˣ) :
    (s01GL : GL (Fin 3) K) ∉ torus3 M ⊔ Subgroup.zpowers cycGL := by
  intro h
  obtain ⟨t, ht, j, hj, heq⟩ := exists_mem_torus3_mul_cyc M h
  obtain ⟨d, -, -, rfl⟩ := (mem_torus3 M).1 ht
  interval_cases j
  · have h00 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) heq
    simp [coe_s01GL, s01Mat, coe_diagHom] at h00
    exact (d 0).ne_zero h00.symm
  · have h22 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 2 2) heq
    simp [coe_s01GL, s01Mat, coe_diagHom, coe_cycGL, cycMat, Matrix.mul_apply,
      Fin.sum_univ_three] at h22
  · have h22 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 2 2) heq
    simp [coe_s01GL, s01Mat, coe_diagHom, coe_cycGL, cycMat, Matrix.mul_apply,
      Fin.sum_univ_three, sq] at h22

theorem six_mul_le_card_torus3_sup [Finite K] (M : Subgroup Kˣ) :
    6 * Nat.card M ^ 2 ≤
      Nat.card ↥(torus3 M ⊔ Subgroup.closure ({s01GL, s12GL} : Set (GL (Fin 3) K))) := by
  set N := torus3 M ⊔ Subgroup.closure ({s01GL, s12GL} : Set (GL (Fin 3) K))
  have hs01 : (s01GL : GL (Fin 3) K) ∈ N :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hs12 : (s12GL : GL (Fin 3) K) ∈ N :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hle : torus3 M ⊔ Subgroup.zpowers cycGL ≤ N := by
    refine sup_le le_sup_left ?_
    rw [Subgroup.zpowers_le, ← s01GL_mul_s12GL]
    exact N.mul_mem hs01 hs12
  have hlt : torus3 M ⊔ Subgroup.zpowers cycGL < N :=
    lt_of_le_of_ne hle fun h => s01GL_not_mem_torus3_sup_cyc M (h ▸ hs01)
  have hdvd := Subgroup.card_dvd_of_le hle
  have hcard := Subgroup.card_lt_of_lt hlt
  rw [card_torus3_sup_cyc] at hdvd hcard
  obtain ⟨k, hk⟩ := hdvd
  rw [hk] at hcard ⊢
  have hk2 : 2 ≤ k := by
    by_contra hk2
    interval_cases k <;> omega
  nlinarith

end Monomial

section Lifted

open Matrix CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K]

theorem lifted_monomial_subgroup {H : Subgroup (GL (Fin 3) K)} {M : Subgroup Kˣ}
    (hH : MonomialData H M) {E : Type*} [Group E] [Finite E] (π : E →* H)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) :
    ∃ N : Subgroup E,
      N.map π = (torus3 M ⊔ Subgroup.closure ({s01GL, s12GL} : Set (GL (Fin 3) K))).subgroupOf H ∧
      Function.Injective (π.comp N.subtype) ∧
      Nat.card ((torus3 M ⊔ Subgroup.closure ({s01GL, s12GL} : Set (GL (Fin 3) K))).subgroupOf
        H) = 6 * Nat.card M ^ 2 := by
  classical
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := M)
  set e := Nat.card M with hedef
  have he : 0 < e := Nat.card_pos
  have hζe : ζ ^ e = 1 := pow_card_eq_one'
  set aG : GL (Fin 3) K := torusHom M (ζ, 1) with haGdef
  set bG : GL (Fin 3) K := torusHom M (1, ζ) with hbGdef
  have haH : aG ∈ H := torus3_le M hH ⟨_, rfl⟩
  have hbH : bG ∈ H := torus3_le M hH ⟨_, rfl⟩
  set a : H := ⟨aG, haH⟩
  set b : H := ⟨bG, hbH⟩
  set s01 : H := ⟨s01GL, hH.s01_mem⟩
  set s02 : H := ⟨s02GL, hH.s02_mem⟩
  set s12 : H := ⟨s12GL, hH.s12_mem⟩
  have hζ1 : ((ζ : Kˣ) * 1)⁻¹ = (ζ : Kˣ)⁻¹ := by rw [mul_one]
  have ha_apply : aG = diagHom 3 ![(ζ : Kˣ), 1, (ζ : Kˣ)⁻¹] := by
    rw [haGdef, torusHom_apply]
    simp
  have hb_apply : bG = diagHom 3 ![1, (ζ : Kˣ), (ζ : Kˣ)⁻¹] := by
    rw [hbGdef, torusHom_apply]
    simp
  have hinv : ∀ d : Fin 3 → Kˣ, (diagHom 3 d)⁻¹ = diagHom 3 d⁻¹ := fun d => (map_inv _ d).symm
  obtain ⟨N, hNmap, hNcard⟩ := exists_monomial_lift (a := a) (b := b) (s₀₁ := s01) (s₀₂ := s02)
    (s₁₂ := s12) hπ hC hodd (Subtype.ext s01GL_sq) (Subtype.ext s02GL_sq) (Subtype.ext s12GL_sq)
    (Subtype.ext (by
      change aG * bG = bG * aG
      rw [haGdef, hbGdef, ← map_mul, ← map_mul, mul_comm]))
    (Subtype.ext (by
      change s02GL * aG * s02GL⁻¹ = aG⁻¹
      rw [ha_apply, s02GL_conj_diagHom, hinv]
      congr 1
      funext i
      fin_cases i <;> simp))
    (Subtype.ext (by
      change s12GL * bG * s12GL⁻¹ = bG⁻¹
      rw [hb_apply, s12GL_conj_diagHom, hinv]
      congr 1
      funext i
      fin_cases i <;> simp))
    (Subtype.ext (by
      change s01GL * aG * s01GL⁻¹ = bG
      rw [ha_apply, hb_apply, s01GL_conj_diagHom]
      rfl))
    (Subtype.ext (by
      change s12GL * aG * s12GL⁻¹ = aG * bG⁻¹
      rw [ha_apply, hb_apply, s12GL_conj_diagHom, hinv, ← map_mul]
      congr 1
      funext i
      fin_cases i <;> simp))
    (Subtype.ext s01GL_conj_s02GL) (Subtype.ext s12GL_conj_s02GL)
    (Subtype.ext (by
      change (s01GL * s12GL) ^ 3 = 1
      rw [s01GL_mul_s12GL, cycGL_pow_three]))
    he
    (Subtype.ext (by
      change aG ^ e = 1
      rw [haGdef, ← map_pow, Prod.pow_mk, hζe, one_pow, Prod.mk_one_one, map_one]))
    (Subtype.ext (by
      change bG ^ e = 1
      rw [hbGdef, ← map_pow, Prod.pow_mk, hζe, one_pow, Prod.mk_one_one, map_one]))
  have hT : Subgroup.closure ({aG, bG} : Set (GL (Fin 3) K)) = torus3 M := by
    apply le_antisymm
    · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
    · rintro _ ⟨⟨m₁, m₂⟩, rfl⟩
      obtain ⟨i, hi⟩ := hζ m₁
      obtain ⟨j, hj⟩ := hζ m₂
      have hxT : aG ∈ Subgroup.closure ({aG, bG} : Set (GL (Fin 3) K)) :=
        Subgroup.subset_closure (by simp)
      have hyT : bG ∈ Subgroup.closure ({aG, bG} : Set (GL (Fin 3) K)) :=
        Subgroup.subset_closure (by simp)
      have hm : ((m₁, m₂) : M × M) = (ζ, 1) ^ i * (1, ζ) ^ j := by
        simp only at hi hj
        ext <;> simp [hi, hj]
      have : torusHom M (m₁, m₂) = aG ^ i * bG ^ j := by
        rw [haGdef, hbGdef, ← map_zpow, ← map_zpow, ← map_mul, hm]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hxT _) (Subgroup.zpow_mem _ hyT _)
  set N₀ := torus3 M ⊔ Subgroup.closure ({s01GL, s12GL} : Set (GL (Fin 3) K)) with hN₀def
  have hN₀H : N₀ ≤ H := by
    refine sup_le (torus3_le M hH) ?_
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hH.s01_mem, hH.s12_mem⟩
  have hmap : N.map π = N₀.subgroupOf H := by
    rw [hNmap]
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hN₀H, Subgroup.map_sup,
      MonoidHom.map_closure, MonoidHom.map_closure, Set.image_pair, Set.image_pair]
    exact congrArg₂ (· ⊔ ·) hT rfl
  have hN₀card : Nat.card (N₀.subgroupOf H) = Nat.card N₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₀H).toEquiv
  have hsurj : Function.Surjective (π.subgroupMap N) := MonoidHom.subgroupMap_surjective π N
  have hle1 : Nat.card ↥(N.map π) ≤ Nat.card N := Nat.card_le_card_of_surjective _ hsurj
  have hge := six_mul_le_card_torus3_sup (K := K) M
  rw [← hN₀card, ← hmap, ← hedef] at hge
  have hbij := hsurj.bijective_of_nat_card_le (by omega)
  refine ⟨N, hmap, fun n₁ n₂ h12 => hbij.1 (Subtype.ext h12), ?_⟩
  rw [← hmap]
  omega

theorem prime_classical_three_lifted_monomial_subgroup {p : ℕ} (hp : p.Prime) {ε : ℤ}
    {H : Subgroup (GL (Fin 3) K)} {M : Subgroup Kˣ}
    (hH : (ε = 1 ∧ Nat.card K = p ∧ H = StatedSL 3 K ∧ M = ⊤) ∨
      (ε = -1 ∧ Nat.card K = p ^ 2 ∧ H = StatedSU 3 p K ∧ M = normOne K p))
    {E : Type*} [Group E] [Finite E] (π : E →* H) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) :
    ∃ N : Subgroup E,
      N.map π = (torus3 M ⊔ Subgroup.closure ({s01GL, s12GL} : Set (GL (Fin 3) K))).subgroupOf H ∧
      Function.Injective (π.comp N.subtype) ∧
      (Nat.card ((torus3 M ⊔ Subgroup.closure ({s01GL, s12GL} : Set (GL (Fin 3) K))).subgroupOf
        H) : ℤ) = 6 * (p - ε) ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hMD : MonomialData H M ∧ (Nat.card M : ℤ) = p - ε := by
    rcases hH with ⟨rfl, hK, rfl, rfl⟩ | ⟨rfl, hK, rfl, rfl⟩
    · refine ⟨monomialData_statedSL, ?_⟩
      rw [Subgroup.card_top, card_units_eq, hK, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
    · have : CharP K p := by
        have := Fintype.ofFinite K
        exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK])
      refine ⟨by simpa only [pow_one] using monomialData_statedSU (K := K) (p := p) (f := 1), ?_⟩
      rw [card_normOne hK]
      push_cast
      ring
  obtain ⟨N, hN, hinj, hcard⟩ := lifted_monomial_subgroup hMD.1 π hπ hC hodd
  refine ⟨N, hN, hinj, ?_⟩
  rw [hcard]
  push_cast
  rw [hMD.2]

end Lifted

end CFSG.SectionRank.OddCover
