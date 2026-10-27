module

public import CFSG.GH74.GLS.Stage2.Final.ModelLUSyl
public import CFSG.GH74.GLS.Stage2.Final.ModelLUMap

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local

theorem exists_equiv_sylow {G H : Type*} [Group G] [Group H] [Finite G] [Finite H] (e : G ≃* H)
    (S₁ : Sylow 2 H) (S : Sylow 2 G) :
    ∃ Φ : G ≃* H, (S : Subgroup G).map Φ.toMonoidHom = (S₁ : Subgroup H) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H (sylowMap e S) S₁
  have hcoe : ((g • sylowMap e S : Sylow 2 H) : Subgroup H) =
      ((sylowMap e S : Sylow 2 H) : Subgroup H).map (MulAut.conj g).toMonoidHom :=
    toSubmonoid_inj.mp rfl
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have h1 : (S : Subgroup G).map (e.trans (MulAut.conj g)).toMonoidHom =
      ((S : Subgroup G).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_map]
    rfl
  rw [h1, ← coe_sylowMap, ← hcoe, hg]

theorem equiv_center_eq {G H : Type*} [Group G] [Group H] (Φ : G ≃* H) {S' : Subgroup G} {z' : G}
    {S₀ : Subgroup H} {y : H} (hy : orderOf y = 2) (hS : S'.map Φ.toMonoidHom = S₀)
    (hc : CenterIs S' z') (hc₀ : CenterIs S₀ y) : Φ z' = y := by
  have h := hc.map_equiv Φ
  rw [hS] at h
  have h1 : Φ z' ∈ Subgroup.zpowers y := (hc₀ _).1 ((h _).2 (Subgroup.mem_zpowers _))
  have h2 : y ∈ Subgroup.zpowers (Φ z') := (h _).1 ((hc₀ _).2 (Subgroup.mem_zpowers _))
  have hne : Φ z' ≠ 1 := by
    intro h3
    rw [h3, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at h2
    rw [h2, orderOf_one] at hy
    omega
  have hdvd : orderOf (Φ z') ∣ 2 := by
    have := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers y) h1
    rwa [Nat.card_zpowers, hy] at this
  have hord : orderOf (Φ z') = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h3 | h3
    · exact absurd (orderOf_eq_one_iff.1 h3) hne
    · exact h3
  exact eq_of_mem_zpowers_of_orderOf_two hy hord h1

theorem luModelData_transfer {Gs : Type} [Group Gs] [Finite Gs] {F : Type} [Field F] [Finite F]
    {M : ModelData F} (e : Gs ≃* PG M) {S₀ : Sylow 2 (PG M)} (hS₀ : CenterIs (S₀ : Subgroup (PG M)) (yP M))
    (h2 : (2 : F) ≠ 0) (S' : Sylow 2 Gs) (z' : Gs)
    (hz' : (Subgroup.center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = Subgroup.zpowers z')
    {q : ℕ} {ε : ℤ} {E₁ E₂ : Subgroup (PG M)} {t u : PG M}
    (hdata : LUModelData (PG M) q ε (yP M) S₀ E₁ E₂ t u) :
    ∃ (E₁' E₂' : Subgroup Gs) (t' u' : Gs), LUModelData Gs q ε z' S' E₁' E₂' t' u' := by
  obtain ⟨Φ, hΦ⟩ := exists_equiv_sylow e S₀ S'
  have hz'c : CenterIs (S' : Subgroup Gs) z' := (centerIs_iff _ _).1 hz'
  have hΦz : Φ z' = yP M := equiv_center_eq Φ (orderOf_yP M h2) hΦ hz'c hS₀
  have hS : (S₀ : Subgroup (PG M)) = (S' : Subgroup Gs).map Φ.toMonoidHom := hΦ.symm
  have key := ModelLUT.luModelData_map Φ.symm
    (S := S₀) (S' := S') (by
      rw [hS, ModelLUT.map_symm_map]) hdata
  rw [show Φ.symm (yP M) = z' by rw [← hΦz]; simp] at key
  exact ⟨_, _, _, _, key⟩

theorem spModelData_transfer {Gs : Type} [Group Gs] [Finite Gs] {F : Type} [Field F] [Finite F]
    {M : ModelData F} (e : Gs ≃* PG M) {S₀ : Sylow 2 (PG M)} (hS₀ : CenterIs (S₀ : Subgroup (PG M)) (yP M))
    (h2 : (2 : F) ≠ 0) (S' : Sylow 2 Gs) (z' : Gs)
    (hz' : (Subgroup.center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = Subgroup.zpowers z')
    {q : ℕ} {E₁ E₂ : Subgroup (PG M)} {t : PG M}
    (hdata : CFSG.GH74.GLS.SP.Local.SPModelData (PG M) q (yP M) S₀ E₁ E₂ t) :
    ∃ (E₁' E₂' : Subgroup Gs) (t' : Gs),
      CFSG.GH74.GLS.SP.Local.SPModelData Gs q z' S' E₁' E₂' t' := by
  obtain ⟨Φ, hΦ⟩ := exists_equiv_sylow e S₀ S'
  have hz'c : CenterIs (S' : Subgroup Gs) z' := (centerIs_iff _ _).1 hz'
  have hΦz : Φ z' = yP M := equiv_center_eq Φ (orderOf_yP M h2) hΦ hz'c hS₀
  have hS : (S₀ : Subgroup (PG M)) = (S' : Subgroup Gs).map Φ.toMonoidHom := hΦ.symm
  have key := ModelLUT.spModelData_map Φ.symm
    (S := S₀) (S' := S') (by
      rw [hS, ModelLUT.map_symm_map]) hdata
  rw [show Φ.symm (yP M) = z' by rw [← hΦz]; simp] at key
  exact ⟨_, _, _, key⟩

variable {F : Type} [Field F]

theorem units_sq_eq_one_unit {c : Fˣ} (h : c * c = 1) : c = 1 ∨ c = -1 := units_sq_eq_one h

theorem two_power_ratio (l m : Fˣ) {N : ℕ} (hN : ¬ 8 ∣ N) (hl : l ^ N = 1)
    (hlm : l * m * (l * m) = 1) {i : ℕ} (hi : (l * m⁻¹) ^ 2 ^ i = 1) : l = m ∨ l = -m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set r := l * m⁻¹ with hr
  set ε := l * m with hε
  have hε2 : ε * ε = 1 := hlm
  have hl2 : l * l = ε * r := by
    rw [hr, hε, show l * m * (l * m⁻¹) = l * l * (m * m⁻¹) by ac_rfl, mul_inv_cancel, mul_one]
  have hfin : r = 1 ∨ r = -1 → l = m ∨ l = -m := by
    rintro (h | h)
    · left; rw [hr] at h; exact mul_inv_eq_one.1 h
    · right
      rw [hr] at h
      rw [mul_inv_eq_iff_eq_mul] at h
      rw [h]; simp
  obtain ⟨e, -, hordr⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hi)
  rcases e with _ | _ | k
  · apply hfin; left
    rw [pow_zero, orderOf_eq_one_iff] at hordr
    exact hordr
  · apply hfin
    apply units_sq_eq_one
    have : r ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hordr]; simp
    rwa [sq] at this
  · exfalso
    apply hN
    have hr1 : r ^ 2 ^ (k + 1) ≠ 1 := by
      intro h
      have := orderOf_dvd_of_pow_eq_one h
      rw [hordr] at this
      have h3 := Nat.le_of_dvd (by positivity) this
      have : 2 ^ (k + 1) < 2 ^ (k + 1 + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have hr2 : r ^ 2 ^ (k + 1 + 1) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hordr]
    have hε' : ε ^ 2 ^ (k + 1) = 1 := by
      rw [pow_succ', pow_mul, show ε ^ 2 = 1 by rw [sq]; exact hε2, _root_.one_pow]
    have hl3 : l ^ 2 ^ (k + 1 + 1) = r ^ 2 ^ (k + 1) := by
      rw [pow_succ' 2 (k + 1), pow_mul, sq, hl2, mul_pow, hε', one_mul]
    have hl4 : l ^ 2 ^ (k + 1 + 1 + 1) = 1 := by
      rw [pow_succ 2 (k + 1 + 1), pow_mul, hl3, ← pow_mul, ← pow_succ, hr2]
    have hord : orderOf l = 2 ^ (k + 1 + 1 + 1) :=
      orderOf_eq_prime_pow (by rw [hl3]; exact hr1) hl4
    have := orderOf_dvd_of_pow_eq_one hl
    rw [hord] at this
    have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [h8]
    exact dvd_trans (pow_dvd_pow 2 (by omega)) this

theorem sc2_neg_eq (m : Fˣ) : (sc2 (-m) : GL (Fin 2) F) = sc2 m * (-1) := by
  rw [← neg_one_mul m, ← sc2_mul, sc2_neg_one, neg_one_mul, mul_neg_one]

theorem hcs_gen [Finite F] (M : ModelData F) {N : ℕ} (hN8 : ¬ 8 ∣ N)
    (hN : ∀ l m : Fˣ, diagGL (sc2 l) (sc2 m) ∈ M.K4 → l ^ N = 1) :
    ∀ s ∈ BSsub M, (∃ i : ℕ, s ^ 2 ^ i = 1) → s = 1 ∨ s = yP M := by
  rintro s ⟨p, rfl⟩ ⟨i, hi⟩
  obtain ⟨⟨l, m⟩, hp⟩ := p
  have hp' : diagGL (sc2 l) (sc2 m) ∈ M.K4 := hp
  have h1 : bscP M ((⟨(l, m), hp⟩ : Bsc M) ^ 2 ^ i) = 1 := by rw [map_pow]; exact hi
  rw [bscP_eq_one_iff] at h1
  have hpow : ((⟨(l, m), hp⟩ : Bsc M) ^ 2 ^ i : Bsc M).1 = (l ^ 2 ^ i, m ^ 2 ^ i) := rfl
  rw [hpow] at h1
  have h1' : l ^ 2 ^ i = m ^ 2 ^ i := h1
  have hlm : l * m * (l * m) = 1 := by
    have hd := (M.diagGL_mem_K4_iff.1 hp').2.2
    rw [det_sc2, det_sc2] at hd
    apply Units.ext
    simp only [Units.val_mul, Units.val_one]
    linear_combination hd
  have hi' : (l * m⁻¹) ^ 2 ^ i = 1 := by
    rw [mul_pow, inv_pow, h1', mul_inv_cancel]
  rcases two_power_ratio l m hN8 (hN l m hp') hlm hi' with h | h
  · left
    exact (bscP_eq_one_iff M ⟨(l, m), hp⟩).2 h
  · right
    have hyK : diagGL (-1 : GL (Fin 2) F) 1 ∈ M.K4 := M.yGL_mem_K4
    have key := (mkP_diag_eq_iff (M := M) hyK hp').2 ⟨m, by rw [h, sc2_neg_eq, sc2_comm], by rw [mul_one]⟩
    exact key.symm

theorem index_E_Cg_eq [Finite F] (M : ModelData F) {n : ℕ}
    (h : Nat.card ↥(Cg M) = n * Nat.card ↥(K1 M ⊔ K2 M)) :
    ((K1 M ⊔ K2 M).subgroupOf (Cg M)).index = n := by
  have h1 := Subgroup.card_mul_index ((K1 M ⊔ K2 M).subgroupOf (Cg M))
  have h2 : Nat.card ↥((K1 M ⊔ K2 M).subgroupOf (Cg M)) = Nat.card ↥(K1 M ⊔ K2 M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (E_le_Cg M)).toEquiv
  rw [h2, h] at h1
  have hpos : 0 < Nat.card ↥(K1 M ⊔ K2 M) := Nat.card_pos
  rw [mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos h1

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
