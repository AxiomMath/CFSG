module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2Beta

public section

namespace CFSG.OddStandard.AltStdSmall4.G2

open Subgroup Matrix
open scoped Pointwise

section Generic

variable {G : Type} [Group G] {k : ℕ} {A : Subgroup G}
  (ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ k)))

theorem mat_eq_mat_iff (g g' : normalizer (A : Set G)) :
    mat ι g = mat ι g' ↔ ∀ a ∈ A, (g : G) * a * (g : G)⁻¹ = (g' : G) * a * (g' : G)⁻¹ := by
  constructor
  · intro h1 a ha
    obtain ⟨x, rfl⟩ := exists_el_eq ι ha
    rw [mat_spec, mat_spec, h1]
  · intro h1
    exact matrix_ext_mulVec fun x => el_injective ι (by
      rw [← mat_spec, ← mat_spec, h1 _ (el_mem ι x)])

theorem mat_mul_mat_inv (g : normalizer (A : Set G)) : mat ι g * mat ι g⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

theorem red_mat_eq_one {L : Subgroup G} {n : ℕ} {θ : L ≃* alternatingGroup (Fin n)}
    {hn : 8 ≤ n} (hι : ECoords θ hn k A ι) {g : normalizer (A : Set G)}
    (hg : (g : G) ∈ centralizer (E θ hn : Set G)) : red k (mat ι g) = 1 := by
  refine matrix_ext_mulVec fun v => epsV_injective θ hn ?_
  rw [← red_mat ι hι g v, one_mulVec, ← mem_centralizer_iff.1 hg _ (epsV_mem_E θ hn v),
    mul_inv_cancel_right]

theorem red_mat_eq {L : Subgroup G} {n : ℕ} {θ : L ≃* alternatingGroup (Fin n)}
    {hn : 8 ≤ n} (hι : ECoords θ hn k A ι) {g : normalizer (A : Set G)}
    {M : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hg : ∀ v, (g : G) * epsV θ hn v * (g : G)⁻¹ = epsV θ hn (M *ᵥ v)) : red k (mat ι g) = M := by
  refine matrix_ext_mulVec fun v => epsV_injective θ hn ?_
  rw [← red_mat ι hι g v, hg v]

end Generic

section Scalar

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {k : ℕ} {A : Subgroup G}
  (c : Config G L Q n θ z) (h : LevelDatum θ c.hn8 z k A)

omit [Finite G] in
theorem LevelDatum.z_not_mem_centralizer {hn : 8 ≤ n} (h : LevelDatum θ hn z k A) :
    z ∉ centralizer (A : Set G) := by
  intro hz
  have hle : A ≤ E θ hn := fun a ha =>
    h.mem_E_of_conj_eq ha (by rw [← mem_centralizer_iff.1 hz a ha, mul_inv_cancel_right])
  have hfin : Finite (E θ hn) := Nat.finite_of_card_ne_zero (by rw [card_E]; norm_num)
  have h1 := Subgroup.card_le_of_le hle
  rw [card_E, h.card] at h1
  have h2 : 2 ^ 6 ≤ 2 ^ (3 * k) := Nat.pow_le_pow_right (by norm_num) (by have := h.two_le; omega)
  omega

variable {ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ k))} (hι : ECoords θ c.hn8 k A ι)
include c h hι

theorem mat_of_betaHat_eq_one {g : normalizer (A : Set G)} (hg : (g : G) ∈ RA θ c.hn8 z A)
    (h1 : betaHat k z (g : G) = 1) :
    mat ι g = 1 ∨ mat ι g = mat ι ⟨z, h.z_mem_normalizer (z_mul_self c)⟩ := by
  set zN : normalizer (A : Set G) := ⟨z, h.z_mem_normalizer (z_mul_self c)⟩ with hzN
  have hk : 1 ≤ k := hι.one_le
  have hzE : red k (mat ι zN) = 1 := red_mat_eq_one ι hι (z_mem_centralizer_E c h)
  have hZ2 : mat ι zN * mat ι zN = 1 := by
    rw [← map_mul, show zN * zN = 1 from Subtype.ext (z_mul_self c), map_one]
  obtain ⟨u, -, hu⟩ := mat_z ι h.zAct (z_mul_self c)
  have hZc : ∀ X, Commute (mat ι zN) X := fun X => by
    rw [hu]
    exact (Commute.one_left X).smul_left u
  obtain ⟨a, ha, haz⟩ := (betaHat_eq_one_iff c h hg).1 h1
  set aN : normalizer (A : Set G) := ⟨a, Subgroup.le_normalizer ha⟩ with haN
  have hmat_a : mat ι aN = 1 :=
    (mat_eq_one_iff ι aN).2 fun b hb => by rw [h.comm ha hb, mul_inv_cancel_right]
  set cN := aN⁻¹ * g with hcN
  have hcR : (cN : G) ∈ RA θ c.hn8 z A :=
    mul_mem (inv_mem (sup_le_RA c h (mem_sup_left ha))) hg
  have hcz : (cN : G) ∈ centralizer ({z} : Set G) := haz
  have hgc : mat ι g = mat ι cN := by
    have e : g = aN * cN := by rw [hcN, mul_inv_cancel_left]
    rw [e, map_mul, hmat_a, one_mul]
  have hcred : red k (mat ι cN) = 1 := red_mat_eq_one ι hι (RA_le_centralizer_E c hcR)
  obtain ⟨s, m, hm, hcm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (cN : G)).ne'
  have hc2 : ((cN : G) ^ m) ^ 2 ^ s = 1 := by
    rw [← pow_mul, mul_comm, ← hcm, pow_orderOf_eq_one]
  have hcB := mem_of_two_pow_RA c (pow_mem hcR m) (pow_mem hcz m) hc2
  have hcoe : ((cN ^ m : normalizer (A : Set G)) : G) = (cN : G) ^ m := by simp
  obtain ⟨i, hi | hi⟩ := (N0.mem_B0_iff c.hn8 c _).1 hcB
  · left
    have hpow : mat ι cN ^ m = 1 := by
      rw [← map_pow]
      refine (mat_eq_one_iff ι _).2 fun b hb => ?_
      rw [hcoe, hi, h.comm (h.E_le (N0.eps_mem_E θ c.hn8 i)) hb, mul_inv_cancel_right]
    rw [hgc]
    exact eq_one_of_red_of_odd hcred hm hpow
  · right
    have hpow : mat ι cN ^ m = mat ι zN := by
      rw [← map_pow]
      refine (mat_eq_mat_iff ι _ _).2 fun b hb => ?_
      rw [hcoe, hi]
      have hb' : N0.eps θ c.hn8 i * b * (N0.eps θ c.hn8 i)⁻¹ = b := by
        rw [h.comm (h.E_le (N0.eps_mem_E θ c.hn8 i)) hb, mul_inv_cancel_right]
      calc z * N0.eps θ c.hn8 i * b * (z * N0.eps θ c.hn8 i)⁻¹ =
          z * (N0.eps θ c.hn8 i * b * (N0.eps θ c.hn8 i)⁻¹) * z⁻¹ := by group
        _ = z * b * z⁻¹ := by rw [hb']
    have hprod : (mat ι cN * mat ι zN) ^ m = 1 := by
      rw [(hZc (mat ι cN)).symm.mul_pow, hpow, ← pow_succ']
      obtain ⟨t, rfl⟩ := hm
      rw [show 2 * t + 1 + 1 = 2 * (t + 1) by ring, pow_mul, sq, hZ2, one_pow]
    have hred : red k (mat ι cN * mat ι zN) = 1 := by rw [red_mul hk, hcred, hzE, one_mul]
    have h1' := eq_one_of_red_of_odd hred hm hprod
    rw [hgc]
    calc mat ι cN = mat ι cN * mat ι zN * mat ι zN := by rw [mul_assoc, hZ2, mul_one]
      _ = mat ι zN := by rw [h1', one_mul]

theorem exists_r1 (hT : ¬ Terminal θ c.hn8 A) :
    ∃ r₁ : normalizer (A : Set G), (r₁ : G) ∈ RA θ c.hn8 z A ∧
      betaHat k z (r₁ : G) = epsV θ c.hn8 e1V ∧
      (mat ι r₁ = 1 ∨ mat ι r₁ = mat ι ⟨z, h.z_mem_normalizer (z_mul_self c)⟩) := by
  set zN : normalizer (A : Set G) := ⟨z, h.z_mem_normalizer (z_mul_self c)⟩ with hzN
  obtain ⟨u, hu, hZu⟩ := mat_z ι h.zAct (z_mul_self c)
  obtain ⟨r, hr, hr1⟩ := (terminal_or_onto c h).resolve_left hT _ (epsV_mem_E θ c.hn8 e1V)
  set r₁ : normalizer (A : Set G) := ⟨r, RA_le_normalizer c h hr⟩ with hr₁
  have key : ∀ M : GL (Fin 3) (ZMod 2), (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ e1V = e1V →
      ∃ κ : normalizer (A : Set G), red k (mat ι κ) = M ∧
        (mat ι κ * mat ι r₁ * mat ι κ⁻¹ = mat ι r₁ ∨
          mat ι κ * mat ι r₁ * mat ι κ⁻¹ = u • mat ι r₁) := by
    intro M hM
    obtain ⟨κ, hκ, hκv⟩ := h.cover M
    set κN : normalizer (A : Set G) := ⟨κ, KA_le_normalizer hκ⟩ with hκN
    refine ⟨κN, red_mat_eq ι hι hκv, ?_⟩
    have hκr : κ * r * κ⁻¹ ∈ RA θ c.hn8 z A := KA_conj_mem_RA c h hκ hr
    set nN : normalizer (A : Set G) := κN * r₁ * κN⁻¹ * r₁⁻¹ with hnN
    have hnG : (nN : G) = κ * r * κ⁻¹ * r⁻¹ := rfl
    have hnR : (nN : G) ∈ RA θ c.hn8 z A := by
      rw [hnG]
      exact mul_mem hκr (inv_mem hr)
    have hβn : betaHat k z (nN : G) = 1 := by
      rw [hnG, betaHat_mul c h hκr (inv_mem hr), betaHat_conj c h hκ, betaHat_inv c h hr, hr1,
        hκv, hM, mul_inv_cancel]
    have hconj : mat ι κN * mat ι r₁ * mat ι κN⁻¹ = mat ι nN * mat ι r₁ := by
      rw [← map_mul, ← map_mul, ← map_mul, hnN, inv_mul_cancel_right]
    rcases mat_of_betaHat_eq_one c h hι hnR hβn with h0 | hZ
    · left
      rw [hconj, h0, one_mul]
    · right
      rw [hconj, hZ, hZu, smul_mul_assoc, one_mul]
  obtain ⟨κ₁, hred₁, hconj₁⟩ := key h1G h1G_mulVec_e1V
  obtain ⟨κ₂, hred₂, hconj₂⟩ := key h2G h2G_mulVec_e1V
  have hw : red k (mat ι r₁) = 1 := red_mat_eq_one ι hι (RA_le_centralizer_E c hr)
  obtain ⟨l, hl⟩ := exists_eq_smul_one hu hw hred₁ (mat_mul_mat_inv ι κ₁) hconj₁ hred₂
    (mat_mul_mat_inv ι κ₂) hconj₂
  refine ⟨r₁, hr, hr1, ?_⟩
  obtain ⟨κa, hκa, hκav⟩ := h.cover g2G
  obtain ⟨κb, hκb, hκbv⟩ := h.cover g3G
  set κaN : normalizer (A : Set G) := ⟨κa, KA_le_normalizer hκa⟩ with hκaN
  set κbN : normalizer (A : Set G) := ⟨κb, KA_le_normalizer hκb⟩ with hκbN
  set xN := r₁ * (κaN * r₁ * κaN⁻¹) * (κbN * r₁ * κbN⁻¹) with hxN
  have hxG : (xN : G) = r * (κa * r * κa⁻¹) * (κb * r * κb⁻¹) := rfl
  have hra := KA_conj_mem_RA c h hκa hr
  have hrb := KA_conj_mem_RA c h hκb hr
  have hxR : (xN : G) ∈ RA θ c.hn8 z A := by
    rw [hxG]
    exact mul_mem (mul_mem hr hra) hrb
  have hβx : betaHat k z (xN : G) = 1 := by
    rw [hxG, betaHat_mul c h (mul_mem hr hra) hrb, betaHat_mul c h hr hra, betaHat_conj c h hκa,
      betaHat_conj c h hκb, hr1, hκav, hκbv, g2G_mulVec_e1V, g3G_mulVec_e1V, ← epsV_add,
      ← epsV_add, show e1V + e2V + (e1V + e2V) = 0 by decide, epsV_zero]
  have hscal : ∀ κ : normalizer (A : Set G), mat ι κ * mat ι r₁ * mat ι κ⁻¹ = l • 1 := by
    intro κ
    rw [hl, mul_smul_comm, mul_one, smul_mul_assoc, mat_mul_mat_inv]
  have hmx : mat ι xN = l ^ 3 • (1 : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) := by
    rw [hxN, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, hscal κaN, hscal κbN, hl,
      smul_mul_smul_comm, smul_mul_smul_comm, one_mul, one_mul]
    congr 1
    ring
  have hcube : l ^ 3 = 1 ∨ l ^ 3 = u := by
    rcases mat_of_betaHat_eq_one c h hι hxR hβx with h0 | hZ
    · left
      have := congrFun (congrFun (hmx.symm.trans h0) 0) 0
      simpa using this
    · right
      rw [hZu] at hZ
      have := congrFun (congrFun (hmx.symm.trans hZ) 0) 0
      simpa using this
  rcases eq_of_cube (sq_eq_one_of_u hu) hcube with h1 | h1
  · left
    rw [hl, h1, one_smul]
  · right
    rw [hl, h1, hZu]

theorem mat_RA (hT : ¬ Terminal θ c.hn8 A) {g : normalizer (A : Set G)}
    (hg : (g : G) ∈ RA θ c.hn8 z A) :
    mat ι g = 1 ∨ mat ι g = mat ι ⟨z, h.z_mem_normalizer (z_mul_self c)⟩ := by
  set zN : normalizer (A : Set G) := ⟨z, h.z_mem_normalizer (z_mul_self c)⟩ with hzN
  have hZ2 : mat ι zN * mat ι zN = 1 := by
    rw [← map_mul, show zN * zN = 1 from Subtype.ext (z_mul_self c), map_one]
  obtain ⟨u, -, hZu⟩ := mat_z ι h.zAct (z_mul_self c)
  obtain ⟨r₁, hr₁, hr₁1, hr₁s⟩ := exists_r1 c h hι hT
  obtain ⟨v, hv⟩ := (mem_E_iff_epsV θ c.hn8 _).1 (betaHat_mem_E c h hg)
  by_cases hv0 : v = 0
  · rw [hv0, epsV_zero] at hv
    exact mat_of_betaHat_eq_one c h hι hg hv.symm
  · obtain ⟨M, hM⟩ := exists_mul_e1 hv0
    obtain ⟨κ, hκ, hκv⟩ := h.cover M
    set κN : normalizer (A : Set G) := ⟨κ, KA_le_normalizer hκ⟩ with hκN
    set yN := κN * r₁ * κN⁻¹ with hyN
    have hyG : (yN : G) = κ * r₁ * κ⁻¹ := rfl
    have hyR : (yN : G) ∈ RA θ c.hn8 z A := by
      rw [hyG]
      exact KA_conj_mem_RA c h hκ hr₁
    have hβy : betaHat k z (yN : G) = epsV θ c.hn8 v := by
      rw [hyG, betaHat_conj c h hκ, hr₁1, hκv, hM]
    set nN := yN⁻¹ * g with hnN
    have hnG : (nN : G) = (yN : G)⁻¹ * g := rfl
    have hnR : (nN : G) ∈ RA θ c.hn8 z A := by
      rw [hnG]
      exact mul_mem (inv_mem hyR) hg
    have hβn : betaHat k z (nN : G) = 1 := by
      rw [hnG, betaHat_mul c h (inv_mem hyR) hg, betaHat_inv c h hyR, hβy, hv, inv_mul_cancel]
    have hmy : mat ι yN = mat ι r₁ := by
      rcases hr₁s with h0 | hZ
      · rw [hyN, map_mul, map_mul, h0, mul_one, mat_mul_mat_inv]
      · rw [hyN, map_mul, map_mul, hZ, hZu, mul_smul_comm, mul_one, smul_mul_assoc,
          mat_mul_mat_inv]
    have hg' : g = yN * nN := by rw [hnN, mul_inv_cancel_left]
    rw [hg', map_mul, hmy]
    rcases hr₁s with h0 | hZ <;> rcases mat_of_betaHat_eq_one c h hι hnR hβn with h0' | hZ'
    · left
      rw [h0, h0', one_mul]
    · right
      rw [h0, hZ', one_mul]
    · right
      rw [hZ, h0', mul_one]
    · left
      rw [hZ, hZ', hZ2]

omit hι in
theorem LevelDatum.scalar (hT : ¬ Terminal θ c.hn8 A) :
    ∀ r ∈ RA θ c.hn8 z A,
      (∀ a ∈ A, r * a * r⁻¹ = a) ∨ (∀ a ∈ A, r * a * r⁻¹ = z * a * z⁻¹) := by
  obtain ⟨ι, hι⟩ := h.exists_ecoords
  intro r hr
  rcases mat_RA c h hι hT (g := ⟨r, RA_le_normalizer c h hr⟩) hr with h0 | hZ
  · exact Or.inl ((mat_eq_one_iff ι _).1 h0)
  · exact Or.inr ((mat_eq_mat_iff ι _ _).1 hZ)

omit hι in
theorem exists_stepData (hT : ¬ Terminal θ c.hn8 A) :
    ∃ P A' : Subgroup G, StepData θ c.hn8 z k A P A' := by
  obtain ⟨P, hPR, hPp, hXP, honto, hker, hcard⟩ := exists_P c h hT
  have hsc := LevelDatum.scalar c h hT
  have hzz := z_mul_self c
  have hzi := z_inv c
  have hzP : z ∈ P := hXP (mem_sup_right (mem_zpowers z))
  have hzC := h.z_not_mem_centralizer
  have hzN : z ∈ normalizer (A : Set G) := h.z_mem_normalizer hzz
  set A' := P ⊓ centralizer (A : Set G) with hA'
  have hsplit : ∀ p ∈ P, p ∈ A' ∨ p * z ∈ A' := by
    intro p hp
    rcases hsc p (hPR hp) with h1 | h1
    · left
      refine Subgroup.mem_inf.2 ⟨hp, mem_centralizer_iff.2 fun a ha => ?_⟩
      calc a * p = p * a * p⁻¹ * p := by rw [h1 a ha]
        _ = p * a := by group
    · right
      refine Subgroup.mem_inf.2 ⟨mul_mem hp hzP, mem_centralizer_iff.2 fun a ha => ?_⟩
      have hza := h.conj_z_mem ha
      have e : p * z * a * (p * z)⁻¹ = a := by
        calc p * z * a * (p * z)⁻¹ = p * (z * a * z⁻¹) * p⁻¹ := by group
          _ = z * (z * a * z⁻¹) * z⁻¹ := h1 _ hza
          _ = (z * z) * a * (z⁻¹ * z⁻¹) := by group
          _ = a := by rw [hzz, hzi, hzz, one_mul, mul_one]
      calc a * (p * z) = p * z * a * (p * z)⁻¹ * (p * z) := by rw [e]
        _ = p * z * a := by group
  have hzA' : z ∉ A' := fun h' => hzC (Subgroup.mem_inf.1 h').2
  have hconjA' : ∀ x ∈ A', z * x * z⁻¹ ∈ A' := by
    intro x hx
    obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hzP hxP) (inv_mem hzP), ?_⟩
    rw [mem_centralizer_iff]
    intro a ha
    have ha' : z⁻¹ * a * z ∈ A := by
      have := h.conj_z_mem ha
      rwa [hzi] at this ⊢
    have := mem_centralizer_iff.1 hxC _ ha'
    calc a * (z * x * z⁻¹) = z * ((z⁻¹ * a * z) * x) * z⁻¹ := by group
      _ = z * (x * (z⁻¹ * a * z)) * z⁻¹ := by rw [this]
      _ = z * x * z⁻¹ * a := by group
  have hzNA' : z ∈ normalizer (A' : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hconjA' x, fun hx => ?_⟩
    have := hconjA' _ hx
    have e : z * (z * x * z⁻¹) * z⁻¹ = x := by
      rw [hzi]
      calc z * (z * x * z) * z = (z * z) * x * (z * z) := by group
        _ = x := by rw [hzz, one_mul, mul_one]
    rwa [e] at this
  have hsupP : A' ⊔ zpowers z = P := by
    apply le_antisymm (sup_le inf_le_left (zpowers_le.2 hzP))
    intro p hp
    rcases hsplit p hp with h1 | h1
    · exact mem_sup_left h1
    · rw [show p = p * z * z⁻¹ by group]
      exact mul_mem (mem_sup_left h1) (inv_mem (mem_sup_right (mem_zpowers z)))
  have hinf : A' ⊓ zpowers z = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyA', hyz⟩
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hyz
    rcases zpow_eq_one_or_eq hzz j with h1 | h1
    · rw [h1]
      exact one_mem _
    · rw [h1] at hyA'
      exact absurd hyA' hzA'
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [sq, hzz]) (z_ne_one c)
  have hcardA' : Nat.card A' = 8 * Nat.card A := by
    have h1 := card_sup_of_inf_eq_bot (zpowers_le.2 hzNA') hinf
    rw [hsupP, hcard, Nat.card_zpowers, hord] at h1
    omega
  have hβz : betaHat k z z = 1 := betaHat_eq_one_of_mem_sup c h (mem_sup_right (mem_zpowers z))
  have hAC : A ≤ centralizer (A : Set G) := fun a ha =>
    mem_centralizer_iff.2 fun b hb => h.comm hb ha
  refine ⟨P, A', ⟨h, hPR, hPp, hXP, rfl, hsplit, hcardA', ?_, ?_, hsc⟩⟩
  · intro e he
    obtain ⟨p, hp, hpe⟩ := honto e he
    rcases hsplit p hp with h1 | h1
    · exact ⟨p, h1, hpe⟩
    · refine ⟨p * z, h1, ?_⟩
      rw [betaHat_mul c h (hPR hp) (hPR hzP), hpe, hβz, mul_one]
  · intro x hx hx1
    obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.1 hx
    rcases (h.mem_sup_iff hzz).1 (hker x hxP hx1) with h1 | h1
    · exact h1
    · exfalso
      apply hzC
      rw [show z = x⁻¹ * (x * z) by group]
      exact mul_mem (inv_mem hxC) (hAC h1)

end Scalar

end CFSG.OddStandard.AltStdSmall4.G2
