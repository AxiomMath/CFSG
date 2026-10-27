module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1NextLevelOne
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1NextCentral
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1StageInd

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1Next

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {v : G → K} {μ : K}

section NoU'

variable (H : U3C1Next G L f t T d V U U₁ k K v μ)
include H

theorem exists_sq_of_pow_eq_one {r : G} (hr : r ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (h1 : r ^ 2 ^ (k + 1) = 1) : ∃ s ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), r = s ^ 2 := by
  obtain ⟨-, hcomm, hcard, hΩ, hpow, -, -, -⟩ := H.stage.nextConf H.mu H.lam H.nu
  exact SzC1.exists_sq_eq_of_pow_eq_one hcomm hΩ hpow
    (by rw [H.stage.card_szA₁, hcard]) hr h1

theorem exists_sq_of_mem_V {r : G} (hr : r ∈ V) :
    ∃ s ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), r = s ^ 2 :=
  H.exists_sq_of_pow_eq_one (H.V_le_V₁ hr) (H.stage.pow r hr)

theorem X_conj_d {w : G} (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    v ((d⁻¹ * w * d) ^ 2 ^ (k + 1)) = μ * v (w ^ 2 ^ (k + 1)) := by
  rw [show d⁻¹ * w * d = d⁻¹ * w * d⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv,
    H.coords.conj _ (H.stage.pow_mem_szA₁_V₁ hw)]

end NoU'

namespace NextUData

variable {H : U3C1Next G L f t T d V U U₁ k K v μ} {U' : Subgroup G} (hD : H.NextUData U')
include hD

theorem chi_mul_right {x : G} (hx : x ∈ U') {w w' : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hw' : w' ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    (w * w')⁻¹ * (x * (w * w') * x⁻¹) = (w⁻¹ * (x * w * x⁻¹)) * (w'⁻¹ * (x * w' * x⁻¹)) := by
  have hcx := H.V_le_V₁ (hD.chi_mem_V hx hw)
  have e1 : w'⁻¹ * (w⁻¹ * (x * w * x⁻¹)) = (w⁻¹ * (x * w * x⁻¹)) * w'⁻¹ :=
    H.V₁_comm (inv_mem hw') hcx
  calc (w * w')⁻¹ * (x * (w * w') * x⁻¹) = w'⁻¹ * (w⁻¹ * (x * w * x⁻¹)) * (x * w' * x⁻¹) := by
        group
    _ = (w⁻¹ * (x * w * x⁻¹)) * w'⁻¹ * (x * w' * x⁻¹) := by rw [e1]
    _ = _ := by group

theorem M_mul_right {x : G} (hx : x ∈ U') {w w' : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hw' : w' ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    v (((w * w')⁻¹ * (x * (w * w') * x⁻¹)) ^ 2 ^ k) =
      v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) + v ((w'⁻¹ * (x * w' * x⁻¹)) ^ 2 ^ k) := by
  have hc := hD.chi_mem_V hx hw
  have hc' := hD.chi_mem_V hx hw'
  rw [hD.chi_mul_right hx hw hw', (Commute.mul_pow (H.stage.comm _ hc _ hc') _),
    H.coords.mul _ (H.stage.pow_mem_szA₁ hc) _ (H.stage.pow_mem_szA₁ hc')]

theorem M_eq_zero_of_mem_V {x : G} (hx : x ∈ U') {r : G} (hr : r ∈ V) :
    v ((r⁻¹ * (x * r * x⁻¹)) ^ 2 ^ k) = 0 := by
  obtain ⟨s, hs, rfl⟩ := H.exists_sq_of_mem_V hr
  have hcs := hD.chi_mem_V hx hs
  rw [sq s, hD.chi_mul_right hx hs hs, ← sq, ← pow_mul, ← pow_succ', H.stage.pow _ hcs,
    H.coords.v_one]

theorem M_eq_of_X_eq {x : G} (hx : x ∈ U') {w w' : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hw' : w' ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hX : v (w ^ 2 ^ (k + 1)) = v (w' ^ 2 ^ (k + 1))) :
    v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) = v ((w'⁻¹ * (x * w' * x⁻¹)) ^ 2 ^ k) := by
  have hV := (H.X_eq_iff hw hw').mp hX
  have e : w' = w * (w⁻¹ * w') := by group
  rw [e, hD.M_mul_right hx hw (H.V_le_V₁ hV), hD.M_eq_zero_of_mem_V hx hV, add_zero]

theorem M_conj_d {x : G} (hx : x ∈ U') {w : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    v (((d⁻¹ * w * d)⁻¹ * ((d⁻¹ * x * d) * (d⁻¹ * w * d) * (d⁻¹ * x * d)⁻¹)) ^ 2 ^ k) =
      μ * v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) := by
  rw [show (d⁻¹ * w * d)⁻¹ * ((d⁻¹ * x * d) * (d⁻¹ * w * d) * (d⁻¹ * x * d)⁻¹) =
    d⁻¹ * (w⁻¹ * (x * w * x⁻¹)) * d⁻¹⁻¹ by group, conj_pow, inv_inv,
    H.coords.conj _ (H.stage.pow_mem_szA₁ (hD.chi_mem_V hx hw))]

theorem S'_mul {x y : G} (hx : x ∈ U') (hy : y ∈ U') :
    v ((x * y * t * (x * y)⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) =
      v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) + v ((y * t * y⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) := by
  have e := hD.perm_zero_mul hx hy
  rw [H.perm_zero, H.perm_zero, H.perm_zero] at e
  exact e

theorem S'_conj_d {x : G} (hx : x ∈ U') :
    v ((d⁻¹ * x * d * t * (d⁻¹ * x * d)⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) =
      μ * v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) := by
  rw [H.stage.comm_t_conj_d x, H.X_conj_d (H.comm_t_mem_V₁ (hD.le hx))]

theorem conj_V₁_of_mem_U₁' {U₁' : Subgroup G} (hle : U₁' ≤ U')
    (hN : U' ≤ normalizer (U₁' : Set G)) (hsup : U₁' ⊔ zpowers t = U')
    (hd : d ∈ normalizer (U₁' : Set G)) (hinf : U₁' ⊓ U = U₁) :
    ∀ x ∈ U₁', ∀ r ∈ U₁ ⊓ centralizer (szT₁ L T : Set G),
      r⁻¹ * (x * r * x⁻¹) ∈ szA₁ (szT₁ L T) := by
  have hf : 2 ≤ f := H.stage.start.two_le
  obtain ⟨-, hV₁comm, -, -, hV₁pow, -, -, -⟩ := H.stage.nextConf H.mu H.lam H.nu
  set S' : G → K := fun x => v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) with hS'
  have htU' : t ∈ U' := hD.U_le H.stage.t_mem_U
  have hS't : S' t = 0 := by
    show v ((t * t * t⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) = 0
    rw [show t * t * t⁻¹ * t⁻¹ = (1 : G) by group, one_pow, H.coords.v_one]
  have hS'mul : ∀ x ∈ U₁', ∀ y ∈ U₁', S' (x * y) = S' x + S' y := fun x hx y hy =>
    hD.S'_mul (hle hx) (hle hy)
  have hS'surj : ∀ s : K, ∃ x ∈ U₁', S' x = s := by
    intro s
    obtain ⟨n, hnU', hn⟩ := hD.surj s
    have hS'n : S' n = s := by
      show v ((n * t * n⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) = s
      rw [← H.perm_zero ⟨n, hD.le hnU'⟩, hn]
    have htN : t ∈ normalizer (U₁' : Set G) := hN htU'
    rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers H.stage.t_mul_self htN
      (hsup ▸ hnU') with h1 | h1
    · exact ⟨n, h1, hS'n⟩
    · refine ⟨n * t, h1, ?_⟩
      have e := hD.S'_mul hnU' htU'
      show v ((n * t * t * (n * t)⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) = s
      rw [e]
      show S' n + S' t = s
      rw [hS't, add_zero, hS'n]
  have hS'ker : ∀ x ∈ U₁', S' x = 0 → x ∈ U₁ := by
    intro x hx h0
    have hxU := hD.mem_U x (hle hx) (by rw [H.perm_zero]; exact h0)
    rw [← hinf]
    exact mem_inf.mpr ⟨hx, hxU⟩
  have hU₁M : ∀ x ∈ U₁, ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G),
      v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) = 0 := by
    intro x hx w hw
    rw [← mem_centralizer_iff.mp (H.U₁_le_centralizer_V₁ hx) w hw, mul_inv_cancel_right,
      inv_mul_cancel, one_pow, H.coords.v_one]
  obtain ⟨D, hD'⟩ := exists_addMonoidHom₂_of_hom (M := U₁') (S := S')
    (Φ := fun x b => v (((H.sec b)⁻¹ * (x * H.sec b * x⁻¹)) ^ 2 ^ k)) hS'mul hS'surj
    (fun x hx y hy b => hD.M_mul (hle hx) (hle hy) (H.sec_mem b))
    (fun x hx b b' => by
      show v (((H.sec (b + b'))⁻¹ * (x * H.sec (b + b') * x⁻¹)) ^ 2 ^ k) =
        v (((H.sec b)⁻¹ * (x * H.sec b * x⁻¹)) ^ 2 ^ k) +
          v (((H.sec b')⁻¹ * (x * H.sec b' * x⁻¹)) ^ 2 ^ k)
      rw [hD.M_eq_of_X_eq (hle hx) (H.sec_mem (b + b')) (mul_mem (H.sec_mem b) (H.sec_mem b'))
        (by rw [H.sec_X, H.X_mul (H.sec_mem b) (H.sec_mem b'), H.sec_X, H.sec_X]),
        hD.M_mul_right (hle hx) (H.sec_mem b) (H.sec_mem b')])
    (fun x hx h0 b => hU₁M x (hS'ker x hx h0) _ (H.sec_mem b))
  have hM : ∀ x ∈ U₁', ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G),
      v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) = D (S' x) (v (w ^ 2 ^ (k + 1))) := by
    intro x hx w hw
    rw [hD.M_eq_of_X_eq (hle hx) hw (H.sec_mem _) (H.sec_X _).symm]
    exact hD' x hx _
  obtain ⟨C, hC⟩ := bilinear_eq_mul_sqrt_of_equivariant H.card_K (by omega) D H.gen
    fun s b => by
      obtain ⟨x, hx, rfl⟩ := hS'surj s
      have hdx : d⁻¹ * x * d ∈ U₁' := by
        simpa using (mem_normalizer_iff.mp (inv_mem hd) x).mp hx
      have hdw := H.stage.conj_d_mem_V₁ (H.sec_mem b)
      have e1 := hM _ hdx _ hdw
      rw [hD.M_conj_d (hle hx) (H.sec_mem b), H.X_conj_d (H.sec_mem b), H.sec_X] at e1
      have e2 : S' (d⁻¹ * x * d) = μ * S' x := hD.S'_conj_d (hle hx)
      rw [e2] at e1
      rw [← e1, hM x hx _ (H.sec_mem b), H.sec_X]
  have hidem : ∀ x ∈ U₁', ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G),
      D (S' x) (v (w ^ 2 ^ (k + 1))) = D (S' x) (D (S' x) (v (w ^ 2 ^ (k + 1)))) := by
    intro x hx w hw
    have hxU' := hle hx
    have hcV := hD.chi_mem_V hxU' hw
    obtain ⟨s, hs, hs2⟩ := H.exists_sq_of_mem_V hcV
    have hx2 : x * (x * w * x⁻¹) * x⁻¹ = w := by
      have h1 := mem_centralizer_iff.mp
        (H.U₁_le_centralizer_V₁ (hD.sq_mem_U₁ hxU')) w hw
      calc x * (x * w * x⁻¹) * x⁻¹ = x ^ 2 * w * (x ^ 2)⁻¹ := by rw [sq]; group
        _ = w := by rw [← h1, mul_inv_cancel_right]
    have e1 := SzC1.chi_sq_mul_chi_chi hx2
    rw [hs2, sq s, hD.chi_mul_right hxU' hs hs, ← sq (s⁻¹ * (x * s * x⁻¹)),
      ← sq s, ← hs2] at e1
    have e2 : (w⁻¹ * (x * w * x⁻¹)) ^ 2 = ((s⁻¹ * (x * s * x⁻¹)) ^ 2)⁻¹ :=
      eq_inv_of_mul_eq_one_left e1
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := H.stage.one_le; omega⟩
    have hcs := hD.chi_mem_V hxU' hs
    have hMeq : v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) = v ((s⁻¹ * (x * s * x⁻¹)) ^ 2 ^ k) := by
      rw [hj, pow_succ', pow_mul, e2, inv_pow, ← pow_mul, ← pow_succ',
        H.inv_eq_self_of_mem_szA₁ (by rw [← hj]; exact H.stage.pow_mem_szA₁ hcs)]
    have hXs : v (s ^ 2 ^ (k + 1)) = v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) := by
      rw [hs2, pow_succ', pow_mul]
    calc D (S' x) (v (w ^ 2 ^ (k + 1))) = v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k) :=
          (hM x hx w hw).symm
      _ = v ((s⁻¹ * (x * s * x⁻¹)) ^ 2 ^ k) := hMeq
      _ = D (S' x) (v (s ^ 2 ^ (k + 1))) := hM x hx s hs
      _ = D (S' x) (v ((w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k)) := by rw [hXs]
      _ = D (S' x) (D (S' x) (v (w ^ 2 ^ (k + 1)))) := by rw [hM x hx w hw]
  have hC0 : C = 0 := by
    obtain ⟨x₁, hx₁, hS₁⟩ := hS'surj 1
    refine SzC1.eq_zero_of_idem H.card_K hf fun b => ?_
    have e := hidem x₁ hx₁ (H.sec b) (H.sec_mem b)
    rw [H.sec_X, hS₁, hC, hC, one_mul, one_mul] at e
    exact e.symm
  intro x hx w hw
  have hxU' := hle hx
  have hxN := hD.le hxU'
  have hk1 : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G),
      (w⁻¹ * (x * w * x⁻¹)) ^ 2 ^ k = 1 := by
    intro w hw
    have hcV := hD.chi_mem_V hxU' hw
    refine H.coords.eq_one_of_v_eq_zero (H.stage.pow_mem_szA₁ hcV) ?_
    rw [hM x hx w hw, hC, hC0, zero_mul]
  have h4 : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), ∃ s ∈ U₁ ⊓ centralizer (szT₁ L T : Set G),
      w⁻¹ * (x * w * x⁻¹) = s ^ 4 := by
    intro w hw
    have hcV₁ := H.V_le_V₁ (hD.chi_mem_V hxU' hw)
    have hc1 := hk1 w hw
    obtain ⟨w₁, hw₁, hw₁e⟩ := H.exists_sq_of_pow_eq_one hcV₁ (by
      rw [pow_succ, pow_mul, hc1, one_pow])
    obtain ⟨s, hs, hse⟩ := H.exists_sq_of_pow_eq_one hw₁ (by
      rw [pow_succ', pow_mul, ← hw₁e, hc1])
    exact ⟨s, hs, by rw [hw₁e, hse, ← pow_mul]⟩
  have hx2 : ∀ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), x * (x * w * x⁻¹) * x⁻¹ = w := by
    intro w hw
    have h1 := mem_centralizer_iff.mp
      (H.U₁_le_centralizer_V₁ (hD.sq_mem_U₁ hxU')) w hw
    calc x * (x * w * x⁻¹) * x⁻¹ = x ^ 2 * w * (x ^ 2)⁻¹ := by rw [sq]; group
      _ = w := by rw [← h1, mul_inv_cancel_right]
  have hsq := SzC1.sq_chi_eq_one hV₁comm hV₁pow (fun w hw => H.conj_mem_V₁ hxN hw) hx2 h4 w hw
  exact H.stage.omega _ (hD.chi_mem_V hxU' hw) hsq

theorem exists_levelData :
    ∃ U₁' : Subgroup G,
      U3C1LevelData G L f t T d (U₁ ⊓ centralizer (szT₁ L T : Set G)) U' U₁' (k + 1) := by
  obtain ⟨U₁', hHU₁, hU₁U, hUU₁, htU₁, hsupU₁, hdU₁, hinf⟩ := hD.exists_U₁'
  have hR := H.stage.szR_V₁_eq H.lam
  refine ⟨U₁',
    { U_le := by rw [hR]; exact hD.le
      U_normal := by rw [hR]; exact hD.normal
      isSylowOf := by rw [hR]; exact hD.isSylowOf
      card_U := hD.card
      szR_le := by rw [hR]; exact hD.U_le
      conj_t_not_mem := fun u hu huR => hD.conj_t_not_mem hu (by rwa [hR] at huR)
      conj_szA₁ := fun u hu b hb => hD.conj_szA₁ hu b hb
      conj_T₁ := hD.conj_T₁
      conj_V₁ := hD.conj_V₁_of_mem_U₁' hU₁U hUU₁ hsupU₁ hdU₁ hinf
      inf_centralizer := hD.inf_centralizer
      U₁_le := hU₁U
      U₁_normal := hUU₁
      sup_eq := hsupU₁
      t_not_mem := htU₁
      inf_eq := by rw [hR, hinf]; exact H.lam
      d_mem_U₁ := hdU₁ }⟩

end NextUData

end U3C1Next

end CFSG.SeitzReduction.RankOne
