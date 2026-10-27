module

public import CFSG.ClassicalInvolution.Asc77.AscT3RAct

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII.T3R

open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.GorensteinWalter
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open CFSG.RankThree.PartTwo.KFacts
open scoped MatrixGroups commutatorElement

theorem z2_cases (g : Multiplicative (ZMod 2)) : g = 1 ∨ g ≠ 1 ∧ g * g = 1 := by
  revert g
  decide

theorem z2_mul_of_ne_one {g h : Multiplicative (ZMod 2)} (hg : g ≠ 1) (hh : h ≠ 1) :
    g * h = 1 := by
  revert g h
  decide

theorem z2_mul_ne_one {g h : Multiplicative (ZMod 2)} (hg : g ≠ 1) (hh : h = 1) :
    g * h ≠ 1 := by
  rw [hh, mul_one]
  exact hg

section Psi

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F]
  {L : Subgroup G} {e : ↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, F)}
  (hK : IsOddPrimePower (Nat.card F))

@[expose] noncomputable def epsG (L : Subgroup G)
    (e : ↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, F)) (x : G) : Multiplicative (ZMod 2) :=
  slEps F hK (phiG L e x)

@[expose] noncomputable def rhoG (L : Subgroup G)
    (e : ↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, F)) (x : G) : F ≃+* F :=
  slRho F (phiG L e x)

variable {hK}

theorem epsG_mul {x y : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hy : y ∈ Subgroup.normalizer (L : Set G)) :
    epsG hK L e (x * y) = epsG hK L e x * epsG hK L e y := by
  simp only [epsG, phiG_mul hx hy, map_mul]

theorem rhoG_mul {x y : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hy : y ∈ Subgroup.normalizer (L : Set G)) :
    rhoG L e (x * y) = rhoG L e x * rhoG L e y := by
  simp only [rhoG, phiG_mul hx hy, map_mul]

theorem epsG_inv {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    epsG hK L e x⁻¹ = (epsG hK L e x)⁻¹ := by
  unfold epsG
  rw [phiG_inv hx]
  exact map_inv _ _

theorem rhoG_inv {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    rhoG L e x⁻¹ = (rhoG L e x)⁻¹ := by
  unfold rhoG
  rw [phiG_inv hx]
  exact map_inv _ _

theorem epsG_one : epsG hK L e 1 = 1 := by
  simp [epsG, phiG_one]

theorem rhoG_one : rhoG L e 1 = 1 := by
  simp [rhoG, phiG_one]

theorem rhoG_comm (x y : G) : rhoG L e x * rhoG L e y = rhoG L e y * rhoG L e x :=
  CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm F _ _

@[expose] noncomputable def psi (hK : IsOddPrimePower (Nat.card F)) (L : Subgroup G)
    (e : ↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, F)) (v x : G) : F ≃+* F :=
  open Classical in
  rhoG L e x * (if epsG hK L e x = 1 then 1 else rhoG L e v)

theorem psi_mul {v : G} (hv : rhoG L e v * rhoG L e v = 1) {x y : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (hy : y ∈ Subgroup.normalizer (L : Set G)) :
    psi hK L e v (x * y) = psi hK L e v x * psi hK L e v y := by
  classical
  unfold psi
  rw [rhoG_mul hx hy, epsG_mul hx hy]
  by_cases h1 : epsG hK L e x = 1 <;> by_cases h2 : epsG hK L e y = 1
  · simp [h1, h2]
  · simp [h1, h2]
    exact mul_assoc _ _ _
  · simp [h1, h2]
    rw [mul_assoc (rhoG L e x) (rhoG L e y), rhoG_comm y v, ← mul_assoc]
  · have h3 : epsG hK L e x * epsG hK L e y = 1 := z2_mul_of_ne_one h1 h2
    simp [h1, h2, h3]
    have hc := rhoG_comm (L := L) (e := e) y v
    calc rhoG L e x * rhoG L e y
        = rhoG L e x * rhoG L e y * (rhoG L e v * rhoG L e v) := by rw [hv, mul_one]
      _ = rhoG L e x * (rhoG L e y * rhoG L e v) * rhoG L e v := by group
      _ = rhoG L e x * (rhoG L e v * rhoG L e y) * rhoG L e v := by rw [hc]
      _ = _ := by group

theorem psi_one (v : G) : psi hK L e v 1 = 1 := by
  classical
  simp [psi, rhoG_one, epsG_one]

theorem mem_of_inner_action [Finite G] (hF : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    {T RL Rp : Subgroup G} (hT2 : IsPGroup 2 ↥T) (hTN : T ≤ Subgroup.normalizer (L : Set G))
    (hRT : RL ≤ T) (hRL : IsSylow2In RL L) (hRp : ∀ y ∈ T, phiG L e y = 1 → y ∈ Rp)
    {y : G} (hyT : y ∈ T) (hε : epsG hK L e y = 1) (hρ : rhoG L e y = 1) : y ∈ RL ⊔ Rp := by
  have hin : phiG L e y ∈ (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range :=
    (slEps_slRho_eq_one_iff F hK h4 _).mp ⟨hε, hρ⟩
  obtain ⟨r, hr, hry⟩ := exists_mem_of_phiG_inner hF hT2 hTN hRT hRL hyT hin
  have hrN : r ∈ Subgroup.normalizer (L : Set G) := hTN (hRT hr)
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hTN hyT
  have h1 : phiG L e (r⁻¹ * y) = 1 := by
    rw [phiG_mul (Subgroup.inv_mem _ hrN) hyN, phiG_inv hrN, hry, inv_mul_cancel]
  have h2 : r⁻¹ * y ∈ Rp := hRp _ (T.mul_mem (T.inv_mem (hRT hr)) hyT) h1
  have : y = r * (r⁻¹ * y) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right h2)

theorem mem_of_psi_eq_one [Finite G] (hF : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    {T RL Rp V : Subgroup G} {v : G} (hT2 : IsPGroup 2 ↥T)
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) (hRT : RL ≤ T) (hRL : IsSylow2In RL L)
    (hRp : ∀ y ∈ T, phiG L e y = 1 → y ∈ Rp) (hvV : v ∈ V) (hvT : v ∈ T)
    (hεv : epsG hK L e v ≠ 1) {x : G} (hxT : x ∈ T) (hψ : psi hK L e v x = 1) :
    x ∈ RL ⊔ Rp ⊔ V := by
  classical
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := hTN hxT
  have hvN : v ∈ Subgroup.normalizer (L : Set G) := hTN hvT
  by_cases hε : epsG hK L e x = 1
  · have hρ : rhoG L e x = 1 := by
      simpa [psi, hε] using hψ
    exact Subgroup.mem_sup_left (mem_of_inner_action hF h4 hT2 hTN hRT hRL hRp hxT hε hρ)
  · have hρ : rhoG L e x * rhoG L e v = 1 := by
      simpa [psi, hε] using hψ
    have hxv : x * v ∈ T := T.mul_mem hxT hvT
    have hε' : epsG hK L e (x * v) = 1 := by
      rw [epsG_mul hxN hvN]
      exact z2_mul_of_ne_one hε hεv
    have hρ' : rhoG L e (x * v) = 1 := by
      rw [rhoG_mul hxN hvN]
      exact hρ
    have h1 := mem_of_inner_action hF h4 hT2 hTN hRT hRL hRp hxv hε' hρ'
    have : x = (x * v) * v⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1)
      (Subgroup.mem_sup_right (V.inv_mem hvV))

theorem psi_inv {v : G} (hv : rhoG L e v * rhoG L e v = 1) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    psi hK L e v x⁻¹ = (psi hK L e v x)⁻¹ := by
  have h := psi_mul (hK := hK) hv (Subgroup.inv_mem _ hx) hx
  rw [inv_mul_cancel, psi_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem epsG_of_mem_L {x : G} (hx : x ∈ L) : epsG hK L e x = 1 := by
  rw [epsG, phiG_of_mem_L hx]
  exact slEps_conj F hK _

theorem rhoG_of_mem_L {x : G} (hx : x ∈ L) : rhoG L e x = 1 := by
  rw [rhoG, phiG_of_mem_L hx]
  exact slRho_conj F _

theorem epsG_of_phiG_eq_one {x : G} (h : phiG L e x = 1) : epsG hK L e x = 1 := by
  rw [epsG, h, map_one]

theorem rhoG_of_phiG_eq_one {x : G} (h : phiG L e x = 1) : rhoG L e x = 1 := by
  rw [rhoG, h, map_one]

@[expose] def psiKer {v : G} (hv : rhoG L e v * rhoG L e v = 1) (T : Subgroup G)
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) : Subgroup G where
  carrier := {x | x ∈ T ∧ psi hK L e v x = 1}
  one_mem' := ⟨T.one_mem, psi_one v⟩
  mul_mem' := by
    rintro x y ⟨hxT, hx⟩ ⟨hyT, hy⟩
    exact ⟨T.mul_mem hxT hyT, by rw [psi_mul hv (hTN hxT) (hTN hyT), hx, hy, mul_one]⟩
  inv_mem' := by
    rintro x ⟨hxT, hx⟩
    exact ⟨T.inv_mem hxT, by rw [psi_inv hv (hTN hxT), hx, inv_one]⟩

theorem psi_eq_one_of_mem {T RL Rp V : Subgroup G} {v : G} (hv : rhoG L e v * rhoG L e v = 1)
    (hεv : epsG hK L e v ≠ 1) (hTN : T ≤ Subgroup.normalizer (L : Set G)) (hRL : RL ≤ L)
    (hRT : RL ≤ T) (hRpT : Rp ≤ T) (hRp : ∀ y ∈ Rp, phiG L e y = 1) (hvT : v ∈ T)
    (hV : V = Subgroup.zpowers v) {x : G} (hx : x ∈ RL ⊔ Rp ⊔ V) : psi hK L e v x = 1 := by
  classical
  have hle : RL ⊔ Rp ⊔ V ≤ psiKer (hK := hK) (e := e) hv T hTN := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro r hr
      refine ⟨hRT hr, ?_⟩
      have h1 := epsG_of_mem_L (hK := hK) (e := e) (hRL hr)
      have h2 := rhoG_of_mem_L (e := e) (hRL hr)
      simp [psi, h1, h2]
    · intro y hy
      refine ⟨hRpT hy, ?_⟩
      have h1 := epsG_of_phiG_eq_one (hK := hK) (hRp y hy)
      have h2 := rhoG_of_phiG_eq_one (hRp y hy)
      simp [psi, h1, h2]
    · rw [hV, Subgroup.zpowers_le]
      refine ⟨hvT, ?_⟩
      simp [psi, hεv, hv]
  exact (hle hx).2

theorem psi_mul_eq_one {v : G} (hv : rhoG L e v * rhoG L e v = 1) {x y : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (hy : y ∈ Subgroup.normalizer (L : Set G))
    (hx1 : psi hK L e v x ≠ 1) (hy1 : psi hK L e v y ≠ 1)
    (hx2 : psi hK L e v x * psi hK L e v x = 1) (hy2 : psi hK L e v y * psi hK L e v y = 1) :
    psi hK L e v (x * y) = 1 := by
  have hcyc : IsCyclic (F ≃+* F) := CFSG.LieType.Chevalley.ringAut_isCyclic
  have hfin : Finite (F ≃+* F) := finite_ringAut F
  have := eq_of_sq_eq_one_of_isCyclic hx2 hy2 hx1 hy1
  rw [psi_mul hv hx hy, ← this, hx2]

omit [Finite F] in
theorem phiG_pow {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) (n : ℕ) :
    phiG L e (x ^ n) = (phiG L e x) ^ n := by
  induction n with
  | zero => simp [phiG_one]
  | succ n ih =>
    rw [pow_succ, phiG_mul (Subgroup.pow_mem _ hx n) hx, ih, pow_succ]

theorem epsG_ne_one_of_cyclic [Finite G] (hF : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    {RL : Subgroup G} (hRL : IsSylow2In RL L) {w : G}
    (hwN : w ∈ Subgroup.normalizer (L : Set G))
    (hsq : ∃ k ∈ L, ∃ y ∈ cStar L, w * w = k * y) (hord : 2 * orderOf w = Nat.card RL)
    (hinj : ∀ n : ℕ, w ^ n ∈ cStar L → w ^ n = 1) : epsG hK L e w ≠ 1 := by
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 SL(2, F)))
  have hβ2 : IsInnerAut (phiG L e w * phiG L e w) := by
    obtain ⟨k, hk, y, hy, hwky⟩ := hsq
    have hkN : k ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hk
    have hyN : y ∈ Subgroup.normalizer (L : Set G) := cStar_le_normalizer L hy
    have h1 : phiG L e (w * w) = phiG L e w * phiG L e w := phiG_mul hwN hwN
    rw [← h1, hwky, phiG_mul hkN hyN, (phiG_eq_one_iff hyN).mpr hy, mul_one,
      phiG_of_mem_L hk]
    exact ⟨_, rfl⟩
  have hordβ : orderOf (phiG L e w) = orderOf w := by
    rw [orderOf_eq_orderOf_iff]
    intro n
    rw [← phiG_pow hwN n]
    constructor
    · intro h
      exact hinj n ((phiG_eq_one_iff (Subgroup.pow_mem _ hwN n)).mp h)
    · intro h
      rw [h, phiG_one]
  have hcard : Nat.card RL = Nat.card Q := natCard_isSylow2In_eq_natCard_sylow (e := e) Q hRL
  exact slEps_ne_one_of_orderOf hF hK h4 Q hβ2 (by rw [hordβ, hord, hcard])

@[expose] def epsKer (hK : IsOddPrimePower (Nat.card F)) (L : Subgroup G)
    (e : ↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, F)) : Subgroup G where
  carrier := {x | x ∈ Subgroup.normalizer (L : Set G) ∧ epsG hK L e x = 1}
  one_mem' := ⟨Subgroup.one_mem _, epsG_one⟩
  mul_mem' := by
    rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
    exact ⟨Subgroup.mul_mem _ hxN hyN, by rw [epsG_mul hxN hyN, hx, hy, mul_one]⟩
  inv_mem' := by
    rintro x ⟨hxN, hx⟩
    exact ⟨Subgroup.inv_mem _ hxN, by rw [epsG_inv hxN, hx]; decide⟩

theorem epsG_eq_one_of_mem_sup {R₁ R₂ : Subgroup G}
    (h₁ : ∀ x ∈ R₁, x ∈ Subgroup.normalizer (L : Set G) ∧ epsG hK L e x = 1)
    (h₂ : ∀ x ∈ R₂, x ∈ Subgroup.normalizer (L : Set G) ∧ epsG hK L e x = 1) {x : G}
    (hx : x ∈ R₁ ⊔ R₂) : epsG hK L e x = 1 := by
  have hle : R₁ ⊔ R₂ ≤ epsKer hK L e := sup_le (fun y hy => h₁ y hy) (fun y hy => h₂ y hy)
  exact (hle hx).2

theorem psi_pow {v : G} (hv : rhoG L e v * rhoG L e v = 1) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (n : ℕ) :
    psi hK L e v (x ^ n) = (psi hK L e v x) ^ n := by
  induction n with
  | zero => simp [psi_one]
  | succ n ih =>
    rw [pow_succ, psi_mul hv (Subgroup.pow_mem _ hx n) hx, ih, pow_succ]

end Psi

end CFSG.ClassicalInvolution.Asc77.T3CII.T3R
