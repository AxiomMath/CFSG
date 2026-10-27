module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4N0StructMod

public section

namespace CFSG.OddStandard.AltStdSmall4.N0

open Subgroup Equiv Equiv.Perm AltStdCycTwo

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ}

structure TData (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (z : G) (P T : Subgroup G)
    (s : G) : Prop where
  le_P : T ≤ P
  E_le : E θ hn ≤ T
  conj_s : ∀ t ∈ T, s * t * s⁻¹ ∈ T
  conj_P : ∀ p ∈ P, ∀ t ∈ T, p * t * p⁻¹ ∈ T
  cent : ∀ t ∈ T, t * z = z * t → t ∈ E θ hn
  trans : ∀ j, ∃ t ∈ T, bz z t = eps θ hn j

section Setup

variable [Finite G] {Q : Subgroup G} {θ : L ≃* alternatingGroup (Fin n)} {z : G}
  (hn : 8 ≤ n) (c : Config G L Q n θ z)
  (hF : ∃ g ∈ N0 θ hn z, g * z * g⁻¹ = z * w θ hn)
  {P O : Subgroup G} {s : G} (hS : SetupData θ hn z P O s)

include c hF hS

theorem cm_s_mem_P {q : G} (hq : q ∈ P) : cm q s ∈ P := by
  have : cm q s = q * (s * q⁻¹ * s⁻¹) := by simp only [cm]; group
  rw [this]
  exact mul_mem hq (conj_s_mem hn c hS (inv_mem hq))

theorem E_le_P : E θ hn ≤ P := fun _ he => hS.B0_le (mem_sup_left he)

theorem cm_s_of_mem_B0 {q : G} (hq : q ∈ B0 θ hn z) : cm q s ∈ E θ hn := by
  obtain ⟨i, rfl | rfl⟩ := (mem_B0_iff hn c q).1 hq
  · have : cm (eps θ hn i) s = eps θ hn i * (s * eps θ hn i * s⁻¹)⁻¹ := by simp only [cm]; group
    rw [this, hS.s_conj]
    exact mul_mem (eps_mem_E θ hn i) (inv_mem (eps_mem_E θ hn _))
  · have hsz : s * z * s⁻¹ = z := by rw [hS.s_comm]; group
    have : cm (z * eps θ hn i) s =
        z * (eps θ hn i * (s * eps θ hn i * s⁻¹)⁻¹) * (s * z * s⁻¹)⁻¹ := by
      simp only [cm]; group
    rw [this, hsz, hS.s_conj, eps_inv, eps_mul, ← eps_comm_z hn c, mul_inv_cancel_right]
    exact eps_mem_E θ hn _

theorem bz_cm_s {q : G} (hq : q ∈ P) (i : Fin 8) (hqi : bz z q = eps θ hn i) :
    bz z (cm q s) = eps θ hn (i ^^^ mPerm i) := by
  have hq' : s * q⁻¹ * s⁻¹ ∈ P := conj_s_mem hn c hS (inv_mem hq)
  have : cm q s = q * (s * q⁻¹ * s⁻¹) := by simp only [cm]; group
  rw [this, bz_mul hn c (hS.P_le hq) (hS.P_le hq'), bz_conj_of_comm c hS.s_comm,
    bz_inv hn c (hS.P_le hq), hqi, eps_inv, hS.s_conj, eps_mul]

theorem exists_T : ∃ T : Subgroup G, TData θ hn z P T s := by
  have hcmE := fun {p q : G} (hp : p ∈ P) (hq : q ∈ P) => cm_mem_E hn c hF hS hp hq
  have hcentral : ∀ {p e : G}, p ∈ P → e ∈ E θ hn → p * e = e * p :=
    fun hp he => P_comm_E hn c hS hp he
  let T : Subgroup G :=
    { carrier := {t | ∃ q ∈ P, ∃ e ∈ E θ hn, t = cm q s * e}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp [cm]⟩
      mul_mem' := by
        rintro _ _ ⟨q₁, hq₁, e₁, he₁, rfl⟩ ⟨q₂, hq₂, e₂, he₂, rfl⟩
        have hxP : cm q₁ s ∈ P := cm_s_mem_P hn c hF hS hq₁
        have hyP : cm q₂ s ∈ P := cm_s_mem_P hn c hF hS hq₂
        have hfE : cm (cm q₁ s)⁻¹ q₂ ∈ E θ hn := hcmE (inv_mem hxP) hq₂
        have h1 : cm (q₂ * q₁) s = cm q₁ s * cm q₂ s * cm (cm q₁ s)⁻¹ q₂ := by
          have h2 : cm (q₂ * q₁) s =
              cm q₁ s * (cm (cm q₁ s)⁻¹ q₂ * cm q₂ s) := by
            simp only [cm]; group
          rw [h2, ← hcentral hyP hfE, mul_assoc]
        refine ⟨q₂ * q₁, mul_mem hq₂ hq₁, (cm (cm q₁ s)⁻¹ q₂)⁻¹ * e₁ * e₂,
          mul_mem (mul_mem (inv_mem hfE) he₁) he₂, ?_⟩
        rw [h1]
        calc cm q₁ s * e₁ * (cm q₂ s * e₂) = cm q₁ s * (e₁ * cm q₂ s) * e₂ := by group
          _ = cm q₁ s * (cm q₂ s * e₁) * e₂ := by rw [hcentral hyP he₁]
          _ = cm q₁ s * cm q₂ s * cm (cm q₁ s)⁻¹ q₂ *
              ((cm (cm q₁ s)⁻¹ q₂)⁻¹ * e₁ * e₂) := by group
      inv_mem' := by
        rintro _ ⟨q, hq, e, he, rfl⟩
        have hxP : cm q s ∈ P := cm_s_mem_P hn c hF hS hq
        have huP : s * q * s⁻¹ ∈ P := conj_s_mem hn c hS hq
        have hgE : cm (s * q * s⁻¹)⁻¹ q ∈ E θ hn := hcmE (inv_mem huP) hq
        have h1 : (cm q s)⁻¹ = cm q⁻¹ s * cm (s * q * s⁻¹)⁻¹ q := by
          simp only [cm]; group
        refine ⟨q⁻¹, inv_mem hq, cm (s * q * s⁻¹)⁻¹ q * e⁻¹, mul_mem hgE (inv_mem he), ?_⟩
        rw [mul_inv_rev, ← hcentral (inv_mem hxP) (inv_mem he), h1, mul_assoc] }
  have hmemT : ∀ t, t ∈ T ↔ ∃ q ∈ P, ∃ e ∈ E θ hn, t = cm q s * e := fun t => Iff.rfl
  have hTP : T ≤ P := by
    rintro _ ⟨q, hq, e, he, rfl⟩
    exact mul_mem (cm_s_mem_P hn c hF hS hq) (E_le_P hn c hF hS he)
  refine ⟨T, hTP, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    exact ⟨1, one_mem _, e, he, by simp [cm]⟩
  · rintro _ ⟨q, hq, e, he, rfl⟩
    refine ⟨s * q * s⁻¹, conj_s_mem hn c hS hq, s * e * s⁻¹, ?_, ?_⟩
    · obtain ⟨i, rfl⟩ := (mem_E_iff θ hn e).1 he
      rw [hS.s_conj]
      exact eps_mem_E θ hn _
    · simp only [cm]; group
  · intro p hp t ht
    have h1 : p * t * p⁻¹ = cm p t * t := by simp only [cm]; group
    rw [h1]
    refine mul_mem ?_ ht
    exact ⟨1, one_mem _, cm p t, hcmE hp (hTP ht), by simp [cm]⟩
  · rintro _ ⟨q, hq, e, he, rfl⟩ hz
    have hB := P_mem_B0_of_comm hn c hS (hTP ⟨q, hq, e, he, rfl⟩) hz
    have hbz : bz z (cm q s * e) = 1 := (bz_eq_one_iff _).2 hz
    obtain ⟨i, hi⟩ := (mem_E_iff θ hn _).1 (bz_mem_E hn c (P_le_N0 hn c hS hq))
    have heD : e ∈ D0 θ hn z := hS.P_le (E_le_P hn c hF hS he)
    rw [bz_mul hn c (hS.P_le (cm_s_mem_P hn c hF hS hq)) heD, bz_cm_s hn c hF hS hq i hi] at hbz
    have hbe : bz z e = 1 := by
      obtain ⟨k, rfl⟩ := (mem_E_iff θ hn e).1 he
      exact bz_of_comm (eps_comm_z hn c k)
    rw [hbe, mul_one, eps_eq_one_iff, xor_mPerm_eq_zero] at hbz
    rw [hbz, eps_zero] at hi
    have hqB := P_mem_B0_of_comm hn c hS hq ((bz_eq_one_iff q).1 hi)
    exact mul_mem (cm_s_of_mem_B0 hn c hF hS hqB) he
  · intro j
    obtain ⟨i, hi⟩ := exists_xor_mPerm_eq j
    obtain ⟨q, hq, hqi⟩ := P_trans hn c hF hS i
    refine ⟨cm q s, ⟨q, hq, 1, one_mem _, by rw [mul_one]⟩, ?_⟩
    rw [bz_cm_s hn c hF hS hq i hqi, hi]

end Setup

section TProps

variable [Finite G] {Q : Subgroup G} {θ : L ≃* alternatingGroup (Fin n)} {z : G}
  (hn : 8 ≤ n) (c : Config G L Q n θ z)
  (hF : ∃ g ∈ N0 θ hn z, g * z * g⁻¹ = z * w θ hn)
  {P O : Subgroup G} {s : G} (hS : SetupData θ hn z P O s) {T : Subgroup G}
  (hT : TData θ hn z P T s)

include c hF hS hT

theorem TData.le_D0 : T ≤ D0 θ hn z := hT.le_P.trans hS.P_le

theorem TData.inv_mul_mem_E {x y : G} (hx : x ∈ T) (hy : y ∈ T) (h : bz z x = bz z y) :
    x⁻¹ * y ∈ E θ hn := by
  apply hT.cent _ (mul_mem (inv_mem hx) hy)
  rw [← bz_eq_one_iff, bz_mul hn c (inv_mem (hT.le_D0 hn c hF hS hx)) (hT.le_D0 hn c hF hS hy),
    bz_inv hn c (hT.le_D0 hn c hF hS hx), h, inv_mul_cancel]

theorem TData.conj_s_pow (k : ℕ) {t : G} (ht : t ∈ T) : s ^ k * t * (s ^ k)⁻¹ ∈ T := by
  induction k with
  | zero => simpa using ht
  | succ k ih =>
    have := hT.conj_s _ ih
    rwa [show s * (s ^ k * t * (s ^ k)⁻¹) * s⁻¹ = s ^ (k + 1) * t * (s ^ (k + 1))⁻¹ by
      rw [pow_succ']; group] at this

theorem TData.exists_gens : ∃ t₀ ∈ T, ∀ k : ℕ, s ^ k * t₀ * (s ^ k)⁻¹ ∈ T ∧
    bz z (s ^ k * t₀ * (s ^ k)⁻¹) = eps θ hn ((mPerm ^ k) 1) := by
  obtain ⟨t₀, ht₀, hb⟩ := hT.trans 1
  refine ⟨t₀, ht₀, fun k => ⟨hT.conj_s_pow hn c hF hS k ht₀, ?_⟩⟩
  rw [bz_conj_of_comm c (s_pow_comm_z hn c hS k), hb, s_pow_conj_eps hn c hS]

theorem TData.cm_mem_E {x y : G} (hx : x ∈ T) (hy : y ∈ T) : cm x y ∈ E θ hn :=
  N0.cm_mem_E hn c hF hS (hT.le_P hx) (hT.le_P hy)

theorem TData.central {x e : G} (hx : x ∈ T) (he : e ∈ E θ hn) : x * e = e * x :=
  P_comm_E hn c hS (hT.le_P hx) he

theorem TData.comm {x y : G} (hx : x ∈ T) (hy : y ∈ T) : x * y = y * x := by
  obtain ⟨t₀, ht₀, hgen⟩ := hT.exists_gens hn c hF hS
  set tk : ℕ → G := fun k => s ^ k * t₀ * (s ^ k)⁻¹ with htk
  have htkT : ∀ k, tk k ∈ T := fun k => (hgen k).1
  have hbk : ∀ k, bz z (tk k) = eps θ hn ((mPerm ^ k) 1) := fun k => (hgen k).2
  have hm : ∀ k : Fin 8, (mPerm ^ (k : ℕ)) 1 = ![1, 2, 4, 3, 6, 7, 5, 1] k := by decide
  have hb : ∀ k : Fin 8, bz z (tk k) = eps θ hn (![1, 2, 4, 3, 6, 7, 5, 1] k) :=
    fun k => by rw [hbk, hm]
  have hb0 : bz z (tk 0) = eps θ hn 1 := hb 0
  have hb1 : bz z (tk 1) = eps θ hn 2 := hb 1
  have hb2 : bz z (tk 2) = eps θ hn 4 := hb 2
  have hb3 : bz z (tk 3) = eps θ hn 3 := hb 3
  have hb6 : bz z (tk 6) = eps θ hn 5 := hb 6
  have hb7 : bz z (tk 7) = eps θ hn 1 := hb 7
  have hD : ∀ k, tk k ∈ D0 θ hn z := fun k => hT.le_D0 hn c hF hS (htkT k)
  have hsucc : ∀ k, tk (k + 1) = s * tk k * s⁻¹ := by
    intro k; simp only [htk, pow_succ']; group
  have hcm : ∀ {a b : G}, a ∈ T → b ∈ T → cm a b ∈ E θ hn :=
    fun ha hb => hT.cm_mem_E hn c hF hS ha hb
  have hrm : ∀ {a b b' : G}, a ∈ T → b ∈ T → b' ∈ T → cm a (b * b') = cm a b * cm a b' := by
    intro a b b' ha hb hb'
    rw [cm_mul_right, hT.central hn c hF hS hb (hcm ha hb'), mul_inv_cancel_right]
  have hlm : ∀ {a a' b : G}, a ∈ T → a' ∈ T → b ∈ T → cm (a * a') b = cm a' b * cm a b := by
    intro a a' b ha ha' hb
    rw [cm_mul_left, hT.central hn c hF hS ha (hcm ha' hb), mul_inv_cancel_right]
  have hcmE : ∀ {a e : G}, a ∈ T → e ∈ E θ hn → cm a e = 1 := by
    intro a e ha he
    rw [cm, hT.central hn c hF hS ha he, mul_inv_cancel_right, mul_inv_cancel]
  have hcmE' : ∀ {a e : G}, a ∈ T → e ∈ E θ hn → cm e a = 1 := by
    intro a e ha he
    rw [← cm_inv, hcmE ha he, inv_one]
  obtain ⟨a, ha⟩ := (mem_E_iff θ hn _).1 (hcm (htkT 0) (htkT 1))
  have hadj : ∀ k, cm (tk k) (tk (k + 1)) = eps θ hn ((mPerm ^ k) a) := by
    intro k
    induction k with
    | zero => simpa using ha
    | succ k ih =>
      have e : tk (k + 1) = s * tk k * s⁻¹ := hsucc k
      have e' : tk (k + 1 + 1) = s * tk (k + 1) * s⁻¹ := hsucc (k + 1)
      calc cm (tk (k + 1)) (tk (k + 1 + 1)) = cm (s * tk k * s⁻¹) (s * tk (k + 1) * s⁻¹) := by
            rw [← e, ← e']
        _ = s * cm (tk k) (tk (k + 1)) * s⁻¹ := cm_conj _ _ _
        _ = s * eps θ hn ((mPerm ^ k) a) * s⁻¹ := by rw [ih]
        _ = eps θ hn (mPerm ((mPerm ^ k) a)) := hS.s_conj _
        _ = eps θ hn ((mPerm ^ (k + 1)) a) := by rw [pow_succ', Perm.mul_apply]

  have hE3 : (tk 0 * tk 1)⁻¹ * tk 3 ∈ E θ hn := hT.inv_mul_mem_E hn c hF hS
    (mul_mem (htkT 0) (htkT 1)) (htkT 3) (by
      rw [bz_mul hn c (hD 0) (hD 1), hb0, hb1, hb3, eps_mul]; rfl)
  have hE6 : (tk 0 * tk 2)⁻¹ * tk 6 ∈ E θ hn := hT.inv_mul_mem_E hn c hF hS
    (mul_mem (htkT 0) (htkT 2)) (htkT 6) (by
      rw [bz_mul hn c (hD 0) (hD 2), hb0, hb2, hb6, eps_mul]; rfl)
  have hE7 : (tk 0)⁻¹ * tk 7 ∈ E θ hn := hT.inv_mul_mem_E hn c hF hS (htkT 0) (htkT 7) (by
      rw [hb0, hb7])
  have h20 : cm (tk 2) (tk 0) = eps θ hn ((mPerm ^ 2) a ^^^ mPerm a) := by
    have e1 : cm (tk 2) (tk 3) = eps θ hn ((mPerm ^ 2) a) := hadj 2
    have h3 : tk 3 = tk 0 * tk 1 * ((tk 0 * tk 1)⁻¹ * tk 3) := by group
    rw [h3, hrm (htkT 2) (mul_mem (htkT 0) (htkT 1)) (T.mul_mem (T.inv_mem (mul_mem (htkT 0)
      (htkT 1))) (htkT 3)), hcmE (htkT 2) hE3, mul_one, hrm (htkT 2) (htkT 0) (htkT 1)] at e1
    have e2 : cm (tk 2) (tk 1) = eps θ hn (mPerm a) := by
      rw [← cm_inv, show cm (tk 1) (tk 2) = eps θ hn ((mPerm ^ 1) a) from hadj 1, pow_one,
        eps_inv]
    rw [e2] at e1
    rw [show eps θ hn ((mPerm ^ 2) a ^^^ mPerm a) = eps θ hn ((mPerm ^ 2) a) * eps θ hn (mPerm a)
      by rw [eps_mul], ← e1, mul_assoc, eps_mul_self, mul_one]
  have h67 : cm (tk 6) (tk 7) = cm (tk 2) (tk 0) := by
    have h6 : tk 6 = tk 0 * tk 2 * ((tk 0 * tk 2)⁻¹ * tk 6) := by group
    have h7 : tk 7 = tk 0 * ((tk 0)⁻¹ * tk 7) := by group
    have hT6 : (tk 0 * tk 2)⁻¹ * tk 6 ∈ T := T.mul_mem (T.inv_mem (mul_mem (htkT 0) (htkT 2)))
      (htkT 6)
    have hT7 : (tk 0)⁻¹ * tk 7 ∈ T := T.mul_mem (T.inv_mem (htkT 0)) (htkT 7)
    rw [h6, h7, hlm (mul_mem (htkT 0) (htkT 2)) hT6 (mul_mem (htkT 0) hT7),
      hcmE' (mul_mem (htkT 0) hT7) hE6, one_mul, hrm (mul_mem (htkT 0) (htkT 2)) (htkT 0) hT7,
      hcmE (mul_mem (htkT 0) (htkT 2)) hE7, mul_one, hlm (htkT 0) (htkT 2) (htkT 0), cm_self,
      mul_one]
  have ha0 : a = 0 := by
    apply eq_zero_of_mPerm_six
    apply eps_injective θ hn
    rw [← hadj 6, h67, h20]
  have h01 : cm (tk 0) (tk 1) = 1 := by rw [ha, ha0, eps_zero]
  have h12 : cm (tk 1) (tk 2) = 1 := by
    rw [show cm (tk 1) (tk 2) = eps θ hn ((mPerm ^ 1) a) from hadj 1, ha0]
    rw [show (mPerm ^ 1) (0 : Fin 8) = 0 by decide, eps_zero]
  have h02 : cm (tk 0) (tk 2) = 1 := by
    rw [← cm_inv, h20, ha0, show (mPerm ^ 2) (0 : Fin 8) ^^^ mPerm 0 = 0 by decide, eps_zero,
      inv_one]
  have hgenT := forall_of_gen hn c (hT.le_D0 hn c hF hS) (fun x hx => hT.E_le hx)
    (fun x hx y hy h => hT.inv_mul_mem_E hn c hF hS hx hy h) (htkT 0) (htkT 1) (htkT 2)
    hb0 hb1 hb2
  have hone : ∀ {g : G}, g ∈ T → cm 1 g = 1 := by intro g _; simp [cm]
  have hone' : ∀ {g : G}, g ∈ T → cm g 1 = 1 := by intro g _; simp [cm]
  have hstep1 : ∀ i : Fin 3, ∀ p ∈ T, cm p (tk i) = 1 := by
    intro i
    refine hgenT (fun p => cm p (tk i) = 1) (fun x hx => hcmE' (htkT i) hx)
      (fun x hx y hy h1 h2 => by rw [hlm hx hy (htkT i), h1, h2, one_mul])
      ?_ ?_ ?_ (hone (htkT i))
    all_goals
      fin_cases i
      all_goals first
        | exact cm_self _
        | exact h01
        | exact h12
        | exact h02
        | exact (by rw [← cm_inv, h01, inv_one])
        | exact (by rw [← cm_inv, h12, inv_one])
        | exact (by rw [← cm_inv, h02, inv_one])
  have hstep2 : ∀ q ∈ T, cm x q = 1 := by
    refine hgenT (fun q => cm x q = 1) (fun e he => hcmE hx he)
      (fun a ha b hb h1 h2 => by rw [hrm hx ha hb, h1, h2, one_mul])
      (hstep1 0 x hx) (hstep1 1 x hx) (hstep1 2 x hx) (hone' hx)
  have := hstep2 y hy
  calc x * y = cm x y * (y * x) := by simp only [cm]; group
    _ = y * x := by rw [this, one_mul]

end TProps

end CFSG.OddStandard.AltStdSmall4.N0
