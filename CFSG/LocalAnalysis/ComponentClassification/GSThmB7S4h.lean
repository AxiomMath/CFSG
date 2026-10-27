module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S4g

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Seven

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem inv_conj_mem {H : Subgroup X} {n : X} (hn : n ∈ normalizer (H : Set X)) {x : X}
    (hx : x ∈ H) : n⁻¹ * x * n ∈ H := by
  have := (mem_normalizer_iff.mp (inv_mem hn) x).mp hx
  rwa [inv_inv] at this

omit [Finite X] in
theorem zpowers_sq_eq_one {x : X} (hxx : x * x = 1) : ∀ y ∈ zpowers x, y * y = 1 := by
  intro y hy
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hxx, one_zpow]

omit [Finite X] in
theorem zpowers_comm {x y : X} (h : x * y = y * x) :
    ∀ v ∈ zpowers x, ∀ w ∈ zpowers y, v * w = w * v := by
  intro v hv w hw
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hv
  obtain ⟨l, rfl⟩ := mem_zpowers_iff.mp hw
  exact ((Commute.zpow_zpow h k l) :)

omit [Finite X] in
theorem orderOf_eq_two_of {x : X} (hxx : x * x = 1) (hx1 : x ≠ 1) : orderOf x = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1

omit [Finite X] in
theorem zpowers_inf_eq_bot {x y : X} (hxx : x * x = 1) (hx1 : x ≠ 1) (hyy : y * y = 1)
    (hy1 : y ≠ 1) (hxy : x ≠ y) : zpowers x ⊓ zpowers y = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hw1, hw2⟩ := mem_inf.mp hw
  rcases eq_one_or_of_mem_zpowers (orderOf_eq_two_of hxx hx1) hw1 with h | h
  · exact h ▸ one_mem _
  · rcases eq_one_or_of_mem_zpowers (orderOf_eq_two_of hyy hy1) hw2 with h' | h'
    · exact h' ▸ one_mem _
    · exact absurd (h.symm.trans h') hxy

@[expose] def CSq (F : Subgroup X) : Set X :=
  {w | (∀ f ∈ F, f * w = w * f) ∧ ∃ f ∈ F, f * f = w}

omit [Finite X] in
theorem conj_mem_CSq {F : Subgroup X} {n : X} (hn : n ∈ normalizer (F : Set X)) {w : X}
    (hw : w ∈ CSq F) : n⁻¹ * w * n ∈ CSq F := by
  obtain ⟨hwc, f, hf, rfl⟩ := hw
  refine ⟨fun g hg => ?_, ⟨n⁻¹ * f * n, inv_conj_mem hn hf, by group⟩⟩
  have hg' : n * g * n⁻¹ ∈ F := (mem_normalizer_iff.mp hn g).mp hg
  have h1 := hwc _ hg'
  calc g * (n⁻¹ * (f * f) * n) = n⁻¹ * ((n * g * n⁻¹) * (f * f)) * n := by group
    _ = n⁻¹ * ((f * f) * (n * g * n⁻¹)) * n := by rw [h1]
    _ = n⁻¹ * (f * f) * n * g := by group

namespace Ctx4

variable (c : Ctx4 X)

theorem rhoImg_sq {A : Subgroup X} (hA2 : ∀ x ∈ A, x * x = 1) :
    ∀ σ ∈ rhoImg c.s.h.J A, σ * σ = 1 := by
  intro σ hσ
  obtain ⟨x, hx, hxN, rfl⟩ := exists_of_mem_rhoImg hσ
  rw [← rhoE_mul hxN hxN, hA2 x hx, rhoE_one]

theorem card_le_8_of_le_P' {A : Subgroup X} (hA : A ≤ c.P') (hA2 : ∀ x ∈ A, x * x = 1) :
    Nat.card A ≤ 8 := by
  have hAN : A ≤ normalizer (c.s.h.J : Set X) := hA.trans c.P'_le_N
  have hAK : A ⊓ coreActionKernel c.s.h.J = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [← c.P'_inf_K]
    exact mem_inf.mpr ⟨hA (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩
  have := c.hRk _ (c.rhoImg_sq hA2)
  rwa [card_rhoImg hAN hAK le_rfl] at this

theorem card_inf_P_le {E : Subgroup X} (hE2 : ∀ x ∈ E, x * x = 1) :
    Nat.card ↥(E ⊓ c.s.h.P) ≤ 8 := by
  rw [← card_conjugate (E ⊓ c.s.h.P) c.u]
  exact c.card_le_8_of_le_P' (map_mono inf_le_right)
    (conjugate_sq_eq_one (fun x hx => hE2 x (mem_inf.mp hx).1) c.u)

theorem card_le_of_le_S {E : Subgroup X} (hES : E ≤ c.s.h.S) (hE2 : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 8 * Nat.card ↥(E ⊓ c.s.h.P) := by
  have hEN : E ≤ normalizer (c.s.h.J : Set X) := hES.trans c.s.h.S_le_normalizer
  have h2 : E ⊓ coreActionKernel c.s.h.J = E ⊓ c.s.h.P := by
    ext x
    constructor
    · intro hx
      exact mem_inf.mpr ⟨(mem_inf.mp hx).1, mem_inf.mpr ⟨hES (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩⟩
    · intro hx
      exact mem_inf.mpr ⟨(mem_inf.mp hx).1, (mem_inf.mp (mem_inf.mp hx).2).2⟩
  rw [card_eq_card_rhoImg_mul hEN, h2]
  exact Nat.mul_le_mul_right _ (c.hRk _ (c.rhoImg_sq hE2))

theorem card_inf_P_of_64 {E : Subgroup X} (hES : E ≤ c.s.h.S) (hE2 : ∀ x ∈ E, x * x = 1)
    (h64 : Nat.card E = 64) : Nat.card ↥(E ⊓ c.s.h.P) = 8 := by
  have h1 := c.card_le_of_le_S hES hE2
  have h2 := c.card_inf_P_le hE2
  omega

theorem card_inf_P'_of_64 {E : Subgroup X} (hES : E ≤ c.s.h.S) (hE2 : ∀ x ∈ E, x * x = 1)
    (h64 : Nat.card E = 64) : Nat.card ↥(E ⊓ c.P') = 8 := by
  have hE'S : conjugate E c.u⁻¹ ≤ c.s.h.S :=
    (map_mono hES).trans (conjugate_le_of_mem_normalizer' (inv_mem c.hu))
  have h3 := c.card_inf_P_of_64 hE'S (conjugate_sq_eq_one hE2 c.u⁻¹)
    ((card_conjugate _ _).trans h64)
  have h4 : conjugate E c.u⁻¹ ⊓ c.s.h.P = conjugate (E ⊓ c.P') c.u⁻¹ := by
    rw [conjugate_inf, conjugate_conjugate_mul, mul_inv_cancel, conjugate_one']
  rwa [h4, card_conjugate] at h3

theorem eq_sup_of_64 {E : Subgroup X} (hES : E ≤ c.s.h.S) (hE2 : ∀ x ∈ E, x * x = 1)
    (h64 : Nat.card E = 64) : E = (E ⊓ c.s.h.P) ⊔ (E ⊓ c.P') := by
  symm
  refine eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_
  have hdisj : (E ⊓ c.s.h.P) ⊓ (E ⊓ c.P') = ⊥ := by
    rw [eq_bot_iff, ← c.P_inf_P']
    exact inf_le_inf inf_le_right inf_le_right
  rw [card_sup_of_commute (fun x hx y hy => c.comm_P_P' (mem_inf.mp hx).2 (mem_inf.mp hy).2)
    hdisj, c.card_inf_P_of_64 hES hE2 h64, c.card_inf_P'_of_64 hES hE2 h64, h64]

theorem le_S_of_64 {E : Subgroup X} (hES1 : E ≤ S1 c.s.h.S c.u) (hE2 : ∀ x ∈ E, x * x = 1)
    (h64 : Nat.card E = 64) : E ≤ c.s.h.S := by
  by_contra hne
  obtain ⟨v, hvE, hvS⟩ := Set.not_subset.mp hne
  have hvu : v * c.u⁻¹ ∈ c.s.h.S := ((mem_S1 c.hu c.huu).mp (hES1 hvE)).resolve_left hvS
  have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    have h1 := hE2 _ (mul_mem hx hy)
    calc x * y = x * (x * y * (x * y)) * y := by rw [h1, mul_one]
      _ = (x * x) * (y * x) * (y * y) := by group
      _ = y * x := by rw [hE2 x hx, hE2 y hy, one_mul, mul_one]
  have hK : (E ⊓ c.s.h.S) ⊓ coreActionKernel c.s.h.J = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwES, hwK⟩ := mem_inf.mp hw
    obtain ⟨hwE, hwS⟩ := mem_inf.mp hwES
    have hwP : w ∈ c.s.h.P := mem_inf.mpr ⟨hwS, hwK⟩
    have h1 : v⁻¹ * w * v = w := by
      rw [mul_assoc, hEab w hwE v hvE, inv_mul_cancel_left]
    have h2 : v⁻¹ * w * v ∈ c.P' := by
      have h3 : (v * c.u⁻¹)⁻¹ * w * (v * c.u⁻¹) ∈ c.s.h.P := by
        have := c.s.h.conj_mem_P (inv_mem hvu) hwP
        rwa [inv_inv] at this
      have := c.mem_P'_of_mem_P h3
      rwa [show c.u⁻¹ * ((v * c.u⁻¹)⁻¹ * w * (v * c.u⁻¹)) * c.u = v⁻¹ * w * v by group]
        at this
    rw [h1] at h2
    rw [← c.P_inf_P']
    exact mem_inf.mpr ⟨hwP, h2⟩
  have hEsN : E ⊓ c.s.h.S ≤ normalizer (c.s.h.J : Set X) :=
    inf_le_right.trans c.s.h.S_le_normalizer
  have h8 : Nat.card ↥(E ⊓ c.s.h.S) ≤ 8 := by
    have := c.hRk _ (c.rhoImg_sq (A := E ⊓ c.s.h.S) (fun x hx => hE2 x (mem_inf.mp hx).1))
    rwa [card_rhoImg hEsN hK le_rfl] at this
  have h16 : Nat.card E ≤ 2 * Nat.card ↥(E ⊓ c.s.h.S) := by
    classical
    have hmem : ∀ x : ↥E, (x : X) ∉ c.s.h.S → v⁻¹ * x ∈ E ⊓ c.s.h.S := by
      intro x hx
      refine mem_inf.mpr ⟨mul_mem (inv_mem hvE) x.2, ?_⟩
      have hxu : (x : X) * c.u⁻¹ ∈ c.s.h.S :=
        ((mem_S1 c.hu c.huu).mp (hES1 x.2)).resolve_left hx
      have h1 := inv_conj_mem c.hu (mul_mem (inv_mem hvu) hxu)
      rwa [show c.u⁻¹ * ((v * c.u⁻¹)⁻¹ * ((x : X) * c.u⁻¹)) * c.u = v⁻¹ * x by group] at h1
    let f : ↥E → ↥(E ⊓ c.s.h.S) ⊕ ↥(E ⊓ c.s.h.S) := fun x =>
      if hx : (x : X) ∈ c.s.h.S then Sum.inl ⟨x, mem_inf.mpr ⟨x.2, hx⟩⟩
      else Sum.inr ⟨v⁻¹ * x, hmem x hx⟩
    have hf : Function.Injective f := by
      intro x y hxy
      by_cases hx : (x : X) ∈ c.s.h.S <;> by_cases hy : (y : X) ∈ c.s.h.S <;>
        simp only [f, hx, hy, dite_true, dite_false, Sum.inl.injEq, Sum.inr.injEq,
          reduceCtorEq] at hxy
      · exact Subtype.ext (congrArg (fun w : ↥(E ⊓ c.s.h.S) => (w : X)) hxy)
      · exact Subtype.ext (mul_left_cancel (congrArg (fun w : ↥(E ⊓ c.s.h.S) => (w : X)) hxy))
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_sum, ← two_mul] at this
  omega

abbrev F : Subgroup X := Je (S1 c.s.h.S c.u)

theorem F_le_S : c.F ≤ c.s.h.S := Je_le_of fun _ hE hE2 h64 => c.le_S_of_64 hE hE2 h64

theorem le_F {E : Subgroup X} (hES : E ≤ c.s.h.S) (hE2 : ∀ x ∈ E, x * x = 1)
    (h64 : Nat.card E = 64) : E ≤ c.F :=
  le_Je (hES.trans (le_S1 _ _)) hE2 h64

theorem S1_le_N : S1 c.s.h.S c.u ≤ normalizer (c.F : Set X) :=
  le_normalizer.trans (normalizer_le_normalizer_Je _)

theorem u_mem_N : c.u ∈ normalizer (c.F : Set X) := c.S1_le_N (mem_S1_self _ _)

theorem F_le_sup : c.F ≤ (c.F ⊓ c.s.h.P) ⊔ (c.F ⊓ c.PW) := by
  refine Je_le_of fun E hE hE2 h64 => ?_
  have hES := c.le_S_of_64 hE hE2 h64
  have hEF : E ≤ c.F := le_Je hE hE2 h64
  rw [c.eq_sup_of_64 hES hE2 h64]
  refine sup_le (le_sup_of_le_left (inf_le_inf_right _ hEF))
    (le_sup_of_le_right (le_inf (inf_le_left.trans hEF) ?_))
  exact c.le_PW_of_E8 inf_le_right (fun x hx => hE2 x (mem_inf.mp hx).1)
    (c.card_inf_P'_of_64 hES hE2 h64)

theorem mem_F {f : X} (hf : f ∈ c.F) :
    ∃ f₁ ∈ c.F ⊓ c.s.h.P, ∃ f₂ ∈ c.F ⊓ c.PW, f = f₁ * f₂ :=
  exists_mul_of_mem_sup (fun _ hx _ hy => c.comm_P_P' (mem_inf.mp hx).2
    (c.PW_le_P' (mem_inf.mp hy).2)) (c.F_le_sup hf)

theorem mem_PW_of_mem_F {g : X} (hgF : g ∈ c.F) (hgP' : g ∈ c.P') : g ∈ c.PW := by
  obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := c.mem_F hgF
  have hg₂P' := c.PW_le_P' (mem_inf.mp hg₂).2
  have h1 : g₁ ∈ c.s.h.P ⊓ c.P' := by
    refine mem_inf.mpr ⟨(mem_inf.mp hg₁).2, ?_⟩
    have := mul_mem hgP' (inv_mem hg₂P')
    rwa [mul_inv_cancel_right] at this
  rw [c.P_inf_P', mem_bot] at h1
  rw [h1, one_mul]
  exact (mem_inf.mp hg₂).2

theorem F_comm_b {f : X} (hf : f ∈ c.F) : f * c.b = c.b * f := by
  obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ := c.mem_F hf
  have hf₂P' := c.PW_le_P' (mem_inf.mp hf₂).2
  have h2 : f₂ * c.b = c.b * f₂ := (c.comm_P_P' c.b_mem_P hf₂P').symm
  have hg : c.u⁻¹ * f₁ * c.u ∈ c.PW :=
    c.mem_PW_of_mem_F (inv_conj_mem c.u_mem_N (mem_inf.mp hf₁).1)
      (c.mem_P'_of_mem_P (mem_inf.mp hf₁).2)
  have h1 := c.PW_comm_b' hg
  have h1' : f₁ * c.b = c.b * f₁ := by
    calc f₁ * c.b = c.u * ((c.u⁻¹ * f₁ * c.u) * c.b') * c.u⁻¹ := by simp only [b']; group
      _ = c.u * (c.b' * (c.u⁻¹ * f₁ * c.u)) * c.u⁻¹ := by rw [h1]
      _ = c.b * f₁ := by simp only [b']; group
  calc f₁ * f₂ * c.b = f₁ * (c.b * f₂) := by rw [mul_assoc, h2]
    _ = c.b * (f₁ * f₂) := by rw [← mul_assoc, h1', mul_assoc]

theorem b'_ne_one : c.b' ≠ 1 := by
  intro h
  apply c.hb1
  calc c.b = c.u * c.b' * c.u⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem z_ne_b' : c.z ≠ c.b' := fun h => c.e_ne_rho_z (congrArg (rhoE c.s.h.J) h.symm)

theorem z_comm_b' : c.z * c.b' = c.b' * c.z := (c.hzS _ (c.P'_le_S c.b'_mem_P')).symm

abbrev K : Subgroup X := zpowers c.z ⊔ zpowers c.b'

theorem K_le_P' : c.K ≤ c.P' :=
  sup_le (zpowers_le.mpr c.z_mem_P') (zpowers_le.mpr c.b'_mem_P')

theorem card_K : Nat.card c.K = 4 := by
  rw [card_sup_of_commute (zpowers_comm c.z_comm_b')
    (zpowers_inf_eq_bot c.hzz c.hz1 c.b'_mul_b' c.b'_ne_one c.z_ne_b'), Nat.card_zpowers,
    Nat.card_zpowers, orderOf_eq_two_of c.hzz c.hz1, orderOf_eq_two_of c.b'_mul_b' c.b'_ne_one]

theorem K_sq : ∀ x ∈ c.K, x * x = 1 :=
  sup_sq_eq_one (zpowers_sq_eq_one c.hzz) (zpowers_sq_eq_one c.b'_mul_b')
    (zpowers_comm c.z_comm_b')

theorem rho_mem_K {x : X} (hx : x ∈ c.K) :
    rhoE c.s.h.J x = 1 ∨ rhoE c.s.h.J x = rhoE c.s.h.J c.z ∨ rhoE c.s.h.J x = c.e ∨
      rhoE c.s.h.J x = rhoE c.s.h.J c.z * c.e := by
  obtain ⟨v, hv, w, hw, rfl⟩ := exists_mul_of_mem_sup (zpowers_comm c.z_comm_b') hx
  have hvN := c.P'_le_N (zpowers_le.mpr c.z_mem_P' hv)
  have hwN := c.P'_le_N (zpowers_le.mpr c.b'_mem_P' hw)
  rw [rhoE_mul hvN hwN]
  rcases eq_one_or_of_mem_zpowers (orderOf_eq_two_of c.hzz c.hz1) hv with rfl | rfl <;>
    rcases eq_one_or_of_mem_zpowers (orderOf_eq_two_of c.b'_mul_b' c.b'_ne_one) hw with
      rfl | rfl <;> simp [rhoE_one]

theorem exists_F_of_inv {σ : MulAut (Jbar c.s.h)} (hσ : σ ∈ innOf (Dbar c.s.h))
    (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) (hσz : σ ≠ rhoE c.s.h.J c.z) :
    ∃ y ∈ c.F, y ∈ c.P' ∧ rhoE c.s.h.J y = σ ∧ c.z ∈ c.F := by
  obtain ⟨y, hyP', hyN, rfl⟩ := exists_of_mem_rhoImg (c.hInn hσ)
  have hyy : y * y = 1 :=
    c.rho_inj (mul_mem hyP' hyP') (one_mem _) (by rw [rhoE_mul hyN hyN, hσ2, rhoE_one])
  have hy1 : y ≠ 1 := fun h => hσ1 (by rw [h, rhoE_one])
  have hyK : y ∉ c.K := by
    intro h
    rcases c.rho_mem_K h with h' | h' | h' | h'
    · exact hσ1 h'
    · exact hσz h'
    · exact c.e_not_mem (h' ▸ hσ)
    · apply c.e_not_mem
      have : c.e = (rhoE c.s.h.J c.z)⁻¹ * rhoE c.s.h.J y := by rw [h', inv_mul_cancel_left]
      rw [this]
      exact mul_mem (inv_mem (c.rho_mem_innOf c.hzD)) hσ
  have hyz : y * c.z = c.z * y := c.hzS y (c.P'_le_S hyP')
  have hyb' : y * c.b' = c.b' * y := by
    apply c.rho_inj (mul_mem hyP' c.b'_mem_P') (mul_mem c.b'_mem_P' hyP')
    rw [rhoE_mul hyN (c.P'_le_N c.b'_mem_P'), rhoE_mul (c.P'_le_N c.b'_mem_P') hyN]
    exact c.e_comm hσ
  have hyKc : ∀ v ∈ zpowers y, ∀ w ∈ c.K, v * w = w * v := by
    intro v hv w hw
    have hwC : w ∈ centralizer ({y} : Set X) := by
      refine (sup_le ?_ ?_ : c.K ≤ centralizer ({y} : Set X)) hw <;> rw [zpowers_le,
        mem_centralizer_singleton_iff]
      · exact hyz.symm
      · exact hyb'.symm
    rw [mem_centralizer_singleton_iff] at hwC
    exact zpowers_comm hwC.symm v hv w (mem_zpowers w)
  set E8 := zpowers y ⊔ c.K with hE8
  have hE8P' : E8 ≤ c.P' := sup_le (zpowers_le.mpr hyP') c.K_le_P'
  have hE8sq : ∀ x ∈ E8, x * x = 1 := sup_sq_eq_one (zpowers_sq_eq_one hyy) c.K_sq hyKc
  have hdisj : zpowers y ⊓ c.K = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
    rcases eq_one_or_of_mem_zpowers (orderOf_eq_two_of hyy hy1) hx1 with h | h
    · exact h ▸ one_mem _
    · exact absurd (h ▸ hx2) hyK
  have hE8card : Nat.card E8 = 8 := by
    rw [hE8, card_sup_of_commute hyKc hdisj, c.card_K, Nat.card_zpowers,
      orderOf_eq_two_of hyy hy1]
  set E8' := conjugate E8 c.u⁻¹ with hE8'
  have hE8'P : E8' ≤ c.s.h.P := by
    intro x hx
    rw [mem_conjugate_iff, inv_inv] at hx
    have := c.mem_P_of_mem_P' (hE8P' hx)
    rwa [show c.u * (c.u⁻¹ * x * c.u) * c.u⁻¹ = x by group] at this
  have hcomm : ∀ x ∈ E8, ∀ w ∈ E8', x * w = w * x := fun x hx w hw =>
    (c.comm_P_P' (hE8'P hw) (hE8P' hx)).symm
  have hdisj' : E8 ⊓ E8' = ⊥ := by
    rw [eq_bot_iff, ← c.P_inf_P']
    intro x hx
    exact mem_inf.mpr ⟨hE8'P (mem_inf.mp hx).2, hE8P' (mem_inf.mp hx).1⟩
  have hEsq := sup_sq_eq_one hE8sq (conjugate_sq_eq_one hE8sq _) hcomm
  have hEcard : Nat.card ↥(E8 ⊔ E8') = 64 := by
    rw [card_sup_of_commute hcomm hdisj', hE8card, hE8', card_conjugate, hE8card]
  have hES : E8 ⊔ E8' ≤ c.s.h.S := sup_le (hE8P'.trans c.P'_le_S) (hE8'P.trans inf_le_left)
  have hEF := c.le_F hES hEsq hEcard
  exact ⟨y, hEF (mem_sup_left (mem_sup_left (mem_zpowers y))), hyP', rfl,
    hEF (mem_sup_left (mem_sup_right (mem_sup_left (mem_zpowers c.z))))⟩

theorem z_mem_F : c.z ∈ c.F := by
  obtain ⟨t, ht, htt1, httC⟩ := c.hsq
  obtain ⟨i, hi, j, hj, hii, hjj, rfl⟩ := c.hprod t ht
  have hσ : MulAut.conj i ∈ innOf (Dbar c.s.h) := mem_map_of_mem _ hi
  have hσ2 : MulAut.conj i * MulAut.conj i = 1 := by rw [← map_mul, hii, map_one]
  have hσ1 : MulAut.conj i ≠ 1 := by
    intro h
    have hi1 : i = 1 := c.conj_injective (h.trans (map_one _).symm)
    apply htt1
    rw [hi1, one_mul, hjj]
  have hσz : MulAut.conj i ≠ rhoE c.s.h.J c.z := by
    intro h
    have hic : ∀ w ∈ Dbar c.s.h, w * i = i * w := by
      intro w hw
      apply c.conj_injective
      rw [map_mul, map_mul, h]
      exact c.rho_z_comm (mem_map_of_mem _ hw)
    apply htt1
    calc i * j * (i * j) = i * (j * i) * j := by group
      _ = i * (i * j) * j := by rw [hic j hj]
      _ = (i * i) * (j * j) := by group
      _ = 1 := by rw [hii, hjj, one_mul]
  obtain ⟨-, -, -, -, hz⟩ := c.exists_F_of_inv hσ hσ2 hσ1 hσz
  exact hz

theorem exists_F_of_innOf {σ : MulAut (Jbar c.s.h)} (hσ : σ ∈ innOf (Dbar c.s.h)) :
    ∃ y ∈ c.F, y ∈ c.P' ∧ rhoE c.s.h.J y = σ := by
  obtain ⟨t, ht, rfl⟩ := hσ
  obtain ⟨i, hi, j, hj, hii, hjj, rfl⟩ := c.hprod t ht
  have key : ∀ k ∈ Dbar c.s.h, k * k = 1 →
      ∃ y ∈ c.F, y ∈ c.P' ∧ rhoE c.s.h.J y = MulAut.conj k := by
    intro k hk hkk
    by_cases h1 : MulAut.conj k = 1
    · exact ⟨1, one_mem _, one_mem _, by rw [rhoE_one, h1]⟩
    by_cases h2 : MulAut.conj k = rhoE c.s.h.J c.z
    · exact ⟨c.z, c.z_mem_F, c.z_mem_P', h2.symm⟩
    obtain ⟨y, hyF, hyP', hy, -⟩ := c.exists_F_of_inv (mem_map_of_mem _ hk)
      (by rw [← map_mul, hkk, map_one]) h1 h2
    exact ⟨y, hyF, hyP', hy⟩
  obtain ⟨yi, hyiF, hyiP', hyi⟩ := key i hi hii
  obtain ⟨yj, hyjF, hyjP', hyj⟩ := key j hj hjj
  refine ⟨yi * yj, mul_mem hyiF hyjF, mul_mem hyiP' hyjP', ?_⟩
  rw [rhoE_mul (c.P'_le_N hyiP') (c.P'_le_N hyjP'), hyi, hyj, map_mul]

theorem CSq_cases {w : X} (hw : w ∈ CSq c.F) :
    w = 1 ∨ w = c.s.h.a ∨ w = c.z ∨ w = c.s.h.a * c.z := by
  obtain ⟨hwc, f, hf, rfl⟩ := hw
  obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ := c.mem_F hf
  have hf₁P := (mem_inf.mp hf₁).2
  have hf₂P' := c.PW_le_P' (mem_inf.mp hf₂).2
  have hc12 : f₁ * f₂ = f₂ * f₁ := c.comm_P_P' hf₁P hf₂P'
  have hsq : f₁ * f₂ * (f₁ * f₂) = (f₁ * f₁) * (f₂ * f₂) := by
    calc f₁ * f₂ * (f₁ * f₂) = f₁ * (f₂ * f₁) * f₂ := by group
      _ = f₁ * (f₁ * f₂) * f₂ := by rw [hc12]
      _ = (f₁ * f₁) * (f₂ * f₂) := by group
  have hlem : ∀ g ∈ c.F, g ∈ c.P' →
      (∀ y ∈ c.F, y ∈ c.P' → (g * g) * y = y * (g * g)) → g * g = 1 ∨ g * g = c.z := by
    intro g hgF hgP' hcomm
    apply c.PW_sq (c.mem_PW_of_mem_F hgF hgP')
    intro τ hτ
    obtain ⟨y, hyF, hyP', rfl⟩ := c.exists_F_of_innOf hτ
    have hgN := c.P'_le_N (mul_mem hgP' hgP')
    have hyN := c.P'_le_N hyP'
    rw [← rhoE_mul hgN hyN, ← rhoE_mul hyN hgN, hcomm y hyF hyP']
  have h2 : f₂ * f₂ = 1 ∨ f₂ * f₂ = c.z := by
    apply hlem f₂ (mem_inf.mp hf₂).1 hf₂P'
    intro y hyF hyP'
    have hy1 := hwc y hyF
    have hy2 : (f₁ * f₁) * y = y * (f₁ * f₁) := c.comm_P_P' (mul_mem hf₁P hf₁P) hyP'
    rw [hsq] at hy1
    calc f₂ * f₂ * y = (f₁ * f₁)⁻¹ * ((f₁ * f₁) * (f₂ * f₂) * y) := by group
      _ = (f₁ * f₁)⁻¹ * (y * ((f₁ * f₁) * (f₂ * f₂))) := by rw [hy1]
      _ = (f₁ * f₁)⁻¹ * ((y * (f₁ * f₁)) * (f₂ * f₂)) := by group
      _ = (f₁ * f₁)⁻¹ * (((f₁ * f₁) * y) * (f₂ * f₂)) := by rw [hy2]
      _ = y * (f₂ * f₂) := by group
  have hf₁c : ∀ y ∈ c.F, y * (f₁ * f₁) = (f₁ * f₁) * y := by
    intro y hy
    have hw := hwc y hy
    rw [hsq] at hw
    have hf2c : y * (f₂ * f₂) = (f₂ * f₂) * y := by
      rcases h2 with h | h
      · rw [h, mul_one, one_mul]
      · rw [h]
        exact c.hzS y (c.F_le_S hy)
    calc y * (f₁ * f₁) = y * ((f₁ * f₁) * (f₂ * f₂)) * (f₂ * f₂)⁻¹ := by group
      _ = (f₁ * f₁) * (f₂ * f₂) * y * (f₂ * f₂)⁻¹ := by rw [hw]
      _ = (f₁ * f₁) * (y * (f₂ * f₂)) * (f₂ * f₂)⁻¹ := by rw [hf2c]; group
      _ = (f₁ * f₁) * y := by group
  have hgF : c.u⁻¹ * f₁ * c.u ∈ c.F := inv_conj_mem c.u_mem_N (mem_inf.mp hf₁).1
  have hgP' : c.u⁻¹ * f₁ * c.u ∈ c.P' := c.mem_P'_of_mem_P hf₁P
  have h1 : f₁ * f₁ = 1 ∨ f₁ * f₁ = c.s.h.a := by
    have hg2 : (c.u⁻¹ * f₁ * c.u) * (c.u⁻¹ * f₁ * c.u) = c.u⁻¹ * (f₁ * f₁) * c.u := by group
    have h3 := hlem _ hgF hgP' (fun y hyF _ => by
      rw [hg2]
      have hy' : c.u * y * c.u⁻¹ ∈ c.F := (mem_normalizer_iff.mp c.u_mem_N y).mp hyF
      have h4 := hf₁c _ hy'
      calc c.u⁻¹ * (f₁ * f₁) * c.u * y = c.u⁻¹ * ((f₁ * f₁) * (c.u * y * c.u⁻¹)) * c.u := by
            group
        _ = c.u⁻¹ * ((c.u * y * c.u⁻¹) * (f₁ * f₁)) * c.u := by rw [h4]
        _ = y * (c.u⁻¹ * (f₁ * f₁) * c.u) := by group)
    rw [hg2] at h3
    rcases h3 with h | h
    · left
      calc f₁ * f₁ = c.u * (c.u⁻¹ * (f₁ * f₁) * c.u) * c.u⁻¹ := by group
        _ = 1 := by rw [h]; group
    · right
      calc f₁ * f₁ = c.u * (c.u⁻¹ * (f₁ * f₁) * c.u) * c.u⁻¹ := by group
        _ = c.u * (c.u⁻¹ * c.s.h.a * c.u) * c.u⁻¹ := by rw [h, c.hua]
        _ = c.s.h.a := by group
  rw [hsq]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2]
  · left; rw [one_mul]
  · right; right; left; rw [one_mul]
  · right; left; rw [mul_one]
  · right; right; right; rfl

theorem z_mem_CSq : c.z ∈ CSq c.F := by
  refine ⟨fun f hf => c.hzS f (c.F_le_S hf), ?_⟩
  obtain ⟨t, ht, htt1, httC⟩ := c.hsq
  obtain ⟨y, hyF, hyP', hy⟩ := c.exists_F_of_innOf (mem_map_of_mem MulAut.conj ht)
  refine ⟨y, hyF, ?_⟩
  have h1 : MulAut.conj (t * t) = rhoE c.s.h.J c.z := by
    rcases c.hZD _ (mul_mem ht ht) httC with h | h
    · exact absurd (c.conj_injective (h.trans (map_one _).symm)) htt1
    · exact h
  apply c.rho_inj (mul_mem hyP' hyP') c.z_mem_P'
  rw [rhoE_mul (c.P'_le_N hyP') (c.P'_le_N hyP'), hy, ← map_mul, h1]

theorem a_mem_CSq : c.s.h.a ∈ CSq c.F := by
  have := conj_mem_CSq (inv_mem c.u_mem_N) c.z_mem_CSq
  rwa [inv_inv, show c.u * c.z * c.u⁻¹ = c.s.h.a by rw [← c.hua]; group] at this

theorem conj_a_cases {n : X} (hn : n ∈ normalizer (c.F : Set X)) :
    n⁻¹ * c.s.h.a * n = c.s.h.a ∨ n⁻¹ * c.s.h.a * n = c.z := by
  rcases c.CSq_cases (conj_mem_CSq hn c.a_mem_CSq) with h | h | h | h
  · exfalso
    have ha1 : c.s.h.a ≠ 1 := by
      intro h'
      have := c.s.h.orderOf_a
      rw [h', orderOf_one] at this
      exact absurd this (by norm_num)
    apply ha1
    calc c.s.h.a = n * (n⁻¹ * c.s.h.a * n) * n⁻¹ := by group
      _ = 1 := by rw [h]; group
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h (c.hnaz n)

theorem mem_centralizer_of_conj {n : X} (h : n⁻¹ * c.s.h.a * n = c.s.h.a) :
    n ∈ centralizer ({c.s.h.a} : Set X) := by
  rw [mem_centralizer_singleton_iff]
  calc n * c.s.h.a = n * (n⁻¹ * c.s.h.a * n) := by rw [h]
    _ = c.s.h.a * n := by group

theorem le_S1_of_isPGroup {W : Subgroup X} (hW2 : IsPGroup 2 W)
    (hS1W : S1 c.s.h.S c.u ≤ W) (hWN : W ≤ normalizer (c.F : Set X)) :
    W ≤ S1 c.s.h.S c.u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWa : W ⊓ centralizer ({c.s.h.a} : Set X) ≤ c.s.h.S := by
    obtain ⟨-, R, hR⟩ := c.s.hSa
    have h2 : IsPGroup 2 ↥((W ⊓ centralizer ({c.s.h.a} : Set X)).subgroupOf
        (centralizer ({c.s.h.a} : Set X))) := (hW2.to_le inf_le_left).comap_subtype
    have hle : (R : Subgroup ↥(centralizer ({c.s.h.a} : Set X))) ≤
        (W ⊓ centralizer ({c.s.h.a} : Set X)).subgroupOf (centralizer ({c.s.h.a} : Set X)) := by
      rw [hR]
      intro x hx
      exact mem_subgroupOf.mpr (mem_inf.mpr ⟨hS1W (le_S1 _ _ (mem_subgroupOf.mp hx)), x.2⟩)
    have heq := R.is_maximal' h2 hle
    intro x hx
    have hx' : (⟨x, (mem_inf.mp hx).2⟩ : ↥(centralizer ({c.s.h.a} : Set X))) ∈
        (W ⊓ centralizer ({c.s.h.a} : Set X)).subgroupOf (centralizer ({c.s.h.a} : Set X)) :=
      mem_subgroupOf.mpr hx
    rw [heq, hR] at hx'
    exact mem_subgroupOf.mp hx'
  intro w hw
  rcases c.conj_a_cases (hWN hw) with h | h
  · exact le_S1 _ _ (hWa (mem_inf.mpr ⟨hw, c.mem_centralizer_of_conj h⟩))
  · have hwu : w * c.u⁻¹ ∈ W ⊓ centralizer ({c.s.h.a} : Set X) := by
      refine mem_inf.mpr ⟨mul_mem hw (inv_mem (hS1W (mem_S1_self _ _))),
        c.mem_centralizer_of_conj ?_⟩
      calc (w * c.u⁻¹)⁻¹ * c.s.h.a * (w * c.u⁻¹) = c.u * (w⁻¹ * c.s.h.a * w) * c.u⁻¹ := by
            group
        _ = c.u * (c.u⁻¹ * c.s.h.a * c.u) * c.u⁻¹ := by rw [h, c.hua]
        _ = c.s.h.a := by group
    exact (mem_S1 c.hu c.huu).mpr (Or.inr (hWa hwu))

theorem S1_sylow : ∃ R : Sylow 2 X, (R : Subgroup X) = S1 c.s.h.S c.u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS1 := isPGroup_S1 c.s.h.isPGroup_S c.hu c.huu
  obtain ⟨V, hV⟩ := hS1.exists_le_sylow
  refine ⟨V, ?_⟩
  by_contra hne
  have hlt : (S1 c.s.h.S c.u).subgroupOf (V : Subgroup X) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    refine le_antisymm (fun x hx => ?_) hV
    have : (⟨x, hx⟩ : ↥(V : Subgroup X)) ∈ (S1 c.s.h.S c.u).subgroupOf (V : Subgroup X) :=
      htop ▸ mem_top _
    exact mem_subgroupOf.mp this
  have : Group.IsNilpotent ↥(V : Subgroup X) := V.isPGroup'.isNilpotent
  obtain ⟨g, hgN, hgS⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hgN' : (g : X) ∈ normalizer (S1 c.s.h.S c.u : Set X) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have := (mem_normalizer_iff.mp hgN ⟨x, hV hx⟩).mp (mem_subgroupOf.mpr hx)
      exact mem_subgroupOf.mp this
    · intro hx
      have hxV : x ∈ (V : Subgroup X) := by
        have := mul_mem (mul_mem (inv_mem g.2) (hV hx)) g.2
        rwa [show (g : X)⁻¹ * ((g : X) * x * (g : X)⁻¹) * g = x by group] at this
      have := (mem_normalizer_iff.mp hgN ⟨x, hxV⟩).mpr (mem_subgroupOf.mpr hx)
      exact mem_subgroupOf.mp this
  have hWV : S1 c.s.h.S c.u ⊔ zpowers (g : X) ≤ (V : Subgroup X) :=
    sup_le hV (zpowers_le.mpr g.2)
  have hWN : S1 c.s.h.S c.u ⊔ zpowers (g : X) ≤ normalizer (c.F : Set X) :=
    sup_le c.S1_le_N (zpowers_le.mpr (normalizer_le_normalizer_Je _ hgN'))
  have h1 := c.le_S1_of_isPGroup (V.isPGroup'.to_le hWV) le_sup_left hWN
    (mem_sup_right (mem_zpowers _))
  exact hgS (mem_subgroupOf.mpr h1)

theorem conj_mem_kernel {n k : X} (hn : n ∈ normalizer (c.s.h.J : Set X))
    (hk : k ∈ coreActionKernel c.s.h.J) : n⁻¹ * k * n ∈ coreActionKernel c.s.h.J := by
  have hkN : k ∈ normalizer (c.s.h.J : Set X) := ((mem_coreActionKernel).mp hk).1
  have hN : n⁻¹ * k * n ∈ normalizer (c.s.h.J : Set X) := mul_mem (mul_mem (inv_mem hn) hkN) hn
  rw [← rhoE_eq_one_iff hN, rhoE_mul (mul_mem (inv_mem hn) hkN) hn, rhoE_mul (inv_mem hn) hkN,
    (rhoE_eq_one_iff hkN).mpr hk, mul_one, rhoE_inv hn, inv_mul_cancel]

theorem elim (c : Ctx4 X) : False := by
  have hS1 := c.S1_sylow
  have hFa : ∀ f ∈ c.F, f * c.s.h.a = c.s.h.a * f := fun f hf => c.s.h.comm_a (c.F_le_S hf)
  have hFz : ∀ f ∈ c.F, f * c.z = c.z * f := fun f hf => c.hzS f (c.F_le_S hf)
  have hFb : ∀ f ∈ c.F, f * c.b = c.b * f := fun f hf => c.F_comm_b hf
  have hC : ∀ x : X, (∀ f ∈ c.F, f * x = x * f) → c.F ≤ centralizer ({x} : Set X) :=
    fun x hx f hf => mem_centralizer_singleton_iff.mpr (hx f hf)
  have hmul : ∀ x y : X, (∀ f ∈ c.F, f * x = x * f) → (∀ f ∈ c.F, f * y = y * f) →
      ∀ f ∈ c.F, f * (x * y) = (x * y) * f := by
    intro x y hx hy f hf
    rw [← mul_assoc, hx f hf, mul_assoc, hy f hf, mul_assoc]
  have hw := hC _ (hmul _ _ hFa hFb)
  have hw' : c.F ≤ centralizer ({c.r⁻¹ * (c.s.h.a * c.b) * c.r} : Set X) := by
    rcases c.hrab with h | h <;> rw [h]
    · exact hC _ hFz
    · exact hC _ (hmul _ _ hFz hFb)
  obtain ⟨n, hnN, hn⟩ := exists_normalizer_conj_of_weaklyClosed hS1 (Je_le _)
    (fun g hg => conjugate_Je_eq hg) hw hw'
  have hbK : c.b ∈ coreActionKernel c.s.h.J := (mem_inf.mp c.b_mem_P).2
  have haK : c.s.h.a ∈ coreActionKernel c.s.h.J := (mem_inf.mp c.s.h.a_mem_P).2
  have hbn : n⁻¹ * c.b * n = (n⁻¹ * c.s.h.a * n)⁻¹ * (c.r⁻¹ * (c.s.h.a * c.b) * c.r) := by
    rw [← hn]
    group
  rcases c.conj_a_cases hnN with ha | ha
  ·
    have hnJ := c.s.hJn (c.mem_centralizer_of_conj ha)
    have h1 := c.conj_mem_kernel hnJ hbK
    rw [hbn, ha] at h1
    have h2 : c.r⁻¹ * (c.s.h.a * c.b) * c.r ∈ coreActionKernel c.s.h.J := by
      have := mul_mem haK h1
      rwa [mul_inv_cancel_left] at this
    have hzK : c.z ∈ coreActionKernel c.s.h.J := by
      rcases c.hrab with h | h <;> rw [h] at h2
      · exact h2
      · have := mul_mem h2 (inv_mem hbK)
        rwa [mul_inv_cancel_right] at this
    exact c.hzP (mem_inf.mpr ⟨c.z_mem_S, hzK⟩)
  ·
    rw [ha] at hbn
    rcases c.hrab with h | h <;> rw [h] at hbn
    · apply c.hb1
      calc c.b = n * (n⁻¹ * c.b * n) * n⁻¹ := by group
        _ = 1 := by rw [hbn, inv_mul_cancel]; group
    ·
      have hbn' : n⁻¹ * c.b * n = c.b := by rw [hbn]; group
      have hn' : (n * c.u⁻¹)⁻¹ * c.s.h.a * (n * c.u⁻¹) = c.s.h.a := by
        calc (n * c.u⁻¹)⁻¹ * c.s.h.a * (n * c.u⁻¹) = c.u * (n⁻¹ * c.s.h.a * n) * c.u⁻¹ := by
              group
          _ = c.u * (c.u⁻¹ * c.s.h.a * c.u) * c.u⁻¹ := by rw [ha, c.hua]
          _ = c.s.h.a := by group
      have hnJ := c.s.hJn (c.mem_centralizer_of_conj hn')
      have h1 := c.conj_mem_kernel hnJ hbK
      rw [show (n * c.u⁻¹)⁻¹ * c.b * (n * c.u⁻¹) = c.u * (n⁻¹ * c.b * n) * c.u⁻¹ by group,
        hbn'] at h1
      have hubS : c.u * c.b * c.u⁻¹ ∈ c.s.h.S := by
        have := inv_conj_mem (inv_mem c.hu) c.b_mem_S
        rwa [inv_inv] at this
      have h2 : c.u * c.b * c.u⁻¹ ∈ c.s.h.P ⊓ c.P' :=
        mem_inf.mpr ⟨mem_inf.mpr ⟨hubS, h1⟩, c.conj_mem_P' c.b_mem_P⟩
      rw [c.P_inf_P', mem_bot] at h2
      apply c.hb1
      calc c.b = c.u⁻¹ * (c.u * c.b * c.u⁻¹) * c.u := by group
        _ = 1 := by rw [h2]; group

end Ctx4

namespace Setting

theorem normalizer_le (s : Setting X) (hConj : CFSp4Conj) (hComp : CFSp4Comp)
    (hOut : CFSp4Outer) (hCent : CFL2Cent) (hD : CFSp4D) (hA : CFL2A) (hC : CFL2C)
    (hRank : CFL2Rank) (hSyl : CFL2Sylow) (hJ : CFL2J) :
    normalizer (s.h.S : Set X) ≤ centralizer ({s.h.a} : Set X) := by
  by_contra hNS
  obtain ⟨c, -⟩ := s.exists_ctx4 hConj hComp hOut hCent hD hA hC hRank hSyl hJ hNS
  exact c.elim

end Setting

end Seven

end CFSG.ComponentClassification.GSThmB
