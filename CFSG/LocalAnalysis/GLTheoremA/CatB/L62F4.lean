module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.L62

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.L62F

open Matrix

abbrev Vx : Type := L62Model.ι → ZMod 2

abbrev Ex : Type := Module.End (ZMod 2) Vx

abbrev Gx : Type := (Matrix L62Model.ι L62Model.ι (ZMod 2))ˣ

noncomputable def rho : Gx →* Ex :=
  (((Matrix.toLinAlgEquiv' (R := ZMod 2) (n := L62Model.ι)) :
    Matrix L62Model.ι L62Model.ι (ZMod 2) ≃ₐ[ZMod 2] Ex).toMonoidHom).comp (Units.coeHom _)

theorem rho_injective : Function.Injective rho := by
  intro a b h
  apply Units.ext
  exact (Matrix.toLinAlgEquiv' (R := ZMod 2) (n := L62Model.ι)).injective h

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  have h := two_mul_card_alternatingGroup (α := Fin 7)
  have hp : Nat.card (Equiv.Perm (Fin 7)) = 5040 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
  simp only [← Nat.card_eq_fintype_card] at h
  omega

theorem simple_of_iso {I : Type} [Group I] (e : I ≃* alternatingGroup (Fin 7)) (N : Subgroup I) [N.Normal] :
    N = ⊥ ∨ N = ⊤ := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup I := e.isSimpleGroup
  exact Subgroup.Normal.eq_bot_or_eq_top N

theorem card_of_iso {I : Type} [Group I] (e : I ≃* alternatingGroup (Fin 7)) : Nat.card I = 2520 := by
  rw [Nat.card_congr e.toEquiv, card_alt7]

theorem hom_trivial_of_small {I : Type} [Group I] (e : I ≃* alternatingGroup (Fin 7)) {M : Type} [Monoid M]
    (φ : I →* M) (hsmall : Nat.card (Set.range φ) < 2520) (i : I) : φ i = 1 := by
  haveI : Finite I := Finite.of_equiv _ e.toEquiv.symm
  haveI : Finite (Set.range φ) := (Set.finite_range φ).to_subtype
  have hn : (φ.ker).Normal := MonoidHom.normal_ker φ
  rcases simple_of_iso e φ.ker with h | h
  · exfalso
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 h
    have hle : Nat.card I ≤ Nat.card (Set.range φ) := by
      have : Function.Injective (fun x : I => (⟨φ x, x, rfl⟩ : Set.range φ)) := by
        intro a b hab
        exact hinj (congrArg Subtype.val hab)
      exact Nat.card_le_card_of_injective _ this
    rw [card_of_iso e] at hle
    omega
  · have : i ∈ φ.ker := by rw [h]; exact Subgroup.mem_top i
    exact this

theorem card_end_le (X : Type) [AddCommGroup X] [Module (ZMod 2) X] [Finite X] :
    Nat.card (X →ₗ[ZMod 2] X) ≤ Nat.card X ^ Module.finrank (ZMod 2) X := by
  let b := Module.finBasis (ZMod 2) X
  have hinj : Function.Injective
      (fun f : X →ₗ[ZMod 2] X => fun i : Fin (Module.finrank (ZMod 2) X) => f (b i)) := by
    intro f g hfg
    apply b.ext
    intro i
    exact congrFun hfg i
  haveI : Finite (Fin (Module.finrank (ZMod 2) X) → X) := inferInstance
  have h1 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at h1
  exact h1

theorem comm_bound (A : Type) [AddCommGroup A] [Module (ZMod 2) A] [Module.Finite (ZMod 2) A] [Finite A]
    (hA : Module.finrank (ZMod 2) A = 4) (R : A →ₗ[ZMod 2] A)
    (hR : ∀ x, R (R x) + R x + x = 0) :
    Nat.card {f : A →ₗ[ZMod 2] A // ∀ x, f (R x) = R (f x)} ≤ 256 := by
  have hchar : ∀ y : A, y + y = 0 := fun y => by
    rw [← two_smul (ZMod 2) y]
    have h2 : (2 : ZMod 2) = 0 := rfl
    rw [h2, zero_smul]
  have hneg : ∀ y : A, -y = y := fun y => neg_eq_of_add_eq_zero_right (hchar y)
  have hcancel : ∀ x y : A, x + y = 0 → y = x := fun x y h => (eq_neg_of_add_eq_zero_right h).trans (hneg x)
  have hR2 : ∀ x, R (R x) = R x + x := fun x =>
    (eq_neg_of_add_eq_zero_left (by rw [← add_assoc]; exact hR x)).trans (hneg _)
  obtain ⟨a1, ha1⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2)).1 (by rw [hA]; norm_num)
  have hRa1 : R a1 ≠ 0 := by
    intro h
    apply ha1
    have := hR a1
    simpa [h] using this
  have hRa1' : R a1 ≠ a1 := by
    intro h
    apply ha1
    have h1 := hR a1
    simp only [h] at h1
    calc a1 = (a1 + a1) + a1 := by rw [hchar a1, zero_add]
      _ = 0 := h1
  have indep2 : ∀ s t : ZMod 2, s • a1 + t • R a1 = 0 → s = 0 ∧ t = 0 := by
    intro s t h
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) s with rfl | rfl <;>
      rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exact absurd (by simpa using h) hRa1
    · exact absurd (by simpa using h) ha1
    · exact absurd (hcancel a1 (R a1) (by simpa using h)) hRa1'
  set P1 := Submodule.span (ZMod 2) ({a1, R a1} : Set A) with hP1def
  have ha1mem : a1 ∈ P1 := Submodule.subset_span (Set.mem_insert _ _)
  have hRmem : R a1 ∈ P1 := Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hP1_mem : ∀ s t : ZMod 2, s • a1 + t • R a1 ∈ P1 := fun s t =>
    P1.add_mem (P1.smul_mem s ha1mem) (P1.smul_mem t hRmem)
  have hPR : ∀ p ∈ P1, R p ∈ P1 := by
    intro p hp
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hp
    have : R (s • a1 + t • R a1) = t • a1 + (s + t) • R a1 := by
      rw [map_add, map_smul, map_smul, hR2]; module
    rw [this]; exact hP1_mem _ _
  have hfin : Module.finrank (ZMod 2) P1 ≤ 2 := by
    classical
    have h := finrank_span_finset_le_card (R := ZMod 2) ({a1, R a1} : Finset A)
    have hc := Finset.card_le_two (a := a1) (b := R a1)
    simp only [Finset.coe_insert, Finset.coe_singleton] at h
    unfold Set.finrank at h
    rw [← hP1def] at h
    omega
  have hlt : P1 < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [h, finrank_top, hA] at hfin
    omega
  obtain ⟨a2, -, ha2⟩ := SetLike.exists_of_lt hlt
  have ha2' : a2 ∉ P1 := ha2
  have hkey : ∀ x y : ZMod 2, x • a2 + y • R a2 ∈ P1 → x = 0 ∧ y = 0 := by
    intro x y hxy
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) x with rfl | rfl <;>
      rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) y with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exfalso
      simp only [zero_smul, one_smul, zero_add] at hxy
      have h1 := hPR _ hxy
      apply ha2'
      have : a2 = R (R a2) + R a2 := by
        rw [hR2]; calc a2 = (R a2 + a2) + R a2 := by rw [add_assoc, add_comm a2, ← add_assoc, hchar, zero_add]
          _ = R a2 + a2 + R a2 := rfl
      rw [this]; exact P1.add_mem h1 hxy
    · exfalso
      simp only [one_smul, zero_smul, add_zero] at hxy
      apply ha2'
      exact hxy
    · exfalso
      simp only [one_smul] at hxy
      have h1 := hPR _ hxy
      apply ha2'
      have : R (a2 + R a2) = a2 := by
        rw [map_add, hR2]; calc R a2 + (R a2 + a2) = (R a2 + R a2) + a2 := by abel
          _ = a2 := by rw [hchar, zero_add]
      rw [← this]; exact h1
  let b : Fin 4 → A := ![a1, R a1, a2, R a2]
  have hli : LinearIndependent (ZMod 2) b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp [Fin.sum_univ_four, b] at hg
    have hq : g 2 • a2 + g 3 • R a2 ∈ P1 := by
      have hXY : (g 0 • a1 + g 1 • R a1) + (g 2 • a2 + g 3 • R a2) = 0 := by
        rw [show (g 0 • a1 + g 1 • R a1) + (g 2 • a2 + g 3 • R a2)
          = g 0 • a1 + g 1 • R a1 + g 2 • a2 + g 3 • R a2 by abel]
        exact hg
      have : g 2 • a2 + g 3 • R a2 = -(g 0 • a1 + g 1 • R a1) := eq_neg_of_add_eq_zero_right hXY
      rw [this]; exact P1.neg_mem (hP1_mem _ _)
    obtain ⟨h2, h3⟩ := hkey _ _ hq
    have hg' : g 0 • a1 + g 1 • R a1 = 0 := by
      rw [h2, h3, zero_smul, zero_smul, add_zero, add_zero] at hg
      exact hg
    obtain ⟨h0, h1⟩ := indep2 _ _ hg'
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hcardb : Fintype.card (Fin 4) = Module.finrank (ZMod 2) A := by simp [hA]
  have hspan : Submodule.span (ZMod 2) (Set.range b) = ⊤ := by
    have := (basisOfLinearIndependentOfCardEqFinrank hli hcardb).span_eq
    rwa [coe_basisOfLinearIndependentOfCardEqFinrank] at this
  have hinj : Function.Injective
      (fun f : {f : A →ₗ[ZMod 2] A // ∀ x, f (R x) = R (f x)} => (f.1 a1, f.1 a2)) := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    simp only [Prod.mk.injEq] at h
    apply Subtype.ext
    apply LinearMap.ext_on_range hspan
    intro i
    fin_cases i
    · exact h.1
    · show f (R a1) = g (R a1)
      rw [hf, hg, h.1]
    · exact h.2
    · show f (R a2) = g (R a2)
      rw [hf, hg, h.2]
  have hcardA : Nat.card A = 16 := by
    haveI := Fintype.ofFinite A
    have := Module.card_eq_pow_finrank (K := ZMod 2) (V := A)
    rw [hA, ← Nat.card_eq_fintype_card] at this
    simpa using this
  calc Nat.card {f : A →ₗ[ZMod 2] A // ∀ x, f (R x) = R (f x)}
      ≤ Nat.card (A × A) := Nat.card_le_card_of_injective _ hinj
    _ = 256 := by rw [Nat.card_prod, hcardA]

theorem fixed_point_ne {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime] (hH : IsPGroup p H)
    {α : Type} [MulAction H α] [Finite α] (a0 : α) (h0 : ∀ h : H, h • a0 = a0)
    (hp : p ∣ Nat.card α) : ∃ a : α, a ≠ a0 ∧ ∀ h : H, h • a = a := by
  by_contra hcon
  push Not at hcon
  have hF : MulAction.fixedPoints H α = {a0} := by
    ext a
    constructor
    · intro ha
      by_contra hne
      obtain ⟨h, hh⟩ := hcon a hne
      exact hh (ha h)
    · intro ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact h0
  have hmod := hH.card_modEq_card_fixedPoints (α := α)
  have hcard1 : Nat.card (↥(MulAction.fixedPoints H α)) = 1 := by rw [hF]; simp
  rw [hcard1] at hmod
  have h1 : (0 : ℕ) ≡ 1 [MOD p] := (Nat.modEq_zero_iff_dvd.2 hp).symm.trans hmod
  have h2 : p ∣ 1 := Nat.modEq_zero_iff_dvd.1 h1.symm
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h2)

theorem exists_three_ne_one {I : Type} [Group I] (e : I ≃* alternatingGroup (Fin 7)) :
    ∃ c : I, c ^ 3 = 1 ∧ c ≠ 1 := by
  let σ : alternatingGroup (Fin 7) := ⟨Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide⟩
  have hσ3 : σ ^ 3 = 1 := Subtype.ext (by decide)
  have hσ1 : σ ≠ 1 := fun h => by
    have := congrArg (fun x : alternatingGroup (Fin 7) => (x : Equiv.Perm (Fin 7)) 0) h
    exact absurd this (by decide)
  refine ⟨e.symm σ, ?_, ?_⟩
  · rw [← map_pow, hσ3, map_one]
  · intro h
    apply hσ1
    have : e (e.symm σ) = e 1 := by rw [h]
    rwa [MulEquiv.apply_symm_apply, map_one] at this

theorem hchar_Vx (v : Vx) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [h2, zero_smul]

theorem rho_cube_apply {d : Gx} (hd : d ^ 3 = 1) (v : Vx) :
    rho d (rho d (rho d v)) = v := by
  have h3 : rho d * (rho d * rho d) = 1 := by rw [← pow_three, ← map_pow, hd, map_one]
  have h := congrArg (fun f : Ex => f v) h3
  simpa [Module.End.mul_apply] using h

noncomputable def epsE (d : Gx) : Ex := 1 + rho d + rho d * rho d

theorem epsE_apply (d : Gx) (v : Vx) : epsE d v = v + rho d v + rho d (rho d v) := by
  simp [epsE, Module.End.mul_apply]

theorem rho_eps {d : Gx} (hd : d ^ 3 = 1) (v : Vx) : rho d (epsE d v) = epsE d v := by
  simp only [epsE_apply, map_add, rho_cube_apply hd]
  abel

theorem epsE_rho {d : Gx} (hd : d ^ 3 = 1) (v : Vx) : epsE d (rho d v) = epsE d v := by
  simp only [epsE_apply, map_add, rho_cube_apply hd]
  abel

theorem epsE_eps {d : Gx} (hd : d ^ 3 = 1) (v : Vx) : epsE d (epsE d v) = epsE d v := by
  have hw := rho_eps hd v
  rw [epsE_apply d (epsE d v)]
  simp only [hw]
  rw [add_assoc, hchar_Vx, add_zero]

theorem range_eps_iff {d : Gx} (hd : d ^ 3 = 1) (w : Vx) :
    w ∈ LinearMap.range (epsE d) ↔ rho d w = w := by
  constructor
  · rintro ⟨x, rfl⟩
    exact rho_eps hd x
  · intro h
    refine ⟨w, ?_⟩
    rw [epsE_apply, h, h, hchar_Vx, zero_add]

theorem range_sup_ker_eq_top {d : Gx} (hd : d ^ 3 = 1) :
    LinearMap.range (epsE d) ⊔ LinearMap.ker (epsE d) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [Submodule.mem_sup]
  refine ⟨epsE d v, ⟨v, rfl⟩, v - epsE d v, ?_, by abel⟩
  rw [LinearMap.mem_ker, map_sub, epsE_eps hd, sub_self]

theorem range_inf_ker_eq_bot {d : Gx} (hd : d ^ 3 = 1) :
    LinearMap.range (epsE d) ⊓ LinearMap.ker (epsE d) = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hw1, hw2⟩
  obtain ⟨x, rfl⟩ := hw1
  rw [Submodule.mem_bot]
  have h := epsE_eps hd x
  have hw2' : epsE d (epsE d x) = 0 := hw2
  rw [hw2'] at h
  exact h.symm

theorem finrank_range_add_ker {d : Gx} :
    Module.finrank (ZMod 2) (LinearMap.range (epsE d)) +
      Module.finrank (ZMod 2) (LinearMap.ker (epsE d)) = 6 := by
  have h := LinearMap.finrank_range_add_finrank_ker (epsE d)
  have hι : Fintype.card L62Model.ι = 6 := by simp [L62Model.ι, L62Model.ι₂]
  rw [Module.finrank_fintype_fun_eq_card, hι] at h
  exact h

@[expose] noncomputable def actV (H : Subgroup Gx) : MulAction H Vx where
  smul h v := rho (h : Gx) v
  one_smul v := by
    change rho ((1 : H) : Gx) v = v
    rw [Subgroup.coe_one, map_one]; rfl
  mul_smul h k v := by
    change rho ((h * k : H) : Gx) v = rho (h : Gx) (rho (k : Gx) v)
    rw [Subgroup.coe_mul, map_mul]; rfl

def stabV (v : Vx) : Subgroup Gx where
  carrier := {g | rho g v = v}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h1 : rho a⁻¹ (rho a v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
    rw [ha] at h1; exact h1

theorem even_of_two_pow_mod_three (k : ℕ) (h : 2 ^ k % 3 = 1) : Even k := by
  rcases Nat.even_or_odd k with hk | ⟨m, rfl⟩
  · exact hk
  · exfalso
    have : 2 ^ (2 * m + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
    rw [this] at h
    norm_num at h

theorem even_finrank_range {d : Gx} (hd : d ^ 3 = 1) (hd1 : d ≠ 1) :
    Even (Module.finrank (ZMod 2) (LinearMap.range (epsE d))) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord : orderOf d = 3 := orderOf_eq_prime hd hd1
  have hcard : Nat.card (Subgroup.zpowers d) = 3 := by rw [Nat.card_zpowers, hord]
  haveI : Finite (Subgroup.zpowers d) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hP : IsPGroup 3 (Subgroup.zpowers d) := IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)
  letI : MulAction (Subgroup.zpowers d) Vx := actV (Subgroup.zpowers d)
  have hfix : MulAction.fixedPoints (Subgroup.zpowers d) Vx =
      ((LinearMap.range (epsE d) : Submodule (ZMod 2) Vx) : Set Vx) := by
    ext v
    rw [MulAction.mem_fixedPoints, SetLike.mem_coe, range_eps_iff hd]
    constructor
    · intro h
      exact h ⟨d, Subgroup.mem_zpowers d⟩
    · intro h y
      have hsub : Subgroup.zpowers d ≤ stabV v := Subgroup.zpowers_le.2 (show d ∈ stabV v from h)
      exact hsub y.2
  have hmod := hP.card_modEq_card_fixedPoints (α := Vx)
  have hV : Nat.card Vx = 64 := by
    simp [Nat.card_fun, L62Model.ι, L62Model.ι₂]
  have hW : Nat.card (LinearMap.range (epsE d)) = 2 ^ Module.finrank (ZMod 2) (LinearMap.range (epsE d)) := by
    haveI := Fintype.ofFinite (LinearMap.range (epsE d))
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2)]
    simp
  rw [hV, hfix] at hmod
  have hW' : Nat.card ((LinearMap.range (epsE d) : Submodule (ZMod 2) Vx) : Set Vx) =
      Nat.card (LinearMap.range (epsE d)) := rfl
  rw [hW'] at hmod
  rw [hW] at hmod
  apply even_of_two_pow_mod_three
  unfold Nat.ModEq at hmod
  rw [← hmod]

end CFSG.LocalAnalysis.GLTheoremA.CatB.L62F
