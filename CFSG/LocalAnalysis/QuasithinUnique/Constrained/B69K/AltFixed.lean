module

public import CFSG.Quasithin.Background.G6Natural
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.B69K

@[expose] def ptStab (m : ℕ) (p₀ : Fin m) : Subgroup (Equiv.Perm (Fin m)) :=
  (alternatingGroup {x : Fin m // x ≠ p₀}).map
    (Equiv.Perm.ofSubtype (p := fun x : Fin m => x ≠ p₀))

theorem mem_ptStab_iff {m : ℕ} (p₀ : Fin m) (σ : Equiv.Perm (Fin m)) :
    σ ∈ ptStab m p₀ ↔ σ ∈ alternatingGroup (Fin m) ∧ σ p₀ = p₀ := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨?_, Equiv.Perm.ofSubtype_apply_of_not_mem τ (by simp)⟩
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_ofSubtype]
    exact Equiv.Perm.mem_alternatingGroup.mp hτ
  · rintro ⟨hσA, hσp⟩
    have h1 : ∀ x, σ x ≠ p₀ ↔ x ≠ p₀ := fun x => by
      conv_lhs => rw [← hσp]
      exact σ.injective.ne_iff
    have h2 : ∀ x, σ x ≠ x → x ≠ p₀ := fun x hx hxp => by
      subst hxp
      exact hx hσp
    have hsign := Equiv.Perm.sign_ofSubtype
      (Equiv.Perm.subtypePerm (p := fun x : Fin m => x ≠ p₀) σ h1)
    rw [Equiv.Perm.ofSubtype_subtypePerm (p := fun x : Fin m => x ≠ p₀) h1 h2] at hsign
    refine Subgroup.mem_map.mpr ⟨Equiv.Perm.subtypePerm (p := fun x : Fin m => x ≠ p₀) σ h1, ?_,
      Equiv.Perm.ofSubtype_subtypePerm (p := fun x : Fin m => x ≠ p₀) h1 h2⟩
    rw [Equiv.Perm.mem_alternatingGroup, ← hsign]
    exact Equiv.Perm.mem_alternatingGroup.mp hσA

theorem ptStab_commutator {m : ℕ} (h7 : 7 ≤ m) (p₀ : Fin m) :
    ⁅ptStab m p₀, ptStab m p₀⁆ = ptStab m p₀ := by
  have h5 : 5 ≤ Nat.card {x : Fin m // x ≠ p₀} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_ne',
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  unfold ptStab
  rw [← Subgroup.map_commutator, commutator_alternatingGroup_eq_self h5]

theorem perfect_of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (hH : ⁅f.range, f.range⁆ = f.range) :
    ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := by
  have key : Subgroup.map f ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = f.range := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, hH]
  rw [eq_top_iff]
  intro x _
  have hx : f x ∈ f.range := MonoidHom.mem_range.mpr ⟨x, rfl⟩
  rw [← key] at hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  rw [hf hyx] at hy
  exact hy

theorem hom_trivial_of_perfect {G A : Type*} [Group G] [CommGroup A] (c : G →* A)
    (hG : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤) (g : G) : c g = 1 := by
  have hle : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ c.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact Commute.all _ _
  rw [hG] at hle
  exact MonoidHom.mem_ker.mp (hle (Subgroup.mem_top g))

@[expose] def stabH {Γ : Type} [Group Γ] {m : ℕ} (ρ : Γ →* Equiv.Perm (Fin m)) (p₀ : Fin m) :
    Subgroup Γ :=
  (ptStab m p₀).comap ρ

theorem mem_stabH_iff {Γ : Type} [Group Γ] {m : ℕ} (ρ : Γ →* Equiv.Perm (Fin m))
    (hρA : ∀ γ, ρ γ ∈ alternatingGroup (Fin m)) (p₀ : Fin m) (γ : Γ) :
    γ ∈ stabH ρ p₀ ↔ ρ γ p₀ = p₀ := by
  unfold stabH
  rw [Subgroup.mem_comap, mem_ptStab_iff]
  exact ⟨fun h => h.2, fun h => ⟨hρA γ, h⟩⟩

theorem stabH_perfect {Γ : Type} [Group Γ] {m : ℕ} (h7 : 7 ≤ m) (ρ : Γ →* Equiv.Perm (Fin m))
    (hρA : ∀ γ, ρ γ ∈ alternatingGroup (Fin m))
    (hρs : ∀ σ ∈ alternatingGroup (Fin m), ∃ γ, ρ γ = σ) (hρi : Function.Injective ρ)
    (p₀ : Fin m) :
    ⁅(⊤ : Subgroup (stabH ρ p₀)), (⊤ : Subgroup (stabH ρ p₀))⁆ = ⊤ := by
  have hr : (ρ.comp (stabH ρ p₀).subtype).range = ptStab m p₀ := by
    ext σ
    constructor
    · rintro ⟨x, rfl⟩
      exact (mem_ptStab_iff p₀ _).mpr ⟨hρA _, (mem_stabH_iff ρ hρA p₀ _).mp x.2⟩
    · intro hσ
      obtain ⟨γ, rfl⟩ := hρs σ ((mem_ptStab_iff p₀ σ).mp hσ).1
      exact ⟨⟨γ, (mem_stabH_iff ρ hρA p₀ γ).mpr ((mem_ptStab_iff p₀ _).mp hσ).2⟩, rfl⟩
  apply perfect_of_injective (ρ.comp (stabH ρ p₀).subtype)
  · intro x y hxy
    exact Subtype.ext (hρi hxy)
  · rw [hr]
    exact ptStab_commutator h7 p₀

@[expose] def epsVec {m : ℕ} (p : Fin m) : Fin m → ZMod 2 := fun i => if i = p then 0 else 1

theorem sum_epsVec {m : ℕ} (hodd : Odd m) (p : Fin m) : ∑ i, epsVec p i = 0 := by
  have h1 : ∀ i, epsVec p i = 1 + (if i = p then 1 else 0) := fun i => by
    unfold epsVec
    by_cases h : i = p <;> simp [h] <;> decide
  have h2 : ∑ i : Fin m, (1 : ZMod 2) = (m : ZMod 2) := by simp
  have h3 : ∑ i : Fin m, (if i = p then (1 : ZMod 2) else 0) = 1 := by simp
  simp only [h1]
  rw [Finset.sum_add_distrib, h2, h3, ZMod.natCast_eq_one_iff_odd.mpr hodd] <;> decide

@[expose] def epsN {m : ℕ} (hodd : Odd m) (p : Fin m) : ↥(G6.coreMod m) :=
  ⟨Multiplicative.ofAdd (epsVec p), by
    simpa [G6.mem_coreMod] using sum_epsVec hodd p⟩

theorem coreAct_epsN {m : ℕ} (hodd : Odd m) (σ : Equiv.Perm (Fin m)) (p : Fin m) :
    G6.coreAct m σ (epsN hodd p) = epsN hodd (σ p) := by
  apply Subtype.ext
  rw [G6.coreAct_coe]
  apply Multiplicative.toAdd.injective
  funext i
  simp [epsN, G6.permAct_apply, epsVec, Equiv.Perm.inv_eq_iff_eq, Equiv.symm_apply_eq]

@[expose] def phiHom {W : Type} [CommGroup W] {U : Subgroup W} {m : ℕ}
    (e : (W ⧸ U) ≃* ↥(G6.coreMod m)) : W →* ↥(G6.coreMod m) :=
  e.toMonoidHom.comp (QuotientGroup.mk' U)

theorem phiHom_apply {W : Type} [CommGroup W] {U : Subgroup W} {m : ℕ}
    (e : (W ⧸ U) ≃* ↥(G6.coreMod m)) (w : W) :
    phiHom e w = e (QuotientGroup.mk w) := rfl

theorem fixed_of_stab {W : Type} [CommGroup W] {Γ : Type} [Group Γ] (act : Γ →* MulAut W)
    {U : Subgroup W} (hU : ∀ γ : Γ, ∀ u ∈ U, act γ u = u) {m : ℕ} (hodd : Odd m)
    (h7 : 7 ≤ m) (ρ : Γ →* Equiv.Perm (Fin m)) (hρA : ∀ γ, ρ γ ∈ alternatingGroup (Fin m))
    (hρs : ∀ σ ∈ alternatingGroup (Fin m), ∃ γ, ρ γ = σ) (hρi : Function.Injective ρ)
    (e : (W ⧸ U) ≃* ↥(G6.coreMod m))
    (he : ∀ γ w, e (QuotientGroup.mk (act γ w)) = G6.coreAct m (ρ γ) (e (QuotientGroup.mk w)))
    (p₀ : Fin m) (w₀ : W) (hw₀ : e (QuotientGroup.mk w₀) = epsN hodd p₀)
    {h : Γ} (hh : ρ h p₀ = p₀) : act h w₀ = w₀ := by
  have hcU : ∀ g : Γ, ρ g p₀ = p₀ → act g w₀ * w₀⁻¹ ∈ U := by
    intro g hg
    have h1 : e (QuotientGroup.mk (act g w₀)) = e (QuotientGroup.mk w₀) := by
      rw [he, hw₀, coreAct_epsN hodd, hg]
    have h2 : (QuotientGroup.mk (act g w₀) : W ⧸ U) = QuotientGroup.mk w₀ := e.injective h1
    have h3 : (act g w₀)⁻¹ * w₀ ∈ U := QuotientGroup.eq.mp h2
    have h4 : ((act g w₀)⁻¹ * w₀)⁻¹ = act g w₀ * w₀⁻¹ := by
      rw [mul_inv_rev, inv_inv, mul_comm]
    rw [← h4]
    exact U.inv_mem h3
  have hmul : ∀ g h' : Γ, ρ h' p₀ = p₀ →
      act (g * h') w₀ * w₀⁻¹ = (act g w₀ * w₀⁻¹) * (act h' w₀ * w₀⁻¹) := by
    intro g h' hh'
    have hc : act h' w₀ * w₀⁻¹ ∈ U := hcU h' hh'
    set c := act h' w₀ * w₀⁻¹ with hc_def
    have e1 : act h' w₀ = c * w₀ := by
      rw [hc_def, inv_mul_cancel_right]
    rw [map_mul, MulAut.mul_apply, e1, map_mul, hU g c hc]
    ac_rfl
  let F : ↥(stabH ρ p₀) →* ↥U :=
    { toFun := fun g => ⟨act g.1 w₀ * w₀⁻¹, hcU g.1 ((mem_stabH_iff ρ hρA p₀ g.1).mp g.2)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun g g' => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        exact hmul g.1 g'.1 ((mem_stabH_iff ρ hρA p₀ g'.1).mp g'.2) }
  have h1 := hom_trivial_of_perfect F (stabH_perfect h7 ρ hρA hρs hρi p₀)
    ⟨h, (mem_stabH_iff ρ hρA p₀ h).mpr hh⟩
  have h2 : act h w₀ * w₀⁻¹ = 1 := congrArg Subtype.val h1
  exact mul_inv_eq_one.mp h2

theorem exists_gamma_point {Γ : Type} [Group Γ] {m : ℕ} (ρ : Γ →* Equiv.Perm (Fin m))
    (hρs : ∀ σ ∈ alternatingGroup (Fin m), ∃ γ, ρ γ = σ) (h7 : 7 ≤ m) (p₀ p : Fin m) :
    ∃ γ, ρ γ p₀ = p := by
  have hcard : ({p₀, p} : Finset (Fin m)).card < (Finset.univ : Finset (Fin m)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Finset.card_le_two (by omega)
  obtain ⟨q, _, hqs⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hqs
  obtain ⟨hq0, hq1⟩ := hqs
  have hσ : (Equiv.swap p q * Equiv.swap p₀ q) p₀ = p := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hσA : Equiv.swap p q * Equiv.swap p₀ q ∈ alternatingGroup (Fin m) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (Ne.symm hq1), Equiv.Perm.sign_swap (Ne.symm hq0)]
    rfl
  obtain ⟨γ, hγ⟩ := hρs _ hσA
  exact ⟨γ, by rw [hγ]; exact hσ⟩

theorem exists_wfam {W : Type} [CommGroup W] {Γ : Type} [Group Γ] (act : Γ →* MulAut W)
    {U : Subgroup W} (hU : ∀ γ : Γ, ∀ u ∈ U, act γ u = u) {m : ℕ} (hodd : Odd m)
    (h7 : 7 ≤ m) (ρ : Γ →* Equiv.Perm (Fin m)) (hρA : ∀ γ, ρ γ ∈ alternatingGroup (Fin m))
    (hρs : ∀ σ ∈ alternatingGroup (Fin m), ∃ γ, ρ γ = σ) (hρi : Function.Injective ρ)
    (e : (W ⧸ U) ≃* ↥(G6.coreMod m))
    (he : ∀ γ w, e (QuotientGroup.mk (act γ w)) = G6.coreAct m (ρ γ) (e (QuotientGroup.mk w)))
    (p₀ : Fin m) (w₀ : W) (hw₀ : e (QuotientGroup.mk w₀) = epsN hodd p₀) :
    ∃ wf : Fin m → W, (∀ g p, act g (wf p) = wf (ρ g p)) ∧
      (∀ p, e (QuotientGroup.mk (wf p)) = epsN hodd p) := by
  choose gam hgam using fun p : Fin m => exists_gamma_point ρ hρs h7 p₀ p
  refine ⟨fun p => act (gam p) w₀, ?_, ?_⟩
  · intro g p
    show act g (act (gam p) w₀) = act (gam (ρ g p)) w₀
    have hρh : ρ ((gam (ρ g p))⁻¹ * (g * gam p)) p₀ = p₀ := by
      rw [map_mul, map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgam p,
        Equiv.Perm.inv_eq_iff_eq, hgam (ρ g p)]
    have hfix := fixed_of_stab act hU hodd h7 ρ hρA hρs hρi e he p₀ w₀ hw₀ hρh
    calc act g (act (gam p) w₀) = act (g * gam p) w₀ := by rw [map_mul, MulAut.mul_apply]
      _ = act (gam (ρ g p) * ((gam (ρ g p))⁻¹ * (g * gam p))) w₀ := by
          rw [mul_inv_cancel_left]
      _ = act (gam (ρ g p)) (act ((gam (ρ g p))⁻¹ * (g * gam p)) w₀) := by
          rw [map_mul, MulAut.mul_apply]
      _ = act (gam (ρ g p)) w₀ := by rw [hfix]
  · intro p
    show e (QuotientGroup.mk (act (gam p) w₀)) = epsN hodd p
    rw [he, hw₀, coreAct_epsN hodd, hgam p]

@[expose] def secS {W : Type} [CommGroup W] {m : ℕ} (wf : Fin m → W) (x : Fin m → ZMod 2) : W :=
  ∏ p, if x p = 1 then wf p else 1

theorem ite_zmod2_add {W : Type} [CommGroup W] (c : W) (hc : c ^ 2 = 1) (a b : ZMod 2) :
    (if a + b = 1 then c else 1) = (if a = 1 then c else 1) * (if b = 1 then c else 1) := by
  have hc' : c * c = 1 := by rw [← pow_two]; exact hc
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide) a with rfl | rfl <;>
    rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide) b with rfl | rfl <;>
    simp [hc', h11]

theorem secS_add {W : Type} [CommGroup W] {m : ℕ} (wf : Fin m → W) (hwf : ∀ p, wf p ^ 2 = 1)
    (x y : Fin m → ZMod 2) : secS wf (x + y) = secS wf x * secS wf y := by
  unfold secS
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun p _ => ite_zmod2_add (wf p) (hwf p) (x p) (y p))

theorem secS_zero {W : Type} [CommGroup W] {m : ℕ} (wf : Fin m → W) :
    secS wf 0 = 1 := by
  simp [secS]

@[expose] def secN {W : Type} [CommGroup W] {m : ℕ} (wf : Fin m → W) (hwf : ∀ p, wf p ^ 2 = 1) :
    ↥(G6.coreMod m) →* W where
  toFun y := secS wf (Multiplicative.toAdd (y : G6.PermMod m))
  map_one' := by
    show secS wf (Multiplicative.toAdd ((1 : ↥(G6.coreMod m)) : G6.PermMod m)) = 1
    rw [Subgroup.coe_one, toAdd_one, secS_zero]
  map_mul' y z := by
    show secS wf (Multiplicative.toAdd ((y * z : ↥(G6.coreMod m)) : G6.PermMod m)) =
      secS wf (Multiplicative.toAdd (y : G6.PermMod m)) *
        secS wf (Multiplicative.toAdd (z : G6.PermMod m))
    rw [Subgroup.coe_mul, toAdd_mul, secS_add wf hwf]

theorem secN_apply {W : Type} [CommGroup W] {m : ℕ} (wf : Fin m → W) (hwf : ∀ p, wf p ^ 2 = 1)
    (y : ↥(G6.coreMod m)) :
    secN wf hwf y = secS wf (Multiplicative.toAdd (y : G6.PermMod m)) := rfl

theorem act_secS {W : Type} [CommGroup W] {m : ℕ} (wf : Fin m → W) (a : MulAut W)
    (σ : Equiv.Perm (Fin m)) (hwf : ∀ p, a (wf p) = wf (σ p)) (x : Fin m → ZMod 2) :
    a (secS wf x) = secS wf (fun q => x (σ⁻¹ q)) := by
  unfold secS
  rw [map_prod]
  have h2 : ∏ p, a (if x p = 1 then wf p else 1) =
      ∏ p, (if x (σ⁻¹ (σ p)) = 1 then wf (σ p) else 1) := by
    apply Finset.prod_congr rfl
    intro p _
    simp [apply_ite a, hwf]
  rw [h2]
  exact Equiv.prod_comp σ (fun q => if x (σ⁻¹ q) = 1 then wf q else 1)

theorem act_secN {W : Type} [CommGroup W] {Γ : Type} [Group Γ] (act : Γ →* MulAut W) {m : ℕ}
    (ρ : Γ →* Equiv.Perm (Fin m)) (wf : Fin m → W) (hwf : ∀ p, wf p ^ 2 = 1)
    (hwEq : ∀ g p, act g (wf p) = wf (ρ g p)) (γ : Γ) (y : ↥(G6.coreMod m)) :
    act γ (secN wf hwf y) = secN wf hwf (G6.coreAct m (ρ γ) y) := by
  rw [secN_apply, secN_apply, act_secS wf (act γ) (ρ γ) (hwEq γ)]
  congr 1

theorem sum_ite_epsVec {m : ℕ} (x : Fin m → ZMod 2) (hx : ∑ i, x i = 0) :
    ∑ p, (if x p = 1 then epsVec p else 0) = x := by
  funext i
  have hpt : ∀ p, (if x p = 1 then epsVec p else 0) i = x p + (if i = p then x p else 0) := by
    intro p
    rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide) (x p) with h | h <;>
      by_cases hi : i = p <;> simp [h, hi, epsVec] <;> decide
  rw [Finset.sum_apply]
  simp only [hpt]
  simp [Finset.sum_add_distrib, hx]

theorem phi_secS {W : Type} [CommGroup W] {U : Subgroup W} {m : ℕ} (hodd : Odd m)
    (e : (W ⧸ U) ≃* ↥(G6.coreMod m)) (wf : Fin m → W)
    (hwphi : ∀ p, e (QuotientGroup.mk (wf p)) = epsN hodd p) (x : Fin m → ZMod 2) :
    phiHom e (secS wf x) = ∏ p, (if x p = 1 then epsN hodd p else 1) := by
  unfold secS
  rw [map_prod]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  split_ifs with h
  · exact hwphi p
  · exact map_one _

theorem toAdd_phi_secS {W : Type} [CommGroup W] {U : Subgroup W} {m : ℕ} (hodd : Odd m)
    (e : (W ⧸ U) ≃* ↥(G6.coreMod m)) (wf : Fin m → W)
    (hwphi : ∀ p, e (QuotientGroup.mk (wf p)) = epsN hodd p) (x : Fin m → ZMod 2) :
    Multiplicative.toAdd ((phiHom e (secS wf x) : ↥(G6.coreMod m)) : G6.PermMod m) =
      ∑ p, (if x p = 1 then epsVec p else 0) := by
  rw [phi_secS hodd e wf hwphi x, SubmonoidClass.coe_finset_prod, toAdd_prod]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs <;> rfl

theorem phi_secN_eq {W : Type} [CommGroup W] {U : Subgroup W} {m : ℕ} (hodd : Odd m)
    (e : (W ⧸ U) ≃* ↥(G6.coreMod m)) (wf : Fin m → W) (hwf : ∀ p, wf p ^ 2 = 1)
    (hwphi : ∀ p, e (QuotientGroup.mk (wf p)) = epsN hodd p) (y : ↥(G6.coreMod m)) :
    phiHom e (secN wf hwf y) = y := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  rw [secN_apply, toAdd_phi_secS hodd e wf hwphi, sum_ite_epsVec _ (G6.mem_coreMod.mp y.2)]

theorem comm_mem_secN {W : Type} [CommGroup W] {U : Subgroup W} {Γ : Type} [Group Γ]
    (act : Γ →* MulAut W) (hU : ∀ γ : Γ, ∀ u ∈ U, act γ u = u) {m : ℕ} (hodd : Odd m)
    (ρ : Γ →* Equiv.Perm (Fin m)) (e : (W ⧸ U) ≃* ↥(G6.coreMod m))
    (wf : Fin m → W) (hwf : ∀ p, wf p ^ 2 = 1)
    (hwEq : ∀ g p, act g (wf p) = wf (ρ g p))
    (hwphi : ∀ p, e (QuotientGroup.mk (wf p)) = epsN hodd p) (γ : Γ) (w : W) :
    act γ w * w⁻¹ ∈ (secN wf hwf).range := by
  have key : ∀ (u : W) (y : ↥(G6.coreMod m)), u ∈ U →
      act γ (u * secN wf hwf y) * (u * secN wf hwf y)⁻¹ ∈ (secN wf hwf).range := by
    intro u y hu
    rw [map_mul, hU γ u hu, act_secN act ρ wf hwf hwEq γ y]
    have h3 : u * secN wf hwf (G6.coreAct m (ρ γ) y) * (u * secN wf hwf y)⁻¹ =
        secN wf hwf (G6.coreAct m (ρ γ) y * y⁻¹) := by
      rw [map_mul, map_inv, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
    rw [h3]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hu : w * (secN wf hwf (phiHom e w))⁻¹ ∈ U := by
    have h1 : phiHom e (w * (secN wf hwf (phiHom e w))⁻¹) = 1 := by
      rw [map_mul, map_inv, phi_secN_eq hodd e wf hwf hwphi, mul_inv_cancel]
    have h2 : (QuotientGroup.mk (w * (secN wf hwf (phiHom e w))⁻¹) : W ⧸ U) = 1 := by
      apply e.injective
      rw [map_one]
      exact h1
    exact (QuotientGroup.eq_one_iff _).mp h2
  have hw : w * (secN wf hwf (phiHom e w))⁻¹ * secN wf hwf (phiHom e w) = w :=
    inv_mul_cancel_right _ _
  have := key _ (phiHom e w) hu
  rw [hw] at this
  exact this

theorem fixed_eq_bot_of_natural {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {Γ : Type} [Group Γ] (act : Γ →* MulAut W) {U : Subgroup W}
    (hU : ∀ γ : Γ, ∀ u ∈ U, act γ u = u) {m : ℕ} (hodd : Odd m) (h7 : 7 ≤ m)
    (ρ : Γ →* Equiv.Perm (Fin m)) (hρA : ∀ γ, ρ γ ∈ alternatingGroup (Fin m))
    (hρs : ∀ σ ∈ alternatingGroup (Fin m), ∃ γ, ρ γ = σ) (hρi : Function.Injective ρ)
    (e : (W ⧸ U) ≃* ↥(G6.coreMod m))
    (he : ∀ γ w, e (QuotientGroup.mk (act γ w)) = G6.coreAct m (ρ γ) (e (QuotientGroup.mk w)))
    (hgen : Subgroup.closure {x : W | ∃ γ w, x = act γ w * w⁻¹} = ⊤) : U = ⊥ := by
  obtain ⟨p₀⟩ : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : W, e (QuotientGroup.mk w₀) = epsN hodd p₀ := by
    obtain ⟨x, hx⟩ := e.surjective (epsN hodd p₀)
    obtain ⟨w₀, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨w₀, hx⟩
  obtain ⟨wf, hwEq, hwphi⟩ := exists_wfam act hU hodd h7 ρ hρA hρs hρi e he p₀ w₀ hw₀
  have hwf : ∀ p, wf p ^ 2 = 1 := fun p => hW2 _
  have hle : Subgroup.closure {x : W | ∃ γ w, x = act γ w * w⁻¹} ≤ (secN wf hwf).range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨γ, w, rfl⟩
    exact comm_mem_secN act hU hodd ρ e wf hwf hwEq hwphi γ w
  rw [hgen] at hle
  rw [eq_bot_iff]
  intro u hu
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (hle (Subgroup.mem_top u))
  have h1 : phiHom e u = 1 := by
    rw [phiHom_apply, (QuotientGroup.eq_one_iff u).mpr hu, map_one]
  have h2 : phiHom e u = y := by
    rw [← hy]
    exact phi_secN_eq hodd e wf hwf hwphi y
  have hy1 : y = 1 := h2.symm.trans h1
  rw [Subgroup.mem_bot, ← hy, hy1, map_one]

end CFSG.Quasithin.B69K
