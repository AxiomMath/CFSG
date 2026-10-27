module

public import CFSG.CGT.Foote82.T66.CaseIS2
import CFSG.Quasithin.Background.G11Basic
public import CFSG.CGT.Foote82.T66.CaseIAltSub

public section

namespace CFSG.CGT.Foote82

namespace CaseIAux

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.Cooperstein.Coordinator
open Equiv Equiv.Perm CaseIPerm CaseIHeart

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

section Bounds

variable {X' : Subgroup (GLV V)} {N : ℕ} {β : ↥(commSpace X' ⊤) →+ altHeart N}

theorem le_finrank_of_dual' {c : GLV V} {r : ℕ} (w : Fin r → ↥(commSpace X' ⊤))
    (hw : ∀ i, (w i : V) ∈ commSpace (Subgroup.zpowers c) ⊤) (φ : Fin r → (altHeart N →+ ZMod 2))
    (hφ : ∀ i k, φ i (β (w k)) = if i = k then 1 else 0) :
    r ≤ Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers c) ⊤) := by
  classical
  set W : Submodule (ZMod 2) V := commSpace (Subgroup.zpowers c) ⊤ ⊓ commSpace X' ⊤ with hW
  let incl : ↥W →+ ↥(commSpace X' ⊤) :=
    (Submodule.inclusion (inf_le_right : W ≤ commSpace X' ⊤)).toAddMonoidHom
  let Φ0 : ↥W →+ (Fin r → ZMod 2) :=
    { toFun := fun v i => φ i (β (incl v))
      map_zero' := by funext i; simp
      map_add' := fun a b => by funext i; simp }
  let Φ : ↥W →ₗ[ZMod 2] (Fin r → ZMod 2) :=
    { toFun := Φ0
      map_add' := Φ0.map_add
      map_smul' := fun a v => by
        rcases (show a = 0 ∨ a = 1 by revert a; decide) with rfl | rfl
        · simp
        · simp }
  have hwW : ∀ k, (w k : V) ∈ W := fun k => ⟨hw k, (w k).2⟩
  have hΦ : ∀ k, Φ ⟨w k, hwW k⟩ = Pi.single k 1 := by
    intro k
    funext i
    have h1 : incl ⟨w k, hwW k⟩ = w k := Subtype.ext rfl
    have h2 : Φ ⟨w k, hwW k⟩ i = φ i (β (incl ⟨w k, hwW k⟩)) := rfl
    rw [h2, h1, hφ, Pi.single_apply]
  have hrange : LinearMap.range Φ = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun (ZMod 2) (Fin r)).span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [Pi.basisFun_apply]
    exact ⟨_, hΦ k⟩
  have h1 := LinearMap.finrank_range_le Φ
  rw [hrange, finrank_top, Module.finrank_fin_fun] at h1
  exact h1.trans (Submodule.finrank_mono inf_le_left)

theorem exists_comm_vec' (hsurj : Function.Surjective β) {c : GLV V}
    (hinv : ∀ u ∈ commSpace X' ⊤, c u ∈ commSpace X' ⊤) {σ : Perm (Fin N)}
    (hequiv : ∀ (w w' : ↥(commSpace X' ⊤)), (w' : V) = c (w : V) → ∀ y : evenWeight N,
      β w = (y : altHeart N) → β w' = (evenWeightPerm σ y : altHeart N))
    (y : evenWeight N) :
    ∃ w : ↥(commSpace X' ⊤), (w : V) ∈ commSpace (Subgroup.zpowers c) ⊤ ∧
      β w = ((evenWeightPerm σ y - y : evenWeight N) : altHeart N) := by
  obtain ⟨u, hu⟩ := hsurj (y : altHeart N)
  have hcu : c (u : V) ∈ commSpace X' ⊤ := hinv _ u.2
  refine ⟨⟨_, hcu⟩ - u, sub_mem_commSpace (Subgroup.mem_zpowers c) Submodule.mem_top, ?_⟩
  rw [map_sub, hequiv u ⟨_, hcu⟩ rfl y hu, hu]
  rfl

theorem four_le_finrank_of_act (hsurj : Function.Surjective β) {c : GLV V}
    (hinv : ∀ u ∈ commSpace X' ⊤, c u ∈ commSpace X' ⊤) {σ : Perm (Fin N)}
    (hequiv : ∀ (w w' : ↥(commSpace X' ⊤)), (w' : V) = c (w : V) → ∀ y : evenWeight N,
      β w = (y : altHeart N) → β w' = (evenWeightPerm σ y : altHeart N))
    (hσ3 : σ ^ 3 = 1) {p d : Fin N} (hp : σ p ≠ p)
    (hd : σ d ≠ d) (hdp : d ≠ p) (hdq : d ≠ σ p) (hdr : d ≠ σ (σ p)) :
    4 ≤ Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers c) ⊤) := by
  obtain ⟨h1, h2, h3, h4⟩ := orbit_ne hσ3 hp
  obtain ⟨k1, k2, k3, k4⟩ := orbit_ne hσ3 hd
  have e1 : σ d ≠ p := fun h => hdr (by rw [← h, k4])
  have e2 : σ d ≠ σ p := fun h => hdp (σ.injective h)
  have e3 : σ d ≠ σ (σ p) := fun h => hdq (σ.injective h)
  have e4 : σ (σ d) ≠ p := fun h => hdq (by rw [← h, k4])
  have e5 : σ (σ d) ≠ σ p := fun h => hdr (by
    have := congrArg σ h
    rw [k4] at this
    exact this)
  have e6 : σ (σ d) ≠ σ (σ p) := fun h => hdp (σ.injective (σ.injective h))
  obtain ⟨w₁, hw₁, hβ₁⟩ := exists_comm_vec' hsurj hinv hequiv (pairEW p (σ p))
  obtain ⟨w₂, hw₂, hβ₂⟩ := exists_comm_vec' hsurj hinv hequiv (pairEW (σ p) (σ (σ p)))
  obtain ⟨w₃, hw₃, hβ₃⟩ := exists_comm_vec' hsurj hinv hequiv (pairEW d (σ d))
  obtain ⟨w₄, hw₄, hβ₄⟩ := exists_comm_vec' hsurj hinv hequiv (pairEW (σ d) (σ (σ d)))
  have F : ∀ (a b x y : Fin N) (w : ↥(commSpace X' ⊤)),
      β w = ((evenWeightPerm σ (pairEW x y) - pairEW x y : evenWeight N) : altHeart N) →
      pairFun a b (β w) =
      ((((if a = σ x then 1 else 0) + (if a = σ y then 1 else 0)) -
        ((if a = x then 1 else 0) + (if a = y then 1 else 0))) +
      (((if b = σ x then 1 else 0) + (if b = σ y then 1 else 0)) -
        ((if b = x then 1 else 0) + (if b = y then 1 else 0))) : ZMod 2) :=
    fun a b x y w h => by rw [h, pairFun_comm]
  have f11 : pairFun p (σ p) (β w₁) = 1 := by
    rw [F _ _ _ _ _ hβ₁]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f12 : pairFun p (σ p) (β w₂) = 0 := by
    rw [F _ _ _ _ _ hβ₂]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f13 : pairFun p (σ p) (β w₃) = 0 := by
    rw [F _ _ _ _ _ hβ₃]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f14 : pairFun p (σ p) (β w₄) = 0 := by
    rw [F _ _ _ _ _ hβ₄]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f21 : pairFun p (σ (σ p)) (β w₁) = 0 := by
    rw [F _ _ _ _ _ hβ₁]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f22 : pairFun p (σ (σ p)) (β w₂) = 1 := by
    rw [F _ _ _ _ _ hβ₂]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f23 : pairFun p (σ (σ p)) (β w₃) = 0 := by
    rw [F _ _ _ _ _ hβ₃]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f24 : pairFun p (σ (σ p)) (β w₄) = 0 := by
    rw [F _ _ _ _ _ hβ₄]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f31 : pairFun d (σ d) (β w₁) = 0 := by
    rw [F _ _ _ _ _ hβ₁]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f32 : pairFun d (σ d) (β w₂) = 0 := by
    rw [F _ _ _ _ _ hβ₂]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f33 : pairFun d (σ d) (β w₃) = 1 := by
    rw [F _ _ _ _ _ hβ₃]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f34 : pairFun d (σ d) (β w₄) = 0 := by
    rw [F _ _ _ _ _ hβ₄]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f41 : pairFun d (σ (σ d)) (β w₁) = 0 := by
    rw [F _ _ _ _ _ hβ₁]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f42 : pairFun d (σ (σ d)) (β w₂) = 0 := by
    rw [F _ _ _ _ _ hβ₂]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f43 : pairFun d (σ (σ d)) (β w₃) = 0 := by
    rw [F _ _ _ _ _ hβ₃]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f44 : pairFun d (σ (σ d)) (β w₄) = 1 := by
    rw [F _ _ _ _ _ hβ₄]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  refine le_finrank_of_dual' (β := β) ![w₁, w₂, w₃, w₄] (fun i => by fin_cases i <;> assumption)
    ![pairFun p (σ p), pairFun p (σ (σ p)), pairFun d (σ d), pairFun d (σ (σ d))] fun i k => ?_
  fin_cases i <;> fin_cases k <;> simp [f11, f12, f13, f14, f21, f22, f23, f24, f31, f32, f33, f34, f41, f42, f43, f44]

end Bounds

variable {G L H₁ : Subgroup (GLV V)} {z : GLV V} {v : V} {m : ℕ}
  {ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))}

theorem Hyp.heartL (h : Hyp G L z v H₁ m ψ) :
    ∃ (ρL : ↥L →* Perm (Fin (m + 6))) (βL : ↥(commSpace L ⊤) →+ altHeart (m + 6)),
      HeartFor L (m + 6) ρL L βL ∧ Function.Injective ρL ∧
      (∀ σ ∈ alternatingGroup (Fin (m + 6)), ∃ l : ↥L, ρL l = σ) ∧
      ∀ a : alternatingGroup (Fin (m + 6)), ρL ⟨jL ψ a, h.jL_mem a⟩ = a := by
  obtain ⟨β, hβ⟩ := h.heartFor
  obtain ⟨ρL, βL, hH, hinj, honto, hcompat⟩ := altSub (k := m + 6) (by omega) hβ ψ.injective
    (fun τ _ => ⟨ψ.symm τ, by simp⟩) h.L_le_H₁ (fun x => by
      have := h.mem_L_iff (ψ x)
      rwa [pe_psi] at this)
  refine ⟨ρL, βL, hH, hinj, honto, fun a => ?_⟩
  have h1 := hcompat ⟨jL ψ a, h.jL_mem a⟩
  have h2 : ψ.toMonoidHom ⟨jL ψ a, h.L_le_H₁ (h.jL_mem a)⟩ =
      iota2 (m + 6) (a : Perm (Fin (m + 6))) := psi_jL a
  exact iota2_injective _ (h1.symm.trans h2)

theorem Hyp.N_invariant (h : Hyp G L z v H₁ m ψ) :
    (∀ x ∈ NN G L, ∀ u ∈ commSpace L ⊤, x u ∈ commSpace L ⊤) ∧
      ∀ x ∈ NN G L, ∀ u ∈ fixedSpace L, x u ∈ fixedSpace L := by
  refine ⟨invariant_commSpace (K := L) (K' := NN G L) (fun k' hk' k hk =>
    (Subgroup.mem_normalizer_iff.1 hk'.2 k).1 hk) (invariant_top _), ?_⟩
  intro x hx u hu l hl
  have hl' : x⁻¹ * l * x ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hx.2) l).1 hl
    rwa [inv_inv] at this
  have h1 : (x⁻¹ * l * x) u = u := hu _ hl'
  have e : l (x u) = x ((x⁻¹ * l * x) u) := by
    show l (x u) = x (x⁻¹ (l (x u)))
    rw [show x (x⁻¹ (l (x u))) = l (x u) from x.apply_symm_apply _]
  rw [e, h1]

theorem Hyp.betaL_equiv (h : Hyp G L z v H₁ m ψ) {ρL : ↥L →* Perm (Fin (m + 6))}
    {βL : ↥(commSpace L ⊤) →+ altHeart (m + 6)} (hH : HeartFor L (m + 6) ρL L βL)
    (hρ : ∀ a, ρL ⟨jL ψ a, h.jL_mem a⟩ = a)
    {θ : ↥(NN G L) →* Perm (Fin (m + 6))}
    (hθ : ∀ (x : ↥(NN G L)) a,
      (x : GLV V) * jL ψ a * (x : GLV V)⁻¹ = jL ψ (CaseIAut.conjA (θ x) a))
    (x : ↥(NN G L)) (w w' : ↥(commSpace L ⊤)) (hw : (w' : V) = (x : GLV V) (w : V))
    (y : evenWeight (m + 6)) (hy : βL w = (y : altHeart (m + 6))) :
    βL w' = (evenWeightPerm (θ x) y : altHeart (m + 6)) := by
  obtain ⟨hinvC, hinvF⟩ := h.N_invariant
  let F : ↥(commSpace L ⊤) →+ ↥(commSpace L ⊤) :=
    { toFun := fun u => ⟨(x : GLV V) u, hinvC x x.2 u u.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ _ _) }
  have hF : ∀ u, ((F u : ↥(commSpace L ⊤)) : V) = (x : GLV V) u := fun _ => rfl
  have hkerF : βL.ker ≤ (βL.comp F).ker := by
    intro u hu
    rw [hH.ker] at hu
    show βL (F u) = 0
    have h1 : F u ∈ βL.ker := by
      rw [hH.ker]
      exact hinvF x x.2 _ hu
    exact h1
  let e := QuotientAddGroup.quotientKerEquivOfSurjective βL hH.surj
  let f : altHeart (m + 6) →+ altHeart (m + 6) :=
    (QuotientAddGroup.lift βL.ker (βL.comp F) hkerF).comp e.symm.toAddMonoidHom
  have hf : ∀ u, f (βL u) = βL (F u) := by
    intro u
    have h1 : e.symm (βL u) = (u : ↥(commSpace L ⊤) ⧸ βL.ker) := by
      rw [AddEquiv.symm_apply_eq]
      rfl
    show QuotientAddGroup.lift βL.ker (βL.comp F) hkerF (e.symm (βL u)) = _
    rw [h1]
    rfl
  have hL : ∀ (a : alternatingGroup (Fin (m + 6))) (u : ↥(commSpace L ⊤)),
      altAct (a : Perm (Fin (m + 6))) (βL u) =
        βL ⟨jL ψ a u, hinvC _ (h.jL_mem_N a) u u.2⟩ := by
    intro a u
    obtain ⟨y', hy'⟩ := QuotientAddGroup.mk_surjective (βL u)
    have h1 := hH.equiv ⟨jL ψ a, h.jL_mem a⟩ u ⟨jL ψ a u, hinvC _ (h.jL_mem_N a) u u.2⟩ rfl y'
      hy'.symm
    rw [hρ] at h1
    rw [h1, ← hy', altAct_mk]
  have htwist : ∀ (a : alternatingGroup (Fin (m + 6))) (u : altHeart (m + 6)),
      f (altAct (a : Perm (Fin (m + 6))) u) =
        altAct ((CaseIAut.conjA (θ x) a : alternatingGroup (Fin (m + 6))) : Perm (Fin (m + 6)))
          (f u) := by
    intro a u
    obtain ⟨u', rfl⟩ := hH.surj u
    rw [hL, hf, hf, hL]
    congr 1
    apply Subtype.ext
    show (x : GLV V) (jL ψ a u') = jL ψ (CaseIAut.conjA (θ x) a) ((x : GLV V) u')
    rw [← hθ x a]
    show (x : GLV V) (jL ψ a u') = (x : GLV V) (jL ψ a ((x : GLV V)⁻¹ ((x : GLV V) u')))
    rw [show (x : GLV V)⁻¹ ((x : GLV V) u') = u' from (x : GLV V).symm_apply_apply _]
  let g : altHeart (m + 6) →+ altHeart (m + 6) := (altAct (θ x)⁻¹).comp f
  have hg : ∀ σ ∈ alternatingGroup (Fin (m + 6)), ∀ u,
      g (altAct σ u) = altAct σ (g u) := by
    intro σ hσ u
    show altAct (θ x)⁻¹ (f (altAct σ u)) = altAct σ (altAct (θ x)⁻¹ (f u))
    have := htwist ⟨σ, hσ⟩ u
    simp only at this
    rw [this, CaseIAut.coe_conjA, ← altAct_mul, ← altAct_mul]
    congr 1
    group
  rcases altHeart_endo_eq_zero_or_id (by omega) g hg with h0 | h1
  · exfalso
    haveI := altHeart_nontrivial (n := m + 6) (by omega)
    obtain ⟨u, hu⟩ := exists_ne (0 : altHeart (m + 6))
    obtain ⟨u', rfl⟩ := hH.surj u
    apply hu
    have h2 : g (βL u') = 0 := by rw [h0]; rfl
    have h3 : f (βL u') = 0 := by
      have := congrArg (altAct (θ x)) h2
      rw [map_zero] at this
      rwa [show altAct (θ x) (g (βL u')) = f (βL u') from altAct_apply_inv _ _] at this
    rw [hf] at h3
    have h4 : F u' ∈ βL.ker := h3
    rw [hH.ker] at h4
    have h5 : (u' : V) ∈ fixedSpace L := by
      have h4' : (x : GLV V) (u' : V) ∈ fixedSpace L := h4
      have := hinvF _ ((NN G L).inv_mem x.2) _ h4'
      rwa [show ((x : GLV V)⁻¹) ((x : GLV V) u') = u' from (x : GLV V).symm_apply_apply _]
        at this
    have h6 : u' ∈ βL.ker := by rw [hH.ker]; exact h5
    exact h6
  · have hfa : ∀ u, f u = altAct (θ x) u := by
      intro u
      have h2 : g u = u := by rw [h1]; rfl
      calc f u = altAct (θ x) (altAct (θ x)⁻¹ (f u)) := (altAct_apply_inv _ _).symm
        _ = altAct (θ x) u := by rw [show altAct (θ x)⁻¹ (f u) = g u from rfl, h2]
    have hw' : w' = F w := Subtype.ext hw
    rw [hw', ← hf, hfa, hy, altAct_mk]

theorem Hyp.four_le_finrank_N (h : Hyp G L z v H₁ m ψ) {θ : ↥(NN G L) →* Perm (Fin (m + 6))}
    (hθ : ∀ (x : ↥(NN G L)) a,
      (x : GLV V) * jL ψ a * (x : GLV V)⁻¹ = jL ψ (CaseIAut.conjA (θ x) a))
    (x : ↥(NN G L)) (h3 : orderOf (θ x) = 3) (hn : ¬ (θ x).IsThreeCycle) :
    4 ≤ Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (x : GLV V)) ⊤) := by
  obtain ⟨ρL, βL, hH, -, -, hρ⟩ := h.heartL
  obtain ⟨hinvC, -⟩ := h.N_invariant
  have hσ1 : θ x ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at h3; exact absurd h3 (by norm_num)
  obtain ⟨p, hp⟩ : ∃ p, θ x p ≠ p := by
    by_contra hc; push Not at hc; exact hσ1 (Perm.ext hc)
  obtain ⟨d, hd, hdp, hdq, hdr⟩ := exists_two_orbits_of_orderOf_eq_three h3 hn hp
  have hpow : θ x ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one _
  exact four_le_finrank_of_act hH.surj (hinvC x x.2)
    (fun w w' hw y hy => h.betaL_equiv hH hρ hθ x w w' hw y hy) hpow hp hd hdp hdq hdr

end CaseIAux

end CFSG.CGT.Foote82
