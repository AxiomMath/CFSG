module

public import CFSG.LargeExtraspecial.DWInsTri
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeAut
public import CFSG.LargeExtraspecial.Types

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

namespace Insp

open Subgroup Module CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {X : Subgroup (V ≃ₗ[ZMod 2] V)}

@[expose] def psi (e : X ≃* omegaT) :
    normalizer (X : Set (V ≃ₗ[ZMod 2] V)) →* autT :=
  autEquiv.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp (normalizerMonoidHom X))

omit [FiniteDimensional (ZMod 2) V] in
theorem psi_spec (e : X ≃* omegaT)
    (n : normalizer (X : Set (V ≃ₗ[ZMod 2] V))) (x : X) :
    ((psi e n : autT) : Equiv.Perm (Fin 360)) * ((e x : omegaT) : Equiv.Perm (Fin 360)) *
        ((psi e n : autT) : Equiv.Perm (Fin 360))⁻¹ =
      ((e (normalizerMonoidHom X n x) : omegaT) : Equiv.Perm (Fin 360)) := by
  rw [← autEquiv_apply]
  simp [psi, MulAut.congr_apply]

omit [FiniteDimensional (ZMod 2) V] in
theorem coe_normalizerMonoidHom (n : normalizer (X : Set (V ≃ₗ[ZMod 2] V))) (x : X) :
    ((normalizerMonoidHom X n x : X) : V ≃ₗ[ZMod 2] V) =
      (n : V ≃ₗ[ZMod 2] V) * x * (n : V ≃ₗ[ZMod 2] V)⁻¹ :=
  rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem triInv_of_conj (hN : dw27Check = true) (e : X ≃* omegaT)
    {b ω : Equiv.Perm (Fin 360)} (hω : ω ∈ omegaT) {m : ℕ} (hm : m = 1 ∨ m = 2)
    (hb : b = ω * gen 8 ^ m) (hconj : ∀ g ∈ omegaT, Rp e (b * g * b⁻¹) = Rp e g) : TriInv e := by
  have hstar : ∀ g ∈ omegaT, Rp e (gen 8 ^ m * g * (gen 8 ^ m)⁻¹) = Rp e g := by
    intro g hg
    have hz : gen 8 ^ m * g * (gen 8 ^ m)⁻¹ ∈ omegaT :=
      (conj_mem_omegaT (autT.pow_mem (gen_mem_autT (by norm_num)) m)).1 hg
    have e1 : b * g * b⁻¹ = ω * (gen 8 ^ m * g * (gen 8 ^ m)⁻¹) * ω⁻¹ := by
      rw [hb]
      group
    rw [← Rp_conj e hω hz, ← e1, hconj g hg]
  intro g hg
  rcases hm with rfl | rfl
  · simpa using hstar g hg
  · have hz : gen 8 ^ 2 * g * (gen 8 ^ 2)⁻¹ ∈ omegaT :=
      (conj_mem_omegaT (autT.pow_mem (gen_mem_autT (by norm_num)) 2)).1 hg
    have h4 : gen 8 ^ 2 * (gen 8 ^ 2 * g * (gen 8 ^ 2)⁻¹) * (gen 8 ^ 2)⁻¹ =
        gen 8 * g * (gen 8)⁻¹ := by
      have h41 : gen 8 ^ 2 * gen 8 ^ 2 = gen 8 := by
        rw [← pow_add, show 2 + 2 = 3 + 1 by rfl, pow_succ, rho_cube hN, one_mul]
      calc gen 8 ^ 2 * (gen 8 ^ 2 * g * (gen 8 ^ 2)⁻¹) * (gen 8 ^ 2)⁻¹ =
          (gen 8 ^ 2 * gen 8 ^ 2) * g * (gen 8 ^ 2 * gen 8 ^ 2)⁻¹ := by group
        _ = gen 8 * g * (gen 8)⁻¹ := by rw [h41]
    rw [← h4, hstar _ hz, hstar g hg]

theorem tau_comm_rep (hN : dw27Check = true) {c : ℕ}
    (hc : c < 2) :
    gen 9 * termPerm (repTerms.getD c []) = termPerm (repTerms.getD c []) * gen 9 := by
  interval_cases c
  · change gen 9 * termPerm [0] = termPerm [0] * gen 9
    rw [termPerm_cons, termPerm_nil, mul_one]
    exact tau_comm_aPerm hN (by norm_num)
  · change gen 9 * termPerm [0, 1] = termPerm [0, 1] * gen 9
    rw [termPerm_cons, termPerm_cons, termPerm_nil, mul_one, ← mul_assoc,
      tau_comm_aPerm hN (i := 0) (by norm_num), mul_assoc, tau_comm_aPerm hN (i := 1) (by norm_num),
      mul_assoc]


theorem inv_step (hN : dw27Check = true) (e : X ≃* omegaT)
    (hT : TriInv e) {d₀ : V ≃ₗ[ZMod 2] V} (hd₀ : d₀ ∈ X) (h1 : d₀ ≠ 1) (h2 : d₀ * d₀ = 1)
    (hr : rc d₀ ≤ 2) : False := by
  set t : omegaT := e ⟨d₀, hd₀⟩ with ht_def
  have ht1 : (t : Equiv.Perm (Fin 360)) ≠ 1 := by
    intro h
    have h' : t = 1 := Subtype.ext h
    rw [ht_def, MulEquiv.map_eq_one_iff] at h'
    exact h1 (congrArg Subtype.val h')
  have ht2 : (t : Equiv.Perm (Fin 360)) ^ 2 = 1 := by
    have : (⟨d₀, hd₀⟩ : X) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, pow_two, h2]; rfl)
    rw [← Subgroup.coe_pow, ht_def, ← map_pow, this, map_one, Subgroup.coe_one]
  have horder : orderOf (t : Equiv.Perm (Fin 360)) = 2 := orderOf_eq_prime ht2 ht1
  obtain ⟨c, hc, i, hi, hct⟩ := exists_conj_mainPerm t.2 horder
  have hcl : (invData.getD i ([], [], 0)).2.2 < 2 := by interval_cases i <;> decide
  obtain ⟨hgu, hxu⟩ := inv_entry hN hi
  have hmem : invData.getD i ([], [], 0) ∈ invData := by
    rw [List.getD_eq_getElem _ _ (by simp [invData]; omega)]
    exact List.getElem_mem _
  have hgO : omegaPerm (invData.getD i ([], [], 0)).1 ∈ omegaT :=
    (omegaPerm_spec (List.all_eq_true.1 invWords_letters _
      (List.mem_append_left _ (List.mem_map.2 ⟨_, hmem, rfl⟩)))).2
  have huO : omegaPerm (invData.getD i ([], [], 0)).2.1 ∈ omegaT :=
    (omegaPerm_spec (List.all_eq_true.1 invWords_letters _
      (List.mem_append_right _ (List.mem_map.2 ⟨_, hmem, rfl⟩)))).2
  generalize omegaPerm (invData.getD i ([], [], 0)).1 = g at hgu hgO
  generalize omegaPerm (invData.getD i ([], [], 0)).2.1 = u at hgu hxu huO
  generalize (invData.getD i ([], [], 0)).2.2 = cl at hgu hcl
  have hrO := termPerm_mem (repTerms.getD cl [])
  generalize hr_def : termPerm (repTerms.getD cl []) = r at hgu hrO
  have hr3 : r ^ 3 = 1 := by rw [← hr_def]; exact termPerm_cube hN _
  have hu_eq : u = g⁻¹ * r * g := by
    calc u = g⁻¹ * (g * u) := by group
      _ = g⁻¹ * r * g := by rw [hgu, mul_assoc]
  have hu3 : u ^ 3 = 1 := by
    have := conj_pow (a := g⁻¹) (b := r) (i := 3)
    rw [inv_inv, hr3, mul_one, inv_mul_cancel] at this
    rw [hu_eq, this]
  have hxux : mainPerm i * u * mainPerm i = u⁻¹ := by
    calc mainPerm i * u * mainPerm i = mainPerm i * u * mainPerm i * (u * u⁻¹) := by group
      _ = (mainPerm i * (u * (mainPerm i * u))) * u⁻¹ := by group
      _ = u⁻¹ := by rw [hxu, one_mul]
  set z := c * u * c⁻¹ with hz_def
  have hz : z ∈ omegaT := (conj_mem_omegaT hc).1 huO
  have hz3 : z ^ 3 = 1 := by rw [hz_def, conj_pow, hu3, mul_one, mul_inv_cancel]
  have htz : (t : Equiv.Perm (Fin 360)) * z * t = z⁻¹ := by
    rw [hct, hz_def]
    calc c * mainPerm i * c⁻¹ * (c * u * c⁻¹) * (c * mainPerm i * c⁻¹) =
        c * (mainPerm i * u * mainPerm i) * c⁻¹ := by group
      _ = (c * u * c⁻¹)⁻¹ := by rw [hxux]; group
  set zX : X := e.symm ⟨z, hz⟩ with hzX
  have hw : e (⟨d₀, hd₀⟩ * (zX * ⟨d₀, hd₀⟩ * zX⁻¹)) = ⟨z, hz⟩ := by
    apply Subtype.ext
    rw [map_mul, map_mul, map_mul, map_inv, hzX, MulEquiv.apply_symm_apply, ← ht_def,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    change (t : Equiv.Perm (Fin 360)) * (z * t * z⁻¹) = z
    calc (t : Equiv.Perm (Fin 360)) * (z * t * z⁻¹) = (t * z * t) * z⁻¹ := by group
      _ = z⁻¹ * z⁻¹ := by rw [htz]
      _ = z := by
        rw [← mul_inv_rev, inv_eq_iff_mul_eq_one, mul_assoc, ← pow_two, ← pow_succ', hz3]
  have hRz : Rp e z = rc (d₀ * ((zX : V ≃ₗ[ZMod 2] V) * d₀ * (zX : V ≃ₗ[ZMod 2] V)⁻¹)) := by
    have h0 := Rp_apply e (⟨d₀, hd₀⟩ * (zX * ⟨d₀, hd₀⟩ * zX⁻¹))
    rw [hw] at h0
    exact h0
  have hle : rc (d₀ * ((zX : V ≃ₗ[ZMod 2] V) * d₀ * (zX : V ≃ₗ[ZMod 2] V)⁻¹)) ≤ 4 :=
    (rc_mul_le _ _).trans (by rw [rc_conj]; omega)
  have hval : Rp e z = rv e cl := by
    obtain ⟨ω', hω', k, -, j, hj, hc_eq⟩ := autT_decomp hN hc
    have hτu : gen 9 ^ j * u * (gen 9 ^ j)⁻¹ ∈ omegaT :=
      (conj_mem_omegaT (autT.pow_mem (gen_mem_autT (by norm_num)) j)).1 huO
    have hρτu : gen 8 ^ k * (gen 9 ^ j * u * (gen 9 ^ j)⁻¹) * (gen 8 ^ k)⁻¹ ∈ omegaT :=
      (conj_mem_omegaT (autT.pow_mem (gen_mem_autT (by norm_num)) k)).1 hτu
    have ez : z = ω' * (gen 8 ^ k * (gen 9 ^ j * u * (gen 9 ^ j)⁻¹) * (gen 8 ^ k)⁻¹) * ω'⁻¹ := by
      rw [hz_def, hc_eq]
      group
    rw [ez, Rp_conj e hω' hρτu, Rp_rho_pow e hT hτu k, rv, hr_def]
    have hconj : ∀ g' ∈ omegaT, Rp e (g'⁻¹ * r * g') = Rp e r := fun g' hg' => by
      have h0 := Rp_conj e (omegaT.inv_mem hg') hrO
      rwa [inv_inv] at h0
    interval_cases j
    · rw [pow_zero, one_mul, inv_one, mul_one, hu_eq]
      exact hconj g hgO
    · have hτr : gen 9 * r * (gen 9)⁻¹ = r := by
        rw [← hr_def, tau_comm_rep hN hcl, mul_inv_cancel_right]
      have hg' : gen 9 * g * (gen 9)⁻¹ ∈ omegaT :=
        (conj_mem_omegaT (gen_mem_autT (by norm_num))).1 hgO
      have e2 : gen 9 ^ 1 * u * (gen 9 ^ 1)⁻¹ =
          (gen 9 * g * (gen 9)⁻¹)⁻¹ * r * (gen 9 * g * (gen 9)⁻¹) := by
        calc gen 9 ^ 1 * u * (gen 9 ^ 1)⁻¹ = gen 9 * (g⁻¹ * r * g) * (gen 9)⁻¹ := by
              rw [pow_one, hu_eq]
          _ = (gen 9 * g * (gen 9)⁻¹)⁻¹ * (gen 9 * r * (gen 9)⁻¹) * (gen 9 * g * (gen 9)⁻¹) := by
              group
          _ = _ := by rw [hτr]
      rw [e2]
      exact hconj _ hg'
  have h6 : 6 ≤ rv e cl := by
    obtain ⟨h0, h1⟩ := rho_bounds hN e hT
    interval_cases cl
    · exact h0
    · exact h1
  omega

end Insp


open Subgroup Module CFSG.Blueprint CFSG.EvenSmallLie.OmegaEight
open CFSG.RankThree.OrthogonalInvolutions Insp

theorem dw2_seven (hN : dw27Check = true) {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {X Y : Subgroup (V ≃ₗ[ZMod 2] V)} (hXY : X ≤ Y)
    (hYN : Y ≤ normalizer (X : Set (V ≃ₗ[ZMod 2] V))) (hX : LieModel X .POmegaPlus 4 2 1)
    {d₀ : V ≃ₗ[ZMod 2] V} (hd₀ : d₀ ∈ X) (h1 : d₀ ≠ 1) (h2 : d₀ * d₀ = 1)
    (hr : finrank (ZMod 2) (commSpace d₀) ≤ 2) :
    ∀ y ∈ Y, ∃ k : ℕ, ∃ x ∈ X, ∃ c ∈ Y, (∀ x' ∈ X, c * x' = x' * c) ∧ y ^ 2 ^ k = x * c := by
  intro y hy
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hX
  set n : normalizer (X : Set (V ≃ₗ[ZMod 2] V)) := ⟨y, hYN hy⟩ with hn
  obtain ⟨ω, hω, m, hm, hsq⟩ := sq_mem_coset hN (psi e n).2
  have hb : ∀ x : X, ((psi e n : autT) : Equiv.Perm (Fin 360)) ^ 2 *
      ((e x : omegaT) : Equiv.Perm (Fin 360)) * (((psi e n : autT) : Equiv.Perm (Fin 360)) ^ 2)⁻¹ =
        ((e (normalizerMonoidHom X (n ^ 2) x) : omegaT) : Equiv.Perm (Fin 360)) := by
    intro x
    have h0 := psi_spec e (n ^ 2) x
    rwa [map_pow, Subgroup.coe_pow] at h0
  have hn2 : ((n ^ 2 : normalizer (X : Set (V ≃ₗ[ZMod 2] V))) : V ≃ₗ[ZMod 2] V) = y ^ 2 := by
    rw [Subgroup.coe_pow, hn]
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | hm12 | hm12
  ·
    rw [pow_zero, mul_one] at hsq
    set x₀ : X := e.symm ⟨ω, hω⟩ with hx₀
    have key : ∀ x' ∈ X, y ^ 2 * x' * (y ^ 2)⁻¹ =
        (x₀ : V ≃ₗ[ZMod 2] V) * x' * (x₀ : V ≃ₗ[ZMod 2] V)⁻¹ := by
      intro x' hx'
      have h0 := hb ⟨x', hx'⟩
      rw [hsq] at h0
      have h3 : e (x₀ * ⟨x', hx'⟩ * x₀⁻¹) = e (normalizerMonoidHom X (n ^ 2) ⟨x', hx'⟩) := by
        apply Subtype.ext
        rw [map_mul, map_mul, map_inv, hx₀, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
          Subgroup.coe_mul, Subgroup.coe_inv]
        exact h0
      have h4 := congrArg (fun z : X => (z : V ≃ₗ[ZMod 2] V)) (e.injective h3)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_normalizerMonoidHom, hn2] at h4
      exact h4.symm
    refine ⟨1, x₀, x₀.2, (x₀ : V ≃ₗ[ZMod 2] V)⁻¹ * y ^ 2,
      Y.mul_mem (Y.inv_mem (hXY x₀.2)) (Y.pow_mem hy 2), ?_, ?_⟩
    · intro x' hx'
      calc (x₀ : V ≃ₗ[ZMod 2] V)⁻¹ * y ^ 2 * x' =
          (x₀ : V ≃ₗ[ZMod 2] V)⁻¹ * (y ^ 2 * x' * (y ^ 2)⁻¹) * y ^ 2 := by group
        _ = (x₀ : V ≃ₗ[ZMod 2] V)⁻¹ * ((x₀ : V ≃ₗ[ZMod 2] V) * x' * (x₀ : V ≃ₗ[ZMod 2] V)⁻¹) *
            y ^ 2 := by rw [key x' hx']
        _ = x' * ((x₀ : V ≃ₗ[ZMod 2] V)⁻¹ * y ^ 2) := by group
    · rw [pow_one]
      group
  all_goals
    exfalso
    have hconj : ∀ g ∈ omegaT, Rp e (((psi e n : autT) : Equiv.Perm (Fin 360)) ^ 2 * g *
        (((psi e n : autT) : Equiv.Perm (Fin 360)) ^ 2)⁻¹) = Rp e g := fun g hg => by
      have h0 := hb (e.symm ⟨g, hg⟩)
      simp only [MulEquiv.apply_symm_apply] at h0
      rw [h0, Rp_apply, coe_normalizerMonoidHom, rc_conj]
      exact (Rp_coe e ⟨g, hg⟩).symm
    exact inv_step hN e (triInv_of_conj hN e hω (by omega) hsq hconj) hd₀ h1 h2 hr

theorem dw2Out_clauseT (hN : dw27Check = true) :
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      (q : QuadraticForm (ZMod 2) V), q.polarBilin.Nondegenerate →
      ∀ X Y : Subgroup (V ≃ₗ[ZMod 2] V), (∀ y ∈ Y, ∀ v, q (y v) = q v) → X ≤ Y →
        Y ≤ normalizer (X : Set (V ≃ₗ[ZMod 2] V)) → LieModel X .POmegaPlus 4 2 1 →
        ∀ D : Set (V ≃ₗ[ZMod 2] V), X = closure D →
          (∃ d₀ ∈ D, ∀ d, d ∈ D ↔ ∃ g ∈ X, d = g * d₀ * g⁻¹) → (∀ d ∈ D, IsTypeA q d 2) →
          ∀ y ∈ Y, ∃ k : ℕ, ∃ x ∈ X, ∃ c ∈ Y, (∀ x' ∈ X, c * x' = x' * c) ∧
            y ^ 2 ^ k = x * c := by
  intro V _ _ _ q _ X Y _ hXY hYN hX D hXD hD0 hDA
  obtain ⟨d₀, hd₀, -⟩ := hD0
  have hd₀X : d₀ ∈ X := by
    rw [hXD]
    exact subset_closure hd₀
  obtain ⟨-, h1, h2, h3, -⟩ := hDA d₀ hd₀
  exact dw2_seven hN hXY hYN hX hd₀X h1 h2 h3.le

end CFSG.LargeExtraspecial.DW
