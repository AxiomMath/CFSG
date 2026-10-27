module

public import CFSG.LargeExtraspecial.DWInsBW
public import CFSG.LargeExtraspecial.DWInsNative

public noncomputable section

namespace CFSG.LargeExtraspecial.DW.Insp

open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {X : Subgroup (V ≃ₗ[ZMod 2] V)}

open scoped Classical in
@[expose] def Rp (e : X ≃* omegaT) (g : Equiv.Perm (Fin 360)) : ℕ :=
  if h : g ∈ omegaT then rc ((e.symm ⟨g, h⟩ : X) : V ≃ₗ[ZMod 2] V) else 0

omit [FiniteDimensional (ZMod 2) V] in
theorem Rp_coe (e : X ≃* omegaT) (g : omegaT) :
    Rp e (g : Equiv.Perm (Fin 360)) = rc ((e.symm g : X) : V ≃ₗ[ZMod 2] V) := by
  rw [Rp, dite_eq_left g.2]

omit [FiniteDimensional (ZMod 2) V] in
theorem Rp_apply (e : X ≃* omegaT) (x : X) :
    Rp e ((e x : omegaT) : Equiv.Perm (Fin 360)) = rc (x : V ≃ₗ[ZMod 2] V) := by
  rw [Rp_coe, MulEquiv.symm_apply_apply]

omit [FiniteDimensional (ZMod 2) V] in
theorem Rp_conj (e : X ≃* omegaT) {ω g : Equiv.Perm (Fin 360)} (hω : ω ∈ omegaT)
    (hg : g ∈ omegaT) : Rp e (ω * g * ω⁻¹) = Rp e g := by
  have hm := omegaT.mul_mem (omegaT.mul_mem hω hg) (omegaT.inv_mem hω)
  have hx : (⟨ω * g * ω⁻¹, hm⟩ : omegaT) = ⟨ω, hω⟩ * ⟨g, hg⟩ * (⟨ω, hω⟩ : omegaT)⁻¹ := rfl
  rw [Rp, dite_eq_left hm, hx, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, rc_conj, Rp, dite_eq_left hg]

theorem Rp_sq (e : X ≃* omegaT) {g : Equiv.Perm (Fin 360)} (hg : g ∈ omegaT) (h3 : g ^ 3 = 1) :
    Rp e (g ^ 2) = Rp e g := by
  have hm := omegaT.pow_mem hg 2
  have hx : (⟨g ^ 2, hm⟩ : omegaT) = (⟨g, hg⟩ : omegaT) ^ 2 := rfl
  have h3' : ((e.symm ⟨g, hg⟩ : X) : V ≃ₗ[ZMod 2] V) ^ 3 = 1 := by
    have h1 : (⟨g, hg⟩ : omegaT) ^ 3 = 1 := Subtype.ext h3
    rw [← Subgroup.coe_pow, ← map_pow, h1, map_one, Subgroup.coe_one]
  rw [Rp, dite_eq_left hm, hx, map_pow, Subgroup.coe_pow, rc_sq h3', Rp, dite_eq_left hg]

theorem Rp_pos (e : X ≃* omegaT) {g : Equiv.Perm (Fin 360)} (hg : g ∈ omegaT) (h1 : g ≠ 1) :
    0 < Rp e g := by
  rw [Rp, dite_eq_left hg]
  apply rc_pos
  intro h
  apply h1
  have h' : e.symm ⟨g, hg⟩ = 1 := Subtype.ext h
  have h'' := congrArg e h'
  rw [MulEquiv.apply_symm_apply, map_one] at h''
  exact congrArg Subtype.val h''

@[expose] def TriInv (e : X ≃* omegaT) : Prop :=
  ∀ g ∈ omegaT, Rp e (gen 8 * g * (gen 8)⁻¹) = Rp e g

omit [FiniteDimensional (ZMod 2) V] in
theorem Rp_rho_pow (e : X ≃* omegaT) (hT : TriInv e)
    {g : Equiv.Perm (Fin 360)} (hg : g ∈ omegaT) :
    ∀ k : ℕ, Rp e (gen 8 ^ k * g * (gen 8 ^ k)⁻¹) = Rp e g
  | 0 => by simp
  | k + 1 => by
    have hk : gen 8 ^ k * g * (gen 8 ^ k)⁻¹ ∈ omegaT :=
      (conj_mem_omegaT (autT.pow_mem (gen_mem_autT (by norm_num)) k)).1 hg
    have e1 : gen 8 ^ (k + 1) * g * (gen 8 ^ (k + 1))⁻¹ =
        gen 8 * (gen 8 ^ k * g * (gen 8 ^ k)⁻¹) * (gen 8)⁻¹ := by
      rw [pow_succ']
      group
    rw [e1, hT _ hk, Rp_rho_pow e hT hg k]

@[expose] def rv (e : X ≃* omegaT) (c : ℕ) : ℕ := Rp e (termPerm (repTerms.getD c []))

theorem bwEntries_exp : bwEntries.all (fun ent => ent.2.2.2.2 == 1 || ent.2.2.2.2 == 2) = true := by
  decide

theorem Rp_entry (hN : dw27Check = true) (e : X ≃* omegaT)
    (hT : TriInv e) {ent : List ℕ × ℕ × List ℤ × ℕ × ℕ} (hent : ent ∈ bwEntries) :
    Rp e (termPerm ent.1) = rv e ent.2.2.2.1 := by
  have key := bw_entry hN hent
  have hw : lettersOK 17 ent.2.2.1 = true :=
    List.all_eq_true.1 bwWords_letters _ (List.mem_map.2 ⟨ent, hent, rfl⟩)
  have hs := List.all_eq_true.1 bwEntries_exp ent hent
  obtain ⟨t, k, w, c, s⟩ := ent
  simp only at key hw hs ⊢
  have hω := (omegaPerm_spec hw).2
  have ht := termPerm_mem t
  have hz : gen 8 ^ k * termPerm t * (gen 8 ^ k)⁻¹ ∈ omegaT :=
    (conj_mem_omegaT (autT.pow_mem (gen_mem_autT (by norm_num)) k)).1 ht
  have e1 : termPerm (repTerms.getD c []) ^ s =
      omegaPerm w * (gen 8 ^ k * termPerm t * (gen 8 ^ k)⁻¹) * (omegaPerm w)⁻¹ := by
    calc termPerm (repTerms.getD c []) ^ s =
        termPerm (repTerms.getD c []) ^ s * (omegaPerm w * gen 8 ^ k) *
          (omegaPerm w * gen 8 ^ k)⁻¹ := by group
      _ = omegaPerm w * gen 8 ^ k * termPerm t * (omegaPerm w * gen 8 ^ k)⁻¹ := by rw [key]
      _ = omegaPerm w * (gen 8 ^ k * termPerm t * (gen 8 ^ k)⁻¹) * (omegaPerm w)⁻¹ := by
        group
  have hR : Rp e (termPerm (repTerms.getD c []) ^ s) = Rp e (termPerm t) := by
    rw [e1, Rp_conj e hω hz, Rp_rho_pow e hT ht k]
  rw [rv]
  simp only [Bool.or_eq_true, beq_iff_eq] at hs
  rcases hs with rfl | rfl
  · rw [pow_one] at hR
    exact hR.symm
  · rw [Rp_sq e (termPerm_mem _) (termPerm_cube hN _)] at hR
    exact hR.symm

theorem Rp_lookup (hN : dw27Check = true) (e : X ≃* omegaT)
    (hT : TriInv e) {t : List ℕ} {c : ℕ}
    (h : (bwEntries.any fun ent => ent.1 == t && ent.2.2.2.1 == c) = true) :
    Rp e (termPerm t) = rv e c := by
  obtain ⟨ent, hent, hb⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  rw [← hb.1, ← hb.2]
  exact Rp_entry hN e hT hent

theorem bw_Rp (hN : dw27Check = true) (e : X ≃* omegaT)
    (la lb lc : List ℕ) :
    ∃ k : ℕ, Rp e (termPerm lc) + Rp e (termPerm lc * termPerm la) +
        Rp e (termPerm lc * termPerm la ^ 2) + Rp e (termPerm lc * termPerm lb) +
        Rp e (termPerm lc * termPerm lb ^ 2) + Rp e (termPerm lc * (termPerm la * termPerm lb)) +
        Rp e (termPerm lc * (termPerm la * termPerm lb) ^ 2) +
        Rp e (termPerm lc * (termPerm la * termPerm lb ^ 2)) +
        Rp e (termPerm lc * (termPerm la * termPerm lb ^ 2) ^ 2) =
      2 * (Rp e (termPerm la) + Rp e (termPerm lb) + Rp e (termPerm la * termPerm lb) +
        Rp e (termPerm la * termPerm lb ^ 2)) + 9 * k := by
  let ι : omegaT →* (V ≃ₗ[ZMod 2] V) := X.subtype.comp e.symm.toMonoidHom
  have hcomm : ∀ x y : omegaT, (x : Equiv.Perm (Fin 360)) * y = y * x → ι x * ι y = ι y * ι x :=
    fun x y h => by rw [← map_mul, ← map_mul, show x * y = y * x from Subtype.ext h]
  have hcube : ∀ x : omegaT, (x : Equiv.Perm (Fin 360)) ^ 3 = 1 → ι x ^ 3 = 1 := fun x h => by
    rw [← map_pow, show x ^ 3 = 1 from Subtype.ext h, map_one]
  have hR : ∀ x : omegaT, rc (ι x) = Rp e (x : Equiv.Perm (Fin 360)) := fun x => (Rp_coe e x).symm
  obtain ⟨k, hk⟩ := bw_line (ι ⟨termPerm la, termPerm_mem la⟩) (ι ⟨termPerm lb, termPerm_mem lb⟩)
    (ι ⟨termPerm lc, termPerm_mem lc⟩) (hcomm _ _ (termPerm_comm hN _ _))
    (hcomm _ _ (termPerm_comm hN _ _)) (hcomm _ _ (termPerm_comm hN _ _))
    (hcube _ (termPerm_cube hN _)) (hcube _ (termPerm_cube hN _)) (hcube _ (termPerm_cube hN _))
  refine ⟨k, ?_⟩
  simp only [← map_mul, ← map_pow, hR, Subgroup.coe_mul, Subgroup.coe_pow] at hk
  exact hk

theorem rho_bounds (hN : dw27Check = true) (e : X ≃* omegaT)
    (hT : TriInv e) : 6 ≤ rv e 0 ∧ 6 ≤ rv e 1 := by
  have v : ∀ (t : List ℕ) (c : ℕ),
      (bwEntries.any fun ent => ent.1 == t && ent.2.2.2.1 == c) = true →
        Rp e (termPerm t) = rv e c := fun t c h => Rp_lookup hN e hT h
  obtain ⟨k₁, h₁⟩ := bw_Rp hN e [1] [2, 3] [0]
  obtain ⟨k₂, h₂⟩ := bw_Rp hN e [1] [2] [0]
  obtain ⟨k₃, h₃⟩ := bw_Rp hN e [0, 1, 1] [2] [0]
  simp only [pow_two, ← termPerm_append, List.cons_append, List.nil_append] at h₁ h₂ h₃
  rw [v [0] 0 (by decide), v [0, 1] 1 (by decide), v [0, 1, 1] 1 (by decide),
    v [0, 2, 3] 2 (by decide), v [0, 2, 3, 2, 3] 2 (by decide), v [0, 1, 2, 3] 0 (by decide),
    v [0, 1, 2, 3, 1, 2, 3] 0 (by decide), v [0, 1, 2, 3, 2, 3] 0 (by decide),
    v [0, 1, 2, 3, 2, 3, 1, 2, 3, 2, 3] 0 (by decide), v [1] 0 (by decide),
    v [2, 3] 1 (by decide), v [1, 2, 3] 2 (by decide), v [1, 2, 3, 2, 3] 2 (by decide)] at h₁
  rw [v [0] 0 (by decide), v [0, 1] 1 (by decide), v [0, 1, 1] 1 (by decide),
    v [0, 2] 1 (by decide), v [0, 2, 2] 1 (by decide), v [0, 1, 2] 2 (by decide),
    v [0, 1, 2, 1, 2] 2 (by decide), v [0, 1, 2, 2] 2 (by decide),
    v [0, 1, 2, 2, 1, 2, 2] 2 (by decide), v [1] 0 (by decide), v [2] 0 (by decide),
    v [1, 2] 1 (by decide), v [1, 2, 2] 1 (by decide)] at h₂
  rw [v [0] 0 (by decide), v [0, 0, 1, 1] 1 (by decide), v [0, 0, 1, 1, 0, 1, 1] 0 (by decide),
    v [0, 2] 1 (by decide), v [0, 2, 2] 1 (by decide), v [0, 0, 1, 1, 2] 2 (by decide),
    v [0, 0, 1, 1, 2, 0, 1, 1, 2] 1 (by decide), v [0, 0, 1, 1, 2, 2] 2 (by decide),
    v [0, 0, 1, 1, 2, 2, 0, 1, 1, 2, 2] 1 (by decide), v [0, 1, 1] 1 (by decide),
    v [2] 0 (by decide), v [0, 1, 1, 2] 2 (by decide), v [0, 1, 1, 2, 2] 2 (by decide)] at h₃
  have hpos : 0 < rv e 2 := Rp_pos e (termPerm_mem _) (termPerm_ne_one hN)
  omega

end CFSG.LargeExtraspecial.DW.Insp
