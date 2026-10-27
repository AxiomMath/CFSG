module

public import CFSG.LargeExtraspecial.S111TOrd3
public import CFSG.LargeExtraspecial.S111BDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial.S4

theorem mem_four {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {U : Submodule (ZMod 2) V} (hU : Nat.card U = 4) {a b : V} (ha : a ∈ U) (hb : b ∈ U)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ≠ b) {v : V} (hv : v ∈ U) :
    v = 0 ∨ v = a ∨ v = b ∨ v = a + b := by
  classical
  have hfin : Finite U := Nat.finite_of_card_ne_zero (by rw [hU]; norm_num)
  have hab0 : a + b ≠ 0 := fun h => hab (by
    rw [add_eq_zero_iff_eq_neg] at h
    rw [h, neg_eq_of_add_eq_zero_right (ZModModule.add_self b)])
  have haab : a ≠ a + b := fun h => hb0 (by
    have := congrArg (fun x => x - a) h
    simpa using this.symm)
  have hbab : b ≠ a + b := fun h => ha0 (by
    have := congrArg (fun x => x - b) h
    simpa using this.symm)
  set s : Finset V := {0, a, b, a + b} with hsdef
  have hs : s.card = 4 := by
    rw [hsdef, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hbab]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, haab⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ha0.symm, hb0.symm, hab0.symm⟩
  have hsub : (s : Set V) ⊆ U := by
    intro x hx
    simp only [hsdef, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact U.zero_mem
    · exact ha
    · exact hb
    · exact U.add_mem ha hb
  have heq : (s : Set V) = U := Set.eq_of_subset_of_ncard_le hsub (by
    rw [Set.ncard_coe_finset, hs, ← Nat.card_coe_set_eq]
    exact hU.le) (Set.toFinite _)
  have hvs : v ∈ (s : Set V) := by rw [heq]; exact hv
  simpa only [hsdef, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] using hvs

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

variable (S) in
noncomputable abbrev perp (U : Submodule (ZMod 2) S.Qt) : Submodule (ZMod 2) S.Qt :=
  LinearMap.BilinForm.orthogonal S.q.polarBilin U

theorem mem_perp_iff {U : Submodule (ZMod 2) S.Qt} {v : S.Qt} :
    v ∈ perp S U ↔ ∀ u ∈ U, polar S.q u v = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  rfl

theorem finrank_perp (U : Submodule (ZMod 2) S.Qt) :
    finrank (ZMod 2) (perp S U) = 2 * S.width - finrank (ZMod 2) U := by
  rw [LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate U, S.finrank_Qt_eq_two_mul_width]

variable {g : G} {A : Subgroup G} {h k k' : G}

namespace Pair111

variable (P : Pair111 S g A h k k')
include P

theorem card_clSub (h8 : Nat.card A = 8) : Nat.card (S.clSub A) = 4 := by
  have := P.cfg.inc.card_eq
  omega

theorem card_clSub' (h8 : Nat.card A = 8) :
    Nat.card (S.clSub (A.map (MulAut.conj h).toMonoidHom)) = 4 := by
  have := P.swap.cfg.inc.card_eq
  rw [card_map_conj] at this
  omega

theorem finrank_clSub (h8 : Nat.card A = 8) : finrank (ZMod 2) (S.clSub A) = 2 := by
  have h1 := P.card_clSub h8
  rw [S.card_submodule] at h1
  exact Nat.pow_right_injective le_rfl (h1.trans (by norm_num))

theorem finrank_clSub' (h8 : Nat.card A = 8) :
    finrank (ZMod 2) (S.clSub (A.map (MulAut.conj h).toMonoidHom)) = 2 := by
  have h1 := P.card_clSub' h8
  rw [S.card_submodule] at h1
  exact Nat.pow_right_injective le_rfl (h1.trans (by norm_num))

variable {m : S.M}

theorem mem_A₂ (W : Ord3 S k m) : (m : G) * k * S.z * ((m : G) * k)⁻¹ ∈ A :=
  W.mem_A P.cfg P.mem P.ne

theorem fix_clSub_of_mem_F (W : Ord3 S k m)
    (hc : ∀ n ∈ Ebar S k k' ⊔ Ebar S k' k, n * S.ρ m = S.ρ m * n) (h8 : Nat.card A = 8)
    {f : S.O} (hf : f ∈ Ebar S k' k) {v : S.Qt} (hv : v ∈ S.clSub A) :
    (f : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  have hkQ := P.memQ
  have hfa := fix_of_mem_normalizer P.hy.hyp4 hf.2
  have hfw : f * S.ρ m = S.ρ m * f := hc f (mem_sup_right hf)
  have hfwa : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl (k * S.z * k⁻¹))) = ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k * S.z * k⁻¹)) := by
    rw [← coe_mul_apply, hfw, coe_mul_apply, hfa]
  have haA : S.cl (k * S.z * k⁻¹) ∈ S.clSub A := S.cl_mem_clSub P.mem hkQ
  have hwaA := W.apply_mem_clSub P.cfg P.mem P.ne haA
  have ha0 : S.cl (k * S.z * k⁻¹) ≠ 0 := cl_conj_z_ne_zero S hkQ P.ne
  have hwa0 : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k * S.z * k⁻¹)) ≠ 0 := fun h0 =>
    ha0 ((LinearEquiv.map_eq_zero_iff _).mp h0)
  have hne : S.cl (k * S.z * k⁻¹) ≠
      ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k * S.z * k⁻¹)) := fun e =>
    W.cl_ne P.cfg P.mem P.ne (by rw [← ρ_cl_conj_z S m hkQ]; exact e.symm)
  rcases mem_four (P.card_clSub h8) haA hwaA ha0 hwa0 hne hv with rfl | rfl | rfl | rfl
  · exact map_zero _
  · exact hfa
  · exact hfwa
  · rw [map_add, hfa, hfwa]

theorem fix_clSub'_of_mem_F (W' : Ord3 S k' m)
    (hc : ∀ n ∈ Ebar S k k' ⊔ Ebar S k' k, n * S.ρ m = S.ρ m * n) {f : S.O}
    (hf : f ∈ Ebar S k' k) {v : S.Qt} (hv : v ∈ S.clSub (A.map (MulAut.conj h).toMonoidHom)) :
    (f : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
  W'.apply_eq_of_commute P.swap.cfg P.mem' P.ne' hf.1 (hc f (mem_sup_right hf)) hv

theorem apply_mem_Wt_of_mem_F (W : Ord3 S k m)
    (hc : ∀ n ∈ Ebar S k k' ⊔ Ebar S k' k, n * S.ρ m = S.ρ m * n) (h8 : Nat.card A = 8)
    {f : S.O} (hf : f ∈ Ebar S k' k) {j : G} (hj : j * S.z * j⁻¹ ∈ A)
    (hjz : j * S.z * j⁻¹ ≠ S.z) {v : S.Qt} (hv : v ∈ Wt S j) :
    (f : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Wt S j := by
  have hjQ := P.cfg.inc.le_QG hj
  have hfix := P.fix_clSub_of_mem_F W hc h8 hf (S.cl_mem_clSub hj hjQ)
  obtain ⟨mf, rfl⟩ := MonoidHom.mem_range.mp (S.Lbar_le_Mbar k' hf.1)
  have h1 := apply_mem_Wt mf hv
  rw [ρ_cl_conj_z S mf hjQ] at hfix
  rwa [Wt_eq_of_cl_eq hjQ hjz (conj_mem_QG' S mf.2 hjQ) hfix] at h1

theorem sub_mem_clSub'_of_mem_F (W' : Ord3 S k' m)
    (hc : ∀ n ∈ Ebar S k k' ⊔ Ebar S k' k, n * S.ρ m = S.ρ m * n) {f : S.O}
    (hf : f ∈ Ebar S k' k) {v : S.Qt}
    (hv : v ∈ perp S (S.clSub (A.map (MulAut.conj h).toMonoidHom))) :
    (f : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ S.clSub (A.map (MulAut.conj h).toMonoidHom) :=
  W'.apply_sub_mem_clSub P.swap.cfg P.mem' P.ne' hf.1 (hc f (mem_sup_right hf))
    fun c hc' => by rw [polar_comm]; exact mem_perp_iff.mp hv c hc'

end Pair111

end CFSG.LargeExtraspecial.S11
