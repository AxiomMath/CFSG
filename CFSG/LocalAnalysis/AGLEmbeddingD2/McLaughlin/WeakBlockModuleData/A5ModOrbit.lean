module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5ModChain
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

@[expose] public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5Mod

open Matrix Equiv

def tau0 : A5 := ⟨inv15 0, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

def T0 : Subgroup A5 := Subgroup.centralizer {tau0}

theorem card_T0 : Nat.card T0 = 4 := by
  have e : Nat.card T0 = Nat.card {t : A5 // tau0 * t = t * tau0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun t => by
      simp [T0, Subgroup.mem_centralizer_iff, eq_comm])
  rw [e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem isPGroup_T0 : IsPGroup 2 T0 := IsPGroup.of_card (n := 2) (by rw [card_T0]; norm_num)

theorem exists_conj (j : Fin 15) :
    ∃ g : A5, (g : Perm (Fin 5)) * inv15 0 * (g : Perm (Fin 5))⁻¹ = inv15 j := by
  revert j
  decide +kernel

theorem mem_T0_iff (t : A5) :
    t ∈ T0 ↔ (t : Perm (Fin 5)) * inv15 0 * (t : Perm (Fin 5))⁻¹ = inv15 0 := by
  simp only [T0, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  rw [tau0]
  constructor
  · intro h
    have := congrArg Subtype.val h
    simp only [Subgroup.coe_mul] at this
    rw [mul_inv_eq_iff_eq_mul, ← this]
  · intro h
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm

section Orbit

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [DistribMulAction A5 W]
  [SMulCommClass A5 (ZMod 2) W] [Finite W]

theorem add_self_eq_zero' (w : W) : w + w = 0 := by
  rw [← two_smul (ZMod 2) w]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_smul]

theorem exists_fixed_vec [Nontrivial W] : ∃ u : W, u ≠ 0 ∧ ∀ t ∈ T0, t • u = u := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have hmod := isPGroup_T0.card_modEq_card_fixedPoints (α := W)
  have h2 : 2 ∣ Nat.card W := by
    have : addOrderOf w = 2 := by
      refine addOrderOf_eq_prime ?_ hw
      rw [two_nsmul, add_self_eq_zero']
    rw [← this]
    exact addOrderOf_dvd_natCard w
  have h2' : 2 ∣ Nat.card (MulAction.fixedPoints T0 W) := (hmod.dvd_iff dvd_rfl).mp h2
  by_contra hcon0
  have hcon : ∀ u : W, (∀ t ∈ T0, t • u = u) → u = 0 := fun u hu => by
    by_contra hne
    exact hcon0 ⟨u, hne, hu⟩
  have hF : Nat.card (MulAction.fixedPoints T0 W) = 1 := by
    haveI : Nonempty (MulAction.fixedPoints T0 W) :=
      ⟨⟨0, by rw [MulAction.mem_fixedPoints]; intro m; exact smul_zero m⟩⟩
    haveI : Subsingleton (MulAction.fixedPoints T0 W) := ⟨fun a b => by
      apply Subtype.ext
      have ha := hcon a.1 (fun t ht => by
        have := a.2
        rw [MulAction.mem_fixedPoints] at this
        exact this ⟨t, ht⟩)
      have hb := hcon b.1 (fun t ht => by
        have := b.2
        rw [MulAction.mem_fixedPoints] at this
        exact this ⟨t, ht⟩)
      exact ha.trans hb.symm⟩
    exact Nat.card_unique
  rw [hF] at h2'
  omega

theorem exists_orbit_family (hs : IsSimpleMod W) [Nontrivial W] :
    ∃ w : Fin 15 → W, (∀ g j, g • w j = w (perm g j)) ∧
      Submodule.span (ZMod 2) (Set.range w) = ⊤ := by
  obtain ⟨u, hu0, hu⟩ := exists_fixed_vec (W := W)
  choose gj hgj using exists_conj
  have key : ∀ (g : A5) (j : Fin 15), g • gj j • u = gj (perm g j) • u := by
    intro g j
    set p := perm g j with hp
    have ht : (gj p)⁻¹ * g * gj j ∈ T0 := by
      rw [mem_T0_iff]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have h1 := hgj j
      have h2 : inv15 p = (g : Perm (Fin 5)) * inv15 j * (g : Perm (Fin 5))⁻¹ := perm_spec g j
      have h3 := hgj p
      calc ((gj p : Perm (Fin 5))⁻¹ * (g : Perm (Fin 5)) * (gj j : Perm (Fin 5))) * inv15 0 *
            ((gj p : Perm (Fin 5))⁻¹ * (g : Perm (Fin 5)) * (gj j : Perm (Fin 5)))⁻¹
          = (gj p : Perm (Fin 5))⁻¹ * ((g : Perm (Fin 5)) *
              ((gj j : Perm (Fin 5)) * inv15 0 * (gj j : Perm (Fin 5))⁻¹) *
              (g : Perm (Fin 5))⁻¹) * (gj p : Perm (Fin 5)) := by group
        _ = (gj p : Perm (Fin 5))⁻¹ * ((g : Perm (Fin 5)) * inv15 j * (g : Perm (Fin 5))⁻¹) *
              (gj p : Perm (Fin 5)) := by rw [h1]
        _ = (gj p : Perm (Fin 5))⁻¹ * ((gj p : Perm (Fin 5)) * inv15 0 *
              (gj p : Perm (Fin 5))⁻¹) * (gj p : Perm (Fin 5)) := by rw [← h2, h3]
        _ = inv15 0 := by group
    have h := hu _ ht
    calc g • gj j • u = (g * gj j) • u := (mul_smul _ _ _).symm
      _ = (gj p * ((gj p)⁻¹ * g * gj j)) • u := by group
      _ = gj p • (((gj p)⁻¹ * g * gj j) • u) := mul_smul _ _ _
      _ = gj p • u := by rw [h]
  refine ⟨fun j => gj j • u, key, ?_⟩
  have hinv : ∀ g : A5, ∀ w ∈ Submodule.span (ZMod 2) (Set.range fun j => gj j • u),
      g • w ∈ Submodule.span (ZMod 2) (Set.range fun j => gj j • u) := by
    intro g w hw
    induction hw using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      rw [key]
      exact Submodule.subset_span ⟨perm g j, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ _ ha
  refine (hs _ hinv).resolve_left fun hbot => ?_
  have hmem : gj 0 • u ∈ Submodule.span (ZMod 2) (Set.range fun j => gj j • u) :=
    Submodule.subset_span ⟨0, rfl⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact hu0 (by simpa using congrArg (fun x => (gj 0)⁻¹ • x) hmem)

theorem S_mul_Mt (g : A5) : S * Mt g = Pm g * S := by
  have h1 : ∀ i m, ∑ l, S i l * Sinv l m = if i = m then 1 else 0 := fun i m => by
    have := congrFun (congrFun S_mul_Sinv i) m
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  ext i k
  simp only [Matrix.mul_apply, Mt, Pm]
  calc ∑ l, S i l * ∑ j, Sinv l (perm g j) * S j k
      = ∑ j, (∑ l, S i l * Sinv l (perm g j)) * S j k := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        ring
    _ = ∑ j, (if i = perm g j then 1 else 0) * S j k := by simp_rw [h1]

theorem exists_y (hs : IsSimpleMod W) [Nontrivial W] :
    ∃ y : Fin 15 → W, (∀ g k, g • y k = ∑ l, Mt g l k • y l) ∧
      Submodule.span (ZMod 2) (Set.range y) = ⊤ := by
  classical
  obtain ⟨w, hw, hspan⟩ := exists_orbit_family hs
  refine ⟨fun k => ∑ j, S j k • w j, ?_, ?_⟩
  · intro g k
    have e1 : g • ∑ j, S j k • w j = ∑ j, S j k • w (perm g j) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_comm, hw]
    have e2 : ∑ l, Mt g l k • ∑ i, S i l • w i = ∑ i, ((S * Mt g) i k) • w i := by
      simp_rw [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
      rw [mul_comm]
    have e3 : ∑ i, ((Pm g * S) i k) • w i = ∑ j, S j k • w (perm g j) := by
      simp only [Matrix.mul_apply, Pm, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [ite_smul, Finset.sum_ite_eq]
    rw [e1, e2, S_mul_Mt, e3]
  · rw [eq_top_iff, ← hspan]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, rfl⟩
    have : w m = ∑ k, Sinv k m • ∑ j, S j k • w j := by
      simp_rw [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      have h1 : ∀ j, ∑ k, Sinv k m * S j k = if j = m then 1 else 0 := fun j => by
        have := congrFun (congrFun S_mul_Sinv j) m
        simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm] using this
      simp_rw [← Finset.sum_smul, h1]
      simp
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end Orbit

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5Mod
