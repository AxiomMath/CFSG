module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.GroupTheory.Complement
import CFSG.FeitThompson.Local.FixedFreeComplementKernelActsTrivially

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
variable {D K R : Subgroup G}

theorem mem_invariants_comp_subtype_iff_forall_mem
    (ρ : Representation k G V) (B : Subgroup G) (v : V) :
    v ∈ Representation.invariants (ρ.comp B.subtype) ↔ ∀ b ∈ B, ρ b v = v := by
  rw [Representation.mem_invariants]
  exact ⟨fun h b hb => h ⟨b, hb⟩, fun h b => h b b.2⟩

private theorem false_of_rank_le_one {N U W : Submodule k V} (hrank : Module.rank k N ≤ 1)
    (hUW : Disjoint U W) {u w : V} (hu : u ∈ U) (hw : w ∈ W)
    (huN : u ∈ N) (hwN : w ∈ N) (hu0 : u ≠ 0) (hw0 : w ≠ 0) : False := by
  obtain ⟨v₀, hle⟩ := (rank_submodule_le_one_iff' N).1 hrank
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hle huN)
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 (hle hwN)
  have ha0 : a ≠ 0 := by rintro rfl; exact hu0 (by simpa using ha.symm)
  have hv₀ : v₀ ∈ U := by
    have : a⁻¹ • u ∈ U := U.smul_mem _ hu
    rwa [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul] at this
  exact hw0 (Submodule.disjoint_def.1 hUW w (hb ▸ U.smul_mem b hv₀) hw)

private theorem natCast_ne_zero_of_dvd {m : ℕ} (hchar : ringChar k = 0 ∨ ¬ ringChar k ∣ m)
    {n : ℕ} (hn : n ∣ m) (hn0 : n ≠ 0) : (n : k) ≠ 0 := by
  intro hc
  have hd := ringChar.dvd (R := k) hc
  rcases hchar with h | h
  · rw [h, zero_dvd_iff] at hd; exact hn0 hd
  · exact h (hd.trans hn)

private theorem centralizer_inf_subgroupOf (hC : ∀ x ∈ R, x ≠ 1 →
    D ⊓ Subgroup.centralizer {x} = ⊥) (x : (D ⊔ R : Subgroup G))
    (hx : x ∈ R.subgroupOf (D ⊔ R)) (hx1 : x ≠ 1) :
    D.subgroupOf (D ⊔ R) ⊓ Subgroup.centralizer {x} = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hcomm : (x : G) * (y : G) = (y : G) * (x : G) :=
    congrArg Subtype.val (hy.2 x (Set.mem_singleton x))
  have hmem : (y : G) ∈ D ⊓ Subgroup.centralizer {(x : G)} :=
    ⟨hy.1, by simpa [Subgroup.mem_centralizer_iff] using hcomm⟩
  rw [hC (x : G) (Subgroup.mem_subgroupOf.1 hx)
    (by simpa using fun h => hx1 (Subtype.ext h))] at hmem
  simpa [Subgroup.mem_bot] using Subtype.ext (by simpa using hmem : (y : G) = 1)

private theorem isComplement'_subgroupOf_sup_of_le_normalizer (hR : R ≤ Subgroup.normalizer D)
    (hDR : D ⊓ R = ⊥) :
    Subgroup.IsComplement' (D.subgroupOf (D ⊔ R)) (R.subgroupOf (D ⊔ R)) := by
  have hnorm : (D.subgroupOf (D ⊔ R)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hR)
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff, eq_bot_iff]
    intro x hx
    have h1 : (x : G) ∈ D ⊓ R := ⟨hx.1, hx.2⟩
    rw [hDR] at h1
    simpa [Subgroup.mem_bot] using Subtype.ext (by simpa using h1 : (x : G) = 1)
  · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
      Subgroup.subgroupOf_self]
    simp

variable [Finite G]

theorem forall_apply_eq_self_of_forall_eq_zero (hR : R ≤ Subgroup.normalizer D)
    (hDR : D ⊓ R = ⊥) (hC : ∀ x ∈ R, x ≠ 1 → D ⊓ Subgroup.centralizer {x} = ⊥)
    (hk : (Nat.card D : k) ≠ 0) (ρ : Representation k G V) {U : Submodule k V}
    (hUinv : ∀ g ∈ D ⊔ R, ∀ u ∈ U, ρ g u ∈ U)
    (h0 : ∀ u ∈ U, (∀ r ∈ R, ρ r u = u) → u = 0) :
    ∀ x ∈ D, ∀ u ∈ U, ρ x u = u := by
  set A : Subgroup G := D ⊔ R with hA
  set σ : Representation k A V := ρ.comp A.subtype with hσ
  have hcomap : ∀ g : A, U ≤ U.comap (σ g) := fun g u hu => hUinv (g : G) g.2 u hu
  set ρ' : Representation k A U := σ.subrepresentation U hcomap with hρ'
  have hbot : Representation.invariants (ρ'.comp (R.subgroupOf A).subtype) = ⊥ := by
    rw [invariants_comp_subtype_eq_bot_iff]
    intro v hv
    refine Subtype.ext (h0 v v.2 fun r hr => ?_)
    have := hv ⟨r, (le_sup_right : R ≤ A) hr⟩ (Subgroup.mem_subgroupOf.2 hr)
    rw [hρ', Representation.subrepresentation_apply] at this
    exact congrArg Subtype.val this
  intro x hx u hu
  have hcard : Nat.card (D.subgroupOf A) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : D ≤ A)).toEquiv
  have key := eq_one_of_invariants_comp_subtype_eq_bot
    (Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hR))
    (isComplement'_subgroupOf_sup_of_le_normalizer hR hDR)
    (fun y hy hy1 => centralizer_inf_subgroupOf hC y hy hy1)
    (by rw [hcard]; exact hk) ρ' hbot
    (Subgroup.mem_subgroupOf.2 hx : (⟨x, (le_sup_left : D ≤ A) hx⟩ : A) ∈ D.subgroupOf A)
  have h2 := congrArg (fun f => (f (⟨u, hu⟩ : U) : V)) key
  rw [hρ'] at h2
  simp only [Representation.subrepresentation_apply, LinearMap.restrict_apply,
    Module.End.one_apply, hσ, MonoidHom.comp_apply, Subgroup.coe_subtype] at h2
  exact h2

theorem exists_ne_zero_mem_invariants (hR : R ≤ Subgroup.normalizer D)
    (hDR : D ⊓ R = ⊥) (hC : ∀ x ∈ R, x ≠ 1 → D ⊓ Subgroup.centralizer {x} = ⊥)
    (hk : (Nat.card D : k) ≠ 0) (ρ : Representation k G V) {U : Submodule k V}
    (hUinv : ∀ g ∈ D ⊔ R, ∀ u ∈ U, ρ g u ∈ U)
    (hnt : ∃ x ∈ D, ∃ u ∈ U, ρ x u ≠ u) :
    ∃ u ∈ U, u ≠ 0 ∧ u ∈ Representation.invariants (ρ.comp R.subtype) := by
  by_contra hcon
  obtain ⟨x, hx, u, hu, hne⟩ := hnt
  refine hne (forall_apply_eq_self_of_forall_eq_zero hR hDR hC hk ρ hUinv ?_ x hx u hu)
  intro v hv hfix
  by_contra hv0
  exact hcon ⟨v, hv, hv0, (mem_invariants_comp_subtype_iff_forall_mem ρ R v).2 hfix⟩

theorem forall_apply_eq_self_of_disjoint_of_rank_invariants_le_one
    (hR : R ≤ Subgroup.normalizer D) (hDR : D ⊓ R = ⊥)
    (hC : ∀ x ∈ R, x ≠ 1 → D ⊓ Subgroup.centralizer {x} = ⊥)
    (hk : (Nat.card D : k) ≠ 0) (ρ : Representation k G V)
    (hrank : Module.rank k (Representation.invariants (ρ.comp R.subtype)) ≤ 1)
    {U W : Submodule k V} (hUW : Disjoint U W)
    (hUinv : ∀ g ∈ D ⊔ R, ∀ u ∈ U, ρ g u ∈ U)
    (hWinv : ∀ g ∈ D ⊔ R, ∀ w ∈ W, ρ g w ∈ W)
    (hnt : ∃ x ∈ D, ∃ u ∈ U, ρ x u ≠ u) :
    ∀ x ∈ D, ∀ w ∈ W, ρ x w = w := by
  obtain ⟨u, hu, hu0, huN⟩ := exists_ne_zero_mem_invariants hR hDR hC hk ρ hUinv hnt
  refine forall_apply_eq_self_of_forall_eq_zero hR hDR hC hk ρ hWinv ?_
  intro w hw hfix
  by_contra hw0
  exact false_of_rank_le_one hrank hUW hu hw huN
    ((mem_invariants_comp_subtype_iff_forall_mem ρ R w).2 hfix) hu0 hw0

theorem forall_apply_eq_self_of_isCompl_of_finrank_invariants_le_one [FiniteDimensional k V]
    (hK : K.Normal) (hKR : Subgroup.IsComplement' K R)
    (hC : ∀ x ∈ R, x ≠ 1 → K ⊓ Subgroup.centralizer {x} = ⊥)
    (hchar : ringChar k = 0 ∨ ¬ ringChar k ∣ Nat.card K)
    (ρ : G →* LinearMap.GeneralLinearGroup k V)
    (hfinrank : Module.finrank k
      (Representation.invariants (((Units.coeHom (V →ₗ[k] V)).comp ρ).comp R.subtype)) ≤ 1)
    {U W : Submodule k V} (hUW : IsCompl U W)
    (hUinv : ∀ g : G, ∀ u ∈ U, (ρ g : V →ₗ[k] V) u ∈ U)
    (hWinv : ∀ g : G, ∀ w ∈ W, (ρ g : V →ₗ[k] V) w ∈ W)
    (hnt : ∃ x ∈ K, ∃ u ∈ U, (ρ x : V →ₗ[k] V) u ≠ u) :
    ∀ x ∈ K, ∀ w ∈ W, (ρ x : V →ₗ[k] V) w = w := by
  have hDR : K ⊓ R = ⊥ := by
    have h := hKR.disjoint
    rw [disjoint_iff] at h
    exact h
  refine forall_apply_eq_self_of_disjoint_of_rank_invariants_le_one
    (Subgroup.le_normalizer_iff.2 fun r _ x hx => hK.conj_mem x hx r) hDR hC
    (natCast_ne_zero_of_dvd hchar dvd_rfl Nat.card_pos.ne')
    ((Units.coeHom (V →ₗ[k] V)).comp ρ) ?_ hUW.disjoint
    (fun g _ => hUinv g) (fun g _ => hWinv g) hnt
  exact_mod_cast FiniteDimensional.finrank_le_iff_rank_le.mp hfinrank

theorem forall_apply_eq_self_of_le_of_finrank_invariants_le_one [FiniteDimensional k V]
    (hKR : Subgroup.IsComplement' K R)
    (hC : ∀ x ∈ R, x ≠ 1 → K ⊓ Subgroup.centralizer {x} = ⊥)
    (hchar : ringChar k = 0 ∨ ¬ ringChar k ∣ Nat.card K)
    (hDK : D ≤ K) (hRD : R ≤ Subgroup.normalizer D)
    (ρ : G →* LinearMap.GeneralLinearGroup k V)
    (hfinrank : Module.finrank k
      (Representation.invariants (((Units.coeHom (V →ₗ[k] V)).comp ρ).comp R.subtype)) ≤ 1)
    {U W : Submodule k V} (hUW : IsCompl U W)
    (hUinv : ∀ g ∈ D ⊔ R, ∀ u ∈ U, (ρ g : V →ₗ[k] V) u ∈ U)
    (hWinv : ∀ g ∈ D ⊔ R, ∀ w ∈ W, (ρ g : V →ₗ[k] V) w ∈ W)
    (hnt : ∃ x ∈ D, ∃ u ∈ U, (ρ x : V →ₗ[k] V) u ≠ u) :
    ∀ x ∈ D, ∀ w ∈ W, (ρ x : V →ₗ[k] V) w = w := by
  have hDR : D ⊓ R = ⊥ := by
    have h := hKR.disjoint
    rw [disjoint_iff] at h
    exact le_antisymm ((inf_le_inf_right R hDK).trans h.le) bot_le
  have hCD : ∀ x ∈ R, x ≠ 1 → D ⊓ Subgroup.centralizer {x} = ⊥ := fun x hx hx1 =>
    le_antisymm (((inf_le_inf_right _ hDK).trans (hC x hx hx1).le)) bot_le
  have hk : (Nat.card D : k) ≠ 0 :=
    natCast_ne_zero_of_dvd hchar (Subgroup.card_dvd_of_le hDK) Nat.card_pos.ne'
  refine forall_apply_eq_self_of_disjoint_of_rank_invariants_le_one hRD hDR hCD hk
    ((Units.coeHom (V →ₗ[k] V)).comp ρ) ?_ hUW.disjoint hUinv hWinv hnt
  exact_mod_cast FiniteDimensional.finrank_le_iff_rank_le.mp hfinrank

end CFSG.FeitThompson
