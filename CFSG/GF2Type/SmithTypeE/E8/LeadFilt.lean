module

public import CFSG.GF2Type.SmithTypeE.E8.LeadGen
public import CFSG.GF2Type.SmithTypeE.E8.LeadRoots
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassD4

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.GF2Type.SmithTypeE.E8.Lead

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.SeitzReduction CFSG.Timmesfeld.ExceptionalOrders
open scoped commutatorElement

@[expose] def Tset (t : ℤ) : Set Vec7 := {β | IsRoot .E7 β ∧ 0 < height β ∧ t ≤ lw β}

@[expose] def Ge (t : ℤ) : Subgroup (ModGL .E7 (ZMod 2)) := rootSpan .E7 (ZMod 2) (Tset t)

@[expose] def xr (β : Vec7) : ModGL .E7 (ZMod 2) := pinnedX .E7 (ZMod 2) β 1

theorem Tset_pos {t : ℤ} {β : Vec7} (h : β ∈ Tset t) : IsRoot .E7 β ∧ 0 < height β :=
  ⟨h.1, h.2.1⟩

theorem Tset_anti {t t' : ℤ} (h : t ≤ t') : Tset t' ⊆ Tset t :=
  fun _ hβ => ⟨hβ.1, hβ.2.1, h.trans hβ.2.2⟩

theorem Tset_finite (t : ℤ) : (Tset t).Finite :=
  finite_of_forall_isRoot_pos fun _ hβ => Tset_pos hβ

theorem Tset_closed (t : ℤ) :
    ∀ α ∈ Tset t, ∀ β ∈ Tset t, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot .E7 (a • α + b • β) →
      a • α + b • β ∈ Tset t := by
  rintro α ⟨hα, hαp, hαt⟩ β ⟨hβ, hβp, hβt⟩ a b ha hb hr
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hl1 := lw_pos hα hαp
  have hl2 := lw_pos hβ hβp
  refine ⟨hr, ?_, ?_⟩
  · rw [height_nsmul_add_nsmul]
    nlinarith
  · rw [lw_nsmul_add_nsmul]
    nlinarith

theorem Tset_ideal (t : ℤ) :
    ∀ α ∈ Phip, ∀ β ∈ Tset t, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot .E7 (a • α + b • β) →
      a • α + b • β ∈ Tset t := by
  rintro α ⟨hα, hαp⟩ β ⟨hβ, hβp, hβt⟩ a b ha hb hr
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hl1 := lw_pos hα hαp
  have hl2 := lw_pos hβ hβp
  refine ⟨hr, ?_, ?_⟩
  · rw [height_nsmul_add_nsmul]
    nlinarith
  · rw [lw_nsmul_add_nsmul]
    nlinarith

theorem Ge_anti {t t' : ℤ} (h : t ≤ t') : Ge t' ≤ Ge t :=
  iSup₂_le fun β hβ => le_iSup₂_of_le β (Tset_anti h hβ) le_rfl

theorem Ge_le_posUnipotent (t : ℤ) : Ge t ≤ posUnipotent .E7 (ZMod 2) :=
  rootSpan_le_posUnipotent fun _ hβ => Tset_pos hβ

theorem Tset_zero : Tset 0 = Phip := by
  ext β
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, (lw_pos h.1 h.2).le⟩⟩

theorem Ge_zero : Ge 0 = posUnipotent .E7 (ZMod 2) := by
  rw [Ge, Tset_zero]
  rfl

theorem Tset_eq_empty {t : ℤ} (ht : 30000 < t) : Tset t = ∅ := by
  ext β
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hβ, hp, h⟩
  have := lw_le hβ hp
  omega

theorem Ge_eq_bot {t : ℤ} (ht : 30000 < t) : Ge t = ⊥ := by
  rw [Ge, Tset_eq_empty ht]
  simp [rootSpan]

theorem xr_mem_Ge {t : ℤ} {β : Vec7} (hβ : β ∈ Tset t) : xr β ∈ Ge t :=
  le_biSup (rootSubgroup .E7 (ZMod 2)) hβ (Subgroup.subset_closure ⟨1, rfl⟩)

theorem xr_mem_posUnipotent {β : Vec7} (hβ : β ∈ Phip) : xr β ∈ posUnipotent .E7 (ZMod 2) :=
  le_biSup (rootSubgroup .E7 (ZMod 2)) hβ (Subgroup.subset_closure ⟨1, rfl⟩)

theorem Ge_normal (t : ℤ) :
    ((Ge t).subgroupOf (posUnipotent .E7 (ZMod 2))).Normal :=
  (positive_root_ideal_normality .E7 (ZMod 2) (J := Tset t) (S := Phip)
    (fun _ hβ => ⟨hβ.1, hβ.2.1⟩) (fun _ h => h) (Tset_ideal t)).2

theorem posUnipotent_le_normalizer_Ge (t : ℤ) :
    posUnipotent .E7 (ZMod 2) ≤ Subgroup.normalizer (Ge t : Set (ModGL .E7 (ZMod 2))) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Ge_le_posUnipotent t)).1 (Ge_normal t)

theorem card_Ge (t : ℤ) : Nat.card (Ge t) = 2 ^ (Tset t).ncard := by
  have h := card_rootSpan (K := ZMod 2) (τ := .E7) (fun _ hβ => Tset_pos hβ) (Tset_closed t)
  rw [Nat.card_zmod] at h
  exact h

theorem Tset_level {γ : Vec7} (hγ : γ ∈ Phip) : Tset (lw γ) = insert γ (Tset (lw γ + 1)) := by
  ext β
  simp only [Set.mem_insert_iff]
  constructor
  · rintro ⟨hβ, hp, h⟩
    by_cases heq : lw β = lw γ
    · exact Or.inl (lw_injOn hβ hp hγ.1 hγ.2 heq)
    · exact Or.inr ⟨hβ, hp, by omega⟩
  · rintro (rfl | ⟨hβ, hp, h⟩)
    · exact ⟨hγ.1, hγ.2, le_rfl⟩
    · exact ⟨hβ, hp, by omega⟩

theorem not_mem_Tset_succ {γ : Vec7} : γ ∉ Tset (lw γ + 1) := fun h => by
  have := h.2.2
  omega

theorem Tset_level_none {t : ℤ} (h : ∀ β ∈ Phip, lw β ≠ t) : Tset t = Tset (t + 1) := by
  ext β
  constructor
  · rintro ⟨hβ, hp, ht⟩
    have := h β ⟨hβ, hp⟩
    exact ⟨hβ, hp, by omega⟩
  · exact fun hβ => Tset_anti (by omega) hβ

theorem Ge_level {γ : Vec7} (hγ : γ ∈ Phip) :
    Ge (lw γ) = rootSubgroup .E7 (ZMod 2) γ ⊔ Ge (lw γ + 1) := by
  rw [Ge, Ge, Tset_level hγ]
  exact iSup_insert

theorem Ge_level_none {t : ℤ} (h : ∀ β ∈ Phip, lw β ≠ t) : Ge t = Ge (t + 1) := by
  rw [Ge, Ge, Tset_level_none h]

theorem rootSubgroup_le_posUnipotent {β : Vec7} (hβ : β ∈ Phip) :
    rootSubgroup .E7 (ZMod 2) β ≤ posUnipotent .E7 (ZMod 2) :=
  le_biSup (rootSubgroup .E7 (ZMod 2)) hβ

theorem rootSubgroup_cases {β : Vec7} {g : ModGL .E7 (ZMod 2)}
    (hg : g ∈ rootSubgroup .E7 (ZMod 2) β) : g = 1 ∨ g = xr β := by
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hg
  have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hc c with rfl | rfl
  · exact Or.inl (pinnedX_zero _ _ _)
  · exact Or.inr rfl

theorem Ge_decomp {γ : Vec7} (hγ : γ ∈ Phip) :
    ∀ h ∈ Ge (lw γ), h ∈ Ge (lw γ + 1) ∨ ∃ n ∈ Ge (lw γ + 1), h = xr γ * n := by
  intro h hh
  have hle : rootSubgroup .E7 (ZMod 2) γ ≤
      Subgroup.normalizer (Ge (lw γ + 1) : Set (ModGL .E7 (ZMod 2))) :=
    (rootSubgroup_le_posUnipotent hγ).trans (posUnipotent_le_normalizer_Ge _)
  rw [Ge_level hγ, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hh
  obtain ⟨x, hx, n, hn, rfl⟩ := hh
  rcases rootSubgroup_cases hx with rfl | rfl
  · exact Or.inl (by simpa using hn)
  · exact Or.inr ⟨n, hn, rfl⟩

theorem xr_not_mem_Ge_succ {γ : Vec7} (hγ : γ ∈ Phip) : xr γ ∉ Ge (lw γ + 1) := by
  intro hx
  have hle : Ge (lw γ) ≤ Ge (lw γ + 1) := by
    intro h hh
    rcases Ge_decomp hγ h hh with h1 | ⟨n, hn, rfl⟩
    · exact h1
    · exact mul_mem hx hn
  have heq : Ge (lw γ) = Ge (lw γ + 1) := le_antisymm hle (Ge_anti (by omega))
  have h1 : Nat.card (Ge (lw γ)) = Nat.card (Ge (lw γ + 1)) :=
    congrArg (fun H : Subgroup (ModGL .E7 (ZMod 2)) => Nat.card H) heq
  rw [card_Ge, card_Ge, Tset_level hγ,
    Set.ncard_insert_of_notMem not_mem_Tset_succ (Tset_finite _), pow_succ] at h1
  have hpos : 0 < 2 ^ (Tset (lw γ + 1)).ncard := Nat.two_pow_pos _
  omega

theorem Ge_commutator_le (s s' : ℤ) : ⁅Ge s, Ge s'⁆ ≤ Ge (s + s') := by
  have e : ∀ t : ℤ, Ge t = ⨆ α : Tset t, rootSubgroup .E7 (ZMod 2) α := fun t =>
    iSup_subtype' (p := (· ∈ Tset t)) (f := fun β _ => rootSubgroup .E7 (ZMod 2) β)
  rw [e s, e s']
  refine commutator_iSup_iSup_le _ _ (Ge (s + s')) ?_ ?_ ?_
  · rw [← e s]
    exact (Ge_le_posUnipotent s).trans (posUnipotent_le_normalizer_Ge _)
  · rw [← e s']
    exact (Ge_le_posUnipotent s').trans (posUnipotent_le_normalizer_Ge _)
  · rintro ⟨α, hα⟩ ⟨β, hβ⟩
    by_cases hab : α = β
    · subst hab
      rw [Subgroup.commutator_le]
      intro x hx y hy
      rw [commutatorElement_eq_one_iff_mul_comm.2 (rootSubgroup_mul_comm (ZMod 2) hx hy)]
      exact one_mem _
    · refine (commutator_rootSubgroup_le (ZMod 2) hα.1 hβ.1 hα.2.1 hβ.2.1 hab).trans ?_
      refine iSup₂_le fun γ hγ => ?_
      obtain ⟨hγr, a, b, ha, hb, hγe⟩ := hγ
      have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
      have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
      have hl1 := lw_pos hα.1 hα.2.1
      have hl2 := lw_pos hβ.1 hβ.2.1
      have hγT : γ ∈ Tset (s + s') := by
        subst hγe
        refine ⟨hγr, ?_, ?_⟩
        · rw [height_nsmul_add_nsmul]
          nlinarith [hα.2.1, hβ.2.1]
        · rw [lw_nsmul_add_nsmul]
          nlinarith [hα.2.2, hβ.2.2]
      exact le_biSup (rootSubgroup .E7 (ZMod 2)) hγT

instance finite_modGL : Finite (ModGL .E7 (ZMod 2)) := by
  have : Finite (Module.End (ZMod 2) (RootModule .E7 (ZMod 2))) :=
    Module.finite_of_finite (ZMod 2)
  infer_instance

@[expose] def Psi (X : Subgroup (ModGL .E7 (ZMod 2))) : Set Vec7 :=
  {δ | δ ∈ Phip ∧ ∃ a ∈ X, a ∈ Ge (lw δ) ∧ a ∉ Ge (lw δ + 1)}

theorem Psi_subset (X : Subgroup (ModGL .E7 (ZMod 2))) : Psi X ⊆ Phip := fun _ h => h.1

theorem Phip_finite : Phip.Finite := finite_of_forall_isRoot_pos fun _ h => h

theorem Psi_finite (X : Subgroup (ModGL .E7 (ZMod 2))) : (Psi X).Finite :=
  Phip_finite.subset (Psi_subset X)

theorem inf_le_of_not_mem_Psi {X : Subgroup (ModGL .E7 (ZMod 2))} {δ : Vec7} (hδ : δ ∈ Phip)
    (h : δ ∉ Psi X) : X ⊓ Ge (lw δ) ≤ Ge (lw δ + 1) := by
  intro a ha
  obtain ⟨haX, haG⟩ := Subgroup.mem_inf.1 ha
  by_contra hna
  exact h ⟨hδ, a, haX, haG, hna⟩

@[expose] def nPsi (X : Subgroup (ModGL .E7 (ZMod 2))) (t : ℤ) : ℕ :=
  (Psi X ∩ {δ | t ≤ lw δ}).ncard

theorem Psi_inter_none (X : Subgroup (ModGL .E7 (ZMod 2))) {t : ℤ} (h : ∀ β ∈ Phip, lw β ≠ t) :
    Psi X ∩ {δ | t ≤ lw δ} = Psi X ∩ {δ | t + 1 ≤ lw δ} := by
  ext δ
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hδ, ht⟩
    have := h δ (Psi_subset X hδ)
    exact ⟨hδ, by omega⟩
  · rintro ⟨hδ, ht⟩
    exact ⟨hδ, by omega⟩

theorem Psi_inter_of_not_mem (X : Subgroup (ModGL .E7 (ZMod 2))) {γ : Vec7} (hγp : γ ∈ Phip)
    (hγ : γ ∉ Psi X) : Psi X ∩ {δ | lw γ ≤ lw δ} = Psi X ∩ {δ | lw γ + 1 ≤ lw δ} := by
  ext δ
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hδ, ht⟩
    have hne : lw δ ≠ lw γ := fun e =>
      hγ ((lw_injOn (Psi_subset X hδ).1 (Psi_subset X hδ).2 hγp.1 hγp.2 e) ▸ hδ)
    exact ⟨hδ, by omega⟩
  · rintro ⟨hδ, ht⟩
    exact ⟨hδ, by omega⟩

theorem Psi_inter_insert (X : Subgroup (ModGL .E7 (ZMod 2))) {γ : Vec7} (hγp : γ ∈ Phip)
    (hγ : γ ∈ Psi X) :
    Psi X ∩ {δ | lw γ ≤ lw δ} = insert γ (Psi X ∩ {δ | lw γ + 1 ≤ lw δ}) := by
  ext δ
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_insert_iff]
  constructor
  · rintro ⟨hδ, ht⟩
    by_cases e : lw δ = lw γ
    · exact Or.inl (lw_injOn (Psi_subset X hδ).1 (Psi_subset X hδ).2 hγp.1 hγp.2 e)
    · exact Or.inr ⟨hδ, by omega⟩
  · rintro (rfl | ⟨hδ, ht⟩)
    · exact ⟨hγ, le_rfl⟩
    · exact ⟨hδ, by omega⟩

theorem nPsi_succ_of_mem (X : Subgroup (ModGL .E7 (ZMod 2))) {γ : Vec7} (hγp : γ ∈ Phip)
    (hγ : γ ∈ Psi X) : nPsi X (lw γ) = nPsi X (lw γ + 1) + 1 := by
  unfold nPsi
  have hnot : γ ∉ Psi X ∩ {δ | lw γ + 1 ≤ lw δ} := by
    intro h
    have := h.2
    simp only [Set.mem_setOf_eq] at this
    omega
  rw [Psi_inter_insert X hγp hγ,
    Set.ncard_insert_of_notMem hnot ((Psi_finite X).subset Set.inter_subset_left)]

theorem card_inf_Ge_step (X : Subgroup (ModGL .E7 (ZMod 2))) (t : ℤ)
    (ih : Nat.card ↥(X ⊓ Ge (t + 1)) ≤ 2 ^ nPsi X (t + 1)) :
    Nat.card ↥(X ⊓ Ge t) ≤ 2 ^ nPsi X t := by
  by_cases hex : ∃ γ ∈ Phip, lw γ = t
  · obtain ⟨γ, hγ, rfl⟩ := hex
    by_cases hψ : γ ∈ Psi X
    · rw [nPsi_succ_of_mem X hγ hψ, pow_succ]
      calc Nat.card ↥(X ⊓ Ge (lw γ))
          ≤ 2 * Nat.card ↥(X ⊓ Ge (lw γ + 1)) :=
            card_inf_le_two_mul X (Ge (lw γ)) (Ge (lw γ + 1)) (Ge_anti (by omega)) (xr γ)
              (Ge_decomp hγ)
        _ ≤ 2 * 2 ^ nPsi X (lw γ + 1) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ nPsi X (lw γ + 1) * 2 := mul_comm _ _
    · rw [card_inf_eq_of_inf_le X (Ge (lw γ)) (Ge (lw γ + 1)) (Ge_anti (by omega))
        (inf_le_of_not_mem_Psi hγ hψ)]
      unfold nPsi at ih ⊢
      rw [Psi_inter_of_not_mem X hγ hψ]
      exact ih
  · push Not at hex
    rw [Ge_level_none hex]
    unfold nPsi at ih ⊢
    rw [Psi_inter_none X hex]
    exact ih

theorem card_inf_Ge_le (X : Subgroup (ModGL .E7 (ZMod 2))) (t : ℤ) (ht : t ≤ 30001) :
    Nat.card ↥(X ⊓ Ge t) ≤ 2 ^ nPsi X t := by
  refine Int.leInductionDown (m := 30001)
    (motive := fun n _ => Nat.card ↥(X ⊓ Ge n) ≤ 2 ^ nPsi X n) ?_ ?_ t ht
  · rw [Ge_eq_bot (by norm_num), inf_bot_eq, Subgroup.card_bot]
    exact Nat.one_le_two_pow
  · intro n hn ih
    have h := card_inf_Ge_step X (n - 1) (by rwa [show n - 1 + 1 = n by omega])
    exact h

theorem card_le_two_pow_Psi {X : Subgroup (ModGL .E7 (ZMod 2))}
    (hX : X ≤ posUnipotent .E7 (ZMod 2)) : Nat.card X ≤ 2 ^ (Psi X).ncard := by
  have h := card_inf_Ge_le X 0 (by norm_num)
  rw [Ge_zero, inf_eq_left.2 hX] at h
  have hset : Psi X ∩ {δ | 0 ≤ lw δ} = Psi X := by
    ext δ
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_iff_left_iff_imp]
    intro hδ
    exact (lw_pos (Psi_subset X hδ).1 (Psi_subset X hδ).2).le
  unfold nPsi at h
  rwa [hset] at h

theorem le_Ge_of_forall_Psi {X : Subgroup (ModGL .E7 (ZMod 2))}
    (hX : X ≤ posUnipotent .E7 (ZMod 2)) {t₀ : ℤ} (ht₀ : 0 ≤ t₀)
    (hΨ : ∀ δ ∈ Psi X, t₀ ≤ lw δ) : X ≤ Ge t₀ := by
  have key : ∀ t, t ≤ t₀ → X ⊓ Ge t ≤ Ge t₀ := by
    intro t ht
    refine Int.leInductionDown (m := t₀) (motive := fun n _ => X ⊓ Ge n ≤ Ge t₀) ?_ ?_ t ht
    · exact inf_le_right
    · intro n hn ih
      by_cases hex : ∃ γ ∈ Phip, lw γ = n - 1
      · obtain ⟨γ, hγ, hlw⟩ := hex
        have hψ : γ ∉ Psi X := fun h => by
          have := hΨ γ h
          omega
        have h1 := inf_le_of_not_mem_Psi hγ hψ
        rw [hlw, show n - 1 + 1 = n by omega] at h1
        rw [hlw] at *
        intro a ha
        obtain ⟨haX, haG⟩ := Subgroup.mem_inf.1 ha
        exact ih (Subgroup.mem_inf.2 ⟨haX, h1 (Subgroup.mem_inf.2 ⟨haX, haG⟩)⟩)
      · push Not at hex
        rw [Ge_level_none hex, show n - 1 + 1 = n by omega]
        exact ih
  have h0 := key 0 ht₀
  rwa [Ge_zero, inf_eq_left.2 hX] at h0

section Leading

theorem mem_of_mul_mul_eq_one {G : Type*} [Group G] {N : Subgroup G} {P Q x : G} (hP : P ∈ N)
    (hQ : Q ∈ N) (h : P * x * Q = 1) : x ∈ N := by
  have e : x = P⁻¹ * (P * x * Q) * Q⁻¹ := by group
  rw [h, mul_one] at e
  rw [e]
  exact mul_mem (inv_mem hP) (inv_mem hQ)

theorem height_neg' (v : Vec7) : height (-v) = - height v := by
  simp [height, Finset.sum_neg_distrib]

theorem commutator_xr {γ δ : Vec7} (hγ : γ ∈ Phip) (hδ : δ ∈ Phip)
    (hr : IsRoot .E7 (γ + δ)) : ⁅xr γ, xr δ⁆ = xr (γ + δ) := by
  have hτ : (Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8) :=
    Or.inr (Or.inr (Or.inl rfl))
  have hiform : iform γ δ = -1 := by
    by_contra hne1
    have h0 : 0 ≤ iform γ δ := by
      by_cases hgd : γ = δ
      · subst hgd
        rw [classD4_iform_self hτ hγ.1]
        norm_num
      · have hneg : γ ≠ -δ := fun e => by
          have h1 := hγ.2
          have h2 := hδ.2
          rw [e, height_neg'] at h1
          omega
        have h := iform_sq_lt hγ.1 hδ.1 hgd hneg
        rw [classD4_iform_self hτ hγ.1, classD4_iform_self hτ hδ.1] at h
        have h3 : -2 < iform γ δ := by nlinarith
        have h4 : iform γ δ < 2 := by nlinarith
        omega
    exact (classD4_not_isRoot_add hτ hγ.1 hδ.1 h0).1 hr
  obtain ⟨-, hne, hne'⟩ := classD4_isRoot_add hτ hγ.1 hδ.1 hiform
  have h := commutatorElement_pinnedX_of_oddDerivLaced (by decide : (2 : ZMod 2) = 0)
    (oddDerivLacedCheck_of_simplyLaced hτ) hγ.1 hδ.1 hne hne' hr (1 : ZMod 2) 1
  simpa [xr] using h

theorem Psi_no_sum {X : Subgroup (ModGL .E7 (ZMod 2))} (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    {δ δ' : Vec7} (hδ : δ ∈ Psi X) (hδ' : δ' ∈ Psi X) : ¬ IsRoot .E7 (δ + δ') := by
  intro hr
  obtain ⟨hδp, a, haX, haG, haN⟩ := hδ
  obtain ⟨hδp', b, hbX, hbG, hbN⟩ := hδ'
  obtain ⟨a₁, ha₁, rfl⟩ := (Ge_decomp hδp a haG).resolve_left haN
  obtain ⟨b₁, hb₁, rfl⟩ := (Ge_decomp hδp' b hbG).resolve_left hbN
  have hsum : δ + δ' ∈ Phip := by
    refine ⟨hr, ?_⟩
    have h1 := hδp.2
    have h2 := hδp'.2
    simp only [height, Pi.add_apply, Finset.sum_add_distrib] at h1 h2 ⊢
    omega
  have hlw : lw (δ + δ') + 1 = lw δ + lw δ' + 1 := by rw [lw_add]
  have hnot := xr_not_mem_Ge_succ hsum
  rw [hlw] at hnot
  have hnorm : ∀ u ∈ posUnipotent .E7 (ZMod 2), ∀ n ∈ Ge (lw δ + lw δ' + 1),
      u * n * u⁻¹ ∈ Ge (lw δ + lw δ' + 1) := fun u hu n hn =>
    (Subgroup.mem_normalizer_iff.1 (posUnipotent_le_normalizer_Ge _ hu) n).1 hn
  have hxδ : xr δ ∈ posUnipotent .E7 (ZMod 2) := xr_mem_posUnipotent hδp
  have hxδ' : xr δ' ∈ posUnipotent .E7 (ZMod 2) := xr_mem_posUnipotent hδp'
  have hxδG : xr δ ∈ Ge (lw δ) := xr_mem_Ge ⟨hδp.1, hδp.2, le_rfl⟩
  have hxδ'G : xr δ' ∈ Ge (lw δ') := xr_mem_Ge ⟨hδp'.1, hδp'.2, le_rfl⟩
  have hyb : xr δ' * b₁ ∈ Ge (lw δ') := mul_mem hxδ'G (Ge_anti (by omega) hb₁)
  have c1 : ⁅a₁, xr δ' * b₁⁆ ∈ Ge (lw δ + lw δ' + 1) := by
    have := Ge_commutator_le (lw δ + 1) (lw δ') (Subgroup.commutator_mem_commutator ha₁ hyb)
    rwa [show lw δ + 1 + lw δ' = lw δ + lw δ' + 1 by ring] at this
  have c2 : ⁅xr δ, b₁⁆ ∈ Ge (lw δ + lw δ' + 1) := by
    have := Ge_commutator_le (lw δ) (lw δ' + 1) (Subgroup.commutator_mem_commutator hxδG hb₁)
    rwa [show lw δ + (lw δ' + 1) = lw δ + lw δ' + 1 by ring] at this
  have hid : ⁅xr δ * a₁, xr δ' * b₁⁆ = (xr δ * ⁅a₁, xr δ' * b₁⁆ * (xr δ)⁻¹) * ⁅xr δ, xr δ'⁆ *
      (xr δ' * ⁅xr δ, b₁⁆ * (xr δ')⁻¹) := by
    simp only [commutatorElement_def]
    group
  have h1 : ⁅xr δ * a₁, xr δ' * b₁⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (hX _ haX _ hbX)
  rw [hid, commutator_xr hδp hδp' hr] at h1
  have n1 := hnorm _ hxδ _ c1
  have n2 := hnorm _ hxδ' _ c2
  exact hnot (mem_of_mul_mul_eq_one n1 n2 h1)

end Leading

end CFSG.GF2Type.SmithTypeE.E8.Lead
