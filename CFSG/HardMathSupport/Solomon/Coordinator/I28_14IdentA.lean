module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_5Section

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Module CFSG.ComponentClassification.OutcomeLocal

section Ident

theorem i28_14_identA_inv_closure {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (C : Submodule (ZMod 2) U) (T : Set (LinearMap.GeneralLinearGroup (ZMod 2) U))
    (hT : ∀ g ∈ T, ∀ w ∈ C, (g : U →ₗ[ZMod 2] U) w ∈ C) :
    ∀ g ∈ Subgroup.closure T, ∀ w ∈ C, (g : U →ₗ[ZMod 2] U) w ∈ C := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact hT g hg
  | one => intro w hw; rwa [i285_one_apply]
  | mul g h _ _ hg hh => intro w hw; rw [i285_mul_apply]; exact hg _ (hh w hw)
  | inv g _ hg =>
    intro w hw
    have hinj : Function.Injective
        (fun x : C => (⟨(g : U →ₗ[ZMod 2] U) x, hg x x.2⟩ : C)) := by
      intro x y hxy
      have h1 := congrArg Subtype.val hxy
      apply Subtype.ext
      have h2 := congrArg ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U) h1
      simpa only [i285_inv_apply_apply] using h2
    obtain ⟨x, hx⟩ := Finite.surjective_of_injective hinj ⟨w, hw⟩
    have h1 := congrArg Subtype.val hx
    have h2 := congrArg ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U) h1
    simp only [i285_inv_apply_apply] at h2
    rw [← h2]
    exact x.2

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

theorem i28_14_identA_D_mem (S : i285_Setup M) {r : ℕ}
    {W : Fin (r + 1) → Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) M)}
    (hW : i285_Decomp S.X S.τ r W) {d : LinearMap.GeneralLinearGroup (ZMod 2) M}
    (hd : d ∈ S.D) : ∃ j, d ∈ W j := by
  obtain ⟨g, hg, rfl⟩ := hd
  obtain ⟨j, hj⟩ := hW.2.2.2.2.2.1 g hg 0
  refine ⟨j, ?_⟩
  rw [← hj]
  exact ⟨S.τ, hW.2.2.2.2.2.2.1, by simp⟩

theorem i28_14_identA_centre_fixed {U : Type} [AddCommGroup U] [Module (ZMod 2) U]
    {g : LinearMap.GeneralLinearGroup (ZMod 2) U} {φ : Module.Dual (ZMod 2) U} {c : U}
    (h : φ c = 0) (hφ : φ ≠ 0) (hc : c ≠ 0) (hcomm : g * tv φ c h = tv φ c h * g) :
    (g : U →ₗ[ZMod 2] U) c = c := by
  obtain ⟨v, hv⟩ := exists_apply_eq_one hφ
  have h1 := congrArg (fun x : LinearMap.GeneralLinearGroup (ZMod 2) U =>
    (x : U →ₗ[ZMod 2] U) v) hcomm
  simp only [i285_mul_apply, tv_apply, hv, one_smul, map_add] at h1
  have h2 : (g : U →ₗ[ZMod 2] U) c = φ ((g : U →ₗ[ZMod 2] U) v) • c := by
    have := h1
    rw [add_right_inj] at this
    exact this
  rcases zmod2_eq_zero_or_one (φ ((g : U →ₗ[ZMod 2] U) v)) with h0 | h0
  · exfalso
    rw [h0, zero_smul] at h2
    apply hc
    have := congrArg ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U) h2
    rwa [i285_inv_apply_apply, map_zero] at this
  · rw [h2, h0, one_smul]

theorem i28_14_identA_comm (S : i285_Setup M) {r : ℕ}
    {W : Fin (r + 1) → Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) M)}
    (hW : i285_Decomp S.X S.τ r W) {j : Fin (r + 1)}
    {e : LinearMap.GeneralLinearGroup (ZMod 2) M} (he : e ∈ S.D) (hej : e ∉ W j)
    {a : LinearMap.GeneralLinearGroup (ZMod 2) M} (ha : a ∈ W j) : a * e = e * a := by
  obtain ⟨k, hk⟩ := i28_14_identA_D_mem S hW he
  have hkj : k ≠ j := fun h => hej (h ▸ hk)
  have := hW.2.2.1 k j hkj hk
  rw [Subgroup.mem_centralizer_iff] at this
  exact this a ha

theorem i285_T_subset_factor [Finite M] (S : i285_Setup M) {r : ℕ}
    {W : Fin (r + 1) → Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) M)}
    (hW : i285_Decomp S.X S.τ r W) {R : Submodule (ZMod 2) M} (hR : S.IsMin R) :
    ∃ j, S.T R ⊆ (W j : Set (LinearMap.GeneralLinearGroup (ZMod 2) M)) := by
  by_contra hcon
  push Not at hcon
  have : Finite (↥R ⧸ S.Q.comap R.subtype) :=
    Finite.of_surjective (Submodule.mkQ (S.Q.comap R.subtype)) (Submodule.mkQ_surjective _)
  obtain ⟨d₀, hd₀⟩ := S.T_nonempty hR
  obtain ⟨j, hj⟩ := i28_14_identA_D_mem S hW hd₀.1
  obtain ⟨e₀, he₀, hne₀⟩ := Set.not_subset.1 (hcon j)
  let f : ∀ d, d ∈ S.T R → LinearMap.GeneralLinearGroup (ZMod 2) (↥R ⧸ S.Q.comap R.subtype) :=
    fun d hd => S.ρ hR ⟨d, Subgroup.subset_closure hd⟩
  have fcomm : ∀ a (ha : a ∈ S.T R) e (he : e ∈ S.T R), a * e = e * a →
      f a ha * f e he = f e he * f a ha := by
    intro a ha e he h
    simp only [f, ← map_mul]
    congr 1
    exact Subtype.ext h
  let C : Submodule (ZMod 2) (↥R ⧸ S.Q.comap R.subtype) :=
    { carrier := {u | ∀ a (ha : a ∈ S.T R), a ∈ W j →
        (f a ha : (↥R ⧸ S.Q.comap R.subtype) →ₗ[ZMod 2] (↥R ⧸ S.Q.comap R.subtype)) u = u}
      add_mem' := fun {u v} hu hv a ha haW => by
        rw [map_add, hu a ha haW, hv a ha haW]
      zero_mem' := fun a ha haW => map_zero _
      smul_mem' := fun c u hu a ha haW => by
        rw [map_smul, hu a ha haW] }
  have hmemC : ∀ u, u ∈ C ↔ ∀ a (ha : a ∈ S.T R), a ∈ W j →
      (f a ha : (↥R ⧸ S.Q.comap R.subtype) →ₗ[ZMod 2] (↥R ⧸ S.Q.comap R.subtype)) u = u :=
    fun u => Iff.rfl
  have hgen : ∀ g ∈ (S.ρ hR) '' (Subtype.val ⁻¹' S.T R), ∀ w ∈ C,
      (g : (↥R ⧸ S.Q.comap R.subtype) →ₗ[ZMod 2] (↥R ⧸ S.Q.comap R.subtype)) w ∈ C := by
    rintro _ ⟨x, hx, rfl⟩ w hw
    rw [hmemC] at hw ⊢
    intro a ha haW
    by_cases hxW : (x : LinearMap.GeneralLinearGroup (ZMod 2) M) ∈ W j
    · have := hw _ hx hxW
      change (f _ hx : (↥R ⧸ S.Q.comap R.subtype) →ₗ[ZMod 2] (↥R ⧸ S.Q.comap R.subtype)) w = w
        at this
      have e1 : (S.ρ hR x : (↥R ⧸ S.Q.comap R.subtype) →ₗ[ZMod 2] (↥R ⧸ S.Q.comap R.subtype))
          w = w := this
      rw [e1]
      exact hw a ha haW
    · have hc := fcomm a ha _ hx (i28_14_identA_comm S hW (S.T_subset_D R hx) hxW haW)
      have := congrArg (fun y : LinearMap.GeneralLinearGroup (ZMod 2)
        (↥R ⧸ S.Q.comap R.subtype) =>
          (y : (↥R ⧸ S.Q.comap R.subtype) →ₗ[ZMod 2] (↥R ⧸ S.Q.comap R.subtype)) w) hc
      simp only [i285_mul_apply] at this
      rw [hw a ha haW] at this
      exact this
  have hC : ∀ g ∈ (S.ρ hR).range, ∀ w ∈ C,
      (g : (↥R ⧸ S.Q.comap R.subtype) →ₗ[ZMod 2] (↥R ⧸ S.Q.comap R.subtype)) w ∈ C := by
    rw [S.ρ_range hR]
    exact i28_14_identA_inv_closure C _ hgen
  rcases S.ρ_irred hR C hC with h | h
  · obtain ⟨φ', c, hφc, hφ', hc, heq⟩ := (isF2Transvection_iff _).1 (S.ρ_transvection hR he₀)
    have hcC : c ∈ C := by
      rw [hmemC]
      intro a ha haW
      have hcomm := fcomm a ha e₀ he₀ (i28_14_identA_comm S hW he₀.1 hne₀ haW)
      have e2 : f e₀ he₀ = tv φ' c hφc := heq
      rw [e2] at hcomm
      exact i28_14_identA_centre_fixed hφc hφ' hc hcomm
    rw [h] at hcC
    exact hc ((Submodule.mem_bot _).1 hcC)
  · apply (S.ρ_transvection hR hd₀).1
    have e1 : S.ρ hR ⟨d₀, Subgroup.subset_closure hd₀⟩ = f d₀ hd₀ := rfl
    rw [e1]
    refine tv_ext fun w => ?_
    have hw : w ∈ C := by rw [h]; trivial
    exact (hmemC w).1 hw d₀ hd₀ hj

theorem i28_14_identA_mem_sup_of_comm {G : Type*} [Group G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        have h : b * a' = a' * b := (hc a' ha' b hb).symm
        calc a * b * (a' * b') = a * (b * a') * b' := by simp only [mul_assoc]
          _ = a * (a' * b) * b' := by rw [h]
          _ = (a * a') * (b * b') := by simp only [mul_assoc]
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        rw [mul_inv_rev]
        exact (Commute.inv_inv (hc a ha b hb)).eq.symm }
  exact (sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩) : A ⊔ B ≤ P) hx

theorem i285_factor_eq_closure [Finite M] (S : i285_Setup M) {r : ℕ}
    {W : Fin (r + 1) → Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) M)}
    (hW : i285_Decomp S.X S.τ r W) (j : Fin (r + 1)) :
    W j = Subgroup.closure (S.D ∩ (W j : Set (LinearMap.GeneralLinearGroup (ZMod 2) M))) := by
  refine le_antisymm ?_ ((Subgroup.closure_le _).2 Set.inter_subset_right)
  let K : Fin (r + 1) → Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) M) := fun i =>
    Subgroup.closure (S.D ∩ (W i : Set (LinearMap.GeneralLinearGroup (ZMod 2) M)))
  have hKW : ∀ i, K i ≤ W i := fun i => (Subgroup.closure_le _).2 Set.inter_subset_right
  have hsup : (⨆ i, W i) ≤ ⨆ i, K i := by
    rw [hW.1]
    refine (Subgroup.closure_le _).2 fun d hd => ?_
    obtain ⟨k, hk⟩ := i28_14_identA_D_mem S hW hd
    exact le_iSup K k (Subgroup.subset_closure ⟨hd, hk⟩)
  intro w hw
  have hw1 : w ∈ ⨆ i, K i := hsup (le_iSup W j hw)
  let L : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) M) := ⨆ i : {i // i ≠ j}, K i
  have hle : (⨆ i, K i) ≤ K j ⊔ L := iSup_le fun i => by
    by_cases h : i = j
    · subst h
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup (fun i : {i // i ≠ j} => K i) ⟨i, h⟩)
  have hcomm : ∀ a ∈ K j, ∀ b ∈ L, a * b = b * a := by
    intro a ha b hb
    have hLle : L ≤ Subgroup.centralizer (K j : Set (LinearMap.GeneralLinearGroup (ZMod 2) M)) :=
      iSup_le fun i => (hKW i).trans
        ((hW.2.2.1 i j i.2).trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (hKW j))))
    have := hLle hb
    rw [Subgroup.mem_centralizer_iff] at this
    exact this a ha
  obtain ⟨a, ha, b, hb, hab⟩ := i28_14_identA_mem_sup_of_comm hcomm (hle hw1)
  have hbW : b ∈ W j ⊓ ⨆ i : {i // i ≠ j}, W i :=
    ⟨by
      have : b = a⁻¹ * w := by rw [hab]; simp
      rw [this]
      exact (W j).mul_mem ((W j).inv_mem (hKW j ha)) hw,
     (iSup_mono (fun i : {i // i ≠ j} => hKW i) : L ≤ ⨆ i : {i // i ≠ j}, W i) hb⟩
  rw [hW.2.2.2.1 j, Subgroup.mem_bot] at hbW
  rw [hab, hbW, mul_one]
  exact ha

end Ident

end CFSG.HardMathSupport.Solomon.Coordinator
