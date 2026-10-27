module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011Gen

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {A : Type} [Group A] [Finite A] {B : Subgroup A} {t : A} {K : Subgroup (MulAut A)}
  {φ : (Fin 5 → ZMod 2) → A}

structure Sec1011A2 (B : Subgroup A) (t : A) (K : Subgroup (MulAut A))
    (φ : (Fin 5 → ZMod 2) → A) : Prop where
  core : Sec1011Core B t K φ
  six : sec1011_orb K t =
    {a | a = t ∨ ∃ v, IsEvenVec v ∧ vecWeight v = 4 ∧ a = t * φ v}
  iso : Nonempty (↥(K ⊓ MulAction.stabilizer (MulAut A) t) ≃* ↥(alternatingGroup (Fin 5))) ∨
    Nonempty (↥(K ⊓ MulAction.stabilizer (MulAut A) t) ≃* Equiv.Perm (Fin 5))

@[expose] def sec1011_delta (t : A) (φ : (Fin 5 → ZMod 2) → A) : Fin 6 → A :=
  Fin.cons t (fun i => t * φ (sec1011_wfour i))

theorem sec1011_delta_zero (t : A) (φ : (Fin 5 → ZMod 2) → A) : sec1011_delta t φ 0 = t := by
  simp [sec1011_delta]

theorem sec1011_delta_succ (t : A) (φ : (Fin 5 → ZMod 2) → A) (i : Fin 5) :
    sec1011_delta t φ i.succ = t * φ (sec1011_wfour i) := by
  simp [sec1011_delta]

private lemma sec1011A_wfour_ne_zero (i : Fin 5) : sec1011_wfour i ≠ 0 := by
  intro h0
  have hw := sec1011_wfour_weight i
  rw [h0] at hw
  simpa [vecWeight] using hw

theorem Sec1011A2.delta_injective (h : Sec1011A2 B t K φ) :
    Function.Injective (sec1011_delta t φ) := by
  intro k l hkl
  cases k using Fin.cases with
  | zero =>
      cases l using Fin.cases with
      | zero => rfl
      | succ j =>
          exfalso
          have h1 : t = t * φ (sec1011_wfour j) := by simpa [sec1011_delta] using hkl
          exact (h.core.ne_one (sec1011_wfour_even j) (sec1011A_wfour_ne_zero j))
            (mul_eq_left.mp h1.symm)
  | succ i =>
      cases l using Fin.cases with
      | zero =>
          exfalso
          have h1 : t * φ (sec1011_wfour i) = t := by simpa [sec1011_delta] using hkl
          exact (h.core.ne_one (sec1011_wfour_even i) (sec1011A_wfour_ne_zero i))
            (mul_eq_left.mp h1)
      | succ j =>
          have h1 : t * φ (sec1011_wfour i) = t * φ (sec1011_wfour j) := by
            simpa [sec1011_delta] using hkl
          have h2 : φ (sec1011_wfour i) = φ (sec1011_wfour j) := mul_left_cancel h1
          have h3 : sec1011_wfour i = sec1011_wfour j :=
            h.core.inj _ _ (sec1011_wfour_even i) (sec1011_wfour_even j) h2
          exact congrArg Fin.succ (sec1011_wfour_injective h3)

theorem Sec1011A2.delta_range (h : Sec1011A2 B t K φ) :
    Set.range (sec1011_delta t φ) = sec1011_orb K t := by
  have hrange : Set.range (sec1011_delta t φ) =
      {a : A | a = t ∨ ∃ v, IsEvenVec v ∧ vecWeight v = 4 ∧ a = t * φ v} := by
    ext a
    constructor
    · rintro ⟨k, rfl⟩
      cases k using Fin.cases with
      | zero => left; simp [sec1011_delta]
      | succ i =>
          right
          exact ⟨sec1011_wfour i, sec1011_wfour_even i, sec1011_wfour_weight i,
            by simp [sec1011_delta]⟩
    · rintro (rfl | ⟨v, hv, hw, rfl⟩)
      · exact ⟨0, by simp [sec1011_delta]⟩
      · obtain ⟨i, rfl⟩ := sec1011_exists_wfour v hw
        exact ⟨i.succ, by simp [sec1011_delta]⟩
  rw [hrange, h.six]

private lemma sec1011A_card_orbit_mul_card_stabilizer {G α : Type} [Group G] [MulAction G α]
    (b : α) : Nat.card (MulAction.orbit G b) * Nat.card (MulAction.stabilizer G b) =
      Nat.card G := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G b)

theorem Sec1011A2.card_K (h : Sec1011A2 B t K φ) :
    Nat.card ↥K = 6 * Nat.card ↥(K ⊓ MulAction.stabilizer (MulAut A) t) := by
  have horb_eq : (MulAction.orbit ↥K t : Set A) = sec1011_orb K t := by
    ext a
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨(m : MulAut A), m.2, hm.symm⟩
    · rintro ⟨α, hα, ha⟩
      exact ⟨⟨α, hα⟩, ha.symm⟩
  have horb : Nat.card (MulAction.orbit ↥K t) = 6 := by
    rw [horb_eq, Nat.card_coe_set_eq]
    exact sec1011_core_ncard_six h.core h.six
  have hstab_eq : MulAction.stabilizer ↥K t =
      (MulAction.stabilizer (MulAut A) t).subgroupOf K := by
    ext m
    simp only [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    constructor <;> intro hm <;> simpa [Subgroup.smul_def, MulAut.smul_def] using hm
  have hcard_stab : Nat.card ↥(MulAction.stabilizer ↥K t) =
      Nat.card ↥(K ⊓ MulAction.stabilizer (MulAut A) t) := by
    rw [hstab_eq]
    rw [← Subgroup.card_subtype K ((MulAction.stabilizer (MulAut A) t).subgroupOf K),
      Subgroup.subgroupOf_map_subtype, inf_comm]
  have hOS := sec1011A_card_orbit_mul_card_stabilizer (G := ↥K) t
  rw [horb, hcard_stab] at hOS
  exact hOS.symm

theorem Sec1011A2.card_K_cases (h : Sec1011A2 B t K φ) :
    Nat.card ↥K = 360 ∨ Nat.card ↥K = 720 := by
  have hK := h.card_K
  rcases h.iso with hp | hp
  · left
    obtain ⟨e⟩ := hp
    have hcard : Nat.card ↥(K ⊓ MulAction.stabilizer (MulAut A) t) = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num
    rw [hK, hcard]
  · right
    obtain ⟨e⟩ := hp
    have hcard : Nat.card ↥(K ⊓ MulAction.stabilizer (MulAut A) t) = 120 := by
      rw [Nat.card_congr e.toEquiv, sec1011_card_perm_five]
    rw [hK, hcard]

private lemma sec1011A_orb_smul (h : Sec1011A2 B t K φ) (α : ↥K) {a : A}
    (ha : a ∈ sec1011_orb K t) : (α : MulAut A) a ∈ sec1011_orb K t := by
  obtain ⟨γ, hγ, rfl⟩ := ha
  exact ⟨(α : MulAut A) * γ, K.mul_mem α.2 hγ, by rw [MulAut.mul_apply]⟩

private lemma sec1011A_delta_mem_image (h : Sec1011A2 B t K φ) (α : ↥K) (i : Fin 6) :
    ∃ j : Fin 6, (α : MulAut A) (sec1011_delta t φ i) = sec1011_delta t φ j := by
  have hi : sec1011_delta t φ i ∈ sec1011_orb K t := by
    rw [← h.delta_range]
    exact ⟨i, rfl⟩
  have hmem : (α : MulAut A) (sec1011_delta t φ i) ∈ Set.range (sec1011_delta t φ) := by
    rw [h.delta_range]
    exact sec1011A_orb_smul h α hi
  obtain ⟨j, hj⟩ := Set.mem_range.mp hmem
  exact ⟨j, hj.symm⟩

private noncomputable def sec1011A_rhoFun (h : Sec1011A2 B t K φ) (α : ↥K) : Fin 6 → Fin 6 :=
  fun i => Classical.choose (sec1011A_delta_mem_image h α i)

private lemma sec1011A_rhoFun_spec (h : Sec1011A2 B t K φ) (α : ↥K) (i : Fin 6) :
    (α : MulAut A) (sec1011_delta t φ i) = sec1011_delta t φ (sec1011A_rhoFun h α i) :=
  Classical.choose_spec (sec1011A_delta_mem_image h α i)

private lemma sec1011A_rhoFun_injective (h : Sec1011A2 B t K φ) (α : ↥K) :
    Function.Injective (sec1011A_rhoFun h α) := by
  intro i j hij
  have h1 : (α : MulAut A) (sec1011_delta t φ i) =
      (α : MulAut A) (sec1011_delta t φ j) := by
    rw [sec1011A_rhoFun_spec h α i, sec1011A_rhoFun_spec h α j, hij]
  exact h.delta_injective ((α : MulAut A).injective h1)

private lemma sec1011A_rhoFun_bijective (h : Sec1011A2 B t K φ) (α : ↥K) :
    Function.Bijective (sec1011A_rhoFun h α) :=
  Finite.injective_iff_bijective.mp (sec1011A_rhoFun_injective h α)

private noncomputable def sec1011A_rho (h : Sec1011A2 B t K φ) :
    ↥K →* Equiv.Perm (Fin 6) :=
  MonoidHom.mk' (fun α => Equiv.ofBijective (sec1011A_rhoFun h α)
      (sec1011A_rhoFun_bijective h α))
    (by
      intro α β
      apply Equiv.ext
      intro i
      change sec1011A_rhoFun h (α * β) i = sec1011A_rhoFun h α (sec1011A_rhoFun h β i)
      apply h.delta_injective
      rw [← sec1011A_rhoFun_spec h (α * β) i,
        ← sec1011A_rhoFun_spec h α (sec1011A_rhoFun h β i),
        ← sec1011A_rhoFun_spec h β i]
      rfl)

private lemma sec1011A_rho_apply (h : Sec1011A2 B t K φ) (α : ↥K) (i : Fin 6) :
    (sec1011A_rho h α) i = sec1011A_rhoFun h α i := rfl

private lemma sec1011A_fix_delta (h : Sec1011A2 B t K φ) {α : ↥K}
    (hα : sec1011A_rho h α = 1) (i : Fin 6) :
    (α : MulAut A) (sec1011_delta t φ i) = sec1011_delta t φ i := by
  rw [sec1011A_rhoFun_spec h α i]
  have hfi : sec1011A_rhoFun h α i = i := by
    rw [← sec1011A_rho_apply h α i, hα]
    rfl
  rw [hfi]

private lemma sec1011A_rho_injective (h : Sec1011A2 B t K φ) :
    Function.Injective (sec1011A_rho h) := by
  rw [injective_iff_map_eq_one]
  intro α hα
  have hfixdelta := sec1011A_fix_delta h hα
  have ht : (α : MulAut A) t = t := by
    rw [← sec1011_delta_zero t φ]
    exact hfixdelta 0
  have hB : ∀ b ∈ B, (α : MulAut A) b = b := by
    apply h.core.fixB_of_fixW4
    intro i
    have hw : φ (sec1011_wfour i) = t * sec1011_delta t φ i.succ := by
      rw [sec1011_delta_succ, ← mul_assoc, h.core.t_sq, one_mul]
    calc (α : MulAut A) (φ (sec1011_wfour i))
        = (α : MulAut A) (t * sec1011_delta t φ i.succ) := by rw [hw]
      _ = (α : MulAut A) t * (α : MulAut A) (sec1011_delta t φ i.succ) := map_mul _ _ _
      _ = t * sec1011_delta t φ i.succ := by rw [ht, hfixdelta i.succ]
      _ = φ (sec1011_wfour i) := hw.symm
  exact Subtype.ext (h.core.eq_one_of_fix hB ht)

theorem sec1011_alt2_act (h : Sec1011A2 B t K φ) :
    ∃ ρ : ↥K →* Equiv.Perm (Fin 6), Function.Injective ρ ∧
      (∀ (α : ↥K) (i : Fin 6),
        (α : MulAut A) (sec1011_delta t φ i) = sec1011_delta t φ (ρ α i)) ∧
      (ρ.range = alternatingGroup (Fin 6) ∨ ρ.range = ⊤) := by
  refine ⟨sec1011A_rho h, sec1011A_rho_injective h, ?_, ?_⟩
  · intro α i
    simpa [sec1011A_rho_apply] using sec1011A_rhoFun_spec h α i
  · have hcard_range : Nat.card ↥(sec1011A_rho h).range = Nat.card ↥K :=
      (Nat.card_congr (MonoidHom.ofInjective (sec1011A_rho_injective h)).toEquiv).symm
    rcases h.card_K_cases with hK | hK
    · left
      apply sec1011_eq_alt_six
      rw [hcard_range, hK]
    · right
      apply sec1011_eq_top_six
      rw [hcard_range, hK]

end CFSG.OddStandard.SmallF3.Omega
