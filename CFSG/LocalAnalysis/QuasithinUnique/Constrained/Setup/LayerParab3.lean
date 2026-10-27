module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerParab2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerParab1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect4

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6 CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem comp_le_oddGen [Finite V] {H L : Subgroup (V ≃ₗ[k] V)} (hL : IsComponentIn L H) :
    L ≤ oddGen H := by
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  have hLq : CFSG.IsQuasisimple ↥L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL.1) hL.2.1
  have hKH : oddGen H ≤ H := (Subgroup.closure_le H).2 fun h hh => hh.1
  have hKn : ((oddGen H).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKH]
    intro d x hd hx
    induction hd using Subgroup.closure_induction with
    | mem y hy =>
      refine Subgroup.subset_closure ⟨H.mul_mem (H.mul_mem hx hy.1) (H.inv_mem hx), ?_⟩
      have := orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective y
      have e : (MulAut.conj x).toMonoidHom y = x * y * x⁻¹ := rfl
      rw [e] at this
      rw [this]
      exact hy.2
    | one => simp
    | mul a b _ _ ha hb =>
      have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have e : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ha
  let K' := (oddGen H).subgroupOf H
  have h2grp : IsPGroup 2 (↥H ⧸ K') := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨a, ?_⟩
    have hx2 : x ^ 2 ^ a ∈ K' := by
      show ((x ^ 2 ^ a : ↥H) : V ≃ₗ[k] V) ∈ oddGen H
      have hdvd : 2 ^ a ∣ orderOf x := ⟨b, hab⟩
      have h1 : orderOf (x ^ 2 ^ a) = b := by
        rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hab]
        exact Nat.mul_div_cancel_left b (pow_pos two_pos a)
      have h2 : orderOf (((x ^ 2 ^ a : ↥H) : V ≃ₗ[k] V)) = b := by
        rw [Subgroup.orderOf_coe]
        exact h1
      exact Subgroup.subset_closure ⟨(x ^ 2 ^ a).2, by rw [h2]; exact hb⟩
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 hx2
  have hnil : Group.IsNilpotent (↥H ⧸ K') := h2grp.isNilpotent
  let φ : ↥L →* (↥H ⧸ K') := (QuotientGroup.mk' K').comp (Subgroup.inclusion hL.1)
  have hperf : Group.IsPerfect ↥φ.range := by
    have := hLq.1
    exact Group.IsPerfect.range φ
  have hsolv : Group.IsSolvable ↥φ.range := inferInstance
  have hrange : φ.range = ⊥ := by
    by_contra hne
    have hnt : Nontrivial ↥φ.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥φ.range
    exact absurd hperf.commutator_eq_top this.ne
  intro l hl
  have h1 : φ ⟨l, hl⟩ = 1 := by
    have := MonoidHom.range_eq_bot_iff.1 hrange
    exact congrArg (fun f => f ⟨l, hl⟩) this
  have h2 : (⟨l, hL.1 hl⟩ : ↥H) ∈ K' := (QuotientGroup.eq_one_iff _).1 h1
  exact h2

structure ParabolicSection (H T : Subgroup (V ≃ₗ[k] V)) : Prop where
  nonempty : ∃ A, IsMinOffender H A
  J_normal : ((offenderJ H).subgroupOf H).Normal
  H_eq : offenderJ H ⊔ T = H
  K_le_J : oddGen H ≤ offenderJ H
  comps : ∀ L : Subgroup (V ≃ₗ[k] V), IsComponentIn L H →
    L ≤ oddGen H ∧ offenderJ H ≤ Subgroup.normalizer (L : Set (V ≃ₗ[k] V)) ∧
      ∃ A, IsMinOffender H A ∧ ⁅L, A⁆ = L ∧ ∃ I : Submodule k V, ComponentSection L A I

variable [CharP k 2] [Finite V]

theorem minimal_parabolic_section (hQ : QuadBestOffendersNormalize k V)
    {H T M E : Subgroup (V ≃ₗ[k] V)}
    (hO2 : ∀ N : Subgroup (V ≃ₗ[k] V), N ≤ H → (N.subgroupOf H).Normal → IsPGroup 2 N → N = ⊥)
    (hT : IsSylowTwoOf T H) (hTn : ¬ (T.subgroupOf H).Normal) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup (V ≃ₗ[k] V), T ≤ Y → Y < H → Y ≤ M)
    (hEH : E ≤ H) (hEne : E ≠ ⊥) (hEel : CFSG.IsElementaryAbelian 2 E)
    (hEoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) E) : ParabolicSection H T := by
  classical
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  obtain ⟨A₀, hA₀⟩ := exists_minOffender hEH hEne hEel hEoff
  have hJn : ((offenderJ H).subgroupOf H).Normal := offenderJ_normal
  have hsup : offenderJ H ⊔ T = H := by
    have hle : offenderJ H ⊔ T ≤ H := sup_le offenderJ_le hT.1
    rcases hle.lt_or_eq with hlt | heq
    · exfalso
      have hJM : offenderJ H ≤ M := (le_sup_left.trans (hmax _ le_sup_right hlt))
      have hodd := normal_le_max_odd hO2 hT hTn hTM hMH hmax (offenderJ H) offenderJ_le hJn hJM
      have hA₀J : A₀ ≤ offenderJ H := le_offenderJ hA₀
      have hdvd : Nat.card ↥A₀ ∣ Nat.card ↥(offenderJ H) := Subgroup.card_dvd_of_le hA₀J
      have h2 : 2 ∣ Nat.card ↥A₀ := by
        have : CFSG.IsElementaryAbelian 2 ↥A₀ := hA₀.2.2.1
        rcases (CFSG.IsElementaryAbelian.isPGroup 2 A₀).card_eq_or_dvd with h1 | h1
        · exfalso
          apply hA₀.2.1
          exact (Subgroup.card_eq_one).1 h1
        · exact h1
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2.trans hdvd))
    · exact heq
  have hKJ : oddGen H ≤ offenderJ H := by
    refine (Subgroup.closure_le _).2 ?_
    rintro h ⟨hh, hodd⟩
    exact odd_mem_of_sup_eq offenderJ_le hJn hT.1 hT.2.1 hsup h hh hodd
  refine ⟨⟨A₀, hA₀⟩, hJn, hsup, hKJ, fun L hL => ?_⟩
  have hLq : CFSG.IsQuasisimple ↥L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL.1) hL.2.1
  have hLK : L ≤ oddGen H := comp_le_oddGen hL
  have hnorm : offenderJ H ≤ Subgroup.normalizer (L : Set (V ≃ₗ[k] V)) := by
    refine iSup₂_le fun A hA => ?_
    have hAn : A ≤ Subgroup.normalizer (H : Set (V ≃ₗ[k] V)) := hA.1.trans Subgroup.le_normalizer
    obtain ⟨-, hnc⟩ := minimal_best_offenders_normalize_components hQ hAn hA.2.2.1 hA.2.1
      hA.2.2.2.1 hA.2.2.2.2
    intro a ha
    exact mem_normalizer_of_conjSub_le (le_of_eq (hnc L hL a ha))
      (le_of_eq (hnc L hL a⁻¹ (A.inv_mem ha)))
  have hex : ∃ A, IsMinOffender H A ∧ ⁅L, A⁆ ≠ ⊥ := by
    by_contra hcon0
    have hcon : ∀ A, IsMinOffender H A → ⁅L, A⁆ = ⊥ := fun A hA => by
      by_contra h
      exact hcon0 ⟨A, hA, h⟩
    have hJc : offenderJ H ≤ Subgroup.centralizer (L : Set (V ≃ₗ[k] V)) := by
      refine iSup₂_le fun A hA => ?_
      have := hcon A hA
      rw [Subgroup.commutator_comm] at this
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 this
    have hLc : L ≤ Subgroup.centralizer (L : Set (V ≃ₗ[k] V)) := hLK.trans (hKJ.trans hJc)
    have h1 : ⁅L, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hLc
    have h2 : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hLq.1
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hLq
    have : L = ⊥ := by rw [← h2, h1]
    exact (Subgroup.nontrivial_iff_ne_bot L).1 hnt this
  obtain ⟨A, hA, hcomm⟩ := hex
  obtain ⟨I, hI⟩ := component_section hQ hL hA.1 hA.2.2.1 hA.2.1 hA.2.2.2.1 hA.2.2.2.2 hcomm
  exact ⟨hLK, hnorm, A, hA, hI.L_perf, I, hI⟩

end CFSG.QuasithinUnique.Setup.Layer
