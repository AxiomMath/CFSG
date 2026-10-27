module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieTwin

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.CGT.PushingUpLit.SolKAb (STSetting sylowImg)
open CFSG.ComponentClassification.AschbacherTheorem3 (IsQuaternionTwoGroup)
open CFSG.Assembly (pCoreOf)
open scoped commutatorElement

theorem twinAt_of_commuting {G : Type*} [Group G] {t : G} (ht : t * t = 1)
    (h : ∀ a ∈ Subgroup.centralizer ({t} : Set G), a ^ 2 = t →
      ∃ g ∈ Subgroup.centralizer ({t} : Set G),
        (g * a * g⁻¹) * a = a * (g * a * g⁻¹) ∧ g * a * g⁻¹ ≠ a ∧ g * a * g⁻¹ ≠ a * t) :
    TwinAt t := by
  intro a ha ha2
  obtain ⟨g, hg, hcomm, hne1, hne2⟩ := h a ha ha2
  have hgt : g * t * g⁻¹ = t := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    calc g * t * g⁻¹ = t * g * g⁻¹ := by rw [this]
      _ = t := by group
  have haa : a * a = t := by rw [← pow_two, ha2]
  have hb2 : (g * a * g⁻¹) * (g * a * g⁻¹) = t := by
    calc (g * a * g⁻¹) * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = t := by rw [haa, hgt]
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · calc (a * (g * a * g⁻¹)) ^ 2 = a * (g * a * g⁻¹) * (a * (g * a * g⁻¹)) := pow_two _
      _ = a * ((g * a * g⁻¹) * a) * (g * a * g⁻¹) := by group
      _ = a * (a * (g * a * g⁻¹)) * (g * a * g⁻¹) := by rw [hcomm]
      _ = (a * a) * ((g * a * g⁻¹) * (g * a * g⁻¹)) := by group
      _ = 1 := by rw [haa, hb2, ht]
  · intro h1
    apply hne2
    have hainv : a⁻¹ = a * t := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, haa, ht])
    rw [← hainv]
    exact eq_inv_of_mul_eq_one_right h1
  · intro h1
    apply hne1
    exact mul_left_cancel (h1.trans haa.symm)

@[expose] def ComponentAt {G : Type*} [Group G] (t : G) : Prop :=
  ∃ E : Subgroup G, E ≤ Subgroup.centralizer ({t} : Set G) ∧
    (∀ g ∈ Subgroup.centralizer ({t} : Set G), ∀ e ∈ E, g * e * g⁻¹ ∈ E) ∧ ⁅E, E⁆ = E ∧
    ¬ IsPGroup 2 E ∧
    ∀ N : Subgroup G, N ≤ E → (∀ g ∈ E, ∀ n ∈ N, g * n * g⁻¹ ∈ N) → IsPGroup 2 N →
      N ≤ Subgroup.centralizer (E : Set G)

theorem ComponentAt.map {G H : Type*} [Group G] [Group H] (e : G ≃* H) {t : G}
    (h : ComponentAt t) : ComponentAt (e t) := by
  obtain ⟨E, hEC, hEn, hEp, hE2, hEc⟩ := h
  refine ⟨E.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hEC hx)
    change e x * e t = e t * e x
    rw [← map_mul, ← map_mul, h1]
  · rintro g hg _ ⟨x, hx, rfl⟩
    have hg' : e.symm g ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hg
    refine ⟨e.symm g * x * (e.symm g)⁻¹, hEn _ hg' x hx, ?_⟩
    simp
  · rw [← Subgroup.map_commutator, hEp]
  · intro hp
    exact hE2 (hp.of_equiv (E.equivMapOfInjective e.toMonoidHom e.injective).symm)
  · intro N hNE hNn hN2 x hx
    set N₀ : Subgroup G := N.map e.symm.toMonoidHom with hN₀
    have hN₀E : N₀ ≤ E := by
      rintro _ ⟨n, hn, rfl⟩
      obtain ⟨y, hy, hyn⟩ := hNE hn
      have : e.symm n = y := by rw [← hyn]; simp
      change e.symm n ∈ E
      rw [this]
      exact hy
    have hN₀n : ∀ g ∈ E, ∀ n ∈ N₀, g * n * g⁻¹ ∈ N₀ := by
      rintro g hg _ ⟨n, hn, rfl⟩
      refine ⟨e g * n * (e g)⁻¹, hNn _ ⟨g, hg, rfl⟩ n hn, ?_⟩
      simp
    have hN₀2 : IsPGroup 2 N₀ :=
      hN2.of_equiv (N.equivMapOfInjective e.symm.toMonoidHom e.symm.injective)
    have hc : e.symm x ∈ Subgroup.centralizer (E : Set G) :=
      hEc N₀ hN₀E hN₀n hN₀2 ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hc y hy
    have h2 := congrArg e h1
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
    exact h2

theorem false_of_componentAt {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (S : STSetting G K) {t : G}
    (hC : Subgroup.centralizer ({t} : Set G) = Subgroup.normalizer (K : Set G))
    (hE : ComponentAt t) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEC, hEn, hEp, hE2, hEc⟩ := hE
  set M := Subgroup.normalizer (K : Set G) with hM
  have hEM : E ≤ M := hC ▸ hEC
  have hnM : ∀ g ∈ M, ∀ e ∈ E, g * e * g⁻¹ ∈ E := fun g hg => hEn g (by rw [hC]; exact hg)
  set U := pCoreOf 2 M with hUdef
  have hUM : U ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hMU : M ≤ Subgroup.normalizer (U : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hU2 : IsPGroup 2 U := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hUn : (U.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUM).mpr hMU
  have h1 : ⁅E, U⁆ ≤ E ⊓ U := by
    refine Subgroup.commutator_le.2 fun e he u hu => ⟨?_, ?_⟩
    · have := E.mul_mem he (hnM u (hUM hu) e⁻¹ (E.inv_mem he))
      rwa [show e * (u * e⁻¹ * u⁻¹) = ⁅e, u⁆ by rw [commutatorElement_def]; group] at this
    · have := hUn.conj_mem ⟨u, hUM hu⟩ (Subgroup.mem_subgroupOf.mpr hu) ⟨e, hEM he⟩
      have h2 := U.mul_mem (Subgroup.mem_subgroupOf.mp this) (U.inv_mem hu)
      rwa [show (⟨e, hEM he⟩ * ⟨u, hUM hu⟩ * ⟨e, hEM he⟩⁻¹ : M).1 * u⁻¹ = ⁅e, u⁆ by
        rw [commutatorElement_def]; rfl] at h2
  have h3 : E ⊓ U ≤ Subgroup.centralizer (E : Set G) :=
    hEc (E ⊓ U) inf_le_left (fun g hg n hn => ⟨E.mul_mem (E.mul_mem hg (Subgroup.mem_inf.mp hn).1)
      (E.inv_mem hg), by
        have := hUn.conj_mem ⟨n, hUM (Subgroup.mem_inf.mp hn).2⟩
          (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp hn).2) ⟨g, hEM hg⟩
        exact Subgroup.mem_subgroupOf.mp this⟩) (hU2.to_le inf_le_right)
  have h4 : ⁅⁅E, U⁆, E⁆ = ⊥ := by
    refine le_bot_iff.mp ((Subgroup.commutator_mono h1 le_rfl).trans ?_)
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.2 h3).le
  have h5 : ⁅⁅U, E⁆, E⁆ = ⊥ := by rw [Subgroup.commutator_comm U E]; exact h4
  have h6 : ⁅⁅E, E⁆, U⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := E) (H₂ := E) (H₃ := U) h4 h5
  rw [hEp] at h6
  have hEU : E ≤ U := by
    intro x hx
    refine S.fstar ⟨hEM hx, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have hm : ⁅x, u⁆ ∈ ⁅E, U⁆ := Subgroup.commutator_mem_commutator hx hu
    rw [h6, Subgroup.mem_bot] at hm
    exact (commutatorElement_eq_one_iff_mul_comm.mp hm).symm
  exact hE2 (hU2.to_le hEU)

theorem not_quaternion_of_twin_or_component {X : Type} [Group X] [Finite X]
    (hcl : ∀ t : X, orderOf t = 2 → TwinAt t ∨ ComponentAt t)
    {K : Subgroup X} (S : STSetting X K) (R : Sylow 2 K) :
    ¬ IsQuaternionTwoGroup (sylowImg R) := by
  intro hq
  obtain ⟨t, P, SP, hD, hPK, hKt, hCN⟩ := exists_tightDatum_of_quaternion S R hq
  rcases hcl t hD.order with htw | hcomp
  · exact false_of_twinAt_datum hD hPK hKt htw
  · exact false_of_componentAt S hCN hcomp

theorem not_quaternion_of_equiv {X Y : Type} [Group X] [Finite X] [Group Y] (e : X ≃* Y)
    (hcl : ∀ s : Y, orderOf s = 2 → TwinAt s ∨ ComponentAt s)
    {K : Subgroup X} (S : STSetting X K) (R : Sylow 2 K) :
    ¬ IsQuaternionTwoGroup (sylowImg R) := by
  refine not_quaternion_of_twin_or_component (fun t ht => ?_) S R
  have h := hcl (e t) (by rwa [MulEquiv.orderOf_eq])
  rcases h with h | h
  · left
    simpa using TwinAt.map e.symm h
  · right
    simpa using ComponentAt.map e.symm h

end CFSG.CGT.PushingUpLit.SolKNA
