module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5ExclSet
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Gold

open Subgroup CFSG.Open CFSG.Goldschmidt

variable {X : Type} [Group X] [Finite X]

theorem false_of_component_of_comm {Q : Type*} [Group Q] (hcomm : ∀ a b : Q, a * b = b * a)
    {K : Subgroup Q} (hK : IsComponentOf K ⊤) : False := by
  haveI : Nontrivial K := CFSG.ComponentClassification.Quasisimple.nontrivial hK.2.2
  have hcen : Subgroup.center ↥K = ⊤ :=
    eq_top_iff.2 fun k _ => Subgroup.mem_center_iff.2 fun g => Subtype.ext (hcomm g k)
  have h1 : commutator ↥K = ⊥ := (commutator_eq_bot_iff_center_eq_top ↥K).2 hcen
  have h2 : commutator ↥K = ⊤ := hK.2.2.1
  rw [h1] at h2
  exact bot_ne_top h2

theorem layer_eq_bot_of_pCore_eq_Abar {A : Subgroup X} (hEA : IsElemAbelian 2 A)
    (hR : pCore 2 (Mbar A) = Abar A) : goldschmidtLayer (Mbar A) = ⊥ := by
  let H : Subgroup X := ((Abar A).comap (proj A)).map (nc A).subtype
  have hHn : H.Normal := by
    constructor
    rintro _ ⟨m₀, hm₀, rfl⟩ g
    refine ⟨MulAut.conjNormal g m₀, ?_, ?_⟩
    · have h1 : proj A m₀ ∈ pCore 2 (Mbar A) := by rw [hR]; exact hm₀
      have h2 := rhoHom_mem_pCore A g h1
      rw [hR] at h2
      exact h2
    · exact MulAut.conjNormal_apply g m₀
  have hAH : (A : Set X) ⊆ H := by
    intro a ha
    exact ⟨⟨a, Subgroup.le_normalClosure ha⟩, piA_mem_Abar A ⟨a, ha⟩, rfl⟩
  have hle : nc A ≤ H := Subgroup.normalClosure_le_normal hAH
  have hall : ∀ q : Mbar A, q ∈ Abar A := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (goldschmidtOddCore ↥(nc A)) q
    obtain ⟨m₀, hm₀, hmm⟩ := hle m.2
    have : m₀ = m := Subtype.ext hmm
    rw [this] at hm₀
    exact hm₀
  have hcomm : ∀ a b : Mbar A, a * b = b * a := fun a b =>
    congrArg Subtype.val ((isElemAbelian_Abar hEA).1.is_comm.comm ⟨a, hall a⟩ ⟨b, hall b⟩)
  rw [goldschmidtLayer.eq_sSup]
  have : {K : Subgroup (Mbar A) | IsComponentOf K ⊤} = ∅ :=
    Set.eq_empty_of_forall_notMem fun K hK => false_of_component_of_comm hcomm hK
  rw [this, sSup_empty]

theorem false_of_pCore_eq_Ubar {A U : Subgroup X} (hEA : IsElemAbelian 2 A) (hUA : U ≤ A)
    (hU : Nat.card U = 16) {x t s h : X} (hx5 : x ^ 5 = 1) (htx : t * x = x * t)
    (hxA : x ∈ normalizer (A : Set X)) (htA : t ∈ normalizer (A : Set X))
    (hfpf : ∀ a ∈ A, x * a * x⁻¹ = a → a = 1)
    (hCt : ∀ a ∈ A, t * a * t⁻¹ = a ↔ a ∈ U)
    (hsh : s = h * t * h⁻¹) (hsA : s ∈ normalizer (A : Set X))
    (hv : (t * s) * x * (t * s)⁻¹ = x⁻¹)
    (hR : pCore 2 (Mbar A) = Ubar A U) : False := by
  have hρ : ∀ r ∈ pCore 2 (Mbar A), rhoHom A s r = r := by
    intro r hr
    have h1 : rhoHom A h⁻¹ r ∈ pCore 2 (Mbar A) := rhoHom_mem_pCore A h⁻¹ hr
    have h2 : rhoHom A h⁻¹ r ∈ Ubar A U := by rw [← hR]; exact h1
    have h3 : rhoHom A t (rhoHom A h⁻¹ r) = rhoHom A h⁻¹ r :=
      (rhoHom_fixed_iff hEA htA hCt (Ubar_le_Abar A U h2)).2 h2
    have h4 : rhoHom A s = rhoHom A h * rhoHom A t * rhoHom A h⁻¹ := by
      rw [hsh, map_mul, map_mul]
    rw [h4, MulAut.mul_apply, MulAut.mul_apply, h3, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel,
      map_one]
    rfl
  have hsU : ∀ u ∈ U, s * u * s⁻¹ = u := by
    intro u hu
    have hmem : piA A ⟨u, hUA hu⟩ ∈ pCore 2 (Mbar A) := by
      rw [hR]
      exact (piA_mem_Ubar_iff hEA ⟨u, hUA hu⟩).2 hu
    have h1 := hρ _ hmem
    rw [rhoHom_piA A hsA] at h1
    exact congrArg Subtype.val (piA_injective hEA.2 h1)
  have hvU : ∀ u ∈ U, (t * s) * u * (t * s)⁻¹ = u := by
    intro u hu
    have : (t * s) * u * (t * s)⁻¹ = t * (s * u * s⁻¹) * t⁻¹ := by group
    rw [this, hsU u hu]
    exact (hCt u (hUA hu)).2 hu
  have hxU : ∀ u ∈ U, x * u * x⁻¹ ∈ U := by
    intro u hu
    have hA1 : x * u * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hxA u).1 (hUA hu)
    rw [← hCt _ hA1]
    have h1 : t * x = x * t := htx
    have h2 : t * u * t⁻¹ = u := (hCt u (hUA hu)).2 hu
    calc t * (x * u * x⁻¹) * t⁻¹ = (t * x) * u * (t * x)⁻¹ := by group
      _ = (x * t) * u * (x * t)⁻¹ := by rw [h1]
      _ = x * (t * u * t⁻¹) * x⁻¹ := by group
      _ = x * u * x⁻¹ := by rw [h2]
  have hxc : ∀ u ∈ U, x * u = u * x := by
    intro u hu
    have hcom : ∀ w ∈ U, (t * s) * w = w * (t * s) := by
      intro w hw
      have := hvU w hw
      calc (t * s) * w = ((t * s) * w * (t * s)⁻¹) * (t * s) := by group
        _ = w * (t * s) := by rw [this]
    have hxinv : x⁻¹ = (t * s) * x * (t * s)⁻¹ := hv.symm
    have h1 : x⁻¹ * u * x = x * u * x⁻¹ := by
      have h2 : x⁻¹ * u * x = ((t * s) * x * (t * s)⁻¹) * u * ((t * s) * x * (t * s)⁻¹)⁻¹ := by
        rw [hv]
        group
      have h3 : ((t * s) * x * (t * s)⁻¹) * u * ((t * s) * x * (t * s)⁻¹)⁻¹ =
          (t * s) * (x * ((t * s)⁻¹ * u * (t * s)) * x⁻¹) * (t * s)⁻¹ := by group
      have h4 : (t * s)⁻¹ * u * (t * s) = u := by
        have := hcom u hu
        calc (t * s)⁻¹ * u * (t * s) = (t * s)⁻¹ * ((t * s) * u) := by rw [this]; group
          _ = u := by group
      rw [h2, h3, h4]
      have h5 := hcom (x * u * x⁻¹) (hxU u hu)
      calc (t * s) * (x * u * x⁻¹) * (t * s)⁻¹ = ((t * s) * (x * u * x⁻¹)) * (t * s)⁻¹ := by group
        _ = ((x * u * x⁻¹) * (t * s)) * (t * s)⁻¹ := by rw [h5]
        _ = x * u * x⁻¹ := by group
    have h6 : (x * x) * u = u * (x * x) := by
      have h6' : x * (x⁻¹ * u * x) * x⁻¹ = x * (x * u * x⁻¹) * x⁻¹ := by rw [h1]
      have e1 : x * (x⁻¹ * u * x) * x⁻¹ = u := by group
      have e2 : x * (x * u * x⁻¹) * x⁻¹ = (x * x) * u * (x * x)⁻¹ := by group
      rw [e1, e2] at h6'
      calc (x * x) * u = ((x * x) * u * (x * x)⁻¹) * (x * x) := by group
        _ = u * (x * x) := by rw [← h6']
    have h7 : (x * x) ^ 3 = x := by
      have h8 : (x * x) ^ 3 = x ^ 5 * x := by
        rw [← sq, ← pow_mul, show 2 * 3 = 5 + 1 from rfl, pow_succ]
      rw [h8, hx5, one_mul]
    have h8 : Commute (x * x) u := h6
    have h9 := (h8.pow_left 3).eq
    rw [h7] at h9
    exact h9
  have hU1 : ∀ u ∈ U, u = 1 := by
    intro u hu
    apply hfpf u (hUA hu)
    calc x * u * x⁻¹ = (u * x) * x⁻¹ := by rw [hxc u hu]
      _ = u := by group
  have hUbot : U = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    exact Subgroup.mem_bot.2 (hU1 u hu)
  rw [hUbot, Subgroup.card_bot] at hU
  omega

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Gold
