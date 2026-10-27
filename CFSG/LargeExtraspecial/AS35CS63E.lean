module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.AS35CS63Hat
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap

namespace S63

variable {G : Type} [Group G] {S : Setting G}

variable (S) in
@[expose] def Akill {t : G} (ht2 : t * t = 1) (u : G) : Subgroup G where
  carrier := {e | e ∈ S.QG ∧ e * t = t * e ∧ (u * e * u⁻¹ * e⁻¹ = 1 ∨ u * e * u⁻¹ * e⁻¹ = t)}
  mul_mem' := by
    rintro e₁ e₂ ⟨h1Q, h1t, h1⟩ ⟨h2Q, h2t, h2⟩
    refine ⟨S.QG.mul_mem h1Q h2Q, by rw [mul_assoc, h2t, ← mul_assoc, h1t, mul_assoc], ?_⟩
    have e1 : u * (e₁ * e₂) * u⁻¹ * (e₁ * e₂)⁻¹ =
        (u * e₁ * u⁻¹ * e₁⁻¹) * (e₁ * (u * e₂ * u⁻¹ * e₂⁻¹) * e₁⁻¹) := by group
    have hc : ∀ a : G, (a = 1 ∨ a = t) → e₁ * a * e₁⁻¹ = a := by
      rintro a (rfl | rfl)
      · group
      · rw [h1t]; group
    rw [e1, hc _ h2]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2]
    · left; group
    · right; group
    · right; group
    · left; exact ht2
  one_mem' := ⟨S.QG.one_mem, by group, Or.inl (by group)⟩
  inv_mem' := by
    rintro e ⟨heQ, het, h⟩
    refine ⟨S.QG.inv_mem heQ, ?_, ?_⟩
    · calc e⁻¹ * t = e⁻¹ * (t * e) * e⁻¹ := by group
        _ = t * e⁻¹ := by rw [← het]; group
    · have e1 : u * e⁻¹ * u⁻¹ * e⁻¹⁻¹ = e⁻¹ * (u * e * u⁻¹ * e⁻¹)⁻¹ * e := by group
      rw [e1]
      rcases h with h | h <;> rw [h]
      · left; group
      · right
        rw [inv_eq_of_mul_eq_one_right ht2]
        calc e⁻¹ * t * e = e⁻¹ * (t * e) := by group
          _ = t := by rw [← het]; group

theorem exists_inner_of_mem_Hhat [Finite G] {t : G} {htQ : t ∈ S.QG} {ht2 : t * t = 1}
    {u : G} (hu : u ∈ Hhat S htQ ht2) :
    ∃ f ∈ S.QG, f * t = t * f ∧ ∀ e ∈ S.QG, e * t = t * e →
      (f⁻¹ * u) * e * (f⁻¹ * u)⁻¹ * e⁻¹ = 1 ∨ (f⁻¹ * u) * e * (f⁻¹ * u)⁻¹ * e⁻¹ = t := by
  by_cases hall : ∀ e ∈ S.QG, e * t = t * e →
      u * e * u⁻¹ * e⁻¹ = 1 ∨ u * e * u⁻¹ * e⁻¹ = t
  · exact ⟨1, S.QG.one_mem, by group, fun e he het => by simpa using hall e he het⟩
  push Not at hall
  obtain ⟨e₀, he₀Q, he₀t, he₀1, he₀2⟩ := hall
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  set A := Akill S ht2 u with hA
  set W := LinearMap.BilinForm.orthogonal S.q.polarBilin ((ZMod 2) ∙ S.cl t) with hW
  have hWsub : S.clSub (S.QG ⊓ centralizer ({t} : Set G)) = W := by
    rw [S.centralizer_singleton_inf_QG htQ, S.clSub_clPre]
  have hAle : S.clSub A ≤ W := by
    rw [← hWsub]
    exact S.clSub_mono fun e he => ⟨he.1, mem_centralizer_singleton_iff.mpr he.2.1⟩
  have hcomm_mul : ∀ e ∈ S.QG, e * t = t * e →
      u * (e * S.z) * u⁻¹ * (e * S.z)⁻¹ = u * e * u⁻¹ * e⁻¹ := by
    intro e he _
    have hzu : u * S.z = S.z * u := S.z_comm hu.1
    have hzu' : S.z * u⁻¹ = u⁻¹ * S.z := by
      calc S.z * u⁻¹ = u⁻¹ * (u * S.z) * u⁻¹ := by group
        _ = u⁻¹ * (S.z * u) * u⁻¹ := by rw [hzu]
        _ = u⁻¹ * S.z := by group
    calc u * (e * S.z) * u⁻¹ * (e * S.z)⁻¹ = u * e * (S.z * u⁻¹) * S.z⁻¹ * e⁻¹ := by group
      _ = u * e * (u⁻¹ * S.z) * S.z⁻¹ * e⁻¹ := by rw [hzu']
      _ = u * e * u⁻¹ * e⁻¹ := by group
  have he₀A : S.cl e₀ ∉ S.clSub A := by
    intro h
    obtain ⟨a, haA, haQ, hae⟩ := S.mem_clSub_iff.mp h
    rcases (S.cl_eq_cl_iff haQ he₀Q).mp hae with h' | h'
    · subst h'
      rcases haA.2.2 with h'' | h''
      · exact he₀1 h''
      · exact he₀2 h''
    · subst h'
      rw [hcomm_mul a haQ haA.2.1] at he₀1 he₀2
      rcases haA.2.2 with h'' | h''
      · exact he₀1 h''
      · exact he₀2 h''
  have he₀W : S.cl e₀ ∈ W := by
    rw [← hWsub]
    exact S.cl_mem_clSub ⟨he₀Q, mem_centralizer_singleton_iff.mpr he₀t⟩ he₀Q
  have hle : LinearMap.BilinForm.orthogonal S.q.polarBilin W ≤
      LinearMap.BilinForm.orthogonal S.q.polarBilin (S.clSub A) :=
    LinearMap.BilinForm.orthogonal_le hAle
  have hne : LinearMap.BilinForm.orthogonal S.q.polarBilin W ≠
      LinearMap.BilinForm.orthogonal S.q.polarBilin (S.clSub A) := by
    intro h
    have h1 := congrArg (LinearMap.BilinForm.orthogonal S.q.polarBilin) h
    rw [LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl,
      LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl] at h1
    exact he₀A (h1 ▸ he₀W)
  obtain ⟨v, hv, hv'⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hle hne)
  obtain ⟨f, hfQ, rfl⟩ := S.exists_cl v
  have hfA : ∀ e ∈ A, e * f = f * e := by
    intro e he
    have h1 := LinearMap.BilinForm.mem_orthogonal_iff.mp hv (S.cl e) (S.cl_mem_clSub he he.1)
    change S.q.polarBilin (S.cl e) (S.cl f) = 0 at h1
    rw [polarBilin_apply_apply, S.polar_cl_eq_zero_iff he.1 hfQ] at h1
    exact h1
  have htA : t ∈ A := ⟨htQ, rfl, Or.inl (by rw [hu.2.1]; group)⟩
  have hft : f * t = t * f := (hfA t htA).symm
  obtain ⟨e₁, he₁Q, he₁t, he₁f⟩ : ∃ e₁ ∈ S.QG, e₁ * t = t * e₁ ∧ e₁ * f ≠ f * e₁ := by
    by_contra hno
    push Not at hno
    apply hv'
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    rw [← hWsub] at hw
    obtain ⟨e, ⟨heQ', het'⟩, heQ, rfl⟩ := S.mem_clSub_iff.mp hw
    change S.q.polarBilin (S.cl e) (S.cl f) = 0
    rw [polarBilin_apply_apply, S.polar_cl_eq_zero_iff heQ hfQ]
    exact hno e heQ (mem_centralizer_singleton_iff.mp het')
  have he₁A : e₁ ∉ A := fun h => he₁f (hfA e₁ h)
  have hZ : ∀ e ∈ S.QG, e * t = t * e → u * e * u⁻¹ * e⁻¹ ∈ Z2 S t :=
    fun e he het => hu.2.2 e he het
  have hnotA : ∀ e ∈ S.QG, e * t = t * e → e ∉ A →
      u * e * u⁻¹ * e⁻¹ = S.z ∨ u * e * u⁻¹ * e⁻¹ = S.z * t := by
    intro e he het heA
    rcases (mem_Z2_iff htQ ht2).mp (hZ e he het) with h | h | h | h
    · exact absurd ⟨he, het, Or.inl h⟩ heA
    · exact Or.inl h
    · exact absurd ⟨he, het, Or.inr h⟩ heA
    · exact Or.inr h
  have hfnot : ∀ e ∈ S.QG, e * t = t * e → e ∉ A → e * f ≠ f * e := by
    intro e he het heA hef
    have hee : e * e₁ ∈ A := by
      refine ⟨S.QG.mul_mem he he₁Q, by rw [mul_assoc, he₁t, ← mul_assoc, het, mul_assoc], ?_⟩
      have hεe : ∀ a ∈ Z2 S t, e * a * e⁻¹ = a := fun a ha => by
        rw [(comm_of_mem_Z2 htQ ht2 ha (S.QG_le_M he) het)]; group
      have e1 : u * (e * e₁) * u⁻¹ * (e * e₁)⁻¹ =
          (u * e * u⁻¹ * e⁻¹) * (e * (u * e₁ * u⁻¹ * e₁⁻¹) * e⁻¹) := by group
      rw [e1, hεe _ (hZ e₁ he₁Q he₁t)]
      have hzt : S.z * t = t * S.z := (S.z_comm_QG htQ).symm
      rcases hnotA e he het heA with h | h <;> rcases hnotA e₁ he₁Q he₁t he₁A with h' | h' <;>
        rw [h, h']
      · left; exact S.z_mul_z
      · right
        calc S.z * (S.z * t) = (S.z * S.z) * t := by group
          _ = t := by rw [S.z_mul_z, one_mul]
      · right
        calc S.z * t * S.z = t * (S.z * S.z) := by rw [hzt]; group
          _ = t := by rw [S.z_mul_z, mul_one]
      · left
        calc S.z * t * (S.z * t) = S.z * (t * S.z) * t := by group
          _ = S.z * (S.z * t) * t := by rw [← hzt]
          _ = (S.z * S.z) * (t * t) := by group
          _ = 1 := by rw [S.z_mul_z, ht2, one_mul]
    apply he₁f
    have h1 := hfA _ hee
    calc e₁ * f = e⁻¹ * ((e * e₁) * f) := by group
      _ = e⁻¹ * (f * (e * e₁)) := by rw [h1]
      _ = e⁻¹ * (f * e) * e₁ := by group
      _ = e⁻¹ * (e * f) * e₁ := by rw [hef]
      _ = f * e₁ := by group
  refine ⟨f, hfQ, hft, fun e he het => ?_⟩
  have hε := hZ e he het
  have hεf : f * (u * e * u⁻¹ * e⁻¹) = (u * e * u⁻¹ * e⁻¹) * f :=
    comm_of_mem_Z2 htQ ht2 hε (S.QG_le_M hfQ) hft
  have e1 : (f⁻¹ * u) * e * (f⁻¹ * u)⁻¹ * e⁻¹ =
      (u * e * u⁻¹ * e⁻¹) * (f⁻¹ * e * f * e⁻¹) := by
    calc (f⁻¹ * u) * e * (f⁻¹ * u)⁻¹ * e⁻¹ = f⁻¹ * ((u * e * u⁻¹ * e⁻¹) * e) * f * e⁻¹ := by
          group
      _ = f⁻¹ * (u * e * u⁻¹ * e⁻¹) * f * (f⁻¹ * e * f * e⁻¹) := by group
      _ = (u * e * u⁻¹ * e⁻¹) * (f⁻¹ * e * f * e⁻¹) := by
          rw [show f⁻¹ * (u * e * u⁻¹ * e⁻¹) * f = u * e * u⁻¹ * e⁻¹ by
            rw [mul_assoc, ← hεf]; group]
  rw [e1]
  by_cases heA : e ∈ A
  · have h1 : f⁻¹ * e * f * e⁻¹ = 1 := by
      calc f⁻¹ * e * f * e⁻¹ = f⁻¹ * (e * f) * e⁻¹ := by group
        _ = 1 := by rw [hfA e heA]; group
    rw [h1, mul_one]
    exact heA.2.2
  · have hef := hfnot e he het heA
    have h1 : f⁻¹ * e * f * e⁻¹ = S.z := by
      rcases S.mul_comm_or he hfQ with h | h
      · exact absurd h hef
      · calc f⁻¹ * e * f * e⁻¹ = f⁻¹ * (e * f) * e⁻¹ := by group
          _ = f⁻¹ * (S.z * (f * e)) * e⁻¹ := by rw [h]
          _ = f⁻¹ * (S.z * f) := by group
          _ = f⁻¹ * (f * S.z) := by rw [← S.z_comm (S.QG_le_M hfQ)]
          _ = S.z := by group
    rw [h1]
    have hzt : S.z * t = t * S.z := (S.z_comm_QG htQ).symm
    rcases hnotA e he het heA with h | h <;> rw [h]
    · left; exact S.z_mul_z
    · right
      calc S.z * t * S.z = t * (S.z * S.z) := by rw [hzt]; group
        _ = t := by rw [S.z_mul_z, mul_one]

end S63

end CFSG.LargeExtraspecial
