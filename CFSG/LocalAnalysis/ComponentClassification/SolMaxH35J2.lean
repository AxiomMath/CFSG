module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxH35Core
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovJ2
public import Certificates.Certificate23301

public section

namespace CFSG.ComponentClassification.SolMax.H35.J2

open Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.ComponentClassification.GSThmB
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.J2Cover
open CFSG.Certificates

theorem j2_h35_check : j2H35Check = true :=
  Certificates.certificate23301

theorem rep_c {j : ℕ} (hj : j < 2) :
    Rep 315 cent2BStrong[j]! (permOfArr 315 cent2BStrong[j]!) :=
  rep_permOfArr_of_chainOK (n := 315) (k := 2) (base := ([0, 3] : List (Fin 315)))
    (chunks := 4) cent2B_check.1 (by have h4 : cent2BStrong.size = 4 := (by decide); omega)

theorem permOfArr_c_mem {j : ℕ} (hj : j < 2) :
    permOfArr 315 cent2BStrong[j]! ∈ centralizerIn P permA := by
  rw [inner_classes.2.2.1, cent2BChain, ofArrays_originalSubgroup]
  exact Subgroup.subset_closure ⟨j, hj, rfl⟩

theorem exists_gh :
    ∃ g h : Equiv.Perm (Fin 315), g ∈ centralizerIn P permA ∧ h ∈ centralizerIn P permA ∧
      g ^ 5 = 1 ∧ h ^ 5 = 1 ∧ g * h * (g * h) = 1 ∧ g * h ≠ 1 ∧
      Nat.card {i : Fin 315 // (g * h) i = i} = 11 := by
  have h := j2_h35_check
  simp only [j2H35Check, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hg5, hh5⟩, hd2⟩, hd1⟩, hfix⟩ := h
  set A₀ := permOfArr 315 cent2BStrong[0]!
  set A₁ := permOfArr 315 cent2BStrong[1]!
  have r₀ : Rep 315 c1 A₀ := rep_c (j := 0) (by norm_num)
  have r₁ : Rep 315 c2 A₁ := rep_c (j := 1) (by norm_num)
  have m₀ : A₀ ∈ centralizerIn P permA := permOfArr_c_mem (j := 0) (by norm_num)
  have m₁ : A₁ ∈ centralizerIn P permA := permOfArr_c_mem (j := 1) (by norm_num)
  have rg : Rep 315 gArr (A₀ * A₀) := rep_compA r₀ r₀
  have rh : Rep 315 hArr (A₀ * A₀ * (A₁ * A₁)) := rep_compA (rep_compA r₀ r₀) (rep_compA r₁ r₁)
  have rd : Rep 315 dArr (A₀ * A₀ * (A₀ * A₀ * (A₁ * A₁))) := rep_compA rg rh
  have pow5 : ∀ {t : Array ℕ} {σ : Equiv.Perm (Fin 315)}, Rep 315 t σ →
      eqA 315 (pow5A t) (idA 315) = true → σ ^ 5 = 1 := by
    intro t σ ht he
    have h1 := eq_of_eqA (rep_compA ht (rep_compA ht (rep_compA ht (rep_compA ht ht))))
      rep_idA he
    rw [← h1]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  refine ⟨A₀ * A₀, A₀ * A₀ * (A₁ * A₁), (centralizerIn P permA).mul_mem m₀ m₀,
    (centralizerIn P permA).mul_mem ((centralizerIn P permA).mul_mem m₀ m₀)
      ((centralizerIn P permA).mul_mem m₁ m₁), pow5 rg hg5, pow5 rh hh5,
    eq_of_eqA (rep_compA rd rd) rep_idA hd2, fun h1 => ?_, ?_⟩
  · rw [h1] at rd
    rw [(eqA_iff rd rep_idA).2 rfl] at hd1
    exact absurd hd1 (by simp)
  · rw [card_fixed_eq_fixedCount rd, hfix]

theorem exists_mem_fixCount_eleven
    {x₀ : NativeSporadic.J2} (hxo : orderOf x₀ = 2)
    (h240 : Nat.card (centralizer ({x₀} : Set NativeSporadic.J2)) = 240)
    {M : Subgroup NativeSporadic.J2}
    (hsub : CFSG.Assembly.IsSubnormal M (centralizer ({x₀} : Set NativeSporadic.J2)))
    (hcop : Nat.Coprime 5 (M.relIndex (centralizer ({x₀} : Set NativeSporadic.J2)))) :
    ∃ D ∈ M, D * D = 1 ∧ D ≠ 1 ∧
      Models.fixCount ((nativeEquivP D : P) : Equiv.Perm (Fin 315)) = 11 := by
  obtain ⟨e, he⟩ : ∃ e : NativeSporadic.J2 ≃* P, e = nativeEquivP := ⟨_, rfl⟩
  obtain ⟨y, hey⟩ : ∃ y : NativeSporadic.J2, e y = ⟨permA, permA_mem⟩ :=
    ⟨e.symm ⟨permA, permA_mem⟩, e.apply_symm_apply _⟩
  have hyo : orderOf y = 2 := by
    rw [← MulEquiv.orderOf_eq e, hey, Subgroup.orderOf_mk, orderOf_permA]
  have hfy : Lift.fixedCount (nativeEquivP y) = 15 := by
    rw [← he, hey, Lift.fixedCount_eq_card]
    exact fixed_points_reps.1
  obtain ⟨c, hc⟩ := CovJ2.exists_conj_of_card hxo hyo h240 hfy
  obtain ⟨g₀, h₀, hgC, hhC, hg5, hh5, hd2, hd1, hdfix⟩ := exists_gh
  obtain ⟨hgP, hgA⟩ := mem_centralizerIn.mp hgC
  obtain ⟨hhP, hhA⟩ := mem_centralizerIn.mp hhC
  have hcomm : ∀ u : P, (u : Equiv.Perm (Fin 315)) * permA = permA * u →
      e.symm u * y = y * e.symm u := by
    intro u hua
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hey]
    exact Subtype.ext hua
  have hcent : ∀ u : NativeSporadic.J2, u * y = y * u →
      c * u * c⁻¹ ∈ centralizer ({x₀} : Set NativeSporadic.J2) := by
    intro u hu
    rw [mem_centralizer_singleton_iff, ← hc]
    calc c * u * c⁻¹ * (c * y * c⁻¹) = c * (u * y) * c⁻¹ := by group
      _ = c * (y * u) * c⁻¹ := by rw [hu]
      _ = c * y * c⁻¹ * (c * u * c⁻¹) := by group
  have hpow : ∀ u : P, u ^ 5 = 1 → (c * e.symm u * c⁻¹) ^ 5 = 1 := by
    intro u hu5
    rw [conj_pow, ← map_pow, hu5, map_one, mul_one, mul_inv_cancel]
  set g : P := ⟨g₀, hgP⟩
  set h : P := ⟨h₀, hhP⟩
  have hg5' : g ^ 5 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hg5)
  have hh5' : h ^ 5 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hh5)
  have hG : c * e.symm g * c⁻¹ ∈ M :=
    mem_of_isSubnormal_of_coprime hsub hcop (hcent _ (hcomm g hgA)) (hpow g hg5')
  have hH : c * e.symm h * c⁻¹ ∈ M :=
    mem_of_isSubnormal_of_coprime hsub hcop (hcent _ (hcomm h hhA)) (hpow h hh5')
  refine ⟨c * e.symm (g * h) * c⁻¹, ?_, ?_, ?_, ?_⟩
  · have h1 : c * e.symm (g * h) * c⁻¹ = c * e.symm g * c⁻¹ * (c * e.symm h * c⁻¹) := by
      rw [map_mul]
      group
    rw [h1]
    exact M.mul_mem hG hH
  · have h2 : g * h * (g * h) = 1 := Subtype.ext hd2
    calc c * e.symm (g * h) * c⁻¹ * (c * e.symm (g * h) * c⁻¹) =
        c * e.symm (g * h * (g * h)) * c⁻¹ := by rw [map_mul e.symm (g * h)]; group
      _ = 1 := by rw [h2, map_one]; group
  · intro h1
    apply hd1
    have h3 : e.symm (g * h) = 1 := by
      calc e.symm (g * h) = c⁻¹ * (c * e.symm (g * h) * c⁻¹) * c := by group
        _ = 1 := by rw [h1]; group
    have h4 : g * h = 1 := by
      rw [← e.apply_symm_apply (g * h), h3, map_one]
    exact congrArg Subtype.val h4
  · rw [← he, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, Models.fixCount_conj, Models.fixCount,
      ← Nat.card_eq_fintype_card]
    exact hdfix

theorem false_of_inner
    {L : Type} [Group L] [Finite L] (hLq : CFSG.Assembly.IsQuasisimple L)
    {t : L} (ht : orderOf t = 2) (hZ : center L = zpowers t) (π : L →* NativeSporadic.J2)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers t) (X : L) (hX2 : X * X ∈ center L)
    {Lt : Subgroup L} (huniq : ∀ y ∈ Lt, y * y = 1 → y = 1 ∨ y = t)
    (hM : CFSG.Assembly.IsComponentOf (Lt.map π)
      (centralizer ({π X} : Set NativeSporadic.J2)))
    (hMt : Cov.SmallQ (↥(Lt.map π) ⧸ center ↥(Lt.map π))) : False := by
  have hx2 : π X * π X = 1 := by
    have h1 : π (X * X) = 1 := by
      rw [← MonoidHom.mem_ker, hker, ← hZ]
      exact hX2
    rwa [map_mul] at h1
  by_cases hx1 : π X = 1
  · have hc : centralizer ({π X} : Set NativeSporadic.J2) = ⊤ := by
      rw [hx1]
      exact eq_top_iff.mpr fun z _ => mem_centralizer_singleton_iff.mpr (by group)
    rw [hc] at hM
    exact CovJ2.false_of_top hM hMt
  have hxo : orderOf (π X) = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  have h240 := CovJ2.card_centralizer_of_component hxo hM
  obtain ⟨D, hDM, hD2, hD1, hDfix⟩ :=
    exists_mem_fixCount_eleven hxo h240 hM.2.1 (coprime_five_relIndex hM.1 h240 hMt)
  have hDo : orderOf D = 2 := orderOf_eq_prime (by rw [sq]; exact hD2) hD1
  obtain ⟨ℓ, hℓ, hℓD₀⟩ := hDM
  have hℓD : π ℓ = D := hℓD₀
  obtain ⟨π₁, hπ₁def⟩ : ∃ f : L →* P, f = nativeEquivP.toMonoidHom.comp π := ⟨_, rfl⟩
  have hπ₁ : Function.Surjective π₁ := by
    rw [hπ₁def, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
    exact nativeEquivP.surjective.comp hπ
  have hker₁ : π₁.ker = zpowers t := by
    rw [← hker]
    ext v
    simp only [hπ₁def, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  obtain ⟨-, h11, -⟩ := j2_double_cover_involution_lift_orders_fixCount hLq ht hZ π₁ hπ₁ hker₁
  have hπ₁ℓ : π₁ ℓ = nativeEquivP D := by
    rw [hπ₁def, MonoidHom.comp_apply, hℓD, MulEquiv.coe_toMonoidHom]
  have hℓo : orderOf ℓ = 2 :=
    h11 ℓ (by rw [hπ₁ℓ, MulEquiv.orderOf_eq, hDo]) (by rw [hπ₁ℓ]; exact hDfix)
  have hℓ2 : ℓ * ℓ = 1 := by rw [← sq, ← hℓo, pow_orderOf_eq_one]
  have htk : π t = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact mem_zpowers t
  rcases huniq ℓ hℓ hℓ2 with h1 | h1
  · exact hD1 (by rw [← hℓD, h1, map_one])
  · exact hD1 (by rw [← hℓD, h1, htk])

theorem false_of_fixed
    {L : Type} [Group L] [Finite L] (hLq : CFSG.Assembly.IsQuasisimple L)
    {t : L} (ht : orderOf t = 2) (hZ : center L = zpowers t) (π : L →* NativeSporadic.J2)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers t) (α : MulAut L) (hα : α * α = 1)
    (β : MulAut NativeSporadic.J2) (hβ : ∀ x, π (α x) = β (π x)) {Lt : Subgroup L}
    (hLt : ⁅Lt, Lt⁆ = Lt) (htL : t ∈ Lt) (hfix : ∀ y ∈ Lt, α y = y)
    (huniq : ∀ y ∈ Lt, y * y = 1 → y = 1 ∨ y = t)
    (hM : CFSG.Assembly.IsComponentOf (Lt.map π) (fixSub β))
    (hMt : Cov.SmallQ (↥(Lt.map π) ⧸ center ↥(Lt.map π))) : False := by
  by_cases hinn : ∃ X : L, ∀ y, α y = X * y * X⁻¹
  · obtain ⟨X, hX⟩ := hinn
    rw [Cov.fixSub_eq_of_inner π hπ α β hβ X hX] at hM
    exact false_of_inner hLq ht hZ π hπ hker X (Cov.mul_self_mem_center_of_inner α hα X hX)
      huniq hM hMt
  · push Not at hinn
    exact false_of_outer (s := .J2) hLq ht hZ π hπ hker α hα
      (fun n hn => (hinn n).elim fun y hy => hy (hn y)) (MulEquiv.refl NativeSporadic.J2)
      ctss_j2_central_double_cover_external_involution_data_frontier hLt htL hfix

end CFSG.ComponentClassification.SolMax.H35.J2
