module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovGen
public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverDisplacement
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternalConjugacy
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers

public section

namespace CFSG.ComponentClassification.GSThmB.CovM12

open Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.ComponentClassification.M12Cover

theorem ordA_one_ne_95040 (m : ℕ) : Open.ordA 1 m ≠ 95040 :=
  Cov.ordA_one_ne_of_lt (B := 58) (by norm_num) (by decide) m

theorem not_ordA_dvd_192 (m : ℕ) (hm : 5 ≤ m) : ¬ Open.ordA 1 m ∣ 192 :=
  Cov.not_ordA_dvd_of_lt (B := 8) (by norm_num) (by norm_num) (by decide) m hm

theorem twist_inner
    {L : Type} [Group L] [Finite L] (hLq : CFSG.Assembly.IsQuasisimple L) {t : L}
    (ht : orderOf t = 2) (hZ : center L = zpowers t) (π : L →* NativeSporadic.M12)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers t) (X : L)
    (hX2 : X * X ∈ center L) {M : Subgroup NativeSporadic.M12}
    (hM : CFSG.Assembly.IsComponentOf M (centralizer ({π X} : Set NativeSporadic.M12)))
    (hMt : Cov.SmallQ (↥M ⧸ center ↥M)) : ∃ h : L, X * h * X⁻¹ = h * t := by
  have htc : t ∈ center L := hZ ▸ mem_zpowers t
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  set x₀ := π X with hx₀def
  have hx2 : x₀ * x₀ = 1 := by
    have h1 : π (X * X) = 1 := by
      rw [← MonoidHom.mem_ker, hker, ← hZ]
      exact hX2
    rwa [map_mul] at h1
  by_cases hx1 : x₀ = 1
  · exfalso
    have hc : centralizer ({x₀} : Set NativeSporadic.M12) = ⊤ := by
      rw [hx1]
      exact eq_top_iff.mpr fun z _ => mem_centralizer_singleton_iff.mpr (by group)
    rw [hc] at hM
    exact Cov.false_of_top' hLq π hπ (hker.trans hZ.symm) hM hMt
      (fun q => by rw [CFSG.Sporadic.Mathieu.card_M12]; exact ordA_one_ne_95040 q)
      (by rw [CFSG.Sporadic.Mathieu.card_M12]; norm_num)
  have hxo : orderOf x₀ = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  obtain ⟨r, hr, c, hc, hxc⟩ := m12_involution_cover.1 (x₀ : Equiv.Perm (Fin 12))
    (by rw [inv_one, one_mul]; exact x₀.2) (by rw [Subgroup.orderOf_coe, hxo])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exfalso
    have hcard : Nat.card (centralizer ({x₀} : Set NativeSporadic.M12)) = 192 := by
      rw [card_centralizer_eq_centralizerIn, hxc, centralizerIn_conj _ hc,
        Subgroup.card_map_of_injective (MulAut.conj c).injective, card_centralizerIn_m12Rep1]
    exact Cov.false_of_component_card hM hMt (N := 192) (by rw [hcard]) not_ordA_dvd_192
      (by decide)
  · obtain ⟨x, y, hx, hy, hxy, hc', hd⟩ := m12_pair_displacement
    obtain ⟨hfc, h4, -⟩ := m12_double_cover_involution_lift_orders hLq ht hZ π hπ hker
    obtain ⟨u, v, hu, hu0, hduv⟩ := Cov.exists_disp_of_pair π hπ ht
      (fun w => fixedCount w = 0) (fun w W hW hw hP => by
        have h4' : fixedCount w = 4 := (hfc w hw).resolve_right hP
        have := h4 W (by rw [hW]; exact hw) (by rw [hW]; exact h4')
        rw [← sq, ← this, pow_orderOf_eq_one]) hx hy hxy hc' (hd L hLq t ht hZ π hπ hker)
    obtain ⟨g₁, hg₁⟩ := conj_elemZ_of_fixedCount_zero u hu hu0
    set C : NativeSporadic.M12 := ⟨c, hc⟩
    have hx₀ : x₀ = C * elemRep2 * C⁻¹ := Subtype.ext hxc
    refine Cov.twist_of_disp π hπ htc ht2 X hX2 (u := u) (v := v)
      (g := C * elemGz⁻¹ * g₁⁻¹) ?_ hduv
    rw [← hx₀def, hx₀, ← hg₁, elemZ_eq_conj]
    group

theorem twist
    {L : Type} [Group L] [Finite L] (hLq : CFSG.Assembly.IsQuasisimple L) {t : L}
    (ht : orderOf t = 2) (hZ : center L = zpowers t) (π : L →* NativeSporadic.M12)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers t) (α : MulAut L) (hα : α * α = 1)
    (β : MulAut NativeSporadic.M12) (hβ : ∀ x, π (α x) = β (π x))
    {M : Subgroup NativeSporadic.M12} (hM : CFSG.Assembly.IsComponentOf M (fixSub β))
    (hMt : Cov.SmallQ (↥M ⧸ center ↥M)) : ∃ h : L, α h = h * t := by
  by_cases hinn : ∃ X : L, ∀ y, α y = X * y * X⁻¹
  · obtain ⟨X, hX⟩ := hinn
    rw [Cov.fixSub_eq_of_inner π hπ α β hβ X hX] at hM
    obtain ⟨h, hh⟩ := twist_inner hLq ht hZ π hπ hker X
      (Cov.mul_self_mem_center_of_inner α hα X hX) hM hMt
    exact ⟨h, by rw [hX]; exact hh⟩
  · push Not at hinn
    have hout : ∀ n : L, ¬ ∀ y, α y = n * y * n⁻¹ := fun n hn =>
      (hinn n).elim fun y hy => hy (hn y)
    have hα1 : α ≠ 1 := fun h1 => hout 1 fun y => by rw [h1]; simp
    refine Cov.twist_of_ext α ht hZ hα hα1 fun x y hx hxo hy hyo => ?_
    obtain ⟨π', hπ'def⟩ : ∃ f : ↥(Cov.Lsub α) →* NativeSporadic.M12,
        f = π.comp (Cov.eL α).symm.toMonoidHom := ⟨_, rfl⟩
    have hπ' : Function.Surjective π' := by
      rw [hπ'def, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
      exact hπ.comp (Cov.eL α).symm.surjective
    have hker' : π'.ker = center (Cov.Lsub α) := by
      rw [hπ'def, Cov.ker_comp_eL_symm α π hker, Cov.center_Lsub α hZ]
    obtain ⟨-, hconj, -⟩ :=
      ctss_m12_central_double_cover_external_involution_conjugacy_frontier
        (Cov.isQuasisimple_Lsub α hLq) (t := Cov.eL α t) (by rw [MulEquiv.orderOf_eq, ht])
        (Cov.center_Lsub α hZ) (Cov.nonempty_quotient_center_equiv π' hπ' hker')
        (Cov.centralizer_Lsub_eq α hα hout hZ)
    exact hconj x y hx hxo hy hyo

end CFSG.ComponentClassification.GSThmB.CovM12
