module

public import CFSG.LargeExtraspecial.S9Mod
public import CFSG.LargeExtraspecial.S4Defs
public import CFSG.LargeExtraspecial.S4SpU
public import CFSG.RankThree.OrthogonalInvolutions.Conjugacy

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Module CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial.S2 CFSG.LargeExtraspecial.S4
open LinearMap (BilinForm)

section Comm

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

theorem commSpace_mul_le (x y : M ≃ₗ[ZMod 2] M) :
    commSpace (x * y) ≤ commSpace x ⊔ commSpace y := by
  intro v hv
  obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
  have e : (x * y) w - w = (x (y w) - y w) + (y w - w) := by
    rw [LinearEquiv.mul_apply]
    abel
  rw [e]
  exact Submodule.add_mem_sup (sub_mem_commSpace x _) (sub_mem_commSpace y w)

theorem finrank_commSpace_conj (x y : M ≃ₗ[ZMod 2] M) :
    finrank (ZMod 2) (commSpace (y * x * y⁻¹)) = finrank (ZMod 2) (commSpace x) := by
  rw [commSpace_conj, LinearEquiv.finrank_map_eq]

end Comm

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {f : BilinForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V]
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
variable (ρ : TauCeti.BilinForm.isometryGroup f →* (M ≃ₗ[ZMod 2] M))

theorem two_mul_finrank_commSpace (hf : f.IsAlt) (hnd : f.Nondegenerate) {m : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * m) {p p₁ : V} (hpp₁ : f p p₁ = 1)
    (hD : SpRadDecomp ρ ⊥ ⊤ p p₁) (x : TauCeti.BilinForm.isometryGroup f)
    (hx : (x : V ≃ₗ[ZMod 2] V) ∈ spPointRadical f p₁) (hx1 : (x : V ≃ₗ[ZMod 2] V) ≠ 1)
    (hxa : ¬ IsSpTypeA f x 2) : 2 * finrank (ZMod 2) (commSpace (ρ x)) = finrank (ZMod 2) M := by
  have hb0 := sp_timmesfeld_2_1_b0 ρ hf hnd (F := ⊥) (bot_inf_eq _) (m := m)
    (by rw [spPerp_bot, finrank_top]; exact hdim) (N := ⊤) (fun _ _ v _ => Submodule.mem_top)
    (by rw [spPerp_bot]; exact Submodule.mem_top) (by rw [spPerp_bot]; exact Submodule.mem_top)
    hpp₁ hD x (by rw [spRadFix_bot]; exact hx) hx1 hxa
  have h2 := sp_finrank_eq_two_mul ρ hf hnd (F := ⊥) (bot_inf_eq _) (N := ⊤)
    (fun _ _ v _ => Submodule.mem_top) (by rw [spPerp_bot]; exact Submodule.mem_top)
    (by rw [spPerp_bot]; exact Submodule.mem_top) hpp₁ hD
  rw [Submodule.map_top] at hb0
  rw [commSpace, hb0.2, h2.1, ← h2.2, finrank_top]

omit [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) M] in
theorem not_isSpTypeA_spRho_one (hf : f.IsAlt) (hnd : f.Nondegenerate) {c e : V} (hc : c ≠ 0)
    (hce : f c e = 0) :
    spRho hf hce 1 ≠ 1 ∧ ¬ IsSpTypeA f (spRho hf hce 1) 2 := by
  obtain ⟨v, hv⟩ : ∃ v, f v c ≠ 0 := by
    by_contra! h
    exact hc (hnd.2 c h)
  have hv1 : f v c = 1 := zmod2_eq_one_of_ne_zero hv
  have key : f v (spRho hf hce 1 v) = 1 := by
    rw [spRho_apply, map_add, map_add, map_smul, map_smul, hf.self_eq_zero, hv1, smul_eq_mul,
      smul_eq_mul]
    ring_nf
    generalize f v e = a
    rcases zmod2_eq_zero_or_eq_one a with rfl | rfl <;> decide
  refine ⟨fun h1 => ?_, fun ha => ?_⟩
  · rw [h1, LinearEquiv.coe_one, id, hf.self_eq_zero] at key
    exact zero_ne_one key
  · rw [ha.2.2.2.2 v] at key
    exact zero_ne_one key

omit [FiniteDimensional (ZMod 2) V] in
theorem commSpace_spRho_le (hf : f.IsAlt) {c d : V} (hcd : f c d = 0) (l : ZMod 2) :
    commSpace (spRho hf hcd l) ≤ Submodule.span (ZMod 2) {d, c} := by
  intro v hv
  obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
  rw [spRho_apply, add_assoc, add_sub_cancel_left]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert d {c})))
    (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem d rfl)))

theorem le_four_mul_finrank_commSpace (hf : f.IsAlt) (hnd : f.Nondegenerate) {m : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * m) {p p₁ : V} (hpp₁ : f p p₁ = 1)
    (hD : SpRadDecomp ρ ⊥ ⊤ p p₁) (x : TauCeti.BilinForm.isometryGroup f)
    (hx : (x : V ≃ₗ[ZMod 2] V) ∈ spPointRadical f p₁) (hx1 : (x : V ≃ₗ[ZMod 2] V) ≠ 1) :
    finrank (ZMod 2) M ≤ 4 * finrank (ZMod 2) (commSpace (ρ x)) := by
  by_cases hxa : IsSpTypeA f x 2
  swap
  · have := two_mul_finrank_commSpace ρ hf hnd hdim hpp₁ hD x hx hx1 hxa
    omega
  obtain ⟨-, hp₁0, -⟩ :=
    linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁)
  obtain ⟨d, hd, l, hxe⟩ := exists_eq_spRho hf hnd hp₁0 hx
  have hdp : d ∉ (ZMod 2) ∙ p₁ := by
    intro hdmem
    have h1 := hxa.2.2.2.1
    have h2 : commSpace (x : V ≃ₗ[ZMod 2] V) ≤ (ZMod 2) ∙ p₁ := by
      rw [hxe]
      refine (commSpace_spRho_le hf hd l).trans ?_
      rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact hdmem
      · exact Submodule.mem_span_singleton_self _
    have h3 := Submodule.finrank_mono h2
    have h4 := finrank_span_le_card (R := ZMod 2) ({p₁} : Set V)
    rw [Set.toFinset_singleton, Finset.card_singleton] at h4
    omega
  have hd0 : d ≠ 0 := fun h0 => hdp (h0 ▸ zero_mem _)
  have hdne : d ≠ p₁ := fun h0 => hdp (h0 ▸ Submodule.mem_span_singleton_self _)
  have hF : (⊥ : Submodule (ZMod 2) V) ⊓ spPerp f ⊥ = ⊥ := bot_inf_eq _
  obtain ⟨d', -, hd'd, hd'p⟩ := exists_mem_spPerp_eq_one_eq_zero hf hnd hF
    (v := d) (w := p₁) (by rw [spPerp_bot]; exact Submodule.mem_top)
    (by rw [spPerp_bot]; exact Submodule.mem_top) (linearIndependent_pair_iff.mpr ⟨hd0, hp₁0, hdne⟩)
  have hp₁d' : f p₁ d' = 0 := by rw [isAlt_symm hf, hd'p]
  have hdd' : f d d' = 1 := by rw [isAlt_symm hf, hd'd]
  set y : TauCeti.BilinForm.isometryGroup f := spTv hf (d + d') with hy
  have hyp₁ : (y : V ≃ₗ[ZMod 2] V) p₁ = p₁ := by
    rw [hy, coe_spTv, spTransvection_apply, map_add, hd, hp₁d', add_zero, zero_smul, add_zero]
  have hyd : (y : V ≃ₗ[ZMod 2] V) d = d' := by
    rw [hy, coe_spTv, spTransvection_apply, map_add, hf.self_eq_zero, hdd', zero_add, one_smul,
      ← add_assoc, vec_add_self, zero_add]
  have hconj : ((y * x * y⁻¹ : TauCeti.BilinForm.isometryGroup f) : V ≃ₗ[ZMod 2] V) =
      spRho hf hp₁d' l := by
    have h1 : f ((y : V ≃ₗ[ZMod 2] V) p₁) ((y : V ≃ₗ[ZMod 2] V) d) = 0 := by
      rw [hyp₁, hyd]
      exact hp₁d'
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hxe,
      conj_spRho hf hd l y.2 h1]
    ext v
    rw [spRho_apply, spRho_apply, hyp₁, hyd]
  have hpd : f p₁ (d + d') = 0 := by rw [map_add, hd, hp₁d', add_zero]
  have hprod : ((x * (y * x * y⁻¹) : TauCeti.BilinForm.isometryGroup f) : V ≃ₗ[ZMod 2] V) =
      spRho hf hpd 1 := by
    rw [Subgroup.coe_mul, hconj, hxe, spRho_mul hf hd hp₁d' l l hpd, hdd', vec_add_self,
      zero_add]
  obtain ⟨hz1, hza⟩ := not_isSpTypeA_spRho_one hf hnd hp₁0 hpd
  have hz := two_mul_finrank_commSpace ρ hf hnd hdim hpp₁ hD (x * (y * x * y⁻¹))
    (by rw [hprod]; exact spRho_mem_spPointRadical hf hpd 1) (by rw [hprod]; exact hz1)
    (by rw [hprod]; exact hza)
  have hle := commSpace_mul_le (ρ x) (ρ (y * x * y⁻¹))
  rw [← map_mul] at hle
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_add_le_finrank_add_finrank (commSpace (ρ x))
    (commSpace (ρ (y * x * y⁻¹)))
  have h3 : finrank (ZMod 2) (commSpace (ρ (y * x * y⁻¹))) =
      finrank (ZMod 2) (commSpace (ρ x)) := by
    rw [map_mul, map_mul, map_inv]
    exact finrank_commSpace_conj (ρ x) (ρ y)
  omega

end CFSG.LargeExtraspecial.S9
