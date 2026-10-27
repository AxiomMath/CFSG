module

public import CFSG.LieType.Chevalley.EvenF4InvolutionSylowDescent
public import CFSG.LieType.Chevalley.EvenQuadraticGraphFieldDescent

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem centralizer_inf_map_conj_of_conj_eq {G : Type*} [Group G] {α β ψ : MulAut G}
    (h : ψ * α * ψ⁻¹ = β) (H : Subgroup (MulAut G))
    (hH : (MulAut.conj : G →* MulAut G).range ≤ H) :
    (MulAut.conj : G →* MulAut G).range ≤ H.map (MulAut.conj ψ).toMonoidHom ∧
    (Subgroup.centralizer {α} ⊓ H).map (MulAut.conj ψ).toMonoidHom =
      Subgroup.centralizer {β} ⊓ H.map (MulAut.conj ψ).toMonoidHom ∧
    ∃ e : ↥(Subgroup.centralizer {α} ⊓ H) ≃*
        ↥(Subgroup.centralizer {β} ⊓ H.map (MulAut.conj ψ).toMonoidHom),
      ∀ γ, (e γ : MulAut G) = ψ * γ * ψ⁻¹ := by
  have hmap : (Subgroup.centralizer {α} ⊓ H).map (MulAut.conj ψ).toMonoidHom =
      Subgroup.centralizer {β} ⊓ H.map (MulAut.conj ψ).toMonoidHom := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj ψ).injective,
      (fixed_centralizer_of_conj_eq h).2.2.1]
  refine ⟨?_, hmap, ((Subgroup.centralizer {α} ⊓ H).equivMapOfInjective
    (MulAut.conj ψ).toMonoidHom (MulAut.conj ψ).injective).trans (MulEquiv.subgroupCongr hmap),
    fun γ => ?_⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨MulAut.conj (ψ⁻¹ x), hH ⟨_, rfl⟩, MulEquiv.ext fun y => ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv,
      MulAut.apply_inv_self]
  · change MulAut.conj ψ (γ : MulAut G) = _
    rw [MulAut.conj_apply]


theorem even_F4_all_outer_involutions_canonical
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ f)
    (α : MulAut (adjointGroup ReeTag.F4.tag K)) (hα : α ^ 2 = 1)
    (hαo : α ∉ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
      MulAut (adjointGroup ReeTag.F4.tag K)).range) :
    ∃ ψ : MulAut (adjointGroup ReeTag.F4.tag K),
      ψ * α * ψ⁻¹ = ReeTag.F4.finiteExceptionalAut K ^ f ∧
      (∀ e : ℕ, f = 2 * e →
        ReeTag.F4.finiteExceptionalAut K ^ f = ReeTag.F4.finiteFrobeniusAut K ^ e ∧
        ∀ δ : K →+* K, (∀ c, δ c = c ^ 2 ^ e) → ∀ u,
          ((ReeTag.F4.finiteExceptionalAut K ^ f) u : ModGL ReeTag.F4.tag K) =
            Units.map (entrywiseHom δ) (u : ModGL ReeTag.F4.tag K)) ∧
      (∀ m : ℕ, f = 2 * m + 1 →
        ReeTag.F4.finiteExceptionalAut K ^ f = ReeTag.F4.finiteReeAut K m ∧
        ψ ∈ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
          MulAut (adjointGroup ReeTag.F4.tag K)).range) ∧
      (α.toMonoidHom.eqLocus (MonoidHom.id _)).map ψ.toMonoidHom =
        (ReeTag.F4.finiteExceptionalAut K ^ f).toMonoidHom.eqLocus (MonoidHom.id _) ∧
      (Subgroup.centralizer {α}).map (MulAut.conj ψ).toMonoidHom =
        Subgroup.centralizer {ReeTag.F4.finiteExceptionalAut K ^ f} ∧
      (∃ e : ↥(Subgroup.centralizer {α}) ≃*
          ↥(Subgroup.centralizer {ReeTag.F4.finiteExceptionalAut K ^ f}),
        ∀ γ, (e γ : MulAut (adjointGroup ReeTag.F4.tag K)) = ψ * γ * ψ⁻¹) ∧
      ∀ H : Subgroup (MulAut (adjointGroup ReeTag.F4.tag K)),
        (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
          MulAut (adjointGroup ReeTag.F4.tag K)).range ≤ H →
        (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
          MulAut (adjointGroup ReeTag.F4.tag K)).range ≤ H.map (MulAut.conj ψ).toMonoidHom ∧
        (Subgroup.centralizer {α} ⊓ H).map (MulAut.conj ψ).toMonoidHom =
          Subgroup.centralizer {ReeTag.F4.finiteExceptionalAut K ^ f} ⊓
            H.map (MulAut.conj ψ).toMonoidHom ∧
        ∃ e : ↥(Subgroup.centralizer {α} ⊓ H) ≃*
            ↥(Subgroup.centralizer {ReeTag.F4.finiteExceptionalAut K ^ f} ⊓
              H.map (MulAut.conj ψ).toMonoidHom),
          ∀ γ, (e γ : MulAut (adjointGroup ReeTag.F4.tag K)) = ψ * γ * ψ⁻¹ := by
  obtain ⟨-, hNF, -, hinv, -, heven, hodd⟩ := even_F4_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨g, k⟩, hgk, -⟩ := hNF α
  have hgf : α = MulAut.conj g * ReeTag.F4.finiteExceptionalAut K ^ f := by
    rcases hinv α g k k.2 hgk hα with h0 | hf'
    · exact absurd ⟨g, by rw [hgk, h0, pow_zero, mul_one]⟩ hαo
    · rw [hgk, hf']
  have hfield : ∀ e : ℕ, f = 2 * e →
      ReeTag.F4.finiteExceptionalAut K ^ f = ReeTag.F4.finiteFrobeniusAut K ^ e ∧
      ∀ δ : K →+* K, (∀ c, δ c = c ^ 2 ^ e) → ∀ u,
        ((ReeTag.F4.finiteExceptionalAut K ^ f) u : ModGL ReeTag.F4.tag K) =
          Units.map (entrywiseHom δ) (u : ModGL ReeTag.F4.tag K) := by
    intro e he
    refine ⟨heven e he, fun δ hδ u => ?_⟩
    obtain ⟨fr, hfr, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two hf hK
    have hσ : ∀ c, (fr ^ e) c = c ^ ReeTag.F4.prime ^ e := ringAut_pow_apply_of_frobenius hfr e
    have hσδ : (fr ^ e).toRingHom = δ := RingHom.ext fun c => by
      rw [hδ]
      exact hσ c
    rw [heven e he, ← exactNormalAut_one_eq_finiteFrobeniusAut_pow ReeTag.F4 hσ,
      coe_exactNormalAut_zero, rootDiagUnit_one, one_mul, inv_one, mul_one, hσδ]
  obtain ⟨ψ, hψ, hψi⟩ : ∃ ψ : MulAut (adjointGroup ReeTag.F4.tag K),
      ψ * α * ψ⁻¹ = ReeTag.F4.finiteExceptionalAut K ^ f ∧
      ∀ m : ℕ, f = 2 * m + 1 → ψ ∈ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
        MulAut (adjointGroup ReeTag.F4.tag K)).range := by
    obtain ⟨n, hn | hn⟩ := Nat.even_or_odd' f
    ·
      have hn1 : 1 ≤ n := by omega
      have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, hn]
      obtain ⟨fr, hfr, -⟩ :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
          Nat.prime_two hf hK
      have hσ : ∀ c, (fr ^ n).toRingHom c = c ^ 2 ^ n := ringAut_pow_apply_of_frobenius hfr n
      obtain ⟨β, hβ, hdesc⟩ :=
        (even_exceptional_quadratic_field_graph_field_involution_descent hn1 K hK'
          (fr ^ n).toRingHom hσ).1 ReeTag.F4.tag
      have hαform : ∀ u, (α u : ModGL ReeTag.F4.tag K) = (g : ModGL ReeTag.F4.tag K) *
          rootDiagUnit ReeTag.F4.tag 1 * Units.map (entrywiseHom (fr ^ n).toRingHom)
            (u : ModGL ReeTag.F4.tag K) * (rootDiagUnit ReeTag.F4.tag 1)⁻¹ *
              (g : ModGL ReeTag.F4.tag K)⁻¹ := fun u => by
        rw [hgf, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
          Subgroup.coe_inv, (hfield n hn).2 _ hσ u, rootDiagUnit_one, mul_one, inv_one, mul_one]
      obtain ⟨-, hψ⟩ := hdesc g 1
      obtain ⟨ψ, hψα, -⟩ := hψ α hαform (by rw [← sq, hα])
      refine ⟨ψ, MulEquiv.ext fun u => Subtype.ext ?_, fun m hm => by omega⟩
      rw [hψα u, (hfield n hn).2 _ hσ u]
    ·
      obtain ⟨-, -, -, hconj⟩ := even_F4_exceptional_involution_Sylow_descent hn K hK
      obtain ⟨h, hh⟩ := hconj g (by rw [← hgf, hα])
      exact ⟨MulAut.conj h, by rw [hgf, hh], fun _ _ => ⟨h, rfl⟩⟩
  obtain ⟨hfix, -, hcent, hiso⟩ := fixed_centralizer_of_conj_eq hψ
  exact ⟨ψ, hψ, hfield, fun m hm => ⟨(hodd m hm).2.1, hψi m hm⟩, hfix, hcent, hiso,
    fun H hH => centralizer_inf_map_conj_of_conj_eq hψ H hH⟩

end CFSG.LieType.Chevalley
