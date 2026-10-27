module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallLocal

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Open

section Generic

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem SporCore.noTwo_sylow (hp : p.Prime) (hp2 : p ≠ 2) {T : Sylow p K} (D : SporCore p K T)
    (hΓ : GLBCore p 1 (T : Subgroup K) ≠ ⊤) (hdvd : p ^ 2 ∣ Nat.card T)
    (hexp : ∀ t : K, (∃ n : ℕ, t ^ p ^ n = 1) → t ^ p = 1) (S : Sylow p K) (U : Subgroup K)
    (hU : IsPGroup 2 U) (hSU : (S : Subgroup K) ≤ Subgroup.normalizer (U : Set K)) : U = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K T S
  set U' : Subgroup K := U.comap (MulAut.conj g).toMonoidHom with hU'
  have hU'p : IsPGroup 2 U' := hU.comap_of_injective _ (MulAut.conj g).injective
  have hmemU' : ∀ x : K, x ∈ U' ↔ g * x * g⁻¹ ∈ U := fun x => Iff.rfl
  have hTU' : (T : Subgroup K) ≤ Subgroup.normalizer (U' : Set K) := by
    intro t ht
    have h1 : g * t * g⁻¹ ∈ (S : Subgroup K) := by
      rw [← hg, coe_smul_sylow_eq_map]
      exact ⟨t, ht, rfl⟩
    have h2 := Subgroup.mem_normalizer_iff.1 (hSU h1)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmemU', hmemU', h2 (g * x * g⁻¹)]
    have : g * (t * x * t⁻¹) * g⁻¹ = g * t * g⁻¹ * (g * x * g⁻¹) * (g * t * g⁻¹)⁻¹ := by group
    rw [this]
  have hexp' : ∀ s ∈ (T : Subgroup K), s ^ p = 1 := by
    intro s hs
    obtain ⟨k, hk⟩ := T.2 ⟨s, hs⟩
    exact hexp s ⟨k, congrArg Subtype.val hk⟩
  have hbot := D.noTwo hp hp2 hΓ hdvd hexp' U' hU'p hTU'
  rw [eq_bot_iff]
  intro u hu
  have hu' : MulAut.conj g⁻¹ u ∈ U' := by
    rw [hmemU']
    have : g * (MulAut.conj g⁻¹ u) * g⁻¹ = u := by
      rw [MulAut.conj_apply]
      group
    rw [this]
    exact hu
  rw [hbot, Subgroup.mem_bot] at hu'
  have : u = 1 := (map_eq_one_iff (MulAut.conj g⁻¹) (MulAut.conj g⁻¹).injective).1 hu'
  exact Subgroup.mem_bot.2 this

theorem exists_plane_of_exponent (hp : p.Prime) (S : Subgroup K) (hdvd : p ^ 2 ∣ Nat.card S)
    (hexp : ∀ s ∈ S, s ^ p = 1) :
    ∃ E : Subgroup K, E ≤ S ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E', hE'⟩ := Sylow.exists_subgroup_card_pow_prime (G := S) p hdvd
  refine ⟨E'.map S.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · have hcomm : IsMulCommutative E' := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hE'
    have : IsElementaryAbelian p E' :=
      { toIsMulCommutative := hcomm
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => by
          apply Subtype.ext
          apply Subtype.ext
          have h := hexp ((x : S) : K) (x : S).2
          simpa [Subgroup.coe_pow] using h }
    exact IsElementaryAbelian.map_subtype
  · rw [Subgroup.card_map_of_injective S.subtype_injective, hE']

end Generic

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
