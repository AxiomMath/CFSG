module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8FrameTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame

open CFSG.Open

theorem FrameProps.of_sylow {Ω : Type*} [Group Ω] [Finite Ω] {ν : Ω → ℕ}
    (hν : ∀ g x, ν (g * x * g⁻¹) = ν x) {s : ℕ} {J₀ T₀ : Subgroup Ω}
    (hT3 : IsPGroup 3 T₀) (hTidx : ¬ 3 ∣ T₀.index)
    (huniq : ∀ J' : Subgroup Ω, J' ≤ T₀ → IsElemAbelian 3 J' → Nat.card J' = 27 → J' = J₀)
    (hF : FrameProps ν s ⊤ J₀) {J' : Subgroup Ω}
    (hJ'ab : IsElemAbelian 3 J') (hJ'card : Nat.card J' = 27) : FrameProps ν s ⊤ J' := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := hJ'ab.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Ω (hT3.toSylow hTidx) Q
  have hle : J'.map (MulAut.conj g⁻¹).toMonoidHom ≤ T₀ := by
    rintro _ ⟨x, hx, rfl⟩
    have hxQ : x ∈ (Q : Subgroup Ω) := hQ hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
    simpa using hxQ
  have hJ'' : J'.map (MulAut.conj g⁻¹).toMonoidHom = J₀ :=
    huniq _ hle (hJ'ab.map _) (by rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
      hJ'card])
  have hmap := hF.map (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (fun x => hν g x)
  have htop : (⊤ : Subgroup Ω).map (MulAut.conj g).toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective
  have hJ0 : J₀.map (MulAut.conj g).toMonoidHom = J' := by
    rw [← hJ'', Subgroup.map_map]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨x, hx, by simp [mul_assoc]⟩
  rwa [htop, hJ0] at hmap

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame
