module

public import CFSG.StronglyEmbedded.BenderBorelTransport

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.Open

variable {G : Type*} [Group G]

private theorem mem_map_conj_inv_iff {M : Subgroup G} {g x : G} :
    x ∈ M.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * x * g⁻¹ ∈ M := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hm
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

theorem fusionStronglyEmbedded_subgroupOf_of_le {H K M : Subgroup G} (hKH : K ≤ H)
    (hM : fusionStronglyEmbedded (M.subgroupOf H)) (hKM : ¬ K ≤ M)
    (heven : Even (Nat.card (M.subgroupOf K))) : fusionStronglyEmbedded (M.subgroupOf K) := by
  refine ⟨fun htop => hKM (Subgroup.subgroupOf_eq_top.mp htop), heven, fun g hg => ?_⟩
  have hg' : (⟨g, hKH g.2⟩ : H) ∉ M.subgroupOf H := hg
  refine (hM.2.2 _ hg').of_dvd_nat ?_
  rw [← Subgroup.card_map_of_injective K.subtype_injective,
    ← Subgroup.card_map_of_injective H.subtype_injective]
  apply Subgroup.card_dvd_of_le
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_inf, mem_map_conj_inv_iff] at ha
  refine Subgroup.mem_map.mpr ⟨⟨a, hKH a.2⟩, Subgroup.mem_inf.mpr ⟨ha.1, ?_⟩, rfl⟩
  rw [mem_map_conj_inv_iff]
  exact ha.2

theorem fusionStronglyEmbedded_map_of_ker_eq {H₁ H₂ : Type*} [Group H₁] [Group H₂] [Finite H₁]
    [Finite H₂] {f₁ : G →* H₁} {f₂ : G →* H₂} (hf₁ : Function.Surjective f₁)
    (hf₂ : Function.Surjective f₂) (hker : f₁.ker = f₂.ker) {M : Subgroup G}
    (hM : fusionStronglyEmbedded (M.map f₁)) : fusionStronglyEmbedded (M.map f₂) := by
  let e₁ : G ⧸ f₁.ker ≃* H₁ := QuotientGroup.liftEquiv f₁.ker hf₁ rfl
  let e₂ : G ⧸ f₁.ker ≃* H₂ := QuotientGroup.liftEquiv f₁.ker hf₂ hker
  have he : ∀ g, (e₁.symm.trans e₂) (f₁ g) = f₂ g := by
    intro g
    have h1 : e₁.symm (f₁ g) = (g : G ⧸ f₁.ker) := by
      rw [MulEquiv.symm_apply_eq]
      exact (QuotientGroup.liftEquiv_coe f₁.ker hf₁ rfl g).symm
    rw [MulEquiv.trans_apply, h1]
    exact QuotientGroup.liftEquiv_coe f₁.ker hf₂ hker g
  have hmap : (M.map f₁).map (e₁.symm.trans e₂).toMonoidHom = M.map f₂ := by
    rw [Subgroup.map_map]
    congr 1
    ext g
    exact he g
  rw [← hmap]
  exact hM.map_mulEquiv _

end CFSG.ProperTwoGeneratedCore.TheoremC
