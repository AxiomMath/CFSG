module

public import CFSG.ClassicalInvolution.Q3.AE.Conj
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2Conj
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2MemberE64

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem exists_local {n : ℕ} (ι ι' : Fin 4 ↪ Fin n) (σ : Equiv.Perm (Fin n))
    (h : ∀ i, σ (ι i) ∈ Set.range ι') : ∃ c : Equiv.Perm (Fin 4), ∀ i, σ (ι i) = ι' (c i) := by
  choose c hc using h
  have hinj : Function.Injective c := fun i j hij => by
    apply ι.injective
    apply σ.injective
    rw [← hc i, ← hc j, hij]
  exact ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.mp hinj), fun i => (hc i).symm⟩

theorem perm_target : ∀ ℓ ∈ fanoLines, ∃ t ∈ permWords, (∀ x ∈ α0, (pc t.1) x ∈ ℓᶜ) ∧
    (∀ s ∈ fanoLines, s.map (pc t.1).toEmbedding ∈ fanoLines ∧
      s.map (pc t.1)⁻¹.toEmbedding ∈ fanoLines) ∧ Equiv.Perm.sign (pc t.1) = 1 := by
  decide +kernel

theorem member_conj : ∀ α ∈ e64Sets, ∀ (h4 : α.card = 4) (b : Bool),
    ∃ g ∈ aeSubOver l32, ∀ x ∈ memBar α0 α0_card true,
      mkQ 7 g * x * (mkQ 7 g)⁻¹ ∈ memBar α h4 b := by
  rintro α ⟨ℓ, hℓ, rfl⟩ h4 b
  obtain ⟨t, ht, hmapα, hσF, hσs⟩ := perm_target ℓ hℓ
  set σ := pc t.1 with hσ
  have hmap : ∀ i, σ (emb α0 α0_card i) ∈ Set.range (emb ℓᶜ h4) := by
    intro i
    rw [range_emb]
    apply hmapα
    have : emb α0 α0_card i ∈ Set.range (emb α0 α0_card) := Set.mem_range_self i
    rw [range_emb] at this
    exact this
  obtain ⟨c, hc⟩ := exists_local _ _ σ hmap
  have hσmem : ofPerm σ ∈ aeSubOver l32 := ofPerm_mem (F := fanoLines) hσF hσs
  have hemb : (emb α0 α0_card).trans σ.toEmbedding = c.toEmbedding.trans (emb ℓᶜ h4) :=
    Function.Embedding.ext fun i => hc i
  have step : ∀ k ∈ kList, ofPerm σ * embed (emb α0 α0_card) k * (ofPerm σ)⁻¹ =
      embed (emb ℓᶜ h4) (ofPerm c * k * (ofPerm c)⁻¹) := by
    intro k _
    rw [conj_perm_embed, hemb, embed_trans_perm]
  obtain ⟨w1, hw1, hw1eq⟩ := exists_conj_memBar (n := 7) (by norm_num) ℓᶜ h4 l32
  have flipT : ∀ y ∈ memBar ℓᶜ h4 true, mkQ 7 w1 * y * (mkQ 7 w1)⁻¹ ∈ memBar ℓᶜ h4 false := by
    intro y hy
    rw [← hw1eq]
    exact ⟨y, hy, rfl⟩
  have flipF : ∀ y ∈ memBar ℓᶜ h4 false, mkQ 7 w1⁻¹ * y * (mkQ 7 w1⁻¹)⁻¹ ∈ memBar ℓᶜ h4 true := by
    intro y hy
    rw [← hw1eq] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have e : mkQ 7 w1⁻¹ * ((MulAut.conj (mkQ 7 w1)).toMonoidHom z) * (mkQ 7 w1⁻¹)⁻¹ = z := by
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, map_inv,
        inv_inv]
      group
    rw [e]; exact hz
  have img : ∀ x ∈ memBar α0 α0_card true, ∃ k ∈ kList,
      mkQ 7 (ofPerm σ) * x * (mkQ 7 (ofPerm σ))⁻¹ =
        mkQ 7 (embed (emb ℓᶜ h4) (ofPerm c * k * (ofPerm c)⁻¹)) := by
    intro x hx
    obtain ⟨k', hk', rfl⟩ := hx
    obtain ⟨k, hk, rfl⟩ := hk'
    refine ⟨k, hk, ?_⟩
    rw [← step k hk, map_mul, map_mul, map_inv]
  have inK : ∀ k ∈ kList, (∀ k' ∈ kList, ofPerm c * k' * (ofPerm c)⁻¹ ∈ kList) →
      mkQ 7 (embed (emb ℓᶜ h4) (ofPerm c * k * (ofPerm c)⁻¹)) ∈ memBar ℓᶜ h4 true := fun k hk hcK =>
    ⟨embed (emb ℓᶜ h4) (ofPerm c * k * (ofPerm c)⁻¹), ⟨_, mem_kQ.mpr (hcK k hk), rfl⟩, rfl⟩
  have inS : ∀ k ∈ kList, (∀ k' ∈ kList, ofPerm c * k' * (ofPerm c)⁻¹ ∈ kStarList) →
      mkQ 7 (embed (emb ℓᶜ h4) (ofPerm c * k * (ofPerm c)⁻¹)) ∈ memBar ℓᶜ h4 false :=
    fun k hk hcK =>
    ⟨embed (emb ℓᶜ h4) (ofPerm c * k * (ofPerm c)⁻¹), ⟨_, mem_kQStar.mpr (hcK k hk), rfl⟩, rfl⟩
  rcases conj_kQ_cases c with hcK | hcS
  · cases b
    · refine ⟨w1 * ofPerm σ, (aeSubOver l32).mul_mem hw1 hσmem, fun x hx => ?_⟩
      obtain ⟨k, hk, hkx⟩ := img x hx
      have := flipT _ (hkx ▸ inK k hk hcK)
      simp only [map_mul, map_inv]
      convert this using 1
      group
    · refine ⟨ofPerm σ, hσmem, fun x hx => ?_⟩
      obtain ⟨k, hk, hkx⟩ := img x hx
      rw [hkx]; exact inK k hk hcK
  · cases b
    · refine ⟨ofPerm σ, hσmem, fun x hx => ?_⟩
      obtain ⟨k, hk, hkx⟩ := img x hx
      rw [hkx]; exact inS k hk hcS
    · refine ⟨w1⁻¹ * ofPerm σ, (aeSubOver l32).mul_mem ((aeSubOver l32).inv_mem hw1) hσmem,
        fun x hx => ?_⟩
      obtain ⟨k, hk, hkx⟩ := img x hx
      have := flipF _ (hkx ▸ inS k hk hcS)
      simp only [map_mul, map_inv] at this ⊢
      convert this using 1
      group

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf
