module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1RA
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM2Q

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.Blueprint

namespace E3S3O

variable {W : Type} [Group W] [Finite W] {Φ : Set (Subgroup W)} {K K' : Subgroup W} {k k' : W}
  {Q : Type} [Group Q]

theorem members_of_simple (h : TwinBase3 Φ K K' k k') (f : W →* Q) (hf : Function.Surjective f)
    (hf2 : IsPGroup 2 ↥f.ker) (hs : IsSimpleGroup Q)
    (hOS : Balance.oddCoreIn (Subgroup.centralizer ({f k} : Set Q)) = ⊥) :
    (∀ g : W, Nonempty (↥(conjSub g K) ≃* QuaternionGroup 2)) ∧
      (∀ g : W, conjSub g K ⊓ f.ker = ⊥) ∧
      ∀ g₁ g₂ : W, (conjSub g₁ K).map f = (conjSub g₂ K).map f → conjSub g₁ K = conjSub g₂ K := by
  have hcl := h.fam.hyp.conjInvariant
  have hker := ker_eq_center_of_simple h f hf hf2 hs
  have hquat : ∀ g : W, Nonempty (↥(conjSub g K) ≃* QuaternionGroup 2) := fun g =>
    h.fam.quat _ (hcl g K h.memK) _
      ⟨le_rfl, isPGroup_conj_of_simple h f hf hf2 hs hOS g, fun _ hV _ hle => le_antisymm hV hle⟩
  exact ⟨hquat, fun g => inf_eq_bot_of_not_mem (h.invK.conj g) hf2 (not_mem_ker h f hf2 g),
    fun g₁ g₂ he => eq_of_map_eq h.fam hker.le (hcl g₁ K h.memK) (hcl g₂ K h.memK)
      (hquat g₂).some he⟩

theorem quatTwinDatum_map_of_simple (h : TwinBase3 Φ K K' k k') (f : W →* Q)
    (hf : Function.Surjective f) (hf2 : IsPGroup 2 ↥f.ker) (hs : IsSimpleGroup Q)
    (hOS : Balance.oddCoreIn (Subgroup.centralizer ({f k} : Set Q)) = ⊥) :
    QuatTwinDatum (K.map f) (f k) := by
  have hcl := h.fam.hyp.conjInvariant
  have hker := ker_eq_center_of_simple h f hf hf2 hs
  have hK2 : IsPGroup 2 ↥K := by
    have h1 := isPGroup_conj_of_simple h f hf hf2 hs hOS 1
    rwa [conjSub_one] at h1
  have hKinf : K ⊓ f.ker = ⊥ :=
    inf_eq_bot_of_not_mem h.invK hf2 (by simpa using not_mem_ker h f hf2 1)
  obtain ⟨eK⟩ : Nonempty (↥K ≃* QuaternionGroup 2) :=
    h.fam.quat K h.memK K ⟨le_rfl, hK2, fun _ hV _ hle => le_antisymm hV hle⟩
  have hCN := h.fam.tight K h.memK k h.invK
  have hlift : ∀ m : W, f m ∈ Subgroup.centralizer ({f k} : Set Q) →
      ∃ ν ∈ Subgroup.center W, m * k * m⁻¹ = k * ν := by
    intro m hm
    refine ⟨k⁻¹ * (m * k * m⁻¹), ?_, by group⟩
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv,
      Subgroup.mem_centralizer_singleton_iff.mp hm, mul_inv_cancel_right, inv_mul_cancel]
  have hnorm : ∀ m : W, m * k * m⁻¹ = k → conjSub m K = K := fun m hm =>
    mem_normalizer_iff_conjSub_eq.mp (hCN (Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc m * k = m * k * m⁻¹ * m := by group
        _ = k * m := by rw [hm])))
  refine ⟨⟨(Classical.choice (nonempty_mulEquiv_map f hKinf)).symm.trans eK⟩,
    isUniqueInvolution_map f hKinf h.invK, ?_, ?_⟩
  · intro c hc
    obtain ⟨m, rfl⟩ := hf c
    obtain ⟨ν, hνZ, hm⟩ := hlift m hc
    by_cases hν1 : ν = 1
    · left
      rw [← AscQuot.map_conjSub, hnorm m (by rw [hm, hν1, mul_one])]
    · right
      have hK₁ := hcl m K h.memK
      have hinv₁ : IsUniqueInvolution (conjSub m K) (k * ν) := hm ▸ h.invK.conj m
      have hne : k ≠ k * ν := fun h1 => hν1 (by
        have h3 := congrArg (k⁻¹ * ·) h1
        simpa using h3.symm)
      have hcomm := commute_of_twin (h.fam.le_centralizer h.memK h.invK)
        (h.fam.le_centralizer hK₁ hinv₁) hCN (h.fam.tight _ hK₁ _ hinv₁)
        (centralizer_mul_central hνZ).symm (Vtx.inf_eq_bot_of_ne_involution hK2 h.invK hinv₁ hne)
      intro x hx y hy
      rw [← AscQuot.map_conjSub] at hy
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      rw [← map_mul, ← map_mul, hcomm x' hx' y' hy']
  · intro c hc
    obtain ⟨m, rfl⟩ := hf c
    obtain ⟨ν, hνZ, hm⟩ := hlift m hc
    have hk2 : k * k = 1 := h.invK.sq
    have hνk : ν * k = k * ν := (Subgroup.mem_center_iff.mp hνZ k).symm
    have hν2 : ν * ν = 1 := by
      calc ν * ν = k * k * (ν * ν) := by rw [hk2, one_mul]
        _ = k * (k * ν) * ν := by group
        _ = k * (ν * k) * ν := by rw [hνk]
        _ = (k * ν) * (k * ν) := by group
        _ = (m * k * m⁻¹) * (m * k * m⁻¹) := by rw [hm]
        _ = m * (k * k) * m⁻¹ := by group
        _ = 1 := by rw [hk2]; group
    have hmν : m * ν * m⁻¹ = ν := by
      rw [Subgroup.mem_center_iff.mp hνZ m, mul_inv_cancel_right]
    have hmm : m * m * k * (m * m)⁻¹ = k := by
      calc m * m * k * (m * m)⁻¹ = m * (m * k * m⁻¹) * m⁻¹ := by group
        _ = m * (k * ν) * m⁻¹ := by rw [hm]
        _ = (m * k * m⁻¹) * (m * ν * m⁻¹) := by group
        _ = k * ν * ν := by rw [hm, hmν]
        _ = k := by rw [mul_assoc, hν2, mul_one]
    rw [← map_mul, ← AscQuot.map_conjSub, hnorm (m * m) hmm]

theorem twin_map_of_simple (h : TwinBase3 Φ K K' k k') (f : W →* Q)
    (hf : Function.Surjective f) (hf2 : IsPGroup 2 ↥f.ker) (hs : IsSimpleGroup Q)
    (hOS : Balance.oddCoreIn (Subgroup.centralizer ({f k} : Set Q)) = ⊥) :
    f k' = f k ∧ (∃ c : W, conjSub c K = K' ∧ f c ∈ Subgroup.centralizer ({f k} : Set Q) ∧
      K'.map f = conjSub (f c) (K.map f)) ∧ K'.map f ≠ K.map f := by
  have hker := ker_eq_center_of_simple h f hf hf2 hs
  obtain ⟨-, -, heq⟩ := members_of_simple h f hf hf2 hs hOS
  obtain ⟨c, hc⟩ := h.memK'
  have hc' : conjSub c K = K' := hc
  have hk' : c * k * c⁻¹ = k' := (h.invK.conj c).eq (hc' ▸ h.invK')
  have hfk : f k' = f k := by
    have h1 : k * k' ∈ f.ker := by
      rw [hker]
      exact h.center
    rw [MonoidHom.mem_ker, map_mul] at h1
    have h3 : f k * f k = 1 := by rw [← map_mul, h.invK.sq, map_one]
    calc f k' = f k * f k * f k' := by rw [h3, one_mul]
      _ = f k := by rw [mul_assoc, h1, mul_one]
  refine ⟨hfk, ⟨c, hc', ?_, by rw [← hc', AscQuot.map_conjSub]⟩, fun he => ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have e : c * k = k' * c := by rw [← hk']; group
    rw [← map_mul, e, map_mul, hfk]
  · have h1 : conjSub c K = K := by
      simpa only [conjSub_one] using heq c 1 (by rw [conjSub_one, hc']; exact he)
    rw [hc'] at h1
    rcases h.invK.unique k' (h1 ▸ h.invK'.mem) h.invK'.sq with h3 | h3
    · exact h.invK'.ne_one h3
    · exact h.ne h3.symm

theorem map_ker_aut (h : TwinBase3 Φ K K' k k') (f : W →* Q) (hf : Function.Surjective f)
    (hf2 : IsPGroup 2 ↥f.ker) (hs : IsSimpleGroup Q) (σ : MulAut W) :
    f.ker.map σ.toMonoidHom = f.ker := by
  rw [ker_eq_center_of_simple h f hf hf2 hs]
  exact Subgroup.characteristic_iff_map_eq.mp inferInstance σ

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
