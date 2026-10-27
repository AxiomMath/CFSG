module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM2B
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM2A

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

namespace E3S3O

variable {W : Type} [Group W]

theorem commute_of_twin {K K₁ : Subgroup W} {a b : W}
    (hKa : K ≤ Subgroup.centralizer ({a} : Set W)) (hK₁b : K₁ ≤ Subgroup.centralizer ({b} : Set W))
    (hCa : Subgroup.centralizer ({a} : Set W) ≤ Subgroup.normalizer (K : Set W))
    (hCb : Subgroup.centralizer ({b} : Set W) ≤ Subgroup.normalizer (K₁ : Set W))
    (hab : Subgroup.centralizer ({a} : Set W) = Subgroup.centralizer ({b} : Set W))
    (h0 : K ⊓ K₁ = ⊥) : ∀ x ∈ K, ∀ y ∈ K₁, x * y = y * x := by
  intro x hx y hy
  have h1 : x * y * x⁻¹ ∈ K₁ :=
    (Subgroup.mem_normalizer_iff.mp (hCb (hab ▸ hKa hx)) y).mp hy
  have h2 : y * x⁻¹ * y⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (hCa (hab.symm ▸ hK₁b hy)) x⁻¹).mp (K.inv_mem hx)
  have hc : x * y * x⁻¹ * y⁻¹ ∈ K ⊓ K₁ := by
    refine ⟨?_, K₁.mul_mem h1 (K₁.inv_mem hy)⟩
    rw [show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
    exact K.mul_mem hx h2
  rw [h0, Subgroup.mem_bot] at hc
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [hc, one_mul]

theorem centralizer_mul_central {a ν : W} (hν : ν ∈ Subgroup.center W) :
    Subgroup.centralizer ({a * ν} : Set W) = Subgroup.centralizer ({a} : Set W) := by
  ext y
  simp only [Subgroup.mem_centralizer_singleton_iff]
  have hνy : y * ν = ν * y := Subgroup.mem_center_iff.mp hν y
  constructor
  · intro h
    calc y * a = y * (a * ν) * ν⁻¹ := by group
      _ = a * ν * y * ν⁻¹ := by rw [h]
      _ = a * (ν * y) * ν⁻¹ := by group
      _ = a * (y * ν) * ν⁻¹ := by rw [hνy]
      _ = a * y := by group
  · intro h
    calc y * (a * ν) = y * a * ν := by group
      _ = a * y * ν := by rw [h]
      _ = a * (y * ν) := by group
      _ = a * (ν * y) := by rw [hνy]
      _ = a * ν * y := by group

variable [Finite W] {Φ : Set (Subgroup W)} {K K' : Subgroup W} {k k' : W} {Q : Type} [Group Q]
  [Finite Q]

theorem quatTwinDatum_map (h : TwinBase3 Φ K K' k k') (f : W →* Q) (hf : Function.Surjective f)
    (hf2 : IsPGroup 2 ↥f.ker) (hQ : PhilipHall.QuaternionBridge.ExLie Q) :
    QuatTwinDatum (K.map f) (f k) := by
  have hcl := h.fam.hyp.conjInvariant
  have hker : f.ker = Subgroup.center W :=
    le_antisymm (ker_le_center h f hf2) (center_le_ker h f hf hf2 hQ)
  have h2 : ∀ g : W, IsPGroup 2 ↥(conjSub g K) := isPGroup_conj h f hf hf2 hQ
  have hK2 : IsPGroup 2 ↥K := by
    have h1 := h2 1
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

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
