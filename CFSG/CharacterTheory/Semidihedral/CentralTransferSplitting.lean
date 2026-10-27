module

public import Mathlib.GroupTheory.Transfer

public noncomputable section

namespace CFSG.Semidihedral.CentralTransferSplitting

universe u v

variable {E : Type u} [Group E]

abbrev centralCommGroup (K : Subgroup E) (hK : K ≤ Subgroup.center E) :
    CommGroup K where
  __ := K.toGroup
  mul_comm x y := Subtype.ext (Subgroup.mem_center_iff.mp (hK y.property) x)

theorem exists_normalized_transfer [Finite E] (p : ℕ) (U : Subgroup E)
    {A : Type v} [CommGroup A] (hpA : IsPGroup p A) (hindex : p.Coprime U.index)
    (φ : U →* A) :
    ∃ T : E →* A, ∀ (w : E) (hw : w ∈ U),
      w ∈ Subgroup.center E → T w = φ ⟨w, hw⟩ := by
  have hbij : Function.Bijective (powMonoidHom (α := A) U.index) :=
    (hpA.powEquiv hindex).bijective
  let power : A ≃* A := MulEquiv.ofBijective (powMonoidHom U.index) hbij
  have htransfer (w : E) (hw : w ∈ U) (hc : w ∈ Subgroup.center E) :
      φ.transfer w = (φ ⟨w, hw⟩) ^ U.index := by
    have key : ∀ (n : ℕ) (e : E),
        e⁻¹ * w ^ n * e ∈ U → e⁻¹ * w ^ n * e = w ^ n := by
      intro n e _
      have hpow : w ^ n ∈ Subgroup.center E := (Subgroup.center E).pow_mem hc n
      rw [Subgroup.mem_center_iff.mp hpow e⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    rw [φ.transfer_eq_pow w key]
    have heq : (⟨w ^ U.index, MonoidHom.transfer_eq_pow_aux w key⟩ : U) =
        (⟨w, hw⟩ : U) ^ U.index := Subtype.ext rfl
    rw [heq, map_pow]
  refine ⟨power.symm.toMonoidHom.comp φ.transfer, fun w hw hc => ?_⟩
  change power.symm (φ.transfer w) = φ ⟨w, hw⟩
  rw [htransfer w hw hc]
  exact power.symm_apply_apply (φ ⟨w, hw⟩)

theorem exists_retraction_of_coprime_index [Finite E] (p : ℕ) (K U : Subgroup E)
    (hKU : K ≤ U) (hcentral : K ≤ Subgroup.center E) (hpK : IsPGroup p K)
    (hindex : p.Coprime U.index) (φ : U →* K)
    (hφ : ∀ k : K, φ (Subgroup.inclusion hKU k) = k) :
    ∃ T : E →* K, ∀ k : K, T (k : E) = k := by
  let : CommGroup K := centralCommGroup K hcentral
  obtain ⟨T, hT⟩ := exists_normalized_transfer p U hpK hindex φ
  refine ⟨T, fun k => ?_⟩
  rw [hT (k : E) (hKU k.property) (hcentral k.property)]
  exact hφ k

variable {G : Type v} [Group G]

@[expose] def localKernelProjection (π : E →* G) (hcentral : π.ker ≤ Subgroup.center E)
    (H : Subgroup G) (s : H →* E) (hs : ∀ x : H, π (s x) = (x : G)) :
    H.comap π →* π.ker where
  toFun u := ⟨(u : E) * (s ⟨π u, u.property⟩)⁻¹, by
    change π ((u : E) * (s ⟨π u, u.property⟩)⁻¹) = 1
    rw [map_mul, map_inv, hs, mul_inv_cancel]⟩
  map_one' := by
    apply Subtype.ext
    have h : (⟨π (1 : E), (1 : H.comap π).property⟩ : H) = 1 :=
      Subtype.ext π.map_one
    change (1 : E) * (s ⟨π (1 : E), (1 : H.comap π).property⟩)⁻¹ = 1
    rw [h, s.map_one, inv_one, mul_one]
  map_mul' u v := by
    apply Subtype.ext
    let x : H := ⟨π u, u.property⟩
    let y : H := ⟨π v, v.property⟩
    have hxy : (⟨π (u * v : H.comap π), (u * v).property⟩ : H) = x * y :=
      Subtype.ext (π.map_mul u v)
    change (u : E) * v * (s ⟨π (u * v : H.comap π), (u * v).property⟩)⁻¹ =
      ((u : E) * (s x)⁻¹) * ((v : E) * (s y)⁻¹)
    rw [hxy, map_mul, mul_inv_rev]
    have hk : (v : E) * (s y)⁻¹ ∈ π.ker := by
      change π ((v : E) * (s y)⁻¹) = 1
      rw [map_mul, map_inv, hs, mul_inv_cancel]
    have hc := Subgroup.mem_center_iff.mp (hcentral hk) ((s x)⁻¹)
    calc
      (u : E) * v * ((s y)⁻¹ * (s x)⁻¹) =
          (u : E) * (((v : E) * (s y)⁻¹) * (s x)⁻¹) := by simp only [mul_assoc]
      _ = (u : E) * ((s x)⁻¹ * ((v : E) * (s y)⁻¹)) := by rw [hc]
      _ = ((u : E) * (s x)⁻¹) * ((v : E) * (s y)⁻¹) := by rw [mul_assoc]

theorem localKernelProjection_inclusion (π : E →* G)
    (hcentral : π.ker ≤ Subgroup.center E) (H : Subgroup G) (s : H →* E)
    (hs : ∀ x : H, π (s x) = (x : G)) (k : π.ker) :
    localKernelProjection π hcentral H s hs
      (Subgroup.inclusion (π.ker_le_comap H) k) = k := by
  apply Subtype.ext
  change (k : E) * (s ⟨π k, (π.ker_le_comap H) k.property⟩)⁻¹ = k
  have h : (⟨π k, (π.ker_le_comap H) k.property⟩ : H) = 1 :=
    Subtype.ext (MonoidHom.mem_ker.mp k.property)
  rw [h, s.map_one, inv_one, mul_one]

theorem exists_section_of_kernel_retraction (π : E →* G) (hπ : Function.Surjective π)
    (T : E →* π.ker) (hT : ∀ k : π.ker, T (k : E) = k) :
    ∃ s₀ : G →* E, ∀ g : G, π (s₀ g) = g := by
  let f : T.ker →* G := π.comp T.ker.subtype
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hk : (y : E)⁻¹ * x ∈ π.ker := π.eq_iff.mp hxy
    have ht : T ((y : E)⁻¹ * x) = 1 := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp y.property,
        MonoidHom.mem_ker.mp x.property, inv_one, one_mul]
    have heq : (⟨(y : E)⁻¹ * x, hk⟩ : π.ker) = 1 := (hT ⟨_, hk⟩).symm.trans ht
    exact (inv_mul_eq_one.mp (congrArg Subtype.val heq)).symm
  have hf_surj : Function.Surjective f := by
    intro g
    obtain ⟨e, he⟩ := hπ g
    let m : E := ((T e : π.ker) : E)⁻¹ * e
    have hm : m ∈ T.ker := by
      change T m = 1
      dsimp only [m]
      rw [map_mul, map_inv, hT, inv_mul_cancel]
    refine ⟨⟨m, hm⟩, ?_⟩
    change π m = g
    dsimp only [m]
    rw [map_mul, map_inv, MonoidHom.mem_ker.mp (T e).property, inv_one, one_mul, he]
  let e : T.ker ≃* G := MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  refine ⟨T.ker.subtype.comp e.symm.toMonoidHom, fun g => ?_⟩
  change f (e.symm g) = g
  exact e.apply_symm_apply g

theorem exists_section_of_coprime_index [Finite E] (p : ℕ) (π : E →* G)
    (hπ : Function.Surjective π) (hcentral : π.ker ≤ Subgroup.center E)
    (hpK : IsPGroup p π.ker) (H : Subgroup G) (hindex : p.Coprime H.index)
    (s : H →* E) (hs : ∀ x : H, π (s x) = (x : G)) :
    ∃ s₀ : G →* E, ∀ g : G, π (s₀ g) = g := by
  have hU : p.Coprime (H.comap π).index := by
    rw [H.index_comap_of_surjective hπ]
    exact hindex
  obtain ⟨T, hT⟩ := exists_retraction_of_coprime_index p π.ker (H.comap π)
    (π.ker_le_comap H) hcentral hpK hU (localKernelProjection π hcentral H s hs)
    (localKernelProjection_inclusion π hcentral H s hs)
  exact exists_section_of_kernel_retraction π hπ T hT

theorem exists_section_of_sylow [Finite E] [Finite G] (p : ℕ) (hp : p.Prime)
    (π : E →* G) (hπ : Function.Surjective π) (hcentral : π.ker ≤ Subgroup.center E)
    (hpK : IsPGroup p π.ker) (P : Sylow p G) (s : P →* E)
    (hs : ∀ x : P, π (s x) = (x : G)) :
    ∃ s₀ : G →* E, ∀ g : G, π (s₀ g) = g := by
  let : Fact p.Prime := ⟨hp⟩
  exact exists_section_of_coprime_index p π hπ hcentral hpK P.toSubgroup
    (hp.coprime_iff_not_dvd.mpr P.not_dvd_index) s hs

end CFSG.Semidihedral.CentralTransferSplitting
