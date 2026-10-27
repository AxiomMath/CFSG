module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29

public section

namespace CFSG.ComponentClassification.GSThmB.P29

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

section Model

variable {M : Type*} [Group M]

@[expose] def ModelConcl (L₀ : Subgroup M) (σ : M) (J S : Subgroup M) (cyc : Prop) : Prop :=
  ∃ t ∈ L₀, t ∈ normalizer (S : Set M) ∧ t ∉ S ∧ t * t ∈ S ∧
    (S ⊓ J) ⊓ conjugate (S ⊓ J) t = ⊥ ∧
    (∀ d ∈ S ⊓ J, ∀ e ∈ conjugate (S ⊓ J) t, d * e = e * d) ∧
    (S ⊓ J) ⊔ conjugate (S ⊓ J) t = S ⊓ L₀ ∧
    (conjugate (S ⊓ J) t ⊓ centralizer (J : Set M)).relIndex (conjugate (S ⊓ J) t) = 2 ∧
    σ ∈ conjugate (S ⊓ J) t ⊓ centralizer (J : Set M) ∧
    (∀ e ∈ conjugate (S ⊓ J) t, σ * e = e * σ) ∧
    (cyc → IsCyclic ↥(conjugate (S ⊓ J) t ⊓ centralizer (J : Set M))) ∧
    ∀ d ∈ conjugate (S ⊓ J) t, d ∉ centralizer (J : Set M) → ∀ j ∈ J, ∃ w ∈ J,
      d * w * d⁻¹ ≠ j * w * j⁻¹

end Model

variable {H M : Type*} [Group H] [Group M]

theorem kernel_eq_centralizer {J : Subgroup H} (hO : pPrimeCore 2 J = ⊥) :
    coreActionKernel J = centralizer (J : Set H) := by
  ext g
  rw [mem_coreActionKernel, hO, Subgroup.map_bot, mem_centralizer_iff]
  constructor
  · rintro ⟨-, h⟩ j hj
    have h1 := h j hj
    rw [mem_bot] at h1
    calc j * g = g * j * (j⁻¹ * g⁻¹ * j * g) := by group
      _ = g * j := by rw [h1, mul_one]
  · intro h
    refine ⟨mem_normalizer_iff.mpr fun j => ⟨fun hj => ?_, fun hj => ?_⟩, fun j hj => ?_⟩
    · rw [← h j hj, mul_inv_cancel_right]
      exact hj
    · have h1 := h _ hj
      have h2 : j = g * j * g⁻¹ := mul_left_cancel (a := g) (by rw [← h1]; group)
      rw [h2]
      exact hj
    · rw [mem_bot]
      calc j⁻¹ * g⁻¹ * j * g = j⁻¹ * g⁻¹ * (j * g) := by group
        _ = 1 := by rw [h j hj]; group

theorem oddCoreIn_eq_bot {J : Subgroup H} (hO : pPrimeCore 2 J = ⊥) : oddCoreIn J = ⊥ := by
  rw [oddCoreIn, hO, Subgroup.map_bot]

theorem map_conjugate_eq (φ : H →* M) (X : Subgroup H) (g : H) :
    (conjugate X g).map φ = conjugate (X.map φ) (φ g) := by
  rw [conjugate, conjugate, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [MulAut.conj_apply, MulAut.conj_apply]
  simp only [map_mul, map_inv]

theorem map_inf_centralizer {φ : H →* M} (hφ : Function.Injective φ) (X J : Subgroup H) :
    (X ⊓ centralizer (J : Set H)).map φ = X.map φ ⊓ centralizer (J.map φ : Set M) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyX, hyC⟩, rfl⟩
    refine ⟨mem_map_of_mem φ hyX, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨j, hj, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hyC j hj]
  · rintro ⟨⟨y, hyX, rfl⟩, hyC⟩
    refine ⟨y, ⟨hyX, mem_centralizer_iff.mpr fun j hj => hφ ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.mp hyC (φ j) ⟨j, hj, rfl⟩

theorem prop29Concl_of_model {H : Type} [Group H] (φ : H →* M) (hφ : Function.Injective φ)
    {ι : H} {J₁ S₁ : Subgroup H} (hO : pPrimeCore 2 J₁ = ⊥)
    (h : ModelConcl ((generalizedFitting H).map φ) (φ ι) (J₁.map φ) (S₁.map φ)
      (¬ Nonempty (↥(generalizedFitting H) ≃* alternatingGroup (Fin 10)))) :
    Prop29Concl H ι J₁ S₁ := by
  obtain ⟨_, ⟨t, htF, rfl⟩, hN, hnS, htt, hbot, hcomm, hsup, hidx, hι, hιc, hcyc, hout⟩ := h
  have hD : S₁.map φ ⊓ J₁.map φ = (S₁ ⊓ J₁).map φ := (map_inf_eq _ _ φ hφ).symm
  have hD' : conjugate ((S₁ ⊓ J₁).map φ) (φ t) = (conjugate (S₁ ⊓ J₁) t).map φ :=
    (map_conjugate_eq φ _ t).symm
  rw [hD, hD'] at hbot hcomm hsup hidx hι hιc hcyc hout
  have hK := kernel_eq_centralizer hO
  unfold Prop29Concl
  refine ⟨t, htF, ?_, fun hs => hnS (mem_map_of_mem φ hs),
    (mem_map_iff_mem hφ).mp (by rw [map_mul]; exact htt), ?_, fun d hd e he => hφ ?_, ?_, ?_, ?_,
    fun e he => hφ ?_, fun hA => ?_, fun d hd hdK j hj => ?_⟩
  · rw [mem_normalizer_iff] at hN ⊢
    intro s
    rw [← mem_map_iff_mem hφ (K := S₁) (x := s), hN (φ s), ← map_inv, ← map_mul, ← map_mul,
      mem_map_iff_mem hφ]
  · apply map_injective hφ
    rw [map_inf_eq _ _ φ hφ, Subgroup.map_bot]
    exact hbot
  · rw [map_mul, map_mul]
    exact hcomm (φ d) (mem_map_of_mem φ hd) (φ e) (mem_map_of_mem φ he)
  · apply map_injective hφ
    rw [Subgroup.map_sup, map_inf_eq S₁ (generalizedFitting H) φ hφ]
    exact hsup
  · rw [hK, ← relIndex_map_map_of_injective _ _ hφ, map_inf_centralizer hφ]
    exact hidx
  · rw [hK, ← mem_map_iff_mem hφ, map_inf_centralizer hφ]
    exact hι
  · rw [map_mul, map_mul]
    exact hιc (φ e) (mem_map_of_mem φ he)
  · rw [hK]
    have := hcyc hA
    rw [← map_inf_centralizer hφ] at this
    exact isCyclic_of_surjective (equivMapOfInjective _ φ hφ).symm (MulEquiv.surjective _)
  · rw [hK] at hdK
    have hdK' : φ d ∉ centralizer (J₁.map φ : Set M) := by
      intro hc
      apply hdK
      have h1 : φ d ∈ (conjugate (S₁ ⊓ J₁) t ⊓ centralizer (J₁ : Set H)).map φ := by
        rw [map_inf_centralizer hφ]
        exact ⟨mem_map_of_mem φ hd, hc⟩
      exact ((mem_map_iff_mem hφ).mp h1).2
    obtain ⟨_, ⟨w, hw, rfl⟩, hne⟩ :=
      hout (φ d) (mem_map_of_mem φ hd) hdK' (φ j) (mem_map_of_mem φ hj)
    refine ⟨w, hw, ?_⟩
    rw [oddCoreIn_eq_bot hO, mem_bot, inv_mul_eq_one]
    intro h1
    apply hne
    simpa [map_mul, map_inv] using congrArg φ h1

theorem eq_of_isSylowIn {X : Type} [Group X] {S Y Q : Subgroup X} (hS : Seven.IsSylowIn S Y)
    (hQY : Q ≤ Y) (hQ : IsPGroup 2 Q) (hSQ : S ≤ Q) : Q = S := by
  obtain ⟨hSY, R, hR⟩ := hS
  have hle : (R : Subgroup Y) ≤ Q.subgroupOf Y := by
    rw [hR]
    exact fun x hx => hSQ hx
  have h1 : Q.subgroupOf Y = S.subgroupOf Y := hR ▸ R.is_maximal' hQ.comap_subtype hle
  rwa [subgroupOf_inj, inf_of_le_left hQY, inf_of_le_left hSY] at h1

theorem mem_smul_sylow_iff {X : Type*} [Group X] {p : ℕ} (P : Sylow p X) (g d : X) :
    d ∈ ((g • P : Sylow p X) : Subgroup X) ↔ g⁻¹ * d * g ∈ (P : Subgroup X) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [MulAut.smul_def, MulAut.conj_apply, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
    exact hy
  · intro h
    exact ⟨_, h, by rw [MulAut.smul_def, MulAut.conj_apply]; group⟩

theorem exists_conj_map_eq {H : Type} [Group H] [Finite H] [Finite M] (φ : H →* M)
    (hφ : Function.Injective φ) {ι : H} {S₁ : Subgroup H}
    (hS : Seven.IsSylowIn S₁ (centralizer ({ι} : Set H))) {P : Subgroup M}
    (hPC : P ≤ centralizer ({φ ι} : Set M)) (hP : IsPGroup 2 P)
    (hPi : ¬ 2 ∣ P.relIndex (centralizer ({φ ι} : Set M))) :
    ∃ g ∈ centralizer ({φ ι} : Set M),
      S₁.map ((MulAut.conj g).toMonoidHom.comp φ) =
        P ⊓ ((MulAut.conj g).toMonoidHom.comp φ).range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({φ ι} : Set M)
  have hSC : S₁.map φ ≤ C := by
    rintro _ ⟨s, hs, rfl⟩
    refine mem_centralizer_iff.mpr ?_
    rintro _ rfl
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp (hS.1 hs) ι rfl]
  have hS2 : IsPGroup 2 (S₁.map φ) := (Seven.IsSylowIn.isPGroup hS).map φ
  let Pc : Sylow 2 C := (hP.comap_subtype (K := C)).toSylow hPi
  obtain ⟨Q, hQ⟩ := (hS2.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C Pc Q
  have key : ∀ s ∈ S₁, (g : M)⁻¹ * φ s * g ∈ P := by
    intro s hs
    have h1 : (⟨φ s, hSC (mem_map_of_mem φ hs)⟩ : C) ∈ ((g • Pc : Sylow 2 C) : Subgroup C) := by
      rw [hg]
      exact hQ (mem_map_of_mem φ hs)
    exact (mem_smul_sylow_iff Pc g _).mp h1
  refine ⟨(g : M)⁻¹, C.inv_mem g.2, ?_⟩
  set ψ := (MulAut.conj (g : M)⁻¹).toMonoidHom.comp φ
  have hψa : ∀ h, ψ h = (g : M)⁻¹ * φ h * g := by
    intro h
    simp [ψ]
  have hψinj : Function.Injective ψ := (MulAut.conj _).injective.comp hφ
  have hψι : ψ ι = φ ι := by
    rw [hψa, mul_assoc, mem_centralizer_iff.mp g.2 (φ ι) rfl, inv_mul_cancel_left]
  have hle : S₁.map ψ ≤ P ⊓ ψ.range := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨by rw [hψa]; exact key s hs, ⟨s, rfl⟩⟩
  have hQ' : (P ⊓ ψ.range).comap ψ = S₁ := by
    refine eq_of_isSylowIn hS (fun h hh => mem_centralizer_iff.mpr ?_)
      ((hP.to_le inf_le_left).comap_of_injective ψ hψinj) (map_le_iff_le_comap.mp hle)
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    apply hψinj
    rw [map_mul, map_mul, hψι]
    exact mem_centralizer_iff.mp (hPC hh.1) (φ ι) rfl
  rw [← hQ', map_comap_eq_self inf_le_right]

end CFSG.ComponentClassification.GSThmB.P29
