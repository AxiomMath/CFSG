module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbedding.KFactProofs.CoverThree.SL3FourGen

open CFSG.Open
open scoped Pointwise

theorem exists_conj_le {G : Type*} [Group G] [Finite G] {R H₀ F : Subgroup G} (hFR : F ≤ R)
    (hF : IsPGroup 3 F) (hH₀R : H₀ ≤ R) (hH₀ : Nat.card H₀ = 27) (hR : Nat.card R = 241920) :
    ∃ g ∈ R, ∀ x ∈ F, g * x * g⁻¹ ∈ H₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF' : IsPGroup 3 (F.subgroupOf R) :=
    hF.of_injective (Subgroup.subgroupOfEquivOfLe hFR).toMonoidHom (MulEquiv.injective _)
  have hcard : Nat.card (H₀.subgroupOf R) = 27 := by
    rw [← hH₀]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH₀R).toEquiv
  have hidx : (H₀.subgroupOf R).index = 8960 := by
    have := (H₀.subgroupOf R).card_mul_index
    rw [hcard, hR] at this
    omega
  obtain ⟨P, hP⟩ := hF'.exists_le_sylow
  let Hs : Sylow 3 R := (IsPGroup.of_card (p := 3) (n := 3) (by rw [hcard]; norm_num)).toSylow
    (by rw [hidx]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R Hs P
  refine ⟨((g⁻¹ : R) : G), (g⁻¹).2, fun x hx => ?_⟩
  have h1 : (⟨x, hFR hx⟩ : R) ∈ (P : Subgroup R) := hP hx
  have h2 : ((g • Hs : Sylow 3 R) : Subgroup R) = (P : Subgroup R) := by rw [hg]
  rw [Sylow.coe_subgroup_smul] at h2
  rw [← h2, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
  have h3 : g⁻¹ * ⟨x, hFR hx⟩ * g ∈ (Hs : Subgroup R) := by simpa using h1
  have h4 : g⁻¹ * ⟨x, hFR hx⟩ * g ∈ H₀.subgroupOf R := h3
  have h5 : (((g⁻¹ * ⟨x, hFR hx⟩ * g : R)) : G) ∈ H₀ := h4
  simpa using h5

theorem closure_pair_eq {G : Type*} [Group G] [Finite G] {F : Subgroup G}
    (hF : Nat.card F = 9) {x y : G} (hx : x ∈ F) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hy : y ∈ F)
    (hyx : y ∉ Subgroup.zpowers x) : Subgroup.closure ({x, y} : Set G) = F := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCF : Subgroup.closure ({x, y} : Set G) ≤ F := by
    rw [Subgroup.closure_le]
    rintro z (rfl | hz)
    · exact hx
    · rw [Set.mem_singleton_iff.1 hz]
      exact hy
  have hZC : Subgroup.zpowers x ≤ Subgroup.closure ({x, y} : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
  have hZ : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  have h1 : 3 ∣ Nat.card (Subgroup.closure ({x, y} : Set G)) := by
    rw [← hZ]
    exact Subgroup.card_dvd_of_le hZC
  have h2 : Nat.card (Subgroup.closure ({x, y} : Set G)) ∣ 9 := by
    rw [← hF]
    exact Subgroup.card_dvd_of_le hCF
  have h3 : Nat.card (Subgroup.closure ({x, y} : Set G)) ≠ 3 := by
    intro h
    have : Subgroup.zpowers x = Subgroup.closure ({x, y} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hZC (by rw [h, hZ])
    exact hyx (this ▸ Subgroup.subset_closure (by simp))
  have h4 : Nat.card (Subgroup.closure ({x, y} : Set G)) = 9 := by
    have hle := Nat.le_of_dvd (by norm_num) h2
    generalize Nat.card (Subgroup.closure ({x, y} : Set G)) = c at *
    interval_cases c <;> omega
  exact Subgroup.eq_of_le_of_card_ge hCF (by rw [h4, hF])

theorem model_gen {G : Type*} [Group G] [Finite G] (R S H₀ : Subgroup G)
    (M : Fin 4 → Subgroup G) (hSn : ∀ g ∈ R, ∀ s ∈ S, g * s * g⁻¹ ∈ S)
    (hR : Nat.card R = 241920) (hH₀R : H₀ ≤ R) (hH₀ : Nat.card H₀ = 27)
    (hM : ∀ k, Nat.card (M k) = 9)
    (hpair : ∀ u ∈ H₀, ∀ v ∈ H₀, u * v = v * u → ∃ k, u ∈ M k ∧ v ∈ M k) (hM0 : M 0 ≤ S)
    (hgen : ∀ k : Fin 4, k ≠ 0 →
      Subgroup.closure {s | s ∈ S ∧ ∃ r ∈ M k, r ≠ 1 ∧ r * s * r⁻¹ = s} = S)
    {F : Subgroup G} (hFR : F ≤ R) (hF : IsElemAbelian 3 F) (hFcard : Nat.card F = 9) :
    F ≤ S ∨ Subgroup.closure {s | s ∈ S ∧ ∃ r ∈ F, r ≠ 1 ∧ r * s * r⁻¹ = s} = S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hFp : IsPGroup 3 F := fun x => ⟨1, Subtype.ext (by simpa using hF.2 x x.2)⟩
  obtain ⟨g, hgR, hg⟩ := exists_conj_le hFR hFp hH₀R hH₀ hR
  have hFbot : F ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hFcard
    omega
  obtain ⟨x₀, hx₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hFbot
  have hx1 : (x₀ : G) ≠ 1 := fun h => hx₀ (Subtype.ext h)
  have hx3 : (x₀ : G) ^ 3 = 1 := hF.2 x₀ x₀.2
  have hZ : Nat.card (Subgroup.zpowers (x₀ : G)) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  obtain ⟨y, hyF, hyx⟩ : ∃ y ∈ F, y ∉ Subgroup.zpowers (x₀ : G) := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (fun y hy => hall y hy : F ≤ Subgroup.zpowers (x₀ : G))
    omega
  have hFeq := closure_pair_eq hFcard x₀.2 hx1 hx3 hyF hyx
  have hcomm : (x₀ : G) * y = y * x₀ :=
    congrArg Subtype.val (hF.1.is_comm.comm x₀ ⟨y, hyF⟩)
  have hu := hg _ x₀.2
  have hv := hg y hyF
  obtain ⟨k, huk, hvk⟩ := hpair _ hu _ hv (by
    calc g * x₀ * g⁻¹ * (g * y * g⁻¹) = g * (x₀ * y) * g⁻¹ := by group
      _ = g * (y * x₀) * g⁻¹ := by rw [hcomm]
      _ = g * y * g⁻¹ * (g * x₀ * g⁻¹) := by group)
  have hFk : F ≤ (M k).comap (MulAut.conj g).toMonoidHom := by
    rw [← hFeq, Subgroup.closure_le]
    rintro z (rfl | hz)
    · exact huk
    · rw [Set.mem_singleton_iff.1 hz]
      exact hvk
  have hcardmap : Nat.card (F.map (MulAut.conj g).toMonoidHom) = 9 := by
    rw [← hFcard]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hmapeq : F.map (MulAut.conj g).toMonoidHom = M k :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.map_le_iff_le_comap.2 hFk) (by rw [hM k, hcardmap])
  have hginv : g⁻¹ ∈ R := R.inv_mem hgR
  by_cases hk0 : k = 0
  · left
    intro z hz
    have h1 : g * z * g⁻¹ ∈ M k := hmapeq ▸ ⟨z, hz, rfl⟩
    have h2 : g * z * g⁻¹ ∈ S := hM0 (hk0 ▸ h1)
    have h3 := hSn g⁻¹ hginv _ h2
    rwa [show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at h3
  · right
    set T := Subgroup.closure {s | s ∈ S ∧ ∃ r ∈ F, r ≠ 1 ∧ r * s * r⁻¹ = s} with hT
    have hTS : T ≤ S := (Subgroup.closure_le S).2 fun s hs => hs.1
    refine le_antisymm hTS fun t ht => ?_
    have hgS : g * t * g⁻¹ ∈ S := hSn g hgR t ht
    rw [← hgen k hk0] at hgS
    have hle : Subgroup.closure {s | s ∈ S ∧ ∃ r ∈ M k, r ≠ 1 ∧ r * s * r⁻¹ = s} ≤
        T.comap (MulAut.conj g⁻¹).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro s ⟨hsS, r, hrM, hr1, hrs⟩
      obtain ⟨z, hzF, rfl⟩ : r ∈ F.map (MulAut.conj g).toMonoidHom := hmapeq ▸ hrM
      refine Subgroup.subset_closure ⟨?_, z, hzF, ?_, ?_⟩
      · have := hSn g⁻¹ hginv s hsS
        simpa using this
      · rintro rfl
        apply hr1
        simp
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hrs ⊢
        calc z * (g⁻¹ * s * g) * z⁻¹
            = g⁻¹ * (g * z * g⁻¹ * s * (g * z * g⁻¹)⁻¹) * g := by group
          _ = g⁻¹ * s * g := by rw [hrs]
    have h5 := hle hgS
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h5
    rwa [show g⁻¹ * (g * t * g⁻¹) * g = t by group] at h5

end CFSG.AGLEmbedding.KFactProofs.CoverThree.SL3FourGen
