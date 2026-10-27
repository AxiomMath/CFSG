module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNHolt

public section

namespace CFSG.ComponentClassification.GrSLit.HeSN

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {X : Type} [Group X] [Finite X]

theorem exists_mem_normalizer_sq {T T₁ : Subgroup X} (hT2 : IsPGroup 2 T) (hT₁T : T₁ ≤ T)
    (hne : ¬ T ≤ T₁) :
    ∃ t ∈ T, t ∉ T₁ ∧ t * t ∈ T₁ ∧ ∀ g ∈ T₁, t * g * t⁻¹ ∈ T₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥T := hT2.isNilpotent
  have hH : T₁.subgroupOf T < ⊤ := lt_top_iff_ne_top.mpr fun h => hne fun x hx => by
    have h1 : (⟨x, hx⟩ : ↥T) ∈ T₁.subgroupOf T := h ▸ mem_top _
    exact h1
  obtain ⟨t₀, ht₀N, ht₀H⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hH)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hT2) t₀
  have hex : ∃ j : ℕ, t₀ ^ (2 ^ (j + 1)) ∈ T₁.subgroupOf T := ⟨n, by
    rw [pow_succ, pow_mul, ← hn, pow_orderOf_eq_one, one_pow]
    exact one_mem _⟩
  have hj : t₀ ^ (2 ^ (Nat.find hex + 1)) ∈ T₁.subgroupOf T := Nat.find_spec hex
  have hjt : t₀ ^ (2 ^ Nat.find hex) ∉ T₁.subgroupOf T := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, pow_zero, pow_one]
      exact ht₀H
    · obtain ⟨j', hj'⟩ : ∃ j', Nat.find hex = j' + 1 := ⟨Nat.find hex - 1, by omega⟩
      have h1 := Nat.find_min hex (show j' < Nat.find hex by omega)
      rw [hj']
      exact h1
  have htN : t₀ ^ (2 ^ Nat.find hex) ∈ normalizer (T₁.subgroupOf T : Set ↥T) := pow_mem ht₀N _
  refine ⟨_, (t₀ ^ (2 ^ Nat.find hex)).2, fun h' => hjt (mem_subgroupOf.mpr h'), ?_,
    fun g hg => ?_⟩
  · have h1 : t₀ ^ (2 ^ (Nat.find hex + 1)) =
        t₀ ^ (2 ^ Nat.find hex) * t₀ ^ (2 ^ Nat.find hex) := by
      rw [pow_succ, pow_mul, pow_two]
    rw [h1] at hj
    exact hj
  · exact (mem_normalizer_iff.mp htN ⟨g, hT₁T hg⟩).mp hg

namespace Setting

variable {a : X} {L W K : Subgroup X} (h : Setting X a L W K)
include h

theorem inf_conjugate_ne_bot {T : Subgroup X} (hTsyl : IsSylowTwoIn T (normalizer (W : Set X)))
    {m : X} (hm : m ∈ normalizer (W : Set X)) : T ⊓ conjugate K m ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup X := normalizer (W : Set X) with hM
  set J : Subgroup X := ⨆ (g : X) (_ : g ∈ M), conjugate K g with hJ
  have hJM : J ≤ M := iSup₂_le fun g hg => conjugate_le_of_mem h.le_normalizer hg
  have hMJ : M ≤ normalizer (J : Set X) := by
    intro g hg
    refine mem_normalizer_of_map_conj_le ?_
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun g' hg' x hx => ?_
    have hmem : g * x * g⁻¹ ∈ conjugate K (g' * g⁻¹) := by
      rw [mem_conjugate_iff] at hx ⊢
      rwa [show g' * g⁻¹ * (g * x * g⁻¹) * (g' * g⁻¹)⁻¹ = g' * x * g'⁻¹ by group]
    simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (le_iSup₂_of_le (f := fun (g : X) (_ : g ∈ M) => conjugate K g) (g' * g⁻¹)
      (mul_mem hg' (inv_mem hg)) le_rfl) hmem
  have hK₃J : conjugate K m ≤ J := le_iSup₂_of_le m hm le_rfl
  have hJK₃ : J ≤ normalizer (conjugate K m : Set X) := by
    refine iSup₂_le fun g hg => ?_
    by_cases he : conjugate K g = conjugate K m
    · rw [he]
      exact le_normalizer
    · exact (GrS5.commutator_le_of_ne (conjugate_le_of_mem h.le_normalizer hm)
        (conjugate_le_of_mem h.le_normalizer hg)
        (isPComponent_conjugate_subgroupOf hm h.isPComponent_K)
        (isPComponent_conjugate_subgroupOf hg h.isPComponent_K) (Ne.symm he)).2
  obtain ⟨R, hR⟩ := RankProjectiveAction.exists_sylow_inf_of_le_normalizer hTsyl.1 hTsyl.2 hJM hMJ
  obtain ⟨R', hR'⟩ := RankProjectiveAction.exists_sylow_inf_of_le_normalizer
    (inf_le_right : T ⊓ J ≤ J) ⟨R, hR⟩ hK₃J hJK₃
  rw [inf_assoc, inf_of_le_right hK₃J] at hR'
  intro hbot
  have hev : 2 ∣ Nat.card ↥(conjugate K m) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp (GrS4.not_odd_card_of_isPComponent
      (conjugate_le_of_mem h.le_normalizer hm)
      (isPComponent_conjugate_subgroupOf hm h.isPComponent_K)))
  apply R'.ne_bot_of_dvd_card hev
  rw [hR', hbot]
  exact (bot_subgroupOf _)

theorem eq_or_eq_of_mem
    (hMax : MaximalTwoComponentInputHe)
    (hS : SchreierFor Blueprint.Catalog) (hHN : HeldNotProperFixedInput)
    (h64 : HeldSylowElementarySixtyFour) (hMult : TBLit.HeldTrivialMultiplier)
    {T : Subgroup X} (hTsyl : IsSylowTwoIn T (normalizer (W : Set X))) (haT : a ∈ T)
    (hTK : ¬ T ≤ normalizer (K : Set X)) :
    ∃ t ∈ T, t ∉ normalizer (K : Set X) ∧ t * t ∈ normalizer (K : Set X) ∧
      ∀ m ∈ normalizer (W : Set X), conjugate K m = K ∨ conjugate K m = conjugate K t := by
  have hT2 := hTsyl.isPGroup
  obtain ⟨t, htT, htT₁, htt, htN⟩ := exists_mem_normalizer_sq hT2
    (inf_le_left : T ⊓ normalizer (K : Set X) ≤ T) fun hle => hTK (hle.trans inf_le_right)
  have htK : t ∉ normalizer (K : Set X) := fun ht => htT₁ (mem_inf.mpr ⟨htT, ht⟩)
  have httK : t * t ∈ normalizer (K : Set X) := (mem_inf.mp htt).2
  refine ⟨t, htT, htK, httK, fun m hm => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  have htM := hTsyl.1 htT
  set T₂ : Subgroup X := T ⊓ normalizer (K : Set X) ⊔ zpowers t with hT₂
  set R : Subgroup X := T₂ ⊓ coreActionKernel K ⊓ coreActionKernel (conjugate K t) with hR
  have hT₂T : T₂ ≤ T := sup_le inf_le_left (zpowers_le.mpr htT)
  have hT₂2 : IsPGroup 2 T₂ := hT2.to_le hT₂T
  have hRT₂ : R ≤ T₂ := inf_le_left.trans inf_le_left
  have hcK : ∀ {g x : X}, g ∈ normalizer (K : Set X) → x ∈ coreActionKernel K →
      g * x * g⁻¹ ∈ coreActionKernel K := fun hg hx => HeDiag.conj_mem_coreActionKernel_of_mem hg hx
  have hT₂n : T₂ ≤ normalizer (R : Set X) := by
    refine sup_le (fun g hg => ?_) (zpowers_le.mpr ?_)
    · refine mem_normalizer_of_map_conj_le ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨⟨hxT₂, hxK⟩, hxKt⟩ := And.intro (mem_inf.mp (mem_inf.mp hx).1) (mem_inf.mp hx).2
      have hgT₂ : g ∈ T₂ := mem_sup_left hg
      refine mem_inf.mpr ⟨mem_inf.mpr ⟨mul_mem (mul_mem hgT₂ hxT₂) (inv_mem hgT₂),
        hcK (mem_inf.mp hg).2 hxK⟩, FooteLit.mem_coreActionKernel_conjugate_iff.mpr ?_⟩
      have h1 := FooteLit.mem_coreActionKernel_conjugate_iff.mp hxKt
      have h2 := hcK (htN g hg |> fun h' => (mem_inf.mp h').2) h1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rwa [show t * g * t⁻¹ * (t * x * t⁻¹) * (t * g * t⁻¹)⁻¹ = t * (g * x * g⁻¹) * t⁻¹ by
        group] at h2
    · refine mem_normalizer_of_map_conj_le ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨⟨hxT₂, hxK⟩, hxKt⟩ := And.intro (mem_inf.mp (mem_inf.mp hx).1) (mem_inf.mp hx).2
      have htT₂ : t ∈ T₂ := mem_sup_right (mem_zpowers t)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine mem_inf.mpr ⟨mem_inf.mpr ⟨mul_mem (mul_mem htT₂ hxT₂) (inv_mem htT₂),
        FooteLit.mem_coreActionKernel_conjugate_iff.mp hxKt⟩,
        FooteLit.mem_coreActionKernel_conjugate_iff.mpr ?_⟩
      have h1 := hcK httK hxK
      rwa [show t * t * x * (t * t)⁻¹ = t * (t * x * t⁻¹) * t⁻¹ by group] at h1
  have hK₃M := conjugate_le_of_mem h.le_normalizer hm
  have hK₃c := isPComponent_conjugate_subgroupOf hm h.isPComponent_K
  have hKtc := isPComponent_conjugate_subgroupOf htM h.isPComponent_K
  have hle : T ⊓ conjugate K m ≤ R := by
    intro x hx
    obtain ⟨hxT, hxK₃⟩ := mem_inf.mp hx
    have hxN : x ∈ normalizer (K : Set X) :=
      (GrS5.commutator_le_of_ne h.le_normalizer hK₃M h.isPComponent_K hK₃c
        (Ne.symm hne1)).2 hxK₃
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨mem_sup_left (mem_inf.mpr ⟨hxT, hxN⟩),
      le_coreActionKernel_of_ne h.le_normalizer hK₃M h.isPComponent_K hK₃c (Ne.symm hne1) hxK₃⟩,
      le_coreActionKernel_of_ne (conjugate_le_of_mem h.le_normalizer htM) hK₃M hKtc hK₃c
        (Ne.symm hne2) hxK₃⟩
  have hRne : R ≠ ⊥ := fun hb => h.inf_conjugate_ne_bot hTsyl hm (eq_bot_iff.mpr (hb ▸ hle))
  obtain ⟨s, hsR, hs2, hsc⟩ := exists_central_involution hT₂2 hRT₂ hT₂n hRne
  have haT₂ : a ∈ T₂ :=
    mem_sup_left (mem_inf.mpr ⟨haT, (mem_coreActionKernel.mp (h.mem_kernel hMax)).1⟩)
  exact htK (h.mem_normalizer_of_commute hMax hS hHN h64 hMult hs2 (hsc a haT₂)
    (mem_inf.mp (mem_inf.mp hsR).1).2 htM (hsc t (mem_sup_right (mem_zpowers t))))

end Setting

end CFSG.ComponentClassification.GrSLit.HeSN
