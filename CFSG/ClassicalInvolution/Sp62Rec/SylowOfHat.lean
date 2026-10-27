module

public import CFSG.ClassicalInvolution.Sp62Rec.ModelCR1CE

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.Open

section Generic

variable {P Q : Type*} [Group P] [Group Q] [Finite P] {p : ℕ} [Fact p.Prime]

theorem bijective_comp_sylow_subtype (ψ : P →* Q) (hψ : Function.Surjective ψ)
    (hQ : IsPGroup p Q) (hker : Nat.Coprime (Nat.card ψ.ker) p) (T : Sylow p P) :
    Function.Bijective (ψ.comp (T : Subgroup P).subtype) := by
  constructor
  · refine (injective_iff_map_eq_one _).mpr fun t ht => ?_
    have hcop : Nat.Coprime (Nat.card (T : Subgroup P)) (Nat.card ψ.ker) := by
      rw [Sylow.card_eq_multiplicity]
      exact Nat.Coprime.pow_left _ hker.symm
    have hdis := Subgroup.disjoint_of_coprime_natCard hcop
    exact Subtype.ext (Subgroup.disjoint_def.mp hdis t.2 ht)
  · intro q
    have htop : (T : Subgroup P).map ψ = ⊤ :=
      ((T.mapSurjective hψ).3 (hQ.to_subgroup ⊤) le_top).symm
    obtain ⟨t, ht, rfl⟩ : q ∈ (T : Subgroup P).map ψ := by
      rw [htop]
      exact Subgroup.mem_top q
    exact ⟨⟨t, ht⟩, rfl⟩

end Generic

section E64

variable {K L : Type} [Group K] [Group L]

theorem isE64_map_of_injective {f : K →* L} (hf : Function.Injective f) {A : Subgroup K}
    (hA : IsE64 A) : IsE64 (A.map f) := by
  obtain ⟨hcomm, hsq, hcard⟩ := hA
  refine ⟨?_, ?_, by rw [Subgroup.card_map_of_injective hf, hcard]⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hsq a ha, map_one]

theorem isE64_comap_of_injective {f : K →* L} (hf : Function.Injective f) {A : Subgroup L}
    (hA : IsE64 A) (hAf : A ≤ f.range) : IsE64 (A.comap f) := by
  obtain ⟨hcomm, hsq, hcard⟩ := hA
  refine ⟨fun a ha b hb => hf ?_, fun a ha => hf ?_, ?_⟩
  · rw [map_mul, map_mul]
    exact hcomm _ ha _ hb
  · rw [map_mul, map_one]
    exact hsq _ ha
  · rw [← Subgroup.card_map_of_injective hf, Subgroup.map_comap_eq_self hAf, hcard]

end E64

theorem exists_sylow_of_hat {G : Type} [Group G] [Finite G] {E B : Subgroup G}
    (φ : ↥B →* ↥Hhat) (hφ : Function.Surjective φ)
    (hker : φ.ker = (oddCoreIn E).subgroupOf B) :
    ∃ T₀ : Subgroup G, T₀ ≤ B ∧ IsPGroup 2 T₀ ∧ Nat.card T₀ = 512 ∧
      (∃ T : Sylow 2 ↥B, (T : Subgroup ↥B) = T₀.subgroupOf B) ∧
      (T₀.subgroupOf B).map φ = S0.subgroupOf Hhat ∧
      (∃ θ : ↥T₀ ≃* ↥S0, ∀ x (hx : x ∈ T₀) (hxB : x ∈ B),
        (θ ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) = φ ⟨x, hxB⟩) ∧
      ∃ A : Subgroup G, A ≤ T₀ ∧ IsE64 A ∧
        (∀ x (hx : x ∈ B), x ∈ A ↔ x ∈ T₀ ∧ (φ ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ A0) ∧
        ∀ A' : Subgroup G, A' ≤ T₀ → IsE64 A' → A' = A := by
  have hkodd : Odd (Nat.card φ.ker) := by
    rw [hker, ← Subgroup.card_map_of_injective B.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
    exact Odd.of_dvd_nat (odd_card_oddCoreIn E) (Subgroup.card_dvd_of_le inf_le_left)
  set S : Subgroup ↥Hhat := S0.subgroupOf Hhat
  have hcardS : Nat.card S = 512 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S0_le_Hhat).toEquiv, card_S0]
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (n := 9) (by rw [hcardS]; norm_num)
  set ψ : ↥(S.comap φ) →* ↥S := φ.subgroupComap S
  have hψ : Function.Surjective ψ := φ.subgroupComap_surjective S hφ
  have hψker : Nat.Coprime (Nat.card ψ.ker) 2 := by
    have hle : ψ.ker.map (S.comap φ).subtype ≤ φ.ker := by
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hx
      rw [MonoidHom.mem_ker]
      exact congrArg (Subtype.val : ↥S → ↥Hhat) hx
    have hdvd : Nat.card ψ.ker ∣ Nat.card φ.ker := by
      rw [← Subgroup.card_map_of_injective (S.comap φ).subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact Nat.coprime_two_right.mpr (Odd.of_dvd_nat hkodd hdvd)
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 ↥(S.comap φ)))
  have hbij := bijective_comp_sylow_subtype ψ hψ hS2 hψker T
  set T₀ : Subgroup G := ((T : Subgroup ↥(S.comap φ)).map (S.comap φ).subtype).map B.subtype
  have hT₀B : T₀ ≤ B := Subgroup.map_subtype_le _
  have hcardT : Nat.card (T : Subgroup ↥(S.comap φ)) = 512 := by
    rw [Nat.card_eq_of_bijective _ hbij, hcardS]
  have hcardT₀ : Nat.card T₀ = 512 := by
    rw [Subgroup.card_map_of_injective B.subtype_injective,
      Subgroup.card_map_of_injective (S.comap φ).subtype_injective, hcardT]
  have hT₀2 : IsPGroup 2 T₀ := IsPGroup.of_card (n := 9) (by rw [hcardT₀]; norm_num)
  have hsub : T₀.subgroupOf B = (T : Subgroup ↥(S.comap φ)).map (S.comap φ).subtype :=
    Subgroup.comap_map_eq_self_of_injective B.subtype_injective _
  have hcardT₀B : Nat.card (T₀.subgroupOf B) = 512 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₀B).toEquiv, hcardT₀]
  have himage : (T₀.subgroupOf B).map φ = S := by
    rw [hsub]
    ext y
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      exact t.2
    · intro hy
      obtain ⟨t, ht⟩ := hbij.2 ⟨y, hy⟩
      exact ⟨t, ⟨t, t.2, rfl⟩, congrArg Subtype.val ht⟩
  have hcardB : Nat.card ↥B = Nat.card φ.ker * 23040 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv, card_Hhat,
      mul_comm]
  have hidx : ¬ 2 ∣ (T₀.subgroupOf B).index := by
    have h := Subgroup.card_mul_index (T₀.subgroupOf B)
    rw [hcardT₀B, hcardB] at h
    obtain ⟨m, hm⟩ := hkodd
    omega
  set f : ↥T₀ →* StatedSp 3 (ZMod 2) := Hhat.subtype.comp (φ.comp (Subgroup.inclusion hT₀B))
  have hf : Function.Injective f := by
    refine (injective_iff_map_eq_one f).mpr fun a ha => ?_
    have hcop : Nat.Coprime (Nat.card (T₀.subgroupOf B)) (Nat.card φ.ker) := by
      rw [hcardT₀B, show (512 : ℕ) = 2 ^ 9 by norm_num]
      exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hkodd)
    have hdis := Subgroup.disjoint_of_coprime_natCard hcop
    have hmem : (⟨a, hT₀B a.2⟩ : ↥B) ∈ T₀.subgroupOf B := a.2
    have hker' : (⟨a, hT₀B a.2⟩ : ↥B) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      exact Subtype.ext ha
    have h1 := Subgroup.disjoint_def.mp hdis hmem hker'
    exact Subtype.ext (congrArg (Subtype.val : ↥B → G) h1)
  have hrange : f.range = S0 := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      have : φ (Subgroup.inclusion hT₀B a) ∈ (T₀.subgroupOf B).map φ :=
        ⟨_, a.2, rfl⟩
      rw [himage] at this
      exact this
    · intro hy
      have hyS : (⟨y, S0_le_Hhat hy⟩ : ↥Hhat) ∈ (T₀.subgroupOf B).map φ := by
        rw [himage]
        exact hy
      obtain ⟨b, hb, hby⟩ := hyS
      exact ⟨⟨b, hb⟩, congrArg Subtype.val hby⟩
  refine ⟨T₀, hT₀B, hT₀2, hcardT₀, ⟨(hT₀2.comap_subtype).toSylow hidx, IsPGroup.toSylow_coe _ _⟩,
    himage, ⟨(MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange),
      fun x hx hxB => rfl⟩, ?_⟩
  set A : Subgroup G := (A0.comap f).map T₀.subtype
  have hA0f : A0 ≤ f.range := hrange ▸ A0_le_S0
  have hAE : IsE64 A :=
    isE64_map_of_injective T₀.subtype_injective (isE64_comap_of_injective hf isE64_A0 hA0f)
  refine ⟨A, Subgroup.map_subtype_le _, hAE, fun x hx => ?_, fun A' hA'T hA' => ?_⟩
  · constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.2, ha⟩
    · rintro ⟨hxT, hxA⟩
      exact ⟨⟨x, hxT⟩, hxA, rfl⟩
  ·
    have hA'' : IsE64 (A'.comap T₀.subtype) :=
      isE64_comap_of_injective T₀.subtype_injective hA' (by rw [Subgroup.range_subtype]; exact hA'T)
    have himg := eq_A0_of_isE64 _ (by rw [← hrange]; exact Subgroup.map_le_range f _)
      (isE64_map_of_injective hf hA'')
    have hle : A' ≤ A := by
      intro x hx
      refine ⟨⟨x, hA'T hx⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, ← himg]
      exact ⟨⟨x, hA'T hx⟩, hx, rfl⟩
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hAE.2.2, hA'.2.2])

end CFSG.ClassicalInvolution.Sp62Rec
