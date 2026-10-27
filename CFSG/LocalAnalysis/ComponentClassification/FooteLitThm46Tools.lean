module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitFooteM

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem commutator_le_inf_of_le_normalizer {A B : Subgroup G} (hAB : A ≤ normalizer (B : Set G))
    (hBA : B ≤ normalizer (A : Set G)) : ⁅A, B⁆ ≤ A ⊓ B := by
  rw [commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  refine mem_inf.mpr ⟨?_, ?_⟩
  · rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
    exact mul_mem ha ((mem_normalizer_iff.mp (hBA hb) _).mp (inv_mem ha))
  · exact mul_mem ((mem_normalizer_iff.mp (hAB ha) _).mp hb) (inv_mem hb)

theorem commutator_eq_of_cover {M X : Subgroup G} (hXM : X ≤ M) (hX : X ≤ oddResidualIn X)
    (hcov : M ≤ X ⊔ oddCoreIn M) (hMp : ⁅M, M⁆ = M) : ⁅X, X⁆ = X := by
  set π := QuotientGroup.mk' (pPrimeCore 2 M) with hπ
  have hX' : (X.subgroupOf M).map π = ⊤ := by
    refine eq_top_iff.mpr fun q _ => ?_
    obtain ⟨⟨m, hm⟩, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 M) q
    have hXO : X ≤ normalizer ((oddCoreIn M : Subgroup G) : Set G) := fun x hx =>
      mem_normalizer_oddCoreIn (le_normalizer (hXM hx))
    have hm' := hcov hm
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right X (oddCoreIn M) hXO] at hm'
    obtain ⟨x, hx, o, ho, hxo⟩ := hm'
    obtain ⟨o', ho', rfl⟩ := mem_map.mp ho
    refine ⟨⟨x, hXM hx⟩, hx, ?_⟩
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have e1 : (⟨x, hXM hx⟩ : M)⁻¹ * ⟨m, hm⟩ = o' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hxo]
      simp
    rw [e1]
    exact ho'
  have hMtop : ⁅(⊤ : Subgroup M), (⊤ : Subgroup M)⁆ = ⊤ := by
    apply map_injective M.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    exact hMp
  have hbar : ⁅(⊤ : Subgroup (M ⧸ pPrimeCore 2 M)), (⊤ : Subgroup (M ⧸ pPrimeCore 2 M))⁆ = ⊤ := by
    have h1 := congrArg (map π) hMtop
    rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, QuotientGroup.range_mk'] at h1
  have hcomm : (⁅X.subgroupOf M, X.subgroupOf M⁆).map π = ⊤ := by
    rw [Subgroup.map_commutator, hX', hbar]
  have hXc : X ≤ ⁅X, X⁆ ⊔ oddCoreIn M := by
    intro x hx
    have h1 : π ⟨x, hXM hx⟩ ∈ (⁅X.subgroupOf M, X.subgroupOf M⁆).map π := hcomm ▸ mem_top _
    obtain ⟨⟨c, hcM⟩, hc, hcx⟩ := mem_map.mp h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hcx
    have hc' : c ∈ ⁅X, X⁆ := by
      have h2 := mem_map_of_mem M.subtype hc
      rwa [Subgroup.map_commutator, map_subgroupOf_eq_of_le hXM] at h2
    rw [show x = c * (c⁻¹ * x) by group]
    exact mul_mem (mem_sup_left hc') (mem_sup_right ⟨_, hcx, by simp⟩)
  apply le_antisymm (commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb))
  refine hX.trans ((closure_le _).mpr fun g hg => ?_)
  obtain ⟨hgX, h2⟩ := hg
  have hCX : ⁅X, X⁆ ≤ X := commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hCO : ⁅X, X⁆ ≤ normalizer ((oddCoreIn M : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_oddCoreIn (le_normalizer (hXM (hCX hx)))
  have hg' := hXc hgX
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ (oddCoreIn M) hCO] at hg'
  obtain ⟨c, hc, o, ho, hco⟩ := hg'
  have hoX : o ∈ X := by
    have h3 : o = c⁻¹ * g := by rw [← hco]; group
    rw [h3]
    exact mul_mem (inv_mem (hCX hc)) hgX
  set A := X ⊓ oddCoreIn M with hA
  have hAodd : Odd (Nat.card A) :=
    Odd.of_dvd_nat (odd_card_oddCoreIn M) (card_dvd_of_le inf_le_right)
  have hAN : A ≤ normalizer ((⁅X, X⁆ : Subgroup G) : Set G) := by
    intro a ha
    apply mem_normalizer_of_map_conj_eq
    rw [Subgroup.map_commutator, map_conj_eq_self_of_mem (mem_inf.mp ha).1]
  have hgsup : g ∈ A ⊔ ⁅X, X⁆ := by
    rw [← hco]
    exact mul_mem (mem_sup_right hc) (mem_sup_left (mem_inf.mpr ⟨hoX, ho⟩))
  exact mem_of_two_element_of_mem_sup hAN
    (by rw [oddResidualIn_eq_bot_of_odd hAodd]; exact bot_le) hgsup h2

theorem isSylowOf_of_cover {M X T : Subgroup G} (hXM : X ≤ M) (hcov : M ≤ X ⊔ oddCoreIn M)
    (hT : IsSylowOf 2 T X) : IsSylowOf 2 T M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff] at hT ⊢
  obtain ⟨hTX, hTp, hTi⟩ := hT
  refine ⟨hTX.trans hXM, hTp, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex T X M hTX hXM]
  intro h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h3 | h3
  · exact hTi h3
  ·
    set N := pPrimeCore 2 M with hN
    have hsup : N ⊔ X.subgroupOf M = ⊤ := by
      apply map_injective M.subtype_injective
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hXM, ← MonoidHom.range_eq_map, range_subtype]
      exact le_antisymm (sup_le (map_subtype_le _) hXM)
        (hcov.trans (by rw [sup_comm]; exact le_rfl))
    have h4 := relIndex_sup_eq_relIndex_of_normal N (X.subgroupOf M)
    rw [hsup] at h4
    have h5 : X.relIndex M = (X.subgroupOf M).relIndex N := by
      rw [← h4, Subgroup.relIndex_top_right]
      rfl
    rw [h5] at h3
    have h6 : (X.subgroupOf M).relIndex N ∣ Nat.card N := Subgroup.relIndex_dvd_card _ _
    have h7 := Nat.Coprime.coprime_dvd_right h6 (pPrimeCore_coprime_card (p := 2) (G := ↥M))
    exact absurd (Nat.Coprime.eq_one_of_dvd h7 h3) (by norm_num)

theorem isSylowOf_map_conj {T Y : Subgroup G} (hT : IsSylowOf 2 T Y) (g : G) :
    IsSylowOf 2 (T.map (MulAut.conj g).toMonoidHom) (Y.map (MulAut.conj g).toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowOf_of_card (map_mono hT.le) ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
    Subgroup.card_map_of_injective (MulAut.conj g).injective, hT.card_eq]

theorem exists_sylow_mulEquiv_of_isSylowOf (h : FooteSec4 G L) {M P : Subgroup G}
    (hM : IsFooteM L M) (hP : IsSylowOf 2 P M) :
    ∃ Q : Sylow 2 (L ⧸ Open.fusionZStar L),
      Nonempty ((Q : Subgroup (L ⧸ Open.fusionZStar L)) ≃* P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨ε⟩⟩ := hM.quotient h
  set f : M →* L ⧸ Open.fusionZStar L :=
    ε.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 M)) with hf
  have hfs : Function.Surjective f := ε.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨Q₀, rfl⟩ := hP
  refine ⟨Q₀.mapSurjective hfs, ⟨?_⟩⟩
  have hinj : Function.Injective (f.comp (Q₀ : Subgroup M).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hf, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, map_eq_one_iff _ ε.injective, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    apply Subtype.ext
    have h1 := eq_bot_of_le_two_group_of_le_odd Q₀.isPGroup' (pPrimeCore_coprime_card (p := 2)
      (G := ↥M) |>.symm |> fun h => (Nat.coprime_two_right.mp h)) (zpowers_le.mpr x.2)
      (zpowers_le.mpr hx)
    rw [zpowers_eq_bot] at h1
    exact h1
  have hrange : (f.comp (Q₀ : Subgroup M).subtype).range = (Q₀ : Subgroup M).map f := by
    rw [MonoidHom.range_comp, range_subtype]
  exact (MulEquiv.subgroupCongr hrange).symm.trans ((MonoidHom.ofInjective hinj).symm.trans
    ((Q₀ : Subgroup M).equivMapOfInjective M.subtype M.subtype_injective))

end CFSG.ComponentClassification.FooteLit
