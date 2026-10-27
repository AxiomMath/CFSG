module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubAbstract
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open Subgroup

section General

variable {Q : Type} [Group Q] {ι : Type} [DecidableEq ι] {G : ι → Type} [∀ j, Group (G j)]

@[expose] def blockEmbOf (S : ∀ j, Subgroup (G j)) (j₀ : ι) : ↥(S j₀) →* ∀ j, G j :=
  (MonoidHom.mulSingle G j₀).comp (S j₀).subtype

@[expose] def blockPreOf (β : Q →* ∀ j, G j) (S : ∀ j, Subgroup (G j)) (j₀ : ι) : Subgroup Q :=
  (blockEmbOf S j₀).range.comap β

theorem apply_of_mem_blockPreOf {β : Q →* ∀ j, G j} {S : ∀ j, Subgroup (G j)} {j₀ : ι} {y : Q}
    (hy : y ∈ blockPreOf β S j₀) {j : ι} (hj : j ≠ j₀) : β y j = 1 := by
  obtain ⟨x, hx⟩ := hy
  rw [← hx]
  simp [blockEmbOf, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj]

theorem apply_mem_of_mem_blockPreOf {β : Q →* ∀ j, G j} {S : ∀ j, Subgroup (G j)} {j₀ : ι}
    {y : Q} (hy : y ∈ blockPreOf β S j₀) : β y j₀ ∈ S j₀ := by
  obtain ⟨x, hx⟩ := hy
  have : β y j₀ = (x : G j₀) := by
    rw [← hx]
    simp [blockEmbOf]
  rw [this]
  exact x.2

@[expose] noncomputable def blockHomOf (β : Q →* ∀ j, G j) (S : ∀ j, Subgroup (G j)) (j₀ : ι) :
    ↥(blockPreOf β S j₀) →* ↥(S j₀) :=
  ((Pi.evalMonoidHom G j₀).comp (β.comp (blockPreOf β S j₀).subtype)).codRestrict (S j₀)
    fun y => apply_mem_of_mem_blockPreOf y.2

theorem coe_blockHomOf {β : Q →* ∀ j, G j} {S : ∀ j, Subgroup (G j)} {j₀ : ι}
    (y : ↥(blockPreOf β S j₀)) : ((blockHomOf β S j₀ y : ↥(S j₀)) : G j₀) = β y j₀ := rfl

theorem blockHomOf_surjective {β : Q →* ∀ j, G j} {S : ∀ j, Subgroup (G j)}
    (hS : Subgroup.pi Set.univ S ≤ β.range) (j₀ : ι) :
    Function.Surjective (blockHomOf β S j₀) := by
  intro x
  have hmem : blockEmbOf S j₀ x ∈ β.range := by
    apply hS
    rw [Subgroup.mem_pi]
    intro b _
    by_cases hb : b = j₀
    · subst hb
      simpa [blockEmbOf] using x.2
    · simp [blockEmbOf, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hb, one_mem]
  obtain ⟨q, hq⟩ := hmem
  refine ⟨⟨q, ⟨x, hq.symm⟩⟩, Subtype.ext ?_⟩
  rw [coe_blockHomOf, hq]
  simp [blockEmbOf]

theorem isPGroup_ker_blockHomOf {β : Q →* ∀ j, G j} (hker : IsPGroup 2 β.ker)
    (S : ∀ j, Subgroup (G j)) (j₀ : ι) : IsPGroup 2 (blockHomOf β S j₀).ker := by
  have hk : ∀ y : ↥(blockPreOf β S j₀), blockHomOf β S j₀ y = 1 → (y : Q) ∈ β.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    funext b
    by_cases hb : b = j₀
    · subst hb
      have := congrArg (fun z : ↥(S b) => (z : G b)) hy
      simpa [coe_blockHomOf] using this
    · simpa using apply_of_mem_blockPreOf y.2 hb
  let φ : (blockHomOf β S j₀).ker →* β.ker :=
    (((blockPreOf β S j₀).subtype.comp (blockHomOf β S j₀).ker.subtype)).codRestrict β.ker
      fun y => hk y.1 y.2
  have hinj : Function.Injective φ := by
    intro y z h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : ↥β.ker => (w : Q)) h
  exact IsPGroup.of_injective hker φ hinj

theorem exists_levi_section_of_blocks [Finite Q] {β : Q →* ∀ j, G j} (hker : IsPGroup 2 β.ker)
    {S : ∀ j, Subgroup (G j)} (hS : Subgroup.pi Set.univ S ≤ β.range) (j₀ : ι)
    (hq : CFSG.Open.IsQuasisimple ↥(S j₀)) {A : Type} [Group A] (ρ : Q →* A)
    (hinj : ∀ y ∈ blockPreOf β S j₀, ρ y = 1 → y = 1) :
    ∃ Y W : Subgroup A, Y ≤ ρ.range ∧ S622IsSimpleSection Y W ∧
      W.relIndex Y = Nat.card (↥(S j₀) ⧸ Subgroup.center ↥(S j₀)) ∧
      ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥(S j₀)) →
        ¬ r ∣ Nat.card W := by
  classical
  set ρ' : ↥(blockPreOf β S j₀) →* A := ρ.comp (blockPreOf β S j₀).subtype with hρ'
  have hρ'inj : Function.Injective ρ' := by
    rw [injective_iff_map_eq_one]
    intro y hy
    exact Subtype.ext (hinj y y.2 hy)
  let eY : ↥(blockPreOf β S j₀) ≃* ↥ρ'.range := MonoidHom.ofInjective hρ'inj
  haveI : Finite ↥(blockPreOf β S j₀) := inferInstance
  haveI : Finite ↥ρ'.range := Finite.of_surjective _ ρ'.rangeRestrict_surjective
  let θ : ↥(blockPreOf β S j₀) →* ↥(S j₀) ⧸ Subgroup.center ↥(S j₀) :=
    (QuotientGroup.mk' (Subgroup.center ↥(S j₀))).comp (blockHomOf β S j₀)
  let θ' : ↥ρ'.range →* ↥(S j₀) ⧸ Subgroup.center ↥(S j₀) := θ.comp eY.symm.toMonoidHom
  have hθ' : Function.Surjective θ' :=
    ((QuotientGroup.mk'_surjective _).comp (blockHomOf_surjective hS j₀)).comp eY.symm.surjective
  haveI : IsSimpleGroup (↥(S j₀) ⧸ Subgroup.center ↥(S j₀)) := hq.2
  have hsec := S622IsSimpleSection.of_surjective θ' hθ'
    (CFSG.AGLEmbedding.LeviBlock.exists_noncomm_centerQuotient hq)
  refine ⟨ρ'.range, θ'.ker.map ρ'.range.subtype, ?_, hsec, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨((y : ↥(blockPreOf β S j₀)) : Q), rfl⟩
  · have h1 := Subgroup.relIndex_map_map_of_injective θ'.ker ⊤ ρ'.range.subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype, Subgroup.relIndex_top_right] at h1
    rw [h1, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hθ', Subgroup.card_top]
  · intro r hr hr2 hrZ hdvd
    rw [Subgroup.card_map_of_injective ρ'.range.subtype_injective] at hdvd
    haveI : Fact r.Prime := ⟨hr⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥θ'.ker) r hdvd
    set w : ↥ρ'.range := z.1 with hw
    set y : ↥(blockPreOf β S j₀) := eY.symm w with hy
    have hyker : y ∈ θ.ker := z.2
    have hordy : orderOf y = r := by
      rw [hy, MulEquiv.orderOf_eq, hw, Subgroup.orderOf_coe, hz]
    have hyc : blockHomOf β S j₀ y ∈ Subgroup.center ↥(S j₀) :=
      (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hyker)
    have hyr : (blockHomOf β S j₀ y) ^ r = 1 := by
      rw [← map_pow, ← hordy, pow_orderOf_eq_one, map_one]
    set u : ↥(Subgroup.center ↥(S j₀)) := ⟨blockHomOf β S j₀ y, hyc⟩ with hu
    have hur : u ^ r = 1 := Subtype.ext (by simpa [hu] using hyr)
    have hdvd1 : orderOf u ∣ r := orderOf_dvd_of_pow_eq_one hur
    have hdvd2 : orderOf u ∣ Nat.card (Subgroup.center ↥(S j₀)) := orderOf_dvd_natCard u
    rcases (Nat.dvd_prime hr).1 hdvd1 with h1 | h1
    · have hu1 : u = 1 := orderOf_eq_one_iff.1 h1
      have hyk : y ∈ (blockHomOf β S j₀).ker := by
        rw [MonoidHom.mem_ker]
        exact congrArg Subtype.val hu1
      obtain ⟨k, hk⟩ := isPGroup_ker_blockHomOf hker S j₀ ⟨y, hyk⟩
      have hyk2 : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have hr2k : r ∣ 2 ^ k := hordy ▸ orderOf_dvd_of_pow_eq_one hyk2
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hr2k))
    · exact hrZ (h1 ▸ hdvd2)

end General

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
