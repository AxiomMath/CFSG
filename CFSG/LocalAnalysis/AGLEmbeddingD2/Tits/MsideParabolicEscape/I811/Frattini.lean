module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.CoreSylow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.AGL81I811Reduction

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811

open CFSG.Open CFSG.AGLEmbeddingD2

theorem isCyclic_of_stronglyEmbedded {G : Type} [Group G] [Finite G] {M H : Subgroup G}
    (hstr : GLBStronglyEmbedded 3 M)
    (hcyc : ∀ X : Subgroup G, X ≤ H ⊓ M → IsPGroup 3 X → IsCyclic X)
    (h3 : 3 ∣ Nat.card (H ⊓ M : Subgroup G)) :
    ∀ X : Subgroup ↥H, IsPGroup 3 X → IsCyclic X := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 3 ↥(H ⊓ M)) := inferInstance
  set ι := Subgroup.inclusion (inf_le_left : H ⊓ M ≤ H) with hι
  have hιinj : Function.Injective ι := Subgroup.inclusion_injective _
  set P₁ : Subgroup ↥H := (Q : Subgroup ↥(H ⊓ M)).map ι with hP₁
  set n := (Nat.card ↥(H ⊓ M)).factorization 3 with hn
  have hP₁card : Nat.card P₁ = 3 ^ n := by
    rw [hP₁, Subgroup.card_map_of_injective hιinj, Sylow.card_eq_multiplicity]
  have hn1 : 1 ≤ n := by
    rw [hn]
    exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three Nat.card_pos.ne').mp h3
  have hP₁M : P₁.map H.subtype ≤ H ⊓ M := by
    rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
    exact y.2
  have hP₁3 : IsPGroup 3 P₁ := Q.isPGroup'.map ι
  have hP₁ne : P₁.map H.subtype ≠ ⊥ := by
    intro h
    have : Nat.card (P₁.map H.subtype) = 1 := by rw [h, Subgroup.card_bot]
    rw [Subgroup.card_map_of_injective H.subtype_injective, hP₁card] at this
    have : 3 ^ n ≥ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
    omega
  have hN : (Subgroup.normalizer (P₁ : Set ↥H)).map H.subtype ≤ H ⊓ M := by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨g.2, ?_⟩
    refine normalizer_le_of_stronglyEmbedded Nat.prime_three hstr (hP₁3.map _)
      (hP₁M.trans inf_le_right) hP₁ne ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg y).mp hy, by simp⟩
    · rintro ⟨y, hy, hyx⟩
      refine ⟨g⁻¹ * y * g, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp hy
        simpa using this
      · have : (y : G) = (g : G) * x * (g : G)⁻¹ := hyx
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, this]
        group
  have hnot : ¬ 3 ^ (n + 1) ∣ Nat.card ↥H := by
    intro hdvd
    have h1 := Sylow.prime_pow_dvd_card_normalizer hdvd hP₁card
    have h2 : Nat.card (Subgroup.normalizer (P₁ : Set ↥H)) ∣ Nat.card ↥(H ⊓ M) := by
      rw [← Subgroup.card_map_of_injective H.subtype_injective]
      exact Subgroup.card_dvd_of_le hN
    exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' Nat.prime_three (h1.trans h2)
  have hfac : (Nat.card ↥H).factorization 3 = n := by
    have hdvd : 3 ^ n ∣ Nat.card ↥H := hP₁card ▸ Subgroup.card_subgroup_dvd_card P₁
    have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp hdvd
    have h2 : ¬ n + 1 ≤ (Nat.card ↥H).factorization 3 := fun h =>
      hnot ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mpr h)
    omega
  let S₁ : Sylow 3 ↥H := Sylow.ofCard P₁ (by rw [hP₁card, hfac])
  intro X hX
  obtain ⟨P, hXP⟩ := hX.exists_le_sylow
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq ↥H P S₁
  have hXb : X.map (MulAut.conj b).toMonoidHom ≤ P₁ := by
    have h := Subgroup.map_mono (f := (MulAut.conj b).toMonoidHom) hXP
    have hP : (P : Subgroup ↥H).map (MulAut.conj b).toMonoidHom = P₁ := by
      have := congrArg (fun S : Sylow 3 ↥H => (S : Subgroup ↥H)) hb
      simp only [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at this
      exact this
    rwa [hP] at h
  have hcycG : IsCyclic ↥((X.map (MulAut.conj b).toMonoidHom).map H.subtype) :=
    hcyc _ ((Subgroup.map_mono hXb).trans hP₁M) ((hX.map _).map _)
  have e1 : ↥X ≃* ↥((X.map (MulAut.conj b).toMonoidHom).map H.subtype) :=
    (X.equivMapOfInjective _ (MulAut.conj b).injective).trans
      (Subgroup.equivMapOfInjective _ _ H.subtype_injective)
  exact isCyclic_of_surjective e1.symm.toMonoidHom e1.symm.surjective

theorem normalizer_map_le_map_normalizer {B : Type} [Group B] [Finite B] (O : Subgroup B)
    [O.Normal] (hO : ¬ 3 ∣ Nat.card O) {A : Subgroup B} (hA : Nat.card A = 3) :
    Subgroup.normalizer ((A.map (QuotientGroup.mk' O) : Subgroup (B ⧸ O)) : Set (B ⧸ O)) ≤
      (Subgroup.normalizer (A : Set B)).map (QuotientGroup.mk' O) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' O with hπ
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective O x
  set D := A ⊔ O with hD
  have hAO : A ⊓ O = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have h1 : Nat.card (A ⊓ O : Subgroup B) ∣ 3 := hA ▸ Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (A ⊓ O : Subgroup B) ∣ Nat.card O := Subgroup.card_dvd_of_le inf_le_right
    have h3 : Nat.card (A ⊓ O : Subgroup B) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
      · exact h
      · exact absurd (h ▸ h2) hO
    exact (Subgroup.card_eq_one.mp h3) ▸ hy
  have hDcard : Nat.card D = 3 * Nat.card O := by
    have h1 := Subgroup.relIndex_sup_right A O
    have h2 := Subgroup.relIndex_mul_card O D
    rw [inf_of_le_left le_sup_right] at h2
    have h3 := Subgroup.relIndex_mul_card O A
    rw [inf_comm, hAO, Subgroup.card_bot, mul_one, hA] at h3
    rw [← h2, h1, h3, mul_comm]
  have hDfac : (Nat.card D).factorization 3 = 1 := by
    rw [hDcard, Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd hO]
  have hAg : A.map (MulAut.conj g).toMonoidHom ≤ D := by
    rintro _ ⟨a, ha, rfl⟩
    have hmem : π (g * a * g⁻¹) ∈ A.map π := by
      have := (Subgroup.mem_normalizer_iff.mp hx (π a)).mp ⟨a, ha, rfl⟩
      simpa [hπ] using this
    obtain ⟨a', ha', he⟩ := hmem
    have hz : a'⁻¹ * (g * a * g⁻¹) ∈ O := by
      rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker, map_mul, map_inv, ← hπ, he,
        inv_mul_cancel]
    have : g * a * g⁻¹ = a' * (a'⁻¹ * (g * a * g⁻¹)) := by group
    change g * a * g⁻¹ ∈ D
    rw [this]
    exact D.mul_mem (Subgroup.mem_sup_left ha') (Subgroup.mem_sup_right hz)
  have hAD : A ≤ D := le_sup_left
  let SA : Sylow 3 ↥D := Sylow.ofCard (A.subgroupOf D) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAD).toEquiv, hA, hDfac, pow_one])
  let SAg : Sylow 3 ↥D := Sylow.ofCard ((A.map (MulAut.conj g).toMonoidHom).subgroupOf D) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAg).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, hA, hDfac, pow_one])
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq ↥D SA SAg
  have hyA : A.map (MulAut.conj (y : B)).toMonoidHom = A.map (MulAut.conj g).toMonoidHom := by
    have h : ((y • SA : Sylow 3 ↥D) : Subgroup ↥D) = (SAg : Subgroup ↥D) := by rw [hy]
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    change Subgroup.map (MulAut.conj y).toMonoidHom (A.subgroupOf D) =
      (A.map (MulAut.conj g).toMonoidHom).subgroupOf D at h
    have hle : A.map (MulAut.conj (y : B)).toMonoidHom ≤ A.map (MulAut.conj g).toMonoidHom := by
      rintro _ ⟨a, ha, rfl⟩
      have hmem : (MulAut.conj y).toMonoidHom ⟨a, hAD ha⟩ ∈
          (A.map (MulAut.conj g).toMonoidHom).subgroupOf D := h ▸ ⟨⟨a, hAD ha⟩, ha, rfl⟩
      exact hmem
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective (MulAut.conj (y : B)).injective]
  have hn : (y : B)⁻¹ * g ∈ Subgroup.normalizer (A : Set B) := by
    rw [Subgroup.mem_normalizer_iff_conj_image_eq]
    have h1 := congrArg (Subgroup.map (MulAut.conj (y : B)⁻¹).toMonoidHom) hyA
    rw [Subgroup.map_map, Subgroup.map_map] at h1
    have h2 : ((MulAut.conj (y : B)⁻¹).toMonoidHom.comp (MulAut.conj (y : B)).toMonoidHom) =
        MonoidHom.id B := by
      ext z
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rw [h2, Subgroup.map_id] at h1
    have h3 : ((MulAut.conj (y : B)⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) =
        (MulAut.conj ((y : B)⁻¹ * g)).toMonoidHom := by
      ext z
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [h3] at h1
    have := congrArg (fun H : Subgroup B => (H : Set B)) h1
    simpa [Subgroup.coe_map] using this.symm
  have hyπ : π (y : B) ∈ (Subgroup.normalizer (A : Set B)).map π := by
    have : π (y : B) ∈ (A ⊔ O).map π := ⟨y, y.2, rfl⟩
    rw [Subgroup.map_sup, hπ, QuotientGroup.map_mk'_self, sup_bot_eq] at this
    exact Subgroup.map_mono Subgroup.le_normalizer this
  have : g = (y : B) * ((y : B)⁻¹ * g) := by group
  rw [this, map_mul]
  exact Subgroup.mul_mem _ hyπ ⟨_, hn, rfl⟩

theorem sup_normalizer_eq_top {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} [K.Normal]
    (hcyc : ∀ X : Subgroup Y, IsPGroup 3 X → IsCyclic X)
    (hK3 : ∀ X : Subgroup Y, Nat.card X = 3 → X ≤ K) {A : Subgroup Y} (hA : Nat.card A = 3) :
    K ⊔ Subgroup.normalizer (A : Set Y) = ⊤ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAK : A ≤ K := hK3 A hA
  have hAp : IsPGroup 3 (A.subgroupOf K) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hA, pow_one]
  obtain ⟨P, hAP⟩ := hAp.exists_le_sylow
  set P₀ := (P : Subgroup ↥K).map K.subtype with hP₀
  have hAP₀ : A ≤ P₀ := by
    intro a ha
    exact ⟨⟨a, hAK ha⟩, hAP ha, rfl⟩
  have hP₀3 : IsPGroup 3 P₀ := P.isPGroup'.map _
  have hP₀c : IsCyclic ↥P₀ := hcyc P₀ hP₀3
  have hNP : Subgroup.normalizer (P₀ : Set Y) ≤ Subgroup.normalizer (A : Set Y) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_conj_image_eq]
    have hAg : A.map (MulAut.conj g).toMonoidHom ≤ P₀ := by
      rw [← map_conj_eq_of_mem_normalizer' hg]
      exact Subgroup.map_mono hAP₀
    have hcomm : A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (A : Set Y) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hc := (IsCyclic.isMulCommutative (α := ↥P₀)).is_comm.comm
        ⟨a, hAP₀ ha⟩ ⟨x, hAg hx⟩
      exact congrArg Subtype.val hc
    have heq := CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.eq_of_card_three_of_le_normalizer
      (B := P₀) (fun X _ hX => hcyc X hX) hAP₀ hAg hA
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hA]) hcomm
    have := congrArg (fun H : Subgroup Y => (H : Set Y)) heq
    simpa [Subgroup.coe_map] using this
  have hF := Sylow.normalizer_sup_eq_top (p := 3) (N := K) P
  rw [eq_top_iff, ← hF, sup_comm]
  exact sup_le_sup_left hNP K

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811
