module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Basic
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.Open Subgroup

theorem index_eq_relIndex_of_sup {X : Type*} [Group X] [Finite X] {K M : Subgroup X} [K.Normal]
    (h : K ⊔ M = ⊤) : M.index = M.relIndex K := by
  have h1 : M.relIndex K * K.index = (M ⊓ K).index := by
    have := relIndex_inf_mul_relIndex M K ⊤
    simpa [Subgroup.relIndex_top_right, inf_top_eq] using this
  have h2 : (M ⊓ K).relIndex M * M.index = (M ⊓ K).index := relIndex_mul_index inf_le_left
  have h3 : (M ⊓ K).relIndex M = K.relIndex M := by
    rw [inf_comm]; exact inf_relIndex_right K M
  have h4 : K.relIndex M = K.index := by
    have := relIndex_sup_right (H := M) (K := K)
    rw [sup_comm, h, relIndex_top_right] at this
    exact this.symm
  have hK : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [h3, h4] at h2
  have h5 : M.relIndex K * K.index = M.index * K.index := by rw [h1, ← h2, mul_comm]
  exact (Nat.eq_of_mul_eq_mul_right hK h5).symm

theorem le_of_not_dvd_index {X : Type*} [Group X] [Finite X] {K P : Subgroup X} [K.Normal]
    (hP : IsPGroup 3 P) (h : ¬ 3 ∣ K.index) : P ≤ K := by
  intro p hp
  obtain ⟨a, ha⟩ := hP ⟨p, hp⟩
  have h1 : orderOf (QuotientGroup.mk p : X ⧸ K) ∣ 3 ^ a := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow]
    have : p ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
    rw [this]; rfl
  have h2 : orderOf (QuotientGroup.mk p : X ⧸ K) ∣ K.index := by
    rw [Subgroup.index_eq_card]; exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (3 ^ a) K.index :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h)
  have : orderOf (QuotientGroup.mk p : X ⧸ K) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact (QuotientGroup.eq_one_iff p).mp (orderOf_eq_one_iff.mp this)

theorem sup_eq_top_of_stronglyEmbedded {X : Type*} [Group X] [Finite X] {K M : Subgroup X}
    [K.Normal] (hM : GLBStronglyEmbedded 3 M) (P : Sylow 3 X) (hPM : (P : Subgroup X) ≤ M)
    (hK3 : 3 ∣ Nat.card K) : K ⊔ M = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 ↥K) := inferInstance
  set R : Subgroup X := (S : Subgroup ↥K).map K.subtype with hR
  have hR3 : IsPGroup 3 R := S.isPGroup'.map _
  have hRK : R ≤ K := Subgroup.map_subtype_le _
  have hRcard : 3 ∣ Nat.card R := by
    have h1 : Nat.card R = Nat.card S :=
      (Nat.card_congr (Subgroup.equivMapOfInjective (S : Subgroup ↥K) K.subtype
        K.subtype_injective).toEquiv).symm
    rw [h1, Sylow.card_eq_multiplicity]
    have : 1 ≤ (Nat.card K).factorization 3 :=
      (Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' hK3)
    exact dvd_pow_self 3 (by omega)
  obtain ⟨P₁, hRP₁⟩ := hR3.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P P₁
  have hP₁ : (P₁ : Subgroup X) = (P : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]; rfl
  have hconj : ∀ r ∈ R, g⁻¹ * r * g ∈ (P : Subgroup X) := by
    intro r hr
    have := hRP₁ hr
    rw [hP₁] at this
    obtain ⟨q, hq, hqr⟩ := this
    have : g⁻¹ * r * g = q := by
      have : g * q * g⁻¹ = r := hqr
      rw [← this]; group
    rw [this]; exact hq
  have hfrat := Sylow.normalizer_sup_eq_top S
  set R' : Subgroup X := R.map (MulAut.conj g⁻¹).toMonoidHom with hR'
  have hmemR' : ∀ y : X, y ∈ R' ↔ g * y * g⁻¹ ∈ R := by
    intro y
    constructor
    · rintro ⟨r, hr, rfl⟩
      simpa [mul_assoc] using hr
    · intro hy
      exact ⟨g * y * g⁻¹, hy, by simp [mul_assoc]⟩
  have hN : ∀ n ∈ Subgroup.normalizer (R : Set X), g⁻¹ * n * g ∈ M := by
    intro n hn
    have hR'P : R' ≤ M := by
      rintro _ ⟨r, hr, rfl⟩
      exact hPM (by simpa [MulAut.conj_apply] using hconj r hr)
    have hR'3 : 3 ∣ Nat.card R' := by
      have : Nat.card R' = Nat.card R :=
        (Nat.card_congr (Subgroup.equivMapOfInjective R (MulAut.conj g⁻¹).toMonoidHom
          (MulAut.conj g⁻¹).injective).toEquiv).symm
      rw [this]; exact hRcard
    have hnR' : g⁻¹ * n * g ∈ Subgroup.normalizer (R' : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [hmemR', hmemR']
      have := Subgroup.mem_normalizer_iff.mp hn (g * y * g⁻¹)
      have e : g * (g⁻¹ * n * g * y * (g⁻¹ * n * g)⁻¹) * g⁻¹ = n * (g * y * g⁻¹) * n⁻¹ := by group
      rw [e]
      exact this
    exact normalizer_le_of_stronglyEmbedded hM hR'P hR'3 hnR'
  refine eq_top_iff.mpr fun w _ => ?_
  have hz : g * w * g⁻¹ ∈ ((Subgroup.normalizer (R : Set X) ⊔ K : Subgroup X) : Set X) := by
    rw [hfrat]; exact Subgroup.mem_top _
  rw [Subgroup.mul_normal] at hz
  obtain ⟨n, hn, k, hk, hnk⟩ := hz
  have hw : w = (g⁻¹ * n * g) * (g⁻¹ * k * g) := by
    have : w = g⁻¹ * (g * w * g⁻¹) * g := by group
    rw [this, ← hnk]; group
  rw [hw, sup_comm]
  refine Subgroup.mul_mem_sup (hN n hn) ?_
  have := (inferInstance : K.Normal).conj_mem k hk g⁻¹
  simpa using this

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
