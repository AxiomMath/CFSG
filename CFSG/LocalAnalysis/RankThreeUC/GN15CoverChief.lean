module

public import CFSG.LocalAnalysis.RankThreeUC.GN15Climb

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
private theorem mem_normalizer_of_normal' {B : Subgroup X} (hB : B.Normal) (g : X) :
    g ∈ Subgroup.normalizer (B : Set X) := by
  rw [Subgroup.normalizer_eq_top_iff.mpr hB]
  exact Subgroup.mem_top g

theorem forall_pow_mem_of_chief_of_pSection {r : ℕ} [Fact r.Prime] {A B R : Subgroup X}
    (hA : A.Normal) (hB : B.Normal) (hBA : B ≤ A)
    (hchief : ∀ D : Subgroup X, D.Normal → B ≤ D → D ≤ A → D = B ∨ D = A)
    (hRA : R ≤ A) (hAR : A ≤ Subgroup.normalizer (R : Set X))
    (hR : ∀ x ∈ R, ∃ k : ℕ, x ^ r ^ k ∈ B) (hne : ¬ R ≤ B) :
    ∀ a ∈ A, ∃ k : ℕ, a ^ r ^ k ∈ B := by
  set π : X →* X ⧸ B := QuotientGroup.mk' B with hπ
  set Ab : Subgroup (X ⧸ B) := A.map π with hAb
  set Rb : Subgroup (X ⧸ B) := R.map π with hRb
  have hRbA : Rb ≤ Ab := Subgroup.map_mono hRA
  have hAbn : Ab ≤ Subgroup.normalizer (Rb : Set (X ⧸ B)) := by
    rintro _ ⟨a, ha, rfl⟩
    exact Subgroup.le_normalizer_map π ⟨a, hAR ha, rfl⟩
  have hRbp : IsPGroup r Rb := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    obtain ⟨k, hk⟩ := hR x hx
    refine ⟨k, Subtype.ext ?_⟩
    show (π x) ^ r ^ k = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hk
  have hRP : Rb ≤ CFSG.Open.pCoreOf r Ab :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer r hRbA hAbn hRbp
  set P : Subgroup (X ⧸ B) := CFSG.Open.pCoreOf r Ab with hP
  have hAbnorm : Ab.Normal := Subgroup.Normal.map hA π (QuotientGroup.mk'_surjective B)
  have hPn : P.Normal := by
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf r Ab
    have h2 : Subgroup.normalizer (Ab : Set (X ⧸ B)) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr hAbnorm
    rw [h2] at h1
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h1)
  have hPA : P ≤ Ab := CFSG.LieType.BorelTits.pCoreOf_le r Ab
  have hO : (P.comap π).Normal := hPn.comap π
  have hBO : B ≤ P.comap π := fun b hb => by
    have h1 : π b = 1 := (QuotientGroup.eq_one_iff b).2 hb
    rw [Subgroup.mem_comap, h1]
    exact P.one_mem
  have hOA : P.comap π ≤ A := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := hPA (Subgroup.mem_comap.1 hx)
    have : a⁻¹ * x ∈ B := QuotientGroup.eq.1 hax
    have hxa : x = a * (a⁻¹ * x) := by group
    rw [hxa]
    exact A.mul_mem ha (hBA this)
  have hRO : R ≤ P.comap π := fun x hx => hRP ⟨x, hx, rfl⟩
  rcases hchief _ hO hBO hOA with h | h
  · exact absurd (fun x hx => by rw [← h]; exact hRO hx) hne
  · intro a ha
    have hmem : π a ∈ P := by
      have : a ∈ P.comap π := by rw [h]; exact ha
      exact this
    have hPp : IsPGroup r P := CFSG.LieType.BorelTits.pCoreOf_isPGroup r Ab
    obtain ⟨k, hk⟩ := hPp ⟨π a, hmem⟩
    refine ⟨k, ?_⟩
    have h1 : (π a) ^ r ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [← map_pow] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1

theorem commutator_le_of_chief_of_decomp {T : Subgroup X} (hT2 : IsPGroup 2 T)
    {A B Y : Subgroup X} (hA : A.Normal) (hB : B.Normal) (hY : Y.Normal) (hBA : B ≤ A)
    (hchief : ∀ D : Subgroup X, D.Normal → B ≤ D → D ≤ A → D = B ∨ D = A)
    (hAY : A ⊓ Y ≤ B)
    (hdec : ∀ a ∈ A, ∃ y ∈ Y, ∃ n ∈ Subgroup.normalizer (thompsonJ T : Set X), a = y * n) :
    (∀ a ∈ A, ∃ k : ℕ, a ^ 2 ^ k ∈ B) ∨ ⁅A, thompsonJ T⁆ ≤ B := by
  set J : Subgroup X := thompsonJ T with hJdef
  have hJ2 : IsPGroup 2 J := hT2.to_le (B6.thompsonJ_le T)
  have hAn : ∀ a ∈ A, a ∈ Subgroup.normalizer ((Y ⊔ J : Subgroup X) : Set X) := by
    intro a ha
    obtain ⟨y, hy, n, hn, rfl⟩ := hdec a ha
    refine mul_mem (Subgroup.le_normalizer (Subgroup.mem_sup_left hy)) ?_
    exact Subgroup.inf_normalizer_le_normalizer_sup Y J ⟨mem_normalizer_of_normal' hY n, hn⟩
  by_cases hQB : A ⊓ (Y ⊔ J) ≤ B
  · right
    rw [Subgroup.commutator_le]
    intro a ha j hj
    apply hQB
    have hrw : ⁅a, j⁆ = a * (j * a⁻¹ * j⁻¹) := by
      rw [commutatorElement_def]
      group
    refine ⟨?_, ?_⟩
    · rw [hrw]
      exact A.mul_mem ha (hA.conj_mem _ (A.inv_mem ha) j)
    · have haj : a * j * a⁻¹ ∈ Y ⊔ J :=
        (Subgroup.mem_normalizer_iff.mp (hAn a ha) j).mp (Subgroup.mem_sup_right hj)
      rw [commutatorElement_def]
      exact (Y ⊔ J).mul_mem haj ((Y ⊔ J).inv_mem (Subgroup.mem_sup_right hj))
  · left
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine forall_pow_mem_of_chief_of_pSection (R := A ⊓ (Y ⊔ J)) hA hB hBA hchief inf_le_left ?_ ?_
      hQB
    · intro a ha
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ha, hAn a ha⟩
    · intro q hq
      obtain ⟨k, hk⟩ := B6.isTwoQuotient_of_sup_eq hJ2
        (fun d _ => mem_normalizer_of_normal' hY d) (rfl : J ⊔ Y = J ⊔ Y) q
        (by rw [sup_comm]; exact hq.2)
      exact ⟨k, hAY ⟨A.pow_mem hq.1 _, hk⟩⟩

theorem cover_of_two_group {T T₁ : Subgroup X} (hT : IsSylowTwoOf T ⊤)
    (h1 : T₁ ≤ omegaOneCenterOf T) {A B : Subgroup X} (hA : A.Normal) (hB : B.Normal)
    (hBA : B ≤ A) (h2 : ∀ a ∈ A, ∃ k : ℕ, a ^ 2 ^ k ∈ B) :
    A ≤ B ⊔ (A ⊓ Subgroup.centralizer (T₁ : Set X)) := by
  have hS : IsSylowTwoOf (T ⊓ A) A :=
    B6.isSylowTwoOf_inf_normal hT le_top fun g _ => mem_normalizer_of_normal' hA g
  have hsup : B ⊔ (T ⊓ A) = A :=
    B6.sup_eq_of_isTwoQuotient hBA (fun d _ => mem_normalizer_of_normal' hB d) h2 hS
  have hTC : T ≤ Subgroup.centralizer (T₁ : Set X) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyc : y ∈ centerOf T :=
      (Subgroup.closure_le (centerOf T)).mpr (fun z hz => hz.1) (h1 hy)
    exact (Subgroup.mem_centralizer_iff.mp hyc.2 t ht).symm
  calc A = B ⊔ (T ⊓ A) := hsup.symm
    _ ≤ B ⊔ (A ⊓ Subgroup.centralizer (T₁ : Set X)) :=
        sup_le_sup_left (fun x hx => ⟨hx.2, hTC hx.1⟩) B

theorem cover_of_chief_of_commutator_le {T T₁ T₂ : Subgroup X} (hT : IsSylowTwoOf T ⊤)
    (h1 : T₁ ≤ omegaOneCenterOf T) (h2 : T₂ ≤ baum T)
    (h2c : (T₂.subgroupOf (baum T)).Characteristic) {A B : Subgroup X} (hA : A.Normal)
    (hB : B.Normal) (hBA : B ≤ A)
    (hchief : ∀ D : Subgroup X, D.Normal → B ≤ D → D ≤ A → D = B ∨ D = A)
    (hcomm : ⁅A, thompsonJ T⁆ ≤ B) :
    A ≤ B ⊔ (A ⊓ Subgroup.centralizer (T₁ : Set X)) ∨
      A ≤ B ⊔ (A ⊓ Subgroup.normalizer (T₂ : Set X)) := by
  refine cover_of_chief_factor_normalizer hT h1 h2 h2c hA hB hBA hchief ?_
  intro a ha
  obtain ⟨b, hb, n, hn, rfl⟩ := eq_mul_normalizer_thompsonJ_of_commutator_le hT hB hBA hcomm a ha
  exact Subgroup.mul_mem_sup hb hn.2

theorem exists_pElement_of_cover {p : ℕ} (hp : p.Prime) {A B H : Subgroup X} (hB : B.Normal)
    (hcov : A ≤ B ⊔ (A ⊓ H)) (hpd : p ∣ B.relIndex A) :
    ∃ x ∈ A ⊓ H, x ∉ B ∧ ∃ k : ℕ, orderOf x = p ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  set B' : Subgroup ↥A := B.subgroupOf A with hB'
  have : B'.Normal := hB.subgroupOf A
  have hcard : Nat.card (↥A ⧸ B') = B.relIndex A := by
    rw [← Subgroup.index_eq_card]
    rfl
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := ↥A ⧸ B') p
    (hcard ▸ hpd : p ∣ Nat.card (↥A ⧸ B'))
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨b, hb, h, hh, hbh⟩ := Subgroup.mem_sup_of_normal_left.mp (hcov a.2)
  have hmk : (QuotientGroup.mk (⟨h, hh.1⟩ : ↥A) : ↥A ⧸ B') = QuotientGroup.mk a := by
    rw [QuotientGroup.eq, hB', Subgroup.mem_subgroupOf]
    have hab : (a : X) = b * h := hbh.symm
    have : h⁻¹ * (a : X) = h⁻¹ * b * h := by rw [hab]; group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, this]
    simpa [mul_assoc] using hB.conj_mem b hb h⁻¹
  have hh0 : orderOf h ≠ 0 := (orderOf_pos h).ne'
  obtain ⟨e, m, hpm, hem⟩ := Nat.exists_eq_pow_mul_and_not_dvd hh0 p hp.one_lt.ne'
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hem
    exact hh0 hem
  have hmdvd : m ∣ orderOf h := hem ▸ Dvd.intro_left _ rfl
  refine ⟨h ^ m, ⟨A.pow_mem hh.1 m, H.pow_mem hh.2 m⟩, fun hx => hpm ?_, e, ?_⟩
  · have h1 : (QuotientGroup.mk (⟨h ^ m, A.pow_mem hh.1 m⟩ : ↥A) : ↥A ⧸ B') = 1 :=
      (QuotientGroup.eq_one_iff _).2 (by simpa [hB', Subgroup.mem_subgroupOf] using hx)
    have h2 : (QuotientGroup.mk (⟨h ^ m, A.pow_mem hh.1 m⟩ : ↥A) : ↥A ⧸ B') =
        (QuotientGroup.mk a) ^ m := by
      rw [← hmk, ← QuotientGroup.mk_pow]
      rfl
    rw [h2] at h1
    rw [← hq]
    exact orderOf_dvd_iff_pow_eq_one.mpr h1
  · rw [orderOf_pow_of_dvd hm0 hmdvd, hem, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
