module

public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift
public import CFSG.LocalAnalysis.GLTheoremB.TwoGroupTools
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type*} [Group G]

theorem card_sup_mul_card_inf_of_normal (A B : Subgroup G) [A.Normal] :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := A ⊔ B)
  rw [Subgroup.relIndex_sup_left, inf_eq_left.mpr le_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [← h1, ← h2]
  ring

theorem card_sup_mul_card_inf {A B : Subgroup G} (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal (A.subgroupOf N) (B.subgroupOf N)
  have hc : ∀ Y : Subgroup G, Y ≤ N → Nat.card (Y.subgroupOf N) = Nat.card Y := fun Y hY =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have hsup : A.subgroupOf N ⊔ B.subgroupOf N = (A ⊔ B).subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAN, inf_eq_left.mpr hB,
      inf_eq_left.mpr (sup_le hAN hB)]
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N := by
    ext g; simp [Subgroup.mem_subgroupOf]
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  exact h


theorem factorization_card_pow {p : ℕ} [hp : Fact p.Prime] {k : ℕ} :
    (p ^ k).factorization p = k := by
  rw [hp.out.factorization_pow]; simp

theorem card_inf_sylow [Finite G] {p : ℕ} [hp : Fact p.Prime] {N H P : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hNH : N ≤ H) (hPH : P ≤ H)
    (hPp : IsPGroup p ↥P) (hPc : Nat.card P = p ^ (Nat.card H).factorization p) :
    Nat.card ↥(P ⊓ N) = p ^ (Nat.card N).factorization p := by
  have hPN : P ≤ Subgroup.normalizer (N : Set G) := hPH.trans hHN
  have h1 := card_sup_mul_card_inf hPN
  have hNP : N ⊔ P ≤ H := sup_le hNH hPH
  have h0P : Nat.card P ≠ 0 := Nat.card_pos.ne'
  have h0N : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have h0H : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have h0NP : Nat.card ↥(N ⊔ P) ≠ 0 := Nat.card_pos.ne'
  have h0I : Nat.card ↥(N ⊓ P) ≠ 0 := Nat.card_pos.ne'
  have hd1 : Nat.card P ∣ Nat.card ↥(N ⊔ P) := Subgroup.card_dvd_of_le le_sup_right
  have hd2 : Nat.card ↥(N ⊔ P) ∣ Nat.card H := Subgroup.card_dvd_of_le hNP
  have hv1 := (Nat.factorization_le_iff_dvd h0P h0NP).2 hd1 p
  have hv2 := (Nat.factorization_le_iff_dvd h0NP h0H).2 hd2 p
  have hv3 : (Nat.card ↥(N ⊔ P) * Nat.card ↥(N ⊓ P)).factorization p =
      (Nat.card N * Nat.card P).factorization p := by rw [h1]
  rw [Nat.factorization_mul h0NP h0I, Nat.factorization_mul h0N h0P] at hv3
  have hvP : (Nat.card P).factorization p = (Nat.card H).factorization p := by
    rw [hPc, factorization_card_pow]
  have hpI : IsPGroup p ↥(N ⊓ P) := hPp.to_inf_right
  obtain ⟨j, hj⟩ := exists_card_eq_pow hpI
  have hjv : j = (Nat.card N).factorization p := by
    have : (Nat.card ↥(N ⊓ P)).factorization p = j := by rw [hj, factorization_card_pow]
    simp only [Finsupp.add_apply] at hv3
    omega
  rw [inf_comm, hj, hjv]

theorem exists_invariant_sylow [Finite G] {p : ℕ} [hp : Fact p.Prime] {M B : Subgroup G}
    (hB : IsPGroup p ↥B) (hBM : B ≤ Subgroup.normalizer (M : Set G)) :
    ∃ R : Subgroup G, R ≤ M ∧ IsPGroup p ↥R ∧ Nat.card R = p ^ (Nat.card M).factorization p ∧
      B ≤ Subgroup.normalizer (R : Set G) := by
  set H : Subgroup G := M ⊔ B with hH
  have hMH : M ≤ H := le_sup_left
  have hBH : B ≤ H := le_sup_right
  have hHM : H ≤ Subgroup.normalizer (M : Set G) :=
    sup_le Subgroup.le_normalizer hBM
  have hBp : IsPGroup p ↥(B.subgroupOf H) := hB.comap_subtype
  obtain ⟨P, hP⟩ := hBp.exists_le_sylow
  set P' : Subgroup G := (P : Subgroup ↥H).map H.subtype with hP'
  have hP'H : P' ≤ H := by
    rintro _ ⟨y, -, rfl⟩; exact y.2
  have hBP' : B ≤ P' := by
    intro b hb
    exact ⟨⟨b, hBH hb⟩, hP (Subgroup.mem_subgroupOf.2 hb), rfl⟩
  have hP'p : IsPGroup p ↥P' := (P.isPGroup').map _
  have hP'c : Nat.card P' = p ^ (Nat.card H).factorization p := by
    rw [hP', Subgroup.card_map_of_injective H.subtype_injective, Sylow.card_eq_multiplicity]
  refine ⟨P' ⊓ M, inf_le_right, hP'p.to_inf_left, card_inf_sylow hHM hMH hP'H hP'p hP'c, ?_⟩
  intro b hb
  have hb1 : b ∈ Subgroup.normalizer (P' : Set G) := Subgroup.le_normalizer (hBP' hb)
  have hb2 : b ∈ Subgroup.normalizer (M : Set G) := hBM hb
  exact CFSG.LocalAnalysis.GLTheoremB.mem_normalizer_inf hb1 hb2


theorem card_le_of_isPGroup [Finite G] {p : ℕ} [hp : Fact p.Prime] {P M : Subgroup G}
    (hPM : P ≤ M) (hP : IsPGroup p ↥P) : Nat.card P ≤ p ^ (Nat.card M).factorization p := by
  obtain ⟨j, hj⟩ := exists_card_eq_pow hP
  have hdvd : Nat.card P ∣ Nat.card M := Subgroup.card_dvd_of_le hPM
  have := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hdvd p
  rw [hj, factorization_card_pow] at this
  rw [hj]
  exact Nat.pow_le_pow_right hp.out.pos this

theorem eq_of_le_sylow [Finite G] {p : ℕ} [hp : Fact p.Prime] {S S' M : Subgroup G}
    (hSS : S ≤ S') (hS'M : S' ≤ M) (hS' : IsPGroup p ↥S')
    (hSc : Nat.card S = p ^ (Nat.card M).factorization p) : S = S' :=
  Subgroup.eq_of_le_of_card_ge hSS (hSc ▸ card_le_of_isPGroup hS'M hS')

theorem card_sup_sylow [Finite G] {p : ℕ} [hp : Fact p.Prime] {M₁ M₂ S T : Subgroup G}
    (h12 : M₂ ≤ Subgroup.normalizer (M₁ : Set G)) (h21 : M₁ ≤ Subgroup.normalizer (M₂ : Set G))
    (hS : S ≤ M₁) (hT : T ≤ M₂) (hSp : IsPGroup p ↥S) (hTp : IsPGroup p ↥T)
    (hSc : Nat.card S = p ^ (Nat.card M₁).factorization p)
    (hTc : Nat.card T = p ^ (Nat.card M₂).factorization p)
    (hcomm : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    IsPGroup p ↥(S ⊔ T) ∧
      Nat.card ↥(S ⊔ T) = p ^ (Nat.card ↥(M₁ ⊔ M₂)).factorization p := by
  have hST : IsPGroup p ↥(S ⊔ T) :=
    isPGroup_sup_of_commute hSp hTp (fun s hs t ht => (hcomm s hs t ht).symm)
  refine ⟨hST, ?_⟩
  have hTc' : T ≤ Subgroup.centralizer (S : Set G) := fun t ht s hs =>
    hcomm s hs t ht
  have hTn : T ≤ Subgroup.normalizer (S : Set G) := hTc'.trans (Subgroup.centralizer_le_normalizer _)
  have hSn1 : S ≤ Subgroup.centralizer (T : Set G) := fun s hs t ht => (hcomm s hs t ht).symm
  have h1 := card_sup_mul_card_inf hTn
  have h2 := card_sup_mul_card_inf h12
  set D : Subgroup G := M₁ ⊓ M₂ with hD
  have hDM₁ : D ≤ M₁ := inf_le_left
  have hM₁D : M₁ ≤ Subgroup.normalizer (D : Set G) :=
    fun g hg => mem_normalizer_inf (Subgroup.le_normalizer hg) (h21 hg)
  have e1 : S = (S ⊔ T) ⊓ M₁ :=
    eq_of_le_sylow (le_inf le_sup_left hS) inf_le_right (hST.to_inf_left) hSc
  have e2 : T = (S ⊔ T) ⊓ M₂ :=
    eq_of_le_sylow (le_inf le_sup_right hT) inf_le_right (hST.to_inf_left) hTc
  have e3 : S ⊓ T = (S ⊔ T) ⊓ D := by
    ext g
    constructor
    · rintro ⟨hgS, hgT⟩
      exact ⟨(le_sup_left : S ≤ S ⊔ T) hgS, hS hgS, hT hgT⟩
    · rintro ⟨hg, hg1, hg2⟩
      refine ⟨by rw [e1]; exact ⟨hg, hg1⟩, by rw [e2]; exact ⟨hg, hg2⟩⟩
  have hSD : Nat.card ↥(S ⊓ D) = p ^ (Nat.card D).factorization p :=
    card_inf_sylow hM₁D hDM₁ hS hSp hSc
  have hle1 : S ⊓ D ≤ S ⊓ T := by
    rw [e3]; exact inf_le_inf le_sup_left le_rfl
  have hle2 : Nat.card ↥(S ⊓ T) ≤ p ^ (Nat.card D).factorization p := by
    rw [e3]
    exact card_le_of_isPGroup inf_le_right (hST.to_inf_left)
  have hlow : p ^ (Nat.card D).factorization p ≤ Nat.card ↥(S ⊓ T) := by
    rw [← hSD]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion hle1) (Subgroup.inclusion_injective hle1)
  have hIc : Nat.card ↥(S ⊓ T) = p ^ (Nat.card D).factorization p := le_antisymm hle2 hlow
  have h0 : ∀ H : Subgroup G, Nat.card H ≠ 0 := fun H => Nat.card_pos.ne'
  have f1 : (Nat.card ↥(S ⊔ T) * Nat.card ↥(S ⊓ T)).factorization p =
      (Nat.card S * Nat.card T).factorization p := by rw [h1]
  have f2 : (Nat.card ↥(M₁ ⊔ M₂) * Nat.card ↥D).factorization p =
      (Nat.card M₁ * Nat.card M₂).factorization p := by rw [h2]
  rw [Nat.factorization_mul (h0 _) (h0 _), Nat.factorization_mul (h0 _) (h0 _)] at f1
  rw [Nat.factorization_mul (h0 _) (h0 _), Nat.factorization_mul (h0 _) (h0 _)] at f2
  simp only [Finsupp.add_apply] at f1 f2
  have g1 : (Nat.card ↥(S ⊓ T)).factorization p = (Nat.card D).factorization p := by
    rw [hIc, factorization_card_pow]
  have g2 : (Nat.card S).factorization p = (Nat.card M₁).factorization p := by
    rw [hSc, factorization_card_pow]
  have g3 : (Nat.card T).factorization p = (Nat.card M₂).factorization p := by
    rw [hTc, factorization_card_pow]
  obtain ⟨j, hj⟩ := exists_card_eq_pow hST
  have hjv : j = (Nat.card ↥(M₁ ⊔ M₂)).factorization p := by
    have : (Nat.card ↥(S ⊔ T)).factorization p = j := by rw [hj, factorization_card_pow]
    omega
  rw [hj, hjv]


theorem exists_fixed_ne_one [Finite G] {p : ℕ} [hp : Fact p.Prime] {P N : Subgroup G}
    (hP : IsPGroup p ↥P) (hPN : P ≤ Subgroup.normalizer (N : Set G)) (hN : N ≠ ⊥)
    (hNp : IsPGroup p ↥N) : ∃ n ∈ N, n ≠ 1 ∧ ∀ g ∈ P, g * n = n * g := by
  classical
  let _ : MulDistribMulAction P N := Subgroup.conjMulDistribMulActionOfLeNormalizer P N hPN
  have hmod := hP.card_modEq_card_fixedPoints ↥N
  obtain ⟨k, hk⟩ := exists_card_eq_pow hNp
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hN
    exact Subgroup.eq_bot_of_card_eq N (by rw [hk]; simp)
  have hdvd : p ∣ Nat.card ↥N := by rw [hk]; exact dvd_pow_self p hk0
  have hdvd2 : p ∣ Nat.card (MulAction.fixedPoints P ↥N) :=
    (Nat.modEq_zero_iff_dvd.1 ((hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 hdvd))))
  have hpos : 0 < Nat.card (MulAction.fixedPoints P ↥N) := by
    have : Finite (MulAction.fixedPoints P ↥N) := inferInstance
    exact Nat.card_pos_iff.2 ⟨⟨⟨1, fun g => by simp⟩⟩, this⟩
  have hge : p ≤ Nat.card (MulAction.fixedPoints P ↥N) := Nat.le_of_dvd hpos hdvd2
  have h2 : 1 < Nat.card (MulAction.fixedPoints P ↥N) := lt_of_lt_of_le hp.out.one_lt hge
  have hnt : Nontrivial (MulAction.fixedPoints P ↥N) := Finite.one_lt_card_iff_nontrivial.1 h2
  have h1fix : (1 : ↥N) ∈ MulAction.fixedPoints P ↥N := fun g => by simp
  obtain ⟨⟨n, hnfix⟩, hne⟩ := exists_ne (⟨1, h1fix⟩ : MulAction.fixedPoints P ↥N)
  refine ⟨n, n.2, fun h => hne (Subtype.ext (Subtype.ext h)), fun g hg => ?_⟩
  have := MulAction.mem_fixedPoints.1 hnfix ⟨g, hg⟩
  have h' : g * (n : G) * g⁻¹ = (n : G) := congrArg Subtype.val this
  calc g * (n : G) = g * (n : G) * g⁻¹ * g := by group
    _ = (n : G) * g := by rw [h']

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
