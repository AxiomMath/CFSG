module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalNineConj

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaLocal.Nine

open SectionSix SectionSix.BarTools

section Abstract

variable {X : Type} [Group X] [Finite X]

theorem exists_invariant_sylow_le {K R P : Subgroup X} (hR : IsPGroup 2 R)
    (hRK : R ≤ Subgroup.normalizer (K : Set X)) (hP : IsPGroup 2 P) (hPK : P ≤ K)
    (hRP : R ≤ Subgroup.normalizer (P : Set X)) :
    ∃ S : Subgroup X, IsSylowOf 2 S K ∧ P ≤ S ∧ R ≤ Subgroup.normalizer (S : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (P ⊔ R : Subgroup X) := IsPGroup.to_sup_of_normal_left' hP hR hRP
  obtain ⟨Q, hQ, hle⟩ := AschbacherTheorem3.exists_isSylowOf_le h2
    (sup_le_sup_right hPK R : P ⊔ R ≤ K ⊔ R)
  refine ⟨Q ⊓ K, hQ.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hRK),
    le_inf (le_sup_left.trans hle) hPK, fun t ht => ?_⟩
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer (hle (Subgroup.mem_sup_right ht)), hRK ht⟩

theorem mem_normalizer_iSup₂ {m : ℕ} {I : Fin m → Prop} {K : Fin m → Subgroup X} {x : X}
    (h : ∀ j, I j → x ∈ Subgroup.normalizer (K j : Set X)) :
    x ∈ Subgroup.normalizer ((⨆ j, ⨆ (_ : I j), K j : Subgroup X) : Set X) := by
  apply AschbacherToolkit.mem_normalizer_of_conj_le
  have hle : (⨆ j, ⨆ (_ : I j), K j : Subgroup X) ≤
      (⨆ j, ⨆ (_ : I j), K j : Subgroup X).comap (MulAut.conj x).toMonoidHom := by
    refine iSup₂_le fun j hj y hy => ?_
    rw [Subgroup.mem_comap]
    exact (le_iSup₂_of_le (f := fun j (_ : I j) => K j) j hj le_rfl :
      K j ≤ ⨆ j, ⨆ (_ : I j), K j) ((Subgroup.mem_normalizer_iff.mp (h j hj) y).mp hy)
  exact fun y hy => hle hy

end Abstract

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem exists_X (h3 : AschbacherTheorem3.Theorem3Statement) (hin : SectionSixInputs)
    (hC : Counterexample G D r Abar) {g : G}
    (hΔ : rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G))) (hr : 3 ≤ r) {a m : Fin r}
    (ham : a ≠ m) {T R : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate (aschbacherThm5Preimage D (Abar a)) g ⊓
      Subgroup.normalizer (D : Set G)))
    (hR2 : IsPGroup 2 R) (hRA : R ≤ aschbacherThm5Preimage D (Abar a))
    (hRHg : R ≤ rightConjugate (Subgroup.normalizer (D : Set G)) g)
    (hRT : R ≤ Subgroup.normalizer (T : Set G)) :
    ∃ X : Subgroup G, IsPGroup 2 X ∧ X ≤ Subgroup.normalizer (D : Set G) ∧ T ≤ X ∧ T ≠ X ∧
      X ≤ orbitProduct (rightConjugate D g) (conjFactors D Abar g) {j | j ≠ m} ∧
      (∀ k, X ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar k) : Set G)) ∧
      R ≤ Subgroup.normalizer (X : Set G) ∧
      (∀ j, j ≠ m → ∃ Y : Subgroup G, Y ≤ X ∧
        Y ≤ rightConjugate (aschbacherThm5Preimage D (Abar j)) g ∧
        ¬ Y ≤ rightConjugate (factorZStar D Abar j) g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set L : Fin r → Subgroup G := fun j => rightConjugate (aschbacherThm5Preimage D (Abar j)) g
    with hLdef
  have hC' := hC.conj g
  have hLeq : ∀ j, L j = aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g j) :=
    fun j => (preimage_conjFactors D Abar g j).symm
  have hRH : R ≤ H := hRA.trans ((preimage_le D _).trans Subgroup.le_normalizer)
  set K : Subgroup G := ⨆ j, ⨆ (_ : j ≠ m), L j ⊓ H with hKdef
  have hLjK : ∀ j, j ≠ m → L j ⊓ H ≤ K := fun j hj => le_iSup₂_of_le j hj le_rfl
  have hLN : ∀ j j', L j' ⊓ H ≤ Subgroup.normalizer ((L j ⊓ H : Subgroup G) : Set G) := by
    intro j j' x hx
    have h1 : x ∈ Subgroup.normalizer (L j : Set G) := by
      rw [hLeq j]
      apply Eight.le_normalizer_factor hC' j
      have := hx.1
      rw [hLeq j'] at this
      exact preimage_le _ _ this
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, Subgroup.le_normalizer hx.2⟩
  have hKN : ∀ j, K ≤ Subgroup.normalizer ((L j ⊓ H : Subgroup G) : Set G) :=
    fun j => iSup₂_le fun j' _ => hLN j j'
  have hRLj : ∀ j, R ≤ Subgroup.normalizer ((L j ⊓ H : Subgroup G) : Set G) := fun j x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨normalizes_conj_of_le h3 hin hC hΔ hr hR2 hRA hRHg j hx, Subgroup.le_normalizer (hRH hx)⟩
  have hRK : R ≤ Subgroup.normalizer (K : Set G) := fun x hx =>
    mem_normalizer_iSup₂ fun j _ => hRLj j hx
  obtain ⟨Sg, hSg, hTSg, hRSg⟩ := exists_invariant_sylow_le hR2 hRK hT.isPGroup
    (hT.le.trans (hLjK a ham)) hRT
  set Tj : Fin r → Subgroup G := fun j => Sg ⊓ (L j ⊓ H) with hTjdef
  have hTjs : ∀ j, j ≠ m → IsSylowOf 2 (Tj j) (L j ⊓ H) := fun j hj =>
    hSg.inf_of_le_normalizer (hLjK j hj) (hKN j)
  have hTTa : T ≤ Tj a := le_inf hTSg hT.le
  set X : Subgroup G := ⨆ j, ⨆ (_ : j ≠ m), Tj j with hXdef
  have hTjX : ∀ j, j ≠ m → Tj j ≤ X := fun j hj => le_iSup₂_of_le j hj le_rfl
  have hXSg : X ≤ Sg := iSup₂_le fun j _ => inf_le_left
  have hXK : X ≤ K := hXSg.trans hSg.le
  have hTjZ : ∀ j, j ≠ m → ¬ Tj j ≤ rightConjugate (factorZStar D Abar j) g :=
    fun j hj => not_le_factorZStar_conj h3 hin hC hΔ j (hTjs j hj)
  refine ⟨X, hSg.isPGroup.to_le hXSg, hXK.trans (iSup₂_le fun j _ => inf_le_right),
    hTTa.trans (hTjX a ham), ?_, ?_, ?_, ?_, fun j hj => ⟨Tj j, hTjX j hj, inf_le_right.trans
      inf_le_left, hTjZ j hj⟩⟩
  ·
    intro hTX
    obtain ⟨b, hba, hbm⟩ := Six.exists_third hr a m
    apply hTjZ b hbm
    intro y hy
    have hyT : y ∈ T := by
      rw [hTX]
      exact hTjX b hbm hy
    have hyLa : y ∈ L a := (hT.le hyT).1
    have hyLb : y ∈ L b := hy.2.1
    rw [← factorZStar_conj]
    refine ⟨by rw [← hLeq b]; exact hyLb, ?_⟩
    rw [hLeq a] at hyLa
    exact factor_le_centralizing hC'.hyp.hcomm hba hyLa
  · exact iSup₂_le fun j hj => (inf_le_right.trans inf_le_left).trans (by
      rw [hLeq j]
      exact factor_le_orbitProduct (I := {j | j ≠ m}) hj)
  · intro k
    refine iSup₂_le fun j hj => ?_
    exact normalizes_of_le h3 hin hC hΔ hr ((hTjs j hj).isPGroup) (inf_le_right.trans inf_le_left)
      (inf_le_right.trans inf_le_right) k
  · intro x hx
    exact mem_normalizer_iSup₂ fun j _ => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hRSg hx, hRLj j hx⟩

end DeltaLocal.Nine

end CFSG.ComponentClassification.AschbacherTheorem5
