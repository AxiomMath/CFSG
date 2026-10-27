module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.CentralLift
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172X

open CFSG.Open

private lemma exists_comm_closure_lift {K R : Type} [Group K] [Finite K] [Group R]
    (φ : K →* R) (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center K)
    {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {h w : Fin k → R}
    (hpow : ∀ i, h i ^ p = 1) (hcomm : ∀ i j, Commute (h i) (h j))
    (hind : Nat.card (Subgroup.closure (Set.range h)) = p ^ k)
    (hinv : ∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹)
    (hcross : ∀ i j, i ≠ j → w i * h j * (w i)⁻¹ * (h j)⁻¹ ∈ Subgroup.zpowers (h i)) :
    ∃ E : Subgroup K, IsElemAbelian p E ∧ Nat.card E = p ^ k ∧
      E ≤ (Subgroup.closure (Set.range h)).comap φ ∧
      E.map φ = Subgroup.closure (Set.range h) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set D : Subgroup R := Subgroup.closure (Set.range h) with hD
  have hDcard : Nat.card D = p ^ k := hind
  have hFcomm := comap_closure_comm_of_cross hφ hker hp hp2 hcomm hpow hinv hcross
  choose y hy using fun i => exists_lift_pow_eq_one hφ hker hp hp2 (hpow i) (hinv i)
  set E : Subgroup K := Subgroup.closure (Set.range y) with hE
  have hyE : ∀ i, y i ∈ E := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  have hEcomap : E ≤ D.comap φ := by
    rw [hE, hD]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_comap.2 (by
      rw [(hy i).1]
      exact Subgroup.subset_closure ⟨i, rfl⟩)
  have hEcomm : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x :=
    fun x hx z hz => hFcomm x (hEcomap hx) z (hEcomap hz)
  have hEmap : E.map φ = D := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]; exact hEcomap
    · rw [hD]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨y i, hyE i, (hy i).1⟩
  have hEcard : Nat.card E = p ^ k := by
    refine le_antisymm ?_ ?_
    · rw [hE]
      refine card_closure_le_pow_of_commuting hp (fun i => (hy i).2) ?_
      intro i j
      exact hEcomm (y i) (hyE i) (y j) (hyE j)
    · have h := Subgroup.card_map_dvd (H := E) φ
      rw [hEmap, hDcard] at h
      exact Nat.le_of_dvd Nat.card_pos h
  have hEab : IsElemAbelian p E :=
    IsElemAbelian.closure_of_commute
      (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hEcomm (y i) (hyE i) (y j) (hyE j))
      (by rintro _ ⟨i, rfl⟩; exact (hy i).2)
  rw [hD] at hEcomap hEmap
  exact ⟨E, hEab, hEcard, hEcomap, hEmap⟩

private lemma inf_ker_eq_bot_of_map_eq_card {K R : Type} [Group K] [Finite K] [Group R]
    (φ : K →* R) {p k : ℕ} (hp : p.Prime) {E : Subgroup K} {D : Subgroup R}
    (hEcomap : E ≤ D.comap φ) (hEmap : E.map φ = D)
    (hEcard : Nat.card E = p ^ k) (hDcard : Nat.card D = p ^ k) :
    E ⊓ φ.ker = ⊥ := by
  let ψ : E →* D := (φ.comp E.subtype).codRestrict D (fun x => hEcomap x.2)
  have hψrange : ψ.range = ⊤ := by
    have hmap : Subgroup.map D.subtype ψ.range = D := by
      apply le_antisymm
      · rintro _ ⟨x, -, rfl⟩
        exact x.2
      · intro d hd
        rw [← hEmap] at hd
        obtain ⟨x, hx, rfl⟩ := hd
        exact ⟨ψ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
    have htop : Subgroup.map D.subtype ψ.range = Subgroup.map D.subtype (⊤ : Subgroup D) := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
      exact hmap
    exact Subgroup.map_injective D.subtype_injective htop
  have hcard := Subgroup.card_ker_mul_card_range ψ
  rw [hψrange, Subgroup.card_top, hEcard, hDcard] at hcard
  have hker1 : Nat.card ψ.ker = 1 := by
    have hpk : 0 < p ^ k := pow_pos hp.pos k
    have h1 : Nat.card ψ.ker * p ^ k = 1 * p ^ k := by rw [hcard, one_mul]
    exact Nat.eq_of_mul_eq_mul_right hpk h1
  have hψker : ψ.ker = ⊥ := (Subgroup.eq_bot_iff_card ψ.ker).mpr hker1
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hx.1⟩ : E) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact MonoidHom.mem_ker.1 hx.2
  rw [hψker] at hx'
  exact Subtype.ext_iff.mp (Subgroup.mem_bot.1 hx')

private lemma exists_two_subgroup_normalized_of_cover_map {K R : Type} [Group K] [Finite K] [Group R]
    (φ : K →* R) (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center K)
    {X : Subgroup R} (hX1 : X ≠ ⊥) (hX2 : IsPGroup 2 X)
    {E : Subgroup K} {D : Subgroup R} (hEcomap : E ≤ D.comap φ)
    (hDnorm : D ≤ Subgroup.normalizer (X : Set R)) :
    ∃ P : Subgroup K, P ≠ ⊥ ∧ IsPGroup 2 P ∧ E ≤ Subgroup.normalizer (P : Set K) := by
  obtain ⟨P, hP1, hP2, hPN⟩ :=
    CFSG.RankThree.CentralCover.exists_two_subgroup_normalized_of_cover hφ hker hX1 hX2
      (S := E) (fun x hx u hu =>
        (Subgroup.le_normalizer_iff.1 hDnorm) (φ x) (Subgroup.mem_comap.1 (hEcomap hx)) u hu)
  exact ⟨P, hP1, hP2, hPN⟩

theorem exists_elemAbelian_lift_normalizing {K R : Type} [Group K] [Finite K] [Group R]
    (φ : K →* R) (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center K)
    {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {h w : Fin k → R}
    (hpow : ∀ i, h i ^ p = 1) (hcomm : ∀ i j, Commute (h i) (h j))
    (hind : Nat.card (Subgroup.closure (Set.range h)) = p ^ k)
    (hinv : ∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹)
    (hcross : ∀ i j, i ≠ j → w i * h j * (w i)⁻¹ * (h j)⁻¹ ∈ Subgroup.zpowers (h i))
    {X : Subgroup R} (hX1 : X ≠ ⊥) (hX2 : IsPGroup 2 X)
    (hNX : ∀ i, h i ∈ Subgroup.normalizer (X : Set R)) :
    ∃ E P : Subgroup K, IsElemAbelian p E ∧ Nat.card E = p ^ k ∧ E ⊓ φ.ker = ⊥ ∧
      P ≠ ⊥ ∧ IsPGroup 2 P ∧ E ≤ Subgroup.normalizer (P : Set K) := by
  classical
  obtain ⟨E, hEab, hEcard, hEcomap, hEmap⟩ :=
    exists_comm_closure_lift φ hφ hker hp hp2 hpow hcomm hind hinv hcross
  have hEker : E ⊓ φ.ker = ⊥ :=
    inf_ker_eq_bot_of_map_eq_card φ hp hEcomap hEmap hEcard hind
  have hDnorm : Subgroup.closure (Set.range h) ≤ Subgroup.normalizer (X : Set R) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, rfl⟩
    exact hNX i
  obtain ⟨P, hP1, hP2, hPN⟩ :=
    exists_two_subgroup_normalized_of_cover_map φ hφ hker hX1 hX2 hEcomap hDnorm
  exact ⟨E, P, hEab, hEcard, hEker, hP1, hP2, hPN⟩

theorem LiftableRank.exists_elemAbelian_lift {K G₀ : Type} [Group K] [Finite K] [Group G₀] {p m : ℕ}
    (hR : LiftableRank p G₀ m) (hp : p.Prime) (hp2 : p ≠ 2) (φ : K →* G₀)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center K) :
    ∃ E P : Subgroup K, IsElemAbelian p E ∧ Nat.card E = p ^ m ∧ E ⊓ φ.ker = ⊥ ∧
      P ≠ ⊥ ∧ IsPGroup 2 P ∧ E ≤ Subgroup.normalizer (P : Set K) := by
  obtain ⟨-, e, t, T, hE, hcard, ht, htc, hT2, hT1, hTN⟩ := hR
  have hmem : ∀ i, e i ∈ Subgroup.closure (Set.range e) := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  refine exists_elemAbelian_lift_normalizing φ hφ hker hp hp2 (h := e) (w := t)
    (fun i => hE.2 _ (hmem i)) (fun i j => (hE.comm (hmem i) (hmem j) : _)) hcard
    (fun i => (ht i).2) ?_ hT1 hT2 (fun i => hTN (hmem i))
  intro i j hij
  rw [htc i j hij]
  simp

end CFSG.LocalAnalysis.GLTheoremA.S172X

end
