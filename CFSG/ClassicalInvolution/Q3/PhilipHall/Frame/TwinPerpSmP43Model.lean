module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmP43Sound
public import CFSG.ClassicalInvolution.Q3.TA3SmallConcrete
public import CFSG.ClassicalInvolution.SmallCases.NobqSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.P43

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.TA3
  CFSG.ClassicalInvolution.Q3.TA3.Check
open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.GH74.KGroups

local notation "P45" => Equiv.Perm (Fin 45)

theorem card_L0 : Nat.card QP45.originalSubgroup = 25920 := by
  rw [card_group QP45 QP45_ok, QP45_valid.2]

theorem card_A0 : Nat.card QA45.originalSubgroup = 51840 := by
  rw [card_group QA45 QA45_ok, QA45_valid.2]

theorem L0_le_A0 : QP45.originalSubgroup ≤ QA45.originalSubgroup := by
  rw [QP45_closure, QA45_closure]
  exact Subgroup.closure_mono
    (Set.insert_subset_insert (Set.singleton_subset_iff.2 (Set.mem_insert _ _)))

section Emb

variable {Y G : Type} [Group Y] [Group G] (N : Subgroup Y) [N.Normal]
  (M : GH74.KGroups.AutModel ↥N G)

noncomputable def emb : Y →* G := M.ι.comp MulAut.conjNormal

theorem emb_coe (hPA : M.P ≤ M.A) (k : ↥N) : emb N M (k : Y) = (M.e k : G) := by
  have hconj : (MulAut.conjNormal (k : Y) : MulAut ↥N) = MulAut.conj k := by
    ext x
    simp [MulAut.conjNormal_apply]
  show (M.Φ (MulAut.conjNormal (k : Y)) : G) = _
  rw [hconj, autModel_Φ_conj_eq M hPA k]

theorem emb_mem (y : Y) : emb N M y ∈ M.A := M.ι_mem _

theorem emb_injective (hC : Subgroup.centralizer (N : Set Y) = ⊥) :
    Function.Injective (emb N M) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have h3 : (MulAut.conjNormal y : MulAut ↥N) = 1 :=
    M.ι_injective (by rw [map_one]; exact hy)
  have hyC : y ∈ Subgroup.centralizer (N : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h4 := congrArg (fun φ : MulAut ↥N => ((φ ⟨x, hx⟩ : ↥N) : Y)) h3
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h4
    calc x * y = (y * x * y⁻¹) * y := by rw [h4]
      _ = y * x := by group
  rw [hC] at hyC
  exact hyC

end Emb

theorem model_embedding {Y : Type} [Group Y] [Finite Y]
    [IsSimpleGroup ↥(genFittingFStar Y)] (hnab : ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a)
    (hF : CFSG.Blueprint.LieModel ↥(genFittingFStar Y) .PSp 2 3 1) :
    ∃ f : Y →* P45, Function.Injective f ∧ (∀ y, f y ∈ QA45.originalSubgroup) ∧
      (∀ y, y ∈ genFittingFStar Y ↔ f y ∈ QP45.originalSubgroup) ∧
      ∀ p ∈ QP45.originalSubgroup, ∃ y, f y = p := by
  haveI : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  obtain ⟨e⟩ := PSp43.equiv_of_lieModel hF
  obtain ⟨M, hMP, hMA⟩ := PSp43.exists_model e
  have hPA : M.P ≤ M.A := by rw [hMP, hMA]; exact L0_le_A0
  have hinj := emb_injective (genFittingFStar Y) M (Nobq.centralizer_genFittingFStar_eq_bot hnab)
  refine ⟨emb _ M, hinj, fun y => hMA ▸ emb_mem _ M y, fun y => ⟨fun hy => ?_, fun hy => ?_⟩,
    fun p hp => ?_⟩
  · have h1 := emb_coe _ M hPA ⟨y, hy⟩
    rw [← hMP]
    rw [show ((⟨y, hy⟩ : ↥(genFittingFStar Y)) : Y) = y from rfl] at h1
    rw [h1]
    exact (M.e ⟨y, hy⟩).2
  · rw [← hMP] at hy
    have h1 := emb_coe _ M hPA (M.e.symm ⟨_, hy⟩)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [← hinj h1]
    exact (M.e.symm ⟨_, hy⟩).2
  · rw [← hMP] at hp
    refine ⟨(M.e.symm ⟨p, hp⟩ : Y), ?_⟩
    rw [emb_coe _ M hPA, MulEquiv.apply_symm_apply]

theorem range_cases {Y : Type} [Group Y] [Finite Y] {f : Y →* P45}
    (hf : Function.Injective f) (hA : ∀ y, f y ∈ QA45.originalSubgroup)
    (hP : ∀ p ∈ QP45.originalSubgroup, ∃ y, f y = p) :
    (Nat.card Y = 25920 ∧ ∀ m, m ∈ elemsT QP45 ↔ ∃ y, f y = m) ∨
      (Nat.card Y = 51840 ∧ ∀ m, m ∈ elemsT QA45 ↔ ∃ y, f y = m) := by
  have hcY : Nat.card Y = Nat.card f.range := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
  have h1 : QP45.originalSubgroup ≤ f.range := fun p hp => hP p hp
  have h2 : f.range ≤ QA45.originalSubgroup := by
    rintro _ ⟨y, rfl⟩
    exact hA y
  have d1 : 25920 ∣ Nat.card Y := by rw [hcY, ← card_L0]; exact Subgroup.card_dvd_of_le h1
  have d2 : Nat.card Y ∣ 51840 := by rw [hcY, ← card_A0]; exact Subgroup.card_dvd_of_le h2
  obtain ⟨k, hk⟩ := d1
  obtain ⟨j, hj⟩ := d2
  have hkj : k * j = 2 := by
    rw [hk, mul_assoc] at hj
    omega
  have hk2 : k = 1 ∨ k = 2 := by
    have hk' : k ∣ 2 := ⟨j, hkj.symm⟩
    have hle := Nat.le_of_dvd (by norm_num) hk'
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hkj
      exact absurd hkj (by norm_num)
    omega
  rcases hk2 with rfl | rfl
  · refine Or.inl ⟨by omega, fun m => ?_⟩
    have heq : QP45.originalSubgroup = f.range :=
      Subgroup.eq_of_le_of_card_ge h1 (by rw [← hcY, card_L0]; omega)
    rw [mem_elemsT QP45 QP45_ok, heq, MonoidHom.mem_range]
  · refine Or.inr ⟨by omega, fun m => ?_⟩
    have heq : f.range = QA45.originalSubgroup :=
      Subgroup.eq_of_le_of_card_ge h2 (by rw [← hcY, card_A0]; omega)
    rw [mem_elemsT QA45 QA45_ok, ← heq, MonoidHom.mem_range]

theorem normalize {Y : Type} [Group Y] {N : Subgroup Y} [N.Normal] {f₀ : Y →* P45}
    (hf₀ : Function.Injective f₀) {Lst : List P45} (hL : ∀ m, m ∈ Lst ↔ ∃ y, f₀ y = m)
    (hN : ∀ y, y ∈ N ↔ f₀ y ∈ QP45.originalSubgroup) {reps : List P45}
    (hcov : coverB reps Lst = true) {t : Y} (ht : orderOf t = 2) :
    ∃ f : Y →* P45, Function.Injective f ∧ (∀ m, m ∈ Lst ↔ ∃ y, f y = m) ∧
      (∀ y, y ∈ N ↔ f y ∈ QP45.originalSubgroup) ∧ f t ∈ reps := by
  obtain ⟨r, hr, g, hg⟩ := cover_of_coverB hf₀ hL hcov ht
  have hfy : ∀ y, (f₀.comp (MulAut.conj g).toMonoidHom) y = f₀ (g * y * g⁻¹) := fun y => by
    simp [MulAut.conj_apply]
  refine ⟨f₀.comp (MulAut.conj g).toMonoidHom, hf₀.comp (MulAut.conj g).injective,
    fun m => ?_, fun y => ?_, ?_⟩
  · rw [hL m]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨g⁻¹ * y * g, by rw [hfy]; congr 1; group⟩
    · rintro ⟨y, rfl⟩
      exact ⟨_, (hfy y).symm⟩
  · rw [hfy, ← hN]
    constructor
    · intro hy
      exact ‹N.Normal›.conj_mem y hy g
    · intro hy
      have h1 := ‹N.Normal›.conj_mem _ hy g⁻¹
      simpa [mul_assoc] using h1
  · rw [hfy, hg]
    exact hr

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.P43
