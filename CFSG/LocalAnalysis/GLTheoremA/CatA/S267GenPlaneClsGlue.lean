module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieCross
import CFSG.LocalAnalysis.UniquenessCase.UC6K36OddSeitz
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2Layer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem eq_bot_of_le_normalizer_seitz (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) {p : ℕ}
    {T : Type} [Group T] [Finite T] {d : TauCeti.ValidLieTypeIndex} (h : OddLie p T d)
    (hT : IsSimpleGroup T) {P : Subgroup (MulAut T)} (hP : IsElemAbelian p P)
    (hcard : Nat.card P = p ^ 2) {J : Subgroup T} (hJP : ∀ x ∈ P, J ≤ fixSubgroup x)
    (hN : ∀ x ∈ P, x ≠ 1 → fixSubgroup x ≤ Subgroup.normalizer (J : Set T)) : J = ⊥ := by
  obtain ⟨e⟩ := h.iso
  set E : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group) :=
    P.map (MulAut.congr e).toMonoidHom with hE
  have hexc : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1 := fun hx =>
    h.charOdd (CFSG.LocalAnalysis.UniquenessCase.UCK.Odd.characteristic_eq_two_of_isD2SeitzException
      hx)
  have hcardE : Nat.card E = p ^ 2 := by
    rw [← hcard, hE]
    exact Subgroup.card_map_of_injective (MulAut.congr e).injective
  have hgen := hS d p h.prime h.odd h.ne hexc E (hP.map _) hcardE
  have hle : Subgroup.closure {k : (TauCeti.CFSGIndex.lie d).Group | ∃ x ∈ E, x ≠ 1 ∧ x k = k} ≤
      (Subgroup.normalizer (J : Set T)).comap e.symm.toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro k ⟨_, ⟨x, hxP, rfl⟩, hx1, hxk⟩
    have hx1' : x ≠ 1 := fun h1 => hx1 (by rw [h1]; exact map_one _)
    refine hN x hxP hx1' ?_
    rw [mem_fixSubgroup]
    have hk : e (x (e.symm k)) = k := hxk
    simpa using congrArg e.symm hk
  have htop : ∀ t : T, t ∈ Subgroup.normalizer (J : Set T) := by
    intro t
    have ht : e t ∈ Subgroup.closure {k : (TauCeti.CFSGIndex.lie d).Group |
        ∃ x ∈ E, x ≠ 1 ∧ x k = k} := by
      rw [hgen]
      exact Subgroup.mem_top _
    simpa using hle ht
  have hJn : J.Normal := ⟨fun n hn g => (Subgroup.mem_normalizer_iff.1 (htop g) n).1 hn⟩
  rcases hT.eq_bot_or_eq_top_of_normal J with hJ | hJ
  · exact hJ
  · exfalso
    have hPbot : P = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      ext t
      have ht : t ∈ fixSubgroup x := hJP x hx (by rw [hJ]; exact Subgroup.mem_top t)
      simpa [mem_fixSubgroup] using ht
    have h1 : Nat.card P = 1 := by
      rw [hPbot]
      exact Subgroup.card_bot
    have h4 : 4 ≤ p ^ 2 := by
      have := h.prime.two_le
      nlinarith
    omega

theorem not_forall_glaPComponent_of_normalizes (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    {p : ℕ} {T : Type} [Group T] [Finite T] {d : TauCeti.ValidLieTypeIndex} (h : OddLie p T d)
    (hT : IsSimpleGroup T) {P : Subgroup (MulAut T)} (hP : IsElemAbelian p P)
    (hcard : Nat.card P = p ^ 2) {J : Subgroup T}
    (hN : ∀ x ∈ P, x ≠ 1 → fixSubgroup x ≤ Subgroup.normalizer (J : Set T)) :
    ¬ ∀ x ∈ P, x ≠ 1 → GLAPComponent p (fixSubgroup x) J := by
  intro hJ
  obtain ⟨x, hxP, hx1⟩ : ∃ x ∈ P, x ≠ 1 := by
    by_contra hne
    push Not at hne
    have hPbot : P = ⊥ := (Subgroup.eq_bot_iff_forall P).2 hne
    have h1 : Nat.card P = 1 := by
      rw [hPbot]
      exact Subgroup.card_bot
    have h4 : 4 ≤ p ^ 2 := by
      have := h.prime.two_le
      nlinarith
    omega
  have hJP : ∀ y ∈ P, J ≤ fixSubgroup y := by
    intro y hy
    by_cases hy1 : y = 1
    · subst hy1
      intro j _
      rfl
    · exact (hJ y hy hy1).1
  exact glaPComponent_ne_bot' (hJ x hxP hx1) (eq_bot_of_le_normalizer_seitz hS h hT hP hcard hJP hN)

theorem not_forall_glaPComponent_of_compNormal (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    {Q : TauCeti.LieTypeIndex → Prop} (h2 : GenCompQuasiOn Q) {p : ℕ} {T : Type} [Group T]
    [Finite T] {d : TauCeti.ValidLieTypeIndex} (h : OddLie p T d) (hQ : Q d.1)
    (hT : IsSimpleGroup T) {P : Subgroup (MulAut T)} (hP : IsElemAbelian p P)
    (hcard : Nat.card P = p ^ 2) (hN : ∀ x ∈ P, x ≠ 1 → CompNormal x) (J : Subgroup T) :
    ¬ ∀ x ∈ P, x ≠ 1 → GLAPComponent p (fixSubgroup x) J := by
  intro hJ
  refine not_forall_glaPComponent_of_normalizes hS h hT hP hcard (J := J) (fun x hx hx1 => ?_) hJ
  exact hN x hx hx1 J (h2 p T d h hQ x (hP.2 x hx) hx1 J (hJ x hx hx1))

theorem exists_lift_mem_fixSubgroup {X T : Type*} [Group X] [Group T] (π : X →* T)
    (hπ : Function.Surjective π) (α : MulAut X) (β : MulAut T) (hαβ : ∀ x, π (α x) = β (π x))
    {p : ℕ} (hαp : α ^ p = 1) (hαZ : ∀ z ∈ π.ker, α z = z)
    (hZp : ∀ z ∈ π.ker, z ^ p = 1 → z = 1) {t : T} (ht : t ∈ fixSubgroup β) :
    ∃ g ∈ fixSubgroup α, π g = t := by
  obtain ⟨g, rfl⟩ := hπ t
  set z : X := g⁻¹ * α g with hzdef
  have hzker : z ∈ π.ker := by
    rw [MonoidHom.mem_ker, hzdef, map_mul, map_inv, hαβ, show β (π g) = π g from ht,
      inv_mul_cancel]
  have hαg : α g = g * z := by rw [hzdef, mul_inv_cancel_left]
  have hz : ∀ k : ℕ, (α ^ k) z = z := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, MulAut.mul_apply, hαZ z hzker, ih]
  have hg : ∀ k : ℕ, (α ^ k) g = g * z ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, MulAut.mul_apply, hαg, map_mul, ih, hz, pow_succ, mul_assoc]
  have hzp : z ^ p = 1 := by
    have h1 := hg p
    rw [hαp, MulAut.one_apply] at h1
    have h2 : g * z ^ p = g * 1 := by rw [mul_one]; exact h1.symm
    exact mul_left_cancel h2
  refine ⟨g, ?_, rfl⟩
  rw [mem_fixSubgroup, hαg, hZp z hzker hzp, mul_one]

theorem compNormal_of_lift {X T : Type*} [Group X] [Group T] (π : X →* T)
    (hπ : Function.Surjective π) (α : MulAut X) (β : MulAut T) (hαβ : ∀ x, π (α x) = β (π x))
    {p : ℕ} (hαp : α ^ p = 1) (hαZ : ∀ z ∈ π.ker, α z = z)
    (hZp : ∀ z ∈ π.ker, z ^ p = 1 → z = 1) {ι : Type*} (F : ι → Subgroup X)
    (hFn : ∀ i, ∀ c ∈ fixSubgroup α, ∀ g ∈ F i, c * g * c⁻¹ ∈ F i)
    (hcomp : ∀ K : Subgroup T, IsComponentOf K (fixSubgroup β) → ∃ i, K = (F i).map π) :
    CompNormal β := by
  intro K hK t ht
  obtain ⟨i, rfl⟩ := hcomp K hK
  obtain ⟨g, hg, rfl⟩ := exists_lift_mem_fixSubgroup π hπ α β hαβ hαp hαZ hZp ht
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨g * f * g⁻¹, hFn i g hg f hf, by simp only [map_mul, map_inv]⟩
  · rintro ⟨f, hf, hfe⟩
    refine ⟨g⁻¹ * f * g⁻¹⁻¹, hFn i g⁻¹ (inv_mem hg) f hf, ?_⟩
    rw [map_mul, map_mul, map_inv, inv_inv, hfe]
    group

theorem compNormal_of_unique {S : Type*} [Group S] (β : MulAut S)
    (h : ∀ K K' : Subgroup S, IsComponentOf K (fixSubgroup β) →
      IsComponentOf K' (fixSubgroup β) → K = K') : CompNormal β := by
  intro K hK t ht
  have hK' := CFSG.HardMathSupport.Solomon.Coordinator.gfr2_isComponentOf_gLBConj hK (inv_mem ht)
  have heq : K.map (MulAut.conj t).toMonoidHom = K := by
    have := h _ _ hK' hK
    simpa only [GLBConj, inv_inv] using this
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    rw [← heq]
    exact ⟨k, hk, rfl⟩
  · intro hk
    rw [← heq] at hk
    obtain ⟨k', hk', hkk⟩ := hk
    have : k' = k := by
      have h1 : t * k' * t⁻¹ = t * k * t⁻¹ := by simpa [MulAut.conj_apply] using hkk
      simpa using h1
    rwa [← this]

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
