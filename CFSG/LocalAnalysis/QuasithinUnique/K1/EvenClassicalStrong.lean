module

public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionQuotient
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.RankOneRecog

structure StronglyClosedWitness (X : Type) [Group X] (P A : Subgroup X) : Prop where
  sylow : IsSylowTwoOf P ⊤
  le : A ≤ P
  elem : IsElemAbelian 2 A
  closed : ∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ P → g⁻¹ * a * g ∈ A

@[expose] def NoStronglyClosedElemAbelian (X : Type) [Group X] : Prop :=
  ∀ P A : Subgroup X, StronglyClosedWitness X P A → A = ⊥

@[expose] def SylowCentralizingAutInner (X : Type) [Group X] : Prop :=
  ∀ Q : Subgroup X, IsSylowTwoOf Q ⊤ → ∀ β : X ≃* X, (∀ q ∈ Q, β q = q) →
    ∃ x : X, ∀ y : X, β y = x⁻¹ * y * x

section Basic

variable {X Y : Type} [Group X] [Group Y]

theorem isSylowTwoOf_top_iff {Q : Subgroup X} :
    IsSylowTwoOf Q ⊤ ↔ IsPGroup 2 Q ∧ ¬ 2 ∣ Q.index := by
  unfold IsSylowTwoOf
  rw [show (Q.subgroupOf ⊤).index = Q.index from Subgroup.relIndex_top_right Q]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨le_top, h.1, h.2⟩⟩

theorem isElemAbelian_mono {A B : Subgroup X} (hAB : A ≤ B) (hB : IsElemAbelian 2 B) :
    IsElemAbelian 2 A := CFSG.Open.IsElemAbelian.mono hB hAB

theorem StronglyClosedWitness.map {P A : Subgroup X} (h : StronglyClosedWitness X P A)
    (e : X ≃* Y) : StronglyClosedWitness Y (P.map e.toMonoidHom) (A.map e.toMonoidHom) := by
  refine ⟨?_, Subgroup.map_mono h.le, isElemAbelian_map h.elem e.toMonoidHom, ?_⟩
  · obtain ⟨hp, hi⟩ := isSylowTwoOf_top_iff.mp h.sylow
    refine isSylowTwoOf_top_iff.mpr ⟨hp.map e.toMonoidHom, ?_⟩
    rw [Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective]
    exact hi
  · rintro _ ⟨a, ha, rfl⟩ g hg
    obtain ⟨g', rfl⟩ := e.surjective g
    obtain ⟨p, hp, hpe⟩ := hg
    have hpe' : p = g'⁻¹ * a * g' := e.injective (by simpa using hpe)
    refine ⟨g'⁻¹ * a * g', h.closed a ha g' (hpe' ▸ hp), ?_⟩
    simp

theorem NoStronglyClosedElemAbelian.of_mulEquiv (e : X ≃* Y)
    (h : NoStronglyClosedElemAbelian Y) : NoStronglyClosedElemAbelian X := by
  intro P A hW
  have := h _ _ (hW.map e)
  exact (Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).mp this

theorem SylowCentralizingAutInner.of_mulEquiv (e : X ≃* Y) (h : SylowCentralizingAutInner Y) :
    SylowCentralizingAutInner X := by
  intro Q hQ β hβ
  have hQ' : IsSylowTwoOf (Q.map e.toMonoidHom) ⊤ := by
    obtain ⟨hp, hi⟩ := isSylowTwoOf_top_iff.mp hQ
    refine isSylowTwoOf_top_iff.mpr ⟨hp.map e.toMonoidHom, ?_⟩
    rw [Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective]
    exact hi
  obtain ⟨x, hx⟩ := h _ hQ' (e.symm.trans (β.trans e)) (by
    rintro _ ⟨q, hq, rfl⟩
    change e (β (e.symm (e q))) = e q
    rw [MulEquiv.symm_apply_apply, hβ q hq])
  refine ⟨e.symm x, fun y => ?_⟩
  have h1 := hx (e y)
  change e (β (e.symm (e y))) = x⁻¹ * e y * x at h1
  rw [MulEquiv.symm_apply_apply] at h1
  apply e.injective
  rw [h1]
  simp

variable [Finite X]

theorem noStronglyClosedElemAbelian_of_sylow (Q₀ : Subgroup X) (hQ₀ : IsSylowTwoOf Q₀ ⊤)
    (h : ∀ A : Subgroup X, StronglyClosedWitness X Q₀ A → A = ⊥) :
    NoStronglyClosedElemAbelian X := by
  intro Q A hW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hi⟩ := isSylowTwoOf_top_iff.mp hW.sylow
  obtain ⟨hp₀, hi₀⟩ := isSylowTwoOf_top_iff.mp hQ₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (hp.toSylow hi) (hp₀.toSylow hi₀)
  have hQ : Q₀ = Q.map (MulAut.conj g).toMonoidHom := by
    have := congrArg (fun T : Sylow 2 X => (T : Subgroup X)) hg
    exact this.symm
  have hmem : ∀ x, x ∈ Q₀ ↔ g⁻¹ * x * g ∈ Q := by
    intro x
    rw [hQ]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hy
    · intro hx
      refine ⟨g⁻¹ * x * g, hx, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have hA : StronglyClosedWitness X Q₀ (A.map (MulAut.conj g).toMonoidHom) := by
    refine ⟨hQ₀, ?_, isElemAbelian_map hW.elem _, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩
      rw [hQ]
      exact ⟨a, hW.le ha, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩ k hk
      have hk' : (g⁻¹ * k * g)⁻¹ * a * (g⁻¹ * k * g) ∈ Q := by
        have := (hmem _).mp hk
        simpa [MulAut.conj_apply, mul_assoc] using this
      have h2 := hW.closed a ha (g⁻¹ * k * g) hk'
      refine ⟨_, h2, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have := h _ hA
  exact (Subgroup.map_eq_bot_iff_of_injective (f := (MulAut.conj g).toMonoidHom) _
    (MulAut.conj g).injective).mp this

theorem exists_ne_one_mem_centralizer {Q A : Subgroup X} (hQ : IsPGroup 2 Q) (hAQ : A ≤ Q)
    (hAn : ∀ a ∈ A, ∀ q ∈ Q, q⁻¹ * a * q ∈ A) (hne : A ≠ ⊥) :
    ∃ a ∈ A, a ≠ 1 ∧ ∀ q ∈ Q, q * a = a * q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent Q := hQ.isNilpotent
  let A' : Subgroup Q := A.subgroupOf Q
  have hA'n : A'.Normal := ⟨fun a ha q => by
    have h := hAn (a : X) ha (q : X)⁻¹ (Q.inv_mem q.2)
    simpa [A', Subgroup.mem_subgroupOf, mul_assoc] using h⟩
  have hA'ne : A' ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro a ha
    have : (⟨a, hAQ ha⟩ : Q) ∈ A' := ha
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hA'ne
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcen
  have hxA : (x : Q) ∈ A' := x.2.1
  have hxc : (x : Q) ∈ Subgroup.center Q := x.2.2
  refine ⟨((x : Q) : X), hxA, ?_, fun q hq => ?_⟩
  · intro h
    apply hx1
    apply Subtype.ext
    apply Subtype.ext
    exact h
  · have := Subgroup.mem_center_iff.mp hxc ⟨q, hq⟩
    exact congrArg Subtype.val this

theorem sylowCentralizingAutInner_of_sylow (Q₀ : Subgroup X) (hQ₀ : IsSylowTwoOf Q₀ ⊤)
    (h : ∀ β : X ≃* X, (∀ q ∈ Q₀, β q = q) → ∃ x : X, ∀ y : X, β y = x⁻¹ * y * x) :
    SylowCentralizingAutInner X := by
  intro Q hQ β hβ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hi⟩ := isSylowTwoOf_top_iff.mp hQ
  obtain ⟨hp₀, hi₀⟩ := isSylowTwoOf_top_iff.mp hQ₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (hp.toSylow hi) (hp₀.toSylow hi₀)
  have hQ : Q₀ = Q.map (MulAut.conj g).toMonoidHom := by
    have := congrArg (fun T : Sylow 2 X => (T : Subgroup X)) hg
    exact this.symm
  have hmem : ∀ x, x ∈ Q₀ → g⁻¹ * x * g ∈ Q := by
    intro x hx
    rw [hQ] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa [MulAut.conj_apply, mul_assoc] using hy
  obtain ⟨x, hx⟩ := h ((MulAut.conj g⁻¹).trans (β.trans (MulAut.conj g))) (by
    intro q hq
    have h1 := hβ _ (hmem q hq)
    simp only [MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
    rw [h1]
    group)
  refine ⟨g⁻¹ * x * g, fun y => ?_⟩
  have h1 := hx (g * y * g⁻¹)
  simp only [MulEquiv.trans_apply, MulAut.conj_apply, inv_inv] at h1
  have h2 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
  rw [h2] at h1
  have h3 : β y = g⁻¹ * (x⁻¹ * (g * y * g⁻¹) * x) * g := by
    rw [← h1]
    group
  rw [h3]
  group

end Basic

end CFSG.QuasithinUnique.K1
