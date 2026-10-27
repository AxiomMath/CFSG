module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

@[expose] def fixPPrime (p : ℕ) {S : Type*} [Group S] (E : Subgroup (MulAut S)) : Set S :=
  {x | ¬ p ∣ orderOf x ∧ ∃ α ∈ E, α ≠ 1 ∧ α x = x}

@[expose] def PPrimeGenAt (p : ℕ) (S : Type*) [Group S] : Prop :=
  ∀ E : Subgroup (MulAut S), CFSG.Open.IsElemAbelian p E → Nat.card E = p ^ 2 →
    Subgroup.closure (fixPPrime p E) = ⊤

@[expose] def NoElemSq (p : ℕ) (S : Type*) [Group S] : Prop :=
  ∀ E : Subgroup (MulAut S), CFSG.Open.IsElemAbelian p E → Nat.card E ≠ p ^ 2

variable {p : ℕ} {S T : Type*} [Group S] [Group T]

theorem PPrimeGenAt.of_noElemSq (h : NoElemSq p S) : PPrimeGenAt p S :=
  fun E hE hc => (h E hE hc).elim

private theorem fixPPrime_map_congr (e : S ≃* T) (E : Subgroup (MulAut S)) :
    fixPPrime p (E.map (MulAut.congr e).toMonoidHom) = e '' fixPPrime p E := by
  ext x
  constructor
  · rintro ⟨hx, _, ⟨α, hα, rfl⟩, hne, hfix⟩
    refine ⟨e.symm x, ⟨by rwa [MulEquiv.orderOf_eq], α, hα, ?_, ?_⟩, by simp⟩
    · rintro rfl
      exact hne (map_one _)
    · simpa using congrArg e.symm hfix
  · rintro ⟨y, ⟨hy, α, hα, hne, hfix⟩, rfl⟩
    refine ⟨by rwa [MulEquiv.orderOf_eq], _, ⟨α, hα, rfl⟩, ?_, by simp [hfix]⟩
    intro h1
    exact hne ((MulAut.congr e).injective (h1.trans (map_one _).symm))

theorem NoElemSq.of_mulEquiv (e : S ≃* T) (h : NoElemSq p T) : NoElemSq p S := by
  intro E hE hc
  refine h _ (hE.map (MulAut.congr e).toMonoidHom) ?_
  rwa [Subgroup.card_map_of_injective (MulAut.congr e).injective]

theorem PPrimeGenAt.of_mulEquiv (e : S ≃* T) (h : PPrimeGenAt p T) : PPrimeGenAt p S := by
  intro E hE hc
  have h' := h _ (hE.map (MulAut.congr e).toMonoidHom)
    (by rwa [Subgroup.card_map_of_injective (MulAut.congr e).injective])
  rw [fixPPrime_map_congr] at h'
  rw [eq_top_iff]
  intro x _
  have h'' : Subgroup.closure (e.toMonoidHom '' fixPPrime p E) = ⊤ := h'
  have hx : e x ∈ (Subgroup.closure (fixPPrime p E)).map e.toMonoidHom := by
    rw [MonoidHom.map_closure, h'']
    exact Subgroup.mem_top _
  simpa using hx

theorem noElemSq_of_not_dvd [Finite S] (_hp : p.Prime)
    (h : ¬ p ^ 2 ∣ Nat.card (MulAut S)) : NoElemSq p S := by
  intro E _ hc
  exact h (hc ▸ Subgroup.card_subgroup_dvd_card E)

private theorem innerRange_normal : (MulAut.conj : S →* MulAut S).range.Normal := by
  refine ⟨fun _ ⟨g, hg⟩ β => ⟨β g, ?_⟩⟩
  subst hg
  ext x
  simp [MulAut.mul_apply, MulAut.inv_apply]

private theorem conj_injective_of_center (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
  intro g hg
  rw [Subgroup.mem_center_iff]
  intro h
  have := DFunLike.congr_fun (MonoidHom.mem_ker.mp hg) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  nth_rewrite 1 [← this]
  group

theorem noElemSq_of_inner [Finite S] (hp : p.Prime) (hZ : Subgroup.center S = ⊥)
    (hidx : ¬ p ∣ (MulAut.conj : S →* MulAut S).range.index)
    (hcyc : ∀ P : Subgroup S, IsPGroup p P → IsCyclic P) : NoElemSq p S := by
  intro E hE hc
  set I := (MulAut.conj : S →* MulAut S).range
  have : I.Normal := innerRange_normal
  have hEI : E ≤ I := by
    have h1 : I.relIndex E ∣ p ^ 2 := hc ▸ (I.subgroupOf E).index_dvd_card
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp h1
    have hk0 : k = 0 := by
      by_contra h0
      exact hidx ((dvd_pow_self p h0).trans (hk' ▸ I.relIndex_dvd_index_of_normal E))
    exact Subgroup.relIndex_eq_one.mp (by rw [hk', hk0, pow_zero])
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := conj_injective_of_center hZ
  set P := E.comap (MulAut.conj : S →* MulAut S)
  have hP : Nat.card P = p ^ 2 := by
    rw [← hc, ← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq_self hEI]
  have hexp : ∀ y : P, y ^ p = 1 := fun y => Subtype.ext (hinj (by
    simpa using hE.2 _ (Subgroup.mem_comap.mp y.2)))
  have hcP := hcyc P (fun y => ⟨1, by simpa using hexp y⟩)
  have h2 : p ^ 2 ∣ p := by
    rw [← hP, ← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hexp
  exact absurd (Nat.le_of_dvd hp.pos h2) (by
    have := hp.two_le; nlinarith)

theorem closure_fixPPrime_map_conj (β : MulAut S) (E : Subgroup (MulAut S)) :
    Subgroup.closure (fixPPrime p (E.map (MulAut.conj β).toMonoidHom)) =
      (Subgroup.closure (fixPPrime p E)).map β.toMonoidHom := by
  have h : (MulAut.conj β).toMonoidHom = (MulAut.congr β).toMonoidHom := by
    ext α x
    simp [MulAut.mul_apply, MulAut.inv_apply]
  rw [h, fixPPrime_map_congr, MonoidHom.map_closure]
  rfl

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
