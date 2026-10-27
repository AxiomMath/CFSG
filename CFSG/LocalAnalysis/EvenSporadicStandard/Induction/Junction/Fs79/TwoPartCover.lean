module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Defs
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover
public import CFSG.LieType.Steinberg.CentralExt.LinearPerfect

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.LieType.Steinberg CFSG.LocalAnalysis.ComponentInitial

theorem two_kernel_card_le {Q : Type} [Group Q]
    (hQ : Nonempty (Q ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel Q .PSL 2 p f)
    {P : Type} [Group P] [Finite P] [Group.IsPerfect P] (η : P →* Q)
    (hη : Function.Surjective η) (hC : η.ker ≤ center P) (h2 : IsPGroup 2 η.ker) :
    Nat.card η.ker ≤ 2 := by
  rcases hQ with ⟨⟨e⟩⟩ | ⟨p, f, hp, hp2, hmodel⟩
  · have hker : (e.toMonoidHom.comp η).ker = η.ker := by
      ext x
      simp [MonoidHom.mem_ker]
    have := alternating_perfect_central_two_kernel_order_at_most_two (n := 7) (by norm_num)
      (e.toMonoidHom.comp η) (e.surjective.comp hη) (hker ▸ hC) (hker ▸ h2)
    rwa [hker] at this
  · exact odd_linear_two_perfect_central_two_kernel_order_at_most_two hp2 inferInstance hη hC h2
      hmodel

theorem card_le_two_of_two_subgroup_center {A : Type} [Group A] [Finite A] [Group.IsPerfect A]
    (h : ExcType A) {Z : Subgroup A} (hZ : Z ≤ center A) (h2 : IsPGroup 2 Z) :
    Nat.card Z ≤ 2 := by
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup A, N = oddPart (center A) le_rfl := ⟨_, rfl⟩
  have hmemN : ∀ c, c ∈ N ↔ c ∈ center A ∧ Odd (orderOf c) := fun c => by rw [hNdef]; rfl
  have : N.Normal := hNdef ▸ oddPart_normal (center A) le_rfl
  have hNle : N ≤ (QuotientGroup.mk' (center A)).ker := by
    rw [QuotientGroup.ker_mk']
    exact fun x hx => ((hmemN x).1 hx).1
  let η : A ⧸ N →* A ⧸ center A := QuotientGroup.lift N (QuotientGroup.mk' (center A)) hNle
  have hη : Function.Surjective η := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨x, rfl⟩
  have hker : η.ker = (center A).map (QuotientGroup.mk' N) := by
    rw [QuotientGroup.ker_lift N (QuotientGroup.mk' (center A)) hNle, QuotientGroup.ker_mk']
  have hcen : η.ker ≤ center (A ⧸ N) := by
    rw [hker]
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    exact congrArg (QuotientGroup.mk (s := N)) (Subgroup.mem_center_iff.1 hc g)
  have h2' : IsPGroup 2 η.ker := by
    rintro ⟨x, hx⟩
    rw [hker] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨a, ha⟩ := exists_pow_two_pow_mem_oddPart (le_rfl : center A ≤ center A) hc
    refine ⟨a, Subtype.ext ?_⟩
    change (QuotientGroup.mk' N c) ^ 2 ^ a = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hNdef]
    exact ha
  have hbound : Nat.card η.ker ≤ 2 := two_kernel_card_le h η hη hcen h2'
  let f : Z →* A ⧸ N := (QuotientGroup.mk' N).comp Z.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have hsN : (s : A) ∈ N := (QuotientGroup.eq_one_iff _).1 hs
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 h2) s
    have hk' : orderOf (s : A) = 2 ^ k := by
      rw [Subgroup.orderOf_coe, hk]
    exact Subtype.ext (eq_one_of_odd_orderOf ((hmemN _).1 hsN).2 hk')
  have hrange : ∀ s, f s ∈ η.ker := fun s => by
    rw [hker]
    exact ⟨(s : A), hZ s.2, rfl⟩
  let f' : Z →* η.ker := f.codRestrict _ hrange
  have hf' : Function.Injective f' := fun s t h => hf (congrArg Subtype.val h)
  exact (Nat.card_le_card_of_injective _ hf').trans hbound

end CFSG.EvenSporadicStandard.Induction.Junction
