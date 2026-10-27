module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Cover
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.MultiplierCheck

public section

namespace CFSG.EvenSmallLie.OmegaEight.Cover

open Subgroup CFSG.RankThree.PerfectCover CFSG.LieType.Multipliers

theorem coverMap_ker_le_closure {X : Type} [Group X] {ι : Type*} {g : ι → X}
    {R : Set (FreeGroup ι)} {w : ι → FreeGroup ι} (hP : IsPresentation g R)
    (hwg : ∀ i, FreeGroup.lift g (w i) = g i) :
    (coverMap hP hwg).ker ≤ closure (PresentedGroup.mk (coverRelators R w) '' R) := by
  have hc : closure (PresentedGroup.mk (coverRelators R w) '' R) ≤
      center (PresentedCover R w) :=
    (closure_le _).2 (by rintro _ ⟨r, hr, rfl⟩; exact mk_mem_center w hr)
  have := normal_of_le_center hc
  intro x hx
  obtain ⟨f, rfl⟩ := PresentedGroup.mk_surjective _ x
  have hf : f ∈ normalClosure R := by
    rw [← hP.ker_lift]
    exact hx
  have hmap : (normalClosure R).map (PresentedGroup.mk (coverRelators R w)) ≤
      closure (PresentedGroup.mk (coverRelators R w) '' R) := by
    rw [map_normalClosure _ _ (PresentedGroup.mk_surjective _)]
    exact normalClosure_le_normal subset_closure
  exact hmap (mem_map_of_mem _ hf)

theorem sq_rhoWord_of_mem_rels {r : List (Fin 4 × Bool)}
    (hr : r ∈ rels) : rhoWord r ^ 2 = 1 := by
  have h := relator_sq_check
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  rw [sq]
  exact h r hr

theorem sq_rhoHom_of_mem_closure
    {c : Cov} (hc : c ∈ closure (PresentedGroup.mk
      (coverRelators (wordSet rels) fun i => FreeGroup.mk (commWords (pairs i))) '' wordSet rels)) :
    rhoHom c ^ 2 = 1 := by
  have hZ : closure (PresentedGroup.mk
      (coverRelators (wordSet rels) fun i => FreeGroup.mk (commWords (pairs i))) '' wordSet rels) ≤
      center Cov :=
    (closure_le _).2 (by rintro _ ⟨r, hr, rfl⟩; exact mk_mem_center _ hr)
  induction hc using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
    rw [rhoHom_mk]
    exact sq_rhoWord_of_mem_rels hv
  | one => rw [map_one, one_pow]
  | mul x y hx hy ihx ihy =>
    rw [map_mul, (Commute.map (mem_center_iff.1 (hZ hy) x) rhoHom).mul_pow, ihx, ihy, one_mul]
  | inv x hx ih => rw [map_inv, inv_pow, ih, inv_one]

theorem sq_rhoU_eq_one
    {m : U} (hm : m ∈ piU.ker) :
    rhoU m ^ 2 = 1 := by
  have h : coverEquiv.symm m ∈ (coverMap isPresentation_omegaT lift_commWords).ker := by
    rw [MonoidHom.mem_ker, ← hopfCoverMap_coverEquiv, MulEquiv.apply_symm_apply]
    exact hm
  exact sq_rhoHom_of_mem_closure (coverMap_ker_le_closure _ _ h)

theorem rhoU_sq_wordU :
    rhoU (wordU uWord ^ 2) = 1 := by
  rw [map_pow, rhoU_wordU, sq]
  exact rho_facts.1

theorem rhoU_tauEquiv_sq_wordU_ne_one :
    rhoU (tauEquiv (wordU uWord ^ 2)) ≠ 1 := by
  have hm₀ := inv_mul_tauEquiv_mem
  have hc : Commute (wordU tuWord) ((wordU tuWord)⁻¹ * tauEquiv (wordU uWord)) :=
    mem_center_iff.1 (hopfMultiplier_le_center hm₀) _
  rw [map_pow, show tauEquiv (wordU uWord) = wordU tuWord * ((wordU tuWord)⁻¹ *
    tauEquiv (wordU uWord)) by rw [mul_inv_cancel_left], hc.mul_pow, map_mul, map_pow, map_pow,
    sq_rhoU_eq_one hm₀, mul_one, rhoU_wordU, sq]
  exact rho_facts.2

theorem sq_eq_one_of_map_ne_one {U : Type*} [Group U] {M : Subgroup U} [Finite M]
    (hM4 : Nat.card M ≤ 4) (τ : U →* U) (hτM : ∀ m ∈ M, τ m ∈ M) {R : Type*} [Group R]
    (ρ : U →* R) (hρM : ∀ m ∈ M, ρ m ^ 2 = 1) {z : U} (hz : z ∈ M) (hρz : ρ z = 1)
    (hρτz : ρ (τ z) ≠ 1) {m : U} (hm : m ∈ M) : m ^ 2 = 1 := by
  by_contra hm2
  have hle : zpowers m ≤ M := zpowers_le.2 hm
  have hdvd : orderOf m ∣ Nat.card M := Nat.card_zpowers m ▸ card_dvd_of_le hle
  have h1 : orderOf m ≠ 1 := fun h => hm2 (by rw [orderOf_eq_one_iff.1 h, one_pow])
  have h2 : orderOf m ≠ 2 := fun h => hm2 (by rw [← h, pow_orderOf_eq_one])
  have hpos : 0 < Nat.card M := Nat.card_pos
  have h0 : 0 < orderOf m := Nat.pos_of_dvd_of_pos hdvd hpos
  have hM : zpowers m = M := eq_of_le_of_card_ge hle (by
    rw [Nat.card_zpowers, Nat.eq_of_dvd_of_lt_two_mul hpos.ne' hdvd (by omega)])
  obtain ⟨a, rfl⟩ := mem_zpowers_iff.1 (show z ∈ zpowers m by rw [hM]; exact hz)
  obtain ⟨b, hb⟩ := mem_zpowers_iff.1 (show τ (m ^ a) ∈ zpowers m by rw [hM]; exact hτM _ hz)
  have hρm : ρ m ≠ 1 := fun h => hρτz (by rw [← hb, map_zpow, h, one_zpow])
  obtain ⟨c, rfl | rfl⟩ := Int.even_or_odd' a
  · refine hρτz ?_
    rw [zpow_mul', zpow_two, ← sq, map_pow, map_pow]
    exact hρM _ (hτM _ (zpow_mem hm c))
  · refine hρm ?_
    have h2' : ρ m ^ (2 : ℤ) = 1 := by
      rw [zpow_two, ← sq]
      exact hρM m hm
    rwa [map_zpow, zpow_add, zpow_mul, h2', one_zpow, one_mul, zpow_one] at hρz

theorem sq_eq_one_of_mem_ker :
    ∀ m ∈ piU.ker, m ^ 2 = 1 := by
  obtain ⟨hfin, h4⟩ := card_hopfMultiplier_le
  exact fun m hm => sq_eq_one_of_map_ne_one h4 tauEquiv.toMonoidHom (fun _ => tauEquiv_mem) rhoU
    (fun _ => sq_rhoU_eq_one) sq_wordU_mem rhoU_sq_wordU rhoU_tauEquiv_sq_wordU_ne_one hm

theorem card_ker_piU :
    Nat.card piU.ker = 4 := by
  obtain ⟨hfin, h4⟩ := card_hopfMultiplier_le
  obtain ⟨hnd, -⟩ := mem_of_exponent_two hopfMultiplier_le_center h4 tauEquiv tauHat_cube
    (fun _ => tauEquiv_mem) rhoU sq_wordU_mem inv_mul_tauEquiv_mem
    (by rw [rhoU_wordU, sq]; exact rho_facts.1) (by rw [rhoU_wordU, sq]; exact rho_facts.2)
    sq_eq_one_of_mem_ker
  have h := length_le_card (M := piU.ker) hnd (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro g (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact sq_wordU_mem
    · exact tauEquiv_mem sq_wordU_mem
    · exact tauEquiv_mem (tauEquiv_mem sq_wordU_mem))
  simp only [List.length_cons, List.length_nil] at h
  exact le_antisymm h4 h

theorem isKleinFour_ker_piU :
    IsKleinFour piU.ker := by
  have h4 := card_ker_piU
  have : Finite piU.ker := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial piU.ker := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  refine ⟨h4, (Monoid.exponent_eq_prime_iff Nat.prime_two).2 fun g hg => orderOf_eq_prime ?_ hg⟩
  exact Subtype.ext ((SubgroupClass.coe_pow g 2).trans (sq_eq_one_of_mem_ker g g.2))

theorem nonempty_griessHopfMultiplier_mulEquiv :
    Nonempty (CFSG.Open.griessHopfMultiplier omegaT ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  have := isKleinFour_ker_piU
  obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := piU.ker)
    (G₂ := Multiplicative (ZMod 2 × ZMod 2))
  exact ⟨((hopfMultiplierEquivGriess omegaT).trans e).trans (MulEquiv.prodMultiplicative _ _)⟩

end CFSG.EvenSmallLie.OmegaEight.Cover
