module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHLoc
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHS5
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHFix

public section

namespace CFSG.EvenSporadicStandard.TwoHS

namespace SignS9

open Equiv Equiv.Perm Subgroup

variable {α : Type*} [Fintype α] [DecidableEq α] {τ : Perm α} {D S : Subgroup (Perm α)}
  {eD : D ≃* DihedralGroup 4} {eS : S ≃* Perm (Fin 5)}

theorem cycleType_tau (h : LocalPair τ D S eD eS) (hα : Fintype.card α = 9) :
    τ.cycleType = {2, 2} :=
  cycleType_eq_two_two hα (tau_ne_one h) h.tau_sq (card_centralizer h)

theorem card_fixedPoints_tau (h : LocalPair τ D S eD eS) (hα : Fintype.card α = 9) :
    Fintype.card (Function.fixedPoints τ) = 5 :=
  card_fixedPoints_of_cycleType_eq_two_two hα (cycleType_tau h hα)

theorem sign_tau (h : LocalPair τ D S eD eS) (hα : Fintype.card α = 9) : sign τ = 1 :=
  sign_eq_one_of_cycleType_eq_two_two (cycleType_tau h hα)

theorem card_perm_fixedPoints (h : LocalPair τ D S eD eS) (hα : Fintype.card α = 9) :
    Nat.card (Perm (Function.fixedPoints τ)) = 120 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, card_fixedPoints_tau h hα]
  rfl

theorem fix_of_mem_left (h : LocalPair τ D S eD eS) (hα : Fintype.card α = 9) {d : Perm α}
    (hd : d ∈ D) {x : α} (hx : τ x = x) : d x = x := by
  let ρD : D →* Perm (Function.fixedPoints τ) :=
    (fixRestrict τ).comp (Subgroup.inclusion (left_le_centralizer h))
  have hnorm : ρD.range.Normal := by
    refine ⟨?_⟩
    rintro _ ⟨d₁, rfl⟩ u
    obtain ⟨g, rfl⟩ := fixRestrict_surjective τ u
    have hmem := conj_mem_left h (mem_centralizer_singleton_iff.1 g.2) d₁.2
    refine ⟨⟨(g : Perm α) * d₁ * (g : Perm α)⁻¹, hmem⟩, ?_⟩
    have hinc : Subgroup.inclusion (left_le_centralizer h)
        ⟨(g : Perm α) * d₁ * (g : Perm α)⁻¹, hmem⟩ =
        g * Subgroup.inclusion (left_le_centralizer h) d₁ * g⁻¹ := rfl
    change fixRestrict τ _ = _
    rw [hinc, map_mul, map_mul, map_inv]
    rfl
  have hcard : Nat.card ρD.range ∣ 8 := by
    rw [← card_of_equiv_dihedral eD]
    exact Subgroup.card_dvd_of_surjective ρD.rangeRestrict_surjective
  have hbot := eq_bot_of_normal_card_dvd_eight (card_fixedPoints_tau h hα) ρD.range hcard
  have h1 : ρD ⟨d, hd⟩ = 1 := by
    have : ρD ⟨d, hd⟩ ∈ ρD.range := ⟨_, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this
  exact congrArg (fun u : Perm (Function.fixedPoints τ) => (u ⟨x, hx⟩ : α)) h1

theorem mem_left_of_fix (h : LocalPair τ D S eD eS) (hα : Fintype.card α = 9) {g : Perm α}
    (hg : g ∈ centralizer ({τ} : Set (Perm α))) (hfix : ∀ x, τ x = x → g x = x) : g ∈ D := by
  have hle : D.subgroupOf (centralizer {τ}) ≤ (fixRestrict τ).ker := fun g hg =>
    (mem_ker_fixRestrict_iff τ g).2 fun x hx => fix_of_mem_left h hα hg hx
  have hcardker : Nat.card (fixRestrict τ).ker = 8 := by
    have h1 := (fixRestrict τ).ker.card_mul_index
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 (fixRestrict_surjective τ),
      Subgroup.card_top, card_perm_fixedPoints h hα, card_centralizer h] at h1
    omega
  have hcardD : Nat.card (D.subgroupOf (centralizer {τ})) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (left_le_centralizer h)).toEquiv,
      card_of_equiv_dihedral eD]
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcardker, hcardD])
  have hmem : (⟨g, hg⟩ : centralizer ({τ} : Set (Perm α))) ∈ (fixRestrict τ).ker :=
    (mem_ker_fixRestrict_iff τ _).2 hfix
  rw [← heq] at hmem
  exact hmem

theorem sign_eq_neg_one_of_mem_left (h : LocalPair τ D S eD eS) (hα : Fintype.card α = 9)
    {d : Perm α} (hd : d ∈ D) (h4 : orderOf d = 4) : sign d = -1 := by
  refine sign_eq_neg_one_of_orderOf_eq_four h4 ?_
  have hsub : d.support ⊆ τ.support := by
    intro x hx
    rw [mem_support] at hx ⊢
    exact fun hτ => hx (fix_of_mem_left h hα hd hτ)
  rw [← card_support_of_cycleType_eq_two_two (cycleType_tau h hα)]
  exact Finset.card_le_card hsub

theorem sign_eq_sign_fixRestrict (h : LocalPair τ D S eD eS) (hα : Fintype.card α = 9)
    {s : Perm α} (hs : s ∈ S) :
    sign s = sign (fixRestrict τ ⟨s, right_le_centralizer h hs⟩) := by
  set u := fixRestrict τ ⟨s, right_le_centralizer h hs⟩ with hu
  have htC := ofSubtype_mem_centralizer τ u
  have hker : (⟨s, right_le_centralizer h hs⟩ * ⟨ofSubtype u, htC⟩⁻¹ :
      centralizer ({τ} : Set (Perm α))) ∈ (fixRestrict τ).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, fixRestrict_ofSubtype, ← hu, mul_inv_cancel]
  have hsU : s * (ofSubtype u)⁻¹ ∈ D :=
    mem_left_of_fix h hα (Subgroup.mul_mem _ (right_le_centralizer h hs)
      (Subgroup.inv_mem _ htC)) ((mem_ker_fixRestrict_iff τ _).1 hker)
  have hcomm : ∀ d ∈ D, s * (ofSubtype u)⁻¹ * d = d * (s * (ofSubtype u)⁻¹) := by
    intro d hd
    have h1 : Commute s d := (h.comm d hd s hs).symm
    have h2 : Commute (ofSubtype u) d := by
      refine Disjoint.commute fun x => ?_
      by_cases hx : τ x = x
      · exact Or.inr (fix_of_mem_left h hα hd hx)
      · exact Or.inl (ofSubtype_apply_of_not_mem u hx)
    exact h1.mul_left h2.inv_left
  have hsU1 : sign (s * (ofSubtype u)⁻¹) = 1 := by
    rcases eq_one_or_eq_tau h hsU hcomm with h1 | h1
    · rw [h1, map_one]
    · rw [h1, sign_tau h hα]
  calc sign s = sign (s * (ofSubtype u)⁻¹) * sign (ofSubtype u) := by
        rw [← map_mul, inv_mul_cancel_right]
    _ = sign u := by rw [hsU1, one_mul, sign_ofSubtype]

theorem sign_eq_neg_one_of_mem_right (h : LocalPair τ D S eD eS) (hα : Fintype.card α = 9)
    (s : S) (hs : sign (eS s) = -1) : sign (s : Perm α) = -1 := by
  let ρS : S →* Perm (Function.fixedPoints τ) :=
    (fixRestrict τ).comp (Subgroup.inclusion (right_le_centralizer h))
  have hinj : Function.Injective ρS := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have hker : (⟨(t : Perm α), right_le_centralizer h t.2⟩ :
        centralizer ({τ} : Set (Perm α))) ∈ (fixRestrict τ).ker := ht
    have hD : (t : Perm α) ∈ D :=
      mem_left_of_fix h hα (right_le_centralizer h t.2) ((mem_ker_fixRestrict_iff τ _).1 hker)
    exact Subtype.ext (h.inf _ hD t.2)
  have hbij : Function.Bijective ρS :=
    hinj.bijective_of_nat_card_le (by rw [card_perm_fixedPoints h hα, card_of_equiv_perm_five eS])
  have : Nontrivial (Function.fixedPoints τ) :=
    Fintype.one_lt_card_iff_nontrivial.1 (by rw [card_fixedPoints_tau h hα]; norm_num)
  let ψ : Perm (Fin 5) →* ℤˣ := (sign.comp S.subtype).comp eS.symm.toMonoidHom
  have hψ : Function.Surjective ψ := by
    intro ε
    rcases Int.units_eq_one_or ε with rfl | rfl
    · exact ⟨1, map_one ψ⟩
    · obtain ⟨u, hu⟩ := sign_surjective (Function.fixedPoints τ) (-1)
      obtain ⟨s₀, rfl⟩ := hbij.2 u
      refine ⟨eS s₀, ?_⟩
      change sign (((eS.symm (eS s₀) : S)) : Perm α) = -1
      rw [MulEquiv.symm_apply_apply, sign_eq_sign_fixRestrict h hα s₀.2]
      exact hu
  have h2 := congrArg (fun f : Perm (Fin 5) →* ℤˣ => f (eS s)) (eq_sign_of_surjective_hom hψ)
  change sign (((eS.symm (eS s) : S)) : Perm α) = sign (eS s) at h2
  rwa [MulEquiv.symm_apply_apply, hs] at h2

end SignS9

end CFSG.EvenSporadicStandard.TwoHS
