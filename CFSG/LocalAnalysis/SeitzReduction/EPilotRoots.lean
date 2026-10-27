module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotRoots
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEInnerRoots

public section

namespace CFSG.SeitzReduction.EPilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

@[expose] def perpRoots (τ : Tag) : Set (Fin τ.rank → ℤ) :=
  {γ | IsRoot τ γ ∧ γ (highNode τ) = 0}

@[expose] noncomputable def highRootSL2
    (τ : Tag) (K : Type) [Field K] : Subgroup (ModGL τ K) :=
  rootSubgroup τ K (highRoot τ) ⊔ rootSubgroup τ K (-highRoot τ)

theorem iform_highRoot_single (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (j : Fin τ.rank) :
    iform (highRoot τ) (Pi.single j 1) = if j = highNode τ then 1 else 0 := by
  rcases hτ with rfl | rfl | rfl <;> revert j <;> decide +kernel

theorem iform_highRoot (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (v : Fin τ.rank → ℤ) :
    iform (highRoot τ) v = v (highNode τ) := by
  rw [F4Pilot.iform_eq_sum_mul_iform_single]
  simp only [iform_highRoot_single hτ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem highRoot_highNode (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : highRoot τ (highNode τ) = 2 := by
  rcases hτ with rfl | rfl | rfl <;> rfl

theorem iform_highRoot_self (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    iform (highRoot τ) (highRoot τ) = 2 := by
  rw [iform_highRoot hτ, highRoot_highNode hτ]

theorem corootPair_highRoot (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (v : Fin τ.rank → ℤ) :
    corootPair (highRoot τ) v = v (highNode τ) := by
  rw [corootPair, iform_highRoot hτ, iform_highRoot_self hτ]
  omega

theorem sum_highRoot_mul_cartan (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (l : Fin τ.rank) :
    ∑ j, highRoot τ j * τ.cartan j l = if l = highNode τ then 1 else 0 := by
  rcases hτ with rfl | rfl | rfl <;> revert l <;> decide +kernel

theorem exists_iform_single_highNode (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∃ i : Fin τ.rank, iform (Pi.single i 1 : Fin τ.rank → ℤ) (Pi.single (highNode τ) 1) = -1 := by
  rcases hτ with rfl | rfl | rfl
  · exact ⟨(3 : Fin 6), by decide +kernel⟩
  · exact ⟨(2 : Fin 7), by decide +kernel⟩
  · exact ⟨(6 : Fin 8), by decide +kernel⟩

@[expose] def coeffCheck (τ : Tag) : Bool :=
  (List.range τ.rootCertificate.roots.length).all fun k =>
    decide (iform (τ.rootCertificate.root k) (τ.rootCertificate.root k) = 2) &&
      decide (|τ.rootCertificate.root k (highNode τ)| ≤ 2) &&
      (!decide (τ.rootCertificate.root k (highNode τ) = 2) ||
        List.ofFn (τ.rootCertificate.root k) == List.ofFn (highRoot τ))

theorem coeffCheck_E6 : coeffCheck .E6 = true := by decide +kernel

theorem coeffCheck_E7 : coeffCheck .E7 = true := by decide +kernel

theorem coeffCheck_E8 : coeffCheck .E8 = true := by decide +kernel

theorem coeffCheck_eq_true (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : coeffCheck τ = true := by
  rcases hτ with rfl | rfl | rfl
  exacts [coeffCheck_E6, coeffCheck_E7, coeffCheck_E8]

section Membership

variable {γ : Fin τ.rank → ℤ}

theorem coeffCheck_sound (h : coeffCheck τ = true) (hγ : IsRoot τ γ) :
    iform γ γ = 2 ∧ |γ (highNode τ)| ≤ 2 ∧ (γ (highNode τ) = 2 → γ = highRoot τ) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hγ
  simp only [coeffCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h k hk
  refine ⟨h1, h2, fun h4 => ?_⟩
  rcases h3 with h3 | h3
  · exact absurd h4 h3
  · exact RootCertificate.eq_of_ofFn_beq h3

theorem iform_self_eq_two (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hγ : IsRoot τ γ) : iform γ γ = 2 :=
  (coeffCheck_sound (coeffCheck_eq_true hτ) hγ).1

theorem abs_coeff_highNode_le_two
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hγ : IsRoot τ γ) : |γ (highNode τ)| ≤ 2 :=
  (coeffCheck_sound (coeffCheck_eq_true hτ) hγ).2.1

theorem eq_highRoot_of_coeff_highNode_eq_two
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hγ : IsRoot τ γ) (h : γ (highNode τ) = 2) :
    γ = highRoot τ :=
  (coeffCheck_sound (coeffCheck_eq_true hτ) hγ).2.2 h

theorem eq_neg_highRoot_of_coeff_highNode_eq_neg_two
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hγ : IsRoot τ γ) (h : γ (highNode τ) = -2) :
    γ = -highRoot τ := by
  have h' : (-γ) (highNode τ) = 2 := by rw [Pi.neg_apply, h]; norm_num
  rw [← eq_highRoot_of_coeff_highNode_eq_two hτ (IsRoot.neg hγ) h', neg_neg]

theorem abs_coeff_highNode_le_one
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hγ : IsRoot τ γ) (h1 : γ ≠ highRoot τ)
    (h2 : γ ≠ -highRoot τ) : |γ (highNode τ)| ≤ 1 := by
  have h := abs_le.1 (abs_coeff_highNode_le_two hτ hγ)
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · by_contra hc
    exact h2 (eq_neg_highRoot_of_coeff_highNode_eq_neg_two hτ hγ (by omega))
  · by_contra hc
    exact h1 (eq_highRoot_of_coeff_highNode_eq_two hτ hγ (by omega))

theorem mem_perpRoots_iff : γ ∈ perpRoots τ ↔ IsRoot τ γ ∧ γ (highNode τ) = 0 := Iff.rfl

theorem mem_perpRoots_iff_iform (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    γ ∈ perpRoots τ ↔ IsRoot τ γ ∧ iform (highRoot τ) γ = 0 := by
  rw [mem_perpRoots_iff, iform_highRoot hτ]

theorem neg_mem_perpRoots (h : γ ∈ perpRoots τ) : -γ ∈ perpRoots τ :=
  ⟨IsRoot.neg h.1, by rw [Pi.neg_apply, h.2, neg_zero]⟩

theorem single_mem_perpRoots {j : Fin τ.rank} (hj : j ≠ highNode τ) :
    (Pi.single j 1 : Fin τ.rank → ℤ) ∈ perpRoots τ :=
  ⟨isRoot_single τ j, Pi.single_eq_of_ne (Ne.symm hj) _⟩

theorem neg_single_mem_perpRoots {j : Fin τ.rank} (hj : j ≠ highNode τ) :
    (-Pi.single j 1 : Fin τ.rank → ℤ) ∈ perpRoots τ :=
  neg_mem_perpRoots (single_mem_perpRoots hj)

theorem iform_eq_zero_of_mem_perpRoots
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (h : γ ∈ perpRoots τ) : iform γ (highRoot τ) = 0 ∧ iform γ (-highRoot τ) = 0 := by
  have h0 : iform γ (highRoot τ) = 0 := by
    rw [iform_comm, iform_highRoot hτ, h.2]
  refine ⟨h0, ?_⟩
  rw [← neg_one_smul ℤ (highRoot τ), iform_smul_right, h0, mul_zero]

theorem highRoot_not_mem_perpRoots (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    highRoot τ ∉ perpRoots τ ∧ -highRoot τ ∉ perpRoots τ := by
  have h2 := highRoot_highNode hτ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h.2
    omega
  · have := h.2
    rw [Pi.neg_apply, h2] at this
    omega

end Membership

@[expose] def highRootWords : Tag → List ℕ
  | .E6 =>
    [2648458143306, 2648458134634, 2648458143242, 2648458134570, 2648457626218, 2646874531466, 0,
      165528633961, 0, 165528633417, 0, 165528633865, 0, 165528601641, 0, 165429658217, 0, 0,
      10345539624, 0, 10345539592, 10345537608, 0, 10345538056, 0, 10339353640, 0, 0, 646596231,
      646596135, 0, 0, 646596103, 646209607, 0, 646210055, 0, 0, 0, 40412262, 40388134, 0, 0,
      40412166, 40388102, 0, 0, 0, 2525765, 2524261, 0, 0, 2524165, 0, 0, 157860, 157764, 0, 156676,
      0, 0, 9859, 9795, 0, 0, 0, 610, 0, 33, 0, 0, 0]
  | .E7 =>
    [5083088884131702352, 5083088884131693680, 5083088884131702288, 5083088884131693616,
      5083088884131185264, 5083088882548090512, 5082917479433529520, 0, 317693055258231407, 0,
      317693055258230863, 0, 317693055258231311, 0, 317693055258199087, 0, 317693055159255663, 0,
      317682342464595599, 0, 0, 19855815953639470, 0, 19855815953639438, 19855815953637454, 0,
      19855815953637902, 0, 19855815947453486, 0, 19855146404037230, 0, 0, 1240988497102477,
      1240988497102381, 0, 0, 1240988497102349, 1240988496715853, 0, 1240988496716301, 0,
      1240946650252333, 0, 0, 0, 77561781068908, 77561781044780, 0, 0, 77561781068812,
      77561781044748, 77559165640780, 0, 77559165641228, 0, 0, 0, 4847611316811, 4847611315307,
      4847447852587, 0, 0, 0, 4847611315211, 4847447852555, 0, 0, 0, 0, 302975707306, 302975707210,
      302965490794, 0, 0, 302975706122, 302965490698, 0, 0, 0, 18935981705, 18935981641,
      18935343177, 0, 0, 18935342089, 0, 0, 0, 1183498856, 1183458952, 1183458888, 0, 1182950408, 0,
      0, 0, 73968679, 73966183, 73934407, 0, 0, 0, 0, 4623046, 4622886, 4620902, 0, 0, 0, 288933,
      288805, 0, 0, 18052, 17956, 0, 0, 1123, 0, 66, 0, 1, 0, 0, 0]
  | .E8 =>
    [76799839885757453283812772311213660, 76799839885757453283812772311204988,
      76799839885757453283812772311213596, 76799839885757453283812772311204924,
      76799839885757453283812772310696572, 76799839885757453283812770727601820,
      76799839885757453283641367613040828, 76799839885753397456731048176421596, 0,
      4799989992859840830238298269450875, 0, 4799989992859840830238298269450331, 0,
      4799989992859840830238298269450779, 0, 4799989992859840830238298269418555, 0,
      4799989992859840830238298170475131, 0, 4799989992859840830227585475815067, 0,
      4799989992859587341045690511026363, 0, 0, 299999374553740051889893641840698, 0,
      299999374553740051889893641840666, 299999374553740051889893641838682, 0,
      299999374553740051889893641839130, 0, 299999374553740051889893635654714, 0,
      299999374553740051889224092238458, 0, 299999374553724208815355656939162, 0, 0,
      18749960909608753243118352615065, 18749960909608753243118352614969, 0, 0,
      18749960909608753243118352614937, 18749960909608753243118352228441, 0,
      18749960909608753243118352228889, 0, 18749960909608753243076505764921, 0,
      18749960909607763050959728558713, 0, 0, 0, 1171872556850547077694897038456,
      1171872556850547077694897014328, 0, 0, 1171872556850547077694897038360,
      1171872556850547077694897014296, 1171872556850547077692281610328, 0,
      1171872556850547077692281610776, 0, 1171872556850485190684983034936, 0, 0, 0,
      73242034803159192355931064919, 73242034803159192355931063415, 73242034803159192355767600695,
      0, 0, 0, 73242034803159192355931063319, 73242034803159192355767600663,
      73242034803155324417811439703, 0, 73242034803155324417811440151, 0, 0, 0, 0,
      4577627175197449522245691574, 4577627175197449522245691478, 4577627175197449522235475062,
      4577627175197207776113215030, 0, 0, 0, 4577627175197449522245690390,
      4577627175197449522235474966, 4577627175197207776113214998, 0, 0, 0, 0, 0,
      286101698449840595140355733, 286101698449840595140355669, 286101698449840595139717205,
      286101698449825486007075957, 0, 0, 0, 286101698449840595139716117,
      286101698449825486007075861, 0, 0, 0, 0, 17881356153115037196272244,
      17881356153115037196232340, 17881356153115037196232276, 17881356153114092875442260, 0, 0,
      17881356153115037195723796, 17881356153114092875441172, 0, 0, 0, 0, 1117584759569689824767027,
      1117584759569689824764531, 1117584759569630804715155, 1117584759569689824732755,
      1117584759569630804715091, 0, 0, 1117584759569630804206611, 0, 0, 0, 0, 0,
      69849047473105614047954, 69849047473105614047794, 69849047473105614045810,
      69849047473101925294706, 69849047473101925262930, 0, 69849047473051494671378, 0, 0, 0, 0, 0,
      4365565467069100878001, 4365565467069100877873, 4365565467068870330929,
      4365565467068870328945, 4365565467065718416977, 0, 0, 0, 0, 0, 0, 272847841691818804880,
      272847841691804395696, 272847841691818804784, 272847841691804395568, 272847841691607401072, 0,
      0, 0, 0, 0, 17052990105738675311, 17052990105737774735, 17052990105737774639,
      17052990105725462575, 0, 0, 0, 0, 1065811881608667214, 1065811881608610926,
      1065811881607841422, 1065811881607841326, 0, 0, 0, 0, 66613242600541709, 66613242600538189,
      66613242600490093, 66613242599851565, 0, 0, 0, 0, 4163327662533868, 4163327662533644,
      4163327662530636, 4163327662490732, 0, 0, 0, 0, 260207978908363, 260207978908171,
      260207978905675, 0, 0, 0, 16262998681770, 16262998681610, 16262998679626, 0, 0, 0,
      1016437417609, 1016437417481, 0, 0, 63527338600, 63527338504, 0, 0, 3970458663, 3970458631, 0,
      0, 248153670, 248153638, 0, 0, 15509605, 0, 969348, 0, 60579, 0, 3778, 0, 225, 0, 0, 0]
  | _ => []

@[expose] def highRootWordsCheck (τ : Tag) : Bool :=
  (List.range τ.rootCertificate.roots.length).all fun k =>
    decide (height (τ.rootCertificate.root k) ≤ 0) ||
      wordPos τ.rootCertificate (decodeWord ((highRootWords τ).getD k 0)) k == (highRootPos τ).1

theorem highRootWordsCheck_E6 : highRootWordsCheck .E6 = true := by decide +kernel

theorem highRootWordsCheck_E7 : highRootWordsCheck .E7 = true := by decide +kernel

theorem highRootWordsCheck_E8 : highRootWordsCheck .E8 = true := by decide +kernel

theorem highRootWordsCheck_eq_true (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    highRootWordsCheck τ = true := by
  rcases hτ with rfl | rfl | rfl
  exacts [highRootWordsCheck_E6, highRootWordsCheck_E7, highRootWordsCheck_E8]

theorem root_highRootPos (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    (highRootPos τ).1 < τ.rootCertificate.roots.length ∧
      τ.rootCertificate.root (highRootPos τ).1 = highRoot τ := by
  rcases hτ with rfl | rfl | rfl <;>
    exact ⟨by decide +kernel, List.ofFn_injective (by decide +kernel)⟩

section Weyl

variable {γ : Fin τ.rank → ℤ}

theorem exists_smul_eq_highRoot_of_pos
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hγ : IsRoot τ γ) (hpos : 0 < height γ) :
    ∃ w : WeylGroup τ, w • γ = highRoot τ := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hγ
  have h := highRootWordsCheck_eq_true hτ
  simp only [highRootWordsCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  rcases h k hk with h1 | h2
  · exact absurd h1 (not_le.2 hpos)
  · refine ⟨weylOfWord τ (decodeWord ((highRootWords τ).getD k 0)), ?_⟩
    rw [← (wordPos_spec τ.rootCertificate_check _ hk).2, h2]
    exact (root_highRootPos hτ).2

theorem exists_smul_eq_highRoot
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hγ : IsRoot τ γ) :
    ∃ w : WeylGroup τ, w • γ = highRoot τ := by
  rcases lt_or_gt_of_ne hγ.height_ne_zero with hneg | hpos
  · obtain ⟨w, hw⟩ := exists_smul_eq_highRoot_of_pos hτ (IsRoot.neg hγ)
      (by rw [height_neg]; omega)
    refine ⟨rootReflection (highRoot τ) * w, ?_⟩
    rw [mul_smul, ← neg_neg (w • γ), ← smul_neg, hw, smul_neg,
      rootReflection_smul_self (isRoot_highRoot τ), neg_neg]
  · exact exists_smul_eq_highRoot_of_pos hτ hγ hpos

theorem exists_smul_highRoot_eq
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hγ : IsRoot τ γ) :
    ∃ w : WeylGroup τ, w • highRoot τ = γ := by
  obtain ⟨w, hw⟩ := exists_smul_eq_highRoot hτ hγ
  exact ⟨w⁻¹, by rw [← hw, inv_smul_smul]⟩

end Weyl

@[expose] def coverRoots : (τ : Tag) → List (Fin τ.rank → ℤ)
  | .E6 => [highRoot .E6, (Pi.single (5 : Fin 6) 1 : Fin 6 → ℤ),
      (Pi.single (2 : Fin 6) 1 : Fin 6 → ℤ)]
  | .E7 => [highRoot .E7, (Pi.single (6 : Fin 7) 1 : Fin 7 → ℤ),
      (Pi.single (3 : Fin 7) 1 : Fin 7 → ℤ)]
  | .E8 => [highRoot .E8, (Pi.single (1 : Fin 8) 1 : Fin 8 → ℤ),
      (Pi.single (5 : Fin 8) 1 : Fin 8 → ℤ)]
  | _ => []

theorem coverRoots_check (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    (∀ a ∈ coverRoots τ, ∀ b ∈ coverRoots τ, a ≠ b → iform a b = 0) ∧
      ∀ i j : Fin τ.rank, ∃ γ ∈ coverRoots τ,
        iform γ (Pi.single i 1) = 0 ∧ iform γ (Pi.single j 1) = 0 := by
  rcases hτ with rfl | rfl | rfl <;> decide +kernel

theorem isRoot_of_mem_coverRoots (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ coverRoots τ) : IsRoot τ γ := by
  have key : ∀ γ ∈ coverRoots τ, IsRoot τ γ := by
    rcases hτ with rfl | rfl | rfl <;>
      exact List.forall_mem_cons.2 ⟨isRoot_highRoot _, List.forall_mem_cons.2
        ⟨isRoot_single _ _, List.forall_mem_singleton.2 (isRoot_single _ _)⟩⟩
  exact key γ hγ

theorem highRoot_mem_coverRoots (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    highRoot τ ∈ coverRoots τ := by
  rcases hτ with rfl | rfl | rfl <;> exact List.mem_cons_self

theorem exists_weyl_smul_highRoot_eq
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ coverRoots τ) :
    ∃ w : WeylGroup τ, w • highRoot τ = γ :=
  exists_smul_highRoot_eq hτ (isRoot_of_mem_coverRoots hτ hγ)

local instance ePilotRootsNeZeroE6 : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def e6RepRoots : List (List (Fin (Tag.rank .E6) → ℤ)) :=
  [[Pi.single 0 1], [Pi.single 0 1, Pi.single 3 1], [Pi.single 0 1, Pi.single 3 1, Pi.single 5 1]]

@[expose] def e6PairPerp : List (Fin (Tag.rank .E6) → ℤ) :=
  [![1, 2, 2, 3, 2, 1], ![1, 1, 2, 2, 1, 1], ![1, 1, 2, 2, 1, 0], ![0, 1, 0, 1, 1, 1],
    ![0, 1, 0, 1, 1, 0], ![0, 0, 0, 0, 0, 1], ![-1, -2, -2, -3, -2, -1], ![-1, -1, -2, -2, -1, -1],
    ![-1, -1, -2, -2, -1, 0], ![0, -1, 0, -1, -1, -1], ![0, -1, 0, -1, -1, 0],
    ![0, 0, 0, 0, 0, -1]]

theorem e6RepRoots_check :
    (∀ S ∈ e6RepRoots, ∀ β ∈ S, β ∈ rootFinset .E6 ∧ β (highNode .E6) = 0) ∧
      (∀ S ∈ e6RepRoots, ∀ β ∈ S, ∀ β' ∈ S, β ≠ β' → iform β β' = 0) ∧
      ∀ γ ∈ rootFinset .E6, (∀ β ∈ ([Pi.single 0 1, Pi.single 3 1, Pi.single 5 1] :
        List (Fin (Tag.rank .E6) → ℤ)), iform γ β = 0) → γ = highRoot .E6 ∨ γ = -highRoot .E6 := by
  decide +kernel

theorem e6PairPerp_check :
    (∀ γ ∈ e6PairPerp, γ ∈ rootFinset .E6 ∧ iform γ (Pi.single 0 1) = 0 ∧
      iform γ (Pi.single 3 1) = 0) ∧
      (∀ γ ∈ rootFinset .E6, iform γ (Pi.single 0 1) = 0 → iform γ (Pi.single 3 1) = 0 →
        γ ∈ e6PairPerp) ∧ e6PairPerp.Nodup ∧ e6PairPerp.length = 12 ∧
      highRoot .E6 ∈ e6PairPerp ∧ -highRoot .E6 ∈ e6PairPerp := by
  decide +kernel

section E6Reps


theorem mem_perpRoots_of_mem_e6RepRoots {S : List (Fin (Tag.rank .E6) → ℤ)}
    (hS : S ∈ e6RepRoots) {β : Fin (Tag.rank .E6) → ℤ} (hβ : β ∈ S) : β ∈ perpRoots .E6 :=
  ⟨mem_rootFinset.1 (e6RepRoots_check.1 S hS β hβ).1, (e6RepRoots_check.1 S hS β hβ).2⟩

theorem eq_highRoot_or_neg_of_perp_e6Triple {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (h : ∀ β ∈ ([Pi.single 0 1, Pi.single 3 1, Pi.single 5 1] :
      List (Fin (Tag.rank .E6) → ℤ)),
      iform γ β = 0) : γ = highRoot .E6 ∨ γ = -highRoot .E6 :=
  e6RepRoots_check.2.2 γ (mem_rootFinset.2 hγ) h

end E6Reps

end CFSG.SeitzReduction.EPilot
