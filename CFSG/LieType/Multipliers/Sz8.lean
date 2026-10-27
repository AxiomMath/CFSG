module

public import CFSG.LieType.Multipliers.Sz8Bridge
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import CFSG.LieType.Multipliers.Sz8Inputs
public import Certificates.Certificate10007
public meta import CFSG.LieType.Multipliers.Sz8Bridge

public section

namespace CFSG.LieType.Multipliers.Sz8

open Subgroup TauCeti CFSG.CosetTable CFSG.Open

theorem isKleinFour_of_card_le_four {K : Type*} [Group K] [Finite K] (hK : Nat.card K ≤ 4)
    {x y : K} (hxy : x * y = y * x) (h1 : x ≠ 1) (h2 : y ≠ 1) (h3 : x * y ≠ 1)
    (h4 : x * y⁻¹ ≠ 1) (h5 : x * x * y⁻¹ ≠ 1) (h6 : y * y * x⁻¹ ≠ 1) : IsKleinFour K := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hne : x ≠ y := fun h => h4 (by rw [h, mul_inv_cancel])
  have hx_xy : x ≠ x * y := fun h => h2 (by simpa using h)
  have hy_xy : y ≠ x * y := fun h => h1 (by simpa using h)
  set S : Finset K := {1, x, y, x * y}
  have hS : S.card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm h1, Ne.symm h2, Ne.symm h3]),
      Finset.card_insert_of_notMem (by simp [hne, hx_xy]),
      Finset.card_insert_of_notMem (by simp [hy_xy]), Finset.card_singleton]
  have hcard : Nat.card K = 4 := by
    refine le_antisymm hK ?_
    rw [← hS, Nat.card_eq_fintype_card]
    exact Finset.card_le_univ S
  have hmem : ∀ g : K, g ∈ S := by
    have huniv : S = Finset.univ :=
      Finset.eq_univ_of_card S (by rw [hS, ← Nat.card_eq_fintype_card, hcard])
    exact fun g => huniv ▸ Finset.mem_univ g
  have hxx : x * x = 1 := by
    rcases Finset.mem_insert.mp (hmem (x * x)) with h | h
    · exact h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · exact absurd (mul_eq_left.mp h) h1
    · exact absurd (by rw [h, mul_inv_cancel]) h5
    · exact absurd (mul_left_cancel h) hne
  have hyy : y * y = 1 := by
    rcases Finset.mem_insert.mp (hmem (y * y)) with h | h
    · exact h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · exact absurd (by rw [h, mul_inv_cancel]) h6
    · exact absurd (mul_eq_left.mp h) h2
    · exact absurd (mul_right_cancel h) (Ne.symm hne)
  have hsq : ∀ g : K, g ^ 2 = 1 := by
    intro g
    have h := hmem g
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact one_pow 2
    · rw [sq, hxx]
    · rw [sq, hyy]
    · rw [sq, mul_assoc, ← mul_assoc y, ← hxy, mul_assoc, hyy, mul_one, hxx]
  refine ⟨hcard, ?_⟩
  have hdvd : Monoid.exponent K ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (Monoid.exp_eq_one_iff.mp h |>.elim x 1) h1
  · exact h

theorem matCheck_wWord :
    matCheck [wWord 0 ++ [(0, false)], wWord 1 ++ [(1, false)]] = true :=
  Certificates.certificate10007.1

local macro "mem_tac" : tactic =>
  `(tactic| simp only [kerWords, relStrings, List.mem_cons, eq_self_iff_true, true_or, or_true])

theorem lift_genSz_wWord (i : Fin 2) :
    FreeGroup.lift genSz (FreeGroup.mk (wWord i)) = genSz i := by
  have h := matCheck_wWord
  rw [matCheck, List.all_eq_true] at h
  have h' := lift_genSz_eq_one (wordMat_eq_one (of_decide_eq_true (h (wWord i ++ [(i, false)]) (by
    fin_cases i
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self))))
  rw [← FreeGroup.mul_mk, map_mul, mul_eq_one_iff_eq_inv] at h'
  rw [h']
  change (FreeGroup.lift genSz (FreeGroup.of i)⁻¹)⁻¹ = _
  rw [map_inv, inv_inv, FreeGroup.lift_apply_of]

private theorem finite_congr {ι : Type*} {S T : Set (FreeGroup ι)} (h : S = T)
    [Finite (PresentedGroup S)] : Finite (PresentedGroup T) := by
  subst h; infer_instance

private theorem card_congr {ι : Type*} {S T : Set (FreeGroup ι)} (h : S = T) :
    Nat.card (PresentedGroup S) = Nat.card (PresentedGroup T) := by
  subst h; rfl

private theorem orderOf_mk_congr {ι : Type*} {S T : Set (FreeGroup ι)} (h : S = T)
    (x : FreeGroup ι) : orderOf (PresentedGroup.mk S x) = orderOf (PresentedGroup.mk T x) := by
  subst h; rfl

private theorem ne_one_of_two_dvd {G : Type*} [Group G] {g : G} (h : 2 ∣ orderOf g) : g ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at h
  omega

theorem card_cover_le : Finite (PG 2 (coverWords rels wWord)) ∧
    Nat.card (PG 2 (coverWords rels wWord)) ≤ 116480 :=
  Certificates.certificate10007.2.1

theorem two_dvd_orderOf_kerWords
    {u : List (Fin 2 × Bool)} (hu : (u, 2) ∈ kerWords) :
    2 ∣ orderOf (PresentedGroup.mk (wordSet (coverWords rels wWord)) (FreeGroup.mk u)) :=
  Certificates.certificate10007.2.2 u hu

theorem multiplier_of_mulEquiv
    {X : Type} [Group X] (e : suzukiGroup 1 ≃* X) :
    commutator X = ⊤ ∧ Nonempty (griessHopfMultiplier X ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  have hP := isPresentation e
  have hw : ∀ i, FreeGroup.mk (wWord i) ∈ commutator (FreeGroup (Fin 2)) :=
    fun i => mk_commWords_mem_commutator _
  have hwg : ∀ i, FreeGroup.lift (fun j => e (genSz j)) (FreeGroup.mk (wWord i)) = e (genSz i) :=
    fun i => by rw [lift_mulEquiv, lift_genSz_wWord]
  refine ⟨Group.isPerfect_def.mp (isPerfect_of_isPresentation hP hw hwg), ?_⟩
  have hX : Nat.card X = 29120 := by rw [← Nat.card_congr e.toEquiv, card_suzukiGroup]
  have hset := coverRelators_wordSet rels wWord
  obtain ⟨hfin, hle⟩ := card_cover_le
  have : Finite (PresentedCover (wordSet rels) fun i => FreeGroup.mk (wWord i)) :=
    finite_congr hset.symm
  have hPcard : Nat.card (PresentedCover (wordSet rels) fun i => FreeGroup.mk (wWord i)) ≤
      116480 := by
    rw [PresentedCover, card_congr hset]; exact hle
  have hK4 : Nat.card (coverMap hP hwg).ker ≤ 4 := by
    have h := (coverMap hP hwg).ker.card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (coverMap_surjective hP hwg)).toEquiv, hX] at h
    omega
  have hdvd : ∀ u, (u, 2) ∈ kerWords → 2 ∣ orderOf (PresentedGroup.mk
      (coverRelators (wordSet rels) fun i => FreeGroup.mk (wWord i)) (FreeGroup.mk u)) :=
    fun u hu => by rw [orderOf_mk_congr hset]; exact two_dvd_orderOf_kerWords hu
  have hr : ∀ s ∈ relStrings, PresentedGroup.mk
      (coverRelators (wordSet rels) fun i => FreeGroup.mk (wWord i))
      (FreeGroup.mk (parseWord s)) ∈ (coverMap hP hwg).ker := fun s hs => by
    rw [MonoidHom.mem_ker, coverMap_mk]
    exact hP.lift_eq_one (List.mem_map_of_mem (List.mem_map_of_mem hs))
  have hinv : ∀ u : List (Fin 2 × Bool), PresentedGroup.mk
      (coverRelators (wordSet rels) fun i => FreeGroup.mk (wWord i))
      (FreeGroup.mk (FreeGroup.invRev u)) = (PresentedGroup.mk _ (FreeGroup.mk u))⁻¹ :=
    fun u => by rw [← FreeGroup.inv_mk, map_inv]
  have happ : ∀ u v : List (Fin 2 × Bool), PresentedGroup.mk
      (coverRelators (wordSet rels) fun i => FreeGroup.mk (wWord i)) (FreeGroup.mk (u ++ v)) =
      PresentedGroup.mk _ (FreeGroup.mk u) * PresentedGroup.mk _ (FreeGroup.mk v) :=
    fun u v => by rw [← FreeGroup.mul_mk, map_mul]
  have hne : ∀ z : (coverMap hP hwg).ker, 2 ∣ orderOf z.1 → z ≠ 1 := fun z h hz =>
    ne_one_of_two_dvd h (by rw [hz]; rfl)
  obtain ⟨x, hx⟩ : ∃ x : (coverMap hP hwg).ker, x.1 = PresentedGroup.mk _
      (FreeGroup.mk (parseWord relFive)) := ⟨⟨_, hr relFive (by mem_tac)⟩, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : (coverMap hP hwg).ker, y.1 = PresentedGroup.mk _
      (FreeGroup.mk (parseWord relSeven)) := ⟨⟨_, hr relSeven (by mem_tac)⟩, rfl⟩
  have hcomm : x * y = y * x :=
    Subtype.ext (mem_center_iff.mp (coverMap_ker_le_center hP hwg y.2) x)
  have h5 := hdvd _ (show (parseWord relFive, 2) ∈ kerWords by mem_tac)
  have h7 := hdvd _ (show (parseWord relSeven, 2) ∈ kerWords by mem_tac)
  have h57 := hdvd _ (show (parseWord relFive ++ parseWord relSeven, 2) ∈ kerWords by mem_tac)
  have h57' := hdvd _ (show (parseWord relFive ++ FreeGroup.invRev (parseWord relSeven), 2) ∈
    kerWords by mem_tac)
  have h557 := hdvd _ (show (parseWord relFive ++ parseWord relFive ++
    FreeGroup.invRev (parseWord relSeven), 2) ∈ kerWords by mem_tac)
  have h775 := hdvd _ (show (parseWord relSeven ++ parseWord relSeven ++
    FreeGroup.invRev (parseWord relFive), 2) ∈ kerWords by mem_tac)
  rw [happ] at h57
  rw [happ, hinv] at h57'
  rw [happ, happ, hinv] at h557 h775
  rw [← hx] at h5
  rw [← hy] at h7
  rw [← hx, ← hy] at h57 h57' h557 h775
  have hK := isKleinFour_of_card_le_four hK4 hcomm (hne x h5) (hne y h7) (hne (x * y) h57)
    (hne (x * y⁻¹) h57') (hne (x * x * y⁻¹) h557) (hne (y * y * x⁻¹) h775)
  obtain ⟨f⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := (coverMap hP hwg).ker)
    (G₂ := Multiplicative (ZMod 2 × ZMod 2))
  exact ⟨(griessHopfMultiplierEquivKer hP hw hwg).trans (f.trans (MulEquiv.prodMultiplicative _ _))⟩

theorem multiplier_Sz_eight
    (X : Type) [Group X]
    (h : CFSG.Blueprint.LieModel X .twistedB2 0 2 3) :
    commutator X = ⊤ ∧ Nonempty (griessHopfMultiplier X ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_suzukiGroup_of_blueprint h
  exact multiplier_of_mulEquiv e.symm

theorem multiplier_Sz_eight_of_tauCeti
    (X : Type) [Group X]
    (h : CFSG.Models.LieModel X .twistedB2 0 2 3) :
    commutator X = ⊤ ∧ Nonempty (griessHopfMultiplier X ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_suzukiGroup h
  exact multiplier_of_mulEquiv e.symm

end CFSG.LieType.Multipliers.Sz8
