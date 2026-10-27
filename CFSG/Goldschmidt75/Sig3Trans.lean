module

public import CFSG.Goldschmidt75.Sig3Defs
public import CFSG.Goldschmidt75.TheoremBa
public import CFSG.Goldschmidt75.OddCore
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Goldschmidt.Steps.Balance
public import CFSG.Goldschmidt.Steps.G310Bar
public import CFSG.Goldschmidt.Steps.G37Quot

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type} [Group G]

theorem centralizer_zpowers_eq (t : G) :
    centralizer ((zpowers t : Subgroup G) : Set G) = centralizer ({t} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem isPGroup_zpowers {t : G} (ht : orderOf t = 2) : IsPGroup 2 (zpowers t) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])

variable [Finite G]

theorem oddCoreOf_inf_le_of_le {H K : Subgroup G} (hKH : K ≤ H) :
    oddCoreOf H ⊓ K ≤ oddCoreOf K := by
  refine Completion.le_oddCoreOf inf_le_right (fun g hg => mem_normalizer_inf
    (Completion.le_normalizer_oddCoreOf H (hKH hg)) (le_normalizer hg)) ?_
  exact Odd.of_dvd_nat (Balance.odd_card_oddCoreOf _) (card_dvd_of_le inf_le_left)

theorem oddCoreOf_centralizer_inf_le (L A : Subgroup G) :
    oddCoreOf (centralizer (A : Set G)) ⊓ L ≤ oddCoreOf (L ⊓ centralizer (A : Set G)) := by
  intro x hx
  exact oddCoreOf_inf_le_of_le inf_le_right
    ⟨hx.1, hx.2, Subgroup.map_subtype_le _ hx.1⟩

theorem oddCent_inf_le_oddCentSub {V : Subgroup G} {v : G} (hv : v ∈ V) :
    oddCent v ⊓ centralizer (V : Set G) ≤ oddCentSub V :=
  oddCoreOf_inf_le_of_le (centralizer_le (Set.singleton_subset_iff.mpr hv))

theorem barOf_le_oddCoreOf {L A X : Subgroup G} (hAL : A ≤ L) (hA : IsPGroup 2 A)
    (hX : X ≤ oddCoreOf (centralizer (A : Set G))) :
    barOf L X ≤ oddCoreOf (centralizer (barOf L A : Set (L ⧸ goldschmidtOddCore L))) := by
  rintro _ ⟨x, hx, rfl⟩
  have h1 : (x : G) ∈ oddCoreOf (L ⊓ centralizer (A : Set G)) :=
    oddCoreOf_centralizer_inf_le L A ⟨hX (mem_subgroupOf.mp hx), x.2⟩
  have h2 := G310.barOf_mem_oddCoreOf hAL hA h1 x.2
  rw [top_inf_eq] at h2
  exact h2

theorem barOf_le_oddCent {L X : Subgroup G} {t : G} (htL : t ∈ L) (ht : orderOf t = 2)
    (hX : X ≤ oddCent t) :
    barOf L X ≤ oddCent (QuotientGroup.mk' (goldschmidtOddCore L) ⟨t, htL⟩) := by
  have hX' : X ≤ oddCoreOf (centralizer ((zpowers t : Subgroup G) : Set G)) := by
    rw [centralizer_zpowers_eq]
    exact hX
  have h := barOf_le_oddCoreOf (zpowers_le.mpr htL) (isPGroup_zpowers ht) hX'
  rwa [G37.barOf_zpowers htL, centralizer_zpowers_eq] at h

theorem orderOf_mk_eq_two {L : Subgroup G} {t : G} (htL : t ∈ L) (ht : orderOf t = 2) :
    orderOf (QuotientGroup.mk' (goldschmidtOddCore L) ⟨t, htL⟩) = 2 := by
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  apply orderOf_eq_prime
  · rw [← map_pow]
    have : (⟨t, htL⟩ : L) ^ 2 = 1 := Subtype.ext ht2
    rw [this, map_one]
  · intro h
    have hmem := (QuotientGroup.eq_one_iff _).mp h
    have h1 := Completion.eq_one_of_sq_eq_one odd_card_oddCore hmem (Subtype.ext ht2)
    have : t = 1 := congrArg Subtype.val h1
    rw [this, orderOf_one] at ht
    exact absurd ht (by norm_num)

omit [Finite G] in
theorem mk_mem_center (v : G) :
    QuotientGroup.mk' (goldschmidtOddCore (centralizer ({v} : Set G)))
      ⟨v, mem_centralizer_singleton_iff.mpr rfl⟩ ∈
      center (centralizer ({v} : Set G) ⧸ goldschmidtOddCore (centralizer ({v} : Set G))) := by
  rw [mem_center_iff]
  intro y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective _ y
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.mp z.2)

theorem barOf_le_commutator_sup {L V X : Subgroup G} (hXL : X ≤ L) (hVL : V ≤ L)
    (hV : IsPGroup 2 V) (hX : X ≤ ⁅X, V⁆ ⊔ (oddCentSub V ⊓ L)) :
    barOf L X ≤ ⁅barOf L X, barOf L V⁆ ⊔
      oddCoreOf (centralizer (barOf L V : Set (L ⧸ goldschmidtOddCore L))) := by
  have hcL : ⁅X, V⁆ ≤ L := (commutator_mono hXL hVL).trans (Subgroup.commutator_le_self L)
  refine (G37.barOf_mono hX).trans ?_
  rw [G37.barOf_sup hcL inf_le_right, G37.barOf_commutator hXL hVL]
  exact sup_le_sup_left (barOf_le_oddCoreOf hVL hV inf_le_left) _

end CFSG.Goldschmidt75
