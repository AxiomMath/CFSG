module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndBasic
public import CFSG.LocalAnalysis.EvenSmallLie.Setup
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelAction
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaEnd

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

theorem card_of_lieModel_PSU
    {X : Type} [Group X] (h : LieModel X .PSU 6 2 1) :
    Nat.card X = 9196830720 := by
  obtain ⟨e⟩ := CFSG.LieType.Multipliers.U62.nonempty_mulEquiv_T46 h
  rw [Nat.card_congr e.toEquiv, CFSG.Fischer.card_T46]

theorem card_outer_of_lieModel_PSU {X : Type} [Group X] (h : LieModel X .PSU 6 2 1) :
    Nat.card (Outer X) = 6 := by
  have hc : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 6 2 1 := by
    rcases h with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals exact absurd h0 (by norm_num)
  have := (CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound X 6 2 1 hc).2.2.1
  rw [this]
  norm_num

theorem card_mulAut_dvd {X : Type} [Group X] [Finite X] :
    Nat.card (MulAut X) ∣ Nat.card (Outer X) * Nat.card X := by
  have : Finite (MulAut X) :=
    Finite.of_injective (fun e : MulAut X => (e : X → X)) fun a b hab => MulEquiv.ext (congrFun hab)
  rw [card_eq_card_quotient_mul_card_subgroup
    (CFSG.ComponentClassification.OuterAutomorphisms.inner X)]
  refine Nat.mul_dvd_mul_left _ ?_
  change Nat.card (MulAut.conj : X →* MulAut X).range ∣ _
  rw [← Subgroup.index_ker]
  exact Subgroup.index_dvd_card _

theorem card_centralizer_dvd
    {L : Subgroup G} (hL : standardComponentIsStandard L)
    (lie : LieModel (L ⧸ center L) .PSU 6 2 1) {t : G} (ht : orderOf t = 2)
    (htL : t ∈ centralizer (L : Set G))
    (hker : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    Nat.card (centralizer ({t} : Set G)) ∣ 12 * 9196830720 := by
  have hHN := centralizer_le_normalizer_of_standard hL htL ht
  have : Group.IsPerfect L := Group.isPerfect_def.2 hL.1.1
  obtain ⟨θ, -, hθ1⟩ := CFSG.ComponentClassification.M12Cover.CyclicKernel.exists_normalizer_action
    hHN (QuotientGroup.mk' (center L)) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have htC : zpowers t ≤ centralizer ({t} : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_singleton_iff.mpr rfl
  have hkerθ : θ.ker = (zpowers t).subgroupOf (centralizer ({t} : Set G)) := by
    ext h
    rw [MonoidHom.mem_ker, hθ1, mem_subgroupOf, ← hker]
    exact ⟨fun h1 => ⟨h1, h.2⟩, fun h1 => h1.1⟩
  have hcardker : Nat.card θ.ker = 2 := by
    rw [hkerθ, Nat.card_congr (subgroupOfEquivOfLe htC).toEquiv, Nat.card_zpowers, ht]
  have hrange : Nat.card θ.range ∣ 6 * 9196830720 := by
    have h1 := card_mulAut_dvd (X := L ⧸ center L)
    rw [card_outer_of_lieModel_PSU lie, card_of_lieModel_PSU lie] at h1
    exact (Subgroup.card_subgroup_dvd_card _).trans h1
  rw [card_eq_card_quotient_mul_card_subgroup θ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv, hcardker]
  have : 12 * 9196830720 = 6 * 9196830720 * 2 := by norm_num
  rw [this]
  exact Nat.mul_dvd_mul_right hrange 2

theorem card_le_of_isPGroup
    {L : Subgroup G} (hL : standardComponentIsStandard L)
    (lie : LieModel (L ⧸ center L) .PSU 6 2 1) {t : G} (ht : orderOf t = 2)
    (htL : t ∈ centralizer (L : Set G))
    (hker : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {Q : Subgroup G} (hQ : Q ≤ centralizer ({t} : Set G)) (hQ2 : IsPGroup 2 Q) :
    Nat.card Q ≤ 2 ^ 17 := by
  have h1 : Nat.card Q ∣ 2 ^ 17 * 841995 := by
    have := (card_dvd_of_le hQ).trans (card_centralizer_dvd hL lie ht htL hker)
    rwa [show (12 * 9196830720 : ℕ) = 2 ^ 17 * 841995 by norm_num] at this
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ2
  rw [hk] at h1 ⊢
  have hcop : Nat.Coprime (2 ^ k) 841995 := Nat.Coprime.pow_left _ (by norm_num)
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right h1)

omit [Finite G] in
theorem le_of_perfect_of_isSolvable_quotient {A N X : Subgroup G} [(N.subgroupOf A).Normal]
    [Group.IsSolvable (A ⧸ N.subgroupOf A)] (hXA : X ≤ A) (hX : ⁅X, X⁆ = X) : X ≤ N := by
  set q : A →* A ⧸ N.subgroupOf A := QuotientGroup.mk' _ with hq
  set X' := X.subgroupOf A with hX'
  have hX'perf : ⁅X', X'⁆ = X' := by
    apply map_injective A.subtype_injective
    rw [map_commutator, hX', subgroupOf_map_subtype, inf_of_le_left hXA, hX]
  have himg : ⁅X'.map q, X'.map q⁆ = X'.map q := by rw [← map_commutator, hX'perf]
  have hbot := eq_bot_of_perfect_of_isSolvable himg
  intro x hx
  have h1 : q ⟨x, hXA hx⟩ = 1 := by
    have : q ⟨x, hXA hx⟩ ∈ X'.map q := mem_map_of_mem q (show (⟨x, hXA hx⟩ : A) ∈ X' from hx)
    rwa [hbot, mem_bot] at this
  have h2 : (⟨x, hXA hx⟩ : A) ∈ N.subgroupOf A := by
    rwa [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h2

theorem isSolvable_of_card_dvd {X : Type*} [Group X] [Finite X] {a b : ℕ}
    (h : Nat.card X ∣ 2 ^ a * 3 ^ b) : Group.IsSolvable X := by
  obtain ⟨d₁, d₂, h₁, h₂, hd⟩ := Nat.dvd_mul.mp h
  obtain ⟨m₁, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h₁
  obtain ⟨m₂, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h₂
  have := Fintype.ofFinite X
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hd])

variable {L : Subgroup G} {t : G}

theorem relIndex_dvd_twelve
    (hL : standardComponentIsStandard L) (hZ : center L = ⊥)
    (lie : LieModel (L ⧸ center L) .PSU 6 2 1) (ht : orderOf t = 2)
    (htL : t ∈ centralizer (L : Set G))
    (hker : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    L.relIndex (centralizer ({t} : Set G)) ∣ 12 := by
  have hLH : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp htL l hl)
  have hcardL : Nat.card L = 9196830720 := by
    rw [card_eq_card_quotient_mul_card_subgroup (center L), card_of_lieModel_PSU lie, hZ,
      card_bot, mul_one]
  have h1 := Subgroup.relIndex_mul_card L (centralizer ({t} : Set G))
  rw [inf_of_le_left hLH, hcardL] at h1
  have h2 := card_centralizer_dvd hL lie ht htL hker
  rw [← h1] at h2
  exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h2


theorem le_of_perfect
    (hL : standardComponentIsStandard L) (hZ : center L = ⊥)
    (lie : LieModel (L ⧸ center L) .PSU 6 2 1) (ht : orderOf t = 2)
    (htL : t ∈ centralizer (L : Set G))
    (hker : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X : Subgroup G} (hX : X ≤ centralizer ({t} : Set G)) (hperf : ⁅X, X⁆ = X) : X ≤ L := by
  have hLH : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp htL l hl)
  have hHN := centralizer_le_normalizer_of_standard hL htL ht
  have : (L.subgroupOf (centralizer ({t} : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLH).mpr hHN
  have : Group.IsSolvable
      (centralizer ({t} : Set G) ⧸ L.subgroupOf (centralizer ({t} : Set G))) := by
    apply isSolvable_of_card_dvd (a := 2) (b := 1)
    have h12 := relIndex_dvd_twelve hL hZ lie ht htL hker
    rw [Subgroup.relIndex, Subgroup.index] at h12
    exact h12.trans (by norm_num)
  exact le_of_perfect_of_isSolvable_quotient hX hperf

theorem isSolvable_normalizer
    (hL : standardComponentIsStandard L) (hZ : center L = ⊥)
    (lie : LieModel (L ⧸ center L) .PSU 6 2 1) (ht : orderOf t = 2)
    (htL : t ∈ centralizer (L : Set G))
    (hker : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {S : Subgroup G}
    (hS : Nat.card (normalizer (S : Set G) ⊓ L : Subgroup G) = 2 ^ 15 * 3) :
    Group.IsSolvable (normalizer (S : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  set H := centralizer ({t} : Set G) with hHdef
  set N := normalizer (S : Set G) ⊓ H with hN
  have hLH : L ≤ H := fun l hl =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp htL l hl)
  have hHN := centralizer_le_normalizer_of_standard hL htL ht
  have hNH : N ≤ H := inf_le_right
  have hLN : L ⊓ N = normalizer (S : Set G) ⊓ L := by
    rw [hN, inf_comm, inf_assoc, inf_of_le_right hLH]
  have hnormal : (L.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hLH).mpr hHN
  have h2 : L.relIndex N ∣ L.relIndex H := by
    rw [← Subgroup.relIndex_subgroupOf hNH]
    exact Subgroup.relIndex_dvd_index_of_normal _ _
  have h1 := Subgroup.relIndex_mul_card L N
  apply isSolvable_of_card_dvd (a := 17) (b := 2)
  rw [← h1, hLN, hS]
  have h3 := h2.trans (relIndex_dvd_twelve hL hZ lie ht htL hker)
  calc L.relIndex N * (2 ^ 15 * 3) ∣ 12 * (2 ^ 15 * 3) := Nat.mul_dvd_mul_right h3 _
    _ = 2 ^ 17 * 3 ^ 2 := by norm_num

theorem card_le_of_sq_eq_one (hL : standardComponentIsStandard L)
    (lie : LieModel (L ⧸ center L) .PSU 6 2 1) (ht : orderOf t = 2)
    (htL : t ∈ centralizer (L : Set G))
    (hker : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hrank : ∀ (X : Type) [Group X], LieModel X .PSU 6 2 1 →
      ∀ E : Subgroup (MulAut X), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 2 ^ 9)
    {E : Subgroup G} (hE : E ≤ centralizer ({t} : Set G)) (hsq : ∀ e ∈ E, e * e = 1) :
    Nat.card E ≤ 2 ^ 10 := by
  have hHN := centralizer_le_normalizer_of_standard hL htL ht
  have : Group.IsPerfect L := Group.isPerfect_def.2 hL.1.1
  obtain ⟨θ, -, hθ1⟩ := CFSG.ComponentClassification.M12Cover.CyclicKernel.exists_normalizer_action
    hHN (QuotientGroup.mk' (center L)) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have htC : zpowers t ≤ centralizer ({t} : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_singleton_iff.mpr rfl
  have hkerθ : θ.ker = (zpowers t).subgroupOf (centralizer ({t} : Set G)) := by
    ext h
    rw [MonoidHom.mem_ker, hθ1, mem_subgroupOf, ← hker]
    exact ⟨fun h1 => ⟨h1, h.2⟩, fun h1 => h1.1⟩
  have hcardker : Nat.card θ.ker = 2 := by
    rw [hkerθ, Nat.card_congr (subgroupOfEquivOfLe htC).toEquiv, Nat.card_zpowers, ht]
  set E' := E.subgroupOf (centralizer ({t} : Set G)) with hE'
  set ρ := θ.comp E'.subtype with hρ
  have hcardE : Nat.card E = Nat.card E' := (Nat.card_congr (subgroupOfEquivOfLe hE).toEquiv).symm
  have hsplit : Nat.card E' = Nat.card ρ.range * Nat.card ρ.ker := by
    rw [card_eq_card_quotient_mul_card_subgroup ρ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
  have hker' : Nat.card ρ.ker ≤ 2 := by
    rw [← hcardker]
    refine Nat.card_le_card_of_injective (fun x => ⟨(x : E'), ?_⟩) ?_
    · have := x.2
      rw [MonoidHom.mem_ker] at this ⊢
      exact this
    · intro x y hxy
      have h1 := congrArg Subtype.val hxy
      simp only at h1
      exact Subtype.ext (Subtype.ext h1)
  have hrange : Nat.card ρ.range ≤ 2 ^ 9 := by
    refine hrank _ lie ρ.range ?_
    rintro _ ⟨x, rfl⟩
    rw [← map_mul]
    have hx : x * x = 1 := Subtype.ext (Subtype.ext (by
      have := hsq _ x.2
      simpa using this))
    rw [hx, map_one]
  rw [hcardE, hsplit]
  calc Nat.card ρ.range * Nat.card ρ.ker ≤ 2 ^ 9 * 2 := Nat.mul_le_mul hrange hker'
    _ = 2 ^ 10 := by norm_num

end CFSG.EvenSmallLie.UnitarySix.YamadaEnd
