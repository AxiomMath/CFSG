module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.WreathCase
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.XbarDichotomy

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F L1 N : Subgroup G}

@[expose] def U0 (L1 : Subgroup G) : Subgroup G :=
  (piY L1).ker.map (normalizer (L1 : Set G)).subtype

omit [Finite G] in
theorem mem_U0 {L1 : Subgroup G} {g : G} :
    g ∈ U0 L1 ↔ ∃ hg : g ∈ normalizer (L1 : Set G), piY L1 ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

omit [Finite G] in
theorem U0_le_X (L1 : Subgroup G) : U0 L1 ≤ normalizer (L1 : Set G) := fun _ h =>
  (mem_U0.1 h).1

omit [Finite G] in
theorem U0_norm {L1 : Subgroup G} {x : G} (hx : x ∈ normalizer (L1 : Set G)) {u : G}
    (hu : u ∈ U0 L1) : x * u * x⁻¹ ∈ U0 L1 := by
  obtain ⟨hu', h⟩ := mem_U0.1 hu
  refine mem_U0.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hu') (Subgroup.inv_mem _ hx), ?_⟩
  have : (⟨x * u * x⁻¹, _⟩ : ↥(normalizer (L1 : Set G))) = ⟨x, hx⟩ * ⟨u, hu'⟩ * ⟨x, hx⟩⁻¹ :=
    rfl
  rw [this, map_mul, map_mul, h, map_inv, mul_one, mul_inv_cancel]

namespace Setup

variable (S : Setup L z t F L1 N)

include S

omit [Finite G] in
theorem L1_le_U0 : L1 ≤ U0 L1 := by
  intro l hl
  refine mem_U0.2 ⟨Subgroup.le_normalizer hl, ?_⟩
  have hmem : (⟨l, Subgroup.le_normalizer hl⟩ : ↥(normalizer (L1 : Set G))) ∈
      (centralizer (L1 : Set G)).subgroupOf (normalizer (L1 : Set G)) :=
    Subgroup.mem_subgroupOf.2 (mem_centralizer_iff.2 fun x hx => S.L1_comm x hx l hl)
  rw [piY_apply, (QuotientGroup.eq_one_iff _).2 hmem, QuotientGroup.mk_one]

omit [Finite G] in
theorem card_C_L1 :
    Nat.card (centralizer (L1 : Set G)) = Nat.card N * 256 := by
  rw [← S.N_sup]
  have hcomm : N ≤ centralizer (L1 : Set G) := S.N_le
  rw [sup_comm, ← Nat.card_congr (mulEquivProdSup hcomm S.N_disj.symm).toEquiv, Nat.card_prod,
    S.L1_card]
  ring

theorem not_two_dvd_relIndex_U0 : ¬ 2 ∣ L1.relIndex (U0 L1) := by
  set X := normalizer (L1 : Set G) with hX
  set O := fusionOddCore (Xbar L1) with hO
  set Cc := (centralizer (L1 : Set G)).subgroupOf X with hCc
  have hker : (piY L1).ker = O.comap (QuotientGroup.mk' Cc) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    exact QuotientGroup.eq_one_iff _
  have hsurj : Function.Surjective (QuotientGroup.mk' Cc) := QuotientGroup.mk'_surjective _
  have hcard1 : Nat.card (O.comap (QuotientGroup.mk' Cc)) =
      Nat.card (QuotientGroup.mk' Cc).ker * Nat.card O :=
    natCard_comap_of_surjective _ hsurj O
  rw [QuotientGroup.ker_mk'] at hcard1
  have hCcard : Nat.card Cc = Nat.card N * 256 := by
    rw [hCc, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.centralizer_le_normalizer (L1 : Set G))).toEquiv]
    exact card_C_L1 S
  have hU0card : Nat.card (U0 L1) = Nat.card N * 256 * Nat.card O := by
    have : Nat.card (U0 L1) = Nat.card (piY L1).ker :=
      Subgroup.card_map_of_injective X.subtype_injective
    rw [this, hker, hcard1, hCcard]
  have hmul := Subgroup.relIndex_mul_card L1 (U0 L1)
  rw [inf_eq_left.2 (L1_le_U0 S), S.L1_card, hU0card] at hmul
  have hodd : Odd (Nat.card N * Nat.card O) :=
    (Nat.not_even_iff_odd.1 (fun h => S.N_odd (even_iff_two_dvd.1 h))).mul
      (natCard_fusionOddCore_odd _)
  have h2 : L1.relIndex (U0 L1) = Nat.card N * Nat.card O := by
    have : L1.relIndex (U0 L1) * 256 = Nat.card N * Nat.card O * 256 := by
      rw [hmul]; ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) this
  rw [h2]
  intro h'
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h')

end Setup

end CFSG.EvenSporadicStandard.M22Std
