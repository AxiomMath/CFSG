module

public import CFSG.Monster.B.Short.Extraspecial
public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open
open scoped commutatorElement

section Xs

variable {G : Type*} [Group G]

theorem mem_center_map_iff {R : Subgroup G} {x : G} :
    x ∈ (Subgroup.center ↥R).map R.subtype ↔ x ∈ R ∧ ∀ r ∈ R, r * x = x * r := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, fun r hr => congrArg Subtype.val (Subgroup.mem_center_iff.1 hy ⟨r, hr⟩)⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (h g g.2), rfl⟩

theorem comm_mem_center_map {R : Subgroup G} (h : timmesfeldIsExtraspecial ↥R) {g k : G}
    (hg : g ∈ R) (hk : k ∈ R) : ⁅g, k⁆ ∈ (Subgroup.center ↥R).map R.subtype := by
  have hc : ⁅(⟨g, hg⟩ : ↥R), ⟨k, hk⟩⁆ ∈ _root_.commutator ↥R := by
    rw [_root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [h.2.1, h.2.2.1] at hc
  exact ⟨_, hc, rfl⟩

theorem sq_mem_center_map [Finite G] {R : Subgroup G} (h : timmesfeldIsExtraspecial ↥R) {g : G}
    (hg : g ∈ R) : g ^ 2 ∈ (Subgroup.center ↥R).map R.subtype := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 ↥R) := ⟨h.1⟩
  have hf := CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) (⟨g, hg⟩ : ↥R)
  rw [h.2.2.1] at hf
  exact ⟨_, hf, rfl⟩

private theorem mem_center_iff_coe {P : Subgroup G} (x : ↥P) :
    x ∈ Subgroup.center ↥P ↔ (x : G) ∈ (Subgroup.center ↥P).map P.subtype := by
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [← this]

theorem isExtraspecial_of_props [Finite G] {P : Subgroup G} (hP2 : IsPGroup 2 P)
    (hZ : Nat.card ((Subgroup.center ↥P).map P.subtype) = 2)
    (hcomm : ∀ g ∈ P, ∀ k ∈ P, ⁅g, k⁆ ∈ (Subgroup.center ↥P).map P.subtype)
    (hsq : ∀ g ∈ P, g ^ 2 ∈ (Subgroup.center ↥P).map P.subtype)
    (hna : ¬ P ≤ (Subgroup.center ↥P).map P.subtype) : timmesfeldIsExtraspecial ↥P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen : Nat.card (Subgroup.center ↥P) = 2 := by
    rw [← hZ]
    exact (Subgroup.card_map_of_injective P.subtype_injective).symm
  have hcl : _root_.commutator ↥P ≤ Subgroup.center ↥P := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [mem_center_iff_coe]
    have := hcomm a a.2 b b.2
    simpa [commutatorElement_def] using this
  haveI hcomm' : IsMulCommutative (↥P ⧸ Subgroup.center ↥P) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := Subgroup.center ↥P)).2 hcl
  have hexp : Monoid.exponent (↥P ⧸ Subgroup.center ↥P) ∣ 2 := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_center_iff_coe]
      exact hsq x x.2
  have hnt : Nontrivial (↥P ⧸ Subgroup.center ↥P) := by
    rw [← not_subsingleton_iff_nontrivial, QuotientGroup.subsingleton_iff]
    intro htop
    apply hna
    intro g hg
    have : (⟨g, hg⟩ : ↥P) ∈ Subgroup.center ↥P := htop ▸ Subgroup.mem_top _
    exact (mem_center_iff_coe _).1 this
  haveI hE : CFSG.IsExtraspecial 2 ↥P :=
    { center_order_p := hcen
      quotient_elementary_abelian := { exponent_dvd_p := hexp }
      quotient_nontrivial := hnt }
  have h := CFSG.IsExtraspecial.isExtraspecialPGroup (p := 2) (P := ↥P)
  exact ⟨h.1, h.2.1.trans h.2.2.1.symm, h.2.2.1, h.2.2.2⟩

variable [Finite G] {R Z S : Subgroup G}

private theorem card_center_map (hR : timmesfeldIsExtraspecial ↥R)
    (hZ : Z = (Subgroup.center ↥R).map R.subtype) : Nat.card Z = 2 := by
  rw [hZ, Subgroup.card_map_of_injective R.subtype_injective]
  exact hR.2.2.2

theorem isExtraspecial_iff_radical (hR : timmesfeldIsExtraspecial ↥R)
    (hZ : Z = (Subgroup.center ↥R).map R.subtype) (hZS : Z ≤ S) (hSR : S ≤ R) :
    timmesfeldIsExtraspecial ↥S ↔ ¬ S ≤ Z ∧ ∀ s ∈ S, (∀ t ∈ S, s * t = t * s) → s ∈ Z := by
  have hZc : ∀ z ∈ Z, ∀ r ∈ R, r * z = z * r := fun z hz r hr =>
    (mem_center_map_iff.1 (hZ ▸ hz)).2 r hr
  have hZcard := card_center_map hR hZ
  constructor
  · intro hS
    have hZS' : Z ≤ (Subgroup.center ↥S).map S.subtype := fun z hz =>
      mem_center_map_iff.2 ⟨hZS hz, fun s hs => hZc z hz s (hSR hs)⟩
    have hZeq : (Subgroup.center ↥S).map S.subtype = Z := by
      symm
      refine Subgroup.eq_of_le_of_card_ge hZS' ?_
      rw [Subgroup.card_map_of_injective S.subtype_injective, hS.2.2.2, hZcard]
    refine ⟨fun hle => ?_, fun s hs hcomm => ?_⟩
    · have hab : ∀ a b : ↥S, a * b = b * a := fun a b =>
        Subtype.ext (hZc _ (hle a.2) _ (hSR b.2)).symm
      have hbot : _root_.commutator ↥S = ⊥ := by
        rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro a _
        exact Subgroup.mem_centralizer_iff.2 fun b _ => hab b a
      have h1 : Nat.card (Subgroup.center ↥S) = 1 := by
        rw [← hS.2.2.1, ← hS.2.1, hbot]
        simp
      have h2 := hS.2.2.2
      omega
    · rw [← hZeq]
      exact mem_center_map_iff.2 ⟨hs, fun r hr => (hcomm r hr).symm⟩
  · rintro ⟨hna, hrad⟩
    have hZeq : (Subgroup.center ↥S).map S.subtype = Z := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxS, hxc⟩ := mem_center_map_iff.1 hx
        exact hrad x hxS fun t ht => (hxc t ht).symm
      · intro hx
        exact mem_center_map_iff.2 ⟨hZS hx, fun s hs => hZc x hx s (hSR hs)⟩
    refine isExtraspecial_of_props (hR.1.to_le hSR) (by rw [hZeq, hZcard])
      (fun g hg k hk => ?_) (fun g hg => ?_) (by rw [hZeq]; exact hna)
    · rw [hZeq, hZ]
      exact comm_mem_center_map hR (hSR hg) (hSR hk)
    · rw [hZeq, hZ]
      exact sq_mem_center_map hR (hSR hg)

theorem isExtraspecial_or_card_two_iff_radical (hR : timmesfeldIsExtraspecial ↥R)
    (hZ : Z = (Subgroup.center ↥R).map R.subtype) (hZS : Z ≤ S) (hSR : S ≤ R) :
    (timmesfeldIsExtraspecial ↥S ∨ Nat.card S = 2) ↔
      ∀ s ∈ S, (∀ t ∈ S, s * t = t * s) → s ∈ Z := by
  have hZcard := card_center_map hR hZ
  constructor
  · rintro (hS | hS)
    · exact ((isExtraspecial_iff_radical hR hZ hZS hSR).1 hS).2
    · have : Z = S := Subgroup.eq_of_le_of_card_ge hZS (by omega)
      intro s hs _
      rw [this]
      exact hs
  · intro hrad
    by_cases hle : S ≤ Z
    · right
      rw [le_antisymm hle hZS]
      exact hZcard
    · left
      exact (isExtraspecial_iff_radical hR hZ hZS hSR).2 ⟨hle, hrad⟩

theorem normalizer_le_centralizer_of_radical (hZ2 : Nat.card Z = 2) (hZS : Z ≤ S)
    (hZc : ∀ z ∈ Z, ∀ s ∈ S, s * z = z * s)
    (hrad : ∀ s ∈ S, (∀ t ∈ S, s * t = t * s) → s ∈ Z) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (Z : Set G) := by
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hdS : ∀ s, s ∈ S ↔ d * s * d⁻¹ ∈ S := Subgroup.mem_normalizer_iff.1 hd
  have hdS' : ∀ s, s ∈ S ↔ d⁻¹ * s * d ∈ S := fun s => by
    simpa using Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hd) s
  have hw : d * z * d⁻¹ ∈ Z := by
    refine hrad _ ((hdS z).1 (hZS hz)) fun t ht => ?_
    have hc := hZc z hz _ ((hdS' t).1 ht)
    calc d * z * d⁻¹ * t = d * (z * (d⁻¹ * t * d)) * d⁻¹ := by group
      _ = d * ((d⁻¹ * t * d) * z) * d⁻¹ := by rw [hc]
      _ = t * (d * z * d⁻¹) := by group
  by_cases hz1 : z = 1
  · subst hz1
    simp
  · obtain ⟨w, -, hw1⟩ := (Nat.card_eq_two_iff' (1 : ↥Z)).1 hZ2
    have hne : d * z * d⁻¹ ≠ 1 := fun h => hz1 (by simpa using h)
    have h1 : (⟨d * z * d⁻¹, hw⟩ : ↥Z) = ⟨z, hz⟩ := by
      rw [hw1 ⟨d * z * d⁻¹, hw⟩ (fun h => hne (congrArg Subtype.val h)),
        hw1 ⟨z, hz⟩ (fun h => hz1 (congrArg Subtype.val h))]
    have h2 : d * z * d⁻¹ = z := congrArg Subtype.val h1
    calc z * d = d * z * d⁻¹ * d := by rw [h2]
      _ = d * z := by group

end Xs

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
