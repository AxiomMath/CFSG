module

public import CFSG.LocalAnalysis.ComponentInitial.OddCoreQuotient
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

theorem exists_isPComponent_of_isComponent {X : Type*} [Group X] [Finite X] (p : ℕ)
    {K : Subgroup (X ⧸ pPrimeCore p X)} (hK : IsComponent K) :
    ∃ L : Subgroup X, IsPComponent p L ∧ L.map (QuotientGroup.mk' (pPrimeCore p X)) = K := by
  set π := QuotientGroup.mk' (pPrimeCore p X)
  set S : Set (Subgroup X) := {L | L.IsSubnormal ∧ L.map π = K}
  have hS : S.Nonempty := ⟨K.comap π, hK.2.comap π,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) K⟩
  obtain ⟨L, hL⟩ := (Set.toFinite S).exists_minimal hS
  refine ⟨L, ⟨K, hK, hL.1.1, hL.1.2, fun J hJL hJsub hJmap => ?_⟩, hL.1.2⟩
  exact not_le_of_gt hJL (hL.2 ⟨hJsub, hJmap⟩ hJL.le)

theorem ne_bot_of_isComponent {X : Type*} [Group X] {K : Subgroup X} (hK : IsComponent K) :
    K ≠ ⊥ := by
  have := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  exact (Subgroup.nontrivial_iff_ne_bot K).1 this

theorem empty_layer_ordinary_two_components_force_characteristic_two_quotient
    {B : Type*} [Group B] [Finite B]
    (hord : ∀ L : Subgroup B, IsPComponent 2 L → IsComponent L) (hE : layer B = ⊥) :
    let R := pPrimeCore 2 B
    let P := pCore 2 (B ⧸ R)
    (∀ L : Subgroup B, ¬ IsPComponent 2 L) ∧ layer (B ⧸ R) = ⊥ ∧ pPrimeCore 2 (B ⧸ R) = ⊥ ∧
      fittingSubgroup (B ⧸ R) = P ∧ generalizedFitting (B ⧸ R) = P ∧
      centralizer (P : Set (B ⧸ R)) = (center P).map P.subtype ∧
      IsCharacteristicP 2 (B ⧸ R) ∧ ((⊤ : Subgroup (B ⧸ R)) = ⊥ ∨ P ≠ ⊥) ∧
      (Even (Nat.card B) → (⊤ : Subgroup (B ⧸ R)) ≠ ⊥ ∧ P ≠ ⊥) ∧
      (∀ A : Subgroup B, A ≤ center B → IsPGroup 2 A →
        Function.Injective ((QuotientGroup.mk' R).comp A.subtype) ∧
        A.map (QuotientGroup.mk' R) ≤ (center P).map P.subtype) ∧
      (MulAut.conjNormal (H := P)).ker = (center P).map P.subtype ∧
      (∃ _ : ((center P).map P.subtype).Normal,
        Nonempty ((B ⧸ R) ⧸ (center P).map P.subtype ≃* (MulAut.conjNormal (H := P)).range)) ∧
      (Group.IsSolvable B ↔ Group.IsSolvable (MulAut.conjNormal (H := P)).range) := by
  intro R P
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' R with hπ
  have hnoP : ∀ L : Subgroup B, ¬ IsPComponent 2 L := by
    intro L hL
    have hLle : L ≤ layer B := le_sSup (hord L hL)
    rw [hE, le_bot_iff] at hLle
    obtain ⟨K, hK, -, hmap, -⟩ := hL
    apply ne_bot_of_isComponent hK
    rw [← hmap, hLle, Subgroup.map_bot]
  have hlayer : layer (B ⧸ R) = ⊥ := by
    refine sSup_eq_bot.2 fun K hK => ?_
    obtain ⟨L, hL, -⟩ := exists_isPComponent_of_isComponent 2 hK
    exact absurd hL (hnoP L)
  have hcore : pPrimeCore 2 (B ⧸ R) = ⊥ := by
    rw [CFSG.pPrimeCore_eq_piCore]
    have key : ∀ (N : Subgroup B) [N.Normal], N = piCore {q : Nat.Primes | q.val ≠ 2} B →
        piCore {q : Nat.Primes | q.val ≠ 2} (B ⧸ N) = ⊥ := by
      rintro N _ rfl
      exact CFSG.LocalCores.prime_set_core_quotient _
    exact key R (CFSG.pPrimeCore_eq_piCore (G := B) (p := 2))
  have hF : fittingSubgroup (B ⧸ R) = P := Fitting_eq_pcore (B ⧸ R) 2 hcore
  have hFstar : generalizedFitting (B ⧸ R) = P := by
    rw [generalizedFitting, hF, hlayer, sup_bot_eq]
  have hchar : IsCharacteristicP 2 (B ⧸ R) :=
    isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot (B ⧸ R) 2 hcore hlayer
  have hcent : centralizer (P : Set (B ⧸ R)) = (center P).map P.subtype := by
    ext x
    constructor
    · intro hx
      have hxP : x ∈ P := hchar hx
      refine Subgroup.mem_map.2 ⟨⟨x, hxP⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.1 hx g g.2)
    · rintro ⟨z, hz, rfl⟩
      rw [mem_centralizer_iff]
      intro h hh
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨h, hh⟩)
  have hcases : (⊤ : Subgroup (B ⧸ R)) = ⊥ ∨ P ≠ ⊥ := by
    by_cases hP : P = ⊥
    · left
      have h := hchar
      change centralizer (P : Set (B ⧸ R)) ≤ P at h
      rw [hP] at h
      have htop : centralizer ((⊥ : Subgroup (B ⧸ R)) : Set (B ⧸ R)) = ⊤ :=
        centralizer_eq_top_iff_subset.2 (by
          rw [coe_bot]; exact Set.singleton_subset_iff.2 (one_mem _))
      rw [htop] at h
      exact eq_bot_iff.2 h
    · exact Or.inr hP
  have heven : Even (Nat.card B) → (⊤ : Subgroup (B ⧸ R)) ≠ ⊥ ∧ P ≠ ⊥ := by
    intro hev
    have htop : (⊤ : Subgroup (B ⧸ R)) ≠ ⊥ := by
      intro h
      have hR : R = ⊤ := by
        refine eq_top_iff.2 fun b _ => ?_
        have hb : π b ∈ (⊥ : Subgroup (B ⧸ R)) := h ▸ mem_top _
        rw [mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hb
        exact hb
      have hcop := pPrimeCore_coprime_card (p := 2) (G := B)
      rw [show pPrimeCore 2 B = R from rfl, hR, Subgroup.card_top] at hcop
      exact (Nat.not_even_iff_odd.2 (Nat.coprime_two_left.1 hcop)) hev
    exact ⟨htop, hcases.resolve_left htop⟩
  have hcentral : ∀ A : Subgroup B, A ≤ center B → IsPGroup 2 A →
      Function.Injective ((QuotientGroup.mk' R).comp A.subtype) ∧
      A.map (QuotientGroup.mk' R) ≤ (center P).map P.subtype := by
    intro A hA hA2
    refine ⟨?_, ?_⟩
    · rw [injective_iff_map_eq_one]
      intro a ha
      have haR : (a : B) ∈ R := by
        simpa [QuotientGroup.eq_one_iff] using ha
      obtain ⟨k, hk⟩ := hA2 a
      have h1 : orderOf (a : B) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
        have := congrArg Subtype.val hk
        simpa using this)
      have h3 : orderOf (a : B) = 1 :=
        (((coprime_orderOf_of_mem_pPrimeCore haR).pow_left k).symm).eq_one_of_dvd h1
      rw [orderOf_eq_one_iff] at h3
      exact Subtype.ext h3
    · rw [← hcent]
      rintro _ ⟨a, ha, rfl⟩
      rw [mem_centralizer_iff]
      intro h _
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective R h
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 (hA ha) b]
  have hker : (MulAut.conjNormal (H := P)).ker = (center P).map P.subtype := by
    rw [← hcent]
    ext x
    rw [MonoidHom.mem_ker, mem_centralizer_iff]
    constructor
    · intro hx h hh
      have h1 := congrArg (fun φ : MulAut P => ((φ ⟨h, hh⟩ : P) : B ⧸ R)) hx
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc h * x = x * h * x⁻¹ * x := by rw [h1]
        _ = x * h := by group
    · intro hx
      refine MulEquiv.ext fun y => Subtype.ext ?_
      rw [MulAut.conjNormal_apply, MulAut.one_apply, ← hx y y.2, mul_inv_cancel_right]
  have hZn : ((center P).map P.subtype).Normal := hker ▸ (MulAut.conjNormal (H := P)).normal_ker
  have hiso : ∃ _ : ((center P).map P.subtype).Normal,
      Nonempty ((B ⧸ R) ⧸ (center P).map P.subtype ≃* (MulAut.conjNormal (H := P)).range) :=
    ⟨hZn, ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange _)⟩⟩
  have hsolv : Group.IsSolvable B ↔ Group.IsSolvable (MulAut.conjNormal (H := P)).range := by
    constructor
    · intro hB
      have hBR : Group.IsSolvable (B ⧸ R) :=
        Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective R)
      exact Group.isSolvable_of_surjective (MulAut.conjNormal (H := P)).rangeRestrict_surjective
    · intro hρ
      have hKs : Group.IsSolvable (MulAut.conjNormal (H := P)).ker := by
        refine Group.isSolvable_of_comm fun a b => ?_
        have ha : (a : B ⧸ R) ∈ (center P).map P.subtype := hker ▸ a.2
        have hb : (b : B ⧸ R) ∈ (center P).map P.subtype := hker ▸ b.2
        obtain ⟨a', -, haa⟩ := ha
        obtain ⟨b', hb', hbb⟩ := hb
        apply Subtype.ext
        change (a : B ⧸ R) * b = b * a
        rw [← haa, ← hbb]
        exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hb' a')
      have hBR : Group.IsSolvable (B ⧸ R) :=
        Group.isSolvable_of_ker_le_range (MulAut.conjNormal (H := P)).ker.subtype
          (MulAut.conjNormal (H := P)).rangeRestrict
          (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
      have hRs : Group.IsSolvable R := CFSG.FeitThompson.isSolvable_of_odd_natCard _
        (Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := B)))
      exact Group.isSolvable_of_ker_le_range R.subtype (QuotientGroup.mk' R)
        (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  exact ⟨hnoP, hlayer, hcore, hF, hFstar, hcent, hchar, hcases, heven, hcentral, hker, hiso,
    hsolv⟩

end CFSG.LocalAnalysis.ComponentInitial
