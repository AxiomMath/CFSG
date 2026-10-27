module

public import CFSG.HardMathSupport.Solomon.Coordinator.I10_20Cases
import CFSG.Quasithin.Background.G8Dihedral

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open Subgroup

section Reduce

variable {F : Type} [Group F]

theorem i1021_caseA {X : Type} [Group X] [Finite X] {q n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hn : 0 < n) {V : Subgroup F} (hV : IsElemAbelian 2 V) (hVc : Nat.card V = 2 ^ n)
    (ψ : X →* F) (hψ : Function.Surjective ψ) (hY : IsPGroup q ψ.ker) (hYne : ψ.ker ≠ ⊥)
    (hC : centralizer (ψ.ker : Set X) ≤ ψ.ker) : n ≤ pRank q (⊤ : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hY
  have hYodd : Odd (Nat.card ψ.ker) := by rw [ha]; exact (hq.odd_of_ne_two hq2).pow
  obtain ⟨T, -, hT, hTc⟩ := i1020_coprime_lift (p := 2) ψ ⊤
    (by rw [top_inf_eq]; exact hYodd.not_two_dvd_nat)
    (by rw [map_top_of_surjective ψ hψ]; exact le_top) hV hVc
  have hTY : T ⊓ ψ.ker = ⊥ := by
    rw [← disjoint_iff]
    refine disjoint_of_coprime_natCard ?_
    rw [hTc, ha]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2))
  have hfaith : T ⊓ centralizer (ψ.ker : Set X) = ⊥ :=
    le_bot_iff.1 (hTY ▸ inf_le_inf_left T hC)
  have h81 : CFSG.Quasithin.G81 ψ.ker T T :=
    ⟨hT, le_rfl, IsPGroup.of_card hTc, le_normalizer_of_normal, hY.isNilpotent, hYodd, hYne⟩
  obtain ⟨Hs, p, hDF, -, -, hx⟩ := CFSG.Quasithin.g8_6 h81 hn hTc hfaith
  choose x hxY hxH hxo using hx
  have hp : ∀ i, p i = q := by
    intro i
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.1 hY ⟨x i, hxY i⟩
    rw [orderOf_mk, hxo i] at hm
    have h1 : p i ∣ q ^ m := hm ▸ dvd_rfl
    exact (Nat.prime_dvd_prime_iff_eq (hDF.prime i) hq).1 ((hDF.prime i).dvd_of_dvd_pow h1)
  obtain ⟨hE, hEc⟩ := i1020_family x (fun i => (hxo i).trans (hp i))
    (fun i j hij => hDF.commute i j hij _ (hxH i) _ (hxH j))
    (hDF.independent.mono fun i => zpowers_le.2 (hxH i))
  exact CFSG.SectionRank.le_pRank hq.one_lt le_top hE (by rw [hEc, Fintype.card_fin])

theorem i1021_exists_prime_ne {X : Type} [Group X] [Finite X] {q : ℕ} {Y : Subgroup X}
    (hY : ¬ IsPGroup q Y) : ∃ p : ℕ, p.Prime ∧ p ≠ q ∧ p ∣ Nat.card Y := by
  by_contra hno
  push Not at hno
  apply hY
  refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
  intro d hd hdd
  by_contra hne
  exact hno d hd hne hdd

end Reduce

theorem i1021_center_eq_bot {F : Type} [Group F] [IsSimpleGroup F]
    (hnc : ∃ a b : F, a * b ≠ b * a) : Subgroup.center F = ⊥ := by
  rcases (Subgroup.center F).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm

section Main

theorem i1021_main {F : Type} [Group F] [Finite F] [IsSimpleGroup F]
    (hnc : ∃ a b : F, a * b ≠ b * a) {q n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hn : 0 < n)
    {V : Subgroup F} (hV : IsElemAbelian 2 V) (hVc : Nat.card V = 2 ^ n)
    (hcen : ∀ (X1 : Type) [Group X1] [Finite X1] (ψ : X1 →* F), Function.Surjective ψ →
      commutator X1 = ⊤ → ψ.ker ≤ center X1 → IsPGroup q ψ.ker →
        n ≤ pRank q (⊤ : Subgroup X1)) :
    ∀ (m : ℕ) (X : Type) [Group X] [Finite X], Nat.card X ≤ m → ∀ φ : X →* F,
      Function.Surjective φ → n ≤ pRank q (⊤ : Subgroup X) := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨a₀, b₀, hab₀⟩ := hnc
  have : Nontrivial F := ⟨⟨a₀, 1, fun h => hab₀ (by rw [h]; simp)⟩⟩
  have hF1 : ⁅(⊤ : Subgroup F), (⊤ : Subgroup F)⁆ = ⊤ := i1020_commutator_top ⟨a₀, b₀, hab₀⟩
  intro m
  induction m with
  | zero =>
    intro X _ _ hX
    have := Nat.card_pos (α := X)
    omega
  | succ m ih =>
    intro X _ _ hX φ hφ
    by_cases hYq : IsPGroup q φ.ker
    · by_cases hC : centralizer (φ.ker : Set X) ≤ φ.ker
      ·
        have hYne : φ.ker ≠ ⊥ := by
          intro hbot
          obtain ⟨a, ha⟩ := exists_ne (1 : F)
          obtain ⟨x, hx⟩ := hφ a
          have hx1 : x ∈ φ.ker := hC (by
            rw [hbot, mem_centralizer_iff]
            intro h hh
            rw [SetLike.mem_coe, mem_bot] at hh
            rw [hh, one_mul, mul_one])
          rw [MonoidHom.mem_ker, hx] at hx1
          exact ha hx1
        exact i1021_caseA hq hq2 hn hV hVc φ hφ hYq hYne hC
      ·
        set C : Subgroup X := centralizer (φ.ker : Set X) with hCdef
        have hCn : C.Normal := inferInstance
        have hCmap : C.map φ = ⊤ := by
          rcases (hCn.map φ hφ).eq_bot_or_eq_top with h | h
          · exact absurd ((Subgroup.map_eq_bot_iff C).1 h) hC
          · exact h
        obtain ⟨L, ⟨hLC, hLtop⟩, hLmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup X))
          {L : Subgroup X | L ≤ C ∧ L.map φ = ⊤} ⟨C, le_rfl, hCmap⟩
        have hcomm_le : ⁅L, L⁆ ≤ L := commutator_le.2 fun a ha b hb => by
          simp only [commutatorElement_def]
          exact L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)
        have hD : ⁅L, L⁆ = L := by
          by_contra hne
          refine hLmin ⁅L, L⁆ ⟨hcomm_le.trans hLC, ?_⟩ (lt_of_le_of_ne hcomm_le hne)
          rw [map_commutator, hLtop]
          exact hF1
        have hLperf : commutator ↥L = ⊤ := (Subgroup.isPerfect_iff.2 hD).commutator_eq_top
        set ψ : ↥L →* F := φ.comp L.subtype with hψdef
        have hψ : Function.Surjective ψ := by
          intro f
          have : f ∈ L.map φ := hLtop ▸ mem_top f
          obtain ⟨l, hl, hlf⟩ := mem_map.1 this
          exact ⟨⟨l, hl⟩, hlf⟩
        have hker : ∀ l : ↥L, l ∈ ψ.ker ↔ φ (l : X) = 1 := fun l => Iff.rfl
        have hcen' : ψ.ker ≤ center ↥L := by
          intro l hl
          rw [mem_center_iff]
          intro g
          have hlY : (l : X) ∈ φ.ker := (hker l).1 hl
          have hgC : (g : X) ∈ C := hLC g.2
          have := (mem_centralizer_iff.1 hgC) (l : X) hlY
          exact Subtype.ext this.symm
        have hpg : IsPGroup q ψ.ker := by
          rw [IsPGroup.iff_orderOf]
          intro g
          have hgY : ((g : ↥L) : X) ∈ φ.ker := (hker g).1 g.2
          obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hYq ⟨_, hgY⟩
          refine ⟨k, ?_⟩
          have e1 : orderOf g = orderOf (g : ↥L) := (Subgroup.orderOf_coe g).symm
          have e2 : orderOf (g : ↥L) = orderOf ((g : ↥L) : X) := (Subgroup.orderOf_coe _).symm
          have e3 : orderOf (⟨((g : ↥L) : X), hgY⟩ : φ.ker) = orderOf ((g : ↥L) : X) :=
            Subgroup.orderOf_mk _ _
          exact e1.trans (e2.trans (e3.symm.trans hk))
        have := hcen ↥L ψ hψ hLperf hcen' hpg
        exact this.trans (CFSG.SectionRank.pRank_top_le_of_injective hq.one_lt L.subtype
          L.subtype_injective)
    ·
      obtain ⟨p, hp, hpq, hpY⟩ := i1021_exists_prime_ne hYq
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p φ.ker))
      set P' : Subgroup X := (P : Subgroup φ.ker).map φ.ker.subtype with hP'def
      have hfr : normalizer (P' : Set X) ⊔ φ.ker = ⊤ := Sylow.normalizer_sup_eq_top P
      have hP'Y : P' ≤ φ.ker := map_subtype_le _
      obtain ⟨m', hm⟩ := IsPGroup.iff_card.1 (P.isPGroup'.map φ.ker.subtype)
      have hP'q : ¬ q ∣ Nat.card P' := by
        rw [hm]
        intro h
        exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)).symm
      by_cases htop : normalizer (P' : Set X) = ⊤
      ·
        have hP'n : P'.Normal := normalizer_eq_top_iff.1 htop
        have hP'ne : P' ≠ ⊥ :=
          (map_eq_bot_iff_of_injective _ φ.ker.subtype_injective).not.2
            (P.ne_bot_of_dvd_card hpY)
        have hlt : Nat.card (X ⧸ P') < Nat.card X := by
          rw [card_eq_card_quotient_mul_card_subgroup P']
          have h1 : 1 < Nat.card P' := (one_lt_card_iff_ne_bot P').2 hP'ne
          have h2 : 0 < Nat.card (X ⧸ P') := Nat.card_pos
          nlinarith
        have hsurj : Function.Surjective (QuotientGroup.lift P' φ hP'Y) := by
          intro f
          obtain ⟨x, rfl⟩ := hφ f
          exact ⟨x, rfl⟩
        have := ih (X ⧸ P') (by omega) (QuotientGroup.lift P' φ hP'Y) hsurj
        rwa [CFSG.SectionRank.pRank_quotient_eq P' hP'q] at this
      ·
        set X₀ : Subgroup X := normalizer (P' : Set X)
        have hφ₀ : Function.Surjective (φ.comp X₀.subtype) := by
          intro f
          obtain ⟨x, rfl⟩ := hφ f
          have hx : x ∈ X₀ ⊔ φ.ker := hfr ▸ mem_top x
          obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_normal_right.1 hx
          refine ⟨⟨a, ha⟩, ?_⟩
          simp [MonoidHom.mem_ker.1 hb]
        have hlt : Nat.card X₀ < Nat.card X := by
          rw [← card_top (G := X)]
          exact card_lt_of_lt (lt_top_iff_ne_top.2 htop)
        have := ih X₀ (by omega) (φ.comp X₀.subtype) hφ₀
        exact this.trans (CFSG.SectionRank.pRank_top_le_of_injective hq.one_lt X₀.subtype
          X₀.subtype_injective)

end Main

end CFSG.HardMathSupport.Solomon.Coordinator
