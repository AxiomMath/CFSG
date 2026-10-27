module

public import CFSG.Quasithin.Vol2.Ch11SecFQ3

public section

open scoped Pointwise

namespace CFSG

theorem exists_cartan_in_borel_of_central_comap {L X : Type} [Group L] [Finite L] [Group X] [Finite X]
    {e : L →* X} (hsurj : Function.Surjective e)
    (hker : e.ker ≤ Subgroup.center L) (hker2 : IsPGroup 2 e.ker)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {T₀ U₀ : Subgroup X} (hT₀ : T₀ ≤ Subgroup.normalizer (U₀ : Set X))
    (hT₀ab : ∀ a ∈ T₀, ∀ b ∈ T₀, a * b = b * a)
    (hT₀pi : IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} T₀)
    (hr : 3 ≤ CFSG.Open.pRank q T₀) :
    ∃ H : Subgroup L, H ≤ Subgroup.normalizer (U₀.comap e : Set L) ∧
      IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} H ∧
      3 ≤ CFSG.Open.pRank q H := by
  classical
  let H₀ : Subgroup L := T₀.comap e
  let π : Set Nat.Primes := {p : Nat.Primes | (p : ℕ) ≠ 2}
  haveI : Fact q.Prime := ⟨hq⟩
  let g : ↥H₀ →* T₀ := (e.comp H₀.subtype).codRestrict T₀ (fun x => x.2)
  have hg : Function.Surjective g := by
    intro t
    obtain ⟨l, hl⟩ := hsurj (t : X)
    refine ⟨⟨l, ?_⟩, Subtype.ext hl⟩
    rw [Subgroup.mem_comap]
    exact hl ▸ t.2
  have hker_g : g.ker = e.ker.subgroupOf H₀ := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact Subtype.ext_iff
  have hker_le : e.ker ≤ H₀ := by
    intro x hx
    rw [Subgroup.mem_comap]
    rw [MonoidHom.mem_ker] at hx
    rw [hx]
    exact T₀.one_mem
  have hcardker : Nat.card g.ker = Nat.card e.ker := by
    rw [hker_g]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv
  have hK2 : IsPGroup 2 (e.ker.subgroupOf H₀) := hker2.comap_subtype (K := H₀)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardker2 : Nat.card (e.ker.subgroupOf H₀) = Nat.card e.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv
  have hqker : ¬ q ∣ Nat.card g.ker := by
    rw [hcardker, ← hcardker2]
    obtain ⟨k, hk⟩ := hK2.exists_card_eq
    rw [hk]
    intro hdvd
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hdvd))
  haveI : Group.IsSolvable ↥(e.ker.subgroupOf H₀) :=
    CFSG.Quasithin.Vol2.Ch11.SecF.isSolvable_of_isPGroup_two' hK2
  haveI : Group.IsSolvable T₀ :=
    Group.isSolvable_of_comm (fun a b => Subtype.ext (hT₀ab a a.2 b b.2))
  have hsolv : Group.IsSolvable ↥H₀ := by
    refine Group.isSolvable_of_ker_le_range
      (G' := ↥(e.ker.subgroupOf H₀)) (G'' := T₀) (e.ker.subgroupOf H₀).subtype g ?_
    intro x hx
    rw [Subgroup.range_subtype, ← hker_g]
    exact hx
  have hrank_eq : CFSG.Open.pRank q H₀ = CFSG.Open.pRank q T₀ := by
    have hquot := CFSG.SectionRank.pRank_quotient_eq (p := q) (G := ↥H₀) g.ker hqker
    calc
      CFSG.Open.pRank q H₀ = CFSG.Open.pRank q (⊤ : Subgroup ↥H₀) :=
        CFSG.SectionRank.pRank_eq_pRank_top_subgroup H₀
      _ = CFSG.Open.pRank q (⊤ : Subgroup (↥H₀ ⧸ g.ker)) := hquot.symm
      _ = CFSG.Open.pRank q (⊤ : Subgroup T₀) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv hq.one_lt
          (QuotientGroup.quotientKerEquivOfSurjective g hg)
      _ = CFSG.Open.pRank q T₀ :=
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup T₀).symm
  have h3H : 3 ≤ CFSG.Open.pRank q H₀ := by
    rw [hrank_eq]
    exact hr
  obtain ⟨E, -, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (G := ↥H₀) (p := q) hq.one_lt ⊤
  have h3top : 3 ≤ CFSG.Open.pRank q (⊤ : Subgroup ↥H₀) := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup H₀]
    exact h3H
  have hEpi : IsPiSubgroup π E := by
    intro p hp
    have hpdiv : (p : ℕ) ∣ q ^ CFSG.Open.pRank q (⊤ : Subgroup ↥H₀) := by
      rwa [← hEcard]
    have hpq : (p : ℕ) = q :=
      (Nat.prime_dvd_prime_iff_eq p.2 hq).mp (p.2.dvd_of_dvd_pow hpdiv)
    show (p : ℕ) ≠ 2
    rw [hpq]
    exact hq2
  have hE3 : 3 ≤ CFSG.Open.pRank q E := by
    have hle : CFSG.Open.pRank q (⊤ : Subgroup ↥H₀) ≤ CFSG.Open.pRank q E :=
      CFSG.SectionRank.le_pRank hq.one_lt (le_refl E) hE hEcard
    exact h3top.trans hle
  obtain ⟨H', hHall, hEH'⟩ :=
    CFSG.SolvableHall.solvable_hall_containment hsolv π E hEpi
  have hH'3 : 3 ≤ CFSG.Open.pRank q H' :=
    hE3.trans (CFSG.SectionRank.pRank_mono hq.one_lt hEH')
  let Hf : Subgroup L := H'.map H₀.subtype
  refine ⟨Hf, ?_, ?_, ?_⟩
  · have hH₀norm : H₀ ≤ Subgroup.normalizer (U₀.comap e : Set L) :=
      (Subgroup.comap_mono hT₀).trans (Subgroup.le_normalizer_comap (H := U₀) e)
    exact (Subgroup.map_subtype_le H').trans hH₀norm
  · intro p hp
    apply hHall.p_in_pi_of_p_dvd_card p
    rwa [Subgroup.card_map_of_injective H₀.subtype_injective] at hp
  · have hrank : CFSG.Open.pRank q Hf = CFSG.Open.pRank q H' := by
      calc
        CFSG.Open.pRank q Hf = CFSG.Open.pRank q (⊤ : Subgroup ↥Hf) :=
          CFSG.SectionRank.pRank_eq_pRank_top_subgroup Hf
        _ = CFSG.Open.pRank q (⊤ : Subgroup ↥H') :=
          (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hq.one_lt
            (Subgroup.equivMapOfInjective H' H₀.subtype H₀.subtype_injective)).symm
        _ = CFSG.Open.pRank q H' :=
          (CFSG.SectionRank.pRank_eq_pRank_top_subgroup H').symm
    rw [hrank]
    exact hH'3

end CFSG
