module

public import CFSG.FeitThompson.Local.MetacyclicOddGroupUniqueTorsionPlane
public import CFSG.FeitThompson.Local.QuadraticActionsDescendSections
import CFSG.FeitThompson.Local.FrattiniQuotientAutomorphismKernelPGroup
import CFSG.FeitThompson.Local.InvariantCyclicComplementPrimeLine

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {p : ℕ} {R A : Type*} [Group R] [Group A]

theorem commute_mulAut_of_isCyclic (S : Type*) [Group S] [IsCyclic S] (a b : MulAut S) :
    a * b = b * a :=
  (IsCyclic.mulAutMulEquiv (G := S)).injective (by rw [map_mul, map_mul, mul_comm])

private theorem isInvariantSubgroup_of_forall {ρ : A →* MulAut R} {N : Subgroup R}
    (h : ∀ b : A, ∀ v ∈ N, ρ b v ∈ N) : IsInvariantSubgroup ρ N := by
  rw [isInvariantSubgroup_iff_forall_map_eq]
  refine fun b => le_antisymm ?_ ?_
  · rintro x ⟨v, hv, rfl⟩
    exact h b v hv
  · intro v hv
    refine ⟨ρ b⁻¹ v, h b⁻¹ v hv, ?_⟩
    change ρ b (ρ b⁻¹ v) = v
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem exists_invariant_isCompl_of_pow_eq_one_of_isMulCommutative {C : Type*} [Group C]
    [IsMulCommutative C] (hp : p.Prime) (hexp : ∀ x : C, x ^ p = 1) {B : Type*} [Group B]
    [Finite B] (β : B →* MulAut C) (hB : ¬ p ∣ Nat.card B) {S : Subgroup C}
    (hS : ∀ b : B, ∀ x ∈ S, β b x ∈ S) :
    ∃ T : Subgroup C, (∀ b : B, ∀ x ∈ T, β b x ∈ T) ∧ IsCompl S T :=
  letI : CommGroup C := IsMulCommutative.instCommGroup
  exists_invariant_isCompl_of_pow_eq_one hp hexp β hB hS

theorem card_map_mul_card_inf_ker {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    (K : Subgroup G) : Nat.card (K.map f) * Nat.card (K ⊓ f.ker : Subgroup G) = Nat.card K := by
  set g : K →* H := f.comp K.subtype with hg
  have hrange : g.range = K.map f := by
    ext y
    simp only [MonoidHom.mem_range, Subgroup.mem_map, hg, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype]
    exact ⟨fun ⟨x, hx⟩ => ⟨x, x.2, hx⟩, fun ⟨x, hx, hxy⟩ => ⟨⟨x, hx⟩, hxy⟩⟩
  have hker : Nat.card g.ker = Nat.card (K ⊓ f.ker : Subgroup G) := by
    have h1 : g.ker = (f.ker).subgroupOf K := by
      ext x; simp [hg, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rw [h1, ← Subgroup.card_map_of_injective (K := (f.ker).subgroupOf K)
      (f := K.subtype) K.subtype_injective, Subgroup.subgroupOf_map_subtype, inf_comm]
  have h2 := Subgroup.card_mul_index g.ker
  rw [Subgroup.index_ker g, hrange, hker] at h2
  rw [← h2]; ring

theorem natCard_omega1_inf_eq_prime [Finite R] (hp : p.Prime) (hR : IsPGroup p R)
    (hΩ : (omega1 p R : Set R) = {x : R | x ^ p = 1}) {S : Subgroup R} [IsCyclic S]
    [Nontrivial S] : Nat.card ((omega1 p R) ⊓ S : Subgroup R) = p := by
  have := Fact.mk hp
  obtain ⟨K, hKcard, hKmem⟩ :=
    exists_natCard_eq_prime_forall_pow_eq_one_mem (Q := S) hp (hR.to_subgroup S)
  have hKfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hKcard]; exact hp.ne_zero)
  have hKexp : ∀ k : K, ((k : S) : R) ^ p = 1 := by
    intro k
    have h : (k : S) ^ p = 1 := by
      have hk := pow_card_eq_one' (x := k)
      rw [hKcard] at hk
      exact congrArg (Subgroup.subtype K) hk
    exact congrArg (Subgroup.subtype S) h
  have hmem : ∀ x : R, x ∈ omega1 p R → x ^ p = 1 := fun x hx => (Set.ext_iff.mp hΩ x).mp hx
  have heq : K.map S.subtype = (omega1 p R) ⊓ S := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨k, hk, rfl⟩
      exact ⟨mem_omega1_of_pow_eq_one (hKexp ⟨k, hk⟩), k.2⟩
    · rintro x ⟨hxΩ, hxS⟩
      exact ⟨⟨x, hxS⟩, hKmem _ (Subtype.ext (by simpa using hmem x hxΩ)), rfl⟩
  rw [← heq, Subgroup.card_map_of_injective S.subtype_injective, hKcard]

theorem isCyclic_of_natCard_omega1_lt [Finite R] (hp : p.Prime) (hodd : Odd p)
    (hR : IsPGroup p R) (h : Nat.card (omega1 p R) < p ^ 2) : IsCyclic R := by
  by_contra hnc
  obtain ⟨E, hEcard, hEexp⟩ := exists_natCard_eq_prime_sq_forall_pow_eq_one hp hodd hR hnc
  have hle : Nat.card E ≤ Nat.card (omega1 p R) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le
      fun x hx => mem_omega1_of_pow_eq_one (hEexp x hx))
  rw [hEcard] at hle
  omega

theorem isCyclic_commutator_of_isMetacyclic (hm : IsMetacyclic R) : IsCyclic (commutator R) := by
  obtain ⟨S₀, hS₀n, hS₀c, hQc⟩ := isMetacyclic_iff.mp hm
  have := hS₀n
  have := hQc
  exact Subgroup.isCyclic_of_le (Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
    (inferInstance : IsMulCommutative (R ⧸ S₀)))

theorem exists_maximal_invariant_isCyclic [Finite R] (ρ : A →* MulAut R)
    {S₀ : Subgroup R} (hinv : IsInvariantSubgroup ρ S₀) (hcyc : IsCyclic S₀) :
    ∃ S : Subgroup R, IsInvariantSubgroup ρ S ∧ IsCyclic S ∧ S₀ ≤ S ∧
      ∀ T : Subgroup R, IsInvariantSubgroup ρ T → IsCyclic T → S₀ ≤ T →
        Nat.card T ≤ Nat.card S := by
  set s : Set ℕ := {n | ∃ T : Subgroup R,
    (IsInvariantSubgroup ρ T ∧ IsCyclic T ∧ S₀ ≤ T) ∧ Nat.card T = n}
  have hne : s.Nonempty := ⟨Nat.card S₀, S₀, ⟨hinv, hcyc, le_rfl⟩, rfl⟩
  have hbdd : BddAbove s := by
    refine ⟨Nat.card R, ?_⟩
    rintro n ⟨T, -, rfl⟩
    exact T.card_le_card_group
  obtain ⟨S, hSP, hScard⟩ := Nat.sSup_mem hne hbdd
  exact ⟨S, hSP.1, hSP.2.1, hSP.2.2, fun T hT1 hT2 hT3 => by
    rw [hScard]; exact le_csSup hbdd ⟨T, ⟨hT1, hT2, hT3⟩, rfl⟩⟩

theorem le_center_of_invariant_isCyclic (ρ : A →* MulAut R) {S : Subgroup R} [S.Normal]
    [IsCyclic S] (hSinv : IsInvariantSubgroup ρ S)
    (hgen : Subgroup.closure {y : R | ∃ (x : R) (a : A), x⁻¹ * ρ a x = y} = ⊤) :
    S ≤ Subgroup.center R := by
  set φ : R →* MulAut S := MulAut.conjNormal with hφ
  set ψ : A →* MulAut S := hSinv.restrictAut
  have hinv : ∀ (a : A) (s : S), (((ψ a)⁻¹ s : S) : R) = ρ a⁻¹ (s : R) := by
    intro a s
    rw [← map_inv ψ a]
    exact hSinv.coe_restrictAut_apply a⁻¹ s
  have hconj : ∀ (x : R) (a : A), ψ a * φ x * (ψ a)⁻¹ = φ (ρ a x) := by
    intro x a
    ext s
    have h2 : ρ a (ρ a⁻¹ (s : R)) = (s : R) := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    calc (((ψ a * φ x * (ψ a)⁻¹) s : S) : R)
        = ρ a (x * ρ a⁻¹ (s : R) * x⁻¹) := by
          rw [MulAut.mul_apply, MulAut.mul_apply, hSinv.coe_restrictAut_apply, hφ,
            MulAut.conjNormal_apply, hinv]
      _ = ρ a x * (s : R) * (ρ a x)⁻¹ := by rw [map_mul, map_mul, h2, map_inv]
      _ = ((φ (ρ a x) s : S) : R) := by rw [hφ, MulAut.conjNormal_apply]
  have key : ∀ (x : R) (a : A), φ (ρ a x) = φ x := by
    intro x a
    rw [← hconj x a, commute_mulAut_of_isCyclic _ (ψ a) (φ x), mul_assoc, mul_inv_cancel, mul_one]
  have hcent : Subgroup.centralizer (S : Set R) = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro y ⟨x, a, rfl⟩
    have h0 : φ (x⁻¹ * ρ a x) = 1 := by rw [map_mul, map_inv, key x a, inv_mul_cancel]
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro s hs
    have h1 := congrArg (fun f : MulAut S => ((f ⟨s, hs⟩ : S) : R)) h0
    simp only [hφ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  intro s hs
  rw [mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.centralizer (S : Set R) := hcent ▸ mem_top g
  rw [mem_centralizer_iff] at hg
  exact (hg s hs).symm

theorem natCard_omega1_quotient_eq_prime [Finite R] [Finite A] (hp : p.Prime) (hodd : Odd p)
    (hR : IsPGroup p R) (hpA : ¬ p ∣ Nat.card A) (ρ : A →* MulAut R) {S : Subgroup R} [S.Normal]
    [IsCyclic S] [Nontrivial S] (hSinv : IsInvariantSubgroup ρ S) (hR'S : commutator R ≤ S)
    (hSmax : ∀ T : Subgroup R, IsInvariantSubgroup ρ T → IsCyclic T → commutator R ≤ T →
      Nat.card T ≤ Nat.card S)
    (hΩR : (omega1 p R : Set R) = {x : R | x ^ p = 1})
    (hcardΩR : Nat.card (omega1 p R) = p ^ 2) :
    Nat.card (omega1 p (R ⧸ S)) = p := by
  have := Fact.mk hp
  have hRtors : ∀ x : R, x ∈ omega1 p R ↔ x ^ p = 1 := fun x => Set.ext_iff.mp hΩR x
  have hQab : IsMulCommutative (R ⧸ S) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hR'S
  have hcl : commutator (R ⧸ S) ≤ Subgroup.center (R ⧸ S) :=
    le_of_eq_of_le (commutator_eq_bot (R ⧸ S)) bot_le
  set Ω : Subgroup (R ⧸ S) := omega1 p (R ⧸ S)
  set W' : Subgroup (R ⧸ S) := (omega1 p R).map (QuotientGroup.mk' S)
  have hΩQ : ∀ x : R ⧸ S, x ∈ Ω ↔ x ^ p = 1 := fun x => mem_omega1_iff hodd hcl
  have hW'Ω : W' ≤ Ω := by
    rintro y ⟨x, hx, rfl⟩
    exact (hΩQ _).mpr (by rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow,
      (hRtors x).mp hx, QuotientGroup.mk_one])
  have hcardinf : Nat.card ((omega1 p R) ⊓ S : Subgroup R) = p :=
    natCard_omega1_inf_eq_prime hp hR hΩR
  have hcardW' : Nat.card W' = p := by
    have h := card_map_mul_card_inf_ker (QuotientGroup.mk' S) (omega1 p R)
    rw [QuotientGroup.ker_mk', hcardinf, hcardΩR, show p ^ 2 = p * p from by ring] at h
    exact Nat.eq_of_mul_eq_mul_right hp.pos h
  set σ : A →* MulAut (R ⧸ S) := hSinv.quotientAut with hσ
  have hΩinv : IsInvariantSubgroup σ Ω := isInvariantSubgroup_of_characteristic σ _
  have hmkσ : ∀ (b : A) (x : R), σ b (QuotientGroup.mk' S x) = QuotientGroup.mk' S (ρ b x) := by
    intro b x
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hσ, hSinv.quotientAut_mk]
  have hW'inv : IsInvariantSubgroup σ W' := isInvariantSubgroup_of_forall (by
    rintro b y ⟨x, hx, rfl⟩
    exact ⟨ρ b x, (isInvariantSubgroup_of_characteristic ρ (omega1 p R)).apply_mem b hx,
      (hmkσ b x).symm⟩)
  obtain ⟨T, hTinv, hTcompl⟩ := exists_invariant_isCompl_of_pow_eq_one_of_isMulCommutative
    (C := Ω) hp (fun x => Subtype.ext (by simpa using (hΩQ (x : R ⧸ S)).mp x.2))
    hΩinv.restrictAut hpA (S := W'.subgroupOf Ω)
    (by
      intro b x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      simpa using hW'inv.apply_mem b hx)
  set T' : Subgroup (R ⧸ S) := T.map Ω.subtype
  have hT'inv : IsInvariantSubgroup σ T' := isInvariantSubgroup_of_forall (by
    rintro b y ⟨t, ht, rfl⟩
    exact ⟨hΩinv.restrictAut b t, hTinv b t ht, hΩinv.coe_restrictAut_apply b t⟩)
  have hinf : ∀ y : R ⧸ S, y ∈ W' → y ∈ T' → y = 1 := by
    rintro y hyW ⟨t, ht, rfl⟩
    have h1 : t ∈ W'.subgroupOf Ω := Subgroup.mem_subgroupOf.mpr hyW
    have h2 : t ∈ (⊥ : Subgroup Ω) := hTcompl.inf_eq_bot.le ⟨h1, ht⟩
    rw [Subgroup.mem_bot] at h2
    rw [h2]; rfl
  set X : Subgroup R := T'.comap (QuotientGroup.mk' S) with hXdef
  have hSX : S ≤ X := by
    intro x hx
    have h : (QuotientGroup.mk' S) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hXdef, Subgroup.mem_comap, h]
    exact one_mem _
  have hXinv : IsInvariantSubgroup ρ X := isInvariantSubgroup_of_forall (by
    intro b x hx
    rw [hXdef, Subgroup.mem_comap] at hx ⊢
    rw [← hmkσ b x]
    exact hT'inv.apply_mem b hx)
  have htors : ∀ x : R, x ∈ X → x ^ p = 1 → x ∈ (omega1 p R) ⊓ S := by
    intro x hxX hxp
    refine ⟨mem_omega1_of_pow_eq_one hxp, ?_⟩
    have h1 : (QuotientGroup.mk' S) x ∈ W' := ⟨x, mem_omega1_of_pow_eq_one hxp, rfl⟩
    have h3 := hinf _ h1 hxX
    rw [QuotientGroup.mk'_apply] at h3
    exact (QuotientGroup.eq_one_iff x).mp h3
  have hΩXle : omega1 p X ≤ ((omega1 p R) ⊓ S).subgroupOf X := by
    refine omega1_le fun x hx => ?_
    rw [Subgroup.mem_subgroupOf]
    exact htors (x : R) x.2 (by simpa using congrArg (Subgroup.subtype X) hx)
  have hcardΩX : Nat.card (omega1 p X) ≤ p := by
    have h1 : Nat.card (omega1 p X) ∣ Nat.card (((omega1 p R) ⊓ S).subgroupOf X) :=
      Subgroup.card_dvd_of_le hΩXle
    have h2 : Nat.card (((omega1 p R) ⊓ S).subgroupOf X) ∣
        Nat.card ((omega1 p R) ⊓ S : Subgroup R) :=
      Subgroup.card_comap_dvd_of_injective _ _ X.subtype_injective
    rw [hcardinf] at h2
    exact Nat.le_of_dvd hp.pos (h1.trans h2)
  have hXcyc : IsCyclic X := by
    refine isCyclic_of_natCard_omega1_lt hp hodd (hR.to_subgroup X) ?_
    have h : p < p ^ 2 := by nlinarith [hp.two_le]
    omega
  have hXS : S = X :=
    Subgroup.eq_of_le_of_card_ge hSX (hSmax X hXinv hXcyc (hR'S.trans hSX))
  have hT'bot : T' = ⊥ := by
    have h1 : T' = X.map (QuotientGroup.mk' S) :=
      (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective S) T').symm
    rw [h1, ← hXS]
    refine le_antisymm ?_ bot_le
    rintro y ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff x).mpr hx
  have hTbot : T = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective T Ω.subtype_injective).mp hT'bot
  have htop : W'.subgroupOf Ω = ⊤ := by
    have h := hTcompl.sup_eq_top
    rw [hTbot, sup_bot_eq] at h
    exact h
  rw [le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hW'Ω, hcardW']

theorem isMulCommutative_of_isMetacyclic_of_coprime
    [Finite R] [Finite A] (hp : p.Prime) (hodd : Odd p) (hR : IsPGroup p R)
    (hm : IsMetacyclic R) (hcop : (Nat.card A).Coprime (Nat.card R)) (ρ : A →* MulAut R)
    (hgen : Subgroup.closure {y : R | ∃ (x : R) (a : A), x⁻¹ * ρ a x = y} = ⊤) :
    IsMulCommutative R := by
  have := Fact.mk hp
  by_contra hnab
  have hnc : ¬ IsCyclic R := fun h => hnab (@IsCyclic.isMulCommutative _ _ h)
  have hntR : Nontrivial R := by
    rcases subsingleton_or_nontrivial R with h | h
    · exact absurd isCyclic_of_subsingleton hnc
    · exact h
  obtain ⟨n, hn, hcardR⟩ := hR.nontrivial_iff_card.mp hntR
  have hpA : ¬ p ∣ Nat.card A := by
    intro h
    have h2 := Nat.dvd_gcd h (hcardR ▸ dvd_pow_self p hn.ne' : p ∣ Nat.card R)
    rw [Nat.Coprime] at hcop
    rw [hcop] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  have hR'ne : commutator R ≠ ⊥ := fun h => hnab ((commutator_eq_bot_iff R).mp h)
  obtain ⟨S, hSinv, hScyc, hR'S, hSmax⟩ := exists_maximal_invariant_isCyclic ρ
    (isInvariantSubgroup_of_characteristic ρ _) (isCyclic_commutator_of_isMetacyclic hm)
  have := hScyc
  have hSnorm : S.Normal := Subgroup.Normal.of_commutator_le R hR'S
  have := hSnorm
  have hSnt : Nontrivial S :=
    (Subgroup.nontrivial_iff_ne_bot S).mpr fun h => hR'ne (le_bot_iff.mp (h ▸ hR'S))
  have hScen : S ≤ Subgroup.center R := le_center_of_invariant_isCyclic ρ hSinv hgen
  have hΩR : (omega1 p R : Set R) = {x : R | x ^ p = 1} :=
    coe_omega1_of_isMetacyclic hp hodd hR hnc hm
  have hcardΩR : Nat.card (omega1 p R) = p ^ 2 :=
    natCard_omega1_of_isMetacyclic hp hodd hR hnc hm
  have hQcyc : IsCyclic (R ⧸ S) :=
    isCyclic_of_natCard_omega1_lt hp hodd (hR.to_quotient S)
      (by
        rw [natCard_omega1_quotient_eq_prime hp hodd hR hpA ρ hSinv hR'S hSmax hΩR hcardΩR]
        nlinarith [hp.two_le])
  have hcyc : IsCyclic (R ⧸ Subgroup.center R) :=
    isCyclic_of_surjective (QuotientGroup.map S (Subgroup.center R) (MonoidHom.id R) hScen)
      (by
        intro x
        induction x using QuotientGroup.induction_on with
        | H v => exact ⟨QuotientGroup.mk v, rfl⟩)
  exact hnab (isMulCommutative_of_isCyclic_quotient_center_self R)

end

end CFSG.FeitThompson
