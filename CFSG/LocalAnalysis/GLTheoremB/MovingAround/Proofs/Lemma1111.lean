module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BSL34Sylow
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec10Closed3
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113b

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1111

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

section Lines

variable {G : Type} [Group G] [Finite G]

abbrev conjActOn (P U : Subgroup G) (hPU : P ≤ Subgroup.normalizer (U : Set G)) : MulAction P U where
  smul g u := ⟨(g : G) * u * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.1 (hPU g.2) u).1 u.2⟩
  one_smul u := by
    apply Subtype.ext
    show (1 : G) * (u : G) * (1 : G)⁻¹ = u
    simp
  mul_smul g h u := by
    apply Subtype.ext
    show ((g : G) * (h : G)) * (u : G) * ((g : G) * (h : G))⁻¹ =
      (g : G) * ((h : G) * (u : G) * (h : G)⁻¹) * (g : G)⁻¹
    group

theorem card_fixed_eq_inf (P U : Subgroup G) :
    Nat.card {u : U // ∀ g : P, (g : G) * (u : G) * (g : G)⁻¹ = u} =
      Nat.card ↥(U ⊓ Subgroup.centralizer (P : Set G)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨(x.1 : G), ?_⟩
      invFun := fun s => ⟨⟨s.1, (Subgroup.mem_inf.1 s.2).1⟩, ?_⟩
      left_inv := fun x => ?_
      right_inv := fun s => ?_ }
  · refine Subgroup.mem_inf.2 ⟨x.1.2, Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)⟩
    have := x.2 ⟨h, hh⟩
    calc h * (x.1 : G) = (h * (x.1 : G) * h⁻¹) * h := by group
      _ = (x.1 : G) * h := by rw [this]
  · intro g
    have hs := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 s.2).2 (g : G) g.2
    calc (g : G) * s.1 * (g : G)⁻¹ = (s.1 * (g : G)) * (g : G)⁻¹ := by rw [← hs]
      _ = s.1 := by group
  · apply Subtype.ext; apply Subtype.ext; rfl
  · apply Subtype.ext; rfl

theorem card_modEq_fixed (P U : Subgroup G) (hP : IsPGroup 3 ↥P)
    (hPU : P ≤ Subgroup.normalizer (U : Set G)) :
    Nat.card U ≡ Nat.card ↥(U ⊓ Subgroup.centralizer (P : Set G)) [MOD 3] := by
  letI := conjActOn P U hPU
  have h1 := hP.card_modEq_card_fixedPoints U
  have h2 : Nat.card (MulAction.fixedPoints P U) =
      Nat.card {u : U // ∀ g : P, (g : G) * (u : G) * (g : G)⁻¹ = u} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun u => ?_)
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h g
      exact congrArg Subtype.val (h g)
    · intro h g
      apply Subtype.ext
      exact h g
  rw [h2, card_fixed_eq_inf P U] at h1
  exact h1


theorem lines_card_le (P U : Subgroup G) (hP : IsPGroup 3 ↥P)
    (hU9 : Nat.card U = 9) (hPU : P ≤ Subgroup.normalizer (U : Set G)) :
    Nat.card P ≤ 3 * Nat.card ↥(P ⊓ Subgroup.centralizer (U : Set G)) := by
  classical
  letI := conjActOn P U hPU
  have hSU : (U ⊓ Subgroup.centralizer (P : Set G)) ≤ U := inf_le_left
  have hmod := card_modEq_fixed P U hP hPU
  have hSdvd : Nat.card ↥(U ⊓ Subgroup.centralizer (P : Set G)) ∣ 9 := by
    have := Subgroup.card_subgroup_dvd_card ((U ⊓ Subgroup.centralizer (P : Set G)).subgroupOf U)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSU).toEquiv, hU9] at this
    exact this
  have h3dvd : 3 ∣ Nat.card ↥(U ⊓ Subgroup.centralizer (P : Set G)) := by
    unfold Nat.ModEq at hmod
    rw [hU9] at hmod
    omega
  have hScases : Nat.card ↥(U ⊓ Subgroup.centralizer (P : Set G)) = 3 ∨
      Nat.card ↥(U ⊓ Subgroup.centralizer (P : Set G)) = 9 := by
    have hdiv9 : Nat.divisors 9 = {1, 3, 9} := by decide
    have hmem := Nat.mem_divisors.2 ⟨hSdvd, by norm_num⟩
    rw [hdiv9] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · rw [h] at h3dvd; norm_num at h3dvd
    · exact Or.inl h
    · exact Or.inr h
  rcases hScases with hS3 | hS9
  ·
    have hUS : ¬ U ≤ U ⊓ Subgroup.centralizer (P : Set G) := by
      intro hle
      have heq : U = U ⊓ Subgroup.centralizer (P : Set G) := le_antisymm hle hSU
      have := congrArg (fun H : Subgroup G => Nat.card ↥H) heq
      simp only [hU9, hS3] at this
      norm_num at this
    obtain ⟨v0, hv0U, hv0S⟩ : ∃ v0 ∈ U, v0 ∉ U ⊓ Subgroup.centralizer (P : Set G) := by
      by_contra hcon
      exact hUS (fun v hv => by
        by_contra hv'
        exact hcon ⟨v, hv, hv'⟩)
    set v0' : U := ⟨v0, hv0U⟩ with hv0'
    have hnotfix : ¬ ∀ g : P, g • v0' = v0' := by
      intro hfix
      apply hv0S
      refine Subgroup.mem_inf.2 ⟨hv0U, Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)⟩
      have := congrArg Subtype.val (hfix ⟨h, hh⟩)
      change (h : G) * v0 * (h : G)⁻¹ = v0 at this
      calc h * v0 = (h * v0 * (h : G)⁻¹) * h := by group
        _ = v0 * h := by rw [this]
    have hone : (1 : U) ∉ MulAction.orbit P v0' := by
      rintro ⟨g, hg⟩
      have h1 : v0 = 1 := by
        have := congrArg Subtype.val hg
        change (g : G) * v0 * (g : G)⁻¹ = 1 at this
        calc v0 = (g : G)⁻¹ * ((g : G) * v0 * (g : G)⁻¹) * (g : G) := by group
          _ = 1 := by rw [this]; group
      exact hv0S (h1 ▸ Subgroup.one_mem _)
    have hlt : Set.ncard (MulAction.orbit P v0') < Set.ncard (Set.univ : Set U) := by
      apply Set.ncard_lt_ncard _ Set.finite_univ
      rw [Set.ssubset_univ_iff]
      intro heq
      apply hone
      rw [heq]
      exact Set.mem_univ _
    have horb9 : Set.ncard (Set.univ : Set U) = 9 := by
      rw [Set.ncard_univ, hU9]
    obtain ⟨n, hn⟩ := hP.card_orbit v0'
    rw [← Nat.card_coe_set_eq, hn] at hlt
    rw [horb9] at hlt
    have hn1 : n = 1 := by
      rcases Nat.lt_or_ge n 2 with h2 | h2
      · interval_cases n
        ·
          exfalso
          have hsing : Set.ncard (MulAction.orbit P v0') = 1 := by
            rw [Nat.card_coe_set_eq] at hn
            simpa using hn
          obtain ⟨x, hx⟩ := Set.ncard_eq_one.1 hsing
          apply hnotfix
          intro g
          have hmem : g • v0' ∈ MulAction.orbit P v0' := MulAction.mem_orbit _ _
          have hmem' : v0' ∈ MulAction.orbit P v0' := MulAction.mem_orbit_self _
          rw [hx] at hmem hmem'
          rw [Set.mem_singleton_iff] at hmem hmem'
          rw [hmem, hmem']
        · rfl
      · exfalso
        have : 9 ≤ 3 ^ n := by
          calc 9 = 3 ^ 2 := by norm_num
            _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h2
        omega
    have horbcard : Nat.card ↥(MulAction.orbit P v0') = 3 := by
      rw [hn, hn1]
      norm_num
    have hclaim : ∀ g : P, g • v0' = v0' → (g : G) ∈ Subgroup.centralizer (U : Set G) := by
      intro g hg
      have hgv : (g : G) * v0 * (g : G)⁻¹ = v0 := congrArg Subtype.val hg
      have hgv' : (g : G) * v0 = v0 * (g : G) := by
        calc (g : G) * v0 = ((g : G) * v0 * (g : G)⁻¹) * (g : G) := by group
          _ = v0 * (g : G) := by rw [hgv]
      set S := U ⊓ Subgroup.centralizer (P : Set G) with hS
      set T := S ⊔ Subgroup.zpowers v0 with hT
      have hTle : T ≤ Subgroup.centralizer ({(g : G)} : Set G) := by
        refine sup_le ?_ ?_
        · intro s hs
          have hs' := Subgroup.mem_inf.1 hs
          refine Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact Subgroup.mem_centralizer_iff.1 hs'.2 _ g.2
        · rw [Subgroup.zpowers_le]
          refine Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact hgv'
      have hTU : T ≤ U := sup_le inf_le_left (Subgroup.zpowers_le.2 hv0U)
      have hST : S ≤ T := le_sup_left
      have hv0T : v0 ∈ T := (le_sup_right : Subgroup.zpowers v0 ≤ T) (Subgroup.mem_zpowers v0)
      have hSne : S ≠ T := fun h => hv0S (h ▸ hv0T)
      have hTdvd : Nat.card ↥T ∣ 9 := by
        have := Subgroup.card_subgroup_dvd_card (T.subgroupOf U)
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTU).toEquiv, hU9] at this
        exact this
      have h3T : 3 ∣ Nat.card ↥T := by
        have := Subgroup.card_dvd_of_le hST
        rw [hS3] at this
        exact this
      have hT9 : Nat.card ↥T = 9 := by
        have hdiv9 : Nat.divisors 9 = {1, 3, 9} := by decide
        have hmem := Nat.mem_divisors.2 ⟨hTdvd, by norm_num⟩
        rw [hdiv9] at hmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h | h
        · rw [h] at h3T; norm_num at h3T
        · exfalso
          apply hSne
          apply Subgroup.eq_of_le_of_card_ge hST
          rw [h, hS3]
        · exact h
      have hTeq : T = U := Subgroup.eq_of_le_of_card_ge hTU (by rw [hU9, hT9])
      refine Subgroup.mem_centralizer_iff.2 (fun u hu => ?_)
      have huT : u ∈ T := by rw [hTeq]; exact hu
      have := Subgroup.mem_centralizer_iff.1 (hTle huT) (g : G) (Set.mem_singleton _)
      exact this.symm
    have hstab : Nat.card ↥(MulAction.stabilizer P v0') ≤
        Nat.card ↥(P ⊓ Subgroup.centralizer (U : Set G)) := by
      refine Nat.card_le_card_of_injective
        (fun x => ⟨(x.1 : G), Subgroup.mem_inf.2 ⟨x.1.2, hclaim x.1 (MulAction.mem_stabilizer_iff.1 x.2)⟩⟩)
        ?_
      intro x y hxy
      dsimp only at hxy
      simp only [Subtype.mk.injEq] at hxy
      exact Subtype.ext (Subtype.ext hxy)
    haveI : Fintype P := Fintype.ofFinite _
    haveI : Fintype (MulAction.orbit P v0') := Fintype.ofFinite _
    haveI : Fintype (MulAction.stabilizer P v0') := Fintype.ofFinite _
    have horb := MulAction.card_orbit_mul_card_stabilizer_eq_card_group P v0'
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      horbcard] at horb
    omega
  ·
    have hSeq : U ⊓ Subgroup.centralizer (P : Set G) = U :=
      Subgroup.eq_of_le_of_card_ge hSU (by rw [hS9, hU9])
    have hPC : P ≤ Subgroup.centralizer (U : Set G) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have huS : u ∈ U ⊓ Subgroup.centralizer (P : Set G) := by rw [hSeq]; exact hu
      exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 huS).2 g hg).symm
    rw [inf_eq_left.2 hPC]
    omega


theorem normal_inf_centralizer (P U : Subgroup G) (hPU : P ≤ Subgroup.normalizer (U : Set G)) :
    ((P ⊓ Subgroup.centralizer (U : Set G)).subgroupOf P).Normal := by
  constructor
  intro k hk g
  rw [Subgroup.mem_subgroupOf] at hk ⊢
  obtain ⟨hkP, hkC⟩ := Subgroup.mem_inf.1 hk
  refine Subgroup.mem_inf.2 ⟨P.mul_mem (P.mul_mem g.2 hkP) (P.inv_mem g.2), ?_⟩
  refine Subgroup.mem_centralizer_iff.2 (fun u hu => ?_)
  have hv : (g : G)⁻¹ * u * (g : G) ∈ U := by
    have := (Subgroup.mem_normalizer_iff.1 (hPU (P.inv_mem g.2)) u).1 hu
    rwa [inv_inv] at this
  have hvk := Subgroup.mem_centralizer_iff.1 hkC _ hv
  calc u * ((g : G) * (k : G) * (g : G)⁻¹)
      = (g : G) * (((g : G)⁻¹ * u * (g : G)) * (k : G)) * (g : G)⁻¹ := by group
    _ = (g : G) * ((k : G) * ((g : G)⁻¹ * u * (g : G))) * (g : G)⁻¹ := by rw [hvk]
    _ = ((g : G) * (k : G) * (g : G)⁻¹) * u := by group

theorem lines_comm (P U : Subgroup G) (hP : IsPGroup 3 ↥P) (hU9 : Nat.card U = 9)
    (hPU : P ≤ Subgroup.normalizer (U : Set G)) :
    ⁅P, P⁆ ≤ P ⊓ Subgroup.centralizer (U : Set G) := by
  set K : Subgroup P := (P ⊓ Subgroup.centralizer (U : Set G)).subgroupOf P with hKdef
  haveI : K.Normal := normal_inf_centralizer P U hPU
  have hKcard : Nat.card K = Nat.card ↥(P ⊓ Subgroup.centralizer (U : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hlines := lines_card_le P U hP hU9 hPU
  have hPcard : Nat.card P = Nat.card (P ⧸ K) * Nat.card K :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup K)
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hQle : Nat.card (P ⧸ K) ≤ 3 := by
    have h1 : Nat.card (P ⧸ K) * Nat.card K ≤ 3 * Nat.card K := by
      rw [← hPcard, hKcard]; exact hlines
    exact Nat.le_of_mul_le_mul_right h1 hKpos
  have hQpow : ∃ j, Nat.card (P ⧸ K) = 3 ^ j := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.1 hP)
    have hdvd : Nat.card (P ⧸ K) ∣ 3 ^ n := by
      rw [← hn, hPcard]; exact Dvd.intro _ rfl
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    exact ⟨k, hk⟩
  have hQcomm : ∀ a b : P ⧸ K, a * b = b * a := by
    obtain ⟨j, hj⟩ := hQpow
    rcases Nat.lt_or_ge j 1 with hj0 | hj1
    · have hj0' : j = 0 := by omega
      subst hj0'
      have : Subsingleton (P ⧸ K) := Nat.card_eq_one_iff_unique.1 (by simpa using hj) |>.1
      exact fun a b => Subsingleton.elim _ _
    · have hj1' : j = 1 := by
        have : 3 ^ j ≤ 3 := by rw [← hj]; exact hQle
        have : j ≤ 1 := by
          by_contra hc
          have : 9 ≤ 3 ^ j := by
            calc 9 = 3 ^ 2 := by norm_num
              _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        omega
      subst hj1'
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      haveI : IsCyclic (P ⧸ K) := isCyclic_of_prime_card (by simpa using hj)
      letI := IsCyclic.commGroup (α := P ⧸ K)
      exact fun a b => mul_comm a b
  refine Subgroup.commutator_le.2 (fun x hx y hy => ?_)
  rw [commutatorElement_def]
  have hcomm' := hQcomm (QuotientGroup.mk ⟨x, hx⟩) (QuotientGroup.mk ⟨y, hy⟩)
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ : P) : P ⧸ K) = 1 := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hcomm']
    group
  have h2 := (QuotientGroup.eq_one_iff _).1 h1
  rw [hKdef, Subgroup.mem_subgroupOf] at h2
  exact h2

end Lines

section Product

variable {G : Type} [Group G] [Finite G]

def prodHom (H K : Subgroup G) (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) : ↥H × ↥K →* G :=
  { toFun := fun p => (p.1 : G) * (p.2 : G)
    map_one' := by simp
    map_mul' := fun p q => by
      have hcomm := hc (q.1 : G) q.1.2 (p.2 : G) p.2.2
      simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
      calc (p.1 : G) * (q.1 : G) * ((p.2 : G) * (q.2 : G))
          = (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by group
        _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by rw [hcomm]
        _ = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G)) := by group }

theorem range_prodHom (H K : Subgroup G) (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    (prodHom H K hc).range = H ⊔ K := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨⟨h, k⟩, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h.2) (Subgroup.mem_sup_right k.2)
  · refine sup_le ?_ ?_
    · intro h hh
      exact ⟨(⟨h, hh⟩, 1), by simp [prodHom]⟩
    · intro k hk
      exact ⟨(1, ⟨k, hk⟩), by simp [prodHom]⟩

theorem mem_sup_prod {H K : Subgroup G} (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G}
    (hx : x ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  rw [← range_prodHom H K hc] at hx
  obtain ⟨⟨h, k⟩, hp⟩ := hx
  exact ⟨h, h.2, k, k.2, hp.symm⟩

theorem card_sup_mul_card_inf (H K : Subgroup G) (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card ↥H * Nat.card ↥K := by
  have hker : Nat.card (prodHom H K hc).ker = Nat.card ↥(H ⊓ K) := by
    have hK : ∀ p : (prodHom H K hc).ker, (p.1.1 : G) ∈ K := by
      intro p
      have hp : (p.1.1 : G) * (p.1.2 : G) = 1 := p.2
      have : (p.1.1 : G) = (p.1.2 : G)⁻¹ := eq_inv_of_mul_eq_one_left hp
      rw [this]
      exact K.inv_mem p.1.2.2
    refine Nat.card_congr
      { toFun := fun p => ⟨(p.1.1 : G), Subgroup.mem_inf.2 ⟨p.1.1.2, hK p⟩⟩
        invFun := fun z => ⟨(⟨(z : G), (Subgroup.mem_inf.1 z.2).1⟩,
          ⟨(z : G)⁻¹, K.inv_mem (Subgroup.mem_inf.1 z.2).2⟩), MonoidHom.mem_ker.2 (by simp [prodHom])⟩
        left_inv := fun p => ?_
        right_inv := fun z => Subtype.ext rfl }
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      have hp : (p.1.1 : G) * (p.1.2 : G) = 1 := p.2
      show ((p.1.1 : G))⁻¹ = (p.1.2 : G)
      exact inv_eq_of_mul_eq_one_right hp
  have h1 := Subgroup.card_mul_index (prodHom H K hc).ker
  rw [Subgroup.index_ker, range_prodHom, hker, Nat.card_prod] at h1
  rw [← h1]
  ring

end Product




section Extraspecial

variable {G : Type} [Group G] [Finite G]

@[expose] def IsExtraspecialFive (F : Subgroup G) (a : G) : Prop :=
  Nat.card F = 3 ^ 5 ∧ (∀ x ∈ F, x ^ 3 = 1) ∧ a ≠ 1 ∧
    centerOf F = Subgroup.zpowers a ∧ ⁅F, F⁆ = Subgroup.zpowers a

theorem mem_centerOf_iff (H : Subgroup G) (z : G) :
    z ∈ centerOf H ↔ z ∈ H ∧ ∀ h ∈ H, h * z = z * h := by
  unfold centerOf
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
    refine ⟨x.2, fun h hh => ?_⟩
    have := congrArg Subtype.val ((Subgroup.mem_center_iff.1 hx) ⟨h, hh⟩)
    simpa using this
  · rintro ⟨hz, hcomm⟩
    refine Subgroup.mem_map.2 ⟨⟨z, hz⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simpa using (hcomm g.1 g.2)

theorem comm_zpowers_mem {a x y : G} (hx : x ∈ Subgroup.zpowers a) (hy : y ∈ Subgroup.zpowers a) :
    x * y = y * x := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  exact Commute.zpow_zpow_self a m n

theorem card_zpowers_three {a : G} (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1) :
    Nat.card ↥(Subgroup.zpowers a) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime ha3 ha1

theorem central_of_mem {F : Subgroup G} {a : G} (hF : IsExtraspecialFive F a) {z f : G}
    (hz : z ∈ Subgroup.zpowers a) (hf : f ∈ F) : f * z = z * f := by
  obtain ⟨-, -, -, hcen, -⟩ := hF
  have : z ∈ centerOf F := by rw [hcen]; exact hz
  exact ((mem_centerOf_iff F z).1 this).2 f hf

theorem zpowers_le_of_ext {F : Subgroup G} {a : G} (hF : IsExtraspecialFive F a) :
    Subgroup.zpowers a ≤ F := by
  obtain ⟨-, -, -, hcen, -⟩ := hF
  intro z hz
  have : z ∈ centerOf F := by rw [hcen]; exact hz
  exact ((mem_centerOf_iff F z).1 this).1

theorem comm_mem {F : Subgroup G} {a : G} (hF : IsExtraspecialFive F a) {e f : G}
    (he : e ∈ F) (hf : f ∈ F) : e⁻¹ * f⁻¹ * e * f ∈ Subgroup.zpowers a := by
  obtain ⟨-, -, -, -, hder⟩ := hF
  rw [← hder]
  have := Subgroup.commutator_mem_commutator (F.inv_mem he) (F.inv_mem hf)
  rw [commutatorElement_def] at this
  simpa using this

noncomputable def commHom {F : Subgroup G} {a : G} (hF : IsExtraspecialFive F a) {w : G}
    (hw : w ∈ F) : F →* Subgroup.zpowers a where
  toFun f := ⟨w⁻¹ * (f : G)⁻¹ * w * (f : G), comm_mem hF hw f.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' f g := by
    apply Subtype.ext
    have hc : w⁻¹ * (f : G)⁻¹ * w * (f : G) ∈ Subgroup.zpowers a := comm_mem hF hw f.2
    have hd : w⁻¹ * (g : G)⁻¹ * w * (g : G) ∈ Subgroup.zpowers a := comm_mem hF hw g.2
    have hcd : (w⁻¹ * (g : G)⁻¹ * w * (g : G)) * (w⁻¹ * (f : G)⁻¹ * w * (f : G)) =
        (w⁻¹ * (f : G)⁻¹ * w * (f : G)) * (w⁻¹ * (g : G)⁻¹ * w * (g : G)) :=
      comm_zpowers_mem hd hc
    have hcg : (w⁻¹ * (f : G)⁻¹ * w * (f : G)) * (g : G) =
        (g : G) * (w⁻¹ * (f : G)⁻¹ * w * (f : G)) := (central_of_mem hF hc g.2).symm
    have hfw : (f : G)⁻¹ * w * (f : G) = w * (w⁻¹ * (f : G)⁻¹ * w * (f : G)) := by group
    simp only [Subgroup.coe_mul, Subgroup.coe_mk]
    calc w⁻¹ * ((f : G) * (g : G))⁻¹ * w * ((f : G) * (g : G))
        = (w⁻¹ * (g : G)⁻¹ * ((f : G)⁻¹ * w * (f : G)) * (g : G)) := by group
      _ = (w⁻¹ * (g : G)⁻¹ * (w * (w⁻¹ * (f : G)⁻¹ * w * (f : G))) * (g : G)) := by rw [hfw]
      _ = (w⁻¹ * (g : G)⁻¹ * w) * ((w⁻¹ * (f : G)⁻¹ * w * (f : G)) * (g : G)) := by group
      _ = (w⁻¹ * (g : G)⁻¹ * w) * ((g : G) * (w⁻¹ * (f : G)⁻¹ * w * (f : G))) := by rw [hcg]
      _ = (w⁻¹ * (g : G)⁻¹ * w * (g : G)) * (w⁻¹ * (f : G)⁻¹ * w * (f : G)) := by group
      _ = (w⁻¹ * (f : G)⁻¹ * w * (f : G)) * (w⁻¹ * (g : G)⁻¹ * w * (g : G)) := hcd

theorem mul_comm_of_comm_eq_one {w h : G} (this : w⁻¹ * h⁻¹ * w * h = 1) : w * h = h * w := by
  have hkey : h⁻¹ * w * h = w := by
    calc h⁻¹ * w * h = w * (w⁻¹ * h⁻¹ * w * h) := by group
      _ = w := by rw [this, mul_one]
  calc w * h = h * (h⁻¹ * w * h) := by group
    _ = h * w := by rw [hkey]

theorem card_centralizer_inf {F : Subgroup G} {a : G} (hF : IsExtraspecialFive F a) {e : G}
    (he : e ∈ F) (he' : e ∉ Subgroup.zpowers a) :
    Nat.card ↥(F ⊓ Subgroup.centralizer ({e} : Set G)) = 81 := by
  obtain ⟨hcard, hexp, ha1, hcenF, -⟩ := id hF
  have ha3 : a ^ 3 = 1 := hexp a (zpowers_le_of_ext hF (Subgroup.mem_zpowers a))
  set φ := commHom hF he with hφ
  have hne : ∃ f : F, φ f ≠ 1 := by
    by_contra hall
    push Not at hall
    apply he'
    rw [← hcenF, mem_centerOf_iff]
    refine ⟨he, fun h hh => ?_⟩
    have hv : e⁻¹ * h⁻¹ * e * h = 1 := congrArg Subtype.val (hall ⟨h, hh⟩)
    exact (mul_comm_of_comm_eq_one hv).symm
  obtain ⟨f0, hf0⟩ := hne
  have hrange : Nat.card ↥φ.range = 3 := by
    have hdvd : Nat.card ↥φ.range ∣ 3 := by
      have := Subgroup.card_subgroup_dvd_card φ.range
      rwa [card_zpowers_three ha1 ha3] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
    · exfalso
      have hbot : φ.range = ⊥ := (Subgroup.eq_bot_iff_card φ.range).2 h1
      apply hf0
      have hmem : φ f0 ∈ φ.range := MonoidHom.mem_range.2 ⟨f0, rfl⟩
      rw [hbot] at hmem
      exact (Subgroup.mem_bot.1 hmem)
    · exact h1
  have hker : Nat.card φ.ker = 81 := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hrange, hcard] at h1
    omega
  rw [← hker]
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨(x.1 : G), (Subgroup.mem_inf.1 x.2).1⟩, ?_⟩
      invFun := fun y => ⟨(y.1 : G), Subgroup.mem_inf.2 ⟨y.1.2, ?_⟩⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => Subtype.ext (Subtype.ext rfl) }
  · rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show e⁻¹ * (x.1 : G)⁻¹ * e * (x.1 : G) = 1
    have hy : e * (x.1 : G) = (x.1 : G) * e :=
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 x.2).2 e (Set.mem_singleton e)
    calc e⁻¹ * (x.1 : G)⁻¹ * e * (x.1 : G) = e⁻¹ * (x.1 : G)⁻¹ * (e * (x.1 : G)) := by group
      _ = e⁻¹ * (x.1 : G)⁻¹ * ((x.1 : G) * e) := by rw [hy]
      _ = 1 := by group
  · have hv : e⁻¹ * (y.1.1 : G)⁻¹ * e * (y.1.1 : G) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.1 y.2)
    exact Subgroup.mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact mul_comm_of_comm_eq_one hv)

end Extraspecial

section Structure

variable {G : Type} [Group G] [Finite G]

theorem pow_three_of_mem_zpowers {a x : G} (ha3 : a ^ 3 = 1) (hx : x ∈ Subgroup.zpowers a) :
    x ^ 3 = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]

theorem card_zpowers_of_ne_one {a x : G} (ha3 : a ^ 3 = 1) (hx : x ∈ Subgroup.zpowers a)
    (hx1 : x ≠ 1) : Nat.card ↥(Subgroup.zpowers x) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (pow_three_of_mem_zpowers ha3 hx) hx1

theorem zpowers_eq_of_mem {a x : G} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hx : x ∈ Subgroup.zpowers a)
    (hx1 : x ≠ 1) : Subgroup.zpowers x = Subgroup.zpowers a := by
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers a := Subgroup.zpowers_le.2 hx
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [card_zpowers_three ha1 ha3, card_zpowers_of_ne_one ha3 hx hx1])

theorem exists_zpow_eq_of_mem {a x y : G} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hx : x ∈ Subgroup.zpowers a) (hy : y ∈ Subgroup.zpowers a) (hx1 : x ≠ 1) :
    ∃ k : ℤ, x ^ k = y := by
  have h := zpowers_eq_of_mem ha3 ha1 hx hx1
  have hy' : y ∈ Subgroup.zpowers x := by rw [h]; exact hy
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy'
  exact ⟨k, hk⟩

theorem card_eq_of_between {F C Fe : Subgroup G} (hF243 : Nat.card ↥F = 243) (hFe : Fe ≤ C)
    (hCF : C ≤ F) (h81 : Nat.card ↥Fe = 81) (hne : C ≠ Fe) : C = F := by
  have hdvd1 : Nat.card ↥C ∣ 243 := by
    have := Subgroup.card_subgroup_dvd_card (C.subgroupOf F)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCF).toEquiv, hF243] at this
    exact this
  have hdvd2 : 81 ∣ Nat.card ↥C := by
    have := Subgroup.card_dvd_of_le hFe
    rwa [h81] at this
  have hdiv : Nat.divisors 243 = {1, 3, 9, 27, 81, 243} := by decide
  have hmem := Nat.mem_divisors.2 ⟨hdvd1, by norm_num⟩
  rw [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hC : Nat.card ↥C = 81 ∨ Nat.card ↥C = 243 := by
    rcases hmem with h | h | h | h | h | h <;> omega
  rcases hC with h81' | h243'
  · exfalso
    apply hne
    exact (Subgroup.eq_of_le_of_card_ge hFe (by rw [h81', h81])).symm
  · exact Subgroup.eq_of_le_of_card_ge hCF (by rw [h243', hF243])

theorem zpowers_sup_card_le {F : Subgroup G} {a : G} (hF : IsExtraspecialFive F a) {e : G}
    (he : e ∈ F) (he' : e ∉ Subgroup.zpowers a) :
    Nat.card ↥(Subgroup.zpowers e ⊔ Subgroup.zpowers a) ≤ 9 := by
  obtain ⟨hcard, hexp, ha1, hcenF, hder⟩ := id hF
  have ha3 : a ^ 3 = 1 := hexp a (zpowers_le_of_ext hF (Subgroup.mem_zpowers a))
  have hea : Commute e a := central_of_mem hF (Subgroup.mem_zpowers a) he
  have hc : ∀ h ∈ Subgroup.zpowers e, ∀ k ∈ Subgroup.zpowers a, h * k = k * h := by
    intro h hh k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact ((hea.zpow_left m).zpow_right n : Commute (e ^ m) (a ^ n))
  have hprod := card_sup_mul_card_inf (Subgroup.zpowers e) (Subgroup.zpowers a) hc
  have hpos : 0 < Nat.card ↥(Subgroup.zpowers e ⊓ Subgroup.zpowers a) := Nat.card_pos
  have he3 : e ^ 3 = 1 := hexp e he
  have he1 : e ≠ 1 := fun h => he' (h ▸ Subgroup.one_mem _)
  have hce : Nat.card ↥(Subgroup.zpowers e) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime he3 he1
  rw [hce, card_zpowers_three ha1 ha3] at hprod
  nlinarith

theorem center_le_sup {F : Subgroup G} {a : G} (hF : IsExtraspecialFive F a) {e : G} (he : e ∈ F)
    (he' : e ∉ Subgroup.zpowers a) {y : G} (hy : y ∈ F ⊓ Subgroup.centralizer ({e} : Set G))
    (hcomm : ∀ f ∈ F ⊓ Subgroup.centralizer ({e} : Set G), f * y = y * f) :
    y ∈ Subgroup.zpowers e ⊔ Subgroup.zpowers a := by
  obtain ⟨hcard, hexp, ha1, hcenF, hder⟩ := id hF
  have ha3 : a ^ 3 = 1 := hexp a (zpowers_le_of_ext hF (Subgroup.mem_zpowers a))
  have hFe81 := card_centralizer_inf hF he he'
  set Fe := F ⊓ Subgroup.centralizer ({e} : Set G) with hFe
  by_cases hya : y ∈ Subgroup.zpowers a
  · exact Subgroup.mem_sup_right hya
  have hyF : y ∈ F := (Subgroup.mem_inf.1 hy).1
  have hCy : F ⊓ Subgroup.centralizer ({y} : Set G) = Fe := by
    by_contra hne
    have hle : Fe ≤ F ⊓ Subgroup.centralizer ({y} : Set G) := by
      intro f hf
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hf).1, ?_⟩
      refine Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hcomm f hf).symm
    have htop := card_eq_of_between hcard hle inf_le_left hFe81 hne
    apply hya
    rw [← hcenF, mem_centerOf_iff]
    refine ⟨hyF, fun f hf => ?_⟩
    have hf' : f ∈ F ⊓ Subgroup.centralizer ({y} : Set G) := by rw [htop]; exact hf
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hf').2 y (Set.mem_singleton y)).symm
  obtain ⟨f0, hf0F, hf0⟩ : ∃ f0 ∈ F, f0 ∉ Fe := by
    by_contra hall
    push Not at hall
    have heq : F = Fe := Subgroup.eq_of_le_of_card_ge hall (by rw [hFe81, hcard]; norm_num)
    have h2 := congrArg (fun H : Subgroup G => Nat.card ↥H) heq
    simp only [hcard, hFe81] at h2
    norm_num at h2
  have hA1 : f0⁻¹ * e⁻¹ * f0 * e ≠ 1 := fun h => hf0 (Subgroup.mem_inf.2 ⟨hf0F,
    Subgroup.mem_centralizer_iff.2 (fun k hk => by
      rw [Set.mem_singleton_iff] at hk
      subst hk
      exact (mul_comm_of_comm_eq_one h).symm)⟩)
  have hB1 : f0⁻¹ * y⁻¹ * f0 * y ≠ 1 := fun h => hf0 (hCy ▸ Subgroup.mem_inf.2 ⟨hf0F,
    Subgroup.mem_centralizer_iff.2 (fun k hk => by
      rw [Set.mem_singleton_iff] at hk
      subst hk
      exact (mul_comm_of_comm_eq_one h).symm)⟩)
  have hA1mem : f0⁻¹ * e⁻¹ * f0 * e ∈ Subgroup.zpowers a := comm_mem hF hf0F he
  have hB1mem : f0⁻¹ * y⁻¹ * f0 * y ∈ Subgroup.zpowers a := comm_mem hF hf0F hyF
  obtain ⟨k, hk⟩ := exists_zpow_eq_of_mem ha3 ha1 hA1mem hB1mem hA1
  set ψ := commHom hF hf0F with hψ
  have hz1 : f0⁻¹ * (y * e ^ (-k))⁻¹ * f0 * (y * e ^ (-k)) = 1 := by
    have hcoe : ((ψ (⟨y, hyF⟩ * ⟨e, he⟩ ^ (-k)) : Subgroup.zpowers a) : G) = 1 := by
      rw [map_mul, map_zpow, Subgroup.coe_mul, Subgroup.coe_zpow]
      have hB : ((ψ ⟨y, hyF⟩ : Subgroup.zpowers a) : G) = f0⁻¹ * y⁻¹ * f0 * y := rfl
      have hA : ((ψ ⟨e, he⟩ : Subgroup.zpowers a) : G) = f0⁻¹ * e⁻¹ * f0 * e := rfl
      rw [hB, hA, ← hk, ← zpow_add, add_neg_cancel, zpow_zero]
    exact hcoe
  set z := y * e ^ (-k) with hz
  have hzF : z ∈ F := F.mul_mem hyF (F.zpow_mem he _)
  have hz2 : f0 * z = z * f0 := mul_comm_of_comm_eq_one hz1
  have hzFe : ∀ f ∈ Fe, f * z = z * f := by
    intro f hf
    have hfy : f * y = y * f := hcomm f hf
    have hef : e * f = f * e := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hf).2 e
      (Set.mem_singleton e)
    have hfe : e ^ (-k) * f = f * e ^ (-k) := ((show Commute e f from hef).zpow_left (-k))
    calc f * z = (f * y) * e ^ (-k) := by rw [hz, mul_assoc]
      _ = (y * f) * e ^ (-k) := by rw [hfy]
      _ = y * (f * e ^ (-k)) := by rw [mul_assoc]
      _ = y * (e ^ (-k) * f) := by rw [← hfe]
      _ = z * f := by rw [hz, mul_assoc]
  have hCz : F ⊓ Subgroup.centralizer ({z} : Set G) = F := by
    have hle : Fe ≤ F ⊓ Subgroup.centralizer ({z} : Set G) := by
      intro f hf
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hf).1, ?_⟩
      refine Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hzFe f hf).symm
    have hf0C : f0 ∈ F ⊓ Subgroup.centralizer ({z} : Set G) := by
      refine Subgroup.mem_inf.2 ⟨hf0F, Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)⟩
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hz2.symm
    have hne : F ⊓ Subgroup.centralizer ({z} : Set G) ≠ Fe := fun h => hf0 (h ▸ hf0C)
    exact card_eq_of_between hcard hle inf_le_left hFe81 hne
  have hzA : z ∈ Subgroup.zpowers a := by
    rw [← hcenF, mem_centerOf_iff]
    refine ⟨hzF, fun h hh => ?_⟩
    have hh' : h ∈ F ⊓ Subgroup.centralizer ({z} : Set G) := by rw [hCz]; exact hh
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hh').2 z (Set.mem_singleton z)).symm
  have hy_eq : y = z * e ^ k := by rw [hz, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  rw [hy_eq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hzA)
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩))

theorem a_mem_commutator_inf {F : Subgroup G} {a : G} (hF : IsExtraspecialFive F a) {e : G}
    (he : e ∈ F) (he' : e ∉ Subgroup.zpowers a) :
    a ∈ ⁅F ⊓ Subgroup.centralizer ({e} : Set G), F ⊓ Subgroup.centralizer ({e} : Set G)⁆ := by
  obtain ⟨hcard, hexp, ha1, hcenF, hder⟩ := id hF
  have ha3 : a ^ 3 = 1 := hexp a (zpowers_le_of_ext hF (Subgroup.mem_zpowers a))
  have hFe81 := card_centralizer_inf hF he he'
  set Fe := F ⊓ Subgroup.centralizer ({e} : Set G) with hFe
  have hnc : ∃ x ∈ Fe, ∃ y ∈ Fe, x * y ≠ y * x := by
    by_contra hall
    push Not at hall
    have hsub : Fe ≤ Subgroup.zpowers e ⊔ Subgroup.zpowers a := fun y hy =>
      center_le_sup hF he he' hy (fun f hf => hall f hf y hy)
    have hle := Subgroup.card_le_of_le hsub
    have h9 := zpowers_sup_card_le hF he he'
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  have hcomm_mem : x * y * x⁻¹ * y⁻¹ ∈ ⁅Fe, Fe⁆ := by
    rw [← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator hx hy
  have hcF : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers a := by
    rw [← hder]
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_inf.1 hx).1 (Subgroup.mem_inf.1 hy).1
    rw [commutatorElement_def] at this
    exact this
  have hc1 : x * y * x⁻¹ * y⁻¹ ≠ 1 := by
    intro h
    apply hxy
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h, one_mul]
  have hz := zpowers_eq_of_mem ha3 ha1 hcF hc1
  have ha_mem : a ∈ Subgroup.zpowers (x * y * x⁻¹ * y⁻¹) := by
    rw [hz]
    exact Subgroup.mem_zpowers a
  exact (Subgroup.zpowers_le.2 hcomm_mem) ha_mem

end Structure

section Elementary

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_of_le {H K : Subgroup G} (hH : CFSG.Open.IsElemAbelian 3 H) (hKH : K ≤ H) :
    CFSG.Open.IsElemAbelian 3 K := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => hH.2 x (hKH hx)⟩
  have h := hH.1.is_comm.comm ⟨x.1, hKH x.2⟩ ⟨y.1, hKH y.2⟩
  have h' : (x : G) * (y : G) = (y : G) * (x : G) := congrArg Subtype.val h
  exact Subtype.ext h'

theorem isPGroup_of_elemAbelian {K : Subgroup G} (hK : CFSG.Open.IsElemAbelian 3 K) :
    IsPGroup 3 ↥K := fun g => ⟨1, Subtype.ext (by simpa using hK.2 g.1 g.2)⟩

theorem isElemAbelian_sup {H K : Subgroup G} (hH : CFSG.Open.IsElemAbelian 3 H)
    (hK : CFSG.Open.IsElemAbelian 3 K) (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    CFSG.Open.IsElemAbelian 3 (H ⊔ K) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨h1, hh1, k1, hk1, hx1⟩ := mem_sup_prod hc x.2
    obtain ⟨h2, hh2, k2, hk2, hy2⟩ := mem_sup_prod hc y.2
    have e1 : h1 * h2 = h2 * h1 := hH.1.is_comm.comm ⟨h1, hh1⟩ ⟨h2, hh2⟩ |> congrArg Subtype.val
    have e2 : k1 * k2 = k2 * k1 := hK.1.is_comm.comm ⟨k1, hk1⟩ ⟨k2, hk2⟩ |> congrArg Subtype.val
    have e3 : k1 * h2 = h2 * k1 := (hc h2 hh2 k1 hk1).symm
    have e4 : k2 * h1 = h1 * k2 := (hc h1 hh1 k2 hk2).symm
    apply Subtype.ext
    show (x.1 : G) * (y.1 : G) = (y.1 : G) * (x.1 : G)
    rw [hx1, hy2]
    calc h1 * k1 * (h2 * k2) = h1 * (k1 * h2) * k2 := by group
      _ = h1 * (h2 * k1) * k2 := by rw [e3]
      _ = (h1 * h2) * (k1 * k2) := by group
      _ = (h2 * h1) * (k2 * k1) := by rw [e1, e2]
      _ = h2 * (h1 * k2) * k1 := by group
      _ = h2 * (k2 * h1) * k1 := by rw [e4]
      _ = h2 * k2 * (h1 * k1) := by group
  · obtain ⟨h, hh, k, hk, hxk⟩ := mem_sup_prod hc hx
    rw [hxk, Commute.mul_pow (show Commute h k from hc h hh k hk) 3, hH.2 h hh, hK.2 k hk, one_mul]

end Elementary

section NoE4

variable {G : Type} [Group G] [Finite G]

theorem no_E4_contains {m : ℕ} {B M E A : Subgroup G} {a : G}
    (h : Sec10Fails G m 3 B M) (hEA : IsDDpStar 3 M E A)
    (h3 : CFSG.Open.pRank 3 E = 3 ∨ CFSG.Open.pRank 3 A = 3)
    (hnot : ∀ A1 : Subgroup G, inD 3 M A1 → a ∉ A1) (ha1 : a ≠ 1)
    {W : Subgroup G} (hWM : W ≤ M) (hW : CFSG.Open.IsElemAbelian 3 W) (ha : a ∈ W)
    (hW81 : 81 ≤ Nat.card ↥W) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpW := isPGroup_of_elemAbelian hW
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card.1 hpW)
  have hn4 : 4 ≤ n := by
    by_contra hlt
    have : 3 ^ n ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have ha3 : a ^ 3 = 1 := hW.2 a ha
  have hdvdW : 3 ^ 4 ∣ Nat.card ↥W := by
    rw [hn]
    exact Nat.pow_dvd_pow 3 hn4
  have hdvdZ : Nat.card ↥(Subgroup.zpowers a) ∣ 3 ^ 4 := by
    rw [card_zpowers_three ha1 ha3]
    norm_num
  obtain ⟨V, hVcard, haV, hVW⟩ := Sylow.exists_subgroup_card_pow_prime_le_le
    (p := 3) Nat.prime_three (n := 4) hdvdZ hdvdW (Subgroup.zpowers_le.2 ha)
  have hVel : CFSG.Open.IsElemAbelian 3 V := isElemAbelian_of_le hW hVW
  have hVM : V ≤ M := le_trans hVW hWM
  obtain ⟨R, hR, hVR⟩ := Lemma113b.exists_sylowIn_above' hVM (isPGroup_of_elemAbelian hVel)
  have hEk : IsEkIn 3 4 R V := ⟨hVR, hVel, by rw [hVcard]⟩
  obtain ⟨-, -, A1, hA1, hVA1⟩ := (lemma104_v_holds h hEA h3 hR).1 V hEk
  exact hnot A1 hA1 (hVA1 (haV (Subgroup.mem_zpowers a)))

theorem exists_conj_le_sylow {m : ℕ} {B M E A : Subgroup G} (h : Sec10Fails G m 3 B M)
    (hEA : IsDDpStar 3 M E A) {R : Subgroup G} (hR : IsSylowIn 3 M R) :
    ∃ B' : Subgroup G, inD 3 M B' ∧ B' ≤ R ∧ Nat.card ↥B' = Nat.card ↥B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBD : inD 3 M B := lemma101_ii_holds h
  have hBM : B ≤ M := hBD.1.1.1
  obtain ⟨x, hx, S, hSp, hSM, hRS, hBS⟩ := exists_conj_le_pGroup' (p := 3) (K := M) (X := R)
    (Y := B) hR.1 hR.2.1 hBM (isPGroup_of_elemAbelian hBD.1.1.2.1)
  have hSR : S = R := hR.2.2 S hSM hSp hRS
  refine ⟨GLBConj x B, ?_, hSR ▸ hBS, ?_⟩
  · exact (lemma101_i_holds h hx hBD hEA.1.2.1).1
  · unfold GLBConj
    rw [Subgroup.card_map_of_injective]
    exact (MulAut.conj x⁻¹).injective

end NoE4

section Sylow3

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_of_exponent3 {K : Subgroup G} (hK : ∀ x ∈ K, x ^ 3 = 1) : IsPGroup 3 ↥K :=
  fun g => ⟨1, Subtype.ext (by simpa using hK g.1 g.2)⟩

theorem le_centralizer_of_comm {H K : Subgroup G} (h : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) :
    H ≤ Subgroup.centralizer (K : Set G) := by
  intro x hx
  exact Subgroup.mem_centralizer_iff.2 (fun y hy => (h x hx y hy).symm)

theorem comm_of_le_centralizer {H K : Subgroup G} (h : H ≤ Subgroup.centralizer (K : Set G)) :
    ∀ x ∈ H, ∀ y ∈ K, x * y = y * x := by
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 (h hx) y hy).symm

theorem exists_order_three_in {P : Subgroup G} (hP : IsPGroup 3 ↥P) {z : G} (hz : z ∈ P)
    (hz1 : z ≠ 1) : ∃ w ∈ Subgroup.zpowers z, w ≠ 1 ∧ w ^ 3 = 1 := by
  have hex : ∃ k : ℕ, z ^ (3 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hP ⟨z, hz⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  classical
  have hk : z ^ (3 ^ Nat.find hex) = 1 := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hk
    exact hz1 hk
  refine ⟨z ^ (3 ^ (Nat.find hex - 1)), Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _, ?_, ?_⟩
  · intro h1
    exact Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega) h1
  · rw [← pow_mul, ← pow_succ]
    have : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [this]
    exact hk

theorem inf_zpowers_trivial {V : Subgroup G} {u : G} (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1)
    (huV : u ∉ V) : Nat.card ↥(V ⊓ Subgroup.zpowers u) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : Nat.card ↥(V ⊓ Subgroup.zpowers u) ∣ 3 := by
    have := Subgroup.card_subgroup_dvd_card ((V ⊓ Subgroup.zpowers u).subgroupOf (Subgroup.zpowers u))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv,
      card_zpowers_of_ne_one hu3 (Subgroup.mem_zpowers u) hu1] at this
    exact this
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
  · exact h1
  · exfalso
    have heq : V ⊓ Subgroup.zpowers u = Subgroup.zpowers u :=
      Subgroup.eq_of_le_of_card_ge inf_le_right
        (by rw [h1, card_zpowers_of_ne_one hu3 (Subgroup.mem_zpowers u) hu1])
    apply huV
    have : u ∈ V ⊓ Subgroup.zpowers u := by rw [heq]; exact Subgroup.mem_zpowers u
    exact (Subgroup.mem_inf.1 this).1

theorem conj_mem_of_normal {R U : Subgroup G} (hUR : U ≤ R) (hn : (U.subgroupOf R).Normal)
    {r : G} (hr : r ∈ R) {u : G} (hu : u ∈ U) : r * u * r⁻¹ ∈ U := by
  have := hn.conj_mem ⟨u, hUR hu⟩ (Subgroup.mem_subgroupOf.2 hu) ⟨r, hr⟩
  exact Subgroup.mem_subgroupOf.1 this

theorem le_normalizer_of_normal {R U : Subgroup G} (hUR : U ≤ R) (hn : (U.subgroupOf R).Normal) :
    R ≤ Subgroup.normalizer (U : Set G) := by
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact conj_mem_of_normal hUR hn hr hu
  · intro hu
    have h1 := conj_mem_of_normal hUR hn (R.inv_mem hr) hu
    have e : r⁻¹ * (r * u * r⁻¹) * r⁻¹⁻¹ = u := by group
    rw [e] at h1
    exact h1

end Sylow3

section ConjSylow

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_gLBConj {H : Subgroup G} (hH : IsPGroup 3 ↥H) (y : G) :
    IsPGroup 3 ↥(GLBConj y H) := by
  intro g
  obtain ⟨k, hk⟩ := hH ⟨y * g.1 * y⁻¹, (mem_gLBConj).1 g.2⟩
  refine ⟨k, Subtype.ext ?_⟩
  have hk' : y * (g.1 ^ (3 ^ k)) * y⁻¹ = 1 := by
    rw [← conj_pow]
    simpa using congrArg Subtype.val hk
  simp only [OneMemClass.coe_one]
  calc g.1 ^ (3 ^ k) = y⁻¹ * (y * g.1 ^ (3 ^ k) * y⁻¹) * y := by group
    _ = 1 := by rw [hk']; group

theorem isSylowIn_conj {M R : Subgroup G} (hR : IsSylowIn 3 M R) {x : G} (hx : x ∈ M) :
    IsSylowIn 3 M (GLBConj x R) := by
  have hxinv : x⁻¹ ∈ M := M.inv_mem hx
  have hsub : GLBConj x R ≤ M := by
    intro y hy
    rw [mem_gLBConj] at hy
    have h1 := hR.1 hy
    have hy' : y = x⁻¹ * (x * y * x⁻¹) * x := by group
    rw [hy']
    exact M.mul_mem (M.mul_mem hxinv h1) hx
  refine ⟨hsub, isPGroup_gLBConj hR.2.1 x, ?_⟩
  intro T hTM hTp hle
  set T' := GLBConj x⁻¹ T with hT'
  have hT'M : T' ≤ M := by
    intro z hz
    rw [hT', mem_gLBConj] at hz
    have hz' : z = x * (x⁻¹ * z * x⁻¹⁻¹) * x⁻¹ := by group
    rw [hz']
    exact M.mul_mem (M.mul_mem hx (hTM hz)) hxinv
  have hT'p : IsPGroup 3 ↥T' := isPGroup_gLBConj hTp x⁻¹
  have hRT' : R ≤ T' := by
    intro r hr
    rw [hT', mem_gLBConj]
    have hmem : x⁻¹ * r * x⁻¹⁻¹ ∈ GLBConj x R := by
      rw [mem_gLBConj]
      have e : x * (x⁻¹ * r * x⁻¹⁻¹) * x⁻¹ = r := by group
      rw [e]
      exact hr
    exact hle hmem
  have hRT'eq : T' = R := hR.2.2 T' hT'M hT'p hRT'
  have hiff : ∀ z, z ∈ R ↔ z ∈ T' := fun z => by rw [hRT'eq]
  have hk : ∀ z, z ∈ T' ↔ x⁻¹ * z * x⁻¹⁻¹ ∈ T := fun z => by rw [hT', mem_gLBConj]
  ext y
  rw [mem_gLBConj]
  have e : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
  rw [hiff, hk, e]

end ConjSylow

section Setup

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_centralizing {M R0 : Subgroup G} (hR0 : IsSylowIn 3 M R0) {e : G}
    (he : e ∈ centerOf R0) (hCM : Cg e ≤ M) {F' : Subgroup G} (hF'C : F' ≤ Cg e)
    (hF'p : IsPGroup 3 ↥F') (heF' : e ∈ F') :
    ∃ R' : Subgroup G, IsSylowIn 3 M R' ∧ F' ≤ R' ∧ e ∈ centerOf R' := by
  have hR0C : R0 ≤ Cg e := by
    intro r hr
    refine Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (((mem_centerOf_iff R0 h).1 he).2 r hr).symm
  have hR0S : IsSylowIn 3 (Cg e) R0 :=
    ⟨hR0C, hR0.2.1, fun T hTC hTp hle => hR0.2.2 T (hTC.trans hCM) hTp hle⟩
  obtain ⟨R', hR'S, hF'R'⟩ := Lemma113b.exists_sylowIn_above' hF'C hF'p
  obtain ⟨x, hxC, S, hSp, hSC, hR'S', hRS⟩ := exists_conj_le_pGroup' (p := 3) (K := Cg e)
    (X := R') (Y := R0) hR'S.1 hR'S.2.1 hR0C hR0.2.1
  have hSeq : S = R' := hR'S.2.2 S hSC hSp hR'S'
  have hle : GLBConj x R0 ≤ R' := hSeq ▸ hRS
  have hxM : x ∈ M := hCM hxC
  have hR'M : R' ≤ M := hR'S.1.trans hCM
  have hR'eq : R' = GLBConj x R0 :=
    (isSylowIn_conj hR0 hxM).2.2 R' hR'M hR'S.2.1 hle
  have hR'Sy : IsSylowIn 3 M R' := by
    rw [hR'eq]
    exact isSylowIn_conj hR0 hxM
  refine ⟨R', hR'Sy, hF'R', ?_⟩
  refine (mem_centerOf_iff R' e).2 ⟨hF'R' heF', fun h hh => ?_⟩
  have hhC : h ∈ Cg e := hR'S.1 hh
  exact (Subgroup.mem_centralizer_iff.1 hhC e (Set.mem_singleton e)).symm

end Setup

section Helpers3

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_zpowers {x : G} (hx3 : x ^ 3 = 1) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers x) :=
  ⟨⟨⟨fun a b => Subtype.ext (comm_zpowers_mem a.2 b.2)⟩⟩, fun a ha => pow_three_of_mem_zpowers hx3 ha⟩

theorem mem_centralizer_zpowers {x y : G} (h : x * y = y * x) :
    y ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
  refine Subgroup.mem_centralizer_iff.2 (fun k hk => ?_)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  exact (show Commute x y from h).zpow_left n

end Helpers3

section Piece3

variable {G : Type} [Group G] [Finite G]

theorem piece3_contra {m : ℕ} {B M E A : Subgroup G} {a : G} (h : Sec10Fails G m 3 B M)
    (hEA : IsDDpStar 3 M E A) (hA3 : CFSG.Open.pRank 3 A = 3)
    (hnot : ∀ A1 : Subgroup G, inD 3 M A1 → a ∉ A1) (ha : a ∈ A) (ha1 : a ≠ 1)
    {F : Subgroup G} (hAF : A ≤ F) (hF : IsExtraspecialFive F a)
    (hP2 : ∀ R : Subgroup G, IsSylowIn 3 M R → E ⊔ A ≤ R →
      ∀ e ∈ omegaOne 3 (centerOf R), e ≠ 1 → Cg e ≤ M)
    (hI31 : Input31_3) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF' := hF
  obtain ⟨hcardF, hexpF, -, hcenF, hderF⟩ := hF'
  have ha3 : a ^ 3 = 1 := hexpF a (hAF ha)
  have hED : inD 3 M E := hEA.1.1
  have hEM : E ≤ M := hED.1.1.1
  have hAM : A ≤ M := hEA.1.2.1.1.1.1
  have hEAM : E ⊔ A ≤ M := sup_le hEM hAM
  have hEel : CFSG.Open.IsElemAbelian 3 E := hED.1.1.2.1
  have hAel : CFSG.Open.IsElemAbelian 3 A := hEA.1.2.1.1.1.2.1
  have haE : a ∉ E := hnot E hED
  have hSC := lemma104_ii_holds h hEA
  have hpEA : IsPGroup 3 ↥(E ⊔ A) := lemma104_i_holds h hEA
  obtain ⟨R0, hR0, hEAR0⟩ := Lemma113b.exists_sylowIn_above' hEAM hpEA
  have hER0 : E ≤ R0 := le_trans le_sup_left hEAR0
  have hAR0 : A ≤ R0 := le_trans le_sup_right hEAR0
  haveI : Nontrivial ↥R0 := ⟨⟨⟨a, hAR0 ha⟩, 1, fun h' => ha1 (congrArg Subtype.val h')⟩⟩
  haveI hcen : Nontrivial (Subgroup.center ↥R0) := IsPGroup.center_nontrivial hR0.2.1
  obtain ⟨⟨zR, hzc⟩, hz1⟩ := exists_ne (1 : Subgroup.center ↥R0)
  have hzG : zR.1 ∈ centerOf R0 := by
    refine (mem_centerOf_iff R0 zR.1).2 ⟨zR.2, fun h' hh => ?_⟩
    have := congrArg Subtype.val ((Subgroup.mem_center_iff.1 hzc) ⟨h', hh⟩)
    exact this
  have hzne : zR.1 ≠ 1 := fun h' => hz1 (Subtype.ext (Subtype.ext h'))
  obtain ⟨e, hewz, he1, he3⟩ := exists_order_three_in hR0.2.1 zR.2 hzne
  have heC : e ∈ centerOf R0 := Subgroup.zpowers_le.2 hzG hewz
  have heE : e ∈ E := by
    have hsup := isElemAbelian_sup hEel (isElemAbelian_zpowers he3)
      (fun h' hh k hk => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
        exact (show Commute h' e from ((mem_centerOf_iff R0 e).1 heC).2 h' (hER0 hh)).zpow_right n)
    have hEsup : E ⊔ Subgroup.zpowers e = E :=
      hSC.1.2.2 (E ⊔ Subgroup.zpowers e) le_top hsup le_sup_left
    have : e ∈ E ⊔ Subgroup.zpowers e := Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
    rwa [hEsup] at this
  have heA : e ∈ A := by
    have hsup := isElemAbelian_sup hAel (isElemAbelian_zpowers he3)
      (fun h' hh k hk => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
        exact (show Commute h' e from ((mem_centerOf_iff R0 e).1 heC).2 h' (hAR0 hh)).zpow_right n)
    have hAsup : A ⊔ Subgroup.zpowers e = A :=
      hSC.2.2.2 (A ⊔ Subgroup.zpowers e) le_top hsup le_sup_left
    have : e ∈ A ⊔ Subgroup.zpowers e := Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
    rwa [hAsup] at this
  have he' : e ∉ Subgroup.zpowers a := by
    intro hea
    have heq := zpowers_eq_of_mem ha3 ha1 hea he1
    apply haE
    have : a ∈ Subgroup.zpowers e := by
      rw [heq]
      exact Subgroup.mem_zpowers a
    exact (Subgroup.zpowers_le.2 heE) this
  have heF : e ∈ F := hAF heA
  have hCeM : Cg e ≤ M := hP2 R0 hR0 hEAR0 e (by
    unfold omegaOne
    exact Subgroup.subset_closure ⟨heC, he3⟩) he1
  set Fe : Subgroup G := F ⊓ Subgroup.centralizer ({e} : Set G) with hFe
  have heFe : e ∈ Fe := Subgroup.mem_inf.2 ⟨heF, Subgroup.mem_centralizer_iff.2
    (fun h' hh => by rw [Set.mem_singleton_iff] at hh; subst hh; rfl)⟩
  have hFeC : Fe ≤ Cg e := inf_le_right
  have hFep : IsPGroup 3 ↥Fe :=
    isPGroup_of_exponent3 (fun x hx => hexpF x (Subgroup.mem_inf.1 hx).1)
  have hFe81 : Nat.card ↥Fe = 81 := card_centralizer_inf hF heF he'
  obtain ⟨R', hR'M, hFeR', heR'⟩ := exists_sylow_centralizing hR0 heC hCeM hFeC hFep heFe
  obtain ⟨B', hB'D, hB'R', hB'card⟩ := exists_conj_le_sylow h hEA hR'M
  have hB'el : CFSG.Open.IsElemAbelian 3 B' := hB'D.1.1.2.1
  have hBcard : Nat.card ↥B = 3 ^ m := h.standing.card_eq h.bOne
  have hm4 : 4 ≤ m := h.standing.four_le
  have hrank : m ≤ CFSG.Open.pRank 3 R' :=
    CFSG.SectionRank.le_pRank (by norm_num) hB'R' hB'el (k := m) (by rw [hB'card, hBcard])
  obtain ⟨U, hUI, hUn⟩ := hI31 G 3 Nat.prime_three (by norm_num) R' hR'M.2.1 2 (by norm_num)
    (by omega)
  have hU9 : Nat.card ↥U = 9 := by rw [hUI.2.2]; norm_num
  have hUR' : U ≤ R' := hUI.1
  have hUel : CFSG.Open.IsElemAbelian 3 U := hUI.2.1
  have hR'nor : R' ≤ Subgroup.normalizer (U : Set G) := le_normalizer_of_normal hUR' hUn
  have hFenor : Fe ≤ Subgroup.normalizer (U : Set G) := le_trans hFeR' hR'nor
  have hlinesFe := lines_card_le Fe U hFep hU9 hFenor
  have hK1 : 27 ≤ Nat.card ↥(Fe ⊓ Subgroup.centralizer (U : Set G)) := by omega
  have haK1 : a ∈ Fe ⊓ Subgroup.centralizer (U : Set G) :=
    lines_comm Fe U hFep hU9 hFenor (a_mem_commutator_inf hF heF he')
  have heK1 : e ∈ Fe ⊓ Subgroup.centralizer (U : Set G) := Subgroup.mem_inf.2 ⟨heFe,
    Subgroup.mem_centralizer_iff.2 (fun u hu => ((mem_centerOf_iff R' e).1 heR').2 u (hUR' hu))⟩
  obtain ⟨x, hxK1, hxsup⟩ : ∃ x ∈ Fe ⊓ Subgroup.centralizer (U : Set G),
      x ∉ Subgroup.zpowers e ⊔ Subgroup.zpowers a := by
    by_contra hall
    push Not at hall
    have hle := Subgroup.card_le_of_le (show Fe ⊓ Subgroup.centralizer (U : Set G) ≤
      Subgroup.zpowers e ⊔ Subgroup.zpowers a from fun y hy => hall y hy)
    have h9 := zpowers_sup_card_le hF heF he'
    omega
  have hxFe : x ∈ Fe := (Subgroup.mem_inf.1 hxK1).1
  have hxC : x ∈ Subgroup.centralizer (U : Set G) := (Subgroup.mem_inf.1 hxK1).2
  have hxF : x ∈ F := (Subgroup.mem_inf.1 hxFe).1
  have hxe : e * x = x * e := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hxFe).2 e
    (Set.mem_singleton e)
  have hxa : x * a = a * x := central_of_mem hF (Subgroup.mem_zpowers a) hxF
  have hx3 : x ^ 3 = 1 := hexpF x hxF
  have hx1 : x ≠ 1 := fun h' => hxsup (h' ▸ Subgroup.one_mem _)
  have heC_U : e ∈ Subgroup.centralizer (U : Set G) := (Subgroup.mem_inf.1 heK1).2
  have haC_U : a ∈ Subgroup.centralizer (U : Set G) := (Subgroup.mem_inf.1 haK1).2
  have haFe : a ∈ Fe := (Subgroup.mem_inf.1 haK1).1
  have hcomm_ea : ∀ h' ∈ Subgroup.zpowers e, ∀ k ∈ Subgroup.zpowers a, h' * k = k * h' :=
    comm_of_le_centralizer (H := Subgroup.zpowers e) (K := Subgroup.zpowers a)
      (Subgroup.zpowers_le.2 (mem_centralizer_zpowers (central_of_mem hF (Subgroup.mem_zpowers a) heF).symm))
  have hUFe : U ≤ Fe := by
    by_contra hnotU
    obtain ⟨u, huU, huFe⟩ : ∃ u ∈ U, u ∉ Fe := by
      by_contra hall
      push Not at hall
      exact hnotU (fun u hu => hall u hu)
    have hu3 : u ^ 3 = 1 := hUel.2 u huU
    have hu1 : u ≠ 1 := fun h' => huFe (h' ▸ Subgroup.one_mem _)
    have hV1el := isElemAbelian_sup (isElemAbelian_zpowers he3) (isElemAbelian_zpowers ha3) hcomm_ea
    have hVc : Subgroup.zpowers e ⊔ Subgroup.zpowers a ≤
        Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
      sup_le (Subgroup.zpowers_le.2 (mem_centralizer_zpowers hxe.symm))
        (Subgroup.zpowers_le.2 (mem_centralizer_zpowers hxa))
    have hVel := isElemAbelian_sup hV1el (isElemAbelian_zpowers hx3)
      (comm_of_le_centralizer hVc)
    have hVU : Subgroup.zpowers e ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers x ≤
        Subgroup.centralizer (U : Set G) :=
      sup_le (sup_le (Subgroup.zpowers_le.2 heC_U) (Subgroup.zpowers_le.2 haC_U))
        (Subgroup.zpowers_le.2 hxC)
    have hVFe : Subgroup.zpowers e ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers x ≤ Fe :=
      sup_le (sup_le (Subgroup.zpowers_le.2 heFe) (Subgroup.zpowers_le.2 haFe))
        (Subgroup.zpowers_le.2 hxFe)
    have hVuc : Subgroup.zpowers e ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers x ≤
        Subgroup.centralizer (Subgroup.zpowers u : Set G) := by
      intro v hv
      exact mem_centralizer_zpowers (Subgroup.mem_centralizer_iff.1 (hVU hv) u huU)
    have hWel := isElemAbelian_sup hVel (isElemAbelian_zpowers hu3) (comm_of_le_centralizer hVuc)
    have hV1card : Nat.card ↥(Subgroup.zpowers e ⊔ Subgroup.zpowers a) = 9 := by
      have hp := card_sup_mul_card_inf (Subgroup.zpowers e) (Subgroup.zpowers a) hcomm_ea
      rw [card_zpowers_of_ne_one he3 (Subgroup.mem_zpowers e) he1,
        card_zpowers_three ha1 ha3] at hp
      have hi : Nat.card ↥(Subgroup.zpowers e ⊓ Subgroup.zpowers a) = 1 := by
        rw [inf_comm]
        exact inf_zpowers_trivial he3 he1 he'
      rw [hi] at hp
      omega
    have hVcard : Nat.card ↥(Subgroup.zpowers e ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers x) = 27 := by
      have hp := card_sup_mul_card_inf (Subgroup.zpowers e ⊔ Subgroup.zpowers a) (Subgroup.zpowers x)
        (comm_of_le_centralizer hVc)
      have hi : Nat.card ↥((Subgroup.zpowers e ⊔ Subgroup.zpowers a) ⊓ Subgroup.zpowers x) = 1 :=
        inf_zpowers_trivial hx3 hx1 hxsup
      rw [hi, hV1card, card_zpowers_of_ne_one hx3 (Subgroup.mem_zpowers x) hx1] at hp
      omega
    have huV : u ∉ Subgroup.zpowers e ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers x :=
      fun hu => huFe (hVFe hu)
    have hWcard : Nat.card ↥((Subgroup.zpowers e ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers x) ⊔
        Subgroup.zpowers u) = 81 := by
      have hp := card_sup_mul_card_inf (Subgroup.zpowers e ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers x)
        (Subgroup.zpowers u) (comm_of_le_centralizer hVuc)
      have hi : Nat.card ↥((Subgroup.zpowers e ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers x) ⊓
          Subgroup.zpowers u) = 1 := inf_zpowers_trivial hu3 hu1 huV
      rw [hi, hVcard, card_zpowers_of_ne_one hu3 (Subgroup.mem_zpowers u) hu1] at hp
      omega
    have hFeM : Fe ≤ M := hFeC.trans hCeM
    have hVM : Subgroup.zpowers e ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers x ≤ M := hVFe.trans hFeM
    have hWM : (Subgroup.zpowers e ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers x) ⊔
        Subgroup.zpowers u ≤ M :=
      sup_le hVM (Subgroup.zpowers_le.2 (hUR'.trans hR'M.1 huU))
    have haW : a ∈ (Subgroup.zpowers e ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers x) ⊔
        Subgroup.zpowers u :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)))
    exact no_E4_contains h hEA (Or.inr hA3) hnot ha1 hWM
      (isElemAbelian_sup hVel (isElemAbelian_zpowers hu3) (comm_of_le_centralizer hVuc))
      haW (le_of_eq hWcard.symm)
  have haU : a ∈ U := by
    by_contra haU
    have hcomm : ∀ u ∈ U, ∀ f ∈ Fe, u * f = f * u := by
      intro u hu f hf
      have hfR' : f ∈ R' := hFeR' hf
      have hfF : f ∈ F := (Subgroup.mem_inf.1 hf).1
      have huF : u ∈ F := (Subgroup.mem_inf.1 (hUFe hu)).1
      have hc1 : u⁻¹ * f⁻¹ * u * f ∈ Subgroup.zpowers a := comm_mem hF huF hfF
      have hc2 : u⁻¹ * f⁻¹ * u * f ∈ U := by
        have h1 := conj_mem_of_normal hUR' hUn (R'.inv_mem hfR') hu
        have h2 := U.mul_mem (U.inv_mem hu) h1
        have e2 : u⁻¹ * (f⁻¹ * u * f⁻¹⁻¹) = u⁻¹ * f⁻¹ * u * f := by group
        rwa [e2] at h2
      by_cases hc : u⁻¹ * f⁻¹ * u * f = 1
      · exact mul_comm_of_comm_eq_one hc
      · exfalso
        have heq := zpowers_eq_of_mem ha3 ha1 hc1 hc
        apply haU
        have hamem : a ∈ Subgroup.zpowers (u⁻¹ * f⁻¹ * u * f) := by
          rw [heq]
          exact Subgroup.mem_zpowers a
        exact (Subgroup.zpowers_le.2 hc2) hamem
    have hUle : U ≤ Subgroup.zpowers e ⊔ Subgroup.zpowers a := fun u hu =>
      center_le_sup hF heF he' (hUFe hu) (fun f hf => (hcomm u hu f hf).symm)
    have heq : U = Subgroup.zpowers e ⊔ Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge hUle (by rw [hU9]; exact zpowers_sup_card_le hF heF he')
    apply haU
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  by_cases hUB : U ≤ B'
  · exact hnot B' hB'D (hUB haU)
  · have hB'pg : IsPGroup 3 ↥B' := isPGroup_of_elemAbelian hB'el
    have hB'nor : B' ≤ Subgroup.normalizer (U : Set G) := le_trans hB'R' hR'nor
    have hlinesB := lines_card_le B' U hB'pg hU9 hB'nor
    have hBcard81 : 81 ≤ Nat.card ↥B' := by
      rw [hB'card, hBcard, show (81 : ℕ) = 3 ^ 4 by norm_num]
      exact Nat.pow_le_pow_right (by norm_num) hm4
    have hK2 : 27 ≤ Nat.card ↥(B' ⊓ Subgroup.centralizer (U : Set G)) := by omega
    have hUB'card : Nat.card ↥(U ⊓ B') ≤ 3 := by
      have hdvd : Nat.card ↥(U ⊓ B') ∣ 9 := by
        have := Subgroup.card_subgroup_dvd_card ((U ⊓ B').subgroupOf U)
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hU9] at this
        exact this
      have hne : Nat.card ↥(U ⊓ B') ≠ 9 := by
        intro h9
        apply hUB
        have heq : U ⊓ B' = U := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h9, hU9])
        intro u hu
        have hmem : u ∈ U ⊓ B' := by
          rw [heq]
          exact hu
        exact (Subgroup.mem_inf.1 hmem).2
      have hmem := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
      rw [show Nat.divisors 9 = {1, 3, 9} from by decide] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h1 | h1 | h1
      · omega
      · omega
      · exact absurd h1 hne
    have hUK2 : Nat.card ↥(U ⊓ (B' ⊓ Subgroup.centralizer (U : Set G))) ≤ 3 :=
      le_trans (Subgroup.card_le_of_le (inf_le_inf_left _ inf_le_left)) hUB'card
    have hcommK2 : ∀ x ∈ U, ∀ y ∈ B' ⊓ Subgroup.centralizer (U : Set G), x * y = y * x :=
      fun x hx y hy => Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hy).2 x hx
    have hK2el := isElemAbelian_of_le hB'el (inf_le_left : B' ⊓ Subgroup.centralizer (U : Set G) ≤ B')
    have hW'el := isElemAbelian_sup hUel hK2el hcommK2
    have hprod := card_sup_mul_card_inf U (B' ⊓ Subgroup.centralizer (U : Set G)) hcommK2
    rw [hU9] at hprod
    have hW'card : 81 ≤ Nat.card ↥(U ⊔ (B' ⊓ Subgroup.centralizer (U : Set G))) := by
      nlinarith
    have hW'M : U ⊔ (B' ⊓ Subgroup.centralizer (U : Set G)) ≤ M :=
      sup_le (hUR'.trans hR'M.1) ((inf_le_left).trans (hB'R'.trans hR'M.1))
    exact no_E4_contains h hEA (Or.inr hA3) hnot ha1 hW'M hW'el (Subgroup.mem_sup_left haU) hW'card

end Piece3

section Glue

@[expose] def Lemma1111P1Claim : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ) (B M E A : Subgroup G) (a : G) (K : Subgroup G),
    Cex117 G m 3 B M E A a K → IsSLThreeFour (barOf 3 K) →
      ∃ F : Subgroup G, A ≤ F ∧ IsExtraspecialFive F a

@[expose] def Lemma1111P2Claim : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ) (B M E A : Subgroup G) (a : G) (K : Subgroup G),
    Cex117 G m 3 B M E A a K → IsSLThreeFour (barOf 3 K) →
      ∀ R : Subgroup G, IsSylowIn 3 M R → E ⊔ A ≤ R →
        ∀ e ∈ omegaOne 3 (centerOf R), e ≠ 1 → Cg e ≤ M

theorem lemma1111_piece3_of_cex {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G}
    {a : G} {K : Subgroup G} (h : Cex117 G m 3 B M E A a K) (hA3 : CFSG.Open.pRank 3 A = 3)
    {F : Subgroup G} (hAF : A ≤ F) (hF : IsExtraspecialFive F a)
    (hP2 : ∀ R : Subgroup G, IsSylowIn 3 M R → E ⊔ A ≤ R →
      ∀ e ∈ omegaOne 3 (centerOf R), e ≠ 1 → Cg e ≤ M)
    (hI31 : Input31_3) : False :=
  piece3_contra (B := B) h.toCex117Base.toSec11.toSec10Fails h.toCex117Base.toSec11.pair hA3
    (fun A1 hA1 haA1 => h.toCex117Base.notD ⟨A1, hA1, haA1⟩) h.toCex117Base.ha.1
    h.toCex117Base.ha.2 hAF hF hP2 hI31

theorem barOf_L34_or_SL34 {G : Type} [Group G] [Finite G] {X K : Subgroup G}
    (hcov : CFSG.HardMathSupport.Solomon.UniquenessMaximal.InputL34Cover)
    (hK : GLAPComponent 3 X K)
    (hL : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K))) :
    IsLThreeFour (barOf 3 K) ∨ IsSLThreeFour (barOf 3 K) := by
  have hnt : Nontrivial (barOf 3 K) := by
    by_contra hns
    rw [not_nontrivial_iff_subsingleton] at hns
    have hle : Nat.card (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) ≤ Nat.card (barOf 3 K) :=
      Nat.card_le_card_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    have h1 : Nat.card (barOf 3 K) ≤ 1 := (Finite.card_le_one_iff_subsingleton).2 hns
    have h20160 := CFSG.HardMathSupport.Solomon.Coordinator.card_of_isLThreeFour hL
    omega
  have hq := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.isQuasisimple_barOf Nat.prime_three hK hnt
  have hcov' : IsLThreeFour (barOf 3 K ⧸ CFSG.pCore 3 (barOf 3 K)) :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.IsLThreeFour.of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq
        (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510iiNs.pCore_barOf_eq_center hK).symm) hL
  exact hcov (barOf 3 K) hq hcov'

theorem lemma1111_of_inputs
    (hcov : CFSG.HardMathSupport.Solomon.UniquenessMaximal.InputL34Cover)
    (hI31 : Input31_3) (h1110 : Lemma1110Statement)
    (hP1 : Lemma1111P1Claim) (hP2 : Lemma1111P2Claim) : Lemma1111Statement := by
  intro G _ _ m p B M E A a K h
  have hT := h1110 h
  unfold Type117c at hT
  obtain ⟨hp3, hA3, hL⟩ := hT
  subst hp3
  refine ⟨rfl, hA3, ?_⟩
  rcases barOf_L34_or_SL34 hcov h.toCex117Base.hK hL with hL3 | hSL
  · exact hL3
  · exfalso
    obtain ⟨F, hAF, hF⟩ := hP1 G m B M E A a K h hSL
    exact lemma1111_piece3_of_cex h hA3 hAF hF (hP2 G m B M E A a K h hSL) hI31

end Glue

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1111

end
