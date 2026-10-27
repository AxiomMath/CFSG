module

public import CFSG.FeitThompson.Local.CriticalSubgroupFixedLine
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.PSubgroupCentralizersLiftQuotient
import CFSG.FeitThompson.Local.MaximalIntersectionSylowNormalizerControl
import CFSG.FeitThompson.OddOrder.CoprimeNilpotentSubgroupsCommute
import CFSG.FeitThompson.Local.FixedPointsNormalizedProductFixedFree
import CFSG.FeitThompson.Local.PrimeCentralizerComplementNoncentral

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup Pointwise
open scoped commutatorElement

variable {J : Type*} [Group J] {p q r : ℕ} {R Q P H : Subgroup J}

theorem inf_centralizer_sup_eq_inf :
    R ⊓ centralizer ((Q ⊔ P : Subgroup J) : Set J)
      = (R ⊓ centralizer (Q : Set J)) ⊓ centralizer (P : Set J) := by
  have hc : centralizer ((Q ⊔ P : Subgroup J) : Set J)
      = centralizer (Q : Set J) ⊓ centralizer (P : Set J) := by
    refine le_antisymm
      (le_inf (centralizer_le (by exact_mod_cast le_sup_left (a := Q) (b := P)))
        (centralizer_le (by exact_mod_cast le_sup_right (a := Q) (b := P)))) ?_
    rintro x ⟨hxQ, hxP⟩
    rw [mem_centralizer_iff]
    have hle : (Q ⊔ P : Subgroup J) ≤ centralizer ({x} : Set J) :=
      sup_le (fun z hz => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hxQ z hz))
        (fun z hz => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hxP z hz))
    exact fun y hy => mem_centralizer_singleton_iff.1 (hle hy)
  rw [hc, inf_assoc]

theorem exists_le_natCard_eq_prime [Finite J] {D : Subgroup J} (hr : r.Prime)
    (hD : IsPGroup r ↥D) (hne : D ≠ ⊥) : ∃ Z : Subgroup J, Z ≤ D ∧ Nat.card ↥Z = r := by
  have := Fact.mk hr
  have hnt : Nontrivial ↥D := D.nontrivial_iff_ne_bot.2 hne
  obtain ⟨a, ha⟩ := hD.exists_card_eq
  have hapos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h, pow_zero] at ha
      exact absurd ha (Finite.one_lt_card_iff_nontrivial.2 hnt).ne'
    · exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) r (ha ▸ dvd_pow_self r hapos.ne')
  exact ⟨zpowers (x : J), zpowers_le.2 x.2, by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]⟩

theorem mem_centralizer_of_forall_commutatorElement_mem [Finite J] {T Z : Subgroup J}
    (hcop : (Nat.card ↥T).Coprime (Nat.card ↥Z)) (hZT : Z ≤ centralizer (T : Set J))
    {n : J} (hn : ∀ y ∈ T, ⁅n, y⁆ ∈ Z) : n ∈ centralizer (T : Set J) := by
  have hmul : ∀ y z : ↥T, (⟨⁅n, ((y * z : ↥T) : J)⁆, hn _ (y * z).2⟩ : ↥Z)
      = ⟨⁅n, (y : J)⁆, hn _ y.2⟩ * ⟨⁅n, (z : J)⁆, hn _ z.2⟩ := by
    intro y z
    refine Subtype.ext ?_
    have hc : (y : J) * (n * (z : J) * n⁻¹ * (z : J)⁻¹)
        = (n * (z : J) * n⁻¹ * (z : J)⁻¹) * (y : J) := by
      have hcz := mem_centralizer_iff.1 (hZT (hn _ z.2)) (y : J) y.2
      simpa [commutatorElement_def] using hcz
    push_cast
    simp only [commutatorElement_def]
    calc n * ((y : J) * (z : J)) * n⁻¹ * ((y : J) * (z : J))⁻¹
        = (n * y * n⁻¹ * (y : J)⁻¹) * ((y : J) * (n * z * n⁻¹ * (z : J)⁻¹) * (y : J)⁻¹) := by
          group
      _ = (n * y * n⁻¹ * (y : J)⁻¹) * ((n * z * n⁻¹ * (z : J)⁻¹) * (y : J) * (y : J)⁻¹) := by
          rw [hc]
      _ = _ := by group
  set φ : ↥T →* ↥Z := MonoidHom.mk' (fun y => ⟨⁅n, (y : J)⁆, hn _ y.2⟩) hmul with hφ
  rw [mem_centralizer_iff]
  intro y hy
  have h1 : orderOf (φ ⟨y, hy⟩) ∣ Nat.card ↥T :=
    (orderOf_map_dvd φ _).trans (orderOf_dvd_natCard _)
  have h2 : orderOf (φ ⟨y, hy⟩) ∣ Nat.card ↥Z := orderOf_dvd_natCard _
  have h3 : orderOf (φ ⟨y, hy⟩) = 1 := Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd h1 h2)
  have h4 : ⁅n, y⁆ = 1 := by
    have h5 : φ ⟨y, hy⟩ = 1 := orderOf_eq_one_iff.1 h3
    simpa [hφ] using congrArg (Subtype.val (p := fun x => x ∈ Z)) h5
  rw [commutatorElement_def] at h4
  calc y * n = (n * y * n⁻¹ * y⁻¹) * (y * n) := by rw [h4]; group
    _ = n * y := by group

theorem exists_mul_of_mem_sup_of_le_normalizer {A B : Subgroup J}
    (hBA : B ≤ normalizer (A : Set J)) {x : J} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hcoe : (↑(A ⊔ B) : Set J) = (A : Set J) * (B : Set J) :=
    Subgroup.coe_mul_of_right_le_normalizer_left A B hBA
  have hx' : x ∈ (A : Set J) * (B : Set J) := hcoe ▸ (by exact_mod_cast hx)
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem sup_inf_sup_le_of_disjoint (hRQP : R ⊓ (Q ⊔ P) = ⊥) (hQP : Q ⊓ P = ⊥)
    {U N : Subgroup J} (hUN : U ≤ N) (hNR : N ≤ R) (hQN : Q ≤ normalizer (N : Set J))
    (hPU : P ≤ normalizer (U : Set J)) : (N ⊔ Q) ⊓ (U ⊔ P) ≤ U := by
  intro x hx
  obtain ⟨hxNQ, hxUP⟩ := hx
  obtain ⟨n, hn, y, hy, hxn⟩ := exists_mul_of_mem_sup_of_le_normalizer hQN hxNQ
  obtain ⟨u, hu, s, hs, hxu⟩ := exists_mul_of_mem_sup_of_le_normalizer hPU hxUP
  have hkey : u⁻¹ * n = s * y⁻¹ := by
    have hnu : n * y = u * s := by rw [← hxn, ← hxu]
    calc u⁻¹ * n = u⁻¹ * (n * y) * y⁻¹ := by group
      _ = u⁻¹ * (u * s) * y⁻¹ := by rw [hnu]
      _ = s * y⁻¹ := by group
  have h1 : u⁻¹ * n ∈ R := mul_mem (inv_mem (hNR (hUN hu))) (hNR hn)
  have h2 : u⁻¹ * n ∈ (Q ⊔ P : Subgroup J) := by
    rw [hkey]
    exact mul_mem (mem_sup_right hs) (mem_sup_left (inv_mem hy))
  have hmem : u⁻¹ * n ∈ R ⊓ (Q ⊔ P) := ⟨h1, h2⟩
  rw [hRQP, mem_bot, inv_mul_eq_one] at hmem
  have hsy : s = y := by
    rw [hmem] at hkey
    have h3 : (1 : J) = s * y⁻¹ := by simpa using hkey
    exact eq_of_div_eq_one (by simpa [div_eq_mul_inv] using h3.symm)
  have hs1 : s = 1 := by
    have hmem2 : s ∈ Q ⊓ P := ⟨hsy ▸ hy, hs⟩
    rwa [hQP, mem_bot] at hmem2
  rw [hxu, hs1, mul_one]
  exact hu

theorem lt_inf_normalizer_of_lt' [Finite J] (hr : r.Prime) (hH : IsPGroup r ↥H)
    {U : Subgroup J} (hUH : U < H) : U < H ⊓ normalizer (U : Set J) := by
  simpa [inf_comm] using lt_inf_normalizer_of_lt hr hH hUH

theorem exists_critical_subgroup [Finite J] (hr : r.Prime) (hodd : Odd r)
    (hR : IsPGroup r ↥R) (hRne : R ≠ ⊥) :
    ∃ H : Subgroup J, H ≠ ⊥ ∧ H ≤ R ∧ (H.subgroupOf R).Characteristic ∧
      (∀ x ∈ H, x ^ r = 1) ∧
      IsPGroup r ↥(fixingSubgroup (MulAut ↥R) ((H.subgroupOf R : Subgroup ↥R) : Set ↥R)) := by
  have : Nontrivial ↥R := R.nontrivial_iff_ne_bot.mpr hRne
  obtain ⟨H₀, hH₀⟩ := exists_isOddCriticalExponentSubgroup (P := ↥R) hr hodd hR
  refine ⟨H₀.map R.subtype, ?_, Subgroup.map_subtype_le H₀, ?_, ?_, ?_⟩
  · exact fun h => hH₀.ne_bot
      ((Subgroup.map_eq_bot_iff_of_injective H₀ R.subtype_injective).1 h)
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective R.subtype_injective]
    exact hH₀.characteristic
  · rintro x ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (by simpa using hH₀.pow_eq_one y hy)
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective R.subtype_injective]
    exact hH₀.isPGroup_fixingSubgroup

section Quotient

variable {Y : Type*} [Group Y] {s : ℕ} {U M N S T : Subgroup Y}

theorem le_of_map_le_centralizer_map [Finite Y] [U.Normal] (hs : s.Prime)
    (hcop : (Nat.card ↥U).Coprime s) (hS : IsPGroup s ↥S) (hUM : U ≤ M)
    (hMS : M ⊓ centralizer (S : Set Y) = U) {A : Subgroup Y} (hAM : A ≤ M)
    (h : A.map (mk' U) ≤ centralizer ((S.map (mk' U) : Subgroup (Y ⧸ U)) : Set (Y ⧸ U))) :
    A ≤ U := by
  have := Fact.mk hs
  rw [centralizer_map_mk'_eq hcop hS] at h
  intro a ha
  obtain ⟨c, hc, hcx⟩ := h ⟨a, ha, rfl⟩
  simp only [SetLike.mem_coe] at hc
  have hu : a⁻¹ * c ∈ U := by simpa using QuotientGroup.eq.1 hcx.symm
  have hcM : c ∈ M := by
    have hrw : c = a * (a⁻¹ * c) := by group
    rw [hrw]; exact mul_mem (hAM ha) (hUM hu)
  have hcU : c ∈ U := hMS ▸ ⟨hcM, hc⟩
  have hrw : a = c * (a⁻¹ * c)⁻¹ := by group
  rw [hrw]; exact mul_mem hcU (inv_mem hu)

theorem inf_centralizer_map_eq_bot [Finite Y] [U.Normal] (hs : s.Prime)
    (hcop : (Nat.card ↥U).Coprime s) (hS : IsPGroup s ↥S) (hUM : U ≤ M)
    (hMS : M ⊓ centralizer (S : Set Y) = U) :
    (M.map (mk' U)) ⊓ centralizer ((S.map (mk' U) : Subgroup (Y ⧸ U)) : Set (Y ⧸ U)) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  obtain ⟨⟨a, ha, rfl⟩, hc⟩ := hx
  simp only [SetLike.mem_coe] at ha
  refine (QuotientGroup.eq_one_iff _).2 ?_
  refine le_of_map_le_centralizer_map hs hcop hS hUM hMS (A := zpowers a)
    (zpowers_le.2 ha) ?_ (mem_zpowers a)
  rintro y ⟨z, hz, rfl⟩
  obtain ⟨k, rfl⟩ := hz
  simpa using Subgroup.zpow_mem _ hc k

theorem inf_map_mk'_eq_bot [U.Normal] (h : M ⊓ (U ⊔ S) ≤ U) :
    M.map (mk' U) ⊓ S.map (mk' U) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  obtain ⟨hxM, hxS⟩ := hx
  obtain ⟨a, ha, rfl⟩ := hxM
  obtain ⟨b, hb, hba⟩ := hxS
  simp only [SetLike.mem_coe] at ha hb
  have hu : b⁻¹ * a ∈ U := QuotientGroup.eq.1 hba
  have haU : a ∈ U ⊔ S := by
    have hrw : a = b * (b⁻¹ * a) := by group
    rw [hrw]
    exact mul_mem (mem_sup_right hb) (mem_sup_left hu)
  exact (QuotientGroup.eq_one_iff _).2 (h ⟨ha, haU⟩)

theorem natCard_map_mk'_eq [U.Normal] {A : Subgroup Y} (hAU : A ⊓ U = ⊥) :
    Nat.card ↥(A.map (mk' U)) = Nat.card ↥A := by
  have hinj : Function.Injective ((mk' U).comp A.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have hmem : (x : Y) ∈ A ⊓ U := ⟨x.2, by simpa [MonoidHom.mem_ker] using hx⟩
    rw [hAU, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hr : (MonoidHom.comp (mk' U) A.subtype).range = A.map (mk' U) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]

theorem le_of_map_mk'_le_map_mk' [U.Normal] {A : Subgroup Y} (hUT : U ≤ T)
    (h : A.map (mk' U) ≤ T.map (mk' U)) : A ≤ T := by
  have h2 := (le_comap_map (mk' U) A).trans (comap_mono h)
  rwa [QuotientGroup.comap_map_mk', sup_eq_right.2 hUT] at h2

theorem isNilpotent_map_of_inf_centralizer_map_eq_bot [Finite Y] [U.Normal]
    [Group.IsSolvable ↥(M.map (mk' U))] (hs : s.Prime)
    (hScard : Nat.card ↥(S.map (mk' U)) = s)
    (hdisj : (M.map (mk' U)) ⊓ (S.map (mk' U)) = ⊥)
    (hnorm : S.map (mk' U) ≤ normalizer ((M.map (mk' U) : Subgroup (Y ⧸ U)) : Set (Y ⧸ U)))
    (hC : (M.map (mk' U)) ⊓ centralizer ((S.map (mk' U) : Subgroup (Y ⧸ U)) : Set (Y ⧸ U)) = ⊥) :
    Group.IsNilpotent ↥(M.map (mk' U)) := by
  refine isNilpotent_of_isSolvable_of_le_normalizer hdisj ?_ hnorm ?_
  · intro hb
    rw [hb, Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩] at hScard
    exact hs.one_lt.ne hScard
  · intro e he hne
    rw [centralizer_singleton_eq_of_natCard_eq_prime hs hScard he hne]
    exact hC

theorem commutatorElement_mem_of_isNilpotent_map [Finite Y] [U.Normal]
    (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) (hNr : IsPGroup r ↥N) (hTq : IsPGroup q ↥T)
    (hnil : Group.IsNilpotent ↥((N ⊔ T : Subgroup Y).map (mk' U))) :
    ∀ n ∈ N, ∀ y ∈ T, n⁻¹ * y⁻¹ * n * y ∈ U := by
  have := Fact.mk hq
  have := Fact.mk hr
  intro n hn y hy
  set L := (N ⊔ T : Subgroup Y).map (mk' U) with hL
  have hnL : (mk' U n : Y ⧸ U) ∈ L := ⟨n, mem_sup_left hn, rfl⟩
  have hyL : (mk' U y : Y ⧸ U) ∈ L := ⟨y, mem_sup_right hy, rfl⟩
  set x : ↥L := ⟨mk' U n, hnL⟩ with hx
  set z : ↥L := ⟨mk' U y, hyL⟩ with hz
  obtain ⟨k1, hk1⟩ := hNr ⟨n, hn⟩
  obtain ⟨k2, hk2⟩ := hTq ⟨y, hy⟩
  have hxdvd : orderOf x ∣ r ^ k1 := by
    refine orderOf_dvd_of_pow_eq_one (Subtype.ext ?_)
    change (mk' U n) ^ (r ^ k1) = 1
    rw [← map_pow, show (n : Y) ^ (r ^ k1) = 1 from by
      simpa using congrArg (Subtype.val (p := fun y : Y => y ∈ N)) hk1, map_one]
  have hzdvd : orderOf z ∣ q ^ k2 := by
    refine orderOf_dvd_of_pow_eq_one (Subtype.ext ?_)
    change (mk' U y) ^ (q ^ k2) = 1
    rw [← map_pow, show (y : Y) ^ (q ^ k2) = 1 from by
      simpa using congrArg (Subtype.val (p := fun z : Y => z ∈ T)) hk2, map_one]
  have hrq : Nat.Coprime (r ^ k1) (q ^ k2) :=
    Nat.pow_gcd_pow_of_gcd_eq_one ((Nat.coprime_primes hr hq).2 hqr.symm)
  have hcop : (orderOf x).Coprime (orderOf z) :=
    Nat.Coprime.coprime_dvd_left hxdvd (Nat.Coprime.coprime_dvd_right hzdvd hrq)
  have heq : (mk' U n) * (mk' U y) = (mk' U y) * (mk' U n) :=
    congrArg Subtype.val (commute_of_coprime_orderOf (↥L) x z hcop)
  rw [← QuotientGroup.eq_one_iff]
  have hg : ((n⁻¹ * y⁻¹ * n * y : Y) : Y ⧸ U)
      = (mk' U n)⁻¹ * (mk' U y)⁻¹ * ((mk' U n) * (mk' U y)) := by
    simp only [mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
    group
  rw [hg, heq]
  group

end Quotient

section SubgroupOf

variable {W A B : Subgroup J} {s : ℕ}

theorem centralizer_subgroupOf_of_le (hAW : A ≤ W) :
    centralizer ((A.subgroupOf W : Subgroup ↥W) : Set ↥W)
      = (centralizer (A : Set J)).subgroupOf W := by
  ext x
  simp only [mem_centralizer_iff, mem_subgroupOf, SetLike.mem_coe]
  exact ⟨fun h a ha => congrArg Subtype.val (h ⟨a, hAW ha⟩ (by simpa [mem_subgroupOf] using ha)),
    fun h b hb => Subtype.ext (h (b : J) (by simpa [mem_subgroupOf] using hb))⟩

theorem inf_subgroupOf_eq_subgroupOf_inf :
    A.subgroupOf W ⊓ B.subgroupOf W = (A ⊓ B).subgroupOf W :=
  (Subgroup.comap_inf _ _ _).symm

theorem le_normalizer_subgroupOf (h : A ≤ normalizer (B : Set J)) :
    A.subgroupOf W ≤ normalizer ((B.subgroupOf W : Subgroup ↥W) : Set ↥W) := fun a ha => by
  rw [mem_normalizer_iff]
  intro y
  simp only [mem_subgroupOf]
  simpa using mem_normalizer_iff.1 (h (by simpa [mem_subgroupOf] using ha)) (y : J)

theorem isPGroup_subgroupOf (hAW : A ≤ W) (h : IsPGroup s ↥A) : IsPGroup s ↥(A.subgroupOf W) :=
  h.of_surjective (subgroupOfEquivOfLe hAW).symm.toMonoidHom
    (subgroupOfEquivOfLe hAW).symm.surjective

theorem le_of_subgroupOf_le_subgroupOf_of_le (hAW : A ≤ W) (h : A.subgroupOf W ≤ B.subgroupOf W) :
    A ≤ B := fun a ha => by
  simpa [mem_subgroupOf] using h (show (⟨a, hAW ha⟩ : ↥W) ∈ A.subgroupOf W by
    simpa [mem_subgroupOf] using ha)

end SubgroupOf

structure IsCriticalRegularComplementSetup (p q r : ℕ) (R Q P : Subgroup J) : Prop where
  prime_p : p.Prime
  prime_q : q.Prime
  prime_r : r.Prime
  odd_p : Odd p
  odd_q : Odd q
  odd_r : Odd r
  p_ne_q : p ≠ q
  p_ne_r : p ≠ r
  q_ne_r : q ≠ r
  normal_R : R.Normal
  coe_mul_coe : (R : Set J) * ((Q ⊔ P : Subgroup J) : Set J) = Set.univ
  disjoint_R : R ⊓ (Q ⊔ P) = ⊥
  normal_Q : (Q.subgroupOf (Q ⊔ P)).Normal
  disjoint_Q : Q ⊓ P = ⊥
  isPGroup_R : IsPGroup r ↥R
  isPGroup_Q : IsPGroup q ↥Q
  ne_bot_Q : Q ≠ ⊥
  natCard_P : Nat.card ↥P = p
  inf_centralizer_Q : Q ⊓ centralizer (P : Set J) = ⊥
  commutator_R_Q : ⁅R, Q⁆ ≠ ⊥
  rank_centralizer_P : elementaryAbelianPRank r ↥(R ⊓ centralizer (P : Set J)) ≤ 1
  rank_centralizer_Q : elementaryAbelianPRank r ↥(R ⊓ centralizer (Q : Set J)) ≤ 1

namespace IsCriticalRegularComplementSetup

variable (h : IsCriticalRegularComplementSetup p q r R Q P)

include h

theorem ne_bot_R : R ≠ ⊥ := fun hR => h.commutator_R_Q (by rw [hR]; simp)

theorem isCriticalFixedLineSetup {H : Subgroup J} (hne : H ≠ ⊥) (hHR : H ≤ R)
    (hchar : (H.subgroupOf R).Characteristic) (hpow : ∀ x ∈ H, x ^ r = 1)
    (hfix : IsPGroup r ↥(fixingSubgroup (MulAut ↥R) ((H.subgroupOf R : Subgroup ↥R) : Set ↥R))) :
    IsCriticalFixedLineSetup p q r R Q P H where
  prime_p := h.prime_p
  prime_q := h.prime_q
  prime_r := h.prime_r
  odd_p := h.odd_p
  odd_q := h.odd_q
  odd_r := h.odd_r
  p_ne_q := h.p_ne_q
  p_ne_r := h.p_ne_r
  q_ne_r := h.q_ne_r
  normal_R := h.normal_R
  coe_mul_coe := h.coe_mul_coe
  disjoint_R := h.disjoint_R
  normal_Q := h.normal_Q
  disjoint_Q := h.disjoint_Q
  isPGroup_R := h.isPGroup_R
  isPGroup_Q := h.isPGroup_Q
  ne_bot_Q := h.ne_bot_Q
  natCard_P := h.natCard_P
  inf_centralizer_Q := h.inf_centralizer_Q
  commutator_R_Q := h.commutator_R_Q
  rank_centralizer_P := h.rank_centralizer_P
  rank_centralizer_Q := h.rank_centralizer_Q
  ne_bot_H := hne
  le_H := hHR
  characteristic_H := hchar
  pow_eq_one_H := hpow
  isPGroup_fixingSubgroup := hfix

theorem exists_isCriticalFixedLineSetup [Finite J] :
    ∃ H : Subgroup J, IsCriticalFixedLineSetup p q r R Q P H := by
  obtain ⟨H, hne, hHR, hchar, hpow, hfix⟩ :=
    exists_critical_subgroup h.prime_r h.odd_r h.isPGroup_R h.ne_bot_R
  exact ⟨H, h.isCriticalFixedLineSetup hne hHR hchar hpow hfix⟩

theorem inf_centralizer_P_ne_bot [Finite J] [Group.IsSolvable J] :
    R ⊓ centralizer (P : Set J) ≠ ⊥ := by
  obtain ⟨H, hH⟩ := h.exists_isCriticalFixedLineSetup
  exact fun hb => hH.inf_centralizer_H_ne_bot (le_bot_iff.1 (hb ▸ inf_le_inf_right _ hH.le_H))

end IsCriticalRegularComplementSetup

theorem le_centralizer_Q_of_inf_centralizer_sup_ne_bot [Finite J] (hr : r.Prime)
    (hR : IsPGroup r ↥R) (hcyc : IsCyclic ↥(R ⊓ centralizer (P : Set J)))
    (hVcard : Nat.card ↥(H ⊓ centralizer (P : Set J)) = r) (hHR : H ≤ R)
    (hne : R ⊓ centralizer ((Q ⊔ P : Subgroup J) : Set J) ≠ ⊥) :
    H ⊓ centralizer (P : Set J) ≤ R ⊓ centralizer (Q : Set J) := by
  obtain ⟨Z, hZle, hZcard⟩ := exists_le_natCard_eq_prime (r := r)
    (D := R ⊓ centralizer ((Q ⊔ P : Subgroup J) : Set J)) hr (hR.to_le inf_le_left) hne
  have hZP : Z ≤ R ⊓ centralizer (P : Set J) :=
    hZle.trans (inf_le_inf_left _
      (centralizer_le (by exact_mod_cast le_sup_right (a := Q) (b := P))))
  have hVP : H ⊓ centralizer (P : Set J) ≤ R ⊓ centralizer (P : Set J) :=
    inf_le_inf_right _ hHR
  have hZV : Z = H ⊓ centralizer (P : Set J) :=
    eq_of_le_of_natCard_eq_of_isCyclic hZP hVP (by rw [hZcard, hVcard])
  rw [← hZV]
  exact hZle.trans (by rw [inf_centralizer_sup_eq_inf]; exact inf_le_left)

theorem commutatorElement_mem_of_inf_centralizer_sup_eq [Finite J] [Group.IsSolvable J]
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpr : p ≠ r) (hqr : q ≠ r)
    {U N : Subgroup J} (hQ : IsPGroup q ↥Q) (hN : IsPGroup r ↥N)
    (hPcard : Nat.card ↥P = p) (hUcard : Nat.card ↥U = r)
    (hUN : U ≤ N) (hUQ : U ≤ centralizer (Q : Set J)) (hUCP : U ≤ centralizer (P : Set J))
    (hNU : N ≤ normalizer (U : Set J))
    (hPN : P ≤ normalizer (N : Set J)) (hPQ : P ≤ normalizer (Q : Set J))
    (hUPdisj : U ⊓ P = ⊥) (hNQP : (N ⊔ Q) ⊓ (U ⊔ P) ≤ U)
    (hCP : (N ⊔ Q) ⊓ centralizer (P : Set J) = U) :
    ∀ n ∈ N, ∀ y ∈ Q, n⁻¹ * y⁻¹ * n * y ∈ U := by
  have := Fact.mk hp
  have := Fact.mk hq
  have := Fact.mk hr
  have hP : IsPGroup p ↥P := IsPGroup.of_card (n := 1) (by simpa using hPcard)
  set W : Subgroup J := normalizer (U : Set J) with hWdef
  have hUW : U ≤ W := le_normalizer
  have hNW : N ≤ W := hNU
  have hQW : Q ≤ W := (le_centralizer_iff.1 hUQ).trans (centralizer_le_normalizer _)
  have hPW : P ≤ W := (le_centralizer_iff.1 hUCP).trans (centralizer_le_normalizer _)
  have hU'normal : (U.subgroupOf W).Normal := Subgroup.normal_in_normalizer
  have hM' : (N ⊔ Q : Subgroup J).subgroupOf W = N.subgroupOf W ⊔ Q.subgroupOf W :=
    subgroupOf_sup hNW hQW
  have hCP' : ((N ⊔ Q : Subgroup J).subgroupOf W) ⊓
      centralizer ((P.subgroupOf W : Subgroup ↥W) : Set ↥W) = U.subgroupOf W := by
    rw [centralizer_subgroupOf_of_le hPW, inf_subgroupOf_eq_subgroupOf_inf, hCP]
  have hcop : (Nat.card ↥(U.subgroupOf W)).Coprime p := by
    rw [natCard_subgroupOf_of_le' hUW, hUcard]
    exact (Nat.coprime_primes hr hp).2 (Ne.symm hpr)
  have hP' : IsPGroup p ↥(P.subgroupOf W) := isPGroup_subgroupOf hPW hP
  have hUM' : U.subgroupOf W ≤ (N ⊔ Q : Subgroup J).subgroupOf W :=
    comap_mono (hUN.trans le_sup_left)
  have hbot := inf_centralizer_map_eq_bot (U := U.subgroupOf W)
    (M := (N ⊔ Q : Subgroup J).subgroupOf W) (S := P.subgroupOf W) hp hcop hP' hUM' hCP'
  have hPU' : P.subgroupOf W ⊓ U.subgroupOf W = ⊥ := by
    rw [inf_subgroupOf_eq_subgroupOf_inf, inf_comm, hUPdisj, bot_subgroupOf]
  have hScard : Nat.card ↥((P.subgroupOf W).map (mk' (U.subgroupOf W))) = p := by
    rw [natCard_map_mk'_eq hPU', natCard_subgroupOf_of_le' hPW, hPcard]
  have hdisj : ((N ⊔ Q : Subgroup J).subgroupOf W).map (mk' (U.subgroupOf W)) ⊓
      (P.subgroupOf W).map (mk' (U.subgroupOf W)) = ⊥ := by
    refine inf_map_mk'_eq_bot ?_
    have hsup : U.subgroupOf W ⊔ P.subgroupOf W = (U ⊔ P : Subgroup J).subgroupOf W :=
      (subgroupOf_sup hUW hPW).symm
    rw [hsup, inf_subgroupOf_eq_subgroupOf_inf]
    exact comap_mono hNQP
  have hPNQ : P ≤ normalizer ((N ⊔ Q : Subgroup J) : Set J) := fun x hx =>
    normalizer_inf_normalizer_le_normalizer_sup N Q ⟨hPN hx, hPQ hx⟩
  have hnorm : (P.subgroupOf W).map (mk' (U.subgroupOf W)) ≤
      normalizer ((((N ⊔ Q : Subgroup J).subgroupOf W).map (mk' (U.subgroupOf W)) :
        Subgroup (↥W ⧸ U.subgroupOf W)) : Set (↥W ⧸ U.subgroupOf W)) :=
    (Subgroup.map_mono (le_normalizer_subgroupOf hPNQ)).trans (le_normalizer_map _)
  have hnil : Group.IsNilpotent ↥(((N ⊔ Q : Subgroup J).subgroupOf W).map
      (mk' (U.subgroupOf W))) :=
    isNilpotent_map_of_inf_centralizer_map_eq_bot hp hScard hdisj hnorm hbot
  rw [hM'] at hnil
  have hN' : IsPGroup r ↥(N.subgroupOf W) := isPGroup_subgroupOf hNW hN
  have hQ' : IsPGroup q ↥(Q.subgroupOf W) := isPGroup_subgroupOf hQW hQ
  have hkey := commutatorElement_mem_of_isNilpotent_map hq hr hqr hN' hQ' hnil
  intro n hn y hy
  have hcomm := hkey ⟨n, hNW hn⟩ (mem_subgroupOf.2 hn) ⟨y, hQW hy⟩ (mem_subgroupOf.2 hy)
  simpa [mem_subgroupOf] using hcomm

theorem le_centralizer_of_inf_centralizer_sup_eq [Finite J] [Group.IsSolvable J]
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpr : p ≠ r) (hqr : q ≠ r)
    {U N : Subgroup J} (hQ : IsPGroup q ↥Q) (hN : IsPGroup r ↥N) (hU : IsPGroup r ↥U)
    (hPcard : Nat.card ↥P = p) (hUcard : Nat.card ↥U = r)
    (hUN : U ≤ N) (hUQ : U ≤ centralizer (Q : Set J)) (hUCP : U ≤ centralizer (P : Set J))
    (hNU : N ≤ normalizer (U : Set J))
    (hPN : P ≤ normalizer (N : Set J)) (hPQ : P ≤ normalizer (Q : Set J))
    (hUPdisj : U ⊓ P = ⊥) (hNQP : (N ⊔ Q) ⊓ (U ⊔ P) ≤ U)
    (hCP : (N ⊔ Q) ⊓ centralizer (P : Set J) = U) :
    N ≤ centralizer (Q : Set J) := by
  have := Fact.mk hq
  have := Fact.mk hr
  have hcomm := commutatorElement_mem_of_inf_centralizer_sup_eq hp hq hr hpr hqr hQ hN hPcard
    hUcard hUN hUQ hUCP hNU hPN hPQ hUPdisj hNQP hCP
  have hcop : (Nat.card ↥Q).Coprime (Nat.card ↥U) :=
    IsPGroup.coprime_card_of_ne q r hqr Q U hQ hU
  intro n hn
  refine mem_centralizer_of_forall_commutatorElement_mem hcop hUQ fun y hy => ?_
  simpa [commutatorElement_def] using hcomm n⁻¹ (inv_mem hn) y⁻¹ (inv_mem hy)

namespace IsCriticalRegularComplementSetup

variable (h : IsCriticalRegularComplementSetup p q r R Q P)

include h

theorem inf_centralizer_sup_eq_bot_aux [Finite J] [Group.IsSolvable J] :
    R ⊓ centralizer ((Q ⊔ P : Subgroup J) : Set J) = ⊥ := by
  by_contra hne
  obtain ⟨H, hH⟩ := h.exists_isCriticalFixedLineSetup
  have hHR : H ≤ R := hH.le_H
  have hHp : IsPGroup r ↥H := h.isPGroup_R.to_le hHR
  set V : Subgroup J := H ⊓ centralizer (P : Set J) with hVdef
  have hVcard : Nat.card ↥V = r := hH.natCard_inf_centralizer
  have hVne : V ≠ ⊥ := fun hb => by
    rw [hb, Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩] at hVcard
    exact h.prime_r.one_lt.ne hVcard
  have hVQ : V ≤ R ⊓ centralizer (Q : Set J) :=
    le_centralizer_Q_of_inf_centralizer_sup_ne_bot h.prime_r h.isPGroup_R
      hH.isCyclic_inf_centralizer hVcard hHR hne
  have hcycQ : IsCyclic ↥(R ⊓ centralizer (Q : Set J)) :=
    isCyclic_of_elementaryAbelianPRank_le_one h.prime_r h.odd_r
      (h.isPGroup_R.to_le inf_le_left) h.rank_centralizer_Q
  set U : Subgroup J := H ⊓ centralizer (Q : Set J) with hUdef
  have hUle : U ≤ R ⊓ centralizer (Q : Set J) := inf_le_inf_right _ hHR
  have hVU : V ≤ U := le_inf inf_le_left (le_trans hVQ inf_le_right)
  have hUcyc : IsCyclic ↥U := isCyclic_of_le hUle
  have hUne : Nontrivial ↥U := (Subgroup.nontrivial_iff_ne_bot _).2 fun hb =>
    hVne (le_bot_iff.1 (hb ▸ hVU))
  have hUcard : Nat.card ↥U = r :=
    natCard_eq_of_isCyclic_of_forall_pow_eq_one h.prime_r hUne
      fun x => Subtype.ext (by simpa using hH.pow_eq_one_H (x : J) x.2.1)
  have hUV : U = V := (Subgroup.eq_of_le_of_card_ge hVU (by rw [hUcard, hVcard])).symm
  have hUCP : U ≤ centralizer (P : Set J) := hUV ▸ inf_le_right
  have hUCQ : U ≤ centralizer (Q : Set J) := inf_le_right
  have hUH : U ≤ H := inf_le_left
  have hUltH : U < H := by
    refine lt_of_le_of_ne hUH fun heq => hH.not_le_centralizer ?_
    rw [le_centralizer_iff]
    exact heq ▸ hUCQ
  set N : Subgroup J := H ⊓ normalizer (U : Set J) with hNdef
  have hUltN : U < N := lt_inf_normalizer_of_lt' h.prime_r hHp hUltH
  have hNH : N ≤ H := inf_le_left
  have hNU : N ≤ normalizer (U : Set J) := inf_le_right
  have hPU : P ≤ normalizer (U : Set J) :=
    (le_centralizer_iff.1 hUCP).trans (centralizer_le_normalizer _)
  have hQU : Q ≤ normalizer (U : Set J) :=
    (le_centralizer_iff.1 hUCQ).trans (centralizer_le_normalizer _)
  have hPN : P ≤ normalizer (N : Set J) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hH.le_normalizer_H P hx, le_normalizer_normalizer_of_le hPU hx⟩
  have hQN : Q ≤ normalizer (N : Set J) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hH.le_normalizer_H Q hx, le_normalizer_normalizer_of_le hQU hx⟩
  have hPQnorm : P ≤ normalizer (Q : Set J) :=
    le_sup_right.trans (le_normalizer_of_normal_subgroupOf (hK := h.normal_Q) le_sup_left)
  have hNQdisj : Disjoint N Q := by
    rw [Subgroup.disjoint_def]
    intro x hxN hxQ
    have hmem : x ∈ R ⊓ (Q ⊔ P) := ⟨hHR (hNH hxN), mem_sup_left hxQ⟩
    rw [h.disjoint_R] at hmem
    exact hmem
  have hCP : (N ⊔ Q) ⊓ centralizer (P : Set J) = U := by
    rw [sup_inf_centralizer_eq_of_inf_centralizer_eq_bot
      (normal_subgroupOf_of_le_normalizer (sup_le le_normalizer hQN)) hNQdisj hPN hPQnorm
      h.inf_centralizer_Q]
    exact le_antisymm (le_trans (inf_le_inf_right _ hNH) (hUV ▸ le_refl V))
      (le_inf hUltN.le hUCP)
  have hUPdisj : U ⊓ P = ⊥ :=
    le_bot_iff.1 (le_trans (le_inf (le_trans inf_le_left (hUH.trans hHR))
      (le_trans inf_le_right le_sup_right)) (le_of_eq h.disjoint_R))
  have hNQP : (N ⊔ Q) ⊓ (U ⊔ P) ≤ U :=
    sup_inf_sup_le_of_disjoint h.disjoint_R h.disjoint_Q hUltN.le (hNH.trans hHR) hQN hPU
  have hNC : N ≤ centralizer (Q : Set J) :=
    le_centralizer_of_inf_centralizer_sup_eq h.prime_p h.prime_q h.prime_r h.p_ne_r h.q_ne_r
      h.isPGroup_Q (hHp.to_le hNH) (hHp.to_le hUH) h.natCard_P hUcard hUltN.le hUCQ hUCP hNU
      hPN hPQnorm hUPdisj hNQP hCP
  exact absurd (le_inf hNH hNC) (not_le_of_gt hUltN)

theorem inf_centralizer_sup_eq_bot [Finite J] [Group.IsSolvable J] :
    R ⊓ centralizer ((Q ⊔ P : Subgroup J) : Set J) = ⊥ :=
  h.inf_centralizer_sup_eq_bot_aux

end IsCriticalRegularComplementSetup

theorem critical_regular_complement_common_fixed_points [Finite J] [Group.IsSolvable J]
    (h : IsCriticalRegularComplementSetup p q r R Q P) :
    R ⊓ centralizer (P : Set J) ≠ ⊥ ∧
      R ⊓ centralizer ((Q ⊔ P : Subgroup J) : Set J) = ⊥ :=
  ⟨h.inf_centralizer_P_ne_bot, h.inf_centralizer_sup_eq_bot⟩

end CFSG.FeitThompson
