module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Defs
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b
open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTheorem3 CFSG.Open

variable {G : Type} [Group G]

theorem mem_oUpperTwoPrime {K : Subgroup G} {x : G} (hx : x ∈ K) {k : ℕ} (hk : x ^ (2 ^ k) = 1) :
    x ∈ oUpperTwoPrime K :=
  subset_closure ⟨hx, k, hk⟩

theorem oUpperTwoPrime_le (K : Subgroup G) : oUpperTwoPrime K ≤ K :=
  (closure_le _).2 fun _ hx => hx.1

theorem oUpperTwoPrime_oUpperTwoPrime (K : Subgroup G) :
    oUpperTwoPrime (oUpperTwoPrime K) = oUpperTwoPrime K :=
  le_antisymm (oUpperTwoPrime_le _)
    ((closure_le _).2 fun _ ⟨hx, k, hk⟩ => subset_closure ⟨mem_oUpperTwoPrime hx hk, k, hk⟩)

theorem le_oUpperTwoPrime {K P : Subgroup G} (hP : IsPGroup 2 P) (hPK : P ≤ K) :
    P ≤ oUpperTwoPrime K := fun x hx => by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  exact mem_oUpperTwoPrime (hPK hx) (k := k) (by simpa using congrArg Subtype.val hk)

theorem rightConjugate_oUpperTwoPrime (K : Subgroup G) (g : G) :
    rightConjugate (oUpperTwoPrime K) g = oUpperTwoPrime (rightConjugate K g) := by
  rw [rightConjugate, oUpperTwoPrime, MonoidHom.map_closure, oUpperTwoPrime]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, MulEquiv.coe_toMonoidHom, mem_rightConjugate_iff]
  constructor
  · rintro ⟨x, ⟨hx, k, hk⟩, rfl⟩
    refine ⟨by
      simp only [MulAut.conj_apply, inv_inv]
      rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
      exact hx, k, ?_⟩
    rw [← map_pow, hk, map_one]
  · rintro ⟨hy, k, hk⟩
    refine ⟨g * y * g⁻¹, ⟨hy, k, ?_⟩, by simp only [MulAut.conj_apply]; group⟩
    rw [conj_pow, hk, mul_one, mul_inv_cancel]

theorem rightConjugate_le_rightConjugate {A B : Subgroup G} (h : A ≤ B) (g : G) :
    rightConjugate A g ≤ rightConjugate B g :=
  Subgroup.map_mono h

theorem rightConjugate_inf (A B : Subgroup G) (g : G) :
    rightConjugate (A ⊓ B) g = rightConjugate A g ⊓ rightConjugate B g :=
  Subgroup.map_inf_eq _ _ _ (MulAut.conj g⁻¹).injective

theorem rightConjugate_rightConjugate_inv (A : Subgroup G) (g : G) :
    rightConjugate (rightConjugate A g) g⁻¹ = A := by
  rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]

theorem isPGroup_rightConjugate {p : ℕ} {P : Subgroup G} (hP : IsPGroup p P) (g : G) :
    IsPGroup p (rightConjugate P g) :=
  hP.map _

theorem isSylowOf_rightConjugate [Finite G] {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (h : IsSylowOf p P K) (g : G) :
    IsSylowOf p (rightConjugate P g) (rightConjugate K g) := by
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨hle, hP, hdvd⟩ := h
  refine ⟨rightConjugate_le_rightConjugate hle g, isPGroup_rightConjugate hP g, ?_⟩
  unfold rightConjugate
  rw [Subgroup.relIndex_map_map]
  have hker : (MulAut.conj g⁻¹).toMonoidHom.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff _).2 (MulAut.conj g⁻¹).injective
  rw [hker, sup_bot_eq, sup_bot_eq]
  exact hdvd

theorem IsSylowOf.nonempty_mulEquiv {p : ℕ} [Fact p.Prime] {P Q K : Subgroup G}
    (hP : IsSylowOf p P K) (hQ : IsSylowOf p Q K) [Finite K] : Nonempty (P ≃* Q) := by
  obtain ⟨P', rfl⟩ := hP
  obtain ⟨Q', rfl⟩ := hQ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P' Q'
  subst hg
  exact ⟨((Subgroup.equivMapOfInjective _ _ K.subtype_injective).symm.trans
    (Sylow.equivSMul P' g)).trans (Subgroup.equivMapOfInjective _ _ K.subtype_injective)⟩

def thm3Members (K : Subgroup G) : Set (Subgroup G) := Set.range (rightConjugate (oUpperTwoPrime K))

def thm3Gen (K : Subgroup G) : Subgroup G := sSup (thm3Members K)

theorem le_thm3Gen {K M : Subgroup G} (hM : M ∈ thm3Members K) : M ≤ thm3Gen K :=
  le_sSup hM

theorem rightConjugate_mem_thm3Members {K M : Subgroup G} (hM : M ∈ thm3Members K) (g : G) :
    rightConjugate M g ∈ thm3Members K := by
  obtain ⟨a, rfl⟩ := hM
  exact ⟨a * g, (rightConjugate_mul _ a g).symm⟩

theorem thm3Gen_normal (K : Subgroup G) : (thm3Gen K).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : n ∈ ⨆ a : G, rightConjugate (oUpperTwoPrime K) a := by
    rwa [thm3Gen, thm3Members, sSup_range] at hn
  refine Subgroup.iSup_induction _ hn' (C := fun n => g * n * g⁻¹ ∈ thm3Gen K) ?_ ?_ ?_
  · intro a x hx
    refine le_thm3Gen ⟨a * g⁻¹, rfl⟩ ?_
    rw [← rightConjugate_mul, mem_rightConjugate_iff, inv_inv]
    rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]
    exact hx
  · simp
  · intro x y hx hy
    rw [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group]
    exact mul_mem hx hy

variable [Finite G]

theorem even_card_oUpperTwoPrime {K : Subgroup G} (hK : Even (Nat.card K)) :
    Even (Nat.card (oUpperTwoPrime K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (even_iff_two_dvd.1 hK)
  have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
  have hx1 : (x : G) ∈ oUpperTwoPrime K :=
    mem_oUpperTwoPrime x.2 (k := 1) (by simpa using congrArg Subtype.val hx2)
  rw [even_iff_two_dvd, ← hx, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_mk (x : G) hx1]
  exact orderOf_dvd_natCard _

theorem normalizer_oUpperTwoPrime {K : Subgroup G} (hK : TightlyEmbedded K) :
    normalizer (oUpperTwoPrime K : Set G) = normalizer (K : Set G) := by
  ext g
  constructor
  · intro hg
    by_contra hgK
    have hle : oUpperTwoPrime K ≤ K ⊓ rightConjugate K g := by
      refine le_inf (oUpperTwoPrime_le K) ?_
      have h1 := (rightConjugate_eq_self_iff _ g).2 hg
      rw [← h1, rightConjugate_oUpperTwoPrime]
      exact oUpperTwoPrime_le _
    exact (Nat.not_even_iff_odd.2 ((hK.2 g hgK).of_dvd_nat (Subgroup.card_dvd_of_le hle)))
      (even_card_oUpperTwoPrime hK.1)
  · intro hg
    rw [← rightConjugate_eq_self_iff] at hg ⊢
    rw [rightConjugate_oUpperTwoPrime, hg]

omit [Finite G] in
theorem card_thm3Members {K M : Subgroup G} (hM : M ∈ thm3Members K) :
    Nat.card M = Nat.card (oUpperTwoPrime K) := by
  obtain ⟨a, rfl⟩ := hM
  exact rightConjugate_card _ a

theorem odd_card_inf_thm3Members {K M N : Subgroup G} (hK : TightlyEmbedded K)
    (hM : M ∈ thm3Members K) (hN : N ∈ thm3Members K) (hne : M ≠ N) :
    Odd (Nat.card (M ⊓ N : Subgroup G)) := by
  obtain ⟨a, rfl⟩ := hM
  obtain ⟨b, rfl⟩ := hN
  have hab : a * b⁻¹ ∉ normalizer (K : Set G) := by
    intro h
    rw [← normalizer_oUpperTwoPrime hK, ← rightConjugate_eq_self_iff] at h
    apply hne
    calc rightConjugate (oUpperTwoPrime K) a
        = rightConjugate (rightConjugate (oUpperTwoPrime K) (a * b⁻¹)) b := by
          rw [rightConjugate_mul, inv_mul_cancel_right]
      _ = rightConjugate (oUpperTwoPrime K) b := by rw [h]
  have hodd := hK.2 _ hab
  have hconj : rightConjugate (K ⊓ rightConjugate K (a * b⁻¹)) b =
      rightConjugate K b ⊓ rightConjugate K a := by
    rw [rightConjugate_inf, rightConjugate_mul, inv_mul_cancel_right]
  have hodd' : Odd (Nat.card (rightConjugate K b ⊓ rightConjugate K a : Subgroup G)) := by
    rw [← hconj, rightConjugate_card]
    exact hodd
  refine hodd'.of_dvd_nat (Subgroup.card_dvd_of_le ?_)
  exact le_inf (inf_le_right.trans (rightConjugate_le_rightConjugate (oUpperTwoPrime_le K) b))
    (inf_le_left.trans (rightConjugate_le_rightConjugate (oUpperTwoPrime_le K) a))

omit [Finite G] in
theorem oUpperTwoPrime_thm3Members {K M : Subgroup G} (hM : M ∈ thm3Members K) :
    oUpperTwoPrime M = M := by
  obtain ⟨a, rfl⟩ := hM
  rw [rightConjugate_oUpperTwoPrime, oUpperTwoPrime_oUpperTwoPrime]

theorem nonempty_mulEquiv_of_isSylowOf_thm3Members {K M P R : Subgroup G}
    (hM : M ∈ thm3Members K) (hR : IsSylowOf 2 R K) (hP : IsSylowOf 2 P M) :
    Nonempty (P ≃* R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, rfl⟩ := hM
  have hR0 : IsSylowOf 2 R (oUpperTwoPrime K) :=
    hR.of_le (le_oUpperTwoPrime hR.isPGroup hR.le) (oUpperTwoPrime_le K)
  have hP0 := isSylowOf_rightConjugate hP a⁻¹
  rw [rightConjugate_rightConjugate_inv] at hP0
  obtain ⟨e⟩ := IsSylowOf.nonempty_mulEquiv (P := rightConjugate P a⁻¹) hP0 hR0
  exact ⟨(Subgroup.equivMapOfInjective P _ (MulAut.conj a⁻¹⁻¹).injective).trans e⟩

omit [Finite G] in
theorem rightConjugate_subgroupOf (H L : Subgroup G) (g : L) :
    (rightConjugate H (g : G)).subgroupOf L = rightConjugate (H.subgroupOf L) g := by
  ext x
  simp only [mem_subgroupOf, mem_rightConjugate_iff, Subgroup.coe_mul, Subgroup.coe_inv]

omit [Finite G] in
theorem inf_subgroupOf' (H₁ H₂ L : Subgroup G) :
    (H₁ ⊓ H₂).subgroupOf L = H₁.subgroupOf L ⊓ H₂.subgroupOf L := by
  ext x
  simp only [mem_subgroupOf, Subgroup.mem_inf]

omit [Finite G] in
theorem oUpperTwoPrime_subgroupOf {M L : Subgroup G} (hML : M ≤ L) :
    oUpperTwoPrime (M.subgroupOf L) = (oUpperTwoPrime M).subgroupOf L := by
  apply Subgroup.map_injective L.subtype_injective
  rw [map_subgroupOf_eq_of_le ((oUpperTwoPrime_le M).trans hML), oUpperTwoPrime, oUpperTwoPrime,
    MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, mem_subgroupOf, coe_subtype]
  constructor
  · rintro ⟨y, ⟨hy, k, hk⟩, rfl⟩
    exact ⟨hy, k, by simpa using congrArg Subtype.val hk⟩
  · rintro ⟨hx, k, hk⟩
    exact ⟨⟨x, hML hx⟩, ⟨hx, k, Subtype.ext (by simpa using hk)⟩, rfl⟩

def thm3MembersIn (K : Subgroup G) : Set (Subgroup (thm3Gen K)) :=
  (fun M => M.subgroupOf (thm3Gen K)) '' thm3Members K

omit [Finite G] in
theorem sSup_thm3MembersIn (K : Subgroup G) : sSup (thm3MembersIn K) = ⊤ := by
  apply Subgroup.map_injective (thm3Gen K).subtype_injective
  rw [(Subgroup.gc_map_comap _).l_sSup, thm3MembersIn, iSup_image]
  conv_rhs => rw [← Subgroup.subgroupOf_self (thm3Gen K), map_subgroupOf_eq_of_le le_rfl,
    thm3Gen, sSup_eq_iSup]
  refine iSup_congr fun M => iSup_congr fun hM => ?_
  exact map_subgroupOf_eq_of_le (le_thm3Gen hM)

theorem standardComponentOddCore_thm3Gen (K : Subgroup G) (hO : standardComponentOddCore G = ⊥) :
    standardComponentOddCore (thm3Gen K) = ⊥ := by
  have : (thm3Gen K).Normal := thm3Gen_normal K
  have hchar : (standardComponentOddCore (thm3Gen K)).Characteristic :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_characteristic
  have hodd : Odd (Nat.card (standardComponentOddCore (thm3Gen K))) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have hnorm : ((standardComponentOddCore (thm3Gen K)).map (thm3Gen K).subtype).Normal :=
    inferInstance
  have hle : (standardComponentOddCore (thm3Gen K)).map (thm3Gen K).subtype ≤
      standardComponentOddCore G := by
    refine le_sSup ⟨hnorm, ?_⟩
    rw [Subgroup.card_map_of_injective (thm3Gen K).subtype_injective]
    exact hodd
  rw [hO, le_bot_iff, map_eq_bot_iff_of_injective _ (thm3Gen K).subtype_injective] at hle
  exact hle

omit [Finite G] in
theorem isMulCommutative_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    [h : IsMulCommutative B] : IsMulCommutative A :=
  ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul]; exact h.is_comm.comm _ _)⟩⟩

theorem assumption41_thm3MembersIn {K R : Subgroup G} (hK : TightlyEmbedded K)
    (hO : standardComponentOddCore G = ⊥) (hR : IsSylowOf 2 R K)
    (hRd : IsDihedralTwoGroup R) (hRc : ¬ IsMulCommutative R) :
    Assumption41 (thm3MembersIn K) where
  oddCore := standardComponentOddCore_thm3Gen K hO
  conj_mem := by
    rintro _ ⟨M, hM, rfl⟩ g
    exact ⟨rightConjugate M g, rightConjugate_mem_thm3Members hM g,
      rightConjugate_subgroupOf M _ g⟩
  generates := sSup_thm3MembersIn K
  twoPart := by
    rintro _ ⟨M, hM, rfl⟩ _ ⟨N, hN, rfl⟩ -
    rw [Nat.card_congr (subgroupOfEquivOfLe (le_thm3Gen hM)).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (le_thm3Gen hN)).toEquiv, card_thm3Members hM,
      card_thm3Members hN]
  inter := by
    rintro _ ⟨M, hM, rfl⟩ _ ⟨N, hN, rfl⟩ hne
    have hMN : M ≠ N := fun h => hne (by rw [h])
    rw [← inf_subgroupOf', Nat.card_congr
      (subgroupOfEquivOfLe (inf_le_left.trans (le_thm3Gen hM))).toEquiv]
    exact odd_card_inf_thm3Members hK hM hN hMN
  perfect := by
    rintro _ ⟨M, hM, rfl⟩
    rw [oUpperTwoPrime_subgroupOf (le_thm3Gen hM), oUpperTwoPrime_thm3Members hM]
  dihedral := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rintro _ ⟨M, hM, rfl⟩ P hP
    have hP' : IsSylowOf 2 (P.map (thm3Gen K).subtype) M := by
      have := (isSylowOf_map_subtype_iff (thm3Gen K) (p := 2)).2 hP
      rwa [map_subgroupOf_eq_of_le (le_thm3Gen hM)] at this
    obtain ⟨e⟩ := nonempty_mulEquiv_of_isSylowOf_thm3Members hM hR hP'
    have e' : P ≃* R :=
      (Subgroup.equivMapOfInjective P _ (thm3Gen K).subtype_injective).trans e
    refine ⟨?_, fun hc => hRc (isMulCommutative_of_mulEquiv e'.symm)⟩
    obtain ⟨n, hn, ⟨f⟩⟩ := hRd
    exact ⟨n, hn, ⟨e'.trans f⟩⟩

omit [Finite G] in
theorem normalizer_rightConjugate (H : Subgroup G) (g : G) :
    normalizer (rightConjugate H g : Set G) = rightConjugate (normalizer (H : Set G)) g := by
  ext x
  rw [mem_rightConjugate_iff, ← rightConjugate_eq_self_iff, ← rightConjugate_eq_self_iff]
  constructor
  · intro h
    calc rightConjugate H (g * x * g⁻¹)
        = rightConjugate (rightConjugate (rightConjugate H g) x) g⁻¹ := by
          rw [rightConjugate_mul, rightConjugate_mul, mul_assoc]
      _ = H := by rw [h, rightConjugate_rightConjugate_inv]
  · intro h
    calc rightConjugate (rightConjugate H g) x
        = rightConjugate (rightConjugate H (g * x * g⁻¹)) g := by
          rw [rightConjugate_mul, rightConjugate_mul, inv_mul_cancel_right]
      _ = rightConjugate H g := by rw [h]

omit [Finite G] in
theorem rightConjugate_eq_of_normal {N : Subgroup G} (hN : N.Normal) (g : G) :
    rightConjugate N g = N := by
  rw [rightConjugate_eq_self_iff, normalizer_eq_top]
  exact mem_top g

omit [Finite G] in
theorem commute_of_inf_eq_bot {A B : Subgroup G} (hAB : A ≤ normalizer (B : Set G))
    (hBA : B ≤ normalizer (A : Set G)) (hinf : A ⊓ B = ⊥) {a b : G} (ha : a ∈ A) (hb : b ∈ B) :
    a * b = b * a := by
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ A := by
    have : b * a⁻¹ * b⁻¹ ∈ A := (mem_normalizer_iff.1 (hBA hb) _).1 (inv_mem ha)
    rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
    exact mul_mem ha this
  have h2 : a * b * a⁻¹ * b⁻¹ ∈ B := by
    have : a * b * a⁻¹ ∈ B := (mem_normalizer_iff.1 (hAB ha) _).1 hb
    exact mul_mem this (inv_mem hb)
  have h3 : a * b * a⁻¹ * b⁻¹ = 1 := by
    have := mem_inf.2 ⟨h1, h2⟩
    rwa [hinf, mem_bot] at this
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h3, one_mul]

omit [Finite G] in
theorem pow_two_pow_mul_eq_one {a b : G} (hab : Commute a b) {i j : ℕ} (ha : a ^ (2 ^ i) = 1)
    (hb : b ^ (2 ^ j) = 1) : (a * b) ^ (2 ^ (i + j)) = 1 := by
  rw [hab.mul_pow, pow_add, pow_mul, ha, one_pow, one_mul, mul_comm, pow_mul, hb, one_pow]

omit [Finite G] in
theorem inf_le_normalizer_inf {A B : Subgroup G} :
    normalizer (A : Set G) ⊓ normalizer (B : Set G) ≤
      normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro x hx
  rw [mem_inf] at hx
  obtain ⟨hA, hB⟩ := hx
  rw [mem_normalizer_iff] at hA hB ⊢
  intro h
  simp only [mem_inf] at hA hB ⊢
  rw [hA h, hB h]

omit [Finite G] in
theorem eq_bot_of_subgroupOf_eq_bot {H L : Subgroup G} (hHL : H ≤ L) (h : H.subgroupOf L = ⊥) :
    H = ⊥ := by
  rw [← map_subgroupOf_eq_of_le hHL, h, Subgroup.map_bot]

theorem commute_of_thm3Members {K M N : Subgroup G} (hK : TightlyEmbedded K)
    (hO : standardComponentOddCore G = ⊥)
    (hGN : ∀ N ∈ thm3Members K, thm3Gen K ≤ normalizer (N : Set G))
    (hM : M ∈ thm3Members K) (hN : N ∈ thm3Members K) (hne : M ≠ N) {x y : G} (hx : x ∈ M)
    (hy : y ∈ N) : x * y = y * x := by
  have hle : M ⊓ N ≤ thm3Gen K := inf_le_left.trans (le_thm3Gen hM)
  have hn : ((M ⊓ N).subgroupOf (thm3Gen K)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hle).2 ((le_inf (hGN M hM) (hGN N hN)).trans
      inf_le_normalizer_inf)
  have hodd : Odd (Nat.card ((M ⊓ N).subgroupOf (thm3Gen K))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
    exact odd_card_inf_thm3Members hK hM hN hne
  have h0 : (M ⊓ N).subgroupOf (thm3Gen K) = ⊥ := by
    have h1 : (M ⊓ N).subgroupOf (thm3Gen K) ≤ standardComponentOddCore (thm3Gen K) :=
      le_sSup ⟨hn, hodd⟩
    rwa [standardComponentOddCore_thm3Gen K hO, le_bot_iff] at h1
  exact commute_of_inf_eq_bot ((le_thm3Gen hM).trans (hGN N hN))
    ((le_thm3Gen hN).trans (hGN M hM)) (eq_bot_of_subgroupOf_eq_bot hle h0) hx hy

theorem normal_of_thm3Member_normal {K R M : Subgroup G} (hK : TightlyEmbedded K)
    (hgen : normalClosure (K : Set G) = ⊤) (hO : standardComponentOddCore G = ⊥)
    (hR : IsSylowOf 2 R K) (hRc : ¬ IsMulCommutative R) (hM : M ∈ thm3Members K)
    (hMn : (M.subgroupOf (thm3Gen K)).Normal) : K.Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hGM : thm3Gen K ≤ normalizer (M : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (le_thm3Gen hM)).1 hMn
  have hGN : ∀ N ∈ thm3Members K, thm3Gen K ≤ normalizer (N : Set G) := by
    obtain ⟨a, rfl⟩ := hM
    rintro _ ⟨b, rfl⟩
    have := rightConjugate_le_rightConjugate hGM (a⁻¹ * b)
    rwa [rightConjugate_eq_of_normal (thm3Gen_normal K), ← normalizer_rightConjugate,
      rightConjugate_mul, ← mul_assoc, mul_inv_cancel, one_mul] at this
  have hK0 : oUpperTwoPrime K ∈ thm3Members K := ⟨1, rightConjugate_one _⟩
  have hRne : R ≠ ⊥ := by
    rintro rfl
    exact hRc ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  have hNK : ∀ N ∈ thm3Members K, N ≠ oUpperTwoPrime K → N ≤ normalizer (K : Set G) := by
    intro N hN hne x hx
    refine centralizer_two_subgroup_le K R hK hR.isPGroup hR.le hRne ?_
    rw [mem_centralizer_iff]
    intro r hr
    exact (commute_of_thm3Members hK hO hGN hN hK0 hne hx
      (le_oUpperTwoPrime hR.isPGroup hR.le hr)).symm
  have hKN : ∀ y ∈ K, ∀ N ∈ thm3Members K, rightConjugate N y = N := by
    intro y hy N hN
    by_contra hNy
    have hyK0 : rightConjugate (oUpperTwoPrime K) y = oUpperTwoPrime K := by
      rw [rightConjugate_eq_self_iff, normalizer_oUpperTwoPrime hK]
      exact le_normalizer hy
    have hNK0 : N ≠ oUpperTwoPrime K := by
      rintro rfl
      exact hNy hyK0
    have hNy' : rightConjugate N y ∈ thm3Members K := rightConjugate_mem_thm3Members hN y
    have hNyK0 : rightConjugate N y ≠ oUpperTwoPrime K := by
      intro h
      apply hNK0
      rw [← rightConjugate_rightConjugate_inv N y, h]
      rw [rightConjugate_eq_self_iff, normalizer_oUpperTwoPrime hK]
      exact le_normalizer (inv_mem hy)
    have hcent : ∀ m ∈ N, (∃ k : ℕ, m ^ (2 ^ k) = 1) → ∀ n ∈ N, m * n = n * m := by
      rintro m hm ⟨k, hk⟩ n hn
      have hmy : y⁻¹ * m * y ∈ rightConjugate N y := by
        rw [mem_rightConjugate_iff]
        rw [show y * (y⁻¹ * m * y) * y⁻¹ = m by group]
        exact hm
      have hc1 : Commute m⁻¹ (y⁻¹ * m * y) :=
        commute_of_thm3Members hK hO hGN hN hNy' (Ne.symm hNy) (inv_mem hm) hmy
      have hpow : (m⁻¹ * (y⁻¹ * m * y)) ^ (2 ^ (k + k)) = 1 := by
        refine pow_two_pow_mul_eq_one hc1 (by rw [inv_pow, hk, inv_one]) ?_
        rw [show y⁻¹ * m * y = y⁻¹ * m * y⁻¹⁻¹ by rw [inv_inv], conj_pow, hk]
        group
      have hxK : m⁻¹ * (y⁻¹ * m * y) ∈ K := by
        have h1 : m⁻¹ * y⁻¹ * m⁻¹⁻¹ ∈ K :=
          (mem_normalizer_iff.1 (inv_mem (hNK N hN hNK0 hm)) y⁻¹).1 (inv_mem hy)
        rw [show m⁻¹ * (y⁻¹ * m * y) = m⁻¹ * y⁻¹ * m⁻¹⁻¹ * y by group]
        exact mul_mem h1 hy
      have hx0 : m⁻¹ * (y⁻¹ * m * y) ∈ oUpperTwoPrime K := mem_oUpperTwoPrime hxK hpow
      have h2 := commute_of_thm3Members hK hO hGN hK0 hN (Ne.symm hNK0) hx0 hn
      have h3 := commute_of_thm3Members hK hO hGN hNy' hN hNy hmy hn
      have h4 : m⁻¹ * n = n * m⁻¹ := by
        have e : m⁻¹ = (m⁻¹ * (y⁻¹ * m * y)) * (y⁻¹ * m * y)⁻¹ := by group
        rw [e]
        have h3' : (y⁻¹ * m * y)⁻¹ * n = n * (y⁻¹ * m * y)⁻¹ :=
          (show Commute (y⁻¹ * m * y) n from h3).inv_left.eq
        rw [mul_assoc, h3', ← mul_assoc, h2, mul_assoc]
      calc m * n = m * (n * m⁻¹) * m := by group
        _ = m * (m⁻¹ * n) * m := by rw [h4]
        _ = n * m := by group
    have hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
      intro a ha b hb
      have ha' : a ∈ oUpperTwoPrime N := by rwa [oUpperTwoPrime_thm3Members hN]
      have hsub : oUpperTwoPrime N ≤ centralizer (N : Set G) := by
        refine (closure_le _).2 fun m ⟨hm, hk⟩ => ?_
        rw [SetLike.mem_coe, mem_centralizer_iff]
        intro n hn
        exact (hcent m hm hk n hn).symm
      exact (mem_centralizer_iff.1 (hsub ha') b hb).symm
    obtain ⟨P, hP⟩ := exists_isSylowOf 2 N
    obtain ⟨e⟩ := nonempty_mulEquiv_of_isSylowOf_thm3Members hN hR hP
    apply hRc
    have : IsMulCommutative P := ⟨⟨fun a b => Subtype.ext (hNab _ (hP.le a.2) _ (hP.le b.2))⟩⟩
    exact isMulCommutative_of_mulEquiv e.symm
  have hle : normalClosure (K : Set G) ≤ normalizer (oUpperTwoPrime K : Set G) := by
    refine (closure_le _).2 fun x hx => ?_
    obtain ⟨k, hk, hkx⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hkx
    rw [SetLike.mem_coe, ← rightConjugate_eq_self_iff]
    have hN' : rightConjugate (oUpperTwoPrime K) c ∈ thm3Members K := ⟨c, rfl⟩
    have := hKN k hk _ hN'
    calc rightConjugate (oUpperTwoPrime K) (c * k * c⁻¹)
        = rightConjugate (rightConjugate (rightConjugate (oUpperTwoPrime K) c) k) c⁻¹ := by
          rw [rightConjugate_mul, rightConjugate_mul, mul_assoc]
      _ = oUpperTwoPrime K := by rw [this, rightConjugate_rightConjugate_inv]
  rw [hgen, top_le_iff, normalizer_oUpperTwoPrime hK, normalizer_eq_top_iff] at hle
  exact hle

omit [Finite G] in
theorem map_rightConjugate_subtype {L : Subgroup G} (H : Subgroup L) (g : L) :
    (rightConjugate H g).map L.subtype = rightConjugate (H.map L.subtype) g := by
  ext x
  simp only [mem_map, mem_rightConjugate_iff, coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g * y * g⁻¹, hy, by simp⟩
  · rintro ⟨y, hy, hyx⟩
    have hxL : x ∈ L := by
      have : x = (g : G)⁻¹ * y * g := by rw [hyx]; group
      rw [this]
      exact mul_mem (mul_mem (inv_mem g.2) y.2) g.2
    refine ⟨⟨x, hxL⟩, ?_, rfl⟩
    have : g * ⟨x, hxL⟩ * g⁻¹ = y := Subtype.ext (by simp [hyx])
    rw [this]
    exact hy

omit [Finite G] in
theorem centralizer_map_subtype {L : Subgroup G} (H : Subgroup L) :
    centralizer (H : Set L) =
      (centralizer ((H.map L.subtype : Subgroup G) : Set G)).subgroupOf L := by
  ext x
  simp only [mem_subgroupOf, mem_centralizer_iff, SetLike.mem_coe, mem_map, coe_subtype]
  constructor
  · rintro h _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (h y hy)
  · intro h y hy
    exact Subtype.ext (h y ⟨y, hy, rfl⟩)

omit [Finite G] in
theorem isCyclic_subgroupOf {P L : Subgroup G} (hPL : P ≤ L) [IsCyclic P] :
    IsCyclic (P.subgroupOf L) :=
  isCyclic_of_surjective (subgroupOfEquivOfLe hPL).symm.toMonoidHom
    (subgroupOfEquivOfLe hPL).symm.surjective

theorem le_map_sec4W {K : Subgroup G} (S' : Subgroup (thm3Gen K)) {P M R₁ : Subgroup G}
    (hPS : P ≤ S'.map (thm3Gen K).subtype) (hM : M ∈ thm3Members K) (hR₁ : IsSylowOf 2 R₁ M)
    (hPR : P ≤ R₁) (hP : IsCyclic P) (hidx : P.relIndex R₁ = 2) :
    P ≤ (sec4W (thm3MembersIn K) S').map (thm3Gen K).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR₁G : R₁ ≤ thm3Gen K := hR₁.le.trans (le_thm3Gen hM)
  have hPG : P ≤ thm3Gen K := hPR.trans hR₁G
  rw [← map_subgroupOf_eq_of_le hPG]
  refine map_mono ?_
  have hP'S : P.subgroupOf (thm3Gen K) ≤ S' := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hPS hx
    rw [show x = y from Subtype.ext hyx.symm]
    exact hy
  have hR' : IsSylowOf 2 (R₁.subgroupOf (thm3Gen K)) (M.subgroupOf (thm3Gen K)) := by
    rw [← isSylowOf_map_subtype_iff (thm3Gen K), map_subgroupOf_eq_of_le hR₁G,
      map_subgroupOf_eq_of_le (le_thm3Gen hM)]
    exact hR₁
  unfold sec4W
  exact le_iSup_of_le (P.subgroupOf (thm3Gen K)) (le_iSup_of_le hP'S (le_iSup_of_le
    ⟨M.subgroupOf (thm3Gen K), ⟨M, hM, rfl⟩, R₁.subgroupOf (thm3Gen K), hR',
      fun x hx => hPR hx, isCyclic_subgroupOf hPG, by rw [relIndex_subgroupOf hR₁G, hidx]⟩ le_rfl))

open scoped Pointwise in
theorem exists_rightConjugate_le_sylow {L : Subgroup G} (Q₀ : Sylow 2 L) {P : Subgroup G}
    (hPL : P ≤ L) (hP : IsPGroup 2 P) :
    ∃ x ∈ L, rightConjugate P x ≤ (Q₀ : Subgroup L).map L.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf L) := hP.comap_subtype
  obtain ⟨Q₁, hQ₁⟩ := hP'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L Q₁ Q₀
  have key : ∀ y : L, y ∈ (Q₀ : Subgroup L) ↔ g⁻¹ * y * g ∈ (Q₁ : Subgroup L) := by
    intro y
    rw [← hg]
    change y ∈ MulAut.conj g • (Q₁ : Subgroup L) ↔ _
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  refine ⟨(g : G)⁻¹, inv_mem g.2, fun y hy => ?_⟩
  rw [mem_rightConjugate_iff, inv_inv] at hy
  have hyL : y ∈ L := by
    have : y = (g : G) * ((g : G)⁻¹ * y * g) * (g : G)⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem g.2 (hPL hy)) (inv_mem g.2)
  refine ⟨⟨y, hyL⟩, (key _).2 (hQ₁ ?_), rfl⟩
  show ((g⁻¹ * ⟨y, hyL⟩ * g : L) : G) ∈ P
  simpa using hy

omit [Finite G] in
theorem not_commute_of_not_mem_rotations {R : Subgroup G} {m : ℕ} (e : R ≃* DihedralGroup m)
    (hm : 3 ≤ m) {x : G} (hx : x ∈ R)
    (hxU : x ∉ zpowers ((e.symm (DihedralGroup.r 1) : R) : G)) :
    x * (e.symm (DihedralGroup.r 1) : G) ≠ (e.symm (DihedralGroup.r 1) : G) * x := by
  have : NeZero m := ⟨by omega⟩
  intro hc
  set x' : R := ⟨x, hx⟩
  have hc' : x' * e.symm (DihedralGroup.r 1) = e.symm (DihedralGroup.r 1) * x' :=
    Subtype.ext hc
  rcases hxe : e x' with i | i
  · apply hxU
    have : x' = e.symm (DihedralGroup.r 1) ^ i.val := by
      rw [← map_pow, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val, ← hxe, e.symm_apply_apply]
    refine ⟨i.val, ?_⟩
    simp only [zpow_natCast]
    rw [← Subgroup.coe_pow, ← this]
  · have h1 := congrArg e hc'
    rw [map_mul, map_mul, e.apply_symm_apply, hxe, DihedralGroup.sr_mul_r,
      DihedralGroup.r_mul_sr] at h1
    have h2 : (2 : ZMod m) = 0 := by
      have := DihedralGroup.sr.inj h1
      linear_combination this
    have h3 : m ∣ 2 := by
      rw [show (2 : ZMod m) = ((2 : ℕ) : ZMod m) by norm_num, ZMod.natCast_eq_zero_iff] at h2
      exact h2
    exact absurd (Nat.le_of_dvd (by norm_num) h3) (by omega)

omit [Finite G] in
theorem relIndex_rightConjugate (A B : Subgroup G) (g : G) :
    (rightConjugate A g).relIndex (rightConjugate B g) = A.relIndex B := by
  unfold rightConjugate
  rw [Subgroup.relIndex_map_map]
  have hker : (MulAut.conj g⁻¹).toMonoidHom.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff _).2 (MulAut.conj g⁻¹).injective
  rw [hker, sup_bot_eq, sup_bot_eq]

theorem isMulCommutative_normalClosure_of_case_two {K R : Subgroup G} (hR : IsSylowOf 2 R K)
    {m : ℕ} (e : R ≃* DihedralGroup m) (hm : 3 ≤ m) (Q₀ : Sylow 2 (thm3Gen K))
    (hWn : (sec4W (thm3MembersIn K) (Q₀ : Subgroup (thm3Gen K))).Normal)
    (hidx : ∀ M' ∈ thm3MembersIn K, (centralizer
      (sec4W (thm3MembersIn K) (Q₀ : Subgroup (thm3Gen K)) : Set (thm3Gen K))).relIndex M' = 2) :
    IsMulCommutative (normalClosure
      ((zpowers ((e.symm (DihedralGroup.r 1) : R) : G) : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero m := ⟨by omega⟩
  set W := (sec4W (thm3MembersIn K) (Q₀ : Subgroup (thm3Gen K))).map (thm3Gen K).subtype
    with hWdef
  set u : G := ((e.symm (DihedralGroup.r 1) : R) : G) with hudef
  set U := zpowers u with hUdef
  have hR0 : IsSylowOf 2 R (oUpperTwoPrime K) :=
    hR.of_le (le_oUpperTwoPrime hR.isPGroup hR.le) (oUpperTwoPrime_le K)
  have huR : u ∈ R := (e.symm (DihedralGroup.r 1)).2
  have hUR : U ≤ R := (zpowers_le).2 huR
  have hRcard : Nat.card R = 2 * m := by rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hUcard : Nat.card U = m := by
    rw [hUdef, Nat.card_zpowers, hudef, Subgroup.orderOf_coe, MulEquiv.orderOf_eq,
      DihedralGroup.orderOf_r_one]
  have hUidx : U.relIndex R = 2 := by
    have h := Subgroup.relIndex_mul_card U R
    rw [inf_eq_left.2 hUR, hUcard, hRcard] at h
    have : 0 < m := by omega
    nlinarith
  have hWconj : ∀ x ∈ thm3Gen K, rightConjugate W x = W := by
    intro x hx
    rw [hWdef, ← map_rightConjugate_subtype _ ⟨x, hx⟩, rightConjugate_eq_of_normal hWn]
  have hidxG : ∀ M ∈ thm3Members K, (centralizer (W : Set G)).relIndex M = 2 := by
    intro M hM
    have := hidx _ ⟨M, hM, rfl⟩
    rwa [centralizer_map_subtype, relIndex_subgroupOf (le_thm3Gen hM)] at this
  have hUW : ∀ g : G, rightConjugate U g ≤ W := by
    intro g
    have hPG : rightConjugate U g ≤ thm3Gen K :=
      (rightConjugate_le_rightConjugate (hUR.trans hR0.le) g).trans (le_thm3Gen ⟨g, rfl⟩)
    have hP2 : IsPGroup 2 (rightConjugate U g) :=
      isPGroup_rightConjugate (hR.isPGroup.to_le hUR) g
    obtain ⟨x, hx, hxS⟩ := exists_rightConjugate_le_sylow Q₀ hPG hP2
    have hcyc : IsCyclic (rightConjugate U (g * x)) := by
      rw [hUdef, rightConjugate, MonoidHom.map_zpowers]
      infer_instance
    have hle := le_map_sec4W (Q₀ : Subgroup (thm3Gen K)) (P := rightConjugate U (g * x))
      (M := rightConjugate (oUpperTwoPrime K) (g * x)) (R₁ := rightConjugate R (g * x))
      (by rwa [← rightConjugate_mul]) ⟨g * x, rfl⟩ (isSylowOf_rightConjugate hR0 _)
      (rightConjugate_le_rightConjugate hUR _) hcyc (by rw [relIndex_rightConjugate, hUidx])
    calc rightConjugate U g = rightConjugate (rightConjugate U (g * x)) x⁻¹ := by
          rw [rightConjugate_mul, mul_inv_cancel_right]
      _ ≤ rightConjugate W x⁻¹ := rightConjugate_le_rightConjugate hle _
      _ = W := hWconj _ (inv_mem hx)
  have hUC : ∀ g : G, rightConjugate U g ≤ centralizer (W : Set G) := by
    intro g
    have hRgK : rightConjugate R g ≤ rightConjugate (oUpperTwoPrime K) g :=
      rightConjugate_le_rightConjugate hR0.le g
    have hidx' := hidxG _ ⟨g, rfl⟩
    have h1 : (centralizer (W : Set G)).relIndex (rightConjugate R g) ≤ 2 := by
      rw [← hidx']
      exact relIndex_le_of_le_right hRgK (by rw [hidx']; norm_num)
    have h2 := Subgroup.relIndex_mul_card (centralizer (W : Set G)) (rightConjugate R g)
    rw [rightConjugate_card, hRcard] at h2
    have h3 : centralizer (W : Set G) ⊓ rightConjugate R g ≤ rightConjugate U g := by
      intro x hx
      rw [mem_inf] at hx
      obtain ⟨hxC, hxR⟩ := hx
      by_contra hxU
      have hx' : g * x * g⁻¹ ∈ R := (mem_rightConjugate_iff R g x).1 hxR
      have hxU' : g * x * g⁻¹ ∉ U := fun h => hxU ((mem_rightConjugate_iff U g x).2 h)
      have hnc := not_commute_of_not_mem_rotations e hm hx' hxU'
      have hw : g⁻¹ * u * g ∈ W := by
        refine hUW g ((mem_rightConjugate_iff U g _).2 ?_)
        rw [show g * (g⁻¹ * u * g) * g⁻¹ = u by group]
        exact mem_zpowers u
      have hcomm := mem_centralizer_iff.1 hxC _ hw
      apply hnc
      calc g * x * g⁻¹ * u = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * u * g) * x) * g⁻¹ := by rw [hcomm]
        _ = u * (g * x * g⁻¹) := by group
    have h4 : Nat.card (centralizer (W : Set G) ⊓ rightConjugate R g : Subgroup G) ≤ m := by
      rw [← hUcard, ← rightConjugate_card U g]
      exact Subgroup.card_le_of_le h3
    have h5 : m ≤ Nat.card (centralizer (W : Set G) ⊓ rightConjugate R g : Subgroup G) := by
      have := Nat.mul_le_mul_right
        (Nat.card (centralizer (W : Set G) ⊓ rightConjugate R g : Subgroup G)) h1
      omega
    have h6 := Subgroup.eq_of_le_of_card_ge h3 (by rw [rightConjugate_card, hUcard]; exact h5)
    rw [← h6]
    exact inf_le_left
  have hle : normalClosure (U : Set G) ≤ W ⊓ centralizer (W : Set G) := by
    refine (closure_le _).2 fun x hx => ?_
    obtain ⟨k, hk, hkx⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hkx
    have hmem : c * k * c⁻¹ ∈ rightConjugate U c⁻¹ := by
      rw [mem_rightConjugate_iff, show c⁻¹ * (c * k * c⁻¹) * c⁻¹⁻¹ = k by group]
      exact hk
    exact ⟨hUW _ hmem, hUC _ hmem⟩
  exact ⟨⟨fun a b => Subtype.ext (mem_centralizer_iff.1 (hle b.2).2 a (hle a.2).1)⟩⟩

omit [Finite G] in
theorem isSylowOf_top_of_sylow {L : Type*} [Group L] [Finite L] (Q : Sylow 2 L) :
    IsSylowOf 2 (Q : Subgroup L) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff, Subgroup.relIndex_top_right]
  exact ⟨le_top, Q.isPGroup', Q.not_dvd_index⟩

theorem asc76Theorem3Large_of_theorem5 (h5 : Asc76Theorem5) : Asc76Theorem3Large := by
  intro G _ _ K hK hgen hO R hR hRd hR4
  obtain ⟨n, hn, ⟨e⟩⟩ := hRd
  have hcard : Nat.card R = 2 * 2 ^ (n - 1) := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hm : 3 ≤ 2 ^ (n - 1) := by omega
  have hRc : ¬ IsMulCommutative R := fun h =>
    DihedralGroup.not_commutative (n := 2 ^ (n - 1)) (by omega) (by omega)
      (isMulCommutative_of_mulEquiv e.symm)
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow 2 (thm3Gen K)))
  rcases h5 (thm3Gen K) (thm3MembersIn K)
      (assumption41_thm3MembersIn hK hO hR ⟨n, hn, ⟨e⟩⟩ hRc) _ (isSylowOf_top_of_sylow Q₀) with
    ⟨_, ⟨M, hM, rfl⟩, hMn⟩ | ⟨hWn, hidx, -⟩
  · exact Or.inl (normal_of_thm3Member_normal hK hgen hO hR hRc hM hMn)
  · refine Or.inr (Or.inr ⟨zpowers ((e.symm (DihedralGroup.r 1) : R) : G),
      (zpowers_le).2 (e.symm (DihedralGroup.r 1)).2, inferInstance, ?_,
      isMulCommutative_normalClosure_of_case_two hR e hm Q₀ hWn hidx⟩)
    have : NeZero (2 ^ (n - 1)) := ⟨by omega⟩
    have hU : Nat.card (zpowers ((e.symm (DihedralGroup.r 1) : R) : G)) = 2 ^ (n - 1) := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, MulEquiv.orderOf_eq,
        DihedralGroup.orderOf_r_one]
    have h := Subgroup.relIndex_mul_card (zpowers ((e.symm (DihedralGroup.r 1) : R) : G)) R
    rw [inf_eq_left.2 ((zpowers_le).2 (e.symm (DihedralGroup.r 1)).2), hU, hcard] at h
    have : 0 < 2 ^ (n - 1) := by omega
    nlinarith

end CFSG.ComponentClassification.Asc76.Sec4
