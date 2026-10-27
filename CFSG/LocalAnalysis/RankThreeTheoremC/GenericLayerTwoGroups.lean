module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerFacts
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseLayer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.GorensteinWalter CFSG.ABGLocalTools
  Subgroup
open scoped MatrixGroups

section Psl2

variable {K : Type} [Field K]

noncomputable abbrev psl2Root (a : K) : PSL2 K :=
  psl2QuotientMap K (sl2UpperUnipotent a)

theorem psl2Root_add (a b : K) : psl2Root (a + b) = psl2Root a * psl2Root b := by
  simp [psl2Root, ← map_mul]

theorem psl2Root_zero : psl2Root (0 : K) = 1 := by simp [psl2Root]

theorem psl2Root_neg (a : K) : psl2Root (-a) = (psl2Root a)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [← psl2Root_add, add_neg_cancel, psl2Root_zero]

theorem psl2Root_nsmul (n : ℕ) (a : K) : psl2Root (n • a) = psl2Root a ^ n := by
  induction n with
  | zero => simp [psl2Root_zero]
  | succ n ih => rw [succ_nsmul, psl2Root_add, ih, pow_succ]

theorem psl2Root_mem (a : K) : psl2Root a ∈ psl2UpperUnipotentSubgroup K :=
  (mem_psl2UpperUnipotentSubgroup_iff _).2 ⟨a, rfl⟩

theorem psl2Root_pow_prime {p : ℕ} [CharP K p] (a : K) : psl2Root a ^ p = 1 := by
  rw [← psl2Root_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, psl2Root_zero]

theorem psl2Root_smul_infinity (a : K) :
    psl2Root a • psl2ProjectiveInfinity K = psl2ProjectiveInfinity K :=
  MulAction.mem_stabilizer_iff.mp (psl2UpperUnipotent_le_borel (psl2Root_mem a))

theorem psl2Root_smul_affine (a x : K) :
    psl2Root a • psl2AffinePoint K x = psl2AffinePoint K (x + a) :=
  psl2UpperUnipotent_smul_affine a x

theorem exists_conj_of_apply_eq [Finite K] {p f : ℕ} [Fact p.Prime] (hK : Nat.card K = p ^ f)
    (α : MulAut (PSL2 K)) (hα : ∀ a : K, α (psl2Root a) = psl2Root a) :
    ∃ b : K, α = MulAut.conj (psl2Root b) := by
  set τ := psl2MulAutProjectiveLine K hK α with hτ
  have hsm : ∀ g x, τ (g • x) = α g • τ x := psl2MulAutProjectiveLine_smul K hK α
  have hinf : τ (psl2ProjectiveInfinity K) = psl2ProjectiveInfinity K := by
    have h1 : psl2Root (1 : K) • τ (psl2ProjectiveInfinity K) = τ (psl2ProjectiveInfinity K) := by
      have := hsm (psl2Root (1 : K)) (psl2ProjectiveInfinity K)
      rw [psl2Root_smul_infinity, hα] at this
      exact this.symm
    exact (psl2UpperUnipotent_one_fixed_iff K _).mp h1
  have h0 : τ (psl2AffinePoint K 0) ≠ psl2ProjectiveInfinity K := fun h =>
    psl2AffinePoint_ne_infinity 0 (τ.injective (h.trans hinf.symm))
  obtain ⟨b, hb, -⟩ := existsUnique_psl2AffinePoint_eq _ h0
  refine ⟨b, psl2MulAutProjectiveLine_injective K hK (Equiv.ext fun z => ?_)⟩
  rw [psl2MulAutProjectiveLine_conj]
  by_cases hz : z = psl2ProjectiveInfinity K
  · rw [hz, hinf, psl2Root_smul_infinity]
  · obtain ⟨a, rfl, -⟩ := existsUnique_psl2AffinePoint_eq z hz
    have h1 := hsm (psl2Root a) (psl2AffinePoint K 0)
    rw [psl2Root_smul_affine, zero_add, hα, ← hb, psl2Root_smul_affine] at h1
    show τ _ = _
    rw [psl2Root_smul_affine, h1, add_comm]

theorem mem_upperUnipotent_of_commute [Finite K] {a : K} (ha : a ≠ 0) {g : PSL2 K}
    (hg : g * psl2Root a = psl2Root a * g) : g ∈ psl2UpperUnipotentSubgroup K := by
  have hginf : g • psl2ProjectiveInfinity K = psl2ProjectiveInfinity K := by
    by_contra hne
    obtain ⟨x, hx, -⟩ := existsUnique_psl2AffinePoint_eq _ hne
    have h1 : psl2Root a • (g • psl2ProjectiveInfinity K) = g • psl2ProjectiveInfinity K := by
      rw [← mul_smul, ← hg, mul_smul, psl2Root_smul_infinity]
    rw [← hx, psl2Root_smul_affine] at h1
    exact ha (by simpa using psl2AffinePoint_injective h1)
  have h0 : g • psl2AffinePoint K 0 ≠ psl2ProjectiveInfinity K := fun h =>
    psl2AffinePoint_ne_infinity 0 (MulAction.injective g (h.trans hginf.symm))
  obtain ⟨b, hb, -⟩ := existsUnique_psl2AffinePoint_eq _ h0
  set g' : PSL2 K := psl2Root (-b) * g with hg'
  have hg'inf : g' • psl2ProjectiveInfinity K = psl2ProjectiveInfinity K := by
    rw [hg', mul_smul, hginf, psl2Root_smul_infinity]
  have hg'zero : g' • psl2ProjectiveZero K = psl2ProjectiveZero K := by
    rw [← psl2AffinePoint_zero, hg', mul_smul, ← hb, psl2Root_smul_affine]
    simp
  obtain ⟨c, hc⟩ := exists_psl2_smul_affine_eq_mul_of_fixes_infinity_zero g' hg'inf hg'zero
  have hcomm : g' * psl2Root a = psl2Root a * g' := by
    rw [hg', mul_assoc, hg, ← mul_assoc, ← mul_assoc, ← psl2Root_add, ← psl2Root_add, add_comm]
  have hca : c * a = a := by
    have h2 : g' • (psl2Root a • psl2AffinePoint K 0) =
        psl2Root a • (g' • psl2AffinePoint K 0) := by
      rw [← mul_smul, ← mul_smul, hcomm]
    rw [psl2Root_smul_affine, hc, hc, psl2Root_smul_affine] at h2
    simpa using psl2AffinePoint_injective h2
  have hc1 : c = 1 := mul_right_cancel₀ ha (by simpa using hca)
  have hg'1 : g' = 1 := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := PSL2ProjectiveLine K)
    intro z
    by_cases hz : z = psl2ProjectiveInfinity K
    · rw [hz, hg'inf, one_smul]
    · obtain ⟨x, rfl, -⟩ := existsUnique_psl2AffinePoint_eq z hz
      rw [hc, hc1, one_mul, one_smul]
  have hgb : g = psl2Root b := by
    have h1 : psl2Root (-b) * g = 1 := hg'1
    rw [mul_eq_one_iff_eq_inv, psl2Root_neg, inv_inj] at h1
    exact h1.symm
  exact hgb ▸ psl2Root_mem b

theorem eq_bot_of_isPGroup_two_of_le_normalizer [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = p ^ 2) (hp2 : p ≠ 2) {W : Subgroup (PSL2 K)} (hW : IsPGroup 2 W)
    (hN : psl2UpperUnipotentSubgroup K ≤ normalizer (W : Set (PSL2 K))) : W = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow : ∀ u : psl2UpperUnipotentSubgroup K, u ^ p = 1 := by
    rintro ⟨u, hu⟩
    obtain ⟨a, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff u).1 hu
    exact Subtype.ext (psl2Root_pow_prime a)
  have hcard : Nat.card (psl2UpperUnipotentSubgroup K) = p ^ 2 := by
    rw [psl2UpperUnipotentSubgroup_card, hK]
  have hcop : ¬ p ∣ Nat.card W := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hW
    rw [hn]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow (Fact.out : p.Prime) h))
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane p
    Fact.out (psl2UpperUnipotentSubgroup K) W hpow hcard hcop hN
  have hUp : IsPGroup p (psl2UpperUnipotentSubgroup K) := IsPGroup.of_card hcard
  have hdisj : Disjoint W (psl2UpperUnipotentSubgroup K) :=
    IsPGroup.disjoint_of_ne 2 p (Ne.symm hp2) W _ hW hUp
  rw [hgen]
  refine le_bot_iff.mp (iSup_le fun u => iSup_le fun hu1 g hg => ?_)
  obtain ⟨a, ha⟩ := (mem_psl2UpperUnipotentSubgroup_iff _).1 u.2
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hu1 (Subtype.ext (by simpa using ha))
  have hgc : g * psl2Root a = psl2Root a * g := by
    have := mem_centralizer_singleton_iff.mp hg.2
    rw [ha] at this
    exact this
  have hgU := mem_upperUnipotent_of_commute ha0 hgc
  exact Subgroup.disjoint_def.mp hdisj hg.1 hgU

end Psl2

section Transport

theorem factorization_card_of_mulEquiv_psl {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ 2) {L : Subgroup G}
    (e : L ≃* PSL2 K) :
    (Nat.card L).factorization p = 2 := by
  obtain ⟨Q, hQ⟩ := psl2UpperUnipotent_isSylow K hK
  have h1 : Nat.card (Q : Subgroup (PSL2 K)) = p ^ (Nat.card (PSL2 K)).factorization p :=
    Sylow.card_eq_multiplicity Q
  rw [hQ, psl2UpperUnipotentSubgroup_card, hK] at h1
  have h2 : (Nat.card (PSL2 K)).factorization p = 2 :=
    (Nat.pow_right_injective (Fact.out : p.Prime).two_le h1).symm
  rwa [← Nat.card_congr e.toEquiv] at h2

variable {G : Type} [Group G]

theorem exists_mulEquiv_of_isSylowOf_psl [Finite G] {p : ℕ} [Fact p.Prime] {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = p ^ 2) {L U : Subgroup G} (e : L ≃* PSL2 K)
    (hU : IsSylowOf p U L) :
    ∃ e' : L ≃* PSL2 K, ∀ g : L, (g : G) ∈ U ↔ e' g ∈ psl2UpperUnipotentSubgroup K := by
  set U'' : Subgroup L := (psl2UpperUnipotentSubgroup K).map e.symm.toMonoidHom with hU''
  have hU''mem : ∀ g : L, g ∈ U'' ↔ e g ∈ psl2UpperUnipotentSubgroup K := by
    intro g
    rw [hU'', Subgroup.mem_map_equiv]
    simp
  have hU''card : Nat.card U'' = p ^ 2 := by
    rw [hU'', Subgroup.card_map_of_injective e.symm.injective, psl2UpperUnipotentSubgroup_card,
      hK]
  have hU''syl : IsSylowOf p (U''.map L.subtype) L := by
    refine isSylowOf_of_card (map_subtype_le _) ?_
    rw [Subgroup.card_map_of_injective L.subtype_injective, hU''card,
      factorization_card_of_mulEquiv_psl hK e]
  obtain ⟨k, hk, hconj⟩ := hU''syl.exists_mem_conj hU
  refine ⟨(MulAut.conj (⟨k, hk⟩ : L)⁻¹).trans e, fun g => ?_⟩
  have h1 := hconj (g : G)
  have h2 : (k⁻¹ * (g : G) * k) = L.subtype ((⟨k, hk⟩ : L)⁻¹ * g * ⟨k, hk⟩) := by simp
  rw [h1, h2, Subgroup.mem_map_iff_mem L.subtype_injective, hU''mem]
  simp

theorem pow_eq_one_of_mem_isSylowOf_psl [Finite G] {p : ℕ} [Fact p.Prime] {K : Type} [Field K]
    [Finite K] [CharP K p] (hK : Nat.card K = p ^ 2) {L U : Subgroup G} (e : L ≃* PSL2 K)
    (hU : IsSylowOf p U L) {u : G} (hu : u ∈ U) : u ^ p = 1 := by
  obtain ⟨e', he'⟩ := exists_mulEquiv_of_isSylowOf_psl hK e hU
  obtain ⟨a, ha⟩ := (mem_psl2UpperUnipotentSubgroup_iff _).1 ((he' ⟨u, hU.le hu⟩).1 hu)
  have h1 : e' (⟨u, hU.le hu⟩ ^ p) = 1 := by rw [map_pow, ha, psl2Root_pow_prime]
  have h2 := e'.injective (h1.trans (map_one e').symm)
  exact congrArg Subtype.val h2

theorem exists_conj_eq_of_centralizes_isSylowOf_psl [Finite G] {p : ℕ} [Fact p.Prime] {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = p ^ 2) {L U : Subgroup G} (e : L ≃* PSL2 K)
    (hU : IsSylowOf p U L) {g : G} (hg : g ∈ normalizer (L : Set G))
    (hgU : ∀ u ∈ U, g * u = u * g) : ∃ u₀ ∈ U, ∀ l ∈ L, g * l * g⁻¹ = u₀ * l * u₀⁻¹ := by
  obtain ⟨e', he'⟩ := exists_mulEquiv_of_isSylowOf_psl hK e hU
  let β : MulAut L := L.normalizerMonoidHom ⟨g, hg⟩
  have hβ : ∀ l : L, ((β l : L) : G) = g * l * g⁻¹ := fun l => rfl
  let α : MulAut (PSL2 K) := MulAut.congr e' β
  have hα : ∀ a : K, α (psl2Root a) = psl2Root a := by
    intro a
    have hmem : psl2Root a ∈ psl2UpperUnipotentSubgroup K := psl2Root_mem a
    set l : L := e'.symm (psl2Root a) with hl
    have hlU : (l : G) ∈ U := (he' l).2 (by simpa [hl] using hmem)
    have hβl : β l = l := Subtype.ext (by rw [hβ, hgU _ hlU]; group)
    change e' (β (e'.symm (psl2Root a))) = psl2Root a
    rw [← hl, hβl, hl, e'.apply_symm_apply]
  obtain ⟨b, hb⟩ := exists_conj_of_apply_eq hK α hα
  set u₀ : L := e'.symm (psl2Root b) with hu₀
  have hu₀U : (u₀ : G) ∈ U := (he' u₀).2 (by simpa [hu₀] using psl2Root_mem b)
  refine ⟨u₀, hu₀U, fun l hl => ?_⟩
  have h1 : β ⟨l, hl⟩ = u₀ * ⟨l, hl⟩ * u₀⁻¹ := by
    apply e'.injective
    have : α (e' ⟨l, hl⟩) = e' (β ⟨l, hl⟩) := by
      change e' (β (e'.symm (e' ⟨l, hl⟩))) = _
      rw [e'.symm_apply_apply]
    rw [← this, hb, MulAut.conj_apply, map_mul, map_mul, map_inv, hu₀, e'.apply_symm_apply]
  exact congrArg Subtype.val h1

theorem eq_bot_of_isPGroup_two_of_le_normalizer_isSylowOf_psl [Finite G] {p : ℕ} [Fact p.Prime]
    {K : Type} [Field K] [Finite K] [CharP K p] (hK : Nat.card K = p ^ 2) (hp2 : p ≠ 2)
    {L U : Subgroup G} (e : L ≃* PSL2 K) (hU : IsSylowOf p U L) {W : Subgroup G} (hWL : W ≤ L)
    (hW : IsPGroup 2 W) (hN : U ≤ normalizer (W : Set G)) : W = ⊥ := by
  obtain ⟨e', he'⟩ := exists_mulEquiv_of_isSylowOf_psl hK e hU
  set W' : Subgroup (PSL2 K) := (W.subgroupOf L).map e'.toMonoidHom with hW'
  have hW'p : IsPGroup 2 W' := (hW.comap_subtype (K := L)).map e'.toMonoidHom
  have hW'mem : ∀ w : L, e' w ∈ W' ↔ (w : G) ∈ W := fun w => by
    rw [hW', Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    exact Iff.rfl
  have hN' : psl2UpperUnipotentSubgroup K ≤ normalizer (W' : Set (PSL2 K)) := by
    intro ũ hũ
    obtain ⟨u, rfl⟩ := e'.surjective ũ
    have hu : (u : G) ∈ U := (he' u).2 hũ
    have hu' := Subgroup.mem_normalizer_iff.mp (hN hu)
    rw [Subgroup.mem_normalizer_iff]
    intro w
    obtain ⟨w₀, rfl⟩ := e'.surjective w
    rw [← map_inv, ← map_mul, ← map_mul, hW'mem, hW'mem]
    simpa using hu' (w₀ : G)
  have hbot := eq_bot_of_isPGroup_two_of_le_normalizer hK hp2 hW'p hN'
  rw [eq_bot_iff]
  intro w hw
  have hwL : w ∈ L := hWL hw
  have : e' ⟨w, hwL⟩ ∈ W' := (hW'mem _).2 hw
  rw [hbot, Subgroup.mem_bot] at this
  have h1 := e'.injective (this.trans (map_one e').symm)
  exact congrArg Subtype.val h1

theorem eq_bot_of_isPGroup_two_of_le_normalizer_layer [Finite G] {p : ℕ} [Fact p.Prime]
    {K : Type} [Field K] [Finite K] [CharP K p] (hK : Nat.card K = p ^ 2) (hp2 : p ≠ 2)
    {C L U W : Subgroup G} (e : L ≃* PSL2 K) (hU : IsSylowOf p U L) (hLC : L ≤ C)
    (hCL : C ≤ normalizer (L : Set G)) (hodd : ¬ 2 ∣ Nat.card ↥(C ⊓ centralizer (L : Set G)))
    (hWC : W ≤ C) (hW : IsPGroup 2 W) (hN : U ≤ normalizer (W : Set G)) : W = ⊥ := by
  have hUL : U ≤ normalizer (L : Set G) := hU.le.trans Subgroup.le_normalizer
  have h1 : W ⊓ L = ⊥ := eq_bot_of_isPGroup_two_of_le_normalizer_isSylowOf_psl hK hp2 e hU
    inf_le_right hW.to_inf_left (le_normalizer_inf hN hUL)
  have hcomm : ∀ w ∈ W, ∀ u ∈ U, w * u = u * w := by
    intro w hw u hu
    have hwu : w * u * w⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hCL (hWC hw)) u).mp (hU.le hu)
    have hcL : w * u * w⁻¹ * u⁻¹ ∈ L := L.mul_mem hwu (L.inv_mem (hU.le hu))
    have hcW : w * u * w⁻¹ * u⁻¹ ∈ W := by
      have h2 : u * w⁻¹ * u⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hN hu) w⁻¹).mp (W.inv_mem hw)
      simpa [mul_assoc] using W.mul_mem hw h2
    have h3 : w * u * w⁻¹ * u⁻¹ ∈ W ⊓ L := ⟨hcW, hcL⟩
    rw [h1, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
    exact h3
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨u₀, hu₀U, hu₀⟩ := exists_conj_eq_of_centralizes_isSylowOf_psl hK e hU
    (hCL (hWC hw)) (hcomm w hw)
  have hvL : u₀⁻¹ * w ∈ centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h2 := hu₀ l hl
    calc l * (u₀⁻¹ * w) = u₀⁻¹ * (u₀ * l * u₀⁻¹) * w := by group
      _ = u₀⁻¹ * (w * l * w⁻¹) * w := by rw [h2]
      _ = u₀⁻¹ * w * l := by group
  have hu₀C : u₀ ∈ C := hLC (hU.le hu₀U)
  have hvC : u₀⁻¹ * w ∈ C ⊓ centralizer (L : Set G) :=
    ⟨C.mul_mem (C.inv_mem hu₀C) (hWC hw), hvL⟩
  obtain ⟨n, hn⟩ := hW ⟨w, hw⟩
  have hwn : w ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  have hu₀L : u₀ ∈ L := hU.le hu₀U
  have hcop : Nat.Coprime p (2 ^ n) :=
    Nat.Coprime.pow_right n ((Nat.coprime_primes Fact.out Nat.prime_two).mpr hp2)
  have hcomm₀ : Commute u₀ (u₀⁻¹ * w) := Subgroup.mem_centralizer_iff.mp hvL u₀ hu₀L
  have hpow : u₀ ^ (2 ^ n) = 1 := by
    have h2 : (u₀ * (u₀⁻¹ * w)) ^ (2 ^ n) = u₀ ^ (2 ^ n) * (u₀⁻¹ * w) ^ (2 ^ n) :=
      hcomm₀.mul_pow _
    rw [mul_inv_cancel_left, hwn] at h2
    have h3 : u₀ ^ (2 ^ n) = ((u₀⁻¹ * w) ^ (2 ^ n))⁻¹ :=
      eq_inv_of_mul_eq_one_left h2.symm
    refine eq_one_of_commute_of_mulEquiv_psl_two e (L.pow_mem hu₀L _) fun h hh => ?_
    rw [h3]
    have h4 : (u₀⁻¹ * w) ^ (2 ^ n) ∈ centralizer (L : Set G) :=
      (centralizer (L : Set G)).pow_mem hvL _
    have h5 := (centralizer (L : Set G)).inv_mem h4
    rw [Subgroup.mem_centralizer_iff] at h5
    exact h5 h hh
  have hu₀1 : u₀ = 1 := by
    have h1 : orderOf u₀ ∣ p :=
      orderOf_dvd_of_pow_eq_one (pow_eq_one_of_mem_isSylowOf_psl hK e hU hu₀U)
    have h2 : orderOf u₀ ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hpow
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  rw [hu₀1, inv_one, one_mul] at hvC
  have hcop2 : Nat.Coprime (2 ^ n) (Nat.card ↥(C ⊓ centralizer (L : Set G))) :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  have hwo : orderOf (⟨w, hvC⟩ : ↥(C ⊓ centralizer (L : Set G))) = 1 := by
    refine Nat.eq_one_of_dvd_coprimes hcop2 (orderOf_dvd_of_pow_eq_one ?_) (orderOf_dvd_natCard _)
    exact Subtype.ext hwn
  have := orderOf_eq_one_iff.mp hwo
  exact congrArg Subtype.val this

theorem eq_bot_of_isPGroup_two_of_le_normalizer_of_isGenericPoint [Finite G]
    (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {x : G} (hx : IsGenericPoint p P M x) (h5 : 5 ≤ p) {m : ℕ} (hm : 2 ≤ m)
    (e : rankThreeLayer (centralizer ({x} : Set G)) ≃* PSL(2, GaloisField p m))
    {W : Subgroup G} (hWC : W ≤ centralizer ({x} : Set G)) (hW : IsPGroup 2 W)
    (hN : ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) ⊓
      rankThreeLayer (centralizer ({x} : Set G)) ≤ normalizer (W : Set G)) : W = ⊥ := by
  obtain ⟨hxP, hxL, hsyl, hrk⟩ := id hx
  obtain ⟨-, hx1, hxp, -, hxCM⟩ := hxL
  obtain ⟨hm2, -⟩ := eq_two_of_isSylowOf_mulEquiv_psl hsyl (rankThreeLayer_le _)
    (le_normalizer_rankThreeLayer _) ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩ hx1 hxp
    (fun c hc => mem_centralizer_singleton_iff.mp hc) hrk.le hm e
  subst hm2
  have hK : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
  have hLM := not_rankThreeLayer_le_of_mulEquiv_psl hS hU0 hp hM hxCM hsyl hm e
  have hodd := not_two_dvd_card_inf_centralizer_layer hS hD1 hp hM hx hLM hm e
  have hU : IsSylowOf p (((P : Subgroup G) ⊓ centralizer ({x} : Set G)) ⊓
      rankThreeLayer (centralizer ({x} : Set G))) (rankThreeLayer (centralizer ({x} : Set G))) :=
    hsyl.inf_of_le_normalizer (rankThreeLayer_le _) (le_normalizer_rankThreeLayer _)
  exact eq_bot_of_isPGroup_two_of_le_normalizer_layer hK (by omega) e hU (rankThreeLayer_le _)
    (le_normalizer_rankThreeLayer _) hodd hWC hW hN

end Transport

end CFSG.LocalAnalysis.RankThreeTheoremC
