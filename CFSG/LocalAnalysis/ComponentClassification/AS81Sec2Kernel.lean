module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Spread
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step23
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step26Easy

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

namespace Sec2

omit [Finite G] in
theorem card_range_conjPermHom {N : Subgroup G} {Ps : Set (Subgroup G)}
    (hX : N ≤ conjSetStab Ps) (hI : InducesA5 N Ps) : Nat.card (conjPermHom hX).range = 60 := by
  have hPi : {σ : Equiv.Perm ↥Ps | ∃ n ∈ N, ∀ V : ↥Ps,
      ((σ V : ↥Ps) : Subgroup G) = rightConjugate (V : Subgroup G) n} =
      ((conjPermHom hX).range : Set (Equiv.Perm ↥Ps)) := by
    ext σ
    constructor
    · rintro ⟨n, hn, hσ⟩
      refine ⟨⟨n⁻¹, inv_mem hn⟩, Equiv.ext fun V => Subtype.ext ?_⟩
      rw [hσ, conjPermHom_apply]
      simp
    · rintro ⟨n, rfl⟩
      exact ⟨(n : G)⁻¹, inv_mem n.2, fun V => conjPermHom_apply hX n V⟩
  have h := hI.2.2
  rw [hPi] at h
  exact h

theorem exists_fin_four_of_ncard_eq_five {α : Type*} {s : Set α} (hs : s.ncard = 5) {a : α}
    (ha : a ∈ s) : ∃ W : Fin 4 → α, W 0 = a ∧ (∀ i, W i ∈ s) ∧ ∀ i j, i ≠ j → W i ≠ W j := by
  have h1 : (s \ {a}).ncard = 4 := by rw [Set.ncard_sdiff_singleton_of_mem ha, hs]
  have hne1 : (s \ {a}).Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [h1]; norm_num)
  obtain ⟨b, hb⟩ := hne1
  have h2 : ((s \ {a}) \ {b}).ncard = 3 := by rw [Set.ncard_sdiff_singleton_of_mem hb, h1]
  have hne2 : ((s \ {a}) \ {b}).Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [h2]; norm_num)
  obtain ⟨c, hc⟩ := hne2
  have h3 : (((s \ {a}) \ {b}) \ {c}).ncard = 2 := by rw [Set.ncard_sdiff_singleton_of_mem hc, h2]
  have hne3 : (((s \ {a}) \ {b}) \ {c}).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [h3]; norm_num)
  obtain ⟨d, hd⟩ := hne3
  simp only [Set.mem_sdiff, Set.mem_singleton_iff] at hb hc hd
  have hab : a ≠ b := fun h => hb.2 h.symm
  have hac : a ≠ c := fun h => hc.1.2 h.symm
  have had : a ≠ d := fun h => hd.1.1.2 h.symm
  have hbc : b ≠ c := fun h => hc.2 h.symm
  have hbd : b ≠ d := fun h => hd.1.2 h.symm
  have hcd : c ≠ d := fun h => hd.2 h.symm
  refine ⟨![a, b, c, d], rfl, fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i
    · exact ha
    · exact hb.1
    · exact hc.1.1
    · exact hd.1.1.1
  · fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | exact hab | exact hab.symm | exact hac | exact hac.symm | exact had | exact had.symm
        | exact hbc | exact hbc.symm | exact hbd | exact hbd.symm | exact hcd | exact hcd.symm

omit [Finite G] in
theorem fourLines_inf {V Z : Subgroup G} {W : Fin 4 → Subgroup G} (hV : IsElemAbelian 2 V)
    (hV64 : Nat.card V = 64) (hZ4 : Nat.card Z = 4) (hZV : Z ≤ V) (hZW : ∀ i, Z ≤ W i)
    (hcard : ∀ i, Nat.card (V ⊓ W i : Subgroup G) = 16)
    (hinf : ∀ i j, i ≠ j → W i ⊓ W j = Z) : FourLines V Z (fun i => V ⊓ W i) where
  elem := hV
  card := hV64
  cardZ := hZ4
  Z_le i := le_inf hZV (hZW i)
  le _ := inf_le_left
  cardW := hcard
  inf i j hij := by
    rw [inf_inf_inf_comm, inf_idem, hinf i j hij, inf_eq_right.mpr hZV]

omit [Finite G] in
theorem mem_of_mem_sup_of_odd_orderOf {Q O : Subgroup G} (hQ : ∀ q ∈ Q, q * q = 1)
    (hOQ : O ≤ centralizer (Q : Set G)) (hO : Odd (Nat.card O)) {w : G} (hw : w ∈ Q ⊔ O)
    (hwo : Odd (orderOf w)) : w ∈ O := by
  have hON : O ≤ normalizer (Q : Set G) := hOQ.trans (centralizer_le_normalizer _)
  have hw' : w ∈ ((Q ⊔ O : Subgroup G) : Set G) := hw
  rw [coe_mul_of_right_le_normalizer_left Q O hON] at hw'
  obtain ⟨q, hq, o, ho, rfl⟩ := hw'
  show q * o ∈ O
  have hqo : Commute q o := mem_centralizer_iff.mp (hOQ ho) q hq
  obtain ⟨m, hm⟩ := hwo
  have h1 : (q * o) ^ (2 * m + 1) = 1 := by rw [← hm, pow_orderOf_eq_one]
  rw [hqo.mul_pow] at h1
  have hq1 : q ^ (2 * m + 1) = q := by
    rw [pow_succ, pow_mul, sq, hQ q hq, one_pow, one_mul]
  rw [hq1] at h1
  have hqO : q ∈ O := by
    have : q = (o ^ (2 * m + 1))⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact O.inv_mem (O.pow_mem ho _)
  have hq2 : orderOf q ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hQ q hq)
  have hqodd : orderOf q ∣ Nat.card O := by
    have := Subgroup.orderOf_dvd_natCard O hqO
    exact this
  have hq1' : orderOf q = 1 := by
    have h3 := Nat.dvd_gcd hq2 hqodd
    rw [Nat.Coprime.gcd_eq_one ((Nat.coprime_two_left).mpr hO), Nat.dvd_one] at h3
    exact h3
  rw [orderOf_eq_one_iff.mp hq1', one_mul]
  exact ho

omit [Finite G] in
theorem conjPermHom_eq_one_iff {Ps : Set (Subgroup G)} {X : Subgroup G}
    (hX : X ≤ conjSetStab Ps) (k : ↥X) :
    conjPermHom hX k = 1 ↔ ∀ V ∈ Ps, (k : G) ∈ normalizer (V : Set G) := by
  constructor
  · intro h V hV
    have h1 := congrArg (fun σ : Equiv.Perm ↥Ps => ((σ ⟨V, hV⟩ : ↥Ps) : Subgroup G)) h
    simp only [conjPermHom_apply, Equiv.Perm.one_apply] at h1
    simpa using inv_mem ((rightConjugate_eq_self_iff V _).mp h1)
  · intro h
    exact Equiv.ext fun V => Subtype.ext ((rightConjugate_eq_self_iff _ _).mpr
      (inv_mem (h V V.2)))

omit [Finite G] in
theorem closure_pow_two_sec2H (E F : Subgroup G) :
    closure {q : ↥(sec2H E F) | ∃ j : ℕ, q ^ 2 ^ j = 1} = ⊤ := by
  set H := sec2H E F with hHdef
  have h2 : ∀ (X : Subgroup G), IsPGroup 2 X →
      X.subgroupOf H ≤ closure {q : ↥H | ∃ j : ℕ, q ^ 2 ^ j = 1} := by
    intro X hX r hr
    apply Subgroup.subset_closure
    obtain ⟨j, hj⟩ := hX ⟨(r : G), mem_subgroupOf.mp hr⟩
    exact ⟨j, Subtype.ext (by simpa using congrArg Subtype.val hj)⟩
  have hPH : sec2P E ≤ H := le_sup_left
  have hPFH : sec2P F ≤ H := le_sup_right
  have htop : (sec2P E).subgroupOf H ⊔ (sec2P F).subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hPH hPFH]
    exact Subgroup.subgroupOf_self H
  rw [eq_top_iff, ← htop]
  exact sup_le (h2 _ (isPGroup_sec2P E)) (h2 _ (isPGroup_sec2P F))

omit [Finite G] in
theorem closure_pow_two_eq_top_of_surjective {Γ Γ' : Type*} [Group Γ] [Group Γ'] (f : Γ →* Γ')
    (hf : Function.Surjective f) (h : closure {q : Γ | ∃ j : ℕ, q ^ 2 ^ j = 1} = ⊤) :
    closure {q : Γ' | ∃ j : ℕ, q ^ 2 ^ j = 1} = ⊤ := by
  rw [eq_top_iff, ← map_top_of_surjective f hf, ← h, MonoidHom.map_closure]
  refine closure_mono ?_
  rintro _ ⟨q, ⟨j, hj⟩, rfl⟩
  exact ⟨j, by rw [← map_pow, hj, map_one]⟩

end Sec2

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))

include h11 hE16 hF hL hodd

theorem sec2H_le_centralizer_sec2Z : sec2H E F ≤ centralizer (sec2Z A E F : Set G) := by
  have hZEA : (sec2Z A E F : Set G) ⊆ ((E ⊓ A : Subgroup G) : Set G) := by
    rw [hF.sec2Z_eq]
    exact fun z hz => ⟨hz.1.1, hz.2⟩
  have hZFA : (sec2Z A E F : Set G) ⊆ ((F ⊓ A : Subgroup G) : Set G) := by
    rw [hF.sec2Z_eq]
    exact fun z hz => ⟨hz.1.2, hz.2⟩
  exact sup_le ((sec2P_le_centralizer_inf h11 hE16 hF hL hodd).trans (centralizer_le hZEA))
    ((sec2P_le_centralizer_inf h11 hE16 hF.symm hL hodd).trans (centralizer_le hZFA))

theorem mem_centralizer_sec2H_of_odd_orderOf {w : G}
    (hw : w ∈ centralizerMod (sec2H E F) (sec2S A R E F) (sec2Z A E F))
    (hwo : Odd (orderOf w)) : w ∈ centralizer (sec2H E F : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hwH, -, hwS⟩ := mem_centralizerMod.mp hw
  obtain ⟨hES, hFS⟩ := le_sec2S_and_le_sec2S (A := A) (R := R) hF
  have hZE : sec2Z A E F ≤ E := by rw [hF.sec2Z_eq]; exact inf_le_left.trans inf_le_left
  have hZ2 : ∀ z ∈ sec2Z A E F, z * z = 1 := fun z hz => by
    rw [← sq]
    exact hF.elemE.2 z (hZE hz)
  have hwC : w ∈ centralizer (sec2S A R E F : Set G) :=
    Sec2.mem_centralizer_of_odd_orderOf hZ2 (sec2H_le_centralizer_sec2Z h11 hE16 hF hL hodd hwH)
      (fun s hs => by simpa [mul_assoc] using hwS s hs) hwo
  have key : ∀ {E₁ F₁ : Subgroup G}, Frame G A A R g E₁ F₁ → E₁ ≤ sec2S A R E F →
      sec2P E₁ ≤ centralizer ({w} : Set G) := by
    intro E₁ F₁ hF₁ hE₁S
    obtain ⟨hCEO, -, -⟩ := centralizer_eq_sup_oddCoreIn hF₁ hL hodd
    set O := AS76b.oddCoreIn (centralizer (E₁ : Set G)) with hO
    have hwE : w ∈ centralizer (E₁ : Set G) := centralizer_le hE₁S hwC
    have hwO : w ∈ O := by
      rw [hCEO] at hwE
      exact Sec2.mem_of_mem_sup_of_odd_orderOf (fun q hq => by rw [← sq]; exact hF₁.elemE.2 q hq)
        (AS76b.oddCoreIn_le _) (AS76b.odd_card_oddCoreIn _) hwE hwo
    have hP2 := Sec2.isPGroup_sec2P E₁
    have hON : O ≤ normalizer (E₁ : Set G) :=
      (AS76b.oddCoreIn_le _).trans (centralizer_le_normalizer _)
    have hNP := Sec2.normalizer_le_normalizer_sec2P E₁
    have hPN := Sec2.sec2P_le E₁
    have hNO : normalizer (E₁ : Set G) ≤ normalizer (O : Set G) := fun n hn =>
      AS76b.normalizer_le_normalizer_oddCoreIn _ (normalizer_le_normalizer_centralizer E₁ hn)
    have hOP : O ⊓ sec2P E₁ = ⊥ := AS76b.oddCoreIn_inf_eq_bot hP2
    intro p hp
    rw [mem_centralizer_singleton_iff]
    have h1 : w * p * w⁻¹ * p⁻¹ ∈ sec2P E₁ :=
      (sec2P E₁).mul_mem ((mem_normalizer_iff.mp (hNP (hON hwO)) p).mp hp) ((sec2P E₁).inv_mem hp)
    have h2 : w * p * w⁻¹ * p⁻¹ ∈ O := by
      have := O.mul_mem hwO ((mem_normalizer_iff.mp (hNO (hPN hp)) w⁻¹).mp (O.inv_mem hwO))
      simpa [mul_assoc] using this
    have h3 : w * p * w⁻¹ * p⁻¹ = 1 := by
      have h4 : w * p * w⁻¹ * p⁻¹ ∈ O ⊓ sec2P E₁ := ⟨h2, h1⟩
      rwa [hOP, mem_bot] at h4
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h3)).symm
  have hle : sec2H E F ≤ centralizer ({w} : Set G) := sup_le (key hF hES) (key hF.symm hFS)
  rw [mem_centralizer_iff]
  intro q hq
  exact (mem_centralizer_singleton_iff.mp (hle hq))

variable {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F) {h : G} (hh : h ∈ sec2P E)
  (hhS : h ∉ sec2S A R E F) (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))
  (h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E)))

include hx hxS hh hhS h4 h4'

theorem planes_sec2S_facts :
    (∀ V ∈ conjSet E (sec2H E F) ∪ conjSet F (sec2H E F), IsElemAbelian 2 V ∧
      Nat.card V = 64 ∧ sec2Z A E F ≤ V ∧ V ≤ sec2S A R E F) ∧
    (∀ V ∈ conjSet E (sec2H E F), ∀ W ∈ conjSet E (sec2H E F), V ≠ W →
      V ⊓ W = sec2Z A E F) ∧
    (∀ V ∈ conjSet F (sec2H E F), ∀ W ∈ conjSet F (sec2H E F), V ≠ W →
      V ⊓ W = sec2Z A E F) ∧
    ∀ V ∈ conjSet E (sec2H E F), ∀ W ∈ conjSet F (sec2H E F),
      Nat.card (V ⊓ W : Subgroup G) = 16 := by
  have hSc := sec2S_comm h11 hE16 hF hL hodd
  have hU := planes_sec2S_eq_conjSet_union h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hHc : sec2H F E = sec2H E F := sup_comm _ _
  refine ⟨fun V hV => ?_, fun V hV W hW hne => ?_, fun V hV W hW hne => ?_, fun V hV W hW => ?_⟩
  · have hV' : V ∈ {V | V ∈ planes E F ∧ V ≤ sec2S A R E F} := by
      rw [hU]
      exact Or.symm hV
    obtain ⟨he, hc⟩ := isElemAbelian_and_card_of_mem_planes hF hV'.1
    exact ⟨he, hc, sec2Z_le_of_mem_planes h11 hE16 hF hL hodd hV'.1 hV'.2, hV'.2⟩
  · have hV' : V ∈ conjSet E (sec2H F E) := hHc ▸ hV
    have hW' : W ∈ conjSet E (sec2H F E) := hHc ▸ hW
    have := (inf_eq_sec2Z_and_card_inf h11 hE16 hF.symm hL hodd hh (hSc ▸ hhS) hx (hSc ▸ hxS)
      h4' h4 hV').1 W hW' hne
    rwa [sec2Z_comm] at this
  · exact (inf_eq_sec2Z_and_card_inf h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hV).1 W hW hne
  · rw [inf_comm]
    exact (inf_eq_sec2Z_and_card_inf h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hW).2 V hV

theorem fourLines_of_mem_conjSet_F {F' : Subgroup G} (hF' : F' ∈ conjSet F (sec2H E F))
    {W : Fin 4 → Subgroup G} (hW : ∀ i, W i ∈ conjSet E (sec2H E F))
    (hWne : ∀ i j, i ≠ j → W i ≠ W j) : Sec2.FourLines F' (sec2Z A E F) (fun i => F' ⊓ W i) := by
  obtain ⟨hpl, hEE, -, hEF⟩ := planes_sec2S_facts h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  obtain ⟨he, hc, hZ, -⟩ := hpl F' (Or.inr hF')
  refine Sec2.fourLines_inf he hc (hF.card_sec2Z hodd) hZ
    (fun i => (hpl _ (Or.inl (hW i))).2.2.1) (fun i => ?_)
    (fun i j hij => hEE _ (hW i) _ (hW j) (hWne i j hij))
  rw [inf_comm]
  exact hEF _ (hW i) _ hF'

theorem fourLines_of_mem_conjSet_E {E' : Subgroup G} (hE' : E' ∈ conjSet E (sec2H E F))
    {W : Fin 4 → Subgroup G} (hW : ∀ i, W i ∈ conjSet F (sec2H E F))
    (hWne : ∀ i j, i ≠ j → W i ≠ W j) : Sec2.FourLines E' (sec2Z A E F) (fun i => E' ⊓ W i) := by
  obtain ⟨hpl, -, hFF, hEF⟩ := planes_sec2S_facts h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  obtain ⟨he, hc, hZ, -⟩ := hpl E' (Or.inl hE')
  exact Sec2.fourLines_inf he hc (hF.card_sec2Z hodd) hZ
    (fun i => (hpl _ (Or.inr (hW i))).2.2.1) (fun i => hEF _ hE' _ (hW i))
    (fun i j hij => hFF _ (hW i) _ (hW j) (hWne i j hij))

theorem ncard_conjSet_sec2H :
    (conjSet E (sec2H E F)).ncard = 5 ∧ (conjSet F (sec2H E F)).ncard = 5 := by
  have hSc := sec2S_comm h11 hE16 hF hL hodd
  constructor
  · rw [conjSet_E_sec2H_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4']
    exact ncard_sec2Fam h11 hE16 hF.symm hL hodd hh (hSc ▸ hhS)
  · rw [conjSet_F_sec2H_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4']
    exact ncard_sec2Fam h11 hE16 hF hL hodd hx hxS

theorem mem_sec2S_of_pow_two {n : G} (hn : n ∈ sec2H E F)
    (hfix : ∀ V ∈ conjSet E (sec2H E F), n ∈ normalizer (V : Set G)) {m : ℕ}
    (hm : n ^ 2 ^ m = 1) : n ∈ sec2S A R E F := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := sec2H E F with hHdef
  obtain ⟨hE5, hF5⟩ := ncard_conjSet_sec2H h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hHS := sec2H_le_normalizer_sec2S h11 hE16 hF hL hodd
  have hHZ := sec2H_le_normalizer_sec2Z h11 hE16 hF hL hodd
  have hHQ : H ≤ Sec2.conjSetStab (conjSet F H) := Sec2.le_conjSetStab fun k hk V ⟨θ, hθ, hV⟩ =>
    ⟨θ * k, mul_mem hθ hk, by rw [hV, rightConjugate_mul]⟩
  set σ := Sec2.conjPermHom hHQ ⟨n, hn⟩ with hσ
  have hσm : σ ^ 2 ^ m = 1 := by
    have h1 : (⟨n, hn⟩ : ↥H) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hm)
    rw [hσ, ← map_pow, h1, map_one]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hσm)
  have hσ2 : IsPGroup 2 (zpowers σ) := IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hQcard : Nat.card ↥(conjSet F H) = 5 := by rw [Nat.card_coe_set_eq, hF5]
  obtain ⟨V, hV⟩ := hσ2.nonempty_fixed_point_of_prime_not_dvd_card ↥(conjSet F H)
    (by rw [hQcard]; decide)
  have hσV : σ V = V := hV ⟨σ, mem_zpowers σ⟩
  have hnV : n ∈ normalizer ((V : Subgroup G) : Set G) := by
    have h1 := congrArg Subtype.val hσV
    rw [hσ, Sec2.conjPermHom_apply] at h1
    simpa using inv_mem ((rightConjugate_eq_self_iff _ _).mp h1)
  obtain ⟨θ, hθ, hVθ⟩ := V.2
  have hconj : ∀ W : Subgroup G, n ∈ normalizer (rightConjugate W θ : Set G) →
      θ * n * θ⁻¹ ∈ normalizer (W : Set G) := fun W hW => by
    rw [← AschbacherTheorem3.rightConjugate_normalizer, mem_rightConjugate_iff] at hW
    exact hW
  have hn'F : θ * n * θ⁻¹ ∈ normalizer (F : Set G) := hconj F (hVθ ▸ hnV)
  have hn'E : ∀ W ∈ conjSet E H, θ * n * θ⁻¹ ∈ normalizer (W : Set G) := by
    rintro W ⟨θ', hθ', rfl⟩
    refine hconj _ (hfix _ ⟨θ' * θ, mul_mem hθ' hθ, ?_⟩)
    rw [rightConjugate_mul]
  have hn'H : θ * n * θ⁻¹ ∈ H := mul_mem (mul_mem hθ hn) (inv_mem hθ)
  have hn'm : (θ * n * θ⁻¹) ^ 2 ^ m = 1 := by rw [conj_pow, hm, mul_one, mul_inv_cancel]
  have hEmem : E ∈ conjSet E H := ⟨1, one_mem _, (rightConjugate_one E).symm⟩
  have hFmem : F ∈ conjSet F H := ⟨1, one_mem _, (rightConjugate_one F).symm⟩
  obtain ⟨W, -, hWmem, hWne⟩ := Sec2.exists_fin_four_of_ncard_eq_five hE5 hEmem
  have hL4 := fourLines_of_mem_conjSet_F h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hFmem hWmem
    hWne
  have hcen := hL4.forall_mem_of_pow_two (hHZ hn'H)
    (fun i => inf_normalizer_le_normalizer_inf ⟨hn'F, hn'E _ (hWmem i)⟩) hn'm
  have hX : θ * n * θ⁻¹ ∈ centralizer (sec2Z A E F : Set G) ⊓
      centralizerMod ⊤ (R ⊔ sec2Z A E F) (sec2Z A E F) ⊓ normalizer (E : Set G) ⊓
        normalizer (F : Set G) := by
    refine ⟨⟨⟨sec2H_le_centralizer_sec2Z h11 hE16 hF hL hodd hn'H,
      mem_centralizerMod.mpr ⟨mem_top _, hHZ hn'H, fun w hw => ?_⟩⟩, hn'E E hEmem⟩, hn'F⟩
    rw [hF.sup_sec2Z] at hw
    have := hcen w hw.2
    simpa [mul_assoc] using this
  have hsyl := isSylowOf_sec2S h11 hE16 hF hL hodd
  obtain ⟨k', -, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hn'm)
  have hz2 : IsPGroup 2 (zpowers (θ * n * θ⁻¹)) :=
    IsPGroup.of_card (n := k') (by rw [Nat.card_zpowers, hk'])
  have hQ2 := hsyl.isPGroup.to_sup_of_normal_left' hz2 (zpowers_le.mpr (hHS hn'H))
  have hQS := hsyl.eq_of_le le_sup_left (sup_le hsyl.le (zpowers_le.mpr hX)) hQ2
  have hn'S : θ * n * θ⁻¹ ∈ sec2S A R E F := hQS ▸ mem_sup_right (mem_zpowers _)
  have := (mem_normalizer_iff.mp (inv_mem (hHS hθ)) _).mp hn'S
  simpa [mul_assoc] using this

theorem forall_mem_normalizer_F {n : G} (hn : n ∈ sec2H E F)
    (hfix : ∀ V ∈ conjSet E (sec2H E F), n ∈ normalizer (V : Set G)) :
    ∀ V ∈ conjSet F (sec2H E F), n ∈ normalizer (V : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := sec2H E F with hHdef
  have hHP : H ≤ Sec2.conjSetStab (conjSet E H) := Sec2.le_conjSetStab fun k hk V ⟨θ, hθ, hV⟩ =>
    ⟨θ * k, mul_mem hθ hk, by rw [hV, rightConjugate_mul]⟩
  have hHQ : H ≤ Sec2.conjSetStab (conjSet F H) := Sec2.le_conjSetStab fun k hk V ⟨θ, hθ, hV⟩ =>
    ⟨θ * k, mul_mem hθ hk, by rw [hV, rightConjugate_mul]⟩
  set ψE := Sec2.conjPermHom hHP with hψE
  set ψF := Sec2.conjPermHom hHQ with hψF
  have hSc := sec2S_comm h11 hE16 hF hL hodd
  have hIF : InducesA5 H (conjSet F H) := by
    have := inducesA5_sec2H h11 hE16 hF.symm hL hodd hh (hSc ▸ hhS) hx (hSc ▸ hxS) h4' h4
    rwa [show sec2H F E = sec2H E F from sup_comm _ _] at this
  have hQ5 : Nat.card ↥(conjSet F H) = 5 := hIF.1
  have : Fintype ↥(conjSet F H) := Fintype.ofFinite _
  have hcard := Sec2.card_range_conjPermHom hHQ hIF
  have hperm : Nat.card (Equiv.Perm ↥(conjSet F H)) = 120 := by
    rw [Nat.card_perm, hQ5]
    decide
  have hidx : ψF.range.index = 2 := by
    have := ψF.range.index_mul_card
    rw [hcard, hperm] at this
    omega
  have hrange : ψF.range = alternatingGroup ↥(conjSet F H) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx
  have hsimple : IsSimpleGroup ↥ψF.range :=
    (MulEquiv.isSimpleGroup_congr (MulEquiv.subgroupCongr hrange)).mpr
      (alternatingGroup.isSimpleGroup (by rw [hQ5]))
  have hM : (ψE.ker.map ψF.rangeRestrict).Normal :=
    (ψE.normal_ker).map ψF.rangeRestrict ψF.rangeRestrict_surjective
  have hnker : (⟨n, hn⟩ : ↥H) ∈ ψE.ker := (Sec2.conjPermHom_eq_one_iff hHP _).mpr hfix
  obtain ⟨hpl, -⟩ := planes_sec2S_facts h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hSN : ∀ V ∈ conjSet F H, sec2S A R E F ≤ normalizer (V : Set G) := fun V hV =>
    sec2S_le_normalizer_of_sec2Z_le h11 hE16 hF hL hodd (hpl V (Or.inr hV)).2.2.1
      (hpl V (Or.inr hV)).2.2.2
  rcases hsimple.eq_bot_or_eq_top_of_normal (ψE.ker.map ψF.rangeRestrict) with hbot | htop
  · have h1 : ψF.rangeRestrict ⟨n, hn⟩ ∈ ψE.ker.map ψF.rangeRestrict := mem_map_of_mem _ hnker
    rw [hbot, mem_bot] at h1
    have h2 : ψF ⟨n, hn⟩ = 1 := by simpa using congrArg Subtype.val h1
    exact (Sec2.conjPermHom_eq_one_iff hHQ _).mp h2
  · exfalso
    obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card' (G := ↥ψF.range) 2 (by rw [hcard]; norm_num)
    have hτM : τ ∈ ψE.ker.map ψF.rangeRestrict := htop ▸ mem_top τ
    obtain ⟨k, hk, hkτ⟩ := mem_map.mp hτM
    obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
    have hk'ker : k ^ b ∈ ψE.ker := pow_mem hk b
    have hk'2 : ((k ^ b : ↥H) : G) ^ 2 ^ a = 1 := by
      have : (k ^ b) ^ 2 ^ a = 1 := by rw [← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
      simpa using congrArg Subtype.val this
    have hk'S := mem_sec2S_of_pow_two h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' (k ^ b).2
      ((Sec2.conjPermHom_eq_one_iff hHP _).mp hk'ker) hk'2
    have hψk' : ψF (k ^ b) = 1 := (Sec2.conjPermHom_eq_one_iff hHQ _).mpr fun V hV =>
      hSN V hV hk'S
    have hτb : τ ^ b = 1 := by
      rw [← hkτ, ← map_pow]
      exact Subtype.ext (by simpa using hψk')
    have hdvd := orderOf_dvd_of_pow_eq_one hτb
    rw [hτ] at hdvd
    exact (Nat.not_even_iff_odd.mpr hb) (even_iff_two_dvd.mpr hdvd)

theorem forall_mem_of_fix_E {n : G} (hn : n ∈ sec2H E F)
    (hfix : ∀ V ∈ conjSet E (sec2H E F), n ∈ normalizer (V : Set G)) {E' F' : Subgroup G}
    (hE' : E' ∈ conjSet E (sec2H E F)) (hF' : F' ∈ conjSet F (sec2H E F)) {v : G}
    (hv : v ∈ E' ⊓ F') (hvZ : v ∉ sec2Z A E F) (hnv : v⁻¹ * (n⁻¹ * v * n) ∈ sec2Z A E F) :
    ∀ e ∈ E', e⁻¹ * (n⁻¹ * e * n) ∈ sec2Z A E F := by
  obtain ⟨-, hF5⟩ := ncard_conjSet_sec2H h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hfixF := forall_mem_normalizer_F h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hn hfix
  obtain ⟨W, hW0, hWmem, hWne⟩ := Sec2.exists_fin_four_of_ncard_eq_five hF5 hF'
  have hL4 := fourLines_of_mem_conjSet_E h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hE' hWmem hWne
  have hv' : v ∈ E' ⊓ W 0 := by rw [hW0]; exact hv
  exact hL4.forall_mem_of_fix (sec2H_le_normalizer_sec2Z h11 hE16 hF hL hodd hn)
    (fun i => inf_normalizer_le_normalizer_inf ⟨hfix E' hE', hfixF _ (hWmem i)⟩) hv' hvZ hnv

theorem forall_mem_of_fix_F {n : G} (hn : n ∈ sec2H E F)
    (hfix : ∀ V ∈ conjSet E (sec2H E F), n ∈ normalizer (V : Set G)) {E' F' : Subgroup G}
    (hE' : E' ∈ conjSet E (sec2H E F)) (hF' : F' ∈ conjSet F (sec2H E F)) {v : G}
    (hv : v ∈ F' ⊓ E') (hvZ : v ∉ sec2Z A E F) (hnv : v⁻¹ * (n⁻¹ * v * n) ∈ sec2Z A E F) :
    ∀ f ∈ F', f⁻¹ * (n⁻¹ * f * n) ∈ sec2Z A E F := by
  obtain ⟨hE5, -⟩ := ncard_conjSet_sec2H h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hfixF := forall_mem_normalizer_F h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hn hfix
  obtain ⟨W, hW0, hWmem, hWne⟩ := Sec2.exists_fin_four_of_ncard_eq_five hE5 hE'
  have hL4 := fourLines_of_mem_conjSet_F h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hF' hWmem hWne
  have hv' : v ∈ F' ⊓ W 0 := by rw [hW0]; exact hv
  exact hL4.forall_mem_of_fix (sec2H_le_normalizer_sec2Z h11 hE16 hF hL hodd hn)
    (fun i => inf_normalizer_le_normalizer_inf ⟨hfixF F' hF', hfix _ (hWmem i)⟩) hv' hvZ hnv

theorem exists_mem_inf_not_mem_sec2Z_of_mem {V W : Subgroup G} (hV : V ∈ conjSet E (sec2H E F))
    (hW : W ∈ conjSet F (sec2H E F)) : ∃ v ∈ V ⊓ W, v ∉ sec2Z A E F := by
  obtain ⟨-, -, -, hEF⟩ := planes_sec2S_facts h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  by_contra hno
  push Not at hno
  have h1 := Subgroup.card_le_of_le (show V ⊓ W ≤ sec2Z A E F from hno)
  rw [hEF V hV W hW, hF.card_sec2Z hodd] at h1
  omega

theorem forall_mem_sec2S_of_forall_mem_F {n : G} (hn : n ∈ sec2H E F)
    (hfix : ∀ V ∈ conjSet E (sec2H E F), n ∈ normalizer (V : Set G))
    (hcen : ∀ f ∈ F, f⁻¹ * (n⁻¹ * f * n) ∈ sec2Z A E F) :
    ∀ s ∈ sec2S A R E F, s⁻¹ * (n⁻¹ * s * n) ∈ sec2Z A E F := by
  set H := sec2H E F with hHdef
  have hFmem : F ∈ conjSet F H := ⟨1, one_mem _, (rightConjugate_one F).symm⟩
  have hEmem : E ∈ conjSet E H := ⟨1, one_mem _, (rightConjugate_one E).symm⟩
  have hE' : ∀ E' ∈ conjSet E H, ∀ e ∈ E', e⁻¹ * (n⁻¹ * e * n) ∈ sec2Z A E F := by
    intro E' hE'
    obtain ⟨v, hv, hvZ⟩ :=
      exists_mem_inf_not_mem_sec2Z_of_mem h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hE' hFmem
    exact forall_mem_of_fix_E h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hn hfix hE' hFmem hv hvZ
      (hcen v hv.2)
  have hSx := (rightConjugate_inf_eq_and_sec2S_eq h11 hE16 hF hL hodd hx hxS).2
  have hExmem : rightConjugate E x ∈ conjSet E H := ⟨x, mem_sup_right hx, rfl⟩
  have hExS : rightConjugate E x ≤ sec2S A R E F := hSx ▸ le_sup_right
  have hExN : rightConjugate E x ≤ normalizer (E : Set G) :=
    hExS.trans (sec2S_le_normalizer_left hF hL hodd)
  have hZ := centerIn_sec2S_eq h11 hE16 hF hL hodd
  intro s hs
  have hs' : s ∈ ((E ⊔ rightConjugate E x : Subgroup G) : Set G) := hSx ▸ hs
  rw [coe_mul_of_right_le_normalizer_left E _ hExN] at hs'
  obtain ⟨e, he, e', he', rfl⟩ := hs'
  have h1 := hE' E hEmem e he
  have h2 := hE' _ hExmem e' he'
  have he'Z : e' ∈ normalizer (sec2Z A E F : Set G) := by
    rw [← hZ]
    exact mem_normalizer_centerIn (le_normalizer (hExS he'))
  have e₁ : (e * e')⁻¹ * (n⁻¹ * (e * e') * n) =
      (e'⁻¹ * (e⁻¹ * (n⁻¹ * e * n)) * e') * (e'⁻¹ * (n⁻¹ * e' * n)) := by group
  rw [e₁]
  refine mul_mem ?_ h2
  have := (mem_normalizer_iff.mp (inv_mem he'Z) _).mp h1
  rwa [inv_inv] at this

theorem forall_mem_sec2S_cube {n : G} (hn : n ∈ sec2H E F)
    (hfix : ∀ V ∈ conjSet E (sec2H E F), n ∈ normalizer (V : Set G)) :
    ∀ s ∈ sec2S A R E F, s⁻¹ * ((n ^ 3)⁻¹ * s * n ^ 3) ∈ sec2Z A E F := by
  set H := sec2H E F with hHdef
  obtain ⟨hE5, -⟩ := ncard_conjSet_sec2H h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hfixF := forall_mem_normalizer_F h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hn hfix
  have hFmem : F ∈ conjSet F H := ⟨1, one_mem _, (rightConjugate_one F).symm⟩
  have hEmem : E ∈ conjSet E H := ⟨1, one_mem _, (rightConjugate_one E).symm⟩
  obtain ⟨W, -, hWmem, hWne⟩ := Sec2.exists_fin_four_of_ncard_eq_five hE5 hEmem
  have hL4 := fourLines_of_mem_conjSet_F h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hFmem hWmem hWne
  have hc := hL4.forall_mem_cube (sec2H_le_normalizer_sec2Z h11 hE16 hF hL hodd hn)
    (fun i => inf_normalizer_le_normalizer_inf ⟨hfixF F hFmem, hfix _ (hWmem i)⟩)
  exact forall_mem_sec2S_of_forall_mem_F h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' (pow_mem hn 3)
    (fun V hV => pow_mem (hfix V hV) 3) hc

theorem commutator_mem_centralizerMod {k : G} (hk : k ∈ sec2H E F)
    (hfix : ∀ V ∈ conjSet E (sec2H E F), k ∈ normalizer (V : Set G)) {p : G}
    (hp : p ∈ sec2H E F) :
    k⁻¹ * p⁻¹ * k * p ∈ centralizerMod (sec2H E F) (sec2S A R E F) (sec2Z A E F) := by
  set H := sec2H E F with hHdef
  set K₀ := H ⊓ ⨅ V ∈ conjSet E H, normalizer (V : Set G) with hK₀def
  have hK₀ : ∀ g, g ∈ K₀ ↔ g ∈ H ∧ ∀ V ∈ conjSet E H, g ∈ normalizer (V : Set G) := fun g => by
    simp only [hK₀def, mem_inf, mem_iInf]
  set N := centralizerMod H (sec2S A R E F) (sec2Z A E F) with hNdef
  have hHZ := sec2H_le_normalizer_sec2Z h11 hE16 hF hL hodd
  have hHS := sec2H_le_normalizer_sec2S h11 hE16 hF hL hodd
  have hSc := sec2S_comm h11 hE16 hF hL hodd
  have hEmem : E ∈ conjSet E H := ⟨1, one_mem _, (rightConjugate_one E).symm⟩
  have hFmem : F ∈ conjSet F H := ⟨1, one_mem _, (rightConjugate_one F).symm⟩
  have hcK : ∀ y ∈ K₀, ∀ q ∈ H, y⁻¹ * q⁻¹ * y * q ∈ K₀ := by
    intro y hy q hq
    obtain ⟨hyH, hyV⟩ := (hK₀ y).mp hy
    refine (hK₀ _).mpr ⟨mul_mem (mul_mem (mul_mem (inv_mem hyH) (inv_mem hq)) hyH) hq,
      fun V hV => ?_⟩
    have hVq : rightConjugate V q⁻¹ ∈ conjSet E H := by
      obtain ⟨θ, hθ, rfl⟩ := hV
      exact ⟨θ * q⁻¹, mul_mem hθ (inv_mem hq), rightConjugate_mul E θ q⁻¹⟩
    have h1 := hyV _ hVq
    rw [← AschbacherTheorem3.rightConjugate_normalizer, mem_rightConjugate_iff, inv_inv] at h1
    have e : y⁻¹ * q⁻¹ * y * q = y⁻¹ * (q⁻¹ * y * q) := by group
    rw [e]
    exact mul_mem (inv_mem (hyV V hV)) h1
  have hN : ∀ c ∈ K₀, (∀ f ∈ F, f⁻¹ * (c⁻¹ * f * c) ∈ sec2Z A E F) → c ∈ N := by
    intro c hc hcF
    obtain ⟨hcH, hcV⟩ := (hK₀ c).mp hc
    have := forall_mem_sec2S_of_forall_mem_F h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hcH hcV hcF
    exact mem_centralizerMod.mpr ⟨hcH, hHZ hcH, fun s hs => by simpa [mul_assoc] using this s hs⟩
  have hcen : ∀ (X : Subgroup G) (y q : G), y ∈ normalizer (X : Set G) →
      q ∈ centralizer (X : Set G) → ∀ a ∈ X,
        (y⁻¹ * q⁻¹ * y * q)⁻¹ * a * (y⁻¹ * q⁻¹ * y * q) = a := by
    intro X y q hy hq a ha
    have ha₁ : y * a * y⁻¹ ∈ X := (mem_normalizer_iff.mp hy a).mp ha
    have hqb : ∀ b ∈ X, q * b * q⁻¹ = b := fun b hb => by
      rw [← mem_centralizer_iff.mp hq b hb]
      group
    have hqb' : ∀ b ∈ X, q⁻¹ * b * q = b := fun b hb => by
      rw [mul_assoc, mem_centralizer_iff.mp hq b hb]
      group
    calc (y⁻¹ * q⁻¹ * y * q)⁻¹ * a * (y⁻¹ * q⁻¹ * y * q)
        = q⁻¹ * (y⁻¹ * (q * (y * a * y⁻¹) * q⁻¹) * y) * q := by group
      _ = q⁻¹ * (y⁻¹ * (y * a * y⁻¹) * y) * q := by rw [hqb _ ha₁]
      _ = q⁻¹ * a * q := by group
      _ = a := hqb' a ha
  have hP : sec2P E ≤ centralizerMod H K₀ N := by
    intro q hq
    have hqH : q ∈ H := mem_sup_left hq
    refine mem_centralizerMod.mpr ⟨hqH, Sec2.mem_normalizer_centralizerMod (le_normalizer hqH)
      (hHS hqH) (hHZ hqH), fun y hy => ?_⟩
    have hc := hcK y hy q hqH
    obtain ⟨hcH, hcV⟩ := (hK₀ _).mp hc
    obtain ⟨-, hyV⟩ := (hK₀ y).mp hy
    obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
    have hcEA := hcen (E ⊓ A) y q (hD.normalizer_le_normalizer (hyV E hEmem))
      (sec2P_le_centralizer_inf h11 hE16 hF hL hodd hq)
    have hF₀mem : sec2F0 A E x ∈ conjSet F H := by
      rw [conjSet_F_sec2H_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4']
      exact Set.mem_insert _ _
    have hEF₀ : E ⊓ sec2F0 A E x = E ⊓ A := by
      rw [inf_comm]
      exact sec2F0_inf_eq h11 hE16 hF hL hodd hx hxS
    obtain ⟨v, hv, hvZ⟩ :=
      exists_mem_inf_not_mem_sec2Z_of_mem h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hEmem hF₀mem
    have hvEA : v ∈ E ⊓ A := hEF₀ ▸ hv
    have hcE := forall_mem_of_fix_E h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hcH hcV hEmem
      hF₀mem hv hvZ (by rw [hcEA v hvEA, inv_mul_cancel]; exact one_mem _)
    obtain ⟨v', hv', hv'Z⟩ :=
      exists_mem_inf_not_mem_sec2Z_of_mem h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hEmem hFmem
    have hcF := forall_mem_of_fix_F h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hcH hcV hEmem hFmem
      (show v' ∈ F ⊓ E from ⟨hv'.2, hv'.1⟩) hv'Z (hcE v' hv'.1)
    exact hN _ hc hcF
  have hPF : sec2P F ≤ centralizerMod H K₀ N := by
    intro q hq
    have hqH : q ∈ H := mem_sup_right hq
    refine mem_centralizerMod.mpr ⟨hqH, Sec2.mem_normalizer_centralizerMod (le_normalizer hqH)
      (hHS hqH) (hHZ hqH), fun y hy => ?_⟩
    have hc := hcK y hy q hqH
    obtain ⟨hcH, hcV⟩ := (hK₀ _).mp hc
    obtain ⟨hyH, hyV⟩ := (hK₀ y).mp hy
    have hyF := forall_mem_normalizer_F h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hyH hyV F hFmem
    obtain ⟨hD', -⟩ := exists_pointsData h11 hE16 hF.symm hL hodd
    have hcFA := hcen (F ⊓ A) y q (hD'.normalizer_le_normalizer hyF)
      (sec2P_le_centralizer_inf h11 hE16 hF.symm hL hodd hq)
    have hE₀mem : sec2F0 A F h ∈ conjSet E H := by
      rw [conjSet_E_sec2H_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4']
      exact Set.mem_insert _ _
    have hFE₀ : sec2F0 A F h ⊓ F = F ⊓ A := sec2F0_inf_eq h11 hE16 hF.symm hL hodd hh (hSc ▸ hhS)
    obtain ⟨v, hv, hvZ⟩ :=
      exists_mem_inf_not_mem_sec2Z_of_mem h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hE₀mem hFmem
    have hvFA : v ∈ F ⊓ A := hFE₀ ▸ hv
    have hcF := forall_mem_of_fix_F h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hcH hcV hE₀mem hFmem
      (show v ∈ F ⊓ sec2F0 A F h from ⟨hv.2, hv.1⟩) hvZ
      (by rw [hcFA v hvFA, inv_mul_cancel]; exact one_mem _)
    exact hN _ hc hcF
  exact (mem_centralizerMod.mp (sup_le hP hPF hp)).2.2 k ((hK₀ k).mpr ⟨hk, hfix⟩)

theorem mem_centralizerMod_of_forall {k : G} (hk : k ∈ sec2H E F)
    (hfix : ∀ V ∈ conjSet E (sec2H E F), k ∈ normalizer (V : Set G)) :
    k ∈ centralizerMod (sec2H E F) (sec2S A R E F) (sec2Z A E F) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := sec2H E F with hHdef
  set N := centralizerMod H (sec2S A R E F) (sec2Z A E F) with hNdef
  have hNH : N ≤ H := fun n hn => (mem_centralizerMod.mp hn).1
  have hHS := sec2H_le_normalizer_sec2S h11 hE16 hF hL hodd
  have hHZ := sec2H_le_normalizer_sec2Z h11 hE16 hF hL hodd
  have hN' : (N.subgroupOf H).Normal := (normal_subgroupOf_iff hNH).mpr fun n q hn hq =>
    (mem_normalizer_iff.mp (Sec2.mem_normalizer_centralizerMod (le_normalizer hq) (hHS hq)
      (hHZ hq)) n).mp hn
  obtain ⟨hE5, -⟩ := ncard_conjSet_sec2H h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have : Finite ↥(conjSet E H) := (Set.finite_of_ncard_ne_zero (by rw [hE5]; norm_num)).to_subtype
  have hHP : H ≤ Sec2.conjSetStab (conjSet E H) := Sec2.le_conjSetStab fun k hk V ⟨θ, hθ, hV⟩ =>
    ⟨θ * k, mul_mem hθ hk, by rw [hV, rightConjugate_mul]⟩
  set ψ := Sec2.conjPermHom hHP with hψ
  obtain ⟨hpl, -⟩ := planes_sec2S_facts h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hNψ : N.subgroupOf H ≤ ψ.ker := fun n hn => by
    rw [MonoidHom.mem_ker, Sec2.conjPermHom_eq_one_iff]
    intro V hV
    obtain ⟨-, -, hZV, hVS⟩ := hpl V (Or.inl hV)
    obtain ⟨-, -, hnS⟩ := mem_centralizerMod.mp (mem_subgroupOf.mp hn)
    have hinv : (n : G)⁻¹ ∈ normalizer (V : Set G) := Sec2.mem_normalizer_of_forall_conj_mem
      fun v hv => by
        have h1 : (n : G)⁻¹ * v * (n : G)⁻¹⁻¹ = v * (v⁻¹ * (n : G)⁻¹ * v * n) := by group
        rw [h1]
        exact V.mul_mem hv (hZV (hnS v (hVS hv)))
    simpa using inv_mem hinv
  set f := QuotientGroup.lift (N.subgroupOf H) ψ hNψ with hf
  have hrange : f.range = ψ.range := by
    ext σ
    constructor
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H q => exact ⟨q, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨QuotientGroup.mk q, rfl⟩
  have hIE : InducesA5 H (conjSet E H) :=
    inducesA5_sec2H h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hcard := Sec2.card_range_conjPermHom hHP hIE
  have hsq : ¬ 3 ^ 2 ∣ Nat.card f.range := by
    rw [hrange, hcard]
    decide
  have hcen : ∀ m ∈ f.ker, (∃ j : ℕ, m ^ 3 ^ j = 1) → m ∈ center (↥H ⧸ N.subgroupOf H) := by
    intro m hm _
    rw [QuotientGroup.ker_lift] at hm
    obtain ⟨k₁, hk₁, rfl⟩ := mem_map.mp hm
    rw [mem_center_iff]
    intro γ
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective γ
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      mem_subgroupOf]
    have hk₁fix := (Sec2.conjPermHom_eq_one_iff hHP k₁).mp hk₁
    have := commutator_mem_centralizerMod h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' k₁.2 hk₁fix q.2
    simpa [mul_assoc] using this
  have hz : QuotientGroup.mk' (N.subgroupOf H) ⟨k, hk⟩ ∈ f.ker := by
    rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, hf, QuotientGroup.lift_mk]
    exact (Sec2.conjPermHom_eq_one_iff hHP _).mpr hfix
  have hzp : ∃ j : ℕ, (QuotientGroup.mk' (N.subgroupOf H) ⟨k, hk⟩) ^ 3 ^ j = 1 := by
    refine ⟨1, ?_⟩
    rw [pow_one, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
    have hcube := forall_mem_sec2S_cube h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hk hfix
    refine mem_centralizerMod.mpr ⟨by simpa using pow_mem hk 3, by simpa using pow_mem (hHZ hk) 3,
      fun s hs => ?_⟩
    have := hcube s hs
    simpa [mul_assoc] using this
  have h1 := Sec2.eq_one_of_mem_ker_of_pow_prime (p := 3) (by norm_num)
    (Sec2.closure_pow_two_eq_top_of_surjective (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) (Sec2.closure_pow_two_sec2H E F)) f hsq hcen hz hzp
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
  exact h1

theorem eq_one_of_forall_of_pow_prime {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {k : G}
    (hk : k ∈ sec2H E F) (hfix : ∀ V ∈ conjSet E (sec2H E F), k ∈ normalizer (V : Set G))
    {j : ℕ} (hkj : k ^ p ^ j = 1) : k = 1 := by
  classical
  set H := sec2H E F with hHdef
  obtain ⟨hE5, -⟩ := ncard_conjSet_sec2H h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have : Finite ↥(conjSet E H) := (Set.finite_of_ncard_ne_zero (by rw [hE5]; norm_num)).to_subtype
  have hHP : H ≤ Sec2.conjSetStab (conjSet E H) := Sec2.le_conjSetStab fun k hk V ⟨θ, hθ, hV⟩ =>
    ⟨θ * k, mul_mem hθ hk, by rw [hV, rightConjugate_mul]⟩
  set ψ := Sec2.conjPermHom hHP with hψ
  have hIE : InducesA5 H (conjSet E H) :=
    inducesA5_sec2H h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hcard := Sec2.card_range_conjPermHom hHP hIE
  have hsq : ¬ p ^ 2 ∣ Nat.card ψ.range := by
    rw [hcard]
    intro h
    have hle : p ^ 2 ≤ 60 := Nat.le_of_dvd (by norm_num) h
    have hp7 : p ≤ 7 := by nlinarith
    have hpp := hp.out
    revert h hp2 hpp
    interval_cases p <;> decide
  have hcen : ∀ m ∈ ψ.ker, (∃ i : ℕ, m ^ p ^ i = 1) → m ∈ center ↥H := by
    rintro m hm ⟨i, hi⟩
    have hmfix := (Sec2.conjPermHom_eq_one_iff hHP m).mp hm
    have hmN := mem_centralizerMod_of_forall h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' m.2 hmfix
    have hmi : (m : G) ^ p ^ i = 1 := by simpa using congrArg Subtype.val hi
    have hodd' : Odd (orderOf (m : G)) := by
      obtain ⟨l, -, hl⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hmi)
      rw [hl]
      exact (hp.out.eq_two_or_odd'.resolve_left hp2).pow
    have hc := mem_centralizer_sec2H_of_odd_orderOf h11 hE16 hF hL hodd hmN hodd'
    rw [mem_center_iff]
    intro q
    exact Subtype.ext (mem_centralizer_iff.mp hc q q.2)
  have h1 := Sec2.eq_one_of_mem_ker_of_pow_prime hp2 (Sec2.closure_pow_two_sec2H E F) ψ hsq hcen
    (z := ⟨k, hk⟩) ((Sec2.conjPermHom_eq_one_iff hHP _).mpr hfix)
    ⟨j, Subtype.ext (by simpa using hkj)⟩
  simpa using congrArg Subtype.val h1

theorem mem_sec2S_of_forall {n : G} (hn : n ∈ sec2H E F)
    (hfix : ∀ V ∈ conjSet E (sec2H E F), n ∈ normalizer (V : Set G)) : n ∈ sec2S A R E F := by
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
  have hb1 : b = 1 := by
    by_contra hb1
    obtain ⟨p, hp, hpb⟩ := Nat.exists_prime_and_dvd hb1
    have : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := fun h => by
      rw [h] at hpb
      exact (Nat.not_even_iff_odd.mpr hb) (even_iff_two_dvd.mpr hpb)
    have hpn : p ∣ orderOf n := hab ▸ dvd_mul_of_dvd_right hpb _
    have hord := orderOf_pow_orderOf_div (orderOf_pos n).ne' hpn
    have h1 := eq_one_of_forall_of_pow_prime h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hp2
      (pow_mem hn (orderOf n / p)) (fun V hV => pow_mem (hfix V hV) _) (j := 1) (by
        rw [pow_one]
        have := pow_orderOf_eq_one (n ^ (orderOf n / p))
        rwa [hord] at this)
    rw [h1, orderOf_one] at hord
    exact hp.one_lt.ne hord
  rw [hb1, mul_one] at hab
  exact mem_sec2S_of_pow_two h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hn hfix
    (by rw [← hab, pow_orderOf_eq_one])

theorem exists_hom_alternatingGroup_ker_eq :
    ∃ φ : ↥(sec2H E F) →* alternatingGroup (Fin 5), Function.Surjective φ ∧
      φ.ker = (sec2S A R E F).subgroupOf (sec2H E F) := by
  classical
  set H := sec2H E F with hHdef
  have hHP : H ≤ Sec2.conjSetStab (conjSet E H) := Sec2.le_conjSetStab fun k hk V ⟨θ, hθ, hV⟩ =>
    ⟨θ * k, mul_mem hθ hk, by rw [hV, rightConjugate_mul]⟩
  set ψ := Sec2.conjPermHom hHP with hψ
  have hIE : InducesA5 H (conjSet E H) :=
    inducesA5_sec2H h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hP5 : Nat.card ↥(conjSet E H) = 5 := hIE.1
  have : Fintype ↥(conjSet E H) := Fintype.ofFinite _
  have hcard := Sec2.card_range_conjPermHom hHP hIE
  have hperm : Nat.card (Equiv.Perm ↥(conjSet E H)) = 120 := by
    rw [Nat.card_perm, hP5]
    decide
  have hidx : ψ.range.index = 2 := by
    have := ψ.range.index_mul_card
    rw [hcard, hperm] at this
    omega
  have hrange : ψ.range = alternatingGroup ↥(conjSet E H) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx
  have e : ↥(conjSet E H) ≃ Fin 5 :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_eq_nat_card, hP5])
  have hmem : ∀ q : ↥H, ψ q ∈ alternatingGroup ↥(conjSet E H) := fun q =>
    hrange ▸ (⟨q, rfl⟩ : ψ q ∈ ψ.range)
  set ψ' := ψ.codRestrict (alternatingGroup ↥(conjSet E H)) hmem with hψ'
  refine ⟨(Equiv.altCongrHom e).toMonoidHom.comp ψ', ?_, ?_⟩
  · refine (Equiv.altCongrHom e).surjective.comp ?_
    rintro ⟨τ, hτ⟩
    obtain ⟨q, hq⟩ := (hrange ▸ hτ : τ ∈ ψ.range)
    exact ⟨q, Subtype.ext hq⟩
  · obtain ⟨hpl, -⟩ := planes_sec2S_facts h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
    ext q
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, mem_subgroupOf]
    have hq1 : ψ' q = 1 ↔ ψ q = 1 := by
      rw [hψ', ← Subtype.coe_inj]
      rfl
    rw [hq1, Sec2.conjPermHom_eq_one_iff]
    constructor
    · exact mem_sec2S_of_forall h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' q.2
    · intro hqS V hV
      exact sec2S_le_normalizer_of_sec2Z_le h11 hE16 hF hL hodd (hpl V (Or.inl hV)).2.2.1
        (hpl V (Or.inl hV)).2.2.2 hqS

theorem sec2H_inf_centralizer_sec2S_eq :
    sec2H E F ⊓ centralizer (sec2S A R E F : Set G) = sec2Z A E F := by
  have hZ := centerIn_sec2S_eq h11 hE16 hF hL hodd
  obtain ⟨hpl, -⟩ := planes_sec2S_facts h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  refine le_antisymm (fun w hw => ?_) (fun z hz => ?_)
  · have hwS := mem_sec2S_of_forall h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hw.1 fun V hV =>
      centralizer_le_normalizer _ (centralizer_le (hpl V (Or.inl hV)).2.2.2 hw.2)
    rw [← hZ]
    exact ⟨hwS, hw.2⟩
  · rw [← hZ] at hz
    exact ⟨sec2S_le_sec2H hF hz.1, hz.2⟩

end Frame

end CFSG.ComponentClassification.AS81
