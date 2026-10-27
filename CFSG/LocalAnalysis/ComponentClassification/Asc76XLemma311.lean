module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma38

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isMulCommutative_of_forall_sq_eq_one {T : Subgroup G} (h : ∀ x ∈ T, x ^ 2 = 1) :
    IsMulCommutative T := by
  have hinv : ∀ x ∈ T, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_left (by rw [← sq]; exact h x hx)
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  simp only [coe_mul]
  have hab := hinv _ (mul_mem a.2 b.2)
  rw [mul_inv_rev, hinv _ a.2, hinv _ b.2] at hab
  exact hab.symm

omit [Finite G] in
@[expose] noncomputable def conjAutOf (Y : Subgroup G) {t : G} (ht : t ∈ normalizer (Y : Set G)) :
    MulAut Y :=
  ((MulAut.conj t).subgroupMap Y).trans (MulEquiv.subgroupCongr (by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (mem_normalizer_iff.mp ht z).mp hz
    · intro hy
      refine ⟨t⁻¹ * y * t, ?_, by simp [mul_assoc]⟩
      have := (mem_normalizer_iff.mp (inv_mem ht) y).mp hy
      simpa using this))

omit [Finite G] in
theorem conjAutOf_apply (Y : Subgroup G) {t : G} (ht : t ∈ normalizer (Y : Set G)) (y : Y) :
    ((conjAutOf Y ht y : Y) : G) = t * y * t⁻¹ := rfl

theorem mem_of_mem_normalizer_of_isSylowOf {R M : Subgroup G} (hR : IsSylowOf 2 R M) {k : G}
    (hkM : k ∈ M) (hkN : k ∈ normalizer (R : Set G)) {i : ℕ} (hki : k ^ (2 ^ i) = 1) :
    k ∈ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR' := isSylowOf_iff_card.mp hR
  have hR2 : IsPGroup 2 R := IsPGroup.of_card hR'.2
  have hk2 : IsPGroup 2 (zpowers k) := isPGroup_zpowers_of_two_element hki
  have hkR : zpowers k ≤ normalizer (R : Set G) := (zpowers_le).mpr hkN
  have hP : IsPGroup 2 ↥(zpowers k ⊔ R) := hk2.to_sup_of_normal_right' hR2 hkR
  have hle : zpowers k ⊔ R ≤ M := sup_le ((zpowers_le).mpr hkM) hR'.1
  have heq := eq_of_isSylowOf_le hR hP hle le_sup_right
  exact heq ▸ mem_sup_left (mem_zpowers k)

omit [Finite G] in
theorem nclIn_rightConjugate {X L : Subgroup G} (hLX : L ≤ X) {x : G} (hx : x ∈ X) :
    nclIn X (rightConjugate L x) = nclIn X L := by
  have key : ∀ {L' : Subgroup G} {y : G}, L' ≤ X → y ∈ X → nclIn X (rightConjugate L' y) ≤
      nclIn X L' := by
    intro L' y hL' hy
    rw [nclIn, nclIn]
    refine map_mono (normalClosure_le_normal fun z hz => ?_)
    have hz' : (z : G) ∈ rightConjugate L' y := hz
    rw [mem_rightConjugate_iff] at hz'
    have hmem : (⟨y, hy⟩ * z * ⟨y, hy⟩⁻¹ : X) ∈ L'.subgroupOf X := by
      rw [mem_subgroupOf]
      simpa using hz'
    have h1 := normalClosure_normal.conj_mem _ (subset_normalClosure hmem) (⟨y, hy⟩⁻¹ : X)
    simpa [mul_assoc] using h1
  apply le_antisymm (key hLX hx)
  have hLx : rightConjugate L x ≤ X := fun z hz => by
    rw [mem_rightConjugate_iff] at hz
    have h2 := hLX hz
    have : z = x⁻¹ * (x * z * x⁻¹) * x := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hx) h2) hx
  have h := key hLx (inv_mem hx)
  rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h

omit [Finite G] in
theorem le_normalizer_nclIn (X L : Subgroup G) :
    X ≤ normalizer ((nclIn X L : Subgroup G) : Set G) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨x, hx⟩ * w * ⟨x, hx⟩⁻¹, normalClosure_normal.conj_mem w hw _, by simp⟩
  · rintro ⟨w, hw, hwz⟩
    have hzX : z ∈ X := by
      have h1 : x * z * x⁻¹ ∈ X := hwz ▸ w.2
      have : z = x⁻¹ * (x * z * x⁻¹) * x := by group
      rw [this]
      exact mul_mem (mul_mem (inv_mem hx) h1) hx
    refine ⟨⟨z, hzX⟩, ?_, rfl⟩
    have h2 := normalClosure_normal.conj_mem w hw (⟨x, hx⟩⁻¹ : X)
    have e : (⟨x, hx⟩⁻¹ * w * (⟨x, hx⟩⁻¹)⁻¹ : X) = ⟨z, hzX⟩ := by
      apply Subtype.ext
      simp only [coe_mul, coe_inv, inv_inv]
      rw [show (w : G) = x * z * x⁻¹ from hwz]
      group
    rwa [e] at h2

omit [Finite G] in
theorem mem_normalizer_nclIn {X L : Subgroup G} {t : G}
    (htX : t ∈ normalizer (X : Set G)) (htL : t ∈ normalizer (L : Set G)) :
    t ∈ normalizer ((nclIn X L : Subgroup G) : Set G) := by
  have key : ∀ {s : G}, s ∈ normalizer (X : Set G) → s ∈ normalizer (L : Set G) →
      ∀ z ∈ nclIn X L, s * z * s⁻¹ ∈ nclIn X L := by
    intro s hsX hsL z hz
    set φ := conjAutOf X hsX
    have hφ : (normalClosure ((L.subgroupOf X : Subgroup X) : Set X)).map φ.toMonoidHom ≤
        normalClosure ((L.subgroupOf X : Subgroup X) : Set X) := by
      rw [map_normalClosure _ _ φ.surjective]
      refine normalClosure_mono ?_
      rintro _ ⟨w, hw, rfl⟩
      change ((φ w : X) : G) ∈ L
      rw [conjAutOf_apply]
      exact (mem_normalizer_iff.mp hsL _).mp hw
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨φ w, hφ ⟨w, hw, rfl⟩, rfl⟩
  rw [mem_normalizer_iff]
  intro z
  refine ⟨key htX htL z, fun hz => ?_⟩
  have h := key (inv_mem htX) (inv_mem htL) _ hz
  simpa [mul_assoc] using h

theorem oddCoreIn_eq_bot_of_le_normalizer {X K : Subgroup G} (hKX : K ≤ X)
    (hXK : X ≤ normalizer (K : Set G)) (hO : CFSG.oddCore X = ⊥) : oddCoreIn K = ⊥ := by
  have hN : ((oddCoreIn K).subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have := normalizer_le_normalizer_oddCoreIn K (hXK g.2)
    simpa using (mem_normalizer_iff.mp this n).mp hn
  have hodd : Odd (Nat.card ((oddCoreIn K).subgroupOf X)) := by
    rw [← card_map_of_injective X.subtype_injective, subgroupOf_map_subtype,
      inf_of_le_left ((oddCoreIn_le K).trans hKX)]
    exact odd_card_oddCoreIn K
  have hle : (oddCoreIn K).subgroupOf X ≤ CFSG.oddCore X := le_sSup ⟨hN, hodd⟩
  rw [hO, le_bot_iff] at hle
  rw [← map_subgroupOf_eq_of_le ((oddCoreIn_le K).trans hKX), hle, Subgroup.map_bot]

theorem BenderFacts.two_element_mem_of_not_le_normalizer (hB : BenderFacts)
    {M K R : Subgroup G} (hM : IsSzOrU3 M) (hKM : K ≤ M) (hR : IsSylowOf 2 R M) (hRK : R ≤ K)
    (hKN : ¬ K ≤ normalizer (R : Set G)) : ∀ y ∈ M, ∀ i : ℕ, y ^ (2 ^ i) = 1 → y ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hgK, hgN⟩ : ∃ g ∈ K, g ∉ normalizer (R : Set G) := by
    by_contra h
    push Not at h
    exact hKN h
  obtain ⟨PR, hPR⟩ := hR
  have hsylK : ∀ S : Sylow 2 M, (S : Subgroup M).map M.subtype ≤ K := by
    intro S
    by_cases hS : S = PR
    · rw [hS, hPR]
      exact hRK
    · set g' : M := ⟨g, hKM hgK⟩
      have hg' : g' • PR ≠ PR := fun h => hgN (by
        have h2 := map_subtype_smul_sylow PR g'
        rw [h, hPR] at h2
        have h3 := inv_mem ((rightConjugate_eq_self_iff R _).mp h2.symm)
        simpa using h3)
      obtain ⟨r, hr, hrS⟩ := hB.sylow_transitive M hM PR (g' • PR) S hg' hS
      rw [← mul_smul] at hrS
      rw [← hrS, map_subtype_smul_sylow, hPR]
      intro y hy
      rw [mem_rightConjugate_iff, inv_inv] at hy
      have hrK : (r : G) ∈ K := hRK (hPR ▸ ⟨r, hr, rfl⟩)
      have hrg : ((r * g' : M) : G) ∈ K := mul_mem hrK hgK
      have : y = ((r * g' : M) : G) * (((r * g' : M) : G)⁻¹ * y * ((r * g' : M) : G)) *
          ((r * g' : M) : G)⁻¹ := by group
      rw [this]
      exact mul_mem (mul_mem hrg (hRK hy)) (inv_mem hrg)
  intro y hy i hyi
  obtain ⟨S, hS, hyS⟩ := exists_isSylowOf_le ((zpowers_le).mpr hy)
    (isPGroup_zpowers_of_two_element hyi)
  obtain ⟨S', rfl⟩ := hS
  exact hsylK S' (hyS (mem_zpowers y))

theorem eq_of_le_normalizer_of_isSylowOf {M K R : Subgroup G} (hKM : K ≤ M)
    (hR : IsSylowOf 2 R M) (hRK : R ≤ K) (hKN : K ≤ normalizer (R : Set G))
    (hK2 : oUpperTwoPrime K = K) : K = R := by
  refine le_antisymm ?_ hRK
  rw [← hK2]
  refine (closure_le _).mpr fun y hy => ?_
  obtain ⟨hyK, i, hyi⟩ := hy
  exact mem_of_mem_normalizer_of_isSylowOf hR (hKM hyK) (hKN hyK) hyi

end CFSG.ComponentClassification.Asc76X

namespace CFSG.ComponentClassification.Asc76X.MinCounter

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem commutator_eq_bot_of_conc4 (hM : MinCounter Ω) (h22 : Lemma22Four) (hB : BenderFacts)
    {α : Set (Subgroup G)} (hαΩ : α ⊆ Ω) (hαinv : ∀ J ∈ α, ∀ g : G, rightConjugate J g ∈ α)
    (hC : Conc4 (bar (sSup α) '' α)) {K J : Subgroup G} (hK : K ∈ α) (hJ : J ∈ Ω)
    (hJα : J ∉ α) : ⁅K, J⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.setting
  set Xα := sSup α with hXαdef
  have hXn : Xα.Normal := normal_sSup_of_invariant hαinv
  have hO : CFSG.oddCore Xα = ⊥ := oddCore_eq_bot_of_normal' hΩ.oddCore hXn
  have hKX : K ≤ Xα := le_sSup hK
  have hKΩ := hαΩ hK
  have hJK : J ≠ K := fun h => hJα (h ▸ hK)
  obtain ⟨T, hT⟩ := Sec3Setting.exists_sylow J
  have hT' := isSylowOf_iff_card.mp hT
  have hT2 : IsPGroup 2 T := IsPGroup.of_card hT'.2
  have hT1 := hΩ.sylow_ne_bot hJ hT
  have hTX : T ≤ normalizer (Xα : Set G) := by
    rw [normalizer_eq_top_iff.mpr hXn]
    exact le_top
  obtain ⟨P, hP, hTP⟩ := Sec3Setting.exists_sylow_normalized hT2 hTX
  have hP' := isSylowOf_iff_card.mp hP
  have hP2 : IsPGroup 2 P := IsPGroup.of_card hP'.2
  have hS2 : IsPGroup 2 ↥(T ⊔ P) := hT2.to_sup_of_normal_right' hP2 hTP
  have finish : ∀ {y : G} {i : ℕ}, y ∈ J → y ∈ normalizer (K : Set G) → y ≠ 1 →
      y ^ (2 ^ i) = 1 → oddCoreIn K = ⊥ → ⁅K, J⁆ = ⊥ := by
    intro y i hyJ hyN hy1 hyi hOK
    have heven := even_card_of_two_element (mem_inf.mpr ⟨hyJ, hyN⟩) hy1 hyi
    have h35 := (hΩ.lemma35 h22 hKΩ hJ hJK heven).2
    rw [hOK, le_bot_iff] at h35
    rw [commutator_comm]
    exact h35
  by_cases hKn : Xα ≤ normalizer (K : Set G)
  ·
    have hR' : IsSylowOf 2 (P ⊓ K) K := isSylowOf_inf hKX hKn hP
    have hR'1 := hΩ.sylow_ne_bot hKΩ hR'
    have hne : P ⊓ K ≠ T := fun h =>
      hJK (hΩ.eq_of_pGroup_le hJ hKΩ hT2 hT1 hT'.1 (h ▸ inf_le_right))
    have hc := hΩ.commute_of_sylow hS2 hKΩ hJ hR' hT (inf_le_left.trans le_sup_right) le_sup_left
      hne
    have hTN : T ≤ normalizer (K : Set G) := by
      have h1 : T ≤ centralizer ((P ⊓ K : Subgroup G) : Set G) :=
        le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
      exact (h1.trans (centralizer_le_normalizer _)).trans
        (hΩ.normalizer_le_normalizer hKΩ (hP2.to_le inf_le_left) hR'1 inf_le_right)
    obtain ⟨⟨t₀, ht₀T⟩, ht₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT1
    obtain ⟨k, hk⟩ := hT2 ⟨t₀, ht₀T⟩
    exact finish (hT'.1 ht₀T) (hTN ht₀T) (fun h => ht₀1 (Subtype.ext h))
      (by simpa using congrArg Subtype.val hk) (oddCoreIn_eq_bot_of_le_normalizer hKX hKn hO)
  ·
    obtain ⟨-, hC2⟩ := hC (bar Xα K) ⟨K, hK, rfl⟩
    rcases hC2 with hn | ⟨hsz, hsyl⟩
    · exact absurd (hΩ.le_normalizer_of_bar_normal hKΩ hKX hn) hKn
    set Xn := nclIn Xα K with hXndef
    have hszXn : IsSzOrU3 ↥Xn := isSzOrU3_of_mulEquiv (nclInEquiv hO) hsz
    have hXnX : Xn ≤ Xα := map_subtype_le _
    have hKXn : K ≤ Xn := le_nclIn hKX
    have hXnN : Xα ≤ normalizer (Xn : Set G) := le_normalizer_nclIn Xα K
    obtain ⟨R, hR⟩ := Sec3Setting.exists_sylow K
    have hR' := isSylowOf_iff_card.mp hR
    have hR2 : IsPGroup 2 R := IsPGroup.of_card hR'.2
    have hRXn : IsSylowOf 2 R Xn := by
      have h1 := hsyl _ (isSylowOf_bar hKX hR)
      rw [isSylowOf_iff_card] at h1 ⊢
      refine ⟨hR'.1.trans hKXn, ?_⟩
      rw [Nat.card_congr (nclInEquiv (K := K) hO).toEquiv, ← h1.2,
        card_bar_of_pGroup (hR'.1.trans hKX) hR2]
    have hKNR : K ≤ normalizer (R : Set G) := by
      by_contra hcon
      have hall := hB.two_element_mem_of_not_le_normalizer hszXn hKXn hRXn hR'.1 hcon
      apply hKn
      intro z hz
      have hKz : rightConjugate K z ≤ K := by
        rw [← hΩ.perfect _ (hΩ.conj_mem K hKΩ z)]
        refine (closure_le _).mpr fun y hy => ?_
        obtain ⟨hyK, i, hyi⟩ := hy
        refine hall y ?_ i hyi
        rw [mem_rightConjugate_iff] at hyK
        have h1 : z * y * z⁻¹ ∈ Xn := hKXn hyK
        have h2 := (mem_normalizer_iff.mp (hXnN (inv_mem hz)) _).mp h1
        simpa [mul_assoc] using h2
      have heq : rightConjugate K z = K :=
        eq_of_le_of_card_ge hKz (by rw [rightConjugate_card])
      exact (rightConjugate_eq_self_iff K z).mp heq
    have hKR : K = R :=
      eq_of_le_normalizer_of_isSylowOf hKXn hRXn hR'.1 hKNR (hΩ.perfect K hKΩ)
    have hOK : oddCoreIn K = ⊥ := by
      refine two_subgroup_of_odd_eq_bot _ _ ?_ (odd_card_oddCoreIn K) le_rfl
      exact (hKR ▸ hR2).to_le (oddCoreIn_le K)
    have hU : IsSylowOf 2 (P ⊓ Xn) Xn := isSylowOf_inf hXnX hXnN hP
    have hU2 : IsPGroup 2 ↥(P ⊓ Xn) := hP2.to_le inf_le_left
    obtain ⟨x, hxXn, hUx⟩ := exists_conj_of_isSylowOf hRXn hU
    have hK'α := hαinv K hK x
    have hK'Ω := hαΩ hK'α
    have hU' : IsSylowOf 2 (P ⊓ Xn) (rightConjugate K x) := hUx ▸ isSylowOf_rightConjugate hR x
    have hU1 := hΩ.sylow_ne_bot hK'Ω hU'
    have hne : P ⊓ Xn ≠ T := fun h => hJα (by
      have := hΩ.eq_of_pGroup_le hJ hK'Ω hT2 hT1 hT'.1 (h ▸ (isSylowOf_iff_card.mp hU').1)
      rw [this]
      exact hK'α)
    have hc := hΩ.commute_of_sylow hS2 hK'Ω hJ hU' hT (inf_le_left.trans le_sup_right)
      le_sup_left hne
    have hTC : T ≤ centralizer ((P ⊓ Xn : Subgroup G) : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
    obtain ⟨t, htT, ht2⟩ : ∃ t ∈ T, t ^ 2 ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply (hΩ.rank J hJ T hT).2
      exact ⟨isMulCommutative_of_forall_sq_eq_one hcon, hcon⟩
    have htK' : t ∈ normalizer ((rightConjugate K x : Subgroup G) : Set G) := by
      have h1 := hΩ.eq_of_pGroup_le hK'Ω (hΩ.conj_mem _ hK'Ω t) hU2 hU1
        (isSylowOf_iff_card.mp hU').1 (fun u hu => by
          rw [mem_rightConjugate_iff]
          rw [← mem_centralizer_iff.mp (hTC htT) u hu, mul_inv_cancel_right]
          exact (isSylowOf_iff_card.mp hU').1 hu)
      exact (rightConjugate_eq_self_iff _ t).mp h1.symm
    have htXn : t ∈ normalizer (Xn : Set G) := by
      rw [hXndef, ← nclIn_rightConjugate hKX (hXnX hxXn)]
      exact mem_normalizer_nclIn (hTX htT) htK'
    obtain ⟨PU, hPU⟩ := hU
    set ψ := conjAutOf Xn htXn
    have hψ : ∀ u ∈ (PU : Subgroup Xn), ψ u = u := by
      intro u hu
      apply Subtype.ext
      rw [conjAutOf_apply]
      have huU : (u : G) ∈ P ⊓ Xn := hPU ▸ ⟨u, hu, rfl⟩
      rw [← mem_centralizer_iff.mp (hTC htT) u huU, mul_inv_cancel_right]
    obtain ⟨c, hcP, hcC, hψc⟩ := hB.aut_fix_sylow Xn hszXn PU ψ hψ
    have hc2 := hB.center_sq Xn hszXn PU c hcP hcC
    have ht2C : ∀ y ∈ Xn, t ^ 2 * y = y * t ^ 2 := by
      intro y hy
      have h1 : ψ (ψ ⟨y, hy⟩) = ⟨y, hy⟩ := by
        rw [hψc, MulAut.conj_apply, MulAut.conj_apply]
        calc c * (c * ⟨y, hy⟩ * c⁻¹) * c⁻¹ = (c * c) * ⟨y, hy⟩ * (c * c)⁻¹ := by group
          _ = ⟨y, hy⟩ := by rw [← sq, hc2, one_mul, inv_one, mul_one]
      have h2 := congrArg Subtype.val h1
      rw [conjAutOf_apply, conjAutOf_apply] at h2
      calc t ^ 2 * y = (t * (t * y * t⁻¹) * t⁻¹) * t ^ 2 := by rw [sq]; group
        _ = y * t ^ 2 := by rw [h2]
    have ht2N : t ^ 2 ∈ normalizer (K : Set G) := by
      have hcen : t ^ 2 ∈ centralizer (Xn : Set G) :=
        mem_centralizer_iff.mpr fun y hy => (ht2C y hy).symm
      exact centralizer_le_normalizer _ (centralizer_le hKXn hcen)
    obtain ⟨k, hk⟩ := hT2 ⟨t, htT⟩
    have hk' : t ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have ht2k : (t ^ 2) ^ (2 ^ k) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hk', one_pow]
    exact finish (pow_mem (hT'.1 htT) 2) ht2N ht2 ht2k hOK

theorem lemma311 (hM : MinCounter Ω) (h22 : Lemma22Four) (hB : BenderFacts)
    {α : Set (Subgroup G)} (hαΩ : α ⊆ Ω) (hαne : α.Nonempty)
    (hαinv : ∀ J ∈ α, ∀ g : G, rightConjugate J g ∈ α) : ¬ Conc4 (bar (sSup α) '' α) := by
  intro hC
  have hΩ := hM.setting
  set β := Ω \ α with hβ
  have hβinv : ∀ J ∈ β, ∀ g : G, rightConjugate J g ∈ β := by
    rintro J ⟨hJ, hJα⟩ g
    refine ⟨hΩ.conj_mem J hJ g, fun h => hJα ?_⟩
    have := hαinv _ h g⁻¹
    rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at this
  have hαβ : Ω = α ∪ β := (Set.union_sdiff_cancel hαΩ).symm
  have hcomm : ∀ A ∈ α, ∀ B ∈ β, ⁅A, B⁆ = ⊥ := fun A hA B hB' =>
    hM.commutator_eq_bot_of_conc4 h22 hB hαΩ hαinv hC hA hB'.1 hB'.2
  have hlt : β.ncard < Ω.ncard := by
    rw [hβ, Set.ncard_sdiff hαΩ (Set.toFinite α)]
    have h1 : 0 < α.ncard := (Set.ncard_pos (Set.toFinite α)).mpr hαne
    have h2 : α.ncard ≤ Ω.ncard := Set.ncard_le_ncard hαΩ (Set.toFinite Ω)
    omega
  have hCβ : Conc4 (bar (sSup β) '' β) :=
    hM.conc4_bar Set.sdiff_subset (fun J hJ x _ => hβinv J hJ x) (Or.inl hlt)
  exact hM.not_conc (hΩ.conc4_of_split hαβ hαinv hβinv hcomm hC hCβ)

theorem sSup_eq_top (hM : MinCounter Ω) (h22 : Lemma22Four) (hB : BenderFacts)
    {α : Set (Subgroup G)} (hαΩ : α ⊆ Ω) (hαne : α.Nonempty)
    (hαinv : ∀ J ∈ α, ∀ g : G, rightConjugate J g ∈ α) : sSup α = ⊤ := by
  by_contra hne
  apply hM.lemma311 h22 hB hαΩ hαne hαinv
  refine hM.conc4_bar hαΩ (fun J hJ x _ => hαinv J hJ x) (Or.inr ?_)
  exact lt_of_le_of_ne (card_le_card_group _) fun h => hne ((card_eq_iff_eq_top _).mp h)

theorem lemma312 (hM : MinCounter Ω) (h22 : Lemma22Four) (hB : BenderFacts) {K : Subgroup G}
    (hK : K ∈ Ω) : Ω = Set.range (rightConjugate K) := by
  have hΩ := hM.setting
  set α := Set.range (rightConjugate K) with hα
  have hαΩ : α ⊆ Ω := by
    rintro _ ⟨g, rfl⟩
    exact hΩ.conj_mem K hK g
  have hαinv : ∀ J ∈ α, ∀ g : G, rightConjugate J g ∈ α := by
    rintro _ ⟨h, rfl⟩ g
    exact ⟨h * g, (rightConjugate_mul K h g).symm⟩
  have hαne : α.Nonempty := ⟨K, 1, rightConjugate_one K⟩
  by_contra hne
  have hlt : α.ncard < Ω.ncard :=
    Set.ncard_lt_ncard (LE.le.ssubset_of_ne hαΩ (Ne.symm hne)) (Set.toFinite Ω)
  exact hM.lemma311 h22 hB hαΩ hαne hαinv
    (hM.conc4_bar hαΩ (fun J hJ x _ => hαinv J hJ x) (Or.inl hlt))

end CFSG.ComponentClassification.Asc76X.MinCounter
