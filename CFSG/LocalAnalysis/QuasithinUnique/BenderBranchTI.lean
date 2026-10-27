module

public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchPair

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

namespace BenderBranch

variable {G : Type} [Group G] [Finite G] {T M U : Subgroup G} {z : G}

theorem card_U_eq (hd : UniqueFusionDatum T M U z) {L : Subgroup G}
    (hr : PairRecognition M U L) :
    Nat.card U = Nat.card ↥(U ⊓ L) * Nat.card ↥(U ⊓ Subgroup.centralizer (L : Set G)) := by
  have := card_sup_of_commute_of_inf_eq_bot (H := U ⊓ L)
    (K := U ⊓ Subgroup.centralizer (L : Set G))
    (fun h hh k hk => mul_comm_of_mem hd hh.1 hk.1) hr.inf_eq
  rwa [hr.sup_eq] at this

theorem inf_ne_bot_of_card (hd : UniqueFusionDatum T M U z) {D₁ D₂ : Subgroup G} (h₁ : D₁ ≤ U)
    (h₂ : D₂ ≤ U) {a c : ℕ} (hU : Nat.card U = a * c) (hc₁ : Nat.card D₁ = c)
    (hc₂ : Nat.card D₂ = c) (hlarge : a < c) : D₁ ⊓ D₂ ≠ ⊥ := by
  intro hbot
  have h1 := card_sup_of_commute_of_inf_eq_bot
    (fun x hx y hy => mul_comm_of_mem hd (h₁ hx) (h₂ hy)) hbot
  have h2 : Nat.card ↥(D₁ ⊔ D₂) ≤ Nat.card U := Subgroup.card_le_of_le (sup_le h₁ h₂)
  rw [h1, hc₁, hc₂, hU] at h2
  have hcpos : 0 < c := by omega
  exact absurd (Nat.le_of_mul_le_mul_right h2 hcpos) (by omega)

theorem inf_conjugate_eq (hd : UniqueFusionDatum T M U z) (L : Subgroup G) {g : G} (hg : g ∈ M) :
    U ⊓ CFSG.conjugate L g = CFSG.conjugate (U ⊓ L) g := by
  rw [conjugate_inf, conjugate_U_eq hd hg]

theorem inf_centralizer_conjugate_eq (hd : UniqueFusionDatum T M U z) (L : Subgroup G) {g : G}
    (hg : g ∈ M) :
    U ⊓ Subgroup.centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) =
      CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) g := by
  rw [conjugate_inf, conjugate_U_eq hd hg, conjugate_centralizer]

theorem eq_or_commute_of_inf_ne_bot (hrec : LocalComponentRecognition)
    (hemb : ComponentEmbeddingUnderInvolution) (hd : UniqueFusionDatum T M U z) {u₁ u₂ : G}
    {L₁ L₂ : Subgroup G} (h₁ : IsMaximalEscapingPair M U u₁ L₁)
    (h₂ : IsMaximalEscapingPair M U u₂ L₂)
    (h : (U ⊓ Subgroup.centralizer (L₁ : Set G)) ⊓ (U ⊓ Subgroup.centralizer (L₂ : Set G)) ≠ ⊥) :
    L₁ = L₂ ∨ ⁅L₁, L₂⁆ = ⊥ := by
  obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  have hv1' : v ≠ 1 := fun h' => hv1 (Subtype.ext h')
  exact eq_or_commute_of_isComponentIn (propagation_aux hrec hemb hd h₁ hv.1 hv1').2
    (propagation_aux hrec hemb hd h₂ hv.2 hv1').2

theorem exists_odd_prime_dvd_card_sub_one (hd : UniqueFusionDatum T M U z) {L : Subgroup G}
    (hr : PairRecognition M U L) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card ↥(U ⊓ L) - 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥(U ⊓ L) := (isPGroup_two hd).to_le inf_le_left
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hP
  have h4 := hr.card_ge
  have hn1 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥(U ⊓ L) - 1) (by omega)
  refine ⟨p, hp, ?_, hpd⟩
  rintro rfl
  have h2 : 2 ∣ Nat.card ↥(U ⊓ L) := by rw [hn]; exact dvd_pow_self 2 hn1
  omega

theorem card_sub_one_dvd_card_N {L : Subgroup G} (hr : PairRecognition M U L) :
    Nat.card ↥(U ⊓ L) - 1 ∣
      Nat.card ↥(L ⊓ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G)) := by
  apply card_sub_one_dvd_card_of_transitive (S := U ⊓ L)
  · intro n hn s hs
    exact (Subgroup.mem_normalizer_iff.mp hn.2 s).mp hs
  · exact hr.transitive
  · intro hbot
    have := hr.card_ge
    rw [hbot, Subgroup.card_bot] at this
    omega

theorem card_sub_one_dvd_card_comp {L : Subgroup G} (hr : PairRecognition M U L) :
    Nat.card ↥(U ⊓ L) - 1 ∣ Nat.card L :=
  (card_sub_one_dvd_card_N hr).trans (Subgroup.card_dvd_of_le inf_le_left)

omit [Finite G] in
theorem centerless_of_pairRecognition {L : Subgroup G} (hr : PairRecognition M U L) :
    ∀ x ∈ L, (∀ y ∈ L, y * x = x * y) → x = 1 := fun _ hx hc =>
  eq_one_of_commute_of_simple hr.simple hr.nonabelian hx hc

theorem ti_large (hrec : LocalComponentRecognition) (hemb : ComponentEmbeddingUnderInvolution)
    (hd : UniqueFusionDatum T M U z) {u : G} {L : Subgroup G}
    (h : IsMaximalEscapingPair M U u L) {g : G} (hg : g ∈ M) (hne : CFSG.conjugate L g ≠ L)
    (hV : (U ⊓ Subgroup.centralizer (L : Set G)) ⊓
      CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) g ≠ ⊥) :
    ⁅L, CFSG.conjugate L g⁆ = ⊥ ∧
      Nat.card ↥(U ⊓ L) < Nat.card ↥(U ⊓ Subgroup.centralizer (L : Set G)) := by
  have h' := h.conj hd hg
  have hr := pairRecognition hrec hd h.1 h.2.1 h.2.2.1 h.2.2.2.1
  have hr' := pairRecognition hrec hd h'.1 h'.2.1 h'.2.2.1 h'.2.2.2.1
  have hCg := inf_centralizer_conjugate_eq hd L hg
  have hV' : (U ⊓ Subgroup.centralizer (L : Set G)) ⊓
      (U ⊓ Subgroup.centralizer ((CFSG.conjugate L g : Subgroup G) : Set G)) ≠ ⊥ := by
    rwa [hCg]
  have hcomm : ⁅L, CFSG.conjugate L g⁆ = ⊥ :=
    (eq_or_commute_of_inf_ne_bot hrec hemb hd h h' hV').resolve_left (Ne.symm hne)
  refine ⟨hcomm, ?_⟩
  have hcomm' : ⁅CFSG.conjugate L g, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hcomm
  have hA'C : U ⊓ CFSG.conjugate L g ≤ U ⊓ Subgroup.centralizer (L : Set G) := fun x hx =>
    ⟨hx.1, Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm' hx.2⟩
  have hdisj : (U ⊓ CFSG.conjugate L g) ⊓ ((U ⊓ Subgroup.centralizer (L : Set G)) ⊓
      CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) g) = ⊥ := by
    rw [le_bot_iff.symm]
    calc (U ⊓ CFSG.conjugate L g) ⊓ ((U ⊓ Subgroup.centralizer (L : Set G)) ⊓
          CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) g)
        ≤ (U ⊓ CFSG.conjugate L g) ⊓
          (U ⊓ Subgroup.centralizer ((CFSG.conjugate L g : Subgroup G) : Set G)) := by
          rw [hCg]
          exact inf_le_inf_left _ inf_le_right
      _ = ⊥ := hr'.inf_eq
  have hcard := card_sup_of_commute_of_inf_eq_bot
    (H := U ⊓ CFSG.conjugate L g)
    (K := (U ⊓ Subgroup.centralizer (L : Set G)) ⊓
      CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) g)
    (fun x hx y hy => mul_comm_of_mem hd hx.1 hy.1.1) hdisj
  have hle : (U ⊓ CFSG.conjugate L g) ⊔ ((U ⊓ Subgroup.centralizer (L : Set G)) ⊓
      CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) g) ≤
      U ⊓ Subgroup.centralizer (L : Set G) := sup_le hA'C inf_le_left
  have h2 := Subgroup.card_le_of_le hle
  rw [hcard] at h2
  have hVcard : 1 < Nat.card ↥((U ⊓ Subgroup.centralizer (L : Set G)) ⊓
      CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) g) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr hV
  have hAcard : Nat.card ↥(U ⊓ CFSG.conjugate L g) = Nat.card ↥(U ⊓ L) := by
    rw [inf_conjugate_eq hd L hg, card_conjugate]
  rw [hAcard] at h2
  have hA4 := hr.card_ge
  have h3 := Nat.mul_le_mul_left (Nat.card ↥(U ⊓ L)) hVcard
  omega

theorem ti_dichotomy (hrec : LocalComponentRecognition)
    (hemb : ComponentEmbeddingUnderInvolution) (hd : UniqueFusionDatum T M U z) {u : G}
    {L : Subgroup G} (h : IsMaximalEscapingPair M U u L) {g : G} (hg : g ∈ M)
    (hne : CFSG.conjugate L g ≠ L)
    (hlarge : Nat.card ↥(U ⊓ L) < Nat.card ↥(U ⊓ Subgroup.centralizer (L : Set G))) {x : G}
    (hx : x ∈ M) : CFSG.conjugate L x = L ∨ CFSG.conjugate L x = CFSG.conjugate L g := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hx1, hx2⟩ := hcon
  have h' := h.conj hd hg
  have hx' := h.conj hd hx
  have hr := pairRecognition hrec hd h.1 h.2.1 h.2.2.1 h.2.2.2.1
  have hr' := pairRecognition hrec hd h'.1 h'.2.1 h'.2.2.1 h'.2.2.2.1
  have hrx := pairRecognition hrec hd hx'.1 hx'.2.1 hx'.2.2.1 hx'.2.2.2.1
  have hU := card_U_eq hd hr
  have hcg : Nat.card ↥(U ⊓ Subgroup.centralizer ((CFSG.conjugate L g : Subgroup G) : Set G)) =
      Nat.card ↥(U ⊓ Subgroup.centralizer (L : Set G)) := by
    rw [inf_centralizer_conjugate_eq hd L hg, card_conjugate]
  have hcx : Nat.card ↥(U ⊓ Subgroup.centralizer ((CFSG.conjugate L x : Subgroup G) : Set G)) =
      Nat.card ↥(U ⊓ Subgroup.centralizer (L : Set G)) := by
    rw [inf_centralizer_conjugate_eq hd L hx, card_conjugate]
  have n₁₂ := inf_ne_bot_of_card hd (inf_le_left : U ⊓ Subgroup.centralizer (L : Set G) ≤ U)
    (inf_le_left : U ⊓ Subgroup.centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) ≤ U)
    hU rfl hcg hlarge
  have n₁₃ := inf_ne_bot_of_card hd (inf_le_left : U ⊓ Subgroup.centralizer (L : Set G) ≤ U)
    (inf_le_left : U ⊓ Subgroup.centralizer ((CFSG.conjugate L x : Subgroup G) : Set G) ≤ U)
    hU rfl hcx hlarge
  have n₂₃ := inf_ne_bot_of_card hd
    (inf_le_left : U ⊓ Subgroup.centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) ≤ U)
    (inf_le_left : U ⊓ Subgroup.centralizer ((CFSG.conjugate L x : Subgroup G) : Set G) ≤ U)
    hU hcg hcx hlarge
  have c₁₂ : ⁅L, CFSG.conjugate L g⁆ = ⊥ :=
    (eq_or_commute_of_inf_ne_bot hrec hemb hd h h' n₁₂).resolve_left (Ne.symm hne)
  have c₁₃ : ⁅L, CFSG.conjugate L x⁆ = ⊥ :=
    (eq_or_commute_of_inf_ne_bot hrec hemb hd h hx' n₁₃).resolve_left (Ne.symm hx1)
  have c₂₃ : ⁅CFSG.conjugate L g, CFSG.conjugate L x⁆ = ⊥ :=
    (eq_or_commute_of_inf_ne_bot hrec hemb hd h' hx' n₂₃).resolve_left fun e => hx2 e.symm
  obtain ⟨p, hp, hp2, hpd⟩ := exists_odd_prime_dvd_card_sub_one hd hr
  have hAg : Nat.card ↥(U ⊓ CFSG.conjugate L g) = Nat.card ↥(U ⊓ L) := by
    rw [inf_conjugate_eq hd L hg, card_conjugate]
  have hAx : Nat.card ↥(U ⊓ CFSG.conjugate L x) = Nat.card ↥(U ⊓ L) := by
    rw [inf_conjugate_eq hd L hx, card_conjugate]
  have hA1ne : U ⊓ L ≠ ⊥ := fun hbot => by
    have := hr.card_ge
    rw [hbot, Subgroup.card_bot] at this
    omega
  exact three_commuting_factors_obstruction hd.setting.qtke.2.2
    (centerless_of_pairRecognition hr) (centerless_of_pairRecognition hr') c₁₂ c₁₃ c₂₃
    (inf_le_right : U ⊓ L ≤ L) hA1ne ((isPGroup_two hd).to_le inf_le_left) hp hp2
    (hpd.trans (card_sub_one_dvd_card_N hr))
    (by rw [← hAg] at hpd; exact hpd.trans (card_sub_one_dvd_card_comp hr'))
    (by rw [← hAx] at hpd; exact hpd.trans (card_sub_one_dvd_card_comp hrx))

theorem ti_key (hrec : LocalComponentRecognition) (hemb : ComponentEmbeddingUnderInvolution)
    (hd : UniqueFusionDatum T M U z) {u : G} {L : Subgroup G}
    (h : IsMaximalEscapingPair M U u L) {g : G} (hg : g ∈ M)
    (hV : (U ⊓ Subgroup.centralizer (L : Set G)) ⊓
      CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) g ≠ ⊥) :
    CFSG.conjugate L g = L := by
  by_contra hne
  obtain ⟨-, hlarge⟩ := ti_large hrec hemb hd h hg hne hV
  have hr := pairRecognition hrec hd h.1 h.2.1 h.2.2.1 h.2.2.2.1
  have hdich := fun x (hx : x ∈ M) => ti_dichotomy hrec hemb hd h hg hne hlarge hx
  have e1 : ∀ y ∈ M, CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) y =
      U ⊓ Subgroup.centralizer ((CFSG.conjugate L y : Subgroup G) : Set G) :=
    fun y hy => (inf_centralizer_conjugate_eq hd L hy).symm
  have hVinv : ∀ x ∈ M, CFSG.conjugate ((U ⊓ Subgroup.centralizer (L : Set G)) ⊓
      CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) g) x =
      (U ⊓ Subgroup.centralizer (L : Set G)) ⊓
      CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) g := by
    intro x hx
    have hgx : g * x ∈ M := M.mul_mem hg hx
    rw [conjugate_inf, conjugate_conjugate, e1 x hx, e1 (g * x) hgx, e1 g hg]
    rcases hdich x hx with hx1 | hx1
    · have hgx1 : CFSG.conjugate L (g * x) = CFSG.conjugate L g := by
        rcases hdich (g * x) hgx with h1 | h1
        · exfalso
          apply hne
          apply (conjugate_inj (g := x)).mp
          rw [conjugate_conjugate, h1, hx1]
        · exact h1
      rw [hx1, hgx1]
    · have hgx1 : CFSG.conjugate L (g * x) = L := by
        rcases hdich (g * x) hgx with h1 | h1
        · exact h1
        · exfalso
          apply hne
          apply (conjugate_inj (g := x)).mp
          rw [conjugate_conjugate, h1, hx1]
      rw [hx1, hgx1, inf_comm]
  have hnormV : M ≤ Subgroup.normalizer (((U ⊓ Subgroup.centralizer (L : Set G)) ⊓
      CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) g : Subgroup G) : Set G) :=
    fun x hx => conjugate_eq_iff_mem_normalizer.mp (hVinv x hx)
  have hVU : (U ⊓ Subgroup.centralizer (L : Set G)) ⊓
      CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) g ≤ U :=
    inf_le_left.trans inf_le_left
  rcases hd.irreducible _ hVU hnormV with hbot | htop
  · exact hV hbot
  · have h1 : U ≤ (U ⊓ Subgroup.centralizer (L : Set G)) ⊓
        CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) g := htop.ge
    exact inf_centralizer_ne_U hr (le_antisymm inf_le_left (h1.trans inf_le_left))

end BenderBranch

theorem UniqueFusionDatum.maximal_component_centralizer_TI {G : Type} [Group G] [Finite G]
    (hrec : LocalComponentRecognition) (hemb : ComponentEmbeddingUnderInvolution)
    {T M U : Subgroup G} {z : G} (hd : UniqueFusionDatum T M U z) {u : G} {L : Subgroup G}
    (h : IsMaximalEscapingPair M U u L) :
    (∀ g ∈ M, (U ⊓ Subgroup.centralizer (L : Set G)) ⊓
        CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) g ≠ ⊥ →
      CFSG.conjugate L g = L ∧
        CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) g =
          U ⊓ Subgroup.centralizer (L : Set G)) ∧
    M ⊓ Subgroup.normalizer ((U ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) =
      M ⊓ Subgroup.normalizer (L : Set G) := by
  have hCg : ∀ g ∈ M, CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) g =
      U ⊓ Subgroup.centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
    fun g hg => (BenderBranch.inf_centralizer_conjugate_eq hd L hg).symm
  refine ⟨fun g hg hV => ?_, ?_⟩
  · have hL := BenderBranch.ti_key hrec hemb hd h hg hV
    exact ⟨hL, by rw [hCg g hg, hL]⟩
  · ext g
    simp only [Subgroup.mem_inf]
    refine and_congr_right fun hg => ?_
    constructor
    · intro hgC
      have hC : CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) g =
          U ⊓ Subgroup.centralizer (L : Set G) :=
        BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hgC
      have hV : (U ⊓ Subgroup.centralizer (L : Set G)) ⊓
          CFSG.conjugate (U ⊓ Subgroup.centralizer (L : Set G)) g ≠ ⊥ := by
        rw [hC, inf_idem]
        exact BenderBranch.inf_centralizer_ne_bot h
      exact BenderBranch.conjugate_eq_iff_mem_normalizer.mp
        (BenderBranch.ti_key hrec hemb hd h hg hV)
    · intro hgL
      have hL : CFSG.conjugate L g = L := BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hgL
      exact BenderBranch.conjugate_eq_iff_mem_normalizer.mp (by rw [hCg g hg, hL])

end CFSG.QuasithinUnique
