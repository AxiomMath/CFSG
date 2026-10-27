module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenCanon
public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenStage

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

section Pure

theorem eq_top_or_eq_top_of_commute_sup {D : Type*} [Group D] [IsSimpleGroup D]
    {E₀ E₁ : Subgroup D} (hc : ∀ x ∈ E₀, ∀ y ∈ E₁, x * y = y * x) (hsup : E₀ ⊔ E₁ = ⊤) :
    E₀ = ⊤ ∨ E₁ = ⊤ := by
  have hnormal : ∀ {A B : Subgroup D}, (∀ x ∈ A, ∀ y ∈ B, x * y = y * x) → A ⊔ B = ⊤ →
      A.Normal := by
    intro A B hAB hsup'
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup']
    refine sup_le Subgroup.le_normalizer (fun y hy => ?_)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have h1 := hAB h hh y hy
      have h2 : y * h * y⁻¹ = h := by
        calc y * h * y⁻¹ = (h * y) * y⁻¹ := by rw [h1]
          _ = h := by group
      rw [h2]
      exact hh
    · intro hh
      have h1 := hAB (y * h * y⁻¹) hh y hy
      have h2 : h = y * h * y⁻¹ := by
        calc h = y⁻¹ * (y * h * y⁻¹ * y) := by group
          _ = y⁻¹ * (y * (y * h * y⁻¹)) := by rw [h1]
          _ = y * h * y⁻¹ := by group
      rw [h2]
      exact hh
  have hn0 : E₀.Normal := hnormal hc hsup
  have hn1 : E₁.Normal :=
    hnormal (fun x hx y hy => (hc y hy x hx).symm) (by rw [sup_comm]; exact hsup)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal E₀ with h0 | h0
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal E₁ with h1 | h1
    · exfalso
      rw [h0, h1, bot_sup_eq] at hsup
      exact bot_ne_top hsup
    · right; exact h1
  · left; exact h0

end Pure

section Disch

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {z : G}
  {e : L ≃* alternatingGroup (Fin n)}

theorem corr_inf_le (e : L ≃* alternatingGroup (Fin n)) (S S' : Finset (Fin n)) :
    corr (X := G) e (altSub Sᶜ) ⊓ corr (X := G) e (altSub S'ᶜ) ≤
      corr (X := G) e (altSub (S ∪ S')ᶜ) := by
  rintro x ⟨hx1, hx2⟩
  obtain ⟨hxA, h1⟩ := mem_corr.1 hx1
  obtain ⟨_, h2⟩ := mem_corr.1 hx2
  refine mem_corr.2 ⟨hxA, ?_⟩
  obtain ⟨hs, hf1⟩ := mem_altSub.1 h1
  obtain ⟨_, hf2⟩ := mem_altSub.1 h2
  refine mem_altSub.2 ⟨hs, fun i hi => ?_⟩
  simp only [Finset.mem_compl, Finset.mem_union, not_not] at hi
  rcases hi with hi | hi
  · exact hf1 i (by simpa using hi)
  · exact hf2 i (by simpa using hi)

theorem CanonLift.norm_inj {S : Finset (Fin n)} {Q : Subgroup G} (hQ : CanonLift e z S Q)
    {q₁ q₂ : G} (h1 : q₁ ∈ Q) (h2 : q₂ ∈ Q)
    (h : q₁ * (z * q₁ * z⁻¹) = q₂ * (z * q₂ * z⁻¹)) : q₁ = q₂ := by
  have hw : q₂⁻¹ * q₁ ∈ Q := Q.mul_mem (Q.inv_mem h2) h1
  have h3 : q₂⁻¹ * q₁ = (z * q₂ * z⁻¹) * (z * q₁ * z⁻¹)⁻¹ := by
    calc q₂⁻¹ * q₁ = (q₂⁻¹ * (q₁ * (z * q₁ * z⁻¹))) * (z * q₁ * z⁻¹)⁻¹ := by group
      _ = (q₂⁻¹ * (q₂ * (z * q₂ * z⁻¹))) * (z * q₁ * z⁻¹)⁻¹ := by rw [h]
      _ = (z * q₂ * z⁻¹) * (z * q₁ * z⁻¹)⁻¹ := by group
  have hw' : q₂⁻¹ * q₁ ∈ Q.map (MulAut.conj z).toMonoidHom :=
    ⟨q₂ * q₁⁻¹, Q.mul_mem h2 (Q.inv_mem h1), by rw [h3]; show z * (q₂ * q₁⁻¹) * z⁻¹ = _; group⟩
  have h4 := hQ.inf _ hw hw'
  exact (inv_mul_eq_one.1 h4).symm

theorem norm_cjHom (hz : z * z = 1) {u : G} (hcu : u * (z * u * z⁻¹) = (z * u * z⁻¹) * u)
    (a : Bool) : cjHom z a u * (z * cjHom z a u * z⁻¹) = u * (z * u * z⁻¹) := by
  cases a
  · rfl
  · show (z * u * z⁻¹) * (z * (z * u * z⁻¹) * z⁻¹) = u * (z * u * z⁻¹)
    rw [conj_conj_of_sq hz, ← hcu]

theorem CanonLift.eq_cj (hz : z * z = 1) {S : Finset (Fin n)} {Q : Subgroup G}
    (hQ : CanonLift e z S Q) {u v : G} (hcu : u * (z * u * z⁻¹) = (z * u * z⁻¹) * u)
    (hcv : v * (z * v * z⁻¹) = (z * v * z⁻¹) * v)
    (huv : u * (z * u * z⁻¹) = v * (z * v * z⁻¹)) {a b : Bool} (hu : cjHom z a u ∈ Q)
    (hv : cjHom z b v ∈ Q) : u = cjHom z (xor a b) v := by
  have h1 : cjHom z a u = cjHom z b v :=
    hQ.norm_inj hu hv (by rw [norm_cjHom hz hcu, norm_cjHom hz hcv, huv])
  have h2 : u = cjHom z a (cjHom z a u) := by
    rw [cjHom_cjHom hz, Bool.xor_self]; rfl
  rw [h2, h1, cjHom_cjHom hz]

theorem rootLift_bool (h : ExactShape z L n) (hn : 11 ≤ n) {S : Finset (Fin n)}
    (hS : S.card = 3) {Q : Subgroup G} (hQ : CanonLift e z S Q)
    {ψ : ↥(corr (X := G) e (altSub Sᶜ)) →* G} (hψ : IsRootLift e z S ψ) :
    ∃ a : Bool, ∀ b, cjHom z a (ψ b) ∈ Q := by
  have hz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.order, pow_two] at this
  obtain ⟨eB⟩ := exists_equiv_corr_altSub (X := G) e Sᶜ
  have hk : Sᶜ.card = n - 3 := by rw [card_compl_fin, hS]
  have hPC : ψ.range ≤ centralizer (corr (X := G) e (altSub S) : Set G) := by
    rintro _ ⟨b, rfl⟩
    exact hψ.cent b
  have hPP : ∀ a ∈ ψ.range, ∀ b ∈ ψ.range,
      a * (z * b * z⁻¹) = (z * b * z⁻¹) * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact hψ.comm a b
  let eP : ↥ψ.range ≃* alternatingGroup (Fin Sᶜ.card) :=
    (MonoidHom.ofInjective hψ.inj).symm.trans eB
  rcases hQ.absorb Sᶜ.card ψ.range (by omega) (by omega) (by omega) hPC ⟨eP⟩ hPP with hl | hr
  · exact ⟨false, fun b => hl ⟨b, rfl⟩⟩
  · refine ⟨true, fun b => ?_⟩
    obtain ⟨q, hq, hqb⟩ := hr ⟨b, rfl⟩
    have : z * ψ b * z⁻¹ = q := by
      rw [← hqb]
      show z * (z * q * z⁻¹) * z⁻¹ = q
      exact conj_conj_of_sq hz q
    show z * ψ b * z⁻¹ ∈ Q
    rw [this]; exact hq

end Disch

section ClaimAB

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {z : G}
  {e : L ≃* alternatingGroup (Fin n)}

omit [Group G] in
theorem sq_of_exactShape {X : Type} [Group X] {t : X} {A : Subgroup X} {m : ℕ}
    (h : ExactShape t A m) : t * t = 1 := by
  have := pow_orderOf_eq_one t
  rwa [h.order, pow_two] at this

theorem rootLift_rel_disjoint (h : ExactShape z L n) (hn : 11 ≤ n) {S S' : Finset (Fin n)}
    (hS : S.card = 3) (hS' : S'.card = 3) (hdisj : Disjoint S S') {Q' : Subgroup G}
    (hQ' : CanonLift e z S' Q') {ψ : ↥(corr (X := G) e (altSub Sᶜ)) →* G}
    {ψ' : ↥(corr (X := G) e (altSub S'ᶜ)) →* G} (hψ : IsRootLift e z S ψ)
    (hψ' : IsRootLift e z S' ψ') :
    ∃ c : Bool, ∀ (x : G) (hx : x ∈ corr (X := G) e (altSub Sᶜ))
      (hx' : x ∈ corr (X := G) e (altSub S'ᶜ)), ψ ⟨x, hx⟩ = cjHom z c (ψ' ⟨x, hx'⟩) := by
  have hz := sq_of_exactShape h
  obtain ⟨U, hU⟩ : ∃ U : Finset (Fin n), U = (S ∪ S')ᶜ := ⟨_, rfl⟩
  have hUc : U.card = n - 6 := by
    rw [hU, card_compl_fin, Finset.card_union_of_disjoint hdisj, hS, hS']
  have hUS : U ⊆ Sᶜ := fun i hi => by
    simp only [hU, Finset.mem_compl, Finset.mem_union, not_or] at hi ⊢
    exact hi.1
  have hDB : corr (X := G) e (altSub U) ≤ corr (X := G) e (altSub Sᶜ) :=
    corr_mono e (altSub_mono hUS)
  have hS'S : S' ⊆ Sᶜ := fun i hi => by
    simp only [Finset.mem_compl]
    exact fun hiS => Finset.disjoint_left.1 hdisj hiS hi
  have hR'B : corr (X := G) e (altSub S') ≤ corr (X := G) e (altSub Sᶜ) :=
    corr_mono e (altSub_mono hS'S)
  have hUS' : Disjoint U S' := Finset.disjoint_left.2 fun i hi hi' => by
    simp only [hU, Finset.mem_compl, Finset.mem_union, not_or] at hi
    exact hi.2 hi'
  let P : Subgroup G := ((corr (X := G) e (altSub U)).subgroupOf
    (corr (X := G) e (altSub Sᶜ))).map ψ
  have hPC : P ≤ centralizer (corr (X := G) e (altSub S') : Set G) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [mem_centralizer_iff]
    intro r hr
    have hrr : ψ ⟨r, hR'B hr⟩ * (z * ψ ⟨r, hR'B hr⟩ * z⁻¹) = r := hψ.diag ⟨r, hR'B hr⟩
    have hdc : d * ⟨r, hR'B hr⟩ = ⟨r, hR'B hr⟩ * d :=
      Subtype.ext (corr_comm e (T₁ := altSub U) (T₂ := altSub S')
        (fun g hg g' hg' => comm_of_altSub_disjoint hUS' hg hg') (d : G) hd r hr)
    have hψc := hψ.comm d ⟨r, hR'B hr⟩
    calc r * ψ d = (ψ ⟨r, hR'B hr⟩ * (z * ψ ⟨r, hR'B hr⟩ * z⁻¹)) * ψ d := by rw [hrr]
      _ = ψ ⟨r, hR'B hr⟩ * ((z * ψ ⟨r, hR'B hr⟩ * z⁻¹) * ψ d) := by group
      _ = ψ ⟨r, hR'B hr⟩ * (ψ d * (z * ψ ⟨r, hR'B hr⟩ * z⁻¹)) := by rw [hψc]
      _ = (ψ ⟨r, hR'B hr⟩ * ψ d) * (z * ψ ⟨r, hR'B hr⟩ * z⁻¹) := by group
      _ = ψ (⟨r, hR'B hr⟩ * d) * (z * ψ ⟨r, hR'B hr⟩ * z⁻¹) := by rw [map_mul]
      _ = ψ (d * ⟨r, hR'B hr⟩) * (z * ψ ⟨r, hR'B hr⟩ * z⁻¹) := by rw [hdc]
      _ = (ψ d * ψ ⟨r, hR'B hr⟩) * (z * ψ ⟨r, hR'B hr⟩ * z⁻¹) := by rw [map_mul]
      _ = ψ d * (ψ ⟨r, hR'B hr⟩ * (z * ψ ⟨r, hR'B hr⟩ * z⁻¹)) := by group
      _ = ψ d * r := by rw [hrr]
  have hPP : ∀ a ∈ P, ∀ b ∈ P, a * (z * b * z⁻¹) = (z * b * z⁻¹) * a := by
    rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
    exact hψ.comm a b
  obtain ⟨eD⟩ := exists_equiv_corr_altSub (X := G) e U
  let eP : ↥P ≃* alternatingGroup (Fin U.card) :=
    (Subgroup.equivMapOfInjective _ ψ hψ.inj).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hDB).trans eD)
  have hbool : ∃ a' : Bool, ∀ d : ↥(corr (X := G) e (altSub Sᶜ)),
      (d : G) ∈ corr (X := G) e (altSub U) → cjHom z a' (ψ d) ∈ Q' := by
    rcases hQ'.absorb U.card P (by omega) (by omega) (by omega) hPC ⟨eP⟩ hPP with hl | hr
    · exact ⟨false, fun d hd => hl ⟨d, hd, rfl⟩⟩
    · refine ⟨true, fun d hd => ?_⟩
      obtain ⟨q, hq, hqb⟩ := hr ⟨d, hd, rfl⟩
      have : z * ψ d * z⁻¹ = q := by
        rw [← hqb]
        show z * (z * q * z⁻¹) * z⁻¹ = q
        exact conj_conj_of_sq hz q
      show z * ψ d * z⁻¹ ∈ Q'
      rw [this]; exact hq
  obtain ⟨a', ha'⟩ := hbool
  obtain ⟨a, ha⟩ := rootLift_bool h hn hS' hQ' hψ'
  refine ⟨xor a' a, fun x hx hx' => ?_⟩
  have hxD : x ∈ corr (X := G) e (altSub U) := by
    have := corr_inf_le e S S' ⟨hx, hx'⟩
    rwa [← hU] at this
  exact hQ'.eq_cj hz (hψ.comm _ _) (hψ'.comm _ _) (by rw [hψ.diag, hψ'.diag])
    (ha' ⟨x, hx⟩ hxD) (ha ⟨x, hx'⟩)

end ClaimAB

section ClaimC

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {z : G}
  {e : L ≃* alternatingGroup (Fin n)}

theorem exists_root_disjoint (T : Finset (Fin n)) (hT : T.card + 3 ≤ n) :
    ∃ R : Finset (Fin n), R.card = 3 ∧ Disjoint R T := by
  have h3 : 3 ≤ Tᶜ.card := by rw [card_compl_fin]; omega
  obtain ⟨R, hR, hcard⟩ := Finset.exists_subset_card_eq h3
  exact ⟨R, hcard, Finset.disjoint_of_subset_left hR disjoint_compl_left⟩

theorem rootLift_rel_local (h : ExactShape z L n) (hn : 11 ≤ n)
    (hIII : ∀ S : Finset (Fin n), S.card = 3 → CaseIIIAt e z S) {S S' : Finset (Fin n)}
    (hS : S.card = 3) (hS' : S'.card = 3) {ψ : ↥(corr (X := G) e (altSub Sᶜ)) →* G}
    {ψ' : ↥(corr (X := G) e (altSub S'ᶜ)) →* G} (hψ : IsRootLift e z S ψ)
    (hψ' : IsRootLift e z S' ψ') {T : Finset (Fin n)} (hT : T.card ≤ 3) {x : G}
    (hxS : x ∈ corr (X := G) e (altSub Sᶜ)) (hxS' : x ∈ corr (X := G) e (altSub S'ᶜ))
    (hxT : x ∈ corr (X := G) e (altSub T)) :
    ∃ c : Bool, ψ ⟨x, hxS⟩ = cjHom z c (ψ' ⟨x, hxS'⟩) := by
  classical
  have hz := sq_of_exactShape h
  by_cases hSS : Disjoint S S'
  · obtain ⟨Q', hQ'⟩ := exists_canon h e (by omega) hS' (hIII S' hS')
    obtain ⟨c, hc⟩ := rootLift_rel_disjoint h hn hS hS' hSS hQ' hψ hψ'
    exact ⟨c, hc x hxS hxS'⟩
  have hSS' : (S ∪ S').card ≤ 5 := by
    have h1 := Finset.card_union_add_card_inter S S'
    have h2 : (S ∩ S').Nonempty := Finset.not_disjoint_iff_nonempty_inter.1 hSS
    have h3 := h2.card_pos
    omega
  obtain ⟨S'', hS'', hdisj⟩ := exists_root_disjoint (S ∪ S' ∪ T) (by
    have h1 := Finset.card_union_le (S ∪ S') T
    omega)
  have hd1 : Disjoint S S'' := by
    refine Finset.disjoint_left.2 fun i hi hi' => ?_
    exact Finset.disjoint_left.1 hdisj hi' (by simp [hi])
  have hd2 : Disjoint S' S'' := by
    refine Finset.disjoint_left.2 fun i hi hi' => ?_
    exact Finset.disjoint_left.1 hdisj hi' (by simp [hi])
  have hTS'' : T ⊆ S''ᶜ := fun i hi => by
    simp only [Finset.mem_compl]
    exact fun hi' => Finset.disjoint_left.1 hdisj hi' (by simp [hi])
  have hxS'' : x ∈ corr (X := G) e (altSub S''ᶜ) := corr_mono e (altSub_mono hTS'') hxT
  obtain ⟨Q'', hQ''⟩ := exists_canon h e (by omega) hS'' (hIII S'' hS'')
  obtain ⟨ψ'', hψ''⟩ := exists_rootLift h e (by omega) hS'' (hIII S'' hS'')
  obtain ⟨c₁, hc₁⟩ := rootLift_rel_disjoint h hn hS hS'' hd1 hQ'' hψ hψ''
  obtain ⟨c₂, hc₂⟩ := rootLift_rel_disjoint h hn hS' hS'' hd2 hQ'' hψ' hψ''
  refine ⟨xor c₁ c₂, ?_⟩
  have e1 := hc₁ x hxS hxS''
  have e2 := hc₂ x hxS' hxS''
  rw [e1, e2, cjHom_cjHom hz, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

end ClaimC

end CFSG.OddStandard.AltStdSec
