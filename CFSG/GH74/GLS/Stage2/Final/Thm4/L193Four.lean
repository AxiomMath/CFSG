module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.L193T
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4.L193

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6.L20
open CFSG.GH74.Uniqueness.SU.SU1
open scoped commutatorElement

section NonChar

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem exists_central_of_not_char {p : ℕ} (hp : p.Prime) (hΓ : IsPGroup p Γ)
    {Q : Subgroup Γ} (hQc : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hQi : Q.index ≤ p) (ϕ : Γ ≃* Γ)
    (hne : Q.comap ϕ.toMonoidHom ≠ Q) {E₃ : Subgroup Γ} (hE₃Q : E₃ ≤ Q) (hE₃ : Open.IsElemAbelian p E₃)
    (hE₃c : Nat.card E₃ = p ^ 3) :
    ∃ E : Subgroup Γ, Open.IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧ ∀ u ∈ E, ∀ g : Γ, g * u = u * g := by
  have := Fact.mk hp
  set Q₂ := Q.comap ϕ.toMonoidHom with hQ₂
  have hQ₂c : ∀ a ∈ Q₂, ∀ b ∈ Q₂, a * b = b * a := by
    intro a ha b hb
    apply ϕ.injective
    rw [map_mul, map_mul]
    exact hQc _ ha _ hb
  have hQ₂i : Q₂.index = Q.index := Subgroup.index_comap_of_surjective Q ϕ.surjective
  have hQtop : Q ≠ ⊤ := by
    intro h
    apply hne
    rw [hQ₂, h, Subgroup.comap_top]
  have hQp : Q.index = p := by
    obtain ⟨n, hn⟩ := hΓ.index Q
    have h1 : Q.index ≠ 1 := fun h1 => hQtop (Subgroup.index_eq_one.mp h1)
    rw [hn] at hQi h1 ⊢
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · rcases Nat.eq_zero_or_pos n with h0 | h0
      · exact absurd (by rw [h0, pow_zero]) h1
      · have : n = 1 := by omega
        rw [this, pow_one]
    · have : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hp.pos h2
      have h3 : p < p ^ 2 := by
        have := hp.one_lt
        nlinarith
      omega
  have hsup : Q ⊔ Q₂ = ⊤ := by
    have hdvd : (Q ⊔ Q₂).index ∣ Q.index := Subgroup.index_dvd_of_le le_sup_left
    rw [hQp] at hdvd
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact Subgroup.index_eq_one.mp h1
    · exfalso
      have hle : Q ≤ Q ⊔ Q₂ := le_sup_left
      have heq : Q ⊔ Q₂ = Q := by
        refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
        have h2 := Subgroup.card_mul_index (Q ⊔ Q₂)
        have h3 := Subgroup.card_mul_index Q
        rw [h1, ← hQp] at h2
        have hpos : 0 < Q.index := by rw [hQp]; exact hp.pos
        have := Nat.eq_of_mul_eq_mul_right hpos (h2.trans h3.symm)
        exact this.le
      have hQ₂le : Q₂ ≤ Q := heq ▸ le_sup_right
      apply hne
      refine Subgroup.eq_of_le_of_card_ge hQ₂le ?_
      have h2 := Subgroup.card_mul_index Q₂
      have h3 := Subgroup.card_mul_index Q
      rw [hQ₂i] at h2
      have hpos : 0 < Q.index := by rw [hQp]; exact hp.pos
      have := Nat.eq_of_mul_eq_mul_right hpos (h2.trans h3.symm)
      exact this.ge
  have hZc : ∀ z ∈ Q ⊓ Q₂, ∀ g : Γ, g * z = z * g := by
    intro z hz g
    have hle : Q ⊔ Q₂ ≤ centralizer ({z} : Set Γ) := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hQc a ha z hz.1)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hQ₂c a ha z hz.2)
    have : g ∈ centralizer ({z} : Set Γ) := hle (by rw [hsup]; trivial)
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  have hrel : (Q ⊓ Q₂).relIndex E₃ ≤ p := by
    have h1 : (Q ⊓ Q₂).relIndex Q = Q₂.relIndex Q := by
      rw [inf_comm, Subgroup.inf_relIndex_right]
    have h2 : Q₂.relIndex Q ≤ Q₂.relIndex ⊤ := Subgroup.relIndex_le_of_le_right le_top (relIndex_ne_zero_of_finite _ _)
    have h3 : (Q ⊓ Q₂).relIndex E₃ ≤ (Q ⊓ Q₂).relIndex Q := Subgroup.relIndex_le_of_le_right hE₃Q (relIndex_ne_zero_of_finite _ _)
    rw [Subgroup.relIndex_top_right, hQ₂i, hQp] at h2
    omega
  have hmul := Subgroup.relIndex_mul_card (H := Q ⊓ Q₂) (K := E₃)
  rw [hE₃c] at hmul
  have hcardF : p ^ 2 ≤ Nat.card ↥(Q ⊓ Q₂ ⊓ E₃) := by
    have hpos : 0 < (Q ⊓ Q₂).relIndex E₃ := Nat.pos_of_ne_zero (relIndex_ne_zero_of_finite _ _)
    by_contra hlt
    push Not at hlt
    have : (Q ⊓ Q₂).relIndex E₃ * Nat.card ↥(Q ⊓ Q₂ ⊓ E₃) < p * p ^ 2 := by
      calc (Q ⊓ Q₂).relIndex E₃ * Nat.card ↥(Q ⊓ Q₂ ⊓ E₃) ≤ p * Nat.card ↥(Q ⊓ Q₂ ⊓ E₃) :=
            Nat.mul_le_mul_right _ hrel
        _ < p * p ^ 2 := Nat.mul_lt_mul_of_pos_left hlt hp.pos
    rw [hmul] at this
    have e : p * p ^ 2 = p ^ 3 := by ring
    omega
  have hFel : Open.IsElemAbelian p (Q ⊓ Q₂ ⊓ E₃) := IsElemAbelian.mono inf_le_right hE₃
  obtain ⟨E, hEF, hEel, hEc⟩ := exists_vertex_le hp hFel hcardF
  exact ⟨E, hEel, hEc, fun u hu g => hZc u (hEF hu).1 g⟩

end NonChar

section Four

variable {G : Type} [Group G] [Finite G] {z t g : G} {p : ℕ}

omit [Finite G] in
theorem abelian_of_inverted {K : Subgroup G} {t : G} (hK : ∀ y ∈ K, t * y * t⁻¹ = y⁻¹) :
    ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
  intro a ha b hb
  have h1 := hK (a * b) (K.mul_mem ha hb)
  have h2 : t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
  rw [h2, hK a ha, hK b hb, mul_inv_rev] at h1
  have h3 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := h1
  have h4 := congrArg (fun w => w⁻¹) h3
  simpa using h4.symm

omit [Finite G] in
theorem isElemAbelian_subgroupOf' {p : ℕ} {E P : Subgroup G} (hE : Open.IsElemAbelian p E) :
    Open.IsElemAbelian p (E.subgroupOf P) := CFSG.Open.IsElemAbelian.subgroupOf hE P


theorem lemma19_4 (h : Ab G z t g p) {U : Subgroup G} (hU : IsU z p U) :
    ((Qof p (Cen z) U).subgroupOf (Op p (Cen z))).Characteristic := by
  have hpr : Fact p.Prime := ⟨h.prime⟩
  have hPp : IsPGroup p ↥(Op p (Cen z)) := isPGroup_Op p _
  have hTP : ∀ x ∈ Op p (Cen z), t * x * t⁻¹ ∈ Op p (Cen z) := fun x hx => Op_norm p _ h.t_mem_M hx
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t2
  have hfixiff : ∀ y : G, t * y * t⁻¹ = y → t * y = y * t := fun y hy => by
    calc t * y = (t * y * t⁻¹) * t := by group
      _ = y * t := by rw [hy]
  have FA : ∀ V : Subgroup G, NEp p (Op p (Cen z)) V → ∀ x ∈ Op p (Cen z), (∀ u ∈ V, x * u = u * x) →
      t * x = x * t → x ^ p = 1 → x = 1 := fun V hV x hx hxV hxt hxp =>
    by_contra fun hx1 => factA h (IsU_of_NEp hV) hx hxV hxt hxp hx1
  refine ⟨fun ϕ => ?_⟩
  by_contra hne
  have hinv := lemma19_3a h hU
  have hQc : ∀ a ∈ Qof p (Cen z) U, ∀ b ∈ Qof p (Cen z) U, a * b = b * a := abelian_of_inverted hinv
  have hQP : Qof p (Cen z) U ≤ Op p (Cen z) := inf_le_left
  have hQ'c : ∀ a ∈ (Qof p (Cen z) U).subgroupOf (Op p (Cen z)), ∀ b ∈ (Qof p (Cen z) U).subgroupOf (Op p (Cen z)),
      a * b = b * a := fun a ha b hb => Subtype.ext (hQc a.1 ha b.1 hb)
  have hNE : IsNormalEp2 p (Op p (Cen z)) U := ⟨hU.1, fun g' hg' => by
      rw [Subgroup.mem_normalizer_iff]
      intro u
      have hn := (NEp_of_IsU hU).2.1
      refine ⟨fun hu => hn g' hg' u hu, fun hu => ?_⟩
      have := hn g'⁻¹ ((Op p (Cen z)).inv_mem hg') _ hu
      have e : g'⁻¹ * (g' * u * g'⁻¹) * g'⁻¹⁻¹ = u := by group
      rwa [e] at this,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p U).mp hU.2.2.1, hU.2.2.2⟩
  obtain ⟨-, hrel, hrk⟩ := ig10_20_ii h.prime hPp hNE
  have hQi : ((Qof p (Cen z) U).subgroupOf (Op p (Cen z))).index ≤ p := by
    have : (Qof p (Cen z) U).relIndex (Op p (Cen z)) = (centralizer (U : Set G)).relIndex (Op p (Cen z)) := by
      rw [← Subgroup.inf_relIndex_right (centralizer (U : Set G)) (Op p (Cen z))]
      unfold Qof
      rw [inf_comm]
    show (Qof p (Cen z) U).relIndex (Op p (Cen z)) ≤ p
    rw [this]; exact hrel
  have h3 : 3 ≤ Open.pRank p (centralizer (U : Set G) ⊓ Op p (Cen z)) := by
    rw [hrk]
    have := h.rank
    rwa [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank h.prime] at this
  obtain ⟨E₃, hE₃le, hE₃el, hE₃c⟩ := exists_isElemAbelian_of_le_pRank h.prime h3
  have hE₃Q : E₃ ≤ Qof p (Cen z) U := fun x hx => ⟨(hE₃le hx).2, (hE₃le hx).1⟩
  have hE₃P : E₃ ≤ Op p (Cen z) := hE₃Q.trans hQP
  have hE₃'c : Nat.card ↥(E₃.subgroupOf (Op p (Cen z))) = p ^ 3 := by
    rw [← hE₃c]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₃P).toEquiv
  obtain ⟨E', hE'el, hE'c, hE'cent⟩ := exists_central_of_not_char h.prime hPp hQ'c hQi ϕ hne
    (Subgroup.subgroupOf_mono (Op p (Cen z)) hE₃Q) (isElemAbelian_subgroupOf' hE₃el) hE₃'c
  set E : Subgroup G := E'.map (Op p (Cen z)).subtype with hE
  have hEP : E ≤ Op p (Cen z) := Subgroup.map_subtype_le _
  have hEcent : ∀ u ∈ E, ∀ x ∈ Op p (Cen z), x * u = u * x := by
    rintro _ ⟨e, he, rfl⟩ x hx
    exact congrArg Subtype.val (hE'cent e he ⟨x, hx⟩)
  have hEnep : NEp p (Op p (Cen z)) E := ⟨hEP, fun g' hg' u hu => by
      rw [show g' * u * g'⁻¹ = u by rw [hEcent u hu g' hg']; group]; exact hu,
    CFSG.SectionRank.isElemAbelian_map hE'el _, by rw [hE, Subgroup.card_map_of_injective (Op p (Cen z)).subtype_injective, hE'c]⟩
  have hPinv := inverted_of_no_fixed hPp h.t2 hTP (fun e he hte hep =>
    FA E hEnep e he (fun u hu => hEcent u hu e he) (hfixiff e hte) hep)
  have hPc := abelian_of_inverted hPinv
  apply hne
  have hQP' : Op p (Cen z) ≤ Qof p (Cen z) U := fun y hy =>
    ⟨hy, Subgroup.mem_centralizer_iff.mpr fun u hu => hPc u (hU.1 hu) y hy⟩
  have htop : (Qof p (Cen z) U).subgroupOf (Op p (Cen z)) = ⊤ := Subgroup.subgroupOf_eq_top.mpr hQP'
  rw [htop, Subgroup.comap_top]

end Four

end CFSG.GH74.GLS.Stage2.Final.Thm4.L193
