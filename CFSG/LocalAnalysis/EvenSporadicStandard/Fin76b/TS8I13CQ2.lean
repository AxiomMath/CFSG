module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13CQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13HE64a
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8E614Def

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

theorem conj_mem_innAutE {G : Type*} [Group G] {E : Subgroup G} (φ : MulAut ↥E)
    {i : MulAut ↥E} (hi : i ∈ innAutE E) : φ * i * φ⁻¹ ∈ innAutE E := by
  obtain ⟨e, rfl⟩ := hi
  refine ⟨φ e, ?_⟩
  refine MulEquiv.ext fun f => ?_
  have h : (φ * MulAut.conj e * φ⁻¹) f = φ (e * φ.symm f * e⁻¹) := by
    simp [MulAut.conj_apply]
  rw [h]
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem card_innAutE_of_pi {G : Type*} [Group G] {E : Subgroup G} {t : G}
    {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π) (hE : EFacts614 E t) :
    Nat.card ↥(innAutE E) = 16 := by
  have h1 := Subgroup.card_ker_mul_card_range π
  have hker : π.ker = innAutE E := by
    ext φ
    rw [MonoidHom.mem_ker]
    exact hπ.ker φ
  have hrange : π.range = ⊤ := MonoidHom.range_eq_top.2 hπ.surj
  have hcard : Nat.card ↥π.range = 120 := by
    rw [hrange, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]
  rw [hker, hcard, hE.card_aut] at h1
  omega

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ)

include c in
theorem innAutE_comm' {a b : MulAut ↥E} (ha : a ∈ innAutE E) (hb : b ∈ innAutE E) :
    a * b = b * a := by
  obtain ⟨e, rfl⟩ := ha
  obtain ⟨e', rfl⟩ := hb
  refine MulEquiv.ext fun f => ?_
  apply Subtype.ext
  show (e : G) * ((e' : G) * f * (e' : G)⁻¹) * (e : G)⁻¹ =
    (e' : G) * ((e : G) * f * (e : G)⁻¹) * (e' : G)⁻¹
  rcases c.h.E_comm e e.2 e' e'.2 with h1 | h1
  · calc (e : G) * ((e' : G) * f * (e' : G)⁻¹) * (e : G)⁻¹
        = ((e : G) * e') * f * ((e : G) * e')⁻¹ := by group
      _ = ((e' : G) * e) * f * ((e' : G) * e)⁻¹ := by rw [h1]
      _ = (e' : G) * ((e : G) * f * (e : G)⁻¹) * (e' : G)⁻¹ := by group
  · have ht : ∀ g ∈ E, g * t = t * g := c.h.t_comm_E
    have hft : (f : G) * t = t * f := ht f f.2
    have hee : ((e' : G) * e) * t = t * ((e' : G) * e) := ht _ (mul_mem e'.2 e.2)
    calc (e : G) * ((e' : G) * f * (e' : G)⁻¹) * (e : G)⁻¹
        = ((e : G) * e') * f * ((e : G) * e')⁻¹ := by group
      _ = (t * ((e' : G) * e)) * f * (t * ((e' : G) * e))⁻¹ := by rw [h1]
      _ = ((e' : G) * e) * (t * f * t⁻¹) * ((e' : G) * e)⁻¹ := by
          have : t * ((e' : G) * e) = ((e' : G) * e) * t := hee.symm
          rw [this]
          group
      _ = ((e' : G) * e) * f * ((e' : G) * e)⁻¹ := by
          have : t * f * t⁻¹ = f := by rw [← hft]; group
          rw [this]
      _ = (e' : G) * ((e : G) * f * (e : G)⁻¹) * (e' : G)⁻¹ := by group

include c in
theorem cent_big_of_inn {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π)
    (hD : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔ π a = π b) (hE : EFacts614 E t)
    (hFQ : ∀ a ∈ innAutE E, ∀ b ∈ innAutE E, ∃ c₀ : MulAut ↥E, c₀ ∉ innAutE E ∧ c₀ * c₀ = 1 ∧
      c₀ * a = a * c₀ ∧ c₀ * b = b * c₀)
    (ψ : ↥c.rho.range) (ha : ψ.1.1 ∈ innAutE E) (hb : ψ.1.2 ∈ innAutE E) :
    2 ^ 9 ∣ Nat.card ↥(Subgroup.centralizer ({ψ} : Set ↥c.rho.range)) := by
  classical
  have hcardI : Nat.card ↥(innAutE E) = 16 := card_innAutE_of_pi hπ hE
  let N : Subgroup (MulAut ↥E × MulAut ↥E) := (innAutE E).prod (innAutE E)
  have hNle : N ≤ c.rho.range := by
    intro p hp
    exact (hD p.1 p.2).2 (by rw [(hπ.ker p.1).2 hp.1, (hπ.ker p.2).2 hp.2])
  let NΓ : Subgroup ↥c.rho.range := N.subgroupOf c.rho.range
  have hcardN : Nat.card ↥NΓ = 256 := by
    have h1 : Nat.card ↥NΓ = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNle).toEquiv
    have h2 : Nat.card ↥N = Nat.card ↥(innAutE E) * Nat.card ↥(innAutE E) := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (Subgroup.prodEquiv (innAutE E) (innAutE E)).toEquiv
    rw [h1, h2, hcardI]
  obtain ⟨c₀, hc₀I, hc₀2, hc₀a, hc₀b⟩ := hFQ _ ha _ hb
  let g : ↥c.rho.range := ⟨(c₀, c₀), (hD c₀ c₀).2 rfl⟩
  have hgg : g * g = 1 := Subtype.ext (Prod.ext hc₀2 hc₀2)
  have hgN : ∀ x ∈ NΓ, g * x * g⁻¹ ∈ NΓ := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hx' : x.1 ∈ N := hx
    refine ⟨?_, ?_⟩
    · show c₀ * x.1.1 * c₀⁻¹ ∈ innAutE E
      exact conj_mem_innAutE c₀ hx'.1
    · show c₀ * x.1.2 * c₀⁻¹ ∈ innAutE E
      exact conj_mem_innAutE c₀ hx'.2
  have hgNΓ : g ∉ NΓ := by
    intro h
    rw [Subgroup.mem_subgroupOf] at h
    exact hc₀I h.1
  have hsq : g * g ∈ NΓ := by rw [hgg]; exact NΓ.one_mem
  have hNC : NΓ ≤ Subgroup.centralizer ({ψ} : Set ↥c.rho.range) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    refine Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (Prod.ext ?_ ?_))
    · exact (c.innAutE_comm' ha hx.1).symm
    · exact (c.innAutE_comm' hb hx.2).symm
  have hgC : g ∈ Subgroup.centralizer ({ψ} : Set ↥c.rho.range) := by
    refine Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (Prod.ext ?_ ?_))
    · exact hc₀a
    · exact hc₀b
  have hKC : NΓ ⊔ Subgroup.zpowers g ≤ Subgroup.centralizer ({ψ} : Set ↥c.rho.range) :=
    sup_le hNC (Subgroup.zpowers_le.2 hgC)
  have hle2 := I13HE64.card_sup_zpowers_le NΓ g hgN hsq
  have hdvd : Nat.card ↥NΓ ∣ Nat.card ↥(NΓ ⊔ Subgroup.zpowers g) :=
    Subgroup.card_dvd_of_le le_sup_left
  have hgK : g ∈ NΓ ⊔ Subgroup.zpowers g := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have hlt : Nat.card ↥NΓ < Nat.card ↥(NΓ ⊔ Subgroup.zpowers g) := by
    by_contra hnlt
    have heq : NΓ = NΓ ⊔ Subgroup.zpowers g :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (not_lt.1 hnlt)
    exact hgNΓ (heq ▸ hgK)
  obtain ⟨k, hk⟩ := hdvd
  have hK512 : Nat.card ↥(NΓ ⊔ Subgroup.zpowers g) = 512 := by
    rw [hcardN] at hle2 hlt hk
    omega
  have := Subgroup.card_dvd_of_le hKC
  rw [hK512] at this
  simpa using this

variable {c}

theorem IsRs.not_conj_z_of_mem_Qs_delta {Rs : Subgroup G} (hR : c.IsRs Rs)
    {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π)
    (hD : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔ π a = π b) (hE : EFacts614 E t)
    (hFQ : ∀ a ∈ innAutE E, ∀ b ∈ innAutE E, ∃ c₀ : MulAut ↥E, c₀ ∉ innAutE E ∧ c₀ * c₀ = 1 ∧
      c₀ * a = a * c₀ ∧ c₀ * b = b * c₀)
    (hT : Nat.card T ≤ 512) {q : G} (hq : q ∈ c.Qs) (hq2 : q * q = 1)
    (hqz : ∃ g : G, q = g * z * g⁻¹) : False := by
  have hqR : q ∈ Rs ⊓ c.N1 := ⟨hR.Qs_le hq, c.Qs_le_N1 hq⟩
  obtain ⟨e₁, e₂, he⟩ := c.rho_Qs_mem hq
  have hbig := c.cent_big_of_inn hπ hD hE hFQ ⟨c.rho ⟨q, hqR.2⟩, ⟨⟨q, hqR.2⟩, rfl⟩⟩
    (by show (c.rho ⟨q, c.Qs_le_N1 hq⟩).1 ∈ innAutE E; rw [he]; exact ⟨e₁, rfl⟩)
    (by show (c.rho ⟨q, c.Qs_le_N1 hq⟩).2 ∈ innAutE E; rw [he]; exact ⟨e₂, rfl⟩)
  exact hR.not_conj_z_of_mem_R_pt hT hqR hq2 hbig hqz

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
