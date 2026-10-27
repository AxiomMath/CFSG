module

public import CFSG.GH74.Uniqueness.SU.SU13TB3W

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_sylow_sub_ge {p : ℕ} [Fact p.Prime] {W P : Subgroup G} (hPW : P ≤ W) (hPp : IsPGroup p P) :
    ∃ V : Subgroup G, P ≤ V ∧ V ≤ W ∧ IsPGroup p V ∧ ¬ p ∣ V.relIndex W ∧
      Nat.card V = p ^ (Nat.card W).factorization p := by
  have hP' : IsPGroup p ↥(P.subgroupOf W) :=
    IsPGroup.of_equiv hPp (Subgroup.subgroupOfEquivOfLe hPW).symm
  obtain ⟨S, hS⟩ := hP'.exists_le_sylow
  refine ⟨(S : Subgroup ↥W).map W.subtype, ?_, Subgroup.map_subtype_le _, S.isPGroup'.map _, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hPW hx⟩, hS (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  · have hsub : ((S : Subgroup ↥W).map W.subtype).subgroupOf W = S := by
      unfold Subgroup.subgroupOf
      exact Subgroup.comap_map_eq_self_of_injective W.subtype_injective _
    have h1 : ((S : Subgroup ↥W).map W.subtype).relIndex W = (S : Subgroup ↥W).index := by
      unfold Subgroup.relIndex
      rw [hsub]
    rw [h1]
    exact S.not_dvd_index
  · rw [Subgroup.card_map_of_injective W.subtype_injective]
    exact Sylow.card_eq_multiplicity S

omit [Finite G] in
theorem F_le_centralizer (e : Elts G z) (f : FPart10 z e) {g : G} (hg : g ∈ f.F) :
    g ∈ centralizer ({e.s₁} : Set G) := mem_centralizer_singleton_iff.mpr (f.F_s₁ g hg)

theorem sup_invariant (hz : orderOf z = 2) (e : Elts G z) (f : FPart10 z e) {p : ℕ} [Fact p.Prime]
    {V : Subgroup G} (hVW : V ≤ oc (centralizer ({e.s₁} : Set G))) (hVp : IsPGroup p V)
    (hVidx : ¬ p ∣ V.relIndex (oc (centralizer ({e.s₁} : Set G)))) :
    ∀ g ∈ f.F, ∀ u ∈ zpowers e.s₁ ⊔ V, g * u * g⁻¹ ∈ zpowers e.s₁ ⊔ V := by
  set W := oc (centralizer ({e.s₁} : Set G)) with hW
  intro g hg u hu
  have hgX := F_le_centralizer e f hg
  obtain ⟨c, hc, v, hv, rfl⟩ := SU1.mem_sup_of_commute (A := zpowers e.s₁) (B := V)
    (fun a ha b hb => zpowers_comm_of_mem_centralizer (oc_le _ (hVW hb)) ha) hu
  have hKW : V.map (MulAut.conj g).toMonoidHom ≤ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_oc hgX (hVW hx)
  obtain ⟨w, hwW, hw⟩ := CFSG.GH74.GLS.Bg.Thompson.exists_conj_into_sylow (p := p) hKW
    (hVp.map _) hVW hVp hVidx
  have hv' := hw (g * v * g⁻¹) ⟨v, hv, by simp [MulAut.conj_apply]⟩
  set v' := w⁻¹ * (g * v * g⁻¹) * w with hv'def
  have hgv : g * v * g⁻¹ = (w * v' * w⁻¹ * v'⁻¹) * v' := by rw [hv'def]; group
  have hcomm := comm_mem_P hz e f hwW (hVW hv')
  have hgc : g * c * g⁻¹ = c := by
    have := zpowers_comm_of_mem_centralizer hgX hc
    rw [← this]; group
  have heq : g * (c * v) * g⁻¹ = (c * (w * v' * w⁻¹ * v'⁻¹)) * v' := by
    calc g * (c * v) * g⁻¹ = (g * c * g⁻¹) * (g * v * g⁻¹) := by group
      _ = c * ((w * v' * w⁻¹ * v'⁻¹) * v') := by rw [hgc, hgv]
      _ = (c * (w * v' * w⁻¹ * v'⁻¹)) * v' := by group
  rw [heq]
  exact mul_mem (mem_sup_left (mul_mem hc hcomm)) (mem_sup_right hv')

theorem U_le_P (hz : orderOf z = 2) (e : Elts G z) (f : FPart10 z e) {U : Subgroup G}
    (hUW : U ≤ oc (centralizer ({e.s₁} : Set G)))
    (hUinv : ∀ g ∈ f.F, ∀ u ∈ U, g * u * g⁻¹ ∈ U) {q : G} (hq : q ∈ f.F) (hq1 : q ≠ 1)
    (hqU : ∀ u ∈ U, q * u = u * q) : U ≤ zpowers e.s₁ := by
  set K : Subgroup G := f.F ⊓ centralizer (U : Set G) with hK
  have hqK : q ∈ K := mem_inf.mpr ⟨hq, mem_centralizer_iff.mpr fun u hu => (hqU u hu).symm⟩
  have hKne : K ≠ ⊥ := fun h => hq1 (mem_bot.mp (h ▸ hqK))
  have hnorm : ∀ g ∈ f.F, ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro g hg k hk
    obtain ⟨hkF, hkc⟩ := mem_inf.mp hk
    refine mem_inf.mpr ⟨f.F.mul_mem (f.F.mul_mem hg hkF) (f.F.inv_mem hg), mem_centralizer_iff.mpr ?_⟩
    intro u hu
    have hu' : g⁻¹ * u * g ∈ U := by
      have := hUinv g⁻¹ (f.F.inv_mem hg) u hu
      simpa using this
    have := mem_centralizer_iff.mp hkc _ hu'
    calc u * (g * k * g⁻¹) = g * ((g⁻¹ * u * g) * k) * g⁻¹ := by group
      _ = g * (k * (g⁻¹ * u * g)) * g⁻¹ := by rw [this]
      _ = g * k * g⁻¹ * u := by group
  have hzK : z ∈ K := f.F_socle K inf_le_left hnorm hKne
  have hzU : ∀ u ∈ U, u * z = z * u := fun u hu => mem_centralizer_iff.mp (mem_inf.mp hzK).2 u hu
  intro u hu
  obtain ⟨c, hc, h1⟩ := z_inv_mod hz e f (hUW hu)
  have h2 : z * u * z⁻¹ = u := by rw [← hzU u hu]; group
  have h3 : u * u = c * c := by
    have : u = c * c * u⁻¹ := by rw [← h1, h2]
    calc u * u = (c * c * u⁻¹) * u := by rw [← this]
      _ = c * c := by group
  have hodd : Odd (orderOf u) :=
    Odd.of_dvd_nat (odd_card_oc _) (Subgroup.orderOf_dvd_natCard _ (hUW hu))
  obtain ⟨m, hm⟩ := hodd
  have hu1 : u = (u * u) ^ (m + 1) := by
    have : (u * u) ^ (m + 1) = u := by
      rw [← pow_two, ← pow_mul, show 2 * (m + 1) = orderOf u + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    exact this.symm
  rw [hu1, h3]
  exact pow_mem (mul_mem hc hc) _

end CFSG.GH74.Uniqueness.SU.SU13
