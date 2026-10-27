module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1314

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1314b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

section Transport

variable {G : Type} [Group G] [Finite G]

theorem card_barX_of_isPGroup {p : ℕ} (hp : p.Prime) {X E : Subgroup G} (hE : IsPGroup p E)
    (hEX : E ≤ X) : Nat.card (barX p X E) = Nat.card E := by
  have hfi := injective_barX_comp hp hE hEX
  have hrange : barX p X E =
      ((QuotientGroup.mk' (GLAPPrimeCore p ↥X)).comp (E.subgroupOf X).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [hrange, ← Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv]

theorem mk_ne_one {p : ℕ} [Fact p.Prime] {X : Subgroup G} {x : G} (hxX : x ∈ X) (hxp : x ^ p = 1)
    (hx1 : x ≠ 1) : QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨x, hxX⟩ : ↥X) ≠ 1 := by
  intro h1
  have hmem : (⟨x, hxX⟩ : ↥X) ∈ GLAPPrimeCore p ↥X := (QuotientGroup.eq_one_iff _).1 h1
  exact hx1 (Claims1314.eq_one_of_mem_coreOf_of_pow (Lemma1314c.mem_core_iff.2 ⟨hxX, hmem⟩) hxp)

omit [Finite G] in
theorem isPGroup_zpowers {p : ℕ} {x : G} (hxp : x ^ p = 1) : IsPGroup p (Subgroup.zpowers x) := by
  intro g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, ?_⟩
  rw [pow_one]
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hxp, one_zpow]

theorem core_barX_le {p : ℕ} [hp : Fact p.Prime] {C D : Subgroup G} (hDC : D ≤ C) :
    GLAPPrimeCoreOf p (barX p C D) ≤ barX p C (GLAPPrimeCoreOf p D) := by
  classical
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥C) with hπ
  set W := GLAPPrimeCoreOf p (barX p C D) with hW
  set V : Subgroup G := D ⊓ (W.comap π).map C.subtype with hV
  have hcopV : Nat.Coprime p (Nat.card ↥V) := by
    have hcard : Nat.card ↥(W.comap π) = Nat.card ↥(GLAPPrimeCore p ↥C) * Nat.card ↥W :=
      QuotientGroup.card_preimage_mk (GLAPPrimeCore p ↥C) (W : Set (↥C ⧸ GLAPPrimeCore p ↥C))
    have h1 : Nat.Coprime p (Nat.card ↥((W.comap π).map C.subtype)) := by
      rw [Subgroup.card_map_of_injective C.subtype_injective, hcard]
      exact Nat.Coprime.mul_right (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥C))
        (Lemma114Layer.coprime_card_glaPPrimeCoreOf _)
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) h1
  have hDN : D ≤ Subgroup.normalizer (V : Set G) := by
    apply Lemma114Layer.le_normalizer_of_conj
    intro w hw y hy
    obtain ⟨hyD, y', hy', hyy'⟩ := hy
    refine ⟨D.mul_mem (D.mul_mem hw hyD) (D.inv_mem hw), ?_⟩
    refine ⟨⟨w, hDC hw⟩ * y' * (⟨w, hDC hw⟩ : ↥C)⁻¹, ?_, ?_⟩
    · show π (⟨w, hDC hw⟩ * y' * (⟨w, hDC hw⟩ : ↥C)⁻¹) ∈ W
      rw [map_mul, map_mul, map_inv]
      have hwS : π ⟨w, hDC hw⟩ ∈ barX p C D := ⟨⟨w, hDC hw⟩, Subgroup.mem_subgroupOf.2 hw, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1
        (Lemma114Layer.le_normalizer_glaPPrimeCoreOf p _ hwS) _).1 hy'
    · rw [← hyy']
      simp
  have hVcore : V ≤ GLAPPrimeCoreOf p D :=
    Lemma114Layer.le_glaPPrimeCoreOf_of_normal' inf_le_left hDN hcopV
  intro z hz
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 (Lemma114Layer.glaPPrimeCoreOf_le_self p _ hz)
  exact Subgroup.mem_map.2 ⟨c, Subgroup.mem_subgroupOf.2
    (hVcore ⟨Subgroup.mem_subgroupOf.1 hc, c, hz, rfl⟩), rfl⟩

theorem layer_barX_le {p : ℕ} [hp : Fact p.Prime] {C D : Subgroup G} (hDC : D ≤ C) :
    GLAPLayer p (barX p C D) ≤ barX p C (GLAPLayer p D) := by
  set ψ := Prop115b.quotHomOf (p := p) hDC with hψ
  have hmap : (⊤ : Subgroup ↥D).map ψ = barX p C D := by
    rw [← Prop115b.map_subgroupOf_quotHomOf hDC le_rfl, Subgroup.subgroupOf_self]
  have hker : Nat.Coprime p (Nat.card ↥((⊤ : Subgroup ↥D) ⊓ ψ.ker)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      (Prop115b.coprime_card_ker_quotHomOf hDC)
  have hker' : Nat.Coprime p (Nat.card ↥((⊤ : Subgroup ↥D) ⊓ D.subtype.ker)) := by
    rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  refine sSup_le fun J hJ => ?_
  have hJ' : GLAPComponent p ((⊤ : Subgroup ↥D).map ψ) J := by
    rw [hmap]
    exact hJ
  obtain ⟨K₀, hK₀, hK₀J⟩ := exists_glaPComponent_map_eq hp.out ψ hker hJ'
  have hH : GLAPComponent p D (K₀.map D.subtype) := by
    have h1 := glaPComponent_map hp.out D.subtype hker' hK₀
    rwa [Subgroup.map_top, Subgroup.range_subtype] at h1
  have hHD : K₀.map D.subtype ≤ D := Subgroup.map_subtype_le K₀
  have hbar : barX p C (K₀.map D.subtype) = J := by
    rw [← Prop115b.map_subgroupOf_quotHomOf hDC hHD, ← hK₀J]
    congr 1
    exact Subgroup.comap_map_eq_self_of_injective D.subtype_injective K₀
  rw [← hbar]
  exact CFSG.LocalAnalysis.GLTheoremB.barX_mono p (le_sSup (s := {L | GLAPComponent p D L}) hH)

end Transport

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1314b

end
