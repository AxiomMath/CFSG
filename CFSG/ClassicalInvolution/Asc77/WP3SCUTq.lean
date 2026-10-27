module

public import CFSG.ClassicalInvolution.Asc77.AscSixBasic
public import CFSG.ClassicalInvolution.Asc77.WP3Layer

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open scoped commutatorElement

section Normalizer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem mem_normalizer_of_commutes_involution (hΩ : ConjInvariant Ω)
    (hT : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {N : Subgroup G} {w : G} (hN : N ∈ Ω)
    (hw : IsUniqueInvolution N w) {x : G} (hx : x * w = w * x) :
    x ∈ Subgroup.normalizer (N : Set G) := by
  have h1 : IsUniqueInvolution (conjSub x N) (x * w * x⁻¹) := hw.conj x
  have e : x * w * x⁻¹ = w := by rw [hx]; group
  rw [e] at h1
  exact mem_normalizer_iff_conjSub_eq.mpr (hT N hN _ ⟨hΩ x N hN, w, hw, h1⟩)

end Normalizer

section Transfer

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_of_conj_mem {X S : Subgroup G}
    (h : ∀ g ∈ X, ∀ s ∈ S, g * s * g⁻¹ ∈ S) : X ≤ Subgroup.normalizer (S : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨fun hs => h g hg s hs, fun hs => ?_⟩
  have := h g⁻¹ (X.inv_mem hg) _ hs
  simpa [mul_assoc] using this

theorem mem_trivialOnQuot_of_centralizes_modOdd {K : Subgroup G} {z c : G}
    (hK : IsClassicalMember p f K z) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hcK : c ∈ trivialOnQuot K) {x : G} (hxC : x ∈ Subgroup.centralizer ({c} : Set G))
    (hxN : x ∈ Subgroup.normalizer (K : Set G))
    (hcomm : ∀ y ∈ modOdd c (exactCore c K),
      oddQuotMk c ⟨x, hxC⟩ * y = y * oddQuotMk c ⟨x, hxC⟩) : x ∈ trivialOnQuot K := by
  classical
  set E := exactCore c K with hE
  have hxc : x * c * x⁻¹ = c := conj_eq_of_mem_centralizer_singleton hxC
  have hxE : conjSub x E = E := by
    have := exactCore_conjSub x c K
    rw [hxc, conjSub_eq_of_mem_normalizer hxN] at this
    exact this.symm
  have hEC : E ≤ Subgroup.centralizer ({c} : Set G) := exactCore_le_centralizer c K
  have hEK : E ≤ K := exactCore_le_left c K
  have hcomm' : ∀ e ∈ E, x * e * x⁻¹ * e⁻¹ ∈ oddCoreIn K := by
    intro e he
    have heC := hEC he
    have hxe : x * e * x⁻¹ ∈ E := by
      have h := conj_mem_conjSub (n := x) he
      rwa [hxE] at h
    have huE : x * e * x⁻¹ * e⁻¹ ∈ E := E.mul_mem hxe (E.inv_mem he)
    have huC := hEC huE
    have h1 : oddQuotMk c ⟨x * e * x⁻¹ * e⁻¹, huC⟩ = 1 := by
      have h := hcomm (oddQuotMk c ⟨e, heC⟩) (oddQuotMk_mem_modOdd he heC)
      have e1 : (⟨x * e * x⁻¹ * e⁻¹, huC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) =
          ⟨x, hxC⟩ * ⟨e, heC⟩ * ⟨x, hxC⟩⁻¹ * ⟨e, heC⟩⁻¹ := rfl
      rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, h]
      group
    have h2 : x * e * x⁻¹ * e⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({c} : Set G)) :=
      ⟨⟨_, huC⟩, oddQuotMk_eq_one_iff.mp h1, rfl⟩
    have hS : E ⊓ oddCoreIn (Subgroup.centralizer ({c} : Set G)) ≤ oddCoreIn E := by
      refine le_oddCoreIn_of_normalizes inf_le_left ?_ ?_
      · refine le_normalizer_of_conj_mem fun g hg s hs => ⟨E.mul_mem (E.mul_mem hg hs.1)
          (E.inv_mem hg), conj_mem_oddCoreIn (hEC hg) hs.2⟩
      · exact (odd_card_oddCoreIn (Subgroup.centralizer ({c} : Set G))).of_dvd_nat
          (Subgroup.card_dvd_of_le inf_le_right)
    have h3 := hS ⟨huE, h2⟩
    rw [oddCoreIn_exactCore hK hc2 hcK] at h3
    exact h3.2
  rw [mem_trivialOnQuot_iff]
  refine ⟨hxN, fun y hy => ?_⟩
  obtain ⟨e, he, n, hn, rfl⟩ := exactCore_cover hK hc2 hcK y hy
  have hxn : x * n * x⁻¹ ∈ oddCoreIn K := conj_mem_oddCoreIn_of_mem_normalizer hxN hn
  have h4 : x * n * x⁻¹ * n⁻¹ ∈ oddCoreIn K := (oddCoreIn K).mul_mem hxn ((oddCoreIn K).inv_mem hn)
  have h5 : e * (x * n * x⁻¹ * n⁻¹) * e⁻¹ ∈ oddCoreIn K := conj_mem_oddCoreIn (hEK he) h4
  have e2 : ⁅x, e * n⁆ = (x * e * x⁻¹ * e⁻¹) * (e * (x * n * x⁻¹ * n⁻¹) * e⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e2]
  exact (oddCoreIn K).mul_mem (hcomm' e he) h5

end Transfer

section Fixed

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_conj_involution_commuting {N F : Subgroup G} (hN : Odd (Nat.card N))
    (hFN : F ≤ Subgroup.normalizer (N : Set G)) (hF2 : IsPGroup 2 F) {w : G} (hw2 : w * w = 1)
    (hcomm : ∀ x ∈ F, (x * w * x⁻¹) * w ∈ N) :
    ∃ o ∈ N, ∀ x ∈ F, x * (o * w * o⁻¹) = (o * w * o⁻¹) * x := by
  classical
  let N' : Subgroup (ConjAct G) := N.map ConjAct.toConjAct.toMonoidHom
  let S : Set G := MulAction.orbit ↥N' w
  have hSmem : ∀ s, s ∈ S ↔ ∃ o ∈ N, s = o * w * o⁻¹ := by
    intro s
    constructor
    · rintro ⟨⟨c, hc⟩, rfl⟩
      obtain ⟨o, ho, rfl⟩ := hc
      exact ⟨o, ho, by simp [Subgroup.smul_def, ConjAct.smul_def]⟩
    · rintro ⟨o, ho, rfl⟩
      exact ⟨⟨ConjAct.toConjAct o, o, ho, rfl⟩, by simp [Subgroup.smul_def, ConjAct.smul_def]⟩
  have hS : ∀ x ∈ F, ∀ s ∈ S, x * s * x⁻¹ ∈ S := by
    intro x hx s hs
    obtain ⟨o, ho, rfl⟩ := (hSmem s).mp hs
    have hxw2 : (x * w * x⁻¹) * (x * w * x⁻¹) = 1 := by
      have : (x * w * x⁻¹) * (x * w * x⁻¹) = x * (w * w) * x⁻¹ := by group
      rw [this, hw2]
      group
    obtain ⟨o', ho', hxw⟩ := exists_conj_of_mul_mem hw2 hxw2 hN (hcomm x hx)
    refine (hSmem _).mpr ⟨(x * o * x⁻¹) * o', ?_, ?_⟩
    · refine N.mul_mem ?_ ho'
      have := Subgroup.mem_normalizer_iff.mp (hFN hx) o
      exact this.mp ho
    · calc x * (o * w * o⁻¹) * x⁻¹ = (x * o * x⁻¹) * (x * w * x⁻¹) * (x * o * x⁻¹)⁻¹ := by
            group
        _ = _ := by rw [hxw]; group
  let _ : MulAction ↥F ↥S :=
    { smul := fun x s => ⟨(x : G) * s * (x : G)⁻¹, hS x x.2 s s.2⟩
      one_smul := fun s => Subtype.ext (by simp [HSMul.hSMul, SMul.smul])
      mul_smul := fun a b s => Subtype.ext (by simp [HSMul.hSMul, SMul.smul, mul_assoc]) }
  have hcard : Nat.card S ∣ Nat.card N := by
    have h1 : Nat.card S = Nat.card (↥N' ⧸ MulAction.stabilizer ↥N' w) :=
      Nat.card_congr (MulAction.orbitEquivQuotientStabilizer ↥N' w)
    have h2 : Nat.card N' = Nat.card N := Subgroup.card_map_of_injective
      ConjAct.toConjAct.injective
    rw [h1, ← h2]
    exact (MulAction.stabilizer ↥N' w).index_dvd_card
  have hodd : ¬ 2 ∣ Nat.card S := fun h2 =>
    (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr (h2.trans hcard))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs⟩ := hF2.nonempty_fixed_point_of_prime_not_dvd_card (α := ↥S) hodd
  obtain ⟨o, ho, hso⟩ := (hSmem s).mp s.2
  refine ⟨o, ho, fun x hx => ?_⟩
  have h1 := MulAction.mem_fixedPoints.mp hs ⟨x, hx⟩
  have h2 : (x : G) * s * (x : G)⁻¹ = s := congrArg Subtype.val h1
  rw [← hso]
  calc x * (s : G) = x * s * x⁻¹ * x := by group
    _ = s * x := by rw [h2]

end Fixed

end CFSG.ClassicalInvolution.Asc77
