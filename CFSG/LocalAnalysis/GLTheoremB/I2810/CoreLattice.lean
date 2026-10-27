module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.LocalAnalysis.GLTheoremB.I2810.BlocksAux
import CFSG.GroupTheory.ElemAbelianClosure

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.CoreAux

namespace CoreLattice

variable {X : Type} [Group X]

@[expose] def kTriv (K A N : Subgroup X) (hN : ∀ k ∈ K, ∀ x ∈ N, k * x * k⁻¹ ∈ N) : Subgroup X where
  carrier := {k | k ∈ K ∧ ∀ x ∈ A, ⁅k, x⁆ ∈ N}
  one_mem' := ⟨K.one_mem, fun x _ => by simpa using N.one_mem⟩
  mul_mem' := by
    rintro k₁ k₂ ⟨hk₁, h₁⟩ ⟨hk₂, h₂⟩
    refine ⟨K.mul_mem hk₁ hk₂, fun x hx => ?_⟩
    have e : ⁅k₁ * k₂, x⁆ = (k₁ * ⁅k₂, x⁆ * k₁⁻¹) * ⁅k₁, x⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact N.mul_mem (hN k₁ hk₁ _ (h₂ x hx)) (h₁ x hx)
  inv_mem' := by
    rintro k ⟨hk, h⟩
    refine ⟨K.inv_mem hk, fun x hx => ?_⟩
    have e : ⁅k⁻¹, x⁆ = k⁻¹ * (⁅k, x⁆⁻¹) * k⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hN k⁻¹ (K.inv_mem hk) _ (N.inv_mem (h x hx))

theorem mem_kTriv {K A N : Subgroup X} {hN : ∀ k ∈ K, ∀ x ∈ N, k * x * k⁻¹ ∈ N} {k : X} :
    k ∈ kTriv K A N hN ↔ k ∈ K ∧ ∀ x ∈ A, ⁅k, x⁆ ∈ N := Iff.rfl

theorem zpowers_involution_cases {a : X} (ha2 : a ^ 2 = 1) {b : X} (hb : b ∈ Subgroup.zpowers a) :
    b = 1 ∨ b = a := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have h2 : a ^ (2 : ℤ) = 1 := by simpa using ha2
  rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem K_le_of_comm {K D : Subgroup X} {a : X} (ha2 : a ^ 2 = 1)
    (hKc : ⁅K, Subgroup.zpowers a⁆ = K) (hD : ∀ k ∈ K, ⁅k, a⁆ ∈ D) : K ≤ D := by
  rw [← hKc]
  refine Subgroup.commutator_le.2 fun k hk b hb => ?_
  rcases zpowers_involution_cases ha2 hb with rfl | rfl
  · simpa using D.one_mem
  · exact hD k hk

end CoreLattice

section Lattice
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem trans_lattice_proof (h : Setup28 W K S) (hR : Red28 W K S) {a : X} (haS : a ∈ S)
    (ha2 : a ^ 2 = 1) (htr : TransvOn (vOf W K S) a) :
    ∃ (u : X) (U₁ U₂ : Subgroup X), TLattice K (vOf W K S) a u U₁ U₂ := by
  obtain ⟨u, huV, hu1, hu⟩ := htr
  set V := vOf W K S with hV
  have haN : a ∈ Subgroup.normalizer (K : Set X) := h.hN haS
  have hKa : ∀ x ∈ K, a * x * a⁻¹ ∈ K := fun x hx => (Subgroup.mem_normalizer_iff.1 haN x).1 hx
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ha2)
  have hVK : ∀ k ∈ K, ∀ v ∈ V, k * v * k⁻¹ ∈ V := fun k hk v hv =>
    hR.v_nrm k (Subgroup.mem_sup_left hk) v hv
  have hu2 : u * u = 1 := by simpa [pow_two] using hR.v_elem.2 u huV
  have hau : a * u * a⁻¹ = u := by
    rcases hu u huV with h1 | h1
    · exact h1
    · exfalso
      rw [hu2] at h1
      apply hu1
      calc u = a⁻¹ * (a * u * a⁻¹) * a := by group
        _ = 1 := by rw [h1]; group
  let 𝒮 : Set (Subgroup X) := {Y | u ∈ Y ∧ ∀ k ∈ K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y}
  let U₁ : Subgroup X := sInf 𝒮
  have hU₁u : u ∈ U₁ := Subgroup.mem_sInf.2 fun Y hY => hY.1
  have hU₁K : ∀ k ∈ K, ∀ x ∈ U₁, k * x * k⁻¹ ∈ U₁ := fun k hk x hx =>
    Subgroup.mem_sInf.2 fun Y hY => hY.2 k hk x (Subgroup.mem_sInf.1 hx Y hY)
  have hgen : ∀ Y : Subgroup X, u ∈ Y → (∀ k ∈ K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y) → U₁ ≤ Y :=
    fun Y hY hYK => sInf_le ⟨hY, hYK⟩
  have hU₁V : U₁ ≤ V := hgen V huV hVK
  have hU₁a : ∀ x ∈ U₁, a * x * a⁻¹ ∈ U₁ := by
    intro x hx
    refine Subgroup.mem_sInf.2 fun Y hY => ?_
    have hZ : U₁ ≤ Y.comap (MulAut.conj a).toMonoidHom := by
      refine hgen _ ?_ ?_
      · show a * u * a⁻¹ ∈ Y
        rw [hau]; exact hY.1
      · intro k hk y hy
        show a * (k * y * k⁻¹) * a⁻¹ ∈ Y
        have e : a * (k * y * k⁻¹) * a⁻¹ = (a * k * a⁻¹) * (a * y * a⁻¹) * (a * k * a⁻¹)⁻¹ := by
          group
        rw [e]
        exact hY.2 _ (hKa k hk) _ hy
    exact hZ hx
  let 𝒯 : Set (Subgroup X) := {Y | Y ≤ U₁ ∧ u ∉ Y ∧ (∀ k ∈ K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y) ∧
    ∀ y ∈ Y, a * y * a⁻¹ ∈ Y}
  have hbot : (⊥ : Subgroup X) ∈ 𝒯 := by
    refine ⟨bot_le, fun hmem => hu1 (Subgroup.mem_bot.1 hmem), ?_, ?_⟩
    · intro k _ y hy
      rw [Subgroup.mem_bot.1 hy]; simp
    · intro y hy
      rw [Subgroup.mem_bot.1 hy]; simp
  obtain ⟨U₂, hU₂⟩ := Set.Finite.exists_maximal (Set.toFinite 𝒯) ⟨⊥, hbot⟩
  obtain ⟨hU₂U₁, hU₂u, hU₂K, hU₂a⟩ := hU₂.1
  refine ⟨u, U₁, U₂, ?_⟩
  have hfix : ∀ x ∈ U₂, a * x * a⁻¹ = x := by
    intro x hx
    rcases hu x (hU₁V (hU₂U₁ hx)) with h1 | h1
    · exact h1
    · exfalso
      apply hU₂u
      have : u = x⁻¹ * (a * x * a⁻¹) := by rw [h1]; group
      rw [this]
      exact U₂.mul_mem (U₂.inv_mem hx) (hU₂a x hx)
  refine ⟨hU₁u, hU₂u, ⟨hU₂U₁, hU₁V⟩, hu, hU₁K, hU₂K, hU₁a, hU₂a, hgen, hfix, ?_⟩
  intro Y hY₂ hYU₁ hYK hYa
  by_cases huY : u ∈ Y
  · right
    exact le_antisymm hYU₁ (hgen Y huY hYK)
  · left
    have hmem : Y ∈ 𝒯 := ⟨hYU₁, huY, hYK, hYa⟩
    exact le_antisymm (hU₂.2 hmem hY₂) hY₂

theorem trans_sectionM_of_lattice_proof (h : Setup28 W K S) (hR : Red28 W K S) {a : X}
    (haS : a ∈ S) (ha2 : a ^ 2 = 1) {u : X} {U₁ U₂ : Subgroup X}
    (hl : TLattice K (vOf W K S) a u U₁ U₂) (hKc : ⁅K, Subgroup.zpowers a⁆ = K) :
    TransSectionM K (vOf W K S) U₁ U₂ a := by
  set V := vOf W K S with hV
  have haN : a ∈ Subgroup.normalizer (K : Set X) := h.hN haS
  have hKa : ∀ x ∈ K, a * x * a⁻¹ ∈ K := fun x hx => (Subgroup.mem_normalizer_iff.1 haN x).1 hx
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ha2)
  have hconj : ∀ y : X, a⁻¹ * y * a = a * y * a⁻¹ := fun y => by rw [hinv]
  have hVK : ∀ k ∈ K, ∀ v ∈ V, k * v * k⁻¹ ∈ V := fun k hk v hv =>
    hR.v_nrm k (Subgroup.mem_sup_left hk) v hv
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => hR.v_elem.comm hx hy
  have hU₁V : U₁ ≤ V := hl.le.2
  have hKcomm : ∀ k ∈ K, ⁅k, a⁆ ∈ K := fun k hk => by
    have : ⁅k, a⁆ = k * (a * k⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]; exact K.mul_mem hk (hKa _ (K.inv_mem hk))
  have hcalc : ∀ k y : X, ⁅k, a⁆ * y * ⁅k, a⁆⁻¹ =
      k * (a * (k⁻¹ * (a * y * a⁻¹) * k) * a⁻¹) * k⁻¹ := fun k y => by
    rw [← hconj y]; simp only [commutatorElement_def]; group
  have htriv₂ : ∀ k ∈ K, ∀ x ∈ U₂, k * x * k⁻¹ = x := by
    have hN : ∀ k ∈ K, ∀ x ∈ (⊥ : Subgroup X), k * x * k⁻¹ ∈ (⊥ : Subgroup X) := by
      intro k _ x hx; rw [Subgroup.mem_bot.1 hx]; simp
    have hle : K ≤ CoreLattice.kTriv K U₂ ⊥ hN := by
      refine CoreLattice.K_le_of_comm ha2 hKc fun k hk => ⟨hKcomm k hk, fun x hx => ?_⟩
      rw [Subgroup.mem_bot]
      have hy : k⁻¹ * x * k ∈ U₂ := by simpa using hl.inv₂ k⁻¹ (K.inv_mem hk) x hx
      have e : ⁅k, a⁆ * x * ⁅k, a⁆⁻¹ = x := by
        rw [hcalc, hl.a_fix₂ x hx, hl.a_fix₂ _ hy]; group
      rw [commutatorElement_def (⁅k, a⁆), e, mul_inv_cancel]
    intro k hk x hx
    have := (CoreLattice.mem_kTriv.1 (hle hk)).2 x hx
    rw [Subgroup.mem_bot, commutatorElement_def, mul_inv_eq_one] at this
    exact this
  have hcomm_le : ∀ k ∈ K, ∀ v ∈ V, ⁅v, k⁆ ∈ U₁ := by
    have hle : K ≤ CoreLattice.kTriv K V U₁ hl.inv₁ := by
      refine CoreLattice.K_le_of_comm ha2 hKc fun k hk => ⟨hKcomm k hk, fun v hv => ?_⟩
      have hA : ∀ w ∈ V, ∃ p ∈ U₁, a * w * a⁻¹ = w * p := by
        intro w hw
        rcases hl.tr w hw with h1 | h1
        · exact ⟨1, U₁.one_mem, by rw [h1, mul_one]⟩
        · exact ⟨u, hl.u_mem, h1⟩
      obtain ⟨p, hp, hvp⟩ := hA v hv
      have hvpV : v * p ∈ V := V.mul_mem hv (hU₁V hp)
      have hw : k⁻¹ * (v * p) * k ∈ V := by simpa using hVK k⁻¹ (K.inv_mem hk) _ hvpV
      obtain ⟨q, hq, hwq⟩ := hA _ hw
      have hkq : k * q * k⁻¹ ∈ U₁ := hl.inv₁ k hk q hq
      have e : ⁅k, a⁆ * v * ⁅k, a⁆⁻¹ = v * (p * (k * q * k⁻¹)) := by
        rw [hcalc, hvp, hwq]; group
      have hpq : p * (k * q * k⁻¹) ∈ U₁ := U₁.mul_mem hp hkq
      have hcv : v * (p * (k * q * k⁻¹)) = (p * (k * q * k⁻¹)) * v := hVc v hv _ (hU₁V hpq)
      have e2 : ⁅⁅k, a⁆, v⁆ = p * (k * q * k⁻¹) := by
        rw [commutatorElement_def (⁅k, a⁆), e, hcv]; group
      rw [e2]; exact hpq
    intro k hk v hv
    have := (CoreLattice.mem_kTriv.1 (hle hk)).2 v hv
    rw [← commutatorElement_inv]; exact U₁.inv_mem this
  have hnontriv : ∃ k ∈ K, ∃ x ∈ U₁, ⁅x, k⁆ ∉ U₂ := by
    by_contra hcon
    push_neg at hcon
    have h1 : ⁅U₂, K⁆ = ⊥ := by
      rw [eq_bot_iff]
      refine Subgroup.commutator_le.2 fun x hx k hk => ?_
      have := htriv₂ k hk x⁻¹ (U₂.inv_mem hx)
      rw [Subgroup.mem_bot, commutatorElement_def]
      calc x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) := by group
        _ = 1 := by rw [this]; group
    have h2 : ⁅⁅V, K⁆, K⁆ ≤ ⁅U₁, K⁆ :=
      Subgroup.commutator_mono (Subgroup.commutator_le.2 fun v hv k hk => hcomm_le k hk v hv)
        le_rfl
    have h3 : ⁅U₁, K⁆ ≤ U₂ := Subgroup.commutator_le.2 fun x hx k hk => hcon k hk x hx
    have h4 : ⁅⁅⁅V, K⁆, K⁆, K⁆ = ⊥ :=
      le_bot_iff.1 ((Subgroup.commutator_mono (h2.trans h3) le_rfl).trans h1.le)
    have h5 := BlocksAux.comm_eq_bot_of_perfect h.hK.2.1 h4
    have h6 := BlocksAux.comm_eq_bot_of_perfect h.hK.2.1 h5
    apply hR.v_nt
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h6
  have hasec : ASection a U₁ U₂ := by
    refine ⟨hl.ainv₁, hl.ainv₂, ⟨u, hl.u_mem, hl.u_nmem, fun x hx => ?_⟩, ?_⟩
    · have hxV : x ∈ V := hU₁V hx
      rcases hl.tr x hxV with h1 | h1
      · left; rw [h1]; simpa using U₂.one_mem
      · right
        have hcm : x * u = u * x := hVc x hxV u (hU₁V hl.u_mem)
        have : a * x * a⁻¹ * x⁻¹ * u⁻¹ = 1 := by
          rw [h1, hcm]; group
        rw [this]; exact U₂.one_mem
    · by_contra hcon
      push_neg at hcon
      obtain ⟨k, hk, x, hx, hnot⟩ := hnontriv
      apply hnot
      have hle : K ≤ CoreLattice.kTriv K U₁ U₂ hl.inv₂ := by
        refine CoreLattice.K_le_of_comm ha2 hKc fun k hk => ⟨hKcomm k hk, fun x hx => ?_⟩
        have hx₁ : a * x * a⁻¹ ∈ U₁ := hl.ainv₁ x hx
        have hz : k⁻¹ * (a * x * a⁻¹) * k ∈ U₁ := by
          simpa using hl.inv₁ k⁻¹ (K.inv_mem hk) _ hx₁
        have hy₀ := hcon x hx
        have hy₁ := hcon _ hz
        have hky₁ : k * (a * (k⁻¹ * (a * x * a⁻¹) * k) * a⁻¹ * (k⁻¹ * (a * x * a⁻¹) * k)⁻¹) * k⁻¹
            ∈ U₂ := hl.inv₂ k hk _ hy₁
        have e : ⁅⁅k, a⁆, x⁆ = (k * (a * (k⁻¹ * (a * x * a⁻¹) * k) * a⁻¹ *
            (k⁻¹ * (a * x * a⁻¹) * k)⁻¹) * k⁻¹) * (a * x * a⁻¹ * x⁻¹) := by
          rw [commutatorElement_def (⁅k, a⁆), hcalc]; group
        rw [e]
        exact U₂.mul_mem hky₁ hy₀
      have := (CoreLattice.mem_kTriv.1 (hle hk)).2 x hx
      rw [← commutatorElement_inv]; exact U₂.inv_mem this
  refine ⟨⟨hl.le, hl.inv₁, hl.inv₂, htriv₂, hcomm_le, hnontriv⟩, hasec, hl.irredM⟩

end Lattice

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.CoreAux
