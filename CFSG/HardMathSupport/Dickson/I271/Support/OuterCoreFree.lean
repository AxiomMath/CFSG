module

public import CFSG.HardMathSupport.Dickson.I271.Support.ChevInner
public import CFSG.HardMathSupport.Dickson.I271.Support.OuterDefs

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4

@[expose] def KDOutCoreFree : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → idx.1.characteristic = p → ¬ (p = 3 ∧ IsLTwoTwentySeven S) →
        ∀ β : MulAut S, orderOf β = p → β ∉ innerAut S → GLAPPrimeCoreOf p (fixSubgroup β) = ⊥

@[expose] def KDOutCentInner : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → idx.1.characteristic = p → ¬ (p = 3 ∧ IsLTwoTwentySeven S) →
        ∀ β : MulAut S, orderOf β = p → β ∉ innerAut S →
          ∀ w : MulAut S, Nat.Coprime p (orderOf w) → w * β = β * w →
            (∀ x ∈ fixSubgroup β, w x = x) → w ∈ innerAut S

section Reduction

variable {S : Type} [Group S] [Finite S]

theorem mulAut_mul_conj_mul_inv (d : MulAut S) (c : S) :
    d * MulAut.conj c * d⁻¹ = MulAut.conj (d c) := by
  ext x
  simp [MulAut.conj_apply]

theorem conj_mem_centralizer_iff (hZ : Subgroup.center S = ⊥) (d : MulAut S) (c : S) :
    MulAut.conj c ∈ Subgroup.centralizer ({d} : Set (MulAut S)) ↔ c ∈ fixSubgroup d := by
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    have : a ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun f : MulAut S => f y) (MonoidHom.mem_ker.1 ha)
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rwa [hZ, Subgroup.mem_bot] at this
  rw [Subgroup.mem_centralizer_singleton_iff, mem_fixSubgroup]
  constructor
  · intro h
    have h1 : d * MulAut.conj c * d⁻¹ = MulAut.conj c := by
      rw [← h]; group
    rw [mulAut_mul_conj_mul_inv] at h1
    exact hinj h1
  · intro h
    have h1 : d * MulAut.conj c * d⁻¹ = MulAut.conj c := by
      rw [mulAut_mul_conj_mul_inv, h]
    calc MulAut.conj c * d = (d * MulAut.conj c * d⁻¹) * d := by rw [h1]
      _ = d * MulAut.conj c := by group

theorem le_glaPPrimeCoreOf_of_normal' {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {H M : Subgroup G} (hHM : H ≤ M) (hn : (H.subgroupOf M).Normal)
    (hcop : ¬ p ∣ Nat.card H) : H ≤ GLAPPrimeCoreOf p M := by
  have hcop' : Nat.Coprime p (Nat.card (H.subgroupOf M)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHM).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hcop
  have hle : H.subgroupOf M ≤ GLAPPrimeCore p ↥M := le_sSup ⟨hn, hcop'⟩
  calc H = (H.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hHM).symm
    _ ≤ GLAPPrimeCoreOf p M := Subgroup.map_mono hle

theorem conj_mem_glaPPrimeCoreOf {G : Type} [Group G] (p : ℕ) (T : Subgroup G) {t w : G}
    (ht : t ∈ T) (hw : w ∈ GLAPPrimeCoreOf p T) : t * w * t⁻¹ ∈ GLAPPrimeCoreOf p T := by
  obtain ⟨w₀, hw₀, rfl⟩ := hw
  exact ⟨⟨t, ht⟩ * w₀ * ⟨t, ht⟩⁻¹, (GLAPPrimeCore.normal p ↥T).conj_mem w₀ hw₀ ⟨t, ht⟩, rfl⟩

theorem conj_injective_of_center_bot (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  have : a ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := congrArg (fun f : MulAut S => f y) (MonoidHom.mem_ker.1 ha)
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  rwa [hZ, Subgroup.mem_bot] at this

theorem defCharOuterCoreFree_of_kdata (h1 : KDOutCoreFree) (h2 : KDOutCentInner) :
    DefCharOuterCoreFree := by
  intro S _ _ hS hnc idx he p hp hp2 hchar hexc d hd hdout H hH
  haveI := hS
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_simple hnc
  have hinj := conj_injective_of_center_bot hZ
  set T : Subgroup (MulAut S) := H ⊓ Subgroup.centralizer ({d} : Set (MulAut S)) with hT
  set Cbar : Subgroup (MulAut S) := (fixSubgroup d).map (MulAut.conj : S →* MulAut S) with hCbar
  have hCT : Cbar ≤ T := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨hH ⟨c, rfl⟩, (conj_mem_centralizer_iff hZ d c).2 hc⟩
  have hcore : GLAPPrimeCoreOf p Cbar = ⊥ := by
    rw [hCbar, ← map_glaPPrimeCoreOf_of_injective p _ hinj,
      h1 S hS hnc idx he p hp hp2 hchar hexc d hd hdout, Subgroup.map_bot]
  refine eq_bot_iff.2 fun w hw => ?_
  rw [Subgroup.mem_bot]
  have hwT : w ∈ T := (Subgroup.map_subtype_le _) hw
  have hnd : ¬ p ∣ Nat.card (GLAPPrimeCoreOf p T) := not_dvd_card_glaPPrimeCoreOf hp T
  have hfix : ∀ x ∈ fixSubgroup d, w x = x := by
    intro x hx
    have hxT : MulAut.conj x ∈ T := hCT ⟨x, hx, rfl⟩
    have hwx : w x ∈ fixSubgroup d := by
      rw [mem_fixSubgroup] at hx ⊢
      have hwd : w * d = d * w := Subgroup.mem_centralizer_singleton_iff.1 hwT.2
      calc d (w x) = (d * w) x := rfl
        _ = (w * d) x := by rw [hwd]
        _ = w (d x) := rfl
        _ = w x := by rw [hx]
    have hcomm : w * MulAut.conj x * w⁻¹ * (MulAut.conj x)⁻¹ ∈ GLAPPrimeCoreOf p T ⊓ Cbar := by
      refine ⟨?_, ?_⟩
      · have := conj_mem_glaPPrimeCoreOf p T hxT ((GLAPPrimeCoreOf p T).inv_mem hw)
        have h3 := (GLAPPrimeCoreOf p T).mul_mem hw this
        have e : w * MulAut.conj x * w⁻¹ * (MulAut.conj x)⁻¹ =
            w * (MulAut.conj x * w⁻¹ * (MulAut.conj x)⁻¹) := by group
        rw [e]
        exact h3
      · have h3 : w * MulAut.conj x * w⁻¹ = MulAut.conj (w x) := by
          have := mulAut_mul_conj_mul_inv w x
          exact this
        rw [h3]
        exact Cbar.mul_mem ⟨w x, hwx, rfl⟩ (Cbar.inv_mem ⟨x, hx, rfl⟩)
    have hle : GLAPPrimeCoreOf p T ⊓ Cbar ≤ GLAPPrimeCoreOf p Cbar := by
      refine le_glaPPrimeCoreOf_of_normal' hp inf_le_right ?_ fun hdvd => hnd
        (hdvd.trans (Subgroup.card_dvd_of_le inf_le_left))
      refine ⟨fun n hn g => ?_⟩
      have hn' := Subgroup.mem_subgroupOf.1 hn
      have hgT : (g : MulAut S) ∈ T := hCT g.2
      refine Subgroup.mem_subgroupOf.2 ⟨?_, ?_⟩
      · exact conj_mem_glaPPrimeCoreOf p T hgT hn'.1
      · exact Cbar.mul_mem (Cbar.mul_mem g.2 hn'.2) (Cbar.inv_mem g.2)
    have h4 := hle hcomm
    rw [hcore, Subgroup.mem_bot] at h4
    have h5 : w * MulAut.conj x * w⁻¹ = MulAut.conj x := by
      have := congrArg (fun t => t * MulAut.conj x) h4
      simpa using this
    rw [mulAut_mul_conj_mul_inv] at h5
    exact hinj h5
  have hword : Nat.Coprime p (orderOf w) := by
    have hdvd : orderOf w ∣ Nat.card (GLAPPrimeCoreOf p T) := Subgroup.orderOf_dvd_natCard _ hw
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hnd (h.trans hdvd)
  have hwd : w * d = d * w := Subgroup.mem_centralizer_singleton_iff.1 hwT.2
  obtain ⟨s, rfl⟩ := h2 S hS hnc idx he p hp hp2 hchar hexc d hd hdout w hword hwd hfix
  have hsd : s ∈ fixSubgroup d := (conj_mem_centralizer_iff hZ d s).1 hwT.2
  have hsc : ∀ x ∈ fixSubgroup d, s * x = x * s := fun x hx => by
    have := hfix x hx
    simp only [MulAut.conj_apply] at this
    calc s * x = (s * x * s⁻¹) * s := by group
      _ = x * s := by rw [this]
  have hsord : Nat.Coprime p (orderOf s) := by
    have : orderOf (MulAut.conj s) = orderOf s := orderOf_injective _ hinj s
    rwa [← this]
  have hcard : ¬ p ∣ Nat.card (Subgroup.zpowers s) := by
    rw [Nat.card_zpowers]
    exact fun h => ((Nat.Prime.coprime_iff_not_dvd hp).1 hsord) h
  have hsle : Subgroup.zpowers s ≤ GLAPPrimeCoreOf p (fixSubgroup d) := by
    refine le_glaPPrimeCoreOf_of_normal' hp ((Subgroup.zpowers_le).2 hsd) ?_ hcard
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hn)
    have hcg : (g : S) * s = s * g := (hsc g g.2).symm
    refine Subgroup.mem_subgroupOf.2 ?_
    have : (g : S) * n * (g : S)⁻¹ = (n : S) := by
      have hnk : (n : S) = s ^ k := hk.symm
      rw [hnk]
      have hcomm : Commute (g : S) (s ^ k) :=
        Commute.zpow_right (show Commute (g : S) s from hcg) k
      rw [hcomm.eq, mul_inv_cancel_right]
    rw [show (↑(g * n * g⁻¹) : S) = (g : S) * n * (g : S)⁻¹ from rfl, this]
    exact Subgroup.mem_zpowers_iff.2 ⟨k, hk⟩
  have hs1 : s = 1 := by
    have h5 := hsle (Subgroup.mem_zpowers s)
    rw [h1 S hS hnc idx he p hp hp2 hchar hexc d hd hdout, Subgroup.mem_bot] at h5
    exact h5
  rw [hs1, map_one]

end Reduction

end CFSG.HardMathSupport.Dickson.I271
