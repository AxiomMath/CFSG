module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitComponents
public import CFSG.LocalAnalysis.ComponentClassification.TBLitHullTransport
public import CFSG.LocalAnalysis.ComponentClassification.TBLitIntrinsicTypes

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.UnbalancingLocal
open scoped commutatorElement Pointwise MatrixGroups

variable {X : Type} [Group X] [Finite X]

structure CoreConfig (a b γ : X) (S E : Subgroup X) : Prop where
  ha : orderOf a = 2
  hb : orderOf b = 2
  hγ : orderOf γ = 2
  hab : a * b = b * a
  haγ : a * γ = γ * a
  hbγ : b * γ = γ * b
  hS : S ≤ centralizer ({b} : Set X) ⊓ centralizer ({γ} : Set X)
  hSc : IsPComponent 2 (S.subgroupOf (centralizer ({b} : Set X) ⊓ centralizer ({γ} : Set X)))
  hγS : γ ∈ S
  hSL : ∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
    Nonempty (S ⧸ pPrimeCore 2 S ≃* SL(2, GaloisField p n))
  hEa : E ≤ oddCentralizerCore a
  hE : E ≤ centralizer ({b} : Set X) ⊓ centralizer ({γ} : Set X)
  hprop : ActsProperly a E S (oddCoreIn S)

omit [Finite X] in
theorem forall_commutator_mem_oddCoreIn_sup {C M : Subgroup X} (hMC : M ≤ C) {b g : X}
    (hbC : b ∈ C) (hgb : g * b = b * g) (h : ∀ m ∈ M, ⁅m, g⁆ ∈ oddCoreIn C) :
    ∀ k ∈ M ⊔ conjugate M b, ⁅k, g⁆ ∈ oddCoreIn C := by
  have hCn : C ≤ normalizer ((oddCoreIn C : Subgroup X) : Set X) :=
    le_normalizer.trans (normalizer_le_normalizer_oddCoreIn C)
  let Sub : Subgroup X :=
    { carrier := {k | k ∈ normalizer ((oddCoreIn C : Subgroup X) : Set X) ∧
        ⁅k, g⁆ ∈ oddCoreIn C}
      one_mem' := ⟨one_mem _, by rw [commutatorElement_one_left]; exact one_mem _⟩
      mul_mem' := fun {k₁ k₂} h₁ h₂ => ⟨mul_mem h₁.1 h₂.1, by
        have heq : ⁅k₁ * k₂, g⁆ = k₁ * ⁅k₂, g⁆ * k₁⁻¹ * ⁅k₁, g⁆ := by
          simp only [commutatorElement_def]
          group
        rw [heq]
        exact mul_mem ((mem_normalizer_iff.mp h₁.1 _).mp h₂.2) h₁.2⟩
      inv_mem' := fun {k} h => ⟨inv_mem h.1, by
        have heq : ⁅k⁻¹, g⁆ = k⁻¹ * ⁅k, g⁆⁻¹ * k⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [heq]
        exact (mem_normalizer_iff.mp (inv_mem h.1) _).mp (inv_mem h.2)⟩ }
  have hMSub : M ≤ Sub := fun m hm => ⟨hCn (hMC hm), h m hm⟩
  have hMbSub : conjugate M b ≤ Sub := by
    intro x hx
    rw [UnbalancedLayer.mem_conjugate_iff] at hx
    have hxC : x ∈ C := by
      have h1 := mul_mem (mul_mem (inv_mem hbC) (hMC hx)) hbC
      rwa [show b⁻¹ * (b * x * b⁻¹) * b = x by group] at h1
    refine ⟨hCn hxC, ?_⟩
    have h1 := (mem_normalizer_iff.mp (hCn (inv_mem hbC)) _).mp (h _ hx)
    have heq : b⁻¹ * ⁅b * x * b⁻¹, g⁆ * b⁻¹⁻¹ = ⁅x, g⁆ := by
      have hgb' : g = b⁻¹ * g * b := by rw [mul_assoc, hgb]; group
      conv_rhs => rw [hgb']
      simp only [commutatorElement_def]
      group
    rwa [heq] at h1
  intro k hk
  exact (sup_le hMSub hMbSub hk).2

theorem forall_mem_oddCoreIn_of_sup {γ b g : X} {M S : Subgroup X}
    (hM : M ≤ centralizer ({γ} : Set X))
    (hMc : IsPComponent 2 (M.subgroupOf (centralizer ({γ} : Set X))))
    (hbC : b ∈ centralizer ({γ} : Set X)) (hgb : g * b = b * g)
    (hSK : S ≤ M ⊔ conjugate M b) (hSC : S ≤ centralizer ({γ} : Set X))
    (hgS : g ∈ normalizer (S : Set X)) (h : ∀ m ∈ M, ⁅m, g⁆ ∈ oddCoreIn M) :
    ∀ s ∈ S, ⁅s, g⁆ ∈ oddCoreIn S := by
  have hOM := UGSChain.map_pPrimeCore_le_of_isPComponent hM hMc
  have h1 := forall_commutator_mem_oddCoreIn_sup hM hbC hgb (fun m hm => hOM (h m hm))
  intro s hs
  have hSn : S ≤ normalizer ((oddCoreIn (centralizer ({γ} : Set X)) : Subgroup X) : Set X) :=
    hSC.trans (le_normalizer.trans (normalizer_le_normalizer_oddCoreIn _))
  refine inf_le_oddCoreIn (odd_card_oddCoreIn _) hSn (mem_inf.mpr ⟨?_, h1 s (hSK hs)⟩)
  exact commutator_le_of_le_normalizer (zpowers_le.mpr hgS)
    (commutator_mem_commutator hs (mem_zpowers g))

theorem core_pumpUp (hI : TBInputs) (hX : TBSetting X) {a b γ : X} {S E : Subgroup X}
    (hC : CoreConfig a b γ S E) :
    ∃ M : Subgroup X, M ≤ centralizer ({γ} : Set X) ∧
      IsPComponent 2 (M.subgroupOf (centralizer ({γ} : Set X))) ∧ S ≤ M ⊔ conjugate M b ∧
      IsPComponent 2 (S.subgroupOf ((M ⊔ conjugate M b) ⊓ centralizer ({b} : Set X))) ∧
      a ∈ normalizer (M : Set X) ∧ E ≤ normalizer (M : Set X) ∧
      (¬ ∀ m ∈ M, ⁅m, a⁆ ∈ oddCoreIn M) ∧ ∃ e ∈ E, ¬ ∀ m ∈ M, ⁅m, e⁆ ∈ oddCoreIn M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cγ := centralizer ({γ} : Set X) with hCγ
  have hKC := isKGroupCat_centralizer hX.kProper (hX.not_mem_center hC.hγ)
  have hbC : b ∈ Cγ := mem_centralizer_singleton_iff.mpr hC.hbγ
  have haC : a ∈ Cγ := mem_centralizer_singleton_iff.mpr hC.haγ
  have hSE := le_pLayer_of_isPComponent_inf hI.schreier hKC hbC hC.hb hC.hS hC.hSc
  obtain ⟨M, hM, hMc, hSK, hSKc⟩ :=
    UGSChain.exists_orbit_component_of_le_pLayer hC.hb hC.hbγ hC.hS hC.hSc hSE
  have hSC : S ≤ Cγ := hC.hS.trans inf_le_right
  have hEodd : Odd (Nat.card E) := Nat.coprime_two_left.mp
    ((coprime_card_oddCentralizerCore a).coprime_dvd_right (card_dvd_of_le hC.hEa))
  have key : ∀ g, g * b = b * g → g ∈ normalizer (S : Set X) →
      (∀ m ∈ M, ⁅m, g⁆ ∈ oddCoreIn M) → ∀ s ∈ S, ⁅s, g⁆ ∈ oddCoreIn S :=
    fun g hgb hgS h => forall_mem_oddCoreIn_of_sup hM hMc hbC hgb hSK hSC hgS h
  set D := (oddCentralizerCore a ⊓ Cγ).subgroupOf Cγ with hD
  set a' : Cγ := ⟨a, haC⟩ with ha'
  have hDC : D ≤ centralizer ({a'} : Set Cγ) := by
    intro x hx
    obtain ⟨y, -, hy⟩ := (mem_inf.mp (mem_subgroupOf.mp hx)).1
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    change (x : X) * a = a * x
    rw [← hy]
    exact mem_centralizer_singleton_iff.mp y.2
  have hDn : (D.subgroupOf (centralizer ({a'} : Set Cγ))).Normal := by
    rw [normal_subgroupOf_iff hDC]
    intro x c hx hc
    have hca : (c : X) ∈ centralizer ({a} : Set X) :=
      mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc))
    rw [mem_subgroupOf] at hx ⊢
    exact mem_inf.mpr ⟨conj_mem_oddCentralizerCore hca (mem_inf.mp hx).1,
      mul_mem (mul_mem c.2 (mem_inf.mp hx).2) (inv_mem c.2)⟩
  have hDodd : Odd (Nat.card D) := by
    rw [hD, Nat.card_congr (subgroupOfEquivOfLe (inf_le_right :
      oddCentralizerCore a ⊓ Cγ ≤ Cγ)).toEquiv]
    exact Nat.coprime_two_left.mp ((coprime_card_oddCentralizerCore a).coprime_dvd_right
      (card_dvd_of_le inf_le_left))
  have ha2 : orderOf a' = 2 := by rw [Subgroup.orderOf_mk]; exact hC.ha
  have hLD : ¬ ⁅M.subgroupOf Cγ, D⁆ ≤
      (pPrimeCore 2 (M.subgroupOf Cγ)).map (M.subgroupOf Cγ).subtype := by
    intro hle
    obtain ⟨e, he, s, hs, hes⟩ := hC.hprop.exists_nontrivial
    have heγ : e ∈ Cγ := (hC.hE he).2
    have heb : e * b = b * e := mem_centralizer_singleton_iff.mp (hC.hE he).1
    have heS : e ∈ normalizer (S : Set X) :=
      (hC.hprop.1 (subset_closure (Set.mem_insert_of_mem a he))).1
    refine hes (key e heb heS (fun m hm => ?_) s hs)
    have h1 : ⁅(⟨m, hM hm⟩ : Cγ), (⟨e, heγ⟩ : Cγ)⁆ ∈ ⁅M.subgroupOf Cγ, D⁆ :=
      commutator_mem_commutator (show (⟨m, hM hm⟩ : Cγ) ∈ M.subgroupOf Cγ from hm)
        (show (⟨e, heγ⟩ : Cγ) ∈ D from mem_inf.mpr ⟨hC.hEa he, heγ⟩)
    exact (mem_oddCoreIn_subgroupOf_iff hM _).mp (hle h1)
  obtain ⟨hDM, haM, -, -⟩ := UnbalancedLayer.odd_fixed_core_active_two_component ha2 hDC hDn
    hDodd hMc hLD
  have haMX : a ∈ normalizer (M : Set X) := UnbalancedLayer.mem_normalizer_of_subgroupOf hM haM
  have hEM : E ≤ normalizer (M : Set X) := fun e he =>
    UnbalancedLayer.mem_normalizer_of_subgroupOf hM
      (hDM (show (⟨e, (hC.hE he).2⟩ : Cγ) ∈ D from mem_inf.mpr ⟨hC.hEa he, (hC.hE he).2⟩))
  refine ⟨M, hM, hMc, hSK, hSKc, haMX, hEM, fun h => ?_, ?_⟩
  · exact hC.hprop.not_trivial_left hC.ha hEodd
      (key a hC.hab (hC.hprop.1 (subset_closure (Set.mem_insert a _))).1 h)
  · obtain ⟨e, he, s, hs, hes⟩ := hC.hprop.exists_nontrivial
    refine ⟨e, he, fun h => hes (key e (mem_centralizer_singleton_iff.mp (hC.hE he).1)
      (hC.hprop.1 (subset_closure (Set.mem_insert_of_mem a he))).1 h s hs)⟩

end CFSG.ComponentClassification.TBLit
