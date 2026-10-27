module

public import CFSG.CGT.T75R.CaseB
public import CFSG.CGT.T75R.Nbr

public section

namespace CFSG.CGT.T75R

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

@[expose] def TriA : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ → Sec3Global T → Sec3IsoGlobal T →
    Nat.card T = 2 * Nat.card (normIn T T₁) → Nat.card T = 8 →
    ∀ V V' : Subgroup G, (∃ v : G, V = conjSubgroup v T) → (∃ v : G, V' = conjSubgroup v T) →
      V ≠ T → V' ≠ T → V' ≠ V → normIn T V = normIn T T₁ → normIn T V' = normIn T T₁ →
      (∀ y ∈ normIn V T, ∀ z ∈ normIn V' T, y * z = z * y) →
      normIn V' T ⊓ cfgM T V = ⊥ ∨ ∃ t ∈ T, t ∉ normIn T T₁ ∧ V' = conjSubgroup t V

theorem inf_eq_bot_of_conj_ne {T V V' : Subgroup G} (hwc : IsWC T)
    (hV : ∃ v : G, V = conjSubgroup v T) (hV' : ∃ v : G, V' = conjSubgroup v T) (hne : V' ≠ V) :
    V ⊓ V' = ⊥ := by
  obtain ⟨v, rfl⟩ := hV
  obtain ⟨v', rfl⟩ := hV'
  have e : conjSubgroup v' T = conjSubgroup (v' * v⁻¹) (conjSubgroup v T) := by
    rw [conjSubgroup_conjSubgroup]
    congr 1
    group
  rw [e] at hne ⊢
  exact (hwc.conj v).inf_conj_eq_bot hne

structure XData (T L Tx : Subgroup G) (x : G) : Prop where
  hx1 : x ≠ 1
  hx2 : x * x = 1
  hxT : x ∈ Subgroup.normalizer (T : Set G)
  hxL : x ∈ Subgroup.normalizer (L : Set G)
  hxact : ∀ r ∈ T, x * r * x⁻¹ * r⁻¹ ∈ L
  hxl : ∃ l ∈ L, x * l ≠ l * x
  hxD : x ∈ classD T
  hTx : ∃ g : G, Tx = conjSubgroup g T
  hxTx : x ∈ Tx
  hLnot : ¬ L ≤ Subgroup.normalizer (Tx : Set G)

variable [Finite G] {T T₁ L S V Tx : Subgroup G} {x : G}

theorem Nbr.false_of_caseB [IsSimpleGroup G] (h214 : Lemma214) (hInv : InvolutionClassInput)
    (hSz : Section3SzInput) (hnab : ∃ a b : G, a * b ≠ b * a) (hP : MaxPair T T₁)
    (hTc : Nat.card T = 8) (hLT₁ : normIn T T₁ = L) (hLc : Nat.card L = 4)
    (hV : Nbr T L S V) (hS2 : IsPGroup 2 S) (hSN : S ≤ Subgroup.normalizer (T : Set G))
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hxS : x ∈ S) (hX : XData T L Tx x)
    (hVx : conjSubgroup x V ≠ V)
    (hB : normIn (conjSubgroup x V) T ⊓ cfgM T V = ⊥) : False := by
  have hV' := hV.conj_x hX.hxT hX.hxL hxS
  have hcomm := hV.comm_conj_x h214 hInv hSz hnab hS2 hSN hSL hxS
  set V' := conjSubgroup x V with hV'def
  set A := normIn V T with hA
  set B := normIn V' T with hB'
  have hBA : B = conjSubgroup x A := normIn_conj_right_of_mem_normalizer hX.hxT V
  have hcfg : cfgM T V = L ⊔ A := by rw [cfgM, hV.hL]
  have hTV : T ⊓ V = ⊥ := hV.sec3.cfg.inf
  have hLA : L ⊓ A = ⊥ := by
    rw [← hV.hL]
    refine eq_bot_iff.2 fun z hz => ?_
    have h1 : z ∈ T ⊓ V := ⟨(normIn_le _ _) hz.1, (normIn_le _ _) hz.2⟩
    rw [hTV, Subgroup.mem_bot] at h1
    rw [h1]
    exact Subgroup.one_mem _
  have hLA' : ∀ l ∈ L, ∀ a ∈ A, l * a = a * l := fun l hl a ha => by
    refine hV.sec3.cfg.comm_L_L₁ ?_ ha
    rw [hV.hL]; exact hl
  have hLB' : ∀ l ∈ L, ∀ b ∈ B, l * b = b * l := fun l hl b hb => by
    refine hV'.sec3.cfg.comm_L_L₁ ?_ hb
    rw [hV'.hL]; exact hl
  have hLAel : IsElemAbelian 2 (L ⊔ A) := by
    rw [← hcfg]; exact hV.sec3.cfg.isElemAbelian_cfgM
  have hBel : IsElemAbelian 2 B :=
    isElemAbelian_of_le hV'.sec3.cfg.wc₁.1 (normIn_le V' T)
  have hNel : IsElemAbelian 2 (L ⊔ A ⊔ B) := by
    refine isElemAbelian_sup_of_comm hLAel hBel fun m hm b hb => ?_
    obtain ⟨l, hl, a, ha, rfl⟩ := (mem_sup_iff_of_comm hLA').1 hm
    calc l * a * b = l * (a * b) := by rw [mul_assoc]
      _ = l * (b * a) := by rw [hcomm a ha b hb]
      _ = (l * b) * a := by rw [mul_assoc]
      _ = (b * l) * a := by rw [hLB' l hl b hb]
      _ = b * (l * a) := by rw [mul_assoc]
  have hxL' : conjSubgroup x L = L := mem_normalizer_iff_conjSubgroup_eq.1 hX.hxL
  have hxB : conjSubgroup x B = A := by
    rw [hBA, conjSubgroup_conjSubgroup, hX.hx2, conjSubgroup_one]
  have hxN : x ∈ Subgroup.normalizer ((L ⊔ A ⊔ B : Subgroup G) : Set G) := by
    apply mem_normalizer_of_conjSubgroup_eq
    rw [conjSubgroup_sup_eq_sup, conjSubgroup_sup_eq_sup, hxL', ← hBA, hxB]
    rw [sup_right_comm]
  have hVV' : V ⊓ V' = ⊥ :=
    inf_eq_bot_of_conj_ne hP.wc hV.conj hV'.conj hVx
  have hAB : A ⊓ B = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    have h1 : z ∈ V ⊓ V' := ⟨(normIn_le _ _) hz.1, (normIn_le _ _) hz.2⟩
    rw [hVV', Subgroup.mem_bot] at h1
    rw [h1]
    exact Subgroup.one_mem _
  have hLAB : L ⊓ (A ⊔ B) = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    obtain ⟨hzL, hzAB⟩ := hz
    obtain ⟨a₁, ha₁, b₁, hb₁, hz⟩ := (mem_sup_iff_of_comm hcomm).1 hzAB
    have hb₁' : b₁ = a₁⁻¹ * z := by rw [hz]; group
    have hb₁L : b₁ ∈ L ⊔ A :=
      hb₁' ▸ (L ⊔ A).mul_mem (Subgroup.mem_sup_right (A.inv_mem ha₁)) (Subgroup.mem_sup_left hzL)
    have h1 : b₁ ∈ B ⊓ cfgM T V := ⟨hb₁, by rw [hcfg]; exact hb₁L⟩
    rw [hB, Subgroup.mem_bot] at h1
    have hza : z = a₁ := by rw [hz, h1, mul_one]
    have h2 : z ∈ L ⊓ A := ⟨hzL, hza ▸ ha₁⟩
    rw [hLA, Subgroup.mem_bot] at h2
    rw [h2]
    exact Subgroup.one_mem _
  have hA3 : 3 ≤ Nat.card A := by
    have h1 : Nat.card A = Nat.card (normIn T V) := hV.sec3.card_normIn_swap
    rw [h1, hV.hL, hLc]
    norm_num
  exact false_of_pair_swap hP hTc (by rw [hLT₁]; exact hLc.le) hX.hTx hX.hxTx hX.hx1 hX.hxD
    hX.hx2 hNel (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left) hxN hX.hLnot
    hxL' hBA.symm hAB hLAB hX.hxl hA3

end CFSG.CGT.T75R
