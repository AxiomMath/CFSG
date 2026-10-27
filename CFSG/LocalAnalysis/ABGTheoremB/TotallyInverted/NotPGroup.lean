module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.Conjugacy
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.NotPGroupInputs
public import CFSG.LocalAnalysis.ABGTheoremB.Facts

public section

namespace CFSG.ABGTheoremB.TotallyInverted

open CFSG.ABGLocalTools Conjugacy
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

namespace NotPGroup

@[expose] def genP (σ : Setting G) (r : ℕ) : Subgroup G := σ.Ps r 0 ⊔ σ.Ps r 1 ⊔ σ.Ps r 2

omit [Finite G] in
theorem Ps_le_genP (i : Fin 3) : σ.Ps r i ≤ genP σ r := by
  fin_cases i
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

omit [Finite G] in
theorem C_le_normalizer_genP : σ.C ≤ Subgroup.normalizer (genP σ r : Set G) := fun _ hc =>
  mem_normalizer_sup (mem_normalizer_sup (C_le_normalizer_Ps 0 hc) (C_le_normalizer_Ps 1 hc))
    (C_le_normalizer_Ps 2 hc)

theorem a_mem_normalizer_genP (Δ : Data σ r) :
    Δ.a ∈ Subgroup.normalizer (genP σ r : Set G) := by
  rw [← conjSub_eq_self_iff, genP, conjSub_sup, conjSub_sup, Δ.P_conj 0, Δ.P_conj 1, Δ.P_conj 2]
  change σ.Ps r 1 ⊔ σ.Ps r 2 ⊔ σ.Ps r 0 = σ.Ps r 0 ⊔ σ.Ps r 1 ⊔ σ.Ps r 2
  rw [sup_comm (σ.Ps r 1 ⊔ σ.Ps r 2), ← sup_assoc]

theorem d_mem_normalizer_genP (hσ : σ.IsValid) (Δ : Data σ r) :
    Δ.d ∈ Subgroup.normalizer (genP σ r : Set G) := by
  rw [← conjSub_eq_self_iff, genP, conjSub_sup, conjSub_sup, conjSub_d_Ps_zero Δ,
    conjSub_d_Ps_one Δ, conjSub_d_Ps_two hσ Δ, sup_assoc, sup_comm (σ.Ps r 2), ← sup_assoc]

theorem M_le_normalizer_genP (hσ : σ.IsValid) (Δ : Data σ r) :
    σ.M ≤ Subgroup.normalizer (genP σ r : Set G) := by
  rw [Δ.M_eq]
  refine sup_le C_le_normalizer_genP ?_
  rw [Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | rfl
  · exact d_mem_normalizer_genP hσ Δ
  · exact a_mem_normalizer_genP Δ

theorem D_le_normalizer_genP (hσ : σ.IsValid) (Δ : Data σ r) :
    σ.D ≤ Subgroup.normalizer (genP σ r : Set G) :=
  D_le_M.trans (M_le_normalizer_genP hσ Δ)

theorem T_le_normalizer_genP (hσ : σ.IsValid) :
    σ.T ≤ Subgroup.normalizer (genP σ r : Set G) :=
  (σ.T_le_C hσ).trans C_le_normalizer_genP

theorem genP_ne_bot (Δ : Data σ r) : genP σ r ≠ ⊥ :=
  fun h => Ps_ne_bot Δ (eq_bot_iff.mpr (h ▸ Ps_le_genP 0))

theorem normalizer_Ps_mem_familyL (hσ : σ.IsValid) (Δ : Data σ r) :
    Subgroup.normalizer (σ.Ps r 0 : Set G) ∈ σ.familyL r := by
  have hN : σ.N ≤ Subgroup.normalizer (σ.Ps r 0 : Set G) := le_normalizer_pCoreIn r (σ.Ns 0)
  refine ⟨⟨σ.Ps r 0, Ps_ne_bot Δ, isPGroup_Ps 0, rfl⟩, fun l hl => ?_,
    (σ.D_le_N hσ).trans hN, ⟨σ.Ps r 0, Δ.P_sylow, Subgroup.le_normalizer⟩⟩
  exact ⟨l, hN (hσ.L₀_le_N hl), 1, σ.ON.one_mem, mul_one l⟩

section PGroup

variable (hσ : σ.IsValid) (Δ : Data σ r) (hFp : IsPGroup r (genP σ r))
include hσ Δ hFp

omit hσ in
theorem genP_le_oddCore : genP σ r ≤ oddCoreIn (Subgroup.normalizer (genP σ r : Set G)) :=
  le_oddCoreIn Subgroup.le_normalizer le_rfl (odd_card_of_isPGroup Δ.prime Δ.ne_two hFp)

omit hσ in
theorem oddCore_ne_bot : oddCoreIn (Subgroup.normalizer (genP σ r : Set G)) ≠ ⊥ :=
  fun h => genP_ne_bot Δ (eq_bot_iff.mpr (h ▸ genP_le_oddCore Δ hFp))

omit hσ in
theorem genP_inf_C : genP σ r ⊓ σ.C = ⊥ := by
  rw [eq_bot_iff, ← Δ.Op_C]
  exact le_pCoreIn inf_le_right
    (fun c hc => mem_normalizer_inf (C_le_normalizer_genP hc) (Subgroup.le_normalizer hc))
    (hFp.to_le inf_le_left)

omit hσ in
theorem genP_mem_signalizers : genP σ r ∈ signalizers ⊤ σ.C r :=
  ⟨le_top, hFp, C_le_normalizer_genP, genP_inf_C Δ hFp⟩

omit hFp in
theorem three_dvd_automizerIndex :
    3 ∣ CFSG.QuasiDihedralFusion.automizerIndex
      (σ.T.subgroupOf (Subgroup.normalizer (genP σ r : Set G))) := by
  set K := Subgroup.normalizer (genP σ r : Set G)
  have haK : Δ.a ∈ K := M_le_normalizer_genP hσ Δ Δ.a_mem
  have hTK : σ.T ≤ K := T_le_normalizer_genP hσ
  obtain ⟨k, hk⟩ := Δ.a_three
  unfold CFSG.QuasiDihedralFusion.automizerIndex
  refine three_dvd_relIndex (g := (⟨Δ.a, haK⟩ : K)) ?_ ?_ (k := k)
    (Subtype.ext (by simpa using hk))
  · rw [← Subgroup.subgroupOf_normalizer_eq hTK]
    exact a_mem_normalizer_T Δ
  · intro hc
    have hx : (⟨σ.x, hTK σ.x_mem_T⟩ : K) ∈ σ.T.subgroupOf K := σ.x_mem_T
    have h := congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc _ hx)
    simp only [Subgroup.coe_mul] at h
    apply hσ.x_ne_x₂
    have h0 : Δ.a * σ.x * Δ.a⁻¹ = σ.x₂ := Δ.a_cycle 0
    rw [← h, mul_inv_cancel_right] at h0
    exact h0

theorem not_covers (hF : σ.ChapterIIFacts) :
    ¬ (σ.L₀ : Set G) ⊆ (Subgroup.normalizer (genP σ r : Set G) : Set G) * σ.ON := by
  intro hcov
  have hQ := (hF.cover_qgroup _ (T_le_normalizer_genP hσ) (oddCore_ne_bot Δ hFp) hcov).1.1
  exact hF.qgroup_no_three _ hQ σ.T (T_le_normalizer_genP hσ) (isKleinFour_T hσ)
    (three_dvd_automizerIndex hσ Δ)

theorem not_Q_le (hF : σ.ChapterIIFacts) (hq : σ.DeltaEpsMinus ∧ r ∣ σ.q) (i : Fin 3) :
    ¬ Δ.Q i ≤ Subgroup.normalizer (genP σ r : Set G) ∧
      ¬ Δ.Qs i ≤ Subgroup.normalizer (genP σ r : Set G) := by
  set K := Subgroup.normalizer (genP σ r : Set G)
  obtain ⟨-, -, -, hJ, ⟨z, hz, hzQ⟩, -⟩ := Δ.Q_cases hq i
  have hai : Δ.a ^ (i : ℕ) ∈ K := K.pow_mem (M_le_normalizer_genP hσ Δ Δ.a_mem) _
  have hzK : z ∈ K := conjSub_le_of_mem hai (D_le_normalizer_genP hσ Δ) hz
  have hboth : Δ.Q i ≤ K ∨ Δ.Qs i ≤ K → False := by
    intro h
    have hQQ : Δ.Q i ≤ K ∧ Δ.Qs i ≤ K := by
      rcases h with h | h
      · exact ⟨h, hzQ ▸ conjSub_le_of_mem hzK h⟩
      · refine ⟨?_, h⟩
        rw [← conjSub_inv_conjSub z (Δ.Q i), hzQ]
        exact conjSub_le_of_mem (K.inv_mem hzK) h
    have hJi : conjSub (Δ.a ^ (i : ℕ)) Δ.J ≤ K := hJ ▸ sup_le hQQ.1 hQQ.2
    have hJK : Δ.J ≤ K := by
      rw [← conjSub_inv_conjSub (Δ.a ^ (i : ℕ)) Δ.J]
      exact conjSub_le_of_mem (K.inv_mem hai) hJi
    apply not_covers hσ Δ hFp hF
    have hJN : Δ.J ≤ Subgroup.normalizer (σ.ON : Set G) :=
      Δ.J_le.trans (hσ.L₀_le_N.trans σ.N_le_normalizer_ON)
    rw [Δ.L₀_eq, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hJN]
    exact Set.mul_subset_mul hJK subset_rfl
  exact ⟨fun h => hboth (Or.inl h), fun h => hboth (Or.inr h)⟩

omit hσ in
theorem genP_le_of_mem_maximals (homni : Omnibus Δ) {U : Subgroup G}
    (hU : U ∈ maximals (signalizersPerm (Subgroup.normalizer (genP σ r : Set G)) σ.T σ.C r)) :
    genP σ r ≤ U := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  obtain ⟨R₀, hR₀, hR₀U⟩ := (homni _ C_le_normalizer_genP U hU).part_ii_b
  have hR₀K : R₀ ≤ Subgroup.normalizer (genP σ r : Set G) := hR₀.le.trans (oddCoreIn_le _)
  have hp : IsPGroup r (R₀ ⊔ genP σ r : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hR₀.isPGroup hFp hR₀K
  have heq := hR₀.eq_of_le le_sup_left (sup_le hR₀.le (genP_le_oddCore Δ hFp)) hp
  exact (le_sup_right.trans heq.le).trans hR₀U

omit [Finite G] hσ Δ hFp in
private theorem le_of_le_sup_of_inf_eq_bot {P Q V : Subgroup G}
    (hQP : Q ≤ Subgroup.centralizer (P : Set G)) (hPV : P ≤ V) (hVQ : V ≤ Q ⊔ P)
    (hVQ' : V ⊓ Q = ⊥) : V ≤ P := by
  intro v hv
  have hv' : v ∈ ((Q ⊔ P : Subgroup G) : Set G) := hVQ hv
  rw [Subgroup.coe_mul_of_left_le_normalizer_right Q P
    (hQP.trans (Subgroup.centralizer_le_normalizer _))] at hv'
  obtain ⟨q, hq, p, hp, rfl⟩ := hv'
  have hqV : q ∈ V := by simpa using V.mul_mem hv (V.inv_mem (hPV hp))
  have hq1 : q ∈ V ⊓ Q := ⟨hqV, hq⟩
  rw [hVQ', Subgroup.mem_bot] at hq1
  simpa [hq1] using hp

theorem comp_subset_Ps (hF : σ.ChapterIIFacts) (homni : Omnibus Δ) {U : Subgroup G}
    (hU : U ∈ maximals (signalizersPerm (Subgroup.normalizer (genP σ r : Set G)) σ.T σ.C r))
    (i : Fin 3) : comp σ U i ⊆ σ.Ps r i := by
  set K := Subgroup.normalizer (genP σ r : Set G)
  obtain ⟨V, hV, hCV, hcases⟩ := (homni K C_le_normalizer_genP U hU).part_i_b i
  have hPV : σ.Ps r i ≤ V := fun u hu => by
    have : u ∈ (V : Set G) := by
      rw [hV]
      exact Ps_subset_comp Δ i ((Ps_le_genP i).trans (genP_le_of_mem_maximals Δ hFp homni hU))
        hu
    exact this
  have hVK : V ≤ K := fun v hv => by
    have : v ∈ (V : Set G) := hv
    rw [hV] at this
    exact hU.1.1.1 this.1
  rw [← hV]
  suffices h : V ≤ σ.Ps r i from h
  have key : ∀ Q₀ : Subgroup G, Q₀ ≤ Subgroup.centralizer (σ.Ps r i : Set G) →
      σ.C ≤ Subgroup.normalizer (Q₀ : Set G) →
      (∀ X : Subgroup G, X ≤ Q₀ → σ.C ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = Q₀) →
      ¬ Q₀ ≤ K → V ≤ Q₀ ⊔ σ.Ps r i → V ≤ σ.Ps r i := by
    intro Q₀ hQP hCQ hirr hQK hVQ
    refine le_of_le_sup_of_inf_eq_bot hQP hPV hVQ ?_
    rcases hirr (V ⊓ Q₀) inf_le_right
      (fun c hc => mem_normalizer_inf (hCV hc) (hCQ hc)) with h | h
    · exact h
    · exact absurd (h.ge.trans (inf_le_left.trans hVK)) hQK
  rcases hcases with h | h | h
  · exact h
  · by_cases hq : σ.DeltaEpsMinus ∧ r ∣ σ.q
    · obtain ⟨-, -, -, -, -, -, hirr, -, hcQ, -⟩ := Δ.Q_cases hq i
      exact key (Δ.Q i) hcQ (Δ.Q_C i).1 hirr (not_Q_le hσ Δ hFp hF hq i).1 h
    · have hR : R Δ i = σ.Ps r i := by rw [R, (Δ.Q_trivial hq i).1, bot_sup_eq]
      exact hR ▸ h
  · by_cases hq : σ.DeltaEpsMinus ∧ r ∣ σ.q
    · obtain ⟨-, -, -, -, -, -, -, hirr, -, hcQ⟩ := Δ.Q_cases hq i
      exact key (Δ.Qs i) hcQ (Δ.Q_C i).2 hirr (not_Q_le hσ Δ hFp hF hq i).2 h
    · have hR : Rs Δ i = σ.Ps r i := by rw [Rs, (Δ.Q_trivial hq i).2, bot_sup_eq]
      exact hR ▸ h

theorem le_genP_of_mem_signalizers (hF : σ.ChapterIIFacts) (homni : Omnibus Δ)
    {Y : Subgroup G} (hY : Y ∈ signalizers (Subgroup.normalizer (genP σ r : Set G)) σ.C r) :
    Y ≤ genP σ r := by
  obtain ⟨U, hU, hYU⟩ := exists_le_mem_maximals
    (mem_signalizersPerm_of_mem_signalizers (σ.T_le_C hσ) hY)
  refine le_of_comp_subset hσ (odd_card_of_isPGroup Δ.prime Δ.ne_two hY.2.1)
    ((σ.T_le_C hσ).trans hY.2.2.1) hY.2.2.2 fun i u hu => ?_
  exact Ps_le_genP i (comp_subset_Ps hσ Δ hFp hF homni hU i (comp_mono hYU i hu))

theorem U₀_mem_signalizersPerm : Δ.P ⊔ genP σ r ∈ signalizersPerm ⊤ σ.T σ.C r := by
  have hPC : Δ.P ≤ σ.C := Δ.P_sylowC.le
  have hp : IsPGroup r (Δ.P ⊔ genP σ r : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' Δ.P_sylowC.isPGroup hFp (hPC.trans C_le_normalizer_genP)
  refine ⟨⟨le_top, hp, fun t ht => mem_normalizer_sup ?_ (T_le_normalizer_genP hσ ht),
    inf_T_eq_bot hσ Δ.prime Δ.ne_two hp⟩, mul_comm_sup_of_le hPC C_le_normalizer_genP⟩
  exact Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun p hp => (comm_of_mem_C (hPC hp) ht).symm)

theorem U₀_mem_maximals (hF : σ.ChapterIIFacts) (homni : Omnibus Δ) :
    Δ.P ⊔ genP σ r ∈ maximals (signalizersPerm ⊤ σ.T σ.C r) := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  set K := Subgroup.normalizer (genP σ r : Set G)
  refine ⟨U₀_mem_signalizersPerm hσ Δ hFp, fun X hX hUX => ?_⟩
  obtain ⟨X', hX', hXX'⟩ := exists_le_mem_maximals hX
  suffices h : X' ≤ Δ.P ⊔ genP σ r from le_antisymm (hXX'.trans h) hUX
  obtain ⟨hVmax, hVall⟩ := (homni ⊤ le_top X' hX').part_vi
  have hFV : genP σ r ≤ pCoreIn r (X' ⊔ σ.C) :=
    hVall _ (genP_mem_signalizers Δ hFp) (le_sup_right.trans (hUX.trans hXX'))
  have hCK : σ.C ≤ K := C_le_normalizer_genP
  have hVK : pCoreIn r (X' ⊔ σ.C) ⊓ K ≤ genP σ r :=
    le_genP_of_mem_signalizers hσ Δ hFp hF homni ⟨inf_le_right, hVmax.1.2.1.to_le inf_le_left,
      fun c hc => mem_normalizer_inf (hVmax.1.2.2.1 hc) (Subgroup.le_normalizer (hCK hc)),
      eq_bot_iff.mpr ((inf_le_inf_right σ.C inf_le_left).trans hVmax.1.2.2.2.le)⟩
  have hVF : pCoreIn r (X' ⊔ σ.C) = genP σ r := by
    by_contra hne
    have hlt := lt_inf_normalizer hVmax.1.2.1 (lt_of_le_of_ne hFV (Ne.symm hne))
    exact lt_irrefl _ (hlt.trans_le hVK)
  have hX'K : X' ∈ maximals (signalizersPerm K σ.T σ.C r) := by
    refine mem_maximals_of_subset (signalizersPerm_mono le_top) hX' ⟨⟨?_, hX'.1.1.2⟩, hX'.1.2⟩
    have := le_sup_left.trans (le_normalizer_pCoreIn r (X' ⊔ σ.C))
    rwa [hVF] at this
  have hdec := (homni K hCK X' hX'K).part_iii_a (oddCore_ne_bot Δ hFp)
  have hXC : X' ⊓ σ.C = Δ.P := Δ.P_sylowC.eq_of_le
    (le_inf (le_sup_left.trans (hUX.trans hXX')) Δ.P_sylowC.le) inf_le_right
    (hX'.1.1.2.1.to_le inf_le_left)
  rw [hVF, hXC, sup_comm] at hdec
  exact hdec.le

theorem le_U₀ (hF : σ.ChapterIIFacts) (homni : Omnibus Δ) (h91 : ConjugateMaximalTC σ r)
    {V : Subgroup G} (hV : V ∈ signalizersPerm ⊤ σ.T σ.C r) (hPV : Δ.P ≤ V) :
    V ≤ Δ.P ⊔ genP σ r := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  obtain ⟨V', hV', hVV'⟩ := exists_le_mem_maximals hV
  obtain ⟨m, hm, e⟩ := h91 _ (U₀_mem_maximals hσ Δ hFp hF homni) V' hV'
  have hmF : conjSub m (genP σ r) = genP σ r :=
    conjSub_eq_self_iff.mpr (M_le_normalizer_genP hσ Δ hm)
  have hVC : V' ⊓ σ.C = Δ.P := Δ.P_sylowC.eq_of_le (le_inf (hPV.trans hVV') Δ.P_sylowC.le)
    inf_le_right (hV'.1.1.2.1.to_le inf_le_left)
  have hmP : conjSub m Δ.P = Δ.P := by
    refine Subgroup.eq_of_le_of_card_ge ?_ (card_conjSub m Δ.P).ge
    calc conjSub m Δ.P ≤ V' ⊓ σ.C := le_inf ((conjSub_mono le_sup_left).trans e.le)
          ((conjSub_mono Δ.P_sylowC.le).trans (conjSub_eq_self_iff.mpr hm).le)
      _ = Δ.P := hVC
  rw [← e, conjSub_sup, hmP, hmF] at hVV'
  exact hVV'

theorem normalizer_genP_mem_familyL (hF : σ.ChapterIIFacts) (homni : Omnibus Δ)
    (h91 : ConjugateMaximalTC σ r) (h462 : ABG_IV_6_2 σ r) :
    Subgroup.normalizer (genP σ r : Set G) ∈ σ.familyL r := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  set F := genP σ r with hFdef
  set K := Subgroup.normalizer (F : Set G) with hKdef
  have hCK : σ.C ≤ K := C_le_normalizer_genP
  have hPC : Δ.P ≤ σ.C := Δ.P_sylowC.le
  have hPK : Δ.P ≤ Subgroup.normalizer (F : Set G) := hPC.trans hCK
  have hUmax := U₀_mem_maximals hσ Δ hFp hF homni
  have hUK : Δ.P ⊔ F ∈ maximals (signalizersPerm K σ.T σ.C r) :=
    mem_maximals_of_subset (signalizersPerm_mono le_top) hUmax
      ⟨⟨sup_le hPK Subgroup.le_normalizer, hUmax.1.1.2⟩, hUmax.1.2⟩
  set 𝓧 : Set (Subgroup G) := {X | X ≤ F ∧ σ.C ≤ Subgroup.normalizer (X : Set G) ∧
    σ.Ps r 0 ≤ X ∧ Subgroup.normalizer (X : Set G) ∈ σ.familyL r} with h𝓧
  have hP₀ : σ.Ps r 0 ∈ 𝓧 :=
    ⟨Ps_le_genP 0, C_le_normalizer_Ps 0, le_rfl, normalizer_Ps_mem_familyL hσ Δ⟩
  obtain ⟨X, hX, -⟩ := exists_le_mem_maximals hP₀
  obtain ⟨hXF, hCX, hPX, hHX⟩ := hX.1
  by_cases hXF' : X = F
  · rw [hKdef, ← hXF']
    exact hHX
  exfalso
  have hlt : X < F := lt_of_le_of_ne hXF hXF'
  set H := Subgroup.normalizer (X : Set G) with hHdef
  have hCH : σ.C ≤ H := hCX
  have hDH : σ.D ≤ H := hHX.2.2.1
  have hTH : σ.T ≤ H := (σ.T_le_D hσ).trans hDH
  have hXO : X ≤ oddCoreIn H := le_oddCoreIn Subgroup.le_normalizer le_rfl
    (odd_card_of_isPGroup Δ.prime Δ.ne_two (hFp.to_le hXF))
  have hOH : oddCoreIn H ≠ ⊥ := fun h => Ps_ne_bot Δ (eq_bot_iff.mpr (h ▸ hPX.trans hXO))
  have hHN : oddCoreIn H ⊔ (H ⊓ σ.N) = H := (hF.cover_qgroup H hTH hOH hHX.2.1).2
  have hinv : ∀ v ∈ H, Odd (orderOf v) → σ.x * v * σ.x⁻¹ = v⁻¹ → v ∈ oddCoreIn H := by
    intro v hv hodd hxv
    have hv' : v ∈ ((oddCoreIn H ⊔ (H ⊓ σ.N) : Subgroup G) : Set G) := by
      rw [hHN]
      exact hv
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (inf_le_left.trans (le_normalizer_oddCoreIn H))] at hv'
    obtain ⟨o, ho, n, hn, rfl⟩ := hv'
    have hxn : n * σ.x = σ.x * n := (σ.mem_N_iff n).mp hn.2
    have hxo : σ.x * o⁻¹ * σ.x⁻¹ ∈ oddCoreIn H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreIn H (hTH σ.x_mem_T)) o⁻¹).mp
        ((oddCoreIn H).inv_mem ho)
    apply mem_of_sq_mem hodd
    have hsq : (o * n) ^ 2 = o * (σ.x * o⁻¹ * σ.x⁻¹) :=
      calc (o * n) ^ 2 = (o * n) * (σ.x * (o * n) * σ.x⁻¹)⁻¹ := by
            rw [hxv, inv_inv, pow_two]
        _ = o * (n * σ.x) * n⁻¹ * o⁻¹ * σ.x⁻¹ := by group
        _ = o * (σ.x * n) * n⁻¹ * o⁻¹ * σ.x⁻¹ := by rw [hxn]
        _ = o * (σ.x * o⁻¹ * σ.x⁻¹) := by group
    rw [hsq]
    exact (oddCoreIn H).mul_mem ho hxo
  have hR₁p : IsPGroup r (F ⊓ H : Subgroup G) := hFp.to_le inf_le_left
  have hR₁odd : Odd (Nat.card (F ⊓ H : Subgroup G)) :=
    odd_card_of_isPGroup Δ.prime Δ.ne_two hR₁p
  have hXR : X < F ⊓ H := lt_inf_normalizer hFp hlt
  have hR₁O : F ⊓ H ≤ oddCoreIn H := by
    have hTR : σ.T ≤ Subgroup.normalizer ((F ⊓ H : Subgroup G) : Set G) := fun t ht =>
      mem_normalizer_inf (T_le_normalizer_genP hσ ht) (Subgroup.le_normalizer (hTH ht))
    have hR₁C : F ⊓ H ⊓ σ.C = ⊥ :=
      eq_bot_iff.mpr ((inf_le_inf_right σ.C inf_le_left).trans (genP_inf_C Δ hFp).le)
    refine le_of_comp_subset hσ hR₁odd hTR hR₁C fun i u hu => ?_
    have hodd := odd_orderOf_of_mem hR₁odd hu.1
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hi with rfl | rfl | rfl
    · exact hXO (hPX (comp_subset_Ps hσ Δ hFp hF homni hUK 0
        (comp_mono (inf_le_left.trans le_sup_right) 0 hu)))
    · exact hinv u hu.1.2 hodd (conj_x_of_mem_comp_one hu)
    · exact hinv u hu.1.2 hodd (conj_x_of_mem_comp_two hu)
  have hPO : Δ.P ⊓ oddCoreIn H = ⊥ := by
    have hcovN : (σ.L₀ : Set G) ⊆ ((H ⊓ σ.N : Subgroup G) : Set G) * σ.ON := by
      intro l hl
      obtain ⟨h, hh, o, ho, rfl⟩ := hHX.2.1 hl
      have hhN : h ∈ σ.N := by
        simpa using σ.N.mul_mem (hσ.L₀_le_N hl) (σ.N.inv_mem (σ.ON_le_N ho))
      exact ⟨h, ⟨hh, hhN⟩, o, ho, rfl⟩
    have hON := hF.N_oddCore_of_cover (H ⊓ σ.N) inf_le_right hcovN
    have hOHN : oddCoreIn H ⊓ σ.N ≤ oddCoreIn (H ⊓ σ.N) :=
      le_oddCoreIn (inf_le_inf_right _ (oddCoreIn_le H))
        (fun g hg => mem_normalizer_inf (le_normalizer_oddCoreIn H hg.1)
          (Subgroup.le_normalizer hg.2))
        ((odd_card_oddCoreIn H).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    rw [eq_bot_iff, ← Δ.P_L]
    intro g hg
    exact ⟨hg.1, Subgroup.mem_sup_left (hσ.ON_le_L₀ (hON (hOHN ⟨hg.2, σ.C_le_N (hPC hg.1)⟩)))⟩
  have hPX' : Δ.P ⊔ X ∈ signalizersPerm H σ.T σ.C r := by
    have hp : IsPGroup r (Δ.P ⊔ X : Subgroup G) :=
      hUmax.1.1.2.1.to_le (sup_le_sup_left hXF _)
    refine ⟨⟨sup_le (hPC.trans hCH) Subgroup.le_normalizer, hp, fun t ht => mem_normalizer_sup
      ?_ (hCX ((σ.T_le_C hσ) ht)), inf_T_eq_bot hσ Δ.prime Δ.ne_two hp⟩,
      mul_comm_sup_of_le hPC hCX⟩
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun p hp => (comm_of_mem_C (hPC hp) ht).symm)
  obtain ⟨V, hV, hPXV⟩ := exists_le_mem_maximals hPX'
  have hVU : V ≤ Δ.P ⊔ F :=
    le_U₀ hσ Δ hFp hF homni h91 (signalizersPerm_mono le_top hV.1) (le_sup_left.trans hPXV)
  have hUH : (Δ.P ⊔ F) ⊓ H ∈ signalizersPerm H σ.T σ.C r := by
    have hp : IsPGroup r ((Δ.P ⊔ F) ⊓ H : Subgroup G) := hUmax.1.1.2.1.to_le inf_le_left
    exact ⟨⟨inf_le_right, hp, fun t ht => mem_normalizer_inf (hUmax.1.1.2.2.1 ht)
      (Subgroup.le_normalizer (hTH ht)), inf_T_eq_bot hσ Δ.prime Δ.ne_two hp⟩,
      mul_comm_inf_of_le hCH hUmax.1.2⟩
  have hVeq : (Δ.P ⊔ F) ⊓ H = V := hV.2 _ hUH (le_inf hVU hV.1.1.1)
  have hVO : V ⊓ oddCoreIn H = F ⊓ H := by
    rw [← hVeq]
    refine le_antisymm ?_ (le_inf (inf_le_inf_right H le_sup_right) hR₁O)
    rintro v ⟨⟨hvU, hvH⟩, hvO⟩
    have hv' : v ∈ ((Δ.P ⊔ F : Subgroup G) : Set G) := hvU
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hPK] at hv'
    obtain ⟨p, hp, f, hf, rfl⟩ := hv'
    have hpH : p ∈ H := hCH (hPC hp)
    have hfH : f ∈ H := by simpa using H.mul_mem (H.inv_mem hpH) hvH
    have hfO : f ∈ oddCoreIn H := hR₁O ⟨hf, hfH⟩
    have hpO : p ∈ oddCoreIn H := by
      simpa using (oddCoreIn H).mul_mem hvO ((oddCoreIn H).inv_mem hfO)
    have hp1 : p ∈ Δ.P ⊓ oddCoreIn H := ⟨hp, hpO⟩
    rw [hPO, Subgroup.mem_bot] at hp1
    have hfR : f ∈ F ⊓ H := ⟨hf, hfH⟩
    simpa [hp1] using hfR
  obtain ⟨R₀, hR₀, hR₀V⟩ := (homni H hCH V hV).part_ii_b
  have hR₁S : IsSylowOf r (F ⊓ H) (oddCoreIn H) := by
    rw [hR₀.eq_of_le ((le_inf hR₀V hR₀.le).trans hVO.le) hR₁O hR₁p]
    exact hR₀
  have hDR : σ.D ≤ Subgroup.normalizer ((F ⊓ H : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_inf (D_le_normalizer_genP hσ Δ hg) (Subgroup.le_normalizer (hDH hg))
  have hR₁L := h462 H hHX (F ⊓ H) (ne_bot_of_le_ne_bot (Ps_ne_bot Δ) (hPX.trans hXR.le)) hR₁p
    hR₁O hDR (subset_normalizer_mul hR₁S (le_normalizer_oddCoreIn H))
    ⟨F ⊓ H, hR₁S, Subgroup.le_normalizer⟩
  have hR₁X : F ⊓ H ∈ 𝓧 := ⟨inf_le_left, fun c hc => mem_normalizer_inf (hCK hc)
    (Subgroup.le_normalizer (hCH hc)), hPX.trans hXR.le, hR₁L⟩
  exact (ne_of_gt hXR) (hX.2 _ hR₁X hXR.le)

end PGroup

end NotPGroup

open NotPGroup

theorem notPGroupP (hσ : σ.IsValid) (hF : σ.ChapterIIFacts) (Δ : Data σ r)
    (homni : Omnibus Δ) (h462 : ABG_IV_6_2 σ r) : NotPGroupP σ r := fun hFp =>
  not_covers hσ Δ hFp hF
    (normalizer_genP_mem_familyL hσ Δ hFp hF homni (conjugateMaximalTC hσ Δ homni) h462).2.1

end CFSG.ABGTheoremB.TotallyInverted
