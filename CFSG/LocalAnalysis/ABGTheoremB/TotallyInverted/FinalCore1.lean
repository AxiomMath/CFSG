module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalLemmas3

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Sec11

open CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

omit [Finite G] in
theorem mem_sup_iff_of_le_normalizer' {A B : Subgroup G}
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) {g : G} :
    g ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left A B hBA]
  exact Iff.rfl

omit [Finite G] in
theorem inf_sup_eq_of_le_left {A B M : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hAM : A ≤ M) : M ⊓ (A ⊔ B) = A ⊔ (M ⊓ B) := by
  apply le_antisymm
  · rintro g ⟨hgM, hg⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hAB).mp hg
    have hbM : b ∈ M := by
      have := M.mul_mem (M.inv_mem (hAM ha)) hgM
      rwa [inv_mul_cancel_left] at this
    exact Subgroup.mul_mem_sup ha ⟨hbM, hb⟩
  · exact sup_le (le_inf hAM le_sup_left) (inf_le_inf_left _ le_sup_right)

omit [Finite G] in
theorem coe_sup_of_mul_comm {A B : Subgroup G} (h : (A : Set G) * B = B * A) :
    ((A ⊔ B : Subgroup G) : Set G) = A * B := by
  let K : Subgroup G :=
    { carrier := (A : Set G) * B
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        have hba : b * a' ∈ (B : Set G) * A := ⟨b, hb, a', ha', rfl⟩
        rw [← h] at hba
        obtain ⟨a'', ha'', b'', hb'', he⟩ := hba
        have he : a'' * b'' = b * a' := he
        refine ⟨a * a'', A.mul_mem ha ha'', b'' * b', B.mul_mem hb'' hb', ?_⟩
        calc a * a'' * (b'' * b') = a * (a'' * b'') * b' := by group
          _ = a * b * (a' * b') := by rw [he]; group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, one_mul 1⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        have : b⁻¹ * a⁻¹ ∈ (B : Set G) * A := ⟨b⁻¹, B.inv_mem hb, a⁻¹, A.inv_mem ha, rfl⟩
        rw [← h] at this
        simpa [mul_inv_rev] using this }
  apply Set.Subset.antisymm
  · have hle : A ⊔ B ≤ K := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩)
      (fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩)
    exact hle
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

omit [Finite G] in
theorem conjSub_mem_maximals_signalizers {H X Y : Subgroup G} {p : ℕ} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hY : Y ∈ maximals (signalizers H X p)) :
    conjSub g Y ∈ maximals (signalizers (conjSub g H) X p) := by
  have key : ∀ {k : G} {H' Z : Subgroup G}, k ∈ Subgroup.normalizer (X : Set G) →
      Z ∈ signalizers H' X p → conjSub k Z ∈ signalizers (conjSub k H') X p := by
    rintro k H' Z hk ⟨hZH, hZp, hXZ, hZX⟩
    refine ⟨conjSub_mono hZH, isPGroup_conjSub hZp k, le_normalizer_conjSub hk hXZ, ?_⟩
    rw [← conjSub_eq_self_iff.mpr hk, ← conjSub_inf, hZX, conjSub_bot]
  refine ⟨key hg hY.1, fun R' hR' hYR' => ?_⟩
  have h1 := key (Subgroup.inv_mem _ hg) hR'
  rw [conjSub_inv_conjSub] at h1
  have h2 := hY.2 _ h1 (by rwa [← conjSub_le_iff])
  rw [← h2, conjSub_conjSub_inv]

omit [Finite G] in
theorem comp_inf_C_eq_bot {U W : Subgroup G} (hU : Odd (Nat.card U)) {i : Fin 3}
    (hW : (W : Set G) = comp σ U i) : W ⊓ σ.C = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  have hu1 : u ∈ comp σ U i := by rw [← hW]; exact hu.1
  exact eq_one_of_conj_eq_inv_of_commute (odd_orderOf_of_mem hU hu1.1) hu1.2.2
    (Subgroup.mem_centralizer_iff.mp hu.2 _ (xs_mem_T (i + 1)))

theorem pCoreIn_sup_le (hσ : σ.IsValid) (hr : r.Prime) (hr2 : r ≠ 2) {H U : Subgroup G}
    (hCH : σ.C ≤ H) (hU : U ∈ maximals (signalizersPerm H σ.T σ.C r)) :
    pCoreIn r (U ⊔ σ.C) ≤ U := by
  set P := pCoreIn r (U ⊔ σ.C) with hP
  have hPn : U ⊔ σ.C ≤ Subgroup.normalizer (P : Set G) := le_normalizer_pCoreIn r _
  have hUp : IsPGroup r U := hU.1.1.2.1
  have hX : IsPGroup r (U ⊔ P : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hUp (isPGroup_pCoreIn r _) (le_sup_left.trans hPn)
  have hperm : (U : Set G) * σ.C = σ.C * U := hU.1.2
  have hsupU := coe_sup_of_mul_comm hperm
  have hsupU' : ((U ⊔ σ.C : Subgroup G) : Set G) = σ.C * U := hsupU.trans hperm
  have hXle : U ⊔ P ≤ U ⊔ σ.C := sup_le le_sup_left (pCoreIn_le r _)
  have hmulle : ∀ {A B : Subgroup G}, A ≤ U ⊔ σ.C → B ≤ U ⊔ σ.C →
      (A : Set G) * B ⊆ ((U ⊔ σ.C : Subgroup G) : Set G) := by
    rintro A B hA hB _ ⟨a, ha, b, hb, rfl⟩
    exact (U ⊔ σ.C).mul_mem (hA ha) (hB hb)
  have h1 : ((U ⊔ P : Subgroup G) : Set G) * σ.C = (U : Set G) * σ.C := by
    apply Set.Subset.antisymm
    · rw [← hsupU]
      exact hmulle hXle le_sup_right
    · exact Set.mul_subset_mul_right (le_sup_left : U ≤ U ⊔ P)
  have h2 : (σ.C : Set G) * ((U ⊔ P : Subgroup G) : Set G) = σ.C * U := by
    apply Set.Subset.antisymm
    · rw [← hsupU']
      exact hmulle le_sup_right hXle
    · exact Set.mul_subset_mul_left (le_sup_left : U ≤ U ⊔ P)
  have hmem : U ⊔ P ∈ signalizersPerm H σ.T σ.C r :=
    ⟨⟨hXle.trans (sup_le hU.1.1.1 hCH), hX,
      fun t ht => mem_normalizer_sup (hU.1.1.2.2.1 ht)
        (hPn ((le_sup_right : σ.C ≤ U ⊔ σ.C) (σ.T_le_C hσ ht))),
      inf_T_eq_bot hσ hr hr2 hX⟩, by rw [h1, h2, hperm]⟩
  have heq := hU.2 _ hmem le_sup_left
  rw [← heq]
  exact le_sup_right

theorem comp_zero_eq_R_of (hσ : σ.IsValid) (Δ : Data σ r) (homni : Omnibus Δ)
    {H U : Subgroup G} (hCH : σ.C ≤ H) (hU : U ∈ maximals (signalizersPerm H σ.T σ.C r))
    (hRU : R Δ 0 ≤ U) : comp σ U 0 = (R Δ 0 : Set G) := by
  have hUodd : Odd (Nat.card U) := odd_card_of_isPGroup Δ.prime Δ.ne_two hU.1.1.2.1
  obtain ⟨W, hW, hCW, -⟩ := (homni H hCH U hU).part_i_b 0
  have hWmem : W ∈ signalizers σ.N σ.C r := by
    refine ⟨fun u hu => ?_, hU.1.1.2.1.to_le (fun u hu => ?_), hCW, comp_inf_C_eq_bot hUodd hW⟩
    · rw [← SetLike.mem_coe, hW] at hu
      exact (Subgroup.mem_centralizer_singleton_iff.mpr hu.2.1.symm)
    · rw [← SetLike.mem_coe, hW] at hu
      exact hu.1
  have hRW : R Δ 0 ≤ W := fun u hu => by
    rw [← SetLike.mem_coe, hW]
    exact R_subset_comp Δ hσ hRU hu
  rw [← hW, (R_mem_maximals Δ 0).2 W hWmem hRW]

theorem M_le_normalizer_T (Δ : Data σ r) : σ.M ≤ Subgroup.normalizer (σ.T : Set G) := by
  rw [Δ.M_eq]
  refine sup_le (fun c hc => mem_normalizer_of_conj_mem fun t ht => ?_) ?_
  · rw [(Subgroup.mem_centralizer_iff.mp hc t ht).symm, mul_inv_cancel_right]
    exact ht
  · rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact Δ.d_mem.2
    · exact a_mem_normalizer_T Δ

omit [Finite G] in
theorem commutator_mem_oddCoreIn {H : Subgroup G} {t : G} (ht : t ∈ H)
    (hH : oddCoreIn H ⊔ (H ⊓ Subgroup.centralizer ({t} : Set G)) = H) {k : G} (hk : k ∈ H) :
    k * t * k⁻¹ * t⁻¹ ∈ oddCoreIn H := by
  have hle : H ⊓ Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer ((oddCoreIn H : Subgroup G) : Set G) :=
    inf_le_left.trans (le_normalizer_oddCoreIn H)
  have hk' : k ∈ oddCoreIn H ⊔ (H ⊓ Subgroup.centralizer ({t} : Set G)) := by rw [hH]; exact hk
  obtain ⟨o, ho, n, hn, rfl⟩ := (mem_sup_iff_of_le_normalizer' hle).mp hk'
  have htn : n * t * n⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hn.2, mul_inv_cancel_right]
  have hto : t * o⁻¹ * t⁻¹ ∈ oddCoreIn H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreIn H ht) _).mp
      ((oddCoreIn H).inv_mem ho)
  have e : o * n * t * (o * n)⁻¹ * t⁻¹ = o * (t * o⁻¹ * t⁻¹) := by
    calc o * n * t * (o * n)⁻¹ * t⁻¹ = o * (n * t * n⁻¹) * o⁻¹ * t⁻¹ := by group
      _ = o * (t * o⁻¹ * t⁻¹) := by rw [htn]; group
  rw [e]
  exact (oddCoreIn H).mul_mem ho hto

omit [Finite G] in
theorem C_le_normalizer_pCoreIn_sup (U : Subgroup G) :
    σ.C ≤ Subgroup.normalizer (pCoreIn r (U ⊔ σ.C) : Set G) :=
  le_sup_right.trans (le_normalizer_pCoreIn r _)

theorem orderOf_xs (hσ : σ.IsValid) (i : Fin 3) : orderOf (σ.xs i) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact xs_mul_xs hσ i) (xs_ne_one hσ i)

theorem not_Q_sup_Qs_le (hσ : σ.IsValid) (Δ : Data σ r) (hδq : σ.DeltaEpsMinus ∧ r ∣ σ.q)
    (i : Fin 3) {U : Subgroup G} (hU : Odd (Nat.card U)) : ¬ Δ.Q i ⊔ Δ.Qs i ≤ U := by
  intro hle
  have hx : σ.xs i ∈ conjSub (Δ.a ^ (i : ℕ)) Δ.J := by
    have e : σ.xs i = Δ.a ^ (i : ℕ) * σ.xs 0 * (Δ.a ^ (i : ℕ))⁻¹ := by
      rw [a_pow_conj_xs, zero_add]
    rw [e]
    exact conj_mem_conjSub (x_mem_J hσ Δ (J_inf_ON Δ hδq))
  rw [J_conj_eq Δ hδq] at hx
  have hodd := odd_orderOf_of_mem hU (hle hx)
  rw [orderOf_xs hσ] at hodd
  exact absurd hodd (by decide)

structure CoreHyp (Δ : Data σ r) (V U : Subgroup G) (z : G) : Prop where
  valid : σ.IsValid
  facts : σ.ChapterIIFacts
  omni : Omnibus Δ
  inputs : Inputs Δ
  conj91 : ConjugateMaximalTC σ r
  deltaEps : σ.DeltaEpsMinus ∧ r ∣ σ.q
  maxV : V ∈ maximals (signalizersPerm (Kp σ r) σ.T σ.C r)
  R_le_V : R Δ 0 ≤ V
  X_eq : (Δ.Qs 1 : Set G) = comp σ V 1 ∩ Subgroup.centralizer (R Δ 0 : Set G)
  pgroup : IsPGroup r (R Δ 0 ⊔ Rs Δ 1 : Subgroup G)
  not_pGroupR : ¬ PGroupR Δ
  maxU : U ∈ maximals (signalizersPerm ⊤ σ.T σ.C r)
  V_le_U : V ≤ U
  swap : IsSwap Δ z

namespace CoreHyp

variable {Δ : Data σ r} {V U : Subgroup G} {z : G} (h : CoreHyp Δ V U z)
include h

theorem Qs1_subset : (Δ.Qs 1 : Set G) ⊆ comp σ V 1 := fun u hu => by
  have hu' : u ∈ (Δ.Qs 1 : Set G) := hu
  rw [h.X_eq] at hu'
  exact hu'.1

theorem Qs1_le_V : Δ.Qs 1 ≤ V := fun _ hu => (h.Qs1_subset hu).1

theorem Qs1_le_centralizer : Δ.Qs 1 ≤ Subgroup.centralizer (R Δ 0 : Set G) := fun u hu => by
  have hu' : u ∈ (Δ.Qs 1 : Set G) := hu
  rw [h.X_eq] at hu'
  exact hu'.2

theorem odd_V : Odd (Nat.card V) := odd_card_V Δ h.maxV

theorem odd_U : Odd (Nat.card U) :=
  odd_card_of_isPGroup Δ.prime Δ.ne_two h.maxU.1.1.2.1

theorem T_le_C' : σ.T ≤ σ.C := σ.T_le_C h.valid

theorem Y_sylow : IsSylowOf r (V ⊓ oddCoreIn (Kp σ r)) (oddCoreIn (Kp σ r)) :=
  isSylowOf_V_inf_oddCore Δ h.omni h.maxV

theorem Y_C : σ.C ≤ Subgroup.normalizer ((V ⊓ oddCoreIn (Kp σ r) : Subgroup G) : Set G) :=
  C_le_normalizer_V_inf_oddCore h.valid h.facts Δ h.omni h.maxV h.R_le_V

theorem Y_T : σ.T ≤ Subgroup.normalizer ((V ⊓ oddCoreIn (Kp σ r) : Subgroup G) : Set G) :=
  T_le_normalizer_V_inf_oddCore h.valid h.maxV

theorem Y_inf_C : V ⊓ oddCoreIn (Kp σ r) ⊓ σ.C = ⊥ := by
  rw [inf_right_comm]
  exact V_inf_C_inf_oddCore h.valid Δ h.maxV

theorem odd_Y : Odd (Nat.card (V ⊓ oddCoreIn (Kp σ r) : Subgroup G)) :=
  h.odd_V.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

theorem z_mem_Kp : z ∈ Kp σ r := N_le_Kp (h.swap.mem_N h.valid)

theorem conjSub_z_Y : conjSub z (V ⊓ oddCoreIn (Kp σ r)) = V ⊓ oddCoreIn (Kp σ r) := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  have hO : conjSub z (oddCoreIn (Kp σ r)) = oddCoreIn (Kp σ r) :=
    conjSub_eq_self_iff.mpr (le_normalizer_oddCoreIn _ h.z_mem_Kp)
  have hzY : IsSylowOf r (conjSub z (V ⊓ oddCoreIn (Kp σ r))) (oddCoreIn (Kp σ r)) := by
    have h1 := isSylowOf_conjSub h.Y_sylow z
    rw [hO] at h1
    exact h1
  have hTzY := le_normalizer_conjSub h.swap.mem_normalizer_T h.Y_T
  have hTO : σ.T ≤ Subgroup.normalizer ((oddCoreIn (Kp σ r) : Subgroup G) : Set G) :=
    (h.T_le_C'.trans C_le_Kp).trans (le_normalizer_oddCoreIn _)
  obtain ⟨c, hc, hcY⟩ := exists_conjSub_eq_of_coprime (card_T h.valid) (odd_card_oddCoreIn _)
    hTO h.Y_sylow hzY h.Y_T hTzY
  rw [← hcY, conjSub_eq_self_iff.mpr (h.Y_C hc.2)]

theorem Qs1_le_Y : Δ.Qs 1 ≤ V ⊓ oddCoreIn (Kp σ r) :=
  le_inf h.Qs1_le_V
    (fun _ hu => comp_one_subset_oddCore h.valid h.facts Δ h.maxV (h.Qs1_subset hu))

theorem Q2_le_Y : Δ.Q 2 ≤ V ⊓ oddCoreIn (Kp σ r) := by
  have := conjSub_mono (g := z) h.Qs1_le_Y
  rwa [(h.swap.conj_Qs12 h.deltaEps h.valid).1, h.conjSub_z_Y] at this

theorem Q2_le_V : Δ.Q 2 ≤ V := h.Q2_le_Y.trans inf_le_left

theorem Q_inf_C (i : Fin 3) : Δ.Q i ⊓ σ.C = ⊥ :=
  eq_bot_iff.mpr ((inf_le_inf_right _ (Q_le_R Δ i)).trans (R_inf_C Δ h.valid i).le)

theorem Qs_inf_C (i : Fin 3) : Δ.Qs i ⊓ σ.C = ⊥ :=
  eq_bot_iff.mpr ((inf_le_inf_right _ (Qs_le_Rs Δ i)).trans (Rs_inf_C Δ h.valid i).le)

theorem Q_subset_comp (i : Fin 3) {W : Subgroup G} (hW : Δ.Q i ≤ W) :
    (Δ.Q i : Set G) ⊆ comp σ W i := fun _ hu =>
  comp_mono hW i (mem_comp_of_le_Ns h.valid
    (odd_card_of_isPGroup Δ.prime Δ.ne_two (Δ.Q_pgroup i).1)
    (T_le_normalizer_of_C_le h.valid (C_le_normalizer_Q Δ i)) (h.Q_inf_C i)
    (Q_le_Ns Δ h.valid i) hu)

theorem Qs_subset_comp (i : Fin 3) {W : Subgroup G} (hW : Δ.Qs i ≤ W) :
    (Δ.Qs i : Set G) ⊆ comp σ W i := fun _ hu =>
  comp_mono hW i (mem_comp_of_le_Ns h.valid
    (odd_card_of_isPGroup Δ.prime Δ.ne_two (Δ.Q_pgroup i).2)
    (T_le_normalizer_of_C_le h.valid (C_le_normalizer_Qs Δ i)) (h.Qs_inf_C i)
    (Qs_le_Ns Δ h.valid i) hu)

theorem Q2_subset_comp : (Δ.Q 2 : Set G) ⊆ comp σ V 2 := h.Q_subset_comp 2 h.Q2_le_V

theorem U_omni : OmnibusAt Δ ⊤ U := h.omni ⊤ le_top U h.maxU

theorem V_omni : OmnibusAt Δ (Kp σ r) V := omnibusAt_V Δ h.omni h.maxV

theorem R0_le_U : R Δ 0 ≤ U := h.R_le_V.trans h.V_le_U

theorem comp_U_zero : comp σ U 0 = (R Δ 0 : Set G) :=
  comp_zero_eq_R_of h.valid Δ h.omni le_top h.maxU h.R0_le_U

theorem comp_V_zero : comp σ V 0 = (R Δ 0 : Set G) :=
  comp_zero_eq_R_of h.valid Δ h.omni C_le_Kp h.maxV h.R_le_V

theorem Ustar_le_U : pCoreIn r (U ⊔ σ.C) ≤ U :=
  pCoreIn_sup_le h.valid Δ.prime Δ.ne_two le_top h.maxU

theorem Vstar_le_V : pCoreIn r (V ⊔ σ.C) ≤ V :=
  pCoreIn_sup_le h.valid Δ.prime Δ.ne_two C_le_Kp h.maxV

theorem Ustar_inf_C : pCoreIn r (U ⊔ σ.C) ⊓ σ.C = ⊥ := h.U_omni.part_vi.1.1.2.2.2

theorem Vstar_inf_C : pCoreIn r (V ⊔ σ.C) ⊓ σ.C = ⊥ := h.V_omni.part_vi.1.1.2.2.2

theorem comp_U_subset_Ustar (i : Fin 3) : comp σ U i ⊆ pCoreIn r (U ⊔ σ.C) := by
  obtain ⟨W, hW, hCW, -⟩ := h.U_omni.part_i_b i
  have hWU : W ≤ U := fun u hu => by rw [← SetLike.mem_coe, hW] at hu; exact hu.1
  have hWmem : W ∈ signalizers ⊤ σ.C r :=
    ⟨le_top, h.maxU.1.1.2.1.to_le hWU, hCW, comp_inf_C_eq_bot h.odd_U hW⟩
  rw [← hW]
  exact h.U_omni.part_vi.2 W hWmem hWU

theorem comp_V_subset_Vstar (i : Fin 3) : comp σ V i ⊆ pCoreIn r (V ⊔ σ.C) := by
  obtain ⟨W, hW, hCW, -⟩ := h.V_omni.part_i_b i
  have hWV : W ≤ V := fun u hu => by rw [← SetLike.mem_coe, hW] at hu; exact hu.1
  have hWmem : W ∈ signalizers (Kp σ r) σ.C r :=
    ⟨hWV.trans (V_le_Kp h.maxV), h.maxV.1.1.2.1.to_le hWV, hCW, comp_inf_C_eq_bot h.odd_V hW⟩
  rw [← hW]
  exact h.V_omni.part_vi.2 W hWmem hWV

theorem Vstar_le_Ustar : pCoreIn r (V ⊔ σ.C) ≤ pCoreIn r (U ⊔ σ.C) :=
  h.U_omni.part_vi.2 _
    ⟨le_top, isPGroup_pCoreIn r _, C_le_normalizer_pCoreIn_sup V, h.Vstar_inf_C⟩
    (h.Vstar_le_V.trans h.V_le_U)

theorem Rs1_le_U : Rs Δ 1 ≤ U := by
  have hσ := h.valid
  have hδq := h.deltaEps
  set Y₂ : Subgroup G := R Δ 0 ⊔ Rs Δ 1 with hY₂
  have hCY : σ.C ≤ Subgroup.normalizer (Y₂ : Set G) :=
    le_normalizer_sup (C_le_normalizer_R Δ 0) (C_le_normalizer_Rs Δ 1)
  have hY₂mem : Y₂ ∈ signalizersPerm ⊤ σ.T σ.C r :=
    ⟨⟨le_top, h.pgroup, h.T_le_C'.trans hCY, inf_T_eq_bot hσ Δ.prime Δ.ne_two h.pgroup⟩,
      mul_comm_of_le_normalizer hCY⟩
  obtain ⟨U₂, hU₂, hYU₂⟩ := exists_le_mem_maximals hY₂mem
  obtain ⟨m, hm, hmU⟩ := h.conj91 U₂ hU₂ U h.maxU
  have hmT : m ∈ Subgroup.normalizer (σ.T : Set G) := M_le_normalizer_T Δ hm
  obtain ⟨j₀, hj₀⟩ := exists_conj_xs_eq hσ hmT 0
  obtain ⟨j₁, hj₁⟩ := exists_conj_xs_eq hσ hmT 1
  have hNs : ∀ {i j : Fin 3}, m * σ.xs i * m⁻¹ = σ.xs j → conjSub m (σ.Ns i) = σ.Ns j := by
    intro i j hij
    rw [Setting.Ns, conjSub_centralizer_singleton, hij]
    rfl
  have hA : conjSub m (R Δ 0) ∈ maximals (signalizers (σ.Ns j₀) σ.C r) := by
    rw [← hNs hj₀]
    exact conjSub_mem_maximals_signalizers hm (R_mem_maximals Δ 0)
  have hB : conjSub m (Rs Δ 1) ∈ maximals (signalizers (σ.Ns j₁) σ.C r) := by
    rw [← hNs hj₁]
    exact conjSub_mem_maximals_signalizers hm (Rs_mem_maximals Δ 1)
  have hAU : conjSub m (R Δ 0) ≤ U := hmU ▸ conjSub_mono (le_sup_left.trans hYU₂)
  have hBU : conjSub m (Rs Δ 1) ≤ U := hmU ▸ conjSub_mono (le_sup_right.trans hYU₂)
  have hj : j₀ ≠ j₁ := by
    intro he
    rw [he, ← hj₁] at hj₀
    exact hσ.x_ne_x₂ (mul_left_cancel (mul_right_cancel hj₀))
  have hUp : IsPGroup r U := h.maxU.1.1.2.1
  have key : ∀ j : Fin 3, j ≠ 0 → ∀ Y' ∈ maximals (signalizers (σ.Ns j) σ.C r), Y' ≤ U →
      Rs Δ 1 ≤ U := by
    intro j hj0 Y' hY' hY'U
    rw [Δ.lemma71 j] at hY'
    split_ifs at hY'
    match j, hj0, hY' with
    | 1, _, hY' =>
      rcases hY' with rfl | hY'
      · exfalso
        exact not_Q_sup_Qs_le hσ Δ hδq 1 (odd_card_of_isPGroup Δ.prime Δ.ne_two hUp)
          (sup_le (le_sup_right.trans hY'U) (h.Qs1_le_V.trans h.V_le_U))
      · rw [Set.mem_singleton_iff] at hY'
        rw [Rs, sup_comm, ← hY']
        exact hY'U
    | 2, _, hY' =>
      exfalso
      rcases hY' with rfl | hY'
      · exact h.not_pGroupR (hUp.to_le (sup_le h.R0_le_U (by rw [R, sup_comm]; exact hY'U)))
      · rw [Set.mem_singleton_iff] at hY'
        exact not_Q_sup_Qs_le hσ Δ hδq 2 (odd_card_of_isPGroup Δ.prime Δ.ne_two hUp)
          (sup_le (h.Q2_le_V.trans h.V_le_U) (hY' ▸ le_sup_right |>.trans hY'U))
  by_cases hj0 : j₀ = 0
  · exact key j₁ (fun h1 => hj (hj0.trans h1.symm)) _ hB hBU
  · exact key j₀ hj0 _ hA hAU

theorem comp_U_one : comp σ U 1 = (Rs Δ 1 : Set G) := by
  obtain ⟨W, hW, hCW, -⟩ := h.U_omni.part_i_b 1
  have hWmem : W ∈ signalizers (σ.Ns 1) σ.C r := by
    refine ⟨fun u hu => ?_, h.maxU.1.1.2.1.to_le (fun u hu => ?_), hCW,
      comp_inf_C_eq_bot h.odd_U hW⟩
    · rw [← SetLike.mem_coe, hW] at hu
      exact Subgroup.mem_centralizer_singleton_iff.mpr hu.2.1.symm
    · rw [← SetLike.mem_coe, hW] at hu
      exact hu.1
  have hRW : Rs Δ 1 ≤ W := fun u hu => by
    rw [← SetLike.mem_coe, hW]
    exact Rs_subset_comp Δ h.valid h.Rs1_le_U hu
  rw [← hW, (Rs_mem_maximals Δ 1).2 W hWmem hRW]

theorem J_le_normalizer_Y :
    Δ.J ≤ Subgroup.normalizer ((V ⊓ oddCoreIn (Kp σ r) : Subgroup G) : Set G) := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  have hσ := h.valid
  set O := oddCoreIn (Kp σ r) with hO
  set Y : Subgroup G := V ⊓ O with hY
  have hcov := Kp_cover Δ hσ h.facts
  have hxK : σ.x ∈ Kp σ r := N_le_Kp σ.x_mem_N
  have hxY : σ.x ∈ Subgroup.normalizer (Y : Set G) := h.Y_T σ.x_mem_T
  refine (J_le_of_covers hσ Δ (J_inf_ON Δ h.deltaEps)
    (Y := σ.N ⊓ Subgroup.normalizer (Y : Set G)) inf_le_left ?_).trans inf_le_right
  intro l hl
  have hlK : l ∈ Kp σ r := N_le_Kp (hσ.L₀_le_N hl)
  obtain ⟨o, ho, n, hn, rfl⟩ :=
    exists_mul_normalizer_of_isSylowOf h.Y_sylow (le_normalizer_oddCoreIn (Kp σ r)) hlK
  have hnK : n ∈ Kp σ r := by
    have := (Kp σ r).mul_mem ((Kp σ r).inv_mem (oddCoreIn_le _ ho)) hlK
    rwa [inv_mul_cancel_left] at this
  set o' := n * σ.x * n⁻¹ * σ.x⁻¹ with ho'
  have ho'O : o' ∈ O := commutator_mem_oddCoreIn hxK hcov hnK
  have ho'Y : o' ∈ Subgroup.normalizer (Y : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hxY)
      (Subgroup.inv_mem _ hn)) (Subgroup.inv_mem _ hxY)
  have hxinv := x_inv hσ
  have hinv' : σ.x * o' * σ.x⁻¹ = o'⁻¹ := by
    have hxx := x_mul_x hσ
    rw [ho', hxinv, eq_inv_iff_mul_eq_one]
    calc σ.x * (n * σ.x * n⁻¹ * σ.x) * σ.x * (n * σ.x * n⁻¹ * σ.x) =
          σ.x * n * σ.x * n⁻¹ * (σ.x * σ.x) * n * σ.x * n⁻¹ * σ.x := by group
      _ = σ.x * n * σ.x * n⁻¹ * n * σ.x * n⁻¹ * σ.x := by rw [hxx, mul_one]
      _ = σ.x * n * (σ.x * σ.x) * n⁻¹ * σ.x := by group
      _ = 1 := by rw [hxx, mul_one, mul_inv_cancel_right, hxx]
  have ho'odd : Odd (orderOf o') := odd_orderOf_of_mem (odd_card_oddCoreIn _) ho'O
  obtain ⟨m, hm⟩ := exists_pow_sq_eq ho'odd
  set s := o' ^ m with hs
  have hsO : s ∈ O := O.pow_mem ho'O m
  have hsY : s ∈ Subgroup.normalizer (Y : Set G) := Subgroup.pow_mem _ ho'Y m
  have hs2 : s * s = o' := by rw [hs, ← pow_two, ← pow_mul, mul_comm, pow_mul, hm]
  have hxs : σ.x * s * σ.x⁻¹ = s⁻¹ := by
    rw [hs, ← conj_pow, hinv', inv_pow]
  have hsx : s * σ.x * s⁻¹ = n * σ.x * n⁻¹ := by
    calc s * σ.x * s⁻¹ = s * (σ.x * s⁻¹ * σ.x⁻¹) * σ.x := by group
      _ = s * s * σ.x := by
          rw [show σ.x * s⁻¹ * σ.x⁻¹ = (σ.x * s * σ.x⁻¹)⁻¹ by group, hxs, inv_inv, mul_assoc]
      _ = n * σ.x * n⁻¹ := by rw [hs2, ho']; group
  set c := s⁻¹ * n with hc
  have hcN : c ∈ σ.N := by
    rw [Setting.N, Subgroup.mem_centralizer_singleton_iff]
    calc c * σ.x = s⁻¹ * (n * σ.x * n⁻¹) * n := by rw [hc]; group
      _ = s⁻¹ * (s * σ.x * s⁻¹) * n := by rw [hsx]
      _ = σ.x * c := by rw [hc]; group
  have hcY : c ∈ Subgroup.normalizer (Y : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hsY) hn
  have hos : o * s ∈ O ⊓ σ.N := by
    refine ⟨O.mul_mem ho hsO, ?_⟩
    have : o * s = o * n * c⁻¹ := by rw [hc]; group
    rw [this]
    exact σ.N.mul_mem (hσ.L₀_le_N hl) (σ.N.inv_mem hcN)
  have hosON : o * s ∈ σ.ON := oddCore_Kp_inf_N_le_ON hos
  refine ⟨c, ⟨hcN, hcY⟩, c⁻¹ * (o * s) * c, ?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp (σ.N_le_normalizer_ON (σ.N.inv_mem hcN)) _).mp hosON
    simpa [mul_assoc] using this
  · show c * (c⁻¹ * (o * s) * c) = o * n
    rw [hc]
    group

end CoreHyp

end CFSG.ABGTheoremB.TotallyInverted.Sec11
