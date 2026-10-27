module

public import CFSG.LocalAnalysis.ABGTheoremB.V4Lemma5
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusQuotient

public section

namespace CFSG.ABGTheoremB.V4

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools CFSG.ABGTheoremB.TotallyInverted
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {J W : Subgroup G}

theorem le_oddCoreIn_sup_of_le_sup_C (hσ : σ.IsValid) {H U P : Subgroup G} (hTH : σ.T ≤ H)
    (hUH : U ≤ oddCoreIn H ⊔ (H ⊓ σ.C)) (hUp : IsPGroup σ.p U)
    (hTU : σ.T ≤ Subgroup.normalizer (U : Set G)) (hP : IsSylowOf σ.p P σ.C) (hPU : P ≤ U) :
    U ≤ oddCoreIn H ⊔ P := by
  have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
  set A := oddCoreIn H with hA
  have hHA : H ≤ Subgroup.normalizer (A : Set G) := le_normalizer_oddCoreIn H
  have hTA : σ.T ≤ Subgroup.normalizer (A : Set G) := hTH.trans hHA
  have hTUA : σ.T ≤ Subgroup.normalizer ((U ⊓ A : Subgroup G) : Set G) :=
    (le_inf hTU hTA).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hUAp : IsPGroup σ.p (U ⊓ A : Subgroup G) := hUp.to_le inf_le_left
  have hUAsolv : Group.IsSolvable (U ⊓ A : Subgroup G) := by
    have := hUAp.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card σ.T) (Nat.card (U ⊓ A : Subgroup G)) :=
    coprime_card_of_two_of_odd (isPGroup_T hσ)
      (Omnibus.odd_card_of_isPGroup hσ.p_prime hσ.p_ne_two hUAp)
  intro u hu
  obtain ⟨n, hn, hun⟩ := exists_mul_mem_centralizer_of_coprime hTUA hUAsolv hcop (g := u)
    (fun t ht => by
      refine ⟨U.mul_mem (U.inv_mem hu) ((Subgroup.mem_normalizer_iff.mp (hTU ht) u).mp hu), ?_⟩
      have hHC : H ⊓ σ.C ≤ Subgroup.normalizer (A : Set G) := inf_le_left.trans hHA
      obtain ⟨a, ha, c, hc, rfl⟩ := (mem_sup_iff_of_le_normalizer' hHC).mp (hUH hu)
      have htc : t * c * t⁻¹ = c := by
        rw [(Subgroup.mem_centralizer_iff.mp hc.2) t ht]; group
      have hta : a⁻¹ * (t * a * t⁻¹) ∈ A :=
        A.mul_mem (A.inv_mem ha) ((Subgroup.mem_normalizer_iff.mp (hTA ht) a).mp ha)
      have e : (a * c)⁻¹ * (t * (a * c) * t⁻¹) = c⁻¹ * (a⁻¹ * (t * a * t⁻¹)) * c := by
        calc (a * c)⁻¹ * (t * (a * c) * t⁻¹) =
            c⁻¹ * (a⁻¹ * (t * a * t⁻¹)) * (t * c * t⁻¹) := by group
          _ = c⁻¹ * (a⁻¹ * (t * a * t⁻¹)) * c := by rw [htc]
      rw [e]
      have := (Subgroup.mem_normalizer_iff.mp (hHA (H.inv_mem hc.1)) _).mp hta
      simpa [mul_assoc] using this)
  have hUC : U ⊓ σ.C = P :=
    hP.eq_of_le (le_inf hPU hP.le) inf_le_right (hUp.to_le inf_le_left)
  have hunP : u * n ∈ P := by
    rw [← hUC]
    exact ⟨U.mul_mem hu hn.1, hun⟩
  rw [show u = (u * n) * n⁻¹ by group, sup_comm]
  exact Subgroup.mul_mem_sup hunP (A.inv_mem hn.2)

theorem exists_signalizer_hull (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hJ : σ.IsV21Layer J)
    (h31 : LemmaV31Input σ J) (hQS : QGroupSignalizerInput σ) (hDS : DGroupSignalizerInput σ)
    {H : Subgroup G} (hDH : σ.D ≤ H) (hOH : oddCoreIn H ≠ ⊥) {P : Subgroup G}
    (hP : IsSylowOf σ.p P σ.C) (hDP : σ.D ≤ Subgroup.normalizer (P : Set G)) (hPH : P ≤ H)
    (hW : W ∈ σ.familyW J) (hWH : W ≤ H) :
    ∃ Y : Subgroup G, Y ≤ H ∧ oddCoreIn H ≤ Y ∧ Odd (Nat.card Y) ∧
      σ.D ≤ Subgroup.normalizer (Y : Set G) ∧ W ≤ Y ∧
      ∀ U ∈ signalizers H σ.D σ.p, P ≤ U → U ≤ Y := by
  have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
  set A := oddCoreIn H with hA
  have hTD := σ.T_le_D hσ
  have hTH : σ.T ≤ H := hTD.trans hDH
  have hHA : H ≤ Subgroup.normalizer (A : Set G) := le_normalizer_oddCoreIn H
  have hDA : σ.D ≤ Subgroup.normalizer (A : Set G) := hDH.trans hHA
  have hWodd := odd_card_W hσ hJ hW
  have hUodd : ∀ U ∈ signalizers H σ.D σ.p, Odd (Nat.card U) := fun U hU =>
    Omnibus.odd_card_of_isPGroup hσ.p_prime hσ.p_ne_two hU.2.1
  have hcaseO : (∀ Z : Subgroup G, Z ≤ H → Odd (Nat.card Z) →
      σ.D ≤ Subgroup.normalizer (Z : Set G) → Z ≤ A) →
      ∃ Y : Subgroup G, Y ≤ H ∧ A ≤ Y ∧ Odd (Nat.card Y) ∧
        σ.D ≤ Subgroup.normalizer (Y : Set G) ∧ W ≤ Y ∧
        ∀ U ∈ signalizers H σ.D σ.p, P ≤ U → U ≤ Y := by
    intro hZ
    exact ⟨A, oddCoreIn_le H, le_rfl, odd_card_oddCoreIn H, hDA, hZ W hWH hWodd hW.2.1,
      fun U hU _ => hZ U hU.1 (hUodd U hU) hU.2.2.1⟩
  have hHtop : H ≠ ⊤ := by
    rintro rfl
    exact hOH (Omnibus.oddCoreIn_top_eq_bot hσ)
  have hcov : ((σ.C ⊓ σ.L : Subgroup G) : Set G) ⊆
      (H : Set G) * ((σ.C ⊓ σ.ON : Subgroup G) : Set G) :=
    (h31.covers W hW).trans (Set.mul_subset_mul_right
      (SetLike.coe_subset_coe.mpr (sup_le hWH hDH)))
  rcases hII.fusion_cases H hHtop hTH (Or.inl hDH) with hQD | hQ | hD | h2
  · exact absurd hQD (hII.not_qd_of_cover H hTH hOH hcov)
  ·
    have hU := hQS H hQ hDH hcov
    have hWP : (W : Set G) * P = P * W := (mul_comm_W_of_isSylowOf hσ hJ hW hP).symm
    have hWPodd : Odd (Nat.card (W ⊔ P : Subgroup G)) :=
      (hWodd.mul (Omnibus.odd_card_of_isPGroup hσ.p_prime hσ.p_ne_two hP.isPGroup)).of_dvd_nat
        (card_sup_dvd_of_mul_comm hWP)
    refine ⟨A ⊔ (W ⊔ P), sup_le (oddCoreIn_le H) (sup_le hWH hPH), le_sup_left, ?_, ?_,
      le_sup_left.trans le_sup_right, fun U hUs hPU => ?_⟩
    · exact odd_card_sup_of_le_normalizer_of_odd ((sup_le hWH hPH).trans hHA)
        (odd_card_oddCoreIn H) hWPodd
    · exact (le_inf hDA ((le_inf hW.2.1 hDP).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · have hUA := le_oddCoreIn_sup_of_le_sup_C hσ hTH (hU U hUs) hUs.2.1 (hTD.trans hUs.2.2.1)
        hP hPU
      exact hUA.trans (sup_le_sup_left le_sup_right A)
  ·
    by_cases hh : σ.height = 1
    ·
      have hZ := hDS hh H hDH hD
      set Y : Subgroup G := A ⊔ oddCoreIn (H ⊓ σ.N) with hY
      have hDHN : σ.D ≤ H ⊓ σ.N := le_inf hDH (σ.D_le_N hσ)
      refine ⟨Y, sup_le (oddCoreIn_le H) ((oddCoreIn_le _).trans inf_le_left), le_sup_left, ?_,
        ?_, hZ W hWH hWodd hW.2.1, fun U hUs _ => hZ U hUs.1 (hUodd U hUs) hUs.2.2.1⟩
      · exact odd_card_sup_of_le_normalizer_of_odd
          (((oddCoreIn_le _).trans inf_le_left).trans hHA) (odd_card_oddCoreIn H)
          (odd_card_oddCoreIn _)
      · exact (le_inf hDA (hDHN.trans (le_normalizer_oddCoreIn _))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
    ·
      have hSH : (σ.S : Subgroup G) ≤ H := by
        rw [← Omnibus.D_eq_S hσ hh]
        exact hDH
      exact hcaseO fun Z hZH hZodd hDZ =>
        Omnibus.le_oddCoreIn_of_isDGroup hσ hh hSH hD hZH hZodd (hTD.trans hDZ)
  ·
    exact hcaseO fun Z hZH hZodd _ => Omnibus.le_oddCoreIn_of_hasNormalPComplement h2 hZH hZodd

omit [Finite G] in
theorem mul_comm_of_eq_sup_inf_normalizer {X O U W : Subgroup G} (hUX : U ≤ X) (hWX : W ≤ X)
    (hOU : O ≤ U) (hXO : X ≤ Subgroup.normalizer (O : Set G))
    (hX : X = O ⊔ (X ⊓ Subgroup.normalizer (W : Set G))) :
    (U : Set G) * W = W * U := by
  have hNO : X ⊓ Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    inf_le_left.trans hXO
  have key : (U : Set G) * W ⊆ W * U := by
    rintro _ ⟨u, hu, w, hw, rfl⟩
    have huX : u ∈ O ⊔ (X ⊓ Subgroup.normalizer (W : Set G)) := hX ▸ hUX hu
    obtain ⟨o, ho, n, hn, rfl⟩ := (mem_sup_iff_of_le_normalizer' hNO).mp huX
    have hnU : n ∈ U := by
      have : n = o⁻¹ * (o * n) := by group
      rw [this]
      exact U.mul_mem (U.inv_mem (hOU ho)) hu
    have hw' : n * w * n⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hn.2 w).mp hw
    have ho' : (n * w * n⁻¹)⁻¹ * o * (n * w * n⁻¹) ∈ O := by
      have := (Subgroup.mem_normalizer_iff.mp (hXO (X.inv_mem (hWX hw'))) o).mp ho
      simpa [mul_assoc] using this
    refine ⟨n * w * n⁻¹, hw', (n * w * n⁻¹)⁻¹ * o * (n * w * n⁻¹) * n,
      U.mul_mem (hOU ho') hnU, ?_⟩
    show n * w * n⁻¹ * ((n * w * n⁻¹)⁻¹ * o * (n * w * n⁻¹) * n) = o * n * w
    group
  apply Set.Subset.antisymm key
  rintro _ ⟨w, hw, u, hu, rfl⟩
  obtain ⟨w', hw', u', hu', he⟩ := key ⟨u⁻¹, U.inv_mem hu, w⁻¹, W.inv_mem hw, rfl⟩
  refine ⟨u'⁻¹, U.inv_mem hu', w'⁻¹, W.inv_mem hw', ?_⟩
  have he' : w' * u' = u⁻¹ * w⁻¹ := he
  show u'⁻¹ * w'⁻¹ = w * u
  rw [← mul_inv_rev, he', mul_inv_rev, inv_inv, inv_inv]

theorem propV41 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hJ : σ.IsV21Layer J)
    (h31 : LemmaV31Input σ J) (hN' : CommutatorInput σ) (h42 : LemmaII42Input σ J)
    (h46 : LemmaII46Input σ J) (h49 : LemmaII49Input σ J)
    (h21 : ∀ r : ℕ, σ.HypIV7 r → r = σ.p) (hQF : Sec10.QGroupFourFusion G)
    (hQS : QGroupSignalizerInput σ) (hDS : DGroupSignalizerInput σ) : σ.PropV41 J := by
  intro H hDH hOH P hP hDP hPH W hW hWH V hV hPV
  have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
  obtain ⟨Y, hYH, hOY, hYodd, hDY, hWY, hYmax⟩ :=
    exists_signalizer_hull hσ hII hJ h31 hQS hDS hDH hOH hP hDP hPH hW hWH
  have hVY : V ≤ Y := hYmax V hV.1 hPV
  have hD2 : IsPGroup 2 σ.D := isPGroup_D
  have hWodd := odd_card_W hσ hJ hW
  have hWp := h31.coprime W hW
  have hsig : ∀ U : Subgroup G, U ≤ H → IsPGroup σ.p U → σ.D ≤ Subgroup.normalizer (U : Set G) →
      U ∈ signalizers H σ.D σ.p := fun U hUH hUp hDU => by
    refine ⟨hUH, hUp, hDU, ?_⟩
    rw [inf_comm]
    exact Omnibus.inf_eq_bot_of_two_odd hD2
      (Omnibus.odd_card_of_isPGroup hσ.p_prime hσ.p_ne_two hUp)
  set π : Set Nat.Primes := {d | (d : ℕ) = σ.p ∨ (d : ℕ) ∣ Nat.card W} with hπ
  have hVW : (V : Set G) * W = W * V := hV.2
  have hVWπ : ∀ d : Nat.Primes, (d : ℕ) ∣ Nat.card (V ⊔ W : Subgroup G) → d ∈ π := by
    intro d hd
    rcases (Nat.Prime.dvd_mul d.2).mp (hd.trans (card_sup_dvd_of_mul_comm hVW)) with h | h
    · left
      obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hV.1.2.1
      rw [ha] at h
      exact (Nat.prime_dvd_prime_iff_eq d.2 hσ.p_prime).mp (d.2.dvd_of_dvd_pow h)
    · exact Or.inr h
  have hDVW : σ.D ≤ Subgroup.normalizer ((V ⊔ W : Subgroup G) : Set G) :=
    (le_inf hV.1.2.2.1 hW.2.1).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  obtain ⟨X, hXY, hVWX, hDX, hXπ, hXidx⟩ :=
    exists_invariant_hall hD2 hDY hYodd (sup_le hVY hWY) hDVW π hVWπ
  have hXodd : Odd (Nat.card X) := odd_card_of_le hXY hYodd
  obtain ⟨U, hU, hVU, hDU⟩ := exists_isSylowOf_normalized_ge_of_odd hσ.p_prime hD2 hDX hXodd
    (le_sup_left.trans hVWX) hV.1.2.1 hV.1.2.2.1
  have hUY : IsSylowOf σ.p U Y := by
    rw [isSylowOf_iff] at hU ⊢
    refine ⟨hU.1.trans hXY, hU.2.1, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex U X Y hU.1 hXY]
    exact hσ.p_prime.not_dvd_mul hU.2.2 (hXidx ⟨σ.p, hσ.p_prime⟩ (Or.inl rfl))
  have hWX : W ≤ X := le_sup_right.trans hVWX
  obtain ⟨⟨-, hXW⟩, -⟩ := lemmaV45 hσ hII hJ h31 hN' h42 h46 h49 h21 hQF W hW X hDX
    (hWX.trans Subgroup.le_normalizer) (fun ℓ hℓ hℓX => hXπ ⟨ℓ, hℓ⟩ hℓX)
  have hUW : (U : Set G) * W = W * U :=
    mul_comm_of_eq_sup_inf_normalizer hU.le hWX (Omnibus.pCoreIn_le_of_isSylowOf hU)
      (DataConstruction.le_normalizer_pCoreIn σ.p X) hXW
  have hUsig : U ∈ signalizers H σ.D σ.p :=
    hsig U (hU.le.trans (hXY.trans hYH)) hU.isPGroup hDU
  have hUmax : U ∈ maximals (signalizers H σ.D σ.p) :=
    ⟨hUsig, fun U' hU' hUU' => hUY.eq_of_le hUU' (hYmax U' hU' (hPV.trans (hVU.trans hUU')))
      hU'.2.1⟩
  refine ⟨⟨U, ⟨hUsig, hUW⟩, hVU, hUmax,
    hUY.inf_of_le_normalizer hOY (hYH.trans (le_normalizer_oddCoreIn H))⟩, ?_⟩
  set Op := pCoreIn σ.p σ.N with hOp
  set K₀ : Subgroup G := σ.C ⊓ Y with hK₀
  have hWC := W_le_C hσ hJ hW
  have hWK₀ : W ≤ K₀ := le_inf hWC hWY
  have hK₀odd : Odd (Nat.card K₀) := odd_card_of_le inf_le_right hYodd
  have hDC : σ.D ≤ Subgroup.normalizer (σ.C : Set G) := fun d hd =>
    DataConstruction.conjSub_eq_self_iff.mp (conjSub_C (DataConstruction.D_le_normalizer_T hd))
  have hDK₀ : σ.D ≤ Subgroup.normalizer (K₀ : Set G) :=
    (le_inf hDC hDY).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hDOp : σ.D ≤ Subgroup.normalizer (Op : Set G) := (σ.D_le_N hσ).trans N_le_normalizer_pCore
  have hWOp : W ≤ Subgroup.normalizer (Op : Set G) := (W_le_N hσ hJ hW).trans N_le_normalizer_pCore
  have hWK₀n : W ≤ Subgroup.normalizer (K₀ : Set G) :=
    (le_inf (hWC.trans Subgroup.le_normalizer) (hWY.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  set P₀ : Subgroup G := K₀ ⊓ Op with hP₀
  have hP₀p : IsPGroup σ.p P₀ := (DataConstruction.isPGroup_pCoreIn σ.p σ.N).to_le inf_le_right
  have hWP₀ : W ≤ Subgroup.normalizer (P₀ : Set G) :=
    (le_inf hWK₀n hWOp).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hP₀W : P₀ ⊔ W = (W ⊔ Op) ⊓ K₀ := by
    apply le_antisymm
    · exact sup_le (le_inf (inf_le_right.trans le_sup_right) inf_le_left)
        (le_inf le_sup_left hWK₀)
    · intro u hu
      obtain ⟨w, hw, v, hv, rfl⟩ := (mem_sup_iff_of_le_normalizer hWOp).mp hu.1
      have hvK : v ∈ K₀ := by
        have : v = w⁻¹ * (w * v) := by group
        rw [this]
        exact K₀.mul_mem (K₀.inv_mem (hWK₀ hw)) hu.2
      rw [sup_comm]
      exact Subgroup.mul_mem_sup hw ⟨hvK, hv⟩
  have hP₀Wodd : Odd (Nat.card (P₀ ⊔ W : Subgroup G)) :=
    odd_card_of_le (sup_le (inf_le_left.trans inf_le_right) hWY) hYodd
  have hK₀N : K₀ ≤ Subgroup.normalizer ((P₀ ⊔ W : Subgroup G) : Set G) := by
    rw [hP₀W]
    exact (le_inf (inf_le_left.trans (C_le_normalizer_W_sup hJ hW)) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hK₀eq : (K₀ : Set G) =
      (P₀ : Set G) * ((K₀ ⊓ Subgroup.normalizer (W : Set G) : Subgroup G) : Set G) := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨v, hv, hvy⟩ :=
        exists_inv_mul_mem_normalizer_of_complement hP₀p hWP₀ hWp hP₀Wodd (hK₀N hy)
      exact ⟨v, hv, v⁻¹ * y, ⟨K₀.mul_mem (K₀.inv_mem hv.1) hy, hvy⟩, by group⟩
    · rintro _ ⟨v, hv, n, hn, rfl⟩
      exact K₀.mul_mem hv.1 hn.1
  have hDNW : σ.D ≤ Subgroup.normalizer
      ((K₀ ⊓ Subgroup.normalizer (W : Set G) : Subgroup G) : Set G) :=
    (le_inf hDK₀ fun d hd => Subgroup.le_normalizer (hW.2.1 hd)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hcent := centralizer_mul_of_mul_eq hK₀odd hD2 (inf_le_left : P₀ ≤ K₀) inf_le_left
    ((le_inf hDK₀ hDOp).trans Subgroup.inf_normalizer_le_normalizer_inf) hDNW hK₀eq
  have hCOp : σ.C ⊓ Op ≤ P := by
    refine le_trans ?_ (Omnibus.pCoreIn_le_of_isSylowOf hP)
    refine DataConstruction.le_pCoreIn inf_le_left ?_
      ((DataConstruction.isPGroup_pCoreIn _ _).to_le inf_le_right)
    exact (le_inf Subgroup.le_normalizer (σ.C_le_N.trans N_le_normalizer_pCore)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have key : ∀ U' ∈ signalizersPerm H σ.D W σ.p, U' ∈ maximals (signalizers H σ.D σ.p) →
      V ≤ U' → ∃ b ∈ σ.C ⊓ Subgroup.normalizer (W : Set G) ⊓
        Subgroup.centralizer (σ.D : Set G), conjSub b U' = U := by
    intro U' hU' hU'm hVU'
    have hU'Y : U' ≤ Y := hYmax U' hU'.1 (hPV.trans hVU')
    obtain ⟨S, hS, hU'S, hDS'⟩ := exists_isSylowOf_normalized_ge_of_odd hσ.p_prime hD2 hDY
      hYodd hU'Y hU'.1.2.1 hU'.1.2.2.1
    have hSU' : S = U' := hU'm.2 S (hsig S (hS.le.trans hYH) hS.isPGroup hDS') hU'S
    rw [hSU'] at hS
    obtain ⟨c, hc, hcU⟩ := exists_conj_eq_of_isSylowOf_normalized_of_odd hσ.p_prime hD2 hDY
      hYodd hS hUY hU'.1.2.2.1 hDU
    have hcC : c ∈ σ.C := Subgroup.centralizer_le (σ.T_le_D hσ) hc.2
    have hcK : c⁻¹ ∈ (K₀ ⊓ Subgroup.centralizer (σ.D : Set G) : Subgroup G) :=
      Subgroup.inv_mem _ ⟨⟨hcC, hc.1⟩, hc.2⟩
    have hcK' : c⁻¹ ∈ ((K₀ ⊓ Subgroup.centralizer (σ.D : Set G) : Subgroup G) : Set G) := hcK
    rw [hcent] at hcK'
    obtain ⟨u, hu, b, hb, hub⟩ := hcK'
    have hub' : u * b = c⁻¹ := hub
    have huU' : u⁻¹ ∈ U' :=
      U'.inv_mem (hVU' (hPV (hCOp ⟨hu.1.1.1, hu.1.2⟩)))
    refine ⟨b⁻¹, ⟨⟨σ.C.inv_mem hb.1.1.1, Subgroup.inv_mem _ hb.1.2⟩, Subgroup.inv_mem _ hb.2⟩, ?_⟩
    have hc' : c = b⁻¹ * u⁻¹ := by rw [← mul_inv_rev, hub', inv_inv]
    rw [← hcU, hc']
    show conjSub b⁻¹ U' = conjSub (b⁻¹ * u⁻¹) U'
    rw [← DataConstruction.conjSub_conjSub, DataConstruction.conjSub_eq_self_of_mem
      (Subgroup.le_normalizer huU')]
  intro U₁ hU₁ U₂ hU₂ hU₁m hU₂m hVU₁ hVU₂
  obtain ⟨b₁, hb₁, h₁⟩ := key U₁ hU₁ hU₁m hVU₁
  obtain ⟨b₂, hb₂, h₂⟩ := key U₂ hU₂ hU₂m hVU₂
  refine ⟨b₂⁻¹ * b₁, Subgroup.mul_mem _ (Subgroup.inv_mem _ hb₂) hb₁, ?_⟩
  show conjSub (b₂⁻¹ * b₁) U₁ = U₂
  rw [← DataConstruction.conjSub_conjSub, h₁, ← h₂, DataConstruction.conjSub_inv_conjSub]

end CFSG.ABGTheoremB.V4
