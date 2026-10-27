module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsM12
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Suz
public import Certificates.Certificate23310

public section

namespace CFSG.ComponentClassification.Sol76T13.R12.Pcls

open CFSG Subgroup CFSG.Blueprint CFSG.RankThree.PartTwo.Sec4.Census
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.HypOne CFSG.EvenSporadicStandard.HypOne.Suz
open CFSG.Sporadic.SuzOddCore (suzM suzInv suzEquivM fixedCount fixedCount_eq suzInv_fixed
  rep_suzInv inM_iff invT_check)

theorem three_le_pRank_of_transitive_e8 {Q : Type} [Group Q] [Finite Q] {X : Type*} [Group X]
    {φ : Q →* X} (hφ : Function.Surjective φ) (hker : φ.ker = center Q) {t : Q}
    (htZ : t ∈ center Q) (ht2 : orderOf t = 2) (hcen : center Q = zpowers t) {u : Fin 3 → X}
    (hsq : ∀ i, u i ^ 2 = 1) (hcomm : ∀ i j, Commute (u i) (u j)) {e₀ : X}
    (hne : ∀ v : Fin 3 → Fin 2, v ≠ 0 → (List.ofFn fun i => u i ^ (v i : ℕ)).prod ≠ 1)
    (htr : ∀ v : Fin 3 → Fin 2, v ≠ 0 →
      ∃ g : X, g * e₀ * g⁻¹ = (List.ofFn fun i => u i ^ (v i : ℕ)).prod) :
    3 ≤ CFSG.pRank 2 Q := by
  obtain ⟨f, hfinj, hfv⟩ := DoubleCoverLift.exists_prodHom u hsq hcomm hne
  have hE2 : ∀ e ∈ f.range, e ^ 2 = 1 := by
    rintro _ ⟨v, rfl⟩
    rw [← map_pow, DoubleCoverLift.pi_pow_two_eq_one, map_one]
  have hE8 : 8 ≤ Nat.card f.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv]
    simp [Nat.card_eq_fintype_card]
  have htr' : ∀ e ∈ f.range, e ≠ 1 → ∃ g : X, g * e₀ * g⁻¹ = e := by
    rintro _ ⟨v, rfl⟩ hv1
    have hw : (fun i => Multiplicative.toAdd (v i) : Fin 3 → Fin 2) ≠ 0 := fun h => hv1 (by
      have hv : v = 1 := funext fun i => Multiplicative.toAdd.injective (congrFun h i)
      rw [hv, map_one])
    rw [hfv]
    exact htr _ hw
  have ht2' : t ^ 2 = 1 := by rw [← ht2, pow_orderOf_eq_one]
  have hc2 : ∀ c : Q, φ c = 1 → c ^ 2 = 1 := fun c hc => by
    have hc' : c ∈ zpowers t := hcen ▸ hker ▸ hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc'
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2', one_zpow]
  refine three_le_pRank_of_lifts hφ hker (W := f.range) (by omega) (fun y y' hy hy' => ?_)
    (fun y hy => TransitiveLift.exists_sq_eq_sq hφ hker.le hE2 hE8 htr' hy) htZ ht2
  obtain ⟨c, hc, h⟩ := TransitiveLift.exists_commutator_eq_sq hφ hker.le hE2 hE8 htr' hy hy'
  rw [hc2 c hc] at h
  exact commutatorElement_eq_one_iff_mul_comm.mp h

theorem card_fixed_conj {n : ℕ} (c r : Equiv.Perm (Fin n)) :
    (Finset.univ.filter fun i => (c * r * c⁻¹) i = i).card =
      (Finset.univ.filter fun i => r i = i).card := by
  have h : ∀ σ : Equiv.Perm (Fin n),
      (Finset.univ.filter fun i => σ i = i).card = n - σ.support.card := fun σ => by
    have hs : σ.support = Finset.univ.filter fun i => ¬ σ i = i := by
      ext i
      simp [Equiv.Perm.mem_support]
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ) fun i => σ i = i
    rw [Finset.card_univ, Fintype.card_fin] at this
    rw [hs]
    omega
  rw [h, h, Equiv.Perm.card_support_conj]

theorem sporadicCoverRankInput_Suz :
    SporadicCoverRankInput .Suz := by
  intro Q _ _ hQ hZ2 ⟨e⟩
  obtain ⟨t, htZ, ht2, hcen⟩ := exists_center_eq_zpowers hZ2
  let e' : Q ⧸ center Q ≃* suzM := (e : Q ⧸ center Q ≃* NativeSporadic.Suz).trans suzEquivM
  have hφ : Function.Surjective (e'.toMonoidHom.comp (QuotientGroup.mk' (center Q))) :=
    e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker := ker_quotientMap e'
  have h := Certificates.certificate23310
  simp only [SuzE8.suzE8Check, SuzE8.e8Prods, Bool.and_eq_true, List.all_cons, List.all_nil,
    Bool.and_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hpx, hpy⟩, hpz⟩, hsx⟩, hsy⟩, hsz⟩, he8⟩, hfx, hfy, hfz, hfxy, hfxz, hfyz,
    hfxyz⟩ := h
  simp only [e8Check, Bool.and_eq_true] at he8
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hxy, hxz⟩, hyz⟩, hx2⟩, hy2⟩, hz2⟩, hxy2⟩, hxz2⟩, hyz2⟩, hxyz2⟩ := he8
  have rx := rep_tp hpx
  have ry := rep_tp hpy
  have rz := rep_tp hpz
  have hxM := mem_suzM_of_siftM rx hsx
  have hyM := mem_suzM_of_siftM ry hsy
  have hzM := mem_suzM_of_siftM rz hsz
  have order2 : ∀ {T : Table} {g : Equiv.Perm (Fin 1782)}, Rep 1782 T g →
      ordTest 1782 2 T = true → orderOf g = 2 := fun hT hT2 =>
    (ordTest_iff perm_faithful hT (by norm_num)).1 hT2
  have h1M : suzInv 1 ∈ suzM := (inM_iff (rep_suzInv (by norm_num))).1 invT_check.2.2.1
  set e₀ : suzM := ⟨suzInv 1, h1M⟩
  have key : ∀ (p : suzM) {T : Table}, Rep 1782 T (p : Equiv.Perm (Fin 1782)) →
      ordTest 1782 2 T = true → fixedCount (natArr T) = 54 →
        p ≠ 1 ∧ ∃ g : suzM, g * e₀ * g⁻¹ = p := by
    intro p T hT hT2 hfix
    have hp2 : orderOf (p : Equiv.Perm (Fin 1782)) = 2 := order2 hT hT2
    have hfix' : (Finset.univ.filter fun i => (p : Equiv.Perm (Fin 1782)) i = i).card = 54 := by
      rw [← fixedCount_eq (co2Rep_natArr_iff.2 hT), hfix]
    refine ⟨fun h1 => by rw [h1, Subgroup.coe_one, orderOf_one] at hp2; omega, ?_⟩
    obtain ⟨r, hr, c, hc, hpc⟩ := cover_suzM _ p.2 hp2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exfalso
      have h0 := suzInv_fixed (i := 0) (by norm_num)
      rw [← card_fixed_conj c, ← hpc, hfix'] at h0
      exact absurd h0 (by decide)
    · exact ⟨⟨c, hc⟩, Subtype.ext (by simpa using hpc.symm)⟩
  set u : Fin 3 → suzM := ![⟨_, hxM⟩, ⟨_, hyM⟩, ⟨_, hzM⟩] with hu
  have hcxy : (tp 1782 SuzE8.xTab) * tp 1782 SuzE8.yTab = tp 1782 SuzE8.yTab * tp 1782 SuzE8.xTab :=
    (commT_iff rx ry).1 hxy
  have hcxz : (tp 1782 SuzE8.xTab) * tp 1782 SuzE8.zTab = tp 1782 SuzE8.zTab * tp 1782 SuzE8.xTab :=
    (commT_iff rx rz).1 hxz
  have hcyz : (tp 1782 SuzE8.yTab) * tp 1782 SuzE8.zTab = tp 1782 SuzE8.zTab * tp 1782 SuzE8.yTab :=
    (commT_iff ry rz).1 hyz
  have hsq : ∀ i, u i ^ 2 = 1 := by
    intro i
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← orderOf_dvd_iff_pow_eq_one]
    fin_cases i
    · exact (order2 rx hx2).dvd
    · exact (order2 ry hy2).dvd
    · exact (order2 rz hz2).dvd
  have h01 : Commute (u 0) (u 1) := Subtype.ext hcxy
  have h02 : Commute (u 0) (u 2) := Subtype.ext hcxz
  have h12 : Commute (u 1) (u 2) := Subtype.ext hcyz
  have hcomm : ∀ i j, Commute (u i) (u j) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact Commute.refl _
    · exact h01
    · exact h02
    · exact h01.symm
    · exact Commute.refl _
    · exact h12
    · exact h02.symm
    · exact h12.symm
    · exact Commute.refl _
  have hprod : ∀ v : Fin 3 → Fin 2, v ≠ 0 →
      (List.ofFn fun i => u i ^ (v i : ℕ)).prod ≠ 1 ∧
        ∃ g : suzM, g * e₀ * g⁻¹ = (List.ofFn fun i => u i ^ (v i : ℕ)).prod := by
    intro v hv
    obtain ⟨a, b, c, rfl⟩ : ∃ a b c : Fin 2, v = ![a, b, c] :=
      ⟨v 0, v 1, v 2, by ext i; fin_cases i <;> rfl⟩
    fin_cases a <;> fin_cases b <;> fin_cases c
    · exact absurd (by ext i; fin_cases i <;> rfl) hv
    all_goals
      simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_succ, pow_zero, pow_one, mul_one, one_mul, hu]
    · exact key _ rz hz2 hfz
    · exact key _ ry hy2 hfy
    · exact key _ (Rep.compT ry rz) hyz2 hfyz
    · exact key _ rx hx2 hfx
    · exact key _ (Rep.compT rx rz) hxz2 hfxz
    · exact key _ (Rep.compT rx ry) hxy2 hfxy
    · rw [← mul_assoc]
      exact key (⟨_, hxM⟩ * ⟨_, hyM⟩ * ⟨_, hzM⟩) (Rep.compT (Rep.compT rx ry) rz) hxyz2 hfxyz
  exact three_le_pRank_of_transitive_e8 hφ hker htZ ht2 hcen hsq hcomm
    (fun v hv => (hprod v hv).1) (fun v hv => (hprod v hv).2)

end CFSG.ComponentClassification.Sol76T13.R12.Pcls
