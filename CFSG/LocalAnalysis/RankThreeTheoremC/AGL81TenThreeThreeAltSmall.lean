module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAltLarge
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAltSmallPerm
public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.SmallDegreeSix
public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.SmallDegreeDegrees
import CFSG.Milestones.ASVolI.A3OddFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

open CFSG.Open CFSG.AGLEmbedding Subgroup Equiv Equiv.Perm
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (DegreeSix.inner_conjugation_injective)
open CFSG.HardMathSupport.RichardWeiss.Coordinator (ConjSpec centerQuotientAut
  mem_centralizer_of_centerQuotientAut_eq_one card_alternatingGroup_fin)

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem exists_centralizing_lift {P : Subgroup Γ} {β : Γ}
    (hβP : β ∈ normalizer (P : Set Γ)) (hodd : Odd (orderOf β)) {w : Γ} (hw : w ∈ P)
    (hc : β * w * β⁻¹ * w⁻¹ ∈ pCoreOf 2 P) :
    ∃ h : ↥P, QuotientGroup.mk' (CFSG.pCore 2 ↥P) h = QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩ ∧
      β * h = h * β := by
  set O := pCoreOf 2 P with hO
  have hPO : P ≤ normalizer (O : Set Γ) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hβO : β ∈ normalizer (O : Set Γ) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P hβP
  have hOp : IsPGroup 2 O := (CFSG.pCore_isPGroup (p := 2) (G := ↥P)).map P.subtype
  have hsolv : Group.IsSolvable O := by
    haveI := hOp.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card (zpowers β)) (Nat.card O) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (G := O)).1 hOp
    rw [Nat.card_zpowers, hk]
    refine Nat.Coprime.pow_right k (Nat.coprime_comm.mp ?_)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr fun ⟨c, hc⟩ => by
      obtain ⟨d, hd⟩ := hodd
      omega
  have hpow : ∀ n : ℕ, β ^ n * w * (β ^ n)⁻¹ * w⁻¹ ∈ O := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : β * (β ^ n * w * (β ^ n)⁻¹ * w⁻¹) * β⁻¹ ∈ O := (mem_normalizer_iff.1 hβO _).1 ih
      have h2 := O.mul_mem h1 hc
      have he : β * (β ^ n * w * (β ^ n)⁻¹ * w⁻¹) * β⁻¹ * (β * w * β⁻¹ * w⁻¹) =
          β ^ (n + 1) * w * (β ^ (n + 1))⁻¹ * w⁻¹ := by group
      rwa [he] at h2
  obtain ⟨m, hm, hcm⟩ := CFSG.ABGTheoremB.V4.exists_mul_mem_centralizer_of_coprime
    (zpowers_le.mpr hβO) hsolv hcop (g := w) fun a ha => by
      obtain ⟨n, rfl⟩ := mem_powers_iff_mem_zpowers.mpr ha
      have h1 := hpow n
      have h2 : w⁻¹ * (β ^ n * w * (β ^ n)⁻¹ * w⁻¹) * w ∈ O := by
        have := (mem_normalizer_iff.1 (hPO (P.inv_mem hw)) _).1 h1
        simpa using this
      have he : w⁻¹ * (β ^ n * w * (β ^ n)⁻¹ * w⁻¹) * w = w⁻¹ * (β ^ n * w * (β ^ n)⁻¹) := by
        group
      rwa [he] at h2
  obtain ⟨m', hm', rfl⟩ := hm
  refine ⟨⟨w, hw⟩ * m', ?_, ?_⟩
  · rw [map_mul, show QuotientGroup.mk' (CFSG.pCore 2 ↥P) m' = 1 from
      (QuotientGroup.eq_one_iff _).2 hm', mul_one]
  · have := Subgroup.mem_centralizer_iff.1 hcm β (mem_zpowers β)
    simpa using this

theorem centralizes_alt_eight {Lb P : Subgroup Γ} (hPL : P ≤ Lb)
    (e : ↥Lb ≃* ↥(alternatingGroup (Fin 8))) {r s : ℕ} (hs : 6 ≤ s)
    (φ : (↥P ⧸ CFSG.pCore 2 ↥P) ≃* (Perm (Fin r) × Perm (Fin s))) {β : Γ}
    (hβL : β ∈ normalizer (Lb : Set Γ)) (hβP : β ∈ normalizer (P : Set Γ))
    (hodd : Odd (orderOf β))
    (hW : ∀ w (hw : w ∈ P), QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩ ∈
      wSup (↥P ⧸ CFSG.pCore 2 ↥P) → β * w * β⁻¹ * w⁻¹ ∈ pCoreOf 2 P) :
    ∀ y ∈ Lb, β * y = y * β := by
  obtain ⟨σ, hσ, hσA, hσo⟩ := exists_odd_conjSpec (by simp) (by simp) e hβL hodd
  by_cases hσ1 : σ = 1
  · intro y hy
    have hcm : β * y * β⁻¹ ∈ Lb := (mem_normalizer_iff.1 hβL y).1 hy
    have h1 := hσ ⟨y, hy⟩ ⟨_, hcm⟩ rfl
    rw [hσ1, one_mul, inv_one, mul_one] at h1
    have h2 := congrArg Subtype.val (e.injective (Subtype.ext h1))
    calc β * y = (β * y * β⁻¹) * β := by group
      _ = y * β := by rw [show β * y * β⁻¹ = y from h2]
  exfalso
  set D : Subgroup Γ := P ⊓ centralizer {β} with hD
  have hDP : D ≤ P := inf_le_left
  let f : ↥D →* Perm (Fin s) := (MonoidHom.snd _ _).comp
    (φ.toMonoidHom.comp ((QuotientGroup.mk' (CFSG.pCore 2 ↥P)).comp (inclusion hDP)))
  have hA6 : alternatingGroup (Fin s) ≤ f.range := by
    intro a ha
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (φ.symm (1, a))
    have hmk : QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨(w : Γ), w.2⟩ ∈
        wSup (↥P ⧸ CFSG.pCore 2 ↥P) := by
      rw [← map_wSup_eq φ.symm]
      refine ⟨(1, a), bot_prod_alternatingGroup_le_wSup (by omega) ⟨one_mem _, ha⟩, ?_⟩
      exact hw.symm
    obtain ⟨h, hh, hβh⟩ := exists_centralizing_lift hβP hodd w.2 (hW w w.2 hmk)
    refine ⟨⟨h, h.2, mem_centralizer_singleton_iff.2 hβh.symm⟩, ?_⟩
    show (φ (QuotientGroup.mk' (CFSG.pCore 2 ↥P) h)).2 = a
    rw [hh]
    show (φ (QuotientGroup.mk w)).2 = a
    rw [hw, MulEquiv.apply_symm_apply]
  have h8f : 8 ∣ Nat.card f.range := by
    refine Dvd.dvd.trans ?_ (Subgroup.card_dvd_of_le hA6)
    rw [card_alternatingGroup_fin (by omega)]
    obtain ⟨k, hk⟩ := Nat.factorial_dvd_factorial hs
    rw [hk, show Nat.factorial 6 = 2 * 360 by decide, mul_assoc,
      Nat.mul_div_cancel_left _ (by norm_num)]
    exact Dvd.dvd.mul_right (by norm_num) _
  let g : ↥D →* Perm (Fin 8) := (alternatingGroup (Fin 8)).subtype.comp
    (e.toMonoidHom.comp (inclusion (hDP.trans hPL)))
  have hg : Function.Injective g :=
    (Subtype.val_injective.comp e.injective).comp (inclusion_injective _)
  have hgr : g.range ≤ centralizer {σ} ⊓ alternatingGroup (Fin 8) := by
    rintro _ ⟨d, rfl⟩
    refine ⟨?_, (e (inclusion (hDP.trans hPL) d)).2⟩
    have hdβ : β * (d : Γ) * β⁻¹ = d := by
      have := mem_centralizer_singleton_iff.1 d.2.2
      rw [← this]
      group
    have h1 := hσ (inclusion (hDP.trans hPL) d) (inclusion (hDP.trans hPL) d) hdβ.symm
    show g d ∈ centralizer {σ}
    rw [mem_centralizer_singleton_iff]
    show (e _ : Perm (Fin 8)) * σ = σ * (e _ : Perm (Fin 8))
    conv_lhs => rw [h1]
    group
  have h8 : 8 ∣ Nat.card ↥(centralizer {σ} ⊓ alternatingGroup (Fin 8)) := by
    refine h8f.trans ((Subgroup.card_range_dvd f).trans ?_)
    rw [Nat.card_congr (MonoidHom.ofInjective hg).toEquiv]
    exact Subgroup.card_dvd_of_le hgr
  exact not_eight_dvd_card_centralizer_alt_eight hσo hσ1 h8

theorem centralizes_alt_six {Lb P : Subgroup Γ} (hLb : commutator ↥Lb = ⊤)
    (eL : ↥Lb ⧸ Subgroup.center ↥Lb ≃* alternatingGroup (Fin 6)) (hPL : P ≤ Lb)
    (eP : ↥P ⧸ CFSG.pCore 2 ↥P ≃* Perm (Fin 3)) {β : Γ}
    (hβL : β ∈ normalizer (Lb : Set Γ)) (hβP : β ∈ normalizer (P : Set Γ))
    (hodd : Odd (orderOf β))
    (hW : ∀ w (hw : w ∈ P), QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩ ∈
      wSup (↥P ⧸ CFSG.pCore 2 ↥P) → β * w * β⁻¹ * w⁻¹ ∈ pCoreOf 2 P) :
    ∀ y ∈ Lb, β * y = y * β := by
  classical
  set τ : Perm (Fin 3) := swap 0 1 with hτ
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (eP.symm τ)
  have hWtop : (⊤ : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)) ≤ wSup (↥P ⧸ CFSG.pCore 2 ↥P) :=
    le_wSup_of_normal_symThree inferInstance (Subgroup.topEquiv.trans eP)
  obtain ⟨h, hh, hβh⟩ := exists_centralizing_lift hβP hodd w.2 (hW w w.2 (hWtop (mem_top _)))
  have hhτ : eP (QuotientGroup.mk h) = τ := by
    show eP (QuotientGroup.mk' (CFSG.pCore 2 ↥P) h) = τ
    rw [hh]
    show eP (QuotientGroup.mk w) = τ
    rw [hw, MulEquiv.apply_symm_apply]
  set ψ := centerQuotientAut ↥Lb (Lb.normalizerMonoidHom ⟨β, hβL⟩) with hψ
  set α' := MulAut.congr eL ψ with hα'
  have hα'odd : Odd (orderOf α') := by
    rw [hα', MulEquiv.orderOf_eq]
    refine hodd.of_dvd_nat ((orderOf_map_dvd _ _).trans ((orderOf_map_dvd _ _).trans ?_))
    rw [Subgroup.orderOf_mk]
  obtain ⟨g, hg⟩ := CFSG.ASVolI.burnsideA315x_alt6_odd_inner hα'odd
  by_cases hg1 : g = 1
  · have hψ1 : ψ = 1 := by
      apply (MulAut.congr eL).injective
      rw [map_one, ← hα', hg, hg1, map_one]
    have hc := mem_centralizer_of_centerQuotientAut_eq_one hLb hβL hψ1
    intro y hy
    exact (Subgroup.mem_centralizer_iff.1 hc y hy).symm
  exfalso
  set ĥ : ↥Lb ⧸ Subgroup.center ↥Lb := QuotientGroup.mk ⟨h, hPL h.2⟩ with hĥ
  have hψĥ : ψ ĥ = ĥ := by
    show (QuotientGroup.mk ((Lb.normalizerMonoidHom ⟨β, hβL⟩) ⟨h, hPL h.2⟩) :
      ↥Lb ⧸ Subgroup.center ↥Lb) = _
    congr 1
    apply Subtype.ext
    simp [hβh]
  have hcomm : g * eL ĥ = eL ĥ * g := by
    have h1 : α' (eL ĥ) = eL ĥ := by
      rw [hα']
      simp [MulAut.congr_apply, hψĥ]
    rw [hg] at h1
    simpa [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] using h1
  have hgo : Odd (orderOf (g : Perm (Fin 6))) := by
    rw [Subgroup.orderOf_coe,
      ← orderOf_injective (MulAut.conj) DegreeSix.inner_conjugation_injective, ← hg]
    exact hα'odd
  have hg1' : (g : Perm (Fin 6)) ≠ 1 := fun h => hg1 (Subtype.ext h)
  have hmem : ((eL ĥ : alternatingGroup (Fin 6)) : Perm (Fin 6)) ∈
      centralizer {(g : Perm (Fin 6))} ⊓ alternatingGroup (Fin 6) := by
    refine ⟨?_, (eL ĥ).2⟩
    show _ ∈ centralizer {(g : Perm (Fin 6))}
    rw [mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val hcomm).symm
  have hk : Odd (orderOf (eL ĥ)) := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_mk _ hmem]
    exact (odd_card_centralizer_alt_six hgo hg1').of_dvd_nat (orderOf_dvd_natCard _)
  set k := orderOf (eL ĥ) with hkdef
  have hĥk : ĥ ^ k = 1 := by
    apply eL.injective
    rw [map_pow, pow_orderOf_eq_one, map_one]
  have hcen : (⟨((h ^ k : ↥P) : Γ), hPL (h ^ k).2⟩ : ↥Lb) ∈ Subgroup.center ↥Lb := by
    rw [← QuotientGroup.eq_one_iff, ← hĥk, hĥ, ← QuotientGroup.mk_pow]
    rfl
  have hcomm2 : ∀ y : ↥P, y * h ^ k = h ^ k * y := by
    intro y
    have h1 := congrArg (fun z : ↥Lb => (z : Γ)) (Subgroup.mem_center_iff.1 hcen ⟨y, hPL y.2⟩)
    exact Subtype.ext h1
  have hτk : τ ^ k = τ := by
    obtain ⟨j, hj⟩ := hk
    rw [hj, pow_succ, pow_mul, sq, hτ, swap_mul_self, one_pow, one_mul]
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (eP.symm (swap 1 2))
  have h3 := congrArg (fun z => eP (QuotientGroup.mk z)) (hcomm2 y)
  simp only [QuotientGroup.mk_mul, map_mul, QuotientGroup.mk_pow, map_pow, hhτ, hτk, hy,
    MulEquiv.apply_symm_apply] at h3
  revert h3
  rw [hτ]
  decide

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
