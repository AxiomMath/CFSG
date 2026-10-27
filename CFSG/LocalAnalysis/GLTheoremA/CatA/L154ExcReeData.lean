module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcReeInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification
open CFSG.Assembly (LargeEvenInduces LargeEvenMarking)
open CFSG.LieType.Ree

theorem l154_exists_reeF4 {S : Type} [Group S] (h : catalogIs S l154ExcRee) :
    ∃ (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid),
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | reeF4 m => exact ⟨m, hv, ⟨e⟩⟩
    | _ => exact hi.elim

theorem l154_indAut_commute {p : ℕ} {Γ : Type} [Group Γ] {L : Subgroup Γ} {x y : Γ}
    (hx : x ∈ Subgroup.normalizer (L : Set Γ)) (hy : y ∈ Subgroup.normalizer (L : Set Γ))
    (hxy : x * y = y * x) :
    MI.indAut p L x hx * MI.indAut p L y hy = MI.indAut p L y hy * MI.indAut p L x hx := by
  unfold MI.indAut
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (((Commute.inv_inv_iff).2 hxy).eq)

theorem l154_fix_of_commute_conj {Γ : Type} [Group Γ] (hZ : Subgroup.center Γ = ⊥) (s : Γ)
    (φ : MulAut Γ) (h : φ * MulAut.conj s = MulAut.conj s * φ) : φ s = s := by
  have h1 : ∀ g : Γ, φ s * g * (φ s)⁻¹ = s * g * s⁻¹ := by
    intro g
    have := congrArg (fun f : MulAut Γ => f (φ.symm g)) h
    simpa [MulAut.conj_apply] using this
  have h2 : s⁻¹ * φ s ∈ Subgroup.center Γ := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := h1 g
    calc g * (s⁻¹ * φ s) = s⁻¹ * (s * g * s⁻¹) * φ s := by group
      _ = s⁻¹ * (φ s * g * (φ s)⁻¹) * φ s := by rw [this]
      _ = s⁻¹ * φ s * g := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at h2
  exact h2.symm

theorem l154_inner_of_congr_conj {P Γ : Type*} [Group P] [Group Γ] (θ : P ≃* Γ) {α : MulAut P}
    {g : Γ} (hg : MulAut.congr θ α = MulAut.conj g) : α ∈ OuterAutomorphisms.inner P := by
  refine ⟨θ.symm g, ?_⟩
  have e1 : MulAut.congr θ.symm (MulAut.conj g) = MulAut.conj (θ.symm g) :=
    OuterAutomorphisms.congr_conj θ.symm g
  have e3 : MulAut.congr θ.symm (MulAut.congr θ α) = α := by
    ext z
    simp [MulAut.congr_apply]
  rw [← e1, ← hg, e3]

section Model


theorem l154_ree_gammaModel {S : Type} [Group S] (h : catalogIs S l154ExcRee) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.F4.prime),
      1 ≤ a ∧ Nat.card K = 2 ^ (2 * a + 1) ∧ Nonempty (S ≃* ReeTag.F4.reeGamma K a) := by
  obtain ⟨m, hv, ⟨e0⟩⟩ := l154_exists_reeF4 h
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index m hv e0
  obtain ⟨-, a, ha, -, K, i1, i2, i3, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hR
  exact ⟨a, K, i1, i2, i3, ha, hK, ⟨e⟩⟩

end Model

section Marking


theorem l154_ree_marking {p : ℕ} {Ω : Type} [Group Ω] {S : Subgroup Ω}
    (hqP : CFSG.Open.IsQuasisimple (PQuot p S)) (hQ : catalogIs (PSimple p S) l154ExcRee) :
    LargeEvenMarking (PQuot p S) fun lab _ _ _ _ _ => ¬ L154OutdiagCfg p lab := by
  obtain ⟨m, hv, ⟨e0⟩⟩ := l154_exists_reeF4 hQ
  have hLie : CFSG.Blueprint.LieModel (PQuot p S ⧸ Subgroup.center (PQuot p S)) .twistedF4 0 2
      (2 * m + 1) :=
    (CFSG.Blueprint.LieModel.reeTits_iff (by decide)).2
      ⟨rfl, CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index m hv e0⟩
  exact CFSG.StandardType.Canonical.largeEvenMarking_mono
    (fun lab _ _ _ _ _ h => l154_notCfg_of_markTag h.1 (Or.inl rfl))
    (CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hqP.1 hLie)

end Marking

section Setup


theorem l154_innDiag_of_inner {p : ℕ} {Γ : Type} [Group Γ] [Finite Γ] {L : Subgroup Γ} {g : Γ}
    (hq : CFSG.Open.IsQuasisimple (PQuot p L)) (hchev : IsChevSimple 2 (PSimple p L))
    (hg : g ∈ Subgroup.normalizer (L : Set Γ)) (hin : InducesInnerMod p L g) :
    InnDiagOn p (Subgroup.zpowers g) L := by
  refine ⟨Subgroup.zpowers_le.2 hg, ?_⟩
  have h0 := CFSG.StandardType.ChevTwo.ys08_holds (PQuot p L) hq hchev
  have h1 := MI.canon_marking_and_labelAll_simple (P' := MI.RawInnBody 3)
    (fun lab hlab => MI.canonRawInn' Nat.prime_three (by norm_num) hlab) h0
  refine CFSG.StandardType.Canonical.largeEvenMarking_mono ?_ h1
  rintro lab R _ I F θ ⟨-, -, -, hinn, -⟩ a ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have hak : g ^ k ∈ Subgroup.normalizer (L : Set Γ) := Subgroup.zpow_mem _ hg k
  have hmem : MI.indAut p L (g ^ k) hak ∈ OuterAutomorphisms.inner (PSimple p L) := by
    have e : MI.indAut p L (g ^ k) hak = (MI.indAut p L g hg) ^ k := by
      unfold MI.indAut
      rw [← map_zpow]
      congr 1
      exact Subtype.ext (by simp [zpow_neg])
    rw [e]
    exact Subgroup.zpow_mem _ ((MI.indAut_mem_inner_iff_any hq hg).2 hin) k
  obtain ⟨s, hs⟩ := hmem
  refine ⟨MulAut.congr θ (MI.indAut p L (g ^ k) hak), ?_, (MI.induces_indRel_iff hak θ).2 rfl⟩
  rw [← hs, OuterAutomorphisms.congr_conj]
  exact hinn _

theorem l154_ree_setup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} {x y : Ω} (hSn : S.Normal) (hqS : CFSG.Open.IsQuasisimple ↥S)
    (hSp : GLAPPrimeCore p ↥S = ⊥) (hc : IsChevSimple 2 (PSimple p S))
    (hQ : catalogIs (PSimple p S) l154ExcRee) (hxp : x ^ p = 1) (hyp : y ^ p = 1)
    (hxy : x * y = y * x) (hInn : InnDiagOn p (Subgroup.zpowers x) S) (hF : FieldOn p y S)
    (hcm : ¬ CentMod p S x) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.F4.prime)
      (θ : PSimple p S ≃* ReeTag.F4.reeGamma K a) (s : ReeTag.F4.reeGamma K a)
      (φ : MulAut (ReeTag.F4.reeGamma K a)),
      1 ≤ a ∧ Nat.card K = 2 ^ (2 * a + 1) ∧ orderOf s = p ∧ φ ^ p = 1 ∧
      (∀ g, φ ≠ MulAut.conj g) ∧ φ s = s ∧
      LargeEvenInduces θ (indRel p S x) (MulAut.conj s) ∧ LargeEvenInduces θ (indRel p S y) φ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hxN := l154_mem_normalizer_of_normal hSn x
  have hyN := l154_mem_normalizer_of_normal hSn y
  obtain ⟨a, K, _, _, _, ha, hK, ⟨θ⟩⟩ := l154_ree_gammaModel hQ
  have hZ : Subgroup.center (ReeTag.F4.reeGamma K a) = ⊥ :=
    ReeTag.large_Ree_fixed_group_center_trivial a K hK
  let eS : PQuot p S ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hSp).trans QuotientGroup.quotientBot
  have hqP : CFSG.Open.IsQuasisimple (PQuot p S) := hqS.of_mulEquiv eS
  obtain ⟨t, ht⟩ := l154_inner_of_innDiagOn_nonCfg hp hp2 hxN hxp hInn (l154_ree_marking hqP hQ)
  have hconj : MulAut.congr θ (MI.indAut p S x hxN) = MulAut.conj (θ t) := by
    rw [← ht]
    exact OuterAutomorphisms.congr_conj θ t
  have hindx : LargeEvenInduces θ (indRel p S x) (MulAut.conj (θ t)) :=
    (MI.induces_indRel_iff hxN θ).2 hconj.symm
  have hβp : MulAut.conj (θ t) ^ p = 1 := by
    rw [← hconj, ← map_pow, l154_indAut_pow_eq_one hxN hxp, map_one]
  have hβ1 : MulAut.conj (θ t) ≠ 1 := by
    intro h1
    rw [h1] at hindx
    exact hcm (l154_centMod_of_induces_one hqS.1 hxN θ hindx)
  obtain ⟨s, hsc, hsp, hs1⟩ :=
    CFSG.HardMathSupport.Dickson.SuzukiReeB.exists_eq_conj_of_mem_range hZ ⟨θ t, rfl⟩ hβp hβ1
  have hord : orderOf s = p := orderOf_eq_prime hsp hs1
  have hindx' : LargeEvenInduces θ (indRel p S x) (MulAut.conj s) := hsc ▸ hindx
  obtain ⟨φ, hφdef⟩ : ∃ φ : MulAut (ReeTag.F4.reeGamma K a),
      φ = MulAut.congr θ (MI.indAut p S y hyN) := ⟨_, rfl⟩
  have hindy : LargeEvenInduces θ (indRel p S y) φ := (MI.induces_indRel_iff hyN θ).2 hφdef
  have hφp : φ ^ p = 1 := by
    rw [hφdef, ← map_pow, l154_indAut_pow_eq_one hyN hyp, map_one]
  have hφout : ∀ g, φ ≠ MulAut.conj g := by
    intro g hg
    have hin : MI.indAut p S y hyN ∈ OuterAutomorphisms.inner (PSimple p S) :=
      l154_inner_of_congr_conj θ (hφdef ▸ hg)
    exact (MI.field_nonInnDiag_holds hp hp2 hF).2
      (l154_innDiag_of_inner hqP hc hyN ((MI.indAut_mem_inner_iff_any hqP hyN).1 hin))
  have hcomm : φ * MulAut.conj s = MulAut.conj s * φ := by
    have hcx : MulAut.conj s = MulAut.congr θ (MI.indAut p S x hxN) := by
      rw [← hsc, hconj]
    rw [hcx, hφdef, ← map_mul, ← map_mul, l154_indAut_commute hyN hxN hxy.symm]
  exact ⟨a, K, inferInstance, inferInstance, inferInstance, θ, s, φ, ha, hK, hord, hφp, hφout,
    l154_fix_of_commute_conj hZ s φ hcomm, hindx', hindy⟩

end Setup

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
