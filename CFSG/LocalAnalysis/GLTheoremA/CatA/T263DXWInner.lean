module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GVac
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcReeData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DXW

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ}

section Inner


theorem inducesInnerMod_of_ree (hp : p.Prime) (hp2 : p ≠ 2) {S : Subgroup Ω} (hSn : S.Normal)
    (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hQ : catalogIs (↥S ⧸ Subgroup.center ↥S) t263GRee) {b : Ω} (hbp : b ^ p = 1)
    (hInn : InnDiagOn p (Subgroup.zpowers b) S) : InducesInnerMod p S b := by
  have hcomp : GLAPComponent p S S := glaPComponent_self_p hSq hSp
  have hqP : CFSG.Open.IsQuasisimple (PQuot p S) := MI.isQuasisimple_pQuot_any hcomp
  have hQ' : catalogIs (PSimple p S) K155X.l154ExcRee := by
    obtain ⟨i, hi, ⟨e⟩⟩ := hQ
    exact ⟨i, hi, ⟨(pSimpleEquiv hSp).trans e⟩⟩
  have hbN : b ∈ Subgroup.normalizer (S : Set Ω) := t263_normalizer_of_normal hSn
  have hM := K155X.l154_ree_marking hqP hQ'
  have hinn := K155X.l154_inner_of_innDiagOn_nonCfg hp hp2 hbN hbp hInn hM
  exact (MI.indAut_mem_inner_iff_any hqP hbN).1 hinn

end Inner

private theorem actionHom_eq_one_iff_of_core (hp : p.Prime) {S B : Subgroup Ω}
    (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥) (b : ↥B) :
    actionHom S B (fun g _ => t263_normalizer_of_normal hSn) p b = 1 ↔
      (b : Ω) ∈ Subgroup.centralizer (S : Set Ω) := by
  have hcomp : GLAPComponent p S S := glaPComponent_self_p hSq hSp
  have hbN : (b : Ω) ∈ Subgroup.normalizer (S : Set Ω) := t263_normalizer_of_normal hSn
  have := chevAut_eq_one_iff hp hcomp hbN
  rw [← centMod_iff_centralizer hSp hbN]
  exact this

private theorem card_actionHom_of_core (hp : p.Prime) {S B : Subgroup Ω}
    (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hBK : B ≤ Subgroup.normalizer (S : Set Ω)) :
    Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) * Nat.card ↥(actionHom S B hBK p).range =
      Nat.card B := by
  set ψ := actionHom S B hBK p with hψ
  have hmap : ψ.ker.map B.subtype = B ⊓ Subgroup.centralizer (S : Set Ω) := by
    ext g
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, (actionHom_eq_one_iff_of_core hp hSn hSq hSp x).1 hx⟩
    · rintro ⟨hgB, hgC⟩
      exact ⟨⟨g, hgB⟩, (actionHom_eq_one_iff_of_core hp hSn hSq hSp ⟨g, hgB⟩).2 hgC, rfl⟩
  have hker : Nat.card ψ.ker = Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) := by
    rw [← hmap, Subgroup.card_map_of_injective B.subtype_injective]
  rw [← hker]
  exact Subgroup.card_ker_mul_card_range ψ

private theorem actionHom_range_le_inner_of_core (hp : p.Prime) {S B₀ : Subgroup Ω}
    (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hin : ∀ b ∈ B₀, InducesInnerMod p S b) :
    (actionHom S B₀ (fun g _ => t263_normalizer_of_normal hSn) p).range ≤ inner (PSimple p S) := by
  rintro _ ⟨b, rfl⟩
  have hqP : CFSG.Open.IsQuasisimple (PQuot p S) :=
    MI.isQuasisimple_pQuot_any (glaPComponent_self_p hSq hSp)
  have hbN' : (b : Ω)⁻¹ ∈ Subgroup.normalizer (S : Set Ω) :=
    Subgroup.inv_mem _ (t263_normalizer_of_normal hSn)
  have h1 : MI.indAut p S (b : Ω)⁻¹ hbN' ∈ inner (PSimple p S) :=
    (MI.indAut_mem_inner_iff_any hqP hbN').2 (hin (b : Ω)⁻¹ (B₀.inv_mem b.2))
  rw [actionHom_apply]
  simpa only [MI.indAut, inv_inv] using h1

private theorem isElemAbelian_range_of_monoidHom {p : ℕ} {B : Subgroup Ω} {S' : Type} [Group S']
    (hB : IsElemAbelian p B) (θ : ↥B →* MulAut S') : IsElemAbelian p θ.range := by
  have hexp : ∀ α ∈ θ.range, α ^ p = 1 := by
    rintro _ ⟨v, rfl⟩
    rw [← map_pow]
    have : v ^ p = 1 := Subtype.ext (by simpa using hB.2 v v.2)
    rw [this, map_one]
  have hcomm : ∀ α ∈ θ.range, ∀ β ∈ θ.range, α * β = β * α := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have hxy : x * y = y * x := Subtype.ext (isElemAbelian_commute hB x.2 y.2)
    rw [← map_mul, ← map_mul, hxy]
  exact ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, hexp⟩

private theorem isElemAbelian_comap_conj_of_range {S' : Type} [Group S'] {B : Type} [Group B]
    {p : ℕ} (hZ : Subgroup.center S' = ⊥) (θ : B →* MulAut S')
    (hexp : ∀ α ∈ θ.range, α ^ p = 1)
    (hcomm : ∀ α ∈ θ.range, ∀ β ∈ θ.range, α * β = β * α) :
    IsElemAbelian p (θ.range.comap (MulAut.conj : S' →* MulAut S')) := by
  have hcjinj : Function.Injective (MulAut.conj : S' →* MulAut S') :=
    conj_injective_of_center_eq_bot hZ
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    apply hcjinj
    change MulAut.conj ((a : S') * b) = MulAut.conj ((b : S') * a)
    rw [map_mul, map_mul]
    exact hcomm _ a.2 _ b.2
  · apply hcjinj
    rw [map_pow, map_one]
    exact hexp _ hx

private theorem card_comap_conj_of_range_le_inner {S' : Type} [Group S']
    (hZ : Subgroup.center S' = ⊥) {B : Type} [Group B] (θ : B →* MulAut S')
    (hθ : θ.range ≤ inner S') :
    Nat.card ↥(θ.range.comap (MulAut.conj : S' →* MulAut S')) = Nat.card θ.range := by
  have hcjinj : Function.Injective (MulAut.conj : S' →* MulAut S') :=
    conj_injective_of_center_eq_bot hZ
  have h : Nat.card ↥(θ.range.comap (MulAut.conj : S' →* MulAut S')) =
      Nat.card ↥(θ.range ⊓ inner S') := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun s : ↥(θ.range.comap (MulAut.conj : S' →* MulAut S')) =>
        (⟨MulAut.conj (s : S'), s.2, ⟨s, rfl⟩⟩ : ↥(θ.range ⊓ inner S')))
      ⟨fun s t hst => Subtype.ext (hcjinj (congrArg Subtype.val hst)), fun α => ?_⟩)
    obtain ⟨s, hs⟩ := α.2.2
    exact ⟨⟨s, by rw [Subgroup.mem_comap, hs]; exact α.2.1⟩, Subtype.ext hs⟩
  rw [h, inf_eq_left.2 hθ]

private theorem comap_range_conj_le_normalizer_map {S B₀ T : Subgroup Ω} {p : ℕ}
    (hBK : B₀ ≤ Subgroup.normalizer (S : Set Ω)) (hBT : B₀ ≤ Subgroup.normalizer (T : Set Ω))
    {S' : Type} [Group S'] (eS : PSimple p S ≃* S')
    (ψ : ↥B₀ →* MulAut (PSimple p S))
    (hψ : ∀ b : ↥B₀, ψ b = chevAut p S ⟨(b : Ω), hBK b.2⟩) :
    (((MulAut.congr eS).toMonoidHom.comp ψ).range.comap (MulAut.conj : S' →* MulAut S')) ≤
      Subgroup.normalizer
        (((T.subgroupOf S).map (eS.toMonoidHom.comp (chevQuotHom p S))) : Set S') := by
  set θ : ↥B₀ →* MulAut S' := (MulAut.congr eS).toMonoidHom.comp ψ with hθ
  set πK : ↥S →* S' := eS.toMonoidHom.comp (chevQuotHom p S) with hπK
  set Eb : Subgroup S' := θ.range.comap (MulAut.conj : S' →* MulAut S') with hEb
  set Tb : Subgroup S' := (T.subgroupOf S).map πK with hTb
  have key : ∀ s ∈ Eb, ∀ x ∈ Tb, s * x * s⁻¹ ∈ Tb := by
    intro s hs x hx
    obtain ⟨b, hb⟩ : MulAut.conj s ∈ θ.range := hs
    obtain ⟨k, hkT, rfl⟩ := hx
    have h1 : s * πK k * s⁻¹ = (θ b) (πK k) := by
      rw [hb]
      simp [MulAut.conj_apply]
    have h2 : (θ b) (πK k) = πK (S.normalizerMonoidHom ⟨(b : Ω), hBK b.2⟩ k) := by
      have h3 := chevAut_chevQuotHom p S ⟨(b : Ω), hBK b.2⟩ k
      show (MulAut.congr eS (ψ b)) (eS (chevQuotHom p S k)) =
        eS (chevQuotHom p S (S.normalizerMonoidHom ⟨(b : Ω), hBK b.2⟩ k))
      rw [hψ b]
      simp [MulAut.congr_apply, h3]
    rw [h1, h2]
    refine Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ?_)
    have hkT' : (k : Ω) ∈ T := Subgroup.mem_subgroupOf.1 hkT
    exact (Subgroup.mem_normalizer_iff.1 (hBT b.2) (k : Ω)).1 hkT'
  have hnorm : Eb ≤ Subgroup.normalizer (Tb : Set S') := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    refine fun y => ⟨key x hx y, fun hy => ?_⟩
    have := key x⁻¹ (Eb.inv_mem hx) _ hy
    simpa [mul_assoc] using this
  exact hnorm

private theorem map_chevQuotHom_trans_ne_bot (hp : p.Prime) (hp2 : p ≠ 2) {S T : Subgroup Ω}
    (hTS : T ≤ S) (hT2 : IsPGroup 2 ↥T) (hT : T ≠ ⊥) (hSp : GLAPPrimeCore p ↥S = ⊥)
    {S' : Type} [Group S'] (e : ↥S ⧸ Subgroup.center ↥S ≃* S') :
    (T.subgroupOf S).map (((pSimpleEquiv hSp).trans e).toMonoidHom.comp (chevQuotHom p S)) ≠ ⊥ := by
  obtain ⟨t, htT, ht2⟩ := exists_orderOf_two_of_isPGroup hT2 hT
  set k : ↥S := ⟨t, hTS htT⟩ with hk
  have hk2 : orderOf k = 2 := by rw [← ht2, ← Subgroup.orderOf_coe]
  have hkc := t263_not_mem_center_of_orderOf_two hp hp2 hSp hk2
  intro hbot
  have hmem : ((pSimpleEquiv hSp).trans e) (chevQuotHom p S k) ∈
      (T.subgroupOf S).map (((pSimpleEquiv hSp).trans e).toMonoidHom.comp (chevQuotHom p S)) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 htT)
  rw [hbot, Subgroup.mem_bot] at hmem
  apply hkc
  have h1 : e (pSimpleEquiv hSp (chevQuotHom p S k)) = 1 := hmem
  rw [pSimpleEquiv_chevQuotHom hSp, ← map_one e] at h1
  exact (QuotientGroup.eq_one_iff k).1 (e.injective h1)

private theorem exists_elemAbelian_comap_conj_of_range {S B₀ T : Subgroup Ω} {p : ℕ}
    (hBK : B₀ ≤ Subgroup.normalizer (S : Set Ω)) (hBT : B₀ ≤ Subgroup.normalizer (T : Set Ω))
    {S' : Type} [Group S'] (hZ : Subgroup.center S' = ⊥) (hB₀ : IsElemAbelian p B₀)
    (eS : PSimple p S ≃* S') (ψ : ↥B₀ →* MulAut (PSimple p S))
    (hψ : ∀ b : ↥B₀, ψ b = chevAut p S ⟨(b : Ω), hBK b.2⟩)
    (hψinner : ψ.range ≤ inner (PSimple p S)) (hR : p < Nat.card ψ.range) :
    ∃ Eb : Subgroup S', IsElemAbelian p Eb ∧ p < Nat.card Eb ∧
      Eb ≤ Subgroup.normalizer
        (((T.subgroupOf S).map (eS.toMonoidHom.comp (chevQuotHom p S))) : Set S') := by
  let θ : ↥B₀ →* MulAut S' := (MulAut.congr eS).toMonoidHom.comp ψ
  have hBhel : IsElemAbelian p θ.range := isElemAbelian_range_of_monoidHom hB₀ θ
  let Eb : Subgroup S' := θ.range.comap (MulAut.conj : S' →* MulAut S')
  have hEbel : IsElemAbelian p Eb :=
    isElemAbelian_comap_conj_of_range hZ θ (fun α hα => hBhel.2 α hα)
      (fun α hα β hβ => isElemAbelian_commute hBhel hα hβ)
  have hBhinner : θ.range ≤ inner S' := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨w, hw⟩ := hψinner ⟨b, rfl⟩
    refine ⟨eS w, ?_⟩
    show MulAut.conj (eS w) = MulAut.congr eS (ψ b)
    rw [← hw, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
  have hEbcard : Nat.card Eb = Nat.card ψ.range := by
    have hθr : θ.range = ψ.range.map (MulAut.congr eS).toMonoidHom :=
      MonoidHom.range_comp (MulAut.congr eS).toMonoidHom ψ
    refine (card_comap_conj_of_range_le_inner hZ θ hBhinner).trans ?_
    rw [hθr, Subgroup.card_map_of_injective (MulAut.congr eS).injective]
  exact ⟨Eb, hEbel, by rw [hEbcard]; exact hR,
    comap_range_conj_le_normalizer_map hBK hBT eS ψ hψ⟩

theorem t263_false_of_inner_rank (hp : p.Prime) (hp2 : p ≠ 2) {S B₀ T : Subgroup Ω}
    (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hB₀ : IsElemAbelian p B₀) (hin : ∀ b ∈ B₀, InducesInnerMod p S b)
    (hcard : p * Nat.card ↥(B₀ ⊓ Subgroup.centralizer (S : Set Ω)) < Nat.card ↥B₀)
    (hTS : T ≤ S) (hT2 : IsPGroup 2 ↥T) (hT : T ≠ ⊥)
    (hBT : B₀ ≤ Subgroup.normalizer (T : Set Ω)) {S' : Type} [Group S']
    (e : ↥S ⧸ Subgroup.center ↥S ≃* S') (hZ : Subgroup.center S' = ⊥)
    (hS : ∀ E U : Subgroup S', IsElemAbelian p E → IsPGroup 2 ↥U → U ≠ ⊥ →
      E ≤ Subgroup.normalizer (U : Set S') → Nat.card ↥E ≤ p) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite S' := Finite.of_equiv _ e.toEquiv
  have hBK : B₀ ≤ Subgroup.normalizer (S : Set Ω) := fun g _ => t263_normalizer_of_normal hSn
  let ψ := actionHom S B₀ hBK p
  have hψinner : ψ.range ≤ inner (PSimple p S) :=
    actionHom_range_le_inner_of_core hp hSn hSq hSp hin
  have hcardψ : Nat.card ↥(B₀ ⊓ Subgroup.centralizer (S : Set Ω)) * Nat.card ψ.range =
      Nat.card B₀ := card_actionHom_of_core hp hSn hSq hSp hBK
  have hR : p < Nat.card ψ.range := by
    have h : Nat.card ↥(B₀ ⊓ Subgroup.centralizer (S : Set Ω)) * p <
        Nat.card ↥(B₀ ⊓ Subgroup.centralizer (S : Set Ω)) * Nat.card ψ.range := by
      calc Nat.card ↥(B₀ ⊓ Subgroup.centralizer (S : Set Ω)) * p
          = p * Nat.card ↥(B₀ ⊓ Subgroup.centralizer (S : Set Ω)) := Nat.mul_comm _ _
        _ < Nat.card ↥B₀ := hcard
        _ = Nat.card ↥(B₀ ⊓ Subgroup.centralizer (S : Set Ω)) * Nat.card ψ.range := hcardψ.symm
    exact Nat.lt_of_mul_lt_mul_left h
  let eS : PSimple p S ≃* S' := (pSimpleEquiv hSp).trans e
  obtain ⟨Eb, hEbel, hpEb, hnorm⟩ :=
    exists_elemAbelian_comap_conj_of_range hBK hBT hZ hB₀ eS ψ
      (fun b => actionHom_apply S B₀ hBK p b) hψinner hR
  let πK : ↥S →* S' := eS.toMonoidHom.comp (chevQuotHom p S)
  let Tb : Subgroup S' := (T.subgroupOf S).map πK
  have hTb2 : IsPGroup 2 Tb := (hT2.comap_subtype).map πK
  have hTbne : Tb ≠ ⊥ := map_chevQuotHom_trans_ne_bot hp hp2 hTS hT2 hT hSp e
  have hle := hS Eb Tb hEbel hTb2 hTbne hnorm
  omega

end CFSG.LocalAnalysis.GLTheoremA.T263.DXW
