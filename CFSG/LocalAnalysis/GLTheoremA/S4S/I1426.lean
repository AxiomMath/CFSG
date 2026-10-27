module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.PartI.Transfer
public import CFSG.LocalAnalysis.GLTheoremA.PartI.Lift
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Common
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.SignalizerFunctorTheorem
open scoped commutatorElement

private theorem i1426_catalogIs_congr {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (Q : TauCeti.CFSGIndex → Prop) : catalogIs S Q → catalogIs S' Q := by
  rintro ⟨i, hi, ⟨f⟩⟩
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

private theorem i1426_center_map {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') :
    (Subgroup.center Q).map (e : Q →* Q') = Subgroup.center Q' :=
  Subgroup.map_center_eq e

private theorem i1426_center_eq_bot {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : Subgroup.center Q = ⊥) : Subgroup.center Q' = ⊥ := by
  rw [← i1426_center_map e, h, Subgroup.map_bot]

private theorem i1426_quotCenter {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') :
    Nonempty ((Q ⧸ Subgroup.center Q) ≃* (Q' ⧸ Subgroup.center Q')) :=
  ⟨QuotientGroup.congr _ _ e (i1426_center_map e)⟩

private theorem i1426_isChevSimple_congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (r : ℕ) (h : IsChevSimple r (Q ⧸ Subgroup.center Q)) :
    IsChevSimple r (Q' ⧸ Subgroup.center Q') := by
  obtain ⟨f⟩ := i1426_quotCenter e
  unfold IsChevSimple at h ⊢
  rcases h with h | h
  · exact Or.inl (i1426_catalogIs_congr f _ h)
  · exact Or.inr (i1426_catalogIs_congr f _ h)

private theorem i1426_fullLinearCover_congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (u : Bool) (d q : ℕ) (h : FullLinearCover u d q Q) : FullLinearCover u d q Q' := by
  obtain ⟨K, hF, hfin, h⟩ := h
  refine ⟨K, hF, hfin, ?_⟩
  split_ifs at h ⊢
  · exact ⟨h.1, h.2.map fun f => e.symm.trans f⟩
  · exact ⟨h.1, h.2.map fun f => e.symm.trans f⟩

private theorem i1426_k2LinearCover_congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (p : ℕ) (h : K2LinearCover p Q) : K2LinearCover p Q' := by
  obtain ⟨hp, h⟩ := h
  refine ⟨hp, ?_⟩
  rcases h with ⟨n, h1, h2, h3⟩ | ⟨n, h1, h2, h3⟩ | h3
  · exact Or.inl ⟨n, h1, h2, i1426_fullLinearCover_congr e _ _ _ h3⟩
  · exact Or.inr (Or.inl ⟨n, h1, h2, i1426_fullLinearCover_congr e _ _ _ h3⟩)
  · exact Or.inr (Or.inr (i1426_fullLinearCover_congr e _ _ _ h3))

private theorem i1426_k3LinearCover_congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (p : ℕ) (h : K3LinearCover p Q) : K3LinearCover p Q' := by
  obtain ⟨hp, r, f, hr, hf, h⟩ := h
  refine ⟨hp, r, f, hr, hf, ?_⟩
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, i1426_fullLinearCover_congr e _ _ _ h2⟩
  · exact Or.inr ⟨h1, i1426_fullLinearCover_congr e _ _ _ h2⟩

private theorem i1426_simpleCoverList_congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (P : TauCeti.CFSGIndex → Prop) (h : SimpleCoverList Q P) : SimpleCoverList Q' P :=
  ⟨i1426_center_eq_bot e h.1, i1426_catalogIs_congr e P h.2⟩

private theorem i1426_maximalOddCover_congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (i : TauCeti.CFSGIndex) (h : MaximalOddCover Q i) : MaximalOddCover Q' i := by
  obtain ⟨hfin, hq, hsimp, hnab, π, hπs, hπk, hcyc, hodd, huniv⟩ := h
  have hfin' : Finite Q' := Finite.of_equiv Q e
  have hcard : Nat.card (Subgroup.center Q') = Nat.card (Subgroup.center Q) := by
    rw [← i1426_center_map e]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective (Subgroup.center Q) (e : Q →* Q')
      e.injective).toEquiv).symm
  have hcyc' : IsCyclic (Subgroup.center Q') := by
    let φ := (Subgroup.equivMapOfInjective (Subgroup.center Q) (e : Q →* Q') e.injective).trans
      (MulEquiv.subgroupCongr (i1426_center_map e))
    exact (MulEquiv.isCyclic φ).mp hcyc
  refine ⟨hfin', TransportA.isQuasisimple_of_mulEquiv e hq, hsimp, hnab,
    π.comp (e.symm : Q' →* Q), hπs.comp e.symm.surjective, ?_, hcyc', ?_, ?_⟩
  · have hmem : ∀ x : Q', x ∈ Subgroup.center Q' ↔ e.symm x ∈ Subgroup.center Q := by
      intro x
      rw [← i1426_center_map e]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro h
        exact ⟨e.symm x, h, by simp⟩
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hπk]
    exact (hmem x).symm
  · rw [hcard]; exact hodd
  · intro U _ _ hU ρ hρ hρk hoddU
    obtain ⟨f, hf, hfπ⟩ := huniv U hU ρ hρ hρk hoddU
    exact ⟨f.comp (e.symm : Q' →* Q), hf.comp e.symm.surjective, by rw [← MonoidHom.comp_assoc, hfπ]⟩

private theorem i1426_hatCoverList_congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (P : TauCeti.CFSGIndex → Prop) (h : HatCoverList Q P) : HatCoverList Q' P := by
  obtain ⟨i, hP, hmax, hcard⟩ := h
  refine ⟨i, hP, i1426_maximalOddCover_congr e i hmax, ?_⟩
  rw [← i1426_center_map e]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective (Subgroup.center Q) (e : Q →* Q')
      e.injective).toEquiv).symm.trans hcard

private theorem i1426_k1Cover_congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') (p : ℕ)
    (h : K1Cover p Q) : K1Cover p Q' :=
  ⟨TransportA.isQuasisimple_of_mulEquiv e h.1, i1426_isChevSimple_congr e p h.2⟩

private theorem i1426_k2Cover_congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') (p : ℕ)
    (h : K2Cover p Q) : K2Cover p Q' := by
  obtain ⟨hq, h⟩ := h
  refine ⟨TransportA.isQuasisimple_of_mulEquiv e hq, ?_⟩
  rcases h with h | h | h | h
  · exact Or.inl (i1426_simpleCoverList_congr e _ h)
  · exact Or.inr (Or.inl (i1426_simpleCoverList_congr e _ h))
  · exact Or.inr (Or.inr (Or.inl (i1426_k2LinearCover_congr e p h)))
  · exact Or.inr (Or.inr (Or.inr (i1426_hatCoverList_congr e _ h)))

private theorem i1426_k3Cover_congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') (p : ℕ)
    (h : K3Cover p Q) : K3Cover p Q' := by
  obtain ⟨hq, h⟩ := h
  refine ⟨TransportA.isQuasisimple_of_mulEquiv e hq, ?_⟩
  rcases h with h | h | h
  · exact Or.inl (i1426_simpleCoverList_congr e _ h)
  · exact Or.inr (Or.inl (i1426_k3LinearCover_congr e p h))
  · exact Or.inr (Or.inr (i1426_hatCoverList_congr e _ h))

private theorem i1426_fullCoverLevel_congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') (p : ℕ) :
    fullCoverLevel p Q = fullCoverLevel p Q' := by
  have h1 : K1Cover p Q ↔ K1Cover p Q' := ⟨i1426_k1Cover_congr e p, i1426_k1Cover_congr e.symm p⟩
  have h2 : K2Cover p Q ↔ K2Cover p Q' := ⟨i1426_k2Cover_congr e p, i1426_k2Cover_congr e.symm p⟩
  have h3 : K3Cover p Q ↔ K3Cover p Q' := ⟨i1426_k3Cover_congr e p, i1426_k3Cover_congr e.symm p⟩
  unfold fullCoverLevel
  by_cases a : K1Cover p Q
  · rw [if_pos a, if_pos (h1.1 a)]
  · rw [if_neg a, if_neg (fun b => a (h1.2 b))]
    by_cases c : K2Cover p Q
    · rw [if_pos c, if_pos (h2.1 c)]
    · rw [if_neg c, if_neg (fun d => c (h2.2 d))]
      by_cases g : K3Cover p Q
      · rw [if_pos g, if_pos (h3.1 g)]
      · rw [if_neg g, if_neg (fun k => g (h3.2 k))]

private theorem i1426_fixed_coset {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (N : Subgroup X) [N.Normal] (hN : ¬ p ∣ Nat.card N) {P : Subgroup X} (hP : IsPGroup p P)
    {y : X} (hy : ∀ g ∈ P, g * y * g⁻¹ * y⁻¹ ∈ N) :
    ∃ x : X, x * y⁻¹ ∈ N ∧ ∀ g ∈ P, g * x = x * g := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let S := {x : X // x * y⁻¹ ∈ N}
  letI : MulAction P S :=
    { smul := fun g x => ⟨(g : X) * x.1 * (g : X)⁻¹, by
        have h1 : (g : X) * x.1 * (g : X)⁻¹ * y⁻¹ =
            ((g : X) * (x.1 * y⁻¹) * (g : X)⁻¹) * ((g : X) * y * (g : X)⁻¹ * y⁻¹) := by group
        show (g : X) * x.1 * (g : X)⁻¹ * y⁻¹ ∈ N
        rw [h1]
        exact N.mul_mem (Subgroup.Normal.conj_mem inferInstance _ x.2 _) (hy _ g.2)⟩
      one_smul := fun x => Subtype.ext (by
        show ((1 : P) : X) * x.1 * ((1 : P) : X)⁻¹ = x.1
        simp)
      mul_smul := fun g h x => Subtype.ext (by
        show ((g * h : P) : X) * x.1 * ((g * h : P) : X)⁻¹ = ((g : X) * ((h : X) * x.1 * (h : X)⁻¹) *
          (g : X)⁻¹)
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group) }
  have hcard : ¬ p ∣ Nat.card S := by
    have e : S ≃ N :=
      { toFun := fun x => ⟨x.1 * y⁻¹, x.2⟩
        invFun := fun n => ⟨n.1 * y, by simpa using n.2⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun n => Subtype.ext (by simp) }
    rw [Nat.card_congr e]
    exact hN
  obtain ⟨x, hx⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card S hcard
  refine ⟨x.1, x.2, fun g hg => ?_⟩
  have hgx := congrArg Subtype.val (MulAction.mem_fixedPoints.1 hx ⟨g, hg⟩)
  have hgx' : (g : X) * x.1 * (g : X)⁻¹ = x.1 := hgx
  exact mul_inv_eq_iff_eq_mul.1 hgx'

private theorem i1426_mem_core_of_mem {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (N : Subgroup X) [N.Normal] (hN : ¬ p ∣ Nat.card N) {Z : Subgroup X} {g : X}
    (hg : g ∈ Z) (hgN : g ∈ N) : g ∈ GLAPPrimeCoreOf p Z := by
  have hnorm : (N.subgroupOf Z).Normal := inferInstance
  have hcop : Nat.Coprime p (Nat.card (N.subgroupOf Z)) := by
    have h1 : Nat.card ((N.subgroupOf Z).map Z.subtype) = Nat.card (N.subgroupOf Z) :=
      Subgroup.card_map_of_injective Z.subtype_injective
    rw [← h1, Subgroup.subgroupOf_map_subtype]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hN (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hle : N.subgroupOf Z ≤ GLAPPrimeCore p ↥Z := by
    unfold GLAPPrimeCore CFSG.pPrimeCore
    exact le_sSup ⟨hnorm, hcop⟩
  exact Subgroup.mem_map.2 ⟨⟨g, hg⟩, hle (Subgroup.mem_subgroupOf.2 hgN), rfl⟩

private theorem i1426_map_inf_centralizer {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (N : Subgroup X) [N.Normal] (hN : ¬ p ∣ Nat.card N) {K P : Subgroup X} (hNK : N ≤ K)
    (hP : IsPGroup p P) :
    K.map (QuotientGroup.mk' N) ⊓
        Subgroup.centralizer ((P.map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) : Set (X ⧸ N)) =
      (K ⊓ Subgroup.centralizer (P : Set X)).map (QuotientGroup.mk' N) := by
  apply le_antisymm
  · rintro _ ⟨⟨y, hyK, rfl⟩, hC⟩
    have hy : ∀ g ∈ P, g * y * g⁻¹ * y⁻¹ ∈ N := by
      intro g hg
      have h1 : QuotientGroup.mk' N g * QuotientGroup.mk' N y =
          QuotientGroup.mk' N y * QuotientGroup.mk' N g :=
        Subgroup.mem_centralizer_iff.1 hC _ (Subgroup.mem_map.2 ⟨g, hg, rfl⟩)
      have hmk : QuotientGroup.mk' N (g * y * g⁻¹ * y⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        calc QuotientGroup.mk' N g * QuotientGroup.mk' N y * (QuotientGroup.mk' N g)⁻¹ *
              (QuotientGroup.mk' N y)⁻¹
            = (QuotientGroup.mk' N y * QuotientGroup.mk' N g) * (QuotientGroup.mk' N g)⁻¹ *
              (QuotientGroup.mk' N y)⁻¹ := by rw [h1]
          _ = 1 := by group
      exact (QuotientGroup.eq_one_iff _).1 hmk
    obtain ⟨x, hxn, hxc⟩ := i1426_fixed_coset hp N hN hP hy
    have hxK : x ∈ K := by
      have hx : x = (x * y⁻¹) * y := by group
      rw [hx]
      exact K.mul_mem (hNK hxn) hyK
    refine ⟨x, ⟨hxK, Subgroup.mem_centralizer_iff.2 fun g hg => hxc g hg⟩, ?_⟩
    apply QuotientGroup.eq.2
    have hc := Subgroup.Normal.conj_mem inferInstance _ (N.inv_mem hxn) x⁻¹
    have e : x⁻¹ * (x * y⁻¹)⁻¹ * (x⁻¹)⁻¹ = x⁻¹ * y := by group
    rw [e] at hc
    exact hc
  · rintro _ ⟨z, ⟨hzK, hzC⟩, rfl⟩
    refine ⟨Subgroup.mem_map.2 ⟨z, hzK, rfl⟩, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hh
    have hgz : g * z = z * g := (Subgroup.mem_centralizer_iff.1 hzC) g hg
    rw [← map_mul, ← map_mul, hgz]

private theorem i1426_component_unique_of_map {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (N : Subgroup X) [N.Normal] (hN : ¬ p ∣ Nat.card N) {Z J₁ J₂ : Subgroup X}
    (h₁ : GLAPComponent p Z J₁) (h₂ : GLAPComponent p Z J₂)
    (hmap : J₁.map (QuotientGroup.mk' N) = J₂.map (QuotientGroup.mk' N)) : J₁ = J₂ := by
  have key : ∀ {J J' : Subgroup X}, GLAPComponent p Z J → GLAPComponent p Z J' →
      J.map (QuotientGroup.mk' N) = J'.map (QuotientGroup.mk' N) →
      barX p Z J ≤ barX p Z J' := by
    intro J J' hJ hJ' hm
    refine barX_le_of_forall hJ'.1 fun k hk => ?_
    have hk' : QuotientGroup.mk' N k ∈ J'.map (QuotientGroup.mk' N) := by
      rw [← hm]
      exact Subgroup.mem_map_of_mem _ hk
    obtain ⟨j, hj, hjk⟩ := Subgroup.mem_map.1 hk'
    have hjk' : j⁻¹ * k ∈ N := QuotientGroup.eq.1 hjk
    exact ⟨j, hj, i1426_mem_core_of_mem hp N hN (Z.mul_mem (Z.inv_mem (hJ'.1 hj)) (hJ.1 hk)) hjk'⟩
  exact glaPComponent_unique h₁ h₂ (le_antisymm (key h₁ h₂ hmap) (key h₂ h₁ hmap.symm))

private theorem i1426_component_eq_of_le {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {Z J₀ J : Subgroup X} (hJ₀ : GLAPComponent p Z J₀) (hJ : GLAPComponent p Z J)
    (hJJ₀ : J ≤ J₀) : J = J₀ :=
  glaPComponent_eq_of_isQuasisimple (isQuasisimple_pQuot_of_glaPComponent hp hJ₀)
    (glaPComponent_of_le hp hJ hJJ₀ hJ₀.1) (glaPComponent_of_le hp hJ₀ le_rfl hJ₀.1)

private instance i1426_core_normal {X : Type} [Group X] (L₀ : Subgroup X) [L₀.Normal] :
    (GLAPPrimeCoreOf 3 L₀).Normal := by
  have h := normalizer_le_normalizer_glaPPrimeCoreOf 3 L₀
  rw [Subgroup.normalizer_eq_top_iff.2 inferInstance, top_le_iff] at h
  exact Subgroup.normalizer_eq_top_iff.1 h

private theorem i1426_kb_iso {X : Type} [Group X] [Finite X] (L₀ : Subgroup X) [L₀.Normal] :
    Nonempty (PQuot 3 L₀ ≃* ↥(L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)))) := by
  have hcore : GLAPPrimeCoreOf 3 L₀ = (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)).ker ⊓ L₀ := by
    rw [QuotientGroup.ker_mk']
    exact (inf_eq_left.2 (Subgroup.map_subtype_le _)).symm
  exact nonempty_pQuot_equiv_map_self (p := 3) hcore

private theorem i1426_kb_core {X : Type} [Group X] [Finite X] (L₀ : Subgroup X) [L₀.Normal] :
    GLAPPrimeCore 3 ↥(L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀))) = ⊥ := by
  obtain ⟨e⟩ := i1426_kb_iso L₀
  have h := glaPPrimeCore_map_iso 3 e
  rw [← h, glaPPrimeCore_quotient_eq_bot Nat.prime_three, Subgroup.map_bot]

private theorem i1426_kb_quasisimple {X : Type} [Group X] [Finite X] (L₀ : Subgroup X) [L₀.Normal]
    (hq : CFSG.Open.IsQuasisimple (PQuot 3 L₀)) :
    CFSG.Open.IsQuasisimple ↥(L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀))) := by
  obtain ⟨e⟩ := i1426_kb_iso L₀
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hq

private theorem i1426_elemAbelian_map {X Y : Type} [Group X] [Group Y] {p : ℕ} (f : X →* Y)
    {E : Subgroup X} (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    show (a : Y) * (b : Y) = (b : Y) * (a : Y)
    rw [← hxa, ← hyb, ← map_mul, ← map_mul, isElemAbelian_commute hE hx hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]

private theorem i1426_card_map {X Y : Type} [Group X] [Group Y] (f : X →* Y) (B : Subgroup X)
    (hf : ∀ x ∈ B, f x = 1 → x = 1) : Nat.card (B.map f) = Nat.card B := by
  have hinj : Function.Injective (f.comp B.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact Subtype.ext (hf a.1 a.2 (by simpa using ha))
  have hm : (⊤ : Subgroup B).map (f.comp B.subtype) = B.map f := by
    ext y
    constructor
    · rintro ⟨z, -, rfl⟩
      exact ⟨z.1, z.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, Subgroup.mem_top _, rfl⟩
  rw [← hm, Subgroup.card_map_of_injective hinj, Subgroup.card_top]

private theorem i1426_inj_of_coprime {X : Type} [Group X] {N B : Subgroup X} (hp : Nat.Prime 3)
    [Finite N] (hN : ¬ 3 ∣ Nat.card N) (hB : IsElemAbelian 3 B) (x : X) (hxB : x ∈ B)
    (hxN : x ∈ N) : x = 1 := by
  have h3 : x ^ 3 = 1 := hB.2 x hxB
  have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have h2 : orderOf x ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨x, hxN⟩ : N)
    simpa [Subgroup.orderOf_mk] using this
  have hcop : Nat.Coprime 3 (Nat.card N) := (Nat.Prime.coprime_iff_not_dvd hp).2 hN
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

private theorem i1426_coprime_ker {X : Type} [Group X] (N : Subgroup X) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) (A : Subgroup X) :
    Nat.Coprime 3 (Nat.card ↥(A ⊓ (QuotientGroup.mk' N).ker)) := by
  rw [QuotientGroup.ker_mk']
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h =>
    hN (h.trans (Subgroup.card_dvd_of_le inf_le_right))

private theorem i1426_inj_pgroup {X : Type} [Group X] {N W : Subgroup X} (hN : ¬ 3 ∣ Nat.card N)
    (hW : IsPGroup 3 W) (x : X) (hxW : x ∈ W) (hxN : x ∈ N) : x = 1 := by
  obtain ⟨k, hk⟩ := hW ⟨x, hxW⟩
  have hk' : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf x ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨x, hxN⟩ : N)
    simpa [Subgroup.orderOf_mk] using this
  have hcop : Nat.Coprime 3 (Nat.card N) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hcop) h1 h2)

private theorem i1426_exists_ne_bot_component {X : Type} [Group X] {Z : Subgroup X}
    (h : GLAPLayer 3 Z ≠ ⊥) : ∃ J : Subgroup X, GLAPComponent 3 Z J ∧ J ≠ ⊥ := by
  by_contra hcon
  push_neg at hcon
  apply h
  refine le_antisymm (sSup_le fun J hJ => ?_) bot_le
  exact le_of_eq (hcon J hJ)

private theorem i1426_le_layer {X : Type} [Group X] {Z J : Subgroup X}
    (h : GLAPComponent 3 Z J) : J ≤ GLAPLayer 3 Z :=
  le_sSup h

private theorem i1426_le_normalizer_of_normal {X : Type} [Group X] (N A : Subgroup X) [N.Normal] :
    A ≤ Subgroup.normalizer (N : Set X) := by
  have h : Subgroup.normalizer (N : Set X) = ⊤ := Subgroup.normalizer_eq_top_iff.2 inferInstance
  intro x _
  rw [h]
  exact Subgroup.mem_top x

private theorem i1426_lift_elemAbelian {X : Type} [Group X] [Finite X] (L₀ : Subgroup X)
    [L₀.Normal] {E : Subgroup (X ⧸ GLAPPrimeCoreOf 3 L₀)} (hE : IsElemAbelian 3 E) :
    ∃ W : Subgroup X, IsElemAbelian 3 W ∧ W.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) = E ∧
      Nat.card W = Nat.card E := by
  set N₀ := GLAPPrimeCoreOf 3 L₀ with hN₀
  have hN : ¬ 3 ∣ Nat.card N₀ := not_dvd_card_glaPPrimeCoreOf Nat.prime_three L₀
  set E' : Subgroup X := E.comap (QuotientGroup.mk' N₀) with hE'
  have hψE' : ∀ x, x ∈ E' ↔ QuotientGroup.mk' N₀ x ∈ E := fun x => Iff.rfl
  have hOE : N₀ ≤ E' := by
    intro n hn
    have h1 : QuotientGroup.mk' N₀ n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    exact (hψE' n).2 (by rw [h1]; exact E.one_mem)
  have hEp : ∀ e ∈ E', ∃ k : ℕ, e ^ (3 ^ k) ∈ N₀ := by
    intro e he
    refine ⟨1, ?_⟩
    have h3 : QuotientGroup.mk' N₀ (e ^ 3 ^ 1) = 1 := by
      rw [pow_one, map_pow]
      have := hE.2 _ ((hψE' e).1 he)
      exact this
    exact (QuotientGroup.eq_one_iff _).1 h3
  have hD : IsPGroup 3 (⊥ : Subgroup X) := fun g => by
    have hg : g = 1 := Subtype.ext (Subgroup.mem_bot.1 g.2)
    exact ⟨0, by rw [hg]; simp⟩
  have hDE : (⊥ : Subgroup X) ≤ Subgroup.normalizer (E' : Set X) := bot_le
  obtain ⟨W, hWle, hWp, -, hWsup⟩ := exists_pGroup_lift Nat.prime_three hN hOE
    (i1426_le_normalizer_of_normal N₀ E') hEp hD hDE hDE
    (i1426_le_normalizer_of_normal N₀ E') le_sup_left
  have hWE' : W ≤ E' := hWle.trans inf_le_right
  have hmap : W.map (QuotientGroup.mk' N₀) = E := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact (hψE' w).1 (hWE' hw)
    · intro e he
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N₀ e
      have hxE' : x ∈ E' := (hψE' x).2 (by rw [hx]; exact he)
      rw [← hWsup] at hxE'
      obtain ⟨w, hw, n, hn, hwn⟩ := (Subgroup.mem_sup_of_normal_right).1 hxE'
      refine ⟨w, hw, ?_⟩
      have h1 : QuotientGroup.mk' N₀ n = 1 := (QuotientGroup.eq_one_iff n).2 hn
      rw [← hx, ← hwn, map_mul, h1, mul_one]
  have hcardW : Nat.card W = Nat.card E := by
    rw [← hmap]
    exact (i1426_card_map (QuotientGroup.mk' N₀) W (fun x hx hx1 =>
      i1426_inj_pgroup hN hWp x hx ((QuotientGroup.eq_one_iff x).1 hx1))).symm
  have hinj : ∀ x ∈ W, QuotientGroup.mk' N₀ x = 1 → x = 1 := fun x hx hx1 =>
    i1426_inj_pgroup hN hWp x hx ((QuotientGroup.eq_one_iff x).1 hx1)
  have hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
    intro x hx y hy
    have hxE : QuotientGroup.mk' N₀ x ∈ E := (hψE' x).1 (hWE' hx)
    have hyE : QuotientGroup.mk' N₀ y ∈ E := (hψE' y).1 (hWE' hy)
    have hcW : (y * x)⁻¹ * (x * y) ∈ W := W.mul_mem (W.inv_mem (W.mul_mem hy hx)) (W.mul_mem hx hy)
    have hψc : QuotientGroup.mk' N₀ ((y * x)⁻¹ * (x * y)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, isElemAbelian_commute hE hxE hyE, inv_mul_cancel]
    have h1 := hinj _ hcW hψc
    exact (inv_mul_eq_one.1 h1).symm
  refine ⟨W, ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩, hmap, hcardW⟩
  have h3 : QuotientGroup.mk' N₀ (x ^ 3) = 1 := by
    rw [map_pow]
    exact hE.2 _ ((hψE' x).1 (hWE' hx))
  exact hinj _ (W.pow_mem hx 3) h3

private theorem i1426_normalizes_map {X Y : Type} [Group X] [Group Y] (f : X →* Y)
    (U : Subgroup X) (b : X) (hb : b ∈ Subgroup.normalizer (U : Set X)) :
    f b ∈ Subgroup.normalizer ((U.map f : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have key : ∀ u, u ∈ U ↔ b * u * b⁻¹ ∈ U := fun u => (Subgroup.mem_normalizer_iff.1 hb u)
  constructor
  · intro hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hy
    exact Subgroup.mem_map.2 ⟨b * u * b⁻¹, (key u).1 hu, by simp [map_mul, map_inv]⟩
  · intro hy
    obtain ⟨v, hv, hvy⟩ := Subgroup.mem_map.1 hy
    refine Subgroup.mem_map.2 ⟨b⁻¹ * v * b, ?_, ?_⟩
    · apply (key (b⁻¹ * v * b)).2
      have e : b * (b⁻¹ * v * b) * b⁻¹ = v := by group
      rw [e]
      exact hv
    · rw [map_mul, map_mul, map_inv, hvy]
      group

private theorem i1426_maxRank_quot {X : Type} [Group X] [Finite X] (L₀ : Subgroup X) [L₀.Normal]
    (B₀ : Subgroup X) (hB : IsElemAbelian 3 B₀) (hmax : IsMaxRankIn 3 B₀ ⊤) :
    IsMaxRankIn 3 (B₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀))) ⊤ := by
  intro E _ hE
  obtain ⟨W, hWab, -, hWcard⟩ := i1426_lift_elemAbelian L₀ hE
  have hN : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 L₀) := not_dvd_card_glaPPrimeCoreOf Nat.prime_three L₀
  have hcard : Nat.card (B₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀))) = Nat.card B₀ :=
    i1426_card_map _ B₀ (fun x hx hx1 =>
      i1426_inj_of_coprime Nat.prime_three hN hB x hx ((QuotientGroup.eq_one_iff x).1 hx1))
  rw [hcard, ← hWcard]
  exact hmax W le_top hWab

private theorem i1426_sup_map {X : Type} [Group X] (L₀ B₀ : Subgroup X) [L₀.Normal]
    (h : L₀ ⊔ B₀ = ⊤) :
    L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) ⊔
      B₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) = ⊤ := by
  rw [← Subgroup.map_sup, h, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

private theorem i1426_E_cond {X : Type} [Group X] [Finite X] (L₀ : Subgroup X) [L₀.Normal]
    (B₀ : Subgroup X) (hB : IsElemAbelian 3 B₀)
    (hE : ∀ E : Subgroup X, E ≤ B₀ → IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      GLAPLayer 3 (L₀ ⊓ Subgroup.centralizer (E : Set X)) = ⊥)
    (Ē : Subgroup (X ⧸ GLAPPrimeCoreOf 3 L₀))
    (hĒ : Ē ≤ B₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)))
    (hĒab : IsElemAbelian 3 Ē) (hcard : Nat.card Ē = 3 ^ 3) :
    GLAPLayer 3 ((L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀))) ⊓
      Subgroup.centralizer (Ē : Set (X ⧸ GLAPPrimeCoreOf 3 L₀))) = ⊥ := by
  have hN : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 L₀) := not_dvd_card_glaPPrimeCoreOf Nat.prime_three L₀
  set E : Subgroup X := Ē.comap (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) ⊓ B₀ with hEdef
  have hEB : E ≤ B₀ := inf_le_right
  have hEab : IsElemAbelian 3 E := isElemAbelian_mono hB inf_le_right
  have hEmap : E.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) = Ē := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.1
    · intro e he
      obtain ⟨b, hb, hbe⟩ := Subgroup.mem_map.1 (hĒ he)
      exact Subgroup.mem_map.2 ⟨b, ⟨Subgroup.mem_comap.2 (by rw [hbe]; exact he), hb⟩, hbe⟩
  have hcardE : Nat.card E = 3 ^ 3 := by
    rw [← hcard, ← hEmap]
    exact (i1426_card_map _ E (fun x hx hx1 => i1426_inj_of_coprime Nat.prime_three hN hB x
      (hEB hx) ((QuotientGroup.eq_one_iff x).1 hx1))).symm
  have hL : GLAPLayer 3 (L₀ ⊓ Subgroup.centralizer (E : Set X)) = ⊥ := hE E hEB hEab hcardE
  by_contra hne
  have hcentr : (L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀))) ⊓
      Subgroup.centralizer (Ē : Set (X ⧸ GLAPPrimeCoreOf 3 L₀)) =
      (L₀ ⊓ Subgroup.centralizer (E : Set X)).map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) := by
    rw [← hEmap]
    exact i1426_map_inf_centralizer Nat.prime_three _ hN (Subgroup.map_subtype_le _)
      (isPGroup_of_isElemAbelian hEab)
  obtain ⟨J', hJ'c, hJ'ne⟩ := i1426_exists_ne_bot_component hne
  rw [hcentr] at hJ'c
  obtain ⟨J, hJc, hJJ'⟩ := exists_glaPComponent_map_eq Nat.prime_three _
    (i1426_coprime_ker _ hN (L₀ ⊓ Subgroup.centralizer (E : Set X))) hJ'c
  have hJle := i1426_le_layer hJc
  rw [hL, le_bot_iff] at hJle
  apply hJ'ne
  rw [← hJJ', hJle, Subgroup.map_bot]

private theorem i1426_x_centralizer {X : Type} [Group X] [Finite X] (L₀ : Subgroup X) [L₀.Normal]
    (B₀ : Subgroup X) (hB : IsElemAbelian 3 B₀) {x : X} (hxB : x ∈ B₀) (hx1 : x ≠ 1)
    (hxC : ∀ l ∈ L₀, x * l = l * x) :
    B₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) ⊓
      Subgroup.centralizer ((L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) :
        Subgroup (X ⧸ GLAPPrimeCoreOf 3 L₀)) : Set (X ⧸ GLAPPrimeCoreOf 3 L₀)) ≠ ⊥ := by
  have hN : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 L₀) := not_dvd_card_glaPPrimeCoreOf Nat.prime_three L₀
  have hψx : QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀) x ≠ 1 := fun h => hx1
    (i1426_inj_of_coprime Nat.prime_three hN hB x hxB ((QuotientGroup.eq_one_iff x).1 h))
  have hmem : QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀) x ∈
      B₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) ⊓
      Subgroup.centralizer ((L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) :
        Subgroup (X ⧸ GLAPPrimeCoreOf 3 L₀)) : Set (X ⧸ GLAPPrimeCoreOf 3 L₀)) := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem _ hxB,
      Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hh
    rw [← map_mul, ← map_mul, hxC l hl]
  intro hbot
  rw [hbot] at hmem
  exact hψx (Subgroup.mem_bot.1 hmem)

private theorem i1426_M12 {X : Type} [Group X] [Finite X] (L₀ : Subgroup X) [L₀.Normal]
    (B₀ : Subgroup X)
    (hq : catalogIs (PSimple 3 L₀) isM12 → ∃ U : Subgroup X, U ≤ L₀ ∧ IsPGroup 2 U ∧
      B₀ ≤ Subgroup.normalizer (U : Set X) ∧ ¬ U ≤ GLAPPrimeCoreOf 3 L₀) :
    catalogIs (↥(L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀))) ⧸
        Subgroup.center ↥(L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)))) isM12 →
      ∃ U : Subgroup (X ⧸ GLAPPrimeCoreOf 3 L₀), U ≤ L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀))
        ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
        B₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) ≤
          Subgroup.normalizer (U : Set (X ⧸ GLAPPrimeCoreOf 3 L₀)) := by
  intro hsc
  obtain ⟨e⟩ := i1426_kb_iso L₀
  obtain ⟨f⟩ := i1426_quotCenter e.symm
  obtain ⟨U, hUL, hUp, hUB, hUnot⟩ := hq (i1426_catalogIs_congr f isM12 hsc)
  refine ⟨U.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)), Subgroup.map_mono hUL, ?_,
    hUp.map _, ?_⟩
  · intro hbot
    apply hUnot
    intro u hu
    have h1 : QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀) u ∈
        U.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) := Subgroup.mem_map_of_mem _ hu
    rw [hbot] at h1
    exact (QuotientGroup.eq_one_iff u).1 (Subgroup.mem_bot.1 h1)
  · intro y hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hy
    exact i1426_normalizes_map _ U b (hUB hb)

private theorem i1426_pullback_map {X : Type} [Group X] (L₀ B₀ : Subgroup X) [L₀.Normal]
    (Ā : Subgroup (X ⧸ GLAPPrimeCoreOf 3 L₀))
    (hĀ : Ā ≤ B₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀))) :
    (B₀ ⊓ Ā.comap (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀))).map
      (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) = Ā := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_comap.1 hx.2
  · intro a ha
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.1 (hĀ ha)
    exact Subgroup.mem_map.2 ⟨b, ⟨hb, Subgroup.mem_comap.2 (by rw [hba]; exact ha)⟩, hba⟩

private theorem i1426_pullback_centralizer {X : Type} [Group X] [Finite X] (L₀ B₀ : Subgroup X)
    [L₀.Normal] (hB : IsElemAbelian 3 B₀)
    (Ā : Subgroup (X ⧸ GLAPPrimeCoreOf 3 L₀))
    (hĀ : Ā ≤ B₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀))) :
    (L₀ ⊓ Subgroup.centralizer ((B₀ ⊓ Ā.comap (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) :
        Subgroup X) : Set X)).map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) =
      L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) ⊓ Subgroup.centralizer (Ā : Set _) := by
  have hN : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 L₀) := not_dvd_card_glaPPrimeCoreOf Nat.prime_three L₀
  have hP : IsPGroup 3 ↥(B₀ ⊓ Ā.comap (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) : Subgroup X) :=
    isPGroup_of_isElemAbelian (isElemAbelian_mono hB inf_le_left)
  have h := i1426_map_inf_centralizer Nat.prime_three (GLAPPrimeCoreOf 3 L₀) hN
    (Subgroup.map_subtype_le _) hP
  rw [i1426_pullback_map L₀ B₀ Ā hĀ] at h
  exact h.symm

private theorem i1426_components_of_layer {X : Type} [Group X] [Finite X] (L₀ B₀ : Subgroup X)
    [L₀.Normal] (hB : IsElemAbelian 3 B₀)
    (Ā : Subgroup (X ⧸ GLAPPrimeCoreOf 3 L₀))
    (hĀ : Ā ≤ B₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)))
    (hJ : GLAPComponent 3 (L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) ⊓
      Subgroup.centralizer (Ā : Set _)) (GLAPLayer 3 (L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) ⊓
      Subgroup.centralizer (Ā : Set _)))) :
    ∃ J₀ : Subgroup X,
      GLAPComponent 3 (L₀ ⊓ Subgroup.centralizer ((B₀ ⊓ Ā.comap
        (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) : Subgroup X) : Set X)) J₀ ∧
      J₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) = GLAPLayer 3
        (L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) ⊓ Subgroup.centralizer (Ā : Set _)) ∧
      ∀ J, GLAPComponent 3 (L₀ ⊓ Subgroup.centralizer ((B₀ ⊓ Ā.comap
        (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) : Subgroup X) : Set X)) J → J = J₀ := by
  have hp := Nat.prime_three
  have hN : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 L₀) := not_dvd_card_glaPPrimeCoreOf Nat.prime_three L₀
  set Yb := L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) ⊓ Subgroup.centralizer (Ā : Set _)
    with hYb
  set Z := L₀ ⊓ Subgroup.centralizer ((B₀ ⊓ Ā.comap
    (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) : Subgroup X) : Set X) with hZ
  have hall_bar : ∀ J', GLAPComponent 3 Yb J' → J' = GLAPLayer 3 Yb := fun J' hJ' =>
    i1426_component_eq_of_le hp hJ hJ' (i1426_le_layer hJ')
  have hZmap : Z.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) = Yb :=
    i1426_pullback_centralizer L₀ B₀ hB Ā hĀ
  have hcop : Nat.Coprime 3 (Nat.card ↥(Z ⊓ (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)).ker)) :=
    i1426_coprime_ker _ hN Z
  have hJ' : GLAPComponent 3 (Z.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)))
      (GLAPLayer 3 Yb) := by
    rw [hZmap]
    exact hJ
  obtain ⟨J₀, hJ₀c, hJ₀m⟩ := exists_glaPComponent_map_eq hp _ hcop hJ'
  refine ⟨J₀, hJ₀c, hJ₀m, fun J hJc => ?_⟩
  have hJψ : GLAPComponent 3 (Z.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)))
      (J.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀))) := glaPComponent_map hp _ hcop hJc
  rw [hZmap] at hJψ
  have heq : J.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) =
      J₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) := by
    rw [hall_bar _ hJψ, hJ₀m]
  exact i1426_component_unique_of_map hp _ hN hJc hJ₀c heq

private theorem i1426_normalizer_of_unique {X : Type} [Group X] {p : ℕ} {Z J₀ : Subgroup X}
    (hJ₀ : GLAPComponent p Z J₀) (hall : ∀ J, GLAPComponent p Z J → J = J₀) {g : X}
    (hg : g ∈ Subgroup.normalizer (Z : Set X)) : g ∈ Subgroup.normalizer (J₀ : Set X) := by
  have h1 := glaPComponent_gLBConj hJ₀ g
  rw [mem_normalizer_iff_gLBConj_eq.1 hg] at h1
  exact mem_normalizer_iff_gLBConj_eq.2 (hall _ h1)

private theorem i1426_normalizes_centralizer {X : Type} [Group X] (L₀ B₀ A : Subgroup X)
    [L₀.Normal] (hB : IsElemAbelian 3 B₀) (hA : A ≤ B₀) {b : X} (hb : b ∈ B₀) :
    b ∈ Subgroup.normalizer ((L₀ ⊓ Subgroup.centralizer (A : Set X) : Subgroup X) : Set X) := by
  have hconj : ∀ c ∈ B₀, ∀ z ∈ L₀ ⊓ Subgroup.centralizer (A : Set X), c * z * c⁻¹ ∈
      L₀ ⊓ Subgroup.centralizer (A : Set X) := by
    intro c hc z hz
    refine ⟨Subgroup.Normal.conj_mem inferInstance z hz.1 c, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    have hab : c * a = a * c := isElemAbelian_commute hB hc (hA ha)
    have hza : a * z = z * a := (Subgroup.mem_centralizer_iff.1 hz.2) a ha
    calc a * (c * z * c⁻¹) = (a * c) * z * c⁻¹ * (c * c⁻¹) := by group
      _ = (c * a) * z * c⁻¹ := by rw [← hab]; group
      _ = c * (a * z) * c⁻¹ := by group
      _ = c * (z * a) * c⁻¹ := by rw [hza]
      _ = (c * z * c⁻¹) * (c * a * c⁻¹) * (c * c⁻¹) := by group
      _ = (c * z * c⁻¹) * (a * c * c⁻¹) := by rw [← hab]; group
      _ = (c * z * c⁻¹) * a := by group
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact hconj b hb h
  · intro hh
    have h2 := hconj b⁻¹ (B₀.inv_mem hb) _ hh
    have h3 : b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = h := by group
    rw [h3] at h2
    exact h2

private theorem i1426_normalizer_inf {X : Type} [Group X] {g : X} {A B : Subgroup X}
    (hA : g ∈ Subgroup.normalizer (A : Set X)) (hB : g ∈ Subgroup.normalizer (B : Set X)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA h, hB h]

private theorem i1426_two_lift {X : Type} [Group X] [Finite X] (L₀ B₀ J₀ : Subgroup X)
    [L₀.Normal] (hB : IsElemAbelian 3 B₀) (T : Subgroup (X ⧸ GLAPPrimeCoreOf 3 L₀))
    (hJT : T ≤ J₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)))
    (hT : IsElemAbelian 2 T) (hT4 : Nat.card T = 4)
    (hBJ : B₀ ≤ Subgroup.normalizer (J₀ : Set X))
    (hBT : B₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) ≤
      Subgroup.normalizer (T : Set (X ⧸ GLAPPrimeCoreOf 3 L₀))) :
    ∃ T' : Subgroup X, T' ≤ J₀ ∧ IsPGroup 2 T' ∧ B₀ ≤ Subgroup.normalizer (T' : Set X) ∧
      T'.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) = T := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 L₀) := not_dvd_card_glaPPrimeCoreOf Nat.prime_three L₀
  set ψ := QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀) with hψ
  set P : Subgroup X := J₀ ⊓ T.comap ψ with hPdef
  have hPT : P.map ψ = T := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_comap.1 hx.2
    · intro t ht
      obtain ⟨j, hj, hjt⟩ := Subgroup.mem_map.1 (hJT ht)
      exact Subgroup.mem_map.2 ⟨j, ⟨hj, Subgroup.mem_comap.2 (by rw [hjt]; exact ht)⟩, hjt⟩
  have hPJ : P ≤ J₀ := inf_le_left
  have hBP : B₀ ≤ Subgroup.normalizer (P : Set X) := by
    intro b hb
    have h2 : b ∈ Subgroup.normalizer ((T.comap ψ : Subgroup X) : Set X) := by
      have hbT := Subgroup.mem_normalizer_iff.1 (hBT (Subgroup.mem_map_of_mem ψ hb))
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact hbT (ψ h)
    exact i1426_normalizer_inf (hBJ hb) h2
  have hP3 : ¬ 3 ∣ Nat.card P := by
    intro h3
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 3 h3
    have hg3 : (g : X) ^ 3 = 1 := by
      have := pow_orderOf_eq_one g
      rw [hg] at this
      simpa using congrArg Subtype.val this
    have hψg : ψ (g : X) ∈ T := by
      have : ψ (g : X) ∈ P.map ψ := Subgroup.mem_map_of_mem _ g.2
      rwa [hPT] at this
    have h2 : ψ (g : X) ^ 2 = 1 := hT.2 _ hψg
    have h3' : ψ (g : X) ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
    have hψ1 : ψ (g : X) = 1 := by
      calc ψ (g : X) = ψ (g : X) ^ 3 * (ψ (g : X) ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3', h2]; simp
    have hgN : (g : X) ∈ GLAPPrimeCoreOf 3 L₀ := (QuotientGroup.eq_one_iff _).1 hψ1
    have ho : orderOf (g : X) = 3 := by rw [Subgroup.orderOf_coe, hg]
    have hdv := orderOf_dvd_natCard (⟨(g : X), hgN⟩ : ↥(GLAPPrimeCoreOf 3 L₀))
    rw [Subgroup.orderOf_mk, ho] at hdv
    exact hN hdv
  obtain ⟨Ps, hPs⟩ := exists_sylow_normalized (r := 2) (p := 3) (W := P) (S := B₀) hBP
    (isPGroup_of_isElemAbelian hB) hP3
  refine ⟨(Ps : Subgroup P).map P.subtype, (Subgroup.map_subtype_le _).trans hPJ,
    Ps.isPGroup'.map P.subtype, hPs, ?_⟩
  set φ : P →* (X ⧸ GLAPPrimeCoreOf 3 L₀) := ψ.comp P.subtype with hφ
  have hφrange : φ.range = T := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype, hPT]
  set R : Subgroup (X ⧸ GLAPPrimeCoreOf 3 L₀) := (Ps : Subgroup P).map φ with hR
  have hT'R : ((Ps : Subgroup P).map P.subtype).map ψ = R := by
    rw [hR, Subgroup.map_map]
  have hRT : R ≤ T := by
    rw [← hφrange]
    exact Subgroup.map_le_range _ _
  have hPsM : Ps ≤ R.comap φ := fun g hg => Subgroup.mem_comap.2 (Subgroup.mem_map_of_mem _ hg)
  have hodd : ¬ 2 ∣ (R.comap φ).index := fun h =>
    Sylow.not_dvd_index Ps (h.trans (Subgroup.index_dvd_of_le hPsM))
  have hind : (R.comap φ).index = R.relIndex T := by
    rw [Subgroup.index_comap, hφrange]
  have hdvd : R.relIndex T ∣ 2 ^ 2 := by
    have h4 : Nat.card T = 4 := hT4
    have := Subgroup.index_dvd_card (R.subgroupOf T)
    rw [h4] at this
    exact this
  have hd1 : R.relIndex T = 1 := by
    have h2 : ¬ 2 ∣ R.relIndex T := hind ▸ hodd
    obtain ⟨i, hi, hd⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    interval_cases i
    · simpa using hd
    · rw [hd] at h2; norm_num at h2
    · rw [hd] at h2; norm_num at h2
  have hRT' : T ≤ R := Subgroup.relIndex_eq_one.1 hd1
  rw [hT'R, le_antisymm hRT hRT']

private theorem i1426_comm_of_core {X Y : Type} [Group X] [Group Y] (ψ : X →* Y) {j b : X}
    (h : ψ (⁅j, b⁆) = 1) : ψ j * ψ b = ψ b * ψ j := by
  rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv] at h
  calc ψ j * ψ b = (ψ j * ψ b * (ψ j)⁻¹ * (ψ b)⁻¹) * (ψ b * ψ j) := by group
    _ = ψ b * ψ j := by rw [h, one_mul]

private theorem i1426_core_le {X : Type} [Group X] [Finite X] (L₀ J₀ : Subgroup X) [L₀.Normal]
    (hO : GLAPPrimeCore 3 ↥(J₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀))) = ⊥) :
    GLAPPrimeCoreOf 3 J₀ ≤ GLAPPrimeCoreOf 3 L₀ := by
  have hN : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 L₀) := not_dvd_card_glaPPrimeCoreOf Nat.prime_three L₀
  set ψ := QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀) with hψ
  let f : ↥J₀ →* ↥(J₀.map ψ) :=
    (ψ.comp J₀.subtype).codRestrict (J₀.map ψ) (fun x => Subgroup.mem_map_of_mem _ x.2)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hfker : ∀ x ∈ f.ker, (x : X) ∈ GLAPPrimeCoreOf 3 L₀ := by
    intro x hx
    have h1 : ψ (x : X) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      simpa [f] using this
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hker : Nat.Coprime 3 (Nat.card f.ker) := by
    have h1 : f.ker.map J₀.subtype ≤ GLAPPrimeCoreOf 3 L₀ := by
      rintro _ ⟨x, hx, rfl⟩
      exact hfker x hx
    have h2 : Nat.card (f.ker.map J₀.subtype) = Nat.card f.ker :=
      Subgroup.card_map_of_injective J₀.subtype_injective
    rw [← h2]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h =>
      hN (h.trans (Subgroup.card_dvd_of_le h1))
  have hmap := glaPPrimeCore_map_of_surjective Nat.prime_three f hf hker
  rw [hO] at hmap
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
  have hfw : f w ∈ (GLAPPrimeCore 3 ↥J₀).map f := Subgroup.mem_map_of_mem _ hw
  rw [hmap] at hfw
  exact hfker w (by rw [MonoidHom.mem_ker]; exact Subgroup.mem_bot.1 hfw)

private theorem i1426_centMod_iff {X : Type} [Group X] [Finite X] (L₀ B₀ J₀ : Subgroup X)
    [L₀.Normal] (Ā : Subgroup (X ⧸ GLAPPrimeCoreOf 3 L₀))
    (hJ₀ : J₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) = GLAPLayer 3
      (L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) ⊓ Subgroup.centralizer (Ā : Set _)))
    (hcore : GLAPPrimeCoreOf 3 J₀ ≤ GLAPPrimeCoreOf 3 L₀)
    (hcent : ∀ y ∈ B₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)),
      y ∈ Subgroup.centralizer ((GLAPLayer 3
        (L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) ⊓ Subgroup.centralizer (Ā : Set _)) :
          Subgroup (X ⧸ GLAPPrimeCoreOf 3 L₀)) : Set (X ⧸ GLAPPrimeCoreOf 3 L₀)) ↔ y ∈ Ā)
    (hBJ : B₀ ≤ Subgroup.normalizer (J₀ : Set X)) {b : X} (hb : b ∈ B₀) :
    CentMod 3 J₀ b ↔ b ∈ B₀ ⊓ Ā.comap (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) := by
  have hp := Nat.prime_three
  have hN : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 L₀) := not_dvd_card_glaPPrimeCoreOf Nat.prime_three L₀
  set ψ := QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀) with hψ
  have hJmem : ∀ j ∈ J₀, ψ j ∈ GLAPLayer 3 (L₀.map ψ ⊓ Subgroup.centralizer (Ā : Set _)) := by
    intro j hj
    rw [← hJ₀]
    exact Subgroup.mem_map_of_mem _ hj
  constructor
  · rintro ⟨hbN, hcomm⟩
    have hbC : ψ b ∈ Subgroup.centralizer ((GLAPLayer 3
        (L₀.map ψ ⊓ Subgroup.centralizer (Ā : Set _)) : Subgroup (X ⧸ GLAPPrimeCoreOf 3 L₀)) :
          Set (X ⧸ GLAPPrimeCoreOf 3 L₀)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [← hJ₀] at hh
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hh
      have hc : ⁅j, b⁆ ∈ GLAPPrimeCoreOf 3 L₀ :=
        hcore (hcomm (Subgroup.commutator_mem_commutator hj (Subgroup.mem_zpowers b)))
      have h1 : ψ (⁅j, b⁆) = 1 := (QuotientGroup.eq_one_iff _).2 hc
      exact i1426_comm_of_core ψ h1
    have hbĀ : ψ b ∈ Ā := (hcent _ (Subgroup.mem_map_of_mem _ hb)).1 hbC
    exact Subgroup.mem_inf.2 ⟨hb, Subgroup.mem_comap.2 hbĀ⟩
  · rintro hbA
    have hbĀ : ψ b ∈ Ā := Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hbA).2
    have hbC := (hcent _ (Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.1 hbA).1)).2 hbĀ
    refine ⟨hBJ hb, Subgroup.commutator_le.2 fun j hj g hg => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    have hcomm : ψ j * ψ b ^ n = ψ b ^ n * ψ j := by
      have hjC := (Subgroup.mem_centralizer_iff.1 hbC) (ψ j) (hJmem j hj)
      exact ((Commute.zpow_right (show Commute (ψ j) (ψ b) from hjC) n)).eq
    have hgN : ⁅j, b ^ n⁆ ∈ GLAPPrimeCoreOf 3 L₀ := by
      have h1 : ψ (⁅j, b ^ n⁆) = 1 := by
        rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, map_zpow, hcomm]
        group
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hgJ : ⁅j, b ^ n⁆ ∈ J₀ := by
      have hnorm : b ^ n ∈ Subgroup.normalizer (J₀ : Set X) :=
        (Subgroup.normalizer (J₀ : Set X)).zpow_mem (hBJ hb) n
      have h2 : b ^ n * j⁻¹ * (b ^ n)⁻¹ ∈ J₀ :=
        (Subgroup.mem_normalizer_iff.1 hnorm j⁻¹).1 (J₀.inv_mem hj)
      have e : ⁅j, b ^ n⁆ = j * (b ^ n * j⁻¹ * (b ^ n)⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact J₀.mul_mem hj h2
    exact i1426_mem_core_of_mem Nat.prime_three (GLAPPrimeCoreOf 3 L₀) hN hgJ hgN

private theorem i1426_pQuot_embed {X : Type} [Group X] [Finite X] (L₀ J₀ : Subgroup X) [L₀.Normal]
    (hcore : GLAPPrimeCoreOf 3 J₀ ≤ GLAPPrimeCoreOf 3 L₀) :
    ∃ Φ : PQuot 3 J₀ →* (X ⧸ GLAPPrimeCoreOf 3 L₀), Function.Injective Φ ∧
      ∀ x : ↥J₀, Φ (QuotientGroup.mk x) = QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀) (x : X) := by
  have hp := Nat.prime_three
  have hN : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 L₀) := not_dvd_card_glaPPrimeCoreOf Nat.prime_three L₀
  set ψ := QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀) with hψ
  have hle : GLAPPrimeCore 3 ↥J₀ ≤ (ψ.comp J₀.subtype).ker := by
    intro w hw
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hψ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hcore (Subgroup.mem_map_of_mem _ hw)
  let Φ : PQuot 3 J₀ →* (X ⧸ GLAPPrimeCoreOf 3 L₀) := QuotientGroup.lift _ (ψ.comp J₀.subtype) hle
  refine ⟨Φ, ?_, fun x => rfl⟩
  rw [injective_iff_map_eq_one]
  intro q hq
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  have hw : (w : X) ∈ GLAPPrimeCoreOf 3 J₀ := by
    have h1 : ψ (w : X) = 1 := by
      have := hq
      rw [show Φ (QuotientGroup.mk w) = ψ (w : X) from rfl] at this
      exact this
    have hwN : (w : X) ∈ GLAPPrimeCoreOf 3 L₀ := (QuotientGroup.eq_one_iff _).1 h1
    exact i1426_mem_core_of_mem hp _ hN w.2 hwN
  obtain ⟨w', hw', hw'eq⟩ := Subgroup.mem_map.1 hw
  have : w' = w := Subtype.ext hw'eq
  rw [← this]
  exact QuotientGroup.eq_one_iff _ |>.2 hw'

private theorem i1426_imageMod_map {X : Type} [Group X] (L₀ J₀ T : Subgroup X) [L₀.Normal]
    (hT : T ≤ J₀) {Φ : PQuot 3 J₀ →* (X ⧸ GLAPPrimeCoreOf 3 L₀)}
    (hΦ : ∀ x : ↥J₀, Φ (QuotientGroup.mk x) = QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀) (x : X)) :
    (imageMod 3 J₀ T).map Φ = T.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) := by
  unfold imageMod
  rw [Subgroup.map_map]
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [show (Φ.comp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J₀))) t =
      QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀) (t : X) from hΦ t]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.1 ht)
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, hT ht⟩, Subgroup.mem_subgroupOf.2 ht, hΦ ⟨t, hT ht⟩⟩

private theorem i1426_pgroup_of_le {X : Type} [Group X] [Finite X] {p : ℕ} {K H : Subgroup X}
    (hK : IsPGroup p K) (hHK : H ≤ K) : IsPGroup p H := by
  obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.1 hK
  exact IsPGroup.of_card_dvd_pow ((Subgroup.card_dvd_of_le hHK).trans hn)

private theorem i1426_comm_comm {X : Type} [Group X] [Finite X] (B T : Subgroup X)
    (hB : IsElemAbelian 3 B) (hT : IsPGroup 2 T) (hN : B ≤ Subgroup.normalizer (T : Set X)) :
    ⁅⁅T, B⁆, B⁆ = ⁅T, B⁆ := by
  have hcop : Nat.Coprime 3 (Nat.card T) := by
    obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.1 hT
    exact (Nat.Coprime.coprime_dvd_left hn (Nat.Coprime.pow_left n (by norm_num))).symm
  have hBp : IsPGroup 3 B := isPGroup_of_isElemAbelian hB
  have hres : ∀ N : Subgroup X, N ≤ B → (N.subgroupOf B).Normal →
      Nat.Coprime 3 (N.subgroupOf B).index → N = B := by
    intro N hNB hNn hcop'
    obtain ⟨n, hn⟩ := (isPGroup_of_isElemAbelian hB).index (N.subgroupOf B)
    rw [hn] at hcop'
    have h1 : (N.subgroupOf B).index = 1 := by
      rcases n with _ | n
      · simpa using hn
      · exact absurd (Nat.Coprime.eq_one_of_dvd hcop' (dvd_pow_self 3 (Nat.succ_ne_zero n)))
          (by norm_num)
    have htop : N.subgroupOf B = ⊤ := Subgroup.index_eq_one.1 h1
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact le_antisymm hNB htop
  exact i321UsedAt_holds (G := X) 3 Nat.prime_three T B hcop hN hres

private theorem i1426_xlevel {X : Type} [Group X] [Finite X] (L₀ B₀ : Subgroup X) [L₀.Normal]
    (hB : IsElemAbelian 3 B₀)
    (Ā : Subgroup (X ⧸ GLAPPrimeCoreOf 3 L₀))
    (hĀ : Ā ≤ B₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)))
    (hĀab : IsElemAbelian 3 Ā) (hĀcard : Nat.card Ā = 3 ^ 2)
    (hJ : GLAPComponent 3 (L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) ⊓
      Subgroup.centralizer (Ā : Set (X ⧸ GLAPPrimeCoreOf 3 L₀))) (GLAPLayer 3
      (L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) ⊓
        Subgroup.centralizer (Ā : Set (X ⧸ GLAPPrimeCoreOf 3 L₀)))))
    (hcat : catalogIs (PSimple 3 (GLAPLayer 3
      (L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) ⊓
        Subgroup.centralizer (Ā : Set (X ⧸ GLAPPrimeCoreOf 3 L₀))))) k3NoA10)
    (hcent : ∀ y ∈ B₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)),
      y ∈ Subgroup.centralizer ((GLAPLayer 3
        (L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) ⊓
          Subgroup.centralizer (Ā : Set (X ⧸ GLAPPrimeCoreOf 3 L₀))) :
            Subgroup (X ⧸ GLAPPrimeCoreOf 3 L₀)) : Set (X ⧸ GLAPPrimeCoreOf 3 L₀)) ↔ y ∈ Ā)
    (T : Subgroup (X ⧸ GLAPPrimeCoreOf 3 L₀))
    (hT : T ≤ GLAPLayer 3 (L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) ⊓
      Subgroup.centralizer (Ā : Set (X ⧸ GLAPPrimeCoreOf 3 L₀))))
    (hTab : IsElemAbelian 2 T) (hT4 : Nat.card T = 4)
    (hBT : B₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) ≤
      Subgroup.normalizer (T : Set (X ⧸ GLAPPrimeCoreOf 3 L₀)))
    (hTc : ⁅B₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)), T⁆ = T)
    (hO : GLAPPrimeCore 3 ↥(GLAPLayer 3 (L₀.map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) ⊓
      Subgroup.centralizer (Ā : Set (X ⧸ GLAPPrimeCoreOf 3 L₀)))) = ⊥) :
    (B₀ ⊓ Ā.comap (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀))) ≤ B₀ ∧
    IsElemAbelian 3 (B₀ ⊓ Ā.comap (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀))) ∧
    Nat.card ↥(B₀ ⊓ Ā.comap (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) : Subgroup X) = 3 ^ 2 ∧
    (B₀ ⊓ Ā.comap (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀))).map
      (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) = Ā ∧
    ∃ J₀ T₁ : Subgroup X,
      GLAPComponent 3 (L₀ ⊓ Subgroup.centralizer ((B₀ ⊓ Ā.comap
        (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) : Subgroup X) : Set X)) J₀ ∧
      (∀ J, GLAPComponent 3 (L₀ ⊓ Subgroup.centralizer ((B₀ ⊓ Ā.comap
        (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) : Subgroup X) : Set X)) J → J = J₀) ∧
      catalogIs (PSimple 3 J₀) k3NoA10 ∧
      (∀ b ∈ B₀, CentMod 3 J₀ b ↔ b ∈ B₀ ⊓ Ā.comap (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀))) ∧
      T₁ ≤ J₀ ∧ IsPGroup 2 T₁ ∧ B₀ ≤ Subgroup.normalizer (T₁ : Set X) ∧ ⁅B₀, T₁⁆ = T₁ ∧
      (∃ Φ : PQuot 3 J₀ →* (X ⧸ GLAPPrimeCoreOf 3 L₀), Function.Injective Φ ∧
        (imageMod 3 J₀ T₁).map Φ = T) ∧
      GLAPPrimeCoreOf 3 J₀ ≤ GLAPPrimeCoreOf 3 L₀ := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hN : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 L₀) := not_dvd_card_glaPPrimeCoreOf Nat.prime_three L₀
  have hÂle : B₀ ⊓ Ā.comap (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) ≤ B₀ := inf_le_left
  have hÂab : IsElemAbelian 3 (B₀ ⊓ Ā.comap (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀))) :=
    isElemAbelian_mono hB inf_le_left
  have hÂmap := i1426_pullback_map L₀ B₀ Ā hĀ
  have hÂcard : Nat.card ↥(B₀ ⊓ Ā.comap (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) : Subgroup X) = 3 ^ 2 := by
    have h1 := i1426_card_map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀))
      (B₀ ⊓ Ā.comap (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀))) (fun x hx hx1 =>
        i1426_inj_of_coprime hp hN hB x (hÂle hx) ((QuotientGroup.eq_one_iff x).1 hx1))
    rw [hÂmap, hĀcard] at h1
    exact h1.symm
  obtain ⟨J₀, hJ₀c, hJ₀m, hall⟩ := i1426_components_of_layer L₀ B₀ hB Ā hĀ hJ
  have hcore : GLAPPrimeCoreOf 3 J₀ ≤ GLAPPrimeCoreOf 3 L₀ :=
    i1426_core_le L₀ J₀ (by rw [hJ₀m]; exact hO)
  have hBZ : ∀ b ∈ B₀, b ∈ Subgroup.normalizer ((L₀ ⊓ Subgroup.centralizer
      ((B₀ ⊓ Ā.comap (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) : Subgroup X) : Set X) :
        Subgroup X) : Set X) := fun b hb =>
    i1426_normalizes_centralizer L₀ B₀ _ hB hÂle hb
  have hBJ : B₀ ≤ Subgroup.normalizer (J₀ : Set X) := fun b hb =>
    i1426_normalizer_of_unique hJ₀c hall (hBZ b hb)
  have hcat' : catalogIs (PSimple 3 J₀) k3NoA10 := by
    obtain ⟨e⟩ := nonempty_pQuot_equiv_map (ψ := QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) hp
      (by rw [QuotientGroup.ker_mk']; exact hN) J₀
    obtain ⟨f⟩ := i1426_quotCenter e
    rw [← hJ₀m] at hcat
    exact i1426_catalogIs_congr f.symm _ hcat
  have hCM : ∀ b ∈ B₀, CentMod 3 J₀ b ↔
      b ∈ B₀ ⊓ Ā.comap (QuotientGroup.mk' (GLAPPrimeCoreOf 3 L₀)) := fun b hb =>
    i1426_centMod_iff L₀ B₀ J₀ Ā hJ₀m hcore hcent hBJ hb
  obtain ⟨T₁', hT₁'J, hT₁'2, hT₁'N, hT₁'map⟩ := i1426_two_lift L₀ B₀ J₀ hB T
    (by rw [hJ₀m]; exact hT) hTab hT4 hBJ hBT
  have hcomm321 : ⁅B₀, ⁅T₁', B₀⁆⁆ = ⁅T₁', B₀⁆ := by
    rw [Subgroup.commutator_comm]
    exact i1426_comm_comm B₀ T₁' hB hT₁'2 hT₁'N
  set T₁ : Subgroup X := ⁅T₁', B₀⁆ with hT₁
  have hT₁J : T₁ ≤ J₀ := by
    refine Subgroup.commutator_le.2 fun t ht b hb => ?_
    have e : ⁅t, b⁆ = t * (b * t⁻¹ * b⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact J₀.mul_mem (hT₁'J ht) ((Subgroup.mem_normalizer_iff.1 (hBJ hb) t⁻¹).1
      (J₀.inv_mem (hT₁'J ht)))
  have hT₁le : T₁ ≤ T₁' := by
    refine Subgroup.commutator_le.2 fun t ht b hb => ?_
    have e : ⁅t, b⁆ = t * (b * t⁻¹ * b⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact T₁'.mul_mem ht ((Subgroup.mem_normalizer_iff.1 (hT₁'N hb) t⁻¹).1
      (T₁'.inv_mem ht))
  have hT₁2 : IsPGroup 2 T₁ := i1426_pgroup_of_le hT₁'2 hT₁le
  have hBT₁ : ⁅B₀, T₁⁆ = T₁ := hcomm321
  have hT₁N : B₀ ≤ Subgroup.normalizer (T₁ : Set X) := by
    have hconj : ∀ b ∈ B₀, ∀ t ∈ T₁, b * t * b⁻¹ ∈ T₁ := by
      intro b hb t ht
      have h1 : ⁅b, t⁆ ∈ T₁ := by
        have := Subgroup.commutator_mem_commutator hb ht
        rwa [hBT₁] at this
      have e : b * t * b⁻¹ = ⁅b, t⁆ * t := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact T₁.mul_mem h1 ht
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hconj b hb h
    · intro hh
      have h2 := hconj b⁻¹ (B₀.inv_mem hb) _ hh
      have h3 : b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = h := by group
      rw [h3] at h2
      exact h2
  obtain ⟨Φ, hΦinj, hΦ⟩ := i1426_pQuot_embed L₀ J₀ hcore
  refine ⟨hÂle, hÂab, hÂcard, hÂmap, J₀, T₁, hJ₀c, hall, hcat', hCM, hT₁J, hT₁2, hT₁N, hBT₁,
    ⟨Φ, hΦinj, ?_⟩, hcore⟩
  rw [i1426_imageMod_map L₀ J₀ T₁ hT₁J hΦ, hT₁, Subgroup.map_commutator, hT₁'map,
    Subgroup.commutator_comm]
  exact hTc

private theorem i1426_core_map {X G : Type} [Group X] [Group G] {p : ℕ} (s : X →* G)
    (hs : Function.Injective s) (K : Subgroup X) :
    GLAPPrimeCoreOf p (K.map s) = (GLAPPrimeCoreOf p K).map s := by
  let e : ↥K ≃* ↥(K.map s) := Subgroup.equivMapOfInjective K s hs
  have h1 := glaPPrimeCore_map_iso p e
  unfold GLAPPrimeCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem i1426_centMod_map {X G : Type} [Group X] [Group G] {p : ℕ} (s : X →* G)
    (hs : Function.Injective s) (K : Subgroup X) (b : X) :
    CentMod p (K.map s) (s b) ↔ CentMod p K b := by
  unfold CentMod
  rw [i1426_core_map s hs K]
  constructor
  · rintro ⟨hn, hc⟩
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro h
      have hh := Subgroup.mem_normalizer_iff.1 hn (s h)
      have e : s b * s h * (s b)⁻¹ = s (b * h * b⁻¹) := by simp [map_mul, map_inv]
      rw [e, Subgroup.mem_map_iff_mem hs, Subgroup.mem_map_iff_mem hs] at hh
      exact hh
    · rw [← MonoidHom.map_zpowers, ← Subgroup.map_commutator, Subgroup.map_le_map_iff_of_injective hs] at hc
      exact hc
  · rintro ⟨hn, hc⟩
    refine ⟨i1426_normalizes_map s K b hn, ?_⟩
    rw [← MonoidHom.map_zpowers, ← Subgroup.map_commutator, Subgroup.map_le_map_iff_of_injective hs]
    exact hc

private theorem i1426_component_map {X G : Type} [Group X] [Group G] [Finite X] {p : ℕ}
    (hp : p.Prime) (s : X →* G) (hs : Function.Injective s) {Z J : Subgroup X}
    (hJ : GLAPComponent p Z J) : GLAPComponent p (Z.map s) (J.map s) := by
  have hker : s.ker = ⊥ := (MonoidHom.ker_eq_bot_iff s).2 hs
  refine glaPComponent_map hp s ?_ hJ
  rw [hker, inf_bot_eq, Subgroup.card_bot]
  exact Nat.coprime_one_right _

private theorem i1426_pSimple_map {X G : Type} [Group X] [Group G] [Finite X]
    (s : X →* G) (hs : Function.Injective s) (K : Subgroup X) (k : TauCeti.CFSGIndex → Prop)
    (h : catalogIs (PSimple 3 K) k) : catalogIs (PSimple 3 (K.map s)) k := by
  let e : ↥K ≃* ↥(K.map s) := Subgroup.equivMapOfInjective K s hs
  have h1 : Nonempty (PQuot 3 K ≃* PQuot 3 (K.map s)) :=
    ⟨QuotientGroup.congr _ _ e (glaPPrimeCore_map_iso 3 e)⟩
  obtain ⟨f⟩ := h1
  obtain ⟨g⟩ := i1426_quotCenter f
  exact i1426_catalogIs_congr g k h

private theorem i1426_elemAbelian_of_map_inj {X G : Type} [Group X] [Group G] {p : ℕ}
    (s : X →* G) (hs : Function.Injective s) {E : Subgroup X}
    (h : IsElemAbelian p (E.map s)) : IsElemAbelian p E := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hs ?_)⟩⟩, fun x hx => hs ?_⟩
  · simp only [Subgroup.coe_mul, map_mul]
    exact isElemAbelian_commute h (Subgroup.mem_map_of_mem s a.2) (Subgroup.mem_map_of_mem s b.2)
  · rw [map_pow, map_one]
    exact h.2 _ (Subgroup.mem_map_of_mem s hx)

private theorem i1426_normalizer_map_iff {X G : Type} [Group X] [Group G] (s : X →* G)
    (hs : Function.Injective s) (K : Subgroup X) (b : X) :
    s b ∈ Subgroup.normalizer ((K.map s : Subgroup G) : Set G) ↔
      b ∈ Subgroup.normalizer (K : Set X) := by
  constructor
  · intro hn
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hh := Subgroup.mem_normalizer_iff.1 hn (s h)
    have e : s b * s h * (s b)⁻¹ = s (b * h * b⁻¹) := by simp [map_mul, map_inv]
    rw [e, Subgroup.mem_map_iff_mem hs, Subgroup.mem_map_iff_mem hs] at hh
    exact hh
  · exact i1426_normalizes_map s K b

private theorem i1426_map_inf_centralizer_subtype {G : Type} [Group G] {H K : Subgroup G}
    (hKH : K ≤ H) {S : Subgroup H} :
    ((K.subgroupOf H) ⊓ Subgroup.centralizer (S : Set H)).map H.subtype =
      K ⊓ Subgroup.centralizer ((S.map H.subtype : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyK, hyC⟩, rfl⟩
    refine ⟨Subgroup.mem_subgroupOf.1 hyK, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨e, he, rfl⟩
    have h := congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hyC e he)
    simpa using h
  · rintro ⟨hxK, hxC⟩
    refine ⟨⟨x, hKH hxK⟩, ⟨Subgroup.mem_subgroupOf.2 hxK, Subgroup.mem_centralizer_iff.2 ?_⟩, rfl⟩
    intro e he
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 hxC (e : G) (Subgroup.mem_map_of_mem H.subtype he)

private theorem i1426_imageMod_iso {X G : Type} [Group X] [Group G] (s : X →* G)
    (hs : Function.Injective s) (J T : Subgroup X) :
    ∃ ε : PQuot 3 (J.map s) ≃* PQuot 3 J,
      (imageMod 3 (J.map s) (T.map s)).map (ε : PQuot 3 (J.map s) →* PQuot 3 J) =
        imageMod 3 J T := by
  let e : ↥J ≃* ↥(J.map s) := Subgroup.equivMapOfInjective J s hs
  refine ⟨QuotientGroup.congr _ _ e.symm (glaPPrimeCore_map_iso 3 e.symm), ?_⟩
  unfold imageMod
  rw [Subgroup.map_map]
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzT : ((e.symm z : ↥J) : X) ∈ T := by
      obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hz)
      have hts' : s t = s ((e.symm z : ↥J) : X) := hts.trans (congrArg Subtype.val
        (e.apply_symm_apply z)).symm
      have : t = ((e.symm z : ↥J) : X) := hs hts'
      rw [← this]
      exact ht
    exact ⟨e.symm z, Subgroup.mem_subgroupOf.2 hzT, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨e t, Subgroup.mem_subgroupOf.2
      (Subgroup.mem_map_of_mem s (Subgroup.mem_subgroupOf.1 ht)), ?_⟩
    show QuotientGroup.mk (e.symm (e t)) = QuotientGroup.mk t
    rw [e.symm_apply_apply]

private theorem i1426_subgroupOf_map_subtype {G : Type} [Group G] {H : Subgroup G}
    (Z : Subgroup H) : (Z.map H.subtype).subgroupOf H = Z := by
  ext z
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hz
    obtain ⟨z', hz', hz'eq⟩ := Subgroup.mem_map.1 hz
    have : z' = z := Subtype.ext hz'eq
    rw [← this]
    exact hz'
  · intro hz
    exact Subgroup.mem_map_of_mem _ hz

theorem i1426At_of {G : Type} [Group G] [Finite G] (h : KD1426Cat) {p : ℕ} :
    I1426At G p := by
  unfold I1426At
  intro hp3 B x L hB hxB hx1 hcomp hBN hfc hcard hmax hE hM12
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  set H : Subgroup G := L ⊔ B with hH
  have hLH : L ≤ H := le_sup_left
  have hBH : B ≤ H := le_sup_right
  have hxH : x ∈ H := hBH hxB
  haveI hL₀n : (L.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 (sup_le Subgroup.le_normalizer hBN)
  have hinj : Function.Injective H.subtype := H.subtype_injective
  have hB₀map : (B.subgroupOf H).map H.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBH
  have hL₀map : (L.subgroupOf H).map H.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLH
  have hB₀ : IsElemAbelian 3 (B.subgroupOf H) :=
    i1426_elemAbelian_of_map_inj H.subtype hinj (by rw [hB₀map]; exact hB)
  have hcardB₀ : Nat.card (B.subgroupOf H) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
  have hcard₀ : 3 ^ 4 ≤ Nat.card (B.subgroupOf H) := by rw [hcardB₀]; exact hcard
  have hsup : (L.subgroupOf H) ⊔ (B.subgroupOf H) = ⊤ := by
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_sup, hL₀map, hB₀map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmax₀ : IsMaxRankIn 3 (B.subgroupOf H) ⊤ := by
    intro E _ hE'
    have h1 := hmax (E.map H.subtype) (Subgroup.map_subtype_le E)
      (i1426_elemAbelian_map H.subtype hE')
    rw [Subgroup.card_map_of_injective hinj] at h1
    rw [hcardB₀]
    exact h1
  have hx₀ : (⟨x, hxH⟩ : H) ∈ B.subgroupOf H := Subgroup.mem_subgroupOf.2 hxB
  have hx₀1 : (⟨x, hxH⟩ : H) ≠ 1 := fun h' => hx1 (congrArg Subtype.val h')
  have hxC : ∀ l ∈ L.subgroupOf H, (⟨x, hxH⟩ : H) * l = l * (⟨x, hxH⟩ : H) := by
    intro l hl
    apply Subtype.ext
    have hlG : (l : G) ∈ L := Subgroup.mem_subgroupOf.1 hl
    exact Subgroup.mem_centralizer_iff.1 (hcomp.1 hlG) x (Set.mem_singleton x)
  obtain ⟨e₁⟩ := nonempty_pQuot_equiv_subgroupOf 3 hLH
  have hQ : CFSG.Open.IsQuasisimple (PQuot 3 (L.subgroupOf H)) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e₁.symm
      (isQuasisimple_pQuot_of_glaPComponent hp hcomp)
  have hfc₀ : fullCoverLevel 3 (PQuot 3 (L.subgroupOf H)) = 3 :=
    (i1426_fullCoverLevel_congr e₁ 3).trans hfc
  have hEX : ∀ E : Subgroup H, E ≤ B.subgroupOf H → IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      GLAPLayer 3 (L.subgroupOf H ⊓ Subgroup.centralizer (E : Set H)) = ⊥ := by
    intro E hEB hEab hEc
    have hE' := hE (E.map H.subtype) (by rw [← hB₀map]; exact Subgroup.map_mono hEB)
      (i1426_elemAbelian_map H.subtype hEab)
      (by rw [Subgroup.card_map_of_injective hinj]; exact hEc)
    by_contra hne
    obtain ⟨J, hJc, hJne⟩ := i1426_exists_ne_bot_component hne
    have hJG := i1426_component_map hp H.subtype hinj hJc
    rw [i1426_map_inf_centralizer_subtype hLH] at hJG
    have hle := i1426_le_layer hJG
    rw [hE', le_bot_iff] at hle
    exact hJne ((Subgroup.map_eq_bot_iff_of_injective _ hinj).1 hle)
  have hM12X : catalogIs (PSimple 3 (L.subgroupOf H)) isM12 →
      ∃ U : Subgroup H, U ≤ L.subgroupOf H ∧ IsPGroup 2 U ∧ B.subgroupOf H ≤
        Subgroup.normalizer (U : Set H) ∧ ¬ U ≤ GLAPPrimeCoreOf 3 (L.subgroupOf H) := by
    intro hc
    obtain ⟨f⟩ := i1426_quotCenter e₁
    obtain ⟨U, hUL, hUp, hUB, hUnot⟩ := hM12 (i1426_catalogIs_congr f isM12 hc)
    have hUH : U ≤ H := hUL.trans hLH
    refine ⟨U.subgroupOf H, fun y hy => Subgroup.mem_subgroupOf.2
      (hUL (Subgroup.mem_subgroupOf.1 hy)), ?_, ?_, ?_⟩
    · have hcard : Nat.card (U.subgroupOf H) = Nat.card U :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv
      obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.1 hUp
      exact IsPGroup.of_card_dvd_pow (by rw [hcard]; exact hn)
    · intro b hb
      have hbG : (b : G) ∈ B := Subgroup.mem_subgroupOf.1 hb
      have := (i1426_normalizer_map_iff H.subtype hinj (U.subgroupOf H) b).1 (by
        rw [Subgroup.map_subgroupOf_eq_of_le hUH]
        exact hUB hbG)
      exact this
    · intro hle
      apply hUnot
      have := Subgroup.map_mono hle (f := H.subtype)
      rw [Subgroup.map_subgroupOf_eq_of_le hUH,
        map_subtype_glaPPrimeCoreOf_subgroupOf 3 hLH] at this
      exact this
  obtain ⟨eK⟩ := i1426_kb_iso (L.subgroupOf H)
  have hN : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 (L.subgroupOf H)) :=
    not_dvd_card_glaPPrimeCoreOf Nat.prime_three (L.subgroupOf H)
  have hBcardY : Nat.card ↥((B.subgroupOf H).map
      (QuotientGroup.mk' (GLAPPrimeCoreOf 3 (L.subgroupOf H)))) = Nat.card (B.subgroupOf H) :=
    i1426_card_map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 (L.subgroupOf H))) (B.subgroupOf H)
      (fun x hx hx1 => i1426_inj_of_coprime hp hN hB₀ x hx ((QuotientGroup.eq_one_iff x).1 hx1))
  obtain ⟨hcardBY, A, T, hAB, hA, hAcard, hAcomp, hAcat, hAcent, hTL, hTab, hTcard, hBT, hTc, hOc⟩ :=
    h (H ⧸ GLAPPrimeCoreOf 3 (L.subgroupOf H))
      ((L.subgroupOf H).map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 (L.subgroupOf H))))
      ((B.subgroupOf H).map (QuotientGroup.mk' (GLAPPrimeCoreOf 3 (L.subgroupOf H))))
      (Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _))
      (i1426_kb_quasisimple (L.subgroupOf H) hQ)
      (i1426_kb_core (L.subgroupOf H))
      ((i1426_fullCoverLevel_congr eK 3).symm.trans hfc₀)
      (i1426_elemAbelian_map _ hB₀)
      (i1426_sup_map (L.subgroupOf H) (B.subgroupOf H) hsup)
      (by rw [hBcardY]; exact hcard₀)
      (i1426_maxRank_quot (L.subgroupOf H) (B.subgroupOf H) hB₀ hmax₀)
      (i1426_x_centralizer (L.subgroupOf H) (B.subgroupOf H) hB₀ hx₀ hx₀1 hxC)
      (fun E hE1 hE2 hE3 => i1426_E_cond (L.subgroupOf H) (B.subgroupOf H) hB₀ hEX E hE1 hE2 hE3)
      (i1426_M12 (L.subgroupOf H) (B.subgroupOf H) hM12X)
  obtain ⟨hÂle, hÂab, hÂcard, hÂmap, J₀, T₁, hJ₀c, hall, hcat₀, hCM, hT₁J, hT₁2, hT₁N, hBT₁,
    ⟨Φ, hΦinj, hΦimg⟩, hcore⟩ :=
    i1426_xlevel (L.subgroupOf H) (B.subgroupOf H) hB₀ A hAB hA
      (by rw [hAcard]; norm_num) hAcomp hAcat hAcent T hTL hTab hTcard hBT hTc hOc
  have hBcardG : Nat.card B = 3 ^ 4 := by
    rw [← hcardB₀, ← hBcardY]
    exact hcardBY
  have hB₀le : (B.subgroupOf H).map H.subtype ≤ B := le_of_eq hB₀map
  set Âh : Subgroup H := B.subgroupOf H ⊓ A.comap (QuotientGroup.mk' (GLAPPrimeCoreOf 3 (L.subgroupOf H)))
    with hÂh
  set A' : Subgroup G := Âh.map H.subtype with hA'
  set J₁ : Subgroup G := J₀.map H.subtype with hJ₁
  set T₁G : Subgroup G := T₁.map H.subtype with hT₁G
  have hZG : (L.subgroupOf H ⊓ Subgroup.centralizer (Âh : Set H)).map H.subtype =
      L ⊓ Subgroup.centralizer (A' : Set G) := i1426_map_inf_centralizer_subtype hLH
  have hJ₁comp : GLAPComponent 3 (L ⊓ Subgroup.centralizer (A' : Set G)) J₁ := by
    rw [← hZG]
    exact i1426_component_map hp H.subtype hinj hJ₀c
  have hlayer : GLAPLayer 3 (L ⊓ Subgroup.centralizer (A' : Set G)) = J₁ := by
    unfold GLAPLayer
    apply le_antisymm
    · apply sSup_le
      intro J hJ
      have hJH : J ≤ H := hJ.1.trans (inf_le_left.trans hLH)
      have h2 : (L ⊓ Subgroup.centralizer (A' : Set G)).subgroupOf H =
          L.subgroupOf H ⊓ Subgroup.centralizer (Âh : Set H) := by
        rw [← hZG]
        exact i1426_subgroupOf_map_subtype _
      have hJx : GLAPComponent 3 (L.subgroupOf H ⊓ Subgroup.centralizer (Âh : Set H))
          (J.subgroupOf H) := by
        rw [← h2]
        exact glaPComponent_subgroupOf hp (inf_le_left.trans hLH) hJ
      have hJeq := hall _ hJx
      refine le_of_eq ?_
      calc J = (J.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hJH).symm
        _ = J₁ := by rw [hJeq, hJ₁]
    · exact le_sSup hJ₁comp
  obtain ⟨ε, hε⟩ := i1426_imageMod_iso H.subtype hinj J₀ T₁
  have hε' : (imageMod 3 J₁ T₁G).map (ε : PQuot 3 J₁ →* PQuot 3 J₀) = imageMod 3 J₀ T₁ := hε
  have hΨinj : Function.Injective (Φ.comp (ε : PQuot 3 J₁ →* PQuot 3 J₀)) :=
    hΦinj.comp ε.injective
  have hΨimg : (imageMod 3 J₁ T₁G).map (Φ.comp (ε : PQuot 3 J₁ →* PQuot 3 J₀)) = T := by
    rw [← Subgroup.map_map, hε', hΦimg]
  refine ⟨hBcardG, A', J₁, T₁G, (Subgroup.map_mono hÂle).trans hB₀le,
    i1426_elemAbelian_map H.subtype hÂab, ?_,
    hlayer.symm, hJ₁comp, i1426_pSimple_map H.subtype hinj J₀ k3NoA10 hcat₀, ?_,
    Subgroup.map_mono hT₁J, hT₁2.map H.subtype, ?_, ?_,
    i1426_elemAbelian_of_map_inj (Φ.comp (ε : PQuot 3 J₁ →* PQuot 3 J₀)) hΨinj
      (by rw [hΨimg]; exact hTab), ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hinj, hÂcard]
    norm_num
  · intro b hb
    have hb₀ : (⟨b, hBH hb⟩ : H) ∈ B.subgroupOf H := Subgroup.mem_subgroupOf.2 hb
    have key := i1426_centMod_map (p := 3) H.subtype hinj J₀ ⟨b, hBH hb⟩
    rw [show H.subtype ⟨b, hBH hb⟩ = b from rfl, hCM _ hb₀] at key
    show CentMod 3 J₁ b ↔ b ∈ A'
    rw [key]
    exact (Subgroup.mem_map_iff_mem hinj).symm
  · intro b hb
    have hb₀ : (⟨b, hBH hb⟩ : H) ∈ B.subgroupOf H := Subgroup.mem_subgroupOf.2 hb
    exact i1426_normalizes_map H.subtype T₁ ⟨b, hBH hb⟩ (hT₁N hb₀)
  · rw [hT₁G, ← hB₀map, ← Subgroup.map_commutator, hBT₁]
  · rw [← Subgroup.card_map_of_injective (f := Φ.comp (ε : PQuot 3 J₁ →* PQuot 3 J₀)) hΨinj
      (K := imageMod 3 J₁ T₁G), hΨimg, hTcard]
  · rw [hJ₁, i1426_core_map H.subtype hinj J₀, ← map_subtype_glaPPrimeCoreOf_subgroupOf 3 hLH]
    exact Subgroup.map_mono hcore

end CFSG.LocalAnalysis.GLTheoremA
