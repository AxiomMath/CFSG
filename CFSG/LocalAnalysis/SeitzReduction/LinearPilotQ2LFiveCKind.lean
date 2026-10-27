module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallAltK
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.Walter.Cited.OddQuotient

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Basic

variable {N : Type*} [Group N]

theorem cKind_mem_normalizer {s : N} {Lb : Subgroup N}
    (hLs : Lb ≤ centralizer ({s} : Set N)) : s ∈ normalizer (Lb : Set N) :=
  centralizer_le_normalizer _
    (mem_centralizer_iff.2 fun _l hl => mem_centralizer_singleton_iff.1 (hLs hl))

theorem cKind_mem_centralizer {s : N} {Lb : Subgroup N}
    (hLs : Lb ≤ centralizer ({s} : Set N)) : s ∈ centralizer (Lb : Set N) :=
  mem_centralizer_iff.2 fun _l hl => mem_centralizer_singleton_iff.1 (hLs hl)

theorem mem_or_mul_mem_of_centralizer_le_sup {s : N} (hs2 : s * s = 1) {Lb : Subgroup N}
    (hLs : Lb ≤ centralizer ({s} : Set N)) (hCs : centralizer ({s} : Set N) ≤ Lb ⊔ zpowers s)
    {c : N} (hc : c ∈ centralizer ({s} : Set N)) : c ∈ Lb ∨ c * s ∈ Lb :=
  CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers hs2
    (cKind_mem_normalizer hLs) (hCs hc)

theorem normal_subgroupOf_centralizer_of_le_sup {s : N} (hs2 : s * s = 1) {Lb : Subgroup N}
    (hLs : Lb ≤ centralizer ({s} : Set N)) (hCs : centralizer ({s} : Set N) ≤ Lb ⊔ zpowers s) :
    (Lb.subgroupOf (centralizer ({s} : Set N))).Normal := by
  refine ⟨fun x hx c => ?_⟩
  rw [mem_subgroupOf] at hx ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rcases mem_or_mul_mem_of_centralizer_le_sup hs2 hLs hCs c.2 with h | h
  · exact Lb.mul_mem (Lb.mul_mem h hx) (Lb.inv_mem h)
  · have hxs : (x : N) * s = s * x := mem_centralizer_singleton_iff.1 (hLs hx)
    have he : (c : N) * x * (c : N)⁻¹ = ((c : N) * s) * x * ((c : N) * s)⁻¹ := by
      calc (c : N) * x * (c : N)⁻¹ = c * ((x : N) * s) * s⁻¹ * (c : N)⁻¹ := by group
        _ = c * (s * (x : N)) * s⁻¹ * (c : N)⁻¹ := by rw [hxs]
        _ = ((c : N) * s) * x * ((c : N) * s)⁻¹ := by group
    rw [he]
    exact Lb.mul_mem (Lb.mul_mem h hx) (Lb.inv_mem h)

theorem cKind_eq_one_of_mem_centralizer {Lb : Subgroup N} (hLZ : center Lb = ⊥)
    {g : N} (hg : g ∈ Lb) (hgc : g ∈ centralizer (Lb : Set N)) : g = 1 := by
  have hz : (⟨g, hg⟩ : Lb) ∈ center Lb := by
    rw [Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext ((mem_centralizer_iff.1 hgc) h h.2)
  rw [hLZ] at hz
  exact congrArg Subtype.val ((Subgroup.mem_bot).1 hz)

theorem inf_centralizer_le_zpowers_of_le_sup {s : N} (hs2 : s * s = 1) {Lb : Subgroup N}
    (hLs : Lb ≤ centralizer ({s} : Set N)) (hLZ : center Lb = ⊥)
    (hCs : centralizer ({s} : Set N) ≤ Lb ⊔ zpowers s) :
    centralizer ({s} : Set N) ⊓ centralizer (Lb : Set N) ≤ zpowers s := by
  intro u hu
  obtain ⟨hus, huL⟩ := Subgroup.mem_inf.1 hu
  rcases mem_or_mul_mem_of_centralizer_le_sup hs2 hLs hCs hus with h | h
  · rw [cKind_eq_one_of_mem_centralizer hLZ h huL]
    exact one_mem _
  · have h1 := cKind_eq_one_of_mem_centralizer hLZ h
      (mul_mem huL (cKind_mem_centralizer hLs))
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_mem (mem_zpowers s)

theorem card_sup_zpowers_le_two_mul [Finite N] {s : N} (hs2 : s * s = 1) {A : Subgroup N}
    (hsN : s ∈ normalizer (A : Set N)) :
    Nat.card (A ⊔ zpowers s : Subgroup N) ≤ 2 * Nat.card A := by
  let f : A × Fin 2 → (A ⊔ zpowers s : Subgroup N) := fun p =>
    if p.2 = 0 then ⟨p.1, mem_sup_left p.1.2⟩
    else ⟨p.1 * s, mul_mem (mem_sup_left p.1.2) (mem_sup_right (mem_zpowers s))⟩
  have hf : Function.Surjective f := by
    rintro ⟨g, hg⟩
    rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers hs2 hsN hg with h | h
    · exact ⟨(⟨g, h⟩, 0), by simp [f]⟩
    · refine ⟨(⟨g * s, h⟩, 1), ?_⟩
      have hs' : s * s = 1 := hs2
      simp only [f, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false]
      apply Subtype.ext
      simp only
      rw [mul_assoc, hs', mul_one]
  calc Nat.card (A ⊔ zpowers s : Subgroup N) ≤ Nat.card (A × Fin 2) :=
        Nat.card_le_card_of_surjective f hf
    _ = 2 * Nat.card A := by rw [Nat.card_prod, Nat.card_fin, mul_comm]

theorem inf_centralizer_le_of_not_mem {s : N} (hs2 : s * s = 1) {Lh Kc : Subgroup N}
    (hLK : Lh ≤ Kc) (hLs : Lh ≤ centralizer ({s} : Set N))
    (hC : centralizer ({s} : Set N) ≤ Lh ⊔ zpowers s) (hsK : s ∉ Kc) :
    Kc ⊓ centralizer ({s} : Set N) ≤ Lh := by
  intro q hq
  obtain ⟨hqK, hqs⟩ := Subgroup.mem_inf.1 hq
  rcases mem_or_mul_mem_of_centralizer_le_sup hs2 hLs hC hqs with h | h
  · exact h
  · exfalso
    apply hsK
    have : s = q⁻¹ * (q * s) := by group
    rw [this]
    exact mul_mem (inv_mem hqK) (hLK h)

end Basic

section Inheritance

variable {N : Type*} [Group N] [Finite N]

theorem inheritance_of_centralizer_le_sup {s : N} (hs : orderOf s = 2) {Lb : Subgroup N}
    (hLs : Lb ≤ centralizer ({s} : Set N)) (hLq : CFSG.Open.IsQuasisimple Lb)
    (hLZ : center Lb = ⊥) (hCs : centralizer ({s} : Set N) ≤ Lb ⊔ zpowers s) :
    CFSG.Open.IsComponentOf (Lb.map (QuotientGroup.mk' (oddCore N)))
        (centralizer ({QuotientGroup.mk' (oddCore N) s} : Set (N ⧸ oddCore N))) ∧
      (∀ U : Subgroup (N ⧸ oddCore N), IsPGroup 2 U →
        U ≤ centralizer (Lb.map (QuotientGroup.mk' (oddCore N)) : Set (N ⧸ oddCore N)) →
        Nat.card U ≤ 2) ∧
      CFSG.Open.standardComponentIsStandard (Lb.map (QuotientGroup.mk' (oddCore N))) := by
  have hs2 : s * s = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  have hLn := normal_subgroupOf_centralizer_of_le_sup hs2 hLs hCs
  have hsyl : ∀ U : Subgroup N, IsPGroup 2 U →
      U ≤ centralizer ({s} : Set N) ⊓ centralizer (Lb : Set N) → Nat.card U ≤ 2 := by
    intro U _ hU
    calc Nat.card U ≤ Nat.card (zpowers s) :=
          Subgroup.card_le_of_le (hU.trans (inf_centralizer_le_zpowers_of_le_sup hs2 hLs hLZ hCs))
      _ = 2 := by rw [Nat.card_zpowers, hs]
  exact ⟨CFSG.SeitzReduction.isComponentOf_map_oddCore hs hLs hLn hLq,
    fun U hU hUD =>
      CFSG.SeitzReduction.card_le_two_of_le_centralizer_map_oddCore hs hLs hLn hLq hsyl hU hUD,
    CFSG.SeitzReduction.standardComponentIsStandard_map_oddCore hs hLs hLn hLq hsyl⟩

theorem injective_subgroupMap_mk_oddCore_of_center {Lb : Subgroup N}
    (hLq : CFSG.Open.IsQuasisimple Lb) (hLZ : center Lb = ⊥) :
    Function.Injective ((QuotientGroup.mk' (oddCore N)).subgroupMap Lb) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have h1 : QuotientGroup.mk' (oddCore N) (x : N) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have h2 : x ∈ center Lb :=
    CFSG.SeitzReduction.oddCore_subgroupOf_le_center hLq (mem_subgroupOf.2 h1)
  rwa [hLZ] at h2

@[expose] noncomputable def mapOddCoreMulEquivOfCenter {Lb : Subgroup N}
    (hLq : CFSG.Open.IsQuasisimple Lb) (hLZ : center Lb = ⊥) :
    Lb ≃* Lb.map (QuotientGroup.mk' (oddCore N)) :=
  MulEquiv.ofBijective ((QuotientGroup.mk' (oddCore N)).subgroupMap Lb)
    ⟨injective_subgroupMap_mk_oddCore_of_center hLq hLZ,
      (QuotientGroup.mk' (oddCore N)).subgroupMap_surjective Lb⟩

theorem centralizer_mk_le_sup_of_le_sup {s : N} (hs : orderOf s = 2) {Lb : Subgroup N}
    (hCs : centralizer ({s} : Set N) ≤ Lb ⊔ zpowers s) :
    centralizer ({QuotientGroup.mk' (oddCore N) s} : Set (N ⧸ oddCore N)) ≤
      Lb.map (QuotientGroup.mk' (oddCore N)) ⊔ zpowers (QuotientGroup.mk' (oddCore N) s) := by
  have hs2 : s * s = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  have h := CFSG.Walter.Suzuki.centralizer_mk_le_map (oddCore N)
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd hs2
  refine h.trans ?_
  rw [← MonoidHom.map_zpowers, ← Subgroup.map_sup]
  exact Subgroup.map_mono hCs

end Inheritance

theorem neighbourOvergroup_or_inner_of_centralizer_le_sup {N : Type} [Group N] [Finite N]
    (hcat : SLmCatalogueClausesAt 4) {s : N} (hs : orderOf s = 2) {Lb : Subgroup N}
    (hLs : Lb ≤ centralizer ({s} : Set N)) (hLq : CFSG.Open.IsQuasisimple Lb)
    (hLZ : center Lb = ⊥) (hLm : LieModel (Lb ⧸ center Lb) .PSL 4 2 1)
    (hCs : centralizer ({s} : Set N) ≤ Lb ⊔ zpowers s)
    (hsec : ∀ Kc : Subgroup (N ⧸ oddCore N), IsComponent Kc → Catalog (Kc ⧸ center Kc))
    (hnn : ¬ (Lb.map (QuotientGroup.mk' (oddCore N))).Normal) :
    NeighbourOvergroupSLm (QuotientGroup.mk' (oddCore N) s)
        (Lb.map (QuotientGroup.mk' (oddCore N))) 4 1 ∨
      NeighbourOvergroupSLmInner (QuotientGroup.mk' (oddCore N) s)
        (Lb.map (QuotientGroup.mk' (oddCore N))) 4 1 := by
  obtain ⟨hD, hsyl, hstd⟩ := inheritance_of_centralizer_le_sup hs hLs hLq hLZ hCs
  exact neighbour_overgroup_slm_center_or_inner_of_pPrimeCore_eq_bot (by norm_num) hcat
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot N) hsec
    (CFSG.SeitzReduction.orderOf_mk_oddCore hs) hD hsyl hstd hnn
    (lieModel_quotient_center_congr (mapOddCoreMulEquivOfCenter hLq hLZ) hLm)


section Small

open Equiv

variable {Y : Type} [Group Y] [Finite Y]

theorem false_of_alternating_of_centralizer_le_sup {Kc : Subgroup Y} {k : ℕ}
    (ε : Kc ≃* alternatingGroup (Fin k)) {s : Y} (hsN : s ∈ normalizer (Kc : Set Y))
    (hs : orderOf s = 2) (hsK : s ∉ centralizer (Kc : Set Y)) {D : Subgroup Y} (hDK : D < Kc)
    (hDs : D ≤ centralizer ({s} : Set Y))
    (hDcomp : IsComponent (D.subgroupOf (Kc ⊓ centralizer ({s} : Set Y))))
    (hDsimple : IsSimpleGroup D) (hDc : Nat.card D = 20160)
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2)
    (hC : centralizer ({s} : Set Y) ≤ D ⊔ zpowers s) : False := by
  classical
  have hs2 : s * s = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  have hk : k = 10 := eq_ten_of_alternating ε hsN hs2 hsK hDK.le hDK.ne hDs hDcomp hDc hsyl
  subst hk
  set ι : Kc →* Perm (Fin 10) := (alternatingGroup (Fin 10)).subtype.comp ε.toMonoidHom with hι
  have hιinj : Function.Injective ι :=
    (alternatingGroup (Fin 10)).subtype_injective.comp ε.injective
  set DA : Subgroup (Perm (Fin 10)) := (D.subgroupOf Kc).map ι with hDA
  have hDAc : Nat.card DA = 20160 := by
    rw [hDA, Subgroup.card_map_of_injective hιinj,
      Nat.card_congr (D.subgroupOfEquivOfLe hDK.le).toEquiv, hDc]
  by_cases hsKc : s ∈ Kc
  ·
    have hx2 : orderOf (ι ⟨s, hsKc⟩) = 2 := by
      rw [orderOf_injective ι hιinj, orderOf_mk, hs]
    have hDAx : DA ≤ centralizer {ι ⟨s, hsKc⟩} := by
      rintro _ ⟨d, hd, rfl⟩
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.1 (hDs (mem_subgroupOf.1 hd))
    have hsign := (isSwap_of_le_centralizer_ten hx2 hDAx hDAc.ge).sign_eq
    have hmem : ι ⟨s, hsKc⟩ ∈ alternatingGroup (Fin 10) := (ε ⟨s, hsKc⟩).2
    rw [Perm.mem_alternatingGroup] at hmem
    rw [hmem] at hsign
    exact absurd hsign (by decide)
  ·
    set τ := Kc.normalizerMonoidHom ⟨s, hsN⟩ with hτ
    have hτapp : ∀ q : Kc, ((τ q : Kc) : Y) = s * q * s⁻¹ := fun q =>
      Subgroup.normalizerMonoidHom_apply_apply_coe Kc ⟨s, hsN⟩ q
    set σ : MulAut (alternatingGroup (Fin 10)) := (ε.symm.trans τ).trans ε with hσ
    have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 10
      (by norm_num) (by norm_num)
    obtain ⟨π, hπ⟩ := hbij.2 σ
    have key : ∀ q : Kc, π * ((ε q : alternatingGroup (Fin 10)) : Perm (Fin 10)) * π⁻¹ =
        ((ε (τ q) : alternatingGroup (Fin 10)) : Perm (Fin 10)) := by
      intro q
      have h1 := congrArg (fun φ : MulAut (alternatingGroup (Fin 10)) =>
        ((φ (ε q) : alternatingGroup (Fin 10)) : Perm (Fin 10))) hπ
      simp only [hσ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
      exact h1
    have hτD : ∀ (d : Y) (hd : d ∈ D), τ ⟨d, hDK.le hd⟩ = ⟨d, hDK.le hd⟩ := fun d hd => by
      apply Subtype.ext
      rw [hτapp]
      have hds : d * s = s * d := mem_centralizer_singleton_iff.1 (hDs hd)
      calc s * d * s⁻¹ = d * s * s⁻¹ := by rw [hds]
        _ = d := by group
    have hDAπ : DA ≤ centralizer {π} := by
      rintro _ ⟨d, hd, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have h1 := key d
      rw [show d = ⟨(d : Y), hDK.le (mem_subgroupOf.1 hd)⟩ from rfl,
        hτD _ (mem_subgroupOf.1 hd)] at h1
      calc ι d * π = π * ((ε d : alternatingGroup (Fin 10)) : Perm (Fin 10)) * π⁻¹ * π := by
            rw [h1]; rfl
        _ = π * ι d := by simp [hι]
    have hτ2 : τ * τ = 1 := by
      rw [← sq]
      exact F4Pilot.normalizerMonoidHom_sq_eq_one Kc hsN (by rw [sq]; exact hs2)
    have hππ : π * π = 1 := by
      apply hbij.1
      rw [map_mul, hπ, map_one]
      ext x
      have h1 : τ (τ (ε.symm x)) = ε.symm x := by
        rw [← MulAut.mul_apply, hτ2, MulAut.one_apply]
      simp only [hσ, MulAut.mul_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, h1,
        MulEquiv.apply_symm_apply, MulAut.one_apply]
    have hπ1 : π ≠ 1 := by
      rintro rfl
      apply hsK
      rw [mem_centralizer_iff]
      intro q hq
      have h1 := key ⟨q, hq⟩
      simp only [one_mul, inv_one, mul_one] at h1
      have h2 : τ ⟨q, hq⟩ = ⟨q, hq⟩ := hιinj (by simp only [hι, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]; exact h1.symm)
      have h3 := congrArg Subtype.val h2
      rw [hτapp] at h3
      calc q * s = s * q * s⁻¹ * s := by rw [h3]
        _ = s * q := by group
    have hπ2 : orderOf π = 2 := orderOf_eq_prime (by rw [sq]; exact hππ) hπ1
    obtain ⟨a, b, hab, rfl⟩ := isSwap_of_le_centralizer_ten hπ2 hDAπ hDAc.ge
    have hDAs : IsSimpleGroup DA := by
      have e1 : DA ≃* D :=
        ((D.subgroupOf Kc).equivMapOfInjective ι hιinj).symm.trans (D.subgroupOfEquivOfLe hDK.le)
      exact e1.isSimpleGroup
    have hfix : ∀ g ∈ DA, g a = a :=
      apply_eq_of_le_centralizer_swap hDAs (by rw [hDAc]; norm_num) hab hDAπ
    obtain ⟨c, hca, hcb⟩ : ∃ c : Fin 10, c ≠ a ∧ c ≠ b := by
      by_contra h
      push Not at h
      have hsub : (Finset.univ : Finset (Fin 10)) ⊆ {a, b} := fun x _ => by
        by_cases hx : x = a
        · simp [hx]
        · simp [h x hx]
      have := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at this
      have h2 := Finset.card_le_two (a := a) (b := b)
      omega
    obtain ⟨d, hda, hdb, hdc⟩ : ∃ d : Fin 10, d ≠ a ∧ d ≠ b ∧ d ≠ c := by
      by_contra h
      push Not at h
      have hsub : (Finset.univ : Finset (Fin 10)) ⊆ {a, b, c} := fun x _ => by
        by_cases hx : x = a
        · simp [hx]
        · by_cases hx' : x = b
          · simp [hx']
          · simp [h x hx hx']
      have := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at this
      have h3 := Finset.card_le_three (a := a) (b := b) (c := c)
      omega
    have hdisj : (swap a b).Disjoint (swap c d) := by
      intro x
      by_cases hxa : x = a
      · right; rw [hxa]; exact swap_apply_of_ne_of_ne hca.symm hda.symm
      · by_cases hxb : x = b
        · right; rw [hxb]; exact swap_apply_of_ne_of_ne hcb.symm hdb.symm
        · left; exact swap_apply_of_ne_of_ne hxa hxb
    set g : Perm (Fin 10) := swap a b * swap c d with hg
    have hgA : g ∈ alternatingGroup (Fin 10) := by
      rw [Perm.mem_alternatingGroup, hg, Perm.sign_mul, Perm.sign_swap hab,
        Perm.sign_swap hdc.symm]
      decide
    have hgπ : swap a b * g * (swap a b)⁻¹ = g := by
      rw [hg]
      calc swap a b * (swap a b * swap c d) * (swap a b)⁻¹ =
          swap a b * (swap c d * swap a b) * (swap a b)⁻¹ := by rw [hdisj.commute.eq]
        _ = swap a b * swap c d := by group
    set q : Kc := ε.symm ⟨g, hgA⟩ with hq
    have hιq : ι q = g := by simp [hι, hq]
    have hτq : τ q = q := by
      apply hιinj
      have h1 := key q
      have h2 : ((ε q : alternatingGroup (Fin 10)) : Perm (Fin 10)) = g := hιq
      rw [h2, hgπ] at h1
      rw [hιq]
      exact h1.symm
    have hqs : (q : Y) ∈ Kc ⊓ centralizer ({s} : Set Y) := by
      refine Subgroup.mem_inf.2 ⟨q.2, mem_centralizer_singleton_iff.2 ?_⟩
      have h3 := congrArg Subtype.val hτq
      rw [hτapp] at h3
      calc (q : Y) * s = s * q * s⁻¹ * s := by rw [h3]
        _ = s * q := by group
    have hqD : (q : Y) ∈ D := inf_centralizer_le_of_not_mem hs2 hDK.le hDs hC hsKc hqs
    have hgD : g ∈ DA := ⟨q, mem_subgroupOf.2 hqD, hιq⟩
    have hga := hfix g hgD
    rw [hg, Perm.mul_apply, swap_apply_of_ne_of_ne hca.symm hda.symm, swap_apply_left] at hga
    exact hab hga.symm

@[expose] def SporadicFixedLFourTwoInput : Prop :=
  ∀ (S : Type) [Group S] [Finite S], NativeSporadic.SporadicRep S → ∀ τ : MulAut S,
    orderOf τ = 2 → ∀ D : Subgroup (fixedSubgroup τ), LieModel D .PSL 4 2 1 →
      (Nat.card (fixedSubgroup τ) ≤ Nat.card D → False) ∧
      (τ ∈ (MulAut.conj : S →* MulAut S).range →
        Nat.card (fixedSubgroup τ) ≤ 2 * Nat.card D → False)

theorem false_of_sporadic_of_centralizer_le_sup (hspor : SporadicFixedLFourTwoInput)
    {Kc : Subgroup Y} (hKsp : NativeSporadic.SporadicRep Kc) {s : Y}
    (hsN : s ∈ normalizer (Kc : Set Y)) (hs : orderOf s = 2)
    (hsK : s ∉ centralizer (Kc : Set Y)) {D : Subgroup Y} (hDK : D ≤ Kc)
    (hDs : D ≤ centralizer ({s} : Set Y)) (hDm : LieModel D .PSL 4 2 1)
    (hC : centralizer ({s} : Set Y) ≤ D ⊔ zpowers s) : False := by
  have hs2 : s * s = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  have hKs : ¬ Kc ≤ centralizer ({s} : Set Y) := fun h =>
    hsK (mem_centralizer_iff.2 fun k hk => mem_centralizer_singleton_iff.1 (h hk))
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = Kc.normalizerMonoidHom ⟨s, hsN⟩ := ⟨_, rfl⟩
  have hτ2 : orderOf τ = 2 :=
    hτ ▸ F4Pilot.orderOf_normalizerMonoidHom_eq_two Kc hsN (by rw [sq]; exact hs2) hKs
  have hfixeq : fixedSubgroup τ = (centralizer ({s} : Set Y)).subgroupOf Kc :=
    hτ ▸ F4Pilot.fixedSubgroup_normalizerMonoidHom Kc hsN
  have hfixC : ∀ x : fixedSubgroup τ, ((x : Kc) : Y) ∈ centralizer ({s} : Set Y) := by
    intro x
    have hx : (x : Kc) ∈ (centralizer ({s} : Set Y)).subgroupOf Kc := hfixeq ▸ x.2
    exact mem_subgroupOf.1 hx
  have hDfix : D.subgroupOf Kc ≤ fixedSubgroup τ := by
    rw [hfixeq]
    intro x hx
    exact mem_subgroupOf.mpr (hDs (mem_subgroupOf.mp hx))
  have eD := F4Pilot.subgroupOfSubgroupOfEquiv hDK hDfix
  have hD'm : LieModel ((D.subgroupOf Kc).subgroupOf (fixedSubgroup τ)) .PSL 4 2 1 :=
    LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hDm
  have hD'c : Nat.card ((D.subgroupOf Kc).subgroupOf (fixedSubgroup τ)) = Nat.card D :=
    Nat.card_congr eD.toEquiv
  have hinj : ∀ (A : Subgroup Y) (hA : ∀ x : fixedSubgroup τ, ((x : Kc) : Y) ∈ A),
      Nat.card (fixedSubgroup τ) ≤ Nat.card A := by
    intro A hA
    refine Nat.card_le_card_of_injective (fun x => ⟨((x : Kc) : Y), hA x⟩) ?_
    intro x y hxy
    simp only [Subtype.mk.injEq] at hxy
    exact Subtype.ext (Subtype.ext hxy)
  by_cases hsKc : s ∈ Kc
  · have hin : τ ∈ (MulAut.conj : Kc →* MulAut Kc).range :=
      hτ ▸ F4Pilot.normalizerMonoidHom_mem_range_conj Kc hsN hsKc
    refine (hspor Kc hKsp τ hτ2 _ hD'm).2 hin ?_
    rw [hD'c]
    exact (hinj (D ⊔ zpowers s) fun x => hC (hfixC x)).trans
      (card_sup_zpowers_le_two_mul hs2 (cKind_mem_normalizer hDs))
  · refine (hspor Kc hKsp τ hτ2 _ hD'm).1 ?_
    rw [hD'c]
    exact hinj D fun x => inf_centralizer_le_of_not_mem hs2 hDK hDs hC hsKc
      (Subgroup.mem_inf.2 ⟨(x : Kc).2, hfixC x⟩)

theorem not_neighbourOvergroupSLmSmall_of_centralizer_le_sup (hspor : SporadicFixedLFourTwoInput)
    {s : Y} (hs : orderOf s = 2) {Lh : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf Lh (centralizer ({s} : Set Y)))
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (Lh : Set Y) → Nat.card U ≤ 2)
    (hLm : LieModel Lh .PSL 4 2 1) (hLc : Nat.card Lh = 20160)
    (hC : centralizer ({s} : Set Y) ≤ Lh ⊔ zpowers s) :
    ¬ NeighbourOvergroupSLmSmall s Lh 4 1 := by
  rintro ⟨Kc, hKc, hDK, hKt, hsC, hZ, hsm⟩
  have hsN : s ∈ normalizer (Kc : Set Y) := mem_normalizer_iff_map_conj_eq.2 hKt
  have hDs : Lh ≤ centralizer ({s} : Set Y) := hD.1
  have eZ : Kc ≃* Kc ⧸ center Kc :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  rcases hsm with ⟨-, ⟨-, ⟨k, -, ⟨φ⟩⟩⟩ | ⟨h3, -⟩ | ⟨-, ⟨sp, ⟨φ⟩⟩⟩⟩
  · have hDc : IsComponent (Lh.subgroupOf (centralizer ({s} : Set Y))) :=
      (isComponentOf_iff_isComponent_subgroupOf hDs).1
        ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hD)
    have hDcomp := CentralizerComponents.isComponent_subgroupOf_inf_centralizer hDs hDc hDK.le
    exact false_of_alternating_of_centralizer_le_sup (eZ.trans φ) hsN hs hsC hDK hDs hDcomp
      (isSimpleGroup_of_lieModel_PSL hLm) hLc hsyl hC
  · exact absurd h3 (by norm_num)
  · exact false_of_sporadic_of_centralizer_le_sup hspor ⟨sp, ⟨eZ.trans φ⟩⟩ hsN hs hsC hDK.le hDs
      hLm hC

end Small

theorem neighbourOvergroupSLmField_of_centralizer_le_sup {N : Type} [Group N] [Finite N]
    (hcat : SLmCatalogueClausesAt 4) (hdet : SLmEvenTypeDetAt 4)
    (hspor : SporadicFixedLFourTwoInput) {s : N}
    (hs : orderOf s = 2) {Lb : Subgroup N} (hLs : Lb ≤ centralizer ({s} : Set N))
    (hLq : CFSG.Open.IsQuasisimple Lb) (hLZ : center Lb = ⊥)
    (hLm : LieModel (Lb ⧸ center Lb) .PSL 4 2 1) (hLc : Nat.card Lb = 20160)
    (hCs : centralizer ({s} : Set N) ≤ Lb ⊔ zpowers s)
    (hsec : ∀ Kc : Subgroup (N ⧸ oddCore N), IsComponent Kc → Catalog (Kc ⧸ center Kc))
    (hnn : ¬ (Lb.map (QuotientGroup.mk' (oddCore N))).Normal) :
    NeighbourOvergroupSLmField (QuotientGroup.mk' (oddCore N) s)
        (Lb.map (QuotientGroup.mk' (oddCore N))) 4 1 ∧
      center (Lb.map (QuotientGroup.mk' (oddCore N))) = ⊥ := by
  obtain ⟨hD, hsyl, -⟩ := inheritance_of_centralizer_le_sup hs hLs hLq hLZ hCs
  have hsh : orderOf (QuotientGroup.mk' (oddCore N) s) = 2 :=
    CFSG.SeitzReduction.orderOf_mk_oddCore hs
  have hC := centralizer_mk_le_sup_of_le_sup hs hCs
  set φ := mapOddCoreMulEquivOfCenter hLq hLZ with hφ
  have hLhm : LieModel (Lb.map (QuotientGroup.mk' (oddCore N))) .PSL 4 2 1 :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      (((QuotientGroup.quotientMulEquivOfEq hLZ).trans QuotientGroup.quotientBot).trans φ) hLm
  have hLhc : Nat.card (Lb.map (QuotientGroup.mk' (oddCore N))) = 20160 := by
    rw [← Nat.card_congr φ.toEquiv, hLc]
  have hnot := not_neighbourOvergroupSLmSmall_of_centralizer_le_sup hspor hsh hD hsyl hLhm hLhc hC
  rcases neighbourOvergroup_or_inner_of_centralizer_le_sup hcat hs hLs hLq hLZ hLm hCs hsec hnn
    with h | h
  · rcases h.field_or_small (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot N) hsh hD
      (by norm_num) hdet
      (lieModel_quotient_center_congr φ hLm) with h' | h'
    · exact h'
    · exact (hnot h').elim
  · exact (hnot h.small).elim

end CFSG.SeitzReduction.LinearPilot
