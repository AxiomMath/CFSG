module

public import CFSG.GH74.GLS.C3.Layer1.PU3Conj
public import CFSG.GH74.GLS.C3.Layer1.Th2P85Bar
public import CFSG.GH74.GLS.C3.Layer1.BkP89J2Layer

public section

namespace CFSG.GH74.GLS.PU3

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P85
  CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSubnormalIn_of_comp {M L : Subgroup G} (h : IsPCompIn 2 M L) : IsSubnormalIn L M := by
  obtain ⟨K, -, hsub, -⟩ := h.2
  exact ⟨h.1, hsub⟩

theorem pPrimeCoreOf_le_of_comp {M L : Subgroup G} (h : IsPCompIn 2 M L) :
    pPrimeCoreOf 2 L ≤ pPrimeCoreOf 2 M :=
  Th2.pPrimeCoreOf_le_of_subnormal (isSubnormalIn_of_comp h)

theorem inf_pPrimeCoreOf_eq {M L : Subgroup G} (h : IsPCompIn 2 M L) :
    L ⊓ pPrimeCoreOf 2 M = pPrimeCoreOf 2 L := by
  refine le_antisymm ?_ (le_inf (TwoThin.pPrimeCoreOf_le L) (pPrimeCoreOf_le_of_comp h))
  rw [inf_comm]
  exact Th2.inf_le_pPrimeCoreOf h.1

omit [Finite G] in
theorem eq_of_imgM_eq {M L S : Subgroup G} (h : IsPCompIn 2 M L) (hSL : S ≤ L)
    (hS : IsSubnormalIn S M) (himg : imgM M S = imgM M L) : S = L := by
  obtain ⟨K, -, -, hmap, hmin⟩ := h.2
  by_contra hne
  have hle : S.subgroupOf M ≤ L.subgroupOf M := fun x hx => hSL hx
  have hlt : S.subgroupOf M < L.subgroupOf M := by
    refine lt_of_le_of_ne hle fun heq => hne ?_
    apply le_antisymm hSL
    intro x hx
    have hxM : x ∈ M := h.1 hx
    have : (⟨x, hxM⟩ : ↥M) ∈ L.subgroupOf M := hx
    rw [← heq] at this
    exact this
  apply hmin _ hlt hS.2
  rw [← hmap]
  exact himg

theorem imgM_equiv_kBar_self {M L : Subgroup G} (h : IsPCompIn 2 M L) :
    Nonempty (↥(imgM M L) ≃* kBar L) :=
  imgM_equiv_kBar le_rfl (isSubnormalIn_of_comp h)
    (sup_eq_right.2 (TwoThin.pPrimeCoreOf_le L)).symm

theorem Good.imgM_simple {M L : Subgroup G} (h : Good M L) : IsSimpleGroup ↥(imgM M L) := by
  obtain ⟨e⟩ := imgM_equiv_kBar_self h.comp
  exact (MulEquiv.isSimpleGroup_congr e).2 h.simple

theorem Good.imgM_nonab {M L : Subgroup G} (h : Good M L) :
    ∃ a ∈ imgM M L, ∃ b ∈ imgM M L, a * b ≠ b * a := by
  obtain ⟨e⟩ := imgM_equiv_kBar_self h.comp
  obtain ⟨a, b, hab⟩ := h.nonab
  refine ⟨((e.symm a : ↥(imgM M L)) : Mb M), (e.symm a).2, ((e.symm b : ↥(imgM M L)) : Mb M), (e.symm b).2, fun hc => hab ?_⟩
  have : e.symm a * e.symm b = e.symm b * e.symm a := Subtype.ext hc
  have := congrArg e this
  simpa using this


theorem Good.cj_o {M L : Subgroup G} (h : Good M L) {o : G} (ho : o ∈ pPrimeCoreOf 2 M) :
    cj o L = L := by
  by_contra hne
  have hoM : o ∈ M := TwoThin.pPrimeCoreOf_le M ho
  have hL' : IsPCompIn 2 M (cj o L) := by
    have := Stage1.Thm2.Recip.isPCompIn_map_conj h.comp o
    rwa [C3.Layer1.Thm1.map_conj_eq_self_of_mem hoM] at this
  have hle := Stage1.Thm2.Recip.le_cSec_of_ne hL' h.comp hne
  obtain ⟨a, ha, b, hb, hab⟩ := h.imgM_nonab
  obtain ⟨l, hl, rfl⟩ := mem_imgM_iff.1 ha
  obtain ⟨l', hl', rfl⟩ := mem_imgM_iff.1 hb
  apply hab
  have hc : o * (l' : G) * o⁻¹ ∈ cj o L := (mem_cj_iff' o L l').2 hl'
  have h1 : ⁅(l : G), o * (l' : G) * o⁻¹⁆ ∈ pPrimeCoreOf 2 L := (hle hc).2.2 l hl
  have h1' : ⁅(l : G), o * (l' : G) * o⁻¹⁆ ∈ pPrimeCoreOf 2 M := pPrimeCoreOf_le_of_comp h.comp h1
  let o' : ↥M := ⟨o, hoM⟩
  let c' : ↥M := o' * l' * o'⁻¹
  have h2 : barMk ↥M ⁅l, c'⁆ = 1 := by
    rw [barMk_eq_one_iff_mem_pPrimeCoreOf]
    have : ((⁅l, c'⁆ : ↥M) : G) = ⁅(l : G), o * (l' : G) * o⁻¹⁆ := by
      simp [c', o', commutatorElement_def]
    rw [this]
    exact h1'
  rw [map_commutatorElement] at h2
  have h3 : barMk ↥M o' = 1 := (barMk_eq_one_iff_mem_pPrimeCoreOf o').2 ho
  have h4 : barMk ↥M c' = barMk ↥M l' := by
    show barMk ↥M (o' * l' * o'⁻¹) = barMk ↥M l'
    rw [map_mul, map_mul, map_inv, h3]
    simp
  rw [h4] at h2
  exact commutatorElement_eq_one_iff_mul_comm.1 h2

theorem Good.two_dvd_card {M L : Subgroup G} (h : Good M L) : 2 ∣ Nat.card ↥L := by
  have := h.simple
  exact (CFSG.Walter.even_card_of_isSimpleGroup h.nonab).two_dvd.trans
    (Subgroup.card_quotient_dvd_card _)

theorem Good.exists_sylow {M L : Subgroup G} (h : Good M L) :
    ∃ P : Subgroup G, IsSylowOf 2 P L ∧ P ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥L) := inferInstance
  have hP : IsSylowOf 2 ((Q : Subgroup ↥L).map L.subtype) L := ⟨Q, rfl⟩
  refine ⟨_, hP, fun hbot => ?_⟩
  have hcard := hP.card_eq
  rw [hbot, Subgroup.card_bot] at hcard
  have hpos : 0 < Nat.card ↥L := Nat.card_pos
  have hf : 1 ≤ (Nat.card ↥L).factorization 2 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hpos.ne').1 h.two_dvd_card
  have h2lt : 1 < 2 ^ (Nat.card ↥L).factorization 2 := Nat.one_lt_two_pow (by omega)
  omega

theorem Good.normalizer_le_M {M L : Subgroup G} (h : Good M L) : normalizer (L : Set G) ≤ M := by
  obtain ⟨P, hP, hP1⟩ := h.exists_sylow
  have hNP : normalizer (P : Set G) ≤ M := h.normalizer_le P hP.le hP.isPGroup hP1
  intro n hn
  have hnP : cj n P ≤ L := by
    intro c hc
    have h1 : n⁻¹ * c * n ∈ P := (mem_cj_iff n P c).1 hc
    have h2 : n⁻¹ * c * n ∈ L := hP.le h1
    have e : c = n * (n⁻¹ * c * n) * n⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 hn _).1 h2
  have h2 : IsPGroup 2 ↥(cj n P) := hP.isPGroup.of_equiv ((MulAut.conj n).subgroupMap P)
  obtain ⟨g, hgL, hgle⟩ := Th2.exists_cj_le_of_isSylowOf hP hnP h2
  have hle' : cj (g * n) P ≤ P := by
    have e : cj (g * n) P = cj g (cj n P) := (cj_cj g n P).symm
    rw [e]
    exact hgle
  have hcard : Nat.card ↥(cj (g * n) P) = Nat.card ↥P := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (g * n)).injective]
  have heq : cj (g * n) P = P := Subgroup.eq_of_le_of_card_ge hle' (le_of_eq hcard.symm)
  have hgn : g * n ∈ normalizer (P : Set G) := mem_normalizer_of_cj_eq heq
  have hM : g * n ∈ M := hNP hgn
  have e : n = g⁻¹ * (g * n) := by group
  rw [e]
  exact M.mul_mem (M.inv_mem (h.comp.1 hgL)) hM

omit [Finite G] in
theorem commutator_subgroupOf_eq {Y A : Subgroup G} (hYA : Y ≤ A) (hY : ⁅Y, Y⁆ = Y) :
    ⁅Y.subgroupOf A, Y.subgroupOf A⁆ = Y.subgroupOf A := by
  apply Subgroup.map_injective A.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hYA]
  exact hY

theorem Good.perf_le {M L : Subgroup G} (h : Good M L) {Y : Subgroup G}
    (hY : Y ≤ L ⊔ pPrimeCoreOf 2 M) (hperf : ⁅Y, Y⁆ = Y) : Y ≤ L := by
  set A := L ⊔ pPrimeCoreOf 2 M with hA
  have hLA : L ≤ A := le_sup_left
  have hOA : pPrimeCoreOf 2 M ≤ A := le_sup_right
  have hAnorm : A ≤ normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer (fun o ho => mem_normalizer_of_cj_eq (h.cj_o ho))
  have hnormal : (L.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLA).2 hAnorm
  have hLN : L ≤ normalizer (pPrimeCoreOf 2 M : Set G) := fun l hl =>
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer (h.comp.1 hl))
  have hsolv : Group.IsSolvable (↥A ⧸ L.subgroupOf A) := by
    have hOodd : Odd (Nat.card ↥(pPrimeCoreOf 2 M)) := TwoThin.card_pPrimeCoreOf_odd M
    have : Group.IsSolvable ↥(pPrimeCoreOf 2 M) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hOodd
    let ψ : ↥(pPrimeCoreOf 2 M) →* ↥A ⧸ L.subgroupOf A :=
      (QuotientGroup.mk' _).comp (Subgroup.inclusion hOA)
    have hψ : Function.Surjective ψ := by
      intro q
      obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨l, hl, o, ho, hlo⟩ := (Th2.HY.mem_sup_iff_mul_of_le_normalizer hLN).1 ha
      refine ⟨⟨o, ho⟩, ?_⟩
      show QuotientGroup.mk (⟨o, hOA ho⟩ : ↥A) = QuotientGroup.mk ⟨a, ha⟩
      rw [QuotientGroup.eq]
      show o⁻¹ * a ∈ L
      have hono : o⁻¹ ∈ normalizer (L : Set G) := inv_mem (hAnorm (hOA ho))
      have e : o⁻¹ * a = o⁻¹ * l * (o⁻¹)⁻¹ := by rw [hlo]; group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.1 hono l).1 hl
    exact Group.isSolvable_of_surjective hψ
  have hYA : Y ≤ A := hY
  have h1 := Bk.B810.perfect_le_of_solvable_quotient (L.subgroupOf A) hsolv
    (P := Y.subgroupOf A) (commutator_subgroupOf_eq hYA hperf)
  intro y hy
  exact h1 (show (⟨y, hYA hy⟩ : ↥A) ∈ Y.subgroupOf A from hy)

end CFSG.GH74.GLS.PU3
