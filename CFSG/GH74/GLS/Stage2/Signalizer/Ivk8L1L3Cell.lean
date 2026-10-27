module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1Norm
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1Syl
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Abs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Kind
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Gen
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Closed
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812Stmt
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Stmt10
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Stmt12
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Stmt9
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Stmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Open
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt42
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt5
public import CFSG.GH74.Uniqueness.SU.SU13TA1Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12

section Rank

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}

theorem rank_contra_of_index_two (hfr : AFrame A zb Sb Vb) [J.Normal]
    (hidx : Nat.card ↥(J.subgroupOf Sb) * 2 = Nat.card ↥Sb)
    (hrank : ∀ E : Subgroup ↥J, IsElementaryAbelian 2 ↥E → Nat.card ↥E ≤ 4) : False := by
  obtain ⟨E, hEc, hEs, hE16⟩ := exists_elemAbelian_sb hfr
  let ψ : ↥Sb →* A ⧸ J := (QuotientGroup.mk' J).comp Sb.subtype
  have hker : ψ.ker = J.subgroupOf Sb := by
    ext s
    simp [ψ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hrange : Nat.card ↥ψ.range = 2 := by
    have h1 := Subgroup.card_ker_mul_card_range ψ
    rw [hker] at h1
    have h0 : 0 < Nat.card ↥(J.subgroupOf Sb) := Nat.card_pos
    have : Nat.card ↥(J.subgroupOf Sb) * Nat.card ↥ψ.range =
        Nat.card ↥(J.subgroupOf Sb) * 2 := by rw [h1, hidx]
    exact Nat.eq_of_mul_eq_mul_left h0 this
  let ψE : ↥E →* A ⧸ J := ψ.comp E.subtype
  have hEk := Subgroup.card_ker_mul_card_range ψE
  have hrangeE : Nat.card ↥ψE.range ≤ 2 := by
    have hle : ψE.range ≤ ψ.range := by
      rintro _ ⟨e, rfl⟩
      exact ⟨(e : ↥Sb), rfl⟩
    exact (Subgroup.card_le_of_le hle).trans hrange.le
  have hkerE : 8 ≤ Nat.card ↥ψE.ker := by
    by_contra h
    push Not at h
    have : Nat.card ↥ψE.ker * Nat.card ↥ψE.range ≤ 7 * 2 :=
      Nat.mul_le_mul (by omega) hrangeE
    omega
  have hmem : ∀ x : ↥ψE.ker, (((x : ↥E) : ↥Sb) : A) ∈ J := fun x =>
    (QuotientGroup.eq_one_iff _).mp x.2
  let g : ↥ψE.ker →* ↥J :=
    MonoidHom.codRestrict (Sb.subtype.comp (E.subtype.comp ψE.ker.subtype)) J hmem
  have hg : Function.Injective g := by
    intro x y hxy
    have h1 : (((x : ↥E) : ↥Sb) : A) = (((y : ↥E) : ↥Sb) : A) :=
      congrArg (fun z : ↥J => (z : A)) hxy
    exact Subtype.ext (Subtype.ext (Subtype.ext h1))
  let K₀ : Subgroup ↥J := g.range
  have hK₀ : Nat.card ↥K₀ = Nat.card ↥ψE.ker :=
    (Nat.card_congr (MonoidHom.ofInjective hg).toEquiv).symm
  have hKc : ∀ a ∈ K₀, ∀ b ∈ K₀, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subtype.ext (hEc _ (x : ↥E).2 _ (y : ↥E).2))
  have hKs : ∀ a ∈ K₀, a * a = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (Subtype.ext (hEs _ (x : ↥E).2))
    rw [this, map_one]
  have := hrank K₀ (isElementaryAbelian_of_comm_sq K₀ hKc hKs)
  omega

end Rank

section Transport

theorem isSection_congr {X X' B : Type*} [Group X] [Group X'] [Group B] (e : X ≃* X')
    (h : IsSection X B) : IsSection X' B := by
  obtain ⟨U, φ, hφ⟩ := h
  exact ⟨U, e.toMonoidHom.comp φ, e.surjective.comp hφ⟩

theorem isSection_cent_of_equiv {J Y X : Type*} [Group J] [Group Y] [Group X] (e : J ≃* Y) (u : J)
    (h : IsSection X ↥(centralizer ({e u} : Set Y))) :
    IsSection X ↥(centralizer ({u} : Set J)) := by
  let f : ↥(centralizer ({u} : Set J)) →* ↥(centralizer ({e u} : Set Y)) :=
    (e.toMonoidHom.comp (centralizer ({u} : Set J)).subtype).codRestrict _ (fun x => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp x.2
      show e (x : J) * e u = e u * e (x : J)
      rw [← map_mul, ← map_mul, h1])
  have hf : Function.Surjective f := by
    intro y
    refine ⟨⟨e.symm y.1, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_centralizer_singleton_iff.mp y.2
    · apply Subtype.ext
      exact e.apply_symm_apply _
  exact IsSection.of_surjective f hf h

theorem comm_sq_of_isElementaryAbelian {M : Type*} [Group M] {E : Subgroup M}
    (hE : IsElementaryAbelian 2 ↥E) :
    (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ ∀ x ∈ E, x * x = 1 := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · exact congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
  · have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) x hx
    rwa [pow_two] at this

theorem isElementaryAbelian_map {X Z : Type*} [Group X] [Group Z] (f : X →* Z) {E : Subgroup X}
    (hE : IsElementaryAbelian 2 ↥E) : IsElementaryAbelian 2 ↥(E.map f) := by
  obtain ⟨hc, hs⟩ := comm_sq_of_isElementaryAbelian hE
  refine isElementaryAbelian_of_comm_sq _ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hs a ha, map_one]

end Transport

section Cell

structure FL3Facts : Prop where
  card : ∀ (Y : Type) [Group Y] [Finite Y] {p f : ℕ}, p.Prime → 1 ≤ f → p ≠ 2 →
    LieModel Y .PSL 3 p f →
      Nat.card Y * Nat.gcd 3 (p ^ f - 1) = (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)
  not_dvd : ∀ (Y : Type) [Group Y] [Finite Y], FL3 Y → ¬ Nat.card Y ∣ Nat.factorial 11
  sec : ∀ (Y : Type) [Group Y] [Finite Y] {p f : ℕ}, p.Prime → 1 ≤ f → p ≠ 2 →
    LieModel Y .PSL 3 p f → ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      ∀ t : Y, orderOf t = 2 → IsSection (IVK.L2 F) ↥(centralizer ({t} : Set Y))
  aut : ∀ (Y : Type) [Group Y] [Finite Y] {p f : ℕ}, p.Prime → 1 ≤ f → p ≠ 2 →
    LieModel Y .PSL 3 p f → Nat.card (MulAut Y) ∣ Nat.card Y * (6 * f)
  rank : ∀ (Y : Type) [Group Y] [Finite Y] {p f : ℕ}, p.Prime → 1 ≤ f → p ≠ 2 →
    LieModel Y .PSL 3 p f → ∀ E : Subgroup Y, IsElementaryAbelian 2 ↥E → Nat.card ↥E ≤ 4

theorem cellAbs_FL3_of_facts (h : FL3Facts) : CellAbs FL3 := by
  intro A _ _ zb Sb Vb J hfr hJ hnc hY
  exfalso
  have hnot : ¬ KindFactorAll Kind.ly (↥J ⧸ center ↥J) := fun hk =>
    h.not_dvd _ hY (KindFactorAll.card_dvd hk (Or.inr rfl))
  obtain ⟨hZ, hu, hzbJ⟩ := hfr.reduce hJ hnot
  obtain ⟨p, f, hp, hf, hp2, hLie⟩ := hY
  have hJn : J.Normal := Gen.normal_of_unique_comp hJ hu
  let eJ : ↥J ≃* (↥J ⧸ center ↥J) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  obtain ⟨φ, hφ, -⟩ := hfr.embed_aut hJ hZ hu
  have h28 : 2 ^ 8 ∣ Nat.card (↥J ⧸ center ↥J) * (6 * f) := by
    have h1 : Nat.card ↥Sb ∣ Nat.card (MulAut ↥J) := by
      rw [Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    rw [hfr.card] at h1
    have h2 : Nat.card (MulAut ↥J) = Nat.card (MulAut (↥J ⧸ center ↥J)) :=
      Nat.card_congr (MulAut.congr eJ).toEquiv
    exact (h2 ▸ h1).trans (h.aut _ hp hf hp2 hLie)
  have hcard := h.card _ hp hf hp2 hLie
  by_cases hq : p ^ f = 3 ∨ p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 11
  ·
    rcases hq with h3 | h5 | h7 | h11
    · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp h3
      norm_num at hcard h28
      omega
    · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_five).mp h5
      norm_num at hcard h28
      omega
    · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp h7
      norm_num at hcard h28
      omega
    · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 11)).mp h11
      norm_num at hcard h28
      omega
  · by_cases hq9 : p ^ f = 9
    ·
      have hY9 : Nat.card (↥J ⧸ center ↥J) = 42456960 := by
        rw [hq9] at hcard
        norm_num at hcard
        omega
      have hJ9 : Nat.card ↥J = 42456960 := (Nat.card_congr eJ.toEquiv).trans hY9
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hsyl : CFSG.ABGLocalTools.IsSylowOf 2 (Sb ⊓ J) J :=
        hfr.sylow.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top])
      have h2part : (Nat.card ↥J).factorization 2 = 7 := by
        rw [hJ9, show (42456960 : ℕ) = 2 ^ 7 * 331695 by norm_num,
          Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
          Nat.Prime.factorization_pow Nat.prime_two,
          Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
        simp
      have hSbJ : Nat.card ↥(Sb ⊓ J) = 2 ^ 7 := by rw [hsyl.card_eq, h2part]
      have hidx : Nat.card ↥(J.subgroupOf Sb) * 2 = Nat.card ↥Sb := by
        have h1 : Nat.card ↥(J.subgroupOf Sb) = Nat.card ↥(J ⊓ Sb) := by
          rw [← Subgroup.subgroupOf_map_subtype J Sb,
            Subgroup.card_map_of_injective Sb.subtype_injective]
        rw [h1, inf_comm, hSbJ, hfr.card]
        norm_num
      have hrankJ : ∀ E : Subgroup ↥J, IsElementaryAbelian 2 ↥E → Nat.card ↥E ≤ 4 := by
        intro E hE
        have := h.rank _ hp hf hp2 hLie (E.map eJ.toMonoidHom)
          (isElementaryAbelian_map eJ.toMonoidHom hE)
        rwa [Subgroup.card_map_of_injective eJ.injective] at this
      exact rank_contra_of_index_two hfr hidx hrankJ
    ·
      obtain ⟨F, _, _, hFq, hsec⟩ := h.sec _ hp hf hp2 hLie
      have hodd : Odd (Nat.card F) := by
        rw [hFq]
        exact (hp.odd_of_ne_two hp2).pow
      have h5 : 5 ≤ Nat.card F := by
        have h3' : 3 ≤ p ^ f := by
          have := hp.two_le
          calc 3 ≤ p := by omega
            _ ≤ p ^ f := Nat.le_self_pow (by omega) p
        have := Nat.odd_iff.mp hodd
        rw [hFq] at this ⊢
        omega
      have hu0 : orderOf (⟨zb, hzbJ⟩ : ↥J) = 2 := by
        rw [Subgroup.orderOf_mk]
        exact hfr.zb_ord
      have ht : orderOf (eJ ⟨zb, hzbJ⟩) = 2 := by
        rw [MulEquiv.orderOf_eq]
        exact hu0
      have hsecJ := isSection_cent_of_equiv eJ _ (hsec _ ht)
      have hsec' : IsSection (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
          ↥(centralizer ({(⟨zb, hzbJ⟩ : ↥J)} : Set ↥J)) :=
        isSection_congr (IVK.L2.equivPSL F) hsecJ
      have := psl2_simple (F := F) (by omega)
      have hkfa := kfa_of_cent_section hfr J ⟨zb, hzbJ⟩ hu0 (psl2_not_isSolvable (by omega)) hsec'
      have := card_of_kfa_psl2 hodd h5 hkfa
      rw [hFq] at this
      omega

end Cell

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1
