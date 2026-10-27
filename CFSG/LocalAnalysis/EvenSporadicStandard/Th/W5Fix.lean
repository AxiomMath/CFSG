module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5Odd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5Index
public import CFSG.RankThree.Coprime.SolvableFixedCommutator

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa : Subgroup G}
  {z b : G}

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)

include H W W2

theorem ThCyc.mem_zpowers_of_commute_k {k : G} (hkL : k ∈ L)
    (hfix : ∀ x ∈ A, k * x * k⁻¹ = x → x = 1) {c : G}
    (hc : c ∈ Bp A t ⊓ centralizer (Aa : Set G)) (hkc : k * c = c * k) : c ∈ zpowers t := by
  have hcW := H.centralizer_le_Y W hkL hfix hc.1 hkc
  obtain ⟨x, hx, e, rfl⟩ := (H.mem_centralizer_W5_inf_centralizer_Aa_iff W W2).1 ⟨hcW, hc.2⟩
  have hkt : k * t ^ e * k⁻¹ = t ^ e := by
    have : t ^ e * k = k * t ^ e :=
      ((show Commute t k from H.comm_of_mem_L hkL).zpow_left e).eq
    rw [← this]
    group
  have h1 : k * (x * t ^ e) * k⁻¹ = x * t ^ e := by
    rw [hkc]
    group
  have h2 : (k * x * k⁻¹) * t ^ e = x * t ^ e := by
    calc (k * x * k⁻¹) * t ^ e = (k * x * k⁻¹) * (k * t ^ e * k⁻¹) := by rw [hkt]
      _ = k * (x * t ^ e) * k⁻¹ := by group
      _ = x * t ^ e := h1
  have hkx : k * x * k⁻¹ = x := mul_right_cancel h2
  have hx1 : x = 1 := W2.eq_one_of_fixed W hfix hx hkx
  rw [hx1, one_mul]
  exact zpow_mem (mem_zpowers t) e

theorem ThCyc.commute_k_iff_mem_zpowers {k : G} (hkL : k ∈ L)
    (hfix : ∀ x ∈ A, k * x * k⁻¹ = x → x = 1) {c : G}
    (hc : c ∈ Bp A t ⊓ centralizer (Aa : Set G)) : k * c = c * k ↔ c ∈ zpowers t := by
  refine ⟨H.mem_zpowers_of_commute_k W W2 hkL hfix hc, fun h => ?_⟩
  obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
  exact (((show Commute t k from H.comm_of_mem_L hkL).zpow_left e).eq).symm

theorem ThCyc.mem_normalizer_inf_centralizer_Aa {k : G} (hkL : k ∈ L)
    (hkA : ∀ x ∈ A, k * x * k⁻¹ ∈ A) :
    k ∈ normalizer ((Bp A t ⊓ centralizer (Aa : Set G) : Subgroup G) : Set G) := by
  have hkN := H.mem_normalizer_W5_of_L W hkL hkA
  refine mem_normalizer_iff.2 fun c =>
    ⟨fun hc => H.conj_mem_inf_centralizer_Aa W W2 hkN hc, fun hc => ?_⟩
  have := H.conj_mem_inf_centralizer_Aa W W2 ((normalizer _).inv_mem hkN) hc
  have e : k⁻¹ * (k * c * k⁻¹) * k⁻¹⁻¹ = c := by group
  rwa [e] at this

end

@[expose] def kCommutator (C : Subgroup G) (k : G) : Subgroup G :=
  closure {x | ∃ c ∈ C, ∃ a ∈ zpowers k, x = c⁻¹ * (a * c * a⁻¹)}

omit [Finite G] in
open CFSG.LocalAnalysis.ComponentInitial in
theorem map_actionCommutator_subtype (K C : Subgroup G) [Subgroup.Normalizes K C]
    (D : Subgroup ↥C) :
    (actionCommutator ↥K D).map C.subtype =
      closure {x | ∃ d ∈ D.map C.subtype, ∃ a ∈ K, x = d⁻¹ * (a * d * a⁻¹)} := by
  unfold actionCommutator
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨h, hh, a, rfl⟩, rfl⟩
    refine ⟨(h : G), ⟨h, hh, rfl⟩, a, a.2, ?_⟩
    simp
  · rintro ⟨_, ⟨h, hh, rfl⟩, a, ha, rfl⟩
    refine ⟨h⁻¹ * ((⟨a, ha⟩ : ↥K) • h), ⟨h, hh, ⟨a, ha⟩, rfl⟩, ?_⟩
    simp

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)

include H W W2

theorem ThCyc.kCommutator_factorization {C : Subgroup G}
    (hC : C = Bp A t ⊓ centralizer (Aa : Set G)) {k : G} (hkL : k ∈ L)
    (hkA : ∀ x ∈ A, k * x * k⁻¹ ∈ A) (hodd : Odd (orderOf k))
    (hfix : ∀ x ∈ A, k * x * k⁻¹ = x → x = 1) :
    kCommutator C k ≤ C ∧
    (∀ c ∈ C, ∀ d ∈ kCommutator C k, c * d * c⁻¹ ∈ kCommutator C k) ∧
    (∀ d ∈ kCommutator C k, k * d * k⁻¹ ∈ kCommutator C k) ∧
    closure {x | ∃ d ∈ kCommutator C k, ∃ a ∈ zpowers k, x = d⁻¹ * (a * d * a⁻¹)} =
      kCommutator C k ∧
    ∀ c ∈ C, ∃ d ∈ kCommutator C k, ∃ e ∈ zpowers t, c = d * e := by
  classical
  subst hC
  set C : Subgroup G := Bp A t ⊓ centralizer (Aa : Set G) with hC
  have hkn : k ∈ normalizer (C : Set G) := H.mem_normalizer_inf_centralizer_Aa W W2 hkL hkA
  have : Subgroup.Normalizes (zpowers k) C := ⟨(zpowers_le).2 hkn⟩
  have hCorder : Nat.card C = 2 ^ 13 := H.natCard_Bp_inf_centralizer_Aa W W2
  have hsolv : Group.IsSolvable ↥C := by
    have h2 : IsPGroup 2 ↥C := IsPGroup.of_card hCorder
    have : Group.IsNilpotent ↥C := h2.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card ↥C) (Nat.card ↥(zpowers k)) := by
    rw [hCorder, Nat.card_zpowers]
    exact Nat.Coprime.pow_left 13 (Nat.coprime_two_left.2 hodd)
  obtain ⟨hDn, hDinv, hfac, hDD⟩ :=
    CFSG.RankThree.Coprime.solvable_coprime_fixed_commutator_factorization hsolv hcop
  set Dc := CFSG.LocalAnalysis.ComponentInitial.actionCommutator ↥(zpowers k) (⊤ : Subgroup ↥C)
    with hDc
  have hDg : kCommutator C k = Dc.map C.subtype := by
    rw [hDc, map_actionCommutator_subtype (zpowers k) C ⊤, Subgroup.map_top, Subgroup.range_subtype]
    rfl
  rw [hDg]
  refine ⟨Subgroup.map_subtype_le Dc, ?_, ?_, ?_, ?_⟩
  · rintro c hc _ ⟨d, hd, rfl⟩
    exact ⟨(⟨c, hc⟩ : ↥C) * d * (⟨c, hc⟩ : ↥C)⁻¹, hDn.conj_mem d hd ⟨c, hc⟩, rfl⟩
  · rintro _ ⟨d, hd, rfl⟩
    refine ⟨(⟨k, mem_zpowers k⟩ : ↥(zpowers k)) • d, hDinv _ d hd, ?_⟩
    simp
  · have := congrArg (Subgroup.map C.subtype) hDD
    rw [map_actionCommutator_subtype (zpowers k) C Dc] at this
    exact this
  · intro c hc
    obtain ⟨d, hd, f, hf, hcf⟩ := hfac ⟨c, hc⟩
    have hfk : k * (f : G) = (f : G) * k := by
      have h := hf ⟨k, mem_zpowers k⟩
      have h' := congrArg Subtype.val h
      simp at h'
      calc k * (f : G) = k * (f : G) * k⁻¹ * k := by group
        _ = (f : G) * k := by rw [h']
    refine ⟨d, ⟨d, hd, rfl⟩, f, ?_, ?_⟩
    · exact (H.commute_k_iff_mem_zpowers W W2 hkL hfix f.2).1 hfk
    · exact congrArg Subtype.val hcf

end

end CFSG.EvenSporadicStandard.ThStd
