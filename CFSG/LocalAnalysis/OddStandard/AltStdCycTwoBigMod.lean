module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoSplit
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdBasicConj

public section

namespace CFSG.OddStandard.AltStdCycTwo

open Subgroup Equiv Equiv.Perm AltStdBal CFSG.OddStandard.Solomon75
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

section OddPart

variable {G : Type} [Group G] [Finite G]

theorem mem_oddPart_of_odd_orderOf {H P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P)
    (hi : ¬ 2 ∣ P.relIndex H) (hc : IsCyclic P) {h : G} (hh : h ∈ H)
    (hodd : Odd (orderOf h)) : h ∈ oddPart H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf H) := hP.of_equiv (subgroupOfEquivOfLe hPH).symm
  let S : Sylow 2 H := hP'.toSylow hi
  have hS : IsCyclic S := by
    have h : IsCyclic (P.subgroupOf H) := (subgroupOfEquivOfLe hPH).isCyclic.2 hc
    exact h
  obtain ⟨-, -, -, ⟨hnormal, -, hindex, -⟩, -⟩ := cyclic_sylow_normal_odd_complement S hS
  have := hnormal
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  let h' : H := ⟨h, hh⟩
  have h1 : orderOf (QuotientGroup.mk' (pPrimeCore 2 H) h') ∣ orderOf h' :=
    orderOf_map_dvd _ h'
  have h2 : orderOf (QuotientGroup.mk' (pPrimeCore 2 H) h') ∣ 2 ^ k := by
    rw [← hk, ← hindex, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have hodd' : Odd (orderOf (QuotientGroup.mk' (pPrimeCore 2 H) h')) :=
    Odd.of_dvd_nat (by rw [Subgroup.orderOf_mk]; exact hodd) h1
  have h3 := Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd')) h2
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact Subgroup.mem_map.2 ⟨h', h3, rfl⟩

theorem oddPart_conj_mem_of_normalizes {H P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P)
    (hi : ¬ 2 ∣ P.relIndex H) (hc : IsCyclic P) {c : G} (hcH : ∀ h ∈ H, c * h * c⁻¹ ∈ H)
    {w : G} (hw : w ∈ oddPart H) : c * w * c⁻¹ ∈ oddPart H := by
  obtain ⟨hOH, -, hOodd, -, -⟩ := oddPart_spec hPH hP hi hc
  refine mem_oddPart_of_odd_orderOf hPH hP hi hc (hcH w (hOH hw)) ?_
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have h1 := orderOf_dvd_natCard (⟨w, hw⟩ : oddPart H)
  rw [Subgroup.orderOf_mk] at h1
  exact Odd.of_dvd_nat hOodd h1

end OddPart

section Junk

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {P : Subgroup G} {x : G}

theorem cyc_le_inf_cent (d : Cyc L P x) :
    P ≤ centralizer (L : Set G) ⊓ centralizer ({x} : Set G) :=
  le_inf d.le (le_centralizer_of_mem_isCyclic d.cyclic d.mem)

theorem cyc_odd_relIndex_inf (d : Cyc L P x) :
    ¬ 2 ∣ P.relIndex (centralizer (L : Set G) ⊓ centralizer ({x} : Set G)) := by
  intro h2
  apply d.odd_index
  exact h2.trans (Dvd.intro _ (relIndex_mul_relIndex P _ (centralizer (L : Set G))
    (cyc_le_inf_cent d) inf_le_left))

theorem conj_mem_cent_of_mem_normalizer {c k : G} (hc : c ∈ normalizer (L : Set G))
    (hk : k ∈ centralizer (L : Set G)) : c * k * c⁻¹ ∈ centralizer (L : Set G) := by
  rw [mem_centralizer_iff]
  intro h hh
  have h' : c⁻¹ * h * c ∈ L := by
    have := (mem_normalizer_iff.1 (inv_mem hc) h).1 hh
    simpa using this
  have hkh := mem_centralizer_iff.1 hk _ h'
  calc h * (c * k * c⁻¹) = c * ((c⁻¹ * h * c) * k) * c⁻¹ := by group
    _ = c * (k * (c⁻¹ * h * c)) * c⁻¹ := by rw [hkh]
    _ = c * k * c⁻¹ * h := by group

theorem oddJunk_conj_mem (hS : StandardSetting G L) (d : Cyc L P x) {c : G}
    (hc : c ∈ centralizer ({x} : Set G)) {w : G}
    (hw : w ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({x} : Set G))) :
    c * w * c⁻¹ ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({x} : Set G)) :=
  oddPart_conj_mem_of_normalizes (cyc_le_inf_cent d) d.pgroup (cyc_odd_relIndex_inf d) d.cyclic
    (fun _ hk => Subgroup.mem_inf.2 ⟨conj_mem_cent_of_mem_normalizer (cent_le_normalizer hS d hc)
      (Subgroup.mem_inf.1 hk).1, mul_mem (mul_mem hc (Subgroup.mem_inf.1 hk).2) (inv_mem hc)⟩) hw

theorem exists_mul_of_sign_eq_one (hS : StandardSetting G L) (θ : L ≃* alternatingGroup (Fin n))
    (hn : 8 ≤ n) (d : Cyc L P x) {m : G} (hm : m ∈ centralizer ({x} : Set G))
    (hmN : m ∈ normalizer (L : Set G)) (hme : sign (rho θ hn ⟨m, hmN⟩) = 1) :
    ∃ l ∈ L, ∃ k ∈ centralizer (L : Set G) ⊓ centralizer ({x} : Set G), m = l * k := by
  set l : L := θ.symm ⟨rho θ hn ⟨m, hmN⟩, mem_alternatingGroup.2 hme⟩ with hl
  have hlN : (l : G) ∈ normalizer (L : Set G) := Subgroup.le_normalizer l.2
  have hρl : rho θ hn ⟨l, hlN⟩ = rho θ hn ⟨m, hmN⟩ := by
    rw [rho_of_mem θ hn l hlN, hl, MulEquiv.apply_symm_apply]
  have hinv : (l : G)⁻¹ * m ∈ normalizer (L : Set G) := mul_mem (inv_mem hlN) hmN
  have h1 : rho θ hn ⟨(l : G)⁻¹ * m, hinv⟩ = 1 := by
    have : (⟨(l : G)⁻¹ * m, hinv⟩ : normalizer (L : Set G)) = ⟨l, hlN⟩⁻¹ * ⟨m, hmN⟩ := rfl
    rw [this, map_mul, map_inv, hρl, inv_mul_cancel]
  exact ⟨l, l.2, (l : G)⁻¹ * m, Subgroup.mem_inf.2 ⟨(rho_eq_one_iff θ hn _).1 h1,
    mul_mem (inv_mem (le_cent_single hS d l.2)) hm⟩, by group⟩

end Junk

section Conj

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_mem_cent_conj (hS : StandardSetting G L) {g : G}
    (hg : g ∉ normalizer (L : Set G)) {y : G} (hy : Even (orderOf y))
    (hyK : y ∈ centralizer (L : Set G))
    (hyK' : y ∈ CFSG.conjugate (centralizer (L : Set G)) g) : False := by
  have hy1 : y ∈ (centralizer (L : Set G)).map (MulAut.conj (1 : G)).toMonoidHom := by
    simpa using hyK
  have hgN := mem_normalizer_of_even_orderOf_mem hS.standard (a := 1) (b := g⁻¹) (x := y)
    hy hy1 hyK'
  have hgN' : g⁻¹ ∈ normalizer (centralizer (L : Set G) : Set G) := by simpa using hgN
  apply hg
  rw [← hS.standard.2.2.2.1]
  simpa using Subgroup.inv_mem _ hgN'

theorem stdSetting_conjugate (hS : StandardSetting G L) (g : G) :
    StandardSetting G (CFSG.conjugate L g) :=
  ⟨hS.simple, hS.nonab, hS.kProper, standardComponentIsStandard_conjugate g hS.standard⟩

end Conj

end CFSG.OddStandard.AltStdCycTwo
