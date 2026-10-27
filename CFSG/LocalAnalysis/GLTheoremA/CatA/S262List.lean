module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S262Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BAct
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S262

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem prime_dvd_card_pSimple {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ} (hp : p.Prime)
    {X J : Subgroup Ω} (hJ : GLAPComponent p X J) : p ∣ Nat.card (PSimple p J) := by
  by_contra hnd
  obtain ⟨-, hnab⟩ := chev_pSimple_simple_nonabelian hp hJ
  obtain ⟨a, b, hab⟩ := hnab
  have hbot := glaPPrimeCore_pSimple_eq_bot hp hJ
  have htop : (⊤ : Subgroup (PSimple p J)) ≤ GLAPPrimeCore p (PSimple p J) := by
    refine le_sSup ⟨inferInstance, ?_⟩
    rw [Subgroup.card_top]
    exact (hp.coprime_iff_not_dvd).2 hnd
  rw [hbot, top_le_iff] at htop
  apply hab
  have ha : a = 1 := by rw [← Subgroup.mem_bot, htop]; trivial
  have hb : b = 1 := by rw [← Subgroup.mem_bot, htop]; trivial
  rw [ha, hb]

theorem i262_of_nlAct (h : I262) {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X J B D : Subgroup Ω} (hB : IsElemAbelian p B) (hact : S265.NLAct p X J B D)
    (hcard : p ^ 2 * Nat.card D ≤ Nat.card B) (hchev : IsChevSimple 2 (PSimple p J)) :
    (p = 3 ∧ (catalogIs (PSimple p J) S265.tyA ∨ catalogIs (PSimple p J) S265.tyUn ∨
        catalogIs (PSimple p J) S265.tyC ∨ catalogIs (PSimple p J) S265.tyD)) ∨
      (p = 5 ∧ catalogIs (PSimple p J) S265.tyE) ∨ catalogIs (PSimple p J) (S265.tyF p) := by
  let φ : ↥B →* MulAut (PSimple p J) :=
    (chevAut p J).comp (Subgroup.inclusion hact.norm)
  let A : Subgroup (MulAut (PSimple p J)) := φ.range
  have hker : φ.ker = D.subgroupOf B := by
    ext e
    rw [Subgroup.mem_subgroupOf]
    exact hact.ker e.1 e.2 (hact.norm e.2)
  have hcardker : Nat.card ↥φ.ker = Nat.card ↥D := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hact.le).toEquiv
  have hcardB : Nat.card ↥B = Nat.card ↥D * Nat.card ↥A := by
    rw [← Subgroup.card_ker_mul_card_range φ, hcardker]
  have hAel : IsElemAbelian p A := by
    have h := CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hB B) φ
    rwa [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at h
  have hDpos : 0 < Nat.card ↥D := Nat.card_pos
  have hA2 : p ^ 2 ≤ Nat.card ↥A := by
    rw [hcardB, mul_comm (Nat.card ↥D) (Nat.card ↥A)] at hcard
    exact Nat.le_of_mul_le_mul_right hcard hDpos
  have hlayer : ∀ a ∈ A, a ≠ 1 → GLAPLayer p (fixSubgroup a) = ⊥ := by
    intro a haA ha1
    obtain ⟨e, he⟩ := haA
    have hφe : φ e ≠ 1 := fun h1 => ha1 (he.symm.trans h1)
    have heD : e.1 ∉ D := fun heD =>
      hφe ((hact.ker e.1 e.2 (hact.norm e.2)).2 heD)
    have hval : a = chevAut p J ⟨e.1, hact.norm e.2⟩ := by
      rw [← he]
      rfl
    rw [hval]
    exact hact.layer e.1 e.2 heD (hact.norm e.2)
  exact h p hp hp2 (PSimple p J) hchev (prime_dvd_card_pSimple hp hact.comp) A hAel hA2 hlayer

theorem qSList_of_i262 (h : I262)
    (hcl : ∀ (Ω : Type) [Group Ω] [Finite Ω] (p : ℕ), ChevClosureQAt Ω p)
    (h713 : CFSG.HardMathSupport.Solomon.Coordinator.I_7_13_1_pPrime) : S265.QSList := by
  intro p Ω _ _ S B T x D K hN
  have hc := hN.cfg
  obtain ⟨hDB, hDel, hDcard, hxD, hKlayer, hKcomp, hDK⟩ := hc.std
  have hSN : B ≤ Subgroup.normalizer (S : Set Ω) := fun g _ =>
    (Subgroup.normalizer_eq_top_iff.2 hc.normal) ▸ Subgroup.mem_top g
  have hBK : B ≤ Subgroup.normalizer (K : Set Ω) := S171.B_norm_K hc.elem hSN hc.std
  have hKS : K ≤ S := hKcomp.1.trans inf_le_left
  have hpK : p ∣ Nat.card ↥K := by
    have hquot : p ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) :=
      S171.dvd_of_faithful h713 hc.prime hc.odd (hc.kgroup.subgroup S) hKS hKcomp.2.2
        hc.elem hBK (by
          rw [← hDK, hDcard]
          calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
            _ ≤ Nat.card B := hc.big)
    exact hquot.trans (Subgroup.card_quotient_dvd_card (Subgroup.center ↥K))
  have hact : S265.NLAct p (S ⊓ cs D) K B D := hN.nlAct hpK
  have hchevK : IsChevSimple 2 (PSimple p K) :=
    hcl Ω p hc.prime hc.odd 2 Nat.prime_two ⊤ S D (hc.kgroup.subgroup ⊤) hc.comp hc.chev hDel
      (hDB.trans hSN) K hact.comp
  have hcard : p ^ 2 * Nat.card D ≤ Nat.card B := by
    rw [hDcard]
    calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
      _ ≤ Nat.card B := hc.big
  exact i262_of_nlAct h hc.prime hc.odd hc.elem hact hcard hchevK

section Certificates


theorem qUList_of_i262 (h : I262) : S265.QUList := by
  intro p Ω _ _ S B T x b hN
  have hc := hN.cfg
  have hchev : IsChevSimple 2 (PSimple p (Ipart p S b)) :=
    (FR.i91CompAt_holds (G := Ω) hc.prime hc.odd ⊤ S b hc.comp hc.chev
      (hc.elem.2 b hc.hb) hc.prop hc.ipart).2
  have hDgrp : Nat.card (Dgrp b x) = p ^ 2 :=
    (S10.card_Dgrp hc.elem hc.prime hc.hb hc.xB hc.x1 hc.hbx).2.2
  have hact : S265.NLAct p (S ⊓ cx b) (Ipart p S b) B (Dgrp b x) := hN.nlAct
  have hcard : p ^ 2 * Nat.card (Dgrp b x) ≤ Nat.card B := by
    rw [hDgrp]
    calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
      _ ≤ Nat.card B := hc.big
  exact i262_of_nlAct h hc.prime hc.odd hc.elem hact hcard hchev

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.S262

end
