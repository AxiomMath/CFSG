module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigCos
public import Certificates.Certificate27274
public import Certificates.Certificate27275
public import Certificates.Certificate27276
public import Certificates.Certificate27277
public import Certificates.Certificate27278
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43CoverBase

public section

namespace CFSG.EvenSporadicStandard.HSStd.U43

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.M24Std.CU43

theorem rep_tabOf {n : ℕ} {a : Array ℕ} {g : Equiv.Perm (Fin n)} (hn : n < 2 ^ 32)
    (h : CFSG.Monster.B.Co2.Rep n a g) : Rep n (tabOf a) g := by
  intro i hi
  have e : ap (tabOf a) i = a[i]! := by
    unfold ap tabOf
    by_cases hia : i < a.size
    · have : a[i]! < 2 ^ 32 := by
        have h1 : a[i]! = (g ⟨i, hi⟩ : ℕ) := h ⟨i, hi⟩
        have h2 : (g ⟨i, hi⟩ : ℕ) < n := (g ⟨i, hi⟩).2
        omega
      rw [getElem!_pos (a.map UInt32.ofNat) i (by simpa using hia), Array.getElem_map,
        UInt32.toNat_ofNat', ← getElem!_pos a i hia]
      exact Nat.mod_eq_of_lt this
    · rw [getElem!_neg (a.map UInt32.ofNat) i (by simpa using hia), getElem!_neg a i hia]
      rfl
  rw [e, h ⟨i, hi⟩, idx_of_lt g hi]
  rfl

theorem rep_tabOf_rP {j : ℕ} (hj : j < 9) :
    Rep 820 (tabOf reps[j]!) (rP j) := rep_tabOf (by norm_num) (rep_rP hj)

theorem hG_of_cosSet
    {G : Subgroup (Equiv.Perm (Fin 820))} (hP : P ≤ G) (hR : G ≤ R) {ks : List ℕ} {K : Finset ℕ}
    (hK : cosSet G = K) (hKks : ∀ k, k ∈ K ↔ k ∈ ks) (hks8 : ∀ k ∈ ks, k < 8) :
    ∀ x, x ∈ G ↔ ∃ g ∈ P, ∃ k ∈ ks, k < 8 ∧ x = g * tP k := by
  intro x
  rw [mem_iff_cosSet hP hR]
  constructor
  · rintro ⟨g, hg, k, hk, rfl⟩
    rw [hK, hKks] at hk
    exact ⟨g, hg, k, hk, hks8 k hk, rfl⟩
  · rintro ⟨g, hg, k, hk, -, rfl⟩
    refine ⟨g, hg, k, ?_, rfl⟩
    rw [hK, hKks]
    exact hk

theorem solList_facts {d : CaseData} (hd : caseCheck d = true) :
    (solList d).length = d.nsol ∧ ∀ s ∈ solList d, cent5Of d s = 3 := by
  simp only [caseCheck, Bool.and_eq_true, beq_iff_eq] at hd
  obtain ⟨⟨-, hlen⟩, hall⟩ := hd
  refine ⟨hlen, fun s hs => ?_⟩
  have := List.all_eq_true.1 hall s hs
  exact beq_iff_eq.1 this

section Vacuous

theorem eq_of_rep {n : ℕ} {t : Table} {g h : Equiv.Perm (Fin n)} (hg : Rep n t g)
    (hh : Rep n t h) : g = h := by
  refine Equiv.ext fun x => Fin.ext ?_
  have e := (hg x x.2).symm.trans (hh x x.2)
  rw [idx_of_lt g x.2, idx_of_lt h x.2] at e
  simpa using e

theorem caseI4_vacuous {T y c k : Equiv.Perm (Fin 820)}
    (hT : Rep 820 (tabOf reps[4]!) T) (_hT2 : T * T = 1) (hs : SigRel T y c k) (hy : y ∈ R)
    (hc : c ∈ R) (hk : k ∈ R) : False := by
  rw [eq_of_rep hT (rep_tabOf_rP (by norm_num))] at hs
  exact Certificates.certificate27274 hs hy hc hk

theorem caseI5_vacuous {T y c k : Equiv.Perm (Fin 820)}
    (hT : Rep 820 (tabOf reps[5]!) T) (_hT2 : T * T = 1) (hs : SigRel T y c k) (hy : y ∈ R)
    (hc : c ∈ R) (hk : k ∈ R) : False := by
  rw [eq_of_rep hT (rep_tabOf_rP (by norm_num))] at hs
  exact Certificates.certificate27275 hs hy hc hk

end Vacuous

section Solutions

variable
  {G : Subgroup (Equiv.Perm (Fin 820))}

theorem card_of_cosSet_four (hP : P ≤ G) (hR : G ≤ R) (hK : (cosSet G).card = 4) :
    Nat.card G = 13063680 := by
  rw [card_eq_cosSet hP hR, hK, card_P]

theorem caseZ4_spec (hP : P ≤ G) (hR : G ≤ R)
    (hK : cosSet G = {0, 1, 2, 3}) {T y c k : Equiv.Perm (Fin 820)}
    (hT : Rep 820 (tabOf reps[8]!) T) (hT2 : T * T = 1) (hs : SigRel T y c k) (hy : y ∈ G)
    (hc : c ∈ G) (hk' : k ∈ G) :
    Nat.card ↥(G ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 820)))) = 1944 ∧
      Nat.card ↥(G ⊓ centralizer ({y, c, T * c * T⁻¹, k, T * k * T⁻¹} :
        Set (Equiv.Perm (Fin 820)))) = 3 := by
  have hd := Certificates.certificate27276
  have hG := hG_of_cosSet hP hR (ks := dZ4.ks) hK (by intro k; simp [dZ4])
    (by intro k hk; simp [dZ4] at hk; omega)
  have hsz : Nat.card G = dZ4.sizeG := card_of_cosSet_four hP hR (by rw [hK]; rfl)
  obtain ⟨s, hsmem, h1, h2⟩ := case_spec dZ4 hd hG hsz hT hT2 hs hy hc hk'
  exact ⟨h1, h2.trans ((solList_facts hd).2 s hsmem)⟩

theorem caseVb_spec (hP : P ≤ G) (hR : G ≤ R)
    (hK : cosSet G = {0, 2, 5, 7}) {T y c k : Equiv.Perm (Fin 820)}
    (hT : Rep 820 (tabOf reps[8]!) T) (hT2 : T * T = 1) (hs : SigRel T y c k) (hy : y ∈ G)
    (hc : c ∈ G) (hk' : k ∈ G) :
    Nat.card ↥(G ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 820)))) = 1944 ∧
      Nat.card ↥(G ⊓ centralizer ({y, c, T * c * T⁻¹, k, T * k * T⁻¹} :
        Set (Equiv.Perm (Fin 820)))) = 3 := by
  have hd := Certificates.certificate27277
  have hG := hG_of_cosSet hP hR (ks := dVb.ks) hK (by intro k; simp [dVb])
    (by intro k hk; simp [dVb] at hk; omega)
  have hsz : Nat.card G = dVb.sizeG := card_of_cosSet_four hP hR (by rw [hK]; rfl)
  obtain ⟨s, hsmem, h1, h2⟩ := case_spec dVb hd hG hsz hT hT2 hs hy hc hk'
  exact ⟨h1, h2.trans ((solList_facts hd).2 s hsmem)⟩

theorem va_central (hP : P ≤ G) (hR : G ≤ R)
    (hK : cosSet G = {0, 2, 4, 6})
    (hC : Nat.card ↥(G ⊓ centralizer ({rP 8} : Set (Equiv.Perm (Fin 820)))) = 2880) :
    ∃ z ∈ G, z ≠ 1 ∧ z ≠ rP 8 ∧ z * rP 8 = rP 8 * z ∧
      ∀ x ∈ G ⊓ centralizer ({rP 8} : Set (Equiv.Perm (Fin 820))), z * x = x * z := by
  have hd := Certificates.certificate27278
  have hG := hG_of_cosSet hP hR (ks := [0, 2, 4, 6]) hK (by intro k; simp)
    (by intro k hk; simp at hk; omega)
  have hT := rep_tabOf_rP (j := 8) (by norm_num)
  simp only [vaCheck, Bool.and_eq_true, Bool.not_eq_true', Array.all_eq_true'] at hd
  obtain ⟨⟨⟨⟨⟨⟨⟨hTp, hzp⟩, hzm⟩, hzc⟩, hz1⟩, hzT⟩, hcg⟩, hecg⟩ := hd
  have hzperm : permOK 820 (tabOf vaZ) = true := by
    have := hzp
    simp only [permInvOK, Bool.and_eq_true] at this
    exact this.1
  have hz : Rep 820 (tabOf vaZ) (tp 820 (tabOf vaZ)) := rep_tp hzperm
  obtain ⟨hcgperm, -, -, -, hcgcard, -, -⟩ := enumOK_spec hecg
  have hcgle : closure (tp 820 '' {x | x ∈ tabsOf vaCg}) ≤
      G ⊓ centralizer ({rP 8} : Set (Equiv.Perm (Fin 820))) := by
    rw [closure_le]
    rintro _ ⟨x, hx, rfl⟩
    refine mem_inf.2 ⟨mem_G_of_memCos hG (hcgperm x hx).1 (hcg x hx).1.1, ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact (commTT_iff (rep_tp (hcgperm x hx).1) hT).1 (hcg x hx).1.2
  have hCeq : closure (tp 820 '' {x | x ∈ tabsOf vaCg}) =
      G ⊓ centralizer ({rP 8} : Set (Equiv.Perm (Fin 820))) :=
    Subgroup.eq_of_le_of_card_ge hcgle (by rw [hcgcard, hC])
  have hzcomm : closure (tp 820 '' {x | x ∈ tabsOf vaCg}) ≤
      centralizer ({tp 820 (tabOf vaZ)} : Set (Equiv.Perm (Fin 820))) := by
    rw [closure_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact ((commTT_iff hz (rep_tp (hcgperm x hx).1)).1 (hcg x hx).2).symm
  have hzG : tp 820 (tabOf vaZ) ∈ G := mem_G_of_memCos hG hzperm hzm
  refine ⟨tp 820 (tabOf vaZ), hzG, ?_, ?_, ?_, ?_⟩
  · intro h
    have := (tblEq_idT_iff (by norm_num) hz).2 h
    rw [this] at hz1
    exact Bool.noConfusion hz1
  · intro h
    have := (tblEq_iff_eq hz hT).2 h
    rw [this] at hzT
    exact Bool.noConfusion hzT
  · exact (commTT_iff hz hT).1 hzc
  · intro x hx
    rw [← hCeq] at hx
    have := mem_centralizer_singleton_iff.1 (hzcomm hx)
    exact this.symm

end Solutions

end CFSG.EvenSporadicStandard.HSStd.U43
