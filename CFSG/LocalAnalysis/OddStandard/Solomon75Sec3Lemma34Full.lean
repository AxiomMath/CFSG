module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma34
public import CFSG.LocalAnalysis.OddStandard.GH71.Covers
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Tools

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

section Abstract

variable {X : Type} [Group X] [Finite X]

theorem exists_fixed_of_odd_coset_amb (N : Subgroup X) (hodd : Odd (Nat.card N))
    {t h : X} (ht : t ∈ normalizer (N : Set X)) (hh : h ∈ normalizer (N : Set X))
    (ht2 : t * t = 1) (hth : t * h * t⁻¹ * h⁻¹ ∈ N) :
    ∃ n ∈ N, t * (h * n) * t⁻¹ = h * n := by
  set Kn : Subgroup X := normalizer (N : Set X) with hKn
  have hNK : N ≤ Kn := Subgroup.le_normalizer
  haveI : (N.subgroupOf Kn).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).2 le_rfl
  have hodd' : Odd (Nat.card (N.subgroupOf Kn)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv]
    exact hodd
  have hmem : (⟨t, ht⟩ : Kn) * ⟨h, hh⟩ * (⟨t, ht⟩ : Kn)⁻¹ * (⟨h, hh⟩ : Kn)⁻¹ ∈
      N.subgroupOf Kn := hth
  obtain ⟨n, hn, hfix⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.exists_fixed_of_odd_coset
    (K := ↥Kn) (N.subgroupOf Kn) hodd' ⟨t, ht⟩ (Subtype.ext ht2) ⟨h, hh⟩ hmem
  exact ⟨(n : X), Subgroup.mem_subgroupOf.1 hn, congrArg Subtype.val hfix⟩

theorem exists_oddCore_cen_mul_cen {D B : Subgroup X} {s d : X}
    (hs2 : s * s = 1) (hsB : s ∈ B) (hBD : B ≤ D) (hDB : D ≤ pPrimeCoreOf 2 D ⊔ B)
    (hd : d ∈ D) (hds : s * d = d * s) :
    ∃ q ∈ pPrimeCoreOf 2 D ⊓ centralizer ({s} : Set X), ∃ b ∈ B ⊓ centralizer ({s} : Set X),
      d = q * b := by
  set P : Subgroup X := pPrimeCoreOf 2 D with hP
  have hPn : ∀ g ∈ D, g ∈ normalizer (P : Set X) :=
    fun g hg => mem_normalizer_pPrimeCoreOf_of_mem hg
  have hBP : B ≤ normalizer (P : Set X) := fun g hg => hPn g (hBD hg)
  obtain ⟨o, ho, b, hb, hdob⟩ :=
    (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing P B hBP d).1 (hDB hd)
  set N' : Subgroup X := B ⊓ P with hN'
  have hN'odd : Odd (Nat.card N') :=
    Odd.of_dvd_nat (odd_card_oddCoreOf D) (Subgroup.card_dvd_of_le inf_le_right)
  have hN'norm : ∀ g ∈ B, g ∈ normalizer (N' : Set X) := fun g hg =>
    mem_normalizer_inf (Subgroup.le_normalizer hg) (hBP hg)
  have hsos : s * o * s⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 (hPn s (hBD hsB)) o).1 ho
  have h1 : s * (o * b) * s⁻¹ = o * b := by
    have := hds
    rw [← hdob] at this
    exact mul_inv_eq_iff_eq_mul.2 this
  have hcomm : s * b * s⁻¹ * b⁻¹ ∈ N' := by
    refine ⟨B.mul_mem (B.mul_mem (B.mul_mem hsB hb) (B.inv_mem hsB)) (B.inv_mem hb), ?_⟩
    have e : s * b * s⁻¹ * b⁻¹ = (s * o * s⁻¹)⁻¹ * o := by
      calc s * b * s⁻¹ * b⁻¹ = (s * o * s⁻¹)⁻¹ * (s * (o * b) * s⁻¹) * b⁻¹ := by group
        _ = (s * o * s⁻¹)⁻¹ * (o * b) * b⁻¹ := by rw [h1]
        _ = (s * o * s⁻¹)⁻¹ * o := by group
    rw [e]
    exact P.mul_mem (P.inv_mem hsos) ho
  obtain ⟨n, hn, hfix⟩ :=
    exists_fixed_of_odd_coset_amb N' hN'odd (hN'norm s hsB) (hN'norm b hb) hs2 hcomm
  have hbn : b * n ∈ B := B.mul_mem hb hn.1
  have hcb : (b * n) * s = s * (b * n) := (mul_inv_eq_iff_eq_mul.1 hfix).symm
  have hbnC : b * n ∈ centralizer ({s} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hcb
  have hq : d * (b * n)⁻¹ ∈ P := by
    have e : d * (b * n)⁻¹ = o * (b * n⁻¹ * b⁻¹) := by rw [← hdob]; group
    rw [e]
    exact P.mul_mem ho ((Subgroup.mem_normalizer_iff.1 (hBP hb) n⁻¹).1 (P.inv_mem hn.2))
  have hqC : d * (b * n)⁻¹ ∈ centralizer ({s} : Set X) := by
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have hd' : Commute d s := hds.symm
    have hb' : Commute (b * n) s := hcb
    exact (hd'.mul_left hb'.inv_left).eq
  exact ⟨d * (b * n)⁻¹, ⟨hq, hqC⟩, b * n, ⟨hbn, hbnC⟩, by group⟩

theorem cen_oddCoreOf_le_oddCoreOf {C L : Subgroup X} {z₀ : X} (hz2 : z₀ ^ 2 = 1)
    (hLC : L ≤ C) (hLn : C ≤ normalizer (L : Set X)) (hOL : pPrimeCoreOf 2 C ≤ L)
    (hzL : z₀ ∈ zStar L) :
    pPrimeCoreOf 2 (centralizer ({z₀} : Set X)) ⊓ C ≤ pPrimeCoreOf 2 C := by
  set D : Subgroup X := centralizer ({z₀} : Set X) with hD
  set O : Subgroup X := pPrimeCoreOf 2 C with hO
  set Q : Subgroup X := pPrimeCoreOf 2 D ⊓ C with hQ
  have hPn : ∀ g ∈ D, g ∈ normalizer (pPrimeCoreOf 2 D : Set X) :=
    fun g hg => mem_normalizer_pPrimeCoreOf_of_mem hg
  have hOC : O ≤ C := oddCoreOf_le C
  have hCO : C ≤ normalizer (O : Set X) := le_normalizer_oddCoreOf C
  have hoddO : Odd (Nat.card O) := odd_card_oddCoreOf C
  have hCLO : C ≤ normalizer (pPrimeCoreOf 2 L : Set X) :=
    hLn.trans (normalizer_le_normalizer_pPrimeCoreOf L)
  have hOLO : pPrimeCoreOf 2 L ≤ O :=
    le_oddCoreOf_of_normalized ((oddCoreOf_le L).trans hLC) hCLO (odd_card_oddCoreOf L)
  have hLR : ∀ y ∈ L, ∃ o ∈ pPrimeCoreOf 2 L, ∃ r ∈ L ⊓ D, y = o * r :=
    fun y hy => exists_mul_eq_of_mem_zStar_involution hzL hz2 hy
  have hcovL : CFSG.GH74.GLS.Stage2.Signalizer.Covers D L (pPrimeCoreOf 2 L) := by
    intro y hy
    obtain ⟨o, ho, r, hr, rfl⟩ := hLR y hy
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ho) (Subgroup.mem_sup_left ⟨hr.2, hr.1⟩)
  have hQL : Q ⊓ L ≤ pPrimeCoreOf 2 L := by
    refine CFSG.OddStandard.GH71.le_pPrimeCoreOf_of_covers hcovL inf_le_right ?_ ?_
    · exact Odd.of_dvd_nat (odd_card_oddCoreOf D)
        (Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left))
    · intro x hx
      exact mem_normalizer_inf (mem_normalizer_inf (hPn x hx.1)
        (Subgroup.le_normalizer (hLC hx.2))) (Subgroup.le_normalizer hx.2)
  set Cc : Subgroup X := C ⊓ centralizerSection L O with hCc
  have hCcC : Cc ≤ C := inf_le_left
  have hCcnorm : ∀ g ∈ C, ∀ c ∈ Cc, g * c * g⁻¹ ∈ Cc := by
    intro g hg c hc
    obtain ⟨hcC, hcL, hcO, hcom⟩ := hc
    refine ⟨C.mul_mem (C.mul_mem hg hcC) (C.inv_mem hg), ?_, ?_, ?_⟩
    · exact (normalizer (L : Set X)).mul_mem ((normalizer (L : Set X)).mul_mem (hLn hg) hcL)
        ((normalizer (L : Set X)).inv_mem (hLn hg))
    · exact (normalizer (O : Set X)).mul_mem ((normalizer (O : Set X)).mul_mem (hCO hg) hcO)
        ((normalizer (O : Set X)).inv_mem (hCO hg))
    · intro k hk
      have hk' : g⁻¹ * k * g ∈ L := by
        have := (Subgroup.mem_normalizer_iff.1 (hLn (C.inv_mem hg)) k).1 hk
        simpa using this
      have h1 := hcom _ hk'
      have h2 : g * ⁅g⁻¹ * k * g, c⁆ * g⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hCO hg) _).1 h1
      have e : ⁅k, g * c * g⁻¹⁆ = g * ⁅g⁻¹ * k * g, c⁆ * g⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact h2
  have hCCc : C ≤ normalizer (Cc : Set X) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => hCcnorm g hg c hc, fun hc => ?_⟩
    have := hCcnorm g⁻¹ (C.inv_mem hg) _ hc
    simpa [mul_assoc] using this
  have hΘ : pPrimeCoreOf 2 Cc ≤ O :=
    le_oddCoreOf_of_normalized ((oddCoreOf_le Cc).trans hCcC)
      (hCCc.trans (normalizer_le_normalizer_pPrimeCoreOf Cc)) (odd_card_oddCoreOf Cc)
  have hQCc : Q ≤ Cc := by
    intro q hq
    have hqP : q ∈ pPrimeCoreOf 2 D := hq.1
    have hqC : q ∈ C := hq.2
    refine ⟨hqC, hLn hqC, hCO hqC, fun k hk => ?_⟩
    obtain ⟨o, ho, r, hr, rfl⟩ := hLR k hk
    have hrD : r ∈ D := hr.2
    have hrL : r ∈ L := hr.1
    have hrq1 : r * q * r⁻¹ ∈ Q :=
      ⟨(Subgroup.mem_normalizer_iff.1 (hPn r hrD) q).1 hqP,
        C.mul_mem (C.mul_mem (hLC hrL) hqC) (C.inv_mem (hLC hrL))⟩
    have hcomm1 : ⁅r, q⁆ ∈ Q := by
      have e : ⁅r, q⁆ = (r * q * r⁻¹) * q⁻¹ := by simp only [commutatorElement_def]
      rw [e]
      exact Q.mul_mem hrq1 (Q.inv_mem hq)
    have hcomm2 : ⁅r, q⁆ ∈ L := by
      have e : ⁅r, q⁆ = r * (q * r⁻¹ * q⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact L.mul_mem hrL ((Subgroup.mem_normalizer_iff.1 (hLn hqC) r⁻¹).1 (L.inv_mem hrL))
    have hrqO : ⁅r, q⁆ ∈ O := hOLO (hQL ⟨hcomm1, hcomm2⟩)
    have e : ⁅o * r, q⁆ = o * ⁅r, q⁆ * (q * o⁻¹ * q⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact O.mul_mem (O.mul_mem (hOLO ho) hrqO)
      ((Subgroup.mem_normalizer_iff.1 (hCO hqC) o⁻¹).1 (O.inv_mem (hOLO ho)))
  have hOCc : O ≤ Cc := by
    intro o ho
    refine ⟨hOC ho, hLn (hOC ho), hCO (hOC ho), fun k hk => ?_⟩
    have e : ⁅k, o⁆ = (k * o * k⁻¹) * o⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact O.mul_mem ((Subgroup.mem_normalizer_iff.1 (hCO (hLC hk)) o).1 ho) (O.inv_mem ho)
  have hOCc' : O ≤ pPrimeCoreOf 2 Cc :=
    le_oddCoreOf_of_normalized hOCc (fun c hc => hCO (hCcC hc)) hoddO
  have hz₀L : z₀ ∈ L := hzL.1
  have hz₀com : ∀ k ∈ L, ⁅k, z₀⁆ ∈ pPrimeCoreOf 2 L := hzL.2.2.2
  have hz₀Cc : z₀ ∈ Cc :=
    ⟨hLC hz₀L, hLn (hLC hz₀L), hCO (hLC hz₀L), fun k hk => hOLO (hz₀com k hk)⟩
  have hzCc : z₀ ∈ zStar Cc := by
    refine ⟨hz₀Cc, Subgroup.le_normalizer hz₀Cc, mem_normalizer_pPrimeCoreOf_of_mem hz₀Cc,
      fun c hc => ?_⟩
    have h1 : ⁅z₀, c⁆ ∈ O := hc.2.2.2 z₀ hz₀L
    have e : ⁅c, z₀⁆ = (⁅z₀, c⁆)⁻¹ := (commutatorElement_inv z₀ c).symm
    rw [e]
    exact (pPrimeCoreOf 2 Cc).inv_mem (hOCc' h1)
  have hcovCc : CFSG.GH74.GLS.Stage2.Signalizer.Covers D Cc (pPrimeCoreOf 2 Cc) := by
    intro c hc
    obtain ⟨o, ho, r, hr, rfl⟩ := exists_mul_eq_of_mem_zStar_involution hzCc hz2 hc
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ho) (Subgroup.mem_sup_left ⟨hr.2, hr.1⟩)
  have hQCc' : Q ≤ pPrimeCoreOf 2 Cc := by
    refine CFSG.OddStandard.GH71.le_pPrimeCoreOf_of_covers hcovCc hQCc ?_ ?_
    · exact Odd.of_dvd_nat (odd_card_oddCoreOf D) (Subgroup.card_dvd_of_le inf_le_left)
    · intro x hx
      exact mem_normalizer_inf (hPn x hx.1) (Subgroup.le_normalizer (hCcC hx.2))
  exact hQCc'.trans hΘ

end Abstract

section Lemma34

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}

theorem exists_lemma34_witness (hA : HypA X) (hn : IsMaxAhatDeg X n) (hp : IsSec5Pair X n z Z)
    {s : X} (hsN : s ∈ normalizer (Z : Set X)) (hs2 : orderOf s = 2)
    (hJ : K0 X n (K0 X n (normalizer (Z : Set X)) ⊓ centralizer ({s} : Set X)) ≠ ⊥) :
    ∃ z₀ : X, z₀ ^ 2 = 1 ∧ z₀ ∈ centralizer ({s} : Set X) ∧
      z₀ ∈ zStar (LPlusIn (centralizer ({s} : Set X))) ∧
      centralizer ({z₀} : Set X) ≤ pPrimeCoreOf 2 (centralizer ({z₀} : Set X)) ⊔
        (normalizer (Z : Set X) ⊓ centralizer ({z₀} : Set X)) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, z₀, hz₀Z, hz₀C, hM, hMn⟩ := hp.exists_witness_mem_of_K0_ne_bot hA hn hJ
  set F := K0 X n (normalizer (Z : Set X)) with hF
  set Kz := K0 X n (centralizer ({z} : Set X)) with hKz
  set C := centralizer ({s} : Set X) with hC
  set Y := LPlusIn C with hY
  obtain ⟨M₁, hM₁, hM₁n, -⟩ :=
    exists_isIntrinsicIn_centralizer hA hn hs2 (inf_le_right : F ⊓ C ≤ C) hM hMn
  have hzY : z₀ ∈ zStar Y := hM₁.mem_zStar_LPlusIn
  have hz02 : z₀ ^ 2 = 1 := by rw [← hM.1]; exact pow_orderOf_eq_one z₀
  have hz₀N : z₀ ∈ normalizer (Z : Set X) := Subgroup.le_normalizer hz₀Z
  have hFKz : F ≤ Kz := hp.K0_normalizer_le hA hn
  have hcovF : F ⊔ pPrimeCoreOf 2 Kz = Kz :=
    le_antisymm (sup_le hFKz (oddCoreOf_le Kz)) (by rw [sup_comm]; exact hp.K0_centralizer_le_sup)
  have hz₀F : ∀ k ∈ F, ⁅k, z₀⁆ ∈ pPrimeCoreOf 2 F := by
    intro k hk
    have h1 : ⁅k, z₀⁆ ∈ pPrimeCoreOf 2 Kz := (hp.sylow.1 hz₀Z).2.2.2 k (hFKz hk)
    have h2 : ⁅k, z₀⁆ ∈ F := by
      rw [commutatorElement_def]
      exact F.mul_mem (F.mul_mem (F.mul_mem hk (hp.le_K0_normalizer hz₀Z)) (F.inv_mem hk))
        (F.inv_mem (hp.le_K0_normalizer hz₀Z))
    rw [pPrimeCoreOf_eq_inf_of_covers hFKz hcovF]
    exact ⟨h2, h1⟩
  have hDB := lemma33a_of_isSec5Pair hA hn hp z₀ hz₀N hM.1 hz₀F
  exact ⟨z₀, hz02, hz₀C, hzY, hDB.le⟩

theorem lemma34K_full (hA : HypA X) (hn : IsMaxAhatDeg X n) (hp : IsSec5Pair X n z Z) :
    Lemma34K X n Z := by
  intro s hsN hs2 hJ
  obtain ⟨z₀, hz2, hz₀C, hzL, hDB⟩ := exists_lemma34_witness hA hn hp hsN hs2 hJ
  have hs_sq : s ^ 2 = 1 := by rw [← hs2]; exact pow_orderOf_eq_one s
  have hs_mul : s * s = 1 := by rw [← sq]; exact hs_sq
  set C := centralizer ({s} : Set X) with hC
  set L := LPlusIn C with hL
  set D := centralizer ({z₀} : Set X) with hD
  have hsD : s ∈ D := Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_singleton_iff.1 hz₀C).symm
  set B := normalizer (Z : Set X) ⊓ D with hB
  have hsB : s ∈ B := ⟨hsN, hsD⟩
  have hLC : L ≤ C := LPlusIn_le C
  have hLn : C ≤ normalizer (L : Set X) := le_normalizer_LPlusIn C
  have hOL : pPrimeCoreOf 2 C ≤ L := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨w, ?_, rfl⟩
    rw [LPlus_eq_pLayer_sup_NPlus]
    exact Subgroup.mem_sup_right (pPrimeCore_le_NPlus hw)
  have hQ := cen_oddCoreOf_le_oddCoreOf hz2 hLC hLn hOL hzL
  have hOCL : pPrimeCoreOf 2 C ≤ pPrimeCoreOf 2 L :=
    le_oddCoreOf_of_normalized hOL (hLC.trans (le_normalizer_oddCoreOf C)) (odd_card_oddCoreOf C)
  refine le_antisymm ?_ (sup_le (oddCoreOf_le _) inf_le_right)
  intro y hy
  obtain ⟨o, ho, r, hr, hyor⟩ := exists_mul_eq_of_mem_zStar_involution hzL hz2 hy
  have hrL : r ∈ L := hr.1
  have hrD : r ∈ D := hr.2
  have hrs : s * r = r * s := (Subgroup.mem_centralizer_singleton_iff.1 (hLC hrL)).symm
  obtain ⟨q, hq, b, hb, hrqb⟩ := exists_oddCore_cen_mul_cen hs_mul hsB inf_le_right hDB hrD hrs
  have hqL : q ∈ pPrimeCoreOf 2 L := hOCL (hQ hq)
  have hoq : o * q ∈ pPrimeCoreOf 2 L := (pPrimeCoreOf 2 L).mul_mem ho hqL
  have hoqL : o * q ∈ L := oddCoreOf_le L hoq
  have hy' : y = (o * q) * b := by rw [hyor, hrqb]; group
  have hbL : b ∈ L := by
    have e : b = (o * q)⁻¹ * y := by rw [hy']; group
    rw [e]
    exact L.mul_mem (L.inv_mem hoqL) hy
  rw [hy']
  exact Subgroup.mul_mem_sup hoq ⟨hb.1.1, hbL⟩

end Lemma34

end CFSG.OddStandard.Solomon75
