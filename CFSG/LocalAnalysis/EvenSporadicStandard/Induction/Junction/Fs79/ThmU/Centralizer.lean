module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.Swap

public section

namespace CFSG.EvenSporadicStandard.Induction.ThmU

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
  CFSG.ComponentClassification.AschbacherToolkit
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_of_centralizes {M : Subgroup G} {g : G} (hg : ∀ m ∈ M, g * m = m * g) :
    g ∈ normalizer (M : Set G) :=
  Subgroup.centralizer_le_normalizer (M : Set G)
    (Subgroup.mem_centralizer_iff.2 fun m hm => (hg m hm).symm)

namespace SwapConfig

variable {B M : Subgroup G} {x y : G}

theorem centralizes_of_mem_normalizer [Finite G] (h : SwapConfig B x y M) {g : G}
    (hgN : g ∈ normalizer (M : Set G)) (hgB : ∀ b ∈ B, g * b = b * g) :
    (∀ m ∈ M, g * m = m * g) ∧ ∀ m ∈ M, g * (x * m * x⁻¹) = (x * m * x⁻¹) * g := by
  refine centralizes_of_normalizes h.x_mul_self h.diagComm (IsCompIn.perfect h.isCompIn) hgN ?_
  intro m hm
  exact hgB (diag x m) ((h.mem_iff (diag x m)).2 ⟨m, hm, rfl⟩)

theorem relIndex_normalizer_eq_two [Finite G] (h : SwapConfig B x y M) {P : Subgroup G}
    (hPy : P ≤ centralizer ({y} : Set G)) (hPB : ∀ p ∈ P, ∀ b ∈ B, p * b = b * p)
    (hxP : x ∈ P) : (P ⊓ normalizer (M : Set G)).relIndex P = 2 := by
  have hNiff : ∀ g : G, g ∈ normalizer (M : Set G) ↔ cj g M = M := fun g => by
    change g ∈ normalizer (M : Set G) ↔ M.map (MulAut.conj g).toMonoidHom = M
    exact Subgroup.mem_normalizer_iff_map_conj_eq
  have hcancel : cj x (cj x M) = M := cj_cj_of_mul_self h.x_mul_self M
  rw [Subgroup.relIndex_eq_two_iff']
  refine ⟨x, hxP, fun b hbP => ?_⟩
  have hxbP : x * b ∈ P := P.mul_mem hxP hbP
  have hsupp : cj b M = M ∨ cj b M = cj x M :=
    h.cj_mem_support (Subgroup.mem_centralizer_singleton_iff.1 (hPy hbP)) (hPB b hbP)
  have hmap : cj (x * b) M = cj x (cj b M) := (map_conj_map_conj M b x).symm
  have hpx : x * b ∈ P ⊓ normalizer (M : Set G) ↔ x * b ∈ normalizer (M : Set G) :=
    ⟨fun hh => hh.2, fun hh => ⟨hxbP, hh⟩⟩
  have hpb : b ∈ P ⊓ normalizer (M : Set G) ↔ b ∈ normalizer (M : Set G) :=
    ⟨fun hh => hh.2, fun hh => ⟨hbP, hh⟩⟩
  rw [hpx, hpb, hNiff (x * b), hNiff b, hmap]
  rcases hsupp with hbM | hbX
  · right
    rw [hbM]
    exact ⟨rfl, h.ne⟩
  · left
    refine ⟨?_, fun hq => h.ne (hbX.symm.trans hq)⟩
    rw [hbX, hcancel]

end SwapConfig

theorem not_alt3 [Finite G] {B M N L : Subgroup G} {x y r : G} (hxy : x * y = y * x)
    (hxr : x * r = r * x) (hyr : y * r = r * y) (hSy : SwapConfig B x y M)
    (hSr : SwapConfig B x r N) (hL : IsCompIn L (centralizer ({r} : Set G)))
    (hML : ¬ ∀ m ∈ M, ∀ l ∈ L, m * l = l * m) (hLy : cj y L ≠ L) (hMle : M ≤ L ⊔ cj y L)
    (hcard : Nat.card M = Nat.card L) : False := by
  have hxx : x * x = 1 := mul_self_eq_one_of_orderOf hSy.x_ord
  have hyy : y * y = 1 := mul_self_eq_one_of_orderOf hSy.y_ord
  have hxX : x ∈ centralizer ({r} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hxr
  have hyX : y ∈ centralizer ({r} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hyr
  have hLyX : IsCompIn (cj y L) (centralizer ({r} : Set G)) := isCompIn_cj_of_mem hL hyX
  have hL1X : IsCompIn (cj x L) (centralizer ({r} : Set G)) := isCompIn_cj_of_mem hL hxX
  have hL2X : IsCompIn (cj y (cj x L)) (centralizer ({r} : Set G)) :=
    isCompIn_cj_of_mem hL1X hyX
  have hc : DiagComm y L := hL.commute_of_ne hLyX (Ne.symm hLy)
  have hfixed : ∀ k ∈ M, y * k * y⁻¹ = k := by
    intro k hk
    have hk' : k * y = y * k :=
      Subgroup.mem_centralizer_singleton_iff.1 (hSy.isCompIn.1 hk)
    rw [hk'.symm]
    group
  have hMperf : ⁅M, M⁆ = M := IsCompIn.perfect hSy.isCompIn
  have hMd : ∀ g : G, g ∈ M ↔ ∃ l ∈ L, g = diag y l :=
    (diag_of_le_sup_conj (M := L) (x := y) (K := M) hyy hc hMperf hMle hfixed hcard).1
  by_cases hcaseA : cj x L = L ∨ cj x L = cj y L
  · exact hSy.ne (cj_eq_of_diag (M := M) hyy hc hMd hxy hcaseA)
  · push Not at hcaseA
    have hL2_ne_L : cj y (cj x L) ≠ L := by
      intro h1
      apply hcaseA.2
      have h2 := congrArg (cj y) h1
      rwa [cj_cj_of_mul_self hyy] at h2
    have hL2_ne_Ly : cj y (cj x L) ≠ cj y L := by
      intro h1
      apply hcaseA.1
      have h2 := congrArg (cj y) h1
      rwa [cj_cj_of_mul_self hyy (cj x L), cj_cj_of_mul_self hyy L] at h2
    have hBle : cj x M ≤ cj x L ⊔ cj y (cj x L) :=
      cj_le_sup_of_diag (M := M) (L := L) (y := y) (z := x) hyy hMd hxy
    have hcomm1 : ∀ b ∈ cj x M, ∀ l ∈ L, b * l = l * b :=
      commute_of_le_sup_of_ne hL1X hL2X hL (Ne.symm hcaseA.1) (Ne.symm hL2_ne_L) hBle
    have hcomm2 : ∀ b ∈ cj x M, ∀ l ∈ cj y L, b * l = l * b :=
      commute_of_le_sup_of_ne hL1X hL2X hLyX (Ne.symm hcaseA.2) (Ne.symm hL2_ne_Ly) hBle
    have hBnotCentL : ¬ ∀ b ∈ B, ∀ l ∈ L, b * l = l * b := by
      intro hBL
      apply hML
      intro m hm l hl
      have hdm : diag x m ∈ centralizer ({l} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.2
          (hBL (diag x m) ((hSy.mem_iff _).2 ⟨m, hm, rfl⟩) l hl)
      have ham : x * m * x⁻¹ ∈ centralizer ({l} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.2 (hcomm1 _ (conj_mem_cj hm) l hl)
      have hm' : m ∈ centralizer ({l} : Set G) := by
        rw [show m = diag x m * (x * m * x⁻¹)⁻¹ by rw [diag]; group]
        exact Subgroup.mul_mem _ hdm (Subgroup.inv_mem _ ham)
      exact Subgroup.mem_centralizer_singleton_iff.1 hm'
    have hBnotCentLy : ¬ ∀ b ∈ B, ∀ l ∈ cj y L, b * l = l * b := by
      intro hBL
      apply hML
      intro m hm l hl
      have hw : y * l * y⁻¹ ∈ cj y L := conj_mem_cj hl
      have hmw : m * (y * l * y⁻¹) = (y * l * y⁻¹) * m := by
        have hdm : diag x m ∈ centralizer ({(y * l * y⁻¹)} : Set G) :=
          Subgroup.mem_centralizer_singleton_iff.2
            (hBL (diag x m) ((hSy.mem_iff _).2 ⟨m, hm, rfl⟩) (y * l * y⁻¹) hw)
        have ham : x * m * x⁻¹ ∈ centralizer ({(y * l * y⁻¹)} : Set G) :=
          Subgroup.mem_centralizer_singleton_iff.2 (hcomm2 _ (conj_mem_cj hm) _ hw)
        have hm' : m ∈ centralizer ({(y * l * y⁻¹)} : Set G) := by
          rw [show m = diag x m * (x * m * x⁻¹)⁻¹ by rw [diag]; group]
          exact Subgroup.mul_mem _ hdm (Subgroup.inv_mem _ ham)
        exact Subgroup.mem_centralizer_singleton_iff.1 hm'
      have hmy : m * y = y * m :=
        Subgroup.mem_centralizer_singleton_iff.1 (hSy.isCompIn.1 hm)
      have h1 : y * (y * l * y⁻¹) * y = (y * y) * l * (y⁻¹ * y) := by group
      have hl_eq : y * (y * l * y⁻¹) * y = l := by
        rw [h1, hyy, inv_mul_cancel, one_mul, mul_one]
      have hy_m : y ∈ centralizer ({m} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.2 hmy.symm
      have hw_m : y * l * y⁻¹ ∈ centralizer ({m} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.2 hmw.symm
      have hl_m : l ∈ centralizer ({m} : Set G) := by
        have hmem : y * (y * l * y⁻¹) * y ∈ centralizer ({m} : Set G) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ hy_m hw_m) hy_m
        rwa [hl_eq] at hmem
      exact (Subgroup.mem_centralizer_singleton_iff.1 hl_m).symm
    have hLcase : L = N ∨ L = cj x N := by
      by_contra hcon
      push Not at hcon
      exact hBnotCentL (commute_of_le_sup_of_ne hSr.isCompIn hSr.isCompIn_cj hL
        hcon.1 hcon.2 hSr.le_sup)
    have hLycase : cj y L = N ∨ cj y L = cj x N := by
      by_contra hcon
      push Not at hcon
      exact hBnotCentLy (commute_of_le_sup_of_ne hSr.isCompIn hSr.isCompIn_cj hLyX
        hcon.1 hcon.2 hSr.le_sup)
    rcases hLcase with hLN | hLcN
    · have hy : cj y L = cj x N := by
        rcases hLycase with h | h
        · exact absurd (h.trans hLN.symm) hLy
        · exact h
      exact hcaseA.2 ((congrArg (cj x) hLN).trans hy.symm)
    · have hxL : cj x L = N := by rw [hLcN, cj_cj_of_mul_self hxx]
      have hy : cj y L = N := by
        rcases hLycase with h | h
        · exact h
        · exact absurd (h.trans hLcN.symm) hLy
      exact hcaseA.2 (hxL.trans hy.symm)

theorem isCompIn_nine7 {M X : Subgroup G} (h : IsCompIn M X) :
    CFSG.CGT.PushingUpLit.CGT6.Nine7.IsCompIn M X :=
  ⟨h.1, h.2.2, h.isQuasisimple.1.commutator_eq_top, h.isQuasisimple.2.1⟩

theorem involution_bad_and_isCompIn [Finite G] (hLB : LayerBalanceAt G)
    (hglaub : GlaubermanSimplePerfect) {B : Subgroup G} (hB : MaximalF B) {x y : G}
    {M : Subgroup G} (hx : GoodInv B x) (hS : SwapConfig B x y M) (hM : MaximalF M) {r : G}
    (hr : orderOf r = 2) (hrx : r * x = x * r) (hry : r * y = y * r)
    (hrM : ∀ m ∈ M, r * m = m * r) :
    BadInv B r ∧ IsCompIn M (centralizer ({r} : Set G)) ∧
      IsCompIn (cj x M) (centralizer ({r} : Set G)) := by
  have hyy : y * y = 1 := mul_self_eq_one_of_orderOf hS.y_ord
  have hMr : M ≤ centralizer ({r} : Set G) := fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.2 (hrM m hm).symm
  have hxX : x ∈ centralizer ({r} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hrx.symm
  have hxr_conj : x * r * x⁻¹ = r := by rw [hrx.symm]; group
  have hMxr : cj x M ≤ centralizer ({r} : Set G) := by
    calc cj x M ≤ cj x (centralizer ({r} : Set G)) := cj_mono x hMr
      _ = centralizer ({x * r * x⁻¹} : Set G) := cj_centralizer_singleton x r
      _ = centralizer ({r} : Set G) := by rw [hxr_conj]
  have hMlayer : M ≤ layerIn (centralizer ({r} : Set G)) :=
    hLB.le_layerIn hS.y_ord hr hry.symm hS.isCompIn hMr
  have hBcent : B ≤ centralizer ({r} : Set G) := by
    intro b hb
    obtain ⟨m, hm, rfl⟩ := (hS.mem_iff b).1 hb
    have hm' : m ∈ centralizer ({r} : Set G) := hMr hm
    have hxm : x * m * x⁻¹ ∈ centralizer ({r} : Set G) := by
      have hmem : x * m * x⁻¹ ∈ cj x (centralizer ({r} : Set G)) := conj_mem_cj hm'
      rwa [cj_centralizer_singleton x r, hxr_conj] at hmem
    rw [diag]
    exact Subgroup.mul_mem _ hm' hxm
  have hBnotComp : ¬ IsCompIn B (centralizer ({r} : Set G)) := by
    intro hBcomp
    have hle : M ≤ normalizer (B : Set G) :=
      hMlayer.trans (layerIn_le_normalizer hBcomp)
    exact not_le_normalizer_diag hS.x_mul_self hS.diagComm (IsCompIn.perfect hS.isCompIn)
      hS.ne hS.mem_iff hle
  have hbad : BadInv B r := ⟨hr, hBcent, hBnotComp⟩
  obtain ⟨N, hSr, -, -⟩ := exists_swapConfig hLB hglaub hB hx hbad hrx.symm
  obtain ⟨L, hL, hML⟩ := exists_isCompIn_not_commute (B := M) hM.1.isQuasisimple hMlayer
  have hK : IsCompIn M (centralizer ({r} : Set G) ⊓ centralizer ({y} : Set G)) :=
    isCompIn_of_le hS.isCompIn (le_inf hMr hS.isCompIn.1) inf_le_right
  have hyX : y ∈ centralizer ({r} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hry.symm
  have hglaubAt : CFSG.CGT.PushingUpLit.CGT6.Nine7.GlaubermanAt
      (↥L ⧸ Subgroup.center ↥L) :=
    fun hX _ hev S K hK' hfix =>
      hglaub (↥L ⧸ Subgroup.center ↥L) hX hev S K hK' hfix
  have htrich :=
    CFSG.CGT.PushingUpLit.CGT6.Nine7.lemma_2_7_two_amb (H := centralizer ({r} : Set G))
      (t := y) hyX hS.y_ord (isCompIn_nine7 hK) (isCompIn_nine7 hL) hglaubAt
  have hMX : IsCompIn M (centralizer ({r} : Set G)) := by
    rcases htrich with hbot | hMle | ⟨hLyconj, hMcomm⟩
    · have hcommML : ∀ m ∈ M, ∀ l ∈ L, m * l = l * m := by
        intro m hm l hl
        exact (Subgroup.mem_centralizer_iff.1
          ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot) hm) l hl).symm
      exact (hML hcommML).elim
    · have hLtF : LtF M L :=
        ⟨y, r, hS.y_ord, hr, hry.symm, hS.isCompIn, hL, hMle.trans le_sup_left⟩
      obtain ⟨e⟩ := hM.2 L (Relation.TransGen.single hLtF)
      have hcard : Nat.card M = Nat.card L := Nat.card_congr e.toEquiv
      have heq : M = L := Subgroup.eq_of_le_of_card_ge hMle (le_of_eq hcard.symm)
      rw [heq]
      exact hL
    · have hconv : conjugate L y = cj y L := by
        show L.map (MulAut.conj y⁻¹).toMonoidHom = L.map (MulAut.conj y).toMonoidHom
        rw [inv_eq_of_mul_eq_one_right hyy]
      have hyL : cj y L ≠ L := fun h1 => hLyconj (hconv.trans h1)
      have hsup : M ≤ L ⊔ cj y L :=
        hMcomm.trans (commutator_zpowers_le_sup_cj (L := L) (x := y) hyy)
      have hLtF : LtF M L :=
        ⟨y, r, hS.y_ord, hr, hry.symm, hS.isCompIn, hL, hsup⟩
      obtain ⟨e⟩ := hM.2 L (Relation.TransGen.single hLtF)
      have hcard : Nat.card M = Nat.card L := Nat.card_congr e.toEquiv
      exact (not_alt3 hS.comm hrx.symm hry.symm hS hSr hL hML hyL hsup hcard).elim
  exact ⟨hbad, hMX, isCompIn_cj_of_mem hMX hxX⟩

end CFSG.EvenSporadicStandard.Induction.ThmU
