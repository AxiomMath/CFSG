module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3NCPWide

public section

namespace CFSG.OddStandard.SmallF3.Omega.NCPWide

open Subgroup CFSG.Blueprint CFSG.OddStandard.SmallF3.Omega CFSG.LocalAnalysis.ComponentInitial
  CFSG.EvenSporadicStandard.Induction

variable {G : Type} [Group G]

section SwapAPI

open CFSG.EvenSporadicStandard.Induction.ThmU

variable {B M N L : Subgroup G} {x y z r : G}

theorem cj_eq_conjugate_of_sq {x : G} (hx : x * x = 1) (M : Subgroup G) :
    cj x M = CFSG.conjugate M x := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_left hx
  unfold cj CFSG.conjugate
  rw [hxinv]

theorem SwapCfg.x_sq (h : SwapCfg B x y M) : x * x = 1 := mul_self_eq_one_of_orderOf h.x_ord

theorem SwapCfg.y_sq (h : SwapCfg B x y M) : y * y = 1 := mul_self_eq_one_of_orderOf h.y_ord

theorem SwapCfg.ne' (h : SwapCfg B x y M) : cj x M ≠ M := by
  rw [cj_eq_conjugate_of_sq h.x_sq]
  exact h.ne

theorem SwapCfg.mem_iff' (h : SwapCfg B x y M) :
    ∀ b : G, b ∈ B ↔ ∃ m ∈ M, b = diag x m := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_left h.x_sq
  intro b
  rw [h.mem_iff b]
  unfold diag
  rw [hxinv]

theorem SwapCfg.isComp_cj (h : SwapCfg B x y M) :
    IsComponentIn (cj x M) (centralizer ({y} : Set G)) :=
  isCompIn_cj_centralizer h.comm h.comp

theorem SwapCfg.diagComm [Finite G] (h : SwapCfg B x y M) : DiagComm x M :=
  h.comp.commute_of_ne h.isComp_cj h.ne'.symm

theorem SwapCfg.le_sup [Finite G] (h : SwapCfg B x y M) : B ≤ M ⊔ cj x M := by
  intro b hb
  obtain ⟨m, hm, rfl⟩ := (h.mem_iff' b).1 hb
  exact diag_mem_sup hm

theorem SwapCfg.not_centralizes_left [Finite G] (h : SwapCfg B x y M) :
    ¬ ∀ b ∈ B, ∀ m ∈ M, b * m = m * b := by
  intro hc
  apply diag_not_centralize_left h.x_sq h.diagComm (IsCompIn.not_commute h.comp)
  intro m hm n hn
  exact hc (diag x m) ((h.mem_iff' _).2 ⟨m, hm, rfl⟩) n hn

theorem SwapCfg.not_centralizes_right [Finite G] (h : SwapCfg B x y M) :
    ¬ ∀ b ∈ B, ∀ m ∈ cj x M, b * m = m * b := by
  intro hc
  apply diag_not_centralize_right h.x_sq h.diagComm (IsCompIn.not_commute h.comp)
  intro m hm n hn
  exact hc (diag x m) ((h.mem_iff' _).2 ⟨m, hm, rfl⟩) (x * n * x⁻¹) (conj_mem_cj hn)

theorem SwapCfg.support [Finite G] (h : SwapCfg B x y M) {L : Subgroup G}
    (hL : IsComponentIn L (centralizer ({y} : Set G))) :
    (¬ ∀ b ∈ B, ∀ l ∈ L, b * l = l * b) ↔ (L = M ∨ L = cj x M) := by
  constructor
  · intro hnc
    by_contra hcon
    push Not at hcon
    exact hnc (commute_of_le_sup_of_ne h.comp h.isComp_cj hL hcon.1 hcon.2 h.le_sup)
  · rintro (rfl | rfl)
    · exact h.not_centralizes_left
    · exact h.not_centralizes_right

theorem SwapCfg.cj_mem_support [Finite G] (h : SwapCfg B x y M) {g : G} (hgy : g * y = y * g)
    (hgB : ∀ b ∈ B, g * b = b * g) : cj g M = M ∨ cj g M = cj x M := by
  refine (h.support (isCompIn_cj_centralizer hgy h.comp)).1 ?_
  intro hcomm
  apply h.not_centralizes_left
  intro b hb m hm
  have key : b * (g * m * g⁻¹) = (g * m * g⁻¹) * b :=
    hcomm b hb (g * m * g⁻¹) (conj_mem_cj hm)
  have hgb : Commute g b := hgB b hb
  have h1 : g * (b * m) * g⁻¹ = g * (m * b) * g⁻¹ := by
    calc g * (b * m) * g⁻¹ = (g * b) * m * g⁻¹ := by group
      _ = (b * g) * m * g⁻¹ := by rw [hgb.eq]
      _ = b * (g * m * g⁻¹) := by group
      _ = (g * m * g⁻¹) * b := key
      _ = g * m * (g⁻¹ * b) := by group
      _ = g * m * (b * g⁻¹) := by rw [hgb.inv_left.eq]
      _ = g * (m * b) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h1)

theorem SwapCfg.centralizes_of_mem_normalizer [Finite G] (h : SwapCfg B x y M) {g : G}
    (hgN : g ∈ normalizer (M : Set G)) (hgB : ∀ b ∈ B, g * b = b * g) :
    (∀ m ∈ M, g * m = m * g) ∧ ∀ m ∈ M, g * (x * m * x⁻¹) = (x * m * x⁻¹) * g := by
  refine centralizes_of_normalizes h.x_sq h.diagComm (IsCompIn.perfect h.comp) hgN ?_
  intro m hm
  exact hgB (diag x m) ((h.mem_iff' (diag x m)).2 ⟨m, hm, rfl⟩)

theorem SwapCfg.relIndex_normalizer_eq_two [Finite G] (h : SwapCfg B x y M) {P : Subgroup G}
    (hPy : P ≤ centralizer ({y} : Set G)) (hPB : ∀ p ∈ P, ∀ b ∈ B, p * b = b * p)
    (hxP : x ∈ P) : (P ⊓ normalizer (M : Set G)).relIndex P = 2 := by
  have hNiff : ∀ g : G, g ∈ normalizer (M : Set G) ↔ cj g M = M := fun g => by
    change g ∈ normalizer (M : Set G) ↔ M.map (MulAut.conj g).toMonoidHom = M
    exact Subgroup.mem_normalizer_iff_map_conj_eq
  have hcancel : cj x (cj x M) = M := cj_cj_of_mul_self h.x_sq M
  rw [Subgroup.relIndex_eq_two_iff']
  refine ⟨x, hxP, fun b hbP => ?_⟩
  have hxbP : x * b ∈ P := P.mul_mem hxP hbP
  have hsupp : cj b M = M ∨ cj b M = cj x M :=
    h.cj_mem_support (Subgroup.mem_centralizer_singleton_iff.1 (hPy hbP)) (hPB b hbP)
  have hmap : cj (x * b) M = cj x (cj b M) := (Subgroup.map_conj_map_conj M b x).symm
  have hpx : x * b ∈ P ⊓ normalizer (M : Set G) ↔ x * b ∈ normalizer (M : Set G) :=
    ⟨fun hh => hh.2, fun hh => ⟨hxbP, hh⟩⟩
  have hpb : b ∈ P ⊓ normalizer (M : Set G) ↔ b ∈ normalizer (M : Set G) :=
    ⟨fun hh => hh.2, fun hh => ⟨hbP, hh⟩⟩
  rw [hpx, hpb, hNiff (x * b), hNiff b, hmap]
  rcases hsupp with hbM | hbX
  · right
    rw [hbM]
    exact ⟨rfl, h.ne'⟩
  · left
    refine ⟨?_, fun hq => h.ne' (hbX.symm.trans hq)⟩
    rw [hbX, hcancel]

end SwapAPI

section Lemma23

open CFSG.EvenSporadicStandard.Induction.ThmU

variable {B M N L : Subgroup G} {x y z r : G}

@[expose] def diagHom {L : Subgroup G} {y : G} (hc : DiagComm y L) : ↥L →* G where
  toFun m := diag y m.1
  map_one' := diag_one
  map_mul' a b := diag_mul hc a.2 b.2

theorem mem_range_diagHom {L : Subgroup G} {y : G} (hc : DiagComm y L) (g : G) :
    g ∈ (diagHom hc).range ↔ ∃ l ∈ L, g = diag y l := by
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m.1, m.2, hm.symm⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, hm⟩, rfl⟩

theorem isQuasisimple_range_diagHom [Finite G] {L : Subgroup G} {y : G} (hc : DiagComm y L)
    (hLq : CFSG.IsQuasisimple ↥L) : CFSG.IsQuasisimple ↥(diagHom hc).range := by
  have hker : (diagHom hc).ker ≤ center ↥L := by
    intro m hm
    rw [MonoidHom.mem_ker] at hm
    change m.1 * (y * m.1 * y⁻¹) = 1 at hm
    have hinv : y * m.1 * y⁻¹ = m.1⁻¹ := eq_inv_of_mul_eq_one_right hm
    have hmcj : m.1 ∈ cj y L := by
      have h1 : y * m.1⁻¹ * y⁻¹ ∈ cj y L := conj_mem_cj (L.inv_mem m.2)
      have h2 : y * m.1⁻¹ * y⁻¹ = m.1 := by
        have : y * m.1⁻¹ * y⁻¹ = (y * m.1 * y⁻¹)⁻¹ := by group
        rw [this, hinv, inv_inv]
      rwa [h2] at h1
    have hcen := inf_cj_central hc ⟨m.2, hmcj⟩
    refine Subgroup.mem_center_iff.mpr fun n => Subtype.ext ?_
    exact hcen n.1 ((le_sup_left : L ≤ L ⊔ _) n.2)
  exact CFSG.GH74.Generic.S1.isQuasisimple_range_of_ker hLq (diagHom hc) hker

theorem diag_eq_of_component [Finite G] {X K L : Subgroup G} {y : G} (hy : y * y = 1)
    (hc : DiagComm y L) (hLq : CFSG.IsQuasisimple ↥L) (hK : IsComponentIn K X)
    (hKle : K ≤ L ⊔ cj y L) (hKfix : ∀ k ∈ K, y * k * y⁻¹ = k)
    (hD : (diagHom hc).range ≤ X) : ∀ g : G, g ∈ K ↔ ∃ l ∈ L, g = diag y l := by
  have hBD : K ≤ (diagHom hc).range := by
    intro k hk
    obtain ⟨m, hm, hkm⟩ := le_diag_of_perfect hy hc (IsCompIn.perfect hK) hKle hKfix k hk
    exact ⟨⟨m, hm⟩, hkm.symm⟩
  have hDq := isQuasisimple_range_diagHom hc hLq
  have hBD' : IsComponentIn K (diagHom hc).range := hK.mono hBD hD
  have hDD : IsComponentIn (diagHom hc).range (diagHom hc).range :=
    isComponentIn_of_normal le_rfl hDq (by
      rw [Subgroup.subgroupOf_self]
      infer_instance)
  have hBeq : K = (diagHom hc).range := hBD'.eq_of_le hDD hBD
  intro g
  rw [hBeq]
  exact mem_range_diagHom hc g

theorem ncpw_not_alt3 [Finite G] {B M N L : Subgroup G} {x y r : G} (hxy : x * y = y * x)
    (hxr : x * r = r * x) (hyr : y * r = r * y) (hSy : SwapCfg B x y M)
    (hSr : SwapCfg B x r N) (hL : IsComponentIn L (centralizer ({r} : Set G)))
    (hML : ¬ ∀ m ∈ M, ∀ l ∈ L, m * l = l * m) (hLy : cj y L ≠ L)
    (hMd : ∀ g : G, g ∈ M ↔ ∃ l ∈ L, g = diag y l) : False := by
  have hxx : x * x = 1 := hSy.x_sq
  have hyy : y * y = 1 := hSy.y_sq
  have hxX : x ∈ centralizer ({r} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hxr
  have hyX : y ∈ centralizer ({r} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hyr
  have hLyX : IsComponentIn (cj y L) (centralizer ({r} : Set G)) := isCompIn_cj_of_mem hL hyX
  have hL1X : IsComponentIn (cj x L) (centralizer ({r} : Set G)) := isCompIn_cj_of_mem hL hxX
  have hL2X : IsComponentIn (cj y (cj x L)) (centralizer ({r} : Set G)) :=
    isCompIn_cj_of_mem hL1X hyX
  have hc : DiagComm y L := hL.commute_of_ne hLyX (Ne.symm hLy)
  by_cases hcaseA : cj x L = L ∨ cj x L = cj y L
  · exact hSy.ne' (cj_eq_of_diag (M := M) hyy hc hMd hxy hcaseA)
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
          (hBL (diag x m) ((hSy.mem_iff' _).2 ⟨m, hm, rfl⟩) l hl)
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
            (hBL (diag x m) ((hSy.mem_iff' _).2 ⟨m, hm, rfl⟩) (y * l * y⁻¹) hw)
        have ham : x * m * x⁻¹ ∈ centralizer ({(y * l * y⁻¹)} : Set G) :=
          Subgroup.mem_centralizer_singleton_iff.2 (hcomm2 _ (conj_mem_cj hm) _ hw)
        have hm' : m ∈ centralizer ({(y * l * y⁻¹)} : Set G) := by
          rw [show m = diag x m * (x * m * x⁻¹)⁻¹ by rw [diag]; group]
          exact Subgroup.mul_mem _ hdm (Subgroup.inv_mem _ ham)
        exact Subgroup.mem_centralizer_singleton_iff.1 hm'
      have hmy : m * y = y * m :=
        Subgroup.mem_centralizer_singleton_iff.1 (hSy.comp.1 hm)
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
      exact hBnotCentL (commute_of_le_sup_of_ne hSr.comp hSr.isComp_cj hL
        hcon.1 hcon.2 hSr.le_sup)
    have hLycase : cj y L = N ∨ cj y L = cj x N := by
      by_contra hcon
      push Not at hcon
      exact hBnotCentLy (commute_of_le_sup_of_ne hSr.comp hSr.isComp_cj hLyX
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

end Lemma23

end CFSG.OddStandard.SmallF3.Omega.NCPWide
