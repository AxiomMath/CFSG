module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29D5

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

namespace S3Sec29JB

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev Oy (y : G) : Subgroup G := pPrimeCoreOf 2 (centralizer ({y} : Set G))

noncomputable abbrev L1 (K : Subgroup G) (y : G) : Subgroup G := Ly29 K y ⊔ Oy y

theorem Ly_le_centralizer (K : Subgroup G) (y : G) : Ly29 K y ≤ centralizer ({y} : Set G) :=
  (sSup_le fun _ hL => hL.1 : Ly29 K y ≤ K ⊓ centralizer ({y} : Set G)).trans inf_le_right

omit [Finite G] in
theorem Oy_le_centralizer (y : G) : Oy y ≤ centralizer ({y} : Set G) := Subgroup.map_subtype_le _

theorem L1_le_centralizer (K : Subgroup G) (y : G) : L1 K y ≤ centralizer ({y} : Set G) :=
  sup_le (Ly_le_centralizer K y) (Oy_le_centralizer y)

omit [Finite G] in
theorem mem_normalizer_Oy {y g : G} (hg : g ∈ centralizer ({y} : Set G)) :
    g ∈ normalizer ((Oy y : Subgroup G) : Set G) :=
  TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hg)

theorem coprime_card_pPrimeCoreOf (X : Subgroup G) :
    Nat.Coprime 2 (Nat.card ↥(pPrimeCoreOf 2 X)) := by
  rw [pPrimeCoreOf, Subgroup.card_map_of_injective X.subtype_injective]
  exact pPrimeCore_coprime_card

omit [Finite G] in
theorem mem_normalizer_sup {H H' : Subgroup G} {g : G} (hH : g ∈ normalizer (H : Set G))
    (hH' : g ∈ normalizer (H' : Set G)) : g ∈ normalizer ((H ⊔ H' : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hH' ⊢
  rw [Subgroup.map_sup, hH, hH']

omit [Finite G] in
theorem le_pPrimeCoreOf_of_odd {N X : Subgroup G} (hNX : N ≤ X)
    (hXN : X ≤ normalizer (N : Set G)) (hodd : Nat.Coprime 2 (Nat.card ↥N)) :
    N ≤ pPrimeCoreOf 2 X := by
  have hnormal : (N.subgroupOf X).Normal := by
    refine ⟨fun a ha h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hXN h.2) a).mp ha
  have hcop : Nat.Coprime 2 (Nat.card (N.subgroupOf X)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
  have hle : N.subgroupOf X ≤ pPrimeCore 2 ↥X := le_sSup ⟨hnormal, hcop⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hNX]
  exact Subgroup.map_mono hle

omit [Finite G] in
theorem odd_card_sup {H N : Subgroup G} (hHN : H ≤ normalizer (N : Set G)) (hH : Odd (Nat.card H))
    (hN : Odd (Nat.card N)) : Odd (Nat.card (H ⊔ N : Subgroup G)) := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N)),
    ← Nat.card_congr e.toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (le_sup_right : N ≤ H ⊔ N)).toEquiv]
  exact (Odd.of_dvd_nat hH (Subgroup.card_quotient_dvd_card _)).mul hN

omit [Finite G] in
theorem comm_mem_sup {X Y O : Subgroup G} {g : G} (hXO : X ≤ normalizer (O : Set G))
    (hYO : Y ≤ normalizer (O : Set G)) (hX : ∀ k ∈ X, ⁅k, g⁆ ∈ O) (hY : ∀ k ∈ Y, ⁅k, g⁆ ∈ O) :
    ∀ k ∈ X ⊔ Y, ⁅k, g⁆ ∈ O := by
  let S' : Subgroup G :=
    { carrier := {k | k ∈ normalizer (O : Set G) ∧ ⁅k, g⁆ ∈ O}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
        refine ⟨mul_mem haN hbN, ?_⟩
        have e : ⁅a * b, g⁆ = (a * ⁅b, g⁆ * a⁻¹) * ⁅a, g⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact mul_mem ((Subgroup.mem_normalizer_iff.1 haN _).1 hb) ha
      inv_mem' := by
        rintro a ⟨haN, ha⟩
        refine ⟨inv_mem haN, ?_⟩
        have e : ⁅a⁻¹, g⁆ = a⁻¹ * ⁅a, g⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.1 (inv_mem haN) _).1 (inv_mem ha) }
  have hle : X ⊔ Y ≤ S' :=
    sup_le (fun k hk => ⟨hXO hk, hX k hk⟩) (fun k hk => ⟨hYO hk, hY k hk⟩)
  exact fun k hk => (hle hk).2

omit [Finite G] in
theorem comm_mem_Oy {y k g : G} (hk : k ∈ Oy y) (hg : g ∈ centralizer ({y} : Set G)) :
    ⁅k, g⁆ ∈ Oy y := by
  have h1 : g * k⁻¹ * g⁻¹ ∈ Oy y :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_Oy hg) _).mp (inv_mem hk)
  have h2 : ⁅k, g⁆ = k * (g * k⁻¹ * g⁻¹) := by simp only [commutatorElement_def]; group
  rw [h2]
  exact mul_mem hk h1

theorem Oy_le_pPrimeCoreOf_L1 (K : Subgroup G) (y : G) : Oy y ≤ pPrimeCoreOf 2 (L1 K y) :=
  le_pPrimeCoreOf_of_odd le_sup_right (fun _ hg => mem_normalizer_Oy (L1_le_centralizer K y hg))
    (coprime_card_pPrimeCoreOf _)

theorem pPrimeCoreOf_Ly_le_L1 (K : Subgroup G) (y : G) :
    pPrimeCoreOf 2 (Ly29 K y) ≤ pPrimeCoreOf 2 (L1 K y) := by
  set P := pPrimeCoreOf 2 (Ly29 K y) ⊔ Oy y with hP
  have hOL : pPrimeCoreOf 2 (Ly29 K y) ≤ Ly29 K y := Subgroup.map_subtype_le _
  have hPL : P ≤ L1 K y := sup_le_sup_right hOL _
  have hPy : P ≤ centralizer ({y} : Set G) := hPL.trans (L1_le_centralizer K y)
  have hodd : Odd (Nat.card ↥P) := odd_card_sup
    (fun _ hg => mem_normalizer_Oy (hPy (le_sup_left (b := Oy y) hg)))
    (Nat.coprime_two_left.mp (coprime_card_pPrimeCoreOf _))
    (Nat.coprime_two_left.mp (coprime_card_pPrimeCoreOf _))
  have hN : L1 K y ≤ normalizer (P : Set G) := by
    refine sup_le (fun l hl => mem_normalizer_sup ?_ ?_) (le_sup_right.trans Subgroup.le_normalizer)
    · exact TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hl)
    · exact mem_normalizer_Oy (Ly_le_centralizer K y hl)
  exact le_sup_left.trans (le_pPrimeCoreOf_of_odd hPL hN (Nat.coprime_two_left.mpr hodd))

theorem mem_normalizer_L1 {K : Subgroup G} {y g : G} (hgy : g ∈ centralizer ({y} : Set G))
    (hgL : g ∈ normalizer ((Ly29 K y : Subgroup G) : Set G)) :
    g ∈ normalizer ((L1 K y : Subgroup G) : Set G) :=
  mem_normalizer_sup hgL (mem_normalizer_Oy hgy)

theorem L1_le_normalizer_pPrimeCoreOf (K : Subgroup G) (y : G) :
    L1 K y ≤ normalizer (pPrimeCoreOf 2 (L1 K y) : Set G) := fun _ hk =>
  TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hk)

theorem mem_cSec_L1 {K : Subgroup G} {y g : G} (hgy : g ∈ centralizer ({y} : Set G))
    (hgL : g ∈ cSec (Ly29 K y)) : g ∈ cSec (L1 K y) := by
  have hN := mem_normalizer_L1 hgy hgL.1
  refine ⟨hN, TwoThin.mem_normalizer_pPrimeCoreOf hN, ?_⟩
  exact comm_mem_sup (le_sup_left.trans (L1_le_normalizer_pPrimeCoreOf K y))
    (le_sup_right.trans (L1_le_normalizer_pPrimeCoreOf K y))
    (fun k hk => pPrimeCoreOf_Ly_le_L1 K y (hgL.2.2 k hk))
    (fun k hk => Oy_le_pPrimeCoreOf_L1 K y (comm_mem_Oy hk hgy))

theorem le_cSec_L1 {K J : Subgroup G} {y : G} (hJ : IsPCompIn 2 (centralizer ({y} : Set G)) J)
    (h296 : Ly29 K y ≤ cSec J) : J ≤ cSec (L1 K y) := by
  have hOJ : pPrimeCoreOf 2 J ≤ Oy y := Th2.Bal.pPrimeCoreOf_le_of_pCompIn hJ
  have hLN : L1 K y ≤ normalizer (Oy y : Set G) := fun _ hk =>
    mem_normalizer_Oy (L1_le_centralizer K y hk)
  have hc : ∀ j ∈ J, ∀ k ∈ L1 K y, ⁅k, j⁆ ∈ Oy y := by
    intro j hj
    refine comm_mem_sup (le_sup_left.trans hLN) (le_sup_right.trans hLN) (fun l hl => ?_)
      (fun k hk => comm_mem_Oy hk (hJ.1 hj))
    have h1 : ⁅j, l⁆ ∈ pPrimeCoreOf 2 J := (h296 hl).2.2 j hj
    have h2 : ⁅l, j⁆ = ⁅j, l⁆⁻¹ := by simp only [commutatorElement_def]; group
    rw [h2]
    exact hOJ (inv_mem h1)
  have hconj : ∀ j ∈ J, ∀ k ∈ L1 K y, j * k * j⁻¹ ∈ L1 K y := by
    intro j hj k hk
    have h2 : j * k * j⁻¹ = ⁅k, j⁆⁻¹ * k := by simp only [commutatorElement_def]; group
    rw [h2]
    exact mul_mem (inv_mem (le_sup_right (a := Ly29 K y) (hc j hj k hk))) hk
  intro j hj
  have hjN : j ∈ normalizer ((L1 K y : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hconj j hj k hk, fun hk => ?_⟩
    have := hconj j⁻¹ (inv_mem hj) _ hk
    simpa [mul_assoc] using this
  exact ⟨hjN, TwoThin.mem_normalizer_pPrimeCoreOf hjN,
    fun k hk => Oy_le_pPrimeCoreOf_L1 K y (hc j hj k hk)⟩

theorem mem_cSec_Ly_of_L1 {K : Subgroup G} {y g : G}
    (hgN : g ∈ normalizer ((Ly29 K y : Subgroup G) : Set G)) (hg : g ∈ cSec (L1 K y)) :
    g ∈ cSec (Ly29 K y) := by
  refine ⟨hgN, TwoThin.mem_normalizer_pPrimeCoreOf hgN, fun l hl => ?_⟩
  set N := Ly29 K y ⊓ pPrimeCoreOf 2 (L1 K y) with hNdef
  have hNle : N ≤ pPrimeCoreOf 2 (Ly29 K y) := by
    refine le_pPrimeCoreOf_of_odd inf_le_left (fun k hk => TwoThin.mem_normalizer_inf
      (Subgroup.le_normalizer hk)
      (L1_le_normalizer_pPrimeCoreOf K y (le_sup_left (b := Oy y) hk))) ?_
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      (coprime_card_pPrimeCoreOf _)
  have h1 : ⁅l, g⁆ ∈ Ly29 K y := by
    have h2 : g * l⁻¹ * g⁻¹ ∈ Ly29 K y := (Subgroup.mem_normalizer_iff.mp hgN _).mp (inv_mem hl)
    have h3 : ⁅l, g⁆ = l * (g * l⁻¹ * g⁻¹) := by simp only [commutatorElement_def]; group
    rw [h3]
    exact mul_mem hl h2
  exact hNle (Subgroup.mem_inf.2 ⟨h1, hg.2.2 l (le_sup_left (b := Oy y) hl)⟩)

section Setting

variable {x y : G} {K A B Q D J : Subgroup G}

theorem B_le_normalizer_L1 (h : Ctx29w G x K A B Q y y D J) :
    B ≤ normalizer ((L1 K y : Subgroup G) : Set G) := fun _ hb =>
  mem_normalizer_L1 (S3Sec29D2.B_le_centralizer_y h hb) (S3Sec29D5.B_le_normalizer_Ly h hb)

theorem Q_le_cSec_L1 (h : Ctx29w G x K A B Q y y D J) : Q ≤ cSec (L1 K y) := fun _ hq =>
  mem_cSec_L1 (S3Sec29D5.Q_le_centralizer_y h hq) (S3Sec29D5.Q_le_cSec_Ly h hq)

theorem Q_le_normalizer_L1 (h : Ctx29w G x K A B Q y y D J) :
    Q ≤ normalizer ((L1 K y : Subgroup G) : Set G) := fun _ hq => (Q_le_cSec_L1 h hq).1

end Setting

theorem y_mem_cSec_L1 (K : Subgroup G) (y : G) : y ∈ cSec (L1 K y) :=
  S3Ctx29.mem_cSec_of_le_centralizer (L1_le_centralizer K y)

end S3Sec29JB

end CFSG.GH74.Generic.BProg.B3
