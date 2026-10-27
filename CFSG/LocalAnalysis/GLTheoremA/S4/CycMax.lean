module

public import CFSG.LocalAnalysis.GLTheoremA.Sec5A
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma29Comp

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

theorem centralizer_zpowers_eq' (a : G) :
    Subgroup.centralizer (Subgroup.zpowers a : Set G) = Subgroup.centralizer ({a} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem glaPLayer_eq_self_of_glaPComponent {p : ℕ} (hp : p.Prime) {X L : Subgroup G}
    (hL : GLAPComponent p X L) : GLAPLayer p L = L := by
  obtain ⟨hHc, -, hbar⟩ := glaPLayer_of_isQuasisimple (isQuasisimple_pQuot_of_glaPComponent hp hL)
  set H := GLAPLayer p L with hHdef
  have hHL : H ≤ L := hHc.1
  have hsup : H ⊔ GLAPPrimeCoreOf p L = L := sup_glaPPrimeCoreOf_eq_of_barX_eq_top hHL hbar
  have hOX : GLAPPrimeCoreOf p L ≤ GLAPPrimeCoreOf p X := by
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hL.2.1]
    exact inf_le_right
  by_contra hne
  apply hL.2.2.2 H (lt_of_le_of_ne hHL hne) (isSubnormal_trans' hHc.2.1 hL.2.1)
  apply le_antisymm
  · rintro _ ⟨⟨h, hhX⟩, hh, rfl⟩
    exact ⟨⟨h, hhX⟩, hHL hh, rfl⟩
  · rintro _ ⟨⟨l, hlX⟩, hl, rfl⟩
    have hl' : l ∈ (H ⊔ GLAPPrimeCoreOf p L : Subgroup G) := hsup.symm ▸ hl
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right H _
      (hHL.trans (le_normalizer_glaPPrimeCoreOf p L))] at hl'
    obtain ⟨h, hh, o, ho, rfl⟩ := Set.mem_mul.mp hl'
    obtain ⟨o', ho', rfl⟩ := hOX ho
    have hhX : h ∈ X := (hHL.trans hL.1) hh
    refine ⟨⟨h, hhX⟩, hh, ?_⟩
    have e : (⟨h * X.subtype o', hlX⟩ : ↥X) = ⟨h, hhX⟩ * o' := rfl
    rw [e, map_mul, show (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) o' = 1 from
      (QuotientGroup.eq_one_iff o').2 ho', mul_one]

theorem eq_of_glaPComponent_of_glaPComponent {p : ℕ} (hp : p.Prime) {X L K : Subgroup G}
    (hL : GLAPComponent p X L) (hK : GLAPComponent p L K) : K = L := by
  obtain ⟨-, huniq, -⟩ := glaPLayer_of_isQuasisimple (isQuasisimple_pQuot_of_glaPComponent hp hL)
  rw [huniq K hK, glaPLayer_eq_self_of_glaPComponent hp hL]

theorem closureIn_glaPLayer_eq {p : ℕ} (hp : p.Prime) {X L : Subgroup G}
    (hL : GLAPComponent p X L) : closureIn L (GLAPLayer p X) = L := by
  refine closureIn_eq_self (sSup_le fun K hK => ?_)
  by_cases hKL : K = L
  · rw [hKL]
    exact Subgroup.le_normalizer
  · exact fun k hk => CFSG.HardMathSupport.Solomon.LocalBalance.mem_normalizer_of_ne hp hL hK
      (Ne.symm hKL) hk

theorem eq_of_pumpRel_of_cycModSylow {p : ℕ} (hp : p.Prime) {t t' : Triple G}
    (hcyc : CycModSylow p t.2.2) (hrel : PumpRel p t t') : t'.2.2 = t.2.2 := by
  obtain ⟨⟨-, hx, hL⟩, ⟨hB', hx', -⟩, hxB', -, hx'B', hx'L, hL'⟩ := hrel
  have hxp : t.2.1 ^ p = 1 := hB'.1.2 _ hxB'
  have hx'p : t'.2.1 ^ p = 1 := hB'.1.2 _ hx'B'
  have hxC : t.2.1 ∈ Subgroup.centralizer (t.2.2 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1 (hL.1 hl)
  set D := Subgroup.zpowers t.2.1 ⊔ Subgroup.zpowers t'.2.1 with hD
  have hDB : D ≤ t'.1 := sup_le (Subgroup.zpowers_le.2 hxB') (Subgroup.zpowers_le.2 hx'B')
  have hDcm : ∀ d ∈ D, CentMod p t.2.2 d := by
    have hle : D ≤ centModSubgroup p t.2.2 := sup_le
      (Subgroup.zpowers_le.2 (centMod_iff.1 (centMod_of_mem_centralizer hxC)))
      (Subgroup.zpowers_le.2 (centMod_iff.1 hx'L))
    exact fun d hd => centMod_iff.2 (hle hd)
  have hDcyc : IsCyclic D := hcyc D hDcm ((isPGroup_of_isElemAbelian hB'.1).to_le hDB)
  have hDp : Nat.card D ≤ p := card_le_of_isCyclic_of_pow hp hDcyc fun d hd => hB'.1.2 d (hDB hd)
  have hx'x : t'.2.1 ∈ Subgroup.zpowers t.2.1 := mem_zpowers_of_card_sup_le hp hxp hx.2.1 hDp
  have hxx' : t.2.1 ∈ Subgroup.zpowers t'.2.1 := by
    refine mem_zpowers_of_card_sup_le hp hx'p hx'.2.1 ?_
    rw [sup_comm]
    exact hDp
  have hC : Subgroup.centralizer ({t'.2.1} : Set G) = Subgroup.centralizer ({t.2.1} : Set G) := by
    rw [← centralizer_zpowers_eq', ← centralizer_zpowers_eq' t.2.1]
    congr 2
    exact le_antisymm (Subgroup.zpowers_le.2 hx'x) (Subgroup.zpowers_le.2 hxx')
  rw [hC, inf_eq_left.2 hL.1, glaPLayer_eq_self_of_glaPComponent hp hL,
    closureIn_glaPLayer_eq hp hL] at hL'
  exact eq_of_glaPComponent_of_glaPComponent hp hL hL'

theorem isSMax_of_cycModSylow {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {x : G}
    (hS : IsSTriple p B x L) (hcyc : CycModSylow p L) : IsSMax p B x L := by
  refine ⟨hS, ?_⟩
  rintro ⟨t'', s, s', hts, hss', hnc, -⟩
  have hL : ∀ t' : Triple G, Relation.ReflTransGen (PumpRel p) (B, x, L) t' → t'.2.2 = L := by
    intro t' h
    induction h with
    | refl => rfl
    | tail _ hstep ih =>
      rw [eq_of_pumpRel_of_cycModSylow hp (ih ▸ hcyc) hstep, ih]
  apply hnc
  rw [eq_of_pumpRel_of_cycModSylow hp ((hL s hts).symm ▸ hcyc) hss', hL s hts]
  have hsS : IsSTriple p s.1 s.2.1 s.2.2 := hss'.1
  rw [← hL s hts]
  exact centMod_of_mem_centralizer (IsSTriple.mem_centralizer hsS)

end CFSG.LocalAnalysis.GLTheoremA
