module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301CoverLift2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Six

variable {G : Type} [Group G] [Finite G]

theorem SporCfgCore.hK6_sandwich_of_outer {p : ℕ} {row : Row} {x : G} {L : Subgroup G}
    (hx : orderOf x = p) (hL : GLAPComponent p (cx x) L) (hrow : RowL row p L)
    (hout : Nat.card (Outer (PQuot p L)) ≤ 2)
    (hrk1 : ∀ A : Subgroup G, IsElemAbelian p A → A ≤ cx x → (∀ a ∈ A, CentMod p L a) →
      Nat.card A ≤ p)
    (c : SporCfgCore G p x L row) :
    row = .ly ∨ (cfgK p x L c.D c.R ≤ GLAPLayer p (Subgroup.centralizer (c.D : Set G) ⊓
        Subgroup.centralizer (centerOf (cfgR0 c.R c.D) : Set G)) ∧
      GLAPLayer p (Subgroup.centralizer (c.D : Set G) ⊓
        Subgroup.centralizer (centerOf (cfgR0 c.R c.D) : Set G)) ≤
          cfgK p x L c.D c.R ⊔ GLAPPrimeCoreOf p (cx x)) := by
  rcases c.hK6L with h | ⟨hKE, himg⟩
  · exact Or.inl h
  right
  have hp : p.Prime := by rw [hrow.1]; cases row <;> norm_num [Row.prime]
  have hp2 : p ≠ 2 := by rw [hrow.1]; cases row <;> norm_num [Row.prime]
  haveI : Fact p.Prime := ⟨hp⟩
  set W : Subgroup G := Subgroup.centralizer (c.D : Set G) ⊓
    Subgroup.centralizer (centerOf (cfgR0 c.R c.D) : Set G) with hWdef
  set O : Subgroup G := GLAPPrimeCoreOf p (cx x) with hO
  have hWX : W ≤ cx x := inf_le_left.trans (S8.L89.centralizer_le_cx_of_mem c.hD.2.2.2)
  have hWL : W ≤ Subgroup.normalizer (L : Set G) := hWX.trans c.hLn
  have hWLn : ((L ⊓ W).subgroupOf W).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro w hw
    exact S10.mem_normalizer_inf_of (hWL hw) (Subgroup.le_normalizer hw)
  have hEW : GLAPLayer p (L ⊓ W) ≤ GLAPLayer p W := by
    unfold GLAPLayer
    exact sSup_le fun J hJ => le_sSup
      (CFSG.HardMathSupport.Solomon.Proving.glaPComponent_of_normal_overgroup hp inf_le_right
        hWLn hJ)
  have hEK : GLAPLayer p (L ⊓ W) ≤ cfgK p x L c.D c.R ⊔ GLAPPrimeCoreOf p L := by
    intro e he
    have heL : e ∈ L := ((glaPLayer_le_self' _).trans inf_le_left) he
    have hmem : pQuotHom p L ⟨e, heL⟩ ∈ lImg p L (GLAPLayer p (L ⊓ W)) :=
      ⟨⟨e, heL⟩, he, rfl⟩
    rw [himg] at hmem
    obtain ⟨k, hk, hke⟩ := hmem
    have hk' : (k : G) ∈ cfgK p x L c.D c.R := hk
    have hko : (k : G)⁻¹ * e ∈ GLAPPrimeCoreOf p L := (pQuot_mk_eq_mk_iff k ⟨e, heL⟩).1 hke
    rw [show e = (k : G) * ((k : G)⁻¹ * e) by group]
    exact Subgroup.mul_mem_sup hk' hko
  have hOL : GLAPPrimeCoreOf p L ≤ O :=
    HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal p hL.2.1
  have hWK : GLAPLayer p W ≤ cfgK p x L c.D c.R ⊔ O := by
    have hle : GLAPLayer p W ≤ GLAPLayer p (L ⊓ W) := by
      unfold GLAPLayer
      refine sSup_le fun Q hQ => le_sSup ?_
      have hQL : Q ≤ L := le_of_glaPComponent_of_le_cx hp hp2 hx hL hout hrk1 c.hLn hWX hQ
      exact glaPComponent_of_le hp hQ (le_inf hQL hQ.1) inf_le_right
    exact hle.trans (hEK.trans (sup_le_sup_left hOL _))
  exact ⟨hKE.trans hEW, hWK⟩

theorem SporCfgCore.hK6_layer_of_outer {p : ℕ} {row : Row} {x : G} {L : Subgroup G}
    (hx : orderOf x = p) (hL : GLAPComponent p (cx x) L) (hrow : RowL row p L)
    (hout : Nat.card (Outer (PQuot p L)) ≤ 2)
    (hrk1 : ∀ A : Subgroup G, IsElemAbelian p A → A ≤ cx x → (∀ a ∈ A, CentMod p L a) →
      Nat.card A ≤ p)
    (c : SporCfgCore G p x L row) :
    row = .ly ∨ (cfgK p x L c.D c.R ≤ GLAPLayer p (Subgroup.centralizer (c.D : Set G) ⊓
        Subgroup.centralizer (centerOf (cfgR0 c.R c.D) : Set G)) ∧
      GLAPLayer p (Subgroup.centralizer (c.D : Set G) ⊓
        Subgroup.centralizer (centerOf (cfgR0 c.R c.D) : Set G)) ≤
          cfgK p x L c.D c.R ⊔ GLAPPrimeCoreOf p (GLAPLayer p
            (Subgroup.centralizer (c.D : Set G) ⊓
              Subgroup.centralizer (centerOf (cfgR0 c.R c.D) : Set G)))) := by
  rcases c.hK6_sandwich_of_outer hx hL hrow hout hrk1 with h | ⟨hKΛ, hΛKO⟩
  · exact Or.inl h
  right
  refine ⟨hKΛ, ?_⟩
  have hp : p.Prime := by rw [hrow.1]; cases row <;> norm_num [Row.prime]
  haveI : Fact p.Prime := ⟨hp⟩
  set Λ : Subgroup G := GLAPLayer p (Subgroup.centralizer (c.D : Set G) ⊓
    Subgroup.centralizer (centerOf (cfgR0 c.R c.D) : Set G)) with hΛdef
  set O : Subgroup G := GLAPPrimeCoreOf p (cx x) with hO
  have hΛX : Λ ≤ cx x :=
    (glaPLayer_le_self' _).trans (inf_le_left.trans (S8.L89.centralizer_le_cx_of_mem c.hD.2.2.2))
  have hON : cx x ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf p (cx x)
  have hOcop : Nat.Coprime (Nat.card O) p := by
    have h1 : Nat.card O = Nat.card (GLAPPrimeCore p ↥(cx x)) :=
      Subgroup.card_map_of_injective (cx x).subtype_injective
    rw [h1]
    exact (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥(cx x))).symm
  have hcore : Λ ⊓ O ≤ GLAPPrimeCoreOf p Λ := S10.inf_le_glaPPrimeCoreOf (hΛX.trans hON) hOcop
  intro y hy
  have hy' : y ∈ ((cfgK p x L c.D c.R ⊔ O : Subgroup G) : Set G) := hΛKO hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ O ((hKΛ.trans hΛX).trans hON)] at hy'
  obtain ⟨k, hk, o, ho, rfl⟩ := Set.mem_mul.1 hy'
  have hoΛ : o ∈ Λ := by
    have e : o = k⁻¹ * (k * o) := by group
    rw [e]
    exact Λ.mul_mem (Λ.inv_mem (hKΛ hk)) hy
  exact Subgroup.mul_mem_sup hk (hcore ⟨hoΛ, ho⟩)

end Six

theorem i301ACoverAt_of_rows
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    {G : Type} [Group G] [Finite G] {p : ℕ} (hcov : ∀ row : Row, I301ARowCover row) :
    I301ACoverAt G p := by
  intro x L row hc hx1 hx hL hKG hrow hodd hrk1 hrk
  obtain ⟨c⟩ := nonempty_sporCfgCore_cover (hcov row) hc hx1 hx hL hrow hodd hrk1 hrk
  have hp : p.Prime := by rw [hrow.1]; cases row <;> norm_num [Row.prime]
  have hout := card_outer_pQuot_le_two hOut hp hL hrow
  exact ⟨{
    Bs := c.Bs
    R := c.R
    D := c.D
    hBs := c.hBs
    hBsCard := c.hBsCard
    hRL := c.hRL
    hR := c.hR
    hBsN := c.hBsN
    hRN := c.hRN
    hD := c.hD
    hData := c.hData
    hMax := c.hMax
    hR0 := c.hR0
    hK6 := c.hK6_layer_of_outer hx hL hrow hout hrk1
    hNL := c.hNL }⟩

end CFSG.LocalAnalysis.GLTheoremA.H301
