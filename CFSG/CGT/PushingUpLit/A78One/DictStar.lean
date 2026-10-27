module

public import CFSG.CGT.PushingUpLit.A78One.OneStmts
import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.CGT.PushingUpLit.A78One

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.T2K
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L M T T' : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem decomp_sup_of (hT'N : T' ≤ Subgroup.normalizer (L : Set G)) :
    ∀ b ∈ L ⊔ T', ∃ y ∈ L, ∃ q ∈ T', q ∈ L ⊔ T' ∧ y * q = b := by
  intro b hb
  rw [sup_comm] at hb
  obtain ⟨t, ht, l, hl, rfl⟩ := (mem_sup_iff_of_le_normalizer hT'N).1 hb
  exact ⟨t * l * t⁻¹, (Subgroup.mem_normalizer_iff.1 (hT'N ht) l).1 hl, t, ht,
    Subgroup.mem_sup_right ht, by group⟩

theorem sylow_H_of (hyp : T2Hyp G L M n) (nM : M ≤ Subgroup.normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hle : T' ≤ T)
    (hge : (T ⊓ L) ⊔ cexP L T ≤ T') : CFSG.ABGLocalTools.IsSylowOf 2 T' (L ⊔ T') := by
  have hT'N : T' ≤ Subgroup.normalizer (L : Set G) := (hle.trans hT.le).trans nM
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L) L := hT.inf_of_le_normalizer hyp.le nM
  have hLT' : L ⊓ T' = T ⊓ L := le_antisymm (le_inf (inf_le_right.trans hle) inf_le_left)
    (le_inf inf_le_right (le_sup_left.trans hge))
  have hprod := K1214.card_sup_mul_card_inf_of_le_normalizer hT'N
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_sup_right, hT.isPGroup.to_le hle, ?_⟩
  have h1 := Subgroup.relIndex_mul_card T' (L ⊔ T')
  have h2 := Subgroup.relIndex_mul_card (L ⊓ T') L
  rw [inf_eq_left.mpr (le_sup_right : T' ≤ L ⊔ T')] at h1
  rw [inf_eq_left.mpr (inf_le_left : L ⊓ T' ≤ L)] at h2
  have heq : T'.relIndex (L ⊔ T') = (L ⊓ T').relIndex L := by
    have hpos : 0 < Nat.card T' * Nat.card ↥(L ⊓ T') := Nat.mul_pos Nat.card_pos Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc T'.relIndex (L ⊔ T') * (Nat.card T' * Nat.card ↥(L ⊓ T'))
        = (T'.relIndex (L ⊔ T') * Nat.card T') * Nat.card ↥(L ⊓ T') := by ring
      _ = Nat.card ↥(L ⊔ T') * Nat.card ↥(L ⊓ T') := by rw [h1]
      _ = Nat.card L * Nat.card T' := hprod
      _ = ((L ⊓ T').relIndex L * Nat.card ↥(L ⊓ T')) * Nat.card T' := by rw [h2]
      _ = (L ⊓ T').relIndex L * (Nat.card T' * Nat.card ↥(L ⊓ T')) := by ring
  rw [heq, hLT']
  exact (CFSG.ABGLocalTools.isSylowOf_iff.1 hS).2.2

theorem inf_P_of (hyp : T2Hyp G L M n) (nM : M ≤ Subgroup.normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) : L ⊓ cexP L T = oTwoIn L := by
  apply le_antisymm
  · intro y hy
    rw [← hyp.natBlock.inf_centralizer_blockU]
    exact ⟨hy.1, hy.2.2⟩
  · intro y hy
    have hy' : y ∈ L ⊓ Subgroup.centralizer (blockU L : Set G) := by
      rw [hyp.natBlock.inf_centralizer_blockU]
      exact hy
    exact ⟨hy'.1, NatBlock.oTwoIn_le_sylow hyp.le nM hT hy, hy'.2⟩

theorem centralizer_U_of (hyp : T2Hyp G L M n) (nM : M ≤ Subgroup.normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hle : T' ≤ T)
    (hge : (T ⊓ L) ⊔ cexP L T ≤ T') :
    (L ⊔ T') ⊓ Subgroup.centralizer (blockU L : Set G) = cexP L T := by
  have hSyl := sylow_H_of hyp nM hT hle hge
  have hT'N : T' ≤ Subgroup.normalizer (L : Set G) := (hle.trans hT.le).trans nM
  have hHN : L ⊔ T' ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hT'N
  have hHM : L ⊔ T' ≤ M := sup_le hyp.le (hle.trans hT.le)
  apply le_antisymm
  · set R : Subgroup G := (L ⊔ T') ⊓ Subgroup.centralizer (blockU L : Set G) with hR
    have hRn : L ⊔ T' ≤ Subgroup.normalizer (R : Set G) := by
      intro h hh
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hC := Subgroup.mem_normalizer_iff.1
        (mem_normalizer_centralizer (NatBlock.le_normalizer_blockU_of_le nM (hHM hh))) y
      have hH := Subgroup.mem_normalizer_iff.1
        (Subgroup.le_normalizer hh : h ∈ Subgroup.normalizer ((L ⊔ T' : Subgroup G) : Set G)) y
      simp only [hR, Subgroup.mem_inf, hC, hH]
    have hR2 : IsPGroup 2 R := by
      intro r
      obtain ⟨k, hk⟩ := SubTwo.exists_pow_mem_of_decomp (Y := L) hHN
        (hT.isPGroup.to_le hle) (decomp_sup_of hT'N) (r : G) r.2.1
      have hk' : (r : G) ^ 2 ^ k ∈ L ⊓ Subgroup.centralizer (blockU L : Set G) :=
        ⟨hk, Subgroup.pow_mem _ r.2.2 _⟩
      rw [hyp.natBlock.inf_centralizer_blockU] at hk'
      obtain ⟨j, hj⟩ := isPGroup_oTwoIn L ⟨_, hk'⟩
      refine ⟨k + j, Subtype.ext ?_⟩
      have hj' : ((r : G) ^ 2 ^ k) ^ 2 ^ j = 1 := congrArg Subtype.val hj
      rw [Subgroup.coe_pow, pow_add, pow_mul, hj']
      rfl
    exact le_inf ((le_of_isPGroup_normal hSyl inf_le_left hRn hR2).trans hle) inf_le_right
  · exact le_inf ((le_sup_right.trans hge).trans le_sup_right) inf_le_right

theorem exists_phi_of (hyp : T2Hyp G L M n) (nM : M ≤ Subgroup.normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    ∃ φ : ↥(L ⊔ cexP L T) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
      Function.Surjective φ ∧ φ.ker = (cexP L T).subgroupOf (L ⊔ cexP L T) := by
  classical
  have D := hyp.natBlock.natData
  have hPN : cexP L T ≤ Subgroup.normalizer (L : Set G) := (inf_le_left.trans hT.le).trans nM
  have hLP : L ⊓ cexP L T = oTwoIn L := inf_P_of hyp nM hT
  let φ' : G → Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    fun g => if h : g ∈ L then D.φ ⟨g, h⟩ else 1
  have hφ'L : ∀ (g : G) (h : g ∈ L), φ' g = D.φ ⟨g, h⟩ := fun g h => by simp [φ', h]
  have hφ'mul : ∀ g g' : G, g ∈ L → g' ∈ L → φ' (g * g') = φ' g * φ' g' := by
    intro g g' hg hg'
    rw [hφ'L g hg, hφ'L g' hg', hφ'L (g * g') (L.mul_mem hg hg')]
    exact map_mul D.φ ⟨g, hg⟩ ⟨g', hg'⟩
  have hφ'one : φ' 1 = 1 := by
    rw [hφ'L 1 L.one_mem]
    exact map_one D.φ
  have hφ'ker : ∀ g : G, g ∈ L → (φ' g = 1 ↔ g ∈ oTwoIn L) := by
    intro g hg
    rw [hφ'L g hg]
    exact D.φ_ker ⟨g, hg⟩
  have hconj : ∀ p ∈ cexP L T, ∀ l ∈ L, p * l * p⁻¹ ∈ L ∧ φ' (p * l * p⁻¹) = φ' l := by
    intro p hp l hl
    have hpL : p * l * p⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hPN hp) l).1 hl
    have hc : ⁅p, l⁆ ∈ blockU L :=
      hyp.natBlock.comm_centralizer_mem_blockU nM ⟨hT.le hp.1, hp.2⟩ l hl
    have hcL : ⁅p, l⁆ ∈ L := blockU_le L hc
    have e : p * l * p⁻¹ = ⁅p, l⁆ * l := by
      simp only [commutatorElement_def]
      group
    refine ⟨hpL, ?_⟩
    rw [e, hφ'mul _ _ hcL hl, (hφ'ker _ hcL).2 (blockU_le_oTwoIn L hc), one_mul]
  have hwd : ∀ p ∈ cexP L T, ∀ p' ∈ cexP L T, ∀ l ∈ L, ∀ l' ∈ L, p * l = p' * l' →
      φ' l = φ' l' := by
    intro p hp p' hp' l hl l' hl' h
    have hll : l' * l⁻¹ ∈ L := L.mul_mem hl' (L.inv_mem hl)
    have hmemP : l' * l⁻¹ ∈ cexP L T := by
      have e : l' * l⁻¹ = p'⁻¹ * p := by
        calc l' * l⁻¹ = p'⁻¹ * (p' * l') * l⁻¹ := by group
          _ = p'⁻¹ * (p * l) * l⁻¹ := by rw [h]
          _ = p'⁻¹ * p := by group
      rw [e]
      exact (cexP L T).mul_mem ((cexP L T).inv_mem hp') hp
    have h1 : φ' (l' * l⁻¹) = 1 :=
      (hφ'ker _ hll).2 (by rw [← hLP]; exact ⟨hll, hmemP⟩)
    rw [hφ'mul _ _ hl' (L.inv_mem hl)] at h1
    have h2 : φ' l⁻¹ = (φ' l)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← hφ'mul _ _ (L.inv_mem hl) hl, inv_mul_cancel, hφ'one]
    rw [h2, mul_inv_eq_one] at h1
    exact h1.symm
  have hrep : ∀ s : ↥(L ⊔ cexP L T), ∃ p ∈ cexP L T, ∃ l ∈ L, (s : G) = p * l := by
    intro s
    have hs : (s : G) ∈ cexP L T ⊔ L := by
      rw [sup_comm]
      exact s.2
    exact (mem_sup_iff_of_le_normalizer hPN).1 hs
  choose p hp l hl hs using hrep
  have hf : ∀ (s : ↥(L ⊔ cexP L T)) (p' l' : G), p' ∈ cexP L T → l' ∈ L → (s : G) = p' * l' →
      φ' (l s) = φ' l' := fun s p' l' hp' hl' h =>
    hwd (p s) (hp s) p' hp' (l s) (hl s) l' hl' ((hs s).symm.trans h)
  have hmul : ∀ s s' : ↥(L ⊔ cexP L T), φ' (l (s * s')) = φ' (l s) * φ' (l s') := by
    intro s s'
    have hc := hconj (p s')⁻¹ ((cexP L T).inv_mem (hp s')) (l s) (hl s)
    rw [inv_inv] at hc
    have e : ((s * s' : ↥(L ⊔ cexP L T)) : G) =
        (p s * p s') * ((p s')⁻¹ * l s * p s' * l s') := by
      rw [Subgroup.coe_mul, hs s, hs s']
      group
    rw [hf (s * s') (p s * p s') ((p s')⁻¹ * l s * p s' * l s')
      ((cexP L T).mul_mem (hp s) (hp s')) (L.mul_mem hc.1 (hl s')) e,
      hφ'mul _ _ hc.1 (hl s'), hc.2]
  refine ⟨MonoidHom.mk' (fun s => φ' (l s)) hmul, ?_, ?_⟩
  · intro g
    obtain ⟨u, rfl⟩ := D.φ_surj g
    refine ⟨⟨(u : G), Subgroup.mem_sup_left u.2⟩, ?_⟩
    show φ' (l ⟨(u : G), Subgroup.mem_sup_left u.2⟩) = D.φ u
    rw [hf _ 1 (u : G) (cexP L T).one_mem u.2 (one_mul _).symm, hφ'L (u : G) u.2]
  · ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show φ' (l s) = 1 ↔ (s : G) ∈ cexP L T
    constructor
    · intro h
      have hlP : l s ∈ cexP L T := by
        have : l s ∈ oTwoIn L := (hφ'ker _ (hl s)).1 h
        rw [← hLP] at this
        exact this.2
      rw [hs s]
      exact (cexP L T).mul_mem (hp s) hlP
    · intro h
      rw [hf s (s : G) 1 h L.one_mem (mul_one _).symm, hφ'one]

theorem hyp45_of (hyp : T2Hyp G L M n) (nM : M ≤ Subgroup.normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hle : T' ≤ T)
    (hge : (T ⊓ L) ⊔ cexP L T ≤ T') {A : Subgroup G} (hA : IsMaxElemAbelian T' A)
    (hnt : ¬ A ≤ Subgroup.centralizer (blockU L : Set G)) : Hyp45 L (L ⊔ T') T' A n :=
  ⟨hyp.natBlock, le_sup_left,
    sup_le Subgroup.le_normalizer ((hle.trans hT.le).trans nM),
    sylow_H_of hyp nM hT hle hge, hA, hnt⟩

namespace CexCtx

variable {x : G}

theorem sylow_H (c : CexCtx L M n T T' x) : CFSG.ABGLocalTools.IsSylowOf 2 T' (L ⊔ T') :=
  sylow_H_of c.hyp c.nM c.sylow c.le c.ge

theorem centralizer_U (c : CexCtx L M n T T' x) :
    (L ⊔ T') ⊓ Subgroup.centralizer (blockU L : Set G) = cexP L T :=
  centralizer_U_of c.hyp c.nM c.sylow c.le c.ge

theorem inf_P (c : CexCtx L M n T T' x) : L ⊓ cexP L T = oTwoIn L :=
  inf_P_of c.hyp c.nM c.sylow

theorem exists_phi (c : CexCtx L M n T T' x) :
    ∃ φ : ↥(L ⊔ cexP L T) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
      Function.Surjective φ ∧ φ.ker = (cexP L T).subgroupOf (L ⊔ cexP L T) :=
  exists_phi_of c.hyp c.nM c.sylow

theorem hyp45 (c : CexCtx L M n T T' x) {A : Subgroup G} (hA : IsMaxElemAbelian T' A)
    (hnt : ¬ A ≤ Subgroup.centralizer (blockU L : Set G)) : Hyp45 L (L ⊔ T') T' A n :=
  hyp45_of c.hyp c.nM c.sylow c.le c.ge hA hnt

end CexCtx

end CFSG.CGT.PushingUpLit.A78One
