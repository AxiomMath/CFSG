module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2Down
public import CFSG.HardMathSupport.Solomon.Coordinator.I713
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Trans2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.S171
open scoped commutatorElement

section One

theorem i171one_of_facts (G : Type) [Group G] [Finite G] (hShape : T171ShapeFact)
    (hSize : T171SizeFact) (hERank : I171ExtremalRankFact) (hNoAct : T171NoActFact) :
    I171OneAt G := by
  intro p B x L D K hp hp2 hS h4 hq hchev hKG hid hpre
  have hcfg : Cfg G p B x L := cfg_of_sstarMax hp hp2 hS h4 hq hchev hid
  have hmax : MaxG p B := maxG_of_isBmax hp (IsSStarMax.bmax hS)
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := (IsSStarMax.component hS).1
  have hBK : B ≤ Subgroup.normalizer (K : Set G) := B_norm_K hcfg.elem hcfg.norm hpre
  have hKcomp : IsComponentOf K (L ⊓ Subgroup.centralizer (D : Set G)) := hpre.2.2.2.2.2.1
  have hKq : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  have hKL : K ≤ L := hKcomp.1.trans inf_le_left
  have hKY : K ≤ Subgroup.centralizer ({x} : Set G) := hKL.trans hLx
  have hDK : D = B ⊓ Subgroup.centralizer (K : Set G) := hpre.2.2.2.2.2.2
  have hdvd : p ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
    refine dvd_of_faithful CFSG.HardMathSupport.Solomon.Coordinator.i_7_13_1_pPrime_holds hp hp2 hKG hKY hKq
      hcfg.elem hBK ?_
    rw [← hDK, hpre.2.2.1]
    calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
      _ ≤ Nat.card B := h4
  have hKpc : GLAPComponent p (L ⊓ Subgroup.centralizer (D : Set G)) K :=
    S12.glaPComponent_of_quasisimple' hp hKcomp.2.1 hKq hdvd
  obtain ⟨y, hyD, hyx⟩ := exists_y hp hcfg.ne_one hpre
  have hKy : GLAPComponent p (L ⊓ Subgroup.centralizer ({y} : Set G)) K := by
    rw [← L_cs_eq hp hcfg.ne_one hpre hyD hyx hLx]
    exact hKpc
  have hyp : y ^ p = 1 := hpre.2.1.2 y hyD
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hcfg.norm (hpre.1 hyD)
  have hKchev : IsChevSimple 2 (PSimple p K) :=
    chev2DownAt_holds (G := G) p hp hp2 _ L y hKG (IsSStarMax.component hS) hyp hyN hchev K hKy
  have haut := MI.autCalcAt_all G p
  by_contra hnot
  have hex : ∃ β ∈ B, ¬ InnDiagOn p (Subgroup.zpowers β) K := by
    by_contra hall
    push Not at hall
    exact hnot (haut.innDiag_unif _ K B hKpc hKchev hBK hall)
  obtain ⟨β, hβB, hβ⟩ := hex
  have hβD : β ∉ D := by
    intro hβD
    apply hβ
    have hβc : β ∈ Subgroup.centralizer (K : Set G) := by
      rw [hDK] at hβD
      exact hβD.2
    refine haut.inner_innDiag _ K β hKpc hKchev (hBK hβB) ⟨1, K.one_mem, fun z hz => ?_⟩
    have hzβ : z * β = β * z := Subgroup.mem_centralizer_iff.1 hβc z hz
    have : β⁻¹ * z * β = z := by
      rw [mul_assoc, hzβ, inv_mul_cancel_left]
    rw [this]
    simp only [inv_one, one_mul, mul_one, inv_mul_cancel]
    exact Subgroup.one_mem _
  obtain ⟨T, hTN, hTC, hT2, hBT, hne⟩ := exists_T_of_sstarMax hp hp2 hS
  have hBx : B ≤ Subgroup.centralizer ({x} : Set G) := fun b hb => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact isElemAbelian_commute hcfg.elem hb hcfg.mem
  have hLX : L ≤ (L ⊔ B) ⊔ T := le_sup_left.trans le_sup_left
  have hBX : B ≤ (L ⊔ B) ⊔ T := le_sup_right.trans le_sup_left
  have hTX : T ≤ (L ⊔ B) ⊔ T := le_sup_right
  have hxX : x ∈ (L ⊔ B) ⊔ T := hBX hcfg.mem
  have hXC : (L ⊔ B) ⊔ T ≤ Subgroup.centralizer ({x} : Set G) := sup_le (sup_le hLx hBx) hTC
  have hXN : (L ⊔ B) ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer hcfg.norm) hTN
  have hKX : CFSG.Open.IsKGroup ↥((L ⊔ B) ⊔ T) := CFSG.Open.IsKGroup.of_le hKG hXC
  have hLn : (L.subgroupOf ((L ⊔ B) ⊔ T)).Normal := normal_subgroupOf_of_le_normalizer _ hLX hXN
  have hDX : D ≤ (L ⊔ B) ⊔ T := hpre.1.trans hBX
  have hKX' : K ≤ (L ⊔ B) ⊔ T := hKL.trans hLX
  have hβX : β ∈ (L ⊔ B) ⊔ T := hBX hβB
  have hcfgX := cfg_subgroupOf _ hBX hLX hxX hcfg
  have hmaxX := maxG_subgroupOf _ hBX hmax
  have hpreX := (glaStdSubPre_subgroupOf_iff _ hxX hBX hLX hDX hKX').2 hpre
  have hKpcX := (glaPComponent_subgroupOf_iff _ hp hLX hDX hKX').2 hKpc
  have hKchevX := chevSimple_subgroupOf _ hKX' hKchev
  have hβB' : (⟨β, hβX⟩ : ↥((L ⊔ B) ⊔ T)) ∈ B.subgroupOf ((L ⊔ B) ⊔ T) := Subgroup.mem_subgroupOf.2 hβB
  have hβD' : (⟨β, hβX⟩ : ↥((L ⊔ B) ⊔ T)) ∉ D.subgroupOf ((L ⊔ B) ⊔ T) :=
    fun h => hβD (Subgroup.mem_subgroupOf.1 h)
  have hβ' : ¬ InnDiagOn p (Subgroup.zpowers (⟨β, hβX⟩ : ↥((L ⊔ B) ⊔ T))) (K.subgroupOf ((L ⊔ B) ⊔ T)) := by
    rw [← zpowers_subgroupOf_eq _ hβX]
    intro h
    exact hβ ((innDiagOn_subgroupOf_iff _ (p := p) (Subgroup.zpowers_le.2 hβX) hKX').1 h)
  have hextX := hShape p ↥((L ⊔ B) ⊔ T) (B.subgroupOf ((L ⊔ B) ⊔ T)) ⟨x, hxX⟩ (L.subgroupOf ((L ⊔ B) ⊔ T))
    (D.subgroupOf ((L ⊔ B) ⊔ T)) (K.subgroupOf ((L ⊔ B) ⊔ T)) ⟨β, hβX⟩ hKX hcfgX hmaxX hLn hpreX hKpcX hKchevX
    hβB' hβD' hβ'
  have hext : S171.ExtremalType p L := (extremalType_subgroupOf_iff _ hLX).1 hextX
  have hsizeX := hSize p ↥((L ⊔ B) ⊔ T) (B.subgroupOf ((L ⊔ B) ⊔ T)) ⟨x, hxX⟩ (L.subgroupOf ((L ⊔ B) ⊔ T))
    (D.subgroupOf ((L ⊔ B) ⊔ T)) (K.subgroupOf ((L ⊔ B) ⊔ T)) ⟨β, hβX⟩ hKX hcfgX hLn hpreX hKpcX hKchevX
    hβB' hβD' hβ' hextX
  have hsize : (∀ n : ℕ, catalogIs (PSimple p L) (S10.isU6n n) → Nat.card B ≤ 3 ^ 4) ∧
      (∀ n : ℕ, catalogIs (PSimple p L) (S10.isTE6n n) → Nat.card B ≤ 3 ^ 5) := by
    have hcB : Nat.card (B.subgroupOf ((L ⊔ B) ⊔ T)) = Nat.card B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv
    refine ⟨fun n hn => ?_, fun n hn => ?_⟩
    · have h := hsizeX.1 n ((catalogIs_pSimple_subgroupOf _ hLX).1 hn)
      rwa [hcB] at h
    · have h := hsizeX.2 n ((catalogIs_pSimple_subgroupOf _ hLX).1 hn)
      rwa [hcB] at h
  have hrank : ¬ Rank p B L := by
    obtain ⟨hp3, n, hn, hU | hT⟩ := hext
    · subst hp3
      obtain ⟨E, hEL, hE, hEc⟩ := (hERank G L hcfg.qs n hn).1 hU
      exact not_rank_of_big_elem hcfg hEL hEc hE (lt_of_le_of_lt (hsize.1 n hU) (by norm_num))
    · subst hp3
      obtain ⟨E, hEL, hE, hEc⟩ := (hERank G L hcfg.qs n hn).2 hT
      exact not_rank_of_big_elem hcfg hEL hEc hE (lt_of_le_of_lt (hsize.2 n hT) (by norm_num))
  have hnoactX := hNoAct p ↥((L ⊔ B) ⊔ T) (B.subgroupOf ((L ⊔ B) ⊔ T)) ⟨x, hxX⟩ (L.subgroupOf ((L ⊔ B) ⊔ T))
    (D.subgroupOf ((L ⊔ B) ⊔ T)) (K.subgroupOf ((L ⊔ B) ⊔ T)) ⟨β, hβX⟩ hKX hcfgX hmaxX hLn hpreX hKpcX hKchevX
    hβB' hβD' hβ' hextX
  have hcomm : (⁅T, B⁆ : Subgroup G) ≤ Subgroup.centralizer (L : Set G) := by
    apply commutator_le_centralizer_of_subgroupOf _ hTX hBX hLX
    apply hnoactX (T.subgroupOf ((L ⊔ B) ⊔ T))
    · exact le_normalizer_subgroupOf' _ hTX hLX hTN
    · exact le_centralizer_singleton_subgroupOf _ hTX hxX hTC
    · exact IsPGroup.of_injective hT2 (Subgroup.subgroupOfEquivOfLe hTX).toMonoidHom (MulEquiv.injective _)
    · exact le_normalizer_subgroupOf' _ hBX hTX hBT
  have hle : (⁅T, B⁆ : Subgroup G) ≤ T := commutator_le_left_of_normalizes hBT
  exact hrank (rank_of_two_group hcfg.elem hmax hne (IsPGroup.to_le hT2 hle) hcomm
    (le_normalizer_commutator hBT Subgroup.le_normalizer))

end One

end CFSG.LocalAnalysis.GLTheoremA.T171

end
