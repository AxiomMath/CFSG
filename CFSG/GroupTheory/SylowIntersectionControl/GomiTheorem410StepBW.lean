module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepA
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
import CFSG.GroupTheory.PCoreModulo
import CFSG.GroupTheory.ThompsonAxBNormal
import CFSG.GroupTheory.SubnormalJoin
import CFSG.GroupTheory.PowMemSupOfPGroup
public import CFSG.GroupTheory.SylowIntersectionControl.CharPair

public section

namespace CFSG.GroupTheory

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne Subgroup

variable {Ω : Type} [Group Ω] [Finite Ω] {f : PSubgroupSelection 2 Ω}
  {hyp : Subgroup Ω → Prop} {G : Subgroup Ω}

omit [Finite Ω] in
private theorem isPGroup_two_of_isElemAbelian_bw {U : Subgroup Ω}
    (hU : IsElemAbelian 2 U) : IsPGroup 2 U := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  simpa using hU.2 (x : Ω) x.2

omit [Finite Ω] in
private theorem normalizer_le_normalizer_centralizer_bw (U : Subgroup Ω) :
    Subgroup.normalizer (U : Set Ω) ≤
      Subgroup.normalizer (Subgroup.centralizer (U : Set Ω) : Set Ω) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.centralizer_le_normalizer (U : Set Ω))).mp
    (Subgroup.normal_subgroupOf_centralizer_normalizer (U : Set Ω))

omit [Finite Ω] in
private theorem le_normalizer_inf_centralizer_bw {G : Subgroup Ω}
    (hVG : G ≤ Subgroup.normalizer (gomiV G : Set Ω)) :
    G ≤ Subgroup.normalizer
      ((G ⊓ Subgroup.centralizer (gomiV G : Set Ω) : Subgroup Ω) : Set Ω) := by
  refine fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
    (H := G) (K := Subgroup.centralizer (gomiV G : Set Ω)) ?_
  exact Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hg,
    normalizer_le_normalizer_centralizer_bw (gomiV G) (hVG hg)⟩

private theorem subgroupOf_sup_isSubnormal_bw {L C : Subgroup Ω} (hLG : L ≤ G) (hCG : C ≤ G)
    (hL : (L.subgroupOf G).IsSubnormal) (hC : (C.subgroupOf G).IsSubnormal) :
    ((L ⊔ C).subgroupOf G).IsSubnormal := by
  rw [Subgroup.subgroupOf_sup hLG hCG]
  exact isSubnormal_sup hL hC

omit [Finite Ω] in
private theorem le_normalizer_inf_centralizer_of_normalizer_bw {V P H : Subgroup Ω}
    (hHV : H ≤ Subgroup.normalizer (V : Set Ω))
    (hHP : H ≤ Subgroup.normalizer (P : Set Ω)) :
    H ≤ Subgroup.normalizer
      ((V ⊓ Subgroup.centralizer (P : Set Ω) : Subgroup Ω) : Set Ω) := by
  refine fun h hh => Subgroup.inf_normalizer_le_normalizer_inf
    (H := V) (K := Subgroup.centralizer (P : Set Ω)) ?_
  exact Subgroup.mem_inf.mpr ⟨hHV hh, normalizer_le_normalizer_centralizer_bw P (hHP hh)⟩

private theorem subnormal_le_centralizer_bw (h : Gomi410Cex f hyp G)
    (hfZ : ∀ P : Subgroup Ω, IsPGroup 2 P → omegaOneCenterOf P ∈ f.sets P)
    (hchar : CharTwo G) (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H)
    {K D : Subgroup Ω} (hKG : K ≤ G) (hKsub : (K.subgroupOf G).IsSubnormal)
    (hDK : D ≤ K) (hKD : K ≤ Subgroup.normalizer (D : Set Ω))
    (hpwr : ∀ x ∈ D, ∃ k : ℕ, x ^ 2 ^ k ∈ G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) :
    D ≤ G ⊓ Subgroup.centralizer (gomiV G : Set Ω) := by
  have hVG : G ≤ Subgroup.normalizer (gomiV G : Set Ω) := (gomiV_moduleSetting G).2
  have hCG : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) ≤ G := inf_le_left
  have hGC : G ≤ Subgroup.normalizer
      ((G ⊓ Subgroup.centralizer (gomiV G : Set Ω) : Subgroup Ω) : Set Ω) :=
    le_normalizer_inf_centralizer_bw hVG
  obtain ⟨P₀, hCP₀, hP₀G, hGP₀, hP₀pwr, -, hlast⟩ :=
    exists_pCore_quotient_preimage (p := 2)
      (H := G) (C := G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) hCG hGC
  have hP₀C : P₀ ≤ G ⊓ Subgroup.centralizer (gomiV G : Set Ω) := by
    have hle : P₀ ≤ Subgroup.centralizer (gomiV G : Set Ω) :=
      h.le_centralizer_of_normal hfZ hchar hmono hCP₀ hP₀G hGP₀ (fun x hx => by
        obtain ⟨k, hk⟩ := hP₀pwr x hx
        exact ⟨k, hk.2⟩)
    exact fun x hx => ⟨hP₀G hx, hle hx⟩
  exact (hlast K D hKG hKsub hDK hKD hpwr).trans hP₀C

private theorem subnormal_le_centralizer_of_pow_mem_bw (h : Gomi410Cex f hyp G)
    (hfZ : ∀ P : Subgroup Ω, IsPGroup 2 P → omegaOneCenterOf P ∈ f.sets P)
    (hchar : CharTwo G) (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H)
    {K D : Subgroup Ω} (hKG : K ≤ G) (hKsub : (K.subgroupOf G).IsSubnormal)
    (hDK : D ≤ K) (hKD : K ≤ Subgroup.normalizer (D : Set Ω))
    (hpwr : ∀ x ∈ D, ∃ k : ℕ, x ^ 2 ^ k ∈ Subgroup.centralizer (gomiV G : Set Ω)) :
    D ≤ Subgroup.centralizer (gomiV G : Set Ω) := by
  have hpwrC : ∀ x ∈ D, ∃ k : ℕ,
      x ^ 2 ^ k ∈ G ⊓ Subgroup.centralizer (gomiV G : Set Ω) := by
    intro x hx
    obtain ⟨k, hk⟩ := hpwr x hx
    exact ⟨k, ⟨G.pow_mem (hKG (hDK hx)) (2 ^ k), hk⟩⟩
  exact (subnormal_le_centralizer_bw h hfZ hchar hmono hKG hKsub hDK hKD hpwrC).trans
    inf_le_right

private theorem commutator_le_centralizer_bw (h : Gomi410Cex f hyp G)
    (hfZ : ∀ P : Subgroup Ω, IsPGroup 2 P → omegaOneCenterOf P ∈ f.sets P)
    (hchar : CharTwo G) (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H)
    {P LC : Subgroup Ω} (hLCG : LC ≤ G) (hLCsub : (LC.subgroupOf G).IsSubnormal)
    (hLP : LC ≤ Subgroup.normalizer (P : Set Ω))
    (hPL : P ≤ Subgroup.normalizer (LC : Set Ω))
    (hPpwr : ∀ x ∈ P, ∃ k : ℕ, x ^ 2 ^ k ∈ G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) :
    ⁅P, LC⁆ ≤ Subgroup.centralizer (gomiV G : Set Ω) := by
  have h1 : ⁅P, LC⁆ ≤ P :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := LC) (K := P)).mp hLP
  have h2 : ⁅P, LC⁆ ≤ LC :=
    (Subgroup.le_normalizer_iff_commutator_le_right (H := P) (K := LC)).mp hPL
  have h3 : P ⊓ LC ≤ G ⊓ Subgroup.centralizer (gomiV G : Set Ω) :=
    subnormal_le_centralizer_bw h hfZ hchar hmono hLCG hLCsub inf_le_right
      (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        (H := P) (K := LC) (Subgroup.mem_inf.mpr ⟨hLP hx, Subgroup.le_normalizer hx⟩))
      (fun x hx => hPpwr x hx.1)
  exact (le_inf h1 h2).trans (h3.trans inf_le_right)

omit [Finite Ω] in
private theorem inf_centralizer_le_pCore_bw {S LC H P V W : Subgroup Ω}
    (hS2 : IsPGroup 2 S) (hSLC : S ≤ Subgroup.normalizer (LC : Set Ω))
    (hHLCS : H ≤ LC ⊔ S)
    (hLCW : LC ⊓ Subgroup.centralizer (W : Set Ω) ≤ Subgroup.centralizer (V : Set Ω))
    (hHG : H ≤ G)
    (hCP : G ⊓ Subgroup.centralizer (V : Set Ω) ≤ P)
    (hPmax : ∀ N : Subgroup Ω, N ≤ H → H ≤ Subgroup.normalizer (N : Set Ω) →
      (∀ x ∈ N, ∃ k : ℕ, x ^ 2 ^ k ∈ P) → N ≤ P)
    (hHW : H ≤ Subgroup.normalizer (W : Set Ω)) :
    H ⊓ Subgroup.centralizer (W : Set Ω) ≤ P := by
  refine hPmax (H ⊓ Subgroup.centralizer (W : Set Ω)) inf_le_left ?_ ?_
  · exact fun h hh => Subgroup.inf_normalizer_le_normalizer_inf
      (H := H) (K := Subgroup.centralizer (W : Set Ω))
      (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hh,
        normalizer_le_normalizer_centralizer_bw W (hHW hh)⟩)
  · intro x hx
    obtain ⟨k, hk⟩ := exists_pow_prime_pow_mem_of_mem_sup hS2 hSLC (hHLCS hx.1)
    have hkCW : x ^ 2 ^ k ∈ Subgroup.centralizer (W : Set Ω) :=
      (Subgroup.centralizer (W : Set Ω)).pow_mem hx.2 (2 ^ k)
    have hkCV : x ^ 2 ^ k ∈ Subgroup.centralizer (V : Set Ω) := hLCW ⟨hk, hkCW⟩
    have hkG : x ^ 2 ^ k ∈ G := G.pow_mem (hHG hx.1) (2 ^ k)
    exact ⟨k, hCP ⟨hkG, hkCV⟩⟩

omit [Finite Ω] in
private theorem le_centralizer_of_pow_mem_centralizer_bw {H P W : Subgroup Ω}
    (hHCP : H ⊓ Subgroup.centralizer (W : Set Ω) ≤ P)
    (hPCW : P ≤ Subgroup.centralizer (W : Set Ω))
    (hPmax : ∀ N : Subgroup Ω, N ≤ H → H ≤ Subgroup.normalizer (N : Set Ω) →
      (∀ x ∈ N, ∃ k : ℕ, x ^ 2 ^ k ∈ P) → N ≤ P)
    {N : Subgroup Ω} (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set Ω))
    (hpwr : ∀ x ∈ N, ∃ k : ℕ, x ^ 2 ^ k ∈ Subgroup.centralizer (W : Set Ω)) :
    N ≤ Subgroup.centralizer (W : Set Ω) := by
  refine (hPmax N hNH hHN ?_).trans hPCW
  intro x hx
  obtain ⟨k, hk⟩ := hpwr x hx
  exact ⟨k, hHCP ⟨H.pow_mem (hNH hx) (2 ^ k), hk⟩⟩

private theorem basic_facts_bw {S L : Subgroup Ω} (hS : IsSylowTwoOf S G) (hLG : L ≤ G)
    (hL : (L.subgroupOf G).IsSubnormal) (hSL : S ≤ normalizer (L : Set Ω))
    (hCL : G ⊓ centralizer (gomiV G : Set Ω) ≤ normalizer (L : Set Ω)) :
    IsPGroup 2 (gomiV G) ∧
      (G ⊓ centralizer (gomiV G : Set Ω)) ≤ G ∧
      G ≤ normalizer ((G ⊓ centralizer (gomiV G : Set Ω) : Subgroup Ω) : Set Ω) ∧
      ((L ⊔ S) ⊔ (G ⊓ centralizer (gomiV G : Set Ω))) ≤ G ∧
      (G ⊓ centralizer (gomiV G : Set Ω)) ≤
        ((L ⊔ S) ⊔ (G ⊓ centralizer (gomiV G : Set Ω))) ∧
      ((L ⊔ S) ⊔ (G ⊓ centralizer (gomiV G : Set Ω))) ≤ normalizer (L : Set Ω) ∧
      L ⊔ (G ⊓ centralizer (gomiV G : Set Ω)) ≤
        ((L ⊔ S) ⊔ (G ⊓ centralizer (gomiV G : Set Ω))) ∧
      L ⊔ (G ⊓ centralizer (gomiV G : Set Ω)) ≤ G ∧
      ((L ⊔ S) ⊔ (G ⊓ centralizer (gomiV G : Set Ω))) ≤
        normalizer ((L ⊔ (G ⊓ centralizer (gomiV G : Set Ω)) : Subgroup Ω) : Set Ω) ∧
      ((L ⊔ (G ⊓ centralizer (gomiV G : Set Ω))).subgroupOf G).IsSubnormal := by
  have hVG : G ≤ normalizer (gomiV G : Set Ω) := (gomiV_moduleSetting G).2
  have hCG : G ⊓ centralizer (gomiV G : Set Ω) ≤ G := inf_le_left
  have hGC : G ≤ normalizer ((G ⊓ centralizer (gomiV G : Set Ω) : Subgroup Ω) : Set Ω) :=
    le_normalizer_inf_centralizer_bw hVG
  have hHG : (L ⊔ S) ⊔ (G ⊓ centralizer (gomiV G : Set Ω)) ≤ G :=
    sup_le (sup_le hLG hS.1) hCG
  have hLH : (L ⊔ S) ⊔ (G ⊓ centralizer (gomiV G : Set Ω)) ≤ normalizer (L : Set Ω) :=
    sup_le (sup_le Subgroup.le_normalizer hSL) hCL
  have hLCH : (L ⊔ S) ⊔ (G ⊓ centralizer (gomiV G : Set Ω)) ≤
      normalizer ((L ⊔ (G ⊓ centralizer (gomiV G : Set Ω)) : Subgroup Ω) : Set Ω) :=
    fun h hh => Subgroup.inf_normalizer_le_normalizer_sup
      (H := L) (K := G ⊓ centralizer (gomiV G : Set Ω))
      (Subgroup.mem_inf.mpr ⟨hLH hh, hHG.trans hGC hh⟩)
  have hLCsub : ((L ⊔ (G ⊓ centralizer (gomiV G : Set Ω))).subgroupOf G).IsSubnormal :=
    subgroupOf_sup_isSubnormal_bw hLG hCG hL
      (((Subgroup.normal_subgroupOf_iff_le_normalizer hCG).mpr hGC).isSubnormal)
  exact ⟨isPGroup_two_of_isElemAbelian_bw (gomiV_moduleSetting G).1, hCG, hGC, hHG, le_sup_right,
    hLH, sup_le (le_sup_left.trans le_sup_left) le_sup_right, sup_le hLG hCG, hLCH, hLCsub⟩

theorem Gomi410Cex.exists_W (h : Gomi410Cex f hyp G)
    (hfZ : ∀ P : Subgroup Ω, IsPGroup 2 P → omegaOneCenterOf P ∈ f.sets P)
    (hchar : CharTwo G) (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H)
    {S L : Subgroup Ω} (hS : IsSylowTwoOf S G) (hLG : L ≤ G)
    (hL : (L.subgroupOf G).IsSubnormal) (hSL : S ≤ normalizer (L : Set Ω))
    (hCL : G ⊓ centralizer (gomiV G : Set Ω) ≤ normalizer (L : Set Ω)) :
    ∃ W : Subgroup Ω, W ≤ gomiV G ∧
      L ⊔ S ⊔ (G ⊓ centralizer (gomiV G : Set Ω)) ≤ normalizer (W : Set Ω) ∧
      (∀ N : Subgroup Ω, N ≤ L ⊔ S ⊔ (G ⊓ centralizer (gomiV G : Set Ω)) →
        L ⊔ S ⊔ (G ⊓ centralizer (gomiV G : Set Ω)) ≤ normalizer (N : Set Ω) →
        (∀ x ∈ N, ∃ k : ℕ, x ^ 2 ^ k ∈ centralizer (W : Set Ω)) →
        N ≤ centralizer (W : Set Ω)) ∧
      (L ⊔ (G ⊓ centralizer (gomiV G : Set Ω))) ⊓ centralizer (W : Set Ω) ≤
        centralizer (gomiV G : Set Ω) := by
  set V : Subgroup Ω := gomiV G with hV
  set C : Subgroup Ω := G ⊓ Subgroup.centralizer (V : Set Ω) with hC
  set LC : Subgroup Ω := L ⊔ C with hLC
  set H : Subgroup Ω := L ⊔ S ⊔ C with hH
  obtain ⟨hV2, -, hGC, hHG, hCH, -, hLCH2, hLCG, hLCH, hLCsub⟩ :=
    basic_facts_bw hS hLG hL hSL hCL
  obtain ⟨P, hCP, hPH, hHP, hPpwr, hPmax, -⟩ :=
    exists_pCore_quotient_preimage (p := 2) hCH (hHG.trans hGC)
  set W : Subgroup Ω := V ⊓ Subgroup.centralizer (P : Set Ω) with hW
  have hHW : H ≤ Subgroup.normalizer (W : Set Ω) :=
    le_normalizer_inf_centralizer_of_normalizer_bw (hHG.trans (gomiV_moduleSetting G).2) hHP
  have hPV : P ≤ Subgroup.normalizer (V : Set Ω) :=
    hPH.trans (hHG.trans (gomiV_moduleSetting G).2)
  have hNV : LC ≤ Subgroup.normalizer (V : Set Ω) := hLCG.trans (gomiV_moduleSetting G).2
  have hPpowV : ∀ y ∈ P, ∃ k : ℕ, y ^ 2 ^ k ∈ Subgroup.centralizer (V : Set Ω) := fun y hy => by
    obtain ⟨k, hk⟩ := hPpwr y hy; exact ⟨k, hk.2⟩
  have hPN : ⁅P, LC⁆ ≤ Subgroup.centralizer (V : Set Ω) :=
    commutator_le_centralizer_bw h hfZ hchar hmono hLCG hLCsub (hLCH2.trans hHP)
      (hPH.trans hLCH) hPpwr
  have hNcond : ∀ D : Subgroup Ω, D ≤ LC → LC ≤ Subgroup.normalizer (D : Set Ω) →
      (∀ x ∈ D, ∃ k : ℕ, x ^ 2 ^ k ∈ Subgroup.centralizer (V : Set Ω)) →
      D ≤ Subgroup.centralizer (V : Set Ω) := fun D hDLC hLnD hpw =>
    subnormal_le_centralizer_of_pow_mem_bw h hfZ hchar hmono hLCG hLCsub hDLC hLnD hpw
  have hAB : LC ⊓ Subgroup.centralizer (W : Set Ω) ≤ Subgroup.centralizer (V : Set Ω) :=
    inf_centralizer_le_centralizer_of_commutator_le (p := 2) hV2 hPV hNV hPpowV hPN hNcond
  have hHLCS : H ≤ LC ⊔ S := by
    rw [hH, hLC]
    exact sup_le (sup_le ((le_sup_left : L ≤ L ⊔ C).trans le_sup_left) le_sup_right)
      ((le_sup_right : C ≤ L ⊔ C).trans le_sup_left)
  have hHCP : H ⊓ Subgroup.centralizer (W : Set Ω) ≤ P :=
    inf_centralizer_le_pCore_bw hS.2.1 ((le_sup_right.trans le_sup_left).trans hLCH) hHLCS hAB
      hHG hCP hPmax hHW
  exact ⟨W, inf_le_left, hHW,
    fun N hNH hHN hpwr => le_centralizer_of_pow_mem_centralizer_bw hHCP
      ((Subgroup.le_centralizer_iff).mpr inf_le_right) hPmax hNH hHN hpwr, hAB⟩

end CFSG.GroupTheory
