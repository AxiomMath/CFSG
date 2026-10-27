module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepA
import CFSG.GroupTheory.SylowIntersectionControl.GomiOverCore
import CFSG.Quasithin.Background.A4V
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.GroupTheory

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne Subgroup
open scoped commutatorElement

variable {Ω : Type} [Group Ω] [Finite Ω] {f : PSubgroupSelection 2 Ω}
  {hyp : Subgroup Ω → Prop} {G : Subgroup Ω}

omit [Finite Ω] in
private theorem commutator_conjClosure_le_s4d {Q B V : Subgroup Ω} (hBG : B ≤ G)
    (hQn : G ≤ Subgroup.normalizer (Q : Set Ω))
    (hVn : G ≤ Subgroup.normalizer (V : Set Ω))
    (hQB : ⁅Q, B⁆ ≤ V) : ⁅Q, conjClosure B G⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro q hq n hn
  change n ∈ Subgroup.closure {x | ∃ h ∈ G, ∃ z ∈ B, h * z * h⁻¹ = x} at hn
  have hNG : Subgroup.closure {x | ∃ h ∈ G, ∃ z ∈ B, h * z * h⁻¹ = x} ≤ G :=
    conjClosure_le fun _ hh _ hz => G.mul_mem (G.mul_mem hh (hBG hz)) (G.inv_mem hh)
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g, hg, b, hb, rfl⟩ := hx
    have hgq : g⁻¹ * q * g ∈ Q := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hQn (G.inv_mem hg)) q).mp hq
    have hmem : ⁅g⁻¹ * q * g, b⁆ ∈ V := hQB (Subgroup.commutator_mem_commutator hgq hb)
    have hconj := conjugate_commutatorElement (g₁ := g⁻¹ * q * g) (g₂ := b) (g₃ := g)
    rw [show g * (g⁻¹ * q * g) * g⁻¹ = q by group] at hconj
    rw [← hconj]
    exact (Subgroup.mem_normalizer_iff.mp (hVn hg) _).mp hmem
  | one => rw [commutatorElement_one_right]; exact V.one_mem
  | mul a b ha hb iha ihb =>
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hconjV : a * ⁅q, b⁆ * a⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hVn (hNG ha)) _).mp ihb
    rw [show ⁅q, a⁆ * a * ⁅q, b⁆ * a⁻¹ = ⁅q, a⁆ * (a * ⁅q, b⁆ * a⁻¹) by group]
    exact V.mul_mem iha hconjV
  | inv a ha iha =>
    rw [commutatorElement_inv_right]
    have hmemV : ⁅a, q⁆ ∈ V := by
      rw [← commutatorElement_inv]
      exact V.inv_mem iha
    simpa using (Subgroup.mem_normalizer_iff.mp (hVn (G.inv_mem (hNG ha))) ⁅a, q⁆).mp hmemV

private theorem le_of_inf_conjClosure_le_s4d {Q C N S : Subgroup Ω}
    (hCG : C ≤ G) (hNn : G ≤ Subgroup.normalizer (N : Set Ω)) (hsup : G = N ⊔ S)
    (hS2 : IsPGroup 2 S) (hodd : ¬ 2 ∣ Q.relIndex C) (hCNQ : C ⊓ N ≤ Q) : C ≤ Q := by
  have hCin : C ≤ Subgroup.normalizer ((C ⊓ N : Subgroup Ω) : Set Ω) := by
    have hCC : C ≤ Subgroup.normalizer (C : Set Ω) := Subgroup.le_normalizer (H := C)
    have hCN : C ≤ Subgroup.normalizer (N : Set Ω) := hCG.trans hNn
    exact (le_inf hCC hCN).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := (C : Subgroup Ω)) (K := N))
  have hpow : ∀ d ∈ C, ∃ k : ℕ, d ^ 2 ^ k ∈ C ⊓ N := by
    intro d hd
    obtain ⟨k, hk⟩ := CFSG.Quasithin.B6.isTwoQuotient_of_sup_eq (C := N) (D := G)
      (T := S) hS2 hNn (by rw [sup_comm]; exact hsup.symm) d (hCG hd)
    exact ⟨k, C.pow_mem hd _, hk⟩
  obtain ⟨k, hk⟩ := CFSG.Quasithin.B6.exists_relIndex_eq_two_pow hCin hpow
  have hcop : Nat.Coprime ((C ⊓ N).relIndex C) (Q.relIndex C) := by
    rw [hk]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).pow_left k
  let L : Subgroup Ω := (C ⊓ N) ⊔ Q
  have hL : L.relIndex C = 1 := by
    refine Nat.eq_one_of_dvd_coprimes hcop ?_ ?_
    · exact Subgroup.relIndex_dvd_of_le_left (L := C) (show C ⊓ N ≤ L from le_sup_left)
    · exact Subgroup.relIndex_dvd_of_le_left (L := C) (show Q ≤ L from le_sup_right)
  exact (Subgroup.relIndex_eq_one.mp hL).trans (sup_le hCNQ le_rfl)

theorem Gomi410Cex.centralizer_eq (h : Gomi410Cex f hyp G)
    (hfZ : ∀ P : Subgroup Ω, IsPGroup 2 P → omegaOneCenterOf P ∈ f.sets P)
    (hchar : CharTwo G) (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H)
    {B : Subgroup Ω} (hB : IsGomiTwoComponent G B) (hQB : ⁅pCoreOf 2 G, B⁆ ≤ gomiV G)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S) :
    G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G := by
  have hQC : pCoreOf 2 G ≤ G ⊓ Subgroup.centralizer (gomiV G : Set Ω) := by
    refine le_inf (Subgroup.map_subtype_le (pCore 2 G)) ?_
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact ((Subgroup.mem_centralizer_iff.mp
      (CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf (pCoreOf 2 G) hv).2) q hq).symm
  have hQn : G ≤ Subgroup.normalizer (pCoreOf 2 G : Set Ω) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G
  have hVn : G ≤ Subgroup.normalizer (gomiV G : Set Ω) :=
    hQn.trans (CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf (pCoreOf 2 G))
  have hQN : ⁅pCoreOf 2 G, conjClosure B G⁆ ≤ gomiV G :=
    commutator_conjClosure_le_s4d hB.le hQn hVn hQB
  have hCNQ : (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) ⊓ conjClosure B G ≤ pCoreOf 2 G := by
    intro x hx
    obtain ⟨hxC, hxN⟩ := hx
    exact mem_pCoreOf_of_commutator_mem_gomiV hchar hxC.1 hxC.2
      (fun q hq => hQN (Subgroup.commutator_mem_commutator hq hxN))
  have hNn : G ≤ Subgroup.normalizer (conjClosure B G : Set Ω) := le_normalizer_conjClosure B G
  obtain ⟨S, hS⟩ := CFSG.QuasithinUnique.exists_isSylowTwoOf G
  have hSylC : IsSylowTwoOf (pCoreOf 2 G) (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) :=
    h.sylow_centralizer hfZ hchar hmono
  have hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) ≤ pCoreOf 2 G :=
    le_of_inf_conjClosure_le_s4d inf_le_left hNn (hGB S hS) hS.2.1 hSylC.2.2 hCNQ
  exact le_antisymm hCQ hQC

end CFSG.GroupTheory
