module

public import CFSG.RankThree.PartOne.KS.PKitLeaf
public import CFSG.RankThree.PartOne.KS.PKitLines

public section

namespace CFSG.HardMathSupport.Dickson.I271

open Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartOne
open CFSG.Certificates.ChainArrays

@[expose] def leafMem (n : ℕ) (gS : Array (Array ℕ)) (M T : Array ℕ → Bool) (a : Array ℕ) : Bool :=
  let ai := invCand n a
  isInvA n a ai &&
    allLt gS.size (fun l => M (compA n a (compA n gS[l]! ai))) &&
    (!(allLt gS.size fun l => commA n a gS[l]!) || T a)

theorem leafMem_spec {n : ℕ} {gS : Array (Array ℕ)} {M T : Array ℕ → Bool}
    {S : Subgroup (Equiv.Perm (Fin n))} {Pr : Equiv.Perm (Fin n) → Prop}
    (hgv : ∀ l < gS.size, validA n gS[l]! = true)
    (hM : ∀ {t : Array ℕ} {G : Equiv.Perm (Fin n)}, Rep n t G → M t = true → G ∈ S)
    (hT : ∀ {t : Array ℕ} {G : Equiv.Perm (Fin n)}, Rep n t G → T t = true → Pr G)
    {a : Array ℕ} {G : Equiv.Perm (Fin n)} (hG : Rep n a G)
    (h : leafMem n gS M T a = true) :
    (∀ l < gS.size, G * permOfArr n gS[l]! * G⁻¹ ∈ S) ∧
      ((∀ l < gS.size, permOfArr n gS[l]! * G = G * permOfArr n gS[l]!) → Pr G) := by
  simp only [leafMem, Bool.and_eq_true] at h
  obtain ⟨⟨hinv, hconj⟩, hcent⟩ := h
  have hGi : Rep n (invCand n a) G⁻¹ := rep_inv_of_isInvA hG hinv
  constructor
  · intro l hl
    have hrl : Rep n gS[l]! (permOfArr n gS[l]!) := rep_of_validA (hgv l hl)
    have hc : Rep n (compA n a (compA n gS[l]! (invCand n a)))
        (G * (permOfArr n gS[l]! * G⁻¹)) := rep_compA hG (rep_compA hrl hGi)
    have := hM hc (allLt_spec hconj hl)
    rwa [← mul_assoc] at this
  · intro hcomm
    have hall : (allLt gS.size fun l => commA n a gS[l]!) = true := by
      refine allLt_iff.2 fun l hl => ?_
      exact (commA_iff hG (rep_of_validA (hgv l hl))).2 (hcomm l hl).symm
    rw [hall, Bool.not_true, Bool.false_or] at hcent
    exact hT hG hcent

@[expose] def centNormMemOKP (p n : ℕ) (S : Array (Array ℕ)) (base x : Array ℕ)
    (rels : List (ℕ × ℕ × ℕ)) (gS : Array (Array ℕ)) (M T : Array ℕ → Bool) : Bool :=
  relsOKP p n base x rels &&
    allLt gS.size (fun k => validA n gS[k]! && commA n gS[k]! x &&
      siftA n (rawLevels n S base) base 0 gS[k]!) &&
    siftA n (rawLevels n S base) base 0 x &&
    ptailOKQ n (rawLevels n S base) base x (powPA p n x) rels (leafMem n gS M T) base.size 0
      (idA n)

section Spec

variable {n : ℕ}

theorem centNormMem_of_ptailOKQ {p : ℕ} {Q : RawSchreierDatum n} {O S : Array (Array ℕ)}
    {base : Array ℕ} {W : Array (List ℤ)} (hA : ChainArrays Q O S base W)
    (hc : rawChainOK n O S base W 1 = true) {x : Array ℕ} {X : Equiv.Perm (Fin n)}
    (hx : Rep n x X) {rels : List (ℕ × ℕ × ℕ)} {gS : Array (Array ℕ)} {M T : Array ℕ → Bool}
    {Sg : Subgroup (Equiv.Perm (Fin n))} {Pr : Equiv.Perm (Fin n) → Prop}
    (hM : ∀ {t : Array ℕ} {G : Equiv.Perm (Fin n)}, Rep n t G → M t = true → G ∈ Sg)
    (hT : ∀ {t : Array ℕ} {G : Equiv.Perm (Fin n)}, Rep n t G → T t = true → Pr G)
    (h : centNormMemOKP p n S base x rels gS M T = true) :
    X ∈ Q.originalSubgroup ∧
      (∀ l < gS.size, permOfArr n gS[l]! ∈ centralizer {X} ⊓ Q.originalSubgroup) ∧
      ∀ g ∈ centralizer {X} ⊓ Q.originalSubgroup,
        (∀ l < gS.size, g * permOfArr n gS[l]! * g⁻¹ ∈ Sg) ∧
        ((∀ l < gS.size, permOfArr n gS[l]! * g = g * permOfArr n gS[l]!) → Pr g) := by
  simp only [centNormMemOKP, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hrels, hgens⟩, hsx⟩, htail⟩ := h
  have hgv : ∀ l < gS.size, validA n gS[l]! = true := fun l hl => by
    have := allLt_spec hgens hl
    simp only [Bool.and_eq_true] at this
    exact this.1.1
  have hXP : X ∈ Q.originalSubgroup := mem_of_siftA hA hc hx hsx
  refine ⟨hXP, fun l hl => ?_, fun g hg => ?_⟩
  · have hrep := rep_of_validA (hgv l hl)
    have := allLt_spec hgens hl
    simp only [Bool.and_eq_true] at this
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · exact (commA_iff hrep hx).1 this.1.2
    · exact mem_of_siftA hA hc hrep this.2
  · have htail' : ptailOKQ n (rawLevels n S base) base x (powPA p n x) rels
        (leafMem n gS M T) Q.baseCount 0 (idA n) = true := by
      rw [← hA.base_size]
      exact htail
    obtain ⟨e, hre, hT'⟩ := centralizer_subset_of_ptailOKQ hA (chainCheckFacts hc)
      (validSchreier_of_chainOK hA (by norm_num) hc).1 hx (rep_powPA hx) (relsOKP_spec hrels)
      htail' hg
    exact leafMem_spec hgv hM hT hre hT'

theorem case_centNormMem2P {p : ℕ} {S : Array (Array ℕ)} (hn : 1 ≤ n) (hk : 2 ≤ S.size)
    {bs : List (Fin n)} (hb : bs.Nodup) {W : Array (List ℤ)} {a b : Array ℕ}
    {A B : Equiv.Perm (Fin n)} (ha : Rep n a A) (hb' : Rep n b B)
    (hchain : caseChainOK2P n S (bs.map Fin.val).toArray W a b = true) {x : Array ℕ}
    {X : Equiv.Perm (Fin n)} (hx : Rep n x X) {rels : List (ℕ × ℕ × ℕ)}
    {gS : Array (Array ℕ)} {M T : Array ℕ → Bool}
    {Sg : Subgroup (Equiv.Perm (Fin n))} {Pr : Equiv.Perm (Fin n) → Prop}
    (hM : ∀ {t : Array ℕ} {G : Equiv.Perm (Fin n)}, Rep n t G → M t = true → G ∈ Sg)
    (hT : ∀ {t : Array ℕ} {G : Equiv.Perm (Fin n)}, Rep n t G → T t = true → Pr G)
    (hcn : centNormMemOKP p n S (bs.map Fin.val).toArray x rels gS M T = true) :
    X ∈ closure {A, B} ∧
      (∀ l < gS.size, permOfArr n gS[l]! ∈ centralizer {X} ⊓ closure {A, B}) ∧
      ∀ g ∈ centralizer {X} ⊓ closure {A, B},
        (∀ l < gS.size, g * permOfArr n gS[l]! * g⁻¹ ∈ Sg) ∧
        ((∀ l < gS.size, permOfArr n gS[l]! * g = g * permOfArr n gS[l]!) → Pr g) := by
  obtain ⟨hc, e0, e1⟩ := caseChainOK2P_parts hchain
  have hA : ChainArrays (RawSchreierDatum.ofArrays n hn S 2 hk bs hb W) (S.extract 0 2) S
      (bs.map Fin.val).toArray W := chainArrays_ofArrays (chainCheckFacts hc).strong_inv
  have horig := originalSubgroup_ofArrays_twoP (hn := hn) (hk := hk) (hb := hb) hc ha hb' e0 e1
  rw [← horig]
  exact centNormMem_of_ptailOKQ hA hc hx hM hT hcn

end Spec

end CFSG.HardMathSupport.Dickson.I271
