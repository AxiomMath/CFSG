module

public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecDiag
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Sec
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Inner2

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup CFSG.ComponentClassification.GSThmB
  CFSG.ComponentClassification.UnbalancedLayer

structure Config (H : Type) [Group H] [Finite H] where
  a : H
  b : H
  J : Subgroup H
  K : Subgroup H
  simple : IsSimpleGroup ↥(generalizedFitting H)
  centralizer_eq_bot : centralizer (generalizedFitting H : Set H) = ⊥
  orderOf_a : orderOf a = 2
  orderOf_b : orderOf b = 2
  mul_comm_ab : a * b = b * a
  b_mem_K : b ∈ K
  K_le_G : K ≤ generalizedFitting H
  J_le_G : J ≤ generalizedFitting H
  K_le : K ≤ centralizer ({b} : Set H)
  isPComponent_K : IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set H)))
  conjugate_ne : conjugate K a ≠ K
  layer : ∀ M : Subgroup H, M ≤ centralizer ({b} : Set H) →
    IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set H))) → M = K ∨ M = conjugate K a
  card_center : Nat.card (center (K ⧸ pPrimeCore 2 K)) = 2
  sylow : ∀ T : Subgroup H, IsPGroup 2 T →
    T ≤ centralizer ({b} : Set H) ⊓ coreActionKernel (K ⊔ conjugate K a) → Nat.card T ≤ 2
  J_le : J ≤ centralizer ({a} : Set H)
  isPComponent_J : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set H)))
  b_mem_kernel : b ∈ coreActionKernel J
  type_J : (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 7) ∧
      Nonempty (J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n))) ∨
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
      Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f
  quotient_J_K : Nonempty (J ⧸ pPrimeCore 2 J ≃* K ⧸ Open.fusionZStar K)

namespace Config

variable {H : Type} [Group H] [Finite H]

theorem card_le_of_sylow {Y B T : Subgroup H} (hBY : B ≤ Y)
    (hB : ∃ R : Sylow 2 ↥Y, (R : Subgroup _) = B.subgroupOf Y) (hT : IsPGroup 2 T)
    (hTY : T ≤ Y) : Nat.card T ≤ Nat.card B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := hB
  have hT' : IsPGroup 2 (T.subgroupOf Y) := hT.comap_subtype
  obtain ⟨Q, hQ⟩ := hT'.exists_le_sylow
  have hRQ : Nat.card Q = Nat.card R := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  calc Nat.card T = Nat.card (T.subgroupOf Y) :=
        (Nat.card_congr (subgroupOfEquivOfLe hTY).toEquiv).symm
    _ ≤ Nat.card Q := Subgroup.card_le_of_le hQ
    _ = Nat.card R := hRQ
    _ = Nat.card B := by
        rw [hR]
        exact Nat.card_congr (subgroupOfEquivOfLe hBY).toEquiv

theorem exists_ofHyp59 (h : Hyp59 H) (hB : Nat.card h.B = 2) (hKa : conjugate h.K h.a ≠ h.K)
    (hZK : Nat.card (center (h.K ⧸ pPrimeCore 2 h.K)) = 2)
    (hJ : (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 7) ∧
        Nonempty (h.J ⧸ pPrimeCore 2 h.J ≃* alternatingGroup (Fin n))) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p f) :
    ∃ c : Config H, c.J = h.J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb, hBb, hbK⟩ := h.exists_b_mem_K hB hKa hZK
  have hWb : normalizer (h.B : Set H) = centralizer ({b} : Set H) := by
    rw [hBb]
    exact UnbalancedCorr.normalizer_zpowers_eq_centralizer hb
  have hCb : centralizer (h.B : Set H) = centralizer ({b} : Set H) := by
    rw [hBb]
    exact centralizer_zpowers_eq b
  obtain ⟨hF, hsimple, hC, hcomp, huniq⟩ := h.generalizedFitting_simple
  have hLG : pLayer H 2 = generalizedFitting H := by
    rw [ClassicalInvolution.LBalanceProof.pLayer_eq_layer_of_pPrimeCore_eq_bot h.oddCore_eq_bot,
      hF]
    exact le_antisymm (sSup_le fun L hL => (huniq L hL).le) (le_sSup hcomp)
  have hJG : h.J ≤ generalizedFitting H := hF ▸ B5a.le_conjClosure _ _
  have hVG : h.V ≤ generalizedFitting H := hLG ▸ B5a.V_le_pLayer h.toHyp52
  have hbB : b ∈ h.B := hBb ▸ mem_zpowers b
  have hbS : b ∈ h.S := (h.B_le hbB).1
  have hab : h.a * b = b * h.a :=
    (mem_centralizer_singleton_iff.mp (mem_inf.mp (h.S_le hbS)).1).symm
  have haW : h.a ∈ centralizer ({b} : Set H) := mem_centralizer_singleton_iff.mpr hab
  obtain ⟨hKW, hKpc⟩ := h.isPComponent_K
  rw [hWb] at hKW hKpc
  have hKaW := UnbalancedCorr.conjugate_le_of_mem hKW haW
  have hKapc := UnbalancedCorr.isPComponent_conjugate_subgroupOf haW hKpc
  have hlayer : h.K ⊔ conjugate h.K h.a = layerIn (centralizer ({b} : Set H)) := by
    rw [← hWb]
    exact h.layer_eq_K
  have hV : h.V = h.K ⊔ conjugate h.K h.a := by
    rw [hlayer]
    show layerIn (normalizer (h.B : Set H)) = _
    rw [hWb]
  have ha2 : h.a * h.a = 1 := by rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
  obtain ⟨eJ, -⟩ := CatFactsL4U4.exists_oddBar_JB_equiv h.toHyp52
  have hJBa : GSLit.fixedLayer h.J h.B ≤ centralizer ({h.a} : Set H) :=
    (GSLit.fixedLayer_le_inf h.J h.B).trans (inf_le_left.trans h.J_le)
  have hJBpc := B5a.isPComponent_fixedLayer h.toHyp52
  rw [hCb] at hJBpc
  obtain ⟨eK⟩ := nonempty_quotient_equiv_of_diag_in ha2 hb hab hKW hKpc hKa hbK hZK
    ((B5a.fixedLayer_le_V h.toHyp52).trans hV.le) hJBa hJBpc
  refine ⟨{
    a := h.a
    b := b
    J := h.J
    K := h.K
    simple := hsimple
    centralizer_eq_bot := by rw [hF]; exact hC
    orderOf_a := h.orderOf_a
    orderOf_b := hb
    mul_comm_ab := hab
    b_mem_K := hbK
    K_le_G := (le_sup_left.trans hV.symm.le).trans hVG
    J_le_G := hJG
    K_le := hKW
    isPComponent_K := hKpc
    conjugate_ne := hKa
    layer := fun M hMW hMpc => by
      have hMle : M ≤ h.K ⊔ conjugate h.K h.a := by
        rw [hlayer]
        have h1 : M.subgroupOf (centralizer ({b} : Set H)) ≤
            pLayer ↥(centralizer ({b} : Set H)) 2 := le_sSup hMpc
        have h2 := map_mono (f := (centralizer ({b} : Set H)).subtype) h1
        rwa [map_subgroupOf_eq_of_le hMW] at h2
      exact GSLit.eq_or_eq_of_le_sup hMW hMpc hKW hKpc hKaW hKapc hMle
    card_center := hZK
    sylow := fun T hT hTle => by
      have hY := h.B_sylow_kernel
      have hBY := h.B_le_kernel
      rw [hWb] at hY hBY
      rw [← hlayer] at hY hBY
      exact hB ▸ card_le_of_sylow hBY hY hT hTle
    J_le := h.J_le
    isPComponent_J := h.isPComponent_J
    b_mem_kernel := h.toHyp52.B_le_coreActionKernel hbB
    type_J := hJ
    quotient_J_K := ⟨eJ.symm.trans eK⟩ }, rfl⟩

end Config

end CFSG.ComponentClassification.Sp4Rec
