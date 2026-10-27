module

public import CFSG.ClassicalInvolution.Q3.TL3T64
public import CFSG.ClassicalInvolution.Q3.TL3T54
public import CFSG.ClassicalInvolution.Q3.TL3T61

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {G : Type} [Group G] {P Q : Set (Subgroup G)} {n k : ℕ}

variable [Finite G]

theorem SubHyp.map_pairVec' (hM : Model117At k) (hk : 5 ≤ k) (I : AEIdent Q k)
    {I' : AEIdent P n} {c : Fin k ↪ Fin n} (h : SubHyp I' Q c)
    (hlab : ∀ L ∈ Q, ∀ (α : Finset (Fin k)) (hα : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan Q)).map I.φ = memBar α hα b →
      ∃ (hα' : (α.map c).card = 4) (b' : Bool),
        (L.subgroupOf (pSpan P)).map I'.φ = memBar (α.map c) hα' b')
    {L L' : Subgroup G} (hL : L ∈ Q) (hL' : L' ∈ Q) {γ : Finset (Fin k)} {hγ : γ.card = 4}
    {b b' : Bool} (hlabL : (L.subgroupOf (pSpan Q)).map I.φ = memBar γ hγ b)
    (hlabL' : (L'.subgroupOf (pSpan Q)).map I.φ = memBar γ hγ b')
    {l l' : G} (hl : l ∈ L) (hl' : l' ∈ L') {a e : Fin k} (ha : a ∈ γ) (he : e ∈ γ)
    (hI : I.φ ⟨l * l', mul_mem (le_pSpan hL hl) (le_pSpan hL' hl')⟩ =
      mkQ k (ofVec (TL4.pairVec a e))) :
    I'.φ ⟨l * l', h.span_le (mul_mem (le_pSpan hL hl) (le_pSpan hL' hl'))⟩ =
      mkQ n (ofVec (TL4.pairVec (c a) (c e))) := by
  classical
  obtain ⟨v, hv⟩ := h.exists_vec hM hk I hlab
  set y : ↥(pSpan Q) := ⟨l * l', mul_mem (le_pSpan hL hl) (le_pSpan hL' hl')⟩ with hy
  have hcomm : ofVec v * ofVec (TL4.pairVec a e) * (ofVec v)⁻¹ = ofVec (TL4.pairVec a e) := by
    rw [TL4.ofVec_mul_ofVec, add_comm, ← TL4.ofVec_mul_ofVec, mul_inv_cancel_right]
  have hJy : mkQ k (h.pre y) = mkQ k (ofVec (TL4.pairVec a e)) := by
    rw [← AEIdent.restrict_apply I' hk h y, hv y, hI, ← map_mul, ← map_inv, ← map_mul, hcomm]
  have hsupp : ∀ {M : Subgroup G} (hM : M ∈ Q) {b₀ : Bool},
      (M.subgroupOf (pSpan Q)).map I.φ = memBar γ hγ b₀ → ∀ {m : G} (hm : m ∈ M),
      SupportedOn (h.pre ⟨m, le_pSpan hM hm⟩) (Set.range (emb γ hγ)) := by
    intro M hM b₀ hlM m hm
    obtain ⟨hγ', b₁, hl₁⟩ := hlab M hM γ hγ b₀ hlM
    obtain ⟨b₂, hb₂⟩ := exists_memBar_map_eq c γ hγ hγ' b₁
    have hmap := h.map_pre hM hγ hγ' hl₁ hb₂
    have hmem : h.pre ⟨m, le_pSpan hM hm⟩ ∈ memAt γ hγ b₂ := by
      rw [← hmap]
      exact ⟨⟨m, le_pSpan hM hm⟩, Subgroup.mem_subgroupOf.mpr hm, rfl⟩
    exact supportedOn_of_mem_memAt hmem
  have hpre : h.pre y = h.pre ⟨l, le_pSpan hL hl⟩ * h.pre ⟨l', le_pSpan hL' hl'⟩ := by
    rw [← map_mul]
    rfl
  have hS : SupportedOn (h.pre y) (Set.range (emb γ hγ)) := by
    rw [hpre]
    exact (hsupp hL hlabL hl).mul (hsupp hL' hlabL' hl')
  rw [range_emb] at hS
  have hpv : h.pre y = ofVec (TL4.pairVec a e) := by
    rcases mkQ_eq_iff.mp hJy with h1 | h1
    · exact inv_mul_eq_one.mp h1
    · exfalso
      have h2 : ofVec (TL4.pairVec a e) = h.pre y * allOnes k := inv_mul_eq_iff_eq_mul.mp h1
      obtain ⟨x, hx⟩ := AE.Block4.exists_not_mem (s := γ) (by omega)
      have hxa : x ≠ a := fun h' => hx (by rw [h']; exact ha)
      have hxe : x ≠ e := fun h' => hx (by rw [h']; exact he)
      have hxγ : x ∉ (γ : Set (Fin k)) := fun h' => hx (Finset.mem_coe.mp h')
      have e1 := congrFun (congrArg Wr.vec h2) x
      have e2 : (h.pre y * allOnes k).vec x = (h.pre y).vec x + 1 := rfl
      rw [e2, (hS x hxγ).1] at e1
      change TL4.pairVec a e x = 0 + 1 at e1
      simp only [TL4.pairVec_apply, hxa, hxe, ↓reduceIte] at e1
      exact absurd e1 (by decide)
  have e := AEIdent.subQ_pre h y
  rw [hpv, subQ_apply, embW_ofVec, embWVec_pairVec] at e
  exact e.symm

end CFSG.ClassicalInvolution.Q3.TC.Thin
