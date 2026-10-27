module

public import CFSG.ClassicalInvolution.Q3.TL4D1Out
public import CFSG.ClassicalInvolution.Q3.TL3T20
public import CFSG.ClassicalInvolution.Q3.TL4D1AE3
public import CFSG.ClassicalInvolution.Q3.TL4D1PackB
public import CFSG.ClassicalInvolution.Q3.TL4D1Sub

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

theorem exists_d1Sub (hF : D1Facts) (h : T4Hyp 3 G Δ)
    (hall : ∀ K ∈ Δ, ∀ z : G, IsUniqueInvolution K z → TightInO2 z)
    (hD2 : ThmDAbsBelow 3 (Nat.card G + 1)) {J : Subgroup G} (hJ : J ∈ Δ) {u : G}
    (hu : IsUniqueInvolution J u) (hthin : ∀ x ∈ J, x ∈ pCore 2 G → x = 1 ∨ x = u) :
    ∃ X : Subgroup G, D1Sub J X := by
  have h2 : ∀ K ∈ Δ, IsPGroup 2 K := fun K hK => h.isPGroup_of_all hall hK
  have h8 : ∀ K ∈ Δ, Nat.card K = 8 := fun K hK => h.card_eq_eight hK (h2 K hK)
  obtain ⟨X, hJX, hXs, hspan⟩ := exists_subnormal_closure J
  set P : Set (Subgroup G) := {L | ∃ x ∈ X, conjSub x J = L} with hP
  have hPΔ : P ⊆ Δ := by
    rintro L ⟨x, -, rfl⟩
    exact h.hyp.conjInvariant x J hJ
  have hJP : J ∈ P := ⟨1, X.one_mem, conjSub_one J⟩
  have hPne : P.Nonempty := ⟨J, hJP⟩
  have htrans : ∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L' := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    refine ⟨x' * x⁻¹, hspan ▸ X.mul_mem hx' (X.inv_mem hx), ?_⟩
    rw [← conjSub_mul, inv_mul_cancel_right]
  have hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P := by
    rintro _ ⟨x', hx', rfl⟩ x hx
    rw [hspan] at hx
    exact ⟨x * x', X.mul_mem hx hx', conjSub_mul x x' J⟩
  have hodd : classicalInvolutionOddCore ↥(pSpan P) = ⊥ := by
    rw [hspan]
    exact oddCore_eq_bot_of_isSubnormal h.odd hXs
  have hE2 : ∀ L ∈ P, ∀ u' : G, IsUniqueInvolution L u' → ∃ Q : Subgroup G, Q ≤ pSpan P ∧
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧ u' ∈ Q := by
    intro L hL u' hu'
    refine ⟨pSpan P ⊓ pCore 2 G, inf_le_left, fun x hx q hq => ⟨?_, ?_⟩,
      pCore_isPGroup.to_le inf_le_right,
      ⟨le_pSpan hL hu'.mem, mem_pCore_of_tightInO2 (hall L (hPΔ hL) u' hu')⟩⟩
    · exact (pSpan P).mul_mem ((pSpan P).mul_mem hx hq.1) ((pSpan P).inv_mem hx)
    · exact pCore_normal.conj_mem q hq.2 x
  have hcard : Nat.card ↥(pSpan P) < Nat.card G + 1 :=
    Nat.lt_succ_of_le (Subgroup.card_le_card_group _)
  have hout := thmDGen_at h.hyp h2 (fun K hK => by rw [h8 K hK]; norm_num) h.aEmpty hPΔ
    (hD2 _ hcard) htrans hinv hodd hE2
  have hXs' : (pSpan P).IsSubnormal := hspan ▸ hXs
  have hthinP : ∀ L ∈ P, ∀ u' : G, IsUniqueInvolution L u' → ∀ Q : Subgroup G, Q ≤ pSpan P →
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) → IsPGroup 2 Q → ∀ x ∈ L, x ∈ Q →
        x = 1 ∨ x = u' := by
    rintro _ ⟨g, -, rfl⟩ u' hu' Q hQX hQn hQ2 x hxL hxQ
    have hQs : Q ≤ pCore 2 G := le_pCore_of_isSubnormal hXs' hQX hQn hQ2
    rw [mem_conjSub_iff] at hxL
    have hxc : g⁻¹ * x * g ∈ pCore 2 G := by
      have := pCore_normal.conj_mem x (hQs hxQ) g⁻¹
      simpa using this
    have hu'eq : u' = g * u * g⁻¹ := ((hu.conj g).unique u' hu'.mem hu'.sq).resolve_left hu'.ne_one
    rcases hthin _ hxL hxc with h1 | h1
    · left
      have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      rw [this, h1]
      group
    · right
      have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      rw [this, h1, hu'eq]
  rcases hout with hsing | ⟨W, hW⟩ | ⟨E, hE⟩ | hI64 | ⟨m, hm, hI⟩ | hI29
  · exfalso
    have hXJ : X ≤ J := hspan ▸ pSpan_le fun L hL => (hsing L hL J hJP).le
    have hJs : J.IsSubnormal := (le_antisymm hXJ hJX) ▸ hXs
    have hJQ : J ≤ pCore 2 G := le_pCore_of_isSubnormal hJs le_rfl
      (fun w hw x hx => J.mul_mem (J.mul_mem hw hx) (J.inv_mem hw)) (h2 J hJ)
    obtain ⟨x, hx, hx2⟩ := exists_sq_ne_one hu (h8 J hJ)
    rcases hthin x hx (hJQ hx) with h1 | h1
    · exact hx2 (by rw [h1, one_mul])
    · exact hx2 (by rw [h1]; exact hu.sq)
  · exact (false_of_WIn_eq h.hyp h2 h8 hPΔ hPne hinv hthinP hW).elim
  · rw [hspan] at hE
    exact ⟨X, hJX, hXs, hspan, D1Pack.of_e8 hF.e8Normal hF.e8Perfect hE, Or.inl ⟨E, hE⟩⟩
  · obtain ⟨I⟩ := hI64
    have hpack := D1Pack.of_ident h.hyp h2 h8 hPΔ hinv (by norm_num) I
      (I.toLabel.isPGroup_ker hodd) hF.e64.normal hF.e64.perfect hF.e64.three hPne
    rw [hspan] at hpack
    exact ⟨X, hJX, hXs, hspan, hpack, Or.inr ⟨7, _, _, by norm_num, hF.e64.members, ⟨I⟩⟩⟩
  · obtain ⟨I⟩ := nonempty_aeIdentOn_of_aeIdent hI
    have hpack := D1Pack.of_ident h.hyp h2 h8 hPΔ hinv hm I (I.toLabel.isPGroup_ker hodd)
      (hF.aeNormal m hm) (hF.aePerfect m hm) (aeModelThree m) hPne
    rw [hspan] at hpack
    exact ⟨X, hJX, hXs, hspan, hpack, Or.inr ⟨m, _, _, hm, hF.aeMembers m hm, ⟨I⟩⟩⟩
  · obtain ⟨I⟩ := hI29
    have hpack := D1Pack.of_ident h.hyp h2 h8 hPΔ hinv (by norm_num) I
      (I.toLabel.isPGroup_ker hodd) hF.e29.normal hF.e29.perfect hF.e29.three hPne
    rw [hspan] at hpack
    exact ⟨X, hJX, hXs, hspan, hpack, Or.inr ⟨8, _, _, by norm_num, hF.e29.members, ⟨I⟩⟩⟩

end CFSG.ClassicalInvolution.Q3.TL4
