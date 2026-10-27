module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFSec
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFStmts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFNum
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFSeries
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFNC

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.Quasithin Subgroup

variable {V : Type} [CommGroup V] [Finite V]

theorem chief_numerics (hC : U4FFNatural) (hBN : PartBNStmt) (hBO : PartBOStmt)
    (hBO4 : PartBO4Stmt) (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} {L A : Subgroup (MulAut V)}
    (h : U4OffenderData n L A) {Z' Z : Subgroup V} (hch : IsXChief L A Z' Z)
    (hnc : ¬ LTrivOn L Z' Z) (hZD : Z ≤ fixV (cenD L A)) :
    ∃ e : ℕ, ((e = 1 ∧ NatN n (autSec L Z Z')) ∨ (e = 2 ∧ NatO n (autSec L Z Z'))) ∧
      (cenD L A).relIndex A * Nat.card (fixV (autSec A Z Z')) ≤ e * Nat.card (Sec Z Z') ∧
      2 * Nat.card (fixV (autSec A Z Z')) ≤ Nat.card (Sec Z Z') ∧
      (e = 2 → (cenD L A).relIndex A = 4 →
        Nat.card (Sec Z Z') = 2 * Nat.card (fixV (autSec A Z Z')) → False) := by
  obtain ⟨hirr, hnat⟩ := thmC_sec hC hV h hch hnc hZD
  obtain ⟨hZ', hZ, hlt, hmax⟩ := hch
  have hZ'Z : Z' ≤ Z := hlt.le
  have hsq := sec_sq_eq_one hV Z' Z
  have hAel := isElemAbelian2_autSec h.elemAbelian hZ.2 hZ'.2
  have hAnorm := autSec_normalizes h.normalizes hZ hZ'
  have h1n : 1 ≤ n := IsU4Group.one_le h.isU4
  have ha : (cenD L A).relIndex A ≤ Nat.card (autSec A Z Z') :=
    relIndex_cenD_le_card_autSec h hZ'Z hZ hZ' hnc
  have hgpos : 0 < Nat.card (fixV (autSec A Z Z')) := Nat.card_pos
  have h2g : 2 * Nat.card (fixV (autSec A Z Z')) ≤ Nat.card (Sec Z Z') := by
    obtain ⟨a', ha', l', hl', hne⟩ :=
      exists_noncomm_autSec h.simple h.normalizes hZ'Z hZ hZ' hnc h.noncomm
    have hne1 : a' ≠ 1 := fun h1 => hne (by rw [h1]; simp)
    obtain ⟨s, hs⟩ : ∃ s, a' s ≠ s := by
      by_contra hcon
      push Not at hcon
      exact hne1 (MulEquiv.ext fun x => by rw [hcon x]; rfl)
    have hne_top : fixV (autSec A Z Z') ≠ ⊤ := fun htop => hs (by
      have : s ∈ fixV (autSec A Z Z') := by rw [htop]; exact Subgroup.mem_top _
      exact this a' ha')
    have hidx : (fixV (autSec A Z Z')).index ≠ 1 := fun h1 => hne_top (Subgroup.index_eq_one.mp h1)
    have hidx0 : (fixV (autSec A Z Z')).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hcard := Subgroup.card_mul_index (fixV (autSec A Z Z'))
    have h2 : 2 ≤ (fixV (autSec A Z Z')).index := by omega
    calc 2 * Nat.card (fixV (autSec A Z Z'))
        = Nat.card (fixV (autSec A Z Z')) * 2 := by ring
      _ ≤ Nat.card (fixV (autSec A Z Z')) * (fixV (autSec A Z Z')).index :=
          Nat.mul_le_mul_left _ h2
      _ = Nat.card (Sec Z Z') := hcard
  rcases hnat with ⟨F, _, _, hF, ε, ψ, hψ⟩ | ⟨F, _, _, b, c, hF, hirrQ, ε, ψ, hψ⟩
  · have hB := hBN hsq h1n hF ε ψ hψ hAel hAnorm
    refine ⟨1, Or.inl ⟨rfl, F, inferInstance, inferInstance, hF, ε, ψ, hψ⟩, ?_, h2g,
      fun h2' => absurd h2' (by norm_num)⟩
    calc (cenD L A).relIndex A * Nat.card (fixV (autSec A Z Z'))
        ≤ Nat.card (autSec A Z Z') * Nat.card (fixV (autSec A Z Z')) :=
          Nat.mul_le_mul_right _ ha
      _ ≤ Nat.card (Sec Z Z') := hB
      _ = 1 * Nat.card (Sec Z Z') := (one_mul _).symm
  · have hB := hBO hsq h1n hF hirrQ ε ψ hψ hAel hAnorm
    refine ⟨2, Or.inr ⟨rfl, F, inferInstance, inferInstance, b, c, hF, hirrQ, ε, ψ, hψ⟩, ?_, h2g,
      ?_⟩
    · calc (cenD L A).relIndex A * Nat.card (fixV (autSec A Z Z'))
          ≤ Nat.card (autSec A Z Z') * Nat.card (fixV (autSec A Z Z')) :=
            Nat.mul_le_mul_right _ ha
        _ ≤ 2 * Nat.card (Sec Z Z') := hB
    · intro _ ha4 hs2
      have hle4 : Nat.card (autSec A Z Z') ≤ 4 := by
        have : Nat.card (autSec A Z Z') * Nat.card (fixV (autSec A Z Z')) ≤
            4 * Nat.card (fixV (autSec A Z Z')) := by
          calc Nat.card (autSec A Z Z') * Nat.card (fixV (autSec A Z Z'))
              ≤ 2 * Nat.card (Sec Z Z') := hB
            _ = 4 * Nat.card (fixV (autSec A Z Z')) := by rw [hs2]; ring
        exact Nat.le_of_mul_le_mul_right this hgpos
      have hge4 : 4 ≤ Nat.card (autSec A Z Z') := ha4 ▸ ha
      exact hBO4 hsq h1n hF hirrQ ε ψ hψ hAel hAnorm ⟨le_antisymm hle4 hge4, hs2⟩

theorem card_fixV_autSec_le {A : Subgroup (MulAut V)} (W U : Subgroup V) :
    Nat.card (fixV (autSec A W U)) ≤ Nat.card (Sec W U) :=
  Subgroup.card_le_card_group _

theorem single_numerics {A : Subgroup (MulAut V)} {Y M₁ M₀ : Subgroup V} (hYM : M₁ ≤ Y)
    (hMM : M₀ ≤ M₁) (hAY : A ≤ stabSub Y) (hAM₁ : A ≤ stabSub M₁) {a e : ℕ}
    (hB : a * Nat.card (fixV (autSec A M₁ M₀)) ≤ e * Nat.card (Sec M₁ M₀)) :
    a * Nat.card ↥(Y ⊓ fixV A) ≤ e * Nat.card Y := by
  have h1 := card_inf_fixV_le_autSec (A := A) hYM hAY
  have h2 := card_inf_fixV_le_autSec (A := A) hMM hAM₁
  have h3 : Nat.card ↥(M₀ ⊓ fixV A) ≤ Nat.card M₀ := Subgroup.card_le_of_le inf_le_left
  have h4 : Nat.card (fixV (autSec A Y M₁)) ≤ Nat.card (Sec Y M₁) := card_fixV_autSec_le Y M₁
  have h5 := card_sec_mul hYM
  have h6 := card_sec_mul hMM
  calc a * Nat.card ↥(Y ⊓ fixV A)
      ≤ a * (Nat.card (fixV (autSec A Y M₁)) * Nat.card ↥(M₁ ⊓ fixV A)) :=
        Nat.mul_le_mul_left _ h1
    _ ≤ a * (Nat.card (fixV (autSec A Y M₁)) *
          (Nat.card (fixV (autSec A M₁ M₀)) * Nat.card ↥(M₀ ⊓ fixV A))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
    _ ≤ a * (Nat.card (fixV (autSec A Y M₁)) *
          (Nat.card (fixV (autSec A M₁ M₀)) * Nat.card M₀)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3))
    _ = Nat.card (fixV (autSec A Y M₁)) *
          ((a * Nat.card (fixV (autSec A M₁ M₀))) * Nat.card M₀) := by ring
    _ ≤ Nat.card (fixV (autSec A Y M₁)) * ((e * Nat.card (Sec M₁ M₀)) * Nat.card M₀) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hB)
    _ ≤ Nat.card (Sec Y M₁) * ((e * Nat.card (Sec M₁ M₀)) * Nat.card M₀) :=
        Nat.mul_le_mul_right _ h4
    _ = e * (Nat.card (Sec Y M₁) * (Nat.card (Sec M₁ M₀) * Nat.card M₀)) := by ring
    _ = e * (Nat.card (Sec Y M₁) * Nat.card M₁) := by rw [h6]
    _ = e * Nat.card Y := by rw [h5]

theorem chain_numerics {A : Subgroup (MulAut V)} {Y Z₁ Z₀ M₁ M₀ : Subgroup V}
    (hYZ : Z₁ ≤ Y) (hZZ : Z₀ ≤ Z₁) (hZM : M₁ ≤ Z₀) (hMM : M₀ ≤ M₁)
    (hAY : A ≤ stabSub Y) (hAZ₁ : A ≤ stabSub Z₁) (hAZ₀ : A ≤ stabSub Z₀)
    (hAM₁ : A ≤ stabSub M₁) {a : ℕ} (hY : Nat.card Y ≤ a * Nat.card ↥(Y ⊓ fixV A)) :
    Nat.card (Sec M₁ M₀) * Nat.card (Sec Z₁ Z₀) ≤
      a * (Nat.card (fixV (autSec A M₁ M₀)) * Nat.card (fixV (autSec A Z₁ Z₀))) := by
  have h1 := card_inf_fixV_le_autSec (A := A) hYZ hAY
  have h2 := card_inf_fixV_le_autSec (A := A) hZZ hAZ₁
  have h3 := card_inf_fixV_le_autSec (A := A) hZM hAZ₀
  have h4 := card_inf_fixV_le_autSec (A := A) hMM hAM₁
  have h5 : Nat.card ↥(M₀ ⊓ fixV A) ≤ Nat.card M₀ := Subgroup.card_le_of_le inf_le_left
  have hy1 := card_fixV_autSec_le (A := A) Y Z₁
  have hy2 := card_fixV_autSec_le (A := A) Z₀ M₁
  have e1 := card_sec_mul hYZ
  have e2 := card_sec_mul hZZ
  have e3 := card_sec_mul hZM
  have e4 := card_sec_mul hMM
  set P := Nat.card (Sec Y Z₁) * Nat.card (Sec Z₀ M₁) with hP
  set Q := Nat.card (fixV (autSec A Y Z₁)) * Nat.card (fixV (autSec A Z₀ M₁)) with hQ
  have hQP : Q ≤ P := Nat.mul_le_mul hy1 hy2
  have hPpos : 0 < P := Nat.mul_pos Nat.card_pos Nat.card_pos
  have hmpos : 0 < Nat.card M₀ := Nat.card_pos
  have hYcard : Nat.card Y = P * (Nat.card (Sec Z₁ Z₀) * (Nat.card (Sec M₁ M₀) * Nat.card M₀)) := by
    rw [← e1, ← e2, ← e3, ← e4]
    simp only [hP]
    ring
  have hcY : Nat.card ↥(Y ⊓ fixV A) ≤
      Q * (Nat.card (fixV (autSec A Z₁ Z₀)) * (Nat.card (fixV (autSec A M₁ M₀)) *
        Nat.card M₀)) := by
    calc Nat.card ↥(Y ⊓ fixV A)
        ≤ Nat.card (fixV (autSec A Y Z₁)) * Nat.card ↥(Z₁ ⊓ fixV A) := h1
      _ ≤ Nat.card (fixV (autSec A Y Z₁)) * (Nat.card (fixV (autSec A Z₁ Z₀)) *
            Nat.card ↥(Z₀ ⊓ fixV A)) := Nat.mul_le_mul_left _ h2
      _ ≤ Nat.card (fixV (autSec A Y Z₁)) * (Nat.card (fixV (autSec A Z₁ Z₀)) *
            (Nat.card (fixV (autSec A Z₀ M₁)) * Nat.card ↥(M₁ ⊓ fixV A))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
      _ ≤ Nat.card (fixV (autSec A Y Z₁)) * (Nat.card (fixV (autSec A Z₁ Z₀)) *
            (Nat.card (fixV (autSec A Z₀ M₁)) * (Nat.card (fixV (autSec A M₁ M₀)) *
              Nat.card ↥(M₀ ⊓ fixV A)))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h4))
      _ ≤ Nat.card (fixV (autSec A Y Z₁)) * (Nat.card (fixV (autSec A Z₁ Z₀)) *
            (Nat.card (fixV (autSec A Z₀ M₁)) * (Nat.card (fixV (autSec A M₁ M₀)) *
              Nat.card M₀))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
            (Nat.mul_le_mul_left _ h5)))
      _ = Q * (Nat.card (fixV (autSec A Z₁ Z₀)) * (Nat.card (fixV (autSec A M₁ M₀)) *
            Nat.card M₀)) := by simp only [hQ]; ring
  have key : P * (Nat.card (Sec Z₁ Z₀) * (Nat.card (Sec M₁ M₀) * Nat.card M₀)) ≤
      P * (a * (Nat.card (fixV (autSec A Z₁ Z₀)) * (Nat.card (fixV (autSec A M₁ M₀)) *
        Nat.card M₀))) := by
    calc P * (Nat.card (Sec Z₁ Z₀) * (Nat.card (Sec M₁ M₀) * Nat.card M₀))
        = Nat.card Y := hYcard.symm
      _ ≤ a * Nat.card ↥(Y ⊓ fixV A) := hY
      _ ≤ a * (Q * (Nat.card (fixV (autSec A Z₁ Z₀)) * (Nat.card (fixV (autSec A M₁ M₀)) *
            Nat.card M₀))) := Nat.mul_le_mul_left _ hcY
      _ ≤ a * (P * (Nat.card (fixV (autSec A Z₁ Z₀)) * (Nat.card (fixV (autSec A M₁ M₀)) *
            Nat.card M₀))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hQP)
      _ = P * (a * (Nat.card (fixV (autSec A Z₁ Z₀)) * (Nat.card (fixV (autSec A M₁ M₀)) *
            Nat.card M₀))) := by ring
  have key2 := Nat.le_of_mul_le_mul_left key hPpos
  have key3 : (Nat.card (Sec Z₁ Z₀) * Nat.card (Sec M₁ M₀)) * Nat.card M₀ ≤
      (a * (Nat.card (fixV (autSec A Z₁ Z₀)) * Nat.card (fixV (autSec A M₁ M₀)))) *
        Nat.card M₀ := by
    calc (Nat.card (Sec Z₁ Z₀) * Nat.card (Sec M₁ M₀)) * Nat.card M₀
        = Nat.card (Sec Z₁ Z₀) * (Nat.card (Sec M₁ M₀) * Nat.card M₀) := by ring
      _ ≤ a * (Nat.card (fixV (autSec A Z₁ Z₀)) * (Nat.card (fixV (autSec A M₁ M₀)) *
            Nat.card M₀)) := key2
      _ = (a * (Nat.card (fixV (autSec A Z₁ Z₀)) * Nat.card (fixV (autSec A M₁ M₀)))) *
            Nat.card M₀ := by ring
  have key4 := Nat.le_of_mul_le_mul_right key3 hmpos
  calc Nat.card (Sec M₁ M₀) * Nat.card (Sec Z₁ Z₀)
      = Nat.card (Sec Z₁ Z₀) * Nat.card (Sec M₁ M₀) := by ring
    _ ≤ a * (Nat.card (fixV (autSec A Z₁ Z₀)) * Nat.card (fixV (autSec A M₁ M₀))) := key4
    _ = a * (Nat.card (fixV (autSec A M₁ M₀)) * Nat.card (fixV (autSec A Z₁ Z₀))) := by ring

theorem xInv_Y {n : ℕ} {L A : Subgroup (MulAut V)} (h : U4OffenderData n L A) :
    XInv L A (commV L ⊓ fixV (cenD L A)) :=
  (xInv_commV h.normalizes).inf (xInv_fixV_cenD h.comm)

theorem relIndex_cenD_pos (L A : Subgroup (MulAut V)) : 0 < (cenD L A).relIndex A := by
  have h := Subgroup.relIndex_mul_card (cenD L A) A
  rw [inf_eq_left.mpr (cenD_le L A)] at h
  refine Nat.pos_of_ne_zero fun h0 => ?_
  rw [h0, zero_mul] at h
  exact (Nat.card_pos (α := ↥A)).ne' h.symm

theorem eq_one_or_two_of {e : ℕ} {P Q : Prop} (he : (e = 1 ∧ P) ∨ (e = 2 ∧ Q)) :
    e = 1 ∨ e = 2 := he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

theorem ltrivOn_top_of_chief (hC : U4FFNatural) (hBN : PartBNStmt) (hBO : PartBOStmt)
    (hBO4 : PartBO4Stmt) (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} {L A : Subgroup (MulAut V)}
    (h : U4OffenderData n L A) {M₀ M₁ : Subgroup V} (hch : IsXChief L A M₀ M₁)
    (hnc : ¬ LTrivOn L M₀ M₁) (hY : M₁ ≤ commV L ⊓ fixV (cenD L A)) :
    LTrivOn L M₁ (commV L ⊓ fixV (cenD L A)) := by
  by_contra hcon
  have hYinv := xInv_Y h
  have hYD : commV L ⊓ fixV (cenD L A) ≤ fixV (cenD L A) := inf_le_right
  obtain ⟨Z₀, Z₁, hZ₀, hZ₁, hMZ₀, hlt, hZ₁Y, hmax, hnc₂, -⟩ :=
    exists_noncentral_chief h.perfect h.normalizes hch.2.1 hYinv hY hcon
  obtain ⟨e₁, he₁, hB₁, hC₁, hX₁⟩ :=
    chief_numerics hC hBN hBO hBO4 hV h hch hnc (hY.trans hYD)
  obtain ⟨e₂, he₂, hB₂, hC₂, -⟩ :=
    chief_numerics hC hBN hBO hBO4 hV h ⟨hZ₀, hZ₁, hlt, hmax⟩ hnc₂ (hZ₁Y.trans hYD)
  have hoff := card_le_relIndex_cenD_mul h hYinv hYD
  have hchain := chain_numerics hZ₁Y hlt.le hMZ₀ hch.2.2.1.le hYinv.2 hZ₁.2 hZ₀.2 hch.2.1.2 hoff
  have hfin := two_factor_numerics (relIndex_cenD_pos L A) (eq_one_or_two_of he₁)
    (eq_one_or_two_of he₂) Nat.card_pos Nat.card_pos hB₁ hB₂ hC₁ hC₂ hchain
  exact hX₁ hfin.2.1 hfin.1 hfin.2.2.2.1

theorem prop51 {n : ℕ} {L A : Subgroup (MulAut V)} (h : U4OffenderData n L A)
    {M₀ M₁ : Subgroup V} (hM₀₁ : M₀ ≤ M₁) (hM₁Y : M₁ ≤ commV L ⊓ fixV (cenD L A))
    (hAM₁ : A ≤ stabSub M₁) {e : ℕ}
    (hB : (cenD L A).relIndex A * Nat.card (fixV (autSec A M₁ M₀)) ≤ e * Nat.card (Sec M₁ M₀)) :
    Nat.card (commV L) ≤
      e * Nat.card (autSub (cenD L A) (commV L)) * Nat.card ↥(commV L ⊓ fixV (cenD L A)) := by
  have hUinv := xInv_commV h.normalizes
  have hAU : A ≤ stabSub (commV L) := hUinv.2
  have hDA : cenD L A ≤ A := cenD_le L A
  have hoff := h.offender (commV L) hAU
  have hCD : A ⊓ centSub (commV L) ≤ cenD L A :=
    (inf_le_inf_left A (centSub_le_centSec (commV L) ⊥)).trans
      (inf_centSec_le_cenD h.simple h.normalizes bot_le hUinv.1 (XInv.bot L A).1
        h.not_ltriv_commV)
  have hDs : cenD L A ≤ stabSub (commV L) := hDA.trans hAU
  have hc1 : cenD L A ⊓ centSub (commV L) = A ⊓ centSub (commV L) :=
    le_antisymm (inf_le_inf_right _ hDA) (le_inf hCD inf_le_right)
  have hc2 : (A ⊓ centSub (commV L)) ⊓ cenD L A = A ⊓ centSub (commV L) := inf_eq_left.mpr hCD
  have hrelD : (A ⊓ centSub (commV L)).relIndex (cenD L A) =
      Nat.card (autSub (cenD L A) (commV L)) := by
    have e1 := card_autSub_mul hDs
    have e2 := Subgroup.relIndex_mul_card (A ⊓ centSub (commV L)) (cenD L A)
    rw [hc1] at e1
    rw [hc2] at e2
    have hpos : 0 < Nat.card ↥(A ⊓ centSub (commV L)) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (e2.trans e1.symm)
  have hrel : (A ⊓ centSub (commV L)).relIndex A =
      Nat.card (autSub (cenD L A) (commV L)) * (cenD L A).relIndex A := by
    rw [← hrelD]
    exact (Subgroup.relIndex_mul_relIndex _ _ _ hCD hDA).symm
  rw [hrel] at hoff
  have hfixA : commV L ⊓ fixV A ≤ commV L ⊓ fixV (cenD L A) :=
    inf_le_inf_left _ (B1.fixV_le_fixV hDA)
  have hcard : Nat.card ↥(commV L ⊓ fixV A) ≤ Nat.card ↥(commV L ⊓ fixV (cenD L A) ⊓ fixV A) := by
    apply Subgroup.card_le_of_le
    exact le_inf hfixA inf_le_right
  have hsingle := single_numerics (A := A) hM₁Y hM₀₁ (xInv_Y h).2 hAM₁ hB
  calc Nat.card (commV L)
      ≤ Nat.card (autSub (cenD L A) (commV L)) * (cenD L A).relIndex A *
          Nat.card ↥(commV L ⊓ fixV A) := hoff
    _ ≤ Nat.card (autSub (cenD L A) (commV L)) * (cenD L A).relIndex A *
          Nat.card ↥(commV L ⊓ fixV (cenD L A) ⊓ fixV A) := Nat.mul_le_mul_left _ hcard
    _ = Nat.card (autSub (cenD L A) (commV L)) *
          ((cenD L A).relIndex A * Nat.card ↥(commV L ⊓ fixV (cenD L A) ⊓ fixV A)) := by ring
    _ ≤ Nat.card (autSub (cenD L A) (commV L)) *
          (e * Nat.card ↥(commV L ⊓ fixV (cenD L A))) := Nat.mul_le_mul_left _ hsingle
    _ = e * Nat.card (autSub (cenD L A) (commV L)) *
          Nat.card ↥(commV L ⊓ fixV (cenD L A)) := by ring

theorem not_ltrivOn_Y {n : ℕ} {L A : Subgroup (MulAut V)} (h : U4OffenderData n L A)
    (hV : ∀ v : V, v ^ 2 = 1) : ¬ LTrivOn L ⊥ (commV L ⊓ fixV (cenD L A)) := by
  intro hY
  have hD2 : ∀ d ∈ cenD L A, d * d = 1 := fun d hd => h.sq d (cenD_le L A hd)
  have hDc : ∀ d ∈ cenD L A, ∀ e ∈ cenD L A, d * e = e * d := fun d hd e he =>
    h.comm d (cenD_le L A hd) e (cenD_le L A he)
  have hUL : ∀ g ∈ L, ∀ u ∈ commV L, g u ∈ commV L := fun g hg u hu =>
    (commV_stab (le_normalizer_self L hg) u).2 hu
  have hUD : ∀ d ∈ cenD L A, ∀ u ∈ commV L, d u ∈ commV L := fun d hd u hu =>
    (commV_stab (h.normalizes (cenD_le L A hd)) u).2 hu
  have hSL : ∀ j, ∀ g ∈ L, ∀ x ∈ socleSeries (cenD L A) j, g x ∈ socleSeries (cenD L A) j :=
    fun j g hg x hx => (mem_stabSub_socleSeries (fun d hd => cenD_comm hd hg) j x).2 hx
  have hYL : ∀ j, ∀ g ∈ L, ∀ x ∈ commV L ⊓ socleSeries (cenD L A) j,
      g x ∈ commV L ⊓ socleSeries (cenD L A) j := fun j g hg x hx =>
    ⟨hUL g hg x hx.1, hSL j g hg x hx.2⟩
  have key : ∀ j, LTrivOn L ⊥ (commV L ⊓ socleSeries (cenD L A) (j + 1)) := by
    intro j
    induction j with
    | zero =>
      rw [zero_add, socleSeries_one]
      exact hY
    | succ j ih =>
      refine flag_trivial h.perfect (W₀ := ⊥)
        (W₁ := commV L ⊓ socleSeries (cenD L A) (j + 1))
        (M := commV L ⊓ socleSeries (cenD L A) (j + 1 + 1)) (hYL _) ?_ ?_ ih
      · intro g hg w hw
        rw [Subgroup.mem_bot] at hw ⊢
        simp [hw]
      · intro g hg x hx
        refine ⟨(commV L).mul_mem (hUL g hg x hx.1) ((commV L).inv_mem hx.1), ?_⟩
        refine mem_socleSeries_succ.mpr ?_
        intro d hd
        have hdx : d x * x⁻¹ ∈ commV L ⊓ socleSeries (cenD L A) (j + 1) :=
          ⟨(commV L).mul_mem (hUD d hd x hx.1) ((commV L).inv_mem hx.1), hx.2 d hd⟩
        have h1 := ih g hg _ hdx
        rw [Subgroup.mem_bot] at h1
        have hgd : ∀ y, d (g y) = g (d y) := fun y => by
          have := congrArg (fun φ : MulAut V => φ y) (cenD_comm hd hg)
          simp only [MulAut.mul_apply] at this
          exact this.symm
        have e : d (g x * x⁻¹) * (g x * x⁻¹)⁻¹ = g (d x * x⁻¹) * (d x * x⁻¹)⁻¹ := by
          apply cg_eq_of_add
          simp only [map_mul, map_inv, ofMul_mul, ofMul_inv, hgd]
          abel
        rw [e, h1]
        exact (socleSeries (cenD L A) j).one_mem
  obtain ⟨t, ht⟩ := exists_socleSeries_eq_top hV hD2 hDc
  have htop : socleSeries (cenD L A) (t + 1) = ⊤ :=
    top_le_iff.mp (ht ▸ socleSeries_le_succ (cenD L A) t)
  have := key t
  rw [htop, inf_top_eq] at this
  exact h.not_ltriv_commV this

end CFSG.LocalAnalysis.RankThreeUC
