module

public import CFSG.LargeExtraspecial.S97RWC
public import CFSG.LargeExtraspecial.S97RG1
public import CFSG.LargeExtraspecial.S111TMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup CFSG.LargeExtraspecial.S4 CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G} {h k : G}
  {m : S.M}

omit [Finite G] in
theorem inv_mul_mul_eq (m : S.M) (k : G) : ((m⁻¹ : S.M) : G) * ((m : G) * k) = k := by
  rw [Subgroup.coe_inv, inv_mul_cancel_left]

theorem Pair111.isTI97Rev (P : Pair111 S g A h k ((m : G) * k)) (h6 : 6 ≤ S.width)
    (hE : Ebar S k ((m : G) * k) ≠ ⊥) :
    ∀ x ∈ S.Lbar k ⊔ S.Lbar ((m : G) * k),
      (S.Lbar ((m : G) * k) ⊔ (O2Sub (S.Lbar k ⊔ S.Lbar ((m : G) * k)))).map (MulAut.conj x).toMonoidHom = S.Lbar ((m : G) * k) ⊔ (O2Sub (S.Lbar k ⊔ S.Lbar ((m : G) * k))) ∨
        (S.Lbar ((m : G) * k) ⊔ (O2Sub (S.Lbar k ⊔ S.Lbar ((m : G) * k)))).map (MulAut.conj x).toMonoidHom ⊓
          (S.Lbar ((m : G) * k) ⊔ (O2Sub (S.Lbar k ⊔ S.Lbar ((m : G) * k)))) ≤ (O2Sub (S.Lbar k ⊔ S.Lbar ((m : G) * k))) := by
  have P' : Pair111 S (h * g) (A.map (MulAut.conj h).toMonoidHom) h⁻¹ ((m : G) * k)
      (((m⁻¹ : S.M) : G) * ((m : G) * k)) := by
    rw [inv_mul_mul_eq]
    exact P.swap
  have hF : Ebar S ((m : G) * k) (((m⁻¹ : S.M) : G) * ((m : G) * k)) ≠ ⊥ := by
    rw [inv_mul_mul_eq]
    exact P.Ebar_ne_bot' hE
  have h1 := P'.isTI97 (P'.isTIModEF h6 hF)
  unfold S9.IsTI97 at h1
  rw [inv_mul_mul_eq, sup_comm (S.Lbar ((m : G) * k)) (S.Lbar k)] at h1
  exact h1

theorem Pair111.form2 (hS : SimpleCaseStmt) (h215 : Lemma215Stmt) (hI : ListWCIdentification)
    (P : Pair111 S g A h k ((m : G) * k)) (h6 : 6 ≤ S.width) (hE : Ebar S k ((m : G) * k) ≠ ⊥)
    (h4 : 4 * Nat.card (Ebar S k ((m : G) * k)) ≤ Nat.card (S.Lbar k)) :
    commutator (S9.Q97 S k m) = ⊤ ∧ Odd (Nat.card (center (S9.Q97 S k m))) ∧
      IsSimpleGroup (S9.Q97 S k m ⧸ center (S9.Q97 S k m)) ∧
      StdPair (S9.Q97 S k m ⧸ center (S9.Q97 S k m))
        ((S9.Tj97 S k m k).map (QuotientGroup.mk' (center (S9.Q97 S k m)))) ∧
      StdPair (S9.Q97 S k m ⧸ center (S9.Q97 S k m))
        ((S9.Tj97 S k m ((m : G) * k)).map (QuotientGroup.mk' (center (S9.Q97 S k m)))) := by
  have X := P.hyp97 hE
  have hTI := P.isTI97 (P.isTIModEF h6 hE)
  have hTIb := P.isTI97Rev h6 hE
  have hT : IsWC (S9.Tj97 S k m k) := X.Tj97_isWC le_sup_left P.hy.hyp4 P.hy.cons hTI
  have hTb : IsWC (S9.Tj97 S k m ((m : G) * k)) :=
    X.Tj97_isWC le_sup_right P.hy'.hyp4 P.hy'.cons hTIb
  have hEpos : 0 < Nat.card (Ebar S k ((m : G) * k)) := Nat.card_pos
  have h4T : 4 ≤ Nat.card (S9.Tj97 S k m k) := by
    have hc := X.card_Tj97_mul (j := k) le_sup_left
    rw [P.inf_O2Sub_eq] at hc
    nlinarith
  have h4Tb : 4 ≤ Nat.card (S9.Tj97 S k m ((m : G) * k)) := by
    have hc := X.card_Tj97_mul (j := (m : G) * k) le_sup_right
    rw [P.inf_O2Sub_eq', ← P.card_Ebar_eq, P.hy'.cons.card_Lbar, ← P.hy.cons.card_Lbar] at hc
    nlinarith
  have hO2 : ∀ N : Subgroup (S9.Q97 S k m), N.Normal → IsPGroup 2 N → N = ⊥ :=
    fun N hN hP => S9.Q97.eq_bot_of_normal N hN hP
  have hTI' := fun y => X.Tj97_isTI le_sup_left hTI y
  have hTIb' := fun y => X.Tj97_isTI le_sup_right hTIb y
  have hNC := S9.normalClosure_eq_top_of_pair hS h215 hI S9.Tj97_sup hT hTb h4T h4Tb hTI'
    hTIb' hO2
  rcases form2_core_of_simpleCase hS h215 hI hT hNC hO2 with hZ | ⟨-, hcomm, hodd, hsimp, hstd⟩
  · exact absurd hZ (S9.not_zStarCase hT.1 h4T hTI' hO2)
  have := hsimp
  exact ⟨hcomm, hodd, hsimp, hstd, hI _ hstd.listGroup _
    (hTb.map_quotient_central_odd _ le_rfl hodd) (four_le_card_map_central_odd hTb.1 _ hodd h4Tb)⟩

end CFSG.LargeExtraspecial.S11
