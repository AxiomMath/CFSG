module

public import Certificates.Data.Kernel.J2Cent
public import CFSG.Certificates.Kernel.J2EnumSound
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
import all CFSG.Certificates.Kernel.J2Enum.Count
import all CFSG.Certificates.Kernel.J2Enum.Classes
import CFSG.Certificates.Kernel.Child3Inv
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

namespace CFSG.KC.J2Enum.CntPf

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Child3 CFSG.KC.J2Cent

private theorem j2cBlk_eq (n w : ℕ) (LR TR : ℕ → ℕ) (BP E₁ E₂ : ℕ) :
    sumF (rcnt (LR 0)) (blkCent n w LR TR BP E₁ E₂) =
      tri (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) fun a b c =>
        nIf(commB w (mask w) E₁ (fun p => pg w (mask w)
            (pcomp n w (mask w) (TR (roff n (n * w) (LR 0) + a)) (TR (roff n (n * w) (LR 1) + b)))
            (pg w (mask w) (TR (roff n (n * w) (LR 2) + c)) p))
          (pg w (mask w) BP 0) (pg w (mask w) BP 1) (pg w (mask w) BP 2)
          (pg w (mask w) E₁ (pg w (mask w) BP 0)) (pg w (mask w) E₁ (pg w (mask w) BP 1))
          (pg w (mask w) E₁ (pg w (mask w) BP 2)), 1, 0) +
        nIf(commB w (mask w) E₂ (fun p => pg w (mask w)
            (pcomp n w (mask w) (TR (roff n (n * w) (LR 0) + a)) (TR (roff n (n * w) (LR 1) + b)))
            (pg w (mask w) (TR (roff n (n * w) (LR 2) + c)) p))
          (pg w (mask w) BP 0) (pg w (mask w) BP 1) (pg w (mask w) BP 2)
          (pg w (mask w) E₂ (pg w (mask w) BP 0)) (pg w (mask w) E₂ (pg w (mask w) BP 1))
          (pg w (mask w) E₂ (pg w (mask w) BP 2)), Nat.shiftLeft 1 20, 0) := by
  rw [sumF_eq]
  unfold tri
  congr 1
  refine List.map_congr_left fun a _ => ?_
  simp only [blkCent, PF.strictN_eqP, sumF_eq]
  rfl

private theorem j2cCommB_eq {n w BP E : ℕ} {Γ : Subgroup (Equiv.Perm (Fin n))}
    (hbp : ∀ t < 3, pg w (mask w) BP t < n)
    (hsep : ∀ γ : Equiv.Perm (Fin n), γ ∈ Γ →
      (∀ t < 3, ∀ h : pg w (mask w) BP t < n, γ ⟨_, h⟩ = ⟨_, h⟩) → γ = 1)
    {x : ℕ → ℕ} {γ ε : Equiv.Perm (Fin n)} (hx : Acts n x γ) (hγ : γ ∈ Γ) (hε : ε ∈ Γ)
    (hE : Raw.Orb.PRep n w E ε) :
    commB w (mask w) E x (pg w (mask w) BP 0) (pg w (mask w) BP 1) (pg w (mask w) BP 2)
        (pg w (mask w) E (pg w (mask w) BP 0)) (pg w (mask w) E (pg w (mask w) BP 1))
        (pg w (mask w) E (pg w (mask w) BP 2)) = decide (γ * ε = ε * γ) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  unfold commB
  rw [bAnd_iff, bAnd_iff]
  have e : ∀ t (ht : t < 3), (Nat.beq (x (pg w (mask w) E (pg w (mask w) BP t)))
      (pg w (mask w) E (x (pg w (mask w) BP t))) = true ↔
      (γ * ε) ⟨_, hbp t ht⟩ = (ε * γ) ⟨_, hbp t ht⟩) := fun t ht => by
    have h1 : pg w (mask w) E (pg w (mask w) BP t) = (ε ⟨_, hbp t ht⟩ : ℕ) := hE ⟨_, hbp t ht⟩
    have h2 : x (pg w (mask w) BP t) = (γ ⟨_, hbp t ht⟩ : ℕ) := hx _ (hbp t ht)
    have h3 : pg w (mask w) E (γ ⟨_, hbp t ht⟩ : ℕ) = (ε (γ ⟨_, hbp t ht⟩) : ℕ) := hE _
    have h4 : x (ε ⟨_, hbp t ht⟩ : ℕ) = (γ (ε ⟨_, hbp t ht⟩) : ℕ) := hx _ (Fin.is_lt _)
    rw [Nat.beq_eq, h1, h2, h3, h4, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Fin.val_inj]
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num)]
  constructor
  · rintro ⟨h0, h1, h2⟩
    have hz := hsep ((ε * γ)⁻¹ * (γ * ε)) (mul_mem (inv_mem (mul_mem hε hγ)) (mul_mem hγ hε))
      fun t ht h => by
        rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
        interval_cases t
        · exact h0
        · exact h1
        · exact h2
    exact (inv_mul_eq_one.1 hz).symm
  · intro H
    rw [H]
    exact ⟨rfl, rfl, rfl⟩

private theorem j2cTri_countP {M : Type*} (r0 r1 r2 : ℕ) (F : ℕ → ℕ → ℕ → M) (p : M → Bool) :
    tri r0 r1 r2 (fun a b c => if p (F a b c) then 1 else 0) = (trip r0 r1 r2 F).countP p := by
  simp only [tri, trip, List.countP_flatMap, List.countP_singleton, Function.comp_def]

private theorem j2cCard {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))} {L : List (Equiv.Perm (Fin n))}
    (hL : L.Nodup) (hm : ∀ x, x ∈ L ↔ x ∈ G) (P : Equiv.Perm (Fin n) → Prop) [DecidablePred P] :
    Nat.card {g : Equiv.Perm (Fin n) // g ∈ G ∧ P g} = L.countP (fun g => decide (P g)) := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hL.filter _),
    ← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  simp [List.mem_filter, hm]

end CFSG.KC.J2Enum.CntPf

namespace CFSG.KC.J2Cent

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.J2Enum CFSG.KC.Child3 CFSG.KC.J2Enum.CntPf

theorem cntComm_sound {n w kS kO BP NS CH E₁ E₂ : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {D : List (List Int)} {S : Array (Array Nat)} {base : Array Nat}
    (hc : ChainOK3 n w kS kO BP NS CH PS PSI LR TR TRI D S base)
    (h20 : rcnt (LR 0) * rcnt (LR 1) * rcnt (LR 2) < 2 ^ 20)
    {ε₁ ε₂ : Equiv.Perm (Fin n)} (h₁ : ε₁ ∈ Raw.Orb.Gen n S kO) (hE₁ : Raw.Orb.PRep n w E₁ ε₁)
    (h₂ : ε₂ ∈ Raw.Orb.Gen n S kO) (hE₂ : Raw.Orb.PRep n w E₂ ε₂) :
    Nat.card {g : Equiv.Perm (Fin n) // g ∈ Raw.Orb.Gen n S kO ∧ g * ε₁ = ε₁ * g} =
        fld20 (sumF (rcnt (LR 0)) (blkCent n w LR TR BP E₁ E₂)) 0 ∧
      Nat.card {g : Equiv.Perm (Fin n) // g ∈ Raw.Orb.Gen n S kO ∧ g * ε₂ = ε₂ * g} =
        fld20 (sumF (rcnt (LR 0)) (blkCent n w LR TR BP E₁ E₂)) 1 := by
  obtain ⟨hb, hh, hl, hNS, hs, -⟩ := hc
  have C := ch_of hb hh hl hNS hs
  obtain ⟨hT, hsurj, hinj⟩ := GrpPf.enum3 hb hh hl hNS hs
  have hn32 : n < 2 ^ 32 := by have := C.hn; omega
  let F : ℕ → ℕ → ℕ → Equiv.Perm (Fin n) := fun a b c =>
    CFSG.Certificates.ChainArrays.levT n S base 0 a *
      CFSG.Certificates.ChainArrays.levT n S base 1 b *
      CFSG.Certificates.ChainArrays.levT n S base 2 c
  have hL : (trip (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) F).Nodup := trip_nodup hinj
  have hm : ∀ x, x ∈ trip (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) F ↔
      x ∈ Raw.Orb.Gen n S kO := fun x => by
    rw [mem_trip]
    constructor
    · rintro ⟨a, ha, b, hb', c, hc, rfl⟩
      exact mul_mem (mul_mem (hT 0 (by norm_num) a ha).1 (hT 1 (by norm_num) b hb').1)
        (hT 2 (by norm_num) c hc).1
    · exact hsurj x
  have hsum := j2cBlk_eq n w LR TR BP E₁ E₂
  rw [tri_congr (ψ := fun a b c =>
      (if decide (F a b c * ε₁ = ε₁ * F a b c) then 1 else 0) +
        2 ^ 20 * (if decide (F a b c * ε₂ = ε₂ * F a b c) then 1 else 0))
      fun a ha b hb' c hc => by
        have hx : Acts n (fun p => pg w (mask w)
            (pcomp n w (mask w) (TR (roff n (n * w) (LR 0) + a)) (TR (roff n (n * w) (LR 1) + b)))
            (pg w (mask w) (TR (roff n (n * w) (LR 2) + c)) p)) (F a b c) :=
          acts_comp (acts_pg (Raw.Orb.prep_pcomp hn32 (hT 0 (by norm_num) a ha).2
            (hT 1 (by norm_num) b hb').2)) (acts_pg (hT 2 (by norm_num) c hc).2)
        have hFG : F a b c ∈ Raw.Orb.Gen n S kO := (hm _).1 (mem_trip.2 ⟨a, ha, b, hb', c, hc, rfl⟩)
        rw [j2cCommB_eq C.bp_lt C.sep hx hFG h₁ hE₁, j2cCommB_eq C.bp_lt C.sep hx hFG h₂ hE₂]
        cases decide (F a b c * ε₁ = ε₁ * F a b c) <;>
          cases decide (F a b c * ε₂ = ε₂ * F a b c) <;> rfl] at hsum
  simp only [tri_add, tri_mul] at hsum
  have hbd : ∀ φ : ℕ → ℕ → ℕ → ℕ, (∀ a b c, φ a b c ≤ 1) →
      tri (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) φ < 2 ^ 20 := fun φ h =>
    lt_of_le_of_lt (tri_le _ _ _ φ h) h20
  have ind : ∀ (b : Bool), (if b then 1 else 0) ≤ 1 := fun b => by cases b <;> decide
  have P := fld20_pack2 (hbd _ fun a b c => ind (decide (F a b c * ε₁ = ε₁ * F a b c)))
    (hbd _ fun a b c => ind (decide (F a b c * ε₂ = ε₂ * F a b c)))
  rw [hsum]
  exact ⟨(j2cCard hL hm _).trans ((j2cTri_countP _ _ _ F _).symm.trans P.1.symm),
    (j2cCard hL hm _).trans ((j2cTri_countP _ _ _ F _).symm.trans P.2.symm)⟩

end CFSG.KC.J2Cent

end
