module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cHyp
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cStmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cNorm
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cLift
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt41

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section CaseSplit

variable {A : Type} [Group A] [Finite A] {p : ℕ} {V X : Subgroup A} {z : A}

theorem card_Cz_eq_two (h : Setup412 p V X z) (hC : Core412 V X z)
    (h4 : ¬ 4 ≤ Nat.card ↥(V ⊓ centralizer (V : Set A) ⊓ centralizer ({z} : Set A))) :
    Nat.card ↥(V ⊓ centralizer (V : Set A) ⊓ centralizer ({z} : Set A)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCzle : V ⊓ centralizer (V : Set A) ⊓ centralizer ({z} : Set A) ≤ V :=
    inf_le_left.trans inf_le_left
  obtain ⟨j, hj⟩ := (h.W2.to_le hCzle).exists_card_eq
  have hge : 2 ≤ Nat.card ↥(V ⊓ centralizer (V : Set A) ⊓ centralizer ({z} : Set A)) := by
    by_contra hcon
    have h1 : Nat.card ↥(V ⊓ centralizer (V : Set A) ⊓ centralizer ({z} : Set A)) = 1 := by
      have := Nat.card_pos (α := ↥(V ⊓ centralizer (V : Set A) ⊓ centralizer ({z} : Set A)))
      omega
    have hle := hC.card_le
    rw [h1, one_pow, mul_one] at hle
    have hZV : V ⊓ centralizer (V : Set A) = V := Subgroup.eq_of_le_of_card_ge inf_le_left hle
    apply hC.nonab
    intro a ha b hb
    have : a ∈ V ⊓ centralizer (V : Set A) := by rw [hZV]; exact ha
    exact (mem_centralizer_iff.mp this.2 b hb).symm
  have hlt : Nat.card ↥(V ⊓ centralizer (V : Set A) ⊓ centralizer ({z} : Set A)) < 4 := by omega
  rw [hj] at hge hlt ⊢
  rcases j with _ | _ | j
  · simp at hge
  · norm_num
  · exfalso
    have h4le : 4 ≤ 2 ^ (j + 1 + 1) :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (j + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end CaseSplit

theorem prop4_1c_of_fullG (hG : NonCentralDihedral) (hI : Prop4_1c_i) : Prop4_1c := by
  intro G _ _ z k S hctx H₀ H₁ _ hz p X hsig W hW hXW hzW hne
  have hzord : z ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hctx.central.1] at h
  have hz2 : zSec z H₀ hz H₁ * zSec z H₀ hz H₁ = 1 := by
    rw [zSec, ← QuotientGroup.mk_mul]
    have : (⟨z, hz⟩ * ⟨z, hz⟩ : ↥H₀) = 1 := Subtype.ext (by simpa [pow_two] using hzord)
    rw [this]
    rfl
  have hcen : zSec z H₀ hz H₁ ∈ centralizer ({zSec z H₀ hz H₁} : Set (Sec H₀ H₁)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hsetup : Setup412 p W X (zSec z H₀ hz H₁) :=
    { prime := hsig.A.prime
      odd := hsig.A.odd
      W2 := hW
      Xp := hsig.A.pgroup
      XW := hXW
      zW := hzW
      z2 := hz2
      zX := hsig.A.inv _ (Subgroup.mem_top _) hcen
      comm := hsig.A.comm
      Cz := fun c _ hc => hsig.A.inv c (Subgroup.mem_top _)
        (Subgroup.mem_centralizer_singleton_iff.mpr hc) }
  obtain ⟨hle, hXn, hzn, hcomm2, hcent, hsetup'⟩ := reduce412 hsetup
  have hC : Core412 ⁅W, X⁆ X (zSec z H₀ hz H₁) := core412_of_setup hsetup' hcomm2 hne
  have hrel : (centralizer (W : Set (Sec H₀ H₁))).relIndex X =
      (centralizer ((⁅W, X⁆ : Subgroup (Sec H₀ H₁)) : Set (Sec H₀ H₁))).relIndex X := by
    rw [← Subgroup.inf_relIndex_right (centralizer (W : Set (Sec H₀ H₁))) X,
      ← Subgroup.inf_relIndex_right (centralizer ((⁅W, X⁆ : Subgroup (Sec H₀ H₁)) : Set (Sec H₀ H₁))) X,
      inf_comm _ X, inf_comm _ X, hcent]
  by_cases h4 : 4 ≤ Nat.card ↥(zOf ⁅W, X⁆ ⊓ centralizer ({zSec z H₀ hz H₁} : Set (Sec H₀ H₁)))
  ·
    obtain ⟨hk, hL, hrelV, hsyl, hodd⟩ := hI G z k S hctx H₀ H₁ hz p X hsig ⁅W, X⁆ hsetup'.W2 hXn hzn
      hcomm2 hne h4
    exact ⟨hC.X_cent_Z, hrel ▸ hrelV, Or.inl ⟨hk, hL, hsyl, hodd⟩⟩
  ·
    have hcz := card_Cz_eq_two hsetup' hC h4
    obtain ⟨s, u, v, hs1, hsZ, hZ, huV, hvV, hu4, hv4, huv, ⟨e⟩⟩ :=
      exists_quaternion_data hsetup' hcomm2 hne hcz
    refine ⟨hC.X_cent_Z, hrel ▸ relIndex_centralizer_eq_three hsetup' hcomm2 hne e,
      Or.inr ⟨⟨e⟩, ?_, normIso_perm_four hsetup' hcomm2 hne e⟩⟩
    have hsc : ∀ w ∈ (⁅W, X⁆ : Subgroup (Sec H₀ H₁)), w * s = s * w :=
      fun w hw => mem_centralizer_iff.mp hsZ.2 w hw
    have hs2 : s * s = 1 := hC.Z_exp2 s hsZ
    have hXs : ∀ x ∈ X, x * s = s * x :=
      fun x hx => (mem_centralizer_iff.mp (hC.X_cent_Z hx) s hsZ).symm
    obtain ⟨s', hs', hcen', hπ⟩ := isCentralInvolution_of_lift (hG G z k S hctx) H₀ H₁ hsig.odd
      hsig.A.prime hsig.A.odd ⁅W, X⁆ X hsetup'.W2 hsetup'.Xp hXn hcomm2 s u v hsZ.1 hsc hs2 hs1 hXs
      huV hvV hu4 hv4 huv
    exact ⟨s', hs', hcen', by rw [hπ]; exact hsZ⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
