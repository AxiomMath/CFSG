module

public import Certificates.Data.Kernel.SporSch.HeSrch
import CFSG.Certificates.Kernel.SporSch.HeSrchLemmas
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier

variable {n : Nat}

theorem schreierOK_zero (levels : Array Level) (base : Array Nat) (i : Nat)
    (steps : Array (Array Nat)) (L : Level) :
    CFSG.Monster.B.Co2.Native.schreierOK n levels base i steps L 0 = true := by
  simp [CFSG.Monster.B.Co2.Native.schreierOK, parLt]

theorem stab0_sound {w kS BP NS CH NR NL NT BT NQ BQ : Nat} {PS PSI LR Ts LT PT QT : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {b0 : Nat} {bs : List Nat}
    {Q : RawSchreierDatum n} {O : Array (Array Nat)} {W : Array (List Int)} {chunks : Nat}
    (hA : ChainArrays Q O S base W) (hc : rawChainOK n O S base W chunks = true)
    (hch : 0 < chunks)
    (hT : TabChain n w kS 5 BP NS CH NR NL NT BT NQ BQ PS PSI LR Ts LT PT QT S base (b0 :: bs))
    (hb0 : b0 < n) {t : Nat → Bool} {Pr : Equiv.Perm (Fin n) → Prop} [DecidablePred Pr]
    (ht : ∀ F, nfValidK 5 LR F = true → F % 65536 = 0 →
      (t F = true ↔ Pr (nfElt n S base (nfArr 5 F)))) :
    cnt0R LR t 0 (rcnt (LR 1)) =
      Nat.card {g : Q.originalSubgroup // (g : Equiv.Perm (Fin n)) ⟨b0, hb0⟩ = ⟨b0, hb0⟩ ∧
        Pr g} :=
  Tab.stab0_spec hA hc hch hT hb0 ht

theorem srchA_sound {w kS BP NS CH NR NL NT BT NQ BQ : Nat} {PS PSI LR Ts LT PT QT : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {b0 b1 b2 : Nat} {bs : List Nat}
    {Q : RawSchreierDatum n} {O : Array (Array Nat)} {W : Array (List Int)} {chunks : Nat}
    (hA : ChainArrays Q O S base W) (hc : rawChainOK n O S base W chunks = true)
    (hch : 0 < chunks)
    (hT : TabChain n w kS 5 BP NS CH NR NL NT BT NQ BQ PS PSI LR Ts LT PT QT S base
      (b0 :: b1 :: b2 :: bs))
    {X Y : Nat → Nat} {x y : Equiv.Perm (Fin n)} (hX : RepF n X x) (hY : RepF n Y y)
    (hxy : ∀ g ∈ Q.originalSubgroup, (g * x)⁻¹ * (y * g) ∈ Q.originalSubgroup)
    (h0 : X b0 = b0) (h1 : X b1 = b2) :
    sumN (rcnt (LR 0)) (srchAAt w kS NR NL LT PT QT LR (b0 :: b1 :: b2 :: bs) b0 X Y) =
      Nat.card {g : Q.originalSubgroup // (g : Equiv.Perm (Fin n)) * x = y * g} :=
  Tab.srchA_spec hA hc hch hT hX hY hxy h0 h1

theorem srchAAt_sound {w kS BP NS CH NR NL NT BT NQ BQ : Nat} {PS PSI LR Ts LT PT QT : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {b0 b1 b2 : Nat} {bs : List Nat}
    {Q : RawSchreierDatum n} {O : Array (Array Nat)} {W : Array (List Int)} {chunks : Nat}
    (hA : ChainArrays Q O S base W) (hc : rawChainOK n O S base W chunks = true)
    (hch : 0 < chunks)
    (hT : TabChain n w kS 5 BP NS CH NR NL NT BT NQ BQ PS PSI LR Ts LT PT QT S base
      (b0 :: b1 :: b2 :: bs))
    {X Y : Nat → Nat} {x y : Equiv.Perm (Fin n)} (hX : RepF n X x) (hY : RepF n Y y)
    (hxy : ∀ g ∈ Q.originalSubgroup, (g * x)⁻¹ * (y * g) ∈ Q.originalSubgroup)
    (h0 : X b0 = b0) (h1 : X b1 = b2) (hb0 : b0 < n) {a : Nat} (ha : a < rcnt (LR 0)) :
    srchAAt w kS NR NL LT PT QT LR (b0 :: b1 :: b2 :: bs) b0 X Y a =
      Nat.card {g : Q.originalSubgroup // (((g : Equiv.Perm (Fin n)) ⟨b0, hb0⟩ : Fin n) : Nat) =
        trPtT w NR NL LT PT (nat_lit 0) a b0 ∧ (g : Equiv.Perm (Fin n)) * x = y * g} :=
  Tab.srchAAt_card hA hc hch hT hX hY hxy h0 h1 hb0 ha

variable {H : Subgroup (Equiv.Perm (Fin n))} {bs : List Nat}

theorem comm_mem_of_hxy {x y z : Equiv.Perm (Fin n)}
    (hxy : ∀ g ∈ H, (g * x)⁻¹ * (y * g) ∈ H) (hz : z ∈ H) : (z * y)⁻¹ * (y * z) ∈ H := by
  have a1 := hxy 1 H.one_mem
  have az := hxy z hz
  have e : (z * y)⁻¹ * (y * z) = ((1 * x)⁻¹ * (y * 1))⁻¹ *
      ((z * x)⁻¹ * (y * z) * z⁻¹ * ((1 * x)⁻¹ * (y * 1))⁻¹) * ((1 * x)⁻¹ * (y * 1)) * z := by
    group
  rw [e]
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem a1) (H.mul_mem (H.mul_mem az (H.inv_mem hz))
    (H.inv_mem a1))) a1) hz

theorem comm_of_eqOnL (hH : BaseFaithful H bs) {Z Y : Nat → Nat} {z y : Equiv.Perm (Fin n)}
    (hZ : RepF n Z z) (hY : RepF n Y y) (hm : (z * y)⁻¹ * (y * z) ∈ H)
    (h : eqOnL bs (fun b => Z (Y b)) (fun b => Y (Z b)) = true) : z * y = y * z := by
  have h1 := hH _ hm fun u hu => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    refine Fin.ext ?_
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hY _ (z u).2, ← hZ u u.2, ← hZ _ (y u).2,
      ← hY u u.2]
    exact ((eqOnL_iff bs _ _).1 h u hu).symm
  exact inv_mul_eq_one.1 h1

theorem fib_card_mul {x y z : Equiv.Perm (Fin n)} (hz : z ∈ H) (hzy : z * y = y * z)
    (b p : Fin n) :
    Nat.card {g : H // (((g : Equiv.Perm (Fin n)) b : Fin n) : Nat) = (z p : Nat) ∧
        (g : Equiv.Perm (Fin n)) * x = y * g} =
      Nat.card {g : H // (((g : Equiv.Perm (Fin n)) b : Fin n) : Nat) = (p : Nat) ∧
        (g : Equiv.Perm (Fin n)) * x = y * g} := by
  have hzy' : z⁻¹ * y = y * z⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hzy, mul_assoc, mul_inv_cancel, mul_one]
  refine Nat.card_congr
    { toFun := fun g => ⟨⟨z⁻¹ * g, H.mul_mem (H.inv_mem hz) g.1.2⟩, ?_⟩
      invFun := fun g => ⟨⟨z * g, H.mul_mem hz g.1.2⟩, ?_⟩
      left_inv := fun g => Subtype.ext (Subtype.ext (by simp))
      right_inv := fun g => Subtype.ext (Subtype.ext (by simp)) }
  · obtain ⟨hb, hg⟩ := g.2
    refine ⟨?_, ?_⟩
    · have e : ((g : H) : Equiv.Perm (Fin n)) b = z p := Fin.ext hb
      change (((z⁻¹ * (g : H)) : Equiv.Perm (Fin n)) b : Nat) = p
      rw [Equiv.Perm.mul_apply, e, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
    · change z⁻¹ * ((g : H) : Equiv.Perm (Fin n)) * x = y * (z⁻¹ * (g : H))
      rw [mul_assoc, hg, ← mul_assoc, hzy', mul_assoc]
  · obtain ⟨hb, hg⟩ := g.2
    refine ⟨?_, ?_⟩
    · have e : ((g : H) : Equiv.Perm (Fin n)) b = p := Fin.ext hb
      change (((z * (g : H)) : Equiv.Perm (Fin n)) b : Nat) = z p
      rw [Equiv.Perm.mul_apply, e]
    · change z * ((g : H) : Equiv.Perm (Fin n)) * x = y * (z * (g : H))
      rw [mul_assoc, hg, ← mul_assoc, hzy, mul_assoc]

theorem twK_iff (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n) {w NR NL : Nat}
    {LT PT : Nat → Nat} {F : Nat} {g u : Equiv.Perm (Fin n)}
    (hg : RepF n (nfPtT w NR NL LT PT (nat_lit 5) F) g) {U : Nat → Nat} (hU : RepF n U u)
    (hm : (u * g) ^ 2 ∈ H) : twK w NR NL LT PT bs U F = true ↔ (u * g) ^ 2 = 1 := by
  have h : RepF n (fun b => U (nfPtT w NR NL LT PT (nat_lit 5) F
      (U (nfPtT w NR NL LT PT (nat_lit 5) F b)))) ((u * g) ^ 2) :=
    (hU.comp (hg.comp (hU.comp hg))).congr (by rw [sq]; simp only [mul_assoc])
  exact fixL_iff hH hbs h hm

end CFSG.KS.SporSch

end
