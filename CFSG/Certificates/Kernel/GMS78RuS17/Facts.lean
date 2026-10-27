module

public import Certificates.Data.Kernel.GMS78RuSClo
public import CFSG.Certificates.Kernel.GMS78RuGenS
import CFSG.Certificates.Kernel.GMS78RuP.Basic
import CFSG.Certificates.Kernel.GMS78RuS17.Basic
import CFSG.Certificates.Kernel.GMS78RuS17.Idx
import CFSG.Certificates.Kernel.GMS78RuS17.Key
import CFSG.Certificates.Kernel.GMS78RuS17.Zx
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.GMS.S17

open CFSG.KLie.CT CFSG.KC.Loop CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS

section Facts

variable {gA : Array (Fin 8)} {dA : Array (Nat × Fin 8)} {dct : List Lin8} {ε : Bool}
  {m : Nat → Nat → Nat}

private theorem mem_cent {u p : Nat} :
    p ∈ Gen.cent17G gA dA dct ε u ↔ p < 8192 ∧ Gen.mul17G gA dA dct ε p u =
      Gen.mul17G gA dA dct ε u p := by
  unfold Gen.cent17G
  rw [List.mem_filter, List.mem_range, beq_iff_eq]

private theorem nodup_cent (u : Nat) : (Gen.cent17G gA dA dct ε u).Nodup := by
  unfold Gen.cent17G
  exact List.nodup_range.filter _

theorem keyfacts (hEq : ∀ p < 8192, ∀ q < 8192, m p q = Gen.mul17G gA dA dct ε p q)
    (hLt : ∀ p q, Gen.mul17G gA dA dct ε p q < 8192)
    (hc : ∀ p < 8192, m p 256 = m 256 p) {u : Nat} (hu : u < 8192) {k : Nat}
    (hK : kKey17 m u k = true) (hC : kClo17 m u k = true) :
    kN k = (Gen.cent17G gA dA dct ε u).length ∧
    kR1 k = Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε u) u ∧
    kR2 k = Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε u) 256 ∧
    kNeedZ u k = needZ17 u (Gen.cent17G gA dA dct ε u).length
      (Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε u) u)
      (Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε u) 256) ∧
    (kNeedZ u k = true →
      kZ1 k = Gen.zx17G gA dA dct ε (Gen.cent17G gA dA dct ε u) u ∧
      kZ2 k = Gen.zx17G gA dA dct ε (Gen.cent17G gA dA dct ε u) 256) := by
  unfold kKey17 at hK
  rw [P117.andB_iff] at hK
  obtain ⟨hK1, hK2⟩ := hK
  have hK1' : sKey m 8192 u = kKeyPart k := Nat.eq_of_beq_eq_true hK1
  obtain ⟨h1, h2, h3⟩ := key_read hEq hu hK1'
  refine ⟨h1, h2, h3, kNeedZ_eq hEq hu hK1', fun hz => ?_⟩
  rw [sFilter_cent hEq hu] at hK2
  unfold kClo17 at hC
  rw [sFilter_cent hEq hu, P117.orB_eq, P117.notB_eq, hz] at hC
  have hC' : sClosed m (Gen.cent17G gA dA dct ε u) = true := by simpa using hC
  have hK2' : (neLen (Gen.cent17G gA dA dct ε u) == 256 &&
      sZx m (Gen.cent17G gA dA dct ε u) u == Nat.shiftRight k 42) = true := by
    have := hK2
    rw [hz] at this
    simpa [P117.andB_eq, P117.beq_eq] using this
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, neLen_eq] at hK2'
  obtain ⟨hlen, hz2⟩ := hK2'
  have hnd := nodup_cent (gA := gA) (dA := dA) (dct := dct) (ε := ε) u
  have hcl := sClosed_mem hnd (by omega) hC'
  have huC : u ∈ Gen.cent17G gA dA dct ε u := mem_cent.2 ⟨hu, rfl⟩
  have h256 : 256 ∈ Gen.cent17G gA dA dct ε u := by
    refine mem_cent.2 ⟨by omega, ?_⟩
    have := hc u hu
    rw [hEq u hu 256 (by omega), hEq 256 (by omega) u hu] at this
    exact this.symm
  obtain ⟨z1, z2⟩ := kZ_read hnd hlen hcl huC h256 hz2
  have conv : ∀ t < 8192, (Gen.cent17G gA dA dct ε u).countP
      (fun p => (Gen.cent17G gA dA dct ε u).all fun q => m p q == m q p || m p q == m t (m q p)) =
      Gen.zx17G gA dA dct ε (Gen.cent17G gA dA dct ε u) t := by
    intro t ht
    unfold Gen.zx17G
    refine List.countP_congr fun p hp => ?_
    have hp' := (mem_cent.1 hp).1
    rw [List.all_eq_true, List.all_eq_true]
    refine forall_congr' fun q => forall_congr' fun hq => ?_
    have hq' := (mem_cent.1 hq).1
    rw [hEq p hp' q hq', hEq q hq' p hp', hEq t ht _ (hLt q p)]
  exact ⟨(z1.trans (conv u hu)), (z2.trans (conv 256 (by omega)))⟩

end Facts

end CFSG.KC.GMS.S17

end
