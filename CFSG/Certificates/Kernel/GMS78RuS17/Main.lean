module

public import Certificates.Data.Kernel.GMS78RuSClo
public import CFSG.Certificates.Kernel.GMS78RuPSound
import CFSG.Certificates.Kernel.GMS78RuP.Basic
import CFSG.Certificates.Kernel.GMS78RuS17.Basic
import CFSG.Certificates.Kernel.GMS78RuS17.Key
import CFSG.Certificates.Kernel.GMS78RuS17.Facts

public section

namespace CFSG.KC.GMS.S17

open CFSG.KLie.CT CFSG.KC.Loop CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS

private theorem pair_step {gA : Array (Fin 8)} {dA : Array (Nat × Fin 8)} {dct : List Lin8}
    {ε : Bool} {u v ka kb : Nat}
    (a1 : kN ka = (Gen.cent17G gA dA dct ε u).length)
    (a2 : kR1 ka = Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε u) u)
    (a3 : kR2 ka = Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε u) 256)
    (a4 : kNeedZ u ka = needZ17 u (Gen.cent17G gA dA dct ε u).length
      (Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε u) u)
      (Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε u) 256))
    (a5 : needZ17 u (Gen.cent17G gA dA dct ε u).length
      (Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε u) u)
      (Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε u) 256) = true →
      kZ1 ka = Gen.zx17G gA dA dct ε (Gen.cent17G gA dA dct ε u) u ∧
      kZ2 ka = Gen.zx17G gA dA dct ε (Gen.cent17G gA dA dct ε u) 256)
    (b1 : kN kb = (Gen.cent17G gA dA dct ε v).length)
    (b2 : kR1 kb = Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε v) v)
    (b3 : kR2 kb = Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε v) 256)
    (b4 : kNeedZ v kb = needZ17 v (Gen.cent17G gA dA dct ε v).length
      (Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε v) v)
      (Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε v) 256))
    (b5 : needZ17 v (Gen.cent17G gA dA dct ε v).length
      (Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε v) v)
      (Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε v) 256) = true →
      kZ1 kb = Gen.zx17G gA dA dct ε (Gen.cent17G gA dA dct ε v) v ∧
      kZ2 kb = Gen.zx17G gA dA dct ε (Gen.cent17G gA dA dct ε v) 256)
    (h : orB (inX17 u)
      (orB (notB (andB (Nat.beq (kN ka) (kN kb))
          (andB (Nat.beq (kR1 ka) (kR2 kb)) (Nat.beq (kR2 ka) (kR1 kb)))))
        (orB (andB (Nat.beq (kN ka) 128) (orB (Nat.beq (Nat.shiftRight u 10) 1)
          (Nat.beq (Nat.shiftRight u 10) 5)))
          (andB (kNeedZ u ka) (andB (kNeedZ v kb)
            (orB (notB (Nat.beq (kZ1 ka) (kZ2 kb))) (notB (Nat.beq (kZ2 ka) (kZ1 kb)))))))) = true)
    (hx : ¬ inX17 u = true) :
    (!((Gen.key17G gA dA dct ε u).2.1 == (Gen.key17G gA dA dct ε v).2.1 &&
              (Gen.key17G gA dA dct ε u).2.2.1 == (Gen.key17G gA dA dct ε v).2.2.2.1 &&
            (Gen.key17G gA dA dct ε u).2.2.2.1 == (Gen.key17G gA dA dct ε v).2.2.1) ||
        (Gen.key17G gA dA dct ε u).2.1 == 128 &&
          ((Gen.key17G gA dA dct ε u).1 / 1024 == 1 || (Gen.key17G gA dA dct ε u).1 / 1024 == 5) ||
      needZ17 (Gen.key17G gA dA dct ε u).1 (Gen.key17G gA dA dct ε u).2.1
            (Gen.key17G gA dA dct ε u).2.2.1 (Gen.key17G gA dA dct ε u).2.2.2.1 &&
          needZ17 (Gen.key17G gA dA dct ε v).1 (Gen.key17G gA dA dct ε v).2.1
            (Gen.key17G gA dA dct ε v).2.2.1 (Gen.key17G gA dA dct ε v).2.2.2.1 &&
        ((Gen.key17G gA dA dct ε u).2.2.2.2.1 != (Gen.key17G gA dA dct ε v).2.2.2.2.2 ||
          (Gen.key17G gA dA dct ε u).2.2.2.2.2 != (Gen.key17G gA dA dct ε v).2.2.2.2.1)) =
    true := by
  simp only [P117.orB_eq, P117.andB_eq, P117.notB_eq, P117.beq_eq, shr10, a1, a2, a3, a4, b1, b2,
    b3, b4] at h
  simp only [Gen.key17G]
  have hx' : inX17 u = false := by simpa using hx
  rw [hx', Bool.false_or] at h
  generalize needZ17 u (Gen.cent17G gA dA dct ε u).length
    (Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε u) u)
    (Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε u) 256) = nzu at a5 h ⊢
  generalize needZ17 v (Gen.cent17G gA dA dct ε v).length
    (Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε v) v)
    (Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε v) 256) = nzv at b5 h ⊢
  cases nzu <;> cases nzv
  · simpa [or_assoc] using h
  · simpa [or_assoc] using h
  · simpa [or_assoc] using h
  · obtain ⟨e1, e2⟩ := a5 rfl
    obtain ⟨f1, f2⟩ := b5 rfl
    rw [e1, e2, f1, f2] at h
    simpa [or_assoc] using h

theorem check17_of (gA : Array (Fin 8)) (dA : Array (Nat × Fin 8)) (dct : List Lin8) (ε : Bool)
    (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO : Nat) (INVL KEYL : List Nat)
    (hT : sTabs gA dA dct ε GT DPR LIN DM DO)
    (hEq : ∀ p < 8192, ∀ q < 8192, mul17K GT DPR LIN DM DO p q = Gen.mul17G gA dA dct ε p q)
    (hLt : ∀ p q, Gen.mul17G gA dA dct ε p q < 8192)
    (hI : INVL = sInvs (mul17K GT DPR LIN DM DO) 8192)
    (hK : ∀ i < INVL.length, kKey17 (mul17K GT DPR LIN DM DO) (INVL.getD i 0) (KEYL.getD i 0) = true)
    (hC : ∀ i < INVL.length, kClo17 (mul17K GT DPR LIN DM DO) (INVL.getD i 0) (KEYL.getD i 0) = true)
    (hF : kFin17 (mul17K GT DPR LIN DM DO) inX17 INVL KEYL = true) :
    Gen.check17G gA dA dct ε = true := by
  have _ := hT
  generalize hm : mul17K GT DPR LIN DM DO = m at *
  unfold kFin17 at hF
  rw [P117.andB_iff, P117.andB_iff] at hF
  obtain ⟨-, hc, hp⟩ := hF
  rw [allN_iff] at hc
  rw [sAllPairs_iff] at hp
  have hI' : INVL = Gen.inv17G gA dA dct ε := hI.trans (sInvs_eq hEq)
  have hc' : ∀ p < 8192, m p 256 = m 256 p := fun p hp' => Nat.eq_of_beq_eq_true (hc p hp')
  unfold Gen.check17G
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun p hp' => ?_, ?_⟩
  · have h := hc' p (List.mem_range.1 hp')
    rw [hEq p (List.mem_range.1 hp') 256 (by omega), hEq 256 (by omega) p (List.mem_range.1 hp')]
      at h
    exact beq_iff_eq.2 h
  · intro a ha
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ha
    rw [← hI'] at hu
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hu
    rw [Bool.or_eq_true]
    by_cases hx : inX17 INVL[i] = true
    · exact Or.inl hx
    refine Or.inr ?_
    rw [List.all_eq_true]
    intro b hb
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hb
    rw [← hI'] at hv
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hv
    have hpij := hp i hi j hj
    rw [getD_eq' _ _ hi, getD_eq' _ _ hj] at hpij
    have hlt : ∀ x ∈ INVL, x < 8192 := by
      intro x hx
      rw [hI'] at hx
      exact List.mem_range.1 (List.mem_filter.1 hx).1
    have hKi := hK i hi
    have hCi := hC i hi
    have hKj := hK j hj
    have hCj := hC j hj
    rw [getD_eq' _ _ hi] at hKi hCi
    rw [getD_eq' _ _ hj] at hKj hCj
    obtain ⟨a1, a2, a3, a4, a5⟩ := keyfacts hEq hLt hc' (hlt _ hu) hKi hCi
    obtain ⟨b1, b2, b3, b4, b5⟩ := keyfacts hEq hLt hc' (hlt _ hv) hKj hCj
    exact pair_step a1 a2 a3 a4 (fun hz => a5 (a4 ▸ hz)) b1 b2 b3 b4 (fun hz => b5 (b4 ▸ hz)) hpij hx

end CFSG.KC.GMS.S17

end
