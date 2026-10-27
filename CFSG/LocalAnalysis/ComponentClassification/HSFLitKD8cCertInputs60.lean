module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cCertInputs
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cNormMain

public section

namespace CFSG.ComponentClassification.HSFLit.KD8c

open Sec8

@[expose] def cntCC {D : ExtData MC} (a b : Ext D) : ℕ :=
  (Finset.univ.filter fun x : Ext D => x * a = a * x ∧ x * b = b * x).card

@[expose] def inZE {D : ExtData MC} (x : Ext D) : Bool := !x.e && inZ x.a

@[expose] def checkE2 (D : ExtData MC) (bs : ℕ) (qb : Bool) (reps c9 : List ℕ) (tab : ℕ) :
    Bool :=
  decide (64 ≤ ccE (Ext.incl D MC.u)) && chiB bs qb (Ext.incl D MC.u) &&
  reps.all (fun r => seedB true (ofCodeE (D := D) r) || decide (ccE (ofCodeE (D := D) r) ≠ 64) ||
    decide (cntE (ofCodeE (D := D) r) ≠ cntE (Ext.incl D MC.u)) || decide (r ∈ c9)) &&
  decide (∀ x : Ext D, x * x = 1 → x ≠ 1 → chiB bs qb x ≠ chiB bs qb (Ext.incl D MC.u) →
    codeE (conjE tab x * x * (conjE tab x)⁻¹) ∈ reps)

@[expose] def checkC9 (D : ExtData MC) (rc wz wk wzk utab : ℕ) (c9 : List (ℕ × ℕ)) : Bool :=
  decide (ofCodeE (D := D) rc * ofCodeE rc = 1) && decide (ofCodeE (D := D) rc ≠ 1) &&
  decide (ccE (ofCodeE (D := D) rc) = 128) &&
  decide (∀ g : Ext D, inZE ((ofCodeE rc)⁻¹ * (g * ofCodeE rc * g⁻¹)) = true) &&
  decide ((Finset.univ.filter fun g : Ext D => g * ofCodeE rc = ofCodeE rc * g ∧
    g * Ext.incl D MC.z = Ext.incl D MC.z * g ∧ g * Ext.incl D MC.k = Ext.incl D MC.k * g).card
      = 64) &&
  decide (∀ x : Ext D, x * ofCodeE rc = ofCodeE rc * x → x * x * (x * x) = 1 →
    inZE (x * x) = true) &&
  decide (ofCodeE (D := D) wz * ofCodeE rc = ofCodeE rc * ofCodeE wz ∧
    ofCodeE (D := D) wz * ofCodeE wz = Ext.incl D MC.z) &&
  decide (ofCodeE (D := D) wk * ofCodeE rc = ofCodeE rc * ofCodeE wk ∧
    ofCodeE (D := D) wk * ofCodeE wk = Ext.incl D MC.k) &&
  decide (ofCodeE (D := D) wzk * ofCodeE rc = ofCodeE rc * ofCodeE wzk ∧
    ofCodeE (D := D) wzk * ofCodeE wzk = Ext.incl D (MC.z * MC.k)) &&
  decide (∀ g : Ext D, g * Ext.incl D MC.u = Ext.incl D MC.u * g → g * g = 1 → g ≠ 1 →
    16 < cntCC (Ext.incl D MC.u) g → 128 < ccE g ∨
      conjE utab g * g * (conjE utab g)⁻¹ = Ext.incl D MC.t ∨
      conjE utab g * g * (conjE utab g)⁻¹ = Ext.incl D MC.u) &&
  c9.all (fun p => decide (64 ≤ ccE (ofCodeE (D := D) p.1)) &&
    decide (ofCodeE (D := D) p.2 * ofCodeE rc * (ofCodeE p.2)⁻¹ * ofCodeE p.1 =
      ofCodeE p.1 * (ofCodeE p.2 * ofCodeE rc * (ofCodeE p.2)⁻¹)) &&
    decide (16 < cntCC (ofCodeE (D := D) p.1) (ofCodeE p.2 * ofCodeE rc * (ofCodeE p.2)⁻¹)))

@[expose] def tab60 : ℕ :=
  110428046860940689156172021749298775635267333463115063854880568813551616 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (3458666282978755125533038168327556045795570128039305333179428722704384 + 2 ^ 256 *
  (145444772511744 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (1416459206244520987223013793987357487115933848461205319677602510691935191040 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (3545772185663652145794605824244821826196757234452536092714746819976888320 + 2 ^ 256 *
  (216524625834672128 + 2 ^ 256 *
  (8312867270514259033278520891732393984 + 2 ^ 256 *
  (8388608 + 2 ^ 256 *
  (43422033463993598997986378389795714506460374751904240322644729960018504318976 + 2 ^ 256 *
  (1180591620717411303424 + 2 ^ 256 *
  (0 + 2 ^ 256 *
  (97699575293985539889828767636333217894140985201730016143964096804613362024448 + 2 ^ 256 *
  (7975367974709495237424812686519042208 + 2 ^ 256 *
  (524640562142751450404220113593402012908978830462639540482276255449743360 + 2 ^ 256 *
  (16455045573212060421552479418723321377720050621149177265508057088)))))))))))))))))

@[expose] def utab60 : ℕ :=
  0 + 2 ^ 256 *
  (665952636926298946699888446771560448)

@[expose] def chk60 : Bool :=
  checkE2 (D 6 (by decide) (by decide) 0) 10 false [1, 2, 4, 8, 16, 260, 279] [279] tab60 &&
  checkC9 (D 6 (by decide) (by decide) 0) 198 34 17 96 utab60 [(279, 0)]

end CFSG.ComponentClassification.HSFLit.KD8c
