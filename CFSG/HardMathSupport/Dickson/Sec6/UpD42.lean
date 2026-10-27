module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Alt
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Glue
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Reduction
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.OutL2
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.OutUnitary
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.OutSymplectic
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.OutD4
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.OutSuzuki
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.OutTriality
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.OutExc
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.OutTwE6

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie

theorem upD42Chev2Out_of_exceptional
    (hExc : UpD42Chev2Out (fun d => FamG2 d ∨ FamF4 d ∨ FamE7 d ∨ FamE8 d))
    (hE6 : UpD42Chev2Out
      (fun d => match d with | .E6 _ | .twistedE6 _ => True | _ => False))
    (hReeF4 : UpD42Chev2Out FamReeF4) (hTits : UpD42Chev2Out FamTits) :
    UpD42Chev2Out (fun _ => True) := by
  intro S _ _ hs hnab ⟨d, hv⟩ _ hc he α hα hp
  cases d with
  | A r q =>
    exact upD42Chev2Out_linear_holds S hs hnab ⟨.A r q, hv⟩ trivial hc he α hα hp
  | twistedA r q =>
    exact upD42Chev2Out_unitary_holds S hs hnab ⟨.twistedA r q, hv⟩ trivial hc he α hα hp
  | B r q =>
    exact upD42Chev2Out_symplectic_holds S hs hnab ⟨.B r q, hv⟩ (Or.inr hc) hc he α hα hp
  | C r q =>
    exact upD42Chev2Out_symplectic_holds S hs hnab ⟨.C r q, hv⟩ trivial hc he α hα hp
  | D r q =>
    by_cases hr : r = 4
    · exact upD42Chev2Out_d4_holds S hs hnab ⟨.D r q, hv⟩ hr hc he α hα hp
    · exact upD42Chev2Out_orthogonal_holds S hs hnab ⟨.D r q, hv⟩ hr hc he α hα hp
  | twistedD r q =>
    exact upD42Chev2Out_orthogonal_holds S hs hnab ⟨.twistedD r q, hv⟩
      trivial hc he α hα hp
  | E6 q => exact hE6 S hs hnab ⟨.E6 q, hv⟩ trivial hc he α hα hp
  | twistedE6 q => exact hE6 S hs hnab ⟨.twistedE6 q, hv⟩ trivial hc he α hα hp
  | G2 q => exact hExc S hs hnab ⟨.G2 q, hv⟩ (Or.inl trivial) hc he α hα hp
  | F4 q => exact hExc S hs hnab ⟨.F4 q, hv⟩ (Or.inr (Or.inl trivial)) hc he α hα hp
  | E7 q =>
    exact hExc S hs hnab ⟨.E7 q, hv⟩ (Or.inr (Or.inr (Or.inl trivial))) hc he α hα hp
  | E8 q =>
    exact hExc S hs hnab ⟨.E8 q, hv⟩ (Or.inr (Or.inr (Or.inr trivial))) hc he α hα hp
  | trialityD4 q =>
    exact upD42Chev2Out_triality_holds S hs hnab ⟨.trialityD4 q, hv⟩
      trivial hc he α hα hp
  | suzuki m =>
    exact upD42Chev2Out_suzuki_holds S hs hnab ⟨.suzuki m, hv⟩ trivial hc he α hα hp
  | reeG2 _ => exact hc.elim
  | reeF4 m => exact hReeF4 S hs hnab ⟨.reeF4 m, hv⟩ trivial hc he α hα hp
  | tits => exact hTits S hs hnab ⟨.tits, hv⟩ trivial hc he α hα hp

section FiniteCertificates


theorem upD42Chev2Out_of_certificates : UpD42Chev2Out (fun _ => True) :=
  upD42Chev2Out_of_exceptional upD42Chev2Out_exc_holds upD42Chev2Out_e6_holds
    upD42Chev2Out_reeF4 upD42Chev2Out_tits

theorem upD42Chev2Leaf_of_certificates : UpD42Chev2Leaf :=
  upD42Chev2Leaf_of_inn_out upD42Chev2Inn_holds upD42Chev2Out_of_certificates

end FiniteCertificates

theorem upD42Statement_of_leaves (hSpor : UpD42SporLeaf) (hOdd : UpD42OddLeaf)
    (hChev2 : UpD42Chev2Leaf) : UpD42Statement :=
  upD42Statement_of_core (upD42Core_of_leaves upD42AltLeaf_holds hSpor hOdd hChev2)

end CFSG.HardMathSupport.Dickson.Sec6

end
