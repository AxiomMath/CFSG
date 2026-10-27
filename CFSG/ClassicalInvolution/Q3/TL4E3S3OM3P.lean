module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM3
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1M
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1LS
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1UH

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O

theorem model1524Twin3Om_proved :
    Model1524Twin3Om :=
  model1524Twin3Om_of_centTag fun S _ _ t n ht hS => by
    rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h | h | h
    · exact sigmaFixOm3_PSp hS
    · exact sigmaFixOm3_PSL hS
    · exact U4M.sigmaFixOm3_PSU hS
    · exact OM3.sigmaFixOm3_orthBad3 (Or.inl h) hS
    · exact OM3.sigmaFixOm3_orthBad3 (Or.inr (Or.inl h)) hS
    · exact OM3.sigmaFixOm3_orthBad3 (Or.inr (Or.inr h)) hS

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O
