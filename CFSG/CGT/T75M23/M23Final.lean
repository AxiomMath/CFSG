module

public import CFSG.CGT.T75M23.M23PresCert
public import CFSG.CGT.T75M23.L2Cert7

public section

namespace CFSG.CGT.T75M23

theorem r23Statement_of_certificate :
    R23Statement :=
  fun _ _ e hp hK => exists_mulEquiv_m23_of_relations_of_certificate e hp hK

theorem jankoM23CtxInput_of_certificates :
    CFSG.CGT.T75I.JankoM23CtxInput :=
  jankoM23CtxInput_of_parts l2Statement7_of_certificate pStatement7_of_certificate
    r23Statement_of_certificate

end CFSG.CGT.T75M23
