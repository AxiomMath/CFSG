module

public import CFSG.GH74.Generic.BProg.B3.S3T3C
public import CFSG.GH74.Generic.BProg.B3.S3T3E8
public import CFSG.GH74.Generic.BProg.B3.S3Sec29F

public section

namespace CFSG.GH74.Generic.BProg.B3

variable {G : Type} [Group G] [Finite G]

theorem sec29Final_of_lemma2910 (h : Lemma2910Full G) : Sec29Final G :=
  sec29Final_of_nodes exists_H29 h (lemma2912_proved G) (finalE8_proved G)

end CFSG.GH74.Generic.BProg.B3
