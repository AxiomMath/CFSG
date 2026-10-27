module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S10J
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Statements
public import Certificates.Certificate12952
public import Certificates.Certificate14951
public import Certificates.Certificate5952
public import Certificates.Certificate17027

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

theorem g23_four : g23 4 = 0 := by decide +kernel

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

theorem u_mem_P_of {u : G} (hu : u ∈ centerOf (baum S)) (huZ : u ∉ centerOf (borelP M L)) :
    u ∈ borelP M L := by
  rcases X.exists_w_of_Z hu huZ with h | h
  · rw [h]
    exact X.iV_mem_P g1_four
  · rw [h]
    exact X.iV_mem_P g23_four

end Sec

theorem lemma2_4_29_10
    (h247 : Lemma2_4_27) (h245_4 : Lemma245_4) (hC54 : LemmaC54_3)
    (h314 : A314A5Excluded) : Lemma2_4_29_10 := by
  intro G _ _ T M H S L cfg z u K s9
  obtain ⟨C, ⟨X⟩⟩ := a5_exists_sec h247 h245_4 hC54 h314 cfg
  have s7 : A5Step7 T M H S L z u := s9.toA5Step7
  have hzz : z = C.zU := X.z_eq s7.z_gen
  have hu2 : u ^ 2 = 1 := cfg.cs.block.1.1.2.2.1.2 u s7.u_U
  have huP : u ∈ borelP M L := X.u_mem_P_of s7.u_mem s7.u_not
  exact
    { toA5Step9 := s9
      u_mem_P := huP
      IS_norm := C.IS_norm
      IS_inf := X.IS_inf
      trans_P := fun v hv w hw hvZ hwZ hv2 hw2 => X.trans_P hv hw hvZ hwZ hv2 hw2
      sl23_core := fun Y c hY hYM hcM => X.sl23_core hY hYM hcM
      dichotomy := fun i hiM hiIS hi2 => by
        rcases X.dichotomy_aux hiM hiIS hi2 huP s7.u_not hu2 with
          ⟨Y, c, hYc, hY, hc, hzY⟩ | hconj
        · exact Or.inl ⟨Y, c, hYc, hY, hc, by rw [hzz]; exact hzY⟩
        · exact Or.inr hconj
      j_exists := by
        obtain ⟨j, hjT, hjS, hj2⟩ := X.exists_j
        exact ⟨j, hjT, hjS, by rw [hj2, hzz]⟩ }

end CFSG.QuasithinUnique.A5
