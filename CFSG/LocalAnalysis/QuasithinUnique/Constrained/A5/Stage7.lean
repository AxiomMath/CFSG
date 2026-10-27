module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S7D
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S7F
public import Certificates.Certificate17037
public import Certificates.Certificate17027
public import Certificates.Certificate5952
public import Certificates.Certificate12952
public import Certificates.Certificate14951

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

theorem z_eq {z : G} (hz : centerOf (borelP M L) = Subgroup.zpowers z) : z = C.zU := by
  have hzP : z ∈ centerOf (borelP M L) := hz ▸ Subgroup.mem_zpowers z
  rcases (X.centerOf_P_iff z).mp hzP with h | h
  · exfalso
    have h1 : C.zU ∈ centerOf (borelP M L) := (X.centerOf_P_iff _).mpr (Or.inr rfl)
    rw [hz, h, Subgroup.zpowers_one_eq_bot] at h1
    exact C.zU_ne_one (Subgroup.mem_bot.mp h1)
  · exact h

theorem step7
    {z u : G} (h6 : A5Step6 T M H S L) (h5 : IsAltType L 5)
    (hz : centerOf (borelP M L) = Subgroup.zpowers z) (hu : u ∈ centerOf (baum S))
    (huZ : u ∉ centerOf (borelP M L)) (hu0 : u = C.u0) : A5Step7 T M H S L z u := by
  have hzz : z = C.zU := X.z_eq hz
  subst hu0
  subst hzz
  obtain ⟨s, hsS, hsR, hs1, -⟩ := X.exists_s
  refine
    { toA5Step6 := h6
      H_eq := X.H_eq h5 h6.CU_eq h6.L_normal
      z_gen := hz
      u_mem := hu
      u_not := huZ
      u_U := C.u0_mem_U
      s_exists := ⟨s, hsS, hsR, ?_⟩
      Hu := X.Hu_iso
      Su := X.Su rfl hu
      R_index := X.R_index
      CU_card := X.CU_card
      CU_conj := fun v hv hv1 hvu => X.CU_conj rfl hv hv1 hvu
      ZR_eq := X.ZR_eq hu
      ZR_norm := C.ZR_norm
      x_exists := X.x_exists hu
      Tu_eq := X.Tu_eq hu
      Tu_index := X.Tu_index hu
      Tu_sylow := X.Tu_sylow hu
      u_not_conj := X.u_not_conj hu
      Gu_gamma2 := X.Gu_gamma2 hu h6.CU_eq }
  rw [hs1, ← mul_assoc, C.u0_mul_self, one_mul]

end Sec

theorem lemma2_4_29_7
    (h247 : Lemma2_4_27) (h245_4 : Lemma245_4) (hC54 : LemmaC54_3)
    (h314 : A314A5Excluded) : Lemma2_4_29_7 := by
  intro G _ _ T M H S L cfg h6 z u hz hu huZ
  obtain ⟨C, ⟨X⟩⟩ := a5_exists_sec h247 h245_4 hC54 h314 cfg
  rcases X.exists_w_of_Z hu huZ with h | h
  · exact X.step7 h6 cfg.alt5 hz hu huZ h
  · let C' : StdCfg T M H S L :=
      C.relabel rho13 (fun σ hσ => rho13_conj_E σ hσ) (fun σ hσ => rho13_conj_E' σ hσ)
    obtain ⟨X'⟩ := exists_sec C' h6.TC_one
    have hu' : u = C'.u0 := by
      rw [h]
      show _ = ((C.iV (vact rho13⁻¹ g1w) : ↥H) : G)
      rw [rho13_inv, vact_rho13_g1w]
    exact X'.step7 h6 cfg.alt5 hz hu huZ hu'

end CFSG.QuasithinUnique.A5
