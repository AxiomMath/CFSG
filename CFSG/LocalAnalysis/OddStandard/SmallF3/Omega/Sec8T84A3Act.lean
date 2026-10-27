module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Cl2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A1Basic
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Red
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace A3

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G}
  {B K L1 : Subgroup G}

theorem O_comm_t (h8A : Asc82Lemma8A) (hctx : Sec8Ctx G t L S z g B) {o : G}
    (ho : o ∈ oddCoreIn (Nsub8 t B)) : o * t = t * o := by
  have h : o ∈ centralizer (Asub8 t B : Set G) := by
    rw [sec8t84a1_centA h8A hctx]
    exact Subgroup.mem_sup_right ho
  exact (Subgroup.mem_centralizer_iff.mp h t sec8t84a1_t_mem_A).symm

theorem tauFn_conj {n l l' o : G} (hnt : n * t = t * n) (hot : o * t = t * o)
    (h : n * l * n⁻¹ = l' * o) : tauFn t l' = n * tauFn t l * n⁻¹ := by
  have h1 : n * t * n⁻¹ = t := by rw [hnt]; group
  have h2 : o * t * o⁻¹ = t := by rw [hot]; group
  have e1 : n * tauFn t l * n⁻¹ = (n * l * n⁻¹) * t * (n * l * n⁻¹)⁻¹ * t⁻¹ := by
    unfold tauFn
    calc n * (l * t * l⁻¹ * t⁻¹) * n⁻¹
        = (n * l * n⁻¹) * (n * t * n⁻¹) * (n * l * n⁻¹)⁻¹ * (n * t * n⁻¹)⁻¹ := by group
      _ = (n * l * n⁻¹) * t * (n * l * n⁻¹)⁻¹ * t⁻¹ := by rw [h1]
  rw [e1, h]
  unfold tauFn
  calc l' * t * l'⁻¹ * t⁻¹ = l' * (o * t * o⁻¹) * l'⁻¹ * t⁻¹ := by rw [h2]
    _ = l' * o * t * (l' * o)⁻¹ * t⁻¹ := by group

theorem sq_conj {N O : Subgroup G} {n l l' o : G} (hOB : ∀ x ∈ B, x ∈ O → x = 1)
    (hOn : ∀ m ∈ N, ∀ x ∈ O, m * x * m⁻¹ ∈ O) (hl'N : l' ∈ N) (ho : o ∈ O)
    (h1 : l' * l' ∈ B) (h2 : n * (l * l) * n⁻¹ ∈ B) (h : n * l * n⁻¹ = l' * o) :
    l' * l' = n * (l * l) * n⁻¹ := by
  have e : n * (l * l) * n⁻¹ = (l' * l') * ((l'⁻¹ * o * l') * o) := by
    calc n * (l * l) * n⁻¹ = (n * l * n⁻¹) * (n * l * n⁻¹) := by group
      _ = (l' * o) * (l' * o) := by rw [h]
      _ = (l' * l') * ((l'⁻¹ * o * l') * o) := by group
  have hu : l'⁻¹ * o * l' ∈ O := by
    have := hOn l'⁻¹ (N.inv_mem hl'N) o ho
    simpa using this
  have hw : (l'⁻¹ * o * l') * o ∈ O := O.mul_mem hu ho
  have hwB : (l'⁻¹ * o * l') * o ∈ B := by
    have e2 : (l' * l')⁻¹ * (n * (l * l) * n⁻¹) = (l'⁻¹ * o * l') * o := by rw [e]; group
    rw [← e2]
    exact B.mul_mem (B.inv_mem h1) h2
  rw [e, hOB _ hwB hw, mul_one]

theorem setup (hctx : Sec8Ctx G t L S z g B) (h : Sec8T84L1 G t L S z g B K L1) :
    RedAct.Setup (Nsub8 t B) (oddCoreIn (Nsub8 t B)) L1 where
  O_le := (oddCoreIn_normal (Nsub8 t B)).1
  V_le := fun x hx => (h.K_data.le_C (h.le hx)).1
  O_norm := fun n hn o ho => sec8t84a1_O_norm n hn o ho
  inf := RedAct.inf_of_card_two_pow (k := 8) h.card sec8t84a1_O_odd
  inv := h.inv

theorem B_inf_O (hctx : Sec8Ctx G t L S z g B) :
    ∀ x ∈ B, x ∈ oddCoreIn (Nsub8 t B) → x = 1 :=
  RedAct.inf_of_card_two_pow (k := 4) hctx.B_e16.2 sec8t84a1_O_odd

theorem rho_on_B (hctx : Sec8Ctx G t L S z g B) (h : Sec8T84L1 G t L S z g B K L1)
    (n : ↥(Nsub8 t B)) (hn : (n : G) ∈ normalizer (B : Set G)) (b : ↥L1) (hb : (b : G) ∈ B) :
    ((RedAct.redHom (setup hctx h) n b : ↥L1) : G) = (n : G) * b * (n : G)⁻¹ := by
  have hmem : (n : G) * b * (n : G)⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hn b).mp hb
  have := RedAct.redHom_eq_of (setup hctx h) n b ⟨(n : G) * b * (n : G)⁻¹, h.B_le hmem⟩
    (o := 1) (oddCoreIn (Nsub8 t B)).one_mem (by simp)
  rw [this]

theorem tauFn_rho (h8A : Asc82Lemma8A) (hctx : Sec8Ctx G t L S z g B)
    (h : Sec8T84L1 G t L S z g B K L1) (n : ↥(Nsub8 t B)) (hnt : (n : G) * t = t * (n : G))
    (l : ↥L1) :
    tauFn t ((RedAct.redHom (setup hctx h) n l : ↥L1) : G) =
      (n : G) * tauFn t (l : G) * (n : G)⁻¹ := by
  obtain ⟨o, ho, hspec⟩ := RedAct.redHom_spec (setup hctx h) n l
  exact tauFn_conj hnt (O_comm_t h8A hctx ho) hspec

theorem rho_sq (hctx : Sec8Ctx G t L S z g B) (h : Sec8T84L1 G t L S z g B K L1)
    (n : ↥(Nsub8 t B)) (hn : (n : G) ∈ normalizer (B : Set G)) (l : ↥L1) :
    ((RedAct.redHom (setup hctx h) n l : ↥L1) : G) *
        ((RedAct.redHom (setup hctx h) n l : ↥L1) : G) =
      (n : G) * ((l : G) * l) * (n : G)⁻¹ := by
  obtain ⟨o, ho, hspec⟩ := RedAct.redHom_spec (setup hctx h) n l
  have hv : ((RedAct.redHom (setup hctx h) n l : ↥L1) : G) ∈ L1 :=
    (RedAct.redHom (setup hctx h) n l).2
  have hl'N : ((RedAct.redHom (setup hctx h) n l : ↥L1) : G) ∈ Nsub8 t B :=
    (setup hctx h).V_le hv
  have h1 : ((RedAct.redHom (setup hctx h) n l : ↥L1) : G) *
      ((RedAct.redHom (setup hctx h) n l : ↥L1) : G) ∈ B :=
    h.K_data.sq_le _ (h.le hv)
  have h2 : (n : G) * ((l : G) * l) * (n : G)⁻¹ ∈ B :=
    (Subgroup.mem_normalizer_iff.mp hn _).mp (h.K_data.sq_le _ (h.le l.2))
  exact sq_conj (N := Nsub8 t B) (O := oddCoreIn (Nsub8 t B)) (B_inf_O hctx)
    (fun m hm x hx => sec8t84a1_O_norm m hm x hx) hl'N ho h1 h2 hspec

end A3

end CFSG.OddStandard.SmallF3.Omega
