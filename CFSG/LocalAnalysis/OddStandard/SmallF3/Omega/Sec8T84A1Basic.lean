module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Statements
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SD1
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L67a
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}

theorem sec8t84a1_t_mem_A : t ∈ Asub8 t B := by
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)

theorem sec8t84a1_B_le_A : B ≤ Asub8 t B := by
  exact le_sup_right

theorem sec8t84a1_t_comm (hctx : Sec8Ctx G t L S z g B) {b : G} (hb : b ∈ B) :
    t * b = b * t := by
  exact sec9d_t_B hctx.toSec8Base hb

theorem sec8t84a1_t_not_mem_B (hctx : Sec8Ctx G t L S z g B) : t ∉ B := by
  intro htB
  exact sec9d_t_not_mem hctx.toSec8Base ((hctx.B_le htB).1)

theorem sec8t84a1_A_elem (hctx : Sec8Ctx G t L S z g B) : IsElemAb2 (Asub8 t B) 5 := by
  obtain ⟨hAel, hAcard⟩ := sec67_card_sup_zpowers (E := B) (x := t) hctx.B_e16.1
    hctx.toSec3SettingLB.involution (sec8t84a1_t_not_mem_B hctx)
    (fun e he => (sec8t84a1_t_comm hctx he).symm)
  rw [Asub8, sup_comm]
  exact ⟨hAel, by rw [hAcard, hctx.B_e16.2]; norm_num⟩

theorem sec8t84a1_A_le_N : Asub8 t B ≤ Nsub8 t B := by
  exact Subgroup.le_normalizer

theorem sec8t84a1_A_le_centB (hctx : Sec8Ctx G t L S z g B) :
    Asub8 t B ≤ centralizer (B : Set G) := by
  intro a ha
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro b hb
  exact CFSG.Open.IsElemAbelian.comm (sec8t84a1_A_elem hctx).1
    (sec8t84a1_B_le_A hb) ha

theorem sec8t84a1_comm_mem (h8B : Asc82Lemma8B) (hctx : Sec8Ctx G t L S z g B) {n : G}
    (hn : n ∈ Nsub8 t B) : n * t * n⁻¹ * t⁻¹ ∈ B := by
  obtain ⟨b, hb, hb_eq⟩ := (h8B G t L S z g B hctx).1.1 n hn t
    ⟨1, B.one_mem, by rw [mul_one]⟩
  rw [hb_eq]
  have hstep : t * b * t⁻¹ = b := by
    rw [sec8t84a1_t_comm hctx hb]
    group
  rw [hstep]
  exact hb

theorem sec8t84a1_N_le_normalizer (h8B : Asc82Lemma8B) (hctx : Sec8Ctx G t L S z g B) :
    Nsub8 t B ≤ normalizer (B : Set G) := by
  have h2t : ∀ m ∈ Nsub8 t B, ∀ a ∈ cosetSet t B, m * a * m⁻¹ ∈ cosetSet t B :=
    (h8B G t L S z g B hctx).1.1
  have hconj : ∀ m ∈ Nsub8 t B, ∀ b ∈ B, m * b * m⁻¹ ∈ B := by
    intro m hm b hb
    obtain ⟨b₀, hb₀, hb₀eq⟩ := h2t m hm t ⟨1, B.one_mem, by rw [mul_one]⟩
    obtain ⟨b₁, hb₁, hb₁eq⟩ := h2t m hm (t * b) ⟨b, hb, rfl⟩
    have key : m * b * m⁻¹ = (m * t * m⁻¹)⁻¹ * (m * (t * b) * m⁻¹) := by group
    rw [key, hb₀eq, hb₁eq]
    have he : (t * b₀)⁻¹ * (t * b₁) = b₀⁻¹ * b₁ := by group
    rw [he]
    exact B.mul_mem (B.inv_mem hb₀) hb₁
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    exact hconj n hn b hb
  · intro hnb
    have h := hconj n⁻¹ ((Nsub8 t B).inv_mem hn) (n * b * n⁻¹) hnb
    convert h using 1
    group

theorem sec8t84a1_centA (h8A : Asc82Lemma8A) (hctx : Sec8Ctx G t L S z g B) :
    centralizer (Asub8 t B : Set G) = Asub8 t B ⊔ oddCoreIn (Nsub8 t B) := by
  obtain ⟨h1, h2⟩ := h8A G t L S z g B hctx
  exact (h1.trans h2).symm

theorem sec8t84a1_O_le_C (h8A : Asc82Lemma8A) (hctx : Sec8Ctx G t L S z g B) :
    oddCoreIn (Nsub8 t B) ≤ Nsub8 t B ⊓ centralizer (B : Set G) := by
  refine le_inf (oddCoreIn_normal (Nsub8 t B)).1 ?_
  have hO : oddCoreIn (Nsub8 t B) ≤ centralizer (Asub8 t B : Set G) := by
    rw [sec8t84a1_centA h8A hctx]
    exact le_sup_right
  exact hO.trans (Subgroup.centralizer_le (sec8t84a1_B_le_A))

theorem sec8t84a1_AO_le_C (h8A : Asc82Lemma8A) (hctx : Sec8Ctx G t L S z g B) :
    Asub8 t B ⊔ oddCoreIn (Nsub8 t B) ≤ Nsub8 t B ⊓ centralizer (B : Set G) := by
  exact sup_le (le_inf sec8t84a1_A_le_N (sec8t84a1_A_le_centB hctx)) (sec8t84a1_O_le_C h8A hctx)

theorem sec8t84a1_C_normal (h8B : Asc82Lemma8B) (hctx : Sec8Ctx G t L S z g B) :
    ∀ n ∈ Nsub8 t B, ∀ c ∈ Nsub8 t B ⊓ centralizer (B : Set G),
      n * c * n⁻¹ ∈ Nsub8 t B ⊓ centralizer (B : Set G) := by
  have hNnorm : Nsub8 t B ≤ normalizer (B : Set G) := sec8t84a1_N_le_normalizer h8B hctx
  intro n hn c hc
  refine ⟨(Nsub8 t B).mul_mem ((Nsub8 t B).mul_mem hn hc.1) ((Nsub8 t B).inv_mem hn),
    Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro b hb
  set d : G := n⁻¹ * b * n with hddef
  have hd : d ∈ B := by
    rw [hddef]
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp (hNnorm ((Nsub8 t B).inv_mem hn)) b).mp hb
  have hcd : d * c = c * d := Subgroup.mem_centralizer_iff.mp hc.2 d hd
  have hbd : b = n * d * n⁻¹ := by rw [hddef]; group
  calc b * (n * c * n⁻¹)
      = (n * d * n⁻¹) * (n * c * n⁻¹) := by rw [hbd]
    _ = n * (d * c) * n⁻¹ := by group
    _ = n * (c * d) * n⁻¹ := by rw [hcd]
    _ = (n * c * n⁻¹) * b := by rw [hbd]; group

theorem sec8t84a1_O_norm (n : G) (hn : n ∈ Nsub8 t B) :
    ∀ o ∈ oddCoreIn (Nsub8 t B), n * o * n⁻¹ ∈ oddCoreIn (Nsub8 t B) := by
  have hOleN : oddCoreIn (Nsub8 t B) ≤ Nsub8 t B := (oddCoreIn_normal (Nsub8 t B)).1
  have hnormO : Nsub8 t B ≤ normalizer (oddCoreIn (Nsub8 t B) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOleN).mp (oddCoreIn_normal (Nsub8 t B)).2
  intro o ho
  exact (Subgroup.mem_normalizer_iff.mp (hnormO hn) o).mp ho

theorem sec8t84a1_O_odd : Odd (Nat.card (oddCoreIn (Nsub8 t B))) := by
  exact odd_card_oddCoreIn (Nsub8 t B)

theorem sec8t84a1_L_norm_le (hctx : Sec8Ctx G t L S z g B) :
    L ⊓ normalizer (B : Set G) ≤ Nsub8 t B ⊓ centralizer ({t} : Set G) := by
  intro x hx
  have hxt : x * t = t * x := sec9d_comm_t hctx.toSec8Base hx.1
  refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr hxt⟩
  rw [Nsub8]
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  have ht : (↑(MulAut.conj x) : G →* G) t = t := by
    change (MulAut.conj x) t = t
    rw [MulAut.conj_apply, hxt]
    group
  have hBmap : B.map (↑(MulAut.conj x) : G →* G) = B :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hx.2
  rw [Asub8, Subgroup.map_sup, MonoidHom.map_zpowers, ht, hBmap]

end CFSG.OddStandard.SmallF3.Omega
