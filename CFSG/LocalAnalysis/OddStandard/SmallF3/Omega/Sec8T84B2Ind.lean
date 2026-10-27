module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011Au
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8SConjO
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A1Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace B89

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Induces (B : Subgroup G) (y : G) (α : MulAut ↥B) : Prop :=
  ∀ b : ↥B, ((α b : ↥B) : G) = y * b * y⁻¹

namespace Induces

variable {B : Subgroup G} {y y' : G} {α α' : MulAut ↥B}

theorem one (B : Subgroup G) : Induces B 1 1 := fun b => by simp

theorem mul (h : Induces B y α) (h' : Induces B y' α') : Induces B (y * y') (α * α') := by
  intro b
  rw [MulAut.mul_apply, h, h']
  group

theorem inv (h : Induces B y α) : Induces B y⁻¹ α⁻¹ := by
  intro b
  have h1 := h (α⁻¹ b)
  rw [MulAut.apply_inv_self] at h1
  calc ((α⁻¹ b : ↥B) : G) = y⁻¹ * (y * ((α⁻¹ b : ↥B) : G) * y⁻¹) * y := by group
    _ = y⁻¹ * (b : G) * y⁻¹⁻¹ := by rw [← h1]; group

theorem pow (h : Induces B y α) (k : ℕ) : Induces B (y ^ k) (α ^ k) := by
  induction k with
  | zero => simpa using one B
  | succ k ih => simpa [pow_succ] using ih.mul h

theorem mem_normalizer (h : Induces B y α) : y ∈ normalizer (B : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    rw [← h ⟨b, hb⟩]
    exact (α ⟨b, hb⟩).2
  · intro hb
    have h2 := h.inv ⟨y * b * y⁻¹, hb⟩
    have h3 : (y⁻¹ * (y * b * y⁻¹) * y⁻¹⁻¹ : G) = b := by group
    rw [h3] at h2
    rw [← h2]
    exact (α⁻¹ ⟨y * b * y⁻¹, hb⟩).2

theorem eq_conjAut (h : Induces B y α) : α = sec1011_conjAut B y h.mem_normalizer :=
  MulEquiv.ext fun b => Subtype.ext (by rw [h b]; rfl)

end Induces

theorem induces_conjAut (B : Subgroup G) {y : G} (hy : y ∈ normalizer (B : Set G)) :
    Induces B y (sec1011_conjAut B y hy) := fun b => sec1011_conjAut_apply B hy b

theorem exists_induces {H Y : Subgroup G} {α : MulAut ↥Y} (hα : α ∈ autIn H Y) :
    ∃ m ∈ H, Induces Y m α := by
  obtain ⟨m, hmH, hm, rfl⟩ := sec1011_exists_conjAut hα
  exact ⟨m, hmH, induces_conjAut Y hm⟩

theorem mem_autIn_of_induces {H Y : Subgroup G} {m : G} {α : MulAut ↥Y} (hm : m ∈ H)
    (h : Induces Y m α) : α ∈ autIn H Y := by
  rw [h.eq_conjAut]
  exact sec1011_conjAut_mem hm h.mem_normalizer

theorem autIn_mono {H K Y : Subgroup G} (h : H ≤ K) : autIn H Y ≤ autIn K Y := by
  intro α hα
  obtain ⟨m, hmH, hI⟩ := exists_induces hα
  exact mem_autIn_of_induces (h hmH) hI

variable [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B E : Subgroup G}

theorem O_comm_A (h8A : Asc82Lemma8A) (hctx : Sec8Ctx G t L S z g B) {o a : G}
    (ho : o ∈ oddCoreIn (Nsub8 t B)) (ha : a ∈ Asub8 t B) : o * a = a * o := by
  have h : o ∈ centralizer (Asub8 t B : Set G) := by
    rw [sec8t84a1_centA h8A hctx]
    exact Subgroup.mem_sup_right ho
  exact (Subgroup.mem_centralizer_iff.mp h a ha).symm

theorem exists_lift (h8A : Asc82Lemma8A) (hE : Sec8E G t L S z g B E) {α : MulAut ↥B}
    (hα : α ∈ autIn (centralizer ({t} : Set G)) B) :
    ∃ x ∈ normalizer (E : Set G) ⊓ centralizer ({t} : Set G), Induces B x α := by
  obtain ⟨y, hyCt, hI⟩ := exists_induces hα
  have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hyCt
  obtain ⟨o, hoO, hoXy⟩ := sec8s_conj_oddCore hE hyt hI.mem_normalizer
  have hot : o * t = t * o := O_comm_A h8A hE.ctx hoO sec8t84a1_t_mem_A
  have hot' : o⁻¹ * t = t * o⁻¹ := by
    calc o⁻¹ * t = o⁻¹ * (t * o) * o⁻¹ := by group
      _ = o⁻¹ * (o * t) * o⁻¹ := by rw [hot]
      _ = t * o⁻¹ := by group
  refine ⟨o⁻¹ * y, ⟨hoXy, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, ?_⟩
  · calc o⁻¹ * y * t = o⁻¹ * (y * t) := by group
      _ = o⁻¹ * (t * y) := by rw [hyt]
      _ = (o⁻¹ * t) * y := by group
      _ = (t * o⁻¹) * y := by rw [hot']
      _ = t * (o⁻¹ * y) := by group
  · intro b
    rw [hI b]
    have hybB : y * (b : G) * y⁻¹ ∈ B := by rw [← hI b]; exact (α b).2
    have hcomm : o * (y * (b : G) * y⁻¹) = (y * (b : G) * y⁻¹) * o :=
      O_comm_A h8A hE.ctx hoO (sec8t84a1_B_le_A hybB)
    calc y * (b : G) * y⁻¹ = o⁻¹ * (o * (y * (b : G) * y⁻¹)) := by group
      _ = o⁻¹ * ((y * (b : G) * y⁻¹) * o) := by rw [hcomm]
      _ = (o⁻¹ * y) * b * (o⁻¹ * y)⁻¹ := by group

end B89

end CFSG.OddStandard.SmallF3.Omega
