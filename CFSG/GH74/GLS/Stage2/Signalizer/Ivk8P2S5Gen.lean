module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Def
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.BenderProof
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Naturality

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

section Conj

variable {G : Type} [Group G]

@[expose] def cj (b : G) (X : Subgroup G) : Subgroup G := X.map (MulAut.conj b).toMonoidHom

theorem mem_cj {b : G} {X : Subgroup G} {x : G} : x ∈ cj b X ↔ b⁻¹ * x * b ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨b⁻¹ * x * b, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem cj_cj_inv (b : G) (X : Subgroup G) : cj b⁻¹ (cj b X) = X := by
  ext x
  rw [mem_cj, mem_cj]
  simp [mul_assoc]

theorem cj_inj {b : G} {X Y : Subgroup G} (h : cj b X = cj b Y) : X = Y := by
  have := congrArg (cj b⁻¹) h
  rwa [cj_cj_inv, cj_cj_inv] at this

theorem cj_bot (b : G) : cj b (⊥ : Subgroup G) = ⊥ := Subgroup.map_bot _

theorem cj_top (b : G) : cj b (⊤ : Subgroup G) = ⊤ := by
  ext x
  rw [mem_cj]
  simp

theorem cj_inf (b : G) (X Y : Subgroup G) : cj b (X ⊓ Y) = cj b X ⊓ cj b Y :=
  Subgroup.map_inf_eq _ _ _ (MulAut.conj b).injective

theorem cj_self_of_mem {b : G} {M : Subgroup G} (hb : b ∈ M) : cj b M = M := by
  ext x
  rw [mem_cj]
  constructor
  · intro h
    have := M.mul_mem (M.mul_mem hb h) (M.inv_mem hb)
    simpa [mul_assoc] using this
  · intro hx
    exact M.mul_mem (M.mul_mem (M.inv_mem hb) hx) hb

theorem card_cj [Finite G] (b : G) (X : Subgroup G) : Nat.card ↥(cj b X) = Nat.card ↥X :=
  Subgroup.card_map_of_injective (MulAut.conj b).injective

theorem cj_eq_of_le [Finite G] {b : G} {X : Subgroup G} (h : cj b X ≤ X) : cj b X = X :=
  Subgroup.eq_of_le_of_card_ge h (le_of_eq (card_cj b X).symm)

theorem mem_normalizer_of_cj_eq {b : G} {X : Subgroup G} (h : cj b X = X) :
    b ∈ normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 : b * x * b⁻¹ ∈ cj b X ↔ x ∈ X := by
    rw [mem_cj]
    simp [mul_assoc]
  rw [h] at h1
  exact h1.symm

theorem cj_eq_of_mem_normalizer {b : G} {X : Subgroup G} (h : b ∈ normalizer (X : Set G)) :
    cj b X = X := by
  ext x
  rw [mem_cj]
  have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ h)) x
  simpa [mul_assoc] using this.symm

theorem cj_iSup {ι : Sort*} (b : G) (S : ι → Subgroup G) : cj b (⨆ i, S i) = ⨆ i, cj b (S i) :=
  Subgroup.map_iSup _ _

theorem cj_centralizer (b d : G) :
    cj b (centralizer ({d} : Set G)) = centralizer ({b * d * b⁻¹} : Set G) := by
  ext x
  rw [mem_cj, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg (fun y => b * y * b⁻¹) h
    simpa [mul_assoc] using this
  · intro h
    have := congrArg (fun y => b⁻¹ * y * b) h
    simpa [mul_assoc] using this

theorem mem_normalizer_of_forall_conj [Finite G] {b : G} {X : Subgroup G}
    (h : ∀ y ∈ X, b * y * b⁻¹ ∈ X) : b ∈ normalizer (X : Set G) := by
  refine mem_normalizer_of_cj_eq (cj_eq_of_le ?_)
  rintro _ ⟨y, hy, rfl⟩
  simpa [MulAut.conj_apply] using h y hy

theorem Fpi_cj [Finite G] (σ : Set ℕ) (b : G) (N : Subgroup G) :
    Fpi σ (cj b N) = cj b (Fpi σ N) := by
  unfold Fpi cj
  rw [Subgroup.map_iSup]
  congr 1
  funext p
  rw [Subgroup.map_iSup]
  congr 1
  funext hp
  rw [CFSG.GH74.GLS.Stage2.Bender.Thm1.BenderProof.Fm_map (MulAut.conj b) N,
    CFSG.GH74.GLS.Stage2.Bender.Thm2.Op_map p (MulAut.conj b) (Fm N)]

theorem cj_commutator (b : G) (X Y : Subgroup G) : cj b ⁅X, Y⁆ = ⁅cj b X, cj b Y⁆ :=
  Subgroup.map_commutator _ _ _

theorem cj_zpowers {b z : G} (hbz : b * z * b⁻¹ = z) : cj b (zpowers z) = zpowers z := by
  unfold cj
  rw [MonoidHom.map_zpowers]
  simp [MulAut.conj_apply, hbz]

theorem cj_mem_XfamR [Finite G] {z : G} {M V X : Subgroup G} (hMz : M = centralizer {z}) {b : G}
    (hb : b ∈ M) (hX : X ∈ XfamR z M V)
    (hV : ∀ v ∈ V, b⁻¹ * v * b ∈ normalizer (X : Set G)) : cj b X ∈ XfamR z M V := by
  obtain ⟨hbot, htop, hVX, hXz, hF1, hF2⟩ := hX
  have hbz : b * z * b⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.1 (hMz ▸ hb : b ∈ centralizer ({z} : Set G))
    calc b * z * b⁻¹ = z * b * b⁻¹ := by rw [this]
      _ = z := by group
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hbot (cj_inj (h.trans (cj_bot b).symm))
  · intro h
    exact htop (cj_inj (h.trans (cj_top b).symm))
  · intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [mem_cj, mem_cj]
    have := Subgroup.mem_normalizer_iff.1 (hV v hv) (b⁻¹ * h * b)
    rw [this]
    have e : b⁻¹ * (v * h * v⁻¹) * b = (b⁻¹ * v * b) * (b⁻¹ * h * b) * (b⁻¹ * v * b)⁻¹ := by
      group
    rw [e]
  · calc ⁅cj b X, zpowers z⁆ = ⁅cj b X, cj b (zpowers z)⁆ := by rw [cj_zpowers hbz]
      _ = cj b ⁅X, zpowers z⁆ := (cj_commutator b X _).symm
      _ = cj b X := by rw [hXz]
  · rw [Fpi_cj]
    have h1 : cj b (Fpi (piF' M) X ⊓ M) = cj b (Fpi (piF' M) X) ⊓ M := by
      rw [cj_inf, cj_self_of_mem hb]
    rw [← h1, hF1, cj_bot]
  · rw [Fpi_cj]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyM : y ∈ M := hF2 hy
    have := M.mul_mem (M.mul_mem hb hyM) (M.inv_mem hb)
    simpa [MulAut.conj_apply] using this

end Conj

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
