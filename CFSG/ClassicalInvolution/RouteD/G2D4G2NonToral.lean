module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Class

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Conj

theorem sup_centralizer_conj_eq_top_iff {G : Type*} [Group G] (g u v : G) :
    Subgroup.centralizer ({g * u * g⁻¹} : Set G) ⊔ Subgroup.centralizer ({g * v * g⁻¹} : Set G) =
        ⊤ ↔
      Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({v} : Set G) = ⊤ := by
  rw [← conjSub_centralizer_singleton_g2d4, ← conjSub_centralizer_singleton_g2d4,
    ← Subgroup.map_sup]
  constructor
  · intro h
    exact Subgroup.map_injective (MulAut.conj g).injective
      (h.trans (Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective).symm)
  · intro h
    rw [h]
    exact Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective

end Conj

section Ambient

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem torusGroup_mul_comm {t s : ModGL Tag.G2 F} (ht : t ∈ torusGroup Tag.G2 F)
    (hs : s ∈ torusGroup Tag.G2 F) : t * s = s * t := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hs
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

theorem centralizer_sup_eq_top_g2_large (hodd : Odd (Nat.card F)) (h11 : 11 ≤ Nat.card F)
    {z z' : ↥(adjointGroup Tag.G2 F)} (hz : z * z = 1) (hz' : z' * z' = 1) (hz1 : z ≠ 1)
    (hz1' : z' ≠ 1) (hne : z ≠ z') (hcomm : z * z' = z' * z) :
    Subgroup.centralizer ({z} : Set ↥(adjointGroup Tag.G2 F)) ⊔
      Subgroup.centralizer ({z'} : Set ↥(adjointGroup Tag.G2 F)) = ⊤ := by
  obtain ⟨a, ha⟩ : ∃ a : Fin Tag.G2.rank → Fˣ, a = ![-1, 1] := ⟨_, rfl⟩
  obtain ⟨hasq, hane, -⟩ := g2_toral_data_a1 (F := F) hodd ha
  have hda : rootDiagUnit Tag.G2 a ∈ torusGroup Tag.G2 F := g2_rootDiagUnit_mem_torusGroup a
  have hdK : rootDiagUnit Tag.G2 a ∈ adjointGroup Tag.G2 F :=
    (mem_toralCentralizer.mp (torusGroup_le_toralCentralizer a hda)).1
  set d₁ : ↥(adjointGroup Tag.G2 F) := ⟨_, hdK⟩ with hd₁
  have hd₁2 : d₁ * d₁ = 1 := by
    apply Subtype.ext
    show rootDiagUnit Tag.G2 a * rootDiagUnit Tag.G2 a = 1
    rw [← rootDiagUnit_mul, ← rootDiagUnit_one]
    congr 1
    funext i
    rcases hasq i with h | h <;> simp [h]
  have hd₁1 : d₁ ≠ 1 := by
    intro h
    have h' : rootDiagUnit Tag.G2 a = 1 := congrArg Subtype.val h
    rw [← rootDiagUnit_one] at h'
    exact hane (rootDiagUnit_injective h')
  obtain ⟨h, hh⟩ := g2_involutions_conj hodd hz hd₁2 hz1 hd₁1
  set w : ↥(adjointGroup Tag.G2 F) := h * z' * h⁻¹ with hw
  have hw2 : w * w = 1 := by
    calc w * w = h * (z' * z') * h⁻¹ := by rw [hw]; group
      _ = 1 := by rw [hz']; group
  have hw1 : w ≠ 1 := by
    intro h0
    apply hz1'
    calc z' = h⁻¹ * (h * z' * h⁻¹) * h := by group
      _ = 1 := by rw [← hw, h0]; group
  have hwd : w ≠ d₁ := by
    intro h0
    apply hne
    rw [← hh] at h0
    have : h * z' * h⁻¹ = h * z * h⁻¹ := h0
    calc z = h⁻¹ * (h * z * h⁻¹) * h := by group
      _ = h⁻¹ * (h * z' * h⁻¹) * h := by rw [this]
      _ = z' := by group
  have hdw : d₁ * w = w * d₁ := by
    rw [← hh, hw]
    calc h * z * h⁻¹ * (h * z' * h⁻¹) = h * (z * z') * h⁻¹ := by group
      _ = h * (z' * z) * h⁻¹ := by rw [hcomm]
      _ = h * z' * h⁻¹ * (h * z * h⁻¹) := by group
  have hwX : (w : ModGL Tag.G2 F) ∈ toralCentralizer Tag.G2 F a := by
    rw [mem_toralCentralizer]
    refine ⟨w.2, ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    exact congrArg Subtype.val hdw
  obtain ⟨x, hxX, t, ht, hx⟩ := exists_conj_to_torus_mul hodd ha hwX
    (congrArg Subtype.val hw2) (fun h0 => hw1 (Subtype.ext h0))
    (fun h0 => hwd (Subtype.ext h0))
  have htK : t ∈ adjointGroup Tag.G2 F :=
    (mem_toralCentralizer.mp (torusGroup_le_toralCentralizer a ht)).1
  have hm₀K : g2ChartA F WSL * g2ChartB F WSL ∈ adjointGroup Tag.G2 F :=
    mul_mem (g2ChartA_mem WSL) (g2ChartB_mem WSL)
  set y : ↥(adjointGroup Tag.G2 F) := ⟨t * (g2ChartA F WSL * g2ChartB F WSL),
    mul_mem htK hm₀K⟩ with hy
  have hinv : ∀ s ∈ torusGroup Tag.G2 F, (y : ModGL Tag.G2 F) * s * (y : ModGL Tag.G2 F)⁻¹ =
      s⁻¹ := by
    intro s hs
    have hs' : s⁻¹ ∈ torusGroup Tag.G2 F := inv_mem hs
    have hm := g2_m0_inverts (F := F) hs
    calc (y : ModGL Tag.G2 F) * s * (y : ModGL Tag.G2 F)⁻¹
        = t * ((g2ChartA F WSL * g2ChartB F WSL) * s * (g2ChartA F WSL * g2ChartB F WSL)⁻¹) *
            t⁻¹ := by
          show t * (g2ChartA F WSL * g2ChartB F WSL) * s *
            (t * (g2ChartA F WSL * g2ChartB F WSL))⁻¹ = _
          group
      _ = t * s⁻¹ * t⁻¹ := by rw [hm]
      _ = s⁻¹ := by rw [torusGroup_mul_comm ht hs']; group
  have hd₁val : (d₁ : ModGL Tag.G2 F) = rootDiagUnit Tag.G2 ![-1, 1] := by
    show rootDiagUnit Tag.G2 a = _
    rw [ha]
  have hgen := centralizer_sup_eq_top_of_inverting hodd h11 hd₁val hinv
  set x' : ↥(adjointGroup Tag.G2 F) := ⟨x, (mem_toralCentralizer.mp hxX).1⟩ with hx'
  have hyx : x' * w * x'⁻¹ = y := by
    apply Subtype.ext
    exact hx
  have hxd : x' * d₁ * x'⁻¹ = d₁ := by
    apply Subtype.ext
    have h1 := (mem_toralCentralizer.mp hxX).2
    rw [mul_inv_eq_iff_eq_mul] at h1
    show x * rootDiagUnit Tag.G2 a * x⁻¹ = rootDiagUnit Tag.G2 a
    rw [mul_inv_eq_iff_eq_mul]
    exact h1.symm
  have hX : Subgroup.centralizer ({d₁} : Set ↥(adjointGroup Tag.G2 F)) ⊔
      Subgroup.centralizer ({w} : Set ↥(adjointGroup Tag.G2 F)) = ⊤ := by
    apply (sup_centralizer_conj_eq_top_iff x' d₁ w).mp
    rw [hxd, hyx]
    exact hgen
  apply (sup_centralizer_conj_eq_top_iff h z z').mp
  rw [hh]
  exact hX

end Ambient

section Model

variable {p e : ℕ} [Fact p.Prime]

theorem g2NonToralGenerate_large (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .G2 0 p e)
    (h11 : 11 ≤ p ^ e) (z z' : (modelUniv .G2 0 p e Fact.out).K) (hz : z * z = 1)
    (hz' : z' * z' = 1) (hz1 : z ≠ 1) (hz1' : z' ≠ 1) (hne : z ≠ z') (hcomm : z * z' = z' * z) :
    Subgroup.centralizer ({z} : Set (modelUniv .G2 0 p e Fact.out).K) ⊔
      Subgroup.centralizer ({z'} : Set (modelUniv .G2 0 p e Fact.out).K) = ⊤ := by
  have he : e ≠ 0 := by have := hadm.2.1; omega
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he
  have hodd : Odd (Nat.card (GaloisField p e)) := by
    rw [hcard]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have : Finite (GaloisField p e) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (pow_pos (Fact.out : p.Prime).pos e).ne')
  exact centralizer_sup_eq_top_g2_large (F := GaloisField p e) hodd (by rw [hcard]; exact h11)
    hz hz' hz1 hz1' hne hcomm

@[expose] def G2NonToralGenerateSmall (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ e : ℕ, StatedLieAdmissible .G2 0 p e → p ≠ 2 → 5 ≤ p ^ e → p ^ e < 11 →
    ∀ z z' : (modelUniv .G2 0 p e Fact.out).K, z * z = 1 → z' * z' = 1 → z ≠ 1 → z' ≠ 1 →
      z ≠ z' → z * z' = z' * z → ¬ ToralPair (F := GaloisField p e) z z' →
        Subgroup.centralizer ({z} : Set (modelUniv .G2 0 p e Fact.out).K) ⊔
          Subgroup.centralizer ({z'} : Set (modelUniv .G2 0 p e Fact.out).K) = ⊤

theorem g2NonToralGenerate_of_small (hs : G2NonToralGenerateSmall p) : G2NonToralGenerate p := by
  intro e hadm hp2 hq z z' hz hz' hz1 hz1' hne hcomm hT
  by_cases h11 : 11 ≤ p ^ e
  · exact g2NonToralGenerate_large hp2 hadm h11 z z' hz hz' hz1 hz1' hne hcomm
  · exact hs e hadm hp2 hq (by omega) z z' hz hz' hz1 hz1' hne hcomm hT

end Model

end CFSG.ClassicalInvolution.G2D4Models
