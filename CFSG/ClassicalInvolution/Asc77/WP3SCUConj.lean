module

public import CFSG.ClassicalInvolution.Asc77.WP3ChainVRank3
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.WP3FrameModelPSU

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Conj

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {Ω : Set (Subgroup G)} {K J K' : Subgroup G} {z t z' : G}

structure ChainConjData (hs : ChainFrameSetting p f Ω K J K' z t z') (C : ChainCtx p f Ω z)
    (g a b : G) (M : Subgroup G) : Prop where
  hCK : C.K = K
  hgt : g * t * g⁻¹ = z
  ha : a = g * z * g⁻¹
  hb : b = g * z' * g⁻¹
  hM : M = conjSub g K
  isElemAbelian : IsElemAbelian 2 (conjSub g (Subgroup.closure ({z, t, z'} : Set G)))
  card_eight : Nat.card (conjSub g (Subgroup.closure ({z, t, z'} : Set G))) = 8
  closure_eq : conjSub g (Subgroup.closure ({z, t, z'} : Set G)) =
    Subgroup.closure ({a, z, b} : Set G)
  a_ne_one : a ≠ 1
  a_ne_z : a ≠ z
  b_ne_one : b ≠ 1
  b_ne_z : b ≠ z
  ba_ne_one : b * a ≠ 1
  ba_ne_z : b * a ≠ z
  mem : M ∈ tqMembers Ω z
  cls : IsClassicalMember p f M a
  tq_K : a ∈ trivialOnQuot C.K
  tq_M : b ∈ trivialOnQuot M

theorem chainFrame_conj (hs : ChainFrameSetting p f Ω K J K' z t z') {n : ℕ}
    (hr : ChainShapeRank p f n Ω z) (hn : 3 ≤ n) :
    ∃ (C : ChainCtx p f Ω z) (g a b : G) (M : Subgroup G),
      C.D.rank C.i₁ = n ∧ ChainConjData hs C g a b M := by
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  have hd := hs.frame
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := hr
  have hpairD : ChainPair (fundamentalSubgroups (D.tag i₁) (compModel D i₁).D) :=
    chainPair_model hp (D.tag i₁) (D.rank i₁) (D.exp i₁) ht₁ (by omega) (D.admissible i₁)
  let C : ChainCtx p f Ω z :=
    { K := K, hK := hd.mem, hKz := hd.hz, hΩ := hΩ, hp := hp, hq := hq, D := D,
      card_eq := hcard, i₀ := i₀, i₁ := i₁, ne := hne, tag₁ := ht₁, tag₀ := ht₀, rank₀ := hr₀,
      pair := hpairD }
  obtain ⟨g₀, hg₀⟩ := hs.trans J hd.memJ
  have hKcl : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hd.mem hd.hz
  have hgz : g₀ * z * g₀⁻¹ = t := by
    have h1 : IsUniqueInvolution (conjSub g₀ K) (g₀ * z * g₀⁻¹) :=
      ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq (hKcl.conj g₀)
    rw [hg₀] at h1
    exact h1.eq hd.ht
  have hzt : g₀⁻¹ * t * g₀⁻¹⁻¹ = z := by rw [← hgz]; group
  have hzB : z ∈ Subgroup.closure ({z, t, z'} : Set G) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, t, z'} : Set G) := Subgroup.subset_closure (by simp)
  have hz'B : z' ∈ Subgroup.closure ({z, t, z'} : Set G) := Subgroup.subset_closure (by simp)
  have hB := hd.isElemAbelian hp hΩ
  have hinj : ∀ x y : G, g₀⁻¹ * x * g₀⁻¹⁻¹ = g₀⁻¹ * y * g₀⁻¹⁻¹ → x = y := fun x y h =>
    mul_left_cancel (mul_right_cancel h)
  have htz := hd.t_ne_z hp hq hΩ
  have hz'z := hd.z'_ne_z hp hq hΩ
  have hz't := hd.z'_ne_t hΩ
  have hz'zt := hd.z'_ne_zt hp hq hΩ
  have hztc := hd.comm_zt hp hΩ
  have hzsq := hd.hz.sq
  have hmemM : conjSub g₀⁻¹ K ∈ tqMembers Ω z := by
    refine ⟨hΩ.conjInvariant g₀⁻¹ K hd.mem, ?_⟩
    have h := trivialOnQuot_conjSub (hd.tq_t hp hq hΩ) g₀⁻¹
    rwa [hzt] at h
  have haK : g₀⁻¹ * z * g₀⁻¹⁻¹ ∈ trivialOnQuot K := by
    have h := trivialOnQuot_conjSub (hd.tq_z_J hp hq hΩ) g₀⁻¹
    rwa [← hg₀, conjSub_inv_conjSub] at h
  have hbM : g₀⁻¹ * z' * g₀⁻¹⁻¹ ∈ trivialOnQuot (conjSub g₀⁻¹ K) :=
    trivialOnQuot_conjSub (hd.tq_z' hp hq hΩ) g₀⁻¹
  have hB8 : Nat.card (conjSub g₀⁻¹ (Subgroup.closure ({z, t, z'} : Set G))) = 8 := by
    rw [show Nat.card (conjSub g₀⁻¹ (Subgroup.closure ({z, t, z'} : Set G))) =
      Nat.card (Subgroup.closure ({z, t, z'} : Set G)) from
      Subgroup.card_map_of_injective (MulAut.conj g₀⁻¹).injective]
    exact hd.natCard_eight hp hq hΩ
  have hba : (g₀⁻¹ * z' * g₀⁻¹⁻¹) * (g₀⁻¹ * z * g₀⁻¹⁻¹) = g₀⁻¹ * (z' * z) * g₀⁻¹⁻¹ := by
    group
  have ha1 : g₀⁻¹ * z * g₀⁻¹⁻¹ ≠ 1 := fun h => hd.hz.ne_one (hinj z 1 (by rw [h]; group))
  have haz : g₀⁻¹ * z * g₀⁻¹⁻¹ ≠ z := fun h => htz (hinj t z (by rw [hzt]; exact h.symm))
  have hb1 : g₀⁻¹ * z' * g₀⁻¹⁻¹ ≠ 1 := fun h => hd.hz'.ne_one (hinj z' 1 (by rw [h]; group))
  have hbz : g₀⁻¹ * z' * g₀⁻¹⁻¹ ≠ z := fun h => hz't (hinj z' t (by rw [hzt]; exact h))
  have hba1 : (g₀⁻¹ * z' * g₀⁻¹⁻¹) * (g₀⁻¹ * z * g₀⁻¹⁻¹) ≠ 1 := by
    intro h
    have h1 : z' * z = 1 := hinj (z' * z) 1 (by rw [← hba, h]; group)
    apply hz'z
    calc z' = z' * (z * z) := by rw [hzsq, mul_one]
      _ = (z' * z) * z := by group
      _ = z := by rw [h1, one_mul]
  have hbaz : (g₀⁻¹ * z' * g₀⁻¹⁻¹) * (g₀⁻¹ * z * g₀⁻¹⁻¹) ≠ z := by
    intro h
    have h1 : z' * z = t := hinj (z' * z) t (by rw [← hba, h, hzt])
    apply hz'zt
    calc z' = z' * (z * z) := by rw [hzsq, mul_one]
      _ = (z' * z) * z := by group
      _ = t * z := by rw [h1]
      _ = z * t := hztc.symm
  have hcl : conjSub g₀⁻¹ (Subgroup.closure ({z, t, z'} : Set G)) =
      Subgroup.closure ({g₀⁻¹ * z * g₀⁻¹⁻¹, z, g₀⁻¹ * z' * g₀⁻¹⁻¹} : Set G) := by
    unfold conjSub
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, (rfl | rfl | rfl), rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (by simpa using hzt))
      · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact ⟨z, Or.inl rfl, rfl⟩
      · exact ⟨t, Or.inr (Or.inl rfl), by simpa using hzt⟩
      · exact ⟨z', Or.inr (Or.inr rfl), rfl⟩
  exact ⟨C, g₀⁻¹, g₀⁻¹ * z * g₀⁻¹⁻¹, g₀⁻¹ * z' * g₀⁻¹⁻¹, conjSub g₀⁻¹ K, hr₁,
    ⟨rfl, hzt, rfl, rfl, rfl, isElemAbelian_conjSub hB g₀⁻¹, hB8, hcl, ha1, haz, hb1, hbz, hba1,
      hbaz, hmemM, hKcl.conj g₀⁻¹, haK, hbM⟩⟩

end Conj

end CFSG.ClassicalInvolution.Asc77
