module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34Z
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34Transfer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34Cos

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open CFSG.GH74.GLS.Bg.Thompson (IsExtremalIn exists_conj_into_sylow)
open scoped MatrixGroups

section Main

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

section End

variable (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) (hI : Inputs2436)
  (hK : A3A3K T M H S L s x z₁ z₂ K) (hc : blockU2 L s ≤ Subgroup.centralizer (K : Set G))

section NoF

include hD h27_1 hK

omit hD h27_1 in
theorem A3A3K.baum_comm_z₂ {r : G} (hr : r ∈ baum S) : r * z₂ = z₂ * r := by
  have hz₁ : z₁ ∈ Subgroup.centralizer ((baum S : Subgroup G) : Set G) := by
    have : z₁ ∈ Subgroup.zpowers z₁ := Subgroup.mem_zpowers z₁
    rw [hK.toA3A3x.z₁_gen] at this
    exact this.2
  have hsN : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hK.s_mem
  have hr' : s * r * s⁻¹ ∈ baum S := (Subgroup.mem_normalizer_iff.mp hsN r).mp hr
  have h1 : (s * r * s⁻¹) * z₁ = z₁ * (s * r * s⁻¹) := Subgroup.mem_centralizer_iff.mp hz₁ _ hr'
  rw [hK.toA3A3x.z₂_def]
  calc r * (s⁻¹ * z₁ * s) = s⁻¹ * ((s * r * s⁻¹) * z₁) * s := by group
    _ = s⁻¹ * (z₁ * (s * r * s⁻¹)) * s := by rw [h1]
    _ = (s⁻¹ * z₁ * s) * r := by group

end NoF

include hD h27_1 hI hK hc

theorem A3A3K.false_of_blockU2_le_centralizer
    : False := by
  have hcs := hK.cs
  have hB := basic31 hD h27_1 hK.toA3A3
  have : IsSimpleGroup G := hcs.setting.simple
  obtain ⟨ρ, hρR, hρ2⟩ := hK.exists_rho hD h27_1 hI hc
  have hρS : ρ ∈ S := (inf_le_left : baum S ≤ S) hρR
  have hST : S ≤ T := hcs.le_T
  have hxT : x ∈ T := hK.x_mem
  have hxS : x ∉ S := hK.x_not_mem
  have hx'T : ρ * x ∈ T := T.mul_mem (hST hρS) hxT
  have hx'S : ρ * x ∉ S := fun h => hxS (by simpa using S.mul_mem (S.inv_mem hρS) h)
  have hx'1 : ρ * x ≠ 1 := fun h => hx'S (h ▸ S.one_mem)
  have hxR : x⁻¹ * (ρ * x) ∈ baum S := by
    have hxN : x ∈ normalizer (baum S : Set G) := hK.toA3A3x.x_mem_normalizer_baum hB
    have := (Subgroup.mem_normalizer_iff.mp ((normalizer (baum S : Set G)).inv_mem hxN) ρ).mp hρR
    simpa [mul_assoc] using this
  have hx'K : ρ * x ∈ normalizer (K : Set G) :=
    (normalizer (K : Set G)).mul_mem (hK.baum_le_normalizer_K hD h27_1 hI hc hρR) hK.x_mem_normalizer_K
  have hx'z₂ : (ρ * x) * z₂ = z₂ * (ρ * x) := by
    calc (ρ * x) * z₂ = ρ * (x * z₂) := by group
      _ = ρ * (z₂ * x) := by rw [hK.toA3A3x.x_comm₂]
      _ = (ρ * z₂) * x := by group
      _ = (z₂ * ρ) * x := by rw [hK.baum_comm_z₂ hρR]
      _ = z₂ * (ρ * x) := by group
  have hx'₁ : ¬ ρ * x ∈ conjClass z₂ :=
    hK.not_mem_conjClass_z₂_of_mem_xR hD h27_1 hI hc hρ2 hxR
  have hx'₂ : ¬ ρ * x ∈ conjClass (z₁ * z₂) :=
    hK.not_mem_conjClass_z_of_outer hD h27_1 hI hc hρ2 hx'K hx'z₂
      (hK.not_inner_of_mem_xR hD h27_1 hI hc hxR)
  have hTidx : ¬ 2 ∣ T.index := by
    have h1 := hcs.setting.sylow.2.2
    rwa [index_subgroupOf_top] at h1
  obtain ⟨g, hyS, hyext⟩ := exists_extremal_conj_mem_of_index_two hcs.setting.nonabelian
    hcs.setting.isPGroup hTidx hST hB.idx_T hx'T hx'S hρ2
  set y : G := g⁻¹ * (ρ * x) * g with hy
  have hyT : y ∈ T := hST hyS
  have hy2 : y * y = 1 := by
    calc y * y = g⁻¹ * ((ρ * x) * (ρ * x)) * g := by rw [hy]; group
      _ = 1 := by rw [hρ2]; group
  have hy1 : y ≠ 1 := fun h => hx'1 (by
    have : ρ * x = g * y * g⁻¹ := by rw [hy]; group
    rw [this, h]; group)
  have hyz₂ : ¬ y ∈ conjClass z₂ := fun h => hx'₁ (by
    apply mem_conjClass_of_conj (g := g⁻¹)
    simpa using h)
  have hyz : ¬ y ∈ conjClass (z₁ * z₂) := fun h => hx'₂ (by
    apply mem_conjClass_of_conj (g := g⁻¹)
    simpa using h)
  have hTN := hK.T_le_normalizer_sup hD h27_1 hI hc hyT
  rcases hK.conjR_K_cases hD h27_1 hI hc hTN with hKy | hKy
  ·
    have hyK : y ∈ normalizer (K : Set G) := mem_normalizer_iff_conjR_eq.mpr hKy
    rcases hK.mem_baum_or_xR hD h27_1 hI hc hyT hyK with hR | hxy
    · rcases hK.involution_sup_cases hD h27_1 hI hc (hK.baum_le_sup hD h27_1 hI hc hR) hy2 hy1 with h | h
      · exact hyz₂ h
      · exact hyz h
    · exfalso
      have h1 : x⁻¹ * y ∈ S := (inf_le_left : baum S ≤ S) hxy
      have h2 : x⁻¹ ∈ S := by simpa using S.mul_mem h1 (S.inv_mem hyS)
      exact hxS (by simpa using S.inv_mem h2)
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hz₂2 : z₂ * z₂ = 1 := by simpa [pow_two] using hK.toA3A3x.sq₂
    have hz'' : g⁻¹ * z₂ * g ∈ conjClass z₂ := ⟨g, rfl⟩
    have hyz'' : (g⁻¹ * z₂ * g) * y = y * (g⁻¹ * z₂ * g) := by
      calc (g⁻¹ * z₂ * g) * y = g⁻¹ * (z₂ * (ρ * x)) * g := by rw [hy]; group
        _ = g⁻¹ * ((ρ * x) * z₂) * g := by rw [hx'z₂]
        _ = y * (g⁻¹ * z₂ * g) := by rw [hy]; group
    have hz''2 : (g⁻¹ * z₂ * g) * (g⁻¹ * z₂ * g) = 1 := by
      calc (g⁻¹ * z₂ * g) * (g⁻¹ * z₂ * g) = g⁻¹ * (z₂ * z₂) * g := by group
        _ = 1 := by rw [hz₂2]; group
    have hz''1 : g⁻¹ * z₂ * g ≠ 1 := fun h => hK.toA3A3x.z₂_ne (by
      have : z₂ = g * (g⁻¹ * z₂ * g) * g⁻¹ := by group
      rw [this, h]; group)
    have hz''P : IsPGroup 2 (Subgroup.zpowers (g⁻¹ * z₂ * g)) := by
      rw [IsPGroup.iff_card, Nat.card_zpowers,
        orderOf_eq_prime (by rw [pow_two]; exact hz''2) hz''1]
      exact ⟨1, by simp⟩
    have hKN : Subgroup.zpowers (g⁻¹ * z₂ * g) ≤ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hyz''
    obtain ⟨hext1, hext2, hext3⟩ := hyext
    obtain ⟨c, hcC, hc'⟩ := exists_conj_into_sylow (p := 2) hKN hz''P hext1 hext2 hext3
    obtain ⟨hz'T, hz'C⟩ := hc' (g⁻¹ * z₂ * g) (Subgroup.mem_zpowers _)
    have hz'cl : c⁻¹ * (g⁻¹ * z₂ * g) * c ∈ conjClass z₂ := conj_mem_conjClass hz'' c
    have hz'2 : (c⁻¹ * (g⁻¹ * z₂ * g) * c) * (c⁻¹ * (g⁻¹ * z₂ * g) * c) = 1 := by
      calc (c⁻¹ * (g⁻¹ * z₂ * g) * c) * (c⁻¹ * (g⁻¹ * z₂ * g) * c)
          = c⁻¹ * ((g⁻¹ * z₂ * g) * (g⁻¹ * z₂ * g)) * c := by group
        _ = 1 := by rw [hz''2]; group
    have hz'1 : c⁻¹ * (g⁻¹ * z₂ * g) * c ≠ 1 := fun h => hz''1 (by
      have : g⁻¹ * z₂ * g = c * (c⁻¹ * (g⁻¹ * z₂ * g) * c) * c⁻¹ := by group
      rw [this, h]; group)
    have hcomm : y * (c⁻¹ * (g⁻¹ * z₂ * g) * c) * y⁻¹ = c⁻¹ * (g⁻¹ * z₂ * g) * c := by
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hz'C
      calc y * (c⁻¹ * (g⁻¹ * z₂ * g) * c) * y⁻¹
          = (y * (c⁻¹ * (g⁻¹ * z₂ * g) * c)) * y⁻¹ := rfl
        _ = ((c⁻¹ * (g⁻¹ * z₂ * g) * c) * y) * y⁻¹ := by rw [h1]
        _ = c⁻¹ * (g⁻¹ * z₂ * g) * c := by group
    have hinf := hK.inf_K_Ks hD h27_1 hI hc
    rcases hK.mem_K_or_Ks_of_conjClass hD h27_1 hI hc hz'T hz'2 hz'cl with hzK | hzK'
    · have hmem : c⁻¹ * (g⁻¹ * z₂ * g) * c ∈ conjR K y := by
        rw [mem_conjR, hcomm]; exact hzK
      rw [hKy] at hmem
      have : c⁻¹ * (g⁻¹ * z₂ * g) * c ∈ K ⊓ conjR K s := ⟨hzK, hmem⟩
      rw [hinf, Subgroup.mem_bot] at this
      exact hz'1 this
    · have hmem : c⁻¹ * (g⁻¹ * z₂ * g) * c ∈ K := by
        have h1 : c⁻¹ * (g⁻¹ * z₂ * g) * c ∈ conjR K y := by rw [hKy]; exact hzK'
        rw [mem_conjR, hcomm] at h1
        exact h1
      have : c⁻¹ * (g⁻¹ * z₂ * g) * c ∈ K ⊓ conjR K s := ⟨hmem, hzK'⟩
      rw [hinf, Subgroup.mem_bot] at this
      exact hz'1 this

end End

theorem lemma2_4_34_used_of_inputs
    (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (hI : Inputs2436) : Lemma2_4_34_used := by
  intro G _ _ T M H S L s x z₁ z₂ K hK hc
  exact hK.false_of_blockU2_le_centralizer hD h27_1 hI hc

end Main

end CFSG.QuasithinUnique.DoubleA3
