module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.IsoOn
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G]

private theorem conjNormal_injective_eight :
    Function.Injective (MulAut.conjNormal (H := alternatingGroup (Fin 8)) :
      Equiv.Perm (Fin 8) →* MulAut (alternatingGroup (Fin 8))) :=
  CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 8 (by norm_num)

private theorem nat_card_alternatingGroup_eight :
    Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private theorem nat_card_sym_eight : Nat.card (Sym 8) = 40320 := by
  change Nat.card (Equiv.Perm (Fin 8)) = 40320
  rw [Nat.card_perm, Nat.card_fin]
  norm_num

theorem not_inner_of_equiv_sym_eight {K : Subgroup G} {c : G}
    (hK : Nonempty (alternatingGroup (Fin 8) ≃* ↥K))
    (hM : Nonempty (↥(K ⊔ Subgroup.zpowers c) ≃* Sym 8)) :
    ¬ ∃ g ∈ K, ∀ x ∈ K, c * x * c⁻¹ = g * x * g⁻¹ := by
  classical
  rintro ⟨g, hgK, hconj⟩
  let M : Subgroup G := K ⊔ Subgroup.zpowers c
  have hM' : Nonempty (↥M ≃* Sym 8) := hM
  obtain ⟨ψ⟩ := hM'
  have hgM : g ∈ M := Subgroup.mem_sup_left hgK
  have hcM : c ∈ M := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  let d : M := ⟨g⁻¹ * c, M.mul_mem (M.inv_mem hgM) hcM⟩
  have hd_comm : ∀ x : M, (x : G) ∈ K → d * x * d⁻¹ = x := by
    intro x hx
    apply Subtype.ext
    show (g⁻¹ * c) * (x : G) * (g⁻¹ * c)⁻¹ = (x : G)
    calc (g⁻¹ * c) * (x : G) * (g⁻¹ * c)⁻¹
        = g⁻¹ * (c * (x : G) * c⁻¹) * g := by group
      _ = g⁻¹ * (g * (x : G) * g⁻¹) * g := by rw [hconj (x : G) hx]
      _ = (x : G) := by group
  let H : Subgroup (Sym 8) := (K.subgroupOf M).map ψ.toMonoidHom
  have hcardKM : Nat.card (K.subgroupOf M) = Nat.card K := by
    rw [← Subgroup.card_subtype M (K.subgroupOf M),
      Subgroup.map_subgroupOf_eq_of_le (le_sup_left : K ≤ M)]
  obtain ⟨φ⟩ := hK
  have hcardK : Nat.card K = 20160 := by
    rw [← Nat.card_congr φ.toEquiv]
    exact nat_card_alternatingGroup_eight
  have hcardH : Nat.card H = 20160 := by
    change Nat.card ((K.subgroupOf M).map ψ.toMonoidHom) = 20160
    rw [Subgroup.card_map_of_injective (K := K.subgroupOf M) (f := ψ.toMonoidHom) ψ.injective,
      hcardKM, hcardK]
  have hHindex : H.index = 2 := by
    have h := Subgroup.card_mul_index H
    rw [hcardH] at h
    change 20160 * H.index = Nat.card (Equiv.Perm (Fin 8)) at h
    rw [Nat.card_perm, Nat.card_fin] at h
    norm_num at h
    omega
  have hHA : H = alternatingGroup (Fin 8) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two (α := Fin 8) hHindex
  let τ : Sym 8 := ψ d
  have hτ_cent : ∀ a : alternatingGroup (Fin 8),
      MulAut.conjNormal (H := alternatingGroup (Fin 8)) τ a = a := by
    intro a
    have ha : (a : Equiv.Perm (Fin 8)) ∈ H := by
      rw [hHA]
      exact a.2
    obtain ⟨y, hy, hψy⟩ := Subgroup.mem_map.mp ha
    have hyK : (y : G) ∈ K := Subgroup.mem_subgroupOf.mp hy
    have hdy : d * y * d⁻¹ = y := hd_comm y hyK
    have hψ := congrArg ψ hdy
    have h1 : ψ (d * y * d⁻¹) = ψ d * ψ y * (ψ d)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    have h2 : ψ y = (a : Equiv.Perm (Fin 8)) := hψy
    rw [h1, h2] at hψ
    have hτa : τ * (a : Equiv.Perm (Fin 8)) * τ⁻¹ = (a : Equiv.Perm (Fin 8)) := by
      simpa [τ] using hψ
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    exact hτa
  have hconjτ : MulAut.conjNormal (H := alternatingGroup (Fin 8)) τ = 1 := by
    ext a
    rw [hτ_cent a, MulAut.one_apply]
  have hτ1 : τ = 1 :=
    conjNormal_injective_eight (by rw [hconjτ, map_one])
  have hd1 : d = 1 := ψ.injective (by rw [map_one]; exact hτ1)
  have hgc : g⁻¹ * c = 1 := by
    have := congrArg (fun z : M => (z : G)) hd1
    simpa [d] using this
  have hcg : c = g := (eq_of_inv_mul_eq_one hgc).symm
  have hzp : Subgroup.zpowers c ≤ K := by
    rw [hcg]
    exact Subgroup.zpowers_le.mpr hgK
  have hMK : M = K := sup_eq_left.mpr hzp
  have hcardM : Nat.card M = Nat.card K := by rw [hMK]
  have heq : Nat.card K = Nat.card (Sym 8) := by
    rw [← hcardM]
    exact Nat.card_congr ψ.toEquiv
  rw [hcardK, nat_card_sym_eight] at heq
  omega

theorem out_alt_eight {ψ₁ ψ₂ : MulAut (alternatingGroup (Fin 8))}
    (h₁ : ¬ ∃ g : alternatingGroup (Fin 8), ∀ x, ψ₁ x = g * x * g⁻¹)
    (h₂ : ¬ ∃ g : alternatingGroup (Fin 8), ∀ x, ψ₂ x = g * x * g⁻¹) :
    ∃ g : alternatingGroup (Fin 8), ∀ x, ψ₁ (ψ₂ x) = g * x * g⁻¹ := by
  classical
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8
    (by norm_num) (by norm_num)
  obtain ⟨σ₁, hσ₁⟩ := hbij.2 ψ₁
  obtain ⟨σ₂, hσ₂⟩ := hbij.2 ψ₂
  have hinner : ∀ (σ : Equiv.Perm (Fin 8)) (ψ : MulAut (alternatingGroup (Fin 8))),
      MulAut.conjNormal σ = ψ → σ ∈ alternatingGroup (Fin 8) →
      ∃ g : alternatingGroup (Fin 8), ∀ x, ψ x = g * x * g⁻¹ := by
    intro σ ψ hσ hmem
    refine ⟨⟨σ, hmem⟩, fun x => ?_⟩
    apply Subtype.ext
    rw [← hσ, MulAut.conjNormal_apply]
    rfl
  have hsign₁ : Equiv.Perm.sign σ₁ = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ₁) with h | h
    · exact absurd (Equiv.Perm.mem_alternatingGroup.mpr h) (fun hmem => h₁ (hinner σ₁ ψ₁ hσ₁ hmem))
    · exact h
  have hsign₂ : Equiv.Perm.sign σ₂ = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ₂) with h | h
    · exact absurd (Equiv.Perm.mem_alternatingGroup.mpr h) (fun hmem => h₂ (hinner σ₂ ψ₂ hσ₂ hmem))
    · exact h
  have hmem : σ₁ * σ₂ ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, hsign₁, hsign₂]
    decide
  refine ⟨⟨σ₁ * σ₂, hmem⟩, fun x => ?_⟩
  have hcomp : ψ₁ (ψ₂ x) = MulAut.conjNormal (H := alternatingGroup (Fin 8)) (σ₁ * σ₂) x := by
    have hm : MulAut.conjNormal (H := alternatingGroup (Fin 8)) (σ₁ * σ₂) =
        MulAut.conjNormal σ₁ * MulAut.conjNormal σ₂ := map_mul _ σ₁ σ₂
    rw [← hσ₁, ← hσ₂, hm]
    rfl
  rw [hcomp]
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  rfl

theorem out_of_equiv_alt_eight {N : Subgroup G} (e : alternatingGroup (Fin 8) ≃* ↥N)
    {ψ₁ ψ₂ : G → G} (h₁ : IsIsoOn N N ψ₁) (h₂ : IsIsoOn N N ψ₂)
    (n₁ : ¬ ∃ g ∈ N, ∀ x ∈ N, ψ₁ x = g * x * g⁻¹)
    (n₂ : ¬ ∃ g ∈ N, ∀ x ∈ N, ψ₂ x = g * x * g⁻¹) :
    ∃ g ∈ N, ∀ x ∈ N, ψ₁ (ψ₂ x) = g * x * g⁻¹ := by
  classical
  let Ψ₁ : MulAut (alternatingGroup (Fin 8)) := (e.trans h₁.toMulEquiv).trans e.symm
  let Ψ₂ : MulAut (alternatingGroup (Fin 8)) := (e.trans h₂.toMulEquiv).trans e.symm
  have he₁ : ∀ y : alternatingGroup (Fin 8),
      ((e (Ψ₁ y) : ↥N) : G) = ψ₁ ((e y : ↥N) : G) := by
    intro y
    have h : e (Ψ₁ y) = h₁.toMulEquiv (e y) := by simp [Ψ₁]
    rw [h]
    exact IsIsoOn.toMulEquiv_apply h₁ (e y)
  have he₂ : ∀ y : alternatingGroup (Fin 8),
      ((e (Ψ₂ y) : ↥N) : G) = ψ₂ ((e y : ↥N) : G) := by
    intro y
    have h : e (Ψ₂ y) = h₂.toMulEquiv (e y) := by simp [Ψ₂]
    rw [h]
    exact IsIsoOn.toMulEquiv_apply h₂ (e y)
  have hnoninner : ∀ (Ψ : MulAut (alternatingGroup (Fin 8))) (ψ : G → G),
      (∀ y, ((e (Ψ y) : ↥N) : G) = ψ ((e y : ↥N) : G)) →
      (¬ ∃ g ∈ N, ∀ x ∈ N, ψ x = g * x * g⁻¹) →
      ¬ ∃ g : alternatingGroup (Fin 8), ∀ y, Ψ y = g * y * g⁻¹ := by
    rintro Ψ ψ he n ⟨g, hg⟩
    refine n ⟨(e g : ↥N), (e g).2, fun x hx => ?_⟩
    obtain ⟨y, hy⟩ := e.surjective (⟨x, hx⟩ : ↥N)
    have hxy : ((e y : ↥N) : G) = x := congrArg Subtype.val hy
    rw [← hxy]
    calc ψ ((e y : ↥N) : G)
        = ((e (Ψ y) : ↥N) : G) := (he y).symm
      _ = ((e (g * y * g⁻¹) : ↥N) : G) := by rw [hg y]
      _ = ((e g * e y * (e g)⁻¹ : ↥N) : G) := by rw [map_mul, map_mul, map_inv]
      _ = ((e g : ↥N) : G) * ((e y : ↥N) : G) * (((e g : ↥N) : G))⁻¹ := rfl
  have hn₁ := hnoninner Ψ₁ ψ₁ he₁ n₁
  have hn₂ := hnoninner Ψ₂ ψ₂ he₂ n₂
  obtain ⟨g, hg⟩ := out_alt_eight hn₁ hn₂
  refine ⟨(e g : ↥N), (e g).2, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := e.surjective (⟨x, hx⟩ : ↥N)
  have hxy : ((e y : ↥N) : G) = x := congrArg Subtype.val hy
  rw [← hxy]
  calc ψ₁ (ψ₂ ((e y : ↥N) : G))
      = ψ₁ ((e (Ψ₂ y) : ↥N) : G) := by rw [he₂ y]
    _ = ((e (Ψ₁ (Ψ₂ y)) : ↥N) : G) := (he₁ (Ψ₂ y)).symm
    _ = ((e (g * y * g⁻¹) : ↥N) : G) := by rw [hg y]
    _ = ((e g * e y * (e g)⁻¹ : ↥N) : G) := by rw [map_mul, map_mul, map_inv]
    _ = ((e g : ↥N) : G) * ((e y : ↥N) : G) * (((e g : ↥N) : G))⁻¹ := rfl

end CFSG.EvenSporadicStandard.HNRecog.Section4
