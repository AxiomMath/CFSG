module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZLeviStabWeyl

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Chevalley.RootOps (isRootB isRootB_iff)

local instance e6ZLeviStabUnipNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def zRootA1 : Fin Tag.E6.rank → ℤ := ![1, 0, 0, 0, 0, 0]

@[expose] def zRootA2 : Fin Tag.E6.rank → ℤ := ![0, 1, 0, 0, 0, 0]

@[expose] def zRootA3 : Fin Tag.E6.rank → ℤ := ![0, 0, 1, 0, 0, 0]

@[expose] def zRootA13 : Fin Tag.E6.rank → ℤ := ![1, 0, 1, 0, 0, 0]

@[expose] def zRootA5 : Fin Tag.E6.rank → ℤ := ![0, 0, 0, 0, 1, 0]

@[expose] def zRootA6 : Fin Tag.E6.rank → ℤ := ![0, 0, 0, 0, 0, 1]

@[expose] def zRootA56 : Fin Tag.E6.rank → ℤ := ![0, 0, 0, 0, 1, 1]

@[expose] def zRootU1 : Fin Tag.E6.rank → ℤ := ![1, 1, 1, 2, 2, 1]

@[expose] def zRootU2 : Fin Tag.E6.rank → ℤ := ![1, 1, 2, 2, 1, 1]

@[expose] def zRootU3 : Fin Tag.E6.rank → ℤ := ![1, 1, 2, 2, 2, 1]

@[expose] def zRootL3 : Fin Tag.E6.rank → ℤ := ![1, 1, 1, 2, 1, 0]

@[expose] def zLeviPos : List (Fin Tag.E6.rank → ℤ) :=
  [zRootA2, zRootA1, zRootA3, zRootA13, zRootA5, zRootA6, zRootA56]

theorem zLeviPos_check :
    (∀ γ ∈ rootFinset .E6, (γ 3 = 0 ∧ 0 < height γ) ↔ γ ∈ zLeviPos) ∧ zLeviPos.Nodup ∧
      ∀ γ ∈ zLeviPos, γ ∈ rootFinset .E6 ∧ γ 3 = 0 ∧ 0 < height γ := by
  decide +kernel

theorem zAB_check :
    (∀ a ∈ [zRootA1, zRootA3, zRootA13], ∀ b ∈ [zRootA5, zRootA6, zRootA56],
      isRootB .E6 a = true ∧ isRootB .E6 b = true ∧ a ≠ -b ∧ isRootB .E6 (a + b) = false) ∧
    (zRootA1, zRootA5) ∈ zSPairs ∧ (zRootA3, zRootA6) ∈ zSPairs ∧ (zRootA13, zRootA56) ∈ zSPairs ∧
    zRootA2 = Pi.single 1 1 := by
  decide +kernel

section Coord


theorem parabolicPosRoots_nsmul_add_nsmul_mem (J : Set (Fin Tag.E6.rank)) :
    ∀ α ∈ parabolicPosRoots .E6 J, ∀ β ∈ parabolicPosRoots .E6 J, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot .E6 (a • α + b • β) → a • α + b • β ∈ parabolicPosRoots .E6 J := by
  intro α hα β hβ a b ha hb hr
  obtain ⟨⟨-, hαJ⟩, -, hαp⟩ := hα
  obtain ⟨⟨-, hβJ⟩, -, hβp⟩ := hβ
  obtain ⟨-, hp, -⟩ := nsmul_add_nsmul_mem_heightSet (τ := .E6) (h := 1) (k := 1)
    ⟨hαp, by omega⟩ ⟨hβp, by omega⟩ ha hb hr
  refine ⟨⟨hr, fun i hi => ?_⟩, hr, hp⟩
  simp only [Pi.add_apply, Pi.smul_apply, hαJ i hi, hβJ i hi, smul_zero, add_zero]

theorem parabolicPosRoots_zNodes_eq :
    parabolicPosRoots .E6 zNodes = {γ | γ ∈ zLeviPos} := by
  ext γ
  simp only [parabolicPosRoots, parabolicRoots, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hr, h⟩, -, hpos⟩
    exact (zLeviPos_check.1 γ (mem_rootFinset.2 hr)).1 ⟨h 3 (by simp [zNodes]), hpos⟩
  · intro h
    obtain ⟨hr, h3, hpos⟩ := zLeviPos_check.2.2 γ h
    refine ⟨⟨mem_rootFinset.1 hr, fun i hi => ?_⟩, mem_rootFinset.1 hr, hpos⟩
    have : i = 3 := by simpa [zNodes] using hi
    rw [this]
    exact h3

end Coord

section Conj

variable {K : Type} [Field K]


variable (K) in
@[expose] noncomputable def zAElt (a b c : K) : ModGL .E6 K :=
  pinnedX .E6 K zRootA1 a * pinnedX .E6 K zRootA3 b * pinnedX .E6 K zRootA13 c

variable (K) in
@[expose] noncomputable def zBElt (a b c : K) : ModGL .E6 K :=
  pinnedX .E6 K zRootA5 a * pinnedX .E6 K zRootA6 b * pinnedX .E6 K zRootA56 c

@[expose] noncomputable def zBCoeff (a b c : K) : (Fin Tag.E6.rank → ℤ) → K :=
  conjCoeff zRootA5 a zPsi (conjCoeff zRootA6 b zPsi (conjCoeff zRootA56 c zPsi zCoeff))

theorem zBElt_conj_zAS [CharP K 2] (a b c : K) :
    zBElt K a b c * zAS K * (zBElt K a b c)⁻¹ = rootProd .E6 K zPsi (zBCoeff a b c) := by
  have h5 : IsRoot .E6 zRootA5 := isRootB_iff.1 ((zAB_check.1 zRootA1 (by simp) zRootA5 (by simp)).2.1)
  have h6 : IsRoot .E6 zRootA6 := isRootB_iff.1 ((zAB_check.1 zRootA1 (by simp) zRootA6 (by simp)).2.1)
  have h56 : IsRoot .E6 zRootA56 :=
    isRootB_iff.1 ((zAB_check.1 zRootA1 (by simp) zRootA56 (by simp)).2.1)
  have l5 : (0 : ℤ) ≤ zRootA5 3 := by decide
  have l6 : (0 : ℤ) ≤ zRootA6 3 := by decide
  have l56 : (0 : ℤ) ≤ zRootA56 3 := by decide
  rw [← rootProd_zPsi_zCoeff, zBCoeff, ← conj_rootProd_zPsi h5 l5, ← conj_rootProd_zPsi h6 l6,
    ← conj_rootProd_zPsi h56 l56, zBElt]
  group

theorem conjCoeff_zPsi_of_mem {α ρ ρ' : Fin Tag.E6.rank → ℤ} (hρ : ρ ∈ zPsi) (h : ρ - α = ρ')
    (hρ' : ρ' ∈ zPsi) (hne : α ≠ ρ') (t : K) (c : (Fin Tag.E6.rank → ℤ) → K) :
    conjCoeff α t zPsi c ρ = c ρ + t * c ρ' := by
  rw [conjCoeff_apply zPsi_nodup (fun _ hβ => isRoot_of_mem_zPsi hβ) α t c hρ, h,
    ite_eq_left ⟨hρ', hne⟩]

theorem conjCoeff_zPsi_of_not_mem {α ρ : Fin Tag.E6.rank → ℤ} (hρ : ρ ∈ zPsi)
    (h : ρ - α ∉ zPsi) (t : K) (c : (Fin Tag.E6.rank → ℤ) → K) :
    conjCoeff α t zPsi c ρ = c ρ := by
  rw [conjCoeff_apply zPsi_nodup (fun _ hβ => isRoot_of_mem_zPsi hβ) α t c hρ,
    ite_eq_right fun h' => h h'.1, add_zero]

theorem zBCoeff_apply (a b c : K) :
    zBCoeff a b c zRootU1 = a ∧ zBCoeff a b c zRootU2 = b ∧
      zBCoeff a b c zRootU3 = c + a * b := by
  set c₁ := conjCoeff zRootA56 c zPsi (zCoeff (K := K)) with hc₁
  set c₂ := conjCoeff zRootA6 b zPsi c₁ with hc₂
  have m1 : (zRootU1 : Fin Tag.E6.rank → ℤ) ∈ zPsi := by decide
  have m2 : (zRootU2 : Fin Tag.E6.rank → ℤ) ∈ zPsi := by decide
  have m3 : (zRootU3 : Fin Tag.E6.rank → ℤ) ∈ zPsi := by decide
  have mδ : (zδ : Fin Tag.E6.rank → ℤ) ∈ zPsi := by decide
  have mε : (zε : Fin Tag.E6.rank → ℤ) ∈ zPsi := by decide
  have mL : (zRootL3 : Fin Tag.E6.rank → ℤ) ∈ zPsi := by decide
  have z1 : (zCoeff : (Fin Tag.E6.rank → ℤ) → K) zRootU1 = 0 :=
    zCoeff_eq_zero_of_not_mem (by decide)
  have z2 : (zCoeff : (Fin Tag.E6.rank → ℤ) → K) zRootU2 = 0 :=
    zCoeff_eq_zero_of_not_mem (by decide)
  have z3 : (zCoeff : (Fin Tag.E6.rank → ℤ) → K) zRootU3 = 0 :=
    zCoeff_eq_zero_of_not_mem (by decide)
  have zδ' : (zCoeff : (Fin Tag.E6.rank → ℤ) → K) zδ = 1 :=
    zCoeff_eq_one_of_mem (by decide)
  have zε' : (zCoeff : (Fin Tag.E6.rank → ℤ) → K) zε = 1 :=
    zCoeff_eq_one_of_mem (by decide)
  have zL : (zCoeff : (Fin Tag.E6.rank → ℤ) → K) zRootL3 = 0 :=
    zCoeff_eq_zero_of_not_mem (by decide)
  have c₁1 : c₁ zRootU1 = 0 := by
    rw [hc₁, conjCoeff_zPsi_of_mem m1 (by decide) mL (by decide), z1, zL, mul_zero, add_zero]
  have c₁2 : c₁ zRootU2 = 0 := by
    rw [hc₁, conjCoeff_zPsi_of_not_mem m2 (by decide), z2]
  have c₁3 : c₁ zRootU3 = c := by
    rw [hc₁, conjCoeff_zPsi_of_mem m3 (by decide) mε (by decide), z3, zε', mul_one, zero_add]
  have c₁δ : c₁ zδ = 1 := by
    rw [hc₁, conjCoeff_zPsi_of_not_mem mδ (by decide), zδ']
  have c₁ε : c₁ zε = 1 := by
    rw [hc₁, conjCoeff_zPsi_of_not_mem mε (by decide), zε']
  have c₁L : c₁ zRootL3 = 0 := by
    rw [hc₁, conjCoeff_zPsi_of_not_mem mL (by decide), zL]
  have c₂1 : c₂ zRootU1 = 0 := by
    rw [hc₂, conjCoeff_zPsi_of_not_mem m1 (by decide), c₁1]
  have c₂2 : c₂ zRootU2 = b := by
    rw [hc₂, conjCoeff_zPsi_of_mem m2 (by decide) mε (by decide), c₁2, c₁ε, mul_one, zero_add]
  have c₂3 : c₂ zRootU3 = c := by
    rw [hc₂, conjCoeff_zPsi_of_not_mem m3 (by decide), c₁3]
  have c₂δ : c₂ zδ = 1 := by
    rw [hc₂, conjCoeff_zPsi_of_mem mδ (by decide) mL (by decide), c₁δ, c₁L, mul_zero, add_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [zBCoeff, ← hc₁, ← hc₂, conjCoeff_zPsi_of_mem m1 (by decide) mδ (by decide), c₂1, c₂δ,
      mul_one, zero_add]
  · rw [zBCoeff, ← hc₁, ← hc₂, conjCoeff_zPsi_of_not_mem m2 (by decide), c₂2]
  · rw [zBCoeff, ← hc₁, ← hc₂, conjCoeff_zPsi_of_mem m3 (by decide) m2 (by decide), c₂3, c₂2]

theorem eq_of_zBElt_conj_eq [CharP K 2] {a b c a' b' c' : K}
    (h : zBElt K a b c * zAS K * (zBElt K a b c)⁻¹ =
      zBElt K a' b' c' * zAS K * (zBElt K a' b' c')⁻¹) :
    a = a' ∧ b = b' ∧ c = c' := by
  rw [zBElt_conj_zAS, zBElt_conj_zAS] at h
  have hinj := rootProd_injective zPsi_nodup (fun _ hρ => pos_of_mem_zPsi hρ) h
  obtain ⟨e1, e2, e3⟩ := zBCoeff_apply a b c
  obtain ⟨e1', e2', e3'⟩ := zBCoeff_apply a' b' c'
  have ha : a = a' := by rw [← e1, ← e1', hinj _ (by decide)]
  have hb : b = b' := by rw [← e2, ← e2', hinj _ (by decide)]
  have hc : c + a * b = c' + a' * b' := by rw [← e3, ← e3', hinj _ (by decide)]
  rw [ha, hb] at hc
  exact ⟨ha, hb, add_right_cancel hc⟩

end Conj

section Main

variable {K : Type} [Field K]


theorem commute_pinnedX_zAB {a b : Fin Tag.E6.rank → ℤ}
    (ha : a ∈ ([zRootA1, zRootA3, zRootA13] : List (Fin Tag.E6.rank → ℤ)))
    (hb : b ∈ ([zRootA5, zRootA6, zRootA56] : List (Fin Tag.E6.rank → ℤ))) (s t : K) :
    Commute (pinnedX .E6 K a s) (pinnedX .E6 K b t) := by
  obtain ⟨h1, h2, h3, h4⟩ := zAB_check.1 a ha b hb
  exact commute_pinnedX_of_isRootB_zS h1 h2 h3 h4 s t

theorem zAElt_mul_zBElt_mem_zS (a b c : K) : zAElt K a b c * zBElt K a b c ∈ zS K := by
  obtain ⟨-, p1, p2, p3, -⟩ := zAB_check
  have e : zAElt K a b c * zBElt K a b c =
      (pinnedX .E6 K zRootA1 a * pinnedX .E6 K zRootA5 a) *
        (pinnedX .E6 K zRootA3 b * pinnedX .E6 K zRootA6 b) *
          (pinnedX .E6 K zRootA13 c * pinnedX .E6 K zRootA56 c) := by
    have c53 := commute_pinnedX_zAB (K := K) (a := zRootA3) (b := zRootA5) (by simp) (by simp) b a
    have c513 := commute_pinnedX_zAB (K := K) (a := zRootA13) (b := zRootA5) (by simp) (by simp) c a
    have c613 := commute_pinnedX_zAB (K := K) (a := zRootA13) (b := zRootA6) (by simp) (by simp) c b
    rw [zAElt, zBElt]
    calc pinnedX .E6 K zRootA1 a * pinnedX .E6 K zRootA3 b * pinnedX .E6 K zRootA13 c *
          (pinnedX .E6 K zRootA5 a * pinnedX .E6 K zRootA6 b * pinnedX .E6 K zRootA56 c)
        = pinnedX .E6 K zRootA1 a * pinnedX .E6 K zRootA3 b *
            (pinnedX .E6 K zRootA13 c * pinnedX .E6 K zRootA5 a) * pinnedX .E6 K zRootA6 b *
              pinnedX .E6 K zRootA56 c := by group
      _ = pinnedX .E6 K zRootA1 a * pinnedX .E6 K zRootA3 b *
            (pinnedX .E6 K zRootA5 a * pinnedX .E6 K zRootA13 c) * pinnedX .E6 K zRootA6 b *
              pinnedX .E6 K zRootA56 c := by rw [c513.eq]
      _ = pinnedX .E6 K zRootA1 a * (pinnedX .E6 K zRootA3 b * pinnedX .E6 K zRootA5 a) *
            (pinnedX .E6 K zRootA13 c * pinnedX .E6 K zRootA6 b) *
              pinnedX .E6 K zRootA56 c := by group
      _ = pinnedX .E6 K zRootA1 a * (pinnedX .E6 K zRootA5 a * pinnedX .E6 K zRootA3 b) *
            (pinnedX .E6 K zRootA6 b * pinnedX .E6 K zRootA13 c) *
              pinnedX .E6 K zRootA56 c := by rw [c53.eq, c613.eq]
      _ = _ := by group
  rw [e]
  exact mul_mem (mul_mem (pinnedX_mul_pinnedX_mem_zS p1 a) (pinnedX_mul_pinnedX_mem_zS p2 b))
    (pinnedX_mul_pinnedX_mem_zS p3 c)

theorem mem_zJ_sup_zS_of_mem_parabolicLeviUnipotent [CharP K 2] {u : ModGL .E6 K}
    (hu : u ∈ parabolicLeviUnipotent .E6 K zNodes) (hc : u * zAS K = zAS K * u) :
    u ∈ zJ K ⊔ zS K := by
  obtain ⟨-, hnd, hmem⟩ := zLeviPos_check
  obtain ⟨-, hsurj, -⟩ := CFSG.LieType.Ree.list_prod_pinnedX_bijective (K := K)
    (S := parabolicPosRoots .E6 zNodes) (fun δ hδ => ⟨hδ.1.1, hδ.2.2⟩)
    (parabolicPosRoots_nsmul_add_nsmul_mem zNodes) hnd parabolicPosRoots_zNodes_eq.symm
  obtain ⟨c, rfl⟩ := hsurj u hu
  have e : (zLeviPos.map fun δ => pinnedX .E6 K δ (c δ)).prod =
      pinnedX .E6 K zRootA2 (c zRootA2) * (zAElt K (c zRootA1) (c zRootA3) (c zRootA13) *
        zBElt K (c zRootA5) (c zRootA6) (c zRootA56)) := by
    simp only [zLeviPos, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      zAElt, zBElt, mul_assoc]
  set A := zAElt K (c zRootA1) (c zRootA3) (c zRootA13)
  set B := zBElt K (c zRootA5) (c zRootA6) (c zRootA56)
  set B' := zBElt K (c zRootA1) (c zRootA3) (c zRootA13)
  set s := A * B' with hs
  have hsS : s ∈ zS K := zAElt_mul_zBElt_mem_zS _ _ _
  have hx2J : pinnedX .E6 K zRootA2 (c zRootA2) ∈ zJ K :=
    mem_sup_left (mem_rootSubgroup.2 ⟨c zRootA2, by rw [zAB_check.2.2.2.2]⟩)
  have hcen := (zJ_le_levi_inf_centralizer (K := K)).trans inf_le_right
  have hx2z := mem_centralizer_singleton_iff.1 (hcen hx2J)
  have hsz := mem_centralizer_singleton_iff.1 (zS_le_centralizer hsS)
  rw [e] at hc ⊢
  set v := B'⁻¹ * B with hv
  have hvdef : pinnedX .E6 K zRootA2 (c zRootA2) * (A * B) = pinnedX .E6 K zRootA2 (c zRootA2) * s * v := by
    rw [hs, hv]; group
  have hvz : v * zAS K = zAS K * v := by
    have hm : v ∈ centralizer ({zAS K} : Set (ModGL .E6 K)) := by
      have e' : v = s⁻¹ * (pinnedX .E6 K zRootA2 (c zRootA2))⁻¹ * (pinnedX .E6 K zRootA2 (c zRootA2) * (A * B)) := by
        rw [hvdef]; group
      rw [e']
      exact mul_mem (mul_mem (inv_mem (mem_centralizer_singleton_iff.2 hsz))
        (inv_mem (mem_centralizer_singleton_iff.2 hx2z))) (mem_centralizer_singleton_iff.2 hc)
    exact mem_centralizer_singleton_iff.1 hm
  have hBB : B * zAS K * B⁻¹ = B' * zAS K * B'⁻¹ := by
    have e1 : B = B' * v := by rw [hv]; group
    rw [e1]
    calc B' * v * zAS K * (B' * v)⁻¹ = B' * (v * zAS K) * v⁻¹ * B'⁻¹ := by group
      _ = B' * (zAS K * v) * v⁻¹ * B'⁻¹ := by rw [hvz]
      _ = B' * zAS K * B'⁻¹ := by group
  obtain ⟨e1, e2, e3⟩ := eq_of_zBElt_conj_eq hBB
  have hB : B = B' := by
    show zBElt K (c zRootA5) (c zRootA6) (c zRootA56) = zBElt K (c zRootA1) (c zRootA3) (c zRootA13)
    rw [e1, e2, e3]
  have hv1 : v = 1 := by rw [hv, hB, inv_mul_cancel]
  rw [hvdef, hv1, mul_one]
  exact mul_mem (mem_sup_left hx2J) (mem_sup_right hsS)

end Main

end CFSG.SeitzReduction.E6Pilot
