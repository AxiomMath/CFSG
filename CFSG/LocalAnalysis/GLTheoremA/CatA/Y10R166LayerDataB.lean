module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166FamB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.SeitzReduction.SymplecticPilot CFSG.ClassicalInvolution.Models.SymplecticPairs
open SignalizerFunctorTheorem.NonLocal
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] [CharP F 2] {q : ℕ} {ζ : Fˣ}

private noncomputable def blockSpOf {r n : ℕ} (σ : Fin r → Fin n)
    (hσ : Function.Injective σ) : Subgroup (StatedSp n F) :=
  (spEmbed σ hσ).range

private theorem blockSpOf_eq_suppGroup {r n : ℕ} {σ : Fin r → Fin n}
    (hσ : Function.Injective σ) :
    blockSpOf (F := F) σ hσ = suppGroup (K := F) (Set.range (Sum.map σ σ)) := by
  rw [blockSpOf, range_spEmbed]

private theorem isQuasisimple_blockSpOf {r n : ℕ} {σ : Fin r → Fin n}
    (hσ : Function.Injective σ) (hr : 1 ≤ r) (hF : 4 ≤ Nat.card F) :
    CFSG.IsQuasisimple (blockSpOf (F := F) σ hσ) := by
  have hQ : CFSG.IsQuasisimple (StatedSp r F) :=
    CFSG.LieType.Universal.Symplectic.isQuasisimple r F hr (Or.inl (Or.inr hF))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (MonoidHom.ofInjective (spEmbed_injective hσ)) hQ

private theorem center_blockSpOf {r n : ℕ} {σ : Fin r → Fin n}
    (hσ : Function.Injective σ) (hr : 1 ≤ r) :
    Subgroup.center (blockSpOf (F := F) σ hσ) = ⊥ := by
  haveI : NeZero r := ⟨by omega⟩
  exact (center_eq_bot_congr
    (MonoidHom.ofInjective (spEmbed_injective hσ))).2
    (center_statedSp_eq_bot r)

private theorem dvd_card_blockSpOf {r n : ℕ} {σ : Fin r → Fin n}
    (hσ : Function.Injective σ) (hr : 1 ≤ r) (hq : q.Prime)
    (hqdvd : q ∣ Nat.card F - 1) :
    q ∣ Nat.card (blockSpOf (F := F) σ hσ) := by
  haveI : NeZero r := ⟨by omega⟩
  have hcard : Nat.card (blockSpOf (F := F) σ hσ) = Nat.card (StatedSp r F) :=
    Nat.card_congr
      (MonoidHom.ofInjective (spEmbed_injective hσ)).toEquiv.symm
  rw [hcard]
  have hrt : q ∣ Nat.card (rootTorusSp F (0 : Fin r)) := by
    rw [card_rootTorusSp]
    exact hqdvd
  exact hrt.trans (Subgroup.card_subgroup_dvd_card _)

private theorem blockSpOf_normal_centralizer_two {r n : ℕ} {σ : Fin r → Fin n}
    (hσ : Function.Injective σ) {i j : Fin n} (hij : i ≠ j)
    (hLi : blockSpOf (F := F) σ hσ ≤ complSp F i)
    (hLj : blockSpOf (F := F) σ hσ ≤ complSp F j)
    (hInf : complSp F i ⊓ complSp F j ≤ blockSpOf (F := F) σ hσ)
    {ζ : Fˣ} {q : ℕ} (hζ : orderOf ζ = q) (hζ2 : ζ * ζ ≠ 1) :
    ((blockSpOf (F := F) σ hσ).subgroupOf
      (Subgroup.centralizer (symplecticE2Torus (F := F) (n := n) i j ζ :
        Set (StatedSp n F)))).Normal := by
  have hLH : blockSpOf (F := F) σ hσ ≤
      Subgroup.centralizer (symplecticE2Torus (F := F) (n := n) i j ζ :
        Set (StatedSp n F)) := by
    rw [symplecticE2Torus, CFSG.GroupTheory.centralizer_sup_eq_inf_centralizer]
    refine le_inf ?_ ?_
    · exact hLi.trans
        ((complSp_le_centralizer_rootTorusSp (K := F) i).trans
          (Subgroup.centralizer_le (Subgroup.zpowers_le.2
            (rootTorusHom_mem_rootTorusSp i ζ))))
    · exact hLj.trans
        ((complSp_le_centralizer_rootTorusSp (K := F) j).trans
          (Subgroup.centralizer_le (Subgroup.zpowers_le.2
            (rootTorusHom_mem_rootTorusSp j ζ))))
  refine (Subgroup.normal_subgroupOf_iff hLH).2 ?_
  intro l g hl hg
  have hiE : rootTorusHom F n i ζ ∈ symplecticE2Torus (F := F) (n := n) i j ζ :=
    rootTorusHom_mem_symplecticE2Torus_left i j ζ
  have hjE : rootTorusHom F n j ζ ∈ symplecticE2Torus (F := F) (n := n) i j ζ :=
    rootTorusHom_mem_symplecticE2Torus_right i j ζ
  have hgi : Commute g (rootTorusHom F n i ζ) :=
    (Subgroup.mem_centralizer_iff.1 hg _ hiE).symm
  have hgj : Commute g (rootTorusHom F n j ζ) :=
    (Subgroup.mem_centralizer_iff.1 hg _ hjE).symm
  obtain ⟨u0, y0, hy0, hg_eq0⟩ :=
    exists_eq_mul_of_commute_rootTorusHom (k := i) hζ2 hgi
  set a0 : StatedSp n F := rootTorusHom F n i u0 with ha0
  have ha0j : Commute a0 (rootTorusHom F n j ζ) :=
    commute_rootTorusHom_of_ne hij u0 ζ
  have hy0_eq : y0 = a0⁻¹ * g := by
    rw [hg_eq0]
    group
  have hy0_comm : y0 * rootTorusHom F n j ζ = rootTorusHom F n j ζ * y0 := by
    rw [hy0_eq]
    calc a0⁻¹ * g * rootTorusHom F n j ζ
        = a0⁻¹ * (g * rootTorusHom F n j ζ) := by group
      _ = a0⁻¹ * (rootTorusHom F n j ζ * g) := by rw [hgj.eq]
      _ = (a0⁻¹ * rootTorusHom F n j ζ) * g := by group
      _ = (rootTorusHom F n j ζ * a0⁻¹) * g := by rw [ha0j.inv_left.eq]
      _ = rootTorusHom F n j ζ * (a0⁻¹ * g) := by group
  obtain ⟨u1, y1, hy1, hy0_eq1⟩ :=
    exists_eq_mul_of_commute_rootTorusHom (k := j) hζ2 hy0_comm
  set a1 : StatedSp n F := rootTorusHom F n j u1 with ha1
  have ha1i : a1 ∈ complSp F i :=
    rootTorusHom_mem_complSp_of_ne_gen (Ne.symm hij) u1
  have hy1_i : y1 ∈ complSp F i := by
    have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ ha1i) hy0
    rw [hy0_eq1, ha1] at h
    simpa using h
  have hy1L : y1 ∈ blockSpOf (F := F) σ hσ := hInf ⟨hy1_i, hy1⟩
  have hl_i : l ∈ complSp F i := hLi hl
  have hl_j : l ∈ complSp F j := hLj hl
  have ha0l : Commute a0 l :=
    commute_of_mem_longRootSp2_of_mem_complSp
      (rootTorusSp_le_longRootSp2 i ⟨u0, rfl⟩) hl_i
  have ha1l : Commute a1 l :=
    commute_of_mem_longRootSp2_of_mem_complSp
      (rootTorusSp_le_longRootSp2 j ⟨u1, rfl⟩) hl_j
  have hz : y1 * l * y1⁻¹ ∈ blockSpOf (F := F) σ hσ :=
    Subgroup.mul_mem _
      (Subgroup.mul_mem _ hy1L hl) (Subgroup.inv_mem _ hy1L)
  have hz_i : y1 * l * y1⁻¹ ∈ complSp F i := hLi hz
  have hz_j : y1 * l * y1⁻¹ ∈ complSp F j := hLj hz
  have hz0 : Commute a0 (y1 * l * y1⁻¹) :=
    commute_of_mem_longRootSp2_of_mem_complSp
      (rootTorusSp_le_longRootSp2 i ⟨u0, rfl⟩) hz_i
  have hz1 : Commute a1 (y1 * l * y1⁻¹) :=
    commute_of_mem_longRootSp2_of_mem_complSp
      (rootTorusSp_le_longRootSp2 j ⟨u1, rfl⟩) hz_j
  have hconj : g * l * g⁻¹ = y1 * l * y1⁻¹ := by
    rw [hg_eq0, hy0_eq1]
    have hz1' : a1 * (y1 * l * y1⁻¹) * a1⁻¹ = y1 * l * y1⁻¹ := by
      rw [hz1.eq]; group
    have hz0' : a0 * (y1 * l * y1⁻¹) * a0⁻¹ = y1 * l * y1⁻¹ := by
      rw [hz0.eq]; group
    calc (a0 * (a1 * y1)) * l * (a0 * (a1 * y1))⁻¹
        = a0 * (a1 * (y1 * l * y1⁻¹) * a1⁻¹) * a0⁻¹ := by group
      _ = a0 * (y1 * l * y1⁻¹) * a0⁻¹ := by rw [hz1']
      _ = y1 * l * y1⁻¹ := hz0'
  rw [hconj]
  exact hz

section TwoPlaneDefs

variable {m : ℕ}

private def blockEmbedTwo (m : ℕ) : Fin (m - 2) → Fin m :=
  fun i => ⟨i.val + 2, by have h := i.isLt; omega⟩

private theorem blockEmbedTwo_val (m : ℕ) (i : Fin (m - 2)) :
    (blockEmbedTwo (m := m) i).val = i.val + 2 := rfl

private theorem blockEmbedTwo_injective (m : ℕ) :
    Function.Injective (blockEmbedTwo (m := m)) := by
  intro i j h
  have h' := congrArg Fin.val h
  simp only [blockEmbedTwo_val] at h'
  exact Fin.ext (by omega)

private noncomputable def blockSpTwo (m : ℕ) : Subgroup (StatedSp m F) :=
  blockSpOf (F := F) (blockEmbedTwo m) (blockEmbedTwo_injective m)

end TwoPlaneDefs

section TwoPlane

variable {m : ℕ} [NeZero m]

private theorem exists_blockEmbedTwo_eq_iff (hm : 3 ≤ m) (i : Fin m) :
    (∃ j : Fin (m - 2), blockEmbedTwo (m := m) j = i) ↔
      i ≠ (0 : Fin m) ∧ i ≠ (1 : Fin m) := by
  have hv0 : (0 : Fin m).val = 0 := rfl
  have hv1 : (1 : Fin m).val = 1 := by
    show 1 % m = 1
    exact Nat.mod_eq_of_lt (by omega)
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨?_, ?_⟩ <;> intro h
    · have h' := congrArg Fin.val h
      rw [hv0, blockEmbedTwo_val] at h'
      omega
    · have h' := congrArg Fin.val h
      rw [hv1, blockEmbedTwo_val] at h'
      omega
  · rintro ⟨h0, h1⟩
    have hi0 : i.val ≠ 0 := fun h => h0 (Fin.ext (by rw [hv0]; exact h))
    have hi1 : i.val ≠ 1 := fun h => h1 (Fin.ext (by rw [hv1]; exact h))
    have hi : 2 ≤ i.val := by omega
    refine ⟨⟨i.val - 2, by omega⟩, Fin.ext ?_⟩
    show i.val - 2 + 2 = i.val
    omega

private theorem range_blockEmbedTwo (hm : 3 ≤ m) :
    Set.range (Sum.map (blockEmbedTwo (m := m)) (blockEmbedTwo (m := m))) =
      (coords (0 : Fin m) ∪ coords (1 : Fin m))ᶜ := by
  ext a
  rcases a with i | i
  · simpa [Sum.map, exists_blockEmbedTwo_eq_iff hm i, mem_coords, and_assoc]
  · simpa [Sum.map, exists_blockEmbedTwo_eq_iff hm i, mem_coords, and_assoc]

private theorem blockSpTwo_eq_inf (hm : 3 ≤ m) :
    blockSpTwo (F := F) (m := m) =
      complSp F (0 : Fin m) ⊓ complSp F (1 : Fin m) := by
  rw [blockSpTwo, blockSpOf_eq_suppGroup, range_blockEmbedTwo hm, complSp, complSp,
    suppGroup_inf]
  congr 1
  rw [Set.compl_union]

private theorem blockSpTwo_le_centralizer (hm : 3 ≤ m) {ζ : Fˣ} :
    blockSpTwo (F := F) (m := m) ≤
      Subgroup.centralizer
        (symplecticE2Torus (F := F) (n := m) (0 : Fin m) (1 : Fin m) ζ :
          Set (StatedSp m F)) := by
  have hL := blockSpTwo_eq_inf (F := F) (m := m) hm
  have hL0 : blockSpTwo (F := F) (m := m) ≤ complSp F (0 : Fin m) := by
    rw [hL]
    exact inf_le_left
  have hL1 : blockSpTwo (F := F) (m := m) ≤ complSp F (1 : Fin m) := by
    rw [hL]
    exact inf_le_right
  rw [symplecticE2Torus, CFSG.GroupTheory.centralizer_sup_eq_inf_centralizer]
  exact le_inf
    (hL0.trans ((complSp_le_centralizer_rootTorusSp (K := F) (0 : Fin m)).trans
      (Subgroup.centralizer_le (Subgroup.zpowers_le.2
        (rootTorusHom_mem_rootTorusSp (0 : Fin m) ζ)))))
    (hL1.trans ((complSp_le_centralizer_rootTorusSp (K := F) (1 : Fin m)).trans
      (Subgroup.centralizer_le (Subgroup.zpowers_le.2
        (rootTorusHom_mem_rootTorusSp (1 : Fin m) ζ)))))

end TwoPlane

theorem layerData166_statedSp {F : Type} [Field F] [Finite F] [CharP F 2]
    {m n q : ℕ} (hm : 3 ≤ m) (hn : 2 ≤ n) (hcard : Nat.card F = 2 ^ n)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqdvd : q ∣ Nat.card F - 1) :
    LayerData166 (StatedSp m F) q m := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hF4 : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hqdvd' : q ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) q hqdvd'
  have hζ2 : ζ * ζ ≠ 1 := by
    intro h
    have h2 : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    have hpq : q ∣ 2 := hζ ▸ h2
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hpq)
  let i0 : Fin m := 0
  let i1 : Fin m := 1
  have hi01 : i0 ≠ i1 := by
    intro h
    have h' := congrArg Fin.val h
    simp only [i0, i1, Fin.val_zero] at h'
    exact absurd h' (by
      have hv1 : (1 : Fin m).val = 1 := by
        show 1 % m = 1
        exact Nat.mod_eq_of_lt (by omega)
      rw [hv1] at h'
      omega)
  refine ⟨symplecticQTorus (F := F) (ℓ := m) q, spSiegel m F,
    symplecticE2Torus (F := F) (n := m) i0 i1 ζ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isElemAbelian_symplecticQTorus (F := F) (ℓ := m) hq
  · exact card_symplecticQTorus (F := F) (ℓ := m) hq hqdvd
  · exact isPGroup_spSiegel m
  · exact symplecticQTorus_le_normalizer_spSiegel (F := F) (m := m) q
  · exact symplecticQTorus_inf_centralizer_spSiegel (F := F) (m := m) hq hq2
  · exact symplecticE2Torus_le_symplecticQTorus (F := F) (n := m) (i := i0) (j := i1) hζ
  · exact card_symplecticE2Torus (F := F) (n := m) (i := i0) (j := i1) hq hi01 hζ
  · let EJ : Subgroup (StatedSp m F) :=
      symplecticE2Torus (F := F) (n := m) i0 i1 ζ
    let L : Subgroup (StatedSp m F) := blockSpTwo (F := F) (m := m)
    have hLinf : L = complSp F (0 : Fin m) ⊓ complSp F (1 : Fin m) :=
      blockSpTwo_eq_inf (F := F) (m := m) hm
    have hLi : L ≤ complSp F (0 : Fin m) := by
      rw [hLinf]
      exact inf_le_left
    have hLj : L ≤ complSp F (1 : Fin m) := by
      rw [hLinf]
      exact inf_le_right
    have hInf : complSp F (0 : Fin m) ⊓ complSp F (1 : Fin m) ≤ L := by
      rw [hLinf]
    have hLH : L ≤ Subgroup.centralizer (EJ : Set (StatedSp m F)) :=
      blockSpTwo_le_centralizer (F := F) (m := m) hm (ζ := ζ)
    have hN : (L.subgroupOf
        (Subgroup.centralizer (EJ : Set (StatedSp m F)))).Normal :=
      blockSpOf_normal_centralizer_two (F := F) (σ := blockEmbedTwo m)
        (blockEmbedTwo_injective m) hi01 hLi hLj hInf hζ hζ2
    have hQ : CFSG.IsQuasisimple L :=
      isQuasisimple_blockSpOf (F := F) (σ := blockEmbedTwo m)
        (blockEmbedTwo_injective m) (by omega) hF4
    have hcenter : Subgroup.center L = ⊥ :=
      center_blockSpOf (F := F) (σ := blockEmbedTwo m)
        (blockEmbedTwo_injective m) (by omega)
    have hqL : q ∣ Nat.card L :=
      dvd_card_blockSpOf (F := F) (σ := blockEmbedTwo m)
        (blockEmbedTwo_injective m) (by omega) hq hqdvd
    have hdvd : q ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
      have hquot : Nat.card (↥L ⧸ Subgroup.center ↥L) = Nat.card L := by
        rw [hcenter]
        exact Nat.card_congr (QuotientGroup.quotientBot).toEquiv
      rwa [hquot]
    exact glaPLayer_ne_bot_of_normal_quasisimple hq hLH hN
      ⟨hQ.1.commutator_eq_top, hQ.2.1⟩ hdvd

section Certs

theorem layerData166At_B {m n : ℕ} (hm : 3 ≤ m) (hn : 2 ≤ n) :
    LayerData166At (⟨.B, m, n⟩ : GLALabel) := by
  intro J _ _ q hK hZ hq hq2 hqn
  obtain ⟨F, hField, hFinite, hChar, hcard, hEquiv⟩ :=
    exists_mulEquiv_statedSp_of_isLabel (K := J) (N := m) (n := n) hK hZ
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  obtain ⟨e⟩ := hEquiv
  have hqn' : q ∣ Nat.card F - 1 := by
    rw [hcard]
    exact hqn
  exact LayerData166.of_mulEquiv e
    (layerData166_statedSp (F := F) (m := m) (n := n) hm hn hcard hq hq2 hqn') hq

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
