module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415P47
public import CFSG.GH74.Orders.LieType
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PK

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

namespace L415

theorem isOfType_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {F : (Y : Type) → [Group Y] → Prop} (e : A ≃* B) (h : IsOfType F A) : IsOfType F B := by
  obtain ⟨h2, Y, _, hY, ⟨eY⟩⟩ := h
  have hk1 : ¬ 2 ∣ Nat.card e.symm.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr e.symm.injective, card_bot]
    norm_num
  obtain ⟨eZ⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective e.symm.toMonoidHom
    e.symm.surjective hk1
  exact ⟨isTwoQuasisimple_of_mulEquiv e h2, Y, inferInstance, hY, ⟨eZ.trans eY⟩⟩

theorem layer_map_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (layer A).map e.toMonoidHom = layer B := by
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← map_le_iff_le_comap]
    exact le_sSup (LocalCores.isComponent_map_mulEquiv e hK)
  · refine sSup_le fun L hL => ?_
    have hle : L.map e.symm.toMonoidHom ≤ layer A :=
      le_sSup (LocalCores.isComponent_map_mulEquiv e.symm hL)
    calc L = (L.map e.symm.toMonoidHom).map e.toMonoidHom := by
          rw [map_map, show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id B by
            ext; simp, map_id]
      _ ≤ (layer A).map e.toMonoidHom := map_mono hle

theorem component_eq_layer {G : Type*} [Group G] [Finite G] (hE : IsQuasisimple ↥(layer G))
    {M : Subgroup G} (hM : IsComponent M) : M = layer G := by
  have hME : M ≤ layer G := LocalCores.component_le_layer hM
  have hsn := GorensteinWalter.isSubnormal_subgroupOf_of_subnormal_of_le hME hM.2
  rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hE hsn with h | h
  · refine le_antisymm hME fun x hx => ?_
    have : (⟨x, hx⟩ : ↥(layer G)) ∈ M.subgroupOf (layer G) := by rw [h]; trivial
    exact this
  · exfalso
    have hMp : Group.IsPerfect ↥M := hM.1.1
    have hMn := LocalCores.isQuasisimple_nontrivial hM.1
    have hcomm : commutator ↥M = ⊥ := by
      rw [_root_.commutator_def, commutator_eq_bot_iff_le_centralizer]
      intro x _
      refine mem_centralizer_iff.mpr fun y _ => Subtype.ext ?_
      have hy : (⟨y, hME y.2⟩ : ↥(layer G)) ∈ center ↥(layer G) := h y.2
      exact (congrArg Subtype.val (mem_center_iff.mp hy ⟨x, hME x.2⟩)).symm
    rw [hMp.commutator_eq_top] at hcomm
    obtain ⟨a, b, hab⟩ := exists_pair_ne ↥M
    apply hab
    have h1 : a ∈ (⊤ : Subgroup ↥M) := mem_top a
    have h2 : b ∈ (⊤ : Subgroup ↥M) := mem_top b
    rw [hcomm, mem_bot] at h1 h2
    rw [h1, h2]

end L415

variable {X : Type} [Group X] [Finite X]
  {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X} {w z : X} {V : Subgroup X}
  {i j : ℕ} {z₁ τ α : X} {K₂ W 𝒱 : Subgroup X}

namespace Data415B

variable (hD : Data415B t L p f S w z V i j z₁ τ α K₂ W 𝒱)
include hD

theorem layer_eq_of_lemma46 [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X) (hcat : ¬ Blueprint.Catalog X)
    (h46c : Harris46cInput) (h46d : Harris46dInput)
    (hnβ : ∀ g : X, g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹ ≠ z₁)
    {M : Subgroup (MBar z₁)} (hM : IsComponent M) (hlt : barOf (centralizer {z₁}) K₂ < M) :
    layer (MBar z₁) = M ∧ IsOfType (HarrisF p) ↥M ∧
      (center ↥M ≠ ⊥ → (QuotientGroup.mk ⟨z₁, mem_centralizer_singleton_iff.mpr rfl⟩ :
        MBar z₁) ∈ (center ↥M).map M.subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨g, hg⟩, -⟩ := hD.fd.fusion hnβ
  rw [hD.t_mul_beta] at hg
  have hCC : (centralizer ({w ^ (orderOf w / 2) * t ^ (i + 1) * z ^ j} : Set X)).map
      (MulAut.conj g).toMonoidHom = centralizer ({z₁} : Set X) := by
    rw [L415.map_conj_centralizer, hg]
  obtain ⟨Ψ, hΨb⟩ : ∃ Ψ : MBar (w ^ (orderOf w / 2) * t ^ (i + 1) * z ^ j) ≃* MBar z₁,
      Ψ (betaBar (w ^ (orderOf w / 2) * t ^ (i + 1) * z ^ j)) =
        (QuotientGroup.mk ⟨z₁, mem_centralizer_singleton_iff.mpr rfl⟩ : MBar z₁) := by
    refine ⟨UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (((centralizer ({w ^ (orderOf w / 2) * t ^ (i + 1) * z ^ j} : Set X)).equivMapOfInjective _
        (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hCC)), ?_⟩
    change UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 _ (QuotientGroup.mk _) = _
    rw [UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr_mk]
    congr 1
    exact Subtype.ext hg
  have hΨE := L415.layer_map_mulEquiv' Ψ
  have h46 := h46d X hnab hK hcat t L p f S w z V i j hD.hs (i + 1) j
  rcases h46 with ⟨hq, hF⟩ | ⟨A, B, hsup, -, hcen, -, ⟨eA⟩, ⟨eB⟩, hlie, -, -⟩
  ·
    let eE : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ (i + 1) * z ^ j))) ≃* ↥(layer (MBar z₁)) :=
      ((layer _).equivMapOfInjective _ Ψ.injective).trans (MulEquiv.subgroupCongr hΨE)
    have hqF : IsQuasisimple ↥(layer (MBar z₁)) := LocalCores.isQuasisimple_of_mulEquiv eE hq
    have hMeq := L415.component_eq_layer hqF hM
    subst hMeq
    refine ⟨rfl, L415.isOfType_of_mulEquiv eE hF, fun hZ => ?_⟩
    obtain ⟨-, -, h46c'⟩ := h46c X hnab hK hcat t L p f S w z V i j hD.hs (i + 1) j
    have hZ' : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ (i + 1) * z ^ j))) ≠ ⊥ := by
      intro hbot
      apply hZ
      rw [eq_bot_iff]
      intro x hx
      have h1 : eE.symm x ∈ center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ (i + 1) *
          z ^ j))) := by
        rw [mem_center_iff]
        intro y
        apply eE.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact mem_center_iff.mp hx (eE y)
      rw [hbot, mem_bot] at h1
      have h4 : x = 1 := by rw [← MulEquiv.apply_symm_apply eE x, h1, map_one]
      rw [h4]
      exact one_mem _
    obtain ⟨c, hc, hcb⟩ := h46c' hZ'
    refine Subgroup.mem_map.mpr ⟨eE c, ?_, ?_⟩
    · rw [mem_center_iff]
      intro y
      have h1 := mem_center_iff.mp hc (eE.symm y)
      have h2 := congrArg eE h1
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
    · change ((eE c : ↥(layer (MBar z₁))) : MBar z₁) = _
      rw [← hΨb, ← hcb]
      rfl
  ·
    exfalso
    obtain ⟨hs, hnabA⟩ := L415.simple_nonabelian_of_lieModel hlie
    have : IsSimpleGroup ↥A := eA.isSimpleGroup
    have : IsSimpleGroup ↥B := eB.isSimpleGroup
    have hAn : ∃ a b : ↥A, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnabA
      exact ⟨eA.symm a, eA.symm b, fun h => hab (by simpa using congrArg eA h)⟩
    have hBn : ∃ a b : ↥B, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnabA
      exact ⟨eB.symm a, eB.symm b, fun h => hab (by simpa using congrArg eB h)⟩
    have hJ : IsComponent (M.map Ψ.symm.toMonoidHom) :=
      LocalCores.isComponent_map_mulEquiv Ψ.symm hM
    have hcard : Nat.card M = Nat.card ↥(Standing.Setup42.KBar L
        (w ^ (orderOf w / 2) * t ^ (i + 1) * z ^ j)) := by
      rw [← Subgroup.card_map_of_injective (f := Ψ.symm.toMonoidHom) Ψ.symm.injective]
      rcases L415.component_eq_of_layer_eq_sup hsup hcen hAn hBn hJ with h | h <;> rw [h]
      · exact Nat.card_congr eA.toEquiv
      · exact Nat.card_congr eB.toEquiv
    have hcard' : Nat.card ↥(Standing.Setup42.KBar L
        (w ^ (orderOf w / 2) * t ^ (i + 1) * z ^ j)) =
        Nat.card ↥(Standing.Setup42.KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
      rw [GH74.card_of_lieModel_PSL (by norm_num) hlie,
        GH74.card_of_lieModel_PSL (by norm_num) (hD.hs.lieModel_KBar hD.h412)]
    have h1 := Subgroup.card_lt_of_lt hlt
    have h2 := hD.card_KBar_le
    rw [hcard, hcard'] at h1
    exact absurd h1 (not_lt.mpr h2)

end Data415B

end CFSG.ComponentClassification.HarrisLit
