module

public import CFSG.CharacterTheory.Wreathed.BrauerWongOmega
public import CFSG.CharacterTheory.Wreathed.CentralizerResidual
public import CFSG.CharacterTheory.Wreathed.CompatibleCentralizerFamiliesLocal
public import CFSG.CharacterTheory.Wreathed.CompatibleCentralizerFamiliesSpecial
public import CFSG.CharacterTheory.Wreathed.CompatibleCentralizerLinearFamily

public noncomputable section

namespace CFSG.Wreathed.CompatibleFamilies

open CFSG.Wreathed CFSG.Wreathed.BrauerWong CFSG.Wreathed.BaseFourCentralizerStructure

universe u

variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
  (hnonab : ∃ x y : G, x * y ≠ y * x) {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

omit [Finite G] [IsSimpleGroup G] in
theorem centralizer_zpowers_eq (g : G) :
    Subgroup.centralizer {g} = Subgroup.centralizer (Subgroup.zpowers g : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

include hnonab in
theorem apply_x2_swap (hn : 2 ≤ n)
    (lam : Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))} →* ℂˣ)
    (v : Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))})
    (hv : (v : G) = wreathModelHom S e (Original.x2 (2 ^ n)) *
      wreathModelHom S e (Original.z (2 ^ n))) : lam v = 1 := by
  have hvY : (v : G) ∈ modelY S e := by
    rw [hv, ← map_mul]
    exact Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  rw [← centralizerQuaternion_map n hn S e] at hvY
  obtain ⟨v', hv'Y, hv'⟩ := hvY
  have hvv' : v' = v := Subtype.ext hv'
  subst hvv'
  have hcomm := centralizerQuaternion_le_kernel_commutator hnonab n hn S e hv'Y
  have hle : (commutator (centralizerTransferKernel n hn S e)).map
      (centralizerTransferKernel n hn S e).subtype ≤
        commutator (Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))}) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  exact Abelianization.commutator_subset_ker lam (hle hcomm)

omit [Finite G] [IsSimpleGroup G] in
theorem apply_sylow_of_base_swap (hn : 2 ≤ n)
    (lam : Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))} →* ℂˣ)
    (hU : ∀ v : Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))},
      (v : G) ∈ modelBase S e → lam v = 1)
    (hW : ∀ v : Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))},
      (v : G) = wreathModelHom S e (Original.z (2 ^ n)) → lam v = 1)
    (v : Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))})
    (hvS : (v : G) ∈ (S : Subgroup G)) : lam v = 1 := by
  have hSN := sylow_le_centralizer_x S e hn
  let F : Wreath (2 ^ n) →* ℂˣ :=
    lam.comp ((wreathModelHom S e).codRestrict _ (fun w => hSN (wreathModelHom_mem S e w)))
  have hF : F = 1 := by
    apply MonoidHom.eq_of_eqOn_dense (wreath_eq_generated_s_swap (2 ^ n))
    intro w hw
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact hU _ ((mem_modelBase_iff S e _).mpr (by rw [element_mem_base]))
    · exact hW _ rfl
  obtain ⟨w, hw⟩ := exists_wreathModelHom_eq S e hvS
  have hvw : v = (wreathModelHom S e).codRestrict _ (fun w => hSN (wreathModelHom_mem S e w)) w :=
    Subtype.ext hw.symm
  rw [hvw]
  exact DFunLike.congr_fun hF w

include hnonab in
theorem exists_extension_of_family (hn : 2 ≤ n) {η : G}
    (hη : η ∈ Subgroup.normalizer (modelBase S e : Set G)) {E : Subgroup G}
    (hE : E ≤ Subgroup.centralizer ((S : Subgroup G) : Set G)) (χ : E → ℂ)
    (θt : Subgroup.centralizer ((S : Subgroup G) : Set G) → ℂ)
    (hθt : ∀ (c : Subgroup.centralizer ((S : Subgroup G) : Set G)) (y : E), (c : G) = y →
      θt c = χ y)
    {ψ : ∀ Q : Subgroup G, Subgroup.centralizer (Q : Set G) →* ℂˣ}
    (hψ : CompatibleCentralizerFamily 2 (S : Subgroup G) θt ψ) :
    ∃ lam : Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))} →* ℂˣ,
      (∀ (v : Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))}) (y : E),
        (v : G) = y → (lam v : ℂ) = χ y) ∧
      (∀ v : Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))},
        (v : G) ∈ (S : Subgroup G) → lam v = 1) ∧
      ∀ c c' : Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))},
        (c : G) ∈ Subgroup.centralizer (Subgroup.closure {wreathModelHom S e (Original.x (2 ^ n)),
          wreathModelHom S e (Original.x2 (2 ^ n))} : Set G) →
        (c' : G) = η⁻¹ * c * η → lam c' = lam c := by
  set J := wreathModelHom S e (Original.x (2 ^ n)) with hJdef
  set J₁ := wreathModelHom S e (Original.x2 (2 ^ n)) with hJ₁def
  have hJB : J ∈ modelBase S e := modelHom_x_mem_modelBase S e
  have hJ₁B : J₁ ∈ modelBase S e := modelHom_x2_mem_modelBase S e
  have hBS : modelBase S e ≤ (S : Subgroup G) := modelBase_le_sylow S e
  have hJ1 : J ≠ 1 := ne_one_of_orderOf (orderOf_x S e hn)
  have hZp : IsPGroup 2 (Subgroup.zpowers J) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (hBS hJB))
  have hZ1 : Subgroup.zpowers J ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hJ1
  have hTB : Subgroup.closure {J, J₁} ≤ modelBase S e := by
    rw [Subgroup.closure_le]
    intro z hz
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz <;> rw [hz]
    · exact hJB
    · exact hJ₁B
  have hJT : J ∈ Subgroup.closure {J, J₁} := Subgroup.subset_closure (Set.mem_insert _ _)
  have hcz := centralizer_zpowers_eq J
  let lam : Subgroup.centralizer {J} →* ℂˣ :=
    (ψ (Subgroup.zpowers J)).comp (MulEquiv.subgroupCongr hcz).toMonoidHom
  have hlam : ∀ (v : Subgroup.centralizer {J}) (g' : Subgroup.centralizer
      (Subgroup.zpowers J : Set G)), (g' : G) = v → lam v = ψ (Subgroup.zpowers J) g' := by
    intro v g' hg'
    have : g' = MulEquiv.subgroupCongr hcz v := Subtype.ext hg'
    rw [this]
    rfl
  have hres : ∀ (Q₁ : Subgroup G), IsPGroup 2 Q₁ → J ∈ Q₁ →
      ∀ (v : Subgroup.centralizer {J}) (g : Subgroup.centralizer (Q₁ : Set G)),
        (g : G) = v → lam v = ψ Q₁ g := by
    intro Q₁ hQ₁ hJQ₁ v g hg
    have hle : Subgroup.zpowers J ≤ Q₁ := Subgroup.zpowers_le.mpr hJQ₁
    let g' : Subgroup.centralizer (Subgroup.zpowers J : Set G) :=
      ⟨v, hcz ▸ v.2⟩
    rw [hlam v g' rfl]
    exact hψ.2.2.1 _ _ hZp hZ1 hQ₁ hle g g' hg.symm
  have hBp : IsPGroup 2 (modelBase S e) := S.isPGroup'.to_le hBS
  have hB1 : modelBase S e ≠ ⊥ := by
    intro h
    apply hJ1
    have := hJB
    rw [h, Subgroup.mem_bot] at this
    exact this
  have hlamU : ∀ v : Subgroup.centralizer {J}, (v : G) ∈ modelBase S e → lam v = 1 := by
    intro v hvB
    have hvC : (v : G) ∈ Subgroup.centralizer (modelBase S e : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact modelBase_commute S e _ _ hb hvB
    rw [hres _ hBp hJB v ⟨v, hvC⟩ rfl]
    exact hψ.1 _ hBp hB1 ⟨v, hvC⟩ hvB
  refine ⟨lam, ?_, ?_, ?_⟩
  ·
    intro v y hvy
    have hyS : (y : G) ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := hE y.2
    rw [hres _ S.isPGroup' (hBS hJB) v ⟨y, hyS⟩ hvy.symm,
      hψ.2.2.2 ⟨y, hyS⟩, hθt ⟨y, hyS⟩ y rfl]
  ·
    apply apply_sylow_of_base_swap S e hn lam hlamU
    intro v hv
    have hSN := sylow_le_centralizer_x S e hn
    have hJ₁N : J₁ ∈ Subgroup.centralizer {J} := hSN (hBS hJ₁B)
    have hvJ₁ : lam ⟨J₁, hJ₁N⟩ = 1 := hlamU _ hJ₁B
    have hprod : lam (⟨J₁, hJ₁N⟩ * v) = 1 :=
      apply_x2_swap hnonab S e hn lam _ (by rw [Subgroup.coe_mul, hv])
    rw [map_mul, hvJ₁, one_mul] at hprod
    exact hprod
  ·
    intro c c' hcC hc'
    have hηT : η ∈ Subgroup.normalizer (Subgroup.closure {J, J₁} : Set G) := by
      rw [← modelT_eq_closure S e (by omega)]
      exact modelBase_normalizer_le_modelT_normalizer n (by omega) S e hη
    have hc'C : (c' : G) ∈ Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G) := by
      rw [hc']
      exact LocalConfig.conj_mem_centralizer hηT hcC
    have hTp : IsPGroup 2 (Subgroup.closure {J, J₁}) := hBp.to_le hTB
    have hT1 : Subgroup.closure {J, J₁} ≠ ⊥ := by
      intro h
      apply hJ1
      have := hJT
      rw [h, Subgroup.mem_bot] at this
      exact this
    rw [hres _ hTp hJT c ⟨c, hcC⟩ rfl, hres _ hTp hJT c' ⟨c', hc'C⟩ rfl]
    exact CompatibleFamily.family_conj_invariant hψ hTp hT1
      ((Subgroup.normalizer _).inv_mem hηT) ⟨c, hcC⟩ ⟨c', hc'C⟩ (by rw [inv_inv]; exact hc')

end CFSG.Wreathed.CompatibleFamilies
