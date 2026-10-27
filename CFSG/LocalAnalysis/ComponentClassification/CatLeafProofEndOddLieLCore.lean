module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieQuat
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndInputs

public section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddCore

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.FooteLit

structure Config {X : Type} [Group X] (z : X) (K D : Subgroup X) : Prop where
  twoComp : IsTwoComponentAt z K
  unique : ∀ K₂ : Subgroup X, IsTwoComponentAt z K₂ → K₂ = K
  simple : IsSimpleGroup (K ⧸ pPrimeCore 2 K)
  foote : FooteFamilyType K
  mem_D : z ∈ D
  D_le : D ≤ centralizer ({z} : Set X) ⊓ coreActionKernel K
  dihedral : AschbacherTheorem3.IsDihedralTwoGroup D
  card_D : 8 ≤ Nat.card D
  pump : ∀ b ∈ D, orderOf b = 2 → ∃ Y : Subgroup X, IsTwoComponentAt b Y ∧
    Nonempty (Y ⧸ pPrimeCore 2 Y ≃* K ⧸ pPrimeCore 2 K)

section Transport

variable {X Y : Type} [Group X] [Group Y]

noncomputable def quotMapEquiv (e : X ≃* Y) (K : Subgroup X) :
    K.map e.toMonoidHom ⧸ pPrimeCore 2 (K.map e.toMonoidHom) ≃* K ⧸ pPrimeCore 2 K :=
  (QuotientGroup.congr _ _ (K.equivMapOfInjective e.toMonoidHom e.injective)
    (pPrimeCore_map_iso 2 _)).symm

theorem isTwoComponentAt_map [Finite X] [Finite Y] (e : X ≃* Y) {a : X} {L : Subgroup X}
    (h : IsTwoComponentAt a L) : IsTwoComponentAt (e a) (L.map e.toMonoidHom) := by
  obtain ⟨ha, hLa, hLpc⟩ := h
  refine ⟨by rw [MulEquiv.orderOf_eq]; exact ha, ?_, isPComponent_map_centralizer e hLa hLpc⟩
  rw [← map_centralizer_singleton_mulEquiv e a]
  exact map_mono hLa

theorem mem_coreActionKernel_map (e : X ≃* Y) {L : Subgroup X} {b : X}
    (hb : b ∈ coreActionKernel L) : e b ∈ coreActionKernel (L.map e.toMonoidHom) := by
  refine ⟨mem_normalizer_iff.mpr fun y => ?_, fun y hy => ?_⟩
  · obtain ⟨x, rfl⟩ := e.surjective y
    rw [show e b * e x * (e b)⁻¹ = e (b * x * b⁻¹) by simp only [map_mul, map_inv]]
    rw [mem_map_equiv, mem_map_equiv, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    exact mem_normalizer_iff.mp hb.1 x
  · obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    have hmap : ((pPrimeCore 2 L).map L.subtype).map e.toMonoidHom =
        (pPrimeCore 2 (L.map e.toMonoidHom)).map (L.map e.toMonoidHom).subtype := by
      let f : L ≃* L.map e.toMonoidHom := L.equivMapOfInjective e.toMonoidHom e.injective
      have hcomm : e.toMonoidHom.comp L.subtype =
          (L.map e.toMonoidHom).subtype.comp f.toMonoidHom := by
        ext j
        rfl
      rw [map_map, hcomm, ← map_map, pPrimeCore_map_iso 2 f]
    rw [← hmap]
    refine ⟨x⁻¹ * b⁻¹ * x * b, hb.2 x hx, ?_⟩
    change e (x⁻¹ * b⁻¹ * x * b) = _
    simp only [map_mul, map_inv]
    rfl

theorem map_map_symm (e : X ≃* Y) (M : Subgroup Y) :
    (M.map e.symm.toMonoidHom).map e.toMonoidHom = M := by
  ext y
  rw [mem_map_equiv, mem_map_equiv, MulEquiv.symm_symm, MulEquiv.apply_symm_apply]

theorem Config.map [Finite X] [Finite Y] (e : X ≃* Y) {z : X} {K D : Subgroup X}
    (h : Config z K D) : Config (e z) (K.map e.toMonoidHom) (D.map e.toMonoidHom) where
  twoComp := isTwoComponentAt_map e h.twoComp
  unique K₂ hK₂ := by
    have h1 := isTwoComponentAt_map e.symm hK₂
    rw [MulEquiv.symm_apply_apply] at h1
    rw [← h.unique _ h1, map_map_symm]
  simple := (MulEquiv.isSimpleGroup_congr (quotMapEquiv e K)).mpr h.simple
  foote := footeFamilyType_of_mulEquiv (K.equivMapOfInjective e.toMonoidHom e.injective).symm
    h.foote
  mem_D := mem_map_of_mem _ h.mem_D
  D_le := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨hdz, hdK⟩ := mem_inf.mp (h.D_le hd)
    refine mem_inf.mpr ⟨?_, mem_coreActionKernel_map e hdK⟩
    rw [← map_centralizer_singleton_mulEquiv e z]
    exact mem_map_of_mem _ hdz
  dihedral := by
    obtain ⟨n, hn, ⟨φ⟩⟩ := h.dihedral
    exact ⟨n, hn, ⟨(D.equivMapOfInjective e.toMonoidHom e.injective).symm.trans φ⟩⟩
  card_D := by
    rw [Nat.card_congr (D.equivMapOfInjective e.toMonoidHom e.injective).symm.toEquiv]
    exact h.card_D
  pump := by
    rintro _ ⟨b, hb, rfl⟩ hb2
    obtain ⟨Y₀, hY₀, ⟨φ⟩⟩ := h.pump b hb (by rw [← MulEquiv.orderOf_eq e]; exact hb2)
    exact ⟨Y₀.map e.toMonoidHom, isTwoComponentAt_map e hY₀,
      ⟨((quotMapEquiv e Y₀).trans φ).trans (quotMapEquiv e K).symm⟩⟩

end Transport

variable {X : Type} [Group X]

theorem exists_dihedral_elements {D : Subgroup X} (hD : AschbacherTheorem3.IsDihedralTwoGroup D)
    (h8 : 8 ≤ Nat.card D) :
    ∃ b₁ ∈ D, ∃ b₂ ∈ D, ∃ r ∈ D, orderOf b₁ = 2 ∧ orderOf b₂ = 2 ∧ b₁ ≠ b₂ ∧ b₁ * r ≠ r * b₁ := by
  obtain ⟨n, hn, ⟨φ⟩⟩ := hD
  have hcard : Nat.card D = 2 * 2 ^ (n - 1) := by
    rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
  have hm : 4 ≤ 2 ^ (n - 1) := by omega
  have : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
  have : Fact (1 < 2 ^ (n - 1)) := ⟨by omega⟩
  refine ⟨(φ.symm (DihedralGroup.sr 0) : X), (φ.symm (DihedralGroup.sr 0)).2,
    (φ.symm (DihedralGroup.sr 1) : X), (φ.symm (DihedralGroup.sr 1)).2,
    (φ.symm (DihedralGroup.r 1) : X), (φ.symm (DihedralGroup.r 1)).2, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr]
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr]
  · intro h01
    have h1 := φ.symm.injective (Subtype.ext h01)
    have h2 : (0 : ZMod (2 ^ (n - 1))) = 1 := DihedralGroup.sr.inj h1
    have h3 := congrArg ZMod.val h2
    rw [ZMod.val_zero, ZMod.val_one] at h3
    exact zero_ne_one h3
  · intro hc
    have h1 : φ.symm (DihedralGroup.sr 0 * DihedralGroup.r 1) =
        φ.symm (DihedralGroup.r 1 * DihedralGroup.sr 0) := by
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
      exact hc
    have h2 := φ.symm.injective h1
    rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr] at h2
    have h3 : (0 : ZMod (2 ^ (n - 1))) + 1 = 0 - 1 := DihedralGroup.sr.inj h2
    have h4 : (2 : ZMod (2 ^ (n - 1))) = 0 := by linear_combination h3
    have h5 := congrArg ZMod.val h4
    rw [ZMod.val_zero, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)] at h5
    exact two_ne_zero h5

theorem Config.exists_involution_ne {z : X} {K D : Subgroup X} (h : Config z K D) :
    ∃ b ∈ D, orderOf b = 2 ∧ b ≠ z := by
  obtain ⟨b₁, hb₁, b₂, hb₂, -, -, h₁, h₂, h12, -⟩ := exists_dihedral_elements h.dihedral h.card_D
  by_cases hz : b₁ = z
  · exact ⟨b₂, hb₂, h₂, fun h2z => h12 (hz.trans h2z.symm)⟩
  · exact ⟨b₁, hb₁, h₁, hz⟩

theorem Config.exists_mul_ne {z : X} {K D : Subgroup X} (h : Config z K D) :
    ∃ x ∈ D, ∃ y ∈ D, x * y ≠ y * x := by
  obtain ⟨b₁, hb₁, -, -, r, hr, -, -, -, hne⟩ := exists_dihedral_elements h.dihedral h.card_D
  exact ⟨b₁, hb₁, r, hr, hne⟩

theorem coreActionKernel_le_centralizer {K : Subgroup X} (hK : pPrimeCore 2 K = ⊥) :
    coreActionKernel K ≤ centralizer (K : Set X) := by
  intro g hg
  rw [mem_centralizer_iff]
  intro j hj
  have h1 := hg.2 j hj
  rw [hK, Subgroup.map_bot, mem_bot] at h1
  have h2 : g⁻¹ * j * g = j := by
    calc g⁻¹ * j * g = j * (j⁻¹ * g⁻¹ * j * g) := by group
      _ = j := by rw [h1, mul_one]
  calc j * g = g * (g⁻¹ * j * g) := by group
    _ = g * j := by rw [h2]

theorem Config.false_of_quat [Finite X] {z : X} {K D : Subgroup X} (h : Config z K D)
    (H : Subgroup K) (e : H ≃* QuaternionGroup 2) : False :=
  false_of_footeFamilyType_quaternion h.simple h.foote H e

theorem Config.hasDihedralSylowTwo [Finite X] {z : X} {K D : Subgroup X} (h : Config z K D) :
    GorensteinWalter.HasDihedralSylowTwo (K ⧸ pPrimeCore 2 K) := by
  have hZ := center_quotient_pPrimeCore_eq_bot_of_footeFamilyType h.simple h.foote
  have hZ' : Open.fusionZStar K = pPrimeCore 2 K := (Sol78.fusionZStar_eq_iff K).2 hZ
  exact OutcomeLocal.hasDihedralSylowTwo_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZ'.symm)
    (FooteLit.hasDihedralSylowTwo_of_footeFamilyType h.foote)

theorem Config.false_of_pump_quat [Finite X] {z : X} {K D : Subgroup X} (h : Config z K D)
    {b : X} (hb : b ∈ D) (hb2 : orderOf b = 2)
    (hQ : ∀ Y : Subgroup X, IsTwoComponentAt b Y →
      ∃ H : Subgroup Y, Nonempty (H ≃* QuaternionGroup 2)) : False := by
  obtain ⟨Y, hY, ⟨φ⟩⟩ := h.pump b hb hb2
  obtain ⟨H, ⟨eH⟩⟩ := hQ Y hY
  have hdY : GorensteinWalter.HasDihedralSylowTwo (Y ⧸ pPrimeCore 2 Y) :=
    OutcomeLocal.hasDihedralSylowTwo_of_mulEquiv φ h.hasDihedralSylowTwo
  let ψ : H →* Y ⧸ pPrimeCore 2 Y := (QuotientGroup.mk' (pPrimeCore 2 Y)).comp H.subtype
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : (x : Y) ∈ pPrimeCore 2 Y := (QuotientGroup.eq_one_iff _).1 hx
    rw [eq_one_of_mem_pPrimeCore_of_quaternion eH hx']
    exact Subgroup.one_mem _
  exact false_of_quaternion_of_hasDihedralSylowTwo hdY ψ.range
    ((MonoidHom.ofInjective hψ).symm.trans eH)

theorem endOddLieInputFor_of_config (T : Finset Assembly.LowTwoRank.StatedLieTag)
    (hT : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X →
      ∀ (τ : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ), τ ∈ T → p.Prime → p ≠ 2 →
        Assembly.LowTwoRank.StatedLieAdmissible τ n p f → Blueprint.LieModel X τ n p f →
        ∀ (z : X) (K D : Subgroup X), Config z K D → False) :
    Sol78.F514.EndOddLieInputFor T := by
  intro X _ _ hX τ n p f hτ hp hp2 hadm hmod z t K P D hK huniq hs hF _ _ _ _ _ hzD hD _ hdih h8
    _ hpump
  exact (hT X hX τ n p f hτ hp hp2 hadm hmod z K D
    { twoComp := hK
      unique := huniq
      simple := hs
      foote := hF
      mem_D := hzD
      D_le := hD
      dihedral := hdih
      card_D := h8
      pump := fun b hb hb2 => by
        obtain ⟨Y, hY, -, hYK⟩ := hpump b hb hb2
        exact ⟨Y, hY, hYK⟩ }).elim

end CFSG.ComponentClassification.CatLeafProof.EndOddCore
