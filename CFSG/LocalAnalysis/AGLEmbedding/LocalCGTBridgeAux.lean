module

public import CFSG.LocalAnalysis.AGLEmbedding.NoXBlockBridgeAux

public section

namespace CFSG.AGLEmbedding.LocalCGT

open CFSG.QuasithinUnique CFSG.RankThree.PartOne CFSG.AGLEmbedding.NoXBlock
open scoped commutatorElement

variable {G : Type} [Group G]

theorem sq_mem_blockZ_of_ker {L : Subgroup G} {V : Type*} [AddGroup V] (hV : ∀ v : V, v + v = 0)
    (ψ : ↥(shortU ↥L) →* Multiplicative V) (hψ : ψ.ker = (shortC ↥L).subgroupOf (shortU ↥L))
    {u : G} (hu : u ∈ CGT.PushingUpLit.blockU L) : u ^ 2 ∈ CGT.PushingUpLit.blockZ L := by
  rw [← CGT.PushingUpLit.map_shortU_subtype] at hu
  obtain ⟨u0, hu0, rfl⟩ := hu
  have h1 : ψ ((⟨u0, hu0⟩ : ↥(shortU ↥L)) ^ 2) = 1 := by
    rw [map_pow]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul]
    exact hV _
  have h2 : (⟨u0, hu0⟩ : ↥(shortU ↥L)) ^ 2 ∈ ψ.ker := h1
  rw [hψ, Subgroup.mem_subgroupOf] at h2
  rw [← CGT.PushingUpLit.map_shortC_subtype]
  exact ⟨u0 ^ 2, h2, map_pow _ _ _⟩

theorem commutatorElement_sq_left {q l : G} (hc : ⁅q, l⁆ * q = q * ⁅q, l⁆) :
    ⁅q ^ 2, l⁆ = ⁅q, l⁆ ^ 2 := by
  rw [commutatorElement_def] at hc
  have h' : l * q⁻¹ * l⁻¹ * q = q * l * q⁻¹ * l⁻¹ := by
    calc l * q⁻¹ * l⁻¹ * q = q⁻¹ * (q * l * q⁻¹ * l⁻¹ * q) := by group
      _ = q⁻¹ * (q * (q * l * q⁻¹ * l⁻¹)) := by rw [hc]
      _ = q * l * q⁻¹ * l⁻¹ := by group
  calc ⁅q ^ 2, l⁆ = q * (q * l * q⁻¹ * l⁻¹) * l * q⁻¹ * l⁻¹ := by
        rw [commutatorElement_def, pow_two]; group
    _ = q * (l * q⁻¹ * l⁻¹ * q) * l * q⁻¹ * l⁻¹ := by rw [h']
    _ = ⁅q, l⁆ ^ 2 := by rw [commutatorElement_def, pow_two]; group

variable [Finite G]

theorem sq_eq_one_of_mem_blockU {L : Subgroup G} (hL : IsShortGroup ↥L)
    (hsq : ∀ u ∈ CGT.PushingUpLit.blockU L, u ^ 2 ∈ CGT.PushingUpLit.blockZ L) :
    ∀ v ∈ CGT.PushingUpLit.blockU L, v ^ 2 = 1 := by
  have hcomm : ∀ a ∈ CGT.PushingUpLit.blockU L, ∀ b ∈ CGT.PushingUpLit.blockU L,
      a * b = b * a := fun a ha b hb =>
    CGT.PushingUpLit.blockU_comm_of_short hL a ha b (CGT.PushingUpLit.blockU_le_oTwoIn L hb)
  let E : Subgroup G :=
    { carrier := {u | u ∈ CGT.PushingUpLit.blockU L ∧ u ^ 2 = 1}
      one_mem' := ⟨one_mem _, one_pow 2⟩
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        exact ⟨mul_mem ha hb, by rw [Commute.mul_pow (hcomm a ha b hb) 2, ha2, hb2, one_mul]⟩
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        exact ⟨inv_mem ha, by rw [inv_pow, ha2, inv_one]⟩ }
  have key : ∀ q ∈ CGT.PushingUpLit.oTwoIn L, ∀ l ∈ L, ⁅q, l⁆ ^ 2 = 1 := by
    intro q hq
    have hsqc : ∀ l ∈ L, ⁅q ^ 2, l⁆ = ⁅q, l⁆ ^ 2 := fun l hl =>
      commutatorElement_sq_left (CGT.PushingUpLit.blockU_comm_of_short hL _
        (Subgroup.commutator_mem_commutator hq hl) q hq)
    have hZ : ∀ l ∈ L, ⁅q ^ 2, l⁆ ∈ CGT.PushingUpLit.blockZ L := fun l hl => by
      rw [hsqc l hl]
      exact hsq _ (Subgroup.commutator_mem_commutator hq hl)
    let θ : ↥L →* G :=
      { toFun := fun l => ⁅q ^ 2, (l : G)⁆
        map_one' := commutatorElement_one_right _
        map_mul' := fun a b => by
          have hb : (a : G) * ⁅q ^ 2, (b : G)⁆ = ⁅q ^ 2, (b : G)⁆ * a :=
            Subgroup.mem_centralizer_iff.mp (hZ b b.2).2 a a.2
          show ⁅q ^ 2, (a : G) * b⁆ = ⁅q ^ 2, (a : G)⁆ * ⁅q ^ 2, (b : G)⁆
          calc ⁅q ^ 2, (a : G) * b⁆ =
                ⁅q ^ 2, (a : G)⁆ * ((a : G) * ⁅q ^ 2, (b : G)⁆ * (a : G)⁻¹) := by
                simp only [commutatorElement_def]; group
            _ = ⁅q ^ 2, (a : G)⁆ * ⁅q ^ 2, (b : G)⁆ := by rw [hb, mul_inv_cancel_right] }
    have hker : θ.ker = ⊤ := by
      refine (CGT.PushingUpLit.oResidualTwo_eq_top_iff).1 hL.residual_eq _ inferInstance
        fun g => ?_
      have hmem : θ g ∈ CGT.PushingUpLit.oTwoIn L :=
        CGT.PushingUpLit.blockU_le_oTwoIn L (hZ g g.2).1
      obtain ⟨k, hk⟩ := CGT.PushingUpLit.isPGroup_oTwoIn L ⟨θ g, hmem⟩
      refine ⟨k, ?_⟩
      rw [MonoidHom.mem_ker, map_pow]
      exact congrArg Subtype.val hk
    intro l hl
    rw [← hsqc l hl]
    have : (⟨l, hl⟩ : ↥L) ∈ θ.ker := hker ▸ Subgroup.mem_top _
    exact this
  have hle : CGT.PushingUpLit.blockU L ≤ E :=
    Subgroup.commutator_le.2 fun q hq l hl =>
      ⟨Subgroup.commutator_mem_commutator hq hl, key q hq l hl⟩
  exact fun v hv => (hle hv).2

theorem isShort2_of_isShortGroup {L : Subgroup G} (hL : IsShortGroup ↥L)
    (hsq : ∀ v ∈ CGT.PushingUpLit.blockU L, v ^ 2 = 1)
    (htype : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∨ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3) :
    IsShort2 L := by
  refine ⟨fun N _ hp => ?_, ?_, ⟨?_, ?_⟩, htype, ?_, ?_⟩
  · exact (CGT.PushingUpLit.oResidualTwo_eq_top_iff).1 hL.residual_eq N inferInstance
      ((CGT.PushingUpLit.isPGroup_two_quotient_iff N).1 hp)
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hchar : CFSG.IsCharacteristicP 2 ↥L :=
      (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥L 2).mpr hL.fitting_eq
    intro x hx
    obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp hx
    have hmem : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.centralizer (CFSG.pCore 2 ↥L : Set ↥L) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have hr' : (r : G) ∈ CFSG.Open.pCoreOf 2 L := ⟨r, by assumption, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC _ hr')
    exact ⟨⟨x, hxL⟩, by exact hchar hmem, rfl⟩
  · rw [blockU_eq_lit, blockQ_eq_oTwoIn]
    intro u hu
    exact Subgroup.mem_inf.mpr ⟨CGT.PushingUpLit.blockU_le_oTwoIn L hu,
      Subgroup.mem_centralizer_iff.mpr fun r hr =>
        (CGT.PushingUpLit.blockU_comm_of_short hL u hu r hr).symm⟩
  · rw [blockU_eq_lit]
    exact hsq
  · rw [blockU_eq_lit, blockZ_eq_lit]
    exact CGT.PushingUpLit.blockZ_lt_of_short hL
  · intro W hZW hWU hLW
    rw [blockU_eq_lit] at hWU ⊢
    rw [blockZ_eq_lit] at hZW ⊢
    exact CGT.PushingUpLit.blockU_irred_of_short hL W hZW hWU fun g hg n hn =>
      (Subgroup.mem_normalizer_iff.mp (hLW hg) n).mp hn

omit [Finite G] in
theorem three_dvd_card_alternatingGroup {m : ℕ} (hm : 3 ≤ m) :
    3 ∣ Nat.card (alternatingGroup (Fin m)) := by
  have hσ : (Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩ *
      Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨2, by omega⟩).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff])
  have h3 : orderOf (⟨_, hσ.mem_alternatingGroup⟩ : alternatingGroup (Fin m)) = 3 := by
    rw [Subgroup.orderOf_mk, hσ.orderOf]
  rw [← h3]
  exact orderOf_dvd_natCard _

omit [Finite G] in
theorem two_dvd_card_specialLinearGroup {F : Type} [Field F] [CharP F 2] :
    2 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
  let t : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have ht2 : t ^ 2 = 1 := by
    rw [pow_two]
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;>
      simp [t, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  have ht1 : t ≠ 1 := by
    intro h
    have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [t] at this
  have h2 : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have := orderOf_dvd_natCard t
  rwa [h2] at this

theorem quotient_type_of_inClassX {L : Subgroup G} (h : InClassX ↥L) :
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∨ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 := by
  obtain ⟨hL, htype⟩ := h
  rcases hL.quotient_type with hq | hp
  · exact Or.inl hq
  · right
    rcases htype with ⟨n, hn, φ, -⟩ | ⟨n, -, φ, -⟩
    · have h3 : 3 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
        rw [Nat.card_congr φ.toEquiv]
        exact three_dvd_card_alternatingGroup (by omega)
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3).symm
    · exfalso
      have h2 : 2 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
        rw [Nat.card_congr φ.toEquiv]
        exact two_dvd_card_specialLinearGroup
      have hc2 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2 :=
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
      have hpg : IsPGroup 2 (↥L ⧸ CFSG.pCore 2 ↥L) :=
        IsPGroup.of_card (n := 1) (by rw [hc2, pow_one])
      have htop : CFSG.pCore 2 ↥L = ⊤ :=
        (CGT.PushingUpLit.oResidualTwo_eq_top_iff).1 hL.residual_eq _ inferInstance
          ((CGT.PushingUpLit.isPGroup_two_quotient_iff _).1 hpg)
      have hidx : (CFSG.pCore 2 ↥L).index = 2 := hc2
      rw [htop, Subgroup.index_top] at hidx
      omega

omit [Finite G] in
theorem coe_shortUEquiv_symm (L : Subgroup G) (w : ↥(QuasithinUnique.blockU L)) :
    ((((shortUEquiv L).symm w : ↥(shortU ↥L)) : ↥L) : G) = (w : G) := by
  have h := coe_shortUEquiv L ((shortUEquiv L).symm w)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

omit [Finite G] in
theorem shortUEquiv_symm_conj {L : Subgroup G} (l : ↥L) {u v : ↥(QuasithinUnique.blockU L)}
    (huv : (v : G) = l * u * l⁻¹) :
    ∃ hmem : l * (((shortUEquiv L).symm u : ↥(shortU ↥L)) : ↥L) * l⁻¹ ∈ shortU ↥L,
      (shortUEquiv L).symm v = ⟨_, hmem⟩ := by
  have he : (((shortUEquiv L).symm v : ↥(shortU ↥L)) : ↥L) =
      l * (((shortUEquiv L).symm u : ↥(shortU ↥L)) : ↥L) * l⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_shortUEquiv_symm]
    exact huv
  exact ⟨he ▸ ((shortUEquiv L).symm v).2, Subtype.ext he⟩

omit [Finite G] in
theorem ker_comp_mk' {L : Subgroup G} {A : Type*} [Group A] (φ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* A) :
    ((φ : (↥L ⧸ CFSG.pCore 2 ↥L) →* A).comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).ker =
      CFSG.pCore 2 ↥L := by
  ext x
  rw [MonoidHom.mem_ker]
  show φ (QuotientGroup.mk x) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

omit [Finite G] in
theorem isLin2Type_of_isNaturalSLTwoModule {L : Subgroup G} {n : ℕ} (hn : n ≠ 0)
    (h : IsNaturalSLTwoModule ↥L n) : IsLin2Type L n := by
  obtain ⟨φ, ψ, hψs, hψk, hψe⟩ := h
  let _ : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 n hn
  refine ⟨GaloisField 2 n, inferInstance, inferInstance, hcard,
    (φ : (↥L ⧸ CFSG.pCore 2 ↥L) →* _).comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L)),
    φ.surjective.comp (QuotientGroup.mk'_surjective _), ker_comp_mk' φ,
    ψ.comp (shortUEquiv L).symm.toMonoidHom, hψs.comp (shortUEquiv L).symm.surjective, ?_, ?_⟩
  · ext w
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← MonoidHom.mem_ker,
      hψk, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, ← shortUEquiv_mem_blockZ_iff,
      MulEquiv.apply_symm_apply]
  · intro l u v huv
    obtain ⟨hmem, hv⟩ := shortUEquiv_symm_conj l huv
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hv, hψe l _ ((shortUEquiv L).symm u).2 hmem]
    rfl

omit [Finite G] in
theorem isAltType_of_isNaturalAltModule {L : Subgroup G} {n : ℕ}
    (h : IsNaturalAltModule ↥L n) : IsAltType L (2 * n + 1) := by
  obtain ⟨φ, ψ, hsum, hsurj, hψk, hψe⟩ := h
  have hmem : ∀ w : ↥(QuasithinUnique.blockU L),
      Multiplicative.toAdd (ψ ((shortUEquiv L).symm w)) ∈ evenWeight (2 * n + 1) := fun w =>
    AddMonoidHom.mem_ker.mpr (hsum _)
  let β : ↥(QuasithinUnique.blockU L) →* Multiplicative ↥(evenWeight (2 * n + 1)) :=
    { toFun := fun w => Multiplicative.ofAdd
        ⟨Multiplicative.toAdd (ψ ((shortUEquiv L).symm w)), hmem w⟩
      map_one' := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        simp }
  have hβ : ∀ w, ((Multiplicative.toAdd (β w) : evenWeight (2 * n + 1)) :
      Fin (2 * n + 1) → ZMod 2) = Multiplicative.toAdd (ψ ((shortUEquiv L).symm w)) :=
    fun _ => rfl
  refine ⟨(φ : (↥L ⧸ CFSG.pCore 2 ↥L) →* _).comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L)),
    φ.surjective.comp (QuotientGroup.mk'_surjective _), ker_comp_mk' φ, β, ?_, ?_, ?_⟩
  · intro w
    have hw : ∑ i, ((Multiplicative.toAdd w : evenWeight (2 * n + 1)) :
        Fin (2 * n + 1) → ZMod 2) i = 0 :=
      AddMonoidHom.mem_ker.mp (Multiplicative.toAdd w).2
    obtain ⟨u, hu⟩ := hsurj _ hw
    refine ⟨shortUEquiv L u, Multiplicative.toAdd.injective (Subtype.ext ?_)⟩
    rw [hβ, MulEquiv.symm_apply_apply, hu]
    rfl
  · ext w
    have h1 : β w = 1 ↔ ψ ((shortUEquiv L).symm w) = 1 := by
      rw [← Multiplicative.toAdd.injective.eq_iff, ← Multiplicative.toAdd.injective.eq_iff,
        ← Subtype.coe_inj, hβ]
      rfl
    rw [MonoidHom.mem_ker, h1, ← MonoidHom.mem_ker, hψk, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, ← shortUEquiv_mem_blockZ_iff, MulEquiv.apply_symm_apply]
  · intro l u v huv i
    obtain ⟨hmem, hv⟩ := shortUEquiv_symm_conj l huv
    rw [hβ, hβ, hv, hψe l _ ((shortUEquiv L).symm u).2 hmem]
    rfl

theorem inClassXBlock_of_inClassX {L : Subgroup G} (h : InClassX ↥L) : InClassXBlock L := by
  have hq := quotient_type_of_inClassX h
  obtain ⟨hL, htype⟩ := h
  have hsq : ∀ u ∈ CGT.PushingUpLit.blockU L, u ^ 2 ∈ CGT.PushingUpLit.blockZ L := by
    rcases htype with ⟨n, -, -, ψ, -, -, hψk, -⟩ | ⟨n, -, -, ψ, -, hψk, -⟩
    · exact fun u hu => sq_mem_blockZ_of_ker
        (fun v => funext fun i => CharTwo.add_self_eq_zero (v i)) ψ hψk hu
    · exact fun u hu => sq_mem_blockZ_of_ker
        (fun v => funext fun i => CharTwo.add_self_eq_zero (v i)) ψ hψk hu
  refine ⟨isShort2_of_isShortGroup hL (sq_eq_one_of_mem_blockU hL hsq) hq, ?_⟩
  rcases htype with ⟨n, hn, hm⟩ | ⟨n, hn, hm⟩
  · exact Or.inr ⟨n, hn, isAltType_of_isNaturalAltModule hm⟩
  · exact Or.inl ⟨n, hn, isLin2Type_of_isNaturalSLTwoModule (by omega) hm⟩

end CFSG.AGLEmbedding.LocalCGT
