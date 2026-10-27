module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSONModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobFactor
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSporXONMat
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSONFacts

public noncomputable section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.ONSchreier CFSG.Sporadic.ONOddCore CFSG.Blueprint.NativeSporadic CFSG.Open

@[expose] def ONPair (G : Type) [Group G] (L K : Subgroup G) (u : G) : Prop :=
  u ∈ L ∧ orderOf u = 2 ∧ K ≤ L ∧ (∀ k ∈ K, k * u = u * k) ∧ Group.IsPerfect K ∧
    Nat.card K = 80640

section Local

theorem on_L_conj_mem {m k : Equiv.Perm (Fin N)} (hm : m ∈ onM) (hk : k ∈ onL) :
    m * k * m⁻¹ ∈ onL := by
  have hEi : (onL.subgroupOf onM).index = 2 := by
    have h := (onL.subgroupOf onM).card_mul_index
    rw [card_L_subgroupOf, card_onM] at h
    omega
  have hn := Subgroup.normal_of_index_eq_two hEi
  have := hn.conj_mem ⟨k, onL_le_M hk⟩ (Subgroup.mem_subgroupOf.2 hk) ⟨m, hm⟩
  exact Subgroup.mem_subgroupOf.1 this

theorem isQuasisimple_onL : CFSG.Open.IsQuasisimple ↥onL := by
  refine ⟨Group.isPerfect_def.1 inferInstance, ?_⟩
  have hcen : Subgroup.center ↥onL = lToS.ker := by
    rw [ker_lToS]
    ext x
    have h1 : (x : Equiv.Perm (Fin N)) ∈ CFSG.centerIn onL ↔ x ∈ Subgroup.center ↥onL := by
      rw [CFSG.centerIn_eq_map_center]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : y = x := Subtype.ext hyx
        rwa [this] at hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [← h1, onL_centerIn, Subgroup.mem_subgroupOf]
  have e1 : ↥onL ⧸ Subgroup.center ↥onL ≃* ↥onL ⧸ lToS.ker :=
    QuotientGroup.quotientMulEquivOfEq hcen
  have e2 := QuotientGroup.quotientKerEquivOfSurjective lToS lToS_surjective
  have hs : IsSimpleGroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
      CFSG.ComponentClassification.PSL3Four.F4) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (by norm_num)
  exact @MulEquiv.isSimpleGroup _ _ _ _ hs (e1.trans e2)

theorem on_standard {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (hL : IsSporadic L .ONan) (hQ : ONPair G L K u) :
    standardComponentIsStandard (K.subgroupOf L) := by
  obtain ⟨hu, hu2, hKL, hKu, hperf, hcard⟩ := hQ
  obtain ⟨Ψ, hΨ, hΨL, hΨR, hΨu⟩ := on_model hL hu hu2
  have hK₀ := on_K₀_eq hu hKL hKu hperf hcard Ψ hΨ hΨL hΨu
  obtain ⟨f⟩ := on_equiv_Pv hL
  let eK : ↥(K.subgroupOf L) ≃* ↥onL :=
    (Subgroup.equivMapOfInjective _ Ψ hΨ).trans (MulEquiv.subgroupCongr hK₀)
  have hquasi : CFSG.Open.IsQuasisimple ↥(K.subgroupOf L) :=
    isQuasisimple_of_mulEquiv' eK.symm isQuasisimple_onL
  have hcardK : Nat.card (K.subgroupOf L) = 80640 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv]
    exact hcard
  have hperfK : Group.IsPerfect (K.subgroupOf L) := isPerfect_subgroupOf_of_le hKL hperf
  have hu2' : orderOf (⟨u, hu⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk, hu2]
  have huC : (⟨u, hu⟩ : ↥L) ∈ centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    refine Subgroup.mem_centralizer_iff.2 fun k hk => ?_
    exact Subtype.ext (hKu k (Subgroup.mem_subgroupOf.1 hk))
  have huniq : ∀ t : ↥L, orderOf t = 2 →
      t ∈ centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L) →
      ∀ K'' : Subgroup ↥L, K'' ≤ centralizer ({t} : Set ↥L) → Group.IsPerfect K'' →
        Nat.card K'' = Nat.card (K.subgroupOf L) → K'' = K.subgroupOf L := by
    intro t ht2 htC K'' hK'' hperf'' hcard''
    have hKt : K.subgroupOf L ≤ centralizer ({t} : Set ↥L) := by
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 htC k hk
    have hC : Nat.card (centralizer ({t} : Set ↥L)) = 161280 := by
      rw [card_centralizer_of_mulEquiv f t]
      exact pv_card_centralizer (f t) (by rw [MulEquiv.orderOf_eq]; exact ht2)
    have hEi : ((K.subgroupOf L).subgroupOf (centralizer ({t} : Set ↥L))).index = 2 := by
      have h := ((K.subgroupOf L).subgroupOf (centralizer ({t} : Set ↥L))).card_mul_index
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKt).toEquiv, hcardK, hC] at h
      omega
    have hFi : (K''.subgroupOf (centralizer ({t} : Set ↥L))).index = 2 := by
      have h := (K''.subgroupOf (centralizer ({t} : Set ↥L))).card_mul_index
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'').toEquiv, hcard'', hcardK, hC] at h
      omega
    have heq := eq_of_index_two_of_isPerfect (isPerfect_subgroupOf_of_le hKt hperfK) hEi hFi
    rw [Subgroup.subgroupOf_inj, inf_eq_left.2 hK'', inf_eq_left.2 hKt] at heq
    exact heq
  have hcent : twoAdic (centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) <
      twoAdic (K.subgroupOf L) := by
    have h1 : (centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)).map Ψ ≤ onQ := by
      rintro _ ⟨c, hc, rfl⟩
      rw [← onM_centralizer_L]
      have hcomm : ∀ y ∈ onL, y * Ψ c = Ψ c * y := by
        rw [← hK₀]
        rintro _ ⟨k, hk, rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subgroup.mem_centralizer_iff.1 hc k hk
      refine ⟨?_, Subgroup.mem_centralizer_iff.2 hcomm⟩
      rw [onM_eq_centralizer_z]
      exact ⟨hΨL c, Subgroup.mem_centralizer_singleton_iff.2 (hcomm _ onz_mem_L).symm⟩
    have h2 := twoAdic_le_of_map_le Ψ hΨ h1
    have h3 : twoAdic onQ = 2 := by
      unfold twoAdic
      rw [card_onQ]
      exact factorization_two_pow_mul 2 (m := 1) (by norm_num) (by norm_num)
    have h4 : twoAdic (K.subgroupOf L) = 8 := by
      unfold twoAdic
      rw [hcardK, show (80640 : ℕ) = 2 ^ 8 * 315 by norm_num]
      exact factorization_two_pow_mul 8 (by norm_num) (by norm_num)
    omega
  exact standard_of_unique hquasi hu2' huC huniq hcent

open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.PSL3Four in
theorem conjAut_mul_dualAut_ne_one (A : GL (Fin 3) F4) :
    LinearFlag.conjAut 3 F4 A * LinearFlag.dualAut 3 F4 ≠ 1 := by
  intro h
  have h1 : LinearFlag.dualAut 3 F4 = LinearFlag.conjAut 3 F4 A⁻¹ := by
    rw [eq_inv_of_mul_eq_one_right h, map_inv]
  exact ProjectivePlane.dualAut_not_mem_semilinearAutGroup (n := 3) (K := F4) (by norm_num)
    (h1 ▸ LinearFlag.linearAutGroup_le_semilinearAutGroup
      (LinearFlag.conjAut_mem_linearAutGroup A⁻¹))

open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.PSL3Four in
theorem conjAut_mul_fieldAut_ne_one (A : GL (Fin 3) F4) :
    LinearFlag.conjAut 3 F4 A * LinearFlag.fieldAut 3 F4 frob ≠ 1 := fun h =>
  CFSG.ComponentClassification.HarrisLit.Hin.SporX.frob_ne_one
    (LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) A frob h).1

theorem on_pointwise_L_inner (β : MulAut Pv)
    (hβ : ∀ x : Pv, (x : Equiv.Perm (Fin N)) ∈ onL → β x = x) :
    β ∈ (MulAut.conj : Pv →* MulAut Pv).range := by
  by_contra hout
  have hz : β zP = zP := hβ zP onz_mem_L
  obtain ⟨-, hsurj, h⟩ := ctuc_on_outer_local_quotient_is_graph_or_field
  obtain ⟨-, -, -, A, hA | hA⟩ := h β hout hz
  · refine conjAut_mul_dualAut_ne_one A (MulEquiv.ext fun s => ?_)
    obtain ⟨a, rfl⟩ := hsurj s
    have h1 := hA a a (by
      have := hβ ⟨a, onM_le (onL_le_M a.2)⟩ a.2
      rw [this])
    exact h1.symm
  · refine conjAut_mul_fieldAut_ne_one A (MulEquiv.ext fun s => ?_)
    obtain ⟨a, rfl⟩ := hsurj s
    have h1 := hA a a (by
      have := hβ ⟨a, onM_le (onL_le_M a.2)⟩ a.2
      rw [this])
    exact h1.symm

theorem on_twoAdic_autCentralizer {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (hL : IsSporadic L .ONan) (hQ : ONPair G L K u) : twoAdic (autCentralizer L K) ≤ 2 := by
  obtain ⟨hu, hu2, hKL, hKu, hperf, hcard⟩ := hQ
  obtain ⟨Ψ, hΨ, hΨL, hΨR, hΨu⟩ := on_model hL hu hu2
  have hK₀ := on_K₀_eq hu hKL hKu hperf hcard Ψ hΨ hΨL hΨu
  let Ψ' : ↥L →* ↥Pv := Ψ.codRestrict Pv hΨL
  have hbij : Function.Bijective Ψ' := ⟨fun a b h => hΨ (congrArg Subtype.val h), fun y => by
    obtain ⟨x, hx⟩ := hΨR y y.2
    exact ⟨x, Subtype.ext hx⟩⟩
  let ψ : ↥L ≃* ↥Pv := MulEquiv.ofBijective Ψ' hbij
  let Θ : MulAut ↥L →* MulAut ↥Pv := (MulAut.congr ψ).toMonoidHom
  have hΘ : Function.Injective Θ := (MulAut.congr ψ).injective
  have hQP : onQ ≤ Pv := onQ_le_L.trans onL_le
  have h1 : (autCentralizer L K).map Θ ≤
      (onQ.subgroupOf Pv).map (MulAut.conj : ↥Pv →* MulAut ↥Pv) := by
    rintro _ ⟨α, hα, rfl⟩
    have hβ : ∀ x : Pv, (x : Equiv.Perm (Fin N)) ∈ onL → (MulAut.congr ψ α) x = x := by
      intro x hx
      obtain ⟨k, rfl⟩ := ψ.surjective x
      have h0 : Ψ k ∈ (K.subgroupOf L).map Ψ := by
        rw [hK₀]
        exact hx
      obtain ⟨k', hk', hkk⟩ := h0
      have hk'k : k' = k := hΨ hkk
      rw [hk'k] at hk'
      have hk : (k : G) ∈ K := Subgroup.mem_subgroupOf.1 hk'
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hα k hk]
    obtain ⟨p, hp⟩ := on_pointwise_L_inner _ hβ
    refine ⟨p, ?_, hp⟩
    show p ∈ onQ.subgroupOf Pv
    rw [Subgroup.mem_subgroupOf]
    have hcomm : ∀ y ∈ onL, y * (p : Equiv.Perm (Fin N)) = (p : Equiv.Perm (Fin N)) * y := by
      intro y hy
      have h2 := hβ ⟨y, onL_le hy⟩ hy
      rw [← hp, MulAut.conj_apply] at h2
      have h3 : p * (⟨y, onL_le hy⟩ : Pv) = (⟨y, onL_le hy⟩ : Pv) * p := by
        calc p * (⟨y, onL_le hy⟩ : Pv) = p * ⟨y, onL_le hy⟩ * p⁻¹ * p := by group
          _ = ⟨y, onL_le hy⟩ * p := by rw [h2]
      exact (congrArg Subtype.val h3).symm
    rw [← onM_centralizer_L]
    refine ⟨?_, Subgroup.mem_centralizer_iff.2 hcomm⟩
    rw [onM_eq_centralizer_z]
    exact ⟨p.2, Subgroup.mem_centralizer_singleton_iff.2 (hcomm _ onz_mem_L).symm⟩
  have h2 := twoAdic_le_of_map_le Θ hΘ h1
  have h3 : twoAdic ((onQ.subgroupOf Pv).map (MulAut.conj : ↥Pv →* MulAut ↥Pv)) ≤
      twoAdic (onQ.subgroupOf Pv) := by
    unfold twoAdic
    exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
      (Subgroup.card_map_dvd _ _) 2
  have h4 : twoAdic (onQ.subgroupOf Pv) = 2 := by
    unfold twoAdic
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv, card_onQ]
    exact factorization_two_pow_mul 2 (m := 1) (by norm_num) (by norm_num)
  omega

theorem solomonLocal_on {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (hL : IsSporadic L .ONan) (hQ : ONPair G L K u) : SolomonLocal L K u := by
  obtain ⟨f⟩ := on_equiv_Pv hL
  obtain ⟨e⟩ := hL
  have e' : ↥L ≃* CFSG.Blueprint.NativeSporadic.ON := e
  have hsimple := CFSG.Sporadic.ON.fam_on_simplicity.2.2
  exact
  { simpleL := @MulEquiv.isSimpleGroup _ _ _ _ hsimple e'
    nonabelianL := not_comm_of_equiv f
    u_order := hQ.2.1
    u_mem := hQ.1
    K_le := hQ.2.2.1
    u_mem_centralizer_K := Subgroup.mem_centralizer_iff.2 fun k hk => hQ.2.2.2.1 k hk
    standard_in_L := on_standard ⟨e⟩ hQ
    autCentralizer_two := on_twoAdic_autCentralizer ⟨e⟩ hQ }

end Local

end CFSG.EvenSporadicStandard.Solomon78
