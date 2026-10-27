module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdLie
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Ex
public import CFSG.ClassicalInvolution.Q3.Q3T8E4NRB
public import CFSG.ClassicalInvolution.Q3.Q3T6AutInn
public import CFSG.ClassicalInvolution.AschTight.S1916F2a
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStarBasic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmA
public import CFSG.ClassicalInvolution.Q3.Q3DBFuzzyEdge
public import CFSG.ClassicalInvolution.Q3.Q3KCGen
public import CFSG.ClassicalInvolution.Q3.Q3NFLink
public import CFSG.ClassicalInvolution.Q3.Q3T6BSymEx
public import CFSG.ClassicalInvolution.Q3.Q3T8E274B
public import CFSG.ClassicalInvolution.Q3.Q3TIMain
public import CFSG.ClassicalInvolution.Q3.Q3TIYOAMain
public import CFSG.ClassicalInvolution.Q3.Q3TKMem
public import CFSG.ClassicalInvolution.Q3.TL4Conn26E4A
public import CFSG.ClassicalInvolution.Q3.TL4Conn274M
public import CFSG.ClassicalInvolution.Q3.TL4SepSub
public import CFSG.ClassicalInvolution.SmallCases.NDBH5
public import CFSG.ClassicalInvolution.SmallCases.NobqFinal

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement MatrixGroups

section Aut

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem map_centralizer_singleton_mulAut (σ : MulAut X) (z : X) :
    (Subgroup.centralizer ({z} : Set X)).map σ.toMonoidHom =
      Subgroup.centralizer ({σ z} : Set X) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hw
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hw]
  · intro hy
    refine ⟨σ.symm y, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply σ.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using hy

omit [Finite X] in
theorem isClassicalMember3_mulAut {L : Subgroup X} {z : X} (h : IsClassicalMember3 L z)
    (σ : MulAut X) : IsClassicalMember3 (L.map σ.toMonoidHom) (σ z) where
  orderOf_eq_two := by rw [MulEquiv.orderOf_eq]; exact h.orderOf_eq_two
  mem := ⟨z, h.mem, rfl⟩
  subnormal := by
    rw [← map_centralizer_singleton_mulAut]
    exact isSubnormal_map_mulEquiv σ h.subnormal
  nonempty_equiv := by
    obtain ⟨e'⟩ := h.nonempty_equiv
    let e : L ≃* L.map σ.toMonoidHom := L.equivMapOfInjective σ.toMonoidHom σ.injective
    have hO : (classicalInvolutionOddCore L).map e.toMonoidHom =
        classicalInvolutionOddCore (L.map σ.toMonoidHom) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    exact ⟨(QuotientGroup.congr _ _ e hO).symm.trans e'⟩

variable {Δ : Set (Subgroup X)} {J L : Subgroup X} {u : X}

omit [Finite X] in
theorem satU_eq_of_oddCoreIn_eq_bot
    (hO : Balance.oddCoreIn (Subgroup.centralizer ({u} : Set X)) = ⊥) :
    satU (.sl2 3 1) L u = L := by
  rw [satU_of_isSolvableType U4.solvableType_three, hO, sup_bot_eq]

theorem lift_map_eq_of_map_eq (hΩ : HypOmegaGen Δ) (hJ : J ∈ Δ) (h : IsLiftOf J L u)
    (hO : Balance.oddCoreIn (Subgroup.centralizer ({u} : Set X)) = ⊥) (σ : MulAut X)
    (hσJ : J.map σ.toMonoidHom = J) (hσu : σ u = u) : L.map σ.toMonoidHom = L := by
  have hm := isClassicalMember3_mulAut h.member σ
  rw [hσu] at hm
  have h' : IsLiftOf J (L.map σ.toMonoidHom) u :=
    ⟨h.inv, hσJ ▸ Subgroup.map_mono h.le, hm⟩
  have := liftFam_eq_of_le hΩ (satU_mem_liftFam hJ h') (satU_mem_liftFam hJ h) hJ h'.le_sat
    h.le_sat
  rwa [satU_eq_of_oddCoreIn_eq_bot hO, satU_eq_of_oddCoreIn_eq_bot hO] at this

theorem lift_oddCore_eq_bot (h : IsLiftOf J L u)
    (hO : Balance.oddCoreIn (Subgroup.centralizer ({u} : Set X)) = ⊥) :
    classicalInvolutionOddCore ↥L = ⊥ := by
  have h1 := Balance.oddCoreIn_le_of_isSubnormal h.member.subnormal
  rw [hO, le_bot_iff] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h1

theorem factorization_two_natCard_sl2Three :
    (Nat.card SL(2, ZMod 3)).factorization 2 = 3 := by
  rw [Q3T6.Aut.sl2Three_natCard]
  have h : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem lift_fix_of_fix (hΩ : HypOmegaGen Δ) (hJ : J ∈ Δ) (hJ2 : IsPGroup 2 ↥J)
    (h : IsLiftOf J L u) (hO : Balance.oddCoreIn (Subgroup.centralizer ({u} : Set X)) = ⊥)
    (σ : MulAut X) (hfix : ∀ j ∈ J, σ j = j) : ∀ k ∈ L, σ k = k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσJ : J.map σ.toMonoidHom = J := by
    ext j
    constructor
    · rintro ⟨j', hj', rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [hfix j' hj']
      exact hj'
    · intro hj
      exact ⟨j, hj, hfix j hj⟩
  have hL := lift_map_eq_of_map_eq hΩ hJ h hO σ hσJ (hfix u h.inv.mem)
  obtain ⟨e⟩ := h.member.nonempty_equiv_sl2 (lift_oddCore_eq_bot h hO)
  let τ : MulAut ↥L :=
    (L.equivMapOfInjective σ.toMonoidHom σ.injective).trans (MulEquiv.subgroupCongr hL)
  have hτ : ∀ k : ↥L, (τ k : X) = σ k := fun _ => rfl
  let α : MulAut SL(2, ZMod 3) := (e.symm.trans τ).trans e
  have hα : ∀ k : ↥L, α (e k) = e (τ k) := by
    intro k
    show e (τ (e.symm (e k))) = e (τ k)
    rw [MulEquiv.symm_apply_apply]
  set Q : Subgroup SL(2, ZMod 3) := (J.subgroupOf L).map e.toMonoidHom with hQdef
  have hQfix : ∀ x ∈ Q, α x = x := by
    rintro _ ⟨j, hj, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [hα]
    congr 1
    apply Subtype.ext
    rw [hτ]
    exact hfix j (Subgroup.mem_subgroupOf.mp hj)
  have hJL2 : IsPGroup 2 ↥(J.subgroupOf L) :=
    hJ2.of_equiv (Subgroup.subgroupOfEquivOfLe h.le).symm
  have hQ2 : IsPGroup 2 ↥Q := hJL2.map _
  obtain ⟨P, hQP⟩ := hQ2.exists_le_sylow
  have hJs : IsSylow2In J L := by
    have := isSylow2In_of_le_liftFam hΩ hJ hJ2 (satU_mem_liftFam hJ h) h.le_sat
    rwa [satU_eq_of_oddCoreIn_eq_bot hO] at this
  have hcardJ : Nat.card ↥J = 8 := natCard_of_isSylow2In_classicalMember3 h.member hJs
  have hcardQ : Nat.card ↥Q = 8 := by
    rw [hQdef, Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv, hcardJ]
  have hcardP : Nat.card ↥(P : Subgroup SL(2, ZMod 3)) = 8 := by
    rw [Sylow.card_eq_multiplicity, factorization_two_natCard_sl2Three]
    norm_num
  have hQP' : Q = P := Subgroup.eq_of_le_of_card_ge hQP (by rw [hcardQ, hcardP])
  have hα1 := Q3T6.sl2Three_mulAut_eq_one_of_fixes_sylow P α fun x hx => hQfix x (hQP' ▸ hx)
  intro k hk
  have h1 : α (e ⟨k, hk⟩) = e ⟨k, hk⟩ := by
    rw [hα1]
    rfl
  rw [hα] at h1
  have h2 := congrArg Subtype.val (e.injective h1)
  rwa [hτ] at h2

theorem SecIdLie3.liftFam_noTwins {K : Subgroup X} {S : Sylow 2 K} {z : X} (hd : TightDatum K S z)
    (hnt : ∀ L ∈ CoreAssembly.conjClass (tightCore K),
      ∀ L' ∈ twinSet (CoreAssembly.conjClass (tightCore K)) L, L' = L) :
    ∀ M ∈ liftFam (CoreAssembly.conjClass (tightCore K)),
      ∀ M' ∈ twinSet (liftFam (CoreAssembly.conjClass (tightCore K))) M, M' = M := by
  have hΩ := hd.hypOmegaGen
  rintro M hM M' ⟨hM', w, hw, hw'⟩
  obtain ⟨J, hJ, hJM⟩ := exists_core_of_mem_liftFam hM
  obtain ⟨J', hJ', hJM'⟩ := exists_core_of_mem_liftFam hM'
  obtain ⟨v, hv⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  obtain ⟨v', hv'⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ'
  have h1 := isUniqueInvolution_of_le_liftFam hv hJM hw
  have h2 := isUniqueInvolution_of_le_liftFam hv' hJM' hw'
  have hJJ : J' = J := hnt J hJ J' ⟨hJ', w, h1, h2⟩
  exact liftFam_eq_of_le hΩ hM' hM hJ (hJJ ▸ hJM') hJM

theorem oddCoreOf_eq_bot_of_two {A : Subgroup X} (hA : IsPGroup 2 ↥A) :
    oddCoreOf A = ⊥ := by
  show (classicalInvolutionOddCore ↥A).map A.subtype = ⊥
  rw [oddCore_eq_bot_of_isPGroup hA, Subgroup.map_bot]

end Aut

section Cit3


variable {X : Type} [Group X] [Finite X] {K : Subgroup X} {S : Sylow 2 K} {z : X}

theorem SecIdLie3.noRoot {n : ℕ} (hCIT : CITBelowT (.sl2 3 1) n) (hIH : IH8T 3 1 n)
    (hn : Nat.card X < n) (hd : TightDatum K S z) (hc : TightCls X K S z) (hl : SecIdLie3 K z)
    (hnt : ∀ L ∈ CoreAssembly.conjClass (tightCore K),
      ∀ L' ∈ twinSet (CoreAssembly.conjClass (tightCore K)) L, L' = L)
    (hds : ¬ T3.DStarConnected (CoreAssembly.conjClass (tightCore K))) :
    ∀ A ∈ CoreAssembly.conjClass (tightCore K),
      ∀ B ∈ omegaNbr (CoreAssembly.conjClass (tightCore K)) A, ∀ x x' : X,
        IsUniqueInvolution A x → IsUniqueInvolution B x' → x * x' ∈ Subgroup.center X →
          (∀ σ : MulAut X, (∀ k ∈ A, σ k * k⁻¹ ∈ oddCoreOf A) →
            (∀ k ∈ B, σ k * k⁻¹ ∈ oddCoreOf B) → σ * σ ≠ MulAut.conj x) ∧
          (∀ e : X, (∀ k ∈ A, ⁅e, k⁆ ∈ oddCoreOf A) → (∀ k ∈ B, ⁅e, k⁆ ∈ oddCoreOf B) →
            e * e ≠ x * x') := by
  set Δ := CoreAssembly.conjClass (tightCore K) with hΔ
  have hΩ : HypOmegaGen Δ := hd.hypOmegaGen
  have h2 : ∀ J ∈ Δ, IsPGroup 2 ↥J := hl.isPGroup_members hc.2.2
  have hlift : HasLifts Δ := hl.hasLifts hd
  have hex : ExactSylow Δ := hl.exactSylow hc.2.2
  obtain ⟨hΛ, hgΛ, hAΛ⟩ := hl.liftFam_hyp hd hc
  have hOC : ∀ {J L : Subgroup X} {u : X}, IsLiftOf J L u →
      Balance.oddCoreIn (Subgroup.centralizer ({u} : Set X)) = ⊥ := fun h =>
    hl.oddCoreIn_centralizer_eq_bot hc.2.2
      (orderOf_eq_prime (by rw [pow_two]; exact h.inv.sq) h.inv.ne_one)
  have hO : classicalInvolutionOddCore X = ⊥ := hc.2.2
  have hntΛ := SecIdLie3.liftFam_noTwins hd hnt
  have hdsΛ : ¬ T3.DStarConnected (liftFam Δ) := fun h' =>
    hds (dstarConnected_of_liftFam hΩ h2 hlift hex h')
  intro A hAΔ B hB x x' hx hx' hxx'
  obtain ⟨LA, uA, hLA⟩ := hlift A hAΔ
  obtain ⟨LB, uB, hLB⟩ := hlift B hB.1
  have hMA := satU_mem_liftFam hAΔ hLA
  have hMB := satU_mem_liftFam hB.1 hLB
  have hxΛ := isUniqueInvolution_liftFam_of_le hMA hx hLA.le_sat
  have hx'Λ := isUniqueInvolution_liftFam_of_le hMB hx' hLB.le_sat
  have hBΛ := mem_omegaNbr_liftFam_of_mem hΩ h2 hAΔ hMA hLA.le_sat hMB hLB.le_sat hB
  have hR := Q3T8.Asc77.e4SecNoRoot3 n hCIT hIH X hn (liftFam Δ) hΛ hO hgΛ hAΛ hntΛ hdsΛ _ hMA
    _ hBΛ x x' hxΛ hx'Λ hxx'
  rw [satU_eq_of_oddCoreIn_eq_bot (hOC hLA)] at hR
  rw [satU_eq_of_oddCoreIn_eq_bot (hOC hLB)] at hR
  have key : ∀ {J L : Subgroup X} {u : X}, J ∈ Δ → IsLiftOf J L u → ∀ σ : MulAut X,
      (∀ k ∈ J, σ k * k⁻¹ ∈ oddCoreOf J) → ∀ k ∈ L, σ k * k⁻¹ ∈ oddCoreOf L := by
    intro J L u hJ h σ hσ k hk
    have hfix : ∀ j ∈ J, σ j = j := by
      intro j hj
      have := hσ j hj
      rw [oddCoreOf_eq_bot_of_two (h2 J hJ), Subgroup.mem_bot,
        mul_inv_eq_one] at this
      exact this
    rw [lift_fix_of_fix hΩ hJ (h2 J hJ) h (hOC h) σ hfix k hk, mul_inv_cancel]
    exact (oddCoreOf L).one_mem
  refine ⟨fun σ hσA hσB => hR.1 σ (key hAΔ hLA σ hσA) (key hB.1 hLB σ hσB), fun e heA heB => ?_⟩
  have hc' : ∀ {J L : Subgroup X} {u : X}, J ∈ Δ → IsLiftOf J L u →
      (∀ k ∈ J, ⁅e, k⁆ ∈ oddCoreOf J) → ∀ k ∈ L, ⁅e, k⁆ ∈ oddCoreOf L := by
    intro J L u hJ h he k hk
    have h1 := key hJ h (MulAut.conj e) (fun j hj => by
      simpa [commutatorElement_def, mul_assoc] using he j hj) k hk
    simpa [commutatorElement_def, mul_assoc] using h1
  exact hR.2 e (hc' hAΔ hLA heA) (hc' hB.1 hLB heB)


theorem SecIdLie3.e4Gen {n : ℕ} (hCIT : CITBelowT (.sl2 3 1) n) (hIH : IH8T 3 1 n)
    (hn : Nat.card X < n) (hd : TightDatum K S z) (hc : TightCls X K S z) (hl : SecIdLie3 K z)
    (hnt : ∀ L ∈ CoreAssembly.conjClass (tightCore K),
      ∀ L' ∈ twinSet (CoreAssembly.conjClass (tightCore K)) L, L' = L)
    (hds : ¬ T3.DStarConnected (CoreAssembly.conjClass (tightCore K))) :
    ∀ A ∈ CoreAssembly.conjClass (tightCore K),
      ∀ B ∈ omegaNbr (CoreAssembly.conjClass (tightCore K)) A, ∀ x x' : X,
        IsUniqueInvolution A x → IsUniqueInvolution B x' → x * x' ∈ Subgroup.center X →
          ∀ σ : MulAut X, σ * σ = 1 → σ x' = x' → (∀ k ∈ A, σ k * k⁻¹ ∈ oddCoreOf A) →
            (∀ k ∈ B, σ k ∈ B) → (¬ ∀ k ∈ B, σ k * k⁻¹ ∈ oddCoreOf B) →
              Subgroup.closure ({g | σ g = g} ∪ {g | x' * g = g * x'} ∪
                {g | σ (x' * g * x'⁻¹) = g}) = ⊤ := by
  set Δ := CoreAssembly.conjClass (tightCore K) with hΔ
  have hΩ : HypOmegaGen Δ := hd.hypOmegaGen
  have h2 : ∀ J ∈ Δ, IsPGroup 2 ↥J := hl.isPGroup_members hc.2.2
  have hlift : HasLifts Δ := hl.hasLifts hd
  have hex : ExactSylow Δ := hl.exactSylow hc.2.2
  obtain ⟨hΛ, hgΛ, hAΛ⟩ := hl.liftFam_hyp hd hc
  have hOC : ∀ {J L : Subgroup X} {u : X}, IsLiftOf J L u →
      Balance.oddCoreIn (Subgroup.centralizer ({u} : Set X)) = ⊥ := fun h =>
    hl.oddCoreIn_centralizer_eq_bot hc.2.2
      (orderOf_eq_prime (by rw [pow_two]; exact h.inv.sq) h.inv.ne_one)
  have hO : classicalInvolutionOddCore X = ⊥ := hc.2.2
  have hntΛ := SecIdLie3.liftFam_noTwins hd hnt
  have hdsΛ : ¬ T3.DStarConnected (liftFam Δ) := fun h' =>
    hds (dstarConnected_of_liftFam hΩ h2 hlift hex h')
  intro A hAΔ B hB x x' hx hx' hxx' σ hσ2 hσx' hσA hσB hσnB
  obtain ⟨LA, uA, hLA⟩ := hlift A hAΔ
  obtain ⟨LB, uB, hLB⟩ := hlift B hB.1
  have hMA := satU_mem_liftFam hAΔ hLA
  have hMB := satU_mem_liftFam hB.1 hLB
  have hxΛ := isUniqueInvolution_liftFam_of_le hMA hx hLA.le_sat
  have hx'Λ := isUniqueInvolution_liftFam_of_le hMB hx' hLB.le_sat
  have hBΛ := mem_omegaNbr_liftFam_of_mem hΩ h2 hAΔ hMA hLA.le_sat hMB hLB.le_sat hB
  have hR := Q3T8.Asc77.e4SecGen3 n hCIT hIH X hn (liftFam Δ) hΛ hO hgΛ hAΛ hntΛ hdsΛ _ hMA
    _ hBΛ x x' hxΛ hx'Λ hxx' σ hσ2 hσx'
  rw [satU_eq_of_oddCoreIn_eq_bot (hOC hLA)] at hR
  rw [satU_eq_of_oddCoreIn_eq_bot (hOC hLB)] at hR
  have hOLB : oddCoreOf LB = ⊥ := by
    show (classicalInvolutionOddCore ↥LB).map LB.subtype = ⊥
    rw [lift_oddCore_eq_bot hLB (hOC hLB), Subgroup.map_bot]
  refine hR ?_ ?_ ?_
  ·
    have hfix : ∀ j ∈ A, σ j = j := by
      intro j hj
      have := hσA j hj
      rw [oddCoreOf_eq_bot_of_two (h2 A hAΔ), Subgroup.mem_bot,
        mul_inv_eq_one] at this
      exact this
    intro k hk
    rw [lift_fix_of_fix hΩ hAΔ (h2 A hAΔ) hLA (hOC hLA) σ hfix k hk, mul_inv_cancel]
    exact (oddCoreOf LA).one_mem
  ·
    have huB : uB = x' := (hx'.unique uB hLB.inv.mem hLB.inv.sq).resolve_left hLB.inv.ne_one
    have hσB' : B.map σ.toMonoidHom = B := by
      have hle : B.map σ.toMonoidHom ≤ B := by
        rintro _ ⟨k, hk, rfl⟩
        exact hσB k hk
      exact Subgroup.eq_of_le_of_card_ge hle
        (le_of_eq (Subgroup.card_map_of_injective σ.injective).symm)
    have hLB' := lift_map_eq_of_map_eq hΩ hB.1 hLB (hOC hLB) σ hσB' (huB ▸ hσx')
    intro k hk
    rw [← hLB']
    exact ⟨k, hk, rfl⟩
  ·
    intro hall
    apply hσnB
    intro k hk
    have h1 := hall k (hLB.le hk)
    rw [hOLB, Subgroup.mem_bot, mul_inv_eq_one] at h1
    rw [h1, mul_inv_cancel]
    exact (oddCoreOf B).one_mem

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
