module

public import CFSG.Holt.H78.Sec4FinalC4

public section


namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open CFSG.GH74.Uniqueness.Bender (rootCenter)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Pointwise

namespace FinalC

section DIter

variable {G : Type*} [Group G]

@[expose] def dIter (k : ℕ) (H : Subgroup G) : Subgroup G := (fun K : Subgroup G => ⁅K, K⁆)^[k] H

@[simp] theorem dIter_zero (H : Subgroup G) : dIter 0 H = H := rfl

theorem dIter_succ (k : ℕ) (H : Subgroup G) : dIter (k + 1) H = ⁅dIter k H, dIter k H⁆ :=
  Function.iterate_succ_apply' _ k H

theorem dIter_add (a b : ℕ) (H : Subgroup G) : dIter (a + b) H = dIter b (dIter a H) := by
  rw [dIter, dIter, dIter, add_comm, Function.iterate_add_apply]

theorem dIter_mono (k : ℕ) {H K : Subgroup G} (h : H ≤ K) : dIter k H ≤ dIter k K := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [dIter_succ, dIter_succ]
    exact Subgroup.commutator_mono ih ih

theorem dIter_le (k : ℕ) (H : Subgroup G) : dIter k H ≤ H := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [dIter_succ]
    exact (Subgroup.commutator_le_self _).trans ih

theorem map_dIter {G' : Type*} [Group G'] (f : G →* G') (k : ℕ) (H : Subgroup G) :
    (dIter k H).map f = dIter k (H.map f) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [dIter_succ, dIter_succ, Subgroup.map_commutator, ih]

theorem dIter_eq_of_commutator_eq {N : Subgroup G} (hN : ⁅N, N⁆ = N) (k : ℕ) : dIter k N = N := by
  induction k with
  | zero => rfl
  | succ k ih => rw [dIter_succ, ih, hN]

theorem dIter_top (k : ℕ) : dIter k (⊤ : Subgroup G) = derivedSeries G k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [dIter_succ, ih, derivedSeries_succ]

theorem dIter_le_map_ker {H : Subgroup G} {S : Type*} [Group S] (f : H →* S) {k : ℕ}
    (hk : derivedSeries S k = ⊥) : dIter k H ≤ f.ker.map H.subtype := by
  have h1 : dIter k H = (derivedSeries H k).map H.subtype := by
    rw [← dIter_top, map_dIter, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h1]
  refine Subgroup.map_mono fun x hx => ?_
  have h2 := map_derivedSeries_le_derivedSeries f k ⟨x, hx, rfl⟩
  rw [hk] at h2
  exact Subgroup.mem_bot.mp h2

end DIter

section Solvable

variable {Δ : Type} [Finite Δ] {L : Subgroup (Equiv.Perm Δ)}

theorem isSolvable_normalizer_inf_stabilizer (hL : IsNaturalSE L) (b : Δ) :
    Group.IsSolvable ↥(Subgroup.normalizer (L : Set (Equiv.Perm Δ)) ⊓
      stabilizer (Equiv.Perm Δ) b) := by
  obtain ⟨n, i, e, hA⟩ := isNaturalSE_iff.mp hL
  have : Finite L := inferInstance
  have hLb : Group.IsSolvable ↥(stabilizer ↥L b) := by
    obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer b
    obtain ⟨t, hc⟩ := hA.benderType.exists_benderCore Q
    rw [hA.stabilizer_eq_borel hQ]
    exact hc.isSolvable_borel
  have hout : Group.IsSolvable (Outer ↥L) := BenderType.isSolvable_outer hA.benderType
  set X := Subgroup.normalizer (L : Set (Equiv.Perm Δ)) ⊓ stabilizer (Equiv.Perm Δ) b
  let φ : (L.subgroupOf X) →* stabilizer (↥L) b :=
    { toFun := fun x => ⟨⟨((x : X) : Equiv.Perm Δ), x.2⟩,
        mem_stabilizer_iff.mpr (mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (x : X).2).2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := fun x y hxy => by
    have := congrArg (fun z : stabilizer (↥L) b => ((z : ↥L) : Equiv.Perm Δ)) hxy
    exact Subtype.ext (Subtype.ext this)
  have : Group.IsSolvable (L.subgroupOf X) := Group.isSolvable_of_isSolvable_injective hφ
  refine Group.isSolvable_of_ker_le_range (L.subgroupOf X).subtype
    ((normalizerOuterHom L).comp (Subgroup.inclusion inf_le_left)) fun x hx => ?_
  have h1 := (hL.normalizerOuterHom_eq_one_iff _).mp hx
  exact ⟨⟨x, h1⟩, rfl⟩

end Solvable

end FinalC

namespace FinConfig

section MM

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

noncomputable def MM (hS : Sec4Setting G Ω) : Subgroup G where
  carrier := {y | ∃ hy : y ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G),
    C.piM hS ⟨y, hy⟩ ∈ C.Dv.M C.i}
  mul_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨mul_mem ha hb, by
    rw [show (⟨a * b, mul_mem ha hb⟩ : Subgroup.centralizer
      ((Subgroup.zpowers v : Subgroup G) : Set G)) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, map_mul]
    exact mul_mem ha' hb'⟩
  one_mem' := ⟨one_mem _, by
    rw [show (⟨1, one_mem _⟩ : Subgroup.centralizer
      ((Subgroup.zpowers v : Subgroup G) : Set G)) = 1 from rfl, map_one]
    exact one_mem _⟩
  inv_mem' := fun {a} ⟨ha, ha'⟩ => ⟨inv_mem ha, by
    rw [show (⟨a⁻¹, inv_mem ha⟩ : Subgroup.centralizer
      ((Subgroup.zpowers v : Subgroup G) : Set G)) = (⟨a, ha⟩)⁻¹ from rfl, map_inv]
    exact inv_mem ha'⟩

theorem mem_MM (hS : Sec4Setting G Ω) {y : G} : y ∈ C.MM hS ↔
    ∃ hy : y ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G),
      C.piM hS ⟨y, hy⟩ ∈ C.Dv.M C.i := Iff.rfl

noncomputable def MMc (hS : Sec4Setting G Ω) (D : C.Splitting hS) (y : C.MM hS) : G :=
  (D.exists_piM _ ((C.mem_MM hS).mp y.2).2).choose

theorem MMc_spec (hS : Sec4Setting G Ω) (D : C.Splitting hS) (y : C.MM hS) :
    ∃ hc : C.MMc hS D y ∈ D.Mc, C.piM hS ⟨_, C.centralizer_Y_le hS (D.Mc_le hc)⟩ =
      C.piM hS ⟨y, ((C.mem_MM hS).mp y.2).1⟩ :=
  (D.exists_piM _ ((C.mem_MM hS).mp y.2).2).choose_spec

theorem inv_mul_mem_fixingSubgroup (hS : Sec4Setting G Ω) (D : C.Splitting hS) {c y : G}
    (hc : c ∈ D.Mc)
    (hy : y ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (h : C.piM hS ⟨c, C.centralizer_Y_le hS (D.Mc_le hc)⟩ = C.piM hS ⟨y, hy⟩) :
    c⁻¹ * y ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) := by
  have h1 : C.piM hS ((⟨c, C.centralizer_Y_le hS (D.Mc_le hc)⟩)⁻¹ * ⟨y, hy⟩) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  exact (mem_fixingSubgroup_iff G).mpr ((C.piM_eq_one_iff hS _).mp h1)

theorem psi_inv_mul_eq (hS : Sec4Setting G Ω) (D : C.Splitting hS) {c c' y : G}
    (hc : c ∈ D.Mc) (hc' : c' ∈ D.Mc)
    (hy : y ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (h : C.piM hS ⟨c, C.centralizer_Y_le hS (D.Mc_le hc)⟩ = C.piM hS ⟨y, hy⟩)
    (h' : C.piM hS ⟨c', C.centralizer_Y_le hS (D.Mc_le hc')⟩ = C.piM hS ⟨y, hy⟩) :
    C.psi ⟨c⁻¹ * y, C.fixingSubgroup_le_pair (C.inv_mul_mem_fixingSubgroup hS D hc hy h)⟩ =
      C.psi ⟨c'⁻¹ * y, C.fixingSubgroup_le_pair (C.inv_mul_mem_fixingSubgroup hS D hc' hy h')⟩ := by
  have hP := C.inv_mul_mem_fixingSubgroup hS D hc hy h
  have hP' := C.inv_mul_mem_fixingSubgroup hS D hc' hy h'
  have hcc : c⁻¹ * c' ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) := by
    have := mul_mem hP (inv_mem hP')
    rwa [show c⁻¹ * y * (c'⁻¹ * y)⁻¹ = c⁻¹ * c' by group] at this
  have hQ := D.mem_oddCore _ (mul_mem (inv_mem hc) hc') hcc
  have h1 := C.psi_eq_one_of_mem_oddCoreOf hS hQ
  rw [show (⟨c⁻¹ * y, C.fixingSubgroup_le_pair hP⟩ : stabilizer G ({α, β} : Set Ω)) =
    ⟨c⁻¹ * c', C.fixingSubgroup_le_pair hcc⟩ * ⟨c'⁻¹ * y, C.fixingSubgroup_le_pair hP'⟩ from
      Subtype.ext (by show c⁻¹ * y = c⁻¹ * c' * (c'⁻¹ * y); group), map_mul, h1, one_mul]

noncomputable def tau (hS : Sec4Setting G Ω) (D : C.Splitting hS) :
    C.MM hS →* Equiv.Perm C.Psi where
  toFun y := C.psi ⟨(C.MMc hS D y)⁻¹ * y, C.fixingSubgroup_le_pair
    (C.inv_mul_mem_fixingSubgroup hS D (C.MMc_spec hS D y).1 _ (C.MMc_spec hS D y).2)⟩
  map_one' := by
    obtain ⟨hc, hce⟩ := C.MMc_spec hS D 1
    have h1 := C.psi_inv_mul_eq hS D hc (one_mem D.Mc) _ hce rfl
    refine h1.trans ?_
    rw [show (⟨(1 : G)⁻¹ * ((1 : C.MM hS) : G), _⟩ : stabilizer G ({α, β} : Set Ω)) = 1 from
      Subtype.ext (by simp), map_one]
  map_mul' y₁ y₂ := by
    obtain ⟨hc₁, hce₁⟩ := C.MMc_spec hS D y₁
    obtain ⟨hc₂, hce₂⟩ := C.MMc_spec hS D y₂
    set c₁ := C.MMc hS D y₁
    set c₂ := C.MMc hS D y₂
    have hP₁ := C.inv_mul_mem_fixingSubgroup hS D hc₁ _ hce₁
    have hP₂ := C.inv_mul_mem_fixingSubgroup hS D hc₂ _ hce₂
    have hc₁₂ := mul_mem hc₁ hc₂
    have hce₁₂ : C.piM hS ⟨c₁ * c₂, C.centralizer_Y_le hS (D.Mc_le hc₁₂)⟩ =
        C.piM hS ⟨((y₁ * y₂ : C.MM hS) : G), ((C.mem_MM hS).mp (y₁ * y₂).2).1⟩ := by
      rw [show (⟨c₁ * c₂, C.centralizer_Y_le hS (D.Mc_le hc₁₂)⟩ : Subgroup.centralizer
        ((Subgroup.zpowers v : Subgroup G) : Set G)) = ⟨c₁, C.centralizer_Y_le hS (D.Mc_le hc₁)⟩ *
          ⟨c₂, C.centralizer_Y_le hS (D.Mc_le hc₂)⟩ from rfl, map_mul, hce₁, hce₂, ← map_mul]
      rfl
    obtain ⟨hc₃, hce₃⟩ := C.MMc_spec hS D (y₁ * y₂)
    refine (C.psi_inv_mul_eq hS D hc₃ hc₁₂ _ hce₃ hce₁₂).trans ?_
    have he := C.commutator_mem_oddCoreOf hS D (inv_mem hc₂) hP₁
    rw [inv_inv] at he
    have heP : c₂⁻¹ * (c₁⁻¹ * y₁) * c₂ * (c₁⁻¹ * y₁)⁻¹ ∈
        fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) := Subgroup.map_subtype_le _ he
    have h1 := C.psi_eq_one_of_mem_oddCoreOf hS he
    rw [show (⟨(c₁ * c₂)⁻¹ * ((y₁ * y₂ : C.MM hS) : G), _⟩ : stabilizer G ({α, β} : Set Ω)) =
      ⟨_, C.fixingSubgroup_le_pair heP⟩ * ⟨c₁⁻¹ * y₁, C.fixingSubgroup_le_pair hP₁⟩ *
        ⟨c₂⁻¹ * y₂, C.fixingSubgroup_le_pair hP₂⟩ from Subtype.ext (by
          show (c₁ * c₂)⁻¹ * ((y₁ : G) * y₂) =
            c₂⁻¹ * (c₁⁻¹ * y₁) * c₂ * (c₁⁻¹ * y₁)⁻¹ * (c₁⁻¹ * y₁) * (c₂⁻¹ * y₂)
          group), map_mul, map_mul, h1, one_mul]

theorem exists_mem_Mc_of_tau_eq_one (hS : Sec4Setting G Ω) (D : C.Splitting hS) {y : C.MM hS}
    (hy : C.tau hS D y = 1) : ∃ c ∈ D.Mc, c⁻¹ * (y : G) ∈
      oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) :=
  ⟨_, (C.MMc_spec hS D y).1, C.mem_oddCoreOf_of_psi_eq_one hS
    (C.inv_mul_mem_fixingSubgroup hS D (C.MMc_spec hS D y).1 _ (C.MMc_spec hS D y).2) hy⟩

theorem tau_mem (hS : Sec4Setting G Ω) (D : C.Splitting hS) (y : C.MM hS) :
    C.tau hS D y ∈ Subgroup.normalizer (C.N : Set (Equiv.Perm C.Psi)) ⊓
      stabilizer (Equiv.Perm C.Psi) C.bγ := by
  refine Subgroup.mem_inf.mpr ⟨C.psi_mem_normalizer _, mem_stabilizer_iff.mpr ?_⟩
  exact C.psi_apply_bγ ((mem_fixingSubgroup_iff G).mp
    (C.inv_mul_mem_fixingSubgroup hS D (C.MMc_spec hS D y).1 _ (C.MMc_spec hS D y).2) _ C.γ_mem)

theorem exists_dIter_le (hS : Sec4Setting G Ω) (D : C.Splitting hS) :
    ∃ k : ℕ, ∀ y ∈ FinalC.dIter k
      (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)),
        ∃ c ∈ D.Mc, c⁻¹ * y ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) := by
  have hM := C.isNaturalSE_Dv C.i
  obtain ⟨n, i, e, hA⟩ := hM.exists_isBenderAction
  obtain ⟨n₁, hn₁⟩ := (BenderType.isSolvable_outer hA.benderType).solvable
  obtain ⟨n₂, hn₂⟩ := (FinalC.isSolvable_normalizer_inf_stabilizer C.isNaturalSE_N C.bγ).solvable
  set Cv := Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)
  let f₁ : Cv →* Outer ↥(C.Dv.M C.i) := (normalizerOuterHom (C.Dv.M C.i)).comp
    ((C.piM hS).codRestrict _ (C.piM_mem_normalizer hS))
  have h1 : FinalC.dIter n₁ Cv ≤ C.MM hS := by
    refine (FinalC.dIter_le_map_ker f₁ hn₁).trans ?_
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c.2, (hM.normalizerOuterHom_eq_one_iff _).mp hc⟩
  let f₂ := (C.tau hS D).codRestrict _ (C.tau_mem hS D)
  have h2 := FinalC.dIter_le_map_ker f₂ hn₂
  refine ⟨n₁ + n₂, fun y hy => ?_⟩
  rw [FinalC.dIter_add] at hy
  obtain ⟨y', hy', rfl⟩ := h2 (FinalC.dIter_mono n₂ h1 hy)
  have h3 : C.tau hS D y' = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hy')
  exact C.exists_mem_Mc_of_tau_eq_one hS D h3

end MM

end FinConfig

namespace FinConfig

section Lemma51R

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

noncomputable def coordEquiv (hS : Sec4Setting G Ω) :
    fixSet Ω (Subgroup.zpowers v) ≃ C.Dv.Ψc C.i :=
  Equiv.ofBijective (fun ω => C.Dv.coord ω C.i)
    ⟨fun ω ω' h => C.coord_Dv_injective (funext fun j => by rcases C.eq_i hS j with rfl; exact h),
      fun c => C.Dv.exists_coord_apply_eq C.i c⟩

noncomputable def piPhi (hS : Sec4Setting G Ω) :
    stabilizer G (fixSet Ω (Subgroup.zpowers v)) →* Equiv.Perm (C.Dv.Ψc C.i) :=
  (C.coordEquiv hS).permCongrHom.toMonoidHom.comp (inducedHom _ _ le_rfl)

theorem piPhi_coord (hS : Sec4Setting G Ω) (g : stabilizer G (fixSet Ω (Subgroup.zpowers v)))
    (ω : fixSet Ω (Subgroup.zpowers v)) :
    C.piPhi hS g (C.Dv.coord ω C.i) = C.Dv.coord (inducedHom _ _ le_rfl g ω) C.i := by
  show (C.coordEquiv hS) (inducedHom _ _ le_rfl g ((C.coordEquiv hS).symm
    ((C.coordEquiv hS) ω))) = _
  rw [Equiv.symm_apply_apply]
  rfl

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem centralizer_le_stabilizer (v : G) :
    Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) ≤
      stabilizer G (fixSet Ω (Subgroup.zpowers v)) := fun _ hc =>
  mem_stabilizer_iff.mpr (smul_fixSet_zpowers_of_mem_centralizer hc)

theorem piPhi_eq_piM (hS : Sec4Setting G Ω)
    (g : Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) :
    C.piPhi hS ⟨g, centralizer_le_stabilizer (Ω := Ω) v g.2⟩ = C.piM hS g := by
  ext c
  obtain ⟨ω, rfl⟩ := C.Dv.exists_coord_apply_eq C.i c
  rw [C.piPhi_coord, C.piM_coord]
  rfl

theorem piPhi_eq_one_iff (hS : Sec4Setting G Ω)
    (g : stabilizer G (fixSet Ω (Subgroup.zpowers v))) :
    C.piPhi hS g = 1 ↔ ∀ ω ∈ fixSet Ω (Subgroup.zpowers v), (g : G) • ω = ω := by
  constructor
  · intro h ω hω
    have h1 := C.piPhi_coord hS g ⟨ω, hω⟩
    rw [h, Equiv.Perm.one_apply] at h1
    have h2 := (C.coordEquiv hS).injective h1.symm
    exact congrArg Subtype.val h2
  · intro h
    ext c
    obtain ⟨ω, rfl⟩ := C.Dv.exists_coord_apply_eq C.i c
    rw [C.piPhi_coord, Equiv.Perm.one_apply]
    exact congrArg (fun p => C.Dv.coord p C.i) (Subtype.ext (h ω ω.2))

theorem piM_mem_M_of_mem_longInv (hS : Sec4Setting G Ω) {c : G} (hcJ : c ∈ longInv G Ω)
    (hc : c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) :
    C.piM hS ⟨c, hc⟩ ∈ C.Dv.M C.i := by
  have h3 := three_le_card_fixSet_of_isTypeL hS.star C.isTypeL
  have hπ : centralizerImageElt (Ω := Ω) hc ∈
      longInv (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
    (hS.mem_longInv_centralizerImage_iff C.isPGroup_zpowers h3 _).mpr ⟨c, hcJ, hc, fun _ => rfl⟩
  rw [C.piM_eq_rho hS ⟨c, hc⟩ (mem_jHull_of_mem_longInv hπ)]
  exact C.Dv.rho_mem_M_of_isNaturalSE (C.isNaturalSE_Dv C.i) _

theorem piPhi_mem_normalizer (hS : Sec4Setting G Ω)
    (g : stabilizer G (fixSet Ω (Subgroup.zpowers v))) :
    C.piPhi hS g ∈ Subgroup.normalizer (C.Dv.M C.i : Set (Equiv.Perm (C.Dv.Ψc C.i))) := by
  set Cv := Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)
  set M := C.Dv.M C.i
  have h3 := three_le_card_fixSet_of_isTypeL hS.star C.isTypeL
  have hVΦ : Subgroup.zpowers v ≤ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) := fun _ hg =>
    (mem_fixingSubgroup_iff G).mpr fun ω hω => hω _ hg
  set I : Set (Equiv.Perm (C.Dv.Ψc C.i)) :=
    {m | ∃ c ∈ longInv G Ω, ∃ hc : c ∈ Cv, C.piM hS ⟨c, hc⟩ = m}
  have hIM : Subgroup.closure I ≤ M := (Subgroup.closure_le _).mpr fun m ⟨c, hcJ, hc, hm⟩ =>
    hm ▸ C.piM_mem_M_of_mem_longInv hS hcJ hc
  have hconj : ∀ g' : stabilizer G (fixSet Ω (Subgroup.zpowers v)), ∀ m ∈ I,
      C.piPhi hS g' * m * (C.piPhi hS g')⁻¹ ∈ I := by
    rintro g' _ ⟨c, hcJ, hc, rfl⟩
    have hcs := centralizer_le_stabilizer (Ω := Ω) v hc
    set y := (g' : G) * c * (g' : G)⁻¹
    have hyJ : y ∈ longInv G Ω := conj_mem_longInv hcJ _
    have hys : y ∈ stabilizer G (fixSet Ω (Subgroup.zpowers v)) :=
      mul_mem (mul_mem g'.2 hcs) (inv_mem g'.2)
    obtain ⟨c', hc'J, hc'C, hc'e⟩ := hS.frattini h3 C.isPGroup_zpowers hVΦ hyJ hys
    refine ⟨c', hc'J, hc'C, ?_⟩
    rw [← C.piPhi_eq_piM hS ⟨c, hc⟩, ← C.piPhi_eq_piM hS ⟨c', hc'C⟩, ← map_inv, ← map_mul,
      ← map_mul]
    have h1 : C.piPhi hS ((⟨y, hys⟩ : stabilizer G (fixSet Ω (Subgroup.zpowers v)))⁻¹ *
        ⟨c', centralizer_le_stabilizer v hc'C⟩)
        = 1 := (C.piPhi_eq_one_iff hS _).mpr fun ω hω => by
      show (y⁻¹ * c') • ω = ω
      rw [mul_smul, hc'e ω hω, inv_smul_smul]
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    rw [← h1]
    rfl
  have hcl : ∀ g' : stabilizer G (fixSet Ω (Subgroup.zpowers v)), ∀ m ∈ Subgroup.closure I,
      C.piPhi hS g' * m * (C.piPhi hS g')⁻¹ ∈ Subgroup.closure I := by
    intro g' m hm
    induction hm using Subgroup.closure_induction with
    | mem m hm => exact Subgroup.subset_closure (hconj g' m hm)
    | one => simp
    | mul x y _ _ hx hy =>
      rw [show C.piPhi hS g' * (x * y) * (C.piPhi hS g')⁻¹ = (C.piPhi hS g' * x *
        (C.piPhi hS g')⁻¹) * (C.piPhi hS g' * y * (C.piPhi hS g')⁻¹) by group]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [show C.piPhi hS g' * x⁻¹ * (C.piPhi hS g')⁻¹ =
        (C.piPhi hS g' * x * (C.piPhi hS g')⁻¹)⁻¹ by group]
      exact inv_mem hx
  have hMI : M ≤ Subgroup.closure I := by
    have := C.Dv.isSimpleGroup_M C.i
    have hK : ((Subgroup.closure I).subgroupOf M).Normal := ⟨fun k hk m => by
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      obtain ⟨c₀, hc₀⟩ := C.exists_piM_eq hS m.2
      have h1 := hcl ⟨c₀, centralizer_le_stabilizer v c₀.2⟩ _ hk
      rw [C.piPhi_eq_piM hS c₀, hc₀] at h1
      simpa using h1⟩
    obtain ⟨t, ht, u, hu, htu, hc, htuv, -⟩ := C.isTypeL
    have htC : t ∈ Cv := mem_centralizer_zpowers (by
      rw [← htuv]
      show t * u * t = t * (t * u)
      rw [mul_assoc, hc.eq])
    have htI : C.piM hS ⟨t, htC⟩ ∈ Subgroup.closure I :=
      Subgroup.subset_closure ⟨t, ht.1, htC, rfl⟩
    have ht1 : C.piM hS ⟨t, htC⟩ ≠ 1 := fun h => by
      have h1 := (C.piM_eq_one_iff hS _).mp h β C.mem_fixSet
      exact C.ne (ht.1.2.unique ht.2 h1)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Subgroup.closure I).subgroupOf M) with h | h
    · exfalso
      have h2 : (⟨_, C.piM_mem_M_of_mem_longInv hS ht.1 htC⟩ : M) ∈
          (Subgroup.closure I).subgroupOf M := Subgroup.mem_subgroupOf.mpr htI
      rw [h, Subgroup.mem_bot] at h2
      exact ht1 (congrArg Subtype.val h2)
    · intro m hm
      have h2 : (⟨m, hm⟩ : M) ∈ (Subgroup.closure I).subgroupOf M := h ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp h2
  have hMeq : Subgroup.closure I = M := le_antisymm hIM hMI
  refine Subgroup.mem_normalizer_iff.mpr fun m => ⟨fun hm => ?_, fun hm => ?_⟩
  · rw [← hMeq] at hm ⊢
    exact hcl g m hm
  · rw [← hMeq] at hm ⊢
    have h1 := hcl g⁻¹ _ hm
    rwa [map_inv, inv_inv, show (C.piPhi hS g)⁻¹ * (C.piPhi hS g * m * (C.piPhi hS g)⁻¹) *
      C.piPhi hS g = m by group] at h1

end Lemma51R

end FinConfig

end CFSG.Holt.H78
