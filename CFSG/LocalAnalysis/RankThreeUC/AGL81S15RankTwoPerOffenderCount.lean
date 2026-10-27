module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderNat
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderDescent
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderVLevel
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.RankThree.FFModules
open Matrix MulAction

theorem rho_rho_eq_of_isBestOffenderOn {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {A : Subgroup G} (hbest : IsBestOffenderOn ρ A ⊤)
    {x : G} (hx : x ∈ A) (v : V) : ρ x (ρ x v) = v := by
  have h := (hbest.1 x hx x hx).2 v Submodule.mem_top
  simpa [map_mul, Module.End.mul_apply] using h

private theorem cnt_rho_comm {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {A : Subgroup G} (hbest : IsBestOffenderOn ρ A ⊤)
    {x y : G} (hx : x ∈ A) (hy : y ∈ A) (v : V) : ρ x (ρ y v) = ρ y (ρ x v) :=
  IsElemAbelianOn.comm_top hbest.1 hx hy v

private theorem cnt_T_involutive {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {F : Type*} [Field F] {r : ℕ}
    (N : NatQuot ρ L F r) {A : Subgroup G} (hbest : IsBestOffenderOn ρ A ⊤) {a : G} (haA : a ∈ A)
    (hIa : ∀ v ∈ N.I, ρ a v ∈ N.I) (T : (Fin r → F) ≃+ (Fin r → F))
    (hπa : ∀ v : ↥N.I, N.π ⟨ρ a v, hIa v v.2⟩ = T (N.π v)) :
    ∀ u : Fin r → F, T (T u) = u := by
  intro u
  obtain ⟨v, rfl⟩ := N.surj u
  rw [← hπa v, ← hπa ⟨ρ a v, hIa v v.2⟩]
  congr 1
  apply Subtype.ext
  simpa [map_mul, Module.End.mul_apply] using rho_rho_eq_of_isBestOffenderOn hbest haA (v : V)

theorem ringEquiv_involutive_of_semilinear_involution {F : Type*} [Field F] {r : ℕ} (hr : 0 < r)
    (T : (Fin r → F) ≃+ (Fin r → F)) (hT2 : ∀ u, T (T u) = u)
    (σ : F ≃+* F) (hT : ∀ (c : F) (u : Fin r → F), T (c • u) = σ c • T u) :
    ∀ c : F, σ (σ c) = c := by
  intro c
  let e0 : Fin r → F := Pi.single ⟨0, hr⟩ 1
  have h := hT2 (c • e0)
  rw [hT c e0, hT (σ c) (T e0), hT2 e0] at h
  have h' := congrFun h ⟨0, hr⟩
  simpa [e0, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul] using h'

private noncomputable def cnt_l {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {F : Type*} [Field F] {r : ℕ}
    (N : NatQuot ρ L F r) {K : Subgroup G}
    (hKL : ∀ k ∈ K, ∃ l ∈ L, ∀ v ∈ N.I, ρ k v = ρ l v) (k : ↥K) : ↥L :=
  ⟨Classical.choose (hKL k.1 k.2), (Classical.choose_spec (hKL k.1 k.2)).1⟩

private theorem cnt_l_spec {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {F : Type*} [Field F] {r : ℕ}
    (N : NatQuot ρ L F r) {K : Subgroup G}
    (hKL : ∀ k ∈ K, ∃ l ∈ L, ∀ v ∈ N.I, ρ k v = ρ l v) (k : ↥K) (v : ↥N.I) :
    ρ k.1 v = ρ (cnt_l N hKL k).1 v :=
  (Classical.choose_spec (hKL k.1 k.2)).2 v v.2

private theorem cnt_phi_mulVec {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {F : Type*} [Field F] {r : ℕ}
    (N : NatQuot ρ L F r) {K : Subgroup G}
    (hKL : ∀ k ∈ K, ∃ l ∈ L, ∀ v ∈ N.I, ρ k v = ρ l v)
    (hIK : ∀ k ∈ K, ∀ v ∈ N.I, ρ k v ∈ N.I) (k : ↥K) (v : ↥N.I) :
    (N.Mat (cnt_l N hKL k) : Matrix (Fin r) (Fin r) F) *ᵥ N.π v =
      N.π ⟨ρ k.1 v, hIK k.1 k.2 v v.2⟩ := by
  have h := (N.equiv (cnt_l N hKL k) v).symm
  exact h.trans (congrArg N.π (Subtype.ext (cnt_l_spec N hKL k v))).symm

private noncomputable def cnt_phi {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {F : Type*} [Field F] {r : ℕ}
    (N : NatQuot ρ L F r) {K : Subgroup G}
    (hKL : ∀ k ∈ K, ∃ l ∈ L, ∀ v ∈ N.I, ρ k v = ρ l v)
    (hIK : ∀ k ∈ K, ∀ v ∈ N.I, ρ k v ∈ N.I) : ↥K →* Matrix.GeneralLinearGroup (Fin r) F :=
  MonoidHom.mk' (fun k => N.Mat (cnt_l N hKL k)) (by
    intro k k'
    apply Units.ext
    rw [Matrix.ext_iff_mulVec]
    intro u
    obtain ⟨v, rfl⟩ := N.surj u
    rw [cnt_phi_mulVec N hKL hIK (k * k') v, Matrix.GeneralLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, cnt_phi_mulVec N hKL hIK k' v,
      cnt_phi_mulVec N hKL hIK k ⟨ρ k'.1 v, hIK k'.1 k'.2 v v.2⟩]
    congr 1
    apply Subtype.ext
    simp [map_mul, Module.End.mul_apply])

private theorem cnt_phi_mulVec_apply {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {F : Type*} [Field F]
    {r : ℕ} (N : NatQuot ρ L F r) {K : Subgroup G}
    (hKL : ∀ k ∈ K, ∃ l ∈ L, ∀ v ∈ N.I, ρ k v = ρ l v)
    (hIK : ∀ k ∈ K, ∀ v ∈ N.I, ρ k v ∈ N.I) (k : ↥K) (v : ↥N.I) :
    (cnt_phi N hKL hIK k : Matrix (Fin r) (Fin r) F) *ᵥ N.π v =
      N.π ⟨ρ k.1 v, hIK k.1 k.2 v v.2⟩ :=
  cnt_phi_mulVec N hKL hIK k v

private theorem cnt_phi_mul_comm {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {F : Type*} [Field F]
    {r : ℕ} (N : NatQuot ρ L F r) {K : Subgroup G}
    (hKL : ∀ k ∈ K, ∃ l ∈ L, ∀ v ∈ N.I, ρ k v = ρ l v)
    (hIK : ∀ k ∈ K, ∀ v ∈ N.I, ρ k v ∈ N.I) {A : Subgroup G}
    (hbest : IsBestOffenderOn ρ A ⊤) (hKA : K ≤ A) (k k' : ↥K) :
    cnt_phi N hKL hIK k * cnt_phi N hKL hIK k' =
      cnt_phi N hKL hIK k' * cnt_phi N hKL hIK k := by
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro u
  obtain ⟨v, rfl⟩ := N.surj u
  rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
    Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
  rw [cnt_phi_mulVec_apply N hKL hIK k' v,
    cnt_phi_mulVec_apply N hKL hIK k ⟨ρ k'.1 v, hIK k'.1 k'.2 v v.2⟩,
    cnt_phi_mulVec_apply N hKL hIK k v,
    cnt_phi_mulVec_apply N hKL hIK k' ⟨ρ k.1 v, hIK k.1 k.2 v v.2⟩]
  congr 1
  apply Subtype.ext
  exact cnt_rho_comm hbest (hKA k.2) (hKA k'.2) (v : V)

private theorem cnt_phi_mul_self {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {F : Type*} [Field F]
    {r : ℕ} (N : NatQuot ρ L F r) {K : Subgroup G}
    (hKL : ∀ k ∈ K, ∃ l ∈ L, ∀ v ∈ N.I, ρ k v = ρ l v)
    (hIK : ∀ k ∈ K, ∀ v ∈ N.I, ρ k v ∈ N.I) {A : Subgroup G}
    (hbest : IsBestOffenderOn ρ A ⊤) (hKA : K ≤ A) (k : ↥K) :
    cnt_phi N hKL hIK k * cnt_phi N hKL hIK k = 1 := by
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro u
  obtain ⟨v, rfl⟩ := N.surj u
  rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
    cnt_phi_mulVec_apply N hKL hIK k v,
    cnt_phi_mulVec_apply N hKL hIK k ⟨ρ k.1 v, hIK k.1 k.2 v v.2⟩,
    Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  congr 1
  apply Subtype.ext
  simpa [map_mul, Module.End.mul_apply] using rho_rho_eq_of_isBestOffenderOn hbest (hKA k.2) (v : V)

private theorem cnt_phi_comm_T {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {F : Type*} [Field F]
    {r : ℕ} (N : NatQuot ρ L F r) {K : Subgroup G}
    (hKL : ∀ k ∈ K, ∃ l ∈ L, ∀ v ∈ N.I, ρ k v = ρ l v)
    (hIK : ∀ k ∈ K, ∀ v ∈ N.I, ρ k v ∈ N.I) {A : Subgroup G}
    (hbest : IsBestOffenderOn ρ A ⊤) (hKA : K ≤ A) {a : G} (haA : a ∈ A)
    (hIa : ∀ v ∈ N.I, ρ a v ∈ N.I) (T : (Fin r → F) ≃+ (Fin r → F))
    (hπa : ∀ v : ↥N.I, N.π ⟨ρ a v, hIa v v.2⟩ = T (N.π v)) (k : ↥K) (u : Fin r → F) :
    (cnt_phi N hKL hIK k : Matrix (Fin r) (Fin r) F) *ᵥ T u =
      T ((cnt_phi N hKL hIK k : Matrix (Fin r) (Fin r) F) *ᵥ u) := by
  obtain ⟨v, rfl⟩ := N.surj u
  rw [← hπa v, cnt_phi_mulVec_apply N hKL hIK k ⟨ρ a v, hIa v v.2⟩,
    cnt_phi_mulVec_apply N hKL hIK k v,
    ← hπa ⟨ρ k.1 v, hIK k.1 k.2 v v.2⟩]
  congr 1
  apply Subtype.ext
  exact cnt_rho_comm hbest (hKA k.2) haA (v : V)

private def cnt_Ubar {F : Type*} [Field F] {r : ℕ} (E : Subgroup (Matrix.GeneralLinearGroup (Fin r) F)) :
    Submodule F (Fin r → F) where
  carrier := {u | ∀ g ∈ E, (g : Matrix (Fin r) (Fin r) F) *ᵥ u = u}
  add_mem' {u w} hu hw g hg := by
    rw [Matrix.mulVec_add, hu g hg, hw g hg]
  zero_mem' g _ := by
    rw [Matrix.mulVec_zero]
  smul_mem' c u hu g hg := by
    rw [Matrix.mulVec_smul, hu g hg]

private theorem cnt_mem_Ubar {F : Type*} [Field F] {r : ℕ}
    {E : Subgroup (Matrix.GeneralLinearGroup (Fin r) F)} {u : Fin r → F} :
    u ∈ cnt_Ubar E ↔ ∀ g ∈ E, (g : Matrix (Fin r) (Fin r) F) *ᵥ u = u :=
  Iff.rfl

private theorem cnt_Ubar_T_mem {F : Type*} [Field F] {r : ℕ}
    {E : Subgroup (Matrix.GeneralLinearGroup (Fin r) F)} {T : (Fin r → F) ≃+ (Fin r → F)}
    (hcomm : ∀ e ∈ E, ∀ u : Fin r → F, (e : Matrix (Fin r) (Fin r) F) *ᵥ T u =
      T ((e : Matrix (Fin r) (Fin r) F) *ᵥ u))
    {u : Fin r → F} (hu : u ∈ cnt_Ubar E) : T u ∈ cnt_Ubar E := by
  rw [cnt_mem_Ubar] at hu ⊢
  intro g hg
  rw [hcomm g hg, hu g hg]

private theorem cnt_fixed_lift {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {F : Type*} [Field F] {r : ℕ}
    (N : NatQuot ρ L F r) (hperf : PerfStab N.Mat) {K : Subgroup G}
    (hKL : ∀ k ∈ K, ∃ l ∈ L, ∀ v ∈ N.I, ρ k v = ρ l v)
    (hIK : ∀ k ∈ K, ∀ v ∈ N.I, ρ k v ∈ N.I) {u : Fin r → F}
    (hu : u ∈ cnt_Ubar (cnt_phi N hKL hIK).range) :
    ∃ v : ↥N.I, N.π v = u ∧ ∀ k ∈ K, ρ k v = v := by
  obtain ⟨v, rfl⟩ := N.surj u
  refine ⟨v, rfl, fun k hk => ?_⟩
  have hv : (N.Mat (cnt_l N hKL ⟨k, hk⟩) : Matrix (Fin r) (Fin r) F) *ᵥ N.π v = N.π v :=
    (cnt_mem_Ubar).mp hu (cnt_phi N hKL hIK ⟨k, hk⟩) ⟨⟨k, hk⟩, rfl⟩
  exact (cnt_l_spec N hKL ⟨k, hk⟩ v).trans
    (NatQuot.rho_eq_of_mat_fixes N hperf (cnt_l N hKL ⟨k, hk⟩) v hv)

private theorem cnt_inf_ker_delta {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {A K : Subgroup G} {a : G}
    (hbest : IsBestOffenderOn ρ A ⊤) (hKA : K ≤ A) (haA : a ∈ A)
    (hgen : ∀ g ∈ A, g ∈ K ∨ a * g ∈ K) :
    fixSub ρ K ⊓ LinearMap.ker ((ρ a : V →ₗ[ZMod 2] V) - 1) = fixSub ρ A := by
  ext v
  constructor
  · intro hv
    rw [Submodule.mem_inf, LinearMap.mem_ker] at hv
    rw [mem_fixSub] at hv ⊢
    intro g hg
    rcases hgen g hg with hgK | hagK
    · exact hv.1 g hgK
    · have h1 : ρ a (ρ g v) = v := by
        have := hv.1 (a * g) hagK
        rwa [map_mul, Module.End.mul_apply] at this
      have h2 : ρ a v = v := by
        have h2' : ρ a v - v = 0 := by simpa using hv.2
        exact sub_eq_zero.mp h2'
      have h4 := congrArg (ρ a) (h1.trans h2.symm)
      rw [rho_rho_eq_of_isBestOffenderOn hbest haA, rho_rho_eq_of_isBestOffenderOn hbest haA] at h4
      exact h4
  · intro hv
    rw [Submodule.mem_inf, LinearMap.mem_ker, mem_fixSub] at ⊢
    refine ⟨fun g hg => hv g (hKA hg), ?_⟩
    have h := hv a haA
    simpa using sub_eq_zero.mpr h

private theorem cnt_card_map_delta_le_two {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] {ρ : Representation (ZMod 2) G V} {A K : Subgroup G} {a : G}
    (hbest : IsBestOffenderOn ρ A ⊤) (hKA : K ≤ A) (haA : a ∈ A)
    (hgen : ∀ g ∈ A, g ∈ K ∨ a * g ∈ K) (hidx : Nat.card A = 2 * Nat.card K) :
    Nat.card ↥(Submodule.map ((ρ a : V →ₗ[ZMod 2] V) - 1) (fixSub ρ K)) ≤ 2 := by
  set δ : V →ₗ[ZMod 2] V := (ρ a : V →ₗ[ZMod 2] V) - 1 with hδ
  set W : Submodule (ZMod 2) V := fixSub ρ K with hW
  have hinf : W ⊓ LinearMap.ker δ = fixSub ρ A := by
    rw [hW, hδ]
    exact cnt_inf_ker_delta hbest hKA haA hgen
  have hcard := card_submodule_eq_card_inf_ker_mul_card_map δ W
  rw [hinf] at hcard
  have hle : Nat.card ↥W ≤ 2 * Nat.card ↥(fixSub ρ A) :=
    card_fixSub_le_two_mul_of_index_two ρ hbest hKA hidx
  have hpos : 0 < Nat.card ↥(fixSub ρ A) := Nat.card_pos
  have hmain : Nat.card ↥(fixSub ρ A) * Nat.card ↥(Submodule.map δ W) ≤
      Nat.card ↥(fixSub ρ A) * 2 := by
    calc Nat.card ↥(fixSub ρ A) * Nat.card ↥(Submodule.map δ W)
        = Nat.card ↥W := hcard.symm
      _ ≤ 2 * Nat.card ↥(fixSub ρ A) := hle
      _ = Nat.card ↥(fixSub ρ A) * 2 := by ring
  exact Nat.le_of_mul_le_mul_left hmain hpos

private theorem cnt_card_Ubar_ge {F : Type} [Field F] [Finite F] [CharP F 2] {n r : ℕ}
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (hr : 0 < r)
    (E : Subgroup (Matrix.GeneralLinearGroup (Fin r) F)) (hE : IsElemAbelian 2 E) :
    2 ^ n ≤ Nat.card ↥(cnt_Ubar E) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulAction E (Fin r → F) :=
    { smul := fun g u => (g.1 : Matrix (Fin r) (Fin r) F) *ᵥ u
      one_smul := fun u => by
        show ((1 : E).1 : Matrix (Fin r) (Fin r) F) *ᵥ u = u
        rw [show (1 : E).1 = (1 : Matrix.GeneralLinearGroup (Fin r) F) from rfl,
          Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
      mul_smul := fun g h u => by
        show (((g * h : E).1 : Matrix.GeneralLinearGroup (Fin r) F) : Matrix (Fin r) (Fin r) F) *ᵥ u =
          (g.1 : Matrix (Fin r) (Fin r) F) *ᵥ ((h.1 : Matrix (Fin r) (Fin r) F) *ᵥ u)
        rw [show (g * h : E).1 = (g.1 : Matrix.GeneralLinearGroup (Fin r) F) * h.1 from rfl,
          Matrix.GeneralLinearGroup.coe_mul, Matrix.mulVec_mulVec] }
  have hPG : IsPGroup 2 E := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [pow_one]
    simpa using hE.2 x.1 x.2
  have hcardfun : Nat.card (Fin r → F) = (2 ^ n) ^ r := by
    rw [Nat.card_fun, Nat.card_fin, hF]
  have hdvd : 2 ∣ Nat.card (Fin r → F) := by
    rw [hcardfun]
    exact (dvd_pow_self 2 (by omega)).trans (dvd_pow_self (2 ^ n) (by omega))
  have hfix0 : (0 : Fin r → F) ∈ fixedPoints E (Fin r → F) := by
    rw [mem_fixedPoints]
    intro g
    show (g.1 : Matrix (Fin r) (Fin r) F) *ᵥ (0 : Fin r → F) = 0
    rw [Matrix.mulVec_zero]
  obtain ⟨b, hb, hb0⟩ :=
    hPG.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := Fin r → F) hdvd hfix0
  have hbne : b ≠ 0 := fun h => hb0 h.symm
  have hbU : b ∈ cnt_Ubar E := by
    rw [cnt_mem_Ubar]
    intro g hg
    exact hb ⟨g, hg⟩
  have hne : cnt_Ubar E ≠ ⊥ := (Submodule.ne_bot_iff (cnt_Ubar E)).mpr ⟨b, hbU, hbne⟩
  have hfr : 1 ≤ Module.finrank F ↥(cnt_Ubar E) := Submodule.one_le_finrank_iff.mpr hne
  have hcard : Nat.card ↥(cnt_Ubar E) = Nat.card F ^ Module.finrank F ↥(cnt_Ubar E) :=
    Module.natCard_eq_pow_finrank (K := F) (V := ↥(cnt_Ubar E))
  have hpow : Nat.card F ^ 1 ≤ Nat.card F ^ Module.finrank F ↥(cnt_Ubar E) :=
    Nat.pow_le_pow_right Nat.card_pos hfr
  calc 2 ^ n = Nat.card F := hF.symm
    _ = Nat.card F ^ 1 := (pow_one _).symm
    _ ≤ Nat.card F ^ Module.finrank F ↥(cnt_Ubar E) := hpow
    _ = Nat.card ↥(cnt_Ubar E) := hcard.symm

private theorem cnt_pi_mem_Ubar {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {F : Type*} [Field F] {r : ℕ}
    (N : NatQuot ρ L F r) {K : Subgroup G}
    (hKL : ∀ k ∈ K, ∃ l ∈ L, ∀ v ∈ N.I, ρ k v = ρ l v)
    (hIK : ∀ k ∈ K, ∀ v ∈ N.I, ρ k v ∈ N.I) {v : ↥N.I} (hv : (v : V) ∈ fixSub ρ K) :
    N.π v ∈ cnt_Ubar (cnt_phi N hKL hIK).range := by
  rw [cnt_mem_Ubar]
  intro g hg
  obtain ⟨k, rfl⟩ := hg
  rw [cnt_phi_mulVec_apply N hKL hIK k v]
  congr 1
  apply Subtype.ext
  exact hv k k.2

private theorem cnt_ker_pi_mem_fixSub {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {F : Type*} [Field F]
    {r : ℕ} (N : NatQuot ρ L F r) {K : Subgroup G}
    (hKL : ∀ k ∈ K, ∃ l ∈ L, ∀ v ∈ N.I, ρ k v = ρ l v) {v : ↥N.I} (hv : N.π v = 0) :
    (v : V) ∈ fixSub ρ K := by
  have hL : ∀ l ∈ L, ρ l (v : V) = (v : V) := (N.ker_iff v).mp hv
  rw [mem_fixSub]
  intro k hk
  rw [cnt_l_spec N hKL ⟨k, hk⟩ v]
  exact hL (cnt_l N hKL ⟨k, hk⟩).1 (cnt_l N hKL ⟨k, hk⟩).2

theorem NatQuot.exists_elemAbelian_of_swap {G : Type} [Group G] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
    {F : Type} [Field F] [Finite F] [CharP F 2] {n r : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hr : 0 < r) (N : NatQuot ρ L F r) (hperf : PerfStab N.Mat)
    {A K : Subgroup G} {a : G} (hbest : IsBestOffenderOn ρ A ⊤) (hKA : K ≤ A) (haA : a ∈ A)
    (hgen : ∀ g ∈ A, g ∈ K ∨ a * g ∈ K) (hidx : Nat.card A = 2 * Nat.card K)
    (hIK : ∀ k ∈ K, ∀ v ∈ N.I, ρ k v ∈ N.I) (hIa : ∀ v ∈ N.I, ρ a v ∈ N.I)
    (hKL : ∀ k ∈ K, ∃ l ∈ L, ∀ v ∈ N.I, ρ k v = ρ l v)
    {σ : F ≃+* F} (hσ : ∃ c : F, σ c ≠ c) (T : (Fin r → F) ≃+ (Fin r → F))
    (hT : ∀ (c : F) (u : Fin r → F), T (c • u) = σ c • T u)
    (hπa : ∀ v : ↥N.I, N.π ⟨ρ a v, hIa v v.2⟩ = T (N.π v)) :
    n = 2 ∧ ∃ E : Subgroup (Matrix.GeneralLinearGroup (Fin r) F), IsElemAbelian 2 E ∧
      (∀ e ∈ E, ∀ u : Fin r → F, (e : Matrix (Fin r) (Fin r) F) *ᵥ T u =
        T ((e : Matrix (Fin r) (Fin r) F) *ᵥ u)) ∧ 2 ^ (2 * r - 2) ≤ Nat.card E := by
  classical
  let φ : ↥K →* Matrix.GeneralLinearGroup (Fin r) F := cnt_phi N hKL hIK
  let E : Subgroup (Matrix.GeneralLinearGroup (Fin r) F) := φ.range
  have hEab : IsElemAbelian 2 E := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨k, hk⟩ := x.2
      obtain ⟨k', hk'⟩ := y.2
      apply Subtype.ext
      change x.1 * y.1 = y.1 * x.1
      rw [← hk, ← hk']
      exact cnt_phi_mul_comm N hKL hIK hbest hKA k k'
    · intro x hx
      obtain ⟨k, hk⟩ := hx
      rw [← hk, pow_two]
      exact cnt_phi_mul_self N hKL hIK hbest hKA k
  have hEcomm : ∀ e ∈ E, ∀ u : Fin r → F,
      (e : Matrix (Fin r) (Fin r) F) *ᵥ T u = T ((e : Matrix (Fin r) (Fin r) F) *ᵥ u) := by
    intro e he u
    obtain ⟨k, hk⟩ := he
    rw [← hk]
    exact cnt_phi_comm_T N hKL hIK hbest hKA haA hIa T hπa k u
  have hT2 : ∀ u : Fin r → F, T (T u) = u := cnt_T_involutive N hbest haA hIa T hπa
  have hσ2 : ∀ c : F, σ (σ c) = c := ringEquiv_involutive_of_semilinear_involution hr T hT2 σ hT
  let Ubar : Submodule F (Fin r → F) := cnt_Ubar E
  let c0 : ℕ := Nat.card {y : Fin r → F // y ∈ Ubar ∧ T y = y}
  let φT : ↥Ubar →+ (Fin r → F) :=
    { toFun := fun y => T y.1 - y.1
      map_zero' := by simp
      map_add' := fun y z => by
        show T (y.1 + z.1) - (y.1 + z.1) = (T y.1 - y.1) + (T z.1 - z.1)
        rw [map_add]; abel }
  have hgal : Nat.card ↥Ubar = c0 ^ 2 :=
    card_submodule_eq_sq_card_fixed hσ hσ2 T hT hT2 Ubar
      (fun y hy => cnt_Ubar_T_mem hEcomm hy)
  have hker : Nat.card ↥φT.ker = c0 := by
    apply Nat.card_congr
    refine
      { toFun := fun y => ⟨y.1.1, y.1.2, ?_⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have h := y.2
      rw [AddMonoidHom.mem_ker] at h
      exact sub_eq_zero.mp h
    · rw [AddMonoidHom.mem_ker]
      show T y.1 - y.1 = 0
      rw [y.2.2, sub_self]
    · intro y
      apply Subtype.ext
      rfl
    · intro y
      rfl
  have hiso : Nat.card ↥Ubar = Nat.card ↥φT.ker * Nat.card ↥φT.range :=
    (AddSubgroup.card_ker_mul_card_range φT).symm
  have hc0pos : 0 < c0 := by
    have : Nonempty ↥φT.ker := ⟨0, φT.ker.zero_mem⟩
    rw [← hker]
    exact Nat.card_pos
  have hS_eq_c0 : Nat.card ↥φT.range = c0 := by
    rw [hker] at hiso
    rw [hgal] at hiso
    have h : c0 * c0 = c0 * Nat.card ↥φT.range := by
      rw [← pow_two]; exact hiso
    exact (Nat.mul_left_cancel hc0pos h).symm
  let δ : V →ₗ[ZMod 2] V := (ρ a : V →ₗ[ZMod 2] V) - 1
  let D : Submodule (ZMod 2) V := Submodule.map δ (fixSub ρ K) ⊓ N.I
  have hSsub : ∀ u ∈ φT.range, u ∈ Set.range (fun w : ↥D => N.π ⟨w.1, w.2.2⟩) := by
    intro u hu
    obtain ⟨y, hy⟩ := AddMonoidHom.mem_range.mp hu
    obtain ⟨v, hvπ, hvfix⟩ := cnt_fixed_lift N hperf hKL hIK y.2
    let w : V := ρ a v - v
    have hwI : w ∈ N.I := N.I.sub_mem (hIa v v.2) v.2
    have hwW : w ∈ Submodule.map δ (fixSub ρ K) := by
      refine Submodule.mem_map.mpr ⟨v, ?_, ?_⟩
      · rw [mem_fixSub]; exact hvfix
      · show δ v = w
        rfl
    have hwD : w ∈ D := Submodule.mem_inf.mpr ⟨hwW, hwI⟩
    refine Set.mem_range.mpr ⟨⟨w, hwD⟩, ?_⟩
    show N.π ⟨w, hwD.2⟩ = u
    have hsub : (⟨w, hwD.2⟩ : ↥N.I) = ⟨ρ a v, hIa v v.2⟩ - v := Subtype.ext rfl
    calc N.π ⟨w, hwD.2⟩ = N.π (⟨ρ a v, hIa v v.2⟩ - v) := by rw [hsub]
      _ = N.π ⟨ρ a v, hIa v v.2⟩ - N.π v := map_sub N.π _ _
      _ = T (N.π v) - N.π v := by rw [hπa v]
      _ = T y.1 - y.1 := by rw [hvπ]
      _ = φT y := rfl
      _ = u := hy
  have hS_le : Nat.card ↥φT.range ≤ Nat.card ↥(Submodule.map δ (fixSub ρ K)) := by
    let g : ↥φT.range → ↥(Set.range (fun w : ↥D => N.π ⟨w.1, w.2.2⟩)) :=
      fun u => ⟨u.1, hSsub u.1 u.2⟩
    have h1 : Nat.card ↥φT.range ≤
        Nat.card ↥(Set.range (fun w : ↥D => N.π ⟨w.1, w.2.2⟩)) := by
      apply Nat.card_le_card_of_injective (f := g)
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : ↥(Set.range (fun w : ↥D => N.π ⟨w.1, w.2.2⟩)) =>
        (z : Fin r → F)) hxy
    have h2 : Nat.card ↥(Set.range (fun w : ↥D => N.π ⟨w.1, w.2.2⟩)) ≤ Nat.card ↥D :=
      Finite.card_range_le _
    have h3 : Nat.card ↥D ≤ Nat.card ↥(Submodule.map δ (fixSub ρ K)) :=
      card_le_of_le_submodule inf_le_left
    exact h1.trans (h2.trans h3)
  have hc0_le2 : c0 ≤ 2 := by
    rw [← hS_eq_c0]
    exact hS_le.trans (cnt_card_map_delta_le_two hbest hKA haA hgen hidx)
  have hUbar_le4 : Nat.card ↥Ubar ≤ 4 := by
    rw [hgal]
    calc c0 ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left hc0_le2 2
      _ = 4 := by norm_num
  have hUbar_ge : 2 ^ n ≤ Nat.card ↥Ubar := cnt_card_Ubar_ge hn hF hr E hEab
  have hn2 : n ≤ 2 := by
    have h : 2 ^ n ≤ 2 ^ 2 := hUbar_ge.trans (hUbar_le4.trans (by norm_num))
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
  have hn_eq : n = 2 := le_antisymm hn2 hn
  have hUbar_eq4 : Nat.card ↥Ubar = 4 := by
    refine le_antisymm hUbar_le4 ?_
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn
      _ ≤ Nat.card ↥Ubar := hUbar_ge
  have hc0_eq2 : c0 = 2 := by
    have h1 : c0 ^ 2 = 4 := by rw [← hgal]; exact hUbar_eq4
    nlinarith [h1, hc0_le2, Nat.zero_le c0]
  have hmap_eq2 : Nat.card ↥(Submodule.map δ (fixSub ρ K)) = 2 := by
    have hle := cnt_card_map_delta_le_two hbest hKA haA hgen hidx
    have hge : 2 ≤ Nat.card ↥(Submodule.map δ (fixSub ρ K)) := by
      calc 2 = c0 := hc0_eq2.symm
        _ = Nat.card ↥φT.range := hS_eq_c0.symm
        _ ≤ Nat.card ↥(Submodule.map δ (fixSub ρ K)) := hS_le
    exact le_antisymm hle hge
  have hW_eq : Nat.card ↥(fixSub ρ K) = 2 * Nat.card ↥(fixSub ρ A) := by
    have hcard := card_submodule_eq_card_inf_ker_mul_card_map δ (fixSub ρ K)
    have hinf : fixSub ρ K ⊓ LinearMap.ker δ = fixSub ρ A :=
      cnt_inf_ker_delta hbest hKA haA hgen
    calc Nat.card ↥(fixSub ρ K)
        = Nat.card ↥(fixSub ρ K ⊓ LinearMap.ker δ) *
            Nat.card ↥(Submodule.map δ (fixSub ρ K)) := hcard
      _ = Nat.card ↥(fixSub ρ A) * 2 := by rw [hinf, hmap_eq2]
      _ = 2 * Nat.card ↥(fixSub ρ A) := by ring
  have heq : Nat.card K * Nat.card ↥(fixSub ρ K) =
      Nat.card A * Nat.card ↥(fixSub ρ A) := by
    rw [hW_eq, hidx]; ring
  let B : Subgroup G :=
    { carrier := {k | k ∈ K ∧ ∀ v ∈ N.I, ρ k v = v}
      one_mem' := ⟨K.one_mem, fun v _ => by simp⟩
      mul_mem' := fun {x y} hx hy => ⟨K.mul_mem hx.1 hy.1, fun v hv => by
        rw [map_mul, Module.End.mul_apply, hy.2 v hv, hx.2 v hv]⟩
      inv_mem' := fun {x} hx => ⟨K.inv_mem hx.1, fun v hv => by
        calc ρ x⁻¹ v = ρ x⁻¹ (ρ x v) := by rw [hx.2 v hv]
          _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
              Module.End.one_apply]⟩ }
  have hBK : B ≤ K := fun x hx => hx.1
  have hBI : ∀ b ∈ B, ∀ v ∈ N.I, ρ b v = v := fun b hb => hb.2
  have hApos : 0 < Nat.card A := by
    have hVpos : 0 < Nat.card V := Nat.card_pos
    have h := hbest.2 ⊥ bot_le
    rw [Subgroup.card_bot, fixOn_top, fixSub_bot, card_top_submodule, one_mul] at h
    exact pos_of_mul_pos_left (lt_of_lt_of_le hVpos h) (Nat.zero_le _)
  have hKpos : 0 < Nat.card K := by
    have h : 0 < 2 * Nat.card K := by rw [← hidx]; exact hApos
    omega
  have : Finite ↥A := Nat.finite_of_card_ne_zero hApos.ne'
  have : Finite ↥K := Nat.finite_of_card_ne_zero hKpos.ne'
  have : Finite ↥B := Finite.of_injective (fun b : ↥B => (⟨b.1, hBK b.2⟩ : ↥K))
    (fun x y hxy => by apply Subtype.ext; exact congrArg (fun z : ↥K => (z : G)) hxy)
  have hoff := card_mul_le_of_bestOffender_fixes ρ hbest hKA hBK heq N.I hBI
  have hNI : Nat.card ↥N.I = Nat.card ↥N.π.ker * Nat.card (Fin r → F) := by
    have h := AddSubgroup.card_ker_mul_card_range N.π
    rw [AddMonoidHom.range_eq_top_of_surjective N.π N.surj, AddSubgroup.card_top] at h
    exact h.symm
  let inc : ↥(N.I ⊓ fixSub ρ K) →+ ↥N.I :=
    { toFun := fun x => ⟨x.1, x.2.1⟩
      map_zero' := rfl
      map_add' := fun x y => rfl }
  let ψ : ↥(N.I ⊓ fixSub ρ K) →+ (Fin r → F) := N.π.comp inc
  have hψker : Nat.card ↥ψ.ker = Nat.card ↥N.π.ker := by
    apply Nat.card_congr
    refine
      { toFun := fun x => by
          have h : ψ x = 0 := (AddMonoidHom.mem_ker).mp x.2
          exact ⟨inc x.1, h⟩
        invFun := fun v => by
          have hv : N.π v.1 = 0 := (AddMonoidHom.mem_ker).mp v.2
          refine ⟨⟨v.1.1, ⟨v.1.2, cnt_ker_pi_mem_fixSub N hKL hv⟩⟩, ?_⟩
          rw [AddMonoidHom.mem_ker]
          show N.π (inc ⟨v.1.1, ⟨v.1.2, cnt_ker_pi_mem_fixSub N hKL hv⟩⟩) = 0
          exact hv
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun v => Subtype.ext (Subtype.ext rfl) }
  have hψrange : Nat.card ↥ψ.range = Nat.card ↥Ubar := by
    apply Nat.card_congr
    refine
      { toFun := fun u => by
          let x := Classical.choose ((AddMonoidHom.mem_range (f := ψ)).mp u.2)
          have hx := Classical.choose_spec ((AddMonoidHom.mem_range (f := ψ)).mp u.2)
          refine ⟨u.1, ?_⟩
          rw [← hx]
          exact cnt_pi_mem_Ubar N hKL hIK x.2.2
        invFun := fun u => by
          let v := Classical.choose (cnt_fixed_lift N hperf hKL hIK u.2)
          have hv := Classical.choose_spec (cnt_fixed_lift N hperf hKL hIK u.2)
          refine ⟨u.1, (AddMonoidHom.mem_range (f := ψ)).mpr ?_⟩
          refine ⟨(⟨v.1, ⟨v.2, mem_fixSub.mpr hv.2⟩⟩ : ↥(N.I ⊓ fixSub ρ K)), ?_⟩
          show N.π (inc ⟨v.1, ⟨v.2, mem_fixSub.mpr hv.2⟩⟩) = u.1
          exact hv.1
        left_inv := fun u => by apply Subtype.ext; rfl
        right_inv := fun u => by apply Subtype.ext; rfl }
  have hItil : Nat.card ↥(N.I ⊓ fixSub ρ K) =
      Nat.card ↥N.π.ker * Nat.card ↥Ubar := by
    have h := AddSubgroup.card_ker_mul_card_range ψ
    rw [hψker, hψrange] at h
    exact h.symm
  have hBker : Nat.card ↥φ.ker = Nat.card ↥B := by
    apply Nat.card_congr
    refine
      { toFun := fun k => ⟨k.1.1, k.1.2, ?_⟩
        invFun := fun b => ⟨⟨b.1, b.2.1⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro v hv
      have hφ : cnt_phi N hKL hIK k.1 = 1 := MonoidHom.mem_ker.mp k.2
      have hmat : N.Mat (cnt_l N hKL k.1) = N.Mat 1 := by
        rw [map_one]; exact hφ
      have hl : cnt_l N hKL k.1 = 1 := N.mat_inj hmat
      have hl1 : (cnt_l N hKL k.1).1 = 1 := congrArg Subtype.val hl
      rw [cnt_l_spec N hKL k.1 ⟨v, hv⟩, hl1, map_one, Module.End.one_apply]
    · apply Units.ext
      rw [Matrix.ext_iff_mulVec]
      intro u
      obtain ⟨v, rfl⟩ := N.surj u
      change (N.Mat (cnt_l N hKL ⟨b.1, b.2.1⟩) : Matrix (Fin r) (Fin r) F) *ᵥ N.π v = _
      rw [cnt_phi_mulVec N hKL hIK ⟨b.1, b.2.1⟩ v, Matrix.GeneralLinearGroup.coe_one,
        Matrix.one_mulVec]
      congr 1
      apply Subtype.ext
      exact b.2.2 v v.2
    · intro k; apply Subtype.ext; rfl
    · intro b; apply Subtype.ext; rfl
  have hKcard : Nat.card K = Nat.card B * Nat.card E := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hBker] at h
    rw [← h]
  have hF4 : Nat.card F = 4 := by rw [hF, hn_eq]; norm_num
  have hf4 : Nat.card (Fin r → F) = 4 ^ r := by
    rw [Nat.card_fun, Nat.card_fin, hF4]
  have hmain : Nat.card ↥N.π.ker * Nat.card (Fin r → F) * Nat.card B ≤
      Nat.card B * Nat.card E * (Nat.card ↥N.π.ker * Nat.card ↥Ubar) := by
    have h := hoff
    rwa [hNI, hItil, hKcard] at h
  have hmain2 : Nat.card ↥N.π.ker * Nat.card (Fin r → F) * Nat.card B ≤
      Nat.card B * Nat.card E * (Nat.card ↥N.π.ker * 4) := by
    rw [hUbar_eq4] at hmain
    exact hmain
  have hkpos : 0 < Nat.card ↥N.π.ker := Nat.card_pos
  have hbpos : 0 < Nat.card B := Nat.card_pos
  have hfe : Nat.card (Fin r → F) ≤ 4 * Nat.card E := by
    have h' : Nat.card (Fin r → F) * (Nat.card ↥N.π.ker * Nat.card B) ≤
        (4 * Nat.card E) * (Nat.card ↥N.π.ker * Nat.card B) := by
      calc Nat.card (Fin r → F) * (Nat.card ↥N.π.ker * Nat.card B)
          = Nat.card ↥N.π.ker * Nat.card (Fin r → F) * Nat.card B := by ring
        _ ≤ Nat.card B * Nat.card E * (Nat.card ↥N.π.ker * 4) := hmain2
        _ = (4 * Nat.card E) * (Nat.card ↥N.π.ker * Nat.card B) := by ring
    exact Nat.le_of_mul_le_mul_right h' (Nat.mul_pos hkpos hbpos)
  have h4r : (4 : ℕ) ^ r = 2 ^ (2 * r) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have h2r : 2 ^ (2 * r) ≤ 4 * Nat.card E := by
    rw [← h4r, ← hf4]
    exact hfe
  have hsplit : 2 ^ (2 * r) = 2 ^ 2 * 2 ^ (2 * r - 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hfinal : 2 ^ (2 * r - 2) ≤ Nat.card E := by
    have h : 2 ^ 2 * 2 ^ (2 * r - 2) ≤ 2 ^ 2 * Nat.card E := by
      calc 2 ^ 2 * 2 ^ (2 * r - 2) = 2 ^ (2 * r) := hsplit.symm
        _ ≤ 4 * Nat.card E := h2r
        _ = 2 ^ 2 * Nat.card E := by norm_num
    exact Nat.le_of_mul_le_mul_left h (by norm_num : 0 < 2 ^ 2)
  exact ⟨hn_eq, E, hEab, hEcomm, hfinal⟩

end CFSG.LocalAnalysis.RankThreeUC.S15

end
