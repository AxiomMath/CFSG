module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311f
public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootF4
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4TransportFacts
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InnerIsoFrame
import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.Main
public import CFSG.RankThree.PartOne.S11d.FourSeedTheta
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveFourFrame
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveA4Closing
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FrameDatum
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4FrameCentral

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311d
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcHighThree

section Abstract

theorem uniClosure_eq_top_of_closingFrames {G : Type*} [Group G] {E : Subgroup G} {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hgen : E ≤ Subgroup.closure {a, b}) {X Y : Subgroup G}
    (hX : ClosingFrameAt a X) (hY : ClosingFrameAt b Y)
    (hCE : Group.IsSolvable ↥(Subgroup.centralizer (E : Set G))) {r : ℕ}
    (hXr : X ≤ Subgroup.closure {x | x ∈ X ∧ ∃ n : ℕ, x ^ (r ^ n) = 1})
    (hYr : Y ≤ Subgroup.closure {x | x ∈ Y ∧ ∃ n : ℕ, x ^ (r ^ n) = 1}) :
    Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} = ⊤ := by
  set H := Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} with hH
  have hXH : X ≤ H := hXr.trans ((Subgroup.closure_le _).2 fun k ⟨hk, n, hn⟩ =>
    Subgroup.subset_closure ⟨a, ha, ha1, Subgroup.mem_centralizer_singleton_iff.1 (hX.centralizes hk), n, hn⟩)
  have hYH : Y ≤ H := hYr.trans ((Subgroup.closure_le _).2 fun k ⟨hk, n, hn⟩ =>
    Subgroup.subset_closure ⟨b, hb, hb1, Subgroup.mem_centralizer_singleton_iff.1 (hY.centralizes hk), n, hn⟩)
  refine hX.closing H hXH fun hN => ?_
  refine not_le_normalizer_of_solvable_centralizer hX.centralizes hY.centralizes
    hX.normalizer_solvable hY.nonsolvable ?_ (hYH.trans hN)
  have hle : Subgroup.centralizer ({a, b} : Set G) ≤ Subgroup.centralizer (E : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro h hh
    have hcl : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hx _ (by simp))
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hx _ (by simp))
    exact Subgroup.mem_centralizer_singleton_iff.1 (hcl (hgen hh))
  haveI := hCE
  exact solvable_of_solvable_injective (Subgroup.inclusion_injective hle)

theorem exists_noncentral_pElement_of_perfect {X : Type*} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]
    (hperf : commutator X = ⊤) (hdvd : p ∣ Nat.card X) :
    ∃ d : X, (∃ k : ℕ, orderOf d = p ^ k) ∧ ∃ e : X, d * e ≠ e * d := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨P⟩ : Nonempty (Sylow p X) := inferInstance
  have hPc : ∀ x ∈ (P : Subgroup X), ∀ g : X, x * g = g * x := by
    intro x hx g
    obtain ⟨k, hk⟩ := (P.isPGroup' ⟨x, hx⟩)
    have hk' : x ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1 (orderOf_dvd_of_pow_eq_one hk')
    exact hcon x ⟨j, hj⟩ g
  have hP : Subgroup.normalizer (P : Subgroup X) ≤ Subgroup.centralizer (P : Set X) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact hPc h hh g
  have hker : (MonoidHom.transferSylow P hP).ker = ⊤ := by
    rw [eq_top_iff, ← hperf, commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact Subtype.ext (hPc _ (MonoidHom.transferSylow P hP x).2 _)
  have h1 := MonoidHom.not_dvd_card_ker_transferSylow P hP
  rw [hker, Subgroup.card_top] at h1
  exact h1 hdvd

theorem le_closure_pow_of_quasisimple {G : Type} [Group G] {X : Subgroup G} [Finite X] {r : ℕ}
    [Fact r.Prime] (hX : CFSG.IsQuasisimple ↥X) (hdvd : r ∣ Nat.card X) :
    X ≤ Subgroup.closure {x | x ∈ X ∧ ∃ n : ℕ, x ^ (r ^ n) = 1} := by
  have hperf : commutator ↥X = ⊤ := hX.1.commutator_eq_top
  obtain ⟨d, ⟨k, hk⟩, e, hde⟩ := exists_noncentral_pElement_of_perfect (p := r) hperf hdvd
  have h := CFSG.RankThree.PartOne.FourSeed.le_closure_pElements_of_quasisimple (G := G) hX d.2
    ⟨k, by rw [Subgroup.orderOf_coe]; exact hk⟩
    ⟨e, e.2, fun h => hde (Subtype.ext (by simpa using h))⟩
  intro x hx
  refine Subgroup.closure_mono ?_ (h x hx)
  rintro y ⟨hy, j, hj⟩
  exact ⟨hy, j, by rw [← hj]; exact pow_orderOf_eq_one y⟩

theorem subgroupOf_le_closure_of_le {G : Type*} [Group G] {A X : Subgroup G} (hXA : X ≤ A) {r : ℕ}
    (hX : X ≤ Subgroup.closure {x | x ∈ X ∧ ∃ n : ℕ, x ^ (r ^ n) = 1}) :
    X.subgroupOf A ≤ Subgroup.closure {s | s ∈ X.subgroupOf A ∧ ∃ n : ℕ, s ^ (r ^ n) = 1} := by
  intro y hy
  have h1 : Subgroup.closure {x | x ∈ X ∧ ∃ n : ℕ, x ^ (r ^ n) = 1} ≤
      (Subgroup.closure {s | s ∈ X.subgroupOf A ∧ ∃ n : ℕ, s ^ (r ^ n) = 1}).map A.subtype := by
    rw [Subgroup.closure_le]
    rintro x ⟨hx, n, hn⟩
    refine ⟨⟨x, hXA hx⟩, Subgroup.subset_closure ⟨Subgroup.mem_subgroupOf.2 hx, n, ?_⟩, rfl⟩
    exact Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hn)
  obtain ⟨z, hz, hzy⟩ := h1 (hX (Subgroup.mem_subgroupOf.1 hy))
  rwa [show z = y from Subtype.ext hzy] at hz

theorem uniPlaneGen_of_native_uniClosure {C N : Type*} [Group C] [Group N]
    (e : C ≃* N) (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {p r : ℕ}
    (hnat : ∀ E₀ : Subgroup N, (∀ x ∈ E₀, x ^ p = 1) → Nat.card E₀ = p ^ 2 →
      ¬ (∃ R : Subgroup N, R ≠ ⊥ ∧ IsPGroup r R ∧
        ∀ g ∈ E₀, R.map (MulAut.conj g).toMonoidHom = R) →
      Subgroup.closure {k : N | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} = ⊤)
    {E : Subgroup (MulAut C)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    (hin : E ≤ (MulAut.conj : C →* MulAut C).range)
    (hnorm : ¬ ∃ R : Subgroup C, R ≠ ⊥ ∧ IsPGroup r R ∧ ∀ ε ∈ E, R.map ε.toMonoidHom = R) :
    UniPlaneGen r E := by
  set E₀C : Subgroup C := E.comap (MulAut.conj : C →* MulAut C) with hE₀C
  have hmap : E₀C.map (MulAut.conj : C →* MulAut C) = E := Subgroup.map_comap_eq_self hin
  set E₀ : Subgroup N := E₀C.map e.toMonoidHom with hE₀
  have hE₀p : ∀ x ∈ E₀, x ^ p = 1 := by
    rintro _ ⟨c, hc, rfl⟩
    have h1 : (MulAut.conj : C →* MulAut C) (c ^ p) = 1 := by
      rw [map_pow]
      exact hE.2 _ hc
    have h2 : c ^ p = 1 := hinj (h1.trans (map_one _).symm)
    rw [← map_pow, h2, map_one]
  have hE₀c : Nat.card E₀ = p ^ 2 := by
    rw [hE₀, Subgroup.card_map_of_injective e.injective, ← hcard, ← hmap,
      Subgroup.card_map_of_injective hinj]
  have hnotN : ¬ ∃ R : Subgroup N, R ≠ ⊥ ∧ IsPGroup r R ∧
      ∀ g ∈ E₀, R.map (MulAut.conj g).toMonoidHom = R := fun h =>
    hnorm (hmap ▸ exists_normalized_of_native e h)
  have htop := hnat E₀ hE₀p hE₀c hnotN
  set T : Set C := {k | ∃ c ∈ E₀C, c ≠ 1 ∧ Commute k c ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} with hT
  have himage : e.toMonoidHom '' T =
      {k : N | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} := by
    ext k
    constructor
    · rintro ⟨k₀, ⟨c, hc, hc1, hkc, n, hn⟩, rfl⟩
      exact ⟨e c, ⟨c, hc, rfl⟩, fun h => hc1 (e.injective (h.trans (map_one e).symm)),
        hkc.map e.toMonoidHom, n, by rw [← map_pow, hn, map_one]⟩
    · rintro ⟨_, ⟨c, hc, rfl⟩, hx1, hkx, n, hn⟩
      refine ⟨e.symm k, ⟨c, hc, fun h => hx1 (by rw [h]; exact map_one e.toMonoidHom), ?_, n, ?_⟩, ?_⟩
      · have := hkx.map e.symm.toMonoidHom
        simpa using this
      · rw [← map_pow, hn, map_one]
      · simp
  have hTtop : Subgroup.closure T = ⊤ := by
    rw [eq_top_iff]
    intro k _
    have hk : e.toMonoidHom k ∈
        Subgroup.closure {k : N | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [← himage, ← MonoidHom.map_closure] at hk
    obtain ⟨k₀, hk₀, hk₀e⟩ := hk
    have : k₀ = k := e.injective hk₀e
    rw [← this]
    exact hk₀
  have hle : Subgroup.closure T ≤ uniPlaneClosure r E := by
    rw [Subgroup.closure_le]
    rintro k ⟨c, hc, hc1, hkc, n, hn⟩
    refine mem_uniPlaneClosure (e := MulAut.conj c) ?_ (fun h => hc1 ?_) ?_ hn
    · rw [← hmap]
      exact ⟨c, hc, rfl⟩
    · exact hinj (h.trans (map_one _).symm)
    · rw [MulAut.conj_apply, ← hkc.eq]
      group
  rw [UniPlaneGen, eq_top_iff, ← hTtop]
  exact hle

theorem uniClosure_eq_top_of_conj {G : Type*} [Group G] {E : Subgroup G} (g : G) {r : ℕ}
    (h : Subgroup.closure {k | ∃ x ∈ E.map (MulAut.conj g).toMonoidHom, x ≠ 1 ∧ Commute k x ∧
      ∃ n : ℕ, k ^ (r ^ n) = 1} = ⊤) :
    Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} = ⊤ := by
  set S := {k : G | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} with hS
  have hle : {k | ∃ x ∈ E.map (MulAut.conj g).toMonoidHom, x ≠ 1 ∧ Commute k x ∧
      ∃ n : ℕ, k ^ (r ^ n) = 1} ⊆ ((Subgroup.closure S).map (MulAut.conj g).toMonoidHom : Set G) := by
    rintro k ⟨_, ⟨x, hx, rfl⟩, hx1, hkx, n, hn⟩
    refine ⟨g⁻¹ * k * g, Subgroup.subset_closure ⟨x, hx, fun h => hx1 (by rw [h, map_one]), ?_, n, ?_⟩, ?_⟩
    · have h1 := hkx.map (MulAut.conj g⁻¹).toMonoidHom
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
      simpa [mul_assoc] using h1
    · rw [show g⁻¹ * k * g = (MulAut.conj g⁻¹) k by simp [MulAut.conj_apply], ← map_pow, hn, map_one]
    · simp [MulAut.conj_apply, mul_assoc]
  have htop : (Subgroup.closure S).map (MulAut.conj g).toMonoidHom = ⊤ := by
    rw [eq_top_iff, ← h]
    exact (Subgroup.closure_le _).2 hle
  rw [eq_top_iff]
  intro y _
  have hy : (MulAut.conj g).toMonoidHom y ∈ (Subgroup.closure S).map (MulAut.conj g).toMonoidHom := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨z, hz, hzy⟩ := hy
  rwa [(MulAut.conj g).injective hzy] at hz

theorem map_le_uniClosure {F M : Type*} [Group F] [Group M] (ι : F →* M) (hι : Function.Injective ι)
    (E₃ : Subgroup F) {r : ℕ}
    (hF : Subgroup.closure {k | ∃ x ∈ E₃, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} = ⊤) :
    ι.range ≤ Subgroup.closure {k | ∃ x ∈ E₃.map ι, x ≠ 1 ∧ Commute k x ∧
      ∃ n : ℕ, k ^ (r ^ n) = 1} := by
  rintro _ ⟨y, rfl⟩
  have hy : y ∈ Subgroup.closure {k | ∃ x ∈ E₃, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} := by
    rw [hF]
    exact Subgroup.mem_top y
  have h1 := Subgroup.mem_map_of_mem ι hy
  rw [MonoidHom.map_closure] at h1
  refine (Subgroup.closure_le _).2 ?_ h1
  rintro _ ⟨k, ⟨x, hx, hx1, hkx, n, hn⟩, rfl⟩
  exact Subgroup.subset_closure ⟨ι x, ⟨x, hx, rfl⟩, fun h => hx1 (hι (h.trans (map_one ι).symm)),
    hkx.map ι, n, by rw [← map_pow, hn, map_one]⟩

theorem map_le_closure_pow {G H : Type*} [Group G] [Group H] (f : G →* H) {X : Subgroup G} {r : ℕ}
    (hX : X ≤ Subgroup.closure {x | x ∈ X ∧ ∃ n : ℕ, x ^ (r ^ n) = 1}) :
    X.map f ≤ Subgroup.closure {y | y ∈ X.map f ∧ ∃ n : ℕ, y ^ (r ^ n) = 1} := by
  rintro _ ⟨x, hx, rfl⟩
  have h1 := Subgroup.mem_map_of_mem f (hX hx)
  rw [MonoidHom.map_closure] at h1
  refine Subgroup.closure_mono ?_ h1
  rintro _ ⟨y, ⟨hy, n, hn⟩, rfl⟩
  exact ⟨⟨y, hy, rfl⟩, n, by rw [← map_pow, hn, map_one]⟩

theorem uniClosure_eq_top_of_quotient {G Q : Type*} [Group G] [Group Q] [Finite G] {p r : ℕ}
    [Fact p.Prime] (π : G →* Q) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (hcop : ¬ p ∣ Nat.card π.ker) (hrcop : (Nat.card π.ker).Coprime r)
    (hperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤) (E : Subgroup G) (hE : ∀ x ∈ E, x ^ p = 1)
    (hQ : Subgroup.closure {k : Q | ∃ y ∈ E.map π, y ≠ 1 ∧ k * y = y * k ∧ k ^ r = 1} = ⊤) :
    Subgroup.closure {g : G | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ r = 1} = ⊤ := by
  classical
  set S : Set G := {g | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ r = 1} with hS
  set C : Subgroup G := Subgroup.closure S with hC
  have hlift : ∀ (g x : G), x ∈ E → π g * π x = π x * π g → g * x = x * g := by
    intro g x hx h
    have hc : g * x * g⁻¹ * x⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [h]
      group
    have hcen := Subgroup.mem_center_iff.mp (hker hc)
    have hcp : (g * x * g⁻¹ * x⁻¹) ^ p = 1 := by
      set c := g * x * g⁻¹ * x⁻¹ with hcdef
      have hgx : g * x * g⁻¹ = c * x := by rw [hcdef]; group
      have h1 : g * x ^ p * g⁻¹ = (c * x) ^ p := by
        rw [← hgx, conj_pow]
      rw [hE x hx, mul_one, mul_inv_cancel, (Commute.mul_pow (hcen x).symm), hE x hx, mul_one] at h1
      exact h1.symm
    have := CFSG.HardMathSupport.Lang.AnisoF4.eq_one_of_pow_eq_one_of_not_dvd hcop hc hcp
    have h2 : g * x = x * g := by
      have := congrArg (· * (x * g)) this
      simpa [mul_assoc] using this
    exact h2
  have hmap : C.map π = ⊤ := by
    rw [eq_top_iff, ← hQ, Subgroup.closure_le]
    rintro k ⟨y, ⟨x, hx, rfl⟩, hy1, hk, hkr⟩
    obtain ⟨g₀, rfl⟩ := hπ k
    have hx1 : x ≠ 1 := fun h => hy1 (by rw [h, map_one])
    have hz : g₀ ^ r ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hkr]
    obtain ⟨w, hw⟩ := hrcop.pow_left_bijective.2 (⟨g₀ ^ r, hz⟩ : π.ker)⁻¹
    have hwc : ∀ h : G, h * (w : G) = (w : G) * h := fun h =>
      Subgroup.mem_center_iff.mp (hker w.2) h
    have hwr : (w : G) ^ r = (g₀ ^ r)⁻¹ := by
      have := congrArg Subtype.val hw
      simpa using this
    have hgx : g₀ * x = x * g₀ := hlift g₀ x hx hk
    refine ⟨g₀ * w, Subgroup.subset_closure ⟨x, hx, hx1, ?_, ?_⟩, ?_⟩
    · calc g₀ * (w : G) * x = g₀ * x * w := by rw [mul_assoc, ← hwc x, ← mul_assoc]
        _ = x * g₀ * w := by rw [hgx]
        _ = x * (g₀ * w) := mul_assoc _ _ _
    · rw [(Commute.mul_pow (hwc g₀) r), hwr, mul_inv_cancel]
    · rw [map_mul, MonoidHom.mem_ker.mp w.2, mul_one]
  have hCZ : ∀ g : G, ∃ c ∈ C, ∃ z ∈ Subgroup.center G, g = c * z := by
    intro g
    have : π g ∈ C.map π := hmap ▸ Subgroup.mem_top _
    obtain ⟨c, hcC, hc⟩ := this
    refine ⟨c, hcC, c⁻¹ * g, hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hc]; group), ?_⟩
    group
  rw [eq_top_iff, ← hperf, Subgroup.commutator_le]
  intro a _ b _
  obtain ⟨c1, hc1, z1, hz1, rfl⟩ := hCZ a
  obtain ⟨c2, hc2, z2, hz2, rfl⟩ := hCZ b
  rw [CFSG.HardMathSupport.Lang.AnisoF4.commutator_mul_central c1 c2 z1 z2
    (Subgroup.mem_center_iff.mp hz1) (Subgroup.mem_center_iff.mp hz2)]
  rw [commutatorElement_def]
  exact C.mul_mem (C.mul_mem (C.mul_mem hc1 hc2) (C.inv_mem hc1)) (C.inv_mem hc2)

theorem uniClosure_map_conj {G : Type*} [Group G] (g : G) (E : Subgroup G) {r : ℕ} :
    Subgroup.closure {k | ∃ x ∈ E.map (MulAut.conj g).toMonoidHom, x ≠ 1 ∧ Commute k x ∧
        ∃ n : ℕ, k ^ (r ^ n) = 1} =
      (Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1}).map
        (MulAut.conj g).toMonoidHom := by
  set φ : G →* G := (MulAut.conj g).toMonoidHom with hφ
  have himg : {k | ∃ x ∈ E.map φ, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} =
      φ '' {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} := by
    ext k
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, hx1, hkx, n, hn⟩
      refine ⟨g⁻¹ * k * g, ⟨x, hx, fun h => hx1 (by rw [h, map_one]), ?_, n, ?_⟩, ?_⟩
      · have h := hkx.map (MulAut.conj g⁻¹).toMonoidHom
        simpa [hφ, MulAut.conj_apply, mul_assoc] using h
      · rw [show g⁻¹ * k * g = (MulAut.conj g⁻¹) k by simp [MulAut.conj_apply], ← map_pow, hn,
          map_one]
      · simp [hφ, MulAut.conj_apply, mul_assoc]
    · rintro ⟨k', ⟨x, hx, hx1, hkx, n, hn⟩, rfl⟩
      refine ⟨φ x, ⟨x, hx, rfl⟩, fun h => hx1 ?_, hkx.map φ, n, by rw [← map_pow, hn, map_one]⟩
      exact (MulAut.conj g).injective (h.trans (map_one φ).symm)
  rw [himg, ← MonoidHom.map_closure]

theorem uniClosure_eq_top_of_two_conj {G : Type*} [Group G] {p r : ℕ} (X P : Subgroup G)
    (n : G) (hPX : P ≤ X) (hPXn : P ≤ X.map (MulAut.conj n).toMonoidHom)
    (hclose : ∀ M : Subgroup G, X ≤ M → X.map (MulAut.conj n).toMonoidHom ≤ M → M = ⊤)
    (hX : ∀ E : Subgroup G, E ≤ X → (∀ x ∈ E, x ^ p = 1) → Nat.card E = p ^ 2 →
      X ≤ Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ Commute g x ∧ ∃ m : ℕ, g ^ (r ^ m) = 1})
    (E₀ : Subgroup G) (hE₀p : ∀ x ∈ E₀, x ^ p = 1) (hE₀c : Nat.card E₀ = p ^ 2)
    (hSyl : ∃ g : G, E₀.map (MulAut.conj g).toMonoidHom ≤ P) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (r ^ m) = 1} = ⊤ := by
  obtain ⟨g, hg⟩ := hSyl
  set E₁ := E₀.map (MulAut.conj g).toMonoidHom with hE₁
  have hE₁p : ∀ x ∈ E₁, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE₀p x hx, map_one]
  have hE₁c : Nat.card E₁ = p ^ 2 := by
    rw [hE₁, Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₀c]
  have hE₁X : E₁ ≤ X := hg.trans hPX
  set E₂ := E₁.map (MulAut.conj n⁻¹).toMonoidHom with hE₂
  have hE₂p : ∀ x ∈ E₂, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE₁p x hx, map_one]
  have hE₂c : Nat.card E₂ = p ^ 2 := by
    rw [hE₂, Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective, hE₁c]
  have hE₂X : E₂ ≤ X := by
    have h : E₁ ≤ X.map (MulAut.conj n).toMonoidHom := hg.trans hPXn
    calc E₂ ≤ (X.map (MulAut.conj n).toMonoidHom).map (MulAut.conj n⁻¹).toMonoidHom :=
          Subgroup.map_mono h
      _ = X := CFSG.LieType.SeitzGeneration.ExcHigh.map_conj_map_conj_inv n X
  have hM1 := hX E₁ hE₁X hE₁p hE₁c
  have hM2 := hX E₂ hE₂X hE₂p hE₂c
  have hM2' : X.map (MulAut.conj n).toMonoidHom ≤
      Subgroup.closure {k | ∃ x ∈ E₁, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (r ^ m) = 1} := by
    rw [hE₂, uniClosure_map_conj] at hM2
    have h3 := Subgroup.map_mono (f := (MulAut.conj n).toMonoidHom) hM2
    have h4 := CFSG.LieType.SeitzGeneration.ExcHigh.map_conj_map_conj_inv n⁻¹
      (Subgroup.closure {k | ∃ x ∈ E₁, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (r ^ m) = 1})
    rw [inv_inv] at h4
    rwa [h4] at h3
  exact uniClosure_eq_top_of_conj g (hclose _ hM1 hM2')

end Abstract

section SplitF4

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

theorem closingFrameAt_split (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 1) (ω : Kˣ)
    (hω : orderOf ω = 3) : ClosingFrameAt (zSplit K ω) (frameIn (XS K)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK4 : 4 ≤ Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  set a : Fin Tag.F4.rank → Kˣ := Pi.mulSingle (1 : Fin Tag.F4.rank) ω with ha
  have hchar : ∀ α : Fin Tag.F4.rank → ℤ, rootChar a α = ω ^ (α 1) := by
    intro α
    unfold rootChar
    rw [Finset.prod_eq_single (1 : Fin Tag.F4.rank)]
    · simp [ha]
    · intro j _ hj
      simp [ha, Pi.mulSingle_eq_of_ne hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hS : ∀ α ∈ cosetRoots Tag.F4 1 3, IsRoot Tag.F4 α ∧ rootChar a α = 1 := by
    intro α hα
    refine ⟨hα.1, ?_⟩
    rw [hchar, ← orderOf_dvd_iff_zpow_eq_one, hω]
    exact_mod_cast hα.2
  have hXS : XS K ≤ adjointGroup .F4 K := rootSpan_le_adjointGroup K _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hy' : (y : ModGL .F4 K) ∈ XS K := hy
    have := Subgroup.mem_centralizer_singleton_iff.1
      (rootSpan_le_centralizer_rootDiagUnit (K := K) a hS hy')
    exact this
  · refine nonsolvable_frameIn hXS ?_
    intro hs
    haveI := hs
    haveI h2 : Group.IsSolvable ↥(X2 K) :=
      solvable_of_solvable_injective (Subgroup.inclusion_injective (X2_le_XS K))
    obtain ⟨hperf, -, a₀, b₀, hab⟩ := X2_quasisimple K
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a₀
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b₀
    haveI : Nontrivial ↥(X2 K) := ⟨⟨x, 1, fun h => hab (by rw [h]; simp)⟩⟩
    exact (IsSolvable.commutator_lt_top_of_nontrivial (↥(X2 K))).ne hperf.commutator_eq_top
  · exact closing_of_twFrameClosing hXS
      ((frameClosing_iff Tag.F4 K _).1
        (frameClosing_of_detection_F4 K (by omega) (DetectF4.frameDetection_F4 K (by omega))))
  · exact normalizerSolvable_of_twFrame hXS
      ((frameNormalizerSolvable_iff Tag.F4 K _).1 (frameNormalizerSolvable_F4 K hK4))

theorem pinnedX_pow_eq {τ : Tag} {R : Type*} [CommRing R] (α : Fin τ.rank → ℤ) (c : R) (n : ℕ) :
    pinnedX τ R α c ^ n = pinnedX τ R α ((n : R) * c) := by
  induction n with
  | zero => simp [pinnedX_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← pinnedX_add]
    congr 1
    push_cast
    ring

theorem frameIn_XS_le_closure (K : Type) [Field K] [Finite K] :
    frameIn (XS K) ≤
      Subgroup.closure {x | x ∈ frameIn (XS K) ∧ ∃ n : ℕ, x ^ (ringChar K ^ n) = 1} := by
  refine subgroupOf_le_closure_of_le (rootSpan_le_adjointGroup K _) ?_
  refine iSup₂_le fun α hα => ?_
  rw [rootSubgroup, Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩
  refine Subgroup.subset_closure ⟨?_, 1, ?_⟩
  · exact (le_iSup₂_of_le (f := fun β (_ : β ∈ cosetRoots Tag.F4 1 3) => rootSubgroup Tag.F4 K β) α hα
      le_rfl) (Subgroup.subset_closure ⟨c, rfl⟩)
  · rw [pow_one, pinnedX_pow_eq, ringChar.Nat.cast_ringChar, zero_mul, pinnedX_zero]

end SplitF4

section TwF4

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Tables.T1b
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice

set_option linter.unusedSectionVars false

theorem closingFrameAt_twisted (K : Type) [Field K] [Finite K] (h3 : 3 ≤ Nat.card K)
    (D : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w) (ω : D.Lˣ) (hω3 : orderOf ω = 3)
    (z : adjointGroup TwClass.f4Six.tag K)
    (hzbc : baseChangeGL (algebraMap K D.L) (z : ModGL TwClass.f4Six.tag K) =
      D.g * rootDiagUnit TwClass.f4Six.tag (Pi.mulSingle (⟨1, by decide⟩ : Fin
        TwClass.f4Six.tag.rank) ω) * D.g⁻¹) :
    ClosingFrameAt z (frameIn (TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D)) := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  set i₁ : Fin TwClass.f4Six.tag.rank := ⟨1, by decide⟩ with hi₁
  set a : Fin TwClass.f4Six.tag.rank → D.Lˣ := Pi.mulSingle i₁ ω with ha
  have hzbc' : baseChangeGL (algebraMap K D.L) (z : ModGL TwClass.f4Six.tag K) =
      D.g * rootDiagUnit TwClass.f4Six.tag a * D.g⁻¹ := hzbc
  have hchar : ∀ α : Fin TwClass.f4Six.tag.rank → ℤ, rootChar a α = ω ^ (α i₁) := by
    intro α
    unfold rootChar
    rw [Finset.prod_eq_single i₁]
    · simp [ha]
    · intro j _ hj
      simp [ha, Pi.mulSingle_eq_of_ne hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hS : ∀ S : Set (Fin TwClass.f4Six.tag.rank → ℤ), (∀ α ∈ S, 3 ∣ α i₁) →
      (∀ α ∈ S, IsRoot TwClass.f4Six.tag α) → ∀ α ∈ S, IsRoot TwClass.f4Six.tag α ∧
        rootChar a α = 1 := by
    intro S h3S hrS α hα
    refine ⟨hrS α hα, ?_⟩
    rw [hchar, ← orderOf_dvd_iff_zpow_eq_one, hω3]
    exact_mod_cast h3S α hα
  have hS₁ : ∀ α ∈ TwClass.f4Six.S₁, IsRoot TwClass.f4Six.tag α ∧ rootChar a α = 1 := by
    refine hS _ (fun α hα => ?_) (fun α hα => hα.1)
    have hα' : α ∈ {r | r ∈ f4LongList} := by rw [← QuasiF4.S₁_eq]; exact hα
    have hmem : α ∈ cosetRoots Tag.F4 1 3 := by
      rw [coset_eq]
      exact Or.inl hα'
    exact hmem.2
  have hS₂ : ∀ α ∈ TwClass.f4Six.S₂, IsRoot TwClass.f4Six.tag α ∧ rootChar a α = 1 := by
    refine hS _ (fun α hα => ?_) (fun α hα => hα.1)
    have hα' : α ∈ {r | r ∈ f4ShortList} := by rw [← QuasiF4.S₂_eq]; exact hα
    have hmem : α ∈ cosetRoots Tag.F4 1 3 := by
      rw [coset_eq]
      exact Or.inr hα'
    exact hmem.2
  have hcomm : ∀ S : Set (Fin TwClass.f4Six.tag.rank → ℤ),
      (∀ α ∈ S, IsRoot TwClass.f4Six.tag α ∧ rootChar a α = 1) →
      D.frame S ≤ Subgroup.centralizer ({(z : ModGL TwClass.f4Six.tag K)} :
        Set (ModGL TwClass.f4Six.tag K)) := by
    intro S hS' x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxc := rootSpan_le_centralizer_rootDiagUnit (K := D.L) a hS' hx.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hxc
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxc
    apply baseChangeGL_injective (algebraMap K D.L)
    rw [map_mul, map_mul, hzbc']
    calc baseChangeGL (algebraMap K D.L) x * (D.g * rootDiagUnit TwClass.f4Six.tag a * D.g⁻¹)
        = D.g * ((D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g⁻¹⁻¹) *
            rootDiagUnit TwClass.f4Six.tag a) * D.g⁻¹ := by group
      _ = D.g * (rootDiagUnit TwClass.f4Six.tag a * (D.g⁻¹ * baseChangeGL (algebraMap K D.L) x *
            D.g⁻¹⁻¹)) * D.g⁻¹ := by rw [hxc]
      _ = (D.g * rootDiagUnit TwClass.f4Six.tag a * D.g⁻¹) * baseChangeGL (algebraMap K D.L) x := by
          group
  have hKq : TwClass.f4Six.minQ ≤ Nat.card K := by
    show 3 ≤ Nat.card K
    exact h3
  have hle : TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D ≤ adjointGroup TwClass.f4Six.tag K :=
    sup_le inf_le_left inf_le_left
  have hq3 := twQuasi_of_ne_e6Six TwClass.f4Six (by decide) K hKq D
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hy' : (y : ModGL TwClass.f4Six.tag K) ∈
        TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D := hy
    have hsup : TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D ≤
        Subgroup.centralizer ({(z : ModGL TwClass.f4Six.tag K)} : Set (ModGL TwClass.f4Six.tag K)) :=
      sup_le (hcomm _ hS₁) (hcomm _ hS₂)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hsup hy')
  · refine nonsolvable_frameIn hle ?_
    intro hs
    haveI := hs
    haveI h2 : Group.IsSolvable ↥(TwClass.f4Six.X₂ D) :=
      solvable_of_solvable_injective (Subgroup.inclusion_injective
        (le_sup_right : TwClass.f4Six.X₂ D ≤ TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D))
    obtain ⟨hperf, -, a₀, b₀, hab⟩ := hq3.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a₀
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b₀
    haveI : Nontrivial ↥(TwClass.f4Six.X₂ D) := ⟨⟨x, 1, fun h => hab (by rw [h]; simp)⟩⟩
    exact (IsSolvable.commutator_lt_top_of_nontrivial
      (↥(TwClass.f4Six.X₂ D))).ne hperf.commutator_eq_top
  · exact closing_of_twFrameClosing hle (twClosing_f4Six K h3 D)
  · exact normalizerSolvable_of_twFrame hle (twNormalizer_f4Six K hKq D)

theorem frameIn_twisted_le_closure (K : Type) [Field K] [Finite K] (h3 : 3 ≤ Nat.card K)
    (D : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w) :
    frameIn (TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D) ≤
      Subgroup.closure {x | x ∈ frameIn (TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D) ∧
        ∃ n : ℕ, x ^ (ringChar K ^ n) = 1} := by
  classical
  have hle : TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D ≤ adjointGroup TwClass.f4Six.tag K :=
    sup_le inf_le_left inf_le_left
  refine subgroupOf_le_closure_of_le hle ?_
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hr : ringChar K ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self _ n.ne_zero
  have : Finite (ModGL TwClass.f4Six.tag K) := finite_modGL
  obtain ⟨hc₁, hc₂, -⟩ := TwCardAux.f4Six_frames K h3 D
  have hd : ringChar K ∣ Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 + 1)) :=
    dvd_mul_of_dvd_left (dvd_pow hr (by norm_num)) _
  have h₁ := le_closure_pow_of_quasisimple (r := ringChar K) (isQuasisimple_f4Six_X₁ h3 D)
    (by rw [hc₁]; exact hd)
  have h₂ := le_closure_pow_of_quasisimple (r := ringChar K) (isQuasisimple_f4Six_X₂ h3 D)
    (by rw [hc₂]; exact hd)
  refine sup_le (h₁.trans (Subgroup.closure_mono fun x ⟨hx, k, hk⟩ =>
    ⟨Subgroup.mem_sup_left hx, k, hk⟩)) (h₂.trans (Subgroup.closure_mono fun x ⟨hx, k, hk⟩ =>
    ⟨Subgroup.mem_sup_right hx, k, hk⟩))

end TwF4

section F4Three

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame CFSG.HardMathSupport.Timmesfeld.Torality TauCeti

set_option linter.unusedSectionVars false

theorem f4ThreeUniNative_of_three_le (K : Type) [Field K] [Finite K]
    (h3 : 3 ≤ Nat.card K) (hnd : ¬ 3 ∣ Nat.card K) (E₀ : Subgroup (adjointGroup .F4 K))
    (hexp : ∀ x ∈ E₀, x ^ 3 = 1) (hcard : Nat.card E₀ = 3 ^ 2) (hn : ¬ NormalizesRNative .F4 K E₀) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (ringChar K ^ n) = 1} = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK3 : 3 ≤ Nat.card K := h3
  rcases (langToralOrParabolic_of_langToralPlane langToralPlane_F4_three) K hnd E₀ hexp hcard with
    ⟨⟨D⟩⟩ | hnorm
  · have hreg : ∀ α, IsRoot .F4 α → ¬ D.Kills α := fun α hα hk =>
      hn (normalizesRNative_of_unip (langPlaneKillsRoot_F4 K E₀ D α hα hk))
    obtain ⟨a, ha, b, hb, ha1, hb1, hgen⟩ := exists_gens_of_plane (p := 3) hexp hcard
    rcases (by omega : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2) with hres | hres
    ·
      have hdvd : 3 ∣ Nat.card Kˣ := by
        rw [Nat.card_units]
        have := Nat.card_pos (α := K)
        omega
      obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
      have hX := closingFrameAt_split K hres ω hω
      have hXr := frameIn_XS_le_closure K
      obtain ⟨ga, hga⟩ := f4PureSplit_holds K hres ω hω E₀ hexp hcard D hreg a ha ha1
      obtain ⟨gb, hgb⟩ := f4PureSplit_holds K hres ω hω E₀ hexp hcard D hreg b hb hb1
      have hXa : ClosingFrameAt a ((frameIn (XS K)).map (MulAut.conj ga⁻¹).toMonoidHom) := by
        have := hX.conj ga⁻¹
        rwa [show ga⁻¹ * zSplit K ω * ga⁻¹⁻¹ = a by rw [← hga]; group] at this
      have hXb : ClosingFrameAt b ((frameIn (XS K)).map (MulAut.conj gb⁻¹).toMonoidHom) := by
        have := hX.conj gb⁻¹
        rwa [show gb⁻¹ * zSplit K ω * gb⁻¹⁻¹ = b by rw [← hgb]; group] at this
      exact uniClosure_eq_top_of_closingFrames ha hb ha1 hb1 hgen hXa hXb
        (f4RegularSolvable 1 K hres E₀ hexp hcard D hreg) (map_le_closure_pow _ hXr)
        (map_le_closure_pow _ hXr)
    ·
      obtain ⟨D₁⟩ := exists_langLevi TwClass.f4Six.tag K TwClass.f4Six.w
        (TwClass.w_theta TwClass.f4Six)
      obtain ⟨ω, hω⟩ := exists_cube_root_langLevi K hnd D₁
      obtain ⟨z, hzbc, -, -, -⟩ := f4TwistedFrame_of K hres hK3 D₁ ω hω
      let z₀ : adjointGroup Tag.F4 K := z
      have hX : ClosingFrameAt z₀ (frameIn (TwClass.f4Six.X₁ D₁ ⊔ TwClass.f4Six.X₂ D₁)) :=
        closingFrameAt_twisted K hK3 D₁ ω hω z hzbc
      have hXr := frameIn_twisted_le_closure K hK3 D₁
      obtain ⟨ga, hga⟩ := f4PureTwisted_holds K hres hK3 D₁ ω hω z hzbc E₀ hexp hcard D hreg a ha ha1
      obtain ⟨gb, hgb⟩ := f4PureTwisted_holds K hres hK3 D₁ ω hω z hzbc E₀ hexp hcard D hreg b hb hb1
      have hga' : ga * a * ga⁻¹ = z₀ := hga
      have hgb' : gb * b * gb⁻¹ = z₀ := hgb
      have hXa : ClosingFrameAt a ((frameIn (TwClass.f4Six.X₁ D₁ ⊔ TwClass.f4Six.X₂ D₁)).map
          (MulAut.conj ga⁻¹).toMonoidHom) := by
        have := hX.conj ga⁻¹
        rwa [show ga⁻¹ * z₀ * ga⁻¹⁻¹ = a by rw [← hga']; group] at this
      have hXb : ClosingFrameAt b ((frameIn (TwClass.f4Six.X₁ D₁ ⊔ TwClass.f4Six.X₂ D₁)).map
          (MulAut.conj gb⁻¹).toMonoidHom) := by
        have := hX.conj gb⁻¹
        rwa [show gb⁻¹ * z₀ * gb⁻¹⁻¹ = b by rw [← hgb']; group] at this
      exact uniClosure_eq_top_of_closingFrames ha hb ha1 hb1 hgen hXa hXb
        (f4RegularSolvable 2 K hres E₀ hexp hcard D hreg) (map_le_closure_pow _ hXr)
        (map_le_closure_pow _ hXr)
  · exact absurd hnorm hn

theorem f4ThreeUniNative (K : Type) [Field K] [Finite K]
    (hK2 : ringChar K ≠ 2) (hnd : ¬ 3 ∣ Nat.card K) (E₀ : Subgroup (adjointGroup .F4 K))
    (hexp : ∀ x ∈ E₀, x ^ 3 = 1) (hcard : Nat.card E₀ = 3 ^ 2) (hn : ¬ NormalizesRNative .F4 K E₀) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (ringChar K ^ n) = 1} = ⊤ :=
  f4ThreeUniNative_of_three_le K (orthU3_three_le_card hK2) hnd E₀ hexp hcard hn

theorem uniSeitzPlanes_F4_inner_three :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧ IsF4Index d.1 ∧
      d.1.characteristic ≠ 2 ∧ ¬ NormalizesRSubgroup d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, rfl, ⟨q, hq⟩, hch, hn⟩
  obtain rfl : d = .F4 q := hq
  obtain ⟨K, _, _, hKq, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
  have hring : ringChar K = q.p := ringChar.eq K q.p
  have hq3 : 3 ≠ q.p := fun h => hpd (h.trans (LieTypeIndex.characteristic_F4 q).symm)
  have hnd : ¬ 3 ∣ Nat.card K := by
    rw [hKq, PrimePower.card_def]
    intro hd
    exact hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1
      (Nat.prime_three.dvd_of_dvd_pow hd))
  have hK2 : ringChar K ≠ 2 := by
    rw [hring]
    intro h
    exact hch (by rw [LieTypeIndex.characteristic_F4]; exact h)
  have h := uniPlaneGen_of_native_uniClosure (p := 3) (r := ringChar K) e
    (conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot center_adjointGroup_eq_bot))
    (fun E₀ h1 h2 h3 => f4ThreeUniNative K hK2 hnd E₀ h1 h2
      (fun ⟨R, hR1, hRp, hRn⟩ => h3 ⟨R, hR1, hRp, fun g hg =>
        (map_conj_eq_iff_mem_normalizer R g).2 (hRn hg)⟩))
    hE hc hin ?_
  · rw [hring] at h
    simpa using h
  · rintro ⟨R, hR1, hRp, hRn⟩
    refine hn ⟨R, hR1, ?_, hRn⟩
    show IsPGroup (LieTypeIndex.F4 q).characteristic R
    rw [LieTypeIndex.characteristic_F4, ← hring]
    exact hRp

end F4Three

section E6Three

open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.RankThree.E6 CFSG.HardMathSupport.Lang.AnisoE6 CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TauCeti

set_option linter.unusedSectionVars false

theorem xE_pow_ringChar (τ : Tag) (K : Type) [Field K] (i : Fin τ.rank) (c : K) :
    xE τ K i c ^ ringChar K = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one]
  show xOp τ K i c ^ ringChar K = 1
  rw [xOp_pow_eq, ringChar.Nat.cast_ringChar, zero_mul, xOp_zero]

theorem yE_pow_ringChar (τ : Tag) (K : Type) [Field K] (i : Fin τ.rank) (c : K) :
    yE τ K i c ^ ringChar K = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one]
  show yOp τ K i c ^ ringChar K = 1
  rw [yOp_pow_eq, ringChar.Nat.cast_ringChar, zero_mul, yOp_zero]

theorem e6UniClose_one_of_card (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 1)
    (E₃ : Subgroup (adjointGroup .F4 K)) (hexp : ∀ x ∈ E₃, x ^ 3 = 1) (hcard : Nat.card E₃ = 3 ^ 2)
    (hnF : ¬ NormalizesRNative .F4 K E₃) :
    Subgroup.closure {k : adjointGroup .E6 K | ∃ x ∈ E₃.map (embE6F4 K), x ≠ 1 ∧ Commute k x ∧
      ∃ n : ℕ, k ^ (ringChar K ^ n) = 1} = ⊤ := by
  have hι := embE6F4_injective K
  set H := Subgroup.closure {k : adjointGroup .E6 K | ∃ x ∈ E₃.map (embE6F4 K), x ≠ 1 ∧ Commute k x ∧
      ∃ n : ℕ, k ^ (ringChar K ^ n) = 1} with hH
  have hnd : ¬ 3 ∣ Nat.card K := by omega
  have h3 : 3 ≤ Nat.card K := by
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hrange : (embE6F4 K).range ≤ H :=
    map_le_uniClosure (embE6F4 K) hι E₃ (f4ThreeUniNative_of_three_le K h3 hnd E₃ hexp hcard hnF)
  obtain ⟨ω, hω⟩ := exists_units_orderOf_three K hK
  obtain ⟨D, hD⟩ := hReg_of_NR langPlaneKillsRoot_F4 K hK E₃ hexp hcard hnF
  obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ E₃, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hE : E₃ = ⊥ := (Subgroup.eq_bot_iff_forall E₃).2 hcon
    rw [hE, Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨g, hg⟩ := f4PureSplit_holds K hK ω hω E₃ hexp hcard D hD x hxE hx1
  have hxt : embE6F4 K x = (embE6F4 K g)⁻¹ * embE6F4 K (zSplit K ω) * embE6F4 K g := by
    have hx' : x = g⁻¹ * zSplit K ω * g := by rw [← hg]; group
    rw [hx', map_mul, map_mul, map_inv]
  have hιg : embE6F4 K g ∈ H := hrange ⟨g, rfl⟩
  have hιx1 : embE6F4 K x ≠ 1 := fun h => hx1 (hι (h.trans (map_one _).symm))
  have hιxE : embE6F4 K x ∈ E₃.map (embE6F4 K) := ⟨x, hxE, rfl⟩
  have hroot : ∀ u : adjointGroup .E6 K, Commute (embE6F4 K (zSplit K ω)) u →
      u ^ ringChar K = 1 → u ∈ H := by
    intro u hu hur
    have hcomm : Commute ((embE6F4 K g)⁻¹ * u * embE6F4 K g) (embE6F4 K x) := by
      rw [hxt]
      have := hu.symm.conj ((embE6F4 K g)⁻¹)
      simpa [MulAut.conj_apply, mul_assoc] using this
    have h1 : (embE6F4 K g)⁻¹ * u * embE6F4 K g ∈ H := by
      refine Subgroup.subset_closure ⟨embE6F4 K x, hιxE, hιx1, hcomm, 1, ?_⟩
      rw [pow_one, show (embE6F4 K g)⁻¹ * u * embE6F4 K g = MulAut.conj (embE6F4 K g)⁻¹ u by
        simp [MulAut.conj_apply], ← map_pow, hur, map_one]
    have h2 : u = embE6F4 K g * ((embE6F4 K g)⁻¹ * u * embE6F4 K g) * (embE6F4 K g)⁻¹ := by group
    rw [h2]
    exact mul_mem (mul_mem hιg h1) (inv_mem hιg)
  apply eq_top_of_simpleRootOps_gen
  intro i c
  by_cases hi : i = e6Index 3
  · subst hi
    have h4 := xE_node4_mem_fixE6 K c
    rw [← range_embE6F4] at h4
    exact ⟨hrange h4.1, hrange h4.2⟩
  · obtain ⟨hxc, hyc⟩ := hCent_proved K hK ω hω i hi c
    exact ⟨hroot _ hxc (xE_pow_ringChar _ _ _ _), hroot _ hyc (yE_pow_ringChar _ _ _ _)⟩

theorem e6UniClose_one (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 1) (hK2 : ringChar K ≠ 2)
    (E₃ : Subgroup (adjointGroup .F4 K)) (hexp : ∀ x ∈ E₃, x ^ 3 = 1) (hcard : Nat.card E₃ = 3 ^ 2)
    (hnF : ¬ NormalizesRNative .F4 K E₃) :
    Subgroup.closure {k : adjointGroup .E6 K | ∃ x ∈ E₃.map (embE6F4 K), x ≠ 1 ∧ Commute k x ∧
      ∃ n : ℕ, k ^ (ringChar K ^ n) = 1} = ⊤ :=
  e6UniClose_one_of_card K hK E₃ hexp hcard hnF

theorem frameIn_e6Six_le_closure (K : Type) [Field K] [Finite K] (h3 : 3 ≤ Nat.card K)
    (hK2 : ringChar K ≠ 2) (hK3 : ringChar K ≠ 3) (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) :
    frameIn (TwClass.e6Six.X₁ D ⊔ TwClass.e6Six.X₂ D) ≤
      Subgroup.closure {x | x ∈ frameIn (TwClass.e6Six.X₁ D ⊔ TwClass.e6Six.X₂ D) ∧
        ∃ n : ℕ, x ^ (ringChar K ^ n) = 1} := by
  classical
  refine subgroupOf_le_closure_of_le (e6Frame_le K D) ?_
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hr : ringChar K ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self _ n.ne_zero
  have hr5 : 5 ≤ ringChar K := by
    have := hℓ.two_le
    rcases (by omega : ringChar K = 2 ∨ ringChar K = 3 ∨ ringChar K = 4 ∨ 5 ≤ ringChar K) with
      h | h | h | h
    · exact absurd h hK2
    · exact absurd h hK3
    · exact absurd (h ▸ hℓ) (by norm_num)
    · exact h
  have : Finite (ModGL TwClass.e6Six.tag K) := finite_modGL
  have hq := twQuasi TwClass.e6Six K (show TwClass.e6Six.minQ ≤ Nat.card K from h3) D
  obtain ⟨hc₁, -⟩ := TwCardAux.e6Six_X₁ K h3 D
  have hd₁ : ringChar K ∣ Nat.card ↥(TwClass.e6Six.X₁ D) := by
    rw [hc₁]
    exact dvd_mul_of_dvd_left (dvd_pow hr (by norm_num)) _
  have hd₂ : ringChar K ∣ Nat.card ↥(TwClass.e6Six.X₂ D) := by
    have := TwCardAux.e6Six_X₂_dvd K D hℓ hr5 (k := 1)
      (by rw [pow_one]; exact dvd_mul_of_dvd_left (dvd_pow hr (by norm_num)) _)
    simpa using this
  have h₁ := le_closure_pow_of_quasisimple (r := ringChar K) hq.1 hd₁
  have h₂ := le_closure_pow_of_quasisimple (r := ringChar K) hq.2 hd₂
  refine sup_le (h₁.trans (Subgroup.closure_mono fun x ⟨hx, k, hk⟩ =>
    ⟨Subgroup.mem_sup_left hx, k, hk⟩)) (h₂.trans (Subgroup.closure_mono fun x ⟨hx, k, hk⟩ =>
    ⟨Subgroup.mem_sup_right hx, k, hk⟩))

theorem e6UniFrame_two (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 2) (hK2 : ringChar K ≠ 2)
    (E₃ : Subgroup (adjointGroup .F4 K)) (hexp : ∀ x ∈ E₃, x ^ 3 = 1) (hcard : Nat.card E₃ = 3 ^ 2)
    (hnF : ¬ NormalizesRNative .F4 K E₃) :
    ∃ e ∈ E₃, e ≠ 1 ∧ ∃ X : Subgroup (adjointGroup .E6 K),
      X ≤ Subgroup.centralizer ({embE6F4 K e} : Set (adjointGroup .E6 K)) ∧
      (∀ H : Subgroup (adjointGroup .E6 K), X ≤ H →
        ¬ H ≤ Subgroup.normalizer (X : Set (adjointGroup .E6 K)) → H = ⊤) ∧
      ¬ (fixE6 K ≤ Subgroup.normalizer (X : Set (adjointGroup .E6 K))) ∧
      X ≤ Subgroup.closure {x | x ∈ X ∧ ∃ n : ℕ, x ^ (ringChar K ^ n) = 1} := by
  have hnd : ¬ 3 ∣ Nat.card K := by omega
  have h3 : 3 ≤ Nat.card K := orthU3_three_le_card hK2
  have hK3 : ringChar K ≠ 3 := by
    intro h
    apply hnd
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
    rw [Nat.card_eq_fintype_card, hn, h]
    exact dvd_pow_self 3 n.ne_zero
  have hT : E6TwistedTransport := e6TwistedTransport_of_facts e6TransportLevi_holds
    e6TransportFrob_holds e6TransportBase_holds e6TransportTits_holds e6TransportSplit_holds
  obtain ⟨P, hreg⟩ := hReg2_of_NR langPlaneKillsRoot_F4 K hK E₃ hexp hcard hnF
  obtain ⟨x, hx⟩ : ∃ x : E₃, x ≠ 1 := by
    by_contra hcon
    simp only [ne_eq, not_exists, not_not] at hcon
    have hsub : Subsingleton E₃ := ⟨fun a b => by rw [hcon a, hcon b]⟩
    have h1 : Nat.card E₃ = 1 := Nat.card_eq_one_iff_unique.2 ⟨hsub, ⟨1⟩⟩
    rw [hcard] at h1
    norm_num at h1
  have he : (x : adjointGroup .F4 K) ∈ E₃ := x.2
  have he1 : (x : adjointGroup .F4 K) ≠ 1 := fun h => hx (Subtype.ext h)
  obtain ⟨D₁⟩ := exists_langLevi TwClass.f4Six.tag K TwClass.f4Six.w (TwClass.w_theta TwClass.f4Six)
  obtain ⟨ω, hω⟩ := exists_cube_root_langLevi K hnd D₁
  obtain ⟨z, hz1, hzbc⟩ := f4_twisted_element K hK h3 D₁ ω hω
  obtain ⟨g, hg⟩ := f4PureTwisted_holds K hK h3 D₁ ω hω z hzbc E₃ hexp hcard P hreg _ he he1
  obtain ⟨D₆, ω₆, hω₆, hbc⟩ := hT K hK h3 D₁ ω hω z hzbc
  have hC' := e6FrameCentral_holds K h3 D₆ ω₆ hω₆
    ((embE6F4 K z : adjointGroup .E6 K) : ModGL Tag.E6 K) hbc
  have hcent := e6Frame_centralizes K D₆ (embE6F4 K z) hC'
  haveI hsimpleF4 : IsSimpleGroup (adjointGroup .F4 K) :=
    CFSG.LieType.SeitzGeneration.ExcOuterLeOne.isSimpleGroup_adjointGroup_of_type
      (τ := Tag.F4) (K := K) (Or.inr (Or.inr (Or.inr rfl)))
  haveI hsimpleF : IsSimpleGroup ↥(fixE6 K) := MulEquiv.isSimpleGroup (isoE6F4 K).symm
  have hnc : ∃ a b : ↥(fixE6 K), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := (opposite_simple_root_noncommutativity Tag.F4 K).2.2.1
    refine ⟨isoE6F4 K a, isoE6F4 K b, fun h => hab ?_⟩
    apply (isoE6F4 K).injective
    simpa [map_mul] using h
  have hιzF : embE6F4 K z ∈ fixE6 K := by
    rw [← range_embE6F4 K]
    exact MonoidHom.mem_range.2 ⟨z, rfl⟩
  have hιz1 : embE6F4 K z ≠ 1 := fun h => hz1 (embE6F4_injective K (h.trans (map_one _).symm))
  have hnotX₀ : ¬ fixE6 K ≤ Subgroup.normalizer
      ((frameIn (TwClass.e6Six.X₁ D₆ ⊔ TwClass.e6Six.X₂ D₆) :
        Subgroup (adjointGroup TwClass.e6Six.tag K)) : Set (adjointGroup TwClass.e6Six.tag K)) :=
    not_le_normalizer_of_simple_centralizer (F := fixE6 K) hnc _ hιzF hιz1 hcent
      (e6Frame_normalizerSolvable K h3 D₆)
  have hxz : (x : adjointGroup .F4 K) = g⁻¹ * (z : adjointGroup .F4 K) * g := by
    rw [← hg]
    group
  have hkF : embE6F4 K g⁻¹ ∈ fixE6 K := by
    rw [← range_embE6F4 K]
    exact MonoidHom.mem_range.2 ⟨g⁻¹, rfl⟩
  have hιe : embE6F4 K (x : adjointGroup .F4 K) =
      embE6F4 K g⁻¹ * embE6F4 K z * (embE6F4 K g⁻¹)⁻¹ := by
    rw [hxz]
    simp only [map_mul, map_inv, inv_inv]
  refine ⟨(x : adjointGroup .F4 K), he, he1,
    (frameIn (TwClass.e6Six.X₁ D₆ ⊔ TwClass.e6Six.X₂ D₆)).map (MulAut.conj (embE6F4 K g⁻¹)).toMonoidHom,
    ?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff, hιe]
    have hw : (embE6F4 K g⁻¹)⁻¹ * y * embE6F4 K g⁻¹ ∈
        frameIn (TwClass.e6Six.X₁ D₆ ⊔ TwClass.e6Six.X₂ D₆) := by
      have h0 := (Subgroup.mem_map_equiv (f := MulAut.conj (embE6F4 K g⁻¹))).1 hy
      rwa [MulAut.conj_symm_apply] at h0
    have hcw : (embE6F4 K g⁻¹)⁻¹ * y * embE6F4 K g⁻¹ * embE6F4 K z =
        embE6F4 K z * ((embE6F4 K g⁻¹)⁻¹ * y * embE6F4 K g⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hcent hw)
    calc y * (embE6F4 K g⁻¹ * embE6F4 K z * (embE6F4 K g⁻¹)⁻¹)
        = embE6F4 K g⁻¹ * ((embE6F4 K g⁻¹)⁻¹ * y * embE6F4 K g⁻¹ * embE6F4 K z) *
            (embE6F4 K g⁻¹)⁻¹ := by group
      _ = embE6F4 K g⁻¹ * (embE6F4 K z * ((embE6F4 K g⁻¹)⁻¹ * y * embE6F4 K g⁻¹)) *
            (embE6F4 K g⁻¹)⁻¹ := by rw [hcw]
      _ = embE6F4 K g⁻¹ * embE6F4 K z * (embE6F4 K g⁻¹)⁻¹ * y := by group
  · exact closing_map_conj _ _ (e6Frame_closing K h3 D₆)
  · intro hF
    exact hnotX₀ (normalizer_le_of_map_conj _ _ (fixE6 K) hkF hF)
  · exact map_le_closure_pow _ (frameIn_e6Six_le_closure K h3 hK2 hK3 D₆)

theorem e6UniClose_two (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 2) (hK2 : ringChar K ≠ 2)
    (E₃ : Subgroup (adjointGroup .F4 K)) (hexp : ∀ x ∈ E₃, x ^ 3 = 1) (hcard : Nat.card E₃ = 3 ^ 2)
    (hnF : ¬ NormalizesRNative .F4 K E₃) :
    Subgroup.closure {k : adjointGroup .E6 K | ∃ x ∈ E₃.map (embE6F4 K), x ≠ 1 ∧ Commute k x ∧
      ∃ n : ℕ, k ^ (ringChar K ^ n) = 1} = ⊤ := by
  have hι := embE6F4_injective K
  have hnd : ¬ 3 ∣ Nat.card K := by omega
  have hrange : (embE6F4 K).range ≤ _ :=
    map_le_uniClosure (embE6F4 K) hι E₃ (f4ThreeUniNative K hK2 hnd E₃ hexp hcard hnF)
  obtain ⟨e, he, he1, X, hX, hclose, hnorm, hXr⟩ := e6UniFrame_two K hK hK2 E₃ hexp hcard hnF
  have hιe1 : embE6F4 K e ≠ 1 := fun h => he1 (hι (h.trans (map_one _).symm))
  refine hclose _ (hXr.trans ((Subgroup.closure_le _).2 fun k ⟨hk, n, hn⟩ =>
    Subgroup.subset_closure ⟨embE6F4 K e, ⟨e, he, rfl⟩, hιe1,
      (Subgroup.mem_centralizer_singleton_iff.1 (hX hk)), n, hn⟩)) fun hN => hnorm ?_
  rw [← range_embE6F4]
  exact hrange.trans hN

theorem e6ThreeUniNative (K : Type) [Field K] [Finite K] (hK2 : ringChar K ≠ 2) (hnd : ¬ 3 ∣ Nat.card K)
    (E₀ : Subgroup (adjointGroup .E6 K)) (hexp : ∀ x ∈ E₀, x ^ 3 = 1) (hcard : Nat.card E₀ = 3 ^ 2)
    (hn : ¬ NormalizesRNative .E6 K E₀) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (ringChar K ^ n) = 1} = ⊤ := by
  have hres : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2 := by omega
  obtain ⟨g, hg⟩ : ∃ g : adjointGroup .E6 K, ∀ x ∈ E₀, g * x * g⁻¹ ∈ (embE6F4 K).range := by
    rcases hres with hres | hres
    · exact conjOne_of_innerIsotropic (e6InnerIsotropic_of_frame
        (ExcWideThree.e6HeisFrameNormalizesR_of_fixedElt (ExcWideThree.e6HeisFrameFixedElt_of_classD
            ExcWideThree.e6HeisFrameFixedEltD_holds)))
        K hres E₀ hexp hcard hn
    · exact conj_into_fixE6_two K hres hexp
  set E₁ : Subgroup (adjointGroup .E6 K) := E₀.map (MulAut.conj g).toMonoidHom with hE₁def
  have hE₁le : E₁ ≤ (embE6F4 K).range := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  have hι := embE6F4_injective K
  set E₃ : Subgroup (adjointGroup .F4 K) := E₁.comap (embE6F4 K) with hE₃def
  have hE₃map : E₃.map (embE6F4 K) = E₁ := Subgroup.map_comap_eq_self hE₁le
  have hcardE₁ : Nat.card E₁ = 3 ^ 2 := by
    rw [hE₁def, Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  have hcardE₃ : Nat.card E₃ = 3 ^ 2 := by
    have h1 : Nat.card (E₃.map (embE6F4 K)) = Nat.card E₃ := Subgroup.card_map_of_injective hι
    rw [← h1, hE₃map, hcardE₁]
  have hexp₃ : ∀ x ∈ E₃, x ^ 3 = 1 := by
    intro x hx
    have hmem : (embE6F4 K) x ∈ E₀.map (MulAut.conj g).toMonoidHom := hx
    obtain ⟨y, hy, hyx⟩ := hmem
    apply hι
    rw [map_pow, map_one, ← hyx, ← map_pow, hexp y hy, map_one]
  have hnF : ¬ NormalizesRNative .F4 K E₃ :=
    not_normalizesRIn_comap_of_map (embE6F4 K) hι g hn E₃ hE₃map
  refine uniClosure_eq_top_of_conj g ?_
  rw [← hE₁def, ← hE₃map]
  rcases hres with hres | hres
  · exact e6UniClose_one K hres hK2 E₃ hexp₃ hcardE₃ hnF
  · exact e6UniClose_two K hres hK2 E₃ hexp₃ hcardE₃ hnF

theorem uniSeitzPlanes_E6_inner_three :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧ IsE6Index d.1 ∧
      d.1.characteristic ≠ 2 ∧ ¬ NormalizesRSubgroup d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, rfl, ⟨q, hq⟩, hch, hn⟩
  obtain rfl : d = .E6 q := hq
  obtain ⟨K, _, _, hKq, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  have hring : ringChar K = q.p := ringChar.eq K q.p
  have hq3 : 3 ≠ q.p := fun h => hpd (h.trans (LieTypeIndex.characteristic_E6 q).symm)
  have hnd : ¬ 3 ∣ Nat.card K := by
    rw [hKq, PrimePower.card_def]
    intro hd
    exact hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1
      (Nat.prime_three.dvd_of_dvd_pow hd))
  have hK2 : ringChar K ≠ 2 := by
    rw [hring]
    intro h
    exact hch (by rw [LieTypeIndex.characteristic_E6]; exact h)
  have h := uniPlaneGen_of_native_uniClosure (p := 3) (r := ringChar K) e
    (conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot center_adjointGroup_eq_bot))
    (fun E₀ h1 h2 h3 => e6ThreeUniNative K hK2 hnd E₀ h1 h2
      (fun ⟨R, hR1, hRp, hRn⟩ => h3 ⟨R, hR1, hRp, fun g hg =>
        (map_conj_eq_iff_mem_normalizer R g).2 (hRn hg)⟩))
    hE hc hin ?_
  · rw [hring] at h
    simpa using h
  · rintro ⟨R, hR1, hRp, hRn⟩
    refine hn ⟨R, hR1, ?_, hRn⟩
    show IsPGroup (LieTypeIndex.E6 q).characteristic R
    rw [LieTypeIndex.characteristic_E6, ← hring]
    exact hRp

end E6Three

section TwE6ThreeOne

open CFSG.HardMathSupport.Lang.AnisoE6 CFSG.RankThree.E6 TauCeti

set_option linter.unusedSectionVars false

theorem orbitXY_pow_eq_one {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ.toRingHom a) :
    (∃ n : ℕ, (⟨orbitX TwistTag.E6 K σ.toRingHom a c,
      graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
        (orbitX_mem_graphFixedPosUnipotent _ _ _ _)⟩ : twistedE6RootGroup K σ) ^ (ringChar K ^ n) = 1) ∧
    (∃ n : ℕ, (⟨orbitY TwistTag.E6 K σ.toRingHom a c,
      graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _
        (orbitY_mem_graphFixedNegUnipotent _ _ _ _)⟩ : twistedE6RootGroup K σ) ^ (ringChar K ^ n) = 1) := by
  have hU := (positive_root_triangularity.{0, 0} TwistTag.E6.tag).2 K (ringChar K)
  have hXU : graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom ≤ posUnipotent TwistTag.E6.tag K :=
    inf_le_left
  have hYU : graphFixedNegUnipotent TwistTag.E6 K σ.toRingHom ≤ negUnipotent TwistTag.E6.tag K :=
    inf_le_left
  constructor
  · obtain ⟨n, hn⟩ := hU.2.1 ⟨_, hXU (orbitX_mem_graphFixedPosUnipotent TwistTag.E6 σ.toRingHom a c)⟩
    refine ⟨n, Subtype.ext ?_⟩
    have h := congrArg Subtype.val hn
    simpa using h
  · obtain ⟨n, hn⟩ := hU.2.2.2 ⟨_, hYU (orbitY_mem_graphFixedNegUnipotent TwistTag.E6 σ.toRingHom a c)⟩
    refine ⟨n, Subtype.ext ?_⟩
    have h := congrArg Subtype.val hn
    simpa using h

theorem twE6UniClose_one {k K : Type} [Field k] [Finite k] [Field K] [Finite K] [Algebra k K]
    (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)
    (hkchar : ringChar k = ringChar K) (hq : Nat.card k % 3 = 1) (hk2 : ringChar k ≠ 2)
    (E₃ : Subgroup (adjointGroup .F4 k)) (hexp : ∀ x ∈ E₃, x ^ 3 = 1) (hcard : Nat.card E₃ = 3 ^ 2)
    (hnF : ¬ NormalizesRNative .F4 k E₃) (ω : kˣ) (hω : orderOf ω = 3) (g₁ : adjointGroup .F4 k)
    (hz : zSplit k ω ∈ E₃.map (MulAut.conj g₁).toMonoidHom) :
    Subgroup.closure {x : twistedE6RootGroup K σ | ∃ y ∈ (E₃.map (MulAut.conj g₁).toMonoidHom).map
        ((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom), y ≠ 1 ∧ Commute x y ∧
      ∃ n : ℕ, x ^ (ringChar K ^ n) = 1} = ⊤ := by
  classical
  set ι : adjointGroup .F4 k →* twistedE6RootGroup K σ :=
    (phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom with hιdef
  have hι : Function.Injective ι :=
    (phiG_injective σ hfix).comp (e6FixedF4EquivAll k).symm.injective
  set H := Subgroup.closure {x : twistedE6RootGroup K σ | ∃ y ∈ (E₃.map (MulAut.conj g₁).toMonoidHom).map ι,
      y ≠ 1 ∧ Commute x y ∧ ∃ n : ℕ, x ^ (ringChar K ^ n) = 1} with hH
  have hnd : ¬ 3 ∣ Nat.card k := by omega
  have hF := f4ThreeUniNative k hk2 hnd E₃ hexp hcard hnF
  rw [hkchar] at hF
  have hrange : ι.range ≤ H := by
    have h1 := map_le_uniClosure (ι.comp (MulAut.conj g₁).toMonoidHom)
      (hι.comp (MulAut.conj g₁).injective) E₃ hF
    rw [← Subgroup.map_map] at h1
    refine le_trans ?_ h1
    rintro _ ⟨y, rfl⟩
    exact ⟨g₁⁻¹ * y * g₁, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hφH : ∀ x, phiG σ hfix x ∈ H := fun x =>
    hrange ⟨e6FixedF4EquivAll k x, by simp [hιdef]⟩
  have hzne : zSplit k ω ≠ 1 := (f4SplitFrame_of k hq ω hω).1
  have hz' : ι (zSplit k ω) ∈ (E₃.map (MulAut.conj g₁).toMonoidHom).map ι := ⟨_, hz, rfl⟩
  have hιz1 : ι (zSplit k ω) ≠ 1 := fun h => hzne (hι (h.trans (map_one ι).symm))
  obtain ⟨z, hzz, hgood⟩ := zSplit_twE6_good k K ω
  have hιz : ι (zSplit k ω) = phiG σ hfix z := by
    rw [← hzz, hιdef]
    simp
  have hcH : ∀ y : twistedE6RootGroup K σ,
      Commute (y : ModGL TwistTag.E6.tag K) (phiG σ hfix z : ModGL TwistTag.E6.tag K) →
      (∃ n : ℕ, y ^ (ringChar K ^ n) = 1) → y ∈ H := by
    rintro y hy ⟨n, hn⟩
    refine Subgroup.subset_closure ⟨ι (zSplit k ω), hz', hιz1, ?_, n, hn⟩
    rw [hιz]
    exact Subtype.ext hy.eq
  have hXG : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ.toRingHom a),
      (orbitX TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈ twistedE6RootGroup K σ :=
    fun a c => graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ (orbitX_mem_graphFixedPosUnipotent _ _ _ _)
  have hYG : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ.toRingHom a),
      (orbitY TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈ twistedE6RootGroup K σ :=
    fun a c => graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _ (orbitY_mem_graphFixedNegUnipotent _ _ _ _)
  have hmemX : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ.toRingHom a),
      (⟨orbitX TwistTag.E6 K σ.toRingHom a c, hXG a c⟩ : twistedE6RootGroup K σ) ∈ H ∧
      (⟨orbitY TwistTag.E6 K σ.toRingHom a c, hYG a c⟩ : twistedE6RootGroup K σ) ∈ H := by
    intro a c
    have hr := orbitXY_pow_eq_one σ a c
    obtain ⟨a, ha⟩ := a
    have ha4 : a < 4 := ha
    interval_cases a
    · have h := commute_orbitXY_short σ.toRingHom
        (e := (phiG σ hfix z : ModGL TwistTag.E6.tag K)) hgood ⟨0, ha⟩ (Or.inl rfl) c
      exact ⟨hcH _ h.1.symm hr.1, hcH _ h.2.symm hr.2⟩
    · have h := commute_orbitXY_short σ.toRingHom
        (e := (phiG σ hfix z : ModGL TwistTag.E6.tag K)) hgood ⟨1, ha⟩ (Or.inr rfl) c
      exact ⟨hcH _ h.1.symm hr.1, hcH _ h.2.symm hr.2⟩
    · have hc : σ.toRingHom (c : K) = c := by
        have := mem_orbitField.1 c.2
        rwa [card_orbit_two, pow_one] at this
      have hcc : (c : K) ^ Nat.card k = c := by
        rw [← hσ]
        exact hc
      obtain ⟨c', hc'⟩ := CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := k) hcc
      have hxm := xyUnit_mem_fixed_of_orbitWord_eq k ⟨1, by decide⟩ (e6Index 3) orbitWord_f4_one c'
      have hX : (⟨orbitX TwistTag.E6 K σ.toRingHom ⟨2, ha⟩ c, hXG _ c⟩ : twistedE6RootGroup K σ) =
          phiG σ hfix ⟨(xUnit Tag.E6 k (e6Index 3) c' : ModGL TwistTag.E6.tag k), hxm.1⟩ := by
        apply Subtype.ext
        change (orbitX TwistTag.E6 K σ.toRingHom ⟨2, ha⟩ c : ModGL TwistTag.E6.tag K) =
          baseChangeGL (algebraMap k K) (xUnit Tag.E6 k (e6Index 3) c' : ModGL TwistTag.E6.tag k)
        rw [baseChangeGL_xUnit, hc']
        exact coe_orbitX_two σ.toRingHom c
      have hY : (⟨orbitY TwistTag.E6 K σ.toRingHom ⟨2, ha⟩ c, hYG _ c⟩ : twistedE6RootGroup K σ) =
          phiG σ hfix ⟨(yUnit Tag.E6 k (e6Index 3) c' : ModGL TwistTag.E6.tag k), hxm.2⟩ := by
        apply Subtype.ext
        change (orbitY TwistTag.E6 K σ.toRingHom ⟨2, ha⟩ c : ModGL TwistTag.E6.tag K) =
          baseChangeGL (algebraMap k K) (yUnit Tag.E6 k (e6Index 3) c' : ModGL TwistTag.E6.tag k)
        rw [baseChangeGL_yUnit, hc']
        exact coe_orbitY_two σ.toRingHom c
      exact ⟨by rw [hX]; exact hφH _, by rw [hY]; exact hφH _⟩
    · have hc : σ.toRingHom (c : K) = c := by
        have := mem_orbitField.1 c.2
        rwa [card_orbit_three, pow_one] at this
      have hcc : (c : K) ^ Nat.card k = c := by
        rw [← hσ]
        exact hc
      obtain ⟨c', hc'⟩ := CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := k) hcc
      have hxm := xyUnit_mem_fixed_of_orbitWord_eq k ⟨0, by decide⟩ (e6Index 1) orbitWord_f4_zero c'
      have hX : (⟨orbitX TwistTag.E6 K σ.toRingHom ⟨3, ha⟩ c, hXG _ c⟩ : twistedE6RootGroup K σ) =
          phiG σ hfix ⟨(xUnit Tag.E6 k (e6Index 1) c' : ModGL TwistTag.E6.tag k), hxm.1⟩ := by
        apply Subtype.ext
        change (orbitX TwistTag.E6 K σ.toRingHom ⟨3, ha⟩ c : ModGL TwistTag.E6.tag K) =
          baseChangeGL (algebraMap k K) (xUnit Tag.E6 k (e6Index 1) c' : ModGL TwistTag.E6.tag k)
        rw [baseChangeGL_xUnit, hc']
        exact coe_orbitX_three σ.toRingHom c
      have hY : (⟨orbitY TwistTag.E6 K σ.toRingHom ⟨3, ha⟩ c, hYG _ c⟩ : twistedE6RootGroup K σ) =
          phiG σ hfix ⟨(yUnit Tag.E6 k (e6Index 1) c' : ModGL TwistTag.E6.tag k), hxm.2⟩ := by
        apply Subtype.ext
        change (orbitY TwistTag.E6 K σ.toRingHom ⟨3, ha⟩ c : ModGL TwistTag.E6.tag K) =
          baseChangeGL (algebraMap k K) (yUnit Tag.E6 k (e6Index 1) c' : ModGL TwistTag.E6.tag k)
        rw [baseChangeGL_yUnit, hc']
        exact coe_orbitY_three σ.toRingHom c
      exact ⟨by rw [hX]; exact hφH _, by rw [hY]; exact hφH _⟩
  have hG : twistedE6RootGroup K σ ≤ H.map (twistedE6RootGroup K σ).subtype := by
    have hgen' := graphFixedRootGroup_eq_iSup_orbitRankOneGroup (t := TwistTag.E6)
      (σ := σ.toRingHom) σ.surjective
    refine (le_of_eq hgen').trans (iSup_le fun a => (Subgroup.closure_le _).2 ?_)
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨_, (hmemX a c).1, rfl⟩
    · exact ⟨_, (hmemX a c).2, rfl⟩
  refine (Subgroup.eq_top_iff' _).2 fun x => ?_
  obtain ⟨y, hy, hyx⟩ := hG x.2
  have : y = x := Subtype.ext hyx
  exact this ▸ hy

theorem twE6ThreeUniNative_one (q : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q) (hq : q % 3 = 1) (hK2 : ringChar K ≠ 2)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) (hexp : ∀ x ∈ E₀, x ^ 3 = 1)
    (hcard : Nat.card E₀ = 3 ^ 2) (hn : ¬ NormalizesRIn (ringChar K) E₀) :
    Subgroup.closure {x | ∃ y ∈ E₀, y ≠ 1 ∧ Commute x y ∧ ∃ n : ℕ, x ^ (ringChar K ^ n) = 1} = ⊤ := by
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hq2 : 2 ≤ q := by
    by_contra h
    push Not at h
    have : Nat.card K ≤ 1 := by
      rw [hK]
      interval_cases q <;> norm_num
    omega
  obtain ⟨k, hkF, hkfin, hkalg, hkq, hkchar, hfix⟩ := exists_fixed_subfield q K σ hK hσ hq2
  have hσk : ∀ c : K, σ c = c ^ Nat.card k := fun c => by rw [hkq]; exact hσ c
  have hK' : Nat.card K = (Nat.card k) ^ 2 := by rw [hkq]; exact hK
  have hq' : Nat.card k % 3 = 1 := by rw [hkq]; exact hq
  have hq2' : 2 ≤ Nat.card k := by rw [hkq]; exact hq2
  obtain ⟨g₀, hg₀⟩ := threeSubgroup_conj_into_F4 σ hσk hK' hfix hq' hq2' E₀ hexp
  set ι : adjointGroup .F4 k →* twistedE6RootGroup K σ :=
    (phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom with hιdef
  have hι : Function.Injective ι :=
    (phiG_injective σ hfix).comp (e6FixedF4EquivAll k).symm.injective
  set E₃ : Subgroup (adjointGroup .F4 k) := (E₀.map (MulAut.conj g₀).toMonoidHom).comap ι with hE₃def
  have hE₃ : E₃.map ι = E₀.map (MulAut.conj g₀).toMonoidHom := Subgroup.map_comap_eq_self hg₀
  have hexp₃ : ∀ x ∈ E₃, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hx)
    apply hι
    rw [map_pow, map_one, ← hyx, ← map_pow, hexp y hy, map_one]
  have hcardE₃ : Nat.card E₃ = 3 ^ 2 := by
    have h1 : Nat.card (E₃.map ι) = Nat.card E₃ := Subgroup.card_map_of_injective hι
    have h2 : Nat.card (E₀.map (MulAut.conj g₀).toMonoidHom) = Nat.card E₀ :=
      Subgroup.card_map_of_injective (MulAut.conj g₀).injective
    rw [← h1, hE₃, h2, hcard]
  have hn3 : ¬ NormalizesRIn (ringChar k) E₃ := by
    rw [hkchar]
    exact not_normalizesRIn_of_map hn g₀ ι E₃ hι hE₃
  obtain ⟨ω, hω, g₁, hg₁⟩ :=
    exists_conj_zSplit_mem langPlaneKillsRoot_F4 f4PureSplit_holds k hq' E₃ hexp₃ hcardE₃ hn3
  have hk2 : ringChar k ≠ 2 := by
    rw [hkchar]
    exact hK2
  have hcl := twE6UniClose_one σ hσk hfix hkchar hq' hk2 E₃ hexp₃ hcardE₃ hn3 ω hω g₁ hg₁
  have hE : (E₃.map (MulAut.conj g₁).toMonoidHom).map ι =
      E₀.map (MulAut.conj (ι g₁ * g₀)).toMonoidHom := by
    rw [Subgroup.map_map]
    have hc1 : ι.comp (MulAut.conj g₁).toMonoidHom = ((MulAut.conj (ι g₁)).toMonoidHom).comp ι := by
      ext x
      simp [MulAut.conj_apply, map_mul, map_inv]
    rw [hc1, ← Subgroup.map_map, hE₃, Subgroup.map_map]
    have hc2 : ((MulAut.conj (ι g₁)).toMonoidHom).comp (MulAut.conj g₀).toMonoidHom =
        (MulAut.conj (ι g₁ * g₀)).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hc2]
  refine uniClosure_eq_top_of_conj (ι g₁ * g₀) ?_
  rw [← hE]
  exact hcl

theorem uniSeitzPlanes_twE6_inner_three_one :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧
      (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ q.card % 3 = 1) ∧
      d.1.characteristic ≠ 2 ∧ ¬ NormalizesRSubgroup d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, rfl, ⟨q, hq, hmod⟩, hch, hn⟩
  obtain rfl : d = .twistedE6 q := hq
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have hchK : CharP K q.p := charP_of_card_eq_prime_pow (f := q.exponent * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have hring : ringChar K = q.p := ringChar.eq K q.p
  have hK2 : ringChar K ≠ 2 := by
    rw [hring]
    intro h
    exact hch (by rw [LieTypeIndex.characteristic_twistedE6]; exact h)
  have h := uniPlaneGen_of_native_uniClosure (p := 3) (r := ringChar K) e
    (conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot
      (CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot σ.surjective)))
    (fun E₀ h1 h2 h3 => twE6ThreeUniNative_one _ K σ hK hσ
      (by rw [← TauCeti.PrimePower.card_def]; exact hmod) hK2 E₀ h1 h2
      (fun ⟨R, hR1, hRp, hRn⟩ => h3 ⟨R, hR1, hRp, fun g hg =>
        (map_conj_eq_iff_mem_normalizer R g).2 (hRn hg)⟩))
    hE hc hin ?_
  · rw [hring] at h
    simpa using h
  · rintro ⟨R, hR1, hRp, hRn⟩
    refine hn ⟨R, hR1, ?_, hRn⟩
    show IsPGroup (LieTypeIndex.twistedE6 q).characteristic R
    rw [LieTypeIndex.characteristic_twistedE6, ← hring]
    exact hRp

end TwE6ThreeOne

section F4TwoUni

open CFSG.LieType.SeitzGeneration.ExcHigh CFSG.HardMathSupport.Lang.AnisoF4 CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ComponentClassification.CatLeafProof TauCeti

set_option linter.unusedSectionVars false

theorem iSup_b4Chain_le_uniClosure_two {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (E : Subgroup (adjointGroup .F4 K)) (hE : E ≤ ⨆ k, b4Chain K k) (hEp : ∀ x ∈ E, x ^ p = 1)
    (hEc : Nat.card E = p ^ 2) :
    ⨆ k, b4Chain K k ≤ Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ Commute g x ∧
      ∃ m : ℕ, g ^ (ringChar K ^ m) = 1} := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hℓ2 : ringChar K ≠ 2 := by
    intro h
    apply h2
    have : CharP K 2 := h ▸ ringChar.charP K
    exact CharTwo.two_eq_zero
  obtain ⟨Ψ, hΨker, hΨrange, -, -⟩ := exists_psi_B4_F4_frame hℓ hℓ2 hK h2
  have hn3 : 3 ≤ 4 := by norm_num
  have : Nonempty (Fin 4 ⊕ Fin 4 ⊕ Unit) := ⟨Sum.inr (Sum.inr ())⟩
  have : Finite (spinGroup (quadOdd 4 K)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadOdd (n := 4) h2 hn3
  set π := spinToStatedProj (quadOdd 4 K) (range_spinMatrix_quadOdd h2 hn3) with hπdef
  have hpq1 : ¬ p ∣ Nat.card K - 1 := by
    intro hd
    have hq1 : 1 ≤ Nat.card K := Nat.card_pos
    have h3 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq hd
    have e : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [e] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hcen : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadOdd 4 K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadOdd 4 K) (range_spinMatrix_quadOdd h2 hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadOdd_iff h2 x).mp hx)) hp2 hpq1
  have hrq1 : ¬ ringChar K ∣ Nat.card K - 1 := by
    intro hd
    have h1 : ringChar K ∣ Nat.card K := by rw [hK]; exact dvd_pow_self _ n.ne_zero
    have hq1 : 1 ≤ Nat.card K := Nat.card_pos
    have h3 : ringChar K ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub h1 hd
    rw [show Nat.card K - (Nat.card K - 1) = 1 by omega] at h3
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp h3)
  have hrcen : ¬ ringChar K ∣ Nat.card (Subgroup.center (spinGroup (quadOdd 4 K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadOdd 4 K) (range_spinMatrix_quadOdd h2 hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadOdd_iff h2 x).mp hx)) hℓ2 hrq1
  have hπcop : ¬ p ∣ Nat.card π.ker := by
    intro hd
    apply hcen
    have : Nat.card π.ker ∣ Nat.card (Subgroup.center (spinGroup (quadOdd 4 K))) := by
      rw [hZ]
    exact hd.trans this
  have hrcop : (Nat.card π.ker).Coprime (ringChar K) := by
    have h' : ¬ ringChar K ∣ Nat.card π.ker := by
      intro hd
      apply hrcen
      have : Nat.card π.ker ∣ Nat.card (Subgroup.center (spinGroup (quadOdd 4 K))) := by
        rw [hZ]
      exact hd.trans this
    exact ((Nat.Prime.coprime_iff_not_dvd hℓ).2 h').symm
  have hΨcop : ¬ p ∣ Nat.card Ψ.ker := by
    intro hd
    apply hcen
    exact hd.trans (Subgroup.card_dvd_of_le hΨker)
  have hperf : ⁅(⊤ : Subgroup (spinGroup (quadOdd 4 K))), ⊤⁆ = ⊤ :=
    (isPerfect_spinGroup_quadOdd h2 hn3).commutator_eq_top
  have hpK : ¬ p ∣ Nat.card K := by
    intro hd
    have h1 : p ∣ 1 := (Nat.dvd_add_right hd).mp hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    let _ : CommGroup E := IsPGroup.commGroupOfCardEqPrimeSq hEc
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hE_le : E ≤ Ψ.range := hΨrange ▸ hE
  set Ψ' : spinGroup (quadOdd 4 K) →* Ψ.range := Ψ.rangeRestrict with hΨ'
  have hΨ'surj : Function.Surjective Ψ' := Ψ.rangeRestrict_surjective
  have hΨ'ker : Ψ'.ker = Ψ.ker := Ψ.ker_rangeRestrict
  set E1 : Subgroup Ψ.range := E.subgroupOf Ψ.range with hE1def
  have hE1 : IsElemAbelian p E1 :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (hEcomm a.1.1 a.2 b.1.1 b.2)),
     fun x hx => Subtype.ext (hEp x hx)⟩
  obtain ⟨E', hmapE', hdisE', hE'ea⟩ :=
    exists_lift_elemAbelian_of_coprime_ker Ψ' hΨ'surj (hΨ'ker ▸ hΨcop) hE1
  have hcardE1 : Nat.card E1 = p ^ 2 := by
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le).toEquiv
  have hcardE' : Nat.card E' = p ^ 2 := by
    rw [← CFSG.LieType.SeitzGeneration.ExcHigh.card_map_eq_of_disjoint_ker Ψ' hdisE', hmapE',
      hcardE1]
  set Ebar : Subgroup _ := E'.map π with hEbar
  have hEbarea : IsElemAbelian p Ebar :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE'ea π
  have hcardEbar : Nat.card Ebar = p ^ 2 := by
    rw [hEbar, CFSG.LieType.SeitzGeneration.ExcHigh.card_map_eq_of_disjoint_ker π
      (disjoint_ker_of_exponent π hπcop hE'ea.2), hcardE']
  have hmodel := orthU3_oddPlanes (r := 4) (by norm_num) hp hp2 hpK h2 Ebar hEbarea hcardEbar
  have hG := uniClosure_eq_top_of_quotient π hπsurj hZ.le hπcop hrcop hperf E' hE'ea.2 hmodel
  have hdisΨ : Disjoint E' Ψ.ker := hΨ'ker ▸ hdisE'
  rw [← hΨrange, MonoidHom.range_eq_map, ← hG, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨g, ⟨x, hx, hx1, hg, hgr⟩, rfl⟩
  refine ⟨Ψ x, ?_, ?_, ?_, 1, ?_⟩
  · have : Ψ' x ∈ E1 := hmapE' ▸ ⟨x, hx, rfl⟩
    exact this
  · intro h1
    exact hx1 (Subgroup.disjoint_def.mp hdisΨ hx (MonoidHom.mem_ker.mpr h1))
  · show Ψ g * Ψ x = Ψ x * Ψ g
    rw [← map_mul, ← map_mul]
    exact congrArg Ψ hg
  · rw [pow_one, ← map_pow, hgr, map_one]

theorem f4TwoUniNative (K : Type) [Field K] [Finite K] (h2 : (2 : K) ≠ 0) (p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1) (E₀ : Subgroup (adjointGroup .F4 K))
    (hE₀p : ∀ x ∈ E₀, x ^ p = 1) (hE₀c : Nat.card E₀ = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (ringChar K ^ m) = 1} = ⊤ :=
  uniClosure_eq_top_of_two_conj (p := p) (⨆ k, b4Chain K k) (f4FrameGroup K)
    (CFSG.LieType.Chevalley.weylElement .F4 K (f4Node 3)) f4FrameGroup_le_b4 f4FrameGroup_le_conj_b4
    (fun M hX hn => eq_top_of_b4Chain_le_of_conj_le M hX hn)
    (fun E hE hEp hEc => iSup_b4Chain_le_uniClosure_two h2 Fact.out hp5 hpq E hE hEp hEc) E₀ hE₀p
    hE₀c (f4TwoSylow K p hp5 hpq E₀ hE₀p hE₀c)

theorem uniSeitzPlanes_F4_inner_two :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧
      (∃ q : TauCeti.PrimePower, d.1 = .F4 q ∧ (p ∣ q.card - 1 ∨ p ∣ q.card + 1)) ∧
      d.1.characteristic ≠ 2 ∧ ¬ NormalizesRSubgroup d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, ⟨q, hq, hpq⟩, hch, hn⟩
  obtain rfl : d = .F4 q := hq
  haveI : Fact p.Prime := ⟨hp⟩
  rcases hpq with hpq | hpq
  · exact absurd (normalizesRSubgroup_F4_of_dvd_sub_one q hv hp hp5 hpq (IsPGroup.of_card hc) hin) hn
  obtain ⟨K, _, _, hKq, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
  have hring : ringChar K = q.p := ringChar.eq K q.p
  have hK2 : ringChar K ≠ 2 := by
    rw [hring]
    intro h
    exact hch (by rw [LieTypeIndex.characteristic_F4]; exact h)
  have hpqK : p ∣ Nat.card K + 1 := by rw [hKq]; exact hpq
  have h := uniPlaneGen_of_native_uniClosure (p := p) (r := ringChar K) e
    (conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot center_adjointGroup_eq_bot))
    (fun E₀ h1 h2 _ => f4TwoUniNative K (Ring.two_ne_zero hK2) p hp5 hpqK E₀ h1 h2)
    hE hc hin ?_
  · rw [hring] at h
    simpa using h
  · rintro ⟨R, hR1, hRp, hRn⟩
    refine hn ⟨R, hR1, ?_, hRn⟩
    show IsPGroup (LieTypeIndex.F4 q).characteristic R
    rw [LieTypeIndex.characteristic_F4, ← hring]
    exact hRp

end F4TwoUni

section E8TwoUni

open CFSG.LieType.SeitzGeneration.ExcHigh CFSG.HardMathSupport.Lang.AnisoF4
  CFSG.HardMathSupport.Lang.AnisoE8 CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.ComponentClassification.CatLeafProof TauCeti

set_option linter.unusedSectionVars false

theorem iSup_d8Chain_le_uniClosure_of_ne {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) (hpq1 : ¬ p ∣ Nat.card K - 1)
    (Ψ : spinGroup (CFSG.LieType.Universal.Spin.quadPlus 8 K) →* adjointGroup .E8 K)
    (hker : Ψ.ker ≤ Subgroup.center (spinGroup (CFSG.LieType.Universal.Spin.quadPlus 8 K)))
    (hrange : Ψ.range = ⨆ k, e8D8Chain K k)
    (E : Subgroup (adjointGroup .E8 K)) (hE : E ≤ ⨆ k, e8D8Chain K k)
    (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    ⨆ k, e8D8Chain K k ≤ Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ Commute g x ∧
      ∃ m : ℕ, g ^ (ringChar K ^ m) = 1} := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hn3 : 3 ≤ 8 := by norm_num
  have : Nonempty (Fin 8 ⊕ Fin 8) := ⟨Sum.inl 0⟩
  have : Finite (spinGroup (quadPlus 8 K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadPlus (n := 8) (K := K) hn3
  set π := spinToStatedProj (quadPlus 8 K) (range_spinMatrix_quadPlus hn3) with hπdef
  have hcen : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 8 K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadPlus 8 K) (range_spinMatrix_quadPlus hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hp2 hpq1
  have hrq1 : ¬ ringChar K ∣ Nat.card K - 1 := by
    intro hd
    have h1 : ringChar K ∣ Nat.card K := by rw [hK]; exact dvd_pow_self _ n.ne_zero
    have hq1 : 1 ≤ Nat.card K := Nat.card_pos
    have h3 : ringChar K ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub h1 hd
    rw [show Nat.card K - (Nat.card K - 1) = 1 by omega] at h3
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp h3)
  have hrcen : ¬ ringChar K ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 8 K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadPlus 8 K) (range_spinMatrix_quadPlus hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hK2 hrq1
  have hπcop : ¬ p ∣ Nat.card π.ker := by
    intro hd
    apply hcen
    have : Nat.card π.ker ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 8 K))) := by
      rw [hZ]
    exact hd.trans this
  have hrcop : (Nat.card π.ker).Coprime (ringChar K) := by
    have h' : ¬ ringChar K ∣ Nat.card π.ker := by
      intro hd
      apply hrcen
      have : Nat.card π.ker ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 8 K))) := by
        rw [hZ]
      exact hd.trans this
    exact ((Nat.Prime.coprime_iff_not_dvd hℓ).2 h').symm
  have hΨcop : ¬ p ∣ Nat.card Ψ.ker := by
    intro hd
    apply hcen
    exact hd.trans (Subgroup.card_dvd_of_le hker)
  have hperf : ⁅(⊤ : Subgroup (spinGroup (quadPlus 8 K))), ⊤⁆ = ⊤ :=
    (isPerfect_spinGroup_quadPlus hn3).commutator_eq_top
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    let _ : CommGroup E := IsPGroup.commGroupOfCardEqPrimeSq hEc
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hE_le : E ≤ Ψ.range := hrange ▸ hE
  set Ψ' : spinGroup (quadPlus 8 K) →* Ψ.range := Ψ.rangeRestrict with hΨ'
  have hΨ'surj : Function.Surjective Ψ' := Ψ.rangeRestrict_surjective
  have hΨ'ker : Ψ'.ker = Ψ.ker := Ψ.ker_rangeRestrict
  set E1 : Subgroup Ψ.range := E.subgroupOf Ψ.range with hE1def
  have hE1 : IsElemAbelian p E1 :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (hEcomm a.1.1 a.2 b.1.1 b.2)),
     fun x hx => Subtype.ext (hEp x hx)⟩
  obtain ⟨E', hmapE', hdisE', hE'ea⟩ :=
    exists_lift_elemAbelian_of_coprime_ker Ψ' hΨ'surj (hΨ'ker ▸ hΨcop) hE1
  have hcardE1 : Nat.card E1 = p ^ 2 := by
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le).toEquiv
  have hcardE' : Nat.card E' = p ^ 2 := by
    rw [← CFSG.LieType.SeitzGeneration.ExcHigh.card_map_eq_of_disjoint_ker Ψ' hdisE', hmapE',
      hcardE1]
  set Ebar : Subgroup _ := E'.map π with hEbar
  have hEbarea : IsElemAbelian p Ebar :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE'ea π
  have hcardEbar : Nat.card Ebar = p ^ 2 := by
    rw [hEbar, CFSG.LieType.SeitzGeneration.ExcHigh.card_map_eq_of_disjoint_ker π
      (disjoint_ker_of_exponent π hπcop hE'ea.2), hcardE']
  have hmodel := orthU3_plusPlanes (r := 8) (by norm_num) hp hp2 hpK hK2 Ebar hEbarea hcardEbar
  have hG := uniClosure_eq_top_of_quotient π hπsurj hZ.le hπcop hrcop hperf E' hE'ea.2 hmodel
  have hdisΨ : Disjoint E' Ψ.ker := hΨ'ker ▸ hdisE'
  rw [← hrange, MonoidHom.range_eq_map, ← hG, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨g, ⟨x, hx, hx1, hg, hgr⟩, rfl⟩
  refine ⟨Ψ x, ?_, ?_, ?_, 1, ?_⟩
  · have : Ψ' x ∈ E1 := hmapE' ▸ ⟨x, hx, rfl⟩
    exact this
  · intro h1
    exact hx1 (Subgroup.disjoint_def.mp hdisΨ hx (MonoidHom.mem_ker.mpr h1))
  · show Ψ g * Ψ x = Ψ x * Ψ g
    rw [← map_mul, ← map_mul]
    exact congrArg Ψ hg
  · rw [pow_one, ← map_pow, hgr, map_one]

theorem e8TwoUniNative (K : Type) [Field K] [Finite K] (hK2 : ringChar K ≠ 2) (p : ℕ)
    [hpF : Fact p.Prime] (hp7 : 7 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (E₀ : Subgroup (adjointGroup .E8 K)) (hE₀p : ∀ x ∈ E₀, x ^ p = 1) (hE₀c : Nat.card E₀ = p ^ 2)
    (hN : ¬ NormalizesRGroup (ringChar K) E₀) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (ringChar K ^ m) = 1} = ⊤ := by
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family (exists_e8D8_family K)
  have hpK : ¬ p ∣ Nat.card K := by
    intro hd
    have h1 : p ∣ 1 := (Nat.dvd_add_right hd).mp hpq
    exact hpF.out.one_lt.ne' (Nat.dvd_one.mp h1)
  have hpq1 : ¬ p ∣ Nat.card K - 1 := by
    intro hd
    have hq1 : 1 ≤ Nat.card K := Nat.card_pos
    have h3 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq hd
    have e : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [e] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hSyl : ∃ g : adjointGroup .E8 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e8FrameGroup K := by
    rcases (by omega : p = 7 ∨ 11 ≤ p ∨ p = 8 ∨ p = 9 ∨ p = 10) with rfl | h11 | h | h | h
    · exact e8TwoSylowSeven K hpq E₀ hE₀p hE₀c hN
    · exact e8TwoSylow K p h11 hpq E₀ hE₀p hE₀c
    all_goals subst h; exact absurd hpF.out (by norm_num)
  exact uniClosure_eq_top_of_two_conj (p := p) (⨆ k, e8D8Chain K k) (e8FrameGroup K)
    (weylWordElt .E8 K e8Word) e8FrameGroup_le_d8 e8FrameGroup_le_conj_d8
    (fun M hX hn => eq_top_of_e8D8Chain_le_of_conj_le M hX hn)
    (fun E hE hEp hEc => iSup_d8Chain_le_uniClosure_of_ne hK2 hpF.out (by omega) hpK hpq1 Ψ hker
      hrange E hE hEp hEc) E₀ hE₀p hE₀c hSyl

theorem e8FourUniNative (K : Type) [Field K] [Finite K] (hK2 : ringChar K ≠ 2) (p : ℕ)
    [hpF : Fact p.Prime] (hp7 : 7 ≤ p) (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 4)
    (E₀ : Subgroup (adjointGroup .E8 K)) (hE₀p : ∀ x ∈ E₀, x ^ p = 1) (hE₀c : Nat.card E₀ = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (ringChar K ^ m) = 1} = ⊤ := by
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family (exists_e8D8_family K)
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  exact uniClosure_eq_top_of_two_conj (p := p) (⨆ k, e8D8Chain K k) (e8D4Group K)
    (weylWordElt .E8 K e8Word) e8D4Group_le_d8 e8D4Group_le_conj_d8
    (fun M hX hn => eq_top_of_e8D8Chain_le_of_conj_le M hX hn)
    (fun E hE hEp hEc => iSup_d8Chain_le_uniClosure_of_ne hK2 hpF.out (by omega)
      (not_dvd_of_orderOf_eq_four hpF.out he) (not_dvd_pred_of_orderOf_eq_four hpF.out hq1 he)
      Ψ hker hrange E hE hEp hEc) E₀ hE₀p hE₀c (e8FourSylow K p hp7 he E₀ hE₀p hE₀c)

theorem e8FourUniNative_five
    (K : Type) [Field K] [Finite K] (hK2 : ringChar K ≠ 2)
    (he : orderOf ((Nat.card K : ℕ) : ZMod 5) = 4) (E₀ : Subgroup (adjointGroup .E8 K))
    (hE₀p : ∀ x ∈ E₀, x ^ 5 = 1) (hE₀c : Nat.card E₀ = 5 ^ 2)
    (hN : ¬ NormalizesRGroup (ringChar K) E₀) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (ringChar K ^ m) = 1} = ⊤ := by
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hpK : ¬ 5 ∣ Nat.card K := e8Five_not_dvd_of_orderOf_eq_four he
  have hpq1 : ¬ 5 ∣ Nat.card K - 1 := e8Five_not_dvd_pred_of_orderOf_eq_four hq1 he
  have hn' : ¬ NormalizesRNative Tag.E8 K E₀ := fun h =>
    hN (CFSG.LieType.SeitzGeneration.ExcHigh.normalizesRGroup_of_native h)
  obtain ⟨D, hD⟩ := e8Five_regular_datum hpK hE₀p hE₀c hn'
  obtain ⟨k, hk⟩ := exists_conj_le_of_frameDatum hE₀p D
    (e8FiveFourFrameDatum_holds K he D.Fr D.hFr D.w
      (e8FiveFourSquare_holds K he E₀ hE₀p hE₀c D hD))
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family (exists_e8D8_family K)
  exact uniClosure_eq_top_of_two_conj (p := 5) (⨆ k, e8D8Chain K k) (e8D4Group K)
    (weylWordElt .E8 K e8Word) e8D4Group_le_d8 e8D4Group_le_conj_d8
    (fun M hX hn => eq_top_of_e8D8Chain_le_of_conj_le M hX hn)
    (fun E hE hEp hEc => iSup_d8Chain_le_uniClosure_of_ne hK2 Nat.prime_five le_rfl hpK hpq1 Ψ hker
      hrange E hE hEp hEc) E₀ hE₀p hE₀c ⟨k, hk⟩

end E8TwoUni

section E8FiveUni

open CFSG.LieType.SeitzGeneration.ExcHigh CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Tables.T1b
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.HardMathSupport.Malle.SeitzCube
  CFSG.HardMathSupport.Lang.AnisoE8 CFSG.ComponentClassification.CatLeafProof

set_option linter.unusedSectionVars false

theorem closingFrameAt_splitE8 (K : Type) [Field K] [Finite K] (hK : 5 ∣ Nat.card K - 1) (ζ : Kˣ)
    (hζ : orderOf ζ = 5) : ClosingFrameAt (zSplitE8 K ζ) (frameIn (XS K)) := by
  have hK4 : 4 ≤ Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  set a : Fin Tag.E8.rank → Kˣ := Pi.mulSingle (4 : Fin Tag.E8.rank) ζ with ha
  have hchar : ∀ α : Fin Tag.E8.rank → ℤ, rootChar a α = ζ ^ (α 4) := by
    intro α
    unfold rootChar
    rw [Finset.prod_eq_single (4 : Fin Tag.E8.rank)]
    · simp [ha]
    · intro j _ hj
      simp [ha, Pi.mulSingle_eq_of_ne hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hS : ∀ α ∈ cosetRoots Tag.E8 4 5, IsRoot Tag.E8 α ∧ rootChar a α = 1 := by
    intro α hα
    refine ⟨hα.1, ?_⟩
    rw [hchar, ← orderOf_dvd_iff_zpow_eq_one, hζ]
    exact_mod_cast hα.2
  have hXS : XS K ≤ adjointGroup Tag.E8 K := rootSpan_le_adjointGroup K _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hy' : (y : ModGL .E8 K) ∈ XS K := hy
    have := Subgroup.mem_centralizer_singleton_iff.1
      (rootSpan_le_centralizer_rootDiagUnit (K := K) a hS hy')
    exact this
  · refine nonsolvable_frameIn hXS ?_
    intro hs
    haveI := hs
    haveI h2 : Group.IsSolvable ↥(X2 K) :=
      solvable_of_solvable_injective (Subgroup.inclusion_injective (X2_le_XS K))
    obtain ⟨hperf, -, a₀, b₀, hab⟩ := X2_quasisimple K
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a₀
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b₀
    haveI : Nontrivial ↥(X2 K) := ⟨⟨x, 1, fun h => hab (by rw [h]; simp)⟩⟩
    exact (IsSolvable.commutator_lt_top_of_nontrivial (↥(X2 K))).ne hperf.commutator_eq_top
  · exact closing_of_twFrameClosing hXS
      ((frameClosing_iff Tag.E8 K _).1
        (frameClosing_of_detection_E8 K (frameDetection_E8 K)))
  · exact normalizerSolvable_of_twFrame hXS
      ((frameNormalizerSolvable_iff Tag.E8 K _).1 (frameNormalizerSolvable_E8 K hK4))

theorem frameIn_XS_E8_le_closure (K : Type) [Field K] [Finite K] :
    frameIn (XS K) ≤
      Subgroup.closure {x | x ∈ frameIn (XS K) ∧ ∃ n : ℕ, x ^ (ringChar K ^ n) = 1} := by
  refine subgroupOf_le_closure_of_le (rootSpan_le_adjointGroup K _) ?_
  refine iSup₂_le fun α hα => ?_
  rw [rootSubgroup, Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩
  refine Subgroup.subset_closure ⟨?_, 1, ?_⟩
  · exact (le_iSup₂_of_le (f := fun β (_ : β ∈ cosetRoots Tag.E8 4 5) => rootSubgroup Tag.E8 K β) α hα
      le_rfl) (Subgroup.subset_closure ⟨c, rfl⟩)
  · rw [pow_one, pinnedX_pow_eq, ringChar.Nat.cast_ringChar, zero_mul, pinnedX_zero]

theorem closingFrameAt_twistedE8 (K : Type) [Field K] [Finite K] (hK : 5 ∣ Nat.card K + 1)
    (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w) (ζ : D.Lˣ) (hζ : orderOf ζ = 5)
    (z : adjointGroup TwClass.e8Ten.tag K)
    (hzbc : baseChangeGL (algebraMap K D.L) (z : ModGL TwClass.e8Ten.tag K) =
      D.g * rootDiagUnit TwClass.e8Ten.tag (Pi.mulSingle (⟨4, by decide⟩ : Fin
        TwClass.e8Ten.tag.rank) ζ) * D.g⁻¹) :
    ClosingFrameAt z (frameIn (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D)) := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  set i₁ : Fin TwClass.e8Ten.tag.rank := ⟨4, by decide⟩ with hi₁
  set a : Fin TwClass.e8Ten.tag.rank → D.Lˣ := Pi.mulSingle i₁ ζ with ha
  have hzbc' : baseChangeGL (algebraMap K D.L) (z : ModGL TwClass.e8Ten.tag K) =
      D.g * rootDiagUnit TwClass.e8Ten.tag a * D.g⁻¹ := hzbc
  have hchar : ∀ α : Fin TwClass.e8Ten.tag.rank → ℤ, rootChar a α = ζ ^ (α i₁) := by
    intro α
    unfold rootChar
    rw [Finset.prod_eq_single i₁]
    · simp [ha]
    · intro j _ hj
      simp [ha, Pi.mulSingle_eq_of_ne hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hS : ∀ S : Set (Fin TwClass.e8Ten.tag.rank → ℤ), (∀ α ∈ S, 5 ∣ α i₁) →
      (∀ α ∈ S, IsRoot TwClass.e8Ten.tag α) → ∀ α ∈ S, IsRoot TwClass.e8Ten.tag α ∧
        rootChar a α = 1 := by
    intro S h5S hrS α hα
    refine ⟨hrS α hα, ?_⟩
    rw [hchar, ← orderOf_dvd_iff_zpow_eq_one, hζ]
    exact_mod_cast h5S α hα
  have hS₁ : ∀ α ∈ TwClass.e8Ten.S₁, IsRoot TwClass.e8Ten.tag α ∧ rootChar a α = 1 := by
    refine hS _ (fun α hα => ?_) (fun α hα => hα.1)
    have hα' : α ∈ {r | r ∈ e8ListB} := by rw [← QuasiE8Ten.S₁_eq]; exact hα
    have hmem : α ∈ cosetRoots Tag.E8 4 5 := by
      rw [e8_coset_eq]
      exact Or.inr hα'
    exact hmem.2
  have hS₂ : ∀ α ∈ TwClass.e8Ten.S₂, IsRoot TwClass.e8Ten.tag α ∧ rootChar a α = 1 := by
    refine hS _ (fun α hα => ?_) (fun α hα => hα.1)
    have hα' : α ∈ {r | r ∈ e8ListA} := by rw [← QuasiE8Ten.S₂_eq]; exact hα
    have hmem : α ∈ cosetRoots Tag.E8 4 5 := by
      rw [e8_coset_eq]
      exact Or.inl hα'
    exact hmem.2
  have hcomm : ∀ S : Set (Fin TwClass.e8Ten.tag.rank → ℤ),
      (∀ α ∈ S, IsRoot TwClass.e8Ten.tag α ∧ rootChar a α = 1) →
      D.frame S ≤ Subgroup.centralizer ({(z : ModGL TwClass.e8Ten.tag K)} :
        Set (ModGL TwClass.e8Ten.tag K)) := by
    intro S hS' x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxc := rootSpan_le_centralizer_rootDiagUnit (K := D.L) a hS' hx.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hxc
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxc
    apply baseChangeGL_injective (algebraMap K D.L)
    rw [map_mul, map_mul, hzbc']
    calc baseChangeGL (algebraMap K D.L) x * (D.g * rootDiagUnit TwClass.e8Ten.tag a * D.g⁻¹)
        = D.g * ((D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g⁻¹⁻¹) *
            rootDiagUnit TwClass.e8Ten.tag a) * D.g⁻¹ := by group
      _ = D.g * (rootDiagUnit TwClass.e8Ten.tag a * (D.g⁻¹ * baseChangeGL (algebraMap K D.L) x *
            D.g⁻¹⁻¹)) * D.g⁻¹ := by rw [hxc]
      _ = (D.g * rootDiagUnit TwClass.e8Ten.tag a * D.g⁻¹) * baseChangeGL (algebraMap K D.L) x := by
          group
  have hKq : TwClass.e8Ten.minQ ≤ Nat.card K := by
    show 2 ≤ Nat.card K
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hle : TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤ adjointGroup TwClass.e8Ten.tag K :=
    sup_le inf_le_left inf_le_left
  have hq3 := twQuasi_of_ne_e6Six TwClass.e8Ten (by decide) K hKq D
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hy' : (y : ModGL TwClass.e8Ten.tag K) ∈
        TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D := hy
    have hsup : TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤
        Subgroup.centralizer ({(z : ModGL TwClass.e8Ten.tag K)} :
          Set (ModGL TwClass.e8Ten.tag K)) :=
      sup_le (hcomm _ hS₁) (hcomm _ hS₂)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hsup hy')
  · refine nonsolvable_frameIn hle ?_
    intro hs
    haveI := hs
    haveI h2 : Group.IsSolvable ↥(TwClass.e8Ten.X₂ D) :=
      solvable_of_solvable_injective (Subgroup.inclusion_injective
        (le_sup_right : TwClass.e8Ten.X₂ D ≤ TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D))
    obtain ⟨hperf, -, a₀, b₀, hab⟩ := hq3.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a₀
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b₀
    haveI : Nontrivial ↥(TwClass.e8Ten.X₂ D) := ⟨⟨x, 1, fun h => hab (by rw [h]; simp)⟩⟩
    exact (IsSolvable.commutator_lt_top_of_nontrivial
      (↥(TwClass.e8Ten.X₂ D))).ne hperf.commutator_eq_top
  · have h3 : 3 ≤ Nat.card K := by
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      omega
    exact closing_of_twFrameClosing hle (E8TenAux.twClosing_e8Ten_three K D h3)
  · exact normalizerSolvable_of_twFrame hle (twNormalizer_e8Ten K hKq D)

theorem frameIn_twistedE8_le_closure (K : Type) [Field K] [Finite K]
    (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w) :
    frameIn (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D) ≤
      Subgroup.closure {x | x ∈ frameIn (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D) ∧
        ∃ n : ℕ, x ^ (ringChar K ^ n) = 1} := by
  classical
  have hle : TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤ adjointGroup TwClass.e8Ten.tag K :=
    sup_le inf_le_left inf_le_left
  refine subgroupOf_le_closure_of_le hle ?_
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hr : ringChar K ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self _ n.ne_zero
  have : Finite (ModGL TwClass.e8Ten.tag K) := finite_modGL
  obtain ⟨hc₁, hc₂, -⟩ := TwCardAux.e8Ten_frames K D
  have hd : ringChar K ∣ Nat.card K ^ 10 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 + 1) *
      ((Nat.card K ^ 4 - 1) * (Nat.card K ^ 5 + 1))) :=
    dvd_mul_of_dvd_left (dvd_pow hr (by norm_num)) _
  have h₁ := le_closure_pow_of_quasisimple (r := ringChar K) (isQuasisimple_e8Ten_X₁ D)
    (by rw [hc₁]; exact hd)
  have h₂ := le_closure_pow_of_quasisimple (r := ringChar K) (isQuasisimple_e8Ten_X₂ D)
    (by rw [hc₂]; exact hd)
  refine sup_le (h₁.trans (Subgroup.closure_mono fun x ⟨hx, k, hk⟩ =>
    ⟨Subgroup.mem_sup_left hx, k, hk⟩)) (h₂.trans (Subgroup.closure_mono fun x ⟨hx, k, hk⟩ =>
    ⟨Subgroup.mem_sup_right hx, k, hk⟩))

theorem exists_e8FiveFrameElt_split (K : Type) [Field K] [Finite K]
    (hK : 5 ∣ Nat.card K - 1) (ζ : Kˣ) (hζ : orderOf ζ = 5) :
    ∃ F : E8FiveFrameElt K, F.z = zSplitE8 K ζ := by
  obtain ⟨-, -, X, hX⟩ := e8SplitFrame_of K hK ζ hζ
  set ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have hω : orderOf (Units.map ι.toMonoidHom ζ) = 5 :=
    (orderOf_injective (Units.map ι.toMonoidHom) (Units.map_injective ι.injective) ζ).trans hζ
  refine ⟨⟨Units.map ι.toMonoidHom ζ, hω, zSplitE8 K ζ, 1, 1, 1, one_mem _, one_mem _,
    by norm_num, fun Fr _ => by simp, by simp, ?_, ⟨X, hX⟩⟩, rfl⟩
  change baseChangeGL ι (rootDiagUnit Tag.E8 (Pi.mulSingle (4 : Fin Tag.E8.rank) ζ)) =
    1 * rootDiagUnit Tag.E8 (Pi.mulSingle (4 : Fin Tag.E8.rank) (Units.map ι.toMonoidHom ζ)) * 1⁻¹
  rw [baseChangeGL_rootDiagUnit, inv_one, mul_one, one_mul]
  congr 1
  funext i
  by_cases hi : i = 4
  · subst hi
    simp
  · simp [Pi.mulSingle_eq_of_ne hi]

theorem exists_e8FiveFrameElt_twisted (K : Type) [Field K] [Finite K]
    (hK : 5 ∣ Nat.card K + 1) :
    ∃ (F : E8FiveFrameElt K) (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w) (ζ : D.Lˣ),
      orderOf ζ = 5 ∧ baseChangeGL (algebraMap K D.L) (F.z : ModGL Tag.E8 K) =
        D.g * rootDiagUnit TwClass.e8Ten.tag (Pi.mulSingle (⟨4, by decide⟩ : Fin
          TwClass.e8Ten.tag.rank) ζ) * D.g⁻¹ := by
  have hnd : ¬ 5 ∣ Nat.card K := by omega
  obtain ⟨Fr, hFr, g, hg, hlang⟩ := exists_langLevi_algebraicClosure TwClass.e8Ten.tag K
    TwClass.e8Ten.w e8Ten_w_theta
  let D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w :=
    ⟨AlgebraicClosure K, Fr, hFr, g, hg, hlang⟩
  obtain ⟨ω, hω⟩ := exists_fifth_root_langLevi K hnd D
  obtain ⟨z, hzbc, -, -, X, hX⟩ := e8TwistedFrame_of K hK D ω hω
  refine ⟨⟨ω, hω, z, g,
    canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) TwClass.e8Ten.w, 4,
    parabolicLevi_le_adjointGroup (K := AlgebraicClosure K) (τ := TwClass.e8Ten.tag) _ hg,
    canonicalRep_mem_adjointGroup _ _ _, by norm_num,
    ?_, e8Ten_conj_rootDiagUnit hω, hzbc, ⟨X, hX⟩⟩, D, ω, hω, hzbc⟩
  intro Fr' hFr'
  have hFr'' : Fr' = Fr := RingHom.ext fun c => (hFr' c).trans (hFr c).symm
  subst hFr''
  exact hlang

theorem e8FiveUniClose_of_frameElt {K : Type} [Field K] [Finite K]
    (hpK : ¬ 5 ∣ Nat.card K) {E₀ : Subgroup (adjointGroup Tag.E8 K)} (hE₀p : ∀ x ∈ E₀, x ^ 5 = 1)
    (hE₀c : Nat.card E₀ = 5 ^ 2) (D : LangPlaneData Tag.E8 K E₀)
    (hreg : ∀ α, IsRoot Tag.E8 α → ¬ D.Kills α) {V : WeylGroup Tag.E8} (hV1 : V ≠ 1)
    (hV : ∀ x ∈ E₀, ∀ a : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit Tag.E8 a = diagMap D x → ∀ v, rootChar a (V • v) = rootChar a v)
    (F : E8FiveFrameElt K) {X : Subgroup (adjointGroup Tag.E8 K)} (hX : ClosingFrameAt F.z X)
    (hXr : X ≤ Subgroup.closure {x | x ∈ X ∧ ∃ n : ℕ, x ^ (ringChar K ^ n) = 1}) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (ringChar K ^ n) = 1} =
      ⊤ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨a, ha, b, hb, ha1, hb1, hgen⟩ := exists_gens_of_plane (p := 5) hE₀p hE₀c
  obtain ⟨ga, hga⟩ := E8FiveSq.exists_conj_frameElt hpK hE₀p hE₀c D hreg hV1 hV F ha ha1
  obtain ⟨gb, hgb⟩ := E8FiveSq.exists_conj_frameElt hpK hE₀p hE₀c D hreg hV1 hV F hb hb1
  have hXa : ClosingFrameAt a (X.map (MulAut.conj ga⁻¹).toMonoidHom) := by
    have := hX.conj ga⁻¹
    rwa [show ga⁻¹ * F.z * ga⁻¹⁻¹ = a by rw [← hga]; group] at this
  have hXb : ClosingFrameAt b (X.map (MulAut.conj gb⁻¹).toMonoidHom) := by
    have := hX.conj gb⁻¹
    rwa [show gb⁻¹ * F.z * gb⁻¹⁻¹ = b by rw [← hgb]; group] at this
  exact uniClosure_eq_top_of_closingFrames ha hb ha1 hb1 hgen hXa hXb
    (E8FiveSq.isSolvable_centralizer_of_regular_five hpK hE₀p hE₀c D hreg)
    (map_le_closure_pow _ hXr) (map_le_closure_pow _ hXr)

theorem e8OneUniNative_five (K : Type) [Field K] [Finite K]
    (hpq : 5 ∣ Nat.card K - 1) (E₀ : Subgroup (adjointGroup .E8 K)) (hE₀p : ∀ x ∈ E₀, x ^ 5 = 1)
    (hE₀c : Nat.card E₀ = 5 ^ 2) (hN : ¬ NormalizesRGroup (ringChar K) E₀) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (ringChar K ^ m) = 1} = ⊤ := by
  have hK1 : 0 < Nat.card K := Nat.card_pos
  have hpK : ¬ 5 ∣ Nat.card K := by omega
  have hn' : ¬ NormalizesRNative Tag.E8 K E₀ := fun h =>
    hN (CFSG.LieType.SeitzGeneration.ExcHigh.normalizesRGroup_of_native h)
  obtain ⟨D, hD⟩ := e8Five_regular_datum hpK hE₀p hE₀c hn'
  have hw : D.w ≠ 1 := fun hw => hn' (e8_normalizesRNative_of_split_datum D hw)
  obtain ⟨ζ, hζ⟩ := e8SplitFrame K hpq
  obtain ⟨F, hF⟩ := exists_e8FiveFrameElt_split K hpq ζ hζ
  have hX : ClosingFrameAt F.z (frameIn (XS K)) := by
    rw [hF]
    exact closingFrameAt_splitE8 K hpq ζ hζ
  refine e8FiveUniClose_of_frameElt hpK hE₀p hE₀c D hD hw ?_ F hX (frameIn_XS_E8_le_closure K)
  intro x hx a ha v
  rw [E8FiveSq.rootChar_smul_eq_pow_of_mem D hx ha v]
  obtain ⟨m, hm⟩ := hpq
  rw [show Nat.card K = 5 * m + 1 by omega, pow_succ, pow_mul,
    E8FiveSq.rootChar_pow_five_of_mem hE₀p D hx ha v, one_pow, one_mul]

theorem e8TwoUniNative_five (K : Type) [Field K] [Finite K]
    (hK2 : ringChar K ≠ 2) (hpq : 5 ∣ Nat.card K + 1) (E₀ : Subgroup (adjointGroup .E8 K))
    (hE₀p : ∀ x ∈ E₀, x ^ 5 = 1) (hE₀c : Nat.card E₀ = 5 ^ 2)
    (hN : ¬ NormalizesRGroup (ringChar K) E₀) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (ringChar K ^ m) = 1} = ⊤ := by
  have hpK : ¬ 5 ∣ Nat.card K := by omega
  have hpq1 : ¬ 5 ∣ Nat.card K - 1 := by omega
  have hn' : ¬ NormalizesRNative Tag.E8 K E₀ := fun h =>
    hN (CFSG.LieType.SeitzGeneration.ExcHigh.normalizesRGroup_of_native h)
  obtain ⟨D, hD⟩ := e8Five_regular_datum hpK hE₀p hE₀c hn'
  by_cases hw : ∀ u : Fin Tag.E8.rank → ℤ, D.w • u = -u
  · obtain ⟨k, hk⟩ := exists_conj_le_of_frameDatum hE₀p D
      (e8FiveTwoFrameDatum_holds K hpq D.Fr D.hFr D.w hw)
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family (exists_e8D8_family K)
    exact uniClosure_eq_top_of_two_conj (p := 5) (⨆ k, e8D8Chain K k) (e8FrameGroup K)
      (weylWordElt .E8 K e8Word) e8FrameGroup_le_d8 e8FrameGroup_le_conj_d8
      (fun M hX hn => eq_top_of_e8D8Chain_le_of_conj_le M hX hn)
      (fun E hE hEp hEc => iSup_d8Chain_le_uniClosure_of_ne hK2 Nat.prime_five le_rfl hpK hpq1 Ψ
        hker hrange E hE hEp hEc) E₀ hE₀p hE₀c ⟨k, hk⟩
  · obtain ⟨u, hu⟩ := not_forall.1 hw
    obtain ⟨F, D', ζ, hζ, hzbc⟩ := exists_e8FiveFrameElt_twisted K hpq
    obtain ⟨w₀, hw₀⟩ := E8FiveSq.exists_weyl_neg_E8_five
    refine e8FiveUniClose_of_frameElt (V := w₀ * D.w) hpK hE₀p hE₀c D hD ?_ ?_ F
      (closingFrameAt_twistedE8 K hpq D' ζ hζ F.z hzbc) (frameIn_twistedE8_le_closure K D')
    · intro h1
      apply hu
      rw [eq_inv_of_mul_eq_one_right h1, inv_smul_eq_iff, hw₀, neg_neg]
    · intro x hx a ha v
      rw [mul_smul, hw₀, ← neg_one_zsmul, CFSG.LieType.Chevalley.rootChar_zsmul, zpow_neg_one,
        E8FiveSq.rootChar_smul_eq_pow_of_mem D hx ha v]
      obtain ⟨m, hm⟩ := hpq
      have h5 := E8FiveSq.rootChar_pow_five_of_mem hE₀p D hx ha v
      rw [show Nat.card K = 5 * (m - 1) + 4 by omega, pow_add, pow_mul, h5, one_pow, one_mul,
        inv_eq_iff_mul_eq_one, ← pow_succ]
      exact h5

end E8FiveUni

section E8Glue

open CFSG.LieType.SeitzGeneration.ExcHigh TauCeti

set_option linter.unusedSectionVars false

theorem orderOf_zmod_five_eq_four {q : ℕ} (h : q % 5 = 2 ∨ q % 5 = 3) :
    orderOf ((q : ℕ) : ZMod 5) = 4 := by
  have hq : ((q : ℕ) : ZMod 5) = ((q % 5 : ℕ) : ZMod 5) := (ZMod.natCast_mod q 5).symm
  rw [hq]
  rcases h with h | h <;> rw [h] <;> rw [orderOf_eq_iff (by norm_num)] <;>
    refine ⟨by decide, ?_⟩ <;> intro m hm hm0 <;> interval_cases m <;> decide

theorem uniPlaneGen_E8_of_native {q : TauCeti.PrimePower} (hv : (LieTypeIndex.E8 q).Valid) {p : ℕ}
    (hch : (LieTypeIndex.E8 q).characteristic ≠ 2)
    (hnat : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q.card → ringChar K ≠ 2 →
      ∀ E₀ : Subgroup (adjointGroup .E8 K), (∀ x ∈ E₀, x ^ p = 1) → Nat.card E₀ = p ^ 2 →
        ¬ NormalizesRGroup (ringChar K) E₀ →
          Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (ringChar K ^ m) = 1} = ⊤)
    {E : Subgroup (MulAut (CFSG.LieType.SeitzGeneration.Cat ⟨.E8 q, hv⟩))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) (hin : InnerPlane ⟨.E8 q, hv⟩ p E)
    (hn : ¬ NormalizesRSubgroup ⟨.E8 q, hv⟩ E) :
    UniPlaneGen (LieTypeIndex.E8 q).characteristic E := by
  obtain ⟨K, _, _, hKq, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
  have hring : ringChar K = q.p := ringChar.eq K q.p
  have hK2 : ringChar K ≠ 2 := by
    rw [hring]
    intro h
    exact hch (by rw [LieTypeIndex.characteristic_E8]; exact h)
  have h := uniPlaneGen_of_native_uniClosure (p := p) (r := ringChar K) e
    (conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot center_adjointGroup_eq_bot))
    (fun E₀ h1 h2 h3 => hnat K hKq hK2 E₀ h1 h2 h3) hE hc hin ?_
  · rw [hring] at h
    rw [LieTypeIndex.characteristic_E8]
    exact h
  · rintro ⟨R, hR1, hRp, hRn⟩
    refine hn ⟨R, hR1, ?_, hRn⟩
    show IsPGroup (LieTypeIndex.E8 q).characteristic R
    rw [LieTypeIndex.characteristic_E8, ← hring]
    exact hRp

theorem uniSeitzPlanes_E8_inner :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧
      (∃ q : TauCeti.PrimePower, d.1 = .E8 q ∧
        (p = 5 ∨ (7 ≤ p ∧ (p ∣ q.card - 1 ∨ p ∣ q.card + 1)) ∨
          orderOf ((q.card : ℕ) : ZMod p) = 4)) ∧
      d.1.characteristic ≠ 2 ∧ ¬ NormalizesRSubgroup d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, ⟨q, hq, hpq⟩, hch, hn⟩
  obtain rfl : d = .E8 q := hq
  haveI : Fact p.Prime := ⟨hp⟩
  have hfour : ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 2 →
      orderOf ((Nat.card K : ℕ) : ZMod p) = 4 → ∀ E₀ : Subgroup (adjointGroup .E8 K),
        (∀ x ∈ E₀, x ^ p = 1) → Nat.card E₀ = p ^ 2 → ¬ NormalizesRGroup (ringChar K) E₀ →
          Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧
            ∃ m : ℕ, k ^ (ringChar K ^ m) = 1} = ⊤ := by
    intro K _ _ hK2 he E₀ h1 h2 h3
    rcases (by omega : p = 5 ∨ p = 6 ∨ 7 ≤ p) with rfl | rfl | hp7
    · exact e8FourUniNative_five K hK2 he E₀ h1 h2 h3
    · exact absurd hp (by norm_num)
    · exact e8FourUniNative K hK2 p hp7 he E₀ h1 h2
  rcases hpq with rfl | ⟨hp7, hpq | hpq⟩ | hpq
  ·
    have hq5 : ¬ 5 ∣ q.card := by
      rw [TauCeti.PrimePower.card_def]
      intro hd
      exact hpd (by
        rw [LieTypeIndex.characteristic_E8]
        exact (Nat.prime_dvd_prime_iff_eq Nat.prime_five q.prime_p).1
          (Nat.prime_five.dvd_of_dvd_pow hd))
    have hq1 : 1 ≤ q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact Nat.one_le_pow _ _ q.prime_p.pos
    rcases (by omega : 5 ∣ q.card - 1 ∨ 5 ∣ q.card + 1 ∨ q.card % 5 = 2 ∨ q.card % 5 = 3) with
      h1 | h4 | h23
    · exact uniPlaneGen_E8_of_native hv hch (fun K _ _ hKq _ E₀ h1' h2 h3 =>
        e8OneUniNative_five K (by rw [hKq]; exact h1) E₀ h1' h2 h3) hE hc hin hn
    · exact uniPlaneGen_E8_of_native hv hch (fun K _ _ hKq hK2 E₀ h1' h2 h3 =>
        e8TwoUniNative_five K hK2 (by rw [hKq]; exact h4) E₀ h1' h2 h3) hE hc hin hn
    · exact uniPlaneGen_E8_of_native hv hch (fun K _ _ hKq hK2 E₀ h1' h2 h3 =>
        hfour K hK2 (by rw [hKq]; exact orderOf_zmod_five_eq_four h23) E₀ h1' h2 h3) hE hc hin hn
  · exact absurd (normalizesRSubgroup_E8_of_dvd_sub_one q hv hp hp7 hpq (IsPGroup.of_card hc) hin) hn
  · exact uniPlaneGen_E8_of_native hv hch (fun K _ _ hKq hK2 E₀ h1 h2 h3 =>
      e8TwoUniNative K hK2 p hp7 (by rw [hKq]; exact hpq) E₀ h1 h2 h3) hE hc hin hn
  · exact uniPlaneGen_E8_of_native hv hch (fun K _ _ hKq hK2 E₀ h1 h2 h3 =>
      hfour K hK2 (by rw [hKq]; exact hpq) E₀ h1 h2 h3) hE hc hin hn

end E8Glue

@[expose] def OddCpfRest3
    (d : TauCeti.ValidLieTypeIndex) (p : ℕ)
    (E : Subgroup (MulAut (CFSG.LieType.SeitzGeneration.Cat d))) : Prop :=
  OddCpfRest d p E ∧
    ((¬ InnerPlane d p E ∧ p = 3 ∧ IsDFourIndex d.1 ∧ ¬ orthOut3_SimilarityPlane d E) ∨
      (InnerPlane d p E ∧ IsChevalleyExcIndex d.1 ∧
        ((5 ≤ p ∧ ¬ (∃ q : TauCeti.PrimePower, d.1 = .F4 q ∧ (p ∣ q.card - 1 ∨ p ∣ q.card + 1)) ∧
            ¬ (∃ q : TauCeti.PrimePower, d.1 = .E8 q ∧
              (p = 5 ∨ (7 ≤ p ∧ (p ∣ q.card - 1 ∨ p ∣ q.card + 1)) ∨
                orderOf ((q.card : ℕ) : ZMod p) = 4))) ∨
          (p = 3 ∧ (IsG2Index d.1 ∨ IsTrialityIndex d.1 ∨
            ∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ q.card % 3 = 2)))) ∨
      (¬ InnerPlane d p E ∧ p = 3 ∧
        (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K)
          (σ : K ≃+* K), Nat.card K = (q.p ^ q.exponent) ^ 2 ∧ (∀ c, σ c = c ^ (q.p ^ q.exponent)) ∧
          ∃ e : CFSG.LieType.SeitzGeneration.Cat d ≃* twistedE6RootGroup K σ,
            E.map (MulAut.congr e).toMonoidHom ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) ∧
        ¬ IsTwE6DiagParabolicPlane d E) ∨
      (¬ InnerPlane d p E ∧ p = 3 ∧ IsTrialityIndex d.1))

section Residual

open TauCeti

set_option linter.unusedSectionVars false

theorem uniSeitzPlanes_oddCpfRest2_of_rest3 (h : UniSeitzPlanes OddCpfRest3) :
    UniSeitzPlanes OddCpfRest2 := by
  intro d p hp hp2 hpd hex E hE hc hs
  obtain ⟨hR, hcase⟩ := hs
  have hch : d.1.characteristic ≠ 2 := hR.1.1
  have hres : OddCpfRest3 d p E → UniPlaneGen d.1.characteristic E :=
    h d p hp hp2 hpd hex E hE hc
  rcases hcase with hb | ⟨hin, hexc⟩ | ⟨hout, hp3, ⟨q, hq, -⟩, hdiag⟩ | ⟨hout, hp3, ⟨q, hq⟩, hpar⟩ | htri
  · exact hres ⟨hR, Or.inl hb⟩
  · have hnR : ¬ NormalizesRSubgroup d E := fun hN => hR.2.2 ⟨hin, hexc, hN⟩
    have hp35 : p = 3 ∨ 5 ≤ p := by
      have h2 := hp.two_le
      rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h' | h' | h' | h'
      · exact absurd h' hp2
      · exact Or.inl h'
      · exact absurd (h' ▸ hp) (by norm_num)
      · exact Or.inr h'
    rcases hp35 with rfl | hp5
    · have hexc' : (IsG2Index d.1 ∨ IsF4Index d.1 ∨ IsE6Index d.1 ∨ IsE7Index d.1 ∨ IsE8Index d.1) ∨
          (IsTrialityIndex d.1 ∨ IsTwistedE6Index d.1) := hexc
      rcases hexc' with (hg | hf | he6 | he7 | he8) | (ht | ⟨q, hq⟩)
      · exact hres ⟨hR, Or.inr (Or.inl ⟨hin, hexc, Or.inr ⟨rfl, Or.inl hg⟩⟩)⟩
      · exact uniSeitzPlanes_F4_inner_three d 3 hp hp2 hpd hex E hE hc ⟨hin, rfl, hf, hch, hnR⟩
      · exact uniSeitzPlanes_E6_inner_three d 3 hp hp2 hpd hex E hE hc ⟨hin, rfl, he6, hch, hnR⟩
      · exact uniSeitzPlanes_E78_inner_three d 3 hp hp2 hpd hex E hE hc ⟨hin, rfl, Or.inl he7, hnR⟩
      · exact uniSeitzPlanes_E78_inner_three d 3 hp hp2 hpd hex E hE hc ⟨hin, rfl, Or.inr he8, hnR⟩
      · exact hres ⟨hR, Or.inr (Or.inl ⟨hin, hexc, Or.inr ⟨rfl, Or.inr (Or.inl ht)⟩⟩)⟩
      · have hq3 : 3 ≠ q.p := by
          intro h3
          apply hpd
          rw [hq, LieTypeIndex.characteristic_twistedE6, h3]
        rcases card_mod_three_of_ne hq3 with h1 | h2
        · exact uniSeitzPlanes_twE6_inner_three_one d 3 hp hp2 hpd hex E hE hc
            ⟨hin, rfl, ⟨q, hq, h1⟩, hch, hnR⟩
        · exact hres ⟨hR, Or.inr (Or.inl ⟨hin, hexc, Or.inr ⟨rfl, Or.inr (Or.inr ⟨q, hq, h2⟩)⟩⟩)⟩
    · by_cases hF : ∃ q : TauCeti.PrimePower, d.1 = .F4 q ∧ (p ∣ q.card - 1 ∨ p ∣ q.card + 1)
      · exact uniSeitzPlanes_F4_inner_two d p hp hp2 hpd hex E hE hc ⟨hin, hp5, hF, hch, hnR⟩
      by_cases hE8 : ∃ q : TauCeti.PrimePower, d.1 = .E8 q ∧
          (p = 5 ∨ (7 ≤ p ∧ (p ∣ q.card - 1 ∨ p ∣ q.card + 1)) ∨
            orderOf ((q.card : ℕ) : ZMod p) = 4)
      · exact uniSeitzPlanes_E8_inner d p hp hp2 hpd hex E hE hc ⟨hin, hp5, hE8, hch, hnR⟩
      exact hres ⟨hR, Or.inr (Or.inl ⟨hin, hexc, Or.inl ⟨hp5, hF, hE8⟩⟩)⟩
  · have hq2 : q.p ≠ 2 := by
      intro h2
      apply hch
      rw [hq, LieTypeIndex.characteristic_E6, h2]
    exact uniSeitzPlanes_E6_field d p hp hp2 hpd hex E hE hc ⟨hout, hp3, ⟨q, hq, hq2⟩, hdiag⟩
  · have hq2 : q.p ≠ 2 := by
      intro h2
      apply hch
      rw [hq, LieTypeIndex.characteristic_twistedE6, h2]
    by_cases hmodel : ∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ ∃ (K : Type) (_ : Field K)
        (_ : Finite K) (σ : K ≃+* K), Nat.card K = (q.p ^ q.exponent) ^ 2 ∧
        (∀ c, σ c = c ^ (q.p ^ q.exponent)) ∧
        ∃ e : CFSG.LieType.SeitzGeneration.Cat d ≃* twistedE6RootGroup K σ,
          E.map (MulAut.congr e).toMonoidHom ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ
    · exact hres ⟨hR, Or.inr (Or.inr (Or.inl ⟨hout, hp3, hmodel, hpar⟩))⟩
    · exact uniSeitzPlanes_twE6_field d p hp hp2 hpd hex E hE hc ⟨hout, hp3, ⟨q, hq, hq2⟩, hmodel⟩
  · exact hres ⟨hR, Or.inr (Or.inr (Or.inr htri))⟩

end Residual

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f
