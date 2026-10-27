module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslMain

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.GLTheoremB

section Lift

variable {Xs T : Type} [Group Xs] [Group T] (π : Xs →* T)

theorem exists_ker_cube [Finite Xs] (hker : π.ker ≤ Subgroup.center Xs)
    (hZ3 : ∀ z ∈ π.ker, z ^ 3 = 1 → z = 1) {z : Xs} (hz : z ∈ π.ker) :
    ∃ w ∈ π.ker, w ^ 3 = z := by
  classical
  let f : ↥π.ker → ↥π.ker := fun w => ⟨(w : Xs) ^ 3, π.ker.pow_mem w.2 3⟩
  have hinj : Function.Injective f := by
    intro w1 w2 h12
    have h12' : (w1 : Xs) ^ 3 = (w2 : Xs) ^ 3 := congrArg Subtype.val h12
    have hc : Commute (w1 : Xs) (w2 : Xs) :=
      (Subgroup.mem_center_iff.mp (hker w1.2) _).symm
    have h1 : ((w1 : Xs) * (w2 : Xs)⁻¹) ^ 3 = 1 := by
      rw [(hc.inv_right).mul_pow, h12', inv_pow, mul_inv_cancel]
    have h2 := hZ3 _ (π.ker.mul_mem w1.2 (π.ker.inv_mem w2.2)) h1
    exact Subtype.ext (mul_inv_eq_one.1 h2)
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨z, hz⟩
  exact ⟨w, w.2, congrArg Subtype.val hw⟩

theorem exists_lift_cube' [Finite Xs] (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Xs) (hZ3 : ∀ z ∈ π.ker, z ^ 3 = 1 → z = 1) {y : T}
    (hy : y ^ 3 = 1) : ∃ b : Xs, π b = y ∧ b ^ 3 = 1 := by
  obtain ⟨b0, rfl⟩ := hπ y
  have h1 : b0 ^ 3 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hy
  obtain ⟨w, hw, hw3⟩ := exists_ker_cube π hker hZ3 (π.ker.inv_mem h1)
  have hwc : Commute w b0 := (Subgroup.mem_center_iff.mp (hker hw) _).symm
  refine ⟨w * b0, ?_, ?_⟩
  · rw [map_mul, (MonoidHom.mem_ker.mp hw), one_mul]
  · rw [hwc.mul_pow, hw3, inv_mul_cancel]

theorem commute_of_lift [Finite Xs] (hker : π.ker ≤ Subgroup.center Xs)
    (hZ3 : ∀ z ∈ π.ker, z ^ 3 = 1 → z = 1) {a b : Xs} (ha3 : a ^ 3 = 1)
    (h : π a * π b = π b * π a) : a * b = b * a := by
  set l : Xs := a * b * a⁻¹ * b⁻¹ with hl
  have hlk : l ∈ π.ker := by
    rw [MonoidHom.mem_ker, hl, map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have hlc : l ∈ Subgroup.center Xs := hker hlk
  have hab : a * b * a⁻¹ = l * b := by rw [hl]; group
  have hconj : ∀ k : ℕ, a ^ k * b * (a ^ k)⁻¹ = l ^ k * b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hc : a * l ^ k = l ^ k * a := Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hlc k) a
      have e : a ^ (k + 1) * b * (a ^ (k + 1))⁻¹ = a * (a ^ k * b * (a ^ k)⁻¹) * a⁻¹ := by
        rw [pow_succ', mul_inv_rev]; group
      rw [e, ih]
      calc a * (l ^ k * b) * a⁻¹ = (a * l ^ k) * b * a⁻¹ := by group
        _ = (l ^ k * a) * b * a⁻¹ := by rw [hc]
        _ = l ^ k * (a * b * a⁻¹) := by group
        _ = l ^ k * (l * b) := by rw [hab]
        _ = l ^ (k + 1) * b := by group
  have h3 := hconj 3
  rw [ha3, inv_one, one_mul, mul_one] at h3
  have hl3 : l ^ 3 = 1 := by
    have : l ^ 3 * b = 1 * b := by rw [← h3, one_mul]
    exact mul_right_cancel this
  have hl1 : l = 1 := hZ3 l hlk hl3
  have : a * b * a⁻¹ = b := by rw [hab, hl1, one_mul]
  calc a * b = a * b * a⁻¹ * a := by group
    _ = b * a := by rw [this]

theorem centralizer_map_eq [Finite Xs] (hker : π.ker ≤ Subgroup.center Xs)
    (hZ3 : ∀ z ∈ π.ker, z ^ 3 = 1 → z = 1) (hπ : Function.Surjective π) {a : Xs}
    (ha3 : a ^ 3 = 1) :
    Subgroup.centralizer ({π a} : Set T) = (Subgroup.centralizer ({a} : Set Xs)).map π := by
  ext z
  constructor
  · intro hz
    obtain ⟨g, rfl⟩ := hπ z
    refine ⟨g, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rw [Subgroup.mem_centralizer_singleton_iff] at hz
    have h' : π a * π g = π g * π a := hz.symm
    exact (commute_of_lift π hker hZ3 ha3 h').symm
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hy]

end Lift

section Shell

variable {Xs T : Type} [Group Xs] [Finite Xs] [Group T] [Finite T]

theorem s1431_false_of_lift_blocks (π : Xs →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Xs) (hZ3 : ∀ z ∈ π.ker, z ^ 3 = 1 → z = 1)
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T))
    {A : Subgroup (MulAut T)} {ψ : MulAut T} {J : Subgroup T} {q : ℕ} (c : S1431Cfg T A ψ J q)
    (hA : ∀ a ∈ A, IsInnerAut a)
    (data : ∀ a : Xs, a ^ 3 = 1 → π a ≠ 1 → ∃ (ι : Type) (_ : Finite ι) (N : ι → Subgroup Xs),
      (∀ i, N i ≤ Subgroup.centralizer ({a} : Set Xs)) ∧
      (∀ i, ∀ g ∈ Subgroup.centralizer ({a} : Set Xs), ∀ m ∈ N i, g * m * g⁻¹ ∈ N i) ∧
      (∀ i, CFSG.IsQuasisimple (N i)) ∧
      (∃ k : ℕ, ∀ g ∈ derivedSeries ↥(Subgroup.centralizer ({a} : Set Xs)) k,
        (g : Xs) ∈ ⨆ i, N i) ∧
      (∀ i, IsTypeL2 q (N i) → ∀ b ∈ Subgroup.centralizer ({a} : Set Xs), b ^ 3 = 1 →
        ∃ s ∈ N i, ∀ m ∈ N i, b * m * b⁻¹ = s * m * s⁻¹)) : False := by
  classical
  refine c.false_of_induced_inner ?_
  intro η hηA hηψ hstab
  obtain ⟨x, hx⟩ := hA ψ c.mem
  obtain ⟨y, hy⟩ := hA η hηA
  have hψ3 : ψ ^ 3 = 1 := c.elemAbelian.2 ψ c.mem
  have hη3 : η ^ 3 = 1 := c.elemAbelian.2 η hηA
  have hx3 : x ^ 3 = 1 := hinj (by rw [map_pow, hx, hψ3, map_one])
  have hy3 : y ^ 3 = 1 := hinj (by rw [map_pow, hy, hη3, map_one])
  have hxy : x * y = y * x := by
    apply hinj
    rw [map_mul, map_mul, hx, hy]
    have := c.elemAbelian.1.is_comm.comm ⟨ψ, c.mem⟩ ⟨η, hηA⟩
    exact congrArg Subtype.val this
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact c.ne_one (by rw [← hx, map_one])
  obtain ⟨a, hax, ha3⟩ := exists_lift_cube' π hπ hker hZ3 hx3
  obtain ⟨b, hby, hb3⟩ := exists_lift_cube' π hπ hker hZ3 hy3
  have hba : b * a = a * b :=
    commute_of_lift π hker hZ3 ha3 (by rw [hax, hby]; exact hxy) |>.symm
  have hπa1 : π a ≠ 1 := by rw [hax]; exact hx1
  set X := Subgroup.centralizer ({π a} : Set T) with hX
  have hψX : fixSub ψ = X := by
    rw [← hx, ← hax, fixSub_conj_eq_centralizer]
  have hJ : GLAPComponent 3 X J := hψX ▸ c.comp
  have hbX : y ∈ X := by
    rw [hX, Subgroup.mem_centralizer_singleton_iff, hax]
    exact hxy.symm
  obtain ⟨ι, hfin, N, hNc, hNn, hNq, hk, key⟩ := data a ha3 hπa1
  set C := Subgroup.centralizer ({a} : Set Xs) with hC
  have hXC : X = C.map π := centralizer_map_eq π hker hZ3 hπ ha3
  let N' : ι → Subgroup T := fun i => (N i).map π
  have hNX : ∀ i, N' i ≤ X := fun i => by
    rw [hXC]
    exact Subgroup.map_mono (hNc i)
  have hNn' : ∀ i, ∀ g ∈ X, ∀ m ∈ N' i, g * m * g⁻¹ ∈ N' i := by
    intro i g hg m hm
    rw [hXC] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    obtain ⟨m0, hm0, rfl⟩ := hm
    exact ⟨g0 * m0 * g0⁻¹, hNn i g0 hg0 m0 hm0, by simp⟩
  have hNq' : ∀ i, CFSG.IsQuasisimple (N' i) := by
    intro i
    refine CFSG.LocalCores.isQuasisimple_map (hNq i) π fun hle => ?_
    have hle' : N i ≤ Subgroup.centralizer (N i : Set Xs) := fun g hg =>
      (Subgroup.mem_centralizer_iff).2 fun h hh => (Subgroup.mem_center_iff.mp (hker (hle hg)) h)
    exact not_le_centralizer_of_isQuasisimple (isQuasisimple_open (hNq i)) hle'
  have hk' : ∃ k : ℕ, ∀ g ∈ derivedSeries ↥X k, (g : T) ∈ ⨆ i, N' i := by
    obtain ⟨k, hk⟩ := hk
    have hmemX : ∀ g : ↥C, π (g : Xs) ∈ X := by
      intro g
      rw [hXC]
      exact ⟨_, g.2, rfl⟩
    let π' : ↥C →* ↥X := (π.comp C.subtype).codRestrict X hmemX
    have hπ's : Function.Surjective π' := by
      intro z
      have hz : (z : T) ∈ C.map π := by
        rw [← hXC]
        exact z.2
      obtain ⟨g, hg, hgz⟩ := hz
      exact ⟨⟨g, hg⟩, Subtype.ext hgz⟩
    refine ⟨k, fun g hg => ?_⟩
    rw [← map_derivedSeries_eq hπ's k] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have hmem := hk g0 hg0
    have h2 : π (g0 : Xs) ∈ (⨆ i, N i).map π := ⟨_, hmem, rfl⟩
    rw [Subgroup.map_iSup] at h2
    exact h2
  have hb : ∀ i, barX 3 X (N' i) = barX 3 X J →
      ∃ m ∈ N' i, ∃ g ∈ X, (∀ m' ∈ N' i, g * m' = m' * g) ∧ y = m * g := by
    intro i hi
    have hT' : IsTypeL2 q ↥(N' i) :=
      isTypeL2_of_barX_eq hJ (hNX i) (hNn' i) (hNq' i) hi.symm c.typeL2
    have hT : IsTypeL2 q ↥(N i) := by
      refine (isTypeL2_congr_of_central (hNq i).1 (π.subgroupMap (N i))
        (π.subgroupMap_surjective (N i)) ?_).2 hT'
      intro g hg
      rw [MonoidHom.mem_ker] at hg
      have hg1 : π (g : Xs) = 1 := congrArg Subtype.val hg
      have hgc : (g : Xs) ∈ Subgroup.center Xs := hker hg1
      rw [Subgroup.mem_center_iff]
      intro g'
      exact Subtype.ext ((Subgroup.mem_center_iff.mp hgc) g')
    have hbC : b ∈ C := by
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      exact hba
    obtain ⟨s, hs, hsm⟩ := key i hT b hbC hb3
    refine ⟨π s, ⟨s, hs, rfl⟩, (π s)⁻¹ * y, ?_, ?_, ?_⟩
    · exact X.mul_mem (X.inv_mem (hNX i ⟨s, hs, rfl⟩)) hbX
    · rintro _ ⟨m0, hm0, rfl⟩
      have h2 : π b * π m0 * (π b)⁻¹ = π s * π m0 * (π s)⁻¹ := by
        have := congrArg π (hsm m0 hm0)
        simpa only [map_mul, map_inv] using this
      rw [hby] at h2
      calc (π s)⁻¹ * y * π m0 = (π s)⁻¹ * (y * π m0 * y⁻¹) * y := by group
        _ = (π s)⁻¹ * (π s * π m0 * (π s)⁻¹) * y := by rw [h2]
        _ = π m0 * ((π s)⁻¹ * y) := by group
    · rw [mul_inv_cancel_left]
  obtain ⟨j₀, hj₀, hbj⟩ := exists_inner_of_blocks hJ N' hNX hNn' hNq' hk' hbX hb
  subst hy
  exact isInnerAut_inducedBarHom_of_barX hJ hbX hstab hj₀ hbj

end Shell

end CFSG.HardMathSupport.Dickson.Sec6.I1431
