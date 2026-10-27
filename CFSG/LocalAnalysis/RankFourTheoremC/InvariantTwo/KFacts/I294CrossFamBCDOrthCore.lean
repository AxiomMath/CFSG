module

public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup Matrix CFSG.ClassicalGroups.Orthogonal

section Restrict

variable {M₀ : Type} [Group M₀] [Finite M₀] {p : ℕ} [hp : Fact p.Prime]

theorem restrict_isMulCommutative (M' : Subgroup M₀)
    (hM₀ : ∀ P : Subgroup M₀, IsPGroup p P → IsMulCommutative P) :
    ∀ P : Subgroup M', IsPGroup p P → IsMulCommutative P := fun P hP =>
  isMulCommutative_of_map_injective M'.subtype M'.subtype_injective (hM₀ _ (hP.map _))

theorem restrict_le_pRank (M' : Subgroup M₀) (hcont : ∀ g : M₀, g ^ p = 1 → g ∈ M') {d : ℕ}
    (hd : d ≤ CFSG.Open.pRank p (⊤ : Subgroup M₀)) :
    d ≤ CFSG.Open.pRank p (⊤ : Subgroup M') := by
  obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.out.one_lt (⊤ : Subgroup M₀)
  have hEM : E ≤ M' := fun x hx => hcont x (hE.2 x hx)
  obtain ⟨F, hF, hFcard, -⟩ := exists_isElemAbelian_subgroupOf hE M'
  have hFE : Nat.card F = p ^ CFSG.Open.pRank p (⊤ : Subgroup M₀) := by
    rw [hFcard, inf_eq_left.2 hEM, hEcard]
  exact hd.trans (CFSG.SectionRank.le_pRank hp.out.one_lt le_top hF hFE)

theorem restrict_centralizer (M' : Subgroup M₀) (hcont : ∀ g : M₀, g ^ p = 1 → g ∈ M')
    (hbig : ∀ y₀ : M₀, y₀ ^ p = 1 → 3 ≤ CFSG.Open.pRank p (centralizer ({y₀} : Set M₀))) :
    ∀ y : M', y ^ p = 1 → 3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set M')) := by
  intro y hy
  have hy' : (y : M₀) ^ p = 1 := by simpa using congrArg Subtype.val hy
  obtain ⟨E, hEle, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.out.one_lt
    (centralizer ({(y : M₀)} : Set M₀))
  have hEM : E ≤ M' := fun x hx => hcont x (hE.2 x hx)
  obtain ⟨F, hF, hFcard, hFmem⟩ := exists_isElemAbelian_subgroupOf hE M'
  have hFC : F ≤ centralizer ({y} : Set M') := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hEle ((hFmem f).1 hf)
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact Subtype.ext this
  have hFcard' : Nat.card F = p ^ CFSG.Open.pRank p (centralizer ({(y : M₀)} : Set M₀)) := by
    rw [hFcard, inf_eq_left.2 hEM, hEcard]
  exact (hbig _ hy').trans (CFSG.SectionRank.le_pRank hp.out.one_lt hFC hF hFcard')

theorem not_dvd_index_of_contains_pElements (M' : Subgroup M₀)
    (hcont : ∀ g : M₀, (∃ k : ℕ, g ^ (p ^ k) = 1) → g ∈ M') : ¬ p ∣ M'.index := by
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p M₀))
  have hSM : (S : Subgroup M₀) ≤ M' := fun x hx => hcont x (by
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩)
  have h1 := Subgroup.relIndex_mul_index hSM
  intro hd
  apply S.not_dvd_index
  rw [← h1]
  exact Dvd.dvd.mul_left hd _

end Restrict

section Isometry

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}

theorem isometry_of_mem_statedOmega (hQ : ⇑Q = Q₀) {g : GL ι K} (hg : g ∈ StatedOmega Q₀)
    (v : ι → K) :
    Q₀ ((g : Matrix ι ι K) *ᵥ v) = Q₀ v := by
  rw [statedOmega_eq_comap hQ, Subgroup.mem_comap] at hg
  have h1 : toLinEquiv ι K g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    have : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
        TauCeti.QuadraticMap.orthogonalGroup Q := Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
    exact this hg
  have := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 h1 v
  rw [toLinEquiv_apply, hQ] at this
  exact this

theorem sq_mem_statedOmega (hQ : ⇑Q = Q₀)
    (hab : CFSG.IsElementaryAbelian 2 (Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q)))
    {g : GL ι K} (hg : ∀ v, Q₀ ((g : Matrix ι ι K) *ᵥ v) = Q₀ v) : g ^ 2 ∈ StatedOmega Q₀ := by
  have hmem : g ∈ Subgroup.closure {A : GL ι K | ∀ v, Q₀ ((A : Matrix ι ι K) *ᵥ v) = Q₀ v} :=
    Subgroup.subset_closure hg
  rw [closure_isometries_eq_comap hQ, Subgroup.mem_comap] at hmem
  set x : TauCeti.QuadraticMap.orthogonalGroup Q := ⟨toLinEquiv ι K g, hmem⟩ with hx
  have h1 : Abelianization.of x ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (CFSG.IsElementaryAbelian.exponent_dvd_p 2 _) _
  rw [← map_pow] at h1
  have h1' : x ^ 2 ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact h1
  have h2 : toLinEquiv ι K g ^ 2 ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    have h1'' : x ^ 2 ∈ ⁅(⊤ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)), ⊤⁆ := h1'
    have h3 := Subgroup.mem_map_of_mem (TauCeti.QuadraticMap.orthogonalGroup Q).subtype h1''
    rw [Subgroup.map_commutator] at h3
    have htop : (⊤ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)).map
        (TauCeti.QuadraticMap.orthogonalGroup Q).subtype =
        TauCeti.QuadraticMap.orthogonalGroup Q := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [htop] at h3
    simpa using h3
  rw [statedOmega_eq_comap hQ, Subgroup.mem_comap]
  simpa using h2

theorem mem_statedOmega_of_pow_eq_one (hQ : ⇑Q = Q₀)
    (hab : CFSG.IsElementaryAbelian 2 (Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q)))
    {p : ℕ} (hp2 : Odd p) {g : GL ι K} (hg : ∀ v, Q₀ ((g : Matrix ι ι K) *ᵥ v) = Q₀ v) {k : ℕ}
    (hk : g ^ (p ^ k) = 1) : g ∈ StatedOmega Q₀ := by
  have hodd : Odd (p ^ k) := hp2.pow
  obtain ⟨m, hm⟩ := hodd
  have hg2 := sq_mem_statedOmega hQ hab hg
  have : g = (g ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = p ^ k + 1 by omega, pow_succ, hk, one_mul]
  rw [this]
  exact Subgroup.pow_mem _ hg2 _

theorem sq_eq_one_of_scalar_isometry (hhom : ∀ (c : K) (w : ι → K), Q₀ (c • w) = c ^ 2 * Q₀ w)
    {w₀ : ι → K} (hw₀ : Q₀ w₀ = 1) (c : Kˣ)
    (hc : ∀ v, Q₀ (((Matrix.GeneralLinearGroup.scalar ι c : GL ι K) : Matrix ι ι K) *ᵥ v) =
      Q₀ v) : c ^ 2 = 1 := by
  have h1 := hc w₀
  have h2 : ((Matrix.GeneralLinearGroup.scalar ι c : GL ι K) : Matrix ι ι K) *ᵥ w₀ =
      (c : K) • w₀ := by
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  rw [h2, hhom, hw₀, mul_one] at h1
  exact Units.ext (by simpa using h1)

end Isometry

end CFSG.LocalAnalysis.RankFourTheoremC
