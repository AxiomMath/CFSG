module

public import CFSG.LocalAnalysis.GL83PartI.I_33
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCSymplecticCore
public import CFSG.LocalAnalysis.SteinbergBKSolvableQuaternionWitness
public import CFSG.LocalAnalysis.LargeEvenClassification.RankOneAction
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.P55.I336

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem twoRank_le_one {Y : Subgroup G}
    (h : ∀ U : Subgroup G, U ≤ Y → IsElemAbelian 2 U → Nat.card U ≤ 2) : twoRank ↥Y ≤ 1 := by
  apply csSup_le'
  rintro k ⟨E, -, hE, hcard⟩
  have h1 := h (E.map Y.subtype) (Subgroup.map_subtype_le E)
    (CFSG.Open.IsElemAbelian.map hE Y.subtype)
  rw [Subgroup.card_map_of_injective Y.subtype_injective, hcard] at h1
  by_contra hk
  have h2 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem cyclic_or_quaternion {Y : Subgroup G} (hY2 : IsPGroup 2 Y)
    (h : ∀ U : Subgroup G, U ≤ Y → IsElemAbelian 2 U → Nat.card U ≤ 2) :
    IsCyclic Y ∨ ∃ n : ℕ, 3 ≤ n ∧ Nonempty (Y ≃* QuaternionGroup (2 ^ (n - 2))) :=
  CFSG.TwoRankLowerBound.Helpers.rank_one_two_group_cyclic_or_quaternion ↥Y hY2
    (twoRank_le_one h)

theorem isCyclic_of_isMulCommutative {Y X : Subgroup G} (hY2 : IsPGroup 2 Y)
    (h : ∀ U : Subgroup G, U ≤ Y → IsElemAbelian 2 U → Nat.card U ≤ 2) (hXY : X ≤ Y)
    (hX : IsMulCommutative X) : IsCyclic X := by
  haveI : IsMulCommutative (X.subgroupOf Y) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (by
      have := hX.is_comm.comm ⟨a.1, a.2⟩ ⟨b.1, b.2⟩
      simpa using congrArg Subtype.val this))⟩⟩
  have hc := CFSG.TwoRankLowerBound.Helpers.abelian_subgroup_of_rank_one_two_group_isCyclic
    ↥Y hY2 (twoRank_le_one h) (X.subgroupOf Y)
  exact (Subgroup.subgroupOfEquivOfLe hXY).isCyclic.mp hc

theorem le_normalizer_of_forall_mem {B S : Subgroup G} (h : ∀ g ∈ B, ∀ y ∈ S, g * y * g⁻¹ ∈ S) :
    B ≤ Subgroup.normalizer (S : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h g hg y hy, fun hy => ?_⟩
  have := h g⁻¹ (B.inv_mem hg) _ hy
  simpa [mul_assoc] using this

theorem mul_conj_comm {a d x : G} (had : a * d = d * a) (hxa : a * x = x * a) :
    a * (d * x * d⁻¹) = d * x * d⁻¹ * a := by
  have hinv : a * d⁻¹ = d⁻¹ * a := by
    calc a * d⁻¹ = d⁻¹ * (d * a) * d⁻¹ := by group
      _ = d⁻¹ * (a * d) * d⁻¹ := by rw [had]
      _ = d⁻¹ * a := by group
  calc a * (d * x * d⁻¹) = (a * d) * x * d⁻¹ := by group
    _ = d * a * x * d⁻¹ := by rw [had]
    _ = d * (a * x) * d⁻¹ := by group
    _ = d * (x * a) * d⁻¹ := by rw [hxa]
    _ = d * x * (a * d⁻¹) := by group
    _ = d * x * (d⁻¹ * a) := by rw [hinv]
    _ = d * x * d⁻¹ * a := by group

theorem exists_fixed_mem_coset {p : ℕ} (hp : p.Prime) {A N : Subgroup G} (hA : IsPGroup p A)
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hN : ¬ p ∣ Nat.card N) {y : G}
    (hy : ∀ a ∈ A, y⁻¹ * (a * y * a⁻¹) ∈ N) :
    ∃ n ∈ N, y * n ∈ Subgroup.centralizer (A : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmem : ∀ (a : A) (n : N), y⁻¹ * ((a : G) * (y * n) * (a : G)⁻¹) ∈ N := by
    intro a n
    have e : y⁻¹ * ((a : G) * (y * n) * (a : G)⁻¹) =
        (y⁻¹ * (a * y * (a : G)⁻¹)) * (a * n * (a : G)⁻¹) := by group
    rw [e]
    exact N.mul_mem (hy a a.2) ((Subgroup.mem_normalizer_iff.mp (hAN a.2) n).mp n.2)
  letI : MulAction A N :=
    { smul := fun a n => ⟨y⁻¹ * ((a : G) * (y * n) * (a : G)⁻¹), hmem a n⟩
      one_smul := fun n => Subtype.ext (by
        show y⁻¹ * (((1 : A) : G) * (y * n) * ((1 : A) : G)⁻¹) = n
        simp)
      mul_smul := fun a b n => Subtype.ext (by
        show y⁻¹ * (((a * b : A) : G) * (y * n) * ((a * b : A) : G)⁻¹) =
          y⁻¹ * ((a : G) * (y * (y⁻¹ * ((b : G) * (y * n) * (b : G)⁻¹))) * (a : G)⁻¹)
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group) }
  obtain ⟨n, hn⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card N hN
  refine ⟨n, n.2, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
  have h := MulAction.mem_fixedPoints.mp hn ⟨a, ha⟩
  have h2 : y⁻¹ * (a * (y * n) * a⁻¹) = n := congrArg Subtype.val h
  have h3 : a * (y * n) * a⁻¹ = y * n := by
    calc a * (y * n) * a⁻¹ = y * (y⁻¹ * (a * (y * n) * a⁻¹)) := by group
      _ = y * n := by rw [h2]
  calc a * (y * n) = a * (y * n) * a⁻¹ * a := by group
    _ = y * n * a := by rw [h3]

theorem conjAut_pow_eq_one {X : Subgroup G} {d : G} (hd : d ∈ Subgroup.normalizer (X : Set G))
    {n : ℕ} (hdn : d ^ n = 1) : (X.normalizerMonoidHom ⟨d, hd⟩) ^ n = 1 := by
  rw [← map_pow]
  have : (⟨d, hd⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ n = 1 :=
    Subtype.ext (by simpa using hdn)
  rw [this, map_one]

theorem cyclic_two_group_centralized {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup G}
    (hX2 : IsPGroup 2 X) (hXc : IsCyclic X) {d : G}
    (hd : d ∈ Subgroup.normalizer (X : Set G)) (hdp : d ^ p = 1) {x : G} (hx : x ∈ X) :
    d * x * d⁻¹ = x := by
  haveI := hXc
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have h1 := CFSG.LocalAnalysis.GorensteinLyons.mulAut_eq_one_of_odd hX2 hodd
    (conjAut_pow_eq_one hd hdp)
  have h2 := congrArg (fun f : MulAut ↥X => ((f ⟨x, hx⟩ : ↥X) : G)) h1
  simpa using h2

theorem centralized_of_isPGroup_mulAut {p : ℕ} (hp2 : p ≠ 2) (hp : p.Prime) {Y : Subgroup G}
    (hA : IsPGroup 2 (MulAut ↥Y)) {d : G} (hd : d ∈ Subgroup.normalizer (Y : Set G))
    (hdp : d ^ p = 1) {y : G} (hy : y ∈ Y) : d * y * d⁻¹ = y := by
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  obtain ⟨k, hk⟩ := hA (Y.normalizerMonoidHom ⟨d, hd⟩)
  have h1 := CFSG.LocalAnalysis.GorensteinLyons.eq_one_of_pow_two_pow_of_pow_odd hk hodd
    (conjAut_pow_eq_one hd hdp)
  have h2 := congrArg (fun f : MulAut ↥Y => ((f ⟨y, hy⟩ : ↥Y) : G)) h1
  simpa using h2

theorem quat_of_action {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y D : Subgroup G}
    (hY2 : IsPGroup 2 Y) (hrk : ∀ U : Subgroup G, U ≤ Y → IsElemAbelian 2 U → Nat.card U ≤ 2)
    (hD : IsElemAbelian p D) (hDY : D ≤ Subgroup.normalizer (Y : Set G))
    (hYD : (⁅Y, D⁆ : Subgroup G) ≠ ⊥) :
    p = 3 ∧ Nonempty (Y ≃* QuaternionGroup 2) := by
  have hnt : ∃ d ∈ D, ∃ y ∈ Y, d * y * d⁻¹ ≠ y := by
    by_contra hcon
    push Not at hcon
    apply hYD
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h := hcon d hd y hy
    calc d * y = d * y * d⁻¹ * d := by group
      _ = y * d := by rw [h]
  obtain ⟨d, hd, y, hy, hne⟩ := hnt
  have hdn : d ∈ Subgroup.normalizer (Y : Set G) := hDY hd
  set σ : MulAut ↥Y := Y.normalizerMonoidHom ⟨d, hdn⟩ with hσ
  have hσp : σ ^ p = 1 := conjAut_pow_eq_one hdn (hD.2 d hd)
  have hσ1 : σ ≠ 1 := by
    intro h1
    have h2 := congrArg (fun f : MulAut ↥Y => ((f ⟨y, hy⟩ : ↥Y) : G)) h1
    apply hne
    simpa [hσ] using h2
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf σ = p := orderOf_eq_prime hσp hσ1
  have hdvd : p ∣ Nat.card (MulAut ↥Y) := hord ▸ orderOf_dvd_natCard σ
  have hp3 : p = 3 := by
    rcases CFSG.LargeEvenClassification.Helpers.rank_one_two_group_aut_prime_support_exact hY2
      (twoRank_le_one hrk) hp hdvd with h | h
    · exact absurd h hp2
    · exact h
  refine ⟨hp3, ?_⟩
  rcases cyclic_or_quaternion hY2 hrk with hcyc | ⟨n, hn3, ⟨e⟩⟩
  · exact absurd (cyclic_two_group_centralized hp hp2 hY2 hcyc hdn (hD.2 d hd) hy) hne
  · by_cases hn : n = 3
    · subst hn
      exact ⟨e⟩
    · exfalso
      have hk : 2 ≤ n - 2 := by omega
      have hA : IsPGroup 2 (MulAut ↥Y) :=
        (CFSG.LocalAnalysis.SteinbergBK.isPGroup_mulAut_quaternionGroup hk).of_equiv
          (MulAut.congr e).symm
      exact hne (centralized_of_isPGroup_mulAut hp2 hp hA hdn (hD.2 d hd) hy)

theorem card_mul_eq_of_index_eq {p : ℕ} {D₀ D : Subgroup G} (h : D₀ ≤ D)
    (hi : (D₀.subgroupOf D).index = p) : Nat.card D₀ * p = Nat.card D := by
  have h1 := Subgroup.card_mul_index (D₀.subgroupOf D)
  have h2 : Nat.card (D₀.subgroupOf D) = Nat.card D₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  rw [h2, hi] at h1
  exact h1

theorem abelian_le_centralizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T D : Subgroup G}
    (hT : IsPGroup 2 T) (hD : IsElemAbelian p D) (hDne : D ≠ ⊥)
    (hDT : D ≤ Subgroup.normalizer (T : Set G))
    (hrk : ∀ D₀ : Subgroup G, D₀ ≤ D → Nat.card D₀ * p = Nat.card D →
      (⁅T ⊓ Subgroup.centralizer (D₀ : Set G), D⁆ : Subgroup G) ≠ ⊥ →
      ∀ U : Subgroup G, U ≤ T ⊓ Subgroup.centralizer (D₀ : Set G) → IsElemAbelian 2 U →
        Nat.card U ≤ 2)
    {R : Subgroup G} (hRT : R ≤ T) (hR : IsMulCommutative R)
    (hDR : D ≤ Subgroup.normalizer (R : Set G)) :
    R ≤ Subgroup.centralizer (D : Set G) := by
  have hR2 : IsPGroup 2 R := hT.to_le hRT
  refine (GL83.le_iSup_hyperplane hp hp2 hDne hD hR2 hDR).trans (iSup₂_le fun A hA => ?_)
  have hAcard : Nat.card A * p = Nat.card D := card_mul_eq_of_index_eq hA.1 hA.2
  by_cases hc : (⁅T ⊓ Subgroup.centralizer (A : Set G), D⁆ : Subgroup G) = ⊥
  · exact (inf_le_inf_right _ hRT).trans
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc).trans le_rfl)
  · have hrank := hrk A hA.1 hAcard hc
    set X : Subgroup G := R ⊓ Subgroup.centralizer (A : Set G) with hX
    have hXab : IsMulCommutative X :=
      ⟨⟨fun a b => Subtype.ext (by
        have := hR.is_comm.comm ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩
        simpa using congrArg Subtype.val this)⟩⟩
    have hXT : X ≤ T ⊓ Subgroup.centralizer (A : Set G) := inf_le_inf_right _ hRT
    have hXcyc : IsCyclic X :=
      isCyclic_of_isMulCommutative (hT.to_le inf_le_left) hrank hXT hXab
    have hX2 : IsPGroup 2 X := hT.to_le (hXT.trans inf_le_left)
    have hDX : D ≤ Subgroup.normalizer (X : Set G) := by
      refine le_normalizer_of_forall_mem fun d hd x hx => ?_
      obtain ⟨hxR, hxA⟩ := hx
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hDR hd) x).mp hxR, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have had : a * d = d * a := CFSG.Open.IsElemAbelian.comm hD (hA.1 ha) hd
      have hxa : a * x = x * a := Subgroup.mem_centralizer_iff.mp hxA a ha
      exact mul_conj_comm had hxa
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have := cyclic_two_group_centralized hp hp2 hX2 hXcyc (hDX hd) (hD.2 d hd) hx
    calc d * x = d * x * d⁻¹ * d := by group
      _ = x * d := by rw [this]

end CFSG.LocalAnalysis.GLTheoremA.P55.I336
