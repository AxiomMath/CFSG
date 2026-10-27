module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4OrthCent
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Main

public section

namespace CFSG.ComponentClassification.Sol76T13.Hq4

open CFSG Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.GH74.Filter
open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Steinberg.CentralExt
open scoped IsMulCommutative

@[expose] noncomputable def twoPowProdHom {C : Type*} [CommGroup C] {r : ℕ} (v : Fin r → C)
    (hv : ∀ i, v i ^ 2 = 1) : (Fin r → Multiplicative (ZMod 2)) →* C where
  toFun a := ∏ i, v i ^ (Multiplicative.toAdd (a i)).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.mul_apply, toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ (hv i), pow_add]

theorem pow_dvd_card_centralizer_of_commuting_involutions {P : Type*} [Group P] [Finite P]
    {r : ℕ} (u : Fin r → P) (hsq : ∀ i, u i ^ 2 = 1) (hcomm : ∀ i j, Commute (u i) (u j))
    (hker : ∀ a : Fin r → Fin 2, a ≠ 0 → (List.ofFn fun i => u i ^ (a i : ℕ)).prod ≠ 1)
    {s : P} (hs : ∀ i, u i * s = s * u i) :
    2 ^ r ∣ Nat.card (centralizer ({s} : Set P)) := by
  set C := Subgroup.closure (Set.range u)
  have : IsMulCommutative C := Subgroup.isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hcomm i j)
  let v : Fin r → C := fun i => ⟨u i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hv : ∀ i, v i ^ 2 = 1 := fun i => Subtype.ext (by simpa [v] using hsq i)
  let φ : (Fin r → Multiplicative (ZMod 2)) →* P := C.subtype.comp (twoPowProdHom v hv)
  have hφ : ∀ a, φ a = (List.ofFn fun i => u i ^ (Multiplicative.toAdd (a i)).val).prod := by
    intro a
    simp only [φ, MonoidHom.comp_apply, twoPowProdHom, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
    rfl
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, hφ] at ha
    rw [Subgroup.mem_bot]
    by_contra hne
    refine hker (fun i => Multiplicative.toAdd (a i)) (fun h0 => hne ?_) ha
    funext i
    exact Multiplicative.toAdd.injective (congrFun h0 i)
  have hle : φ.range ≤ centralizer ({s} : Set P) := by
    rintro _ ⟨a, rfl⟩
    have hCle : C ≤ centralizer ({s} : Set P) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact mem_centralizer_singleton_iff.mpr (hs i)
    exact hCle (twoPowProdHom v hv a).2
  have hcard : Nat.card φ.range = 2 ^ r := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, card_pi_zmod_two]
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hle

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem fourCommuting_of_sq_scalar [Fintype K] [DecidableEq K] [FiniteDimensional K V]
    (h2 : (2 : K) ≠ 0) (hnd : ∀ v, (∀ w, polar Q v w = 0) → v = 0)
    (hdim : 8 ≤ Module.finrank K V) {g : V ≃ₗ[K] V}
    (hgΩ : g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hg2 : g * g ∈ scalars K V) : FourCommuting Q g := by
  have hle : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hle hgΩ
  obtain ⟨c, hc⟩ := mem_scalars.mp hg2
  obtain ⟨-, v, hv, -⟩ := exists_orth_of_lt_finrank (x := (Fin.elim0 : Fin 0 → V)) h2 hnd
    ⟨fun i => i.elim0, fun i => i.elim0⟩ (by rw [Fintype.card_fin]; omega)
  have hc2 : c ^ 2 = 1 := by
    have h := map_of_mem (Subgroup.mul_mem _ hg hg) v
    rw [hc v, map_smul_eq_sq] at h
    exact (mul_eq_right₀ hv).mp h
  rw [pow_two] at hc2
  rcases mul_self_eq_one_iff.mp hc2 with rfl | rfl
  · exact fourCommuting_of_sq_one h2 hnd hdim hg (LinearEquiv.ext fun w => by
      rw [hc w, one_smul]; rfl)
  · exact fourCommuting_of_sq_neg_one h2 hnd hdim hg hgΩ (fun w => by
      rw [← LinearEquiv.mul_apply, hc w, neg_one_smul])

theorem pow_four_dvd_card_centralizer_statedProj {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Fintype K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
    {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    (hnd : ∀ v, (∀ w, polar Q v w = 0) → v = 0) (hdim : 8 ≤ Fintype.card ι)
    {s : StatedProj (StatedOmega Q₀)} (hs2 : s * s = 1) :
    2 ^ 4 ∣ Nat.card (centralizer ({s} : Set (StatedProj (StatedOmega Q₀)))) := by
  classical
  have hΩ := statedOmega_eq_comap hQ
  set N := (StatedScalars ι K).subgroupOf (StatedOmega Q₀) with hN
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective N s
  let Φ : StatedOmega Q₀ →* ((ι → K) ≃ₗ[K] (ι → K)) :=
    (toLinEquiv ι K).toMonoidHom.comp (StatedOmega Q₀).subtype
  have hΦinj : Function.Injective Φ := (toLinEquiv ι K).injective.comp Subtype.val_injective
  have hΦmem : ∀ B : StatedOmega Q₀, Φ B ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    fun B => Subgroup.mem_comap.mp ((congrArg (fun H => (B : GL ι K) ∈ H) hΩ).mp B.2)
  have hscal : ∀ B : StatedOmega Q₀, QuotientGroup.mk' N B = 1 ↔ Φ B ∈ scalars K (ι → K) := by
    intro B
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf,
      mem_statedScalars_iff]
    rfl
  have hg2 : Φ A * Φ A ∈ scalars K (ι → K) := by
    rw [← map_mul, ← hscal, map_mul]
    exact hs2
  have hfin : Module.finrank K (ι → K) = Fintype.card ι := Module.finrank_fintype_fun_eq_card K
  obtain ⟨u, huΩ, husq, hucomm, hug, huind⟩ :=
    fourCommuting_of_sq_scalar h2 hnd (by rw [hfin]; exact hdim) (hΦmem A) hg2
  have hmem : ∀ k, (toLinEquiv ι K).symm (u k) ∈ StatedOmega Q₀ := fun k =>
    (congrArg (fun H => (toLinEquiv ι K).symm (u k) ∈ H) hΩ).mpr
      (Subgroup.mem_comap.mpr (by simpa using huΩ k))
  let x : Fin 4 → StatedOmega Q₀ := fun k => ⟨(toLinEquiv ι K).symm (u k), hmem k⟩
  have hΦx : ∀ k, Φ (x k) = u k := fun k => (toLinEquiv ι K).apply_symm_apply (u k)
  refine pow_dvd_card_centralizer_of_commuting_involutions
    (fun k => QuotientGroup.mk' N (x k)) (fun k => ?_) (fun i j => ?_) (fun a ha hone => ?_)
    (fun k => ?_)
  · rw [← map_pow, pow_two, hscal, map_mul, hΦx]
    exact husq k
  · change QuotientGroup.mk' N (x i) * QuotientGroup.mk' N (x j) =
      QuotientGroup.mk' N (x j) * QuotientGroup.mk' N (x i)
    rw [← map_mul, ← map_mul]
    exact congrArg _ (hΦinj (by rw [map_mul, map_mul, hΦx, hΦx, hucomm]))
  · apply huind a ha
    have h1 : QuotientGroup.mk' N (List.ofFn fun i => x i ^ (a i : ℕ)).prod = 1 := by
      rw [map_list_prod, List.map_ofFn]
      simpa [Function.comp_def, map_pow] using hone
    rw [hscal, map_list_prod, List.map_ofFn] at h1
    simpa [Function.comp_def, map_pow, hΦx] using h1
  · rw [← map_mul, ← map_mul]
    exact congrArg _ (hΦinj (by rw [map_mul, map_mul, hΦx, hug]))

theorem pOmegaPlusCentralizerInput : POmegaPlusCentralizerInput := by
  intro S _ _ n p f hp2 _ hL s hs2 _
  classical
  obtain ⟨⟨hp, -, hn4⟩, K, _, _, hK, ⟨e⟩⟩ :=
    GriessNative.classical_of_lieModel (t := .POmegaPlus) hL (by decide)
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := SectionRank.ClassicalOdd.charP_of_card hK
  have := Fintype.ofFinite K
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP p hp2
  have hnd : ∀ v, (∀ w, polar (LieType.Universal.Spin.quadPlus n K) v w = 0) → v = 0 :=
    fun v hv => by
      ext x
      rcases x with j | j
      · rw [Pi.zero_apply, ← LieType.Universal.Spin.polar_quadPlus_single_inr n K v j]
        exact hv _
      · rw [Pi.zero_apply, ← LieType.Universal.Spin.polar_quadPlus_single_inl n K v j]
        exact hv _
  rw [card_centralizer_mulEquiv e]
  exact pow_four_dvd_card_centralizer_statedProj h2 (LieType.Universal.Spin.coe_quadPlus n K) hnd
    (by rw [Fintype.card_sum, Fintype.card_fin]; omega)
    (by rw [← map_mul, hs2, map_one])

end CFSG.ComponentClassification.Sol76T13.Hq4
