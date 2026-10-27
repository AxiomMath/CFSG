module

public import CFSG.RankThree.PartOne.KF.ClsSUUpper
import CFSG.RankThree.PartOne.KF.ClsSpUpper
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperShared

public section

namespace CFSG.RankThree.PartOne.KFU

open Module CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank Polynomial
open CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix
open CFSG.Assembly.RankThreeEven (localRank)

variable {K : Type} [Field K] [Finite K]

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem card_le_pow_card_of_injective_rootsOfUnity {G α : Type*} [Finite G] [Fintype α] {p : ℕ}
    [NeZero p] (φ : G → α → K) (hφ : Function.Injective φ)
    (hroot : ∀ g a, φ g a ^ p = 1) : Nat.card G ≤ p ^ Fintype.card α := by
  classical
  set S : Finset K := (Polynomial.nthRoots p (1 : K)).toFinset
  have hS : S.card ≤ p :=
    Multiset.toFinset_card_le _ |>.trans (Polynomial.card_nthRoots p 1)
  let ψ : G → (α → S) := fun g a =>
    ⟨φ g a, by
      rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (Nat.pos_of_ne_zero (NeZero.ne p))]
      exact hroot g a⟩
  have hψ : Function.Injective ψ := fun g g' h =>
    hφ (funext fun a => congrArg Subtype.val (congrFun h a))
  calc Nat.card G ≤ Nat.card (α → S) := Nat.card_le_card_of_injective ψ hψ
    _ = S.card ^ Fintype.card α := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_coe]
    _ ≤ p ^ Fintype.card α := Nat.pow_le_pow_left hS _

theorem commutative_det_one_card_le_pow_sub_two_of_fixed {p : ℕ} [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (E : Subgroup (V ≃ₗ[K] V))
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ p = 1)
    (hdet : ∀ g ∈ E, LinearMap.det ((g : V ≃ₗ[K] V) : V →ₗ[K] V) = 1)
    {v₀ : V} (hv₀ : v₀ ≠ 0) (hfix : ∀ g ∈ E, ((g : V ≃ₗ[K] V) : V →ₗ[K] V) v₀ = v₀) :
    Nat.card E ≤ p ^ (finrank K V - 2) := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun f : V ≃ₗ[K] V => (f : V → V)) DFunLike.coe_injective
  haveI : Finite E := Subtype.finite
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let f : E → End K V := fun g => ((g : V ≃ₗ[K] V) : V →ₗ[K] V)
  have hfcomm : ∀ i j : E, Commute (f i) (f j) := fun i j => by
    have h2 : (i * j : E) = (j * i : E) := Subtype.ext (hcomm i i.2 j j.2)
    apply LinearMap.ext
    intro v
    calc (f i * f j) v = ((i * j : E) : V →ₗ[K] V) v := rfl
      _ = ((j * i : E) : V →ₗ[K] V) v := by rw [h2]
      _ = (f j * f i) v := rfl
  have hfpow : ∀ i : E, f i ^ p = 1 := fun i => by
    rw [← CFSG.RankThree.PartOne.LIT.coe_pow_eq, hexp i i.2]
    rfl
  obtain ⟨b, μ, hb⟩ := exists_basis_common_eigenvectors_of_pow_eq_one hζ f hfcomm hfpow
  have hinj : Function.Injective (fun g : E => fun j => μ g j) := by
    intro g h hgh
    have h1 : f g = f h := by
      apply b.ext
      intro j
      have hgh' : μ g j = μ h j := congrFun hgh j
      rw [hb g j, hb h j, hgh']
    exact Subtype.ext (LinearEquiv.ext fun v => LinearMap.congr_fun h1 v)
  have hroot : ∀ g : E, ∀ j, μ g j ^ p = 1 := by
    intro g j
    have key : ∀ k : ℕ, (f g ^ k) (b j) = (μ g j) ^ k • b j := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, Module.End.mul_apply, hb g j, map_smul, ih, smul_smul, ← pow_succ']
    have h2 : (f g ^ p) (b j) = b j := by rw [hfpow g, Module.End.one_apply]
    rw [key p] at h2
    have h3 : ((μ g j) ^ p - 1) • b j = 0 := by rw [sub_smul, h2, one_smul, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right (b.ne_zero j))
  have hprod : ∀ g : E, ∏ j, μ g j = 1 := by
    intro g
    have hmat : LinearMap.toMatrix b b (f g) = Matrix.diagonal (fun j => μ g j) := by
      ext i j
      rw [LinearMap.toMatrix_apply, hb g j]
      by_cases hij : i = j
      · subst hij; simp [Matrix.diagonal]
      · simp [Matrix.diagonal, hij, Pi.smul_apply]
    calc ∏ j, μ g j = (Matrix.diagonal (fun j => μ g j)).det := Matrix.det_diagonal.symm
      _ = (LinearMap.toMatrix b b (f g)).det := by rw [hmat]
      _ = LinearMap.det ((g : V ≃ₗ[K] V) : V →ₗ[K] V) := LinearMap.det_toMatrix b (f g)
      _ = 1 := hdet g g.2
  have hmatg : ∀ g : E, LinearMap.toMatrix b b (f g) = Matrix.diagonal (fun j => μ g j) := by
    intro g
    ext i j
    rw [LinearMap.toMatrix_apply, hb g j]
    by_cases hij : i = j
    · subst hij; simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hij, Pi.smul_apply]
  obtain ⟨j₀, hj₀⟩ : ∃ j, b.repr v₀ j ≠ 0 := by
    by_contra h
    push Not at h
    apply hv₀
    have := b.sum_repr v₀
    simp only [h, zero_smul, Finset.sum_const_zero] at this
    exact this.symm
  have hcoord : ∀ g : E, μ g j₀ = 1 := by
    intro g
    have h1 : b.repr ((f g) v₀) j₀ = μ g j₀ * b.repr v₀ j₀ := by
      rw [← LinearMap.toMatrix_mulVec_repr b b (f g) v₀, hmatg g]
      have hdiag : (Matrix.diagonal (fun j => μ g j) *ᵥ (b.repr v₀ : Fin (finrank K V) → K)) j₀ =
          μ g j₀ * b.repr v₀ j₀ := by
        simp [Matrix.mulVec, Matrix.diagonal, dotProduct, Finset.sum_eq_single j₀]
      exact hdiag
    have h2 : b.repr ((f g) v₀) j₀ = b.repr v₀ j₀ := by rw [hfix g g.2]
    rw [h1] at h2
    have h3 : μ g j₀ * b.repr v₀ j₀ = 1 * b.repr v₀ j₀ := by rw [one_mul]; exact h2
    exact mul_right_cancel₀ hj₀ h3
  rcases lt_or_ge (finrank K V) 2 with hm | hm
  · have hpos : 0 < finrank K V := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨v₀, hv₀⟩
    have hfr : finrank K V = 1 := by omega
    have hspan : Submodule.span K {v₀} = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_singleton hv₀, hfr]
    have hsub : Subsingleton E := by
      refine ⟨fun a c => Subtype.ext (LinearEquiv.ext fun v => ?_)⟩
      have hv : v ∈ Submodule.span K {v₀} := by rw [hspan]; exact Submodule.mem_top
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
      show ((a : V ≃ₗ[K] V) : V →ₗ[K] V) (t • v₀) = ((c : V ≃ₗ[K] V) : V →ₗ[K] V) (t • v₀)
      rw [LinearMap.map_smul, LinearMap.map_smul, hfix a a.2, hfix c c.2]
    have hcard : Nat.card E = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    rw [hcard, show finrank K V - 2 = 0 by omega]
    simp
  · obtain ⟨j₁, hj₁⟩ : ∃ j, j ≠ j₀ := by
      by_contra h
      push Not at h
      have hcard : Fintype.card (Fin (finrank K V)) ≤ 1 := by
        rw [Fintype.card_le_one_iff]
        intro a c
        exact (h a).trans (h c).symm
      simp at hcard
      omega
    let β := {j : Fin (finrank K V) // j ≠ j₀ ∧ j ≠ j₁}
    let ν : E → β → K := fun g j => μ g j.1
    have hνinj : Function.Injective ν := by
      intro g h hgh
      refine hinj (funext fun j => ?_)
      by_cases h0 : j = j₀
      · rw [h0]; exact (hcoord g).trans (hcoord h).symm
      · by_cases h1 : j = j₁
        · have hgp : μ g j₁ * ∏ i ∈ Finset.univ.erase j₁, μ g i = 1 := by
            rw [← hprod g]
            exact Finset.mul_prod_erase (Finset.univ) (fun i => μ g i) (Finset.mem_univ j₁)
          have hhp : μ h j₁ * ∏ i ∈ Finset.univ.erase j₁, μ h i = 1 := by
            rw [← hprod h]
            exact Finset.mul_prod_erase (Finset.univ) (fun i => μ h i) (Finset.mem_univ j₁)
          have hsame : ∏ i ∈ Finset.univ.erase j₁, μ g i =
              ∏ i ∈ Finset.univ.erase j₁, μ h i := by
            refine Finset.prod_congr rfl fun i hi => ?_
            by_cases hi0 : i = j₀
            · rw [hi0, hcoord g, hcoord h]
            · exact congrFun hgh ⟨i, hi0, Finset.ne_of_mem_erase hi⟩
          have hne : ∏ i ∈ Finset.univ.erase j₁, μ g i ≠ 0 := by
            refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
            intro h0'
            have hr := hroot g i
            rw [h0', zero_pow (Fact.out : p.Prime).ne_zero] at hr
            exact zero_ne_one hr
          have key : μ g j₁ * (∏ i ∈ Finset.univ.erase j₁, μ g i) =
              μ h j₁ * (∏ i ∈ Finset.univ.erase j₁, μ g i) := by
            rw [← hsame] at hhp
            rw [hgp, hhp]
          rw [h1]
          exact mul_right_cancel₀ hne key
        · exact congrFun hgh ⟨j, h0, h1⟩
    have hfin : Fintype.card β = finrank K V - 2 := by
      have hβ : Fintype.card β =
          ((Finset.univ.erase j₀ : Finset (Fin (finrank K V))).erase j₁).card := by
        simp only [β, Fintype.card_subtype]
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
        tauto
      rw [hβ, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hj₁, Finset.mem_univ j₁⟩),
        Finset.card_erase_of_mem (Finset.mem_univ j₀), Finset.card_univ, Fintype.card_fin]
      omega
    have hle := card_le_pow_card_of_injective_rootsOfUnity (K := K) (p := p) ν hνinj
      (fun g j => hroot g j.1)
    rwa [hfin] at hle

theorem card_le_pow_sub_two_of_normalizes_statedSU [CharP K 2] {f d : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hd : 3 ≤ d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ f + 1)
    {E R : Subgroup (StatedSU d (2 ^ f) K)} (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥)
    (hER : E ≤ Subgroup.normalizer (R : Set (StatedSU d (2 ^ f) K)))
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ p = 1) :
    Nat.card E ≤ p ^ (d - 2) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_ne_two hp hp2
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h
    · exfalso
      rw [h0] at hpq
      norm_num at hpq
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpq)
    · exact h
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hpK1 : p ∣ Nat.card K - 1 := by
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have h2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have key : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      zify [h1, h2]
      ring
    rw [hK, key]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨ζ, hζord⟩ : ∃ ζ : Kˣ, orderOf ζ = p :=
    exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rwa [Nat.card_units])
  have hζ : IsPrimitiveRoot (ζ : K) p := by
    rw [IsPrimitiveRoot.iff_orderOf, orderOf_units]
    exact hζord
  let F : ReflForm K (Fin d → K) := unitaryForm 2 f hK d
  let ρ : StatedSU d (2 ^ f) K →* Module.End K (Fin d → K) := natRep (StatedSU d (2 ^ f) K)
  have hρ : IsIsometric F ρ := isIsometric_natRep_statedSU hK d
  have hinj : Function.Injective ρ := natRep_injective _
  obtain ⟨W, hW0, hWiso, hWE⟩ := exists_invariant_isotropic F ρ hρ hinj hR hR1 hER
  have hD : Module.finrank K (Fin d → K) = d := Module.finrank_fin_fun K
  have hWpos : 1 ≤ Module.finrank K W := Submodule.one_le_finrank_iff.mpr hW0
  rcases eq_or_lt_of_le hWpos with hk | hk
  ·
    obtain ⟨w₀, hw₀W, hw₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have hw₀perp : w₀ ∈ F.perp W := hWiso hw₀W
    let ρE : E →* Module.End K (Fin d → K) := ρ.comp E.subtype
    have hW' : ∀ g : E, ∀ w ∈ W, ρE g w ∈ W := fun g w hw => hWE g g.2 w hw
    have hWinv : ∀ g ∈ E, ∀ w ∈ W, ρ g⁻¹ w ∈ W := fun g hg w hw => hWE g⁻¹ (E.inv_mem hg) w hw
    have hPinv : ∀ g ∈ E, ∀ v ∈ F.perp W, ρ g v ∈ F.perp W :=
      fun g hg v hv => hρ.apply_mem_perp_of_forall (hWinv g hg) hv
    have hPinvE : ∀ g : E, ∀ v ∈ F.perp W, ρE g v ∈ F.perp W :=
      fun g v hv => hPinv g g.2 v hv
    let ρW : E →* (W ≃ₗ[K] W) := LIT.restrictAction (FlagSplit.repAut ρE) W hW'
    let E₀ : Subgroup E := ρW.ker
    let ρP : E →* ((F.perp W) ≃ₗ[K] (F.perp W)) :=
      LIT.restrictAction (FlagSplit.repAut ρE) (F.perp W) hPinvE
    let ρP₀ : E₀ →* ((F.perp W) ≃ₗ[K] (F.perp W)) := ρP.comp E₀.subtype
    have hfixW : ∀ g : E₀, ∀ w ∈ W, ρ ((g : E) : StatedSU d (2 ^ f) K) w = w := by
      intro g w hw
      have h1 : ρW (g : E) = 1 := MonoidHom.mem_ker.mp g.2
      have h2 : ρW (g : E) ⟨w, hw⟩ = ⟨w, hw⟩ := by rw [h1]; rfl
      exact congrArg Subtype.val h2
    have hVW : ∀ g : E₀, ∀ v : Fin d → K, ρ ((g : E) : StatedSU d (2 ^ f) K) v - v ∈ F.perp W := by
      intro g v
      rw [ReflForm.mem_perp]
      intro w hw
      rw [ReflForm.β_sub_right]
      have h1 := hρ ((g : E) : StatedSU d (2 ^ f) K) w v
      rw [hfixW g w hw] at h1
      rw [h1, sub_self]
    have hdetP : ∀ g : E₀,
        LinearMap.det (((ρP₀ g : (F.perp W) ≃ₗ[K] (F.perp W)) : (F.perp W) →ₗ[K] (F.perp W))) = 1 := by
      intro g
      have hdetg : LinearMap.det (ρ ((g : E) : StatedSU d (2 ^ f) K)) = 1 :=
        CFSG.RankThree.PartTwo.Census.det_natRep_statedSU hU _
      have he := hPinvE (g : E)
      have hmul := LinearMap.det_eq_det_mul_det (e := ρ ((g : E) : StatedSU d (2 ^ f) K))
        (W := F.perp W) he
      have hmapQ : (F.perp W).mapQ (F.perp W) (ρ ((g : E) : StatedSU d (2 ^ f) K)) he =
          LinearMap.id := by
        refine LinearMap.ext fun x => ?_
        refine Submodule.Quotient.induction_on _ x fun v => ?_
        show Submodule.Quotient.mk (ρ ((g : E) : StatedSU d (2 ^ f) K) v) =
          Submodule.Quotient.mk v
        rw [Submodule.Quotient.eq]
        exact hVW g v
      rw [hdetg, hmapQ, LinearMap.det_id, mul_one] at hmul
      have hcoe : ((ρP₀ g : (F.perp W) ≃ₗ[K] (F.perp W)) : (F.perp W) →ₗ[K] (F.perp W)) =
          (ρ ((g : E) : StatedSU d (2 ^ f) K)).restrict he := by
        apply LinearMap.ext
        intro v
        rfl
      rw [hcoe]
      exact hmul.symm
    have hinjP : Function.Injective ρP₀ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro g hg
      rw [MonoidHom.mem_ker] at hg
      refine Subtype.ext (Subtype.ext ?_)
      refine FlagSplit.eq_one_of_fixes_flag F ρ hρ hinj hp hp2
        (hexp (((g : E₀) : E) : StatedSU d (2 ^ f) K) (((g : E₀) : E)).2) (hfixW g) ?_
      intro v hv
      have h1 : ρP₀ g ⟨v, hv⟩ = ⟨v, hv⟩ := by rw [hg]; rfl
      have h2 : ρ ((g : E) : StatedSU d (2 ^ f) K) v = v := by
        have h2' : ((ρP₀ g ⟨v, hv⟩ : F.perp W) : Fin d → K) = v := by rw [h1]
        have h2'' : ((ρP₀ g ⟨v, hv⟩ : F.perp W) : Fin d → K) =
            ρ ((g : E) : StatedSU d (2 ^ f) K) v := rfl
        rw [← h2'', h2']
      rw [h2, sub_self]
      exact W.zero_mem
    have hcardE₀ : Nat.card E₀ ≤ p ^ (d - 3) := by
      haveI : Finite (W ≃ₗ[K] W) := FlagSplit.finite_linearEquiv (K := K)
      have hcommRange : ∀ a ∈ ρP₀.range, ∀ b ∈ ρP₀.range, a * b = b * a := by
        rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
        rw [← map_mul, ← map_mul]
        exact congrArg ρP₀ (Subtype.ext (Subtype.ext
          (hcomm (a : E) (a : E).2 (b : E) (b : E).2)))
      have hexpRange : ∀ a ∈ ρP₀.range, a ^ p = 1 := by
        rintro _ ⟨a, rfl⟩
        rw [← map_pow]
        have h1 : (a : E₀) ^ p = 1 :=
          Subtype.ext (Subtype.ext
            (hexp (((a : E₀) : E) : StatedSU d (2 ^ f) K) (((a : E₀) : E)).2))
        rw [h1, map_one]
      have hfixv : ∀ a : E₀, (ρP₀ a) ⟨w₀, hw₀perp⟩ = ⟨w₀, hw₀perp⟩ := by
        intro a
        have h1 : ((ρP₀ a ⟨w₀, hw₀perp⟩ : F.perp W) : Fin d → K) =
            (FlagSplit.repAut ρE ((a : E₀) : E)) w₀ :=
          LIT.restrictAction_apply (FlagSplit.repAut ρE) (F.perp W) hPinvE
            ((a : E₀) : E) ⟨w₀, hw₀perp⟩
        refine Subtype.ext ?_
        exact h1.trans (hfixW a w₀ hw₀W)
      have hle := commutative_det_one_card_le_pow_sub_two_of_fixed hζ ρP₀.range
        hcommRange hexpRange (by rintro _ ⟨a, rfl⟩; exact hdetP a)
        (v₀ := ⟨w₀, hw₀perp⟩)
        (fun h0 => hw₀ (congrArg Subtype.val h0))
        (by rintro _ ⟨a, rfl⟩; exact hfixv a)
      have hfinrankP : Module.finrank K ↥(F.perp W) = d - 1 := by
        have h1 := F.finrank_perp W
        rw [hD] at h1
        omega
      rw [hfinrankP, show d - 1 - 2 = d - 3 by omega] at hle
      have hbij : Function.Bijective (MonoidHom.rangeRestrict ρP₀) :=
        ⟨MonoidHom.rangeRestrict_injective_iff.mpr hinjP, MonoidHom.rangeRestrict_surjective ρP₀⟩
      have hcard : Nat.card ρP₀.range = Nat.card E₀ :=
        (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
      rwa [hcard] at hle
    have hcommE : ∀ g h : E, g * h = h * g := fun g h => Subtype.ext (hcomm g g.2 h h.2)
    have hexpE : ∀ g : E, g ^ p = 1 := fun g => Subtype.ext (hexp g g.2)
    have hrangeW : Nat.card ρW.range ≤ p := by
      have h := FlagSplit.card_range_le_pow_div (d := 1) ρW hp hpK one_pos
        (fun i _ hi1 => absurd hi1 (by omega)) hcommE hexpE
      rw [← hk, Nat.div_one, pow_one] at h
      exact h
    have hcardE : Nat.card E = Nat.card E₀ * Nat.card ρW.range := by
      have h1 : Nat.card E = Nat.card (E ⧸ E₀) * Nat.card E₀ :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup E₀
      have h2 : Nat.card (E ⧸ E₀) = Nat.card ρW.range :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ρW).toEquiv
      rw [h1, h2, mul_comm]
    calc Nat.card E = Nat.card E₀ * Nat.card ρW.range := hcardE
      _ ≤ p ^ (d - 3) * p := Nat.mul_le_mul hcardE₀ hrangeW
      _ = p ^ ((d - 3) + 1) := (pow_succ p (d - 3)).symm
      _ = p ^ (d - 2) := by congr 1; omega
  ·
    have hk2 : 2 ≤ Module.finrank K W := hk
    have h2k : 2 * Module.finrank K W ≤ d := by
      have h1 := F.finrank_perp W
      have h2 : Module.finrank K W ≤ Module.finrank K (F.perp W) := Submodule.finrank_mono hWiso
      rw [hD] at h1
      omega
    have hle := card_le_of_invariant_isotropic F ρ hρ hinj hp hp2 hpK (d := 1) one_pos
      (fun i _ hi1 => absurd hi1 (by omega)) E hcomm hexp W hWiso hWE
    rw [hD, Nat.div_one, Nat.div_one] at hle
    calc Nat.card E ≤ p ^ Module.finrank K W * p ^ (d - 2 * Module.finrank K W) := hle
      _ = p ^ (Module.finrank K W + (d - 2 * Module.finrank K W)) := (pow_add _ _ _).symm
      _ ≤ p ^ (d - 2) := Nat.pow_le_pow_right hp.pos (by omega)

theorem localRank_statedSU_six_le_four [CharP K 2] {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) :
    localRank p ↥(StatedSU 6 (2 ^ f) K) ≤ 4 := by
  refine CFSG.LocalAnalysis.GLTheoremA.twoLocalPrimeRank_le_of_card_le hp ?_
  intro R E hR hR1 hER hE
  have hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩)
  haveI : CFSG.IsElementaryAbelian p E := hE.isElementaryAbelian
  have hexp : ∀ g ∈ E, g ^ p = 1 := fun g hg =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian g hg
  have h := card_le_pow_sub_two_of_normalizes_statedSU hK (d := 6) (by norm_num) hp hp2 hpq
    hR1 hR hER hcomm hexp
  simpa using h

theorem twoLocalPrimeRank_statedProj_statedSU_six_le_four_of_ne_three [CharP K 2] {f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpq : p ∣ 2 ^ f + 1) :
    localRank p (StatedProj (StatedSU 6 (2 ^ f) K)) ≤ 4 := by
  have hp6 : ¬ p ∣ 6 := by
    intro h
    rw [show (6 : ℕ) = 2 * 3 by norm_num] at h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
  refine (localRank_statedProj_statedSU_le hK (n := 6) (by norm_num) hp hp2 ?_).trans
    (localRank_statedSU_six_le_four hK hp hp2 hpq)
  intro h
  exact hp6 (h.trans (Nat.gcd_dvd_left 6 (2 ^ f + 1)))

end CFSG.RankThree.PartOne.KFU
