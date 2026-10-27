module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S7Reduce
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S7Index
public import Certificates.Certificate26420
public import Certificates.Certificate26421
public import Certificates.Certificate26422
public import Certificates.Certificate26423
public import Certificates.Certificate26424

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

structure Sect7Hyps (G : Type) [Group G] [Finite G] (L : Subgroup G) (f s y : G)
    (S₀ : Subgroup G) (n : G) : Prop where
  std : CFSG.EvenSporadicStandard.StdHyp G L
  card_center : Nat.card (center L) = 2
  quot : IsSporadic (L ⧸ center L) .HS
  four : FourHyp G L f
  tight : IsTight L s
  yy : y * y = 1
  yf : y * f * y⁻¹ = f⁻¹
  y_not : y ∉ L ⊔ zpowers f
  cent_eq : centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y
  y_conj : ∃ g : G, y = g * f ^ 2 * g⁻¹
  s_conj : ∃ g : G, s ^ 2 = g * f ^ 2 * g⁻¹
  not_conj : ¬ ∃ g : G, s ^ 2 * f ^ 2 = g * f ^ 2 * g⁻¹
  u : ∃ u : L, (u : G) = s ^ 2 ∧ u * u = 1 ∧ u ∉ center L
  f_mem : f ∈ S₀
  S₀_t : S₀ ≤ centralizer ({f ^ 2} : Set G)
  S₀_s : S₀ ≤ centralizer ({s ^ 2} : Set G)
  pgroup : IsPGroup 2 S₀
  rel : ¬ 2 ∣ S₀.relIndex (centralizer ({f ^ 2} : Set G))
  n_norm : ∀ x : G, x ∈ S₀ ↔ n * x * n⁻¹ ∈ S₀
  n_t : n * f ^ 2 * n⁻¹ = s ^ 2

@[expose] def Sect8InputA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f s y : G) (S₀ : Subgroup G) (n : G),
    Sect7Hyps G L f s y S₀ n → ∃ C : ECoord G, Sect8Hyp C f n S₀

@[expose] def Sect8InputU (hQ : Q0Facts) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f s y : G) (S₀ : Subgroup G) (n : G),
    Sect7Hyps G L f s y S₀ n → ∀ (C : ECoord G), Sect8Hyp C f n S₀ → ∀ T K : Subgroup G,
      Lemma61Out C hQ f S₀ T K →
        ∃ U : Subgroup G, U ≤ T ∧ U.relIndex T = 2 ∧ f ∉ U ∧ C.E1sub hQ ≤ U ∧
          (∀ w ∈ T, w * f ^ 2 = f ^ 2 * w → w ∈ L ⊔ zpowers y → w ∈ U) ∧
          ∀ x ∈ T, x ∉ U → x * x = 1 →
            ∃ z ∈ T, x * (z⁻¹ * f ^ 2 * z) = (z⁻¹ * f ^ 2 * z) * x

@[expose] def Sect8InputFy : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f s y : G) (S₀ : Subgroup G) (n : G),
    Sect7Hyps G L f s y S₀ n → ∀ w : G, w * f ^ 2 = f ^ 2 * w → w ∉ L ⊔ zpowers y →
      w ∉ L ⊔ zpowers f → ∀ g : G, w ≠ g⁻¹ * f ^ 2 * g

theorem sect7Existence_of_inputs
    (hA : Sect8InputA) (hU : ∀ hQ : Q0Facts, Sect8InputU hQ)
    (hFy : Sect8InputFy) : Sect7Existence := by
  intro G _ _ L f s y S₀ n hL hZ hq H hs hyy hyf hy hN hyc hsc hn hu hfS₀ hS₀f hS₀s hS₀2 hS₀rel
    hn1 hn2
  have hH : Sect7Hyps G L f s y S₀ n :=
    ⟨hL, hZ, hq, H, hs, hyy, hyf, hy, hN, hyc, hsc, hn, hu, hfS₀, hS₀f, hS₀s, hS₀2, hS₀rel, hn1,
      hn2⟩
  obtain ⟨C, hC⟩ := hA G L f s y S₀ n hH
  have hQ : Q0Facts := Certificates.certificate26420
  have hNC : NormComplete := Certificates.certificate26421
  have hCF : CandFacts := Certificates.certificate26422
  have hAF : AlphaFacts :=
    alphaFacts_of Certificates.certificate26423 Certificates.certificate26424
  have hs2 : s ^ 2 ≠ f ^ 2 := by
    intro h2
    obtain ⟨u, hu1, -, hu3⟩ := hu
    obtain ⟨τ, hτ, hτ'⟩ := H.exists_center_gen
    apply hu3
    have : u = τ := Subtype.ext (hu1.trans (h2.trans hτ'.symm))
    rw [this]
    exact hτ
  obtain ⟨T, K, hT⟩ := sect8_lemma61 hC hQ hNC hCF hAF H.order hn2 hs2 hn
  obtain ⟨U, hUT, hUidx, hfU, hE1U, hUint, hfix⟩ := hU hQ G L f s y S₀ n hH C hC T K hT
  refine ⟨T, U, C.E, C.E1sub hQ, K, {x : G | ∃ u ∈ C.Fsub hQ, x = f ^ 2 * u}, ?_⟩
  exact
    { pgroup := hT.sylow.pgroup
      sylow := hT.sylow.sylow
      f_mem := hT.sylow.E_le hC.f_mem
      U_le := hUT
      U_index := hUidx
      f_not_mem := hfU
      E₁_le := hE1U
      core := hT.core
      K_cent := hT.K_cent
      sq_fusion := hT.sq_fusion
      sq_coset := hT.sq_coset
      inv_conj := inv_conj_of_fixed_point hUT hUidx hfix
      U_inter := fun w hwT hwc hwU hwL => hwU (hUint w hwT hwc hwL)
      fy_fusion := hFy G L f s y S₀ n hH }

end CFSG.EvenSporadicStandard.TwoHS
