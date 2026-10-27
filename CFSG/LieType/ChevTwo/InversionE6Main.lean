module

public import CFSG.LieType.ChevTwo.InversionE6
public import CFSG.LieType.ChevTwo.InversionCases
public import CFSG.LieType.Chevalley.ExactNormalFormE
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
import CFSG.LieType.ChevTwo.InversionKlein
import CFSG.LieType.ChevTwo.InversionFamilies
import CFSG.LieType.Chevalley.EvenQuadraticGraphFieldDescent
import CFSG.LieType.Chevalley.OrdinaryEOuterOrder
import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.LieType.ChevTwo.Reductions
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LieType.Chevalley.EvenRootCommutatorF4
import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies
import CFSG.LieType.SeitzGeneration.Lift
import CFSG.LieType.Simplicity.Finiteness
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.ChevTwo.Inversion
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

local notation "innerAut" => CFSG.ComponentClassification.OuterAutomorphisms.inner


theorem e6_inner_of_theta_one {K : Type} [Field K] [Finite K]
    (Θ : MulAut (adjointGroup Tag.E6 K) →* RingAut K × Multiplicative (ZMod (exactE Tag.E6)))
    (hker : ∀ α : MulAut (adjointGroup Tag.E6 K), α ∈ Θ.ker ↔
      ∃ (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ), ∀ h : adjointGroup Tag.E6 K,
        (α h : ModGL Tag.E6 K) = (g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a *
          (h : ModGL Tag.E6 K) * (rootDiagUnit Tag.E6 a)⁻¹ * (g : ModGL Tag.E6 K)⁻¹)
    {α : MulAut (adjointGroup Tag.E6 K)} (h2 : α ^ 2 = 1) (h1 : Θ α = 1) :
    α ∈ innerAut (adjointGroup Tag.E6 K) := by
  obtain ⟨Φ, -, hkerΦ, hdvd⟩ := exists_outer_hom_E (K := K) (τ := Tag.E6) (Or.inl rfl)
  obtain ⟨g, a, hα⟩ := (hker α).1 (MonoidHom.mem_ker.2 h1)
  have hαeq : α = MulAut.conj g * rootDiagAut Tag.E6 K a := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [hα x, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_rootDiagAut, Subgroup.coe_inv]
    simp only [mul_assoc]
  have hmem : (QuotientGroup.mk α : Outer (adjointGroup Tag.E6 K)) ∈ Φ.ker := by
    rw [hkerΦ]
    refine ⟨a, ?_⟩
    change (QuotientGroup.mk (rootDiagAut Tag.E6 K a) : Outer (adjointGroup Tag.E6 K)) =
      QuotientGroup.mk α
    rw [hαeq, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (N := innerAut (adjointGroup Tag.E6 K))
      (MulAut.conj g)).2 (MonoidHom.mem_range.2 ⟨g, rfl⟩), one_mul]
  have h3 : Nat.card Φ.ker ∣ 3 := by simpa [det_cartan_E6] using hdvd
  set x : Φ.ker := ⟨_, hmem⟩ with hx
  have hx2 : x ^ 2 = 1 := Subtype.ext (by
    change (QuotientGroup.mk α : Outer (adjointGroup Tag.E6 K)) ^ 2 = 1
    rw [← QuotientGroup.mk_pow, h2, QuotientGroup.mk_one])
  have hord : orderOf x ∣ 1 := by
    have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx2) ((orderOf_dvd_natCard x).trans h3)
    simpa using this
  have hx1 : x = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hord)
  exact (QuotientGroup.eq_one_iff α).1 (congrArg Subtype.val hx1)

theorem e6_klein_inverts {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {A : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (hA : OuterKleinFour A) : InvertsOddElt A := by
  obtain ⟨hAe, hcard, hAI⟩ := hA
  haveI : CharP K 2 := charP_two_of_card_two_pow hf hK
  obtain ⟨Θ, -, hexpr, hker, hsq, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  have hR : ∀ x y : RingAut K, x ^ 2 = 1 → y ^ 2 = 1 → x ≠ 1 → y ≠ 1 → x = y := by
    intro x y hx hy hx1 hy1
    obtain ⟨-, hxc, -⟩ := ringEquiv_sq_eq_one_facts Nat.prime_two hf hK hx hx1
    obtain ⟨-, hyc, -⟩ := ringEquiv_sq_eq_one_facts Nat.prime_two hf hK hy hy1
    exact RingEquiv.ext fun c => (hxc c).trans (hyc c).symm
  let Θ₀ : ↥A →* RingAut K × Multiplicative (ZMod 2) := Θ.comp A.subtype
  have hinj : Function.Injective Θ₀ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, ha⟩ h1
    have h2 : a ^ 2 = 1 := hAe.2 a ha
    have hin : a ∈ innerAut (adjointGroup Tag.E6 K) := e6_inner_of_theta_one Θ hker h2 h1
    have hbot : a ∈ A ⊓ innerAut (adjointGroup Tag.E6 K) := ⟨ha, hin⟩
    rw [hAI, Subgroup.mem_bot] at hbot
    exact Subtype.ext hbot
  have hA2 : ∀ a : ↥A, a ^ 2 = 1 := fun ⟨a, ha⟩ => Subtype.ext (hAe.2 a ha)
  obtain ⟨⟨a₀, ha₀⟩, hs, he⟩ := exists_both_ne_one hR hA2 hcard Θ₀ hinj
  have h20 : a₀ ^ 2 = 1 := hAe.2 a₀ ha₀
  obtain ⟨g, a, σ, ε, hnf⟩ :=
    exists_conj_mul_exactNormalAut (K := K) (τ := Tag.E6) (Or.inl rfl) a₀
  have hexp : ∀ h : adjointGroup Tag.E6 K, (a₀ h : ModGL Tag.E6 K) = (g : ModGL Tag.E6 K) *
      rootDiagUnit Tag.E6 a * exactQ Tag.E6 K ε * Units.map (entrywiseHom σ.toRingHom)
        (h : ModGL Tag.E6 K) * (exactQ Tag.E6 K ε)⁻¹ * (rootDiagUnit Tag.E6 a)⁻¹ *
          (g : ModGL Tag.E6 K)⁻¹ := by
    intro h
    rw [hnf, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_exactNormalAut, Subgroup.coe_inv]
    simp only [mul_assoc]
  have hΘ := hexpr a₀ g a σ ε hexp
  have hs' : (Θ a₀).1 ≠ 1 := hs
  have he' : (Θ a₀).2 ≠ 1 := he
  have ha01 : a₀ ≠ 1 := fun h1 => hs' (by rw [h1, map_one]; rfl)
  rw [hΘ] at hs' he'
  have hσ1 : σ ≠ 1 := hs'
  have hε1 : (ε : ℕ) = 1 := by
    have hlt : (ε : ℕ) < 2 := ε.2
    by_contra hne
    have h0 : (ε : ℕ) = 0 := by omega
    exact he' (by rw [h0]; simp)
  have hσ2 : σ ^ 2 = 1 := hsq a₀ g a σ ε hexp h20
  obtain ⟨⟨e, he2⟩, hpow, -⟩ := ringEquiv_sq_eq_one_facts Nat.prime_two hf hK hσ2 hσ1
  have hfe : f / 2 = e := by omega
  have he1 : 1 ≤ e := by omega
  have hK2 : Nat.card K = 2 ^ (2 * e) := by rw [hK]; congr 1; omega
  have hδ : ∀ c, σ.toRingHom c = c ^ 2 ^ e := fun c => by
    have := hpow c
    rw [hfe] at this
    exact this
  obtain ⟨-, β, -, hdesc⟩ :=
    even_exceptional_quadratic_field_graph_field_involution_descent he1 K hK2 σ.toRingHom hδ
  have hQ : exactQ Tag.E6 K (ε : ℕ) = diagramMap TwistTag.E6 K := by
    rw [hε1]
    exact pow_one _
  obtain ⟨ψ₀, hψ₀, -⟩ := (hdesc g a).2 a₀ (fun u => by
    have h := hexp u
    rw [hQ] at h
    exact h) ((pow_two a₀).symm.trans h20)
  let ψ : MulAut (adjointGroup Tag.E6 K) := ψ₀
  have hψ : ∀ u : adjointGroup Tag.E6 K, ((ψ * a₀ * ψ⁻¹) u : ModGL Tag.E6 K) =
      e6Twist σ.toRingHom (u : ModGL Tag.E6 K) := hψ₀
  obtain ⟨x, hxmem, hx7, hxinv⟩ := e6_twistHom_inverts_order_seven (K := K) σ.toRingHom
  set x' : adjointGroup Tag.E6 K := ⟨x, hxmem⟩ with hx'
  have hβx : (ψ * a₀ * ψ⁻¹) x' = x'⁻¹ := Subtype.ext (by
    rw [hψ x']
    exact hxinv)
  have h1 : ψ (a₀ (ψ⁻¹ x')) = x'⁻¹ := hβx
  have h2 : a₀ (ψ⁻¹ x') = ψ⁻¹ (x'⁻¹) := by rw [← h1, MulAut.inv_apply_self]
  have hord : orderOf (ψ⁻¹ x') = 7 := by
    rw [MulEquiv.orderOf_eq ψ⁻¹ x', hx', Subgroup.orderOf_mk]
    exact hx7
  refine ⟨a₀, ha₀, ha01, ψ⁻¹ x', ?_, ?_, ?_⟩
  · rw [hord]; decide
  · rw [hord]; norm_num
  · rw [h2, map_inv]

theorem chev2RankTwoInverts_E6_of_certs {S : Type} [Group S] (h : IsE6TwoFamily S)
    {A : Subgroup (MulAut S)} (hA : OuterKleinFour A) : InvertsOddElt A := by
  obtain ⟨q, hv, hp, ⟨e⟩⟩ := h
  obtain ⟨K, _, _, hK, -, ⟨e'⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  have hK2 : Nat.card K = 2 ^ q.exponent := by
    rw [hK, TauCeti.PrimePower.card_def, hp]
  exact inverts_of_mulEquiv (e.trans e') hA fun A' hA' => e6_klein_inverts q.exponent_pos hK2 hA'

end CFSG.LieType.ChevTwo
