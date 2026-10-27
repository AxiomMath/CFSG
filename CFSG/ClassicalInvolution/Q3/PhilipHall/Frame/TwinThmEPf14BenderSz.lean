module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf14BenderPsl
public import CFSG.GH74.Generic.S1.Exo.Q3SingleSz8
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Aut
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Bridge
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Generic.S1.Exo.NbDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Models.BenderSuzuki
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.FinalTheorem

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace TwinThmE

namespace BenderSz

open CFSG.Blueprint CFSG.LieType.Ree CFSG.GH74.Generic.S1.Exo QuaternionGroup

section NoQ8

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem false_of_suzuki_relations (h2 : (2 : K) = 0) {s t x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hs : s ≠ 0) (hc : s * x = t * y) (ha : s * y + t * x = s * x)
    (hb : x ^ 2 * t + y ^ 2 * s = x ^ 2 * s) : False := by
  have h1 : s * (x ^ 2 + x * y + y ^ 2) = 0 := by
    linear_combination y * ha + x * hc + (s * x * y) * h2
  have hq : x ^ 2 + x * y + y ^ 2 = 0 := (mul_eq_zero.mp h1).resolve_left hs
  have h3 : s * (x ^ 3 + y ^ 3 + x ^ 2 * y) = 0 := by
    linear_combination y * hb + x ^ 2 * hc + (s * x ^ 2 * y) * h2
  have hp : x ^ 3 + y ^ 3 + x ^ 2 * y = 0 := (mul_eq_zero.mp h3).resolve_left hs
  have h4 : x ^ 2 * y = 0 := by
    linear_combination (x + y) * hq - hp - (x * y ^ 2) * h2
  exact mul_ne_zero (pow_ne_zero 2 hx) hy h4

theorem no_q8_suzukiGroup (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ψ : QuaternionGroup 2 →* suzukiGroup a K) (hψ : Function.Injective ψ) : False := by
  have hQ : IsPGroup 2 (QuaternionGroup 2) := IsPGroup.of_card (n := 3) (by
    rw [Nat.card_eq_fintype_card, show Fintype.card (QuaternionGroup 2) = 8 from
      QuaternionGroup.card (n := 2)]
    norm_num)
  obtain ⟨g, hg⟩ := exists_conj_mem_suzukiU hK hQ ψ
  let φ : QuaternionGroup 2 →* suzukiGroup a K := (MulAut.conj g⁻¹).toMonoidHom.comp ψ
  have hφ : Function.Injective φ := (MulAut.conj g⁻¹).injective.comp hψ
  have hφU : ∀ x, φ x ∈ suzukiU a K := fun x => by
    simpa [φ, MulAut.conj_apply, mul_assoc] using hg x
  have hii : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
      QuaternionGroup.a 2 := by decide
  have hjj : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
      QuaternionGroup.a 2 := by decide
  have hz1 : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide
  have hcomm : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 * QuaternionGroup.a 2 := by decide
  obtain ⟨u₁, v₁, h1⟩ := (mem_suzukiU_iff hK).1 (hφU (QuaternionGroup.a 1))
  obtain ⟨u₂, v₂, h2⟩ := (mem_suzukiU_iff hK).1 (hφU (QuaternionGroup.xa 0))
  obtain ⟨h2K, hadd, hθθ⟩ := CFSG.LieType.Ree.suzuki_frob_data a hK
  have hsq : ∀ u v : K, suzukiSElt a K u v * suzukiSElt a K u v =
      suzukiSElt a K 0 (u ^ 2 ^ (a + 1) * u) := by
    intro u v
    rw [suzukiSElt_mul hK]
    congr 1
    · linear_combination u * h2K
    · linear_combination v * h2K
  have hsq1 : suzukiSElt a K 0 (u₁ ^ 2 ^ (a + 1) * u₁) = φ (QuaternionGroup.a 2) := by
    rw [← hii, map_mul, ← h1, hsq]
  have hsq2 : suzukiSElt a K 0 (u₂ ^ 2 ^ (a + 1) * u₂) = φ (QuaternionGroup.a 2) := by
    rw [← hjj, map_mul, ← h2, hsq]
  have hne : u₁ ^ 2 ^ (a + 1) * u₁ ≠ 0 := by
    intro h0
    apply hz1
    apply hφ
    rw [← hsq1, h0, suzukiSElt_zero_zero hK, map_one]
  have heq : u₁ ^ 2 ^ (a + 1) * u₁ = u₂ ^ 2 ^ (a + 1) * u₂ := by
    have := (suzukiSElt_inj (a := a) (K := K)).1 (hsq1.trans hsq2.symm)
    exact this.2
  have hu₁ : u₁ ≠ 0 := by
    intro h0
    apply hne
    rw [h0]
    simp
  have hu₂ : u₂ ≠ 0 := by
    intro h0
    apply hne
    rw [heq, h0]
    simp
  have hs : u₁ ^ 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ hu₁
  have hrel : φ (QuaternionGroup.a 1) * φ (QuaternionGroup.xa 0) =
      φ (QuaternionGroup.xa 0) * φ (QuaternionGroup.a 1) * φ (QuaternionGroup.a 2) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← hcomm]
  rw [← h1, ← h2, ← hsq1, suzukiSElt_mul hK, suzukiSElt_mul hK, suzukiSElt_mul hK] at hrel
  have hE := ((suzukiSElt_inj (a := a) (K := K)).1 hrel).2
  have hE2 : u₁ ^ 2 ^ (a + 1) * u₂ =
      u₂ ^ 2 ^ (a + 1) * u₁ + u₁ ^ 2 ^ (a + 1) * u₁ := by
    have : v₁ + v₂ + u₁ ^ 2 ^ (a + 1) * u₂ =
        v₂ + v₁ + u₂ ^ 2 ^ (a + 1) * u₁ + u₁ ^ 2 ^ (a + 1) * u₁ +
          (u₂ + u₁) ^ 2 ^ (a + 1) * 0 := hE
    linear_combination this
  set s := u₁ ^ 2 ^ (a + 1) with hsdef
  set t := u₂ ^ 2 ^ (a + 1) with htdef
  have ha : s * u₂ + t * u₁ = s * u₁ := by linear_combination hE2 + (t * u₁) * h2K
  have hb : u₁ ^ 2 * t + u₂ ^ 2 * s = u₁ ^ 2 * s := by
    have := congrArg (fun w : K => w ^ 2 ^ (a + 1)) ha
    simp only [hadd, mul_pow, hsdef, htdef, hθθ] at this
    simpa [hsdef, htdef] using this
  exact false_of_suzuki_relations h2K hu₁ hu₂ hs heq ha hb

end NoQ8

section Out

open CFSG.Open

theorem szModel_eq_sz (n : ℕ) : CFSG.Theory.Comparator.SzModel n = Sz n :=
  CFSG.Models.benderSzModel_eq_sz n

theorem no_q8_sz {n : ℕ} (hn : 1 ≤ n) (ψ : QuaternionGroup 2 →* Sz n)
    (hψ : Function.Injective ψ) : False := by
  obtain ⟨E⟩ := CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup n
  have hK : Nat.card (GaloisField 2 (2 * n + 1)) = 2 ^ (2 * n + 1) :=
    GaloisField.card 2 (2 * n + 1) (by omega)
  exact no_q8_suzukiGroup hK (E.toMonoidHom.comp ψ) (E.injective.comp hψ)

theorem no_q8_of_sz {G : Type} [Group G] (F : Subgroup G) [F.Normal]
    (hC : Subgroup.centralizer (F : Set G) = ⊥) {n : ℕ} (hn : 1 ≤ n)
    (e : F ≃* CFSG.Theory.Comparator.SzModel n) (R : Subgroup G) (eR : R ≃* QuaternionGroup 2) :
    False := by
  let e2 : F ≃* Sz n := e.trans (MulEquiv.subgroupCongr (szModel_eq_sz n))
  let ρ : G →* MulAut (Sz n) := (MulAut.congr e2).toMonoidHom.comp (MulAut.conjNormal (H := F))
  have hρ : Function.Injective ρ := (MulAut.congr e2).injective.comp (BenderPsl.conjNormal_injective F hC)
  have hRF : R ≤ F := by
    intro r hr
    have h4 : r ^ 4 = 1 := by
      have hq : ∀ q : QuaternionGroup 2, q ^ 4 = 1 := by decide
      have := hq (eR ⟨r, hr⟩)
      rw [← map_pow] at this
      have h' := eR.injective (this.trans (map_one eR).symm)
      exact congrArg Subtype.val h'
    have hg4 : (ρ r) ^ 4 = 1 := by rw [← map_pow, h4, map_one]
    have hdvd : orderOf (ρ r) ∣ 4 := orderOf_dvd_of_pow_eq_one hg4
    have hcop2 : Nat.Coprime (2 * n + 1) 2 :=
      Nat.Coprime.symm (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))
    have hcop4 : Nat.Coprime (2 * n + 1) 4 := by
      have := Nat.Coprime.pow_right 2 hcop2
      simpa using this
    obtain ⟨x, hx⟩ := CFSG.SignalizerFunctorTheorem.McBride.SzModel.exists_conj_of_coprime_orderOf hn
      (ρ r) (Nat.Coprime.coprime_dvd_right hdvd hcop4)
    have hy : ρ ((e2.symm x : F) : G) = ρ r := by
      rw [hx]
      simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conjNormal_val]
      ext x'
      simp [MulAut.congr_apply, MulAut.conj_apply]
    have : r = ((e2.symm x : F) : G) := (hρ hy).symm
    rw [this]
    exact (e2.symm x).2
  let ψ : QuaternionGroup 2 →* Sz n :=
    e2.toMonoidHom.comp ((Subgroup.inclusion hRF).comp eR.symm.toMonoidHom)
  have hψ : Function.Injective ψ :=
    e2.injective.comp ((Subgroup.inclusion_injective hRF).comp eR.symm.injective)
  exact no_q8_sz hn ψ hψ

end Out

section Bender

open CFSG.BenderSuzuki

theorem benderNoQ8' :
    ∀ (G : Type) [Group G] [Finite G] (F : Subgroup G) [F.Normal],
      Subgroup.centralizer (F : Set G) = ⊥ →
      ((∃ n : ℕ, 2 ≤ n ∧ Nonempty (↥F ≃* PSL2Model n)) ∨
        (∃ n : ℕ, 1 ≤ n ∧ Nonempty (↥F ≃* SzModel n))) →
      ∀ R : Subgroup G, ¬ Nonempty (↥R ≃* QuaternionGroup 2) := by
  intro G _ _ F _ hC h R ⟨eR⟩
  rcases h with ⟨n, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact BenderPsl.no_q8_of_psl2 F hC n e R eR
  · exact no_q8_of_sz F hC hn e R eR

end Bender

end BenderSz

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
