module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.Chevalley.SteinbergBID4RegularCentralizer
public import CFSG.RankThree.PartOne.FOC.ReeLayerDvd
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.KLR.SectorOrder
public import CFSG.RankThree.PartOne.KLR.SectorTori
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Subgroup CFSG CFSG.Open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.TCF
  CFSG.RankThree.PartOne.FOC
open scoped commutatorElement Pointwise

section Generic

theorem oddPCoreInClosure_of_two_elements_in_simple {C : Type*} [Group C] [Finite C] {p : ℕ}
    (hp : p.Prime) (N : Subgroup C) (hN2 : ∀ g : C, (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ N)
    (hNs : SimpleOrBot N) (hNd : N ≠ ⊥ → p ∣ Nat.card N) : OddPCoreInClosure p C := by
  classical
  intro K hK _ hKcop
  by_contra hodd
  have h2 : 2 ∣ Nat.card K := (Nat.not_odd_iff_even.1 hodd).two_dvd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 h2
  have hy' : orderOf (y : C) = 2 := by rw [Subgroup.orderOf_coe, hy]
  have hyN : (y : C) ∈ N := hN2 _ ⟨1, by rw [hy', pow_one]⟩
  have hy1 : (y : C) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hy'
    omega
  rcases hNs with rfl | ⟨hsimple, -⟩
  · exact hy1 (Subgroup.mem_bot.1 hyN)
  · have hN1 : N ≠ ⊥ := fun h => hy1 (Subgroup.mem_bot.1 (h ▸ hyN))
    haveI := hsimple
    haveI : (K.subgroupOf N).Normal := Subgroup.Normal.subgroupOf hK N
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf N) with hbot | htop
    · have : (⟨(y : C), hyN⟩ : N) ∈ K.subgroupOf N := y.2
      rw [hbot] at this
      exact hy1 (congrArg Subtype.val (Subgroup.mem_bot.1 this))
    · have hNK : N ≤ K := fun n hn => by
        have : (⟨n, hn⟩ : N) ∈ K.subgroupOf N := by rw [htop]; exact Subgroup.mem_top _
        exact this
      have hpK : p ∣ Nat.card K := (hNd hN1).trans (Subgroup.card_dvd_of_le hNK)
      exact ((Nat.Prime.coprime_iff_not_dvd hp).1 hKcop) hpK

end Generic

section Master

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.RF4
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.LargeReeOrder

variable {L : Type} [Field L]

section MasterThm

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  [Algebra K L] [IsAlgClosure K L] (D : ReeFrameData K L a)

theorem simple_layer_data_of_frame_dvd
    {n g₀ : ModGL ReeTag.F4.tag L}
    (hg₀ : g₀ ∈ adjointGroup ReeTag.F4.tag L) (hFg₀ : Fext D.F g₀ = g₀ * n)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hconj : ∀ x : ReeTag.F4.reeGamma K a, orderOf x = p →
      ∃ c : ReeTag.F4.reeGamma K a,
        g₀⁻¹ * thetaGamma L a (c * x * c⁻¹) * g₀ ∈ torusGroup ReeTag.F4.tag L)
    (hrad : ∀ b : Fin ReeTag.F4.tag.rank → Lˣ,
      orderOf (rootDiagUnit ReeTag.F4.tag b) = p →
      rootDiagUnit ReeTag.F4.tag b ∈ twistedFixed D.F n →
      StarSimpleDvd D n (rootCharKernel b))
    (x : ReeTag.F4.reeGamma K a) (hx : orderOf x = p) :
    ∃ N : Subgroup (ReeTag.F4.reeGamma K a),
      N ≤ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) ∧
      (∀ g ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
        (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ N) ∧
      SimpleOrBot N ∧ (N ≠ ⊥ → Nat.card K - 1 ∣ Nat.card N) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨c, hcH⟩ := hconj x hx
  let ψ : ReeTag.F4.reeGamma K a →* ModGL ReeTag.F4.tag L :=
    ((MulAut.conj g₀⁻¹).toMonoidHom.comp (thetaGamma L a)).comp (MulAut.conj c).toMonoidHom
  have hψ : ∀ d, ψ d = g₀⁻¹ * thetaGamma L a (c * d * c⁻¹) * g₀ := fun d => by
    simp [ψ, MulAut.conj_apply]
  have hψinj : Function.Injective ψ := by
    intro d₁ d₂ h
    rw [hψ, hψ] at h
    have h1 := mul_left_cancel (mul_right_cancel h)
    have h2 := mul_left_cancel (mul_right_cancel (thetaGamma_injective L h1))
    exact h2
  have hψmem : ∀ d, ψ d ∈ adjointGroup ReeTag.F4.tag L := fun d => by
    rw [hψ]
    exact mul_mem (mul_mem (inv_mem hg₀) (thetaGamma_mem_adjointGroup L _)) hg₀
  have hψtw : ∀ d, ψ d ∈ twistedFixed D.F n := fun d => by
    rw [hψ]
    exact conj_mem_twistedFixed D.F hg₀ hFg₀ (thetaGamma_mem_adjointGroup L _) (D.fext_theta _)
  have hy : ψ x = g₀⁻¹ * thetaGamma L a (c * x * c⁻¹) * g₀ := hψ x
  have hyH : ψ x ∈ torusGroup ReeTag.F4.tag L := by rw [hy]; exact hcH
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hyH
  have hordy : orderOf (rootDiagUnit ReeTag.F4.tag b) = p := by
    rw [← hb, orderOf_injective ψ hψinj x]
    exact hx
  have hap := CFSG.RankThree.Chevalley.pow_eq_one_of_orderOf_rootDiagUnit hordy
  have ha1 := ne_one_of_orderOf_rootDiagUnit hp hordy
  have hordW : ¬ p ∣ Nat.card (WeylGroup ReeTag.F4.tag) := not_dvd_card_weylGroup_F4 hp hp3
  have hS : ∀ α ∈ rootCharKernel b, IsRoot ReeTag.F4.tag α := fun α hα => hα.1
  have hSn : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨(isRoot_neg_iff).2 hα.1, by rw [← zero_sub, rootChar_sub, rootChar_zero, hα.2]; simp⟩
  have hcommh : ∀ d ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
      ψ d * rootDiagUnit ReeTag.F4.tag b = rootDiagUnit ReeTag.F4.tag b * ψ d := by
    intro d hd
    rw [← hb, ← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_centralizer_singleton_iff.1 hd
  have hHQ : ∀ d ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
      ψ d ∈ (torusGroup ReeTag.F4.tag L : Set (ModGL ReeTag.F4.tag L)) *
        (rootSpan ReeTag.F4.tag L (rootCharKernel b) : Set (ModGL ReeTag.F4.tag L)) :=
    fun d hd => mem_torus_mul_rootSpan_of_commute hp hordW hap ha1 hS hSn (fun _ h => h)
      (hψmem d) (hcommh d hd)
  have hL2 : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : ExpChar L 2 := ExpChar.prime Nat.prime_two
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : PerfectRing L 2 := PerfectField.toPerfectRing 2
  obtain ⟨σ, hσ⟩ : ∃ σ : L ≃+* L, ∀ c, σ c = c ^ 2 :=
    ⟨frobeniusEquiv L 2, fun c => by simp [frobeniusEquiv_apply, frobenius_def]⟩
  set P : Subgroup (ModGL ReeTag.F4.tag L) :=
    rootSpan ReeTag.F4.tag L (rootCharKernel b) ⊓ twistedFixed D.F n with hP
  have hPψ : ∀ u ∈ P, ∃ d ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
      ψ d = u := by
    rintro u ⟨huQ, huT⟩
    obtain ⟨hadj, hfix⟩ := fixed_of_mem_twistedFixed D.F hg₀ hFg₀ huT
    obtain ⟨γ, hγ⟩ := D.exists_theta_of_fixed hadj hfix
    have hθc : thetaGamma L a (c * x * c⁻¹) = g₀ * ψ x * g₀⁻¹ := by
      rw [hy]; group
    have huy : u * ψ x = ψ x * u := by
      rw [hb]
      exact Subgroup.mem_centralizer_singleton_iff.1
        (rootSpan_rootCharKernel_le_centralizer b huQ)
    have hcomm : γ * (c * x * c⁻¹) = (c * x * c⁻¹) * γ := by
      apply thetaGamma_injective L
      rw [map_mul (thetaGamma L a) γ (c * x * c⁻¹), map_mul (thetaGamma L a) (c * x * c⁻¹) γ, hγ,
        hθc]
      calc g₀ * u * g₀⁻¹ * (g₀ * ψ x * g₀⁻¹) = g₀ * (u * ψ x) * g₀⁻¹ := by group
        _ = g₀ * (ψ x * u) * g₀⁻¹ := by rw [huy]
        _ = g₀ * ψ x * g₀⁻¹ * (g₀ * u * g₀⁻¹) := by group
    have hd : c⁻¹ * γ * c ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (c⁻¹ * γ * c) * x = c⁻¹ * (γ * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x * c⁻¹) * γ) * c := by rw [hcomm]
        _ = x * (c⁻¹ * γ * c) := by group
    refine ⟨c⁻¹ * γ * c, hd, ?_⟩
    rw [hψ, show c * (c⁻¹ * γ * c) * c⁻¹ = γ by group, hγ]
    group
  have hrad' : SimpleOrBotDvd (Nat.card K - 1) P := hrad b hordy (by rw [← hb]; exact hψtw x)
  set C : Subgroup (ReeTag.F4.reeGamma K a) :=
    Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) with hC
  let N : Subgroup (ReeTag.F4.reeGamma K a) := P.comap ψ ⊓ C
  have hNC : N ≤ C := inf_le_right
  have hCN : ⁅C, C⁆ ≤ N := by
    refine Subgroup.commutator_le.2 fun d₁ hd₁ d₂ hd₂ => ?_
    have hdC : ⁅d₁, d₂⁆ ∈ C := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hd₁ hd₂) (inv_mem hd₁)) (inv_mem hd₂)
    refine ⟨?_, hdC⟩
    show ψ ⁅d₁, d₂⁆ ∈ P
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hT : ψ d₁ * ψ d₂ * (ψ d₁)⁻¹ * (ψ d₂)⁻¹ ∈ twistedFixed D.F n :=
      (twistedFixed D.F n).mul_mem ((twistedFixed D.F n).mul_mem
        ((twistedFixed D.F n).mul_mem (hψtw d₁) (hψtw d₂))
        ((twistedFixed D.F n).inv_mem (hψtw d₁))) ((twistedFixed D.F n).inv_mem (hψtw d₂))
    exact ⟨commutator_mem_rootSpan hS (hHQ d₁ hd₁) (hHQ d₂ hd₂), hT⟩
  have h2 : ∀ g ∈ C, (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ N := by
    rintro g hg ⟨k, hk⟩
    have h1 : ψ g ^ (2 ^ k) = 1 := by
      rw [← map_pow, ← hk, pow_orderOf_eq_one, map_one]
    exact ⟨⟨mem_rootSpan_of_pow_two_pow_eq_one σ hσ hS (hHQ g hg) h1, hψtw g⟩, hg⟩
  have hNP : N.map ψ = P := by
    ext u
    constructor
    · rintro ⟨d, ⟨hdP, -⟩, rfl⟩
      exact hdP
    · intro hu
      obtain ⟨d, hdC, rfl⟩ := hPψ u hu
      exact ⟨d, ⟨hu, hdC⟩, rfl⟩
  have hNs : SimpleOrBotDvd (Nat.card K - 1) N :=
    SimpleOrBotDvd.of_map ψ hψinj (by rw [hNP]; exact hrad')
  exact ⟨N, hNC, h2, hNs.1, hNs.2⟩

end MasterThm

theorem oddPCoreInClosure_ree_split {a p : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ 2 ^ (2 * a + 1) - 1) (x : ReeTag.F4.reeGamma K a) (hx : orderOf x = p) :
    OddPCoreInClosure p ↥(Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) := by
  classical
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hK2 : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨E, hEH, hEF, hE⟩ := torus_phi1 D.isFrob
  obtain ⟨g₀, hg₀, hFg₀, hconj⟩ := sector_hconj D _ E hEH hEF _ hE hp
    (pow_factorization_card_reeGamma_dvd_phi1 hK hp hp3 hpq)
  obtain ⟨N, hNC, h2, hNs, hdvd⟩ := simple_layer_data_of_frame_dvd D hg₀ hFg₀ hp hp3 hconj
    (fun b hordb hbT => starSimpleDvd D ha hK wPhi1 hp hp3 hordb hbT) x hx
  set C := Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) with hC
  refine oddPCoreInClosure_of_two_elements_in_simple hp (N.subgroupOf C) ?_ ?_ ?_
  · intro g ⟨k, hk⟩
    have hg : (g : ReeTag.F4.reeGamma K a) ∈ N :=
      h2 g g.2 ⟨k, by rw [Subgroup.orderOf_coe, hk]⟩
    exact hg
  · exact hNs.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNC).symm
  · intro hne
    have hN1 : N ≠ ⊥ := by
      intro h
      apply hne
      rw [h]
      exact Subgroup.bot_subgroupOf (H := C)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv]
    refine Nat.dvd_trans ?_ (hdvd hN1)
    rw [hK]
    exact hpq

end Master

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
