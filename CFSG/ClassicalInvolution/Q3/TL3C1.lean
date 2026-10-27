module

public import CFSG.ClassicalInvolution.Q3.Q3TLTShapeAb
public import CFSG.LocalAnalysis.ComponentClassification.ThompsonAB
public import CFSG.ClassicalInvolution.TwoGroupCase.Fusion

public section

namespace CFSG.ClassicalInvolution.Q3.TC

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_odd_of_mem_isPGroup {P : Subgroup G} (hP : IsPGroup 2 P) {x : G}
    (hxP : x ∈ P) (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨m, hm⟩ := hP ⟨x, hxP⟩
  have hdvd : orderOf x ∣ 2 ^ m := by
    have h1 := congrArg Subtype.val hm
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h1
    exact orderOf_dvd_of_pow_eq_one h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj0 : j = 0 := by
    by_contra hj0
    rw [hj] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hj0).mpr even_two)
  rw [hj0, pow_zero] at hj
  exact orderOf_eq_one_iff.mp hj

omit [Finite G] in
theorem eq_one_of_mem_odd_of_mem_isPGroup {A P : Subgroup G} (hA : Odd (Nat.card A))
    (hP : IsPGroup 2 P) {x : G} (hxA : x ∈ A) (hxP : x ∈ P) : x = 1 :=
  eq_one_of_odd_of_mem_isPGroup hP hxP
    (hA.of_dvd_nat (Subgroup.orderOf_dvd_natCard A hxA))

theorem oddCoreImg_le_of_normal {E : Subgroup G} (hE : E.Normal) :
    oddCoreImg E ≤ classicalInvolutionOddCore G := by
  have hn : (oddCoreImg E).Normal := by
    refine ⟨fun o ho g => ?_⟩
    have hg : g ∈ Subgroup.normalizer (E : Set G) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hE]
      exact Subgroup.mem_top g
    exact conj_mem_oddCoreImg hg ho
  exact le_sSup ⟨hn, odd_natCard_oddCoreImg E⟩

omit [Finite G] in
theorem le_oddCoreImg_of_normalizes {E N : Subgroup G} (hNE : N ≤ E)
    (hnorm : ∀ e ∈ E, ∀ n ∈ N, e * n * e⁻¹ ∈ N) (hodd : Odd (Nat.card N)) : N ≤ oddCoreImg E := by
  set M : Subgroup E := N.subgroupOf E with hM
  have hMn : M.Normal := by
    refine ⟨fun m hm e => ?_⟩
    rw [hM, Subgroup.mem_subgroupOf] at hm ⊢
    exact hnorm e e.2 m hm
  have hMcard : Nat.card M = Nat.card N := by
    rw [hM]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNE).toEquiv
  have hMle : M ≤ classicalInvolutionOddCore E := le_sSup ⟨hMn, hMcard ▸ hodd⟩
  intro n hn
  exact ⟨⟨n, hNE hn⟩, hMle (Subgroup.mem_subgroupOf.mpr hn), rfl⟩

theorem oddCoreImg_centralizer_eq_bot (hO : classicalInvolutionOddCore G = ⊥) {t : G}
    {P : Subgroup G} (hPn : P.Normal) (hP2 : IsPGroup 2 P) (htP : t ∈ P) :
    oddCoreImg (Subgroup.centralizer ({t} : Set G)) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := Subgroup.centralizer ({t} : Set G) with hC
  set X : Subgroup G := oddCoreImg C with hX
  set F : Subgroup G := genFittingFitting G with hF
  set E : Subgroup G := genFittingLayer G with hE
  have hFn : F.Normal := genFittingFitting_normal
  have hEn : E.Normal := genFittingLayer_normal
  have hO' : oddCore G = ⊥ := hO
  have hF2 : IsPGroup 2 F := isPGroup_two_genFittingFitting hO'
  have hPF : P ≤ F := le_sSup ⟨hPn, hP2.isNilpotent⟩
  have htF : t ∈ F := hPF htP
  have hXC : X ≤ C := oddCoreImg_le C
  have hXodd : Odd (Nat.card X) := odd_natCard_oddCoreImg C
  have hXnorm : ∀ c ∈ C, ∀ x ∈ X, c * x * c⁻¹ ∈ X := fun c hc x hx =>
    conj_mem_oddCoreImg (Subgroup.le_normalizer hc) hx
  have hcommX : ∀ x ∈ X, ∀ c ∈ C, ⁅x, c⁆ ∈ X := by
    intro x hx c hc
    rw [commutatorElement_def]
    have h1 : c * x⁻¹ * c⁻¹ ∈ X := hXnorm c hc _ (X.inv_mem hx)
    have h2 : x * (c * x⁻¹ * c⁻¹) ∈ X := X.mul_mem hx h1
    simpa [mul_assoc] using h2
  have hXord : ∀ x ∈ X, Odd (orderOf x) := fun x hx =>
    hXodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard X hx)
  have hstep1 : ∀ x ∈ X, ∀ q ∈ F, x * q = q * x := by
    intro x hx q hq
    have hxC : x ∈ C := hXC hx
    have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
    set B : Subgroup G := Subgroup.zpowers t with hB
    have hBF : B ≤ F := Subgroup.zpowers_le.mpr htF
    have hB2 : IsPGroup 2 B := hF2.to_le hBF
    have hV2 : IsPGroup 2 F := hF2
    let action : B →* MulAut F := (MulAut.conjNormal (H := F)).comp B.subtype
    let δ : MulAut F := MulAut.conjNormal x
    have hcomm : ∀ b : B, Commute δ (action b) := by
      intro b
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp b.2
      have hxb : x * (b : G) = (b : G) * x := by
        rw [← hk]
        exact (Commute.zpow_right hxt k).eq
      show δ * action b = action b * δ
      show MulAut.conjNormal x * MulAut.conjNormal (b : G) =
        MulAut.conjNormal (b : G) * MulAut.conjNormal x
      rw [← map_mul, ← map_mul, hxb]
    have hfix : ∀ p : F, (∀ b : B, action b p = p) → δ p = p := by
      intro p hp
      have htp : t * (p : G) * t⁻¹ = p := by
        have := congrArg Subtype.val (hp ⟨t, Subgroup.mem_zpowers t⟩)
        simpa [action, MulAut.conjNormal_apply] using this
      have hpC : (p : G) ∈ C := by
        rw [hC, Subgroup.mem_centralizer_singleton_iff]
        calc (p : G) * t = t * (p : G) * t⁻¹ * t := by rw [htp]
          _ = t * p := by group
      have hw : ⁅x, (p : G)⁆ ∈ X := hcommX x hx _ hpC
      have hwF : ⁅x, (p : G)⁆ ∈ F := by
        rw [commutatorElement_def]
        exact F.mul_mem (hFn.conj_mem _ p.2 x) (F.inv_mem p.2)
      have h1 : ⁅x, (p : G)⁆ = 1 := eq_one_of_mem_odd_of_mem_isPGroup hXodd hF2 hw hwF
      apply Subtype.ext
      show x * (p : G) * x⁻¹ = p
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      rw [h1, mul_inv_cancel_right]
    have hpow : δ ^ orderOf x = 1 := by
      show (MulAut.conjNormal x) ^ orderOf x = 1
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have hcop : (orderOf x).Coprime 2 :=
      Nat.coprime_two_right.mpr (hXord x hx)
    have h1 := ComponentClassification.ThompsonAB.coprime_eq_one 2 hV2 hB2 action δ hcomm hfix
      (orderOf x) hpow hcop
    have h2 := congrArg (fun φ : MulAut F => ((φ ⟨q, hq⟩ : F) : G)) h1
    simp only [δ, MulAut.conjNormal_apply, MulAut.one_apply] at h2
    calc x * q = x * q * x⁻¹ * x := by group
      _ = q * x := by rw [h2]
  have hEC : E ≤ C := by
    intro e he
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact layer_commutes_fitting he htF
  have hstep2 : ∀ x ∈ X, ∀ e ∈ E, x * e = e * x := by
    intro x hx e he
    have hw : ⁅x, e⁆ ∈ X := hcommX x hx e (hEC he)
    have hwE : ⁅x, e⁆ ∈ E := by
      rw [commutatorElement_def]
      exact E.mul_mem (hEn.conj_mem _ he x) (E.inv_mem he)
    have hnorm : ∀ e' ∈ E, ∀ n ∈ X ⊓ E, e' * n * e'⁻¹ ∈ X ⊓ E := by
      intro e' he' n hn
      exact ⟨hXnorm e' (hEC he') n hn.1, hEn.conj_mem n hn.2 e'⟩
    have hodd : Odd (Nat.card (X ⊓ E : Subgroup G)) :=
      hXodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    have hle := le_oddCoreImg_of_normalizes inf_le_right hnorm hodd
    have hw1 : ⁅x, e⁆ ∈ classicalInvolutionOddCore G :=
      oddCoreImg_le_of_normal hEn (hle ⟨hw, hwE⟩)
    rw [hO, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hw1
    exact hw1
  have hcent : X ≤ Subgroup.centralizer (genFittingFStar G : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    have hle : genFittingFStar G ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le (fun q hq => ?_) (fun e he => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hstep1 x hx q hq).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hstep2 x hx e he).symm
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  have hcent2 := isPGroup_two_centralizer_genFittingFStar hO'
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  exact eq_one_of_odd_of_mem_isPGroup hcent2 (hcent hx) (hXord x hx)

end CFSG.ClassicalInvolution.Q3.TC
