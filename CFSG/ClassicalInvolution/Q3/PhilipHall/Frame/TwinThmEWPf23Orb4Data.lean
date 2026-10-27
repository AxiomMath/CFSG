module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf9Sev2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf23Orb4Shape
public import CFSG.ClassicalInvolution.Asc77.AscE187B2f
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Hyp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

namespace TwinThmEW

section Pair

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def GoodFourWD (S : Subgroup G) (H W : Subgroup G) (t : G) : Prop :=
  ∃ d₁ d₂ : G, GoodInv H t d₁ ∧ GoodInv H t d₂ ∧ GoodInv H t (d₁ * d₂) ∧ d₁ * d₂ = d₂ * d₁ ∧
    d₁ ∈ W ∧ d₂ ∈ W ∧ D4Shape S t d₁ d₂

theorem orb4_rset_ne_of_ne (hΩ : HypOmegaGen Ω) {K J R R' : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hKJ : K ≠ J) (hR : R ∈ RSet Ω) (hRK : R ≤ K) (hR'J : R' ≤ J) : R ≠ R' := by
  intro h
  subst h
  have hR2 : IsPGroup 2 R := by
    obtain ⟨J', -, -, h2, -⟩ := mem_RSet_iff.mp hR
    exact h2
  have h1 := hΩ.card_le_two_of_le_inf hK hJ hKJ hR2 hRK hR'J
  have h8 := hΩ.eight_le_of_mem_RSet hR
  omega

theorem goodFourD_pair (hΩ : HypOmegaGen Ω) (S : Sylow 2 G) {W H : Subgroup G}
    (hWn : ∀ s ∈ (S : Subgroup G), conjSub s W = W) (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hQ8 : ∀ P ∈ RSet Ω, IsQ8 P) {Ka Kb Ra Rb : Subgroup G} {z t u u' : G} (hKa : Ka ∈ Ω)
    (hKb : Kb ∈ Ω) (hKab : Ka ≠ Kb) (hza : IsUniqueInvolution Ka z) (hzb : IsUniqueInvolution Kb z)
    (hRa : Ra ∈ RSet Ω) (hRb : Rb ∈ RSet Ω) (hRaK : Ra ≤ Ka) (hRbK : Rb ≤ Kb)
    (hRaS : Ra ≤ (S : Subgroup G)) (hRbS : Rb ≤ (S : Subgroup G)) (htz : t * z = z * t)
    (hua : u ∈ Ra) (hu4 : orderOf u = 4) (huW : u ∈ W) (hub : u' ∈ Rb) (hu'4 : orderOf u' = 4)
    (hu'W : u' ∈ W) (htd : (u * u') * t = t * (u * u'))
    (hzcent : Subgroup.centralizer ({z} : Set G) ≤ H)
    (h2 : ∀ a ∈ Ra ⊔ Rb, a ∈ W → a ≠ 1 → a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H) :
    GoodFourWD (S : Subgroup G) H W t := by
  have hu2 : u * u = z := sq_eq_of_orderOf_four hza (hRaK hua) hu4
  have hu'2 : u' * u' = z := sq_eq_of_orderOf_four hzb (hRbK hub) hu'4
  have hRne : Ra ≠ Rb := orb4_rset_ne_of_ne hΩ hKa hKb hKab hRa hRaK hRbK
  have hcomm : Commutes Ra Rb := orb4_rset_commutes hΩ S hRa hRb hRaS hRbS hRne
  have huu' : u * u' = u' * u := hcomm u hua u' hub
  have huR' : u ∈ Ra ⊔ Rb := Subgroup.mem_sup_left hua
  have hu'R' : u' ∈ Ra ⊔ Rb := Subgroup.mem_sup_right hub
  have hzu : z * u = u * z := hza.commute_of_mem (hRaK hua)
  have hzu' : z * u' = u' * z := hzb.commute_of_mem (hRbK hub)
  have hno : ∀ x ∈ Ka, x ∈ Kb → orderOf x = 4 → False := by
    intro x hxK hxK' hx4
    have h := hΩ.card_le_two_of_le_inf hKa hKb hKab (isPGroup_zpowers_of_orderOf_four hx4)
      (Subgroup.zpowers_le.mpr hxK) (Subgroup.zpowers_le.mpr hxK')
    rw [Nat.card_zpowers, hx4] at h
    omega
  obtain ⟨d, hd⟩ : ∃ d, d = u * u' := ⟨_, rfl⟩
  have hdd : d * d = 1 := by
    calc d * d = u * (u' * u) * u' := by rw [hd]; group
      _ = u * (u * u') * u' := by rw [huu']
      _ = (u * u) * (u' * u') := by group
      _ = 1 := by rw [hu2, hu'2, hza.sq]
  have hd1 : d ≠ 1 := by
    intro h
    have h1 : u' = u⁻¹ := by
      have : u * u' = 1 := hd ▸ h
      exact (inv_eq_of_mul_eq_one_right this).symm
    have hu_K' : u ∈ Kb := by
      have := Kb.inv_mem (hRbK hub)
      rwa [h1, inv_inv] at this
    exact hno u (hRaK hua) hu_K' hu4
  have hdR : d ∈ Ra ⊔ Rb := hd ▸ (Ra ⊔ Rb).mul_mem huR' hu'R'
  have hzR : z ∈ Ra ⊔ Rb := hu2 ▸ (Ra ⊔ Rb).mul_mem huR' huR'
  have hzd : z * d = d * z := by
    calc z * d = (z * u) * u' := by rw [hd]; group
      _ = u * z * u' := by rw [hzu]
      _ = u * (z * u') := by group
      _ = u * (u' * z) := by rw [hzu']
      _ = d * z := by rw [hd]; group
  have htd' : d * t = t * d := hd ▸ htd
  have hzdne : z * d ≠ 1 := by
    intro h
    have h1 : u' = u⁻¹ * z := by
      have h2' : u * u' = z⁻¹ := by
        have : z * (u * u') = 1 := by rw [← hd]; exact h
        exact eq_inv_of_mul_eq_one_right this
      rw [inv_eq_of_mul_eq_one_right hza.sq] at h2'
      calc u' = u⁻¹ * (u * u') := by group
        _ = u⁻¹ * z := by rw [h2']
    have hu'K0 : u' ∈ Ka := by rw [h1]; exact Ka.mul_mem (Ka.inv_mem (hRaK hua)) hza.mem
    exact hno u' hu'K0 (hRbK hub) hu'4
  have hzdsq : (z * d) * (z * d) = 1 := by
    calc (z * d) * (z * d) = z * (d * z) * d := by group
      _ = z * (z * d) * d := by rw [hzd]
      _ = (z * z) * (d * d) := by group
      _ = 1 := by rw [hza.sq, hdd, one_mul]
  have hzW' : z ∈ W := hu2 ▸ W.mul_mem huW huW
  have hdW : d ∈ W := hd ▸ W.mul_mem huW hu'W
  have hshape : D4Shape (S : Subgroup G) t z d := by
    rw [hd]
    exact shape_commute hΩ S hWn hWab hQ8 hRa hRb hRaS hRbS hRne hua huW hu4 hub hu'W hu'4 hu2 hu'2 t
  refine ⟨z, d, ⟨hza.ne_one, hza.sq, htz.symm, hzcent⟩, ⟨hd1, hdd, htd', ?_⟩,
    ⟨hzdne, hzdsq, ?_, ?_⟩, hzd, hzW', hdW, hshape⟩
  · exact h2 d hdR hdW hd1 hdd
  · calc z * d * t = z * (d * t) := by group
      _ = z * (t * d) := by rw [htd']
      _ = (z * t) * d := by group
      _ = (t * z) * d := by rw [htz]
      _ = t * (z * d) := by group
  · exact h2 (z * d) ((Ra ⊔ Rb).mul_mem hzR hdR) (W.mul_mem hzW' hdW) hzdne hzdsq

end Pair

section Commute

variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCexQ8.isQ8_of_mem_RSet (c : MinCexQ8 Ω K S R W H) : ∀ P ∈ RSet Ω, IsQ8 P := by
  intro P hP
  obtain ⟨J, hJ, hPJ⟩ := exists_isSylow2In_of_mem_RSet hP
  exact TwinDisc.forall_sylow_iso_of_exists (c.stand.q8 J hJ) P hPJ

theorem MinCexQ8.W_abelian (c : MinCexQ8 Ω K S R W H) : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
  obtain ⟨η, -, -, -, habel, -⟩ := c.exists_eta (etaAbelian_of_gen c.stand.hyp)
  exact habel

theorem orb4_swap_htd {u t : G} (ht2 : t * t = 1) (huu' : u * (t * u * t⁻¹) = (t * u * t⁻¹) * u) :
    (u * (t * u * t⁻¹)) * t = t * (u * (t * u * t⁻¹)) := by
  have e1 : t * (t * u * t⁻¹) * t⁻¹ = u := by
    have : t * (t * u * t⁻¹) * t⁻¹ = (t * t) * u * (t * t)⁻¹ := by group
    rw [this, ht2]
    group
  have e : t * (u * (t * u * t⁻¹)) * t⁻¹ = u * (t * u * t⁻¹) := by
    calc t * (u * (t * u * t⁻¹)) * t⁻¹ = (t * u * t⁻¹) * (t * (t * u * t⁻¹) * t⁻¹) := by group
      _ = (t * u * t⁻¹) * u := by rw [e1]
      _ = u * (t * u * t⁻¹) := huu'.symm
  exact (mul_inv_eq_iff_eq_mul.mp e).symm

theorem MinCexQ8.goodFourD_of_commute (c : MinCexQ8 Ω K S R W H) {z g t : G}
    (hz : IsUniqueInvolution K z) (hzH : Subgroup.centralizer ({z} : Set G) ≤ H) (hg : g ∉ H)
    (ht : t = g * z * g⁻¹) (htS : t ∈ (S : Subgroup G)) (hcomm : t * z = z * t) :
    GoodFourWD (S : Subgroup G) H W t := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hA : EtaAbelian Ω := etaAbelian_of_gen hΩ
  have hM : EtaMeet Ω := etaMeet_of_gen hΩ
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨-, hWS, hWn⟩ := c.stand.hW
  obtain ⟨K', hK'tw, hne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  have hWab := c.W_abelian
  have hQ8 := c.isQ8_of_mem_RSet
  have hK : K ∈ Ω := c.stand.mem
  have hC : ∀ M ∈ Ω, IsUniqueInvolution M z → ∀ x ∈ M, orderOf x = 4 → t * x ≠ x * t := by
    have := c.hC_of_conj hA hM hz hzH hg
    rwa [← ht] at this
  have hfour : ∀ {M R₀ : Subgroup G}, M ∈ Ω → R₀ ∈ RSet Ω → R₀ ≤ M → R₀ ≤ (S : Subgroup G) →
      IsCyclic ↥(M ⊓ W) ∧ ∃ u ∈ M ⊓ W, orderOf u = 4 :=
    fun hM' hR₀ hR₀M hR₀S => c.exists_order_four_of_inf_W hA hM hM' hR₀ hR₀M hR₀S
  have hcentW : ∀ {K₀ J R₀ R₂ : Subgroup G}, K₀ ∈ twinSet Ω K → J ∈ KPerp Ω K₀ → R₀ ∈ RSet Ω →
      R₀ ≤ K₀ → R₀ ≤ (S : Subgroup G) → R₂ ∈ RSet Ω → R₂ ≤ J → R₂ ≤ (S : Subgroup G) →
      ∀ a ∈ R₀ ⊔ R₂, a ∈ W → a ≠ 1 → a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H :=
    fun {_ J R₀ R₂} hK₀tw hJ hR₀ hR₀K₀ hR₀S hR₂ hR₂J hR₂S a ha haW ha1 ha2 =>
      c.hyp.cent _ hK₀tw.1
        (inf_W_mem_USet' hΩ c.stand.hW.1 c.stand.hW.2.1 hK₀tw.1 hR₀ hR₀K₀ hR₀S) _ hJ R₀ R₂ hR₀
        hR₀K₀ hR₀S hR₂ hR₂J hR₂S (commutes_or_eq_of_le_sylow hΩ hR₀ hR₂ hR₀S hR₂S) a ha haW ha1 ha2
  have ht2 : t * t = 1 := by
    rw [ht]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  have hWt : ∀ x ∈ W, t * x * t⁻¹ ∈ W := fun x hx => by
    have := conj_mem_conjSub (n := t) hx
    rwa [hWn t htS] at this
  have hK'Ω : K' ∈ Ω := hK'tw.1
  have hKtw : K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩
  obtain ⟨-, z', hzz', hz'K'⟩ := id hK'tw
  have hz' : IsUniqueInvolution K' z := by
    have := hz.eq hzz'
    rwa [← this] at hz'K'
  have htzt : t * z * t⁻¹ = z := by rw [hcomm]; group
  have hconjt : ∀ M : Subgroup G, IsUniqueInvolution M z → IsUniqueInvolution (conjSub t M) z := by
    intro M hMz
    have := hMz.conj t
    rwa [htzt] at this
  have hK'perp : K' ∈ KPerp Ω K := mem_kPerp_of_twin_gen hΩ hK'Ω hK hz' hz
  have hmemR : ∀ u : G, u ∈ K → u ∈ W → u ∈ R := fun u huK huW => by
    have : u ∈ K ⊓ (S : Subgroup G) := ⟨huK, hWS huW⟩
    rwa [inf_S_eq_of_mem_RSet hΩ hK hRR hRK hRS] at this
  have hmemR' : ∀ u : G, u ∈ K' → u ∈ W → u ∈ R' := fun u huK huW => by
    have : u ∈ K' ⊓ (S : Subgroup G) := ⟨huK, hWS huW⟩
    rwa [inf_S_eq_of_mem_RSet hΩ hK'Ω hR' hR'K' hR'S] at this
  have hRR'2 : IsPGroup 2 ↥(R ⊔ R') := S.isPGroup'.to_le (sup_le hRS hR'S)
  have hswap : ∀ {K₀ R₀ : Subgroup G} {u : G}, K₀ ∈ twinSet Ω K → R₀ ∈ RSet Ω → R₀ ≤ K₀ →
      R₀ ≤ (S : Subgroup G) → conjSub t K₀ ≠ K₀ → u ∈ R₀ → u ∈ W → orderOf u = 4 →
      (∀ a ∈ R₀ ⊔ conjSub t R₀, a ∈ W → a ≠ 1 → a * a = 1 →
        Subgroup.centralizer ({a} : Set G) ≤ H) → GoodFourWD (S : Subgroup G) H W t := by
    intro K₀ R₀ u hK₀tw hR₀ hR₀K hR₀S hnK hu huW hu4 h2
    have hK₀Ω : K₀ ∈ Ω := hK₀tw.1
    have hz₀ : IsUniqueInvolution K₀ z := by
      obtain ⟨-, z'', hzK, hzK₀⟩ := hK₀tw
      have := hz.eq hzK
      rwa [← this] at hzK₀
    have hKtΩ : conjSub t K₀ ∈ Ω := hΩ.conjInvariant t K₀ hK₀Ω
    have hRtΩ : conjSub t R₀ ∈ RSet Ω := RSet.conj hΩ.conjInvariant hR₀ t
    have hRtS : conjSub t R₀ ≤ (S : Subgroup G) := orb4_conjSub_le_of_mem htS hR₀S
    have hRne : R₀ ≠ conjSub t R₀ :=
      orb4_rset_ne_of_ne hΩ hK₀Ω hKtΩ (Ne.symm hnK) hR₀ hR₀K (conjSub_mono hR₀K)
    have hcm : Commutes R₀ (conjSub t R₀) := orb4_rset_commutes hΩ S hR₀ hRtΩ hR₀S hRtS hRne
    have hu'R : t * u * t⁻¹ ∈ conjSub t R₀ := conj_mem_conjSub hu
    have hu'4 : orderOf (t * u * t⁻¹) = 4 := by rw [orderOf_conj_mul_inv_eq]; exact hu4
    exact goodFourD_pair hΩ S hWn hWab hQ8 hK₀Ω hKtΩ (Ne.symm hnK) hz₀ (hconjt K₀ hz₀) hR₀ hRtΩ
      hR₀K (conjSub_mono hR₀K) hR₀S hRtS hcomm hu hu4 huW hu'R hu'4 (hWt u huW)
      (orb4_swap_htd ht2 (hcm u hu _ hu'R)) hzH h2
  by_cases hnK : conjSub t K = K
  · by_cases hnK' : conjSub t K' = K'
    · obtain ⟨hcycK, u, huKW, hu4⟩ := hfour hK hRR hRK hRS
      obtain ⟨hcycK', u', hu'KW, hu'4⟩ := hfour hK'Ω hR' hR'K' hR'S
      have huR := hmemR u huKW.1 huKW.2
      have hu'R := hmemR' u' hu'KW.1 hu'KW.2
      have hRne : R ≠ R' := orb4_rset_ne_of_ne hΩ hK hK'Ω (Ne.symm hne) hRR hRK hR'K'
      have hcomm' : Commutes R R' := orb4_rset_commutes hΩ S hRR hR' hRS hR'S hRne
      have hinv : ∀ (M : Subgroup G), M ∈ Ω → IsUniqueInvolution M z → conjSub t M = M →
          IsCyclic ↥(M ⊓ W) → ∀ x ∈ M, x ∈ W → orderOf x = 4 → t * x * t⁻¹ = x⁻¹ := by
        intro M hM' hzM htM hMW x hxM hxW hx4
        have h1 : t * x * t⁻¹ ∈ M ⊓ W := by
          refine ⟨?_, ?_⟩
          · have := conj_mem_conjSub (n := t) hxM
            rwa [htM] at this
          · exact hWt x hxW
        rcases eq_or_eq_inv_of_orderOf_four_of_cyclic hMW ⟨hxM, hxW⟩ h1
          hx4 (by rw [orderOf_conj_mul_inv_eq, hx4]) with h | h
        · exfalso
          apply hC M hM' hzM x hxM hx4
          calc t * x = (t * x * t⁻¹) * t := by group
            _ = x * t := by rw [h]
        · exact h
      have huu' : u * u' = u' * u := hcomm' u huR u' hu'R
      have hd2 : (u * u') * (u * u') = 1 := by
        calc (u * u') * (u * u') = u * (u' * u) * u' := by group
          _ = u * (u * u') * u' := by rw [huu']
          _ = (u * u) * (u' * u') := by group
          _ = 1 := by
            rw [sq_eq_of_orderOf_four hz huKW.1 hu4, sq_eq_of_orderOf_four hz' hu'KW.1 hu'4, hz.sq]
      have htd : (u * u') * t = t * (u * u') := by
        have htW : conjSub t K = K := hnK
        have e : t * (u * u') * t⁻¹ = u * u' := by
          calc t * (u * u') * t⁻¹ = (t * u * t⁻¹) * (t * u' * t⁻¹) := by group
            _ = u⁻¹ * u'⁻¹ := by
              rw [hinv K hK hz hnK hcycK u huKW.1 huKW.2 hu4,
                hinv K' hK'Ω hz' hnK' hcycK' u' hu'KW.1 hu'KW.2 hu'4]
            _ = (u' * u)⁻¹ := by group
            _ = (u * u')⁻¹ := by rw [huu']
            _ = u * u' := inv_eq_of_mul_eq_one_right hd2
        exact (mul_inv_eq_iff_eq_mul.mp e).symm
      exact goodFourD_pair hΩ S hWn hWab hQ8 hK hK'Ω (Ne.symm hne) hz hz' hRR hR' hRK hR'K' hRS hR'S
        hcomm huR hu4 huKW.2 hu'R hu'4 hu'KW.2 htd hzH
        (fun a ha haW ha1 ha2 => hcentW hKtw hK'perp hRR hRK hRS hR' hR'K' hR'S a ha haW ha1 ha2)
    · obtain ⟨hcycK', u', hu'KW, hu'4⟩ := hfour hK'Ω hR' hR'K' hR'S
      have hKtΩ : conjSub t K' ∈ Ω := hΩ.conjInvariant t K' hK'Ω
      have hJ : conjSub t K' ∈ KPerp Ω K' :=
        mem_kPerp_of_twin_gen hΩ hKtΩ hK'Ω (hconjt K' hz') hz'
      exact hswap hK'tw hR' hR'K' hR'S hnK' (hmemR' u' hu'KW.1 hu'KW.2) hu'KW.2 hu'4
        (fun a ha haW ha1 ha2 => hcentW hK'tw hJ hR' hR'K' hR'S (RSet.conj hΩ.conjInvariant hR' t)
          (conjSub_mono hR'K') (orb4_conjSub_le_of_mem htS hR'S) a ha haW ha1 ha2)
  · obtain ⟨hcycK, u, huKW, hu4⟩ := hfour hK hRR hRK hRS
    have hKtΩ : conjSub t K ∈ Ω := hΩ.conjInvariant t K hK
    have hJ : conjSub t K ∈ KPerp Ω K := mem_kPerp_of_twin_gen hΩ hKtΩ hK (hconjt K hz) hz
    exact hswap hKtw hRR hRK hRS hnK (hmemR u huKW.1 huKW.2) huKW.2 hu4
      (fun a ha haW ha1 ha2 => hcentW hKtw hJ hRR hRK hRS (RSet.conj hΩ.conjInvariant hRR t)
        (conjSub_mono hRK) (orb4_conjSub_le_of_mem htS hRS) a ha haW ha1 ha2)

end Commute

section NonCommute

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem goodFourD_of_noncommute_of (hΩ : HypOmegaGen Ω) (hQ8 : ∀ P ∈ RSet Ω, IsQ8 P)
    (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hcmm : ∀ (M₁ M₂ R₁ R₂ : Subgroup G), M₁ ∈ Ω → M₂ ∈ Ω → M₁ ≠ M₂ → R₁ ∈ RSet Ω → R₁ ≤ M₁ →
      R₁ ≤ (S : Subgroup G) → R₂ ∈ RSet Ω → R₂ ≤ M₂ → R₂ ≤ (S : Subgroup G) →
      ∀ x ∈ M₁ ⊓ (S : Subgroup G), ∀ y ∈ M₂ ⊓ (S : Subgroup G), x * y = y * x)
    (hfour : ∀ {M R₀ : Subgroup G}, M ∈ Ω → R₀ ∈ RSet Ω → R₀ ≤ M → R₀ ≤ (S : Subgroup G) →
      ∃ u ∈ M ⊓ W, orderOf u = 4)
    (hKS : K ⊓ (S : Subgroup G) = R) (hquat : IsQuatSub R)
    (hnt : ∀ {x : G}, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≠ ⊤)
    (hZ0 : ∀ {K₃ K₄ R₃ R₄ : Subgroup G}, K₃ ∈ twinSet Ω K → K₄ ∈ twinSet Ω K → K₄ ≠ K₃ →
      R₃ ∈ RSet Ω → R₃ ≤ K₃ → R₃ ≤ (S : Subgroup G) → R₄ ∈ RSet Ω → R₄ ≤ K₄ →
      R₄ ≤ (S : Subgroup G) → K₄ ∈ twinSet Ω K₃ → ∀ x : G, x ≠ 1 → x * x = 1 →
      IsPGroup 2 (Subgroup.zpowers x) →
      R₃ ⊔ R₄ ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) →
      Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≠ ⊤ →
      Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ H)
    (hK : K ∈ Ω) (hRR : R ∈ RSet Ω) (hRK : R ≤ K) (hRS : R ≤ (S : Subgroup G))
    (hWS : W ≤ (S : Subgroup G)) (hWn : ∀ s ∈ (S : Subgroup G), conjSub s W = W)
    {K' R' : Subgroup G} (hK'tw : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hR' : R' ∈ RSet Ω)
    (hR'K' : R' ≤ K') (hR'S : R' ≤ (S : Subgroup G)) (hKS' : K' ⊓ (S : Subgroup G) = R') {z g t : G} (hz : IsUniqueInvolution K z)
    (ht : t = g * z * g⁻¹) (htS : t ∈ (S : Subgroup G)) (hnc : ¬ t * z = z * t)
    (htt : ∃ (B : Subgroup G) (b : G) (g' : G), B ≤ (S : Subgroup G) ∧
      B ≤ Subgroup.centralizer ({t} : Set G) ∧ IsUniqueInvolution B b ∧ 8 ≤ Nat.card B ∧
      b = z * (t * z * t⁻¹) ∧ b ∈ W ∧ Subgroup.centralizer ({b} : Set G) ≤ H ∧
      t = g' * z * g'⁻¹ ∧ g' ∉ H ∧ (∀ β ∈ B, g'⁻¹ * β * g' ∈ (S : Subgroup G)) ∧
      ∃ β₃ ∈ B, ∃ β₄ ∈ B, conjSub (g'⁻¹ * β₃ * g') K ≠ conjSub (g'⁻¹ * β₄ * g') K ∧
        conjSub (g'⁻¹ * β₃ * g') K ≠ K ∧ conjSub (g'⁻¹ * β₃ * g') K ≠ K' ∧
        conjSub (g'⁻¹ * β₄ * g') K ≠ K ∧ conjSub (g'⁻¹ * β₄ * g') K ≠ K') :
    GoodFourWD (S : Subgroup G) H W t := by
  classical
  classical
  have hK'Ω : K' ∈ Ω := hK'tw.1
  have hz' : IsUniqueInvolution K' z := by
    obtain ⟨-, z', hz'K, hz'K'⟩ := hK'tw
    have := hz.eq hz'K
    rwa [← this] at hz'K'
  obtain ⟨B, b, g', hBS, hBt, hBb, hB8, hbdef, hbW, hbH, ht', hg'H, hBg', β₃, hβ₃, β₄, hβ₄,
    hne34, hK₃K, hK₃K', hK₄K, hK₄K'⟩ := htt
  have ht2 : t * t = 1 := by
    rw [ht]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hz2 := hz.sq
  have hRS' : R ≤ (S : Subgroup G) := hRS

  have hconjdata : ∀ s : G, s ∈ (S : Subgroup G) → ∀ M R₀ : Subgroup G, M ∈ Ω → R₀ ∈ RSet Ω →
      R₀ ≤ M → R₀ ≤ (S : Subgroup G) → conjSub s M ∈ Ω ∧ conjSub s R₀ ∈ RSet Ω ∧
        conjSub s R₀ ≤ conjSub s M ∧ conjSub s R₀ ≤ (S : Subgroup G) :=
    fun s hs M R₀ hM hR₀ hR₀M hR₀S => ⟨hΩ.conjInvariant s M hM, RSet.conj hΩ.conjInvariant hR₀ s,
      conjSub_mono hR₀M, conjSub_le_of_mem hs hR₀S⟩

  obtain ⟨zt, hzt⟩ : ∃ zt, zt = t * z * t⁻¹ := ⟨_, rfl⟩
  have hzt1 : IsUniqueInvolution (conjSub t K) zt := hzt ▸ hz.conj t
  have hz't1 : IsUniqueInvolution (conjSub t K') zt := hzt ▸ hz'.conj t
  have hzzt : z ≠ zt := by
    intro h'
    apply hnc
    calc t * z = (t * z * t⁻¹) * t := by group
      _ = z * t := by rw [← hzt, ← h']
  obtain ⟨hKtΩ, hRtmem, hRtK, hRtS⟩ := hconjdata t htS K R hK hRR hRK hRS
  obtain ⟨hK'tΩ, hR'tmem, hR'tK, hR'tS⟩ := hconjdata t htS K' R' hK'Ω hR' hR'K' hR'S

  have hsz : ∀ β ∈ B, (g'⁻¹ * β * g') * z * (g'⁻¹ * β * g')⁻¹ = z := by
    intro β hβ
    have hβt : β * t = t * β := Subgroup.mem_centralizer_singleton_iff.mp (hBt hβ)
    calc (g'⁻¹ * β * g') * z * (g'⁻¹ * β * g')⁻¹
        = g'⁻¹ * (β * (g' * z * g'⁻¹) * β⁻¹) * g' := by group
      _ = g'⁻¹ * (β * t * β⁻¹) * g' := by rw [← ht']
      _ = g'⁻¹ * (t * β * β⁻¹) * g' := by rw [hβt]
      _ = g'⁻¹ * t * g' := by group
      _ = z := by rw [ht']; group
  have hs₃S := hBg' β₃ hβ₃
  have hs₄S := hBg' β₄ hβ₄
  have hs₃z := hsz β₃ hβ₃
  have hs₄z := hsz β₄ hβ₄
  generalize g'⁻¹ * β₃ * g' = s₃ at hne34 hK₃K hK₃K' hs₃S hs₃z
  generalize g'⁻¹ * β₄ * g' = s₄ at hne34 hK₄K hK₄K' hs₄S hs₄z
  obtain ⟨hK₃Ω, hR₃mem, hR₃K, hR₃S⟩ := hconjdata s₃ hs₃S K R hK hRR hRK hRS
  obtain ⟨hK₄Ω, hR₄mem, hR₄K, hR₄S⟩ := hconjdata s₄ hs₄S K R hK hRR hRK hRS
  have hK₃z : IsUniqueInvolution (conjSub s₃ K) z := by
    have := hz.conj s₃
    rwa [hs₃z] at this
  have hK₄z : IsUniqueInvolution (conjSub s₄ K) z := by
    have := hz.conj s₄
    rwa [hs₄z] at this

  obtain ⟨u, huKW, hu4⟩ := hfour hK hRR hRK hRS
  obtain ⟨u', hu'KW, hu'4⟩ := hfour hK'Ω hR' hR'K' hR'S
  obtain ⟨ut, hut⟩ : ∃ ut, ut = t * u * t⁻¹ := ⟨_, rfl⟩
  obtain ⟨u't, hu't⟩ : ∃ u't, u't = t * u' * t⁻¹ := ⟨_, rfl⟩
  have huS : u ∈ (S : Subgroup G) := hWS huKW.2
  have hu'S : u' ∈ (S : Subgroup G) := hWS hu'KW.2
  have hutS : ut ∈ (S : Subgroup G) := by
    rw [hut]; exact S.mul_mem (S.mul_mem htS huS) (S.inv_mem htS)
  have hu'tS : u't ∈ (S : Subgroup G) := by
    rw [hu't]; exact S.mul_mem (S.mul_mem htS hu'S) (S.inv_mem htS)
  have hutK : ut ∈ conjSub t K := hut ▸ conj_mem_conjSub huKW.1
  have hu'tK : u't ∈ conjSub t K' := hu't ▸ conj_mem_conjSub hu'KW.1
  have hu2 : u * u = z := sq_eq_of_orderOf_four hz huKW.1 hu4
  have hu'2 : u' * u' = z := sq_eq_of_orderOf_four hz' hu'KW.1 hu'4
  have hut2 : ut * ut = zt := by
    rw [hut, hzt, ← hu2]; group
  have hu't2 : u't * u't = zt := by
    rw [hu't, hzt, ← hu'2]; group
  have ht1 : t * u * t⁻¹ = ut := hut.symm
  have ht3 : t * u' * t⁻¹ = u't := hu't.symm
  have ht2' : t * ut * t⁻¹ = u := by
    rw [hut]
    have : t * (t * u * t⁻¹) * t⁻¹ = (t * t) * u * (t * t)⁻¹ := by group
    rw [this, ht2]; group
  have ht4 : t * u't * t⁻¹ = u' := by
    rw [hu't]
    have : t * (t * u' * t⁻¹) * t⁻¹ = (t * t) * u' * (t * t)⁻¹ := by group
    rw [this, ht2]; group

  have hKK' : K ≠ K' := Ne.symm hne
  have hKKt : K ≠ conjSub t K := ne_of_involution_ne hz hzt1 hzzt
  have hKK't : K ≠ conjSub t K' := ne_of_involution_ne hz hz't1 hzzt
  have hK'Kt : K' ≠ conjSub t K := ne_of_involution_ne hz' hzt1 hzzt
  have hK'K't : K' ≠ conjSub t K' := ne_of_involution_ne hz' hz't1 hzzt
  have hKtK't : conjSub t K ≠ conjSub t K' := fun h' => hne ((conjSub_inj t).mp h').symm

  have huut : u * ut = ut * u :=
    hcmm K (conjSub t K) R (conjSub t R) hK hKtΩ hKKt hRR hRK hRS hRtmem hRtK hRtS u
      ⟨huKW.1, huS⟩ ut ⟨hutK, hutS⟩
  have huu' : u * u' = u' * u :=
    hcmm K K' R R' hK hK'Ω hKK' hRR hRK hRS hR' hR'K' hR'S u ⟨huKW.1, huS⟩ u'
      ⟨hu'KW.1, hu'S⟩
  have huu't : u * u't = u't * u :=
    hcmm K (conjSub t K') R (conjSub t R') hK hK'tΩ hKK't hRR hRK hRS hR'tmem hR'tK
      hR'tS u ⟨huKW.1, huS⟩ u't ⟨hu'tK, hu'tS⟩
  have hutu' : ut * u' = u' * ut :=
    hcmm (conjSub t K) K' (conjSub t R) R' hKtΩ hK'Ω (Ne.symm hK'Kt) hRtmem hRtK hRtS hR' hR'K'
      hR'S ut ⟨hutK, hutS⟩ u' ⟨hu'KW.1, hu'S⟩
  have hutu't : ut * u't = u't * ut :=
    hcmm (conjSub t K) (conjSub t K') (conjSub t R) (conjSub t R') hKtΩ hK'tΩ hKtK't hRtmem hRtK
      hRtS hR'tmem hR'tK hR'tS ut ⟨hutK, hutS⟩ u't ⟨hu'tK, hu'tS⟩
  have hu'u't : u' * u't = u't * u' :=
    hcmm K' (conjSub t K') R' (conjSub t R') hK'Ω hK'tΩ hK'K't hR' hR'K' hR'S hR'tmem hR'tK
      hR'tS u' ⟨hu'KW.1, hu'S⟩ u't ⟨hu'tK, hu'tS⟩

  have hu_inf : u ∈ K ⊓ (S : Subgroup G) := ⟨huKW.1, huS⟩
  have huR : u ∈ R := by
    rw [← hKS]
    exact hu_inf
  obtain ⟨y, hyR, hy1⟩ : ∃ y ∈ R, y * u ≠ u * y := by
    by_contra hcon
    push Not at hcon
    have := hquat.sq_eq_one_of_central huR
      (fun y hy => (hcon y hy).symm)
    exact hz.ne_one (hu2 ▸ this)
  have hyin : y ∈ K ⊓ (S : Subgroup G) := ⟨hRK hyR, hRS hyR⟩
  have hy2 : y * ut = ut * y :=
    hcmm K (conjSub t K) R (conjSub t R) hK hKtΩ hKKt hRR hRK hRS hRtmem hRtK hRtS y
      hyin ut ⟨hutK, hutS⟩
  have hy3 : y * u' = u' * y :=
    hcmm K K' R R' hK hK'Ω hKK' hRR hRK hRS hR' hR'K' hR'S y hyin u'
      ⟨hu'KW.1, hu'S⟩
  have hy4 : y * u't = u't * y :=
    hcmm K (conjSub t K') R (conjSub t R') hK hK'tΩ hKK't hRR hRK hRS hR'tmem hR'tK
      hR'tS y hyin u't ⟨hu'tK, hu'tS⟩
  have hb : b = z * zt := by rw [hbdef, hzt]
  have hb2 : b * b = 1 := hBb.sq
  obtain ⟨he2, he1, he3, hebc, het⟩ := core4 hu2 hut2 hu'2 hu't2 huut huu' huu't hutu' hutu't
    hu'u't hb hb2 ht1 ht2' ht3 ht4 hy1 hy2 hy3 hy4
  obtain ⟨e, he⟩ : ∃ e, e = (u * ut) * (u' * u't)⁻¹ := ⟨_, rfl⟩
  rw [← he] at he2 he1 he3 hebc het
  have hutW : ut ∈ W := by
    rw [hut]
    have := conj_mem_conjSub (n := t) huKW.2
    rwa [hWn t htS] at this
  have hu'tW : u't ∈ W := by
    rw [hu't]
    have := conj_mem_conjSub (n := t) hu'KW.2
    rwa [hWn t htS] at this
  have heW : e ∈ W := by
    rw [he]
    exact W.mul_mem (W.mul_mem huKW.2 hutW) (W.inv_mem (W.mul_mem hu'KW.2 hu'tW))

  have hcent : ∀ M R₀ : Subgroup G, M ∈ Ω → R₀ ∈ RSet Ω → R₀ ≤ M → R₀ ≤ (S : Subgroup G) →
      M ≠ K → M ≠ conjSub t K → M ≠ K' → M ≠ conjSub t K' →
      ∀ y' ∈ R₀, y' * e = e * y' ∧ y' * b = b * y' := by
    intro M R₀ hM hR₀ hR₀M hR₀S hMK hMKt hMK' hMK't y' hy'
    have hy'in : y' ∈ M ⊓ (S : Subgroup G) := ⟨hR₀M hy', hR₀S hy'⟩
    have cu : Commute y' u :=
      hcmm M K R₀ R hM hK hMK hR₀ hR₀M hR₀S hRR hRK hRS y' hy'in u hu_inf
    have cut : Commute y' ut :=
      hcmm M (conjSub t K) R₀ (conjSub t R) hM hKtΩ hMKt hR₀ hR₀M hR₀S hRtmem hRtK hRtS y' hy'in
        ut ⟨hutK, hutS⟩
    have cu' : Commute y' u' :=
      hcmm M K' R₀ R' hM hK'Ω hMK' hR₀ hR₀M hR₀S hR' hR'K' hR'S y' hy'in u' ⟨hu'KW.1, hu'S⟩
    have cu't : Commute y' u't :=
      hcmm M (conjSub t K') R₀ (conjSub t R') hM hK'tΩ hMK't hR₀ hR₀M hR₀S hR'tmem hR'tK hR'tS
        y' hy'in u't ⟨hu'tK, hu'tS⟩
    refine ⟨?_, ?_⟩
    · rw [he]
      exact (((cu.mul_right cut).mul_right ((cu'.mul_right cu't).inv_right))).eq
    · rw [hb, ← hu2, ← hut2]
      exact ((cu.mul_right cu).mul_right (cut.mul_right cut)).eq

  have hK₃tw : conjSub s₃ K ∈ twinSet Ω K := ⟨hK₃Ω, z, hz, hK₃z⟩
  have hK₄tw : conjSub s₄ K ∈ twinSet Ω K := ⟨hK₄Ω, z, hz, hK₄z⟩
  have hK₄tw' : conjSub s₄ K ∈ twinSet Ω (conjSub s₃ K) := ⟨hK₄Ω, z, hK₃z, hK₄z⟩
  have hZ : ∀ x : G, x ≠ 1 → x * x = 1 → (∀ y' ∈ conjSub s₃ R, y' * x = x * y') →
      (∀ y' ∈ conjSub s₄ R, y' * x = x * y') → Subgroup.centralizer ({x} : Set G) ≤ H := by
    intro x hx1 hx2 hc3 hc4
    have hA2 : IsPGroup 2 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_two_of_sq hx1 hx2]; norm_num)
    have hsup : conjSub s₃ R ⊔ conjSub s₄ R ≤
        Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      rw [centralizer_zpowers_eq_singleton]
      refine sup_le (fun y' hy' => ?_) (fun y' hy' => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hc3 y' hy'
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hc4 y' hy'
    have hXne : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≠ ⊤ := by
      rw [centralizer_zpowers_eq_singleton]
      exact hnt hx1
    have := hZ0 hK₃tw hK₄tw (Ne.symm hne34) hR₃mem hR₃K hR₃S hR₄mem hR₄K hR₄S hK₄tw' x hx1 hx2 hA2
      hsup hXne
    rwa [centralizer_zpowers_eq_singleton] at this
  have hne3 : ∀ M : Subgroup G, M = conjSub s₃ K → M ≠ conjSub t K ∧ M ≠ conjSub t K' := by
    rintro M rfl
    exact ⟨ne_of_involution_ne hK₃z hzt1 hzzt, ne_of_involution_ne hK₃z hz't1 hzzt⟩
  have hne4 : ∀ M : Subgroup G, M = conjSub s₄ K → M ≠ conjSub t K ∧ M ≠ conjSub t K' := by
    rintro M rfl
    exact ⟨ne_of_involution_ne hK₄z hzt1 hzzt, ne_of_involution_ne hK₄z hz't1 hzzt⟩
  have hc3 := hcent (conjSub s₃ K) (conjSub s₃ R) hK₃Ω hR₃mem hR₃K hR₃S hK₃K
    (hne3 _ rfl).1 hK₃K' (hne3 _ rfl).2
  have hc4 := hcent (conjSub s₄ K) (conjSub s₄ R) hK₄Ω hR₄mem hR₄K hR₄S hK₄K
    (hne4 _ rfl).1 hK₄K' (hne4 _ rfl).2
  have hbt : b * t = t * b := Subgroup.mem_centralizer_singleton_iff.mp (hBt hBb.mem)
  have hte : e * t = t * e := (mul_inv_eq_iff_eq_mul.mp het).symm
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hbe1 : b * e ≠ 1 := by
    intro h'
    apply he3
    have := eq_inv_of_mul_eq_one_right h'
    rw [this, hbi]
  have hbe2 : (b * e) * (b * e) = 1 := by
    calc (b * e) * (b * e) = b * (e * b) * e := by group
      _ = b * (b * e) * e := by rw [hebc]
      _ = (b * b) * (e * e) := by group
      _ = 1 := by rw [hb2, he2, one_mul]
  have hbet : (b * e) * t = t * (b * e) := by
    calc (b * e) * t = b * (e * t) := by group
      _ = b * (t * e) := by rw [hte]
      _ = (b * t) * e := by group
      _ = (t * b) * e := by rw [hbt]
      _ = t * (b * e) := by group
  have hu'R : u' ∈ R' := by
    rw [← hKS']
    exact ⟨hu'KW.1, hu'S⟩
  have hshape : D4Shape (S : Subgroup G) t b e := by
    have hne₁₂ : R ≠ R' := orb4_rset_ne_of_ne hΩ hK hK'Ω hKK' hRR hRK hR'K'
    have hne₁₃ : R ≠ conjSub t R := orb4_rset_ne_of_ne hΩ hK hKtΩ hKKt hRR hRK (conjSub_mono hRK)
    have hne₁₄ : R ≠ conjSub t R' := orb4_rset_ne_of_ne hΩ hK hK'tΩ hKK't hRR hRK (conjSub_mono hR'K')
    have hne₂₃ : R' ≠ conjSub t R := orb4_rset_ne_of_ne hΩ hK'Ω hKtΩ hK'Kt hR' hR'K' (conjSub_mono hRK)
    have hne₂₄ : R' ≠ conjSub t R' :=
      orb4_rset_ne_of_ne hΩ hK'Ω hK'tΩ hK'K't hR' hR'K' (conjSub_mono hR'K')
    have hshape0 := shape_noncommute hΩ S hWn hWab hQ8 hRR hR' hRS hR'S htS ht2 hne₁₂ hne₁₃ hne₁₄
      hne₂₃ hne₂₄ huR huKW.2 hu4 hu'R hu'KW.2 hu'4 hu2 hu'2
      (fun h' => hzzt (by rw [hzt]; exact h'.symm))
    rw [hb, he, hzt, hut, hu't]
    exact hshape0
  refine ⟨b, e, ⟨hBb.ne_one, hb2, hbt, hbH⟩,
    ⟨he1, he2, hte, hZ e he1 he2 (fun y' hy' => (hc3 y' hy').1) (fun y' hy' => (hc4 y' hy').1)⟩,
    ⟨hbe1, hbe2, hbet, hZ (b * e) hbe1 hbe2 ?_ ?_⟩, hebc.symm, hbW, heW, hshape⟩
  · intro y' hy'
    obtain ⟨h1, h2⟩ := hc3 y' hy'
    calc y' * (b * e) = (y' * b) * e := by group
      _ = (b * y') * e := by rw [h2]
      _ = b * (y' * e) := by group
      _ = b * (e * y') := by rw [h1]
      _ = (b * e) * y' := by group
  · intro y' hy'
    obtain ⟨h1, h2⟩ := hc4 y' hy'
    calc y' * (b * e) = (y' * b) * e := by group
      _ = (b * y') * e := by rw [h2]
      _ = b * (y' * e) := by group
      _ = b * (e * y') := by rw [h1]
      _ = (b * e) * y' := by group

end NonCommute

section NonCommuteMin

variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCexQ8.goodFourD_of_noncommute (h : E18_6Q8) (h4 : E18_4CQ8)
    (c : MinCexQ8 Ω K S R W H) {z g t : G} (hz : IsUniqueInvolution K z) (hzW : z ∈ W)
    (hzH : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hSylz : IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
      (Subgroup.centralizer ({z} : Set G)))
    (hg : g ∉ H) (ht : t = g * z * g⁻¹) (htS : t ∈ (S : Subgroup G)) (hnc : ¬ t * z = z * t) :
    GoodFourWD (S : Subgroup G) H W t := by
  classical
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hA : EtaAbelian Ω := etaAbelian_of_gen hΩ
  have hM : EtaMeet Ω := etaMeet_of_gen hΩ
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨-, hWS, hWn⟩ := c.stand.hW
  obtain ⟨K', hK'tw, hne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  exact goodFourD_of_noncommute_of (K' := K') (R' := R') (z := z) (g := g) (t := t) hΩ
    c.isQ8_of_mem_RSet c.W_abelian
    (fun M₁ M₂ R₁ R₂ hM₁ hM₂ hne hR₁ hR₁M hR₁S hR₂ hR₂M hR₂S =>
      commutes_inf_S h hΩ hM₁ hM₂ hne hR₁ hR₁M hR₁S hR₂ hR₂M hR₂S)
    (fun hM' hR₀ hR₀M hR₀S => by
      obtain ⟨-, u, hu, hu4⟩ := c.exists_order_four_of_inf_W hA hM hM' hR₀ hR₀M hR₀S
      exact ⟨u, hu, hu4⟩)
    (inf_S_eq_of_mem_RSet hΩ c.stand.mem hRR hRK hRS) (Sec6Gen.isQuatSub_of_mem_RSet hΩ hRR)
    (fun hx1 => c.centralizer_ne_top h hx1)
    (fun hK₃tw hK₄tw hne43 hR₃ hR₃K hR₃S hR₄ hR₄K hR₄S hK₄tw' x hx1 hx2 hA2 hsup hXne =>
      (c.rename h hK₃tw hR₃ hR₃K hR₃S hK₄tw hne43 hR₄ hR₄K hR₄S).centralizer_le_H' h4 hK₄tw'
        hne43 hR₄ hR₄K hR₄S hA2 ⟨x, hx1, hx2, rfl⟩ hsup hXne)
    c.stand.mem hRR hRK hRS hWS hWn hK'tw hne hR' hR'K' hR'S
    (inf_S_eq_of_mem_RSet hΩ hK'tw.1 hR' hR'K' hR'S) hz ht htS hnc
    (c.exists_two_twins h hz hzW hzH hSylz hg ht htS hnc (K' := K'))

end NonCommuteMin

section ChooseT

variable {G : Type} [Group G] [Finite G]

theorem orb4_natCard_conjSub (n : G) (K : Subgroup G) : Nat.card (conjSub n K) = Nat.card K :=
  Subgroup.card_map_of_injective (MulAut.conj n).injective

theorem orb4_exists_conj_le_sylow {S : Sylow 2 G} {H : Subgroup G} (hSH : (S : Subgroup G) ≤ H)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPH : P ≤ H) :
    ∃ h ∈ H, conjSub h P ≤ (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 H := S.subtype hSH
  have hW : IsPGroup 2 (P.subgroupOf H) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  obtain ⟨Q, hQ⟩ := hW.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq H Q S'
  refine ⟨(m : G), m.2, ?_⟩
  intro x hx
  rw [mem_conjSub_iff] at hx
  have hxH : (m : G)⁻¹ * x * (m : G) ∈ H := hPH hx
  have hyQ : (⟨(m : G)⁻¹ * x * (m : G), hxH⟩ : H) ∈ (Q : Subgroup H) :=
    hQ (Subgroup.mem_subgroupOf.mpr hx)
  have hmem : MulAut.conj m (⟨(m : G)⁻¹ * x * (m : G), hxH⟩ : H) ∈
      ((m • Q : Sylow 2 H) : Subgroup H) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hyQ
  rw [hm] at hmem
  have hmem' : MulAut.conj m (⟨(m : G)⁻¹ * x * (m : G), hxH⟩ : H) ∈
      (S : Subgroup G).subgroupOf H := by
    rw [← Sylow.coe_subtype S hSH]
    exact hmem
  have e : ((MulAut.conj m (⟨(m : G)⁻¹ * x * (m : G), hxH⟩ : H) : H) : G) = x := by
    simp [MulAut.conj_apply]
    group
  have := Subgroup.mem_subgroupOf.mp hmem'
  rwa [e] at this

theorem exists_good_t {S : Sylow 2 G} {H : Subgroup G} (hSH : (S : Subgroup G) ≤ H) {z g₁ : G}
    (hg₁ : g₁ ∉ H) (ht₁S : g₁ * z * g₁⁻¹ ∈ (S : Subgroup G)) :
    ∃ g₃ : G, g₃ ∉ H ∧ g₃ * z * g₃⁻¹ ∈ (S : Subgroup G) ∧
      IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({g₃ * z * g₃⁻¹} : Set G))
        (Subgroup.centralizer ({g₃ * z * g₃⁻¹} : Set G) ⊓ H) := by
  classical
  obtain ⟨t₁, ht₁⟩ : ∃ t₁, t₁ = g₁ * z * g₁⁻¹ := ⟨_, rfl⟩
  rw [← ht₁] at ht₁S
  let 𝒯 : Set G := {s | s ∈ (S : Subgroup G) ∧ ∃ h ∈ H, s = h * t₁ * h⁻¹}
  have hne : 𝒯.Nonempty := ⟨t₁, ht₁S, 1, H.one_mem, by simp⟩
  haveI : Nonempty ↥𝒯 := hne.to_subtype
  obtain ⟨⟨s, hsS, h₀, hh₀, hs⟩, hmax⟩ := Finite.exists_max
    (fun x : ↥𝒯 => Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer ({(x : G)} : Set G)))
  have e : h₀ * g₁ * z * (h₀ * g₁)⁻¹ = s := by rw [hs, ht₁]; group
  refine ⟨h₀ * g₁, fun hmem => hg₁ ?_, by rw [e]; exact hsS, ?_⟩
  · have := H.mul_mem (H.inv_mem hh₀) hmem
    simpa using this
  rw [e]
  set P₀ : Subgroup G := (S : Subgroup G) ⊓ Subgroup.centralizer ({s} : Set G) with hP₀def
  have hP₀2 : IsPGroup 2 ↥P₀ := S.isPGroup'.to_le inf_le_left
  have hP₀H : P₀ ≤ Subgroup.centralizer ({s} : Set G) ⊓ H :=
    le_inf inf_le_right (inf_le_left.trans hSH)
  obtain ⟨P, hP, hP₀P⟩ := IsSylow2In.exists_ge hP₀2 hP₀H
  obtain ⟨h, hhH, hhP⟩ := orb4_exists_conj_le_sylow hSH hP.2.1 (hP.1.trans inf_le_right)
  have hsP : s ∈ P := hP₀P ⟨hsS, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hs'S : h * s * h⁻¹ ∈ (S : Subgroup G) := hhP (conj_mem_conjSub hsP)
  have hs'𝒯 : h * s * h⁻¹ ∈ 𝒯 := ⟨hs'S, h * h₀, H.mul_mem hhH hh₀, by rw [hs]; group⟩
  have hle : conjSub h P ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ({h * s * h⁻¹} : Set G) := by
    refine le_inf hhP (fun x hx => ?_)
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [mem_conjSub_iff] at hx
    have h1 : s * (h⁻¹ * x * h) = (h⁻¹ * x * h) * s :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hP.1 hx).1).symm
    calc x * (h * s * h⁻¹) = h * ((h⁻¹ * x * h) * s) * h⁻¹ := by group
      _ = h * (s * (h⁻¹ * x * h)) * h⁻¹ := by rw [h1]
      _ = (h * s * h⁻¹) * x := by group
  have hcard := hmax ⟨h * s * h⁻¹, hs'𝒯⟩
  have h1 : Nat.card P ≤ Nat.card P₀ := by
    calc Nat.card P = Nat.card (conjSub h P) := (orb4_natCard_conjSub h P).symm
      _ ≤ Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer ({h * s * h⁻¹} : Set G)) :=
        Subgroup.card_le_of_le hle
      _ ≤ Nat.card P₀ := hcard
  have hPeq : P₀ = P := Subgroup.eq_of_le_of_card_ge hP₀P h1
  rw [← hPeq] at hP
  exact hP

end ChooseT

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
