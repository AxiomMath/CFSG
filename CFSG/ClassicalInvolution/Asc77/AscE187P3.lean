module

public import CFSG.ClassicalInvolution.Asc77.AscE187P2
public import CFSG.ClassicalInvolution.Asc77.AscSixZW
public import CFSG.ClassicalInvolution.Asc77.AscSteps185

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.exists_z (c : MinCex p f Ω K S R W H) :
    ∃ z : G, IsUniqueInvolution K z ∧ z ∈ W ∧ Subgroup.centralizer ({z} : Set G) ≤ H := by
  obtain ⟨z, hz, hzW⟩ := e18_zW p f G Ω K S R W H c
  exact ⟨z, hz, hzW, c.centralizer_le p f hz⟩

theorem inf_S_eq_of_mem_RSet (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {S : Sylow 2 G}
    {M R' : Subgroup G} (hM : M ∈ Ω) (hR' : R' ∈ RSet Ω) (hR'M : R' ≤ M)
    (hR'S : R' ≤ (S : Subgroup G)) : M ⊓ (S : Subgroup G) = R' := by
  have hsyl : IsSylow2In R' M := hΩ.isSylow2In_of_mem_RSet_of_le hp hM hR' hR'M
  exact hsyl.eq_of_le (S.isPGroup'.to_le inf_le_right) inf_le_left (le_inf hR'M hR'S)

theorem MinCex.inf_W_mem_USet (c : MinCex p f Ω K S R W H) (hA : EtaAbelian Ω) (hM : EtaMeet Ω)
    {M R' : Subgroup G} (hMΩ : M ∈ Ω) (hR' : R' ∈ RSet Ω) (hR'M : R' ≤ M)
    (hR'S : R' ≤ (S : Subgroup G)) : M ⊓ W ∈ USet Ω := by
  obtain ⟨η, hη, hWη, hηU, -, -⟩ := c.exists_eta hA
  have h2 : 2 < Nat.card ↥(M ⊓ (S : Subgroup G)) := by
    have h8 := c.stand.hyp.eight_le_of_mem_RSet c.stand.odd hR'
    have := Subgroup.card_le_of_le (le_inf hR'M hR'S)
    omega
  have hmem := hM S η hη (fun V hV => (hηU V hV).2) M hMΩ h2
  rw [← hWη] at hmem
  exact (hηU _ hmem).1

theorem MinCex.exists_order_four_of_inf_W (c : MinCex p f Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {M R' : Subgroup G} (hMΩ : M ∈ Ω) (hR' : R' ∈ RSet Ω) (hR'M : R' ≤ M)
    (hR'S : R' ≤ (S : Subgroup G)) :
    IsCyclic ↥(M ⊓ W) ∧ ∃ u ∈ M ⊓ W, orderOf u = 4 := by
  have hU := c.inf_W_mem_USet hA hM hMΩ hR' hR'M hR'S
  obtain ⟨R'', -, J, -, hRJ, hUR, hcyc, -, h4⟩ :=
    c.stand.hyp.exists_data_of_mem_USet c.stand.odd hU
  refine ⟨hcyc, ?_⟩
  obtain ⟨u, hu, hu4⟩ := exists_orderOf_eq_four_of_isPGroup_of_isCyclic
    (c.stand.hyp.isPGroup_of_mem_USet c.stand.odd hU) hcyc h4
  exact ⟨u, hu, hu4⟩

theorem E187C.hbad_of_conj_of (hc : ConjInvariant Ω)
    (hdc : ∀ {M : Subgroup G}, M ∈ twinSet Ω K → M ∈ dstarComp Ω K)
    (hmc : ∀ {M : Subgroup G} {u x : G}, M ∈ dstarComp Ω K → u ∈ M → orderOf u = 4 →
      x * u * x⁻¹ ∈ H → x ∈ H)
    {z g : G} (hz : IsUniqueInvolution K z) (hg : g ∉ H) :
    ∀ M ∈ Ω, IsUniqueInvolution M (g * z * g⁻¹) → ∀ u ∈ M, orderOf u = 4 → u ∉ H := by
  intro M hMΩ hMt u hu hu4 huH
  have hM₀ : IsUniqueInvolution (conjSub g⁻¹ M) z := by
    have := hMt.conj g⁻¹
    rwa [show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at this
  have hM₀tw : conjSub g⁻¹ M ∈ twinSet Ω K := ⟨hc g⁻¹ M hMΩ, z, hz, hM₀⟩
  have hM₀S : conjSub g⁻¹ M ∈ dstarComp Ω K := hdc hM₀tw
  have hu₀ : g⁻¹ * u * g ∈ conjSub g⁻¹ M := by
    rw [mem_conjSub_iff, inv_inv]
    have e : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
    rw [e]
    exact hu
  have hu₀4 : orderOf (g⁻¹ * u * g) = 4 := by
    have := orderOf_conj_mul_inv_eq g⁻¹ u
    simpa using this.trans hu4
  have := hmc hM₀S hu₀ hu₀4 (x := g) (by
    have e : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
    rw [e]
    exact huH)
  exact hg this


theorem E187C.hC_of_conj_of
    (hdc : ∀ {M : Subgroup G}, M ∈ twinSet Ω K → M ∈ dstarComp Ω K)
    (hmc : ∀ {M : Subgroup G} {u x : G}, M ∈ dstarComp Ω K → u ∈ M → orderOf u = 4 →
      x * u * x⁻¹ ∈ H → x ∈ H)
    {z g : G} (hz : IsUniqueInvolution K z) (hzH : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hg : g ∉ H) :
    ∀ M ∈ Ω, IsUniqueInvolution M z → ∀ x ∈ M, orderOf x = 4 →
      (g * z * g⁻¹) * x ≠ x * (g * z * g⁻¹) := by
  intro M hMΩ hMz x hx hx4 hcomm
  have hMtw : M ∈ twinSet Ω K := ⟨hMΩ, z, hz, hMz⟩
  have hMS : M ∈ dstarComp Ω K := hdc hMtw
  have hcz : z * (g⁻¹ * x * g) = (g⁻¹ * x * g) * z := by
    have e1 : g⁻¹ * ((g * z * g⁻¹) * x) * g = z * (g⁻¹ * x * g) := by group
    have e2 : g⁻¹ * (x * (g * z * g⁻¹)) * g = (g⁻¹ * x * g) * z := by group
    rw [← e1, ← e2, hcomm]
  have hyH : g⁻¹ * x * g ∈ H := by
    apply hzH
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcz.symm
  have := hmc hMS hx hx4 (x := g⁻¹) (by simpa using hyH)
  exact hg (by simpa using H.inv_mem this)


theorem MinCex.hbad_of_conj (c : MinCex p f Ω K S R W H) (hA : EtaAbelian Ω) (hM : EtaMeet Ω)
    {z g : G} (hz : IsUniqueInvolution K z) (hg : g ∉ H) :
    ∀ M ∈ Ω, IsUniqueInvolution M (g * z * g⁻¹) → ∀ u ∈ M, orderOf u = 4 → u ∉ H := by
  exact E187C.hbad_of_conj_of c.stand.hyp.conjInvariant (fun hM => mem_dstarComp_of_twin c.stand.odd c.stand.hyp c.stand.mem hM)
    (fun hMS hu hu4 hx => c.mem_of_conj_mem_dstar hA hM hMS hu hu4 hx) hz hg

theorem MinCex.hC_of_conj (c : MinCex p f Ω K S R W H) (hA : EtaAbelian Ω) (hM : EtaMeet Ω)
    {z g : G} (hz : IsUniqueInvolution K z) (hzH : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hg : g ∉ H) :
    ∀ M ∈ Ω, IsUniqueInvolution M z → ∀ x ∈ M, orderOf x = 4 →
      (g * z * g⁻¹) * x ≠ x * (g * z * g⁻¹) := by
  exact E187C.hC_of_conj_of (fun hM => mem_dstarComp_of_twin c.stand.odd c.stand.hyp c.stand.mem hM)
    (fun hMS hu hu4 hx => c.mem_of_conj_mem_dstar hA hM hMS hu hu4 hx) hz hzH hg

theorem E187C.goodFour_of_commute_of {Q : Prop} {Wp : G → Prop} {z g t : G} {K' R' : Subgroup G}
    (hc : ConjInvariant Ω)
    (hkp : ∀ {K₁ K₂ : Subgroup G} {z₀ : G}, K₁ ∈ Ω → K₂ ∈ Ω → IsUniqueInvolution K₁ z₀ →
      IsUniqueInvolution K₂ z₀ → K₁ ∈ KPerp Ω K₂)
    (hKSeq : ∀ {M R₀ : Subgroup G}, M ∈ Ω → R₀ ∈ RSet Ω → R₀ ≤ M → R₀ ≤ (S : Subgroup G) →
      M ⊓ (S : Subgroup G) = R₀)
    (hfour : ∀ {M R₀ : Subgroup G}, M ∈ Ω → R₀ ∈ RSet Ω → R₀ ≤ M → R₀ ≤ (S : Subgroup G) →
      IsCyclic ↥(M ⊓ W) ∧ ∃ u ∈ M ⊓ W, orderOf u = 4)
    (hcmmtw : ∀ {K₁ J : Subgroup G} {z₀ : G} {A B : Subgroup G}, K₁ ∈ Ω → J ∈ Ω → K₁ ≠ J →
      IsUniqueInvolution K₁ z₀ → IsUniqueInvolution J z₀ → A ≤ K₁ → B ≤ J →
      IsPGroup 2 ↥(A ⊔ B) → Commutes A B)
    (hC : ∀ M ∈ Ω, IsUniqueInvolution M z → ∀ x ∈ M, orderOf x = 4 → t * x ≠ x * t)
    (hfixed : IsPGroup 2 ↥(R ⊔ R') → K ∈ Ω → K' ∈ Ω → K ≠ K' → IsUniqueInvolution K z →
      IsUniqueInvolution K' z → t * z = z * t → conjSub t K = K → conjSub t K' = K' →
      conjSub t W = W → IsCyclic ↥(K ⊓ W) → IsCyclic ↥(K' ⊓ W) → ∀ u u' : G, u ∈ K → u ∈ W →
      u ∈ R → orderOf u = 4 → u' ∈ K' → u' ∈ W → u' ∈ R' → orderOf u' = 4 →
      (∀ M ∈ Ω, IsUniqueInvolution M z → ∀ x ∈ M, orderOf x = 4 → t * x ≠ x * t) →
      Subgroup.centralizer ({z} : Set G) ≤ H →
      (∀ a ∈ R ⊔ R', Wp a → a ≠ 1 → a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H) → Q)
    (hswap : ∀ {K₀ R₀ : Subgroup G} {u : G}, IsPGroup 2 ↥(R₀ ⊔ conjSub t R₀) → K₀ ∈ Ω →
      IsUniqueInvolution K₀ z → t * t = 1 → t * z = z * t → conjSub t K₀ ≠ K₀ → u ∈ K₀ →
      u ∈ R₀ → orderOf u = 4 → u ∈ W → (∀ x ∈ W, t * x * t⁻¹ ∈ W) →
      Subgroup.centralizer ({z} : Set G) ≤ H →
      (∀ a ∈ R₀ ⊔ conjSub t R₀, Wp a → a ≠ 1 → a * a = 1 →
        Subgroup.centralizer ({a} : Set G) ≤ H) → Q)
    (hcent : ∀ {K₀ J R₀ R₂ : Subgroup G}, K₀ ∈ twinSet Ω K → J ∈ KPerp Ω K₀ → R₀ ∈ RSet Ω →
      R₀ ≤ K₀ → R₀ ≤ (S : Subgroup G) → R₂ ∈ RSet Ω → R₂ ≤ J → Commutes R₀ R₂ →
      ∀ a ∈ R₀ ⊔ R₂, Wp a → a ≠ 1 → a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H)
    (hK : K ∈ Ω) (hRR : R ∈ RSet Ω) (hRK : R ≤ K) (hRS : R ≤ (S : Subgroup G))
    (hWS : W ≤ (S : Subgroup G)) (hWn : ∀ s ∈ (S : Subgroup G), conjSub s W = W)
    (hK'tw : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K')
    (hR'S : R' ≤ (S : Subgroup G)) (hz : IsUniqueInvolution K z)
    (hzH : Subgroup.centralizer ({z} : Set G) ≤ H) (ht : t = g * z * g⁻¹)
    (htS : t ∈ (S : Subgroup G)) (hcomm : t * z = z * t) : Q := by
  have ht2 : t * t = 1 := by
    rw [ht]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  have htW : conjSub t W = W := hWn t htS
  have hWt : ∀ x ∈ W, t * x * t⁻¹ ∈ W := fun x hx => by
    have := conj_mem_conjSub (n := t) hx
    rwa [htW] at this
  have htSt : conjSub t (S : Subgroup G) = S := conjSub_eq_self_of_mem htS
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
  have hK'perp : K' ∈ KPerp Ω K := hkp hK'Ω hK hz' hz
  have hKS : K ⊓ (S : Subgroup G) = R := hKSeq hK hRR hRK hRS
  have hK'S : K' ⊓ (S : Subgroup G) = R' := hKSeq hK'Ω hR' hR'K' hR'S
  have hmemR : ∀ u : G, u ∈ K → u ∈ W → u ∈ R := fun u huK huW => by
    have : u ∈ K ⊓ (S : Subgroup G) := ⟨huK, hWS huW⟩
    rwa [hKS] at this
  have hmemR' : ∀ u : G, u ∈ K' → u ∈ W → u ∈ R' := fun u huK huW => by
    have : u ∈ K' ⊓ (S : Subgroup G) := ⟨huK, hWS huW⟩
    rwa [hK'S] at this
  have htle : ∀ X : Subgroup G, X ≤ (S : Subgroup G) → conjSub t X ≤ (S : Subgroup G) :=
    fun X hX => (conjSub_mono (n := t) hX).trans htSt.le
  have hRR'2 : IsPGroup 2 ↥(R ⊔ R') := S.isPGroup'.to_le (sup_le hRS hR'S)
  have hR2 : IsPGroup 2 ↥(R ⊔ conjSub t R) := S.isPGroup'.to_le (sup_le hRS (htle R hRS))
  have hR'2 : IsPGroup 2 ↥(R' ⊔ conjSub t R') := S.isPGroup'.to_le (sup_le hR'S (htle R' hR'S))
  by_cases hnK : conjSub t K = K
  · by_cases hnK' : conjSub t K' = K'
    · obtain ⟨hcycK, u, huKW, hu4⟩ :=
        hfour hK hRR hRK hRS
      obtain ⟨hcycK', u', hu'KW, hu'4⟩ :=
        hfour hK'Ω hR' hR'K' hR'S
      have hcommRR' : Commutes R R' :=
        hcmmtw hK hK'Ω (Ne.symm hne) hz hz' hRK hR'K' hRR'2
      exact hfixed hRR'2 hK hK'Ω (Ne.symm hne) hz hz' hcomm hnK hnK' htW hcycK hcycK' u u'
        huKW.1 huKW.2 (hmemR u huKW.1 huKW.2) hu4 hu'KW.1 hu'KW.2 (hmemR' u' hu'KW.1 hu'KW.2) hu'4
        hC hzH
        (fun a ha haW ha1 ha2 => hcent hKtw hK'perp hRR hRK hRS hR' hR'K' hcommRR' a ha haW ha1
          ha2)
    · obtain ⟨hcycK', u', hu'KW, hu'4⟩ :=
        hfour hK'Ω hR' hR'K' hR'S
      have hK'tΩ : conjSub t K' ∈ Ω := hc t K' hK'Ω
      have hJ : conjSub t K' ∈ KPerp Ω K' := hkp hK'tΩ hK'Ω (hconjt K' hz') hz'
      have hcommR' : Commutes R' (conjSub t R') :=
        hcmmtw hK'Ω hK'tΩ (Ne.symm hnK') hz' (hconjt K' hz') hR'K'
          (conjSub_mono hR'K') hR'2
      exact hswap hR'2 hK'Ω hz' ht2 hcomm hnK' hu'KW.1 (hmemR' u' hu'KW.1 hu'KW.2) hu'4 hu'KW.2
        hWt hzH
        (fun a ha haW ha1 ha2 => hcent hK'tw hJ hR' hR'K' hR'S (RSet.conj hc hR' t)
          (conjSub_mono hR'K') hcommR' a ha haW ha1 ha2)
  · obtain ⟨hcycK, u, huKW, hu4⟩ :=
      hfour hK hRR hRK hRS
    have hKtΩ : conjSub t K ∈ Ω := hc t K hK
    have hJ : conjSub t K ∈ KPerp Ω K := hkp hKtΩ hK (hconjt K hz) hz
    have hcommR : Commutes R (conjSub t R) :=
      hcmmtw hK hKtΩ (Ne.symm hnK) hz (hconjt K hz) hRK
        (conjSub_mono hRK) hR2
    exact hswap hR2 hK hz ht2 hcomm hnK huKW.1 (hmemR u huKW.1 huKW.2) hu4 huKW.2 hWt hzH
      (fun a ha haW ha1 ha2 => hcent hKtw hJ hRR hRK hRS (RSet.conj hc hRR t)
        (conjSub_mono hRK) hcommR a ha haW ha1 ha2)

theorem MinCex.goodFour_of_commute (h : E187Hyps p f) (c : MinCex p f Ω K S R W H) {z g t : G}
    (hz : IsUniqueInvolution K z) (hzH : Subgroup.centralizer ({z} : Set G) ≤ H) (hg : g ∉ H)
    (ht : t = g * z * g⁻¹) (htS : t ∈ (S : Subgroup G)) (hcomm : t * z = z * t) :
    GoodFour H t := by
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  have hA : EtaAbelian Ω := h.etaAbelian hp hq hΩ
  have hM : EtaMeet Ω := h.etaMeet hp hq hΩ
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨-, hWS, hWn⟩ := c.stand.hW
  obtain ⟨K', hK'tw, hne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  exact E187C.goodFour_of_commute_of (z := z) (g := g) (t := t) (K' := K') (R' := R') (Q := GoodFour H t) (Wp := fun _ => True) hΩ.conjInvariant
    (fun hK₁ hK₂ hz₁ hz₂ => mem_kPerp_of_twin hΩ hK₁ hK₂ hz₁ hz₂)
    (fun hM' hR₀ hR₀M hR₀S => inf_S_eq_of_mem_RSet hp hΩ hM' hR₀ hR₀M hR₀S)
    (fun hM' hR₀ hR₀M hR₀S => c.exists_order_four_of_inf_W hA hM hM' hR₀ hR₀M hR₀S)
    (fun hK₁ hJ hKJ hz₁ hz₂ hA₁ hB₁ hAB => hΩ.commutes_of_twin_of_isPGroup hK₁ hJ hKJ hz₁ hz₂ hA₁ hB₁ hAB)
    (by have := c.hC_of_conj hA hM hz hzH hg; rwa [← ht] at this)
    (fun hR2 hK₁ hK'Ω hKK' hz₁ hz₂ htz htK htK' htW hUK hUK' u u' huK huW huR hu4 hu'K hu'W hu'R
        hu'4 hC' hzcent h2 =>
      goodFour_of_fixed hΩ hR2 hK₁ hK'Ω hKK' hz₁ hz₂ htz htK htK' htW hUK hUK' huK huW huR hu4
        hu'K hu'W hu'R hu'4 hC' hzcent (fun a ha ha1 ha2 => h2 a ha trivial ha1 ha2))
    (fun hR2 hK₁ hz₁ ht2 htz hnK huK huR hu4 huW hWt hzcent h2 =>
      goodFour_of_swap hΩ hR2 hK₁ hz₁ ht2 htz hnK huK huR hu4 hzcent
        (fun a ha ha1 ha2 => h2 a ha trivial ha1 ha2))
    (fun hK₀tw hJ hR₀ hR₀K₀ _ hR₂ hR₂J hcm a ha _ ha1 ha2 =>
      c.hyp.cent _ hK₀tw _ hJ _ _ hR₀ hR₀K₀ hR₂ hR₂J (Or.inl hcm) a ha ha1 ha2)
    c.stand.mem hRR hRK hRS hWS hWn hK'tw hne hR' hR'K' hR'S hz hzH ht htS hcomm

end CFSG.ClassicalInvolution.Asc77
