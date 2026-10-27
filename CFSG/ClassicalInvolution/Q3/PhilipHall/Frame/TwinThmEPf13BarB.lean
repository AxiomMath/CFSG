module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf3OddStand

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

namespace TwinThmE

section LiftB

variable {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}
  {N : Subgroup Y} [N.Normal]

theorem exists_lift_twin_pair_gen (hΛ : HypOmegaGen Λ) (hN : Odd (Nat.card N)) {K : Subgroup Y} {z : Y}
    (hK : K ∈ Λ) (hz : IsUniqueInvolution K z) {K'' : Subgroup (Y ⧸ N)}
    (hK'' : K'' ∈ twinSet (quotFamily Λ N) (K.map (QuotientGroup.mk' N)))
    (hne : K'' ≠ K.map (QuotientGroup.mk' N)) {Rb₁ Rb₂ : Subgroup (Y ⧸ N)}
    (hRb₁ : IsSylow2In Rb₁ (K.map (QuotientGroup.mk' N))) (hRb₂ : IsSylow2In Rb₂ K'')
    (hRbc : Commutes Rb₁ Rb₂) :
    ∃ K₃ ∈ twinSet Λ K, K₃ ≠ K ∧ K₃.map (QuotientGroup.mk' N) = K'' ∧
      ∃ R₁ R₃ : Subgroup Y, IsSylow2In R₁ K ∧ IsSylow2In R₃ K₃ ∧ Commutes R₁ R₃ ∧
        IsPGroup 2 ↥(R₁ ⊔ R₃) ∧ R₁.map (QuotientGroup.mk' N) = Rb₁ ∧
        R₃.map (QuotientGroup.mk' N) = Rb₂ := by
  set mk := QuotientGroup.mk' N with hmk
  
  obtain ⟨L, hLtw, hLmap⟩ := exists_lift_twin hΛ hN hK hK''
  obtain ⟨hLΛ, z₀, hz₀K, hz₀L⟩ := hLtw
  have hz₀ : z₀ = z := hz₀K.eq hz
  have hzL : IsUniqueInvolution L z := hz₀ ▸ hz₀L
  obtain ⟨R₁, hR₁, hR₁map⟩ := exists_lift_sylow hN hRb₁
  have hRb₂' : IsSylow2In Rb₂ (L.map mk) := by
    rw [hLmap]
    exact hRb₂
  obtain ⟨R₂, hR₂, hR₂map⟩ := exists_lift_sylow hN hRb₂'
  have hR₁2 : IsPGroup 2 R₁ := hR₁.2.1
  have hR₂2 : IsPGroup 2 R₂ := hR₂.2.1
  obtain ⟨m, hm, hP⟩ := exists_conj_isPGroup_sup hN hR₁2 hR₂2 (by rw [hR₁map, hR₂map]; exact hRbc)
  have hmk1 : mk m = 1 := (QuotientGroup.eq_one_iff _).mpr hm
  set L' : Subgroup Y := conjSub m L with hL'
  set R₃ : Subgroup Y := conjSub m R₂ with hR₃
  have hL'Λ : L' ∈ Λ := hΛ.conjInvariant m L hLΛ
  have hL'img : L'.map mk = K'' := by
    rw [hL', AscQuot.map_conjSub, hmk1, conjSub_one, hLmap]
  have hR₃syl : IsSylow2In R₃ L' := hR₂.conj m
  have hR₃img : R₃.map mk = Rb₂ := by
    rw [hR₃, AscQuot.map_conjSub, hmk1, conjSub_one, hR₂map]
  have hL'ne : L' ≠ K := by
    intro h
    apply hne
    rw [← hL'img, h]
  
  have hR₁Ω : R₁ ∈ RSet Λ := mem_RSet_of_isSylow2In hK hR₁
  have hR₃Ω : R₃ ∈ RSet Λ := mem_RSet_of_isSylow2In hL'Λ hR₃syl
  have h8₁ := hΛ.eight_le_of_mem_RSet hR₁Ω
  have h8₃ := hΛ.eight_le_of_mem_RSet hR₃Ω
  have hRne : R₁ ≠ R₃ := by
    intro h
    exact hL'ne (hΛ.eq_of_le_of_le hL'Λ hK hR₃syl.2.1 (by omega) hR₃syl.1 (h ▸ hR₁.1))
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  have hcomm : Commutes R₁ R₃ :=
    Q3CP.l67Gen Y Λ hΛ S R₁ hR₁Ω R₃ hR₃Ω (le_sup_left.trans hS) (le_sup_right.trans hS)
      hRne
  
  have hzR₁ : z ∈ R₁ := AscL62.mem_of_uniqueInvolution_of_pGroup hz hR₁.1 hR₁2 (by omega)
  have hz'L' : IsUniqueInvolution L' (m * z * m⁻¹) := hzL.conj m
  have hz'R₃ : m * z * m⁻¹ ∈ R₃ :=
    AscL62.mem_of_uniqueInvolution_of_pGroup hz'L' hR₃syl.1 hR₃syl.2.1 (by omega)
  have hzz' : z * (m * z * m⁻¹) = (m * z * m⁻¹) * z := hcomm z hzR₁ _ hz'R₃
  have hzz'1 : z * (m * z * m⁻¹) = 1 := by
    have hsq : (z * (m * z * m⁻¹)) * (z * (m * z * m⁻¹)) = 1 := by
      calc (z * (m * z * m⁻¹)) * (z * (m * z * m⁻¹))
          = z * ((m * z * m⁻¹) * z) * (m * z * m⁻¹) := by group
        _ = z * (z * (m * z * m⁻¹)) * (m * z * m⁻¹) := by rw [← hzz']
        _ = (z * z) * ((m * z * m⁻¹) * (m * z * m⁻¹)) := by group
        _ = 1 := by rw [hz.sq, hz'L'.sq, one_mul]
    have hmem : z * (m * z * m⁻¹) ∈ N := by
      refine (QuotientGroup.eq_one_iff _).mp ?_
      show mk _ = 1
      rw [map_mul, map_mul, map_mul, map_inv, hmk1, one_mul, inv_one, mul_one, ← map_mul, hz.sq,
        map_one]
    have hdvd : orderOf (z * (m * z * m⁻¹)) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hsq)
    have hodd : Odd (orderOf (z * (m * z * m⁻¹))) :=
      hN.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hmem)
    have h1 : orderOf (z * (m * z * m⁻¹)) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact orderOf_eq_one_iff.mp h1
  have hz'z : m * z * m⁻¹ = z := by
    have := eq_inv_of_mul_eq_one_right hzz'1
    rw [this, inv_eq_of_mul_eq_one_right hz.sq]
  have hL'tw : L' ∈ twinSet Λ K := ⟨hL'Λ, z, hz, hz'z ▸ hz'L'⟩
  exact ⟨L', hL'tw, hL'ne, hL'img, R₁, R₃, hR₁, hR₃syl, hcomm, hP, hR₁map, hR₃img⟩

theorem exists_conj_normalizer_of_commutes_gen (hN : Odd (Nat.card N)) {U P : Subgroup Y}
    (hU : IsPGroup 2 U) (hP : IsPGroup 2 P)
    (hc : Commutes (U.map (QuotientGroup.mk' N)) (P.map (QuotientGroup.mk' N))) :
    ∃ m ∈ N, U ≤ Subgroup.normalizer ((conjSub m P : Subgroup Y) : Set Y) := by
  set mk := QuotientGroup.mk' N with hmk
  have hS₁ : IsSylow2In P (P ⊔ N) := isSylow2In_sup_of_odd hN hP
  have hperm : ∀ x ∈ U, ∃ n ∈ N, conjSub x P = conjSub n P := by
    intro x hx
    have hxb : conjSub (mk x) (P.map mk) = P.map mk :=
      conjSub_eq_of_mem_of_commutes (Subgroup.mem_map_of_mem _ hx) hc
    have hmapx : (conjSub x P).map mk = P.map mk := by rw [AscQuot.map_conjSub, hxb]
    have hxle : conjSub x P ≤ P ⊔ N := by
      intro y hy
      have hy' : mk y ∈ P.map mk := hmapx ▸ Subgroup.mem_map_of_mem _ hy
      obtain ⟨r, hr, hry⟩ := hy'
      have hrn : r⁻¹ * y ∈ N := by
        have : QuotientGroup.mk' N (r⁻¹ * y) = 1 := by
          rw [map_mul, map_inv, hry, inv_mul_cancel]
        exact (QuotientGroup.eq_one_iff _).mp this
      have : y = r * (r⁻¹ * y) := by group
      rw [this]
      exact (P ⊔ N).mul_mem (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right hrn)
    have hS₂ : IsSylow2In (conjSub x P) (P ⊔ N) :=
      hS₁.of_natCard_le (hP.map _) hxle (by
        rw [Nat.card_congr (Subgroup.equivMapOfInjective P (MulAut.conj x).toMonoidHom
          (MulAut.conj x).injective).toEquiv]
        rfl)
    obtain ⟨p', hp', hpx⟩ := exists_conjSub_eq_of_isSylow2In hS₁ hS₂
    obtain ⟨r, hr, n, hn, hrn⟩ := Subgroup.mem_sup_of_normal_right.mp hp'
    refine ⟨r * n * r⁻¹, ‹N.Normal›.conj_mem n hn r, ?_⟩
    rw [← hpx, ← hrn]
    calc conjSub (r * n) P = conjSub ((r * n * r⁻¹) * r) P := by congr 1; group
      _ = conjSub (r * n * r⁻¹) (conjSub r P) := conjSub_mul _ _ _
      _ = conjSub (r * n * r⁻¹) P := by rw [conjSub_eq_self_of_mem hr]
  exact exists_conj_normalizer_of_perm hN P hU hperm

theorem e189_lift_b_syl_gen (hΛ : HypOmegaGen Λ) (hN : Odd (Nat.card N)) {K : Subgroup Y} {z t : Y}
    (hK : K ∈ Λ) (ht2 : t * t = 1) (hz : IsUniqueInvolution K z) (hzt : z * t = t * z)
    (ha1 : z * t ≠ 1) {xb : Y ⧸ N} {Mb : Subgroup (Y ⧸ N)}
    (hM : Mb ∈ twinSet (quotFamily Λ N) (conjSub xb (K.map (QuotientGroup.mk' N))))
    (hMne : Mb ≠ conjSub xb (K.map (QuotientGroup.mk' N))) {Rb₁ Rb₂ : Subgroup (Y ⧸ N)}
    (hRb₁ : IsSylow2In Rb₁ (conjSub xb (K.map (QuotientGroup.mk' N)))) (hRb₂ : IsSylow2In Rb₂ Mb)
    (hRbc : Commutes Rb₁ Rb₂)
    (hcomm : ∀ w ∈ Rb₁ ⊔ Rb₂, w * (QuotientGroup.mk' N z * QuotientGroup.mk' N t) =
      (QuotientGroup.mk' N z * QuotientGroup.mk' N t) * w) :
    ∃ x : Y, ∃ M' ∈ twinSet Λ (conjSub x K), M' ≠ conjSub x K ∧
      ∃ R₁ R₂ : Subgroup Y, IsSylow2In R₁ (conjSub x K) ∧ IsSylow2In R₂ M' ∧ Commutes R₁ R₂ ∧
        ∀ w ∈ R₁ ⊔ R₂, w * (z * t) = (z * t) * w := by
  set mk := QuotientGroup.mk' N with hmk
  set a := z * t with ha
  have ha2 : a * a = 1 := mul_involution_of_commute hz.sq ht2 hzt
  have hmka : mk a = mk z * mk t := map_mul _ _ _
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk'_surjective N xb
  set K₁ := conjSub x₀ K with hK₁
  have hK₁Λ : K₁ ∈ Λ := hΛ.conjInvariant x₀ K hK
  have hK₁img : K₁.map mk = conjSub xb (K.map mk) := by
    rw [hK₁, AscQuot.map_conjSub, hx₀]
  obtain ⟨z₁, hz₁⟩ : ∃ z₁, IsUniqueInvolution K₁ z₁ := ⟨_, hz.conj x₀⟩
  obtain ⟨K₃, hK₃tw, hK₃ne, hK₃img, R₁, R₃, hR₁, hR₃, hcR, hP, hR₁map, hR₃map⟩ :=
    exists_lift_twin_pair_gen hΛ hN hK₁Λ hz₁ (K'' := Mb) (hK₁img ▸ hM)
      (hK₁img ▸ hMne) (Rb₁ := Rb₁) (Rb₂ := Rb₂) (hK₁img ▸ hRb₁) hRb₂ hRbc
  obtain ⟨hK₃Λ, z₃, hz₃K, hz₃K₃⟩ := hK₃tw
  have hU2 : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_involution ha1 ha2
  have hP2 : IsPGroup 2 ↥(R₁ ⊔ R₃) := hP
  have hPimg : (R₁ ⊔ R₃).map mk = Rb₁ ⊔ Rb₂ := by rw [Subgroup.map_sup, hR₁map, hR₃map]
  have hcU : Commutes ((Subgroup.zpowers a).map mk) ((R₁ ⊔ R₃).map mk) := by
    rw [hPimg]
    intro u hu w hw
    obtain ⟨v, hv, rfl⟩ := hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    rw [map_zpow]
    have hw' : Commute w (mk a) := by rw [hmka]; exact hcomm w hw
    exact (hw'.zpow_right k).eq.symm
  obtain ⟨n, hn, hUn⟩ := exists_conj_normalizer_of_commutes_gen hN hU2 hP2 hcU
  have hmkn : mk n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
  have haP : conjSub a (conjSub n (R₁ ⊔ R₃)) = conjSub n (R₁ ⊔ R₃) :=
    mem_normalizer_iff_conjSub_eq.mp (hUn (Subgroup.mem_zpowers a))
  have hPn2 : IsPGroup 2 ↥(conjSub n (R₁ ⊔ R₃)) := hP2.map _
  have hc' : ∀ r ∈ conjSub n (R₁ ⊔ R₃), r * a = a * r := by
    refine commutes_of_normalizes_sylow hN hPn2 haP ?_
    intro r hr
    have hr' : mk r ∈ (conjSub n (R₁ ⊔ R₃)).map mk := Subgroup.mem_map_of_mem _ hr
    rw [AscQuot.map_conjSub, hmkn, conjSub_one, hPimg] at hr'
    rw [hmka]
    exact hcomm _ hr'
  have hK₁n : conjSub (n * x₀) K = conjSub n K₁ := conjSub_mul n x₀ K
  refine ⟨n * x₀, conjSub n K₃, ?_, ?_, conjSub n R₁, conjSub n R₃, ?_, ?_, ?_, ?_⟩
  · rw [hK₁n]
    exact ⟨hΛ.conjInvariant n K₃ hK₃Λ, n * z₃ * n⁻¹, hz₃K.conj n, hz₃K₃.conj n⟩
  · rw [hK₁n]
    intro h
    apply hK₃ne
    have := congrArg (conjSub n⁻¹) h
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  · rw [hK₁n]
    exact hR₁.conj n
  · exact hR₃.conj n
  · intro x hx y hy
    rw [mem_conjSub_iff] at hx hy
    have h1 := hcR _ hx _ hy
    have h2 : n * ((n⁻¹ * x * n) * (n⁻¹ * y * n)) * n⁻¹ =
        n * ((n⁻¹ * y * n) * (n⁻¹ * x * n)) * n⁻¹ := by rw [h1]
    convert h2 using 1 <;> group
  · intro w hw
    have hle : conjSub n R₁ ⊔ conjSub n R₃ ≤ conjSub n (R₁ ⊔ R₃) := by
      refine sup_le (fun r hr => ?_) (fun r hr => ?_)
      · rw [mem_conjSub_iff] at hr ⊢
        exact Subgroup.mem_sup_left hr
      · rw [mem_conjSub_iff] at hr ⊢
        exact Subgroup.mem_sup_right hr
    exact hc' w (hle hw)

end LiftB

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
