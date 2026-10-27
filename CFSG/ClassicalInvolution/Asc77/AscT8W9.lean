module

public import CFSG.ClassicalInvolution.Asc77.AscT8V4
public import CFSG.ClassicalInvolution.Asc77.AscT8V5
public import CFSG.ClassicalInvolution.Asc77.AscT8W2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace T8W

section Triv

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem oddCoreOf_inf_le_oddCoreOf {L Y : Subgroup G} (hLY : L ≤ Y) :
    oddCoreOf Y ⊓ L ≤ oddCoreOf L := by
  set N : Subgroup G := oddCoreOf Y ⊓ L with hN
  have hNL : N ≤ L := inf_le_right
  have hnorm : L ≤ Subgroup.normalizer (N : Set G) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have hu' : u ∈ Y := hLY hu
    have h1 := mem_normalizer_oddCoreOf hu'
    constructor
    · rintro ⟨hn1, hn2⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp h1 n).mp hn1, ?_⟩
      exact L.mul_mem (L.mul_mem hu hn2) (L.inv_mem hu)
    · rintro ⟨hn1, hn2⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp h1 n).mpr hn1, ?_⟩
      have := L.mul_mem (L.mul_mem (L.inv_mem hu) hn2) hu
      simpa [mul_assoc] using this
  have hodd : Odd (Nat.card N) :=
    (oddCoreOf_odd_natCard Y).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  exact fun x hx => T8V.le_oddCoreOf_of_normal_odd' hNL hnorm hodd hx

theorem mem_oddCoreOf_layerRes_of_mk_mem {a : G} {M : Subgroup G} (hM : T8.XMem Ω a M)
    (c : ↥(T8.layerJoin Ω a)) (hcM : (c : G) ∈ T8.layerRes a M)
    (hc : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(T8.layerJoin Ω a)) c :
      T8.LayerQuot Ω a) ∈ oddCoreOf (T8.layerImg Ω a M)) :
    (c : G) ∈ oddCoreOf (T8.layerRes a M) := by
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(T8.layerJoin Ω a))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hLY : T8.layerRes a M ≤ T8.layerJoin Ω a := T8.le_layerJoin ⟨M, hM, rfl⟩
  have h2 := oddCoreOf_map_mk_of_odd (K := (T8.layerRes a M).subgroupOf (T8.layerJoin Ω a))
    (X := classicalInvolutionOddCore ↥(T8.layerJoin Ω a)) (odd_natCard_inf hodd _)
  unfold T8.layerImg at hc
  rw [h2] at hc
  obtain ⟨c', hc', hcc'⟩ := Subgroup.mem_map.mp hc
  rw [oddCoreOf_subgroupOf hLY] at hc'
  have hc'L : (c' : G) ∈ oddCoreOf (T8.layerRes a M) := Subgroup.mem_subgroupOf.mp hc'
  have hdiv : c'⁻¹ * c ∈ classicalInvolutionOddCore ↥(T8.layerJoin Ω a) :=
    QuotientGroup.eq.mp hcc'
  have hmem : ((c' : G)⁻¹ * c) ∈ oddCoreOf (T8.layerJoin Ω a) ⊓ T8.layerRes a M := by
    refine ⟨mem_oddCoreOf_iff.mpr ⟨(T8.layerJoin Ω a).mul_mem ((T8.layerJoin Ω a).inv_mem c'.2)
      c.2, ?_⟩, ?_⟩
    · convert hdiv using 1
    · exact (T8.layerRes a M).mul_mem ((T8.layerRes a M).inv_mem (mem_oddCoreOf_iff.mp hc'L).1)
        hcM
  have h3 := oddCoreOf_inf_le_oddCoreOf hLY hmem
  have : (c : G) = (c' : G) * ((c' : G)⁻¹ * c) := by group
  rw [this]
  exact (oddCoreOf (T8.layerRes a M)).mul_mem hc'L h3

theorem not_trivial_on_layerImg_J [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hE : MuIsoE4 Ω W) {t₁ : G} (ht1 : t₁ ∈ T8.cenZ (z * t))
    (ht1sq : t₁ * t₁ = 1) (hne : t₁ ≠ t) (hnJ : conjSub t₁ J = J) {J₁ : Subgroup G}
    (hJ₁ : J₁ ∈ Ω) (hJ₁X : J₁ ≤ omegaNbrGen Ω K) (hJ₁t : IsUniqueInvolution J₁ t₁) :
    ¬ ∀ kb ∈ T8.layerImg Ω (z * t) J,
      s26Act (T8.layerJoin Ω (z * t)) ⟨t₁, mem_normalizer_iff_conjSub_eq.mpr
        (T8.layerJoin_conjSub_eq hs.stand.hyp ht1)⟩ kb * kb⁻¹ ∈
          oddCoreOf (T8.layerImg Ω (z * t) J) := by
  intro H₀
  classical
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  have hXJ : T8.XMem Ω (z * t) J := T8V.xMem_J hs
  have hyY : t₁ ∈ Subgroup.normalizer ((T8.layerJoin Ω (z * t) : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (T8.layerJoin_conjSub_eq hΩ ht1)
  have hJN : t₁ ∈ Subgroup.normalizer (J : Set G) := mem_normalizer_iff_conjSub_eq.mpr hnJ
  have hLaN : t₁ ∈ Subgroup.normalizer (T8.layerRes (z * t) J : Set G) :=
    T8.mem_normalizer_layerRes hJN ht1
  have hstep1 : ∀ k ∈ T8.layerRes (z * t) J, ⁅t₁, k⁆ ∈ oddCoreOf (T8.layerRes (z * t) J) := by
    intro k hk
    have hkY : k ∈ T8.layerJoin Ω (z * t) := T8.le_layerJoin ⟨J, hXJ, rfl⟩ hk
    have hyk : t₁ * k * t₁⁻¹ ∈ T8.layerJoin Ω (z * t) :=
      (Subgroup.mem_normalizer_iff.mp hyY k).mp hkY
    have hkb : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(T8.layerJoin Ω (z * t)))
        (⟨k, hkY⟩ : ↥(T8.layerJoin Ω (z * t))) : T8.LayerQuot Ω (z * t)) ∈
        T8.layerImg Ω (z * t) J := ⟨⟨k, hkY⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have h0 := H₀ _ hkb
    have e := s26Act_mk (T8.layerJoin Ω (z * t)) ⟨t₁, hyY⟩ ⟨k, hkY⟩ ⟨t₁ * k * t₁⁻¹, hyk⟩ rfl
    have hc : ((⟨t₁ * k * t₁⁻¹, hyk⟩ * (⟨k, hkY⟩ : ↥(T8.layerJoin Ω (z * t)))⁻¹ :
        ↥(T8.layerJoin Ω (z * t))) : G) = ⁅t₁, k⁆ := by
      simp [commutatorElement_def]
    have hcomm_mem : ⁅t₁, k⁆ ∈ T8.layerRes (z * t) J := by
      rw [commutatorElement_def]
      exact (T8.layerRes (z * t) J).mul_mem ((Subgroup.mem_normalizer_iff.mp hLaN k).mp hk)
        ((T8.layerRes (z * t) J).inv_mem hk)
    rw [← hc]
    refine mem_oddCoreOf_layerRes_of_mk_mem hXJ _ (by rw [hc]; exact hcomm_mem) ?_
    change s26Act (T8.layerJoin Ω (z * t)) ⟨t₁, hyY⟩ (↑(⟨k, hkY⟩ : ↥(T8.layerJoin Ω (z * t)))) *
      (↑(⟨k, hkY⟩ : ↥(T8.layerJoin Ω (z * t))))⁻¹ ∈ _ at h0
    rw [e] at h0
    simpa [QuotientGroup.mk'_apply, map_mul, map_inv] using h0
  set La : Subgroup G := T8.layerRes (z * t) J with hLa
  have hLaJ : La ≤ J := T8.layerRes_le _ J
  have hTJ : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hJΩ hs.hT.1 hs.hT.2.1
  have hTLa : IsSylow2In T La := hXJ.isSylow2In_layerRes_of_le hp hq hΩ hx hTJ (T8V.T_le_cenZ hs)
  have hzp : IsPGroup 2 ↥(Subgroup.zpowers t₁) := by
    obtain ⟨m, hm⟩ := T8.exists_orderOf_eq_two_pow ht1sq
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hĴN : La ⊔ Subgroup.zpowers t₁ ≤ Subgroup.normalizer (La : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hLaN)
  obtain ⟨V, hV, hVt⟩ := IsSylow2In.exists_ge hzp
    (le_sup_right : Subgroup.zpowers t₁ ≤ La ⊔ Subgroup.zpowers t₁)
  have hP : IsSylow2In (V ⊓ La) La :=
    AscP1Nine3.isSylow2In_inf_of_le_normalizer' hV le_sup_left hĴN
  have hPcard : Nat.card ↥(V ⊓ La) = Nat.card T := hP.natCard_eq hTLa
  have hPJ : IsSylow2In (V ⊓ La) J :=
    IsSylow2In.of_natCard_le hTJ hP.2.1 (inf_le_right.trans hLaJ) (le_of_eq hPcard.symm)
  have hPc : V ⊓ La ≤ Subgroup.centralizer ({t₁} : Set G) := by
    intro k hk
    have hkV : k ∈ V := hk.1
    have hkLa : k ∈ La := hk.2
    have ht1V : t₁ ∈ V := hVt (Subgroup.mem_zpowers t₁)
    have hmemV : ⁅t₁, k⁆ ∈ V := by
      rw [commutatorElement_def]
      exact V.mul_mem (V.mul_mem (V.mul_mem ht1V hkV) (V.inv_mem ht1V)) (V.inv_mem hkV)
    have hpg : IsPGroup 2 ↥(Subgroup.zpowers ⁅t₁, k⁆) :=
      hV.2.1.to_le (Subgroup.zpowers_le.mpr hmemV)
    have h1 : ⁅t₁, k⁆ = 1 :=
      eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) (hstep1 k hkLa) hpg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have hPR : V ⊓ La ∈ RSet Ω := mem_RSet_of_isSylow2In hJΩ hPJ
  have h8 : 8 ≤ Nat.card ↥(V ⊓ La) := hΩ.eight_le_of_mem_RSet hp hPR
  have hJJ₁ : J ≠ J₁ := by
    intro h
    have h1 : t₁ ∈ J := h ▸ hJ₁t.mem
    rcases hs.ht.unique t₁ h1 ht1sq with h2 | h2
    · exact hJ₁t.ne_one h2
    · exact hne h2
  have hPN : V ⊓ La ≤ Subgroup.normalizer (J₁ : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hJ₁ hJΩ (Ne.symm hJJ₁) hJ₁t
      (inf_le_right.trans hLaJ) hP.2.1 (by omega) hPc
  have hJnb : J ∈ omegaNbr Ω J₁ :=
    ⟨hJΩ, hJJ₁, V ⊓ La, hPR, inf_le_right.trans hLaJ, hPN⟩
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hJX : J ≤ X := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hs.hJ
  have hNodd : Odd (Nat.card (classicalInvolutionOddCore ↥X)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hΛ : HypOmegaMod p f (restrictFamily Ω X) := hΩ.restrict X
  have hJ₁Λ : J₁.subgroupOf X ∈ restrictFamily Ω X := subgroupOf_mem_restrictFamily hJ₁ hJ₁X
  have hJΛ : J.subgroupOf X ∈ restrictFamily Ω X := subgroupOf_mem_restrictFamily hJΩ hJX
  have h1 := omegaNbr_subgroupOf hp hΩ hJ₁X hJX hJΩ hJnb
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have himg := T8S2.map_ne_of_noTwins hp hΛ hNodd (isUniqueInvolution_subgroupOf hJ₁t hJ₁X)
    (isUniqueInvolution_subgroupOf hs.ht hJX) h1 (by
      rintro ⟨-, z', hz'K, hz'J⟩
      have hJK : J ∈ twinSet Ω J₁ :=
        ⟨hJΩ, (z' : G), isUniqueInvolution_of_subgroupOf hz'K hJ₁X,
          isUniqueInvolution_of_subgroupOf hz'J hJX⟩
      rw [hnt J₁ hJ₁ J hJK])
  have hnbr' := T8S2.omegaNbr_map_odd hp hΛ hNodd h1 himg
  have hDE := s26XEdgeless_E4 hs hdisc hE
  exact hDE _ ⟨_, hJ₁Λ, rfl⟩ _ ⟨_, hJΛ, rfl⟩ (Or.inl hnbr')

end Triv

end T8W

end CFSG.ClassicalInvolution.Asc77
