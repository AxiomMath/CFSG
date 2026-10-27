module

public import CFSG.ClassicalInvolution.Q3.Q3T7H4
public import CFSG.ClassicalInvolution.Asc77.AscE186Main
public import CFSG.ClassicalInvolution.Q3.Q3T7FUE4
public import CFSG.ClassicalInvolution.Q3.Q3T7T2Main

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

abbrev _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.WSet :=
  @CFSG.ClassicalInvolution.Asc77.WSet

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic

@[expose] def E189E4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex Ω K S R W H →
      ∀ K' ∈ twinSet Ω K, K' ≠ K → ∀ R' ∈ RSet Ω, R' ≤ K' → IsPGroup 2 ↥(R ⊔ R') →
        ∀ A : Subgroup G, IsPGroup 2 A → (∃ w : G, w ≠ 1 ∧ w * w = 1 ∧ A = Subgroup.zpowers w) → R
            ⊔ R' ≤ Subgroup.centralizer (A : Set G) →
          Subgroup.centralizer (A : Set G) ≠ ⊤ → Subgroup.centralizer (A : Set G) ≤ H

private theorem centralizer_zpowers_eq_singleton' {G : Type} [Group G] (u : G) :
    Subgroup.centralizer (Subgroup.zpowers u : Set G) = Subgroup.centralizer ({u} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem e18_9 (h3 : E18_3) (h6 : E18_6) (h7 : E18_7)
    (h4 : E189E4) (hsect : E189Sect) : E18_9 := by
  intro G _ _ Ω K S R W H c z hz h _ htz hzt
  set t : G := h⁻¹ * z * h with ht
  have hΩ : Q3T7M.HM Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  have hzH : Subgroup.centralizer ({z} : Set G) ≤ H := c.centralizer_le hz
  have ht2 : t * t = 1 := by
    calc (h⁻¹ * z * h) * (h⁻¹ * z * h) = h⁻¹ * (z * z) * h := by group
      _ = 1 := by rw [hz.sq]; group
  have ht1 : t ≠ 1 := by
    intro h1
    apply hz.ne_one
    have : z = h * t * h⁻¹ := by rw [ht]; group
    rw [this, h1]
    group
  have hJ : conjSub h⁻¹ K ∈ Ω := hΩ.conjInvariant h⁻¹ K hK
  have hJt : IsUniqueInvolution (conjSub h⁻¹ K) t := by
    have := hz.conj h⁻¹
    simpa [ht] using this
  have hzt' : z * t = t * z := hzt
  have ha2 : (z * t) * (z * t) = 1 := mul_involution_of_commute hz.sq ht2 hzt'
  have ha1 : z * t ≠ 1 := by
    intro h1
    apply htz
    have : t = z⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this, inv_eq_of_mul_eq_one_right hz.sq]
  have hzfix : FixesUniqueCoset z H :=
    fixesUniqueCoset_of_centralizer_le hzH (h7 G Ω K S R W H c z hz.ne_one hz.sq hzH)
  have hKcent : ∀ w ∈ K, z * w = w * z := fun w hw => e189_commute_of_mem hz hw
  have hKH : K ≤ H := fun w hw =>
    hzH (Subgroup.mem_centralizer_singleton_iff.mpr (hKcent w hw).symm)
  have htH : t ∈ H := hzH (Subgroup.mem_centralizer_singleton_iff.mpr hzt'.symm)
  by_cases hnorm : conjSub t K = K
  ·
    rcases e189_caseA hΩ hK hJ hz hJt htz hzt' hnorm with ⟨g, hg⟩ | hperp
    · have e : g * t * g⁻¹ = (g * h⁻¹) * z * (g * h⁻¹)⁻¹ := by rw [ht]; group
      rw [← hg, e]
      exact fixesUniqueCoset_conj hzfix _
    · have hne : conjSub h⁻¹ K ≠ K := fun h' => htz (hJt.eq (by rw [h']; exact hz))
      have hnbr : conjSub h⁻¹ K ∈ omegaNbr Ω K := hperp.resolve_left hne
      obtain ⟨R₁, T, hR₁, hTsyl, -, hRT⟩ := AscE186.exists_commuting_sylow_pair hΩ hK hnbr
      have hR₁Ω : R₁ ∈ RSet Ω := mem_RSet_of_isSylow2In hK hR₁
      have hTΩ : T ∈ RSet Ω := mem_RSet_of_isSylow2In hJ hTsyl
      have hzR : z ∈ R₁ := mem_of_isUniqueInvolution_of_isPGroup hz hR₁.1 hR₁.2.1
        (by have := hΩ.eight_le_of_mem_RSet hR₁Ω; omega)
      have htT : t ∈ T := mem_of_isUniqueInvolution_of_isPGroup hJt hTsyl.1 hTsyl.2.1
        (by have := hΩ.eight_le_of_mem_RSet hTΩ; omega)
      have hca := c.hyp.cent K (mem_twinSet_self hK hz) _ hperp R₁ T hR₁Ω hR₁.1 hTΩ hTsyl.1
        (Or.inl hRT) (z * t) (Subgroup.mul_mem _ (Subgroup.mem_sup_left hzR)
          (Subgroup.mem_sup_right htT)) ha1 ha2
      exact fixesUniqueCoset_of_centralizer_le hca (h7 G Ω K S R W H c _ ha1 ha2 hca)
  ·
    obtain ⟨k, hkH, hk⟩ := h7 G Ω K S R W H c z hz.ne_one hz.sq hzH h⁻¹
      (by simpa [ht] using htH)
    have hkt : k * z * k⁻¹ = t := by rw [hk, ht]; simp
    have hJ' : conjSub k K ∈ Ω := hΩ.conjInvariant k K hK
    have hJ'H : conjSub k K ≤ H := by
      have := conjSub_mono (n := k) hKH
      rwa [conjSub_eq_self_of_mem hkH] at this
    have hJ't : IsUniqueInvolution (conjSub k K) t := by
      have := hz.conj k
      rwa [hkt] at this
    have hHn : Nat.card H < Nat.card G := natCard_lt_of_ne_top c.proper
    have hAΩ : ∀ L ∈ Ω, AEmpty Ω L :=
      aEmpty_forall_of_transitive hΩ.conjInvariant (h3 G Ω K S R W H c) c.stand.aEmpty
    rcases e189_sect_apply hsect c.stand.below c.stand.ih hΩ hAΩ hHn hK hJ' hKH hJ'H hz hJ't hzt'
      hnorm with ⟨K'', hK''tw, -, R₁, R₂, hR₁Ω, hR₁K, hR₂Ω, hR₂K'', hRc, u, x, hu, hu1, hu2, hux⟩ |
      ⟨x, hxH, M', hM'tw, hM'ne, R₁, R₂, hR₁Ω, hR₁K, hR₂Ω, hR₂M', hRc, hcommM⟩
    ·
      obtain ⟨hK''Ω, z', hz'K, hz'K''⟩ := hK''tw
      have hperp : K'' ∈ KPerp Ω K := CFSG.ClassicalInvolution.Q3.Q3T7M.mem_kPerp_of_twin hΩ hK''Ω
          hK hz'K'' hz'K
      have hcu := c.hyp.cent K (mem_twinSet_self hK hz) K'' hperp R₁ R₂ hR₁Ω hR₁K hR₂Ω hR₂K''
        (Or.inl hRc) u hu hu1 hu2
      have hfu := fixesUniqueCoset_of_centralizer_le hcu (h7 G Ω K S R W H c u hu1 hu2 hcu)
      rw [← hux]
      exact fixesUniqueCoset_conj hfu x
    ·
      have hxK : conjSub x K ∈ Ω := hΩ.conjInvariant x K hK
      have hRsyl : IsSylow2In R K :=
        hΩ.isSylow2In_of_mem_RSet_of_le hK c.stand.hR.1 c.stand.hR.2.1
      have hRx : IsSylow2In (conjSub x R) (conjSub x K) := hRsyl.conj x
      have hR₁syl : IsSylow2In R₁ (conjSub x K) :=
        hΩ.isSylow2In_of_mem_RSet_of_le hxK hR₁Ω hR₁K
      
      obtain ⟨k, hk, hkR⟩ := exists_conjSub_eq_of_isSylow2In hRx hR₁syl
      have hxKH : conjSub x K ≤ H := by
        have := conjSub_mono (n := x) hKH
        rwa [conjSub_eq_self_of_mem hxH] at this
      have hx'H : k * x ∈ H := H.mul_mem (hxKH hk) hxH
      have hKx' : conjSub (k * x) K = conjSub x K := by
        rw [conjSub_mul, conjSub_eq_self_of_mem hk]
      have hRx' : conjSub (k * x) R = R₁ := by rw [conjSub_mul, hkR]
      have cx := c.conj_of_mem hx'H
      rw [hKx', hRx'] at cx
      have hR₂syl : IsSylow2In R₂ M' := hΩ.isSylow2In_of_mem_RSet_of_le hM'tw.1 hR₂Ω hR₂M'
      have hR₁₂2 : IsPGroup 2 ↥(R₁ ⊔ R₂) :=
        hR₁syl.2.1.to_sup_of_normal_left' hR₂syl.2.1 fun y hy =>
          mem_normalizer_iff_conjSub_eq.mpr
            (conjSub_eq_of_mem_of_commutes hy fun a ha b hb => (hRc b hb a ha).symm)
      have ha2' : IsPGroup 2 (Subgroup.zpowers (z * t)) :=
        isPGroup_zpowers_of_involution ha1 ha2
      have hRA : R₁ ⊔ R₂ ≤ Subgroup.centralizer ((Subgroup.zpowers (z * t) : Subgroup G) :
          Set G) := by
        rw [centralizer_zpowers_eq_singleton']
        exact fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hcommM r hr)
      have hX : Subgroup.centralizer ((Subgroup.zpowers (z * t) : Subgroup G) : Set G) ≠ ⊤ := by
        rw [centralizer_zpowers_eq_singleton']
        exact c.centralizer_ne_top h6 ha1
      have hC := h4 G Ω (conjSub x K) (conjSylow (k * x) S) R₁ (conjSub (k * x) W) H cx M' hM'tw
        hM'ne R₂ hR₂Ω hR₂M' hR₁₂2 _ ha2' ⟨z * t, ha1, ha2, rfl⟩ hRA hX
      rw [centralizer_zpowers_eq_singleton'] at hC
      exact fixesUniqueCoset_of_centralizer_le hC (h7 G Ω K S R W H c _ ha1 ha2 hC)
end Asc77

end

section

namespace Asc77.AscE186
open CFSG.ClassicalInvolution.Asc77.AscE186
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G} {N : Subgroup G} [N.Normal]

theorem exists_lift_twin (hH : H ≠ ⊤) (hcent : E186Cent2 Ω K H) (hN2 : IsPGroup 2 ↥N)
    (c : CentQuot Ω N) (hK : K ∈ Ω) {Lb : Subgroup (G ⧸ N)}
    (hLb : Lb ∈ twinSet (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    ∃ L ∈ twinSet Ω K, L.map (QuotientGroup.mk' N) = Lb :=
  CFSG.ClassicalInvolution.T7FU.Asc77.AscE186.exists_lift_twin hH hcent hN2 c.toU hK hLb

theorem exists_lift_kperp (c : CentQuot Ω N) {L : Subgroup G} (hL : L ∈ Ω)
    {Jb : Subgroup (G ⧸ N)}
    (hJb : Jb ∈ KPerp (quotFamily Ω N) (L.map (QuotientGroup.mk' N))) :
    ∃ J ∈ KPerp Ω L, J.map (QuotientGroup.mk' N) = Jb :=
  T7FU.Asc77.AscE186.exists_lift_kperp c.toU (fun _ hJ => perfect_of_mem c.hyp hJ) hL hJb

theorem exists_lift_sylow_pair (hN2 : IsPGroup 2 ↥N) (c : CentQuot Ω N) {L J : Subgroup G}
    (hL : L ∈ Ω) (hJ : J ∈ KPerp Ω L) {Rb₁ Rb₂ : Subgroup (G ⧸ N)}
    (hRb₁ : Rb₁ ∈ RSet (quotFamily Ω N)) (hRb₁L : Rb₁ ≤ L.map (QuotientGroup.mk' N))
    (hRb₂ : Rb₂ ∈ RSet (quotFamily Ω N)) (hRb₂J : Rb₂ ≤ J.map (QuotientGroup.mk' N))
    (hc : Commutes Rb₁ Rb₂ ∨ Rb₂ = Rb₁) :
    ∃ R₁ R₂ : Subgroup G, R₁ ∈ RSet Ω ∧ R₁ ≤ L ∧ R₂ ∈ RSet Ω ∧ R₂ ≤ J ∧
      R₁.map (QuotientGroup.mk' N) = Rb₁ ∧ R₂.map (QuotientGroup.mk' N) = Rb₂ ∧
      (Commutes R₁ R₂ ∨ R₂ = R₁) :=
  T7FU.Asc77.AscE186.exists_lift_sylow_pair hN2 c.toU (fun _ hJ => perfect_of_mem c.hyp hJ) hL hJ
    hRb₁ hRb₁L hRb₂ hRb₂J hc

theorem MinCex.mem_of_conj_mem (c : MinCex Ω K S R W H) (h182 : E18_2)
    {M : Subgroup G} (hM : M ∈ dstarComp Ω K) {u : G} (hu : u ∈ M) (hu4 : orderOf u = 4)
    {g : G} (hg : g * u * g⁻¹ ∈ H) : g ∈ H := by
  obtain ⟨h, hhH, hh⟩ := c.hyp.trans M hM
  rw [← hh, mem_conjSub_iff] at hu
  have hu4' : orderOf (h⁻¹ * u * h) = 4 := by
    have := orderOf_injective (MulAut.conj h⁻¹).toMonoidHom (MulAut.conj h⁻¹).injective u
    rw [← hu4]
    simpa [inv_inv] using this
  have hgh : (g * h) * (h⁻¹ * u * h) * (g * h)⁻¹ ∈ H := by
    have : (g * h) * (h⁻¹ * u * h) * (g * h)⁻¹ = g * u * g⁻¹ := by group
    rw [this]
    exact hg
  have := h182 G Ω K S R W H c (h⁻¹ * u * h) hu hu4' (g * h) hgh
  exact (Subgroup.mul_mem_cancel_right H hhH).mp this

theorem E186Cent2.quot_cent (hH : H ≠ ⊤) (hN2 : IsPGroup 2 ↥N)
    (c : CentQuot Ω N) (hK : K ∈ Ω) (hcent : E186Cent2 Ω K H)
    (h18 : ∀ M ∈ dstarComp Ω K, ∀ u ∈ M, orderOf u = 4 → ∀ g : G, g * u * g⁻¹ ∈ H → g ∈ H) :
    E186Cent2 (quotFamily Ω N) (K.map (QuotientGroup.mk' N)) (H.map (QuotientGroup.mk' N)) :=
  CFSG.ClassicalInvolution.T7FU.Asc77.AscE186.E186Cent2.quot_cent (hH := hH) (hN2 := hN2)
    (c := c.toU) (hodd := (fun _ hJ => perfect_of_mem c.hyp hJ)) (hK := hK) (hcent := hcent)
    (h18 := h18)

theorem MinCex.cent_quot_stand (c : MinCex Ω K S R W H) (hc : CentQuot Ω N) :
    ∃ (Sb : Sylow 2 (G ⧸ N)) (Rb Wb : Subgroup (G ⧸ N)),
      EStand (quotFamily Ω N) (K.map (QuotientGroup.mk' N)) Sb Rb Wb := by
  have hΩ : Q3T7M.HM Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨K', hK'tw, hK'ne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  have h3 : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J := e18_3 (l6_7_proved) G Ω K S R W H c
  have hAΩ : ∀ J ∈ Ω, AEmpty Ω J :=
    aEmpty_forall_of_transitive hΩ.conjInvariant h3 c.stand.aEmpty
  set Sb : Sylow 2 (G ⧸ N) :=
    Sylow.mapSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) S with hSbdef
  have hSb : (Sb : Subgroup (G ⧸ N)) = (S : Subgroup G).map (QuotientGroup.mk' N) :=
    Sylow.coe_mapSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) S
  obtain ⟨Wb, hWb, hWbS, hWbn⟩ := exists_W_of_hypOmega hc.hyp' Sb
  have hRsyl : IsSylow2In R K := hΩ.isSylow2In_of_mem_RSet_of_le hK hRR hRK
  obtain ⟨hK'Ω, z, hzK, hzK'⟩ := hK'tw
  have hR'syl : IsSylow2In R' K' := hΩ.isSylow2In_of_mem_RSet_of_le hK'Ω hR' hR'K'
  refine ⟨Sb, R.map (QuotientGroup.mk' N), Wb, ?_⟩
  exact
    { hyp := hc.hyp'
      below := Generic.CITBelowU.mono (natCard_quotient_le N) c.stand.below
      ih := ih8T_mono (natCard_quotient_le N) c.stand.ih
      ob := c.stand.ob
      mem := map_mem_quotFamily hK
      aEmpty := hc.aEmpty_quotFamily hAΩ _ (map_mem_quotFamily hK)
      twin := ⟨K'.map (QuotientGroup.mk' N),
        ⟨map_mem_quotFamily hK'Ω, QuotientGroup.mk' N z,
          AscQuot.isUniqueInvolution_map_mk (hc.meet K hK) hzK,
          AscQuot.isUniqueInvolution_map_mk (hc.meet K' hK'Ω) hzK'⟩,
        hc.map_ne_of_ne hK hK'Ω hK'ne,
        R'.map (QuotientGroup.mk' N),
        mem_RSet_of_isSylow2In (map_mem_quotFamily hK'Ω) (hc.isSylow2In_map hK'Ω hR'syl),
        Subgroup.map_mono hR'K', hSb ▸ Subgroup.map_mono hR'S⟩
      hR := ⟨mem_RSet_of_isSylow2In (map_mem_quotFamily hK) (hc.isSylow2In_map hK hRsyl),
        Subgroup.map_mono hRK, hSb ▸ Subgroup.map_mono hRS⟩
      hW := ⟨hWb, hWbS, hWbn⟩ }

theorem MinCex.cent_quot_trans (c : MinCex Ω K S R W H) (hc : CentQuot Ω N) :
    ∀ Jb ∈ dstarComp (quotFamily Ω N) (K.map (QuotientGroup.mk' N)),
      ∃ hb ∈ H.map (QuotientGroup.mk' N),
        conjSub hb (K.map (QuotientGroup.mk' N)) = Jb := by
  intro Jb hJb
  obtain ⟨M, hM, hMeq⟩ := hc.exists_lift_dstarComp c.stand.mem hJb
  obtain ⟨h, hhH, hh⟩ := c.hyp.trans M hM
  refine ⟨QuotientGroup.mk' N h, Subgroup.mem_map_of_mem _ hhH, ?_⟩
  rw [← hMeq, ← hh, AscQuot.map_conjSub]
end Asc77.AscE186

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G]

theorem e18_6 (hq1 : E186QuotOdd) (hq2 : E186QuotCent)
    (h2 : Thm2) : E18_6 := by
  intro G _ _ Ω K S R W H c
  have hΩ : Q3T7M.HM Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  have h67 : L6_7 := l6_7_proved
  have h69 : L6_9 := l6_9_proved
  have h611 : L6_11 := l6_11_proved
  have h3 : E18_3 := e18_3 h67
  have htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J := h3 G Ω K S R W H c
  have hgen : (⨆ J ∈ Ω, J) = ⊤ := e18_5_of_layer3 G Ω K S R W H c
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hK
  obtain ⟨K', hK'tw, hK'ne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  
  have hA : EtaAbelian Ω := EtaAbelian.of_l6_9 h69 hΩ
  have hM : EtaMeet Ω := EtaMeet.of_l6_11 h611 hΩ
  have hOH : classicalInvolutionOddCore G ≤ H := by
    obtain ⟨U, hUR, -, hcomm, hsq, hU4, hC⟩ :=
      c.exists_fourGroup hA hM hK'tw hK'ne hR' hR'K' hR'S
    have : IsMulCommutative ↥U := ⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩
    exact CFSG.Goldschmidt.LemmaX.le_of_forall_inf_centralizer_le (E := U)
      (N := classicalInvolutionOddCore G) (J := H) this
      (fun x hx => by rw [pow_two]; exact hsq x hx) hU4
      (fun u _ => by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top u)
      (CFSG.ComponentClassification.OddCore.odd_card G)
      (fun e he he1 => inf_le_right.trans (hC e he he1))
  have hO : classicalInvolutionOddCore G = ⊥ :=
    hq1 G Ω K S R W H c _ (CFSG.ComponentClassification.OddCore.odd_card G) hOH
  
  have hmiss : ∀ Q : Subgroup G, Q.Normal → IsPGroup 2 ↥Q → ∀ J ∈ Ω, J ⊓ Q = ⊥ := by
    intro Q hQn hQ2 J hJ
    have hzQ : z ∉ Q := by
      intro hzQ
      have hKn : K.Normal := h2 G Ω hΩ hO hgen K hK htrans z hz ⟨Q, hQn, hQ2, hzQ⟩
      apply hK'ne
      obtain ⟨g, hg⟩ := htrans K' hK'tw.1
      rw [← hg]
      exact AscThmA.conjSub_eq_of_normal K g
    obtain ⟨g, hg⟩ := htrans J hJ
    by_contra hne
    have hzJ : IsUniqueInvolution J (g * z * g⁻¹) := by
      rw [← hg]
      exact hz.conj g
    have hA2 : IsPGroup 2 ↥(J ⊓ Q) := hQ2.to_inf_right
    have hcard : 2 ≤ Nat.card ↥(J ⊓ Q) := by
      have := (Subgroup.one_lt_card_iff_ne_bot (J ⊓ Q)).mpr hne
      omega
    have hmem : g * z * g⁻¹ ∈ J ⊓ Q :=
      AscL62.mem_of_uniqueInvolution_of_pGroup hzJ inf_le_left hA2 hcard
    apply hzQ
    have := hQn.conj_mem _ hmem.2 g⁻¹
    simpa [mul_assoc] using this
  
  have hcent : ∀ Q : Subgroup G, Q.Normal → IsPGroup 2 ↥Q → Q ≤ Subgroup.center G := by
    intro Q hQn hQ2
    have hOQ : oddCoreOf Q = ⊥ := oddCoreOf_eq_bot_of_normal Q hO
    have hQK : ∀ J ∈ Ω, Odd (Nat.card ↥(Q ⊓ J)) := by
      intro J hJ
      rw [inf_comm, hmiss Q hQn hQ2 J hJ]
      simp
    have hJc : ∀ J ∈ Ω, J ≤ Subgroup.centralizer (Q : Set G) := fun J hJ => by
      have := hQn
      exact normal_two_central3 hΩ hQ2 hJ (hmiss Q hQn hQ2 J hJ)
    have hle : (⨆ J ∈ Ω, J) ≤ Subgroup.centralizer (Q : Set G) := iSup₂_le hJc
    intro q hq'
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ ⨆ J ∈ Ω, J := by rw [hgen]; exact Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp (hle hg) q hq').symm
  
  have hZ2 : IsPGroup 2 ↥(Subgroup.center G) := center_isPGroup_two hO
  have hZH : Subgroup.center G ≤ H := by
    obtain ⟨z', hz', hcz'⟩ := c.exists_centralizer_le
    intro x hx
    apply hcz'
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp hx z').symm
  have hZbot : Subgroup.center G = ⊥ :=
    hq2 G Ω K S R W H c (Subgroup.center G) le_rfl hZ2 hZH
      (fun J hJ => hmiss _ inferInstance hZ2 J hJ)
  have h2triv : ∀ Q : Subgroup G, Q.Normal → IsPGroup 2 ↥Q → Q = ⊥ := by
    intro Q hQn hQ2
    have := hcent Q hQn hQ2
    rw [hZbot] at this
    exact le_bot_iff.mp this
  have hsolv := AscThmA.solvable_normal_eq_bot_of_oddCore hO h2triv
  exact ⟨hO, c.stand.ob.simple G Ω hΩ c.stand.below hO hsolv hgen K hK htrans⟩
end Asc77

end

section

namespace Asc77.AscE186
open CFSG.ClassicalInvolution.Asc77.AscE186
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem thm2 : Thm2 :=
  CFSG.ClassicalInvolution.Q3.Q3T7T2.thm2_three

end Asc77.AscE186

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem hbad_twImage (hΩ : Q3T7M.HM Ω) {H : Subgroup G} {t : G}
    (hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H) :
    ∀ L ∈ twFamily Ω t, IsUniqueInvolution L (twT t) → ∀ ū ∈ L, orderOf ū = 4 →
      ū ∉ twImage t H :=
  CFSG.ClassicalInvolution.T7FU.Asc77.hbad_twImage (⟨hΩ, hΩ.toGen⟩) hbad

theorem endgame_four (hΩ : Q3T7M.HM Ω) {H : Subgroup G}
    {t : G} (hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω) (ht : IsUniqueInvolution K₁ t) {d₁ d₂ : G}
    (g₁ : GoodInv H t d₁) (g₂ : GoodInv H t d₂) (g₃ : GoodInv H t (d₁ * d₂))
    (hc : d₁ * d₂ = d₂ * d₁) : False := by
  exact E187C.endgame_four_of
    (fun hb hK ht g₁ g₂ g₃ hc =>
      endgame_four_exact (Ω := twFamily Ω t) (twFamily_hypOmega hΩ t) hb hK ht g₁ g₂ g₃ hc)
    (hbad_twImage hΩ hbad) hK₁ ht g₁ g₂ g₃ hc

end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic

theorem E189E4.of_e187 (h4 : E187E4C) : E189E4 := by
  intro G _ _ Ω K S R W H c K' hK' hne R' hR' hR'K' hRR' A hA hAcyc hRA hX
  have hΩ : Q3T7M.HM Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨P, hP, hRRP⟩ := IsSylow2In.exists_ge hRR' hRA
  obtain ⟨S', hPS'⟩ := IsPGroup.exists_le_sylow hP.2.1
  have hSyl : IsSylow2In ((S' : Subgroup G) ⊓ Subgroup.centralizer (A : Set G))
      (Subgroup.centralizer (A : Set G)) := by
    have hle : P ≤ (S' : Subgroup G) ⊓ Subgroup.centralizer (A : Set G) := le_inf hPS' hP.1
    have hp2 : IsPGroup 2 ↥((S' : Subgroup G) ⊓ Subgroup.centralizer (A : Set G)) :=
      S'.isPGroup'.to_le inf_le_left
    have heq := hP.eq_of_le hp2 inf_le_right hle
    rw [heq]
    exact hP
  obtain ⟨W', hW', hW'S', hW'n⟩ := WSet.exists_normalized_sylow hΩ S'
  have hRS' : R ≤ (S' : Subgroup G) := le_sup_left.trans (hRRP.trans hPS')
  have hR'S' : R' ≤ (S' : Subgroup G) := le_sup_right.trans (hRRP.trans hPS')
  have c' := c.of_sylow hRS' hK' hne hR' hR'K' hR'S' hW' hW'S' hW'n
  exact h4 G Ω K S' R W' H c' K' hK' hne R' hR' hR'K' hR'S' A hA hAcyc hRA hX hSyl
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
