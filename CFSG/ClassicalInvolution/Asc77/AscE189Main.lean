module

public import CFSG.ClassicalInvolution.Asc77.AscE189CaseA
public import CFSG.ClassicalInvolution.Asc77.AscE189Sect
public import CFSG.ClassicalInvolution.Asc77.AscE187Transfer
public import CFSG.ClassicalInvolution.Asc77.AscE187Basic
public import CFSG.ClassicalInvolution.Asc77.AscE184Sec
public import CFSG.ClassicalInvolution.Asc77.AscE186CentA

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

@[expose] def E189E4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex p f Ω K S R W H →
      ∀ K' ∈ twinSet Ω K, K' ≠ K → ∀ R' ∈ RSet Ω, R' ≤ K' → IsPGroup 2 ↥(R ⊔ R') →
        ∀ A : Subgroup G, IsPGroup 2 A → R ⊔ R' ≤ Subgroup.centralizer (A : Set G) →
          Subgroup.centralizer (A : Set G) ≠ ⊤ → Subgroup.centralizer (A : Set G) ≤ H

variable {p f}

private theorem centralizer_zpowers_eq_singleton' {G : Type} [Group G] (u : G) :
    Subgroup.centralizer (Subgroup.zpowers u : Set G) = Subgroup.centralizer ({u} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

variable (p f) in
theorem e18_9 (h3 : E18_3 p f) (h6 : E18_6 p f) (h7 : E18_7 p f)
    (h4 : E189E4 p f) (hsect : E189Sect p f) : E18_9 p f := by
  intro G _ _ Ω K S R W H c z hz h _ htz hzt
  set t : G := h⁻¹ * z * h with ht
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  have hzH : Subgroup.centralizer ({z} : Set G) ≤ H := c.centralizer_le p f hz
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
    rcases e189_caseA hp hq hΩ hK hJ hz hJt htz hzt' hnorm with ⟨g, hg⟩ | hperp
    · have e : g * t * g⁻¹ = (g * h⁻¹) * z * (g * h⁻¹)⁻¹ := by rw [ht]; group
      rw [← hg, e]
      exact fixesUniqueCoset_conj hzfix _
    · have hne : conjSub h⁻¹ K ≠ K := fun h' => htz (hJt.eq (by rw [h']; exact hz))
      have hnbr : conjSub h⁻¹ K ∈ omegaNbr Ω K := hperp.resolve_left hne
      obtain ⟨R₁, T, hR₁, hTsyl, -, hRT⟩ := AscE186.exists_commuting_sylow_pair hp hq hΩ hK hnbr
      have hR₁Ω : R₁ ∈ RSet Ω := mem_RSet_of_isSylow2In hK hR₁
      have hTΩ : T ∈ RSet Ω := mem_RSet_of_isSylow2In hJ hTsyl
      have hzR : z ∈ R₁ := mem_of_isUniqueInvolution_of_isPGroup hz hR₁.1 hR₁.2.1
        (by have := hΩ.eight_le_of_mem_RSet hp hR₁Ω; omega)
      have htT : t ∈ T := mem_of_isUniqueInvolution_of_isPGroup hJt hTsyl.1 hTsyl.2.1
        (by have := hΩ.eight_le_of_mem_RSet hp hTΩ; omega)
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
    rcases e189_sect_apply hsect hp hq c.stand.below hΩ hAΩ hHn hK hJ' hKH hJ'H hz hJ't hzt'
      hnorm with ⟨K'', hK''tw, -, R₁, R₂, hR₁Ω, hR₁K, hR₂Ω, hR₂K'', hRc, u, x, hu, hu1, hu2, hux⟩ |
      ⟨x, hxH, M', hM'tw, hM'ne, R₁, R₂, hR₁Ω, hR₁K, hR₂Ω, hR₂M', hRc, hcommM⟩
    ·
      obtain ⟨hK''Ω, z', hz'K, hz'K''⟩ := hK''tw
      have hperp : K'' ∈ KPerp Ω K := mem_kPerp_of_twin hΩ hK''Ω hK hz'K'' hz'K
      have hcu := c.hyp.cent K (mem_twinSet_self hK hz) K'' hperp R₁ R₂ hR₁Ω hR₁K hR₂Ω hR₂K''
        (Or.inl hRc) u hu hu1 hu2
      have hfu := fixesUniqueCoset_of_centralizer_le hcu (h7 G Ω K S R W H c u hu1 hu2 hcu)
      rw [← hux]
      exact fixesUniqueCoset_conj hfu x
    ·
      have hxK : conjSub x K ∈ Ω := hΩ.conjInvariant x K hK
      have hRsyl : IsSylow2In R K :=
        hΩ.isSylow2In_of_mem_RSet_of_le hp hK c.stand.hR.1 c.stand.hR.2.1
      have hRx : IsSylow2In (conjSub x R) (conjSub x K) := hRsyl.conj x
      have hR₁syl : IsSylow2In R₁ (conjSub x K) :=
        hΩ.isSylow2In_of_mem_RSet_of_le hp hxK hR₁Ω hR₁K
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
      have hR₂syl : IsSylow2In R₂ M' := hΩ.isSylow2In_of_mem_RSet_of_le hp hM'tw.1 hR₂Ω hR₂M'
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
        hM'ne R₂ hR₂Ω hR₂M' hR₁₂2 _ ha2' hRA hX
      rw [centralizer_zpowers_eq_singleton'] at hC
      exact fixesUniqueCoset_of_centralizer_le hC (h7 G Ω K S R W H c _ ha1 ha2 hC)

end CFSG.ClassicalInvolution.Asc77
