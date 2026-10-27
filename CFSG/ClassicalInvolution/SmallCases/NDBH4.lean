module

public import CFSG.ClassicalInvolution.SmallCases.NDBH3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3 CFSG.ClassicalInvolution.Asc77.T8
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen CFSG.ClassicalInvolution.Asc77.T8R

namespace T8R.Loc

section Cert

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} {Q Q' : Subgroup G}


theorem frame_perm (hs : Std8Core p f Ω K J S R T W z t)
    (hX : Loc26 Ω K J S R T z t Q) {n' : G} {X : Subgroup G}
    (hXR : X ∈ RSet Ω) (hXS : X ≤ conjSub n' (S : Subgroup G)) :
    X = conjSub n' R ∨ X = conjSub n' T := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have h1 : conjSub n'⁻¹ X ∈ RSet Ω := RSet.conj hΩ.conjInvariant hXR n'⁻¹
  have h2 : conjSub n'⁻¹ X ≤ (S : Subgroup G) := by
    have := conjSub_mono (n := n'⁻¹) hXS
    rwa [conjSub_inv_conjSub] at this
  rcases hX.rset h1 h2 with h | h
  · left
    have := congrArg (conjSub n') h
    rwa [conjSub_conjSub_inv] at this
  · right
    have := congrArg (conjSub n') h
    rwa [conjSub_conjSub_inv] at this

theorem frame_conj_perm (hs : Std8Core p f Ω K J S R T W z t)
    (hX : Loc26 Ω K J S R T z t Q) {n' q : G}
    (hq : q ∈ conjSub n' (S : Subgroup G)) :
    (conjSub q (conjSub n' R) = conjSub n' R ∧ conjSub q (conjSub n' T) = conjSub n' T) ∨
      (conjSub q (conjSub n' R) = conjSub n' T ∧ conjSub q (conjSub n' T) = conjSub n' R) := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRT : R ≠ T := R_ne_T hs
  have hcl := hΩ.conjInvariant
  have hP : ∀ Y ≤ (S : Subgroup G), conjSub q (conjSub n' Y) ≤ conjSub n' (S : Subgroup G) := by
    intro Y hY
    have := conjSub_mono (n := q) (conjSub_mono (n := n') hY)
    rwa [conjSub_eq_self_of_mem hq] at this
  have hR1 := frame_perm hs hX (RSet.conj hcl (RSet.conj hcl hRΩ n') q) (hP R hRS)
  have hT1 := frame_perm hs hX (RSet.conj hcl (RSet.conj hcl hTΩ n') q) (hP T hTS)
  have hne : conjSub n' R ≠ conjSub n' T := fun h => hRT (conjSub_injective n' h)
  rcases hR1 with hR1 | hR1
  · left
    refine ⟨hR1, ?_⟩
    rcases hT1 with hT1 | hT1
    · exact absurd ((conjSub_injective q) (hT1.trans hR1.symm)) (Ne.symm hne)
    · exact hT1
  · right
    refine ⟨hR1, ?_⟩
    rcases hT1 with hT1 | hT1
    · exact hT1
    · exact absurd ((conjSub_injective q) (hT1.trans hR1.symm)) (Ne.symm hne)

theorem eq_of_swap (hs : Std8Core p f Ω K J S R T W z t)
    (hX : Loc26 Ω K J S R T z t Q) (hV : ExtraTrans Ω K J S z t)
    {g : G} (hb : g⁻¹ * (z * t) * g ∈ (S : Subgroup G))
    (hswap : conjSub (g⁻¹ * (z * t) * g) R = T) : g⁻¹ * (z * t) * g = z * t := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hcl := hΩ.conjInvariant
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hJΩ hTΩ hTJ
  have h8R := hΩ.eight_le_of_mem_RSet hp hRΩ
  have h8T := hΩ.eight_le_of_mem_RSet hp hTΩ
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
  have hzRu : IsUniqueInvolution R z := uniqueInvolution_restrict hs.hz hRK hzR
  have haa : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  have haS : ∀ s ∈ (S : Subgroup G), s * (z * t) = (z * t) * s := fun s hs' => by
    have := conj_zt_of_mem_sylow hs hX hs'
    calc s * (z * t) = (s * (z * t) * s⁻¹) * s := by group
      _ = (z * t) * s := by rw [this]
  obtain ⟨b, hbdef⟩ : ∃ b, b = g⁻¹ * (z * t) * g := ⟨_, rfl⟩
  rw [← hbdef] at hb hswap ⊢
  have hbb : b * b = 1 := by
    rw [hbdef]
    calc g⁻¹ * (z * t) * g * (g⁻¹ * (z * t) * g) = g⁻¹ * ((z * t) * (z * t)) * g := by group
      _ = 1 := by rw [haa]; group
  have hbK : conjSub b K = J :=
    hΩ.eq_of_le_of_le (hcl b K hK) hJΩ hTsyl.2.1 (by omega) (hswap ▸ conjSub_mono hRK) hTJ
  have hbJ : conjSub b J = K := by
    have := congrArg (conjSub b) hbK
    rw [← conjSub_mul, hbb, conjSub_one] at this
    exact this.symm
  have hbz : b * z * b⁻¹ = t := (hs.ht.eq (hbK ▸ hs.hz.conj b)).symm
  have hRT : Commutes R T :=
    l6_7_proved p f hp hq G Ω hΩ S R hRΩ T hTΩ hRS hTS (R_ne_T hs)
  have hTmem : ∀ r ∈ R, b * r * b⁻¹ ∈ T := fun r hr => by
    rw [← hswap]
    exact conj_mem_conjSub hr
  have hcomm : ∀ r ∈ R, ∀ s ∈ R, s * (b * r * b⁻¹) = (b * r * b⁻¹) * s := fun r hr s hs' =>
    hRT s hs' _ (hTmem r hr)
  let φ : ↥R →* G := MonoidHom.mk' (fun r => (r : G) * (b * (r : G) * b⁻¹)) (by
    intro r s
    simp only [Subgroup.coe_mul]
    calc (r : G) * (s : G) * (b * ((r : G) * (s : G)) * b⁻¹)
        = (r : G) * ((s : G) * (b * (r : G) * b⁻¹)) * (b * (s : G) * b⁻¹) := by group
      _ = (r : G) * ((b * (r : G) * b⁻¹) * (s : G)) * (b * (s : G) * b⁻¹) := by
        rw [hcomm r r.2 s s.2]
      _ = ((r : G) * (b * (r : G) * b⁻¹)) * ((s : G) * (b * (s : G) * b⁻¹)) := by group)
  have hφ : ∀ r : ↥R, φ r = (r : G) * (b * (r : G) * b⁻¹) := fun r => rfl
  have hQS : φ.range ≤ (S : Subgroup G) := by
    rintro _ ⟨r, rfl⟩
    rw [hφ]
    exact S.mul_mem (hRS r.2)
      (S.mul_mem (S.mul_mem hb (hRS r.2)) (S.inv_mem hb))
  have hQ2 : IsPGroup 2 ↥φ.range := S.isPGroup'.to_le hQS
  have hQb : ∀ y ∈ φ.range, y * b = b * y := by
    rintro _ ⟨r, rfl⟩
    rw [hφ]
    have h1 : b * ((r : G) * (b * (r : G) * b⁻¹)) * b⁻¹ = (r : G) * (b * (r : G) * b⁻¹) := by
      calc b * ((r : G) * (b * (r : G) * b⁻¹)) * b⁻¹
          = (b * (r : G) * b⁻¹) * ((b * b) * (r : G) * (b * b)⁻¹) := by group
        _ = (b * (r : G) * b⁻¹) * (r : G) := by rw [hbb]; group
        _ = (r : G) * (b * (r : G) * b⁻¹) := (hcomm r r.2 r r.2).symm
    calc (r : G) * (b * (r : G) * b⁻¹) * b
        = (b * ((r : G) * (b * (r : G) * b⁻¹)) * b⁻¹) * b := by rw [h1]
      _ = b * ((r : G) * (b * (r : G) * b⁻¹)) := by group
  have hbn : g⁻¹ * (z * t) * (g⁻¹)⁻¹ = b := by rw [hbdef, inv_inv]
  obtain ⟨n', hn'b, hQn'⟩ := exists_conj_sylow_of_le_centralizer S haS (n := g⁻¹) hQ2
    (fun y hy => by rw [hbn]; exact hQb y hy)
  rw [hbn] at hn'b
  have htT : t ∈ T := T3.mem_of_isPGroup hs.ht hTJ hTsyl.2.1 (by omega)
  have haSm : z * t ∈ (S : Subgroup G) := S.mul_mem (hRS hzR) (hTS htT)
  let Nsub : Subgroup ↥R := (Subgroup.normalizer ((conjSub n' R : Subgroup G) : Set G)).comap φ
  let N : Subgroup G := Nsub.map R.subtype
  have hNR : N ≤ R := Subgroup.map_subtype_le _
  have hmemN : ∀ r : ↥R, (r : G) ∈ N ↔ conjSub (φ r) (conjSub n' R) = conjSub n' R := by
    intro r
    constructor
    · intro h
      obtain ⟨r', hr', hrr'⟩ := Subgroup.mem_map.mp h
      have : r' = r := Subtype.ext hrr'
      subst this
      exact mem_normalizer_iff_conjSub_eq.mp (Subgroup.mem_comap.mp hr')
    · intro h
      exact Subgroup.mem_map.mpr
        ⟨r, Subgroup.mem_comap.mpr (mem_normalizer_iff_conjSub_eq.mpr h), rfl⟩
  have hperm : ∀ r : ↥R, ¬ (conjSub (φ r) (conjSub n' R) = conjSub n' R) →
      conjSub (φ r) (conjSub n' R) = conjSub n' T ∧
        conjSub (φ r) (conjSub n' T) = conjSub n' R := by
    intro r hr
    rcases frame_conj_perm hs hX (hQn' ⟨r, rfl⟩) with h | h
    · exact absurd h.1 hr
    · exact h
  have hprod : ∀ x ∈ R, ∀ y ∈ R, x ∉ N → y ∉ N → x * y ∈ N := by
    intro x hx y hy hxN hyN
    have hx' := hperm ⟨x, hx⟩ (fun h => hxN ((hmemN ⟨x, hx⟩).mpr h))
    have hy' := hperm ⟨y, hy⟩ (fun h => hyN ((hmemN ⟨y, hy⟩).mpr h))
    have : ((⟨x, hx⟩ * ⟨y, hy⟩ : ↥R) : G) ∈ N := by
      rw [hmemN, map_mul, conjSub_mul, hy'.1, hx'.2]
    exact this
  obtain ⟨r₁, hr₁N, hr₁o⟩ := exists_orderOf_four_of_swap hzRu hRsyl.2.1 h8R N hNR hprod
  have hr₁R : r₁ ∈ R := hNR hr₁N
  have hr₁sq : r₁ * r₁ = z := by
    have hr4 : (r₁ * r₁) * (r₁ * r₁) = 1 := by
      have h4 : r₁ ^ 4 = (r₁ * r₁) * (r₁ * r₁) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [← h4, ← hr₁o]
      exact pow_orderOf_eq_one r₁
    rcases hzRu.unique _ (R.mul_mem hr₁R hr₁R) hr4 with h | h
    · exfalso
      have h2 : r₁ ^ 2 = 1 := by rw [pow_two]; exact h
      have h4 : orderOf r₁ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
      rw [hr₁o] at h4
      omega
    · exact h
  have hqsq : φ ⟨r₁, hr₁R⟩ * φ ⟨r₁, hr₁R⟩ = z * t := by
    have h1 : (⟨r₁, hr₁R⟩ : ↥R) * ⟨r₁, hr₁R⟩ = ⟨z, hzR⟩ := Subtype.ext hr₁sq
    calc φ ⟨r₁, hr₁R⟩ * φ ⟨r₁, hr₁R⟩ = φ (⟨r₁, hr₁R⟩ * ⟨r₁, hr₁R⟩) := (map_mul φ _ _).symm
      _ = φ ⟨z, hzR⟩ := by rw [h1]
      _ = z * t := by
        rw [hφ]
        show z * (b * z * b⁻¹) = z * t
        rw [hbz]
  have hqN : conjSub (φ ⟨r₁, hr₁R⟩) (conjSub n' R) = conjSub n' R :=
    (hmemN ⟨r₁, hr₁R⟩).mp hr₁N
  have hqS' : φ ⟨r₁, hr₁R⟩ ∈ conjSub n' (S : Subgroup G) := hQn' ⟨_, rfl⟩
  have hK'Ω : conjSub n' K ∈ Ω := hcl n' K hK
  have hz' : IsUniqueInvolution (conjSub n' K) (n' * z * n'⁻¹) := hs.hz.conj n'
  have hqK' : conjSub (φ ⟨r₁, hr₁R⟩) (conjSub n' K) = conjSub n' K :=
    T8.conjSub_eq_of_conjSub_eq hp hΩ hK'Ω (RSet.conj hcl hRΩ n') (conjSub_mono hRK) hqN
  have hq2 : IsPGroup 2 (Subgroup.zpowers (φ ⟨r₁, hr₁R⟩)) :=
    (isPGroup_conjSub n' S.isPGroup').to_le (Subgroup.zpowers_le.mpr hqS')
  obtain ⟨x₂, hx₂K', hx₂o, hx₂c⟩ := T8.exists_orderFour_centralizes_sq hp hΩ hK'Ω hz' hq2 hqK'
  rw [hqsq] at hx₂c
  have hxK : n'⁻¹ * x₂ * n' ∈ K := mem_conjSub_iff.mp hx₂K'
  have hxo : orderOf (n'⁻¹ * x₂ * n') = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj n'⁻¹) x₂
    rw [MulAut.conj_apply, hx₂o] at this
    simpa using this
  have hxc : (n'⁻¹ * x₂ * n') * (n'⁻¹ * (z * t) * (n'⁻¹)⁻¹) =
      (n'⁻¹ * (z * t) * (n'⁻¹)⁻¹) * (n'⁻¹ * x₂ * n') := by
    rw [inv_inv]
    calc n'⁻¹ * x₂ * n' * (n'⁻¹ * (z * t) * n') = n'⁻¹ * (x₂ * (z * t)) * n' := by group
      _ = n'⁻¹ * ((z * t) * x₂) * n' := by rw [hx₂c]
      _ = n'⁻¹ * (z * t) * n' * (n'⁻¹ * x₂ * n') := by group
  have hw := conj_zt_mul_inv_mem_of_orderFour hs hX hV (n := n'⁻¹) hxK hxo hxc
  have hwb : n'⁻¹ * ((z * t) * b⁻¹) * n' = n'⁻¹ * (z * t) * (n'⁻¹)⁻¹ * (z * t)⁻¹ := by
    rw [← hn'b]
    group
  exact (eq_of_conj_mul_inv_mem_odd S.isPGroup' haSm hb hX.odd n'
    (hwb ▸ hw)).symm

theorem eq_of_centralizes (hs : Std8Core p f Ω K J S R T W z t)
    (hX : Loc26 Ω K J S R T z t Q) (hV : ExtraTrans Ω K J S z t)
    {g x : G} (hb : g⁻¹ * (z * t) * g ∈ (S : Subgroup G)) (hxK : x ∈ K) (hx4 : orderOf x = 4)
    (hxc : x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x) :
    g⁻¹ * (z * t) * g = z * t := by
  have hn : x * (g⁻¹ * (z * t) * (g⁻¹)⁻¹) = (g⁻¹ * (z * t) * (g⁻¹)⁻¹) * x := by
    rw [inv_inv]
    exact hxc
  have h1 := conj_zt_mul_inv_mem_of_orderFour hs hX hV (n := g⁻¹) hxK hx4 hn
  rw [inv_inv] at h1
  exact eq_of_mul_inv_mem_odd S.isPGroup' hb (zt_mem_sylow hs) (hX.odd) h1

theorem eq_of_centralizes_J (hs : Std8Core p f Ω K J S R T W z t)
    (hXs : Loc26 Ω J K S T R t z Q') (hV' : ExtraTrans Ω J K S t z)
    {g x : G} (hb : g⁻¹ * (z * t) * g ∈ (S : Subgroup G)) (hxJ : x ∈ J) (hx4 : orderOf x = 4)
    (hxc : x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x) :
    g⁻¹ * (z * t) * g = z * t := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hzt : z * t = t * z := T8.mul_comm_of_mem_omegaNbr hp hΩ hs.hz hs.hJ hs.ht
  have hs' := hs.symm'
  have hX' := hXs
  rw [hzt] at hb hxc ⊢
  exact eq_of_centralizes hs' hX' hV' hb hxJ hx4 hxc

theorem false_of_loc [IsSimpleGroup G] (hs : Std8Core p f Ω K J S R T W z t)
    (hX : Loc26 Ω K J S R T z t Q) (hXs : Loc26 Ω J K S T R t z Q') (hV : ExtraTrans Ω K J S z t)
    (hV' : ExtraTrans Ω J K S t z) (hO : OuterFusion K J S R T z t) : False := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have haa : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  have hza : orderOf (z * t) = 2 := by
    refine orderOf_eq_prime (by rw [pow_two]; exact haa) ?_
    intro h
    have hzt : z ≠ t := by
      intro h'
      exact hs.hJ.2.1 (hs.noTwins J ⟨hs.hJ.1, z, hs.hz, h' ▸ hs.ht⟩)
    exact hzt ((eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_right hs.ht.sq))
  have haS := zt_mem_sylow hs
  obtain ⟨g, hgS, hgne⟩ := exists_conj_mem_sylow_ne (exists_not_comm hs) S haS
    (fun s hs' => by
      have := conj_zt_of_mem_sylow hs hX hs'
      calc s * (z * t) = (s * (z * t) * s⁻¹) * s := by group
        _ = (z * t) * s := by rw [this]) hza
  apply hgne
  rcases fix_or_swap hs hX hgS with ⟨hR, hT⟩ | ⟨hR, -⟩
  · by_cases hK : ∃ x ∈ K, orderOf x = 4 ∧
        x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x
    · obtain ⟨x, hxK, hx4, hxc⟩ := hK
      exact eq_of_centralizes hs hX hV hgS hxK hx4 hxc
    by_cases hJ : ∃ x ∈ J, orderOf x = 4 ∧
        x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x
    · obtain ⟨x, hxJ, hx4, hxc⟩ := hJ
      exact eq_of_centralizes_J hs hXs hV' hgS hxJ hx4 hxc
    exact hO g hgS hR hT hK hJ
  · exact eq_of_swap hs hX hV hgS hR


end Cert

end T8R.Loc

end CFSG.ClassicalInvolution.Asc77
