module

public import CFSG.GH74.Uniqueness.SU.SU10Hyp
public import CFSG.GH74.Uniqueness.SU.SU10Quat
public import CFSG.GH74.Uniqueness.SU.SU10SL25Base
public import CFSG.GH74.Uniqueness.SU.SU10Fusion

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU8 CFSG.Blueprint

section Embedding

variable {G : Type} [Group G] [Finite G] {Hh S : Subgroup G}

@[expose] noncomputable def sylowBar (hS : IsSylowIn Hh S) : ↥S →* Hbar Hh where
  toFun s := QuotientGroup.mk' (pPrimeCore 2 Hh) ⟨(s : G), hS.1 s.2⟩
  map_one' := by
    have h : (⟨((1 : ↥S) : G), hS.1 (1 : ↥S).2⟩ : ↥Hh) = 1 := Subtype.ext rfl
    show QuotientGroup.mk' (pPrimeCore 2 Hh) ⟨((1 : ↥S) : G), hS.1 (1 : ↥S).2⟩ = 1
    rw [h, map_one]
  map_mul' a b := by
    have h : (⟨((a * b : ↥S) : G), hS.1 (a * b : ↥S).2⟩ : ↥Hh) =
        ⟨(a : G), hS.1 a.2⟩ * ⟨(b : G), hS.1 b.2⟩ := Subtype.ext rfl
    show QuotientGroup.mk' (pPrimeCore 2 Hh) ⟨((a * b : ↥S) : G), hS.1 (a * b : ↥S).2⟩ =
      QuotientGroup.mk' (pPrimeCore 2 Hh) ⟨(a : G), hS.1 a.2⟩ *
        QuotientGroup.mk' (pPrimeCore 2 Hh) ⟨(b : G), hS.1 b.2⟩
    rw [h, map_mul]

theorem sylowBar_injective (hS : IsSylowIn Hh S) : Function.Injective (sylowBar hS) := by
  intro a b hab
  have h := injOn_of_isPGroup (isPGroup_subgroupOf hS)
    (Subgroup.mem_subgroupOf.mpr a.2) (Subgroup.mem_subgroupOf.mpr b.2)
    (show QuotientGroup.mk' (pPrimeCore 2 Hh) ⟨a, hS.1 a.2⟩ =
      QuotientGroup.mk' (pPrimeCore 2 Hh) ⟨b, hS.1 b.2⟩ from hab)
  exact Subtype.ext (congrArg (fun x : ↥Hh => (x : G)) h)

omit [Finite G] in
theorem mem_hbarImage_iff_sylowBar (hS : IsSylowIn Hh S) {t : Hbar Hh} :
    t ∈ hbarImage Hh S ↔ ∃ s : ↥S, sylowBar hS s = t := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨⟨s, hS.1 s.2⟩, Subgroup.mem_subgroupOf.mpr s.2, rfl⟩

end Embedding

section Fusion

variable {G : Type} [Group G] [Finite G]

theorem fusion_contradiction {S : Sylow 2 G} {M : Subgroup G} {z : G} (h : Hyp21 S M z)
    {T : Sylow 2 (Hbar (centralizer ({z} : Set G)))}
    (hT : (T : Subgroup (Hbar (centralizer ({z} : Set G)))) =
      hbarImage (centralizer ({z} : Set G)) (S : Subgroup G))
    {R Q : Subgroup (Hbar (centralizer ({z} : Set G)))} (hpair : QPair R Q (zbar z))
    (hRT : R ≤ (T : Subgroup (Hbar (centralizer ({z} : Set G)))))
    (hQT : Q ≤ (T : Subgroup (Hbar (centralizer ({z} : Set G)))))
    (hdecomp : ∀ t ∈ (T : Subgroup (Hbar (centralizer ({z} : Set G)))), t * t = 1 →
      ∃ r ∈ R, ∃ q ∈ Q, r * q = t) : False := by
  classical
  have hS : IsSylowIn (centralizer ({z} : Set G)) (S : Subgroup G) := h.isSylowIn
  have hzS : z ∈ (S : Subgroup G) := h.z_mem
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.z_invol, sq] at this
  have hz1 : z ≠ 1 := h.z_ne_one
  have hrankT : 3 ≤ Open.pRank 2 (T : Subgroup (Hbar (centralizer ({z} : Set G)))) := by
    rw [hT]
    unfold hbarImage
    rw [pRank_map_pPrimeCore (isPGroup_subgroupOf hS), pRank_subgroupOf_eq hS.1]
    exact h.rank
  obtain ⟨E, hET, hE, hEcard⟩ := SU1.exists_isElemAbelian_of_le_pRank Nat.prime_two hrankT
  have hnc := hpair.exists_noncomm_of_rank hdecomp hET hE hEcard
  have hQinv := hpair.inverter_of_noncomm (T.isPGroup'.to_le hQT) hnc
  let ι : ↥(S : Subgroup G) →* Hbar (centralizer ({z} : Set G)) := sylowBar hS
  have hιinj : Function.Injective ι := sylowBar_injective hS
  have hTι : ∀ s : ↥(S : Subgroup G), ι s ∈ (T : Subgroup (Hbar (centralizer ({z} : Set G)))) := by
    intro s
    rw [hT]
    exact (mem_hbarImage_iff_sylowBar hS).mpr ⟨s, rfl⟩
  have hιT : ∀ t ∈ (T : Subgroup (Hbar (centralizer ({z} : Set G)))),
      ∃ s : ↥(S : Subgroup G), ι s = t := by
    intro t ht
    rw [hT] at ht
    exact (mem_hbarImage_iff_sylowBar hS).mp ht
  obtain ⟨g₀, hg₀ne, hg₀S⟩ := exists_conj_mem_sylow_ne h.simple h.nonab S h.z_invol h.z_center
  let zS : ↥(S : Subgroup G) := ⟨z, hzS⟩
  let xS : ↥(S : Subgroup G) := ⟨g₀ * z * g₀⁻¹, hg₀S⟩
  have hιz : ι zS = zbar z := rfl
  have hxz : xS ≠ zS := fun he => hg₀ne (congrArg Subtype.val he)
  have hxx : xS * xS = 1 := by
    apply Subtype.ext
    show (g₀ * z * g₀⁻¹) * (g₀ * z * g₀⁻¹) = 1
    calc (g₀ * z * g₀⁻¹) * (g₀ * z * g₀⁻¹) = g₀ * (z * z) * g₀⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hxne1 : xS ≠ 1 := by
    intro he
    have h1 : g₀ * z * g₀⁻¹ = 1 := congrArg Subtype.val he
    apply hz1
    calc z = g₀⁻¹ * (g₀ * z * g₀⁻¹) * g₀ := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨r, hr, q, hq, hrq⟩ := hdecomp (ι xS) (hTι xS) (by rw [← map_mul, hxx, map_one])
  have hx1' : r * q ≠ 1 := by
    rw [hrq]
    intro h1
    exact hxne1 (hιinj (by rw [h1, map_one]))
  have hxz' : r * q ≠ zbar z := by
    rw [hrq]
    intro h1
    exact hxz (hιinj (h1.trans hιz.symm))
  have hxsq : (r * q) * (r * q) = 1 := by rw [hrq, ← map_mul, hxx, map_one]
  obtain ⟨s, hs, p, hp, hu2, hv2, hux, hvx, huv⟩ :=
    hpair.exists_noncommuting hQinv hr hq hxsq hx1' hxz'
  obtain ⟨uS, huS⟩ := hιT _ (mul_mem (hRT hs) (hQT hp))
  obtain ⟨vS, hvS⟩ := hιT _ (mul_mem (hRT hr) (mul_mem (hRT hs) (hQT hp)))
  have hu2S : uS * uS = 1 := hιinj (by simp only [map_mul, huS, map_one]; exact hu2)
  have hv2S : vS * vS = 1 := hιinj (by simp only [map_mul, hvS, map_one]; exact hv2)
  have huxS : uS * xS = xS * uS := hιinj (by
    simp only [map_mul, huS, ← hrq]
    exact hux)
  have hvxS : vS * xS = xS * vS := hιinj (by
    simp only [map_mul, hvS, ← hrq]
    exact hvx)
  have huvS : (uS * vS) * (uS * vS) = zS := hιinj (by
    simp only [map_mul, huS, hvS, hιz]
    exact huv)
  let D : Subgroup G := Subgroup.closure {(uS : G), (vS : G)}
  have hDS : D ≤ (S : Subgroup G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro d (rfl | rfl)
    · exact uS.2
    · exact vS.2
  have hDx : D ≤ centralizer ({g₀ * z * g₀⁻¹} : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro d (rfl | rfl)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val huxS
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hvxS
  have hDp : IsPGroup 2 ↥D := S.isPGroup'.to_le hDS
  have hg₁x : g₀⁻¹ * (g₀ * z * g₀⁻¹) * g₀⁻¹⁻¹ = z := by group
  have hKH : D.map (MulAut.conj g₀⁻¹).toMonoidHom ≤ centralizer ({z} : Set G) := by
    have h1 : centralizer ({g₀⁻¹ * (g₀ * z * g₀⁻¹) * g₀⁻¹⁻¹} : Set G) =
        (centralizer ({g₀ * z * g₀⁻¹} : Set G)).map (MulAut.conj g₀⁻¹).toMonoidHom :=
      centralizer_singleton_conj g₀⁻¹ (g₀ * z * g₀⁻¹)
    rw [hg₁x] at h1
    rw [h1]
    exact Subgroup.map_mono hDx
  obtain ⟨y, hyH, hy⟩ := exists_conj_le hS hKH (hDp.map _)
  have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hyH
  have hconjS : ∀ d ∈ D, (y⁻¹ * g₀⁻¹) * d * (y⁻¹ * g₀⁻¹)⁻¹ ∈ (S : Subgroup G) := by
    intro d hd
    have h1 : g₀⁻¹ * d * g₀⁻¹⁻¹ ∈ (S : Subgroup G).map (MulAut.conj y).toMonoidHom :=
      hy ⟨d, hd, rfl⟩
    obtain ⟨s', hs', hs'e⟩ := h1
    have h2 : y * s' * y⁻¹ = g₀⁻¹ * d * g₀⁻¹⁻¹ := hs'e
    have h3 : (y⁻¹ * g₀⁻¹) * d * (y⁻¹ * g₀⁻¹)⁻¹ = s' := by
      calc (y⁻¹ * g₀⁻¹) * d * (y⁻¹ * g₀⁻¹)⁻¹ = y⁻¹ * (g₀⁻¹ * d * g₀⁻¹⁻¹) * y := by group
        _ = y⁻¹ * (y * s' * y⁻¹) * y := by rw [h2]
        _ = s' := by group
    rw [h3]
    exact hs'
  have hgx : (y⁻¹ * g₀⁻¹) * (g₀ * z * g₀⁻¹) * (y⁻¹ * g₀⁻¹)⁻¹ = z := by
    calc (y⁻¹ * g₀⁻¹) * (g₀ * z * g₀⁻¹) * (y⁻¹ * g₀⁻¹)⁻¹ = y⁻¹ * (z * y) := by group
      _ = y⁻¹ * (y * z) := by rw [hyz]
      _ = z := by group
  have huD : (uS : G) ∈ D := Subgroup.subset_closure (Or.inl rfl)
  have hvD : (vS : G) ∈ D := Subgroup.subset_closure (Or.inr rfl)
  let u'S : ↥(S : Subgroup G) := ⟨(y⁻¹ * g₀⁻¹) * (uS : G) * (y⁻¹ * g₀⁻¹)⁻¹, hconjS _ huD⟩
  let v'S : ↥(S : Subgroup G) := ⟨(y⁻¹ * g₀⁻¹) * (vS : G) * (y⁻¹ * g₀⁻¹)⁻¹, hconjS _ hvD⟩
  have hu'2 : u'S * u'S = 1 := by
    apply Subtype.ext
    have h1 : (uS : G) * (uS : G) = 1 := congrArg Subtype.val hu2S
    show ((y⁻¹ * g₀⁻¹) * (uS : G) * (y⁻¹ * g₀⁻¹)⁻¹) * ((y⁻¹ * g₀⁻¹) * (uS : G) * (y⁻¹ * g₀⁻¹)⁻¹) = 1
    calc ((y⁻¹ * g₀⁻¹) * (uS : G) * (y⁻¹ * g₀⁻¹)⁻¹) * ((y⁻¹ * g₀⁻¹) * (uS : G) * (y⁻¹ * g₀⁻¹)⁻¹)
        = (y⁻¹ * g₀⁻¹) * ((uS : G) * (uS : G)) * (y⁻¹ * g₀⁻¹)⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hv'2 : v'S * v'S = 1 := by
    apply Subtype.ext
    have h1 : (vS : G) * (vS : G) = 1 := congrArg Subtype.val hv2S
    show ((y⁻¹ * g₀⁻¹) * (vS : G) * (y⁻¹ * g₀⁻¹)⁻¹) * ((y⁻¹ * g₀⁻¹) * (vS : G) * (y⁻¹ * g₀⁻¹)⁻¹) = 1
    calc ((y⁻¹ * g₀⁻¹) * (vS : G) * (y⁻¹ * g₀⁻¹)⁻¹) * ((y⁻¹ * g₀⁻¹) * (vS : G) * (y⁻¹ * g₀⁻¹)⁻¹)
        = (y⁻¹ * g₀⁻¹) * ((vS : G) * (vS : G)) * (y⁻¹ * g₀⁻¹)⁻¹ := by group
      _ = 1 := by rw [h1]; group
  let w'S : ↥(S : Subgroup G) := (u'S * v'S) * (u'S * v'S)
  have hw' : (w'S : G) = (y⁻¹ * g₀⁻¹) * z * (y⁻¹ * g₀⁻¹)⁻¹ := by
    have h1 : ((uS * vS) * (uS * vS) : ↥(S : Subgroup G)) = zS := huvS
    have h2 : ((uS : G) * (vS : G)) * ((uS : G) * (vS : G)) = z := congrArg Subtype.val h1
    show ((y⁻¹ * g₀⁻¹) * (uS : G) * (y⁻¹ * g₀⁻¹)⁻¹ * ((y⁻¹ * g₀⁻¹) * (vS : G) * (y⁻¹ * g₀⁻¹)⁻¹)) *
      ((y⁻¹ * g₀⁻¹) * (uS : G) * (y⁻¹ * g₀⁻¹)⁻¹ * ((y⁻¹ * g₀⁻¹) * (vS : G) * (y⁻¹ * g₀⁻¹)⁻¹)) = _
    calc ((y⁻¹ * g₀⁻¹) * (uS : G) * (y⁻¹ * g₀⁻¹)⁻¹ * ((y⁻¹ * g₀⁻¹) * (vS : G) * (y⁻¹ * g₀⁻¹)⁻¹)) *
        ((y⁻¹ * g₀⁻¹) * (uS : G) * (y⁻¹ * g₀⁻¹)⁻¹ * ((y⁻¹ * g₀⁻¹) * (vS : G) * (y⁻¹ * g₀⁻¹)⁻¹))
        = (y⁻¹ * g₀⁻¹) * (((uS : G) * (vS : G)) * ((uS : G) * (vS : G))) * (y⁻¹ * g₀⁻¹)⁻¹ := by
          group
      _ = (y⁻¹ * g₀⁻¹) * z * (y⁻¹ * g₀⁻¹)⁻¹ := by rw [h2]
  have hw'sq : w'S * w'S = 1 := by
    apply Subtype.ext
    show (w'S : G) * (w'S : G) = 1
    rw [hw']
    calc ((y⁻¹ * g₀⁻¹) * z * (y⁻¹ * g₀⁻¹)⁻¹) * ((y⁻¹ * g₀⁻¹) * z * (y⁻¹ * g₀⁻¹)⁻¹)
        = (y⁻¹ * g₀⁻¹) * (z * z) * (y⁻¹ * g₀⁻¹)⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hw'ne1 : w'S ≠ 1 := by
    intro he
    have h1 : (y⁻¹ * g₀⁻¹) * z * (y⁻¹ * g₀⁻¹)⁻¹ = 1 := by
      rw [← hw']
      exact congrArg Subtype.val he
    apply hz1
    calc z = (y⁻¹ * g₀⁻¹)⁻¹ * ((y⁻¹ * g₀⁻¹) * z * (y⁻¹ * g₀⁻¹)⁻¹) * (y⁻¹ * g₀⁻¹) := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨r₁, hr₁, q₁, hq₁, hrq₁⟩ := hdecomp (ι u'S) (hTι u'S)
    (by rw [← map_mul, hu'2, map_one])
  obtain ⟨r₂, hr₂, q₂, hq₂, hrq₂⟩ := hdecomp (ι v'S) (hTι v'S)
    (by rw [← map_mul, hv'2, map_one])
  have hw'Q : ι w'S ∈ Q := by
    have h1 := hpair.mul_sq_mem hr₁ hr₂ hq₁ hq₂
    rw [hrq₁, hrq₂] at h1
    have h2 : ι w'S = (ι u'S * ι v'S) * (ι u'S * ι v'S) := by
      simp only [w'S, map_mul]
    rw [h2]
    exact h1
  have hιw'sq : ι w'S * ι w'S = 1 := by rw [← map_mul, hw'sq, map_one]
  have hw'z : w'S = zS := by
    rcases hpair.Q_inv _ hw'Q hιw'sq with h1 | h1
    · exact absurd (hιinj (h1.trans (map_one ι).symm)) hw'ne1
    · exact hιinj (h1.trans hιz.symm)
  have hgz : (y⁻¹ * g₀⁻¹) * z * (y⁻¹ * g₀⁻¹)⁻¹ = z := by
    rw [← hw']
    exact congrArg Subtype.val hw'z
  apply hg₀ne
  calc g₀ * z * g₀⁻¹ = (y⁻¹ * g₀⁻¹)⁻¹ * ((y⁻¹ * g₀⁻¹) * (g₀ * z * g₀⁻¹) * (y⁻¹ * g₀⁻¹)⁻¹) *
        (y⁻¹ * g₀⁻¹) := by group
    _ = (y⁻¹ * g₀⁻¹)⁻¹ * z * (y⁻¹ * g₀⁻¹) := by rw [hgx]
    _ = (y⁻¹ * g₀⁻¹)⁻¹ * ((y⁻¹ * g₀⁻¹) * z * (y⁻¹ * g₀⁻¹)⁻¹) * (y⁻¹ * g₀⁻¹) := by rw [hgz]
    _ = z := by group

end Fusion

end CFSG.GH74.Uniqueness.SU.SU10
