module

public import CFSG.ClassicalInvolution.Q3.Sec13End16G

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin hiding centMembers

variable {G : Type} [Group G] [Finite G]

namespace Sit16

variable {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}

private theorem e16h_conjSub_le {H K : Subgroup G} (hK : K ≤ H) {x : G} (hx : x ∈ H) :
    conjSub x K ≤ H := by
  intro m hm
  rw [mem_conjSub_iff] at hm
  have h1 := H.mul_mem (H.mul_mem hx (hK hm)) (H.inv_mem hx)
  have e1 : x * (x⁻¹ * m * x) * x⁻¹ = m := by group
  rwa [e1] at h1

private theorem e16h_le_centralizer_of_mem {K : Subgroup G} {e : G}
    (he : e ∈ Subgroup.centralizer (K : Set G)) : K ≤ Subgroup.centralizer ({e} : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp he) k hk

private theorem e16h_comm_mul {x u t : G} (hu : x * u = u * x) (ht : x * t = t * x) :
    x * (u * t) = u * t * x := by
  rw [← mul_assoc, hu, mul_assoc u x t, ht, ← mul_assoc]

private theorem e16h_le_centralizer_e {L : Subgroup G} {u e : G} (hu2 : u * u = 1)
    (hLu : L ≤ Subgroup.centralizer ({u} : Set G)) (hLt : IsUniqueInvolution L (u * e)) :
    L ≤ Subgroup.centralizer ({e} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp (hLu hx)
  have h2 : x * (u * e) = u * e * x := (hLt.commute_of_mem hx).symm
  have he : u * (u * e) = e := by rw [← mul_assoc, hu2, one_mul]
  calc x * e = x * (u * (u * e)) := by rw [he]
    _ = u * (u * e) * x := e16h_comm_mul h1 h2
    _ = e * x := by rw [he]

theorem exists_mul_eq_of_mem_centralizer_u (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω)
    (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) {x : G}
    (hx : x ∈ Subgroup.centralizer ({u} : Set G)) :
    ∃ y ∈ pSpan (centMembers Ω u), x * e * x⁻¹ = y * e * y⁻¹ := by
  have hd : Hyp23bData Ω K K' W z u e g := c.data
  have hs : TwinSit Ω K K' z := c.twin
  have hΩ : ConjInvariant Ω := h.thmD.hyp.conjInvariant
  have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp hx
  have hxuc : x * u * x⁻¹ = u := by rw [hxu]; group
  have hue : u * (u * e) = e := by rw [← mul_assoc, hd.hu2, one_mul]
  have hJu : IsUniqueInvolution (conjSub g K) (u * e) := by
    rw [← hd.hgt]; exact hs.isInv.conj g
  have hJ'u : IsUniqueInvolution (conjSub g K') (u * e) := by
    rw [← hd.hgt]; exact hs.mem_twin.2.conj g
  have hc := c.conjSub_le_centralizer_u h h9
  have hJ : conjSub g K ∈ centMembers Ω u := ⟨hΩ g K hs.mem, hc.1⟩
  have hJ' : conjSub g K' ∈ centMembers Ω u := ⟨hΩ g K' hs.mem_twin.1, hc.2⟩
  have hxJ : conjSub x (conjSub g K) ∈ centMembers Ω u := by
    have hm := Generic.conjSub_mem_centMembers hΩ (n := x) hJ
    rwa [hxuc] at hm
  rcases EndHyp.centMembers_cases h h9 hd.hu1 (TwinSit.conj hs hΩ g) hJ hJ' with
    hEq | ⟨hOrb, -⟩
  ·
    have hmem : conjSub x (conjSub g K) = conjSub g K ∨
        conjSub x (conjSub g K) = conjSub g K' := by
      have hm := hxJ
      rw [hEq] at hm
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
    have hxt : x * (u * e) * x⁻¹ = u * e := by
      have hc' := hJu.conj x
      rcases hmem with h1 | h1
      · rw [h1] at hc'; exact hc'.eq hJu
      · rw [h1] at hc'; exact hc'.eq hJ'u
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [one_mul, inv_one, mul_one]
    calc x * e * x⁻¹ = x * (u * (u * e)) * x⁻¹ := by rw [hue]
      _ = (x * u * x⁻¹) * (x * (u * e) * x⁻¹) := by group
      _ = u * (u * e) := by rw [hxuc, hxt]
      _ = e := hue
  ·
    obtain ⟨y, hy, hyJ⟩ := hOrb _ hJ _ hxJ
    have hYC : pSpan (centMembers Ω u) ≤ Subgroup.centralizer ({u} : Set G) :=
      pSpan_le fun L hL => hL.2
    have hyu : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp (hYC hy)
    have hnJ : conjSub (y⁻¹ * x) (conjSub g K) = conjSub g K := by
      rw [conjSub_mul, ← hyJ, conjSub_inv_conjSub]
    have hnt : (y⁻¹ * x) * (u * e) * (y⁻¹ * x)⁻¹ = u * e := by
      have hc' := hJu.conj (y⁻¹ * x)
      rw [hnJ] at hc'
      exact hc'.eq hJu
    have hxt : x * (u * e) * x⁻¹ = y * (u * e) * y⁻¹ := by
      calc x * (u * e) * x⁻¹ = y * ((y⁻¹ * x) * (u * e) * (y⁻¹ * x)⁻¹) * y⁻¹ := by group
        _ = y * (u * e) * y⁻¹ := by rw [hnt]
    refine ⟨y, hy, ?_⟩
    calc x * e * x⁻¹ = x * (u * (u * e)) * x⁻¹ := by rw [hue]
      _ = (x * u * x⁻¹) * (x * (u * e) * x⁻¹) := by group
      _ = u * (y * (u * e) * y⁻¹) := by rw [hxuc, hxt]
      _ = (u * y) * (u * e) * y⁻¹ := by group
      _ = (y * u) * (u * e) * y⁻¹ := by rw [hyu]
      _ = y * (u * (u * e)) * y⁻¹ := by group
      _ = y * e * y⁻¹ := by rw [hue]

theorem conjSub_le_sup_of_mem_centralizer_z
    (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K)
    {x : G} (hx : x ∈ Subgroup.centralizer ({z} : Set G)) :
    conjSub x (pSpan (centMembers Ω e)) ≤ pSpan (centMembers Ω e) ⊔ pSpan (centMembers Ω u) := by
  have hΩ : ConjInvariant Ω := h.thmD.hyp.conjInvariant
  obtain ⟨k, hk, c', hc', rfl⟩ := mem_centralizer_z_decomp c h h9 h13 hx
  have hkC : k ∈ Subgroup.centralizer ({u} : Set G) := centralizer_sup_le_centralizer_u c hk
  obtain ⟨y, hy, hye⟩ := exists_mul_eq_of_mem_centralizer_u c h h9 h13 hkC
  have hc'e : c' * e = e * c' :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc').1
  have hce' : c' * e * c'⁻¹ = e := by rw [hc'e]; group
  have hce : (k * c') * e * (k * c')⁻¹ = k * e * k⁻¹ := by
    calc (k * c') * e * (k * c')⁻¹ = k * (c' * e * c'⁻¹) * k⁻¹ := by group
      _ = k * e * k⁻¹ := by rw [hce']
  have hn : y⁻¹ * (k * c') * e * (y⁻¹ * (k * c'))⁻¹ = e := by
    calc y⁻¹ * (k * c') * e * (y⁻¹ * (k * c'))⁻¹
        = y⁻¹ * ((k * c') * e * (k * c')⁻¹) * y := by group
      _ = y⁻¹ * (k * e * k⁻¹) * y := by rw [hce]
      _ = y⁻¹ * (y * e * y⁻¹) * y := by rw [hye]
      _ = e := by group
  have hnX : conjSub (y⁻¹ * (k * c')) (pSpan (centMembers Ω e)) ≤ pSpan (centMembers Ω e) := by
    have key : pSpan (centMembers Ω e) ≤
        conjSub (y⁻¹ * (k * c'))⁻¹ (pSpan (centMembers Ω e)) := by
      refine pSpan_le fun L hL => ?_
      have hL' := Generic.conjSub_mem_centMembers hΩ (n := y⁻¹ * (k * c')) hL
      rw [hn] at hL'
      have h2 := conjSub_mono (n := (y⁻¹ * (k * c'))⁻¹) (le_pSpan hL')
      rwa [conjSub_inv_conjSub] at h2
    have h3 := conjSub_mono (n := y⁻¹ * (k * c')) key
    rwa [conjSub_conjSub_inv] at h3
  have hXH : pSpan (centMembers Ω e) ≤ pSpan (centMembers Ω e) ⊔ pSpan (centMembers Ω u) :=
    le_sup_left
  have hYH : pSpan (centMembers Ω u) ≤
      pSpan (centMembers Ω e) ⊔ pSpan (centMembers Ω u) := le_sup_right
  have hkc : k * c' = y * (y⁻¹ * (k * c')) := by group
  calc conjSub (k * c') (pSpan (centMembers Ω e))
      = conjSub y (conjSub (y⁻¹ * (k * c')) (pSpan (centMembers Ω e))) := by
        rw [← conjSub_mul, ← hkc]
    _ ≤ conjSub y (pSpan (centMembers Ω e)) := conjSub_mono hnX
    _ ≤ pSpan (centMembers Ω e) ⊔ pSpan (centMembers Ω u) :=
        e16h_conjSub_le hXH (hYH hy)

theorem pSpan_sup_eq_top_of_X (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) :
    pSpan (centMembers Ω e) ⊔ pSpan (centMembers Ω u) = ⊤ := by
  have hΩ : ConjInvariant Ω := h.thmD.hyp.conjInvariant
  set H := pSpan (centMembers Ω e) ⊔ pSpan (centMembers Ω u) with hH_def
  have hXH : pSpan (centMembers Ω e) ≤ H := le_sup_left
  have hK : K ≤ H := by
    have hKc : K ∈ centMembers Ω e :=
      ⟨c.twin.mem, e16h_le_centralizer_of_mem (c.e_mem_centralizer h).1⟩
    exact (le_pSpan hKc).trans hXH
  have hcentres : ∀ {e' : G}, e' ∈ centres Ω K K' z → pSpan (centMembers Ω e') ≤ H := by
    intro e' he'
    obtain ⟨n, hn, hne⟩ := exists_mem_normalizer_conj_centre c h h9 he'
    have hnK : conjSub n K = K := mem_normalizer_iff_conjSub_eq.mp hn
    have hnz : n * z * n⁻¹ = z := c.twin.isInv.conj_eq hnK
    have hnzC : n ∈ Subgroup.centralizer ({z} : Set G) := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      calc n * z = n * z * n⁻¹ * n := by group
        _ = z * n := by rw [hnz]
    have hnH : conjSub n (pSpan (centMembers Ω e)) ≤ H :=
      conjSub_le_sup_of_mem_centralizer_z c h h9 h13 hnzC
    subst hne
    refine pSpan_le fun L hL => ?_
    have hL' := Generic.conjSub_mem_centMembers hΩ (n := n⁻¹) hL
    have hid : n⁻¹ * (n * e * n⁻¹) * n⁻¹⁻¹ = e := by group
    rw [hid] at hL'
    have h2 := conjSub_mono (n := n) (le_pSpan hL')
    rw [conjSub_conjSub_inv] at h2
    exact h2.trans hnH
  have horbit_nbr : ∀ N ∈ omegaStarNbr Ω K, ∃ x ∈ H, conjSub x K = N := by
    intro N hN
    obtain ⟨W', u', e', g', c', hD, -⟩ := exists_frame_of_omegaStarNbr c h h9 hN
    have hcen' : e' ∈ centres Ω K K' z := by
      simp only [centres, Set.mem_setOf_eq]
      exact ⟨W', u', g', c'⟩
    have hNc : N ∈ centMembers Ω e' := dSet_subset_centMembers c' h hD
    have hKc' : K ∈ centMembers Ω e' :=
      ⟨c.twin.mem, e16h_le_centralizer_of_mem (c'.e_mem_centralizer h).1⟩
    obtain ⟨x, hx, hxN⟩ := centMembers_oneClass c' h h9 K hKc' N hNc
    exact ⟨x, hcentres hcen' hx, hxN⟩
  have horbit : ∀ J ∈ dstarComp Ω K, ∃ x ∈ H, conjSub x K = J := by
    intro J hJ
    have hJ' : Relation.ReflTransGen (dstarAdj Ω) K J := hJ
    clear hJ
    induction hJ' with
    | refl => exact ⟨1, H.one_mem, conjSub_one K⟩
    | @tail b M _ hbc ih =>
      obtain ⟨p, hpH, rfl⟩ := ih
      obtain ⟨hMΩ, hcase⟩ := hbc
      have hnbr : M ∈ omegaStarNbr Ω (conjSub p K) := by
        rcases hcase with h1 | h1
        · exact h1
        · exact Q3.Q3T6.Mu.omegaStarNbr_symm h.thmD.hyp hMΩ (hΩ p K c.twin.mem) h1
      have hM₀ : conjSub p⁻¹ M ∈ omegaStarNbr Ω K := by
        have hm := Asc77.omegaStarNbr_conj hΩ hnbr p⁻¹
        rwa [conjSub_inv_conjSub] at hm
      obtain ⟨x, hxH, hxM⟩ := horbit_nbr _ hM₀
      refine ⟨p * x, H.mul_mem hpH hxH, ?_⟩
      rw [conjSub_mul, hxM, conjSub_conjSub_inv]
  have hall : ∀ M ∈ Ω, M ≤ H := by
    intro M hM
    obtain ⟨x, hx, hxM⟩ := horbit M (h.star K c.twin.mem M hM)
    rw [← hxM]
    exact e16h_conjSub_le hK hx
  have htop : (⊤ : Subgroup G) ≤ H := by
    rw [← h.thmD.gen]
    exact pSpan_le hall
  exact eq_top_iff.mpr htop

theorem centMembers_u_ne_pair (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) :
    centMembers Ω u ≠ {conjSub g K, conjSub g K'} := by
  intro hEq
  have hd : Hyp23bData Ω K K' W z u e g := c.data
  have hs : TwinSit Ω K K' z := c.twin
  have hJu : IsUniqueInvolution (conjSub g K) (u * e) := by
    rw [← hd.hgt]; exact hs.isInv.conj g
  have hJ'u : IsUniqueInvolution (conjSub g K') (u * e) := by
    rw [← hd.hgt]; exact hs.mem_twin.2.conj g
  have hYe : pSpan (centMembers Ω u) ≤ Subgroup.centralizer ({e} : Set G) := by
    refine pSpan_le fun L hL => ?_
    have hLm := hL
    rw [hEq] at hLm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hLm
    rcases hLm with rfl | rfl
    · exact e16h_le_centralizer_e hd.hu2 hL.2 hJu
    · exact e16h_le_centralizer_e hd.hu2 hL.2 hJ'u
  have hXe : pSpan (centMembers Ω e) ≤ Subgroup.centralizer ({e} : Set G) :=
    pSpan_le fun L hL => hL.2
  have hall : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({e} : Set G) := by
    rw [← pSpan_sup_eq_top_of_X c h h9 h13]
    exact sup_le hXe hYe
  have hcen : e ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g'
    exact Subgroup.mem_centralizer_singleton_iff.mp (hall (Subgroup.mem_top g'))
  rw [h.toStarHyp.center] at hcen
  exact hd.he1 (Subgroup.mem_bot.mp hcen)

theorem centMembers_u_oneClass (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) :
    ∀ L ∈ centMembers Ω u, ∀ L' ∈ centMembers Ω u,
      ∃ x ∈ pSpan (centMembers Ω u), conjSub x L = L' := by
  have hd : Hyp23bData Ω K K' W z u e g := c.data
  have hs : TwinSit Ω K K' z := c.twin
  have hΩ : ConjInvariant Ω := h.thmD.hyp.conjInvariant
  have hc := c.conjSub_le_centralizer_u h h9
  have hJ : conjSub g K ∈ centMembers Ω u := ⟨hΩ g K hs.mem, hc.1⟩
  have hJ' : conjSub g K' ∈ centMembers Ω u := ⟨hΩ g K' hs.mem_twin.1, hc.2⟩
  rcases EndHyp.centMembers_cases h h9 hd.hu1 (TwinSit.conj hs hΩ g) hJ hJ' with
    hEq | hOrb
  · exact absurd hEq (centMembers_u_ne_pair c h h9 h13)
  · exact hOrb.1

end Sit16

end CFSG.ClassicalInvolution.Q3.Sec13
