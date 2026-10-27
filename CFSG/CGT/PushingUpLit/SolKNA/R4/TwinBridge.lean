module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Step
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm1RTwin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Proving.CentralOddFreeTwoGroup

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.PhilipHall CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {N : Subgroup Y} [N.Normal]

theorem conjSub_map_ne_of_twinR (hd : TightDatum R S t) (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) {c y : Y} (hcN : c ∈ N) (hc1 : c ≠ 1)
    (hy : y * t * y⁻¹ = t * c) :
    conjSub (QuotientGroup.mk' N y) ((tightCore R).map (QuotientGroup.mk' N)) ≠
      (tightCore R).map (QuotientGroup.mk' N) := by
  intro heq
  rw [← TwistQ.conjSub_map (N := N)] at heq
  have h0 := core_inf_eq_bot hd hN2 htN
  have htK : t ∈ tightCore R := hd.isUniqueInvolution_core.mem
  have hcZ : ∀ a : Y, a * c = c * a := Subgroup.mem_center_iff.mp (hNc hcN)
  have hS₀K : (S : Subgroup R).map R.subtype ≤ tightCore R := hd.sylow_core.1
  have hsq : ∀ k ∈ tightCore R, ∀ ν ∈ N, (k * ν) * (k * ν) = t * c → ν * ν = c := by
    intro k hk ν hν hkν
    have hνZ : ∀ a : Y, a * ν = ν * a := Subgroup.mem_center_iff.mp (hNc hν)
    have e1 : (k * ν) * (k * ν) = (k * k) * (ν * ν) := by
      calc (k * ν) * (k * ν) = k * (ν * k) * ν := by group
        _ = k * (k * ν) * ν := by rw [← hνZ k]
        _ = (k * k) * (ν * ν) := by group
    rw [e1] at hkν
    have h2 : t⁻¹ * (k * k) ∈ tightCore R ⊓ N := by
      refine ⟨(tightCore R).mul_mem ((tightCore R).inv_mem htK)
        ((tightCore R).mul_mem hk hk), ?_⟩
      have : t⁻¹ * (k * k) = c * (ν * ν)⁻¹ := by
        have h3 : k * k = t * c * (ν * ν)⁻¹ := by
          rw [← hkν]
          group
        rw [h3]
        have hcc : t⁻¹ * (t * c * (ν * ν)⁻¹) = c * (ν * ν)⁻¹ := by group
        exact hcc
      rw [this]
      exact N.mul_mem hcN (N.inv_mem (N.mul_mem hν hν))
    rw [h0, Subgroup.mem_bot] at h2
    have h3 : k * k = t := by
      calc k * k = t * (t⁻¹ * (k * k)) := by group
        _ = t := by rw [h2, mul_one]
    rw [h3] at hkν
    exact (mul_left_cancel hkν)
  have hdec : ∀ r ∈ tightCore R, ∃ k ∈ tightCore R, ∃ ν ∈ N, y * r * y⁻¹ = k * ν := by
    intro r hr
    have h1 : QuotientGroup.mk' N (y * r * y⁻¹) ∈
        (conjSub y (tightCore R)).map (QuotientGroup.mk' N) :=
      Subgroup.mem_map_of_mem _ (conj_mem_conjSub hr)
    rw [heq] at h1
    obtain ⟨k, hk, hkx⟩ := h1
    refine ⟨k, hk, k⁻¹ * (y * r * y⁻¹), ?_, by group⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkx
    exact hkx
  obtain ⟨r₁, hr₁, r₂, hr₂, h1, h2, h12⟩ := TL4.exists_S₀_pair_R hd
  have hr₁K := hS₀K hr₁
  have hr₂K := hS₀K hr₂
  obtain ⟨k₁, hk₁, ν₁, hν₁, e₁⟩ := hdec r₁ hr₁K
  obtain ⟨k₂, hk₂, ν₂, hν₂, e₂⟩ := hdec r₂ hr₂K
  have hsq₁ : y * r₁ * y⁻¹ * (y * r₁ * y⁻¹) = t * c := by
    calc y * r₁ * y⁻¹ * (y * r₁ * y⁻¹) = y * (r₁ * r₁) * y⁻¹ := by group
      _ = t * c := by rw [h1, hy]
  have hsq₂ : y * r₂ * y⁻¹ * (y * r₂ * y⁻¹) = t * c := by
    calc y * r₂ * y⁻¹ * (y * r₂ * y⁻¹) = y * (r₂ * r₂) * y⁻¹ := by group
      _ = t * c := by rw [h2, hy]
  have hsq₃ : y * (r₁ * r₂) * y⁻¹ * (y * (r₁ * r₂) * y⁻¹) = t * c := by
    calc y * (r₁ * r₂) * y⁻¹ * (y * (r₁ * r₂) * y⁻¹) = y * ((r₁ * r₂) * (r₁ * r₂)) * y⁻¹ := by
          group
      _ = t * c := by rw [h12, hy]
  rw [e₁] at hsq₁
  rw [e₂] at hsq₂
  have hν₁c := hsq k₁ hk₁ ν₁ hν₁ hsq₁
  have hν₂c := hsq k₂ hk₂ ν₂ hν₂ hsq₂
  have hx₃ : y * (r₁ * r₂) * y⁻¹ = (k₁ * k₂) * (ν₁ * ν₂) := by
    have e3 : y * (r₁ * r₂) * y⁻¹ = (y * r₁ * y⁻¹) * (y * r₂ * y⁻¹) := by group
    rw [e3, e₁, e₂]
    have hνZ : ∀ a : Y, a * ν₁ = ν₁ * a := Subgroup.mem_center_iff.mp (hNc hν₁)
    calc k₁ * ν₁ * (k₂ * ν₂) = k₁ * (ν₁ * k₂) * ν₂ := by group
      _ = k₁ * (k₂ * ν₁) * ν₂ := by rw [← hνZ k₂]
      _ = (k₁ * k₂) * (ν₁ * ν₂) := by group
  rw [hx₃] at hsq₃
  have hν₃c := hsq (k₁ * k₂) ((tightCore R).mul_mem hk₁ hk₂) (ν₁ * ν₂) (N.mul_mem hν₁ hν₂) hsq₃
  have hνZ₂ : ∀ a : Y, a * ν₁ = ν₁ * a := Subgroup.mem_center_iff.mp (hNc hν₁)
  have hcc : (ν₁ * ν₂) * (ν₁ * ν₂) = (ν₁ * ν₁) * (ν₂ * ν₂) := by
    calc (ν₁ * ν₂) * (ν₁ * ν₂) = ν₁ * (ν₂ * ν₁) * ν₂ := by group
      _ = ν₁ * (ν₁ * ν₂) * ν₂ := by rw [← hνZ₂ ν₂]
      _ = (ν₁ * ν₁) * (ν₂ * ν₂) := by group
  rw [hcc, hν₁c, hν₂c] at hν₃c
  exact hc1 (mul_left_cancel (a := c) (by rw [mul_one]; exact hν₃c))

theorem exists_twin_mapR (hd : TightDatum R S t) (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) {c y : Y} (hcN : c ∈ N) (hc1 : c ≠ 1)
    (hy : y * t * y⁻¹ = t * c) :
    ∃ K' ∈ twinSet (CoreAssembly.conjClass ((tightCore R).map (QuotientGroup.mk' N)))
      ((tightCore R).map (QuotientGroup.mk' N)),
      K' ≠ (tightCore R).map (QuotientGroup.mk' N) := by
  refine ⟨conjSub (QuotientGroup.mk' N y) ((tightCore R).map (QuotientGroup.mk' N)), ?_,
    conjSub_map_ne_of_twinR hd hNc hN2 htN hcN hc1 hy⟩
  have hz := isUniqueInvolution_map_core hd hN2 htN
  have hfix : QuotientGroup.mk' N y * QuotientGroup.mk' N t * (QuotientGroup.mk' N y)⁻¹ =
      QuotientGroup.mk' N t := by
    have hπc : QuotientGroup.mk' N c = 1 := (QuotientGroup.eq_one_iff c).mpr hcN
    rw [← map_inv, ← map_mul, ← map_mul, hy, map_mul, hπc, mul_one]
  refine ⟨⟨QuotientGroup.mk' N y, ?_⟩, QuotientGroup.mk' N t, hz, ?_⟩
  · rfl
  · have := hz.conj (QuotientGroup.mk' N y)
    rwa [hfix] at this

structure QQuot (r : ℕ) (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (N : Subgroup Y) [N.Normal] :
    Prop where
  datum : Q8TwinDatum (R.map (QuotientGroup.mk' N)) (TwistQ.sylowMap N S) (QuotientGroup.mk' N t)
  cls : TightClsR r (Y ⧸ N) (R.map (QuotientGroup.mk' N)) (TwistQ.sylowMap N S)
    (QuotientGroup.mk' N t)
  hyp : HypOmegaGen (CoreAssembly.conjClass (tightCore (R.map (QuotientGroup.mk' N))))
  sylow : ∃ P : Subgroup (Y ⧸ N), IsSylow2In P (tightCore (R.map (QuotientGroup.mk' N))) ∧
    Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2)))
  twin : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore (R.map (QuotientGroup.mk' N))))
    (tightCore (R.map (QuotientGroup.mk' N))), K' ≠ tightCore (R.map (QuotientGroup.mk' N))
  card_lt : Nat.card (Y ⧸ N) < Nat.card Y

theorem qQuot_of_twin {r : ℕ} (hd : TightDatum R S t) (hc : TightClsR r Y R S t)
    (hNc : N ≤ Subgroup.center Y) (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) {c y : Y} (hcN : c ∈ N)
    (hc1 : c ≠ 1) (hy : y * t * y⁻¹ = t * c) : QQuot r R S t N := by
  have hRN := TwistQ.inf_eq_bot hd hN2 htN
  have hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))) := hc.1
  have hcore : tightCore (R.map (QuotientGroup.mk' N)) = (tightCore R).map (QuotientGroup.mk' N) :=
    (TwistQ.tightCore_map hRN).symm
  refine ⟨q8TwinDatum_map hd hN2 htN, twistQ_clsR hd hNc hN2 htN hc, ?_, ?_, ?_, ?_⟩
  · rw [hcore]
    exact hypOmegaGen_map hd hNc hN2 htN
  · rw [hcore]
    set S₀ : Subgroup Y := (S : Subgroup R).map R.subtype with hS₀
    have hS₀N : S₀ ⊓ N = ⊥ :=
      eq_bot_iff.mpr ((inf_le_inf_right N hd.S₀_le).trans hRN.le)
    refine ⟨S₀.map (QuotientGroup.mk' N),
      Hall196.isSylow2In_map_hom (QuotientGroup.mk' N) hd.sylow_core,
      ⟨((AscQuot.quotRestrictEquiv hS₀N).symm.trans
        (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm).trans
        hq.some⟩⟩
  · rw [hcore]
    exact exists_twin_mapR hd hNc hN2 htN hcN hc1 hy
  · exact TwistQ.card_lt (N := N) (fun h => hc1 (by
      have := hcN
      rw [h, Subgroup.mem_bot] at this
      exact this))

theorem conjSub_eq_of_map_conjSub_eqR (hd : TightDatum R S t) (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) {u : Y}
    (h : conjSub (QuotientGroup.mk' N u) ((tightCore R).map (QuotientGroup.mk' N)) =
      (tightCore R).map (QuotientGroup.mk' N)) :
    conjSub u (tightCore R) = tightCore R := by
  have h0 := core_inf_eq_bot hd hN2 htN
  have htK : t ∈ tightCore R := hd.isUniqueInvolution_core.mem
  have hx : QuotientGroup.mk' N (u * t * u⁻¹) ∈ (tightCore R).map (QuotientGroup.mk' N) := by
    rw [← h]
    have h1 := conj_mem_conjSub (n := QuotientGroup.mk' N u)
      (Subgroup.mem_map_of_mem (QuotientGroup.mk' N) htK)
    rwa [← map_inv, ← map_mul, ← map_mul] at h1
  obtain ⟨k, hk, hkx⟩ := hx
  have hνN : k⁻¹ * (u * t * u⁻¹) ∈ N := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkx
    exact hkx
  set ν : Y := k⁻¹ * (u * t * u⁻¹) with hν
  have hxe : u * t * u⁻¹ = k * ν := by rw [hν]; group
  have hνZ : ∀ a : Y, a * ν = ν * a := Subgroup.mem_center_iff.mp (hNc hνN)
  have hx2 : (u * t * u⁻¹) * (u * t * u⁻¹) = 1 := by
    calc (u * t * u⁻¹) * (u * t * u⁻¹) = u * (t * t) * u⁻¹ := by group
      _ = 1 := by rw [t_mul_t hd]; group
  have hkk : k * k = 1 := by
    rw [hxe] at hx2
    have e1 : (k * ν) * (k * ν) = (k * k) * (ν * ν) := by
      calc (k * ν) * (k * ν) = k * (ν * k) * ν := by group
        _ = k * (k * ν) * ν := by rw [← hνZ k]
        _ = (k * k) * (ν * ν) := by group
    rw [e1] at hx2
    have h2 : k * k ∈ tightCore R ⊓ N := by
      refine ⟨(tightCore R).mul_mem hk hk, ?_⟩
      have : k * k = (ν * ν)⁻¹ := eq_inv_of_mul_eq_one_left hx2
      rw [this]
      exact N.inv_mem (N.mul_mem hνN hνN)
    rw [h0, Subgroup.mem_bot] at h2
    exact h2
  rcases hd.isUniqueInvolution_core.unique k hk hkk with hk1 | hkt
  · exfalso
    apply htN
    have hxN : u * t * u⁻¹ ∈ N := by rw [hxe, hk1, one_mul]; exact hνN
    have h3 := (inferInstance : N.Normal).conj_mem _ hxN u⁻¹
    rwa [show u⁻¹ * (u * t * u⁻¹) * u⁻¹⁻¹ = t by group] at h3
  · by_cases hν1 : ν = 1
    · have hut : u * t * u⁻¹ = t := by rw [hxe, hkt, hν1, mul_one]
      have hC : u ∈ Subgroup.centralizer ({t} : Set Y) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc u * t = (u * t * u⁻¹) * u := by group
          _ = t * u := by rw [hut]
      exact mem_normalizer_iff_conjSub_eq.mp (hd.le_normalizer_core hC)
    · exfalso
      exact conjSub_map_ne_of_twinR hd hNc hN2 htN (c := ν) (y := u) hνN hν1
        (by rw [hxe, hkt]) h

theorem centQuotGen_of_tightR (hd : TightDatum R S t) (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) :
    CentQuotGen (CoreAssembly.conjClass (tightCore R)) N where
  hyp := hd.hypOmegaGen
  hyp' := by
    have h : quotFamily (CoreAssembly.conjClass (tightCore R)) N =
        CoreAssembly.conjClass ((tightCore R).map (QuotientGroup.mk' N)) :=
      image_conjClass (N := N) (tightCore R)
    rw [h]
    exact hypOmegaGen_map hd hNc hN2 htN
  meet J hJ := by
    rw [inf_comm]
    exact inf_conj_eq_bot hd hN2 htN hJ
  eq_of_map := by
    rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩ hmap
    rw [TwistQ.conjSub_map (N := N), TwistQ.conjSub_map (N := N)] at hmap
    have h1 : conjSub (QuotientGroup.mk' N (h⁻¹ * g)) ((tightCore R).map (QuotientGroup.mk' N)) =
        (tightCore R).map (QuotientGroup.mk' N) := by
      rw [map_mul, map_inv, conjSub_mul, hmap, conjSub_inv_conjSub]
    have h2 := conjSub_eq_of_map_conjSub_eqR hd hNc hN2 htN h1
    calc conjSub g (tightCore R) = conjSub h (conjSub (h⁻¹ * g) (tightCore R)) := by
          rw [← conjSub_mul]
          congr 1
          group
      _ = conjSub h (tightCore R) := by rw [h2]
  normalizer_of_map := by
    rintro _ ⟨g, rfl⟩ u hu
    rw [TwistQ.conjSub_map (N := N), mem_normalizer_iff_conjSub_eq] at hu
    have h1 : conjSub (QuotientGroup.mk' N (g⁻¹ * u * g))
        ((tightCore R).map (QuotientGroup.mk' N)) = (tightCore R).map (QuotientGroup.mk' N) := by
      have : conjSub (QuotientGroup.mk' N g)⁻¹ (conjSub (QuotientGroup.mk' N u)
          (conjSub (QuotientGroup.mk' N g) ((tightCore R).map (QuotientGroup.mk' N)))) =
          (tightCore R).map (QuotientGroup.mk' N) := by
        rw [hu, conjSub_inv_conjSub]
      rw [map_mul, map_mul, map_inv, conjSub_mul, conjSub_mul]
      exact this
    have h2 := conjSub_eq_of_map_conjSub_eqR hd hNc hN2 htN h1
    rw [mem_normalizer_iff_conjSub_eq]
    calc conjSub u (conjSub g (tightCore R))
        = conjSub g (conjSub (g⁻¹ * u * g) (tightCore R)) := by
          rw [← conjSub_mul, ← conjSub_mul]
          congr 1
          group
      _ = conjSub g (tightCore R) := by rw [h2]

theorem aEmpty_mapR (hd : TightDatum R S t) (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) :
    AEmpty (CoreAssembly.conjClass ((tightCore R).map (QuotientGroup.mk' N)))
      ((tightCore R).map (QuotientGroup.mk' N)) := by
  have h : quotFamily (CoreAssembly.conjClass (tightCore R)) N =
      CoreAssembly.conjClass ((tightCore R).map (QuotientGroup.mk' N)) :=
    image_conjClass (N := N) (tightCore R)
  have := (centQuotGen_of_tightR hd hNc hN2 htN).aEmpty_quotFamily (fun J hJ => hd.aEmpty J hJ)
    ((tightCore R).map (QuotientGroup.mk' N))
    (map_mem_quotFamily (CoreAssembly.mem_conjClass_self _))
  rw [h] at this
  exact this

theorem aEmpty_map'R (hd : TightDatum R S t) (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) :
    AEmpty (CoreAssembly.conjClass (tightCore (R.map (QuotientGroup.mk' N))))
      (tightCore (R.map (QuotientGroup.mk' N))) := by
  rw [← TwistQ.tightCore_map (TwistQ.inf_eq_bot hd hN2 htN)]
  exact aEmpty_mapR hd hNc hN2 htN

structure QBridge (r : ℕ) (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (N : Subgroup Y) [N.Normal] :
    Prop where
  central : N ≤ Subgroup.center Y
  two : IsPGroup 2 ↥N
  not_mem : t ∉ N
  quat : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))
  quot : QQuot r R S t N
  simple : IsSimpleGroup ↥(genFittingFStar (Y ⧸ N))
  nonab : ∃ a b : ↥(genFittingFStar (Y ⧸ N)), a * b ≠ b * a
  aEmpty : AEmpty (CoreAssembly.conjClass (tightCore (R.map (QuotientGroup.mk' N))))
    (tightCore (R.map (QuotientGroup.mk' N)))

theorem qBridge_of_centTwin {r : ℕ} (hd : TightDatum R S t) (hc : TightClsR r Y R S t)
    (hE2 : ¬ TightInO2 t) (hQ : TightFStarQuasisimple Y) {c y : Y}
    (hcZ : c ∈ Subgroup.center Y) (hc1 : c ≠ 1) (hy : y * t * y⁻¹ = t * c) :
    QBridge r R S t (TA3.fstarCenter Y) := by
  have hNc : TA3.fstarCenter Y ≤ Subgroup.center Y := fstarCenter_le_center_R hd hc hE2
  have hN2 : IsPGroup 2 ↥(TA3.fstarCenter Y) := isPGroup_fstarCenter_R hc
  have htN : t ∉ TA3.fstarCenter Y := not_mem_fstarCenter_R hc hE2
  have hcN : c ∈ TA3.fstarCenter Y := by
    have hcC : c ∈ Subgroup.centralizer (genFittingFStar Y : Set Y) :=
      Subgroup.mem_centralizer_iff.mpr fun g _ => Subgroup.mem_center_iff.mp hcZ g
    have hcF : c ∈ genFittingFStar Y := CFSG.Adapters.generalized_fitting_self_centralizing Y hcC
    refine ⟨⟨c, hcF⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hcZ g)
  obtain ⟨hFs, hFn⟩ := fstar_quot_quasisimple hQ hNc
  exact ⟨hNc, hN2, htN, hc.1, qQuot_of_twin hd hc hNc hN2 htN hcN hc1 hy, hFs, hFn,
    aEmpty_map'R hd hNc hN2 htN⟩

theorem qBridge_of_twisted {r : ℕ} (hd : TightDatum R S t) (hc : TightClsR r Y R S t)
    (hE2 : ¬ TightInO2 t) (htw : TightTwisted Y t)
    (hall : ∀ c ∈ Subgroup.center Y, orderOf c = 2 → ∃ y : Y, y * t * y⁻¹ = t * c) :
    QBridge r R S t (genFittingFitting Y) := by
  obtain ⟨L, hLc, hLn, hlayer, htL, -, hFc, hFL⟩ := htw
  have hN2 : IsPGroup 2 ↥(genFittingFitting Y) := isPGroup_two_genFittingFitting hc.2.2
  have htN : t ∉ genFittingFitting Y := fun h' => hE2 ⟨_, genFittingFitting_normal, hN2, h'⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : genFittingFitting Y ≠ ⊥ := fun h1 => hFL (h1 ▸ bot_le)
  obtain ⟨m, hm⟩ := hN2.exists_card_eq
  have hm0 : m ≠ 0 := by
    intro h1
    rw [h1, pow_zero] at hm
    exact hne (Subgroup.card_eq_one.mp hm)
  have hdvd : 2 ∣ Nat.card ↥(genFittingFitting Y) := by
    rw [hm]
    exact dvd_pow_self 2 hm0
  obtain ⟨c, hc2⟩ := exists_prime_orderOf_dvd_card' (G := ↥(genFittingFitting Y)) 2 hdvd
  have hc2' : orderOf (c : Y) = 2 := by rw [Subgroup.orderOf_coe]; exact hc2
  have hc1 : (c : Y) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hc2'
    exact absurd hc2' (by norm_num)
  obtain ⟨y, hy⟩ := hall (c : Y) (hFc c.2) hc2'
  obtain ⟨hFs, hFn⟩ := fstar_quot_twisted hLc hLn hlayer hFc
  exact ⟨hFc, hN2, htN, hc.1, qQuot_of_twin hd hc hFc hN2 htN c.2 hc1 hy, hFs, hFn,
    aEmpty_map'R hd hFc hN2 htN⟩

section Cit3

@[expose] def Thm1RTwinBelowR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), Q8TwinDatum R S t →
      Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))) → TightSelfGen R →
      TightOddFree Y → HypOmegaGen (CoreAssembly.conjClass (tightCore R)) →
      AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
      (∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        K' ≠ tightCore R) → TightInO2 t ∨ Frame.TwinE4 Y

theorem Thm1RTwinBelowR.mono {r m n : ℕ} (h : m ≤ n) (H : Thm1RTwinBelowR r n) :
    Thm1RTwinBelowR r m :=
  fun Y _ _ hlt => H Y (lt_of_lt_of_le hlt h)

theorem thm1RTwinBelowR_zero (r : ℕ) : Thm1RTwinBelowR r 0 :=
  fun _ _ _ hlt => absurd hlt (Nat.not_lt_zero _)

theorem tightCentTwinLiftR_at {r n : ℕ} (h : Thm1RTwinBelowR r n) : TightCentTwinLiftR r n := by
  intro _ _ Y _ _ hn R S t hd hc hE2 hQ _ c hcZ hc1 hy hE4
  obtain ⟨y, hy⟩ := hy
  have B := qBridge_of_centTwin hd hc hE2 hQ hcZ hc1 hy
  have := B.simple
  have hlt : Nat.card (Y ⧸ TA3.fstarCenter Y) < n := hn ▸ B.quot.card_lt
  have hcN : c ∈ TA3.fstarCenter Y := by
    have hcC : c ∈ Subgroup.centralizer (genFittingFStar Y : Set Y) :=
      Subgroup.mem_centralizer_iff.mpr fun g _ => Subgroup.mem_center_iff.mp hcZ g
    have hcF : c ∈ genFittingFStar Y := CFSG.Adapters.generalized_fitting_self_centralizing Y hcC
    refine ⟨⟨c, hcF⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hcZ g)
  have hNbot : TA3.fstarCenter Y ≠ ⊥ := fun hb' => hc1 (by simpa [hb'] using hcN)
  have ht1 : QuotientGroup.mk' (TA3.fstarCenter Y) t ≠ 1 := by
    intro h1
    have := B.quot.datum.order
    rw [h1, orderOf_one] at this
    omega
  rcases h _ hlt _ _ _ B.quot.datum B.quot.cls.1 B.quot.cls.2.1 B.quot.cls.2.2 B.quot.hyp
      B.aEmpty B.quot.twin with h1 | h2
  · exact absurd h1 (Frame.not_tightInO2_of_fstar B.nonab ht1)
  · exact hE4 (tightE4_of_exLie_quotient B.two hNbot (h2.exLie B.nonab))

theorem tightTwistAllTwinR_at {r n : ℕ} (h : Thm1RTwinBelowR r n) : TightTwistAllTwinR r n := by
  intro _ _ Y _ _ hn R S t hd hc hE2 htw hall _ hE4
  have B := qBridge_of_twisted hd hc hE2 htw hall
  have := B.simple
  have hlt : Nat.card (Y ⧸ genFittingFitting Y) < n := hn ▸ B.quot.card_lt
  obtain ⟨L, -, -, -, -, -, hFc, hFL⟩ := htw
  have hN2 := PhilipHall.Proving.isPGroup_two_genFittingFitting hc.2.2 hFc
  have hNbot := PhilipHall.Proving.genFittingFitting_ne_bot_of_not_le hFL
  have ht1 : QuotientGroup.mk' (genFittingFitting Y) t ≠ 1 := by
    intro h1
    have := B.quot.datum.order
    rw [h1, orderOf_one] at this
    omega
  rcases h _ hlt _ _ _ B.quot.datum B.quot.cls.1 B.quot.cls.2.1 B.quot.cls.2.2 B.quot.hyp
      B.aEmpty B.quot.twin with h1 | h2
  · exact absurd h1 (Frame.not_tightInO2_of_fstar B.nonab ht1)
  · exact hE4 (tightE4_of_exLie_quotient hN2 hNbot (h2.exLie B.nonab))

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4
