module

public import CFSG.LargeExtraspecial.S8CBF3D4Cfg

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup
open scoped commutatorElement

variable {X : Type*} [Group X]

theorem eq_or_eq_of_isSimpleGroup_quotient {R N H : Subgroup X}
    [hNn : (N.subgroupOf R).Normal] [IsSimpleGroup (↥R ⧸ N.subgroupOf R)] (hNH : N ≤ H)
    (hHR : H ≤ R) (hRH : ∀ r ∈ R, ∀ h ∈ H, r * h * r⁻¹ ∈ H) : H = N ∨ H = R := by
  set q := QuotientGroup.mk' (N.subgroupOf R)
  set K' := (H.subgroupOf R).map q with hK'
  have hK'n : K'.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨h, hh, rfl⟩ := hx
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf R) g
    refine ⟨r * h * r⁻¹, ?_, by simp [q]⟩
    rw [SetLike.mem_coe, mem_subgroupOf] at hh ⊢
    simpa using hRH r r.2 h hh
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K' with h1 | h1
  · left
    refine le_antisymm (fun x hx => ?_) hNH
    have hm : q ⟨x, hHR hx⟩ ∈ K' := ⟨⟨x, hHR hx⟩, mem_subgroupOf.2 hx, rfl⟩
    rw [h1, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at hm
    exact hm
  · right
    refine le_antisymm hHR fun x hx => ?_
    have hm : q ⟨x, hx⟩ ∈ K' := h1 ▸ mem_top _
    obtain ⟨y, hy, hyx⟩ := hm
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
      at hyx
    rw [SetLike.mem_coe, mem_subgroupOf] at hy
    have e : x = (y : X) * ((y : X)⁻¹ * x) := by group
    rw [e]
    simp only [coe_mul, coe_inv] at hyx
    exact mul_mem hy (hNH hyx)

theorem exists_mul_ne_of_extraspecial {N : Subgroup X} (hN : CFSG.IsExtraspecialPGroup 2 N) :
    ∃ x ∈ N, ∃ y ∈ N, x * y ≠ y * x := by
  by_contra h
  push Not at h
  have hcomm : commutator N = ⊥ := by
    rw [_root_.commutator_def, commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [mem_centralizer_iff]
    intro y _
    exact Subtype.ext (h y y.2 x x.2)
  have hc := hN.2.2.2
  rw [← hN.2.1, hcomm, card_bot] at hc
  exact absurd hc (by norm_num)

theorem sq_commute_of_mk_commute {U : Subgroup X} {t : X} (htU : t ∈ U) (hto : orderOf t = 2)
    {u : U}
    (hu : QuotientGroup.mk' (center ↥U) u * QuotientGroup.mk' (center ↥U) ⟨t, htU⟩ =
      QuotientGroup.mk' (center ↥U) ⟨t, htU⟩ * QuotientGroup.mk' (center ↥U) u) :
    (u : X) ^ 2 * t = t * (u : X) ^ 2 := by
  have ht2 : t * t = 1 := by rw [← sq, ← hto, pow_orderOf_eq_one]
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at hu
  set T : U := ⟨t, htU⟩ with hT
  obtain ⟨w, hwc, e1⟩ : ∃ w : U, (∀ v : U, v * w = w * v) ∧ T * u = u * T * w :=
    ⟨(u * T)⁻¹ * (T * u), fun v => mem_center_iff.1 hu v, by group⟩
  have ht2' : T * T = 1 := Subtype.ext ht2
  have e2 : u⁻¹ * T * u = T * w := by
    calc u⁻¹ * T * u = u⁻¹ * (T * u) := by group
      _ = u⁻¹ * (u * T * w) := by rw [e1]
      _ = T * w := by group
  have hw2 : w * w = 1 := by
    have h1 : (T * w) * (T * w) = 1 := by
      rw [← e2]
      calc u⁻¹ * T * u * (u⁻¹ * T * u) = u⁻¹ * (T * T) * u := by group
        _ = 1 := by rw [ht2']; group
    calc w * w = (T * T) * (w * w) := by rw [ht2', one_mul]
      _ = T * (T * w) * w := by group
      _ = T * (w * T) * w := by rw [hwc T]
      _ = (T * w) * (T * w) := by group
      _ = 1 := h1
  have e3 : u⁻¹ * u⁻¹ * T * u * u = T := by
    calc u⁻¹ * u⁻¹ * T * u * u = u⁻¹ * (u⁻¹ * T * u) * u := by group
      _ = u⁻¹ * (T * w) * u := by rw [e2]
      _ = u⁻¹ * T * (w * u) := by group
      _ = u⁻¹ * T * (u * w) := by rw [hwc u]
      _ = (u⁻¹ * T * u) * w := by group
      _ = T * (w * w) := by rw [e2]; group
      _ = T := by rw [hw2, mul_one]
  have e4 := congrArg Subtype.val e3
  simp only [coe_mul, coe_inv, hT] at e4
  rw [sq]
  calc (u : X) * u * t = (u : X) * u * ((u : X)⁻¹ * (u : X)⁻¹ * t * u * u) := by rw [e4]
    _ = t * ((u : X) * u) := by group

theorem a5Config_quotient_center {U : Subgroup X} {t : X} (htU : t ∈ U) (hto : orderOf t = 2)
    (hnc : ∃ u ∈ U, u * t ≠ t * u) {R N : Subgroup X} (hNR : N ≤ R) (hRU : R ≤ U)
    (hRt : R ≤ centralizer ({t} : Set X))
    (hRn : ∀ c : X, c * t = t * c → ∀ r ∈ R, c * r * c⁻¹ ∈ R) (hRperf : ⁅R, R⁆ = R)
    [hNn : (N.subgroupOf R).Normal] [IsSimpleGroup (↥R ⧸ N.subgroupOf R)]
    (h60 : Nat.card (↥R ⧸ N.subgroupOf R) = 60) (htN : t ∈ N)
    (hN : CFSG.IsExtraspecialPGroup 2 N) :
    A5Config ⊤ (QuotientGroup.mk' (center ↥U) ⟨t, htU⟩)
        ((R.subgroupOf U).map (QuotientGroup.mk' (center ↥U)))
        ((N.subgroupOf U).map (QuotientGroup.mk' (center ↥U))) ∧
      Nat.card ((N.subgroupOf U).map (QuotientGroup.mk' (center ↥U))) = Nat.card N := by
  have hNU : N ≤ U := hNR.trans hRU
  have htc : ∀ y ∈ N, y * t = t * y := fun y hy => mem_centralizer_singleton_iff.mp (hRt (hNR hy))
  have hcen : ∀ n ∈ N, (∀ u ∈ U, u * n = n * u) → n = 1 := by
    intro n hn hnU
    rcases eq_one_or_eq_of_central_extraspecial htN hto htc hN hn
        (fun y hy => (hnU y (hNU hy)).symm) with h | h
    · exact h
    · exfalso
      obtain ⟨u, hu, hut⟩ := hnc
      exact hut (h ▸ hnU u hu)
  have hcenR : ∀ r ∈ R, (∀ u ∈ U, u * r = r * u) → r = 1 := fun r hr hrU =>
    hcen r (mem_of_mem_center_of_nonabelian hRU (exists_mul_ne_of_card_sixty h60) hr hrU) hrU
  have hinj : ∀ x y : U, (x : X) ∈ R → (y : X) ∈ R →
      QuotientGroup.mk' (center ↥U) x = QuotientGroup.mk' (center ↥U) y → x = y := by
    intro x y hx hy hxy
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxy
    have h := hcenR ((x⁻¹ * y : U) : X) (by simpa using mul_mem (inv_mem hx) hy) fun u hu =>
      congrArg Subtype.val (mem_center_iff.mp hxy ⟨u, hu⟩)
    exact inv_mul_eq_one.mp (Subtype.ext h)
  have hcardH : ∀ H : Subgroup X, H ≤ R →
      Nat.card ((H.subgroupOf U).map (QuotientGroup.mk' (center ↥U))) = Nat.card H := by
    intro H hHR
    have hψ : Function.Injective
        ((QuotientGroup.mk' (center ↥U)).comp (H.subgroupOf U).subtype) := fun x y hxy =>
      Subtype.ext (hinj _ _ (hHR (mem_subgroupOf.mp x.2)) (hHR (mem_subgroupOf.mp y.2)) hxy)
    have h1 : (H.subgroupOf U).map (QuotientGroup.mk' (center ↥U)) =
        ((QuotientGroup.mk' (center ↥U)).comp (H.subgroupOf U).subtype).range := by
      rw [MonoidHom.range_comp, range_subtype]
    rw [h1, Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv.symm]
    exact Nat.card_congr (subgroupOfEquivOfLe (hHR.trans hRU)).toEquiv
  have hRN : Nat.card R = 60 * Nat.card N := by
    rw [card_eq_card_quotient_mul_card_subgroup (N.subgroupOf R), h60,
      Nat.card_congr (subgroupOfEquivOfLe hNR).toEquiv]
  refine ⟨⟨mem_top _, orderOf_mk_center_eq_two htU hto hnc, map_mono fun x hx => hNR hx, ?_, ?_,
    ?_, (hN.1.comap_subtype (K := U)).map _, ?_, ?_, ?_, ?_, ?_, ?_⟩, hcardH N hNR⟩
  · rintro _ ⟨r, hr, rfl⟩
    refine mem_inf.mpr ⟨mem_top _, ?_⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (mem_centralizer_singleton_iff.mp (hRt hr)))
  · have hR'perf : ⁅R.subgroupOf U, R.subgroupOf U⁆ = R.subgroupOf U := by
      apply map_injective U.subtype_injective
      rw [map_commutator, subgroupOf_map_subtype, inf_of_le_left hRU, hRperf]
    rw [← map_commutator, hR'perf]
  · rintro _ ⟨r, hr, rfl⟩ _ ⟨n, hn, rfl⟩
    refine ⟨r * n * r⁻¹, ?_, by simp⟩
    have hc := hNn.conj_mem ⟨n, hNR hn⟩ (mem_subgroupOf.mpr hn) ⟨r, hr⟩
    rw [mem_subgroupOf] at hc
    change ((r * n * r⁻¹ : U) : X) ∈ N
    simpa using hc
  · rintro _ ⟨x, hx, rfl⟩ hxc
    have hx' : ∀ y ∈ N, (x : X) * y = y * x := by
      intro y hy
      have h1 := hxc (QuotientGroup.mk' (center ↥U) ⟨y, hNU hy⟩) ⟨⟨y, hNU hy⟩, hy, rfl⟩
      have h2 : QuotientGroup.mk' (center ↥U) ⁅x, ⟨y, hNU hy⟩⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact h1
      have h3 : ⁅x, (⟨y, hNU hy⟩ : U)⁆ ∈ center ↥U := (QuotientGroup.eq_one_iff _).mp h2
      have h4 : ((⁅x, (⟨y, hNU hy⟩ : U)⁆ : U) : X) = ⁅(x : X), y⁆ :=
        map_commutatorElement U.subtype _ _
      have h5 : ⁅(x : X), y⁆ ∈ N := by
        rw [commutatorElement_def]
        exact N.mul_mem (N.mul_mem (N.mul_mem hx hy) (N.inv_mem hx)) (N.inv_mem hy)
      have h6 := hcen _ h5 fun u hu => by
        rw [← h4]
        exact congrArg Subtype.val (mem_center_iff.mp h3 ⟨u, hu⟩)
      exact commutatorElement_eq_one_iff_mul_comm.mp h6
    rcases eq_one_or_eq_of_central_extraspecial htN hto htc hN hx hx' with h | h
    · left
      rw [show x = 1 from Subtype.ext h, map_one]
    · right
      rw [show x = ⟨t, htU⟩ from Subtype.ext h]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_commutatorElement]
    have h4 : ((⁅x, y⁆ : U) : X) = ⁅(x : X), (y : X)⁆ := map_commutatorElement U.subtype _ _
    rcases commutator_eq_one_or_eq_extraspecial htN hto htc hN hx hy with h | h
    · left
      rw [show ⁅x, y⁆ = 1 from Subtype.ext (h4.trans h), map_one]
    · right
      rw [show ⁅x, y⁆ = ⟨t, htU⟩ from Subtype.ext (h4.trans h)]
  · obtain ⟨x, hx, y, hy, hxy⟩ := exists_mul_ne_of_extraspecial hN
    refine ⟨_, ⟨⟨x, hNU hx⟩, hx, rfl⟩, _, ⟨⟨y, hNU hy⟩, hy, rfl⟩, fun he => hxy ?_⟩
    rw [← map_mul, ← map_mul] at he
    exact congrArg Subtype.val
      (hinj _ _ (mul_mem (hNR hx) (hNR hy)) (mul_mem (hNR hy) (hNR hx)) he)
  · intro H hNH hHR hRH
    set H₀ : Subgroup X := (H.comap (QuotientGroup.mk' (center ↥U))).map U.subtype ⊓ R with hH₀
    have hH : H = (H₀.subgroupOf U).map (QuotientGroup.mk' (center ↥U)) := by
      apply le_antisymm
      · intro h hh
        obtain ⟨r, hr, rfl⟩ := hHR hh
        exact ⟨r, mem_subgroupOf.2 (mem_inf.2 ⟨⟨r, hh, rfl⟩, hr⟩), rfl⟩
      · rintro _ ⟨x, hx, rfl⟩
        obtain ⟨⟨y, hy, hyx⟩, -⟩ := mem_inf.1 (mem_subgroupOf.1 hx)
        have hyx' : y = x := Subtype.ext hyx
        rw [← hyx']
        exact hy
    have hN₀ : N ≤ H₀ := fun n hn =>
      mem_inf.2 ⟨⟨⟨n, hNU hn⟩, hNH ⟨⟨n, hNU hn⟩, hn, rfl⟩, rfl⟩, hNR hn⟩
    have hR₀ : ∀ r ∈ R, ∀ h ∈ H₀, r * h * r⁻¹ ∈ H₀ := by
      intro r hr h hh
      obtain ⟨⟨y, hy, rfl⟩, hyR⟩ := mem_inf.1 hh
      refine mem_inf.2 ⟨⟨⟨r, hRU hr⟩ * y * ⟨r, hRU hr⟩⁻¹, ?_, rfl⟩,
        mul_mem (mul_mem hr hyR) (inv_mem hr)⟩
      rw [SetLike.mem_coe, mem_comap, map_mul, map_mul, map_inv]
      exact hRH _ ⟨⟨r, hRU hr⟩, hr, rfl⟩ _ hy
    rcases eq_or_eq_of_isSimpleGroup_quotient hN₀ inf_le_right hR₀ with h1 | h1
    · left
      rw [hH, h1]
    · right
      rw [hH, h1]
  · rw [hcardH R le_rfl, hcardH N hNR, hRN]
  · intro c hc r hr
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (center ↥U) c
    obtain ⟨r₀, hr₀, rfl⟩ := hr
    have hut : QuotientGroup.mk' (center ↥U) u * QuotientGroup.mk' (center ↥U) ⟨t, htU⟩ =
        QuotientGroup.mk' (center ↥U) ⟨t, htU⟩ * QuotientGroup.mk' (center ↥U) u :=
      mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2
    have hu2 := sq_commute_of_mk_commute htU hto hut
    refine ⟨u ^ 2 * r₀ * (u ^ 2)⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, mem_subgroupOf]
    simpa using hRn _ hu2 _ hr₀

end CFSG.LargeExtraspecial.S8
