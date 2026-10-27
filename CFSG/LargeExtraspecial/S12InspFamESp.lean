module

public import CFSG.LargeExtraspecial.S12InspFamESpCore
public import CFSG.LargeExtraspecial.S12InspFamESpOut
public import CFSG.LargeExtraspecial.S12InspFamSix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions

theorem s12_apply_apply_eq_of_commute {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {W : Submodule (ZMod 2) V} (hW : finrank (ZMod 2) W = 2)
    {x y : V ≃ₗ[ZMod 2] V} (hxW : ∀ w ∈ W, x w ∈ W) (hyW : ∀ w ∈ W, y w ∈ W)
    (hx2 : ∀ w, x (x w) = w) (hxy : ∀ w, x (y w) = y (x w))
    (hx1 : ∃ w ∈ W, x w ≠ w) (hy1 : ∃ w ∈ W, y w ≠ w) : ∀ w ∈ W, x (y w) = w := by
  have hadd : ∀ u : V, u + u = 0 := OrthoF2.vec_add_self
  obtain ⟨w₀, hw₀, hxw₀⟩ := hx1
  set p := x w₀ + w₀ with hpdef
  have hpW : p ∈ W := W.add_mem (hxW _ hw₀) hw₀
  have hp0 : p ≠ 0 := fun h => hxw₀ (by
    calc x w₀ = x w₀ + (w₀ + w₀) := by rw [hadd, add_zero]
      _ = p + w₀ := by rw [hpdef, add_assoc]
      _ = w₀ := by rw [h, zero_add])
  have hxp : x p = p := by rw [hpdef, map_add, hx2, add_comm]
  have hw₀0 : w₀ ≠ 0 := fun h => hxw₀ (by rw [h, map_zero])
  have hpw : p ≠ w₀ := fun h => by
    have : x w₀ = 0 := by
      calc x w₀ = x w₀ + (w₀ + w₀) := by rw [hadd, add_zero]
        _ = p + w₀ := by rw [hpdef, add_assoc]
        _ = 0 := by rw [h, hadd]
    exact hw₀0 (x.injective (by rw [this, map_zero]))
  have hxpw : x (p + w₀) = w₀ := by
    rw [map_add, hxp, hpdef, add_assoc, add_comm w₀, ← add_assoc, hadd, zero_add]
  have hpw' : p + w₀ = x w₀ := by
    rw [hpdef, add_assoc, hadd, add_zero]
  have henum := fun {u : V} (hu : u ∈ W) => s12_mem_of_span_pair hW hpW hw₀ hp0 hw₀0 hpw hu
  have hyp : y p = p := by
    have hfix : x (y p) = y p := by rw [hxy, hxp]
    rcases henum (hyW _ hpW) with h | h | h | h
    · exact absurd (y.injective (by rw [h, map_zero])) hp0
    · exact h
    · rw [h] at hfix
      exact absurd hfix hxw₀
    · rw [h, hxpw] at hfix
      exact absurd hfix.symm (by rw [hpw']; exact hxw₀)
  have hyw₀ : y w₀ = x w₀ := by
    rcases henum (hyW _ hw₀) with h | h | h | h
    · exact absurd (y.injective (by rw [h, map_zero])) hw₀0
    · exact absurd (y.injective (by rw [h, hyp])) hpw.symm
    · exfalso
      obtain ⟨w, hw, hyw⟩ := hy1
      apply hyw
      rcases henum hw with h' | h' | h' | h'
      · rw [h', map_zero]
      · rw [h', hyp]
      · rw [h', h]
      · rw [h', map_add, hyp, h]
    · rw [h, hpw']
  intro w hw
  rcases henum hw with h | h | h | h
  · rw [h, map_zero, map_zero]
  · rw [h, hyp, hxp]
  · rw [h, hyw₀, hx2]
  · rw [h, map_add, hyp, hyw₀, map_add, hxp, hx2]

theorem s12_mem_normalizer_comap {H K : Type*} [Group H] [Group K] (ψ : H →* K)
    {A : Subgroup K} {n : H} (hn : ψ n ∈ normalizer (A : Set K)) :
    n ∈ normalizer ((A.comap ψ : Subgroup H) : Set H) := by
  refine mem_normalizer_iff.mpr fun ℓ => ?_
  rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact mem_normalizer_iff.mp hn (ψ ℓ)

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem mul_mem_fixSub12_of_commute {t c d : S.O}
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (hct : c * t = t * c) (hdt : d * t = t * d)
    (hc2 : c * c = 1) (hcd : c * d = d * c)
    (hc : c ∉ S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)))
    (hd : d ∉ S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt))) :
    c * d ∈ S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  have h2 : ∀ {e : S.O}, e * e = 1 → ∀ w,
      (e : S.Qt ≃ₗ[ZMod 2] S.Qt) ((e : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = w :=
    fun {e} he w => by
      rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, he]
      rfl
  have hcd' : ∀ w, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) ((d : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
      (d : S.Qt ≃ₗ[ZMod 2] S.Qt) ((c : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := fun w => by
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
      hcd]
  have hne : ∀ {e : S.O}, e ∉ S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) →
      ∃ w ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt), (e : S.Qt ≃ₗ[ZMod 2] S.Qt) w ≠ w := by
    intro e he
    by_contra h
    push Not at h
    exact he h
  have key := s12_apply_apply_eq_of_commute htA.2.2.2.1
    (fun w hw => apply_mem_commSpace_of_commute hct hw)
    (fun w hw => apply_mem_commSpace_of_commute hdt hw) (h2 hc2) hcd' (hne hc) (hne hd)
  intro w hw
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
  exact key w hw

theorem s12FuseCert_of_sp {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 5 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (hS : S.S12Standing g t) {m : ℕ}
    (hm : 3 ≤ m) {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (φ : S.Xbar12 g ≃* S12InspSp.SpG b) (htX : t ∈ S.Xbar12 g) {v : Fin (2 * m) → ZMod 2}
    (hv0 : v ≠ 0) (hT : ∀ x, S12InspSp.act (φ ⟨t, htX⟩) x = x + b x v • v) :
    S.S12FuseCert g t := by
  have hXM := xbar12_eq_mbar_of_sp hS hm halt hnd φ
  have h4 : 4 < Fintype.card (Fin (2 * m)) := by rw [Fintype.card_fin]; omega
  set W := commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) with hWdef
  set T := φ ⟨t, htX⟩ with hTdef
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : S12InspSp.SpG b →* S.O,
      ψ = (S.Xbar12 g).subtype.comp φ.symm.toMonoidHom := ⟨_, rfl⟩
  have hψ : ∀ (x : S.O) (hx : x ∈ S.Xbar12 g), ψ (φ ⟨x, hx⟩) = x := fun x hx => by
    rw [hψdef]
    simp
  have hψinj : Function.Injective ψ := by
    rw [hψdef]
    exact (S.Xbar12 g).subtype_injective.comp φ.symm.injective
  have hψT : ψ T = t := hψ t htX
  have hψX : ∀ c, ψ c ∈ S.Xbar12 g := fun c => by
    rw [hψdef]
    exact (φ.symm c).2
  have hψC : ∀ c ∈ centralizer {T}, ψ c * t = t * ψ c := fun c hc => by
    rw [← hψT, ← ψ.map_mul, ← ψ.map_mul, mem_centralizer_singleton_iff.mp hc]
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup (S12InspSp.SpG b), N = (S.fixSub12 W).comap ψ := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L : Subgroup (S12InspSp.SpG b), L = (S.Lbar g).comap ψ := ⟨_, rfl⟩
  have hmemN : ∀ c, c ∈ N ↔ ψ c ∈ S.fixSub12 W := fun c => by rw [hNdef, Subgroup.mem_comap]
  have hmemL : ∀ c, c ∈ L ↔ ψ c ∈ S.Lbar g := fun c => by rw [hLdef, Subgroup.mem_comap]
  have hN : ∀ c ∈ centralizer {T}, ∀ n ∈ N, c * n * c⁻¹ ∈ N := fun c hc n hn => by
    rw [hmemN, ψ.map_mul, ψ.map_mul, ψ.map_inv]
    exact conj_mem_fixSub12 (hψC c hc) ((hmemN n).mp hn)
  have hP : ∀ c ∈ centralizer {T}, ∀ d ∈ centralizer {T}, c * c = 1 → d * d = 1 →
      c * d = d * c → c ∉ N → d ∉ N → c * d ∈ N := fun c hc d hd hc2 _ hcd hcN hdN => by
    rw [hmemN, ψ.map_mul]
    rw [hmemN] at hcN hdN
    exact mul_mem_fixSub12_of_commute htA (hψC c hc) (hψC d hd)
      (by rw [← ψ.map_mul, hc2, ψ.map_one]) (by rw [← ψ.map_mul, hcd, ψ.map_mul]) hcN hdN
  have haW : S.cl (g * S.z * g⁻¹) ∈ W := (S.timmesfeld_12_6 haQ hne ht htA).1
  have hNL : N ≤ normalizer (L : Set (S12InspSp.SpG b)) := fun n hn => by
    have hnM : ψ n ∈ S.Mbar := Xbar12_le_Mbar (hψX n)
    have hfix := (mem_fixSub12.mp ((hmemN n).mp hn)) _ haW
    have hnN := (mem_normalizer_Lbar_iff_fix haQ hne (by omega) hnM).mpr hfix
    rw [hLdef]
    exact s12_mem_normalizer_comap ψ hnN
  have hcommL : ∀ {x y : S.O}, x ∈ S.Lbar g → y ∈ S.Lbar g → x * y = y * x := fun hx hy =>
    congrArg Subtype.val ((S.isElementaryAbelian_Lbar haQ).is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
  have hLC : L ≤ centralizer {T} := fun ℓ hℓ => by
    rw [mem_centralizer_singleton_iff]
    apply hψinj
    rw [ψ.map_mul, ψ.map_mul, hψT]
    exact hcommL ((hmemL ℓ).mp hℓ) ht
  have hL2 : IsPGroup 2 L := by
    have : IsElementaryAbelian 2 (S.Lbar g) := S.isElementaryAbelian_Lbar haQ
    intro ℓ
    refine ⟨1, Subtype.ext (hψinj ?_)⟩
    have h1 : ψ (ℓ : S12InspSp.SpG b) ^ 2 = 1 := by
      simpa using elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := S.Lbar g) _
        ((hmemL ℓ).mp ℓ.2)
    simpa using h1
  have hTL : T ∈ L := by rw [hmemL, hψT]; exact ht
  have hbig : ∃ ℓ ∈ L, ℓ ≠ 1 ∧ ℓ ≠ T := by
    obtain ⟨ℓ, hℓ, hℓ1, hℓt⟩ : ∃ ℓ ∈ S.Lbar g, ℓ ≠ 1 ∧ ℓ ≠ t := by
      by_contra h
      push Not at h
      have hle : S.Lbar g ≤ zpowers t := fun ℓ hℓ => by
        by_cases h1 : ℓ = 1
        · rw [h1]
          exact one_mem _
        · rw [h ℓ hℓ h1]
          exact mem_zpowers t
      have h1 := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers] at h1
      have h2 : orderOf t ≤ 2 :=
        orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact Subtype.ext htA.2.2.1)
      have h3 := S.card_Lbar_ge haQ hne
      have h5 : 2 ^ 4 ≤ 2 ^ (S.width - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hℓX : ℓ ∈ S.Xbar12 g := hXM ▸ S.Lbar_le_Mbar g hℓ
    refine ⟨φ ⟨ℓ, hℓX⟩, by rw [hmemL, hψ]; exact hℓ, fun h => hℓ1 ?_, fun h => hℓt ?_⟩
    · have := congrArg ψ h
      rwa [hψ, ψ.map_one] at this
    · have := congrArg ψ h
      rwa [hψ, hψT] at this
  have hcore := S12InspSp.centralizer_le_normalizer_of halt hnd h4 hv0 hT hN hP hNL hLC hL2 hTL
    hbig
  intro c hcM hct
  have hcX : c ∈ S.Xbar12 g := hXM ▸ hcM
  have hct' : c * t = t * c := by
    calc c * t = c * t * c⁻¹ * c := by group
      _ = t * c := by rw [hct]
  have hcC : φ ⟨c, hcX⟩ ∈ centralizer {T} := by
    rw [mem_centralizer_singleton_iff]
    apply hψinj
    rw [ψ.map_mul, ψ.map_mul, hψ, hψT]
    exact hct'
  have hcn := hcore hcC
  rw [mem_normalizer_iff]
  intro ℓ
  constructor
  · intro hℓ
    have hℓX : ℓ ∈ S.Xbar12 g := hXM ▸ S.Lbar_le_Mbar g hℓ
    have h1 : φ ⟨ℓ, hℓX⟩ ∈ L := by rw [hmemL, hψ]; exact hℓ
    have h2 := (mem_normalizer_iff.mp hcn _).mp h1
    rwa [hmemL, ψ.map_mul, ψ.map_mul, ψ.map_inv, hψ, hψ] at h2
  · intro hℓ
    have hℓX : ℓ ∈ S.Xbar12 g := by
      have h1 : c * ℓ * c⁻¹ ∈ S.Xbar12 g := hXM ▸ S.Lbar_le_Mbar g hℓ
      have h2 : c⁻¹ * (c * ℓ * c⁻¹) * c ∈ S.Xbar12 g := mul_mem (mul_mem (inv_mem hcX) h1) hcX
      simpa [mul_assoc] using h2
    have h1 : φ ⟨c, hcX⟩ * φ ⟨ℓ, hℓX⟩ * (φ ⟨c, hcX⟩)⁻¹ ∈ L := by
      rw [hmemL, ψ.map_mul, ψ.map_mul, ψ.map_inv, hψ, hψ]
      exact hℓ
    have h2 := (mem_normalizer_iff.mp hcn _).mpr h1
    rwa [hmemL, hψ] at h2

end Setting

theorem inspSpTv3 : InspSpTv3 := by
  intro G _ _ _ S g t haQ hne hn ht htA hS hred h
  obtain ⟨hND, m, hm, b, halt, hnd, φ, hφ⟩ := h
  have hdeg : ¬ S.IsNondeg12 g := fun h' => hND (Setting.isNondeg12_iff_inspNondeg.mp h')
  have htX : t ∈ S.Xbar12 g := Setting.subset_Xbar12 (Setting.mem_Ebar12_of_mem_Lbar ht htA)
  obtain ⟨v, hv0, hvT⟩ := (hφ ⟨t, htX⟩).1 (Setting.mem_Ebar12_of_mem_Lbar ht htA)
  exact Or.inr (Or.inr (Or.inr (Or.inl
    ⟨hdeg, Setting.s12FuseCert_of_sp haQ hne hn ht htA hS hm halt hnd φ htX hv0 hvT⟩)))

end CFSG.LargeExtraspecial
