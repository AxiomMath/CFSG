module

public import CFSG.GH74.GLS.C3.Layer1.St1P41Vert
public import CFSG.GH74.GLS.C3.Layer1.St1P41Rank
public import CFSG.GH74.GLS.C3.Layer1.St1P41Lift
public import CFSG.GH74.GLS.C3.Layer1.St1P41Fus

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpElim

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.Th2
open CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.PumpVert
open CFSG.GH74.GLS.C3.Layer1.PumpLift
open CFSG.GH74.E2 (Shape2M12)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_fusion
    {x u z : G} {K K' Λ : Subgroup G} (hlt : PumpUpLT 2 x K u K') (hΛ : IsLam x u K Λ)
    (hxK' : x ∈ normalizer (K' : Set G)) (hshape : Shape2M12 ↥(bar u K'))
    (h60 : Nat.card ↥(bar u Λ) = 60) (hΛq : CFSG.IsQuasisimple ↥(bar u Λ))
    (hxY : x ∈ centralizer ({u} : Set G))
    (hne : ∃ l ∈ bar u K', sbar x hxY * l * (sbar x hxY)⁻¹ ≠ l)
    (hzK : z ∈ K) (hz2 : orderOf z = 2) (hzu : z * u = u * z) (hzx : z * x = x * z) (hzne : z ≠ x) :
    ∃ g : G, g * u = u * g ∧ g * x * g⁻¹ = z * x := by
  have hx2 : orderOf x = 2 := hlt.1.1
  set Y : Subgroup G := centralizer ({u} : Set G) with hYdef
  have hzY : z ∈ Y := mem_centralizer_singleton_iff.2 hzu
  have hz2' : z ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz2] at h
  have hzΛ : z ∈ Λ := hΛ.twoElt z ⟨hzK, hzY⟩ ⟨1, by simpa using hz2'⟩
  have hΛL : bar u Λ ≤ bar u K' := bar_le_of_stable hlt hΛ hxK'
  have hMstab := map_conj_bar_of_normalizes (u := u) (X := K') hxY hxK'
  have hN : sbar x hxY ∈ normalizer ((bar u K' : Subgroup _) : Set _) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMstab
  let σ : MulAut ↥(bar u K') := conjAut hN
  have hs2 : sbar x hxY * sbar x hxY = 1 := by
    have := pow_orderOf_eq_one (sbar x hxY)
    rwa [orderOf_sbar hx2 hxY, pow_two] at this
  have hσσ : ∀ l, σ (σ l) = l := by
    intro l
    apply Subtype.ext
    show sbar x hxY * (sbar x hxY * (l : _) * (sbar x hxY)⁻¹) * (sbar x hxY)⁻¹ = l
    calc sbar x hxY * (sbar x hxY * (l : _) * (sbar x hxY)⁻¹) * (sbar x hxY)⁻¹
        = (sbar x hxY * sbar x hxY) * (l : _) * (sbar x hxY * sbar x hxY)⁻¹ := by group
      _ = l := by rw [hs2]; group
  have hσ2 : σ * σ = 1 := by
    refine MulEquiv.ext fun l => ?_
    rw [MulAut.mul_apply, hσσ l]
    rfl
  have hσ1 : σ ≠ 1 := by
    obtain ⟨l₀, hl₀, hne'⟩ := hne
    intro h
    apply hne'
    have h1 : ((σ ⟨l₀, hl₀⟩ : ↥(bar u K')) : barQ ↥Y) = l₀ := by
      rw [h]; rfl
    exact h1
  let P : Subgroup ↥(bar u K') := (bar u Λ).subgroupOf (bar u K')
  have hPq : CFSG.IsQuasisimple ↥P :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hΛL).symm hΛq
  have hPperf : ⁅P, P⁆ = P := Subgroup.isPerfect_iff.1 hPq.1
  have hP60 : Nat.card ↥P = 60 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΛL).toEquiv).trans h60
  have hPσ : ∀ w ∈ P, σ w = w := by
    intro l hl
    apply Subtype.ext
    exact bar_lam_le_centralizer hxY hΛ (l : _) (Subgroup.mem_subgroupOf.mp hl)
  have hzbΛ : sbar z hzY ∈ bar u Λ := ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.mpr hzΛ, rfl⟩
  let zt : ↥(bar u K') := ⟨sbar z hzY, hΛL hzbΛ⟩
  have hztP : zt ∈ P := Subgroup.mem_subgroupOf.mpr hzbΛ
  have hzt2 : orderOf zt = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_sbar hz2 hzY
  obtain ⟨l₀, hl₀⟩ := exists_twisted_commutator hshape σ hσ2 hσ1 hPperf hP60 hPσ hztP hzt2
  obtain ⟨g₁, hg₁K', hg₁⟩ := Subgroup.mem_map.1 l₀.2
  have hbar : barMk ↥Y (g₁ * ⟨x, hxY⟩ * g₁⁻¹) = barMk ↥Y (⟨z, hzY⟩ * ⟨x, hxY⟩) := by
    have h1 := congrArg Subtype.val hl₀
    have h2 : (l₀ : barQ ↥Y) * (sbar x hxY * (l₀ : barQ ↥Y) * (sbar x hxY)⁻¹)⁻¹ = sbar z hzY := h1
    rw [map_mul, map_mul, map_inv, hg₁]
    show (l₀ : barQ ↥Y) * sbar x hxY * (l₀ : barQ ↥Y)⁻¹ = sbar z hzY * sbar x hxY
    calc (l₀ : barQ ↥Y) * sbar x hxY * (l₀ : barQ ↥Y)⁻¹
        = ((l₀ : barQ ↥Y) * (sbar x hxY * (l₀ : barQ ↥Y) * (sbar x hxY)⁻¹)⁻¹) * sbar x hxY := by
          group
      _ = sbar z hzY * sbar x hxY := by rw [h2]
  have hg₁K : (g₁ : G) ∈ K' := Subgroup.mem_subgroupOf.mp hg₁K'
  have hxsq : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, pow_two] at this
  have hzsq : z * z = 1 := by
    rwa [pow_two] at hz2'
  have haY : (g₁ : G) * x * (g₁ : G)⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem g₁.2 hxY) (Y.inv_mem g₁.2)
  have hbY : z * x ∈ Y := Y.mul_mem hzY hxY
  have ha2 : orderOf ((g₁ : G) * x * (g₁ : G)⁻¹) = 2 := by
    rw [PumpL42.orderOf_conj' (g₁ : G) x, hx2]
  have hb2 : orderOf (z * x) = 2 := by
    have hbb : z * x * (z * x) = 1 := by
      calc z * x * (z * x) = z * (x * z) * x := by group
        _ = z * (z * x) * x := by rw [← hzx]
        _ = (z * z) * (x * x) := by group
        _ = 1 := by rw [hzsq, hxsq, one_mul]
    refine orderOf_eq_prime (by rw [pow_two]; exact hbb) fun h1 => hzne ?_
    have h2 : z = x⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2]
    exact inv_eq_of_mul_eq_one_left hxsq
  have hab : ((g₁ : G) * x * (g₁ : G)⁻¹)⁻¹ * (z * x) ∈ pPrimeCoreOf 2 Y := by
    have h1 := (QuotientGroup.eq).1 hbar
    exact ⟨_, h1, rfl⟩
  obtain ⟨o, ho, hoab⟩ := exists_conj_of_involutions_mod_odd haY hbY ha2 hb2 hab
  have hoY : o ∈ Y := TwoThin.pPrimeCoreOf_le Y ho
  refine ⟨o * g₁, mem_centralizer_singleton_iff.1 (Y.mul_mem hoY g₁.2), ?_⟩
  calc o * (g₁ : G) * x * (o * (g₁ : G))⁻¹ = o * ((g₁ : G) * x * (g₁ : G)⁻¹) * o⁻¹ := by group
    _ = z * x := hoab

theorem vertConfig_false
    (hr4 : pRank 2 G ≤ 4) {x y : G} {K : Subgroup G} (hy2 : orderOf y = 2) (hyN : y ∈ NxK x K)
    (hV : VertConfig x y K) : False := by
  obtain ⟨Q, u, K', Λ, hQ, hyQ, huQ, hu2, hno, hlt, hΛ, hxK', h5, hKs, hshape, h60, hΛq, hxY, hne⟩ :=
    hV
  have hx2 : orderOf x = 2 := hlt.1.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hlt.1.2.2
  have hxK : IsIL2Pair x K := ⟨hx2, hK⟩
  have hL : HasL2Model (kBar K) Odd :=
    Back.hasL2Model_mono (fun q hq => by rw [hq]; exact ⟨2, rfl⟩) h5
  have hKz : Subgroup.center (kBar K) = ⊥ :=
    center_eq_bot_of_simple_quasisimple hKs (isQuasisimple_hat hK)
  have hnorm := Th2.L625.normal_of_pRank_le_four hr4 hxK hL
  have hxC : x ∈ CxK x K := Iv251.self_mem_CxK hK.1
  have hxQ : x ∈ Q :=
    Iv251.mem_of_isSylowOf_of_central hQ hxC hx2 fun c hc =>
      (mem_centralizer_singleton_iff.1 hc.1).symm
  have hQP : IsPGroup 2 ↥Q := (isSylowOf_iff.1 hQ).2.1
  have hyP : IsPGroup 2 ↥(zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy2]; norm_num)
  have hQy : IsPGroup 2 ↥(Q ⊔ zpowers y) := hQP.to_sup_of_normal_left' hyP (zpowers_le.2 hyQ)
  have hPK : Q ⊔ zpowers y ≤ normalizer (K : Set G) :=
    sup_le (fun q hq => (hQ.le hq).2.1) (zpowers_le.2 hyN.2)
  have hK2 : 2 ∣ Nat.card ↥K := by
    obtain ⟨A, -, hA⟩ := exists_isElementaryAbelian_card_pRank (H := ↥K)
    have h2 : 2 ≤ pRank 2 ↥K := Thm1.two_le_pRank_of_shape (Or.inl hL)
    have : 2 ∣ Nat.card A := by
      rw [hA]
      exact dvd_pow_self 2 (by omega)
    exact this.trans (Subgroup.card_subgroup_dvd_card A)
  obtain ⟨z, hzK, hz2, hzc⟩ := exists_involution_central hQy hPK hK2
  have hzu : z * u = u * z := hzc u ((le_sup_left : Q ≤ Q ⊔ zpowers y) huQ)
  have hzy : z * y = y * z :=
    hzc y ((le_sup_right : zpowers y ≤ Q ⊔ zpowers y) (mem_zpowers y))
  have hzx : z * x = x * z := mem_centralizer_singleton_iff.1 (hK.1 hzK)
  have hzQ : z ∉ Q := fun hzQ =>
    not_mem_pPrimeCoreOf hz2 (mem_pPrimeCoreOf_of_cSec hKz hzK (hQ.le hzQ).2)
  have hzne : z ≠ x := fun h =>
    not_mem_pPrimeCoreOf hx2 (mem_pPrimeCoreOf_of_cSec hKz (h ▸ hzK) hxC.2)
  obtain ⟨g, hgu, hgx⟩ := exists_fusion hlt hΛ hxK' hshape h60 hΛq hxY hne hzK hz2 hzu hzx hzne
  have hgu' : g⁻¹ * u * g = u := by
    calc g⁻¹ * u * g = g⁻¹ * (u * g) := by group
      _ = g⁻¹ * (g * u) := by rw [hgu]
      _ = u := by group
  have hguc : g * u * g⁻¹ = u := by
    calc g * u * g⁻¹ = (u * g) * g⁻¹ := by rw [hgu]
      _ = u := by group
  have hyx : y * x = x * y := mem_centralizer_singleton_iff.1 hyN.1
  have hywx : y * (z * x) = (z * x) * y := by
    calc y * (z * x) = (y * z) * x := by group
      _ = (z * y) * x := by rw [hzy]
      _ = z * (y * x) := by group
      _ = z * (x * y) := by rw [hyx]
      _ = (z * x) * y := by group
  have hxg : x = g⁻¹ * (z * x) * g := by
    rw [← hgx]
    group
  have hy'C : g⁻¹ * y * g ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc g⁻¹ * y * g * x = g⁻¹ * y * g * (g⁻¹ * (z * x) * g) := by rw [← hxg]
      _ = g⁻¹ * (y * (z * x)) * g := by group
      _ = g⁻¹ * ((z * x) * y) * g := by rw [hywx]
      _ = (g⁻¹ * (z * x) * g) * (g⁻¹ * y * g) := by group
      _ = x * (g⁻¹ * y * g) := by rw [← hxg]
  have hy'K : g⁻¹ * y * g ∈ normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨hnorm _ hy'C k, fun hk => ?_⟩
    have hy'C' : (g⁻¹ * y * g)⁻¹ ∈ centralizer ({x} : Set G) := inv_mem hy'C
    have := hnorm _ hy'C' _ hk
    simpa [mul_assoc] using this
  have hy'N : g⁻¹ * y * g ∈ NxK x K := ⟨hy'C, hy'K⟩
  have hy'CxK : g⁻¹ * y * g ∈ normalizer (CxK x K : Set G) := PumpL42.mem_normalizer_CxK hy'N
  set Q' : Subgroup G := Q.map (MulAut.conj g⁻¹).toMonoidHom with hQ'
  have hQ'P : IsPGroup 2 ↥Q' := hQP.of_equiv ((MulAut.conj g⁻¹).subgroupMap Q)
  have hD'P : IsPGroup 2 ↥(Q' ⊓ CxK x K) := hQ'P.to_le inf_le_left
  have hmemQ' : ∀ q ∈ Q, g⁻¹ * q * g ∈ Q' := fun q hq => ⟨q, hq, by simp⟩
  have huD : u ∈ Q' ⊓ CxK x K := ⟨hgu' ▸ hmemQ' u huQ, hQ.le huQ⟩
  have hyu : y * u * y⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hyQ u).mp huQ
  have hũ : g⁻¹ * (y * u * y⁻¹) * g ∈ Q' ⊓ CxK x K := by
    refine ⟨hmemQ' _ hyu, ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp hy'CxK u).mp (hQ.le huQ)
    have e : g⁻¹ * y * g * u * (g⁻¹ * y * g)⁻¹ = g⁻¹ * (y * u * y⁻¹) * g := by
      calc g⁻¹ * y * g * u * (g⁻¹ * y * g)⁻¹ = g⁻¹ * y * (g * u * g⁻¹) * y⁻¹ * g := by group
        _ = g⁻¹ * y * u * y⁻¹ * g := by rw [hguc]
        _ = g⁻¹ * (y * u * y⁻¹) * g := by group
    rwa [e] at h1
  have hũ2 : orderOf (g⁻¹ * (y * u * y⁻¹) * g) = 2 := by
    have h1 := PumpL42.orderOf_conj' g⁻¹ (y * u * y⁻¹)
    rw [inv_inv] at h1
    rw [h1, PumpL42.orderOf_conj' y u, hu2]
  have hũne : g⁻¹ * (y * u * y⁻¹) * g ≠ u := by
    intro h
    apply hno
    have h1 : y * u * y⁻¹ = g * u * g⁻¹ := by
      calc y * u * y⁻¹ = g * (g⁻¹ * (y * u * y⁻¹) * g) * g⁻¹ := by group
        _ = g * u * g⁻¹ := by rw [h]
    rw [hguc] at h1
    have h2 : y * u = u * y := by
      calc y * u = (y * u * y⁻¹) * y := by group
        _ = u * y := by rw [h1]
    exact h2.symm
  obtain ⟨E, hED, hEel, hE2⟩ :=
    exists_elem_two_of_two_involutions hD'P huD hũ hu2 hũ2 hũne.symm
  have hxQ' : x ∉ Q' := by
    rintro ⟨q, hq, hqx⟩
    have hqx' : q = z * x := by
      have h1 : g⁻¹ * q * g = x := by simpa [MulAut.conj_apply] using hqx
      calc q = g * (g⁻¹ * q * g) * g⁻¹ := by group
        _ = g * x * g⁻¹ := by rw [h1]
        _ = z * x := hgx
    have hzQ' : z ∈ Q := by
      have : z = q * x⁻¹ := by rw [hqx']; group
      rw [this]
      exact Q.mul_mem hq (Q.inv_mem hxQ)
    exact hzQ hzQ'
  have hxE : x ∉ E := fun h => hxQ' (hED h).1
  have h5' := pRank_add_three_le hxK hL hEel (fun e he => (hED he).2) hxE
  omega

end CFSG.GH74.GLS.C3.Layer1.PumpElim
