module

public import CFSG.GH74.GLS.Stage1.Thm4.L96C1

public section

namespace CFSG.GH74.GLS.Stage1.Thm4.L96

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3 CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm4
  CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.GLS.IVK.Lifted
open scoped commutatorElement

theorem exists_conj_in_odd_normal {C : Type*} [Group C] [Finite C] {N : Subgroup C} [N.Normal]
    (hN : Odd (Nat.card N)) {u v : C} (hu : orderOf u = 2) (hv : orderOf v = 2)
    (huv : u⁻¹ * v ∈ N) : ∃ n ∈ N, n * u * n⁻¹ = v := by
  set H := N ⊔ zpowers u with hH
  have hvH : v ∈ H := by
    have h1 : u ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
    have h2 : u⁻¹ * v ∈ H := Subgroup.mem_sup_left huv
    have := mul_mem h1 h2
    simpa using this
  have key : ∀ w ∈ H, orderOf w = 2 →
      (zpowers w).relIndex H * 2 = Nat.card H := by
    intro w hwH hw
    have := Subgroup.relIndex_mul_card (zpowers w) H
    rwa [inf_eq_left.2 ((Subgroup.zpowers_le).2 hwH), Nat.card_zpowers, hw] at this
  have huH : u ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hodd : Odd ((zpowers u).relIndex H) := by
    rw [hH, CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal N (zpowers u)]
    exact Odd.of_dvd_nat hN (Subgroup.relIndex_dvd_card _ _)
  have hsyl : ∀ w ∈ H, orderOf w = 2 → Sec4.M.Syl2In (zpowers w) H := by
    intro w hwH hw
    refine ⟨(Subgroup.zpowers_le).2 hwH, ?_, ?_⟩
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw]; norm_num)
    · have h1 := key w hwH hw
      have h2 := key u huH hu
      have h3 : (zpowers w).relIndex H = (zpowers u).relIndex H := by omega
      rw [h3]
      exact (Nat.not_even_iff_odd.2 hodd) ∘ even_iff_two_dvd.2
  obtain ⟨c, hcH, hc⟩ := Sec4.M.Syl2In.exists_conj (hsyl u huH hu) (hsyl v hvH hv)
  have hv' : v ∈ zpowers v := Subgroup.mem_zpowers v
  rw [hc, Sec4.M.mem_cj] at hv'
  have hord : orderOf (c * v * c⁻¹) = 2 := by
    have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective v
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rw [this]; exact hv
  have hcvu := eq_of_mem_zpowers_of_orderOf_two hu hv' hord
  have hc'H : c⁻¹ ∈ H := H.inv_mem hcH
  obtain ⟨y, hyN, s, hs, hys⟩ := Subgroup.mem_sup_of_normal_left.1 (hH ▸ hc'H)
  refine ⟨y, hyN, ?_⟩
  have hsu : s * u = u * s := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    exact ((Commute.refl u).zpow_left k).eq
  have hvv : v = c⁻¹ * u * c := by
    have : c * v * c⁻¹ = u := hcvu
    calc v = c⁻¹ * (c * v * c⁻¹) * c := by group
      _ = c⁻¹ * u * c := by rw [this]
  have hc_eq : c = (y * s)⁻¹ := by rw [hys, inv_inv]
  calc y * u * y⁻¹ = y * (s * u * s⁻¹) * y⁻¹ := by rw [hsu]; group
    _ = (y * s) * u * (y * s)⁻¹ := by group
    _ = c⁻¹ * u * c := by rw [hys, hc_eq, mul_inv_rev]; group
    _ = v := hvv.symm

open Equiv Equiv.Perm

section ThetaAll

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {z t : G} {S K : Subgroup G}
  {h : Ctx98 G Lh z t S K} {n : ℕ}

@[expose] noncomputable def ThetaAll (A : Act h n) {g : G} (hg : g * z * g⁻¹ = t) :
    ↥(Cz t) →* Equiv.Perm (Fin n) := A.ρ.comp (conjC hg)

@[expose] def Ot (g z : G) : Subgroup G := (Oz z).map (MulAut.conj g).toMonoidHom

omit [Finite G] in
theorem mem_Ot_iff {g : G} {o : G} : o ∈ Ot g z ↔ g⁻¹ * o * g ∈ Oz z := by
  constructor
  · rintro ⟨x, hx, hxo⟩
    have e : o = g * x * g⁻¹ := by rw [← hxo]; simp [MulAut.conj_apply]
    have e2 : g⁻¹ * o * g = x := by rw [e]; group
    rw [e2]
    exact hx
  · intro ho
    exact ⟨g⁻¹ * o * g, ho, by simp [MulAut.conj_apply]; group⟩

omit [Finite G] in
theorem Ot_le_Cz {g : G} (hg : g * z * g⁻¹ = t) : Ot g z ≤ Cz t := by
  intro o ho
  have ho' := (mem_Ot_iff).1 ho
  have hc : (g⁻¹ * o * g) ∈ Cz z := by
    obtain ⟨y, hy, hyc⟩ := ho'
    have : y.1 = g⁻¹ * o * g := hyc
    rw [← this]
    exact y.2
  rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
  have hz : z = g⁻¹ * t * g := by rw [← hg]; group
  calc o * t = g * (g⁻¹ * o * g * z) * g⁻¹ := by rw [← hg]; group
    _ = g * (z * (g⁻¹ * o * g)) * g⁻¹ := by rw [hc]
    _ = t * o := by rw [← hg]; group

omit [Finite G] in
theorem Ot_conj {g : G} (hg : g * z * g⁻¹ = t) {y : G} (hy : y ∈ Cz t) {o : G} (ho : o ∈ Ot g z) :
    y * o * y⁻¹ ∈ Ot g z := by
  rw [mem_Ot_iff] at ho ⊢
  have hyz : g⁻¹ * y * g ∈ Cz z := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    have hz : z = g⁻¹ * t * g := by rw [← hg]; group
    calc g⁻¹ * y * g * z = g⁻¹ * (y * t) * g := by rw [hz]; group
      _ = g⁻¹ * (t * y) * g := by rw [hy]
      _ = z * (g⁻¹ * y * g) := by rw [hz]; group
  have := Oz_conj hyz ho
  have e : g⁻¹ * y * g * (g⁻¹ * o * g) * (g⁻¹ * y * g)⁻¹ = g⁻¹ * (y * o * y⁻¹) * g := by group
  rwa [e] at this

theorem card_Ot_odd (g z : G) : Odd (Nat.card (Ot g z)) := by
  have h1 : Nat.card (Ot g z) = Nat.card (Oz z) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  rw [h1]
  exact (Nat.coprime_two_left).1 card_Oz_coprime

end ThetaAll

section Ker

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {z t : G} {S K : Subgroup G}
  {h : Ctx98 G Lh z t S K} {n : ℕ}

theorem Ot_subgroupOf_odd {g : G} (hg : g * z * g⁻¹ = t) :
    Odd (Nat.card ((Ot g z).subgroupOf (Cz t))) := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Ot_le_Cz hg)).toEquiv]
  exact card_Ot_odd g z

theorem ThetaAll_ker_mem (A : Act h n) {g : G} (hg : g * z * g⁻¹ = t) {k : ↥(Cz t)}
    (hk : ThetaAll A hg k = 1) :
    k ∈ (zpowers t).subgroupOf (Cz t) ⊔ (Ot g z).subgroupOf (Cz t) := by
  classical
  have htC : t ∈ Cz t := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have h1 := A.ker_ρ (conjC hg k) hk
  have e1 : ((zpowers t).subgroupOf (Cz t) ⊔ (Ot g z).subgroupOf (Cz t)).map (Cz t).subtype =
      zpowers t ⊔ Ot g z := by
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 ((Subgroup.zpowers_le).2 htC), inf_eq_left.2 (Ot_le_Cz hg)]
  have h2 : (k : G) ∈ zpowers t ⊔ Ot g z := by
    have h3 : (k : G) ∈ (zpowers z ⊔ Oz z).map (MulAut.conj g).toMonoidHom := by
      refine ⟨g⁻¹ * (k : G) * g, ?_, ?_⟩
      · rw [← conjC_coe hg k]; exact h1
      · simp [MulAut.conj_apply]; group
    rw [Subgroup.map_sup, MonoidHom.map_zpowers] at h3
    have e2 : (MulAut.conj g).toMonoidHom z = t := by simp [MulAut.conj_apply, hg]
    rw [e2] at h3
    exact h3
  have h4 : (k : G) ∈ ((zpowers t).subgroupOf (Cz t) ⊔ (Ot g z).subgroupOf (Cz t)).map
      (Cz t).subtype := by
    rw [e1]; exact h2
  obtain ⟨y', hy', hy'c⟩ := h4
  have : y' = k := Subtype.ext hy'c
  rwa [this] at hy'

end Ker

section Main

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {z t : G} {S K : Subgroup G}
  {h : Ctx98 G Lh z t S K} {n : ℕ}

theorem ThetaAll_conj_mem (A : Act h n) {g : G} (hg : g * z * g⁻¹ = t)
    (hsurj : Function.Surjective A.ρ) {x : Equiv.Perm (Fin n)}
    (hx : Commute x (ThetaAll A hg ⟨z, z_mem_Cz_t h⟩)) {d : ↥(Cz t)} (hd : (d : G) ∈ Cz z) :
    ∃ d' : ↥(Cz t), (d' : G) ∈ Cz z ∧ x * ThetaAll A hg d * x⁻¹ = ThetaAll A hg d' := by
  classical
  obtain ⟨c, hc⟩ := hsurj x
  have hgcg : g * (c : G) * g⁻¹ ∈ Cz t := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcz : (c : G) * z = z * (c : G) := Subgroup.mem_centralizer_singleton_iff.1 c.2
    calc g * (c : G) * g⁻¹ * t = g * ((c : G) * z) * g⁻¹ := by rw [← hg]; group
      _ = g * (z * (c : G)) * g⁻¹ := by rw [hcz]
      _ = t * (g * (c : G) * g⁻¹) := by rw [← hg]; group
  set y : ↥(Cz t) := ⟨g * (c : G) * g⁻¹, hgcg⟩ with hy
  have hΘy : ThetaAll A hg y = x := by
    have : conjC hg y = c := Subtype.ext (by
      rw [conjC_coe]; show g⁻¹ * (g * (c : G) * g⁻¹) * g = c; group)
    show A.ρ (conjC hg y) = x
    rw [this, hc]
  set zC : ↥(Cz t) := ⟨z, z_mem_Cz_t h⟩ with hzC
  have htC : t ∈ Cz t := Subgroup.mem_centralizer_singleton_iff.2 rfl
  set tC : ↥(Cz t) := ⟨t, htC⟩ with htCdef
  have hΘz : ThetaAll A hg zC = ThetaAll A hg zC := rfl
  set N : Subgroup ↥(Cz t) := (Ot g z).subgroupOf (Cz t) with hN
  have hNnorm : N.Normal := by
    refine ⟨fun m hm y' => ?_⟩
    have hm' : (m : G) ∈ Ot g z := hm
    show ((y' * m * y'⁻¹ : ↥(Cz t)) : G) ∈ Ot g z
    simpa using Ot_conj hg y'.2 hm'
  have hNodd : Odd (Nat.card N) := by
    rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Ot_le_Cz hg)).toEquiv]
    exact card_Ot_odd g z
  have hTcent : ∀ τ ∈ (zpowers t).subgroupOf (Cz t), ∀ c' : ↥(Cz t), c' * τ = τ * c' := by
    intro τ hτ c'
    have hτ' : (τ : G) ∈ zpowers t := hτ
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hτ'
    apply Subtype.ext
    have hct : (c' : G) * t = t * (c' : G) := Subgroup.mem_centralizer_singleton_iff.1 c'.2
    have : (c' : G) * t ^ j = t ^ j * (c' : G) := ((Commute.zpow_right (show Commute (c' : G) t from hct) j).eq)
    simp only [Subgroup.coe_mul]
    rw [← hj]
    exact this
  set kC : ↥(Cz t) := y * zC * y⁻¹ * zC⁻¹ with hkC
  have hΘk : ThetaAll A hg kC = 1 := by
    rw [hkC, map_mul, map_mul, map_mul, map_inv, map_inv, hΘy]
    have := hx.eq
    calc x * ThetaAll A hg zC * x⁻¹ * (ThetaAll A hg zC)⁻¹ = (ThetaAll A hg zC * x) * x⁻¹ * (ThetaAll A hg zC)⁻¹ := by
          rw [this]
      _ = 1 := by group
  have hkmem : kC ∈ (zpowers t).subgroupOf (Cz t) ⊔ N := by
    have h1 := A.ker_ρ (conjC hg kC) hΘk
    have e1 : ((zpowers t).subgroupOf (Cz t) ⊔ N).map (Cz t).subtype = zpowers t ⊔ Ot g z := by
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.2 ((Subgroup.zpowers_le).2 htC), inf_eq_left.2 (Ot_le_Cz hg)]
    have h2 : (kC : G) ∈ zpowers t ⊔ Ot g z := by
      have h3 : (kC : G) ∈ (zpowers z ⊔ Oz z).map (MulAut.conj g).toMonoidHom := by
        refine ⟨g⁻¹ * (kC : G) * g, ?_, ?_⟩
        · rw [← conjC_coe hg kC]; exact h1
        · simp [MulAut.conj_apply]; group
      rw [Subgroup.map_sup, MonoidHom.map_zpowers] at h3
      have e2 : (MulAut.conj g).toMonoidHom z = t := by simp [MulAut.conj_apply, hg]
      rw [e2] at h3
      exact h3
    have h4 : (kC : G) ∈ ((zpowers t).subgroupOf (Cz t) ⊔ N).map (Cz t).subtype := by
      rw [e1]; exact h2
    obtain ⟨y', hy', hy'c⟩ := h4
    have : y' = kC := Subtype.ext hy'c
    rwa [this] at hy'
  have := hNnorm
  obtain ⟨τ, hτ, o, ho, hτo⟩ := (Subgroup.mem_sup_of_normal_right
    (s := (zpowers t).subgroupOf (Cz t)) (t := N)).1 hkmem
  have hτc := hTcent τ hτ
  set d₁ : ↥(Cz t) := y * d * y⁻¹ with hd₁
  have hdz : d * zC = zC * d := Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hd)
  have hw : d₁ * (y * zC * y⁻¹) = (y * zC * y⁻¹) * d₁ := by
    calc d₁ * (y * zC * y⁻¹) = y * (d * zC) * y⁻¹ := by rw [hd₁]; group
      _ = y * (zC * d) * y⁻¹ := by rw [hdz]
      _ = (y * zC * y⁻¹) * d₁ := by rw [hd₁]; group
  have hkz : y * zC * y⁻¹ = kC * zC := by rw [hkC]; group
  have e1 : d₁ * (τ * o * zC) * d₁⁻¹ = τ * o * zC := by
    have h1 : d₁ * (kC * zC) = (kC * zC) * d₁ := by rw [← hkz]; exact hw
    rw [hτo]
    calc d₁ * (kC * zC) * d₁⁻¹ = (kC * zC) * d₁ * d₁⁻¹ := by rw [h1]
      _ = kC * zC := by group
  have hdτ : d₁ * τ * d₁⁻¹ = τ := by rw [hτc d₁]; group
  have e2 : (d₁ * τ * d₁⁻¹) * (d₁ * o * d₁⁻¹) * (d₁ * zC * d₁⁻¹) = τ * o * zC := by
    rw [← e1]; group
  rw [hdτ] at e2
  have e3 : (d₁ * o * d₁⁻¹) * (d₁ * zC * d₁⁻¹) = o * zC := by
    have := e2
    rw [mul_assoc] at this
    exact mul_left_cancel (a := τ) (by rw [← mul_assoc] at this ⊢; simpa [mul_assoc] using this)
  have hv : d₁ * zC * d₁⁻¹ = ((d₁ * o * d₁⁻¹)⁻¹ * o) * zC := by
    calc d₁ * zC * d₁⁻¹ = (d₁ * o * d₁⁻¹)⁻¹ * ((d₁ * o * d₁⁻¹) * (d₁ * zC * d₁⁻¹)) := by group
      _ = ((d₁ * o * d₁⁻¹)⁻¹ * o) * zC := by rw [e3]; group
  have hc₁N : (d₁ * o * d₁⁻¹)⁻¹ * o ∈ N :=
    N.mul_mem (N.inv_mem (hNnorm.conj_mem o ho d₁)) ho
  have hu : orderOf zC = 2 := by
    rw [hzC, Subgroup.orderOf_mk]; exact h.z_ord
  have hvo : orderOf (d₁ * zC * d₁⁻¹) = 2 := by
    have := orderOf_injective (MulAut.conj d₁).toMonoidHom (MulAut.conj d₁).injective zC
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rw [this]; exact hu
  have huv : zC⁻¹ * (d₁ * zC * d₁⁻¹) ∈ N := by
    rw [hv]
    have := hNnorm.conj_mem _ hc₁N zC⁻¹
    simpa [mul_assoc] using this
  obtain ⟨nn, hnnN, hnn⟩ := exists_conj_in_odd_normal hNodd hu hvo huv
  set d₂ : ↥(Cz t) := nn⁻¹ * d₁ with hd₂
  have hd₂z : d₂ * zC = zC * d₂ := by
    have h1 : zC = nn⁻¹ * (d₁ * zC * d₁⁻¹) * nn := by rw [← hnn]; group
    calc d₂ * zC = nn⁻¹ * d₁ * zC := rfl
      _ = nn⁻¹ * (d₁ * zC * d₁⁻¹) * d₁ := by group
      _ = nn⁻¹ * (d₁ * zC * d₁⁻¹) * nn * (nn⁻¹ * d₁) := by group
      _ = zC * d₂ := by rw [← h1]
  have hΘnn : ThetaAll A hg nn = 1 := by
    have hnnO : (nn : G) ∈ Ot g z := hnnN
    have h1 := (mem_Ot_iff).1 hnnO
    exact A.ρ_Oz (conjC hg nn) (by rw [conjC_coe]; exact h1)
  refine ⟨d₂, ?_, ?_⟩
  · have := congrArg Subtype.val hd₂z
    exact Subgroup.mem_centralizer_singleton_iff.2 this
  · have hd₁eq : d₁ = nn * d₂ := by rw [hd₂]; group
    calc x * ThetaAll A hg d * x⁻¹ = ThetaAll A hg y * ThetaAll A hg d * (ThetaAll A hg y)⁻¹ := by rw [hΘy]
      _ = ThetaAll A hg d₁ := by rw [hd₁, map_mul, map_mul, map_inv]
      _ = ThetaAll A hg d₂ := by rw [hd₁eq, map_mul, hΘnn, one_mul]

end Main

end CFSG.GH74.GLS.Stage1.Thm4.L96
