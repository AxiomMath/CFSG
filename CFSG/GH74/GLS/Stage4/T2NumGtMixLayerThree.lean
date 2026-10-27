module

public import CFSG.GH74.GLS.Stage4.T2NumGtMixLayerShape
public import CFSG.GH74.GLS.Stage4.T2NumGtMixLayerNorm
public import CFSG.GH74.GLS.Stage4.T2P56NegStar
public import CFSG.GH74.GLS.Stage4.T2NumGtMixLayerCfg
public import CFSG.GH74.GLS.Stage4.T2P56Three

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Stage4.Hex CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Three

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem exists_J_three_mix
    (hL : SDWreathedLayer)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) (hM11 : NoM11Layer)
    (hStd : Std G)
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn' : ∃ n : ℕ, q₂ = p ^ n) (hmod' : q₁ % 4 ≠ q₂ % 4) (h3 : q₂ = 3) {N : T2N3 G} {u : G}
    (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂) (hq₁ : N.q₁ = q₁) (hq₂ : N.q₂ = q₂)
    (hSec : Ch6Sec5M N u) {y : G} (hyH : y ∈ N.H ⊓ N.K₁) (hyz : y ∉ Subgroup.zpowers N.z)
    (hyp : (orderOf y).Prime) (hyodd : Odd (orderOf y)) (hya : N.a * y * N.a⁻¹ = y) :
    ∃ J : Subgroup G, J ≤ centralizer ({y} : Set G) ∧ K₂ ≤ J ∧
      (IsSLnEps 3 ↥J 1 q₂ ∨ IsLnEps 3 ↥J 1 q₂) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hz hK₁ hK₂ hq₁ hq₂
  have hLoc : Ch6Loc5M N.toT2N2.toT2N1 u := hSec.loc
  have hLocW : Ch6Loc5W N.toT2N2.toT2N1 u := hLoc.toCh6Loc5W
  have hW := hSec.weyl
  have ctx := t2Ctx_ofW hSet hRem hLocW rfl rfl rfl rfl rfl
  have cfg := Ch6Loc5M.toMixCfg hSet hRem hLoc rfl rfl rfl rfl rfl
  have := hSet.finite₁
  have := hSet.finite₂
  obtain ⟨n, hn⟩ := hn'
  have hq₂odd : Odd N.q₂ := hSet.odd₂
  have hmod : N.q₁ % 4 ≠ N.q₂ % 4 := hmod'
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hyp
    exact Nat.not_prime_one hyp
  have hy2 : y * y ≠ 1 := by
    intro h
    have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h3 | h3
    · exact hy1 (orderOf_eq_one_iff.1 h3)
    · rw [h3] at hyodd
      exact absurd hyodd (by decide)
  have hyH' : y ∈ N.H := hyH.1
  have hyK₁ : y ∈ N.K₁ := hyH.2
  have hu : N.u = u := hSec.u_eq
  have haz : N.a⁻¹ * N.z * N.a = u := hu
  have hau : N.a⁻¹ * u * N.a = N.z * u := by
    have := hW.a_cycle
    rwa [hu] at this
  have hz2 : orderOf N.z = 2 := hLoc.z_ord
  have hzz : N.z * N.z = 1 := by
    have h := pow_orderOf_eq_one N.z
    rw [hz2, sq] at h
    exact h
  have hz1 : N.z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hu2 : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hLoc.u_ord, sq] at h
    exact h
  have hu1 : u ≠ 1 := by
    intro h
    have := hLoc.u_ord
    rw [h, orderOf_one] at this
    omega
  have hHc := hLoc.H_comm
  have hzu : N.z * u = u * N.z := hHc _ hLoc.z_mem_H u hLoc.u_mem_H
  have hay : N.a * y = y * N.a := by
    calc N.a * y = (N.a * y * N.a⁻¹) * N.a := by group
      _ = y * N.a := by rw [hya]
  have hX : centralizer ({y} : Set G) ≠ ⊤ := by
    intro htop
    have hy : y ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ centralizer ({y} : Set G) := by rw [htop]; exact Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.1 this
    have hsimple : IsSimpleGroup G := hStd.kps.1
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h0 | h0
    · rw [h0] at hy
      exact hy1 (Subgroup.mem_bot.1 hy)
    · obtain ⟨b, c, hbc⟩ := hStd.kps.2.1
      apply hbc
      have := Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top c : c ∈ Subgroup.center G) b
      exact this
  have hKX := hStd.kps.isKGroupNative_of_ne_top hX
  set X : Subgroup G := centralizer ({y} : Set G) with hXdef
  have hmemX : ∀ x : G, x * y = y * x → x ∈ X := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 hx
  have hXy : ∀ x ∈ X, x * y = y * x := fun x hx => Subgroup.mem_centralizer_singleton_iff.1 hx
  have hcomm : ∀ x ∈ N.H, x * y = y * x := fun x hx => hHc x hx y hyH'
  have hzX : N.z ∈ X := hmemX _ (hcomm _ hLoc.z_mem_H)
  have huX : u ∈ X := hmemX _ (hcomm _ hLoc.u_mem_H)
  have haX : N.a ∈ X := hmemX _ hay
  have hK₂X : N.K₂ ≤ X := fun x hx => hmemX x (hSet.comm y hyK₁ x hx).symm
  have hq₂4 : N.q₂ % 4 = 3 := by omega
  have hq₁4 : N.q₁ % 4 = 1 := by
    have hq₁odd : Odd N.q₁ := hSet.odd₁
    obtain ⟨k, hk⟩ := hq₁odd
    omega
  have hFodd₂ : Odd (Nat.card F₂) := by rw [hSet.card₂]; exact hq₂odd
  obtain ⟨e₂⟩ := hSet.iso₂
  have hshape : (N.q₂ % 4 = 3 ∧ HasSDSylow ↥X) ∨ (N.q₂ % 4 = 1 ∧ HasWreathedSylow ↥X) :=
    Or.inl ⟨hq₂4, hasSDSylow_mix cfg hq₁4 hq₂4 (fun g hg h2 => twoElt_mem_residual hg h2) hyH' hy1
      hyodd (Kj := N.K₂) (fun x hx => (hSet.comm y hyK₁ x hx).symm) hFodd₂ e₂⟩
  have hS : HasSDOrWreathedSylow ↥X := by
    rcases hshape with ⟨-, h⟩ | ⟨-, h⟩
    · exact hasSDOrWreathedSylow_iff.2 (Or.inl h)
    · exact hasSDOrWreathedSylow_iff.2 (Or.inr h)
  let z' : ↥X := ⟨N.z, hzX⟩
  have hz'2 : orderOf z' = 2 := by rw [← hz2]; exact Subgroup.orderOf_mk _ hzX
  have hzK' : z' ∈ N.K₂.subgroupOf X := hLoc.z_mem_K₂
  have hSL₂ : HasSL2Model ↥N.K₂ (fun q => q = p ^ n) :=
    ⟨F₂, inferInstance, hSet.finite₂, hSet.card₂.trans hn,
      ⟨e₂.trans (specialLinearGroupEquivStatedSL 2 F₂)⟩⟩
  have hK' := hasSL2Model_subgroupOf hK₂X hSL₂
  have hCK' : ∀ c : ↥X, c * z' = z' * c → ∀ k ∈ N.K₂.subgroupOf X, c * k * c⁻¹ ∈ N.K₂.subgroupOf X :=
    fun c hc k hk => (t2Ctx_all_normKW hSet hRem hLocW rfl rfl rfl rfl rfl (congrArg Subtype.val hc)).2
      (k : G) hk
  have hfus' : ∃ a' : ↥X, a' * z' * a'⁻¹ ≠ z' ∧ (a' * z' * a'⁻¹) * z' = z' * (a' * z' * a'⁻¹) := by
    obtain ⟨hau', haz', hazu'⟩ := cycle_facts hzz haz hau
    refine ⟨⟨N.a, haX⟩, ?_, ?_⟩
    · intro h
      have h' : N.a * N.z * N.a⁻¹ = N.z := congrArg Subtype.val h
      rw [haz'] at h'
      apply hu1
      have h5 : u * N.z = 1 * N.z := by rw [one_mul]; exact h'
      exact mul_right_cancel h5
    · apply Subtype.ext
      show (N.a * N.z * N.a⁻¹) * N.z = N.z * (N.a * N.z * N.a⁻¹)
      rw [haz']
      calc u * N.z * N.z = u * (N.z * N.z) := by group
        _ = u := by rw [hzz, mul_one]
        _ = N.z * (u * N.z) := by
            calc u = u * (N.z * N.z) := by rw [hzz, mul_one]
              _ = (u * N.z) * N.z := by group
              _ = (N.z * u) * N.z := by rw [hzu]
              _ = N.z * (u * N.z) := by group
  have hq₂pn : 3 ≤ p ^ n := by rw [← hn, h3]
  have hpn3 : p ^ n = 3 := by rw [← hn, h3]
  obtain ⟨E, hEn, hKE, hEodd, hE⟩ := layer_of_quotient hL hKX hS hp hp2 hq₂pn hz'2 hzK' hK' hCK' hfus'
  have := hEn
  have hz'2' : z' * z' = 1 := Subtype.ext (by simpa using hzz)
  have hu'2 : (⟨u, huX⟩ : ↥X) * ⟨u, huX⟩ = 1 := Subtype.ext (by simpa using hu2)
  have hw₁y : N.w₁ * y * N.w₁⁻¹ = y⁻¹ := hLoc.w₁_inv y hyH
  have hw₁y' : N.w₁ * y⁻¹ * N.w₁⁻¹ = y := by
    calc N.w₁ * y⁻¹ * N.w₁⁻¹ = (N.w₁ * y * N.w₁⁻¹)⁻¹ := by group
      _ = (y⁻¹)⁻¹ := by rw [hw₁y]
      _ = y := inv_inv y
  have hw₁iy : N.w₁⁻¹ * y * N.w₁ = y⁻¹ := by
    calc N.w₁⁻¹ * y * N.w₁ = N.w₁⁻¹ * (N.w₁ * y⁻¹ * N.w₁⁻¹) * N.w₁ := by rw [hw₁y']
      _ = y⁻¹ := by group
  have hw₁iy' : N.w₁⁻¹ * y⁻¹ * N.w₁ = y := by
    calc N.w₁⁻¹ * y⁻¹ * N.w₁ = (N.w₁⁻¹ * y * N.w₁)⁻¹ := by group
      _ = (y⁻¹)⁻¹ := by rw [hw₁iy]
      _ = y := inv_inv y
  have hw₁X : ∀ x ∈ X, N.w₁ * x * N.w₁⁻¹ ∈ X := by
    intro x hx
    apply hmemX
    have hxy : x * y⁻¹ = y⁻¹ * x := (show Commute x y from hXy x hx).inv_right.eq
    calc N.w₁ * x * N.w₁⁻¹ * y = N.w₁ * x * (N.w₁⁻¹ * y * N.w₁) * N.w₁⁻¹ := by group
      _ = N.w₁ * (x * y⁻¹) * N.w₁⁻¹ := by rw [hw₁iy]; group
      _ = N.w₁ * (y⁻¹ * x) * N.w₁⁻¹ := by rw [hxy]
      _ = (N.w₁ * y⁻¹ * N.w₁⁻¹) * (N.w₁ * x * N.w₁⁻¹) := by group
      _ = y * (N.w₁ * x * N.w₁⁻¹) := by rw [hw₁y']
  have hw₁X' : ∀ x ∈ X, N.w₁⁻¹ * x * N.w₁ ∈ X := by
    intro x hx
    apply hmemX
    have hxy : x * y⁻¹ = y⁻¹ * x := (show Commute x y from hXy x hx).inv_right.eq
    calc N.w₁⁻¹ * x * N.w₁ * y = N.w₁⁻¹ * x * (N.w₁ * y * N.w₁⁻¹) * N.w₁ := by group
      _ = N.w₁⁻¹ * (x * y⁻¹) * N.w₁ := by rw [hw₁y]; group
      _ = N.w₁⁻¹ * (y⁻¹ * x) * N.w₁ := by rw [hxy]
      _ = (N.w₁⁻¹ * y⁻¹ * N.w₁) * (N.w₁⁻¹ * x * N.w₁) := by group
      _ = y * (N.w₁⁻¹ * x * N.w₁) := by rw [hw₁iy']
  let ψ : MulAut ↥X :=
    { toFun := fun x => ⟨N.w₁ * x * N.w₁⁻¹, hw₁X x x.2⟩
      invFun := fun x => ⟨N.w₁⁻¹ * x * N.w₁, hw₁X' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hψx : ∀ x : ↥X, ((ψ x : ↥X) : G) = N.w₁ * (x : G) * N.w₁⁻¹ := fun x => rfl
  have hK'3 : HasSL2Model ↥(N.K₂.subgroupOf X) (fun q => q = 3) := by
    obtain ⟨F, iF, iFin, hF, e⟩ := hK'
    exact ⟨F, iF, iFin, hF.trans hpn3, e⟩
  have hMne : ¬ (p ^ n = 3 ∧ Nonempty (↥E ≃* CFSG.Open.StatedM11)) := by
    rintro ⟨-, hM⟩
    refine hM11 ψ E hEodd hM ?_ hKE hK'3 hzK' hz'2 ?_ ?_
    · rcases hshape with ⟨-, h⟩ | ⟨h1, -⟩
      · exact h
      · omega
    · intro k hk
      apply Subtype.ext
      rw [hψx]
      have hk' : (k : G) ∈ N.K₂ := hk
      have := hSet.comm N.w₁ hLoc.w₁_mem k hk'
      calc N.w₁ * (k : G) * N.w₁⁻¹ = (k : G) * N.w₁ * N.w₁⁻¹ := by rw [this]
        _ = k := by group
    · intro x
      apply Subtype.ext
      rw [hψx, hψx]
      show N.w₁ * (N.w₁ * (x : G) * N.w₁⁻¹) * N.w₁⁻¹ = N.z * (x : G) * N.z⁻¹
      calc N.w₁ * (N.w₁ * (x : G) * N.w₁⁻¹) * N.w₁⁻¹ = (N.w₁ * N.w₁) * (x : G) * (N.w₁ * N.w₁)⁻¹ := by
            group
        _ = N.z * (x : G) * N.z⁻¹ := by rw [hLoc.w₁_sq]
  obtain ⟨ε, hε, hEε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ IsLnEps 3 ↥E ε (p ^ n) := by
    rcases hE with h | h
    · exact h
    · exact absurd h hMne
  have hshape' : (p ^ n % 4 = 3 ∧ HasSDSylow ↥X) ∨ (p ^ n % 4 = 1 ∧ HasWreathedSylow ↥X) := by
    rw [← hn]; exact hshape
  have hε1 : ε = 1 := eps_eq_one_of_layer hp hp2 hε E hEodd hEε hshape'
  subst hε1
  have hNodd : Odd (Nat.card (pPrimeCore 2 ↥X)) := by
    have hcop := pPrimeCore_coprime_card (p := 2) (G := ↥X)
    rwa [Nat.coprime_two_left] at hcop
  have : (pPrimeCore 2 ↥X).Normal := pPrimeCore_normal
  have hloc : ∀ B : Subgroup G, (∀ b ∈ B, b * y = y * b) →
      (∀ g : G, g * y = y * g → ∀ b ∈ B, g * b * g⁻¹ ∈ B) → Odd (Nat.card B) →
        ∀ b ∈ B, b * N.z = N.z * b → b * u = u * b := by
    intro B hBy hBn hBodd
    exact star_local_neg (z := N.z) (u := u) (y := y) (K₁ := N.K₁) (K₂ := N.K₂) (H := N.H)
      (C₁ := oPrimeResidualOf 2 (centralizer ({N.z} : Set G))) hz1 hu2 hSet.comm hLoc.z_mem_K₁
      hLoc.z_mem_K₂ e₂ hFodd₂ (by rw [hSet.card₂, h3]) hHc hLoc.z_mem_H hLoc.u_mem_H hyH' hyK₁
      hLoc.H₁_cent hy2
      (fun f hf hodd x hx => (t2Ctx_odd_normK ctx hf hodd).2 x hx)
      (fun c hc x hx => ctx.C₁norm c (Subgroup.mem_centralizer_singleton_iff.2 hc) x hx)
      (ctx.SC₁ hLoc.u_mem_S) hSet.index_two B hBy hBn hBodd
  have hstar := hstar_of_local X hzX huX hXy hmemX hloc (pPrimeCore 2 ↥X) hNodd
  have hzu' : z' * (⟨u, huX⟩ : ↥X) = ⟨u, huX⟩ * z' := Subtype.ext hzu
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hmin : N.q₂.minFac = 3 := by rw [h3]; norm_num
  have hKP : ∀ P : Subgroup ↥X, P.Normal →
      P ⊔ pPrimeCore 2 ↥X = E.comap (QuotientGroup.mk' (pPrimeCore 2 ↥X)) →
        N.K₂.subgroupOf X ≤ P := by
    intro P hPn hPsup
    have huP : (⟨u, huX⟩ : ↥X) ∈ P := invol_mem_core (pPrimeCore 2 ↥X) hNodd E hEodd hPsup hu'2
    have hX₂K : N.X₂ ≤ N.K₂ := by rw [hLoc.K₂_eq]; exact le_sup_left
    have hX₂'K : N.X₂' ≤ N.K₂ := by rw [hLoc.K₂_eq]; exact le_sup_right
    have hroot : ∀ Xr : Subgroup G, Xr ≤ N.K₂ → (∀ x ∈ Xr, x ^ 3 = 1) →
        (∀ x ∈ Xr, u * x * u⁻¹ = x⁻¹) → Xr.subgroupOf X ≤ P := by
      intro Xr hXr h3' hinv x hx
      refine order_three_mem_core huP ?_ ?_
      · apply Subtype.ext
        simpa using h3' _ hx
      · apply Subtype.ext
        simpa using hinv _ hx
    have hsup : N.K₂.subgroupOf X = N.X₂.subgroupOf X ⊔ N.X₂'.subgroupOf X := by
      have := Subgroup.subgroupOf_sup (hX₂K.trans hK₂X) (hX₂'K.trans hK₂X)
      rw [← this, ← hLoc.K₂_eq]
    rw [hsup]
    exact sup_le
      (hroot N.X₂ hX₂K (fun x hx => by simpa [hmin] using hLoc.X₂_exp x hx) hLoc.u_inv_X₂)
      (hroot N.X₂' hX₂'K (fun x hx => by simpa [hmin] using hLoc.X₂'_exp x hx) hLoc.u_inv_X₂')
  have hEε3 : IsLnEps 3 ↥E 1 3 := by
    have h := hEε
    rw [hpn3] at h
    exact h
  obtain ⟨P, hKP', hP⟩ := lift_core_gen (pPrimeCore 2 ↥X) E (l3CoverAt_three hGA) hNodd hEε3
    (K := N.K₂.subgroupOf X) hKP (z := z') (u := ⟨u, huX⟩) (a := ⟨N.a, haX⟩) hz'2' hz'1 hu'2
    (fun h => hLoc.u_ne.symm (congrArg Subtype.val h)) hzu' hzK' (Subtype.ext haz) (Subtype.ext hau)
    hstar
  refine ⟨P.map X.subtype, Subgroup.map_subtype_le P, ?_, ?_⟩
  · intro x hx
    have : (⟨x, hK₂X hx⟩ : ↥X) ∈ P := hKP' (Subgroup.mem_subgroupOf.2 hx)
    exact ⟨⟨x, hK₂X hx⟩, this, rfl⟩
  · have e := Subgroup.equivMapOfInjective P X.subtype X.subtype_injective
    rw [h3]
    rcases hP with h | h
    · exact Or.inl (isSLnEps_of_equiv e h)
    · exact Or.inr (isLnEps_of_equiv e h)

end Three

end CFSG.GH74.GLS.Stage4.Rest
