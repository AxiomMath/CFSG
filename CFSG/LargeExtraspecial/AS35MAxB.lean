module

public import CFSG.LargeExtraspecial.AS35MOTwo
public import CFSG.LargeExtraspecial.AS35HSixEightA
public import CFSG.GroupTheory.ThompsonAxB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CQuotE

namespace AS35M

variable {G : Type} [Group G]

theorem commute_of_commSpace_fixed {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {σ τ : V ≃ₗ[ZMod 2] V} (hσ : ∀ v ∈ commSpace τ, σ v = v)
    (hτ : ∀ v ∈ commSpace σ, τ v = v) : σ * τ = τ * σ := by
  refine LinearEquiv.ext fun v => ?_
  have h1 := hσ _ (sub_mem_commSpace τ v)
  have h2 := hτ _ (sub_mem_commSpace σ v)
  rw [map_sub] at h1 h2
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have e1 : σ (τ v) = τ v - v + σ v := by rw [← h1]; abel
  have e2 : τ (σ v) = σ v - v + τ v := by rw [← h2]; abel
  rw [e1, e2]
  abel

theorem eq_one_of_conj_eq_mul_of_odd {c s n : G} (hcs : c * s * c⁻¹ = n * s)
    (hcn : c * n = n * c) (hco : Odd (orderOf c)) {k : ℕ} (hn : n ^ (2 ^ k) = 1) : n = 1 := by
  have hj : ∀ j : ℕ, c ^ j * s * (c ^ j)⁻¹ = n ^ j * s := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hcnj : c * n ^ j = n ^ j * c := ((Commute.pow_right hcn) j).eq
      calc c ^ (j + 1) * s * (c ^ (j + 1))⁻¹ = c * (c ^ j * s * (c ^ j)⁻¹) * c⁻¹ := by
            rw [pow_succ']; group
        _ = c * (n ^ j * s) * c⁻¹ := by rw [ih]
        _ = (c * n ^ j) * s * c⁻¹ := by group
        _ = n ^ j * (c * s * c⁻¹) := by rw [hcnj]; group
        _ = n ^ (j + 1) * s := by rw [hcs, pow_succ]; group
  have h1 := hj (orderOf c)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
  have h2 : n ^ orderOf c = 1 := by
    have := congrArg (· * s⁻¹) h1
    simp only [mul_inv_cancel, mul_inv_cancel_right] at this
    exact this.symm
  have h3 : Nat.Coprime (orderOf c) (2 ^ k) := (Nat.coprime_two_right.mpr hco).pow_right k
  have h4 : orderOf n ∣ Nat.gcd (orderOf c) (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hn)
  rw [h3, Nat.dvd_one, orderOf_eq_one_iff] at h4
  exact h4

theorem commute_of_thompson_AxB [Finite G] {Q B : Subgroup G} {c : G} (hQ : IsPGroup 2 Q)
    (hB : IsPGroup 2 B) (hcQ : c ∈ Subgroup.normalizer (Q : Set G))
    (hBQ : B ≤ Subgroup.normalizer (Q : Set G)) (hc : Odd (orderOf c))
    (hcB : ∀ b ∈ B, c * b = b * c)
    (hfix : ∀ q ∈ Q, (∀ b ∈ B, q * b = b * q) → c * q = q * c) :
    ∀ q ∈ Q, c * q = q * c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := Subgroup.zpowers c with hAdef
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := Subgroup.zpowers_le.mpr hcQ
  let α : A →* MulAut Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hAQ)
  let β : B →* MulAut Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hBQ)
  have hα : ∀ (a : A) (q : Q), ((α a q : Q) : G) = (a : G) * q * (a : G)⁻¹ := fun _ _ => rfl
  have hβ : ∀ (b : B) (q : Q), ((β b q : Q) : G) = (b : G) * q * (b : G)⁻¹ := fun _ _ => rfl
  have hA2 : ¬ 2 ∣ Nat.card A := by
    rw [hAdef, Nat.card_zpowers]
    exact Nat.odd_iff.mp hc |> fun h => by omega
  have hab : ∀ (a : A) (b : B), (a : G) * b = b * a := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (hcB b hb) k).eq
  have hcomm : ∀ a b, α a * β b = β b * α a := by
    intro a b
    ext q
    simp only [MulAut.mul_apply]
    rw [hα, hβ, hβ, hα]
    calc (a : G) * ((b : G) * q * (b : G)⁻¹) * (a : G)⁻¹
        = ((a : G) * b) * q * ((a : G) * b)⁻¹ := by group
      _ = ((b : G) * a) * q * ((b : G) * a)⁻¹ := by rw [hab a b]
      _ = (b : G) * ((a : G) * q * (a : G)⁻¹) * (b : G)⁻¹ := by group
  have hfix' : ∀ a r, (∀ b, β b r = r) → α a r = r := by
    rintro ⟨a, ha⟩ r hr
    have hrB : ∀ b ∈ B, (r : G) * b = b * r := by
      intro b hb
      have h := congrArg Subtype.val (hr ⟨b, hb⟩)
      rw [hβ] at h
      calc (r : G) * b = b * r * b⁻¹ * b := by rw [h]
        _ = b * r := by group
    have hcr := hfix r r.2 hrB
    apply Subtype.ext
    rw [hα]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have : Commute (c ^ k) (r : G) := Commute.zpow_left hcr k
    change c ^ k * r * (c ^ k)⁻¹ = r
    rw [this.eq]
    group
  have h := CFSG.GroupTheory.thompson_A_times_B hQ hA2 hB α β hcomm hfix'
  intro q hq
  have hq' := congrArg (fun φ : MulAut Q => ((φ ⟨q, hq⟩ : Q) : G))
    (h ⟨c, Subgroup.mem_zpowers c⟩)
  rw [hα] at hq'
  change c * q * c⁻¹ = ((1 : MulAut Q) ⟨q, hq⟩ : G) at hq'
  rw [MulAut.one_apply] at hq'
  calc c * q = c * q * c⁻¹ * c := by group
    _ = q * c := by rw [hq']

end AS35M

open AS35M

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem commSpace_le_fixSpace_symm {g h : S.Qt ≃ₗ[ZMod 2] S.Qt}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup S.q)
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup S.q) (hle : commSpace h ≤ fixSpace g) :
    commSpace g ≤ fixSpace h := by
  rw [← S.orthogonal_fixSpace_of_isometry hg, S.fixSpace_eq_orthogonal_commSpace_of_isometry hh]
  exact LinearMap.BilinForm.orthogonal_le hle

theorem commSpace_le_of_fixSpace_le {g h : S.Qt ≃ₗ[ZMod 2] S.Qt}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup S.q)
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup S.q) (hle : fixSpace h ≤ fixSpace g) :
    commSpace g ≤ commSpace h := by
  rw [← S.orthogonal_fixSpace_of_isometry hg, ← S.orthogonal_fixSpace_of_isometry hh]
  exact LinearMap.BilinForm.orthogonal_le hle

theorem rhoL_fix_of_cent {x c : G} (hxM : x ∈ S.M) (hx3 : x ^ 3 = 1) (hcM : c ∈ S.M)
    (hcq : ∀ q ∈ S.QG ⊓ centralizer ({x} : Set G), c * q = q * c) :
    fixSpace (S.rhoL hxM) ≤ fixSpace (S.rhoL hcM) := by
  intro v hv
  rw [← S.cqxSub_eq_fixSpace_of_pow_three hxM hx3] at hv
  obtain ⟨q, hq, hqQ, rfl⟩ := S.mem_clSub_iff.mp hv
  rw [mem_fixSpace, S.rhoL_cl hcM hqQ, hcq q hq]
  congr 1
  group

theorem commute_of_rho_commute_of_odd {x c y : G} (hc : c ∈ S.KCx x)
    (hco : Odd (orderOf c)) (hyM : y ∈ S.M) (hyx : y * x = x * y)
    (h : S.rhoL ((S.mem_KCx).mp hc).1 * S.rhoL hyM = S.rhoL hyM * S.rhoL ((S.mem_KCx).mp hc).1) :
    c * y = y * c := by
  obtain ⟨hcM, hcx, hcq⟩ := (S.mem_KCx).mp hc
  have h4 : S.ρ ⟨c, hcM⟩ * S.ρ ⟨y, hyM⟩ = S.ρ ⟨y, hyM⟩ * S.ρ ⟨c, hcM⟩ := Subtype.ext h
  set n := c * y * c⁻¹ * y⁻¹ with hn
  have hnM : n ∈ S.M := S.M.mul_mem (S.M.mul_mem (S.M.mul_mem hcM hyM) (S.M.inv_mem hcM))
    (S.M.inv_mem hyM)
  have hnQ : n ∈ S.QG := by
    rw [← S.ρ_eq_one_iff ⟨n, hnM⟩]
    change S.ρ (⟨c, hcM⟩ * ⟨y, hyM⟩ * ⟨c, hcM⟩⁻¹ * ⟨y, hyM⟩⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h4]
    group
  have hnx : n * x = x * n := by
    have hcx' : c⁻¹ * x = x * c⁻¹ := by
      calc c⁻¹ * x = c⁻¹ * (x * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * x) * c⁻¹ := by rw [hcx]
        _ = x * c⁻¹ := by group
    have hyx' : y⁻¹ * x = x * y⁻¹ := by
      calc y⁻¹ * x = y⁻¹ * (x * y) * y⁻¹ := by group
        _ = y⁻¹ * (y * x) * y⁻¹ := by rw [hyx]
        _ = x * y⁻¹ := by group
    calc n * x = c * y * c⁻¹ * (y⁻¹ * x) := by rw [hn]; group
      _ = c * y * (c⁻¹ * x) * y⁻¹ := by rw [hyx']; group
      _ = c * (y * x) * c⁻¹ * y⁻¹ := by rw [hcx']; group
      _ = (c * x) * y * c⁻¹ * y⁻¹ := by rw [hyx]; group
      _ = x * n := by rw [hcx, hn]; group
  have hcn : c * n = n * c := hcq n (mem_inf.mpr ⟨hnQ, mem_centralizer_singleton_iff.mpr hnx⟩)
  have h1 := eq_one_of_conj_eq_mul_of_odd (c := c) (s := y) (n := n) (by rw [hn]; group) hcn hco
    (k := 2) (S.pow_four_of_mem_QG hnQ)
  have h2 : c * y * c⁻¹ = y := by
    have : c * y * c⁻¹ * y⁻¹ = 1 := h1
    calc c * y * c⁻¹ = c * y * c⁻¹ * y⁻¹ * y := by group
      _ = y := by rw [this, one_mul]
  calc c * y = c * y * c⁻¹ * c := by group
    _ = y * c := by rw [h2]

section Global

variable {x s : G} (hxM : x ∈ S.M) (hx3 : x ^ 3 = 1) (hsM : s ∈ S.M)
  (hxs : x * s = s * x) (hfix : commSpace (S.rhoL hsM) ≤ fixSpace (S.rhoL hxM))

include hxM hx3 hsM hxs hfix in
theorem commute_of_odd_mem_KCx_s {c : G} (hc : c ∈ S.KCx x) (hco : Odd (orderOf c)) :
    c * s = s * c := by
  obtain ⟨hcM, hcx, hcq⟩ := (S.mem_KCx).mp hc
  have hcfix := S.rhoL_fix_of_cent hxM hx3 hcM hcq
  refine S.commute_of_rho_commute_of_odd hc hco hsM hxs.symm ?_
  refine commute_of_commSpace_fixed (fun v hv => mem_fixSpace.mp (hcfix (hfix hv)))
    (fun v hv => ?_)
  have h1 := S.commSpace_le_of_fixSpace_le (S.rhoL_mem hcM) (S.rhoL_mem hxM) hcfix hv
  exact mem_fixSpace.mp (S.commSpace_le_fixSpace_symm (S.rhoL_mem hxM) (S.rhoL_mem hsM) hfix h1)

theorem commute_of_mem_inf_QaE (hS : S.SixHyp) {h : G} (hs : s ∈ S.DSet)
    (hh : h * S.z * h⁻¹ = s) {a : G} (ha : a ∈ S.QG ⊓ S.Qa h) :
    ∀ b ∈ S.QG ⊓ centralizer ({s} : Set G), b * a = a * b := by
  obtain ⟨haQ, haQs⟩ := mem_inf.mp ha
  intro b hb
  obtain ⟨hbQ, hbs⟩ := mem_inf.mp hb
  have hbs' : b * (h * S.z * h⁻¹) = h * S.z * h⁻¹ * b := by
    rw [hh]
    exact mem_centralizer_singleton_iff.mp hbs
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ S.Qa h := by
    rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
    exact (S.Qa h).mul_mem haQs (S.conj_mem_Qa_of_commute_asc hbs' ((S.Qa h).inv_mem haQs))
  rcases S.commutator_eq_one_or_z haQ hbQ with h2 | h2
  · calc b * a = (a * b * a⁻¹ * b⁻¹)⁻¹ * (a * b) := by group
      _ = a * b := by rw [h2, inv_one, one_mul]
  · exact absurd (h2 ▸ h1) (S.z_not_mem_Qa hS.weak (hh ▸ S.ne_z_of_mem_ESet hs.1))

include hxM hx3 hsM hfix in
theorem commute_of_odd_mem_KCx_Qs_M (hS : S.SixHyp) {h : G} (hs : s ∈ S.DSet)
    (hh : h * S.z * h⁻¹ = s) {c : G} (hc : c ∈ S.KCx x) (hco : Odd (orderOf c)) {u : G}
    (hu : u ∈ S.Qa h) (huM : u ∈ S.M) (hux : u * x = x * u) : c * u = u * c := by
  obtain ⟨hcM, hcx, hcq⟩ := (S.mem_KCx).mp hc
  have hcfix := S.rhoL_fix_of_cent hxM hx3 hcM hcq
  have hxs' := S.commSpace_le_fixSpace_symm (S.rhoL_mem hxM) (S.rhoL_mem hsM) hfix
  have hufix : commSpace (S.rhoL hxM) ≤ fixSpace (S.rhoL huM) := by
    intro v hv
    rw [mem_fixSpace, ← sub_eq_zero]
    have h1 : S.rhoL huM v - v ∈ commSpace (S.rhoL hxM) := by
      obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
      rw [map_sub, S.rhoL_comm_of_commute huM hxM hux.symm w]
      exact Submodule.sub_mem _ (sub_mem_commSpace _ _) (sub_mem_commSpace _ _)
    have h2 : S.rhoL huM v - v ∈ commSpace (S.rhoL hsM) := by
      have hvs : v ∈ fixSpace (S.rhoL hsM) := hxs' hv
      rw [← (S.fiveOne_two hS.sixFour hS.weak hs hsM).2.2] at hvs
      obtain ⟨q, hq, hqQ, rfl⟩ := S.mem_clSub_iff.mp hvs
      have huq : u * q * u⁻¹ ∈ S.QG := S.conj_mem_QG huM hqQ
      have ha : u * q * u⁻¹ * q⁻¹ ∈ S.QG ⊓ S.Qa h := by
        refine mem_inf.mpr ⟨S.QG.mul_mem huq (S.QG.inv_mem hqQ), ?_⟩
        have hqs : q * (h * S.z * h⁻¹) = h * S.z * h⁻¹ * q := by
          rw [hh]
          exact mem_centralizer_singleton_iff.mp (mem_inf.mp hq).2
        rw [show u * q * u⁻¹ * q⁻¹ = u * (q * u⁻¹ * q⁻¹) by group]
        exact (S.Qa h).mul_mem hu (S.conj_mem_Qa_of_commute_asc hqs ((S.Qa h).inv_mem hu))
      have h3 := S.cl_mem_commSpace_of_commute hS.sixFour hS.weak hs hsM (mem_inf.mp ha).1
        (S.commute_of_mem_inf_QaE hS hs hh ha)
      rw [S.cl_mul huq (S.QG.inv_mem hqQ), S.cl_inv hqQ] at h3
      rw [S.rhoL_cl huM hqQ, sub_eq_add_vec (ZMod 2)]
      exact h3
    have h0 := S.commSpace_inf_fixSpace_of_pow_three hxM hx3
    rw [eq_bot_iff] at h0
    exact (Submodule.mem_bot _).mp (h0 (Submodule.mem_inf.mpr ⟨h1, hfix h2⟩))
  refine S.commute_of_rho_commute_of_odd hc hco huM hux ?_
  refine commute_of_commSpace_fixed (fun v hv => mem_fixSpace.mp (hcfix ?_))
    (fun v hv => mem_fixSpace.mp (hufix ?_))
  · exact S.commSpace_le_fixSpace_symm (S.rhoL_mem huM) (S.rhoL_mem hxM) hufix hv
  · exact S.commSpace_le_of_fixSpace_le (S.rhoL_mem hcM) (S.rhoL_mem hxM) hcfix hv

include hxM hx3 hsM hxs hfix in
theorem commute_of_odd_mem_KCx_Qs (hS : S.SixHyp) {h : G} (hs : s ∈ S.DSet)
    (hh : h * S.z * h⁻¹ = s) {c : G} (hc : c ∈ S.KCx x) (hco : Odd (orderOf c)) {u : G}
    (hu : u ∈ S.Qa h) (hux : u * x = x * u) : c * u = u * c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcM, hcx, -⟩ := (S.mem_KCx).mp hc
  have hcs := S.commute_of_odd_mem_KCx_s hxM hx3 hsM hxs hfix hc hco
  set Q' : Subgroup G := S.Qa h ⊓ centralizer ({x} : Set G) with hQ'
  have hnorm : ∀ b : G, b * s = s * b → b * x = x * b → ∀ y ∈ Q', b * y * b⁻¹ ∈ Q' := by
    intro b hbs hbx y hy
    obtain ⟨hyQ, hyx⟩ := mem_inf.mp hy
    refine mem_inf.mpr ⟨S.conj_mem_Qa_of_commute_asc (by rw [hh]; exact hbs) hyQ, ?_⟩
    rw [mem_centralizer_singleton_iff] at hyx ⊢
    have hbx' : b⁻¹ * x = x * b⁻¹ := by
      calc b⁻¹ * x = b⁻¹ * (x * b) * b⁻¹ := by group
        _ = b⁻¹ * (b * x) * b⁻¹ := by rw [hbx]
        _ = x * b⁻¹ := by group
    calc b * y * b⁻¹ * x = b * y * (b⁻¹ * x) := by group
      _ = b * (y * x) * b⁻¹ := by rw [hbx']; group
      _ = b * (x * y) * b⁻¹ := by rw [hyx]
      _ = (b * x) * y * b⁻¹ := by group
      _ = x * (b * y * b⁻¹) := by rw [hbx]; group
  have hinv : ∀ b : G, b * s = s * b → b⁻¹ * s = s * b⁻¹ := fun b hb => by
    calc b⁻¹ * s = b⁻¹ * (s * b) * b⁻¹ := by group
      _ = b⁻¹ * (b * s) * b⁻¹ := by rw [hb]
      _ = s * b⁻¹ := by group
  have hinvx : c⁻¹ * x = x * c⁻¹ := by
    calc c⁻¹ * x = c⁻¹ * (x * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * x) * c⁻¹ := by rw [hcx]
      _ = x * c⁻¹ := by group
  have hnormal : ∀ b : G, b * s = s * b → b * x = x * b →
      b ∈ Subgroup.normalizer (Q' : Set G) := by
    intro b hbs hbx
    rw [mem_normalizer_iff]
    intro y
    refine ⟨hnorm b hbs hbx y, fun hy => ?_⟩
    have hbx' : b⁻¹ * x = x * b⁻¹ := by
      calc b⁻¹ * x = b⁻¹ * (x * b) * b⁻¹ := by group
        _ = b⁻¹ * (b * x) * b⁻¹ := by rw [hbx]
        _ = x * b⁻¹ := by group
    have := hnorm b⁻¹ (hinv b hbs) hbx' _ hy
    rwa [show b⁻¹ * (b * y * b⁻¹) * b⁻¹⁻¹ = y by group] at this
  have hzs : S.z * s = s * S.z := (S.z_comm hsM).symm
  have hzx : S.z * x = x * S.z := (S.z_comm hxM).symm
  have hQ2 : IsPGroup 2 Q' := (S.conjBy h).isPGroup_QG.to_le inf_le_left
  have hB2 : IsPGroup 2 (zpowers S.z) :=
    isPGroup_zpowers_of_pow_two_pow (k := 1) (by rw [pow_one, pow_two]; exact S.z_mul_z)
  refine commute_of_thompson_AxB hQ2 hB2 (hnormal c hcs hcx)
    (zpowers_le.mpr (hnormal S.z hzs hzx)) hco ?_ ?_ u (mem_inf.mpr ⟨hu,
      mem_centralizer_singleton_iff.mpr hux⟩)
  · intro b hb
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (S.z_comm hcM) k).eq
  · intro q hq hqz
    obtain ⟨hqQ, hqx⟩ := mem_inf.mp hq
    have hqM : q ∈ S.M := S.mem_M_iff.mpr (hqz S.z (mem_zpowers _))
    exact S.commute_of_odd_mem_KCx_Qs_M hxM hx3 hsM hfix hS hs hh hc hco hqQ hqM
      (mem_centralizer_singleton_iff.mp hqx)

omit [Finite G] in
theorem mem_centralizer_EOdd {x y : G}
    (h : ∀ c ∈ S.KCx x, Odd (orderOf c) → c * y = y * c) :
    y ∈ centralizer (S.EOdd x : Set G) := by
  have hle : S.EOdd x ≤ centralizer ({y} : Set G) := by
    rw [EOdd, closure_le]
    rintro c ⟨hc, hco⟩
    exact mem_centralizer_singleton_iff.mpr (h c hc hco)
  exact mem_centralizer_iff.mpr fun e he => mem_centralizer_singleton_iff.mp (hle he)

include hxM hx3 hsM hxs hfix in
theorem exists_conj_eq_z_of_sixEightE (hS : S.SixHyp) (hs : s ∈ S.DSet) :
    (∃ c ∈ centralizer (S.EOdd x : Set G), c * S.z * c⁻¹ = s) ∧
      ∃ c ∈ centralizer (S.EOdd x : Set G), c ∉ S.M := by
  obtain ⟨h, hh⟩ := S.exists_conj_of_mem_DSet hs
  have hxc := fun a ha => S.conj_eq_of_mem_inf_Qa hS hs hh hsM hxM hx3 hfix (a := a) ha
  obtain ⟨c₂, hc₂, hc₂x, hc₂z⟩ := S.exists_Qa_conj_ne hS hs hh hx3 hxs hxc
  have hc₂E : c₂ ∈ centralizer (S.EOdd x : Set G) := S.mem_centralizer_EOdd fun c hc hco =>
    S.commute_of_odd_mem_KCx_Qs hxM hx3 hsM hxs hfix hS hs hh hc hco hc₂ hc₂x
  have hpH : c₂ * S.z * c₂⁻¹ ∈ S.zConj (S.HAt h) :=
    Asc77.conj_mem_conjIn_of_mem (le_sup_right (a := S.QG) hc₂) (Asc77.self_mem_conjIn _ _)
  obtain ⟨q, hq, hqs⟩ := S.exists_conj_eq_of_fix hS hs hh hsM hxM hx3 hxs hfix hpH hc₂z
  have hqE : q ∈ centralizer (S.EOdd x : Set G) :=
    S.mem_centralizer_EOdd fun c hc _ => ((S.mem_KCx).mp hc).2.2 q hq
  refine ⟨⟨q⁻¹ * c₂, mul_mem (inv_mem hqE) hc₂E, ?_⟩,
    ⟨c₂, hc₂E, fun hc₂M => hc₂z (S.conj_z_of_mem_M hc₂M)⟩⟩
  calc q⁻¹ * c₂ * S.z * (q⁻¹ * c₂)⁻¹ = q⁻¹ * (c₂ * S.z * c₂⁻¹) * q := by group
    _ = q⁻¹ * (q * s * q⁻¹) * q := by rw [hqs]
    _ = s := by group

end Global

end Setting

end CFSG.LargeExtraspecial
