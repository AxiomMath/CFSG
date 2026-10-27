module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Subgroup

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]

theorem nu_coe_pow (g : V ≃ₗ[ZMod 2] V) (n : ℕ) :
    ((g ^ n : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = (g : V →ₗ[ZMod 2] V) ^ n := by
  exact map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom : (V ≃ₗ[ZMod 2] V) →* _) g n

theorem pow_eq_one_of_two_pow (g : V ≃ₗ[ZMod 2] V) {k m : ℕ} (hg : g ^ (2 ^ k) = 1)
    (hm : finrank (ZMod 2) V ≤ 2 ^ m) : g ^ (2 ^ m) = 1 := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact Subsingleton.elim _ _
  haveI : CharP (Module.End (ZMod 2) V) 2 := by
    haveI : Nontrivial (Module.End (ZMod 2) V) := inferInstance
    exact charP_of_injective_algebraMap (algebraMap (ZMod 2) (Module.End (ZMod 2) V)).injective 2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set G : Module.End (ZMod 2) V := (g : V →ₗ[ZMod 2] V) with hG
  set N : Module.End (ZMod 2) V := G - 1 with hN
  have hGp : ∀ n : ℕ, ((g ^ n : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = G ^ n := nu_coe_pow g
  have hGk : G ^ (2 ^ k) = 1 := by
    have h1 := hGp (2 ^ k)
    rw [hg] at h1
    exact (by simpa using h1.symm : G ^ (2 ^ k) = LinearMap.id)
  have hNk : N ^ (2 ^ k) = 0 := by
    have := sub_pow_char_pow_of_commute (R := Module.End (ZMod 2) V) (p := 2) (n := k)
      (x := G) (y := 1) (Commute.one_right G)
    rw [hN, this, hGk, one_pow, sub_self]
  have hnil : IsNilpotent N := ⟨2 ^ k, hNk⟩
  have hch := IsNilpotent.charpoly_eq_X_pow_finrank hnil
  have hN0 : N ^ finrank (ZMod 2) V = 0 := by
    have := LinearMap.aeval_self_charpoly N
    rw [hch] at this
    simpa using this
  have hNm : N ^ (2 ^ m) = 0 := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hm
    rw [hd, pow_add, hN0, zero_mul]
  have h2 : G ^ (2 ^ m) = 1 := by
    have := sub_pow_char_pow_of_commute (R := Module.End (ZMod 2) V) (p := 2) (n := m)
      (x := G) (y := 1) (Commute.one_right G)
    rw [← hN, hNm, one_pow] at this
    exact (sub_eq_zero.mp this.symm)
  apply LinearEquiv.toLinearMap_injective
  rw [hGp (2 ^ m)]
  exact h2


theorem add_self_eq_zero' (w : V) : w + w = 0 := by
  have : (2 : ZMod 2) = 0 := by decide
  calc w + w = (2 : ZMod 2) • w := by rw [two_smul]
    _ = 0 := by rw [this, zero_smul]

theorem neg_eq_self' (w : V) : -w = w := by
  have h := add_self_eq_zero' w
  exact neg_eq_of_add_eq_zero_right h

theorem nu_apply (g : V ≃ₗ[ZMod 2] V) (v : V) : nu g v = g v - v := by
  simp [nu]

theorem nu_nu_of_sq (g : V ≃ₗ[ZMod 2] V) (hg : g * g = 1) (v : V) : nu g (nu g v) = 0 := by
  have h2 : g (g v) = v := by
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) hg
    simpa using this
  rw [nu_apply, nu_apply, map_sub, h2]
  have e1 : ∀ a b : V, a - b = a + b := fun a b => by rw [sub_eq_add_neg, neg_eq_self']
  rw [e1, e1, e1]
  calc v + g v + (g v + v) = (v + v) + (g v + g v) := by abel
    _ = 0 := by rw [add_self_eq_zero', add_self_eq_zero', add_zero]

theorem range_nu_le_fixSp (g : V ≃ₗ[ZMod 2] V) (hg : g * g = 1) :
    LinearMap.range (nu g) ≤ fixSp g := by
  rintro _ ⟨v, rfl⟩
  exact nu_nu_of_sq g hg v

theorem two_mul_rk_le (g : V ≃ₗ[ZMod 2] V) (hg : g * g = 1) :
    2 * rk g ≤ finrank (ZMod 2) V := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (nu g)
  have h2 : finrank (ZMod 2) (LinearMap.range (nu g)) ≤ finrank (ZMod 2) (fixSp g) :=
    Submodule.finrank_mono (range_nu_le_fixSp g hg)
  unfold rk
  unfold fixSp at h2
  omega


theorem rk_conj (g h : V ≃ₗ[ZMod 2] V) : rk (h * g * h⁻¹) = rk g := by
  have hr : LinearMap.range (nu (h * g * h⁻¹)) =
      (LinearMap.range (nu g)).map (h : V →ₗ[ZMod 2] V) := by
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨nu g (h⁻¹ v), ⟨_, rfl⟩, ?_⟩
      simp [nu_apply]
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      refine ⟨h v, ?_⟩
      simp [nu_apply]
  unfold rk
  rw [hr]
  exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ h.injective _).symm


theorem four_dvd_of_five_dvd_two_pow_sub_one {d : ℕ} (h : 5 ∣ 2 ^ d - 1) : 4 ∣ d := by
  have hpos : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  have h1 : 2 ^ d % 5 = 1 := by omega
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ d = 4 * q + r := ⟨d / 4, d % 4, by omega, by omega⟩
  have h2 : 2 ^ (4 * q + r) % 5 = 2 ^ r % 5 := by
    rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  rw [h2] at h1
  interval_cases r <;> simp_all <;> omega

theorem four_dvd_finrank_of_stable {x : V ≃ₗ[ZMod 2] V} (hx : x ^ 5 = 1)
    {U : Submodule (ZMod 2) V} (hU : Stable x U) (hfix : ∀ u ∈ U, x u = u → u = 0) :
    4 ∣ finrank (ZMod 2) U := by
  classical
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let S : Type _ := {v : V // v ∈ U ∧ v ≠ 0}
  haveI : Finite S := inferInstance
  haveI : Fintype S := Fintype.ofFinite S
  haveI : Fintype U := Fintype.ofFinite U
  let f : Function.End S := fun s => ⟨x s, hU _ s.2.1, fun h0 => s.2.2 (by
    have := congrArg (fun w => x⁻¹ w) h0
    simpa using this)⟩
  have hiter : ∀ (n : ℕ) (s : S), ((f^[n] s : S) : V) = (x ^ n) (s : V) := by
    intro n
    induction n with
    | zero => intro s; rw [Function.iterate_zero_apply, pow_zero]; rfl
    | succ n ih =>
      intro s
      rw [Function.iterate_succ_apply', pow_succ']
      simp [f, ih]
  have hf5 : f ^ (5 ^ 1) = 1 := by
    funext s
    apply Subtype.ext
    have : ((f ^ (5 ^ 1)) s : V) = (x ^ (5 ^ 1)) (s : V) := hiter (5 ^ 1) s
    rw [this, pow_one, hx]
    simp [Function.End.one_def]
  have hfix' : ∀ s : S, ¬ s ∈ f.fixedPoints := by
    intro s h
    have h1 : x (s : V) = s := congrArg Subtype.val h
    exact s.2.2 (hfix _ s.2.1 h1)
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := S) (f := f) (p := 5) (n := 1) hf5
  have hcard0 : Fintype.card f.fixedPoints = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨s, hs⟩ => hfix' s hs⟩
  rw [hcard0] at hmod
  have hS : Fintype.card S = 2 ^ finrank (ZMod 2) U - 1 := by
    have e : S ≃ {u : U // u ≠ 0} :=
      { toFun := fun s => ⟨⟨s.1, s.2.1⟩, fun h => s.2.2 (by simpa using congrArg Subtype.val h)⟩
        invFun := fun u => ⟨u.1.1, u.1.2, fun h => u.2 (Subtype.ext h)⟩
        left_inv := fun s => rfl
        right_inv := fun u => rfl }
    rw [Fintype.card_congr e]
    have h1 : Fintype.card {u : U // u ≠ 0} = Fintype.card U - 1 := by
      have := Fintype.card_subtype_compl (fun u : U => u = 0)
      simp only [Fintype.card_subtype_eq] at this
      simpa using this
    have h2 : Fintype.card U = 2 ^ finrank (ZMod 2) U := by
      have := Module.card_eq_pow_finrank (K := ZMod 2) (V := U)
      simpa using this
    rw [h1, h2]
  rw [hS] at hmod
  apply four_dvd_of_five_dvd_two_pow_sub_one
  exact (Nat.modEq_zero_iff_dvd.mp hmod)


theorem exists_stable_complement (O : Subgroup (V ≃ₗ[ZMod 2] V)) (hodd : Odd (Nat.card O))
    (U : Submodule (ZMod 2) V) (hU : ∀ g ∈ O, Stable g U) :
    ∃ U' : Submodule (ZMod 2) V, IsCompl U U' ∧ ∀ g ∈ O, Stable g U' := by
  classical
  haveI : Finite O := Nat.finite_of_card_ne_zero (by obtain ⟨k, hk⟩ := hodd; omega)
  haveI : Fintype O := Fintype.ofFinite O
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl U
  let π : V →ₗ[ZMod 2] V := U.subtype ∘ₗ Submodule.linearProjOfIsCompl U q hq
  have hπU : ∀ v, π v ∈ U := fun v => (Submodule.linearProjOfIsCompl U q hq v).2
  have hπfix : ∀ u ∈ U, π u = u := fun u hu => by
    have h1 : (U.linearProjOfIsCompl q hq) u = ⟨u, hu⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hq ⟨u, hu⟩
    simp [π, h1]
  let π' : V →ₗ[ZMod 2] V :=
    ∑ g : O, ((g : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) ∘ₗ π ∘ₗ
      (((g : V ≃ₗ[ZMod 2] V)⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V)
  have hπ'v : ∀ v, π' v = ∑ g : O, (g : V ≃ₗ[ZMod 2] V) (π ((g : V ≃ₗ[ZMod 2] V)⁻¹ v)) := by
    intro v
    simp [π', LinearMap.sum_apply]
  have hπ'U : ∀ v, π' v ∈ U := by
    intro v
    rw [hπ'v]
    exact Submodule.sum_mem _ fun g _ => hU g g.2 _ (hπU _)
  have hOcard : ((Nat.card O : ℕ) : ZMod 2) = 1 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk]
    push_cast
    have : (2 : ZMod 2) = 0 := by decide
    rw [this, zero_mul, zero_add]
  have hπ'fix : ∀ u ∈ U, π' u = u := by
    intro u hu
    rw [hπ'v]
    have : ∀ g : O, (g : V ≃ₗ[ZMod 2] V) (π ((g : V ≃ₗ[ZMod 2] V)⁻¹ u)) = u := by
      intro g
      rw [hπfix _ (hU _ (inv_mem g.2) u hu)]
      simp
    simp only [this, Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul (ZMod 2), hOcard, one_smul]
  have hequiv : ∀ h ∈ O, ∀ v, π' (h v) = h (π' v) := by
    intro h hh v
    rw [hπ'v, hπ'v, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨h⁻¹, inv_mem hh⟩ : O)) _ _ ?_
    intro g
    simp [mul_assoc]
  refine ⟨LinearMap.ker π', ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [Submodule.disjoint_def]
      intro v hv hv'
      have h1 : π' v = 0 := hv'
      rw [← hπ'fix v hv, h1]
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have h1 : π' (v - π' v) = 0 := by
        rw [map_sub, hπ'fix _ (hπ'U v), sub_self]
      have : v = π' v + (v - π' v) := by abel
      rw [this]
      exact Submodule.add_mem_sup (hπ'U v) h1
  · intro g hg v hv
    have h1 : π' v = 0 := hv
    show π' (g v) = 0
    rw [hequiv g hg, h1, map_zero]


theorem isCompl_fixSp_range_nu (g : V ≃ₗ[ZMod 2] V) (hg : Odd (orderOf g)) :
    IsCompl (fixSp g) (LinearMap.range (nu g)) := by
  classical
  set n := orderOf g with hn
  have hgn : g ^ n = 1 := pow_orderOf_eq_one g
  let e : V → V := fun v => ∑ i ∈ Finset.range n, (g ^ i) v
  have hnodd : ((n : ℕ) : ZMod 2) = 1 := by
    obtain ⟨k, hk⟩ := hg
    rw [hk]
    push_cast
    have : (2 : ZMod 2) = 0 := by decide
    rw [this, zero_mul, zero_add]
  have hge : ∀ v, g (e v) = e v := by
    intro v
    have h1 : ∑ i ∈ Finset.range (n + 1), (g ^ i) v =
        ∑ i ∈ Finset.range n, (g ^ (i + 1)) v + v := by
      rw [Finset.sum_range_succ']
      simp
    have h2 : ∑ i ∈ Finset.range (n + 1), (g ^ i) v = ∑ i ∈ Finset.range n, (g ^ i) v + v := by
      rw [Finset.sum_range_succ, hgn]
      simp
    have h3 : ∑ i ∈ Finset.range n, (g ^ (i + 1)) v = ∑ i ∈ Finset.range n, (g ^ i) v :=
      add_right_cancel (h1.symm.trans h2)
    show g (∑ i ∈ Finset.range n, (g ^ i) v) = ∑ i ∈ Finset.range n, (g ^ i) v
    rw [map_sum, ← h3]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ']
    rfl
  have hef : ∀ v, g v = v → e v = v := by
    intro v hv
    have : ∀ i : ℕ, (g ^ i) v = v := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [pow_succ', LinearEquiv.mul_apply, ih, hv]
    simp only [e, this, Finset.sum_const, Finset.card_range]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), hnodd, one_smul]
  have hen : ∀ w, e (nu g w) = 0 := by
    intro w
    have hcomm : ∀ i : ℕ, (g ^ i) (g w) = g ((g ^ i) w) := by
      intro i
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← pow_succ, ← pow_succ']
    rw [nu_apply]
    simp only [e, map_sub, Finset.sum_sub_distrib, hcomm]
    have : ∑ i ∈ Finset.range n, g ((g ^ i) w) = g (e w) := by
      show _ = g (∑ i ∈ Finset.range n, (g ^ i) w)
      rw [map_sum]
    rw [this, hge]
    simp [e]
  have hrange : ∀ v i, v - (g ^ i) v ∈ LinearMap.range (nu g) := by
    intro v i
    induction i with
    | zero => simp
    | succ i ih =>
      have e1 : v - (g ^ (i + 1)) v = -(nu g v) + g (v - (g ^ i) v) := by
        rw [nu_apply, pow_succ', LinearEquiv.mul_apply, map_sub]
        abel
      rw [e1]
      refine add_mem (neg_mem ⟨v, rfl⟩) ?_
      obtain ⟨w, hw⟩ := ih
      refine ⟨g w, ?_⟩
      rw [← hw]
      simp only [nu_apply, map_sub]
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro v hv hv'
    obtain ⟨w, rfl⟩ := hv'
    have h1 : g (nu g w) = nu g w := by
      have := (LinearMap.mem_ker.mp hv)
      rw [nu_apply] at this
      exact sub_eq_zero.mp this
    rw [← hef _ h1, hen]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv1 : e v ∈ fixSp g := by
      show nu g (e v) = 0
      rw [nu_apply, hge, sub_self]
    have hv2 : v - e v ∈ LinearMap.range (nu g) := by
      have : v - e v = ∑ i ∈ Finset.range n, (v - (g ^ i) v) := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_range]
        rw [← Nat.cast_smul_eq_nsmul (ZMod 2), hnodd, one_smul]
      rw [this]
      exact Submodule.sum_mem _ fun i _ => hrange v i
    have : v = e v + (v - e v) := by abel
    rw [this]
    exact Submodule.add_mem_sup hv1 hv2


theorem commuting_invol_trivial {x g : V ≃ₗ[ZMod 2] V} (hx : x ^ 5 = 1) (hxg : x * g = g * x)
    {U : Submodule (ZMod 2) V} (hdim : finrank (ZMod 2) U = 4) (hUx : Stable x U)
    (hUg : Stable g U) (hfix : ∀ u ∈ U, x u = u → u = 0)
    (hgg : ∀ u ∈ U, g (g u) = u) : ∀ u ∈ U, g u = u := by
  let W : Submodule (ZMod 2) V := U.map (nu g)
  have hWU : W ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    rw [nu_apply]
    exact U.sub_mem (hUg u hu) hu
  have hcomm : ∀ v, x (g v) = g (x v) := fun v => by
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) hxg
    simpa using this
  have hWx : Stable x W := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨x u, hUx u hu, ?_⟩
    rw [nu_apply, nu_apply, map_sub, hcomm]
  have hdvd : 4 ∣ finrank (ZMod 2) W :=
    four_dvd_finrank_of_stable hx hWx (fun w hw hxw => hfix w (hWU hw) hxw)
  have hle : finrank (ZMod 2) W ≤ 4 := hdim ▸ Submodule.finrank_mono hWU
  have hnn : ∀ u ∈ U, nu g (nu g u) = 0 := by
    intro u hu
    have h2 : g (g u) = u := hgg u hu
    rw [nu_apply, nu_apply, map_sub, h2]
    have e1 : ∀ a b : V, a - b = a + b := fun a b => by rw [sub_eq_add_neg, neg_eq_self']
    rw [e1, e1, e1]
    calc u + g u + (g u + u) = (u + u) + (g u + g u) := by abel
      _ = 0 := by rw [add_self_eq_zero', add_self_eq_zero', add_zero]
  rcases (by omega : finrank (ZMod 2) W = 0 ∨ finrank (ZMod 2) W = 4) with h0 | h4
  · intro u hu
    have : W = ⊥ := Submodule.finrank_eq_zero.mp h0
    have h1 : nu g u ∈ W := ⟨u, hu, rfl⟩
    rw [this, Submodule.mem_bot, nu_apply] at h1
    exact sub_eq_zero.mp h1
  · exfalso
    have hWeq : W = U := Submodule.eq_of_le_of_finrank_eq hWU (by rw [h4, hdim])
    have hz : ∀ u ∈ U, nu g u = 0 := by
      intro u hu
      have : u ∈ W := hWeq ▸ hu
      obtain ⟨u', hu', rfl⟩ := this
      exact hnn u' hu'
    have : W = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨u, hu, rfl⟩
      rw [hz u hu]
      exact Submodule.zero_mem _
    rw [this, finrank_bot] at h4
    omega

theorem commuting_two_elt_trivial {x g : V ≃ₗ[ZMod 2] V} (hx : x ^ 5 = 1) (hxg : x * g = g * x)
    {U : Submodule (ZMod 2) V} (hdim : finrank (ZMod 2) U = 4) (hUx : Stable x U)
    (hUg : Stable g U) (hfix : ∀ u ∈ U, x u = u → u = 0) {k : ℕ} (hk : g ^ (2 ^ k) = 1) :
    ∀ u ∈ U, g u = u := by
  induction k generalizing g with
  | zero =>
    intro u _
    have : g = 1 := by simpa using hk
    rw [this]
    rfl
  | succ k ih =>
    have hh : (g * g) ^ (2 ^ k) = 1 := by
      rw [← sq, ← pow_mul, ← pow_succ']
      exact hk
    have hxh : x * (g * g) = (g * g) * x := by
      rw [← mul_assoc, hxg, mul_assoc, hxg, ← mul_assoc]
    have hUh : Stable (g * g) U := fun u hu => hUg _ (hUg u hu)
    have h1 := ih hxh hUh hh
    exact commuting_invol_trivial hx hxg hdim hUx hUg hfix fun u hu => h1 u hu


theorem stable_pow_six {a : V ≃ₗ[ZMod 2] V} {N : Submodule (ZMod 2) V}
    (hN : finrank (ZMod 2) N ≤ 2) (hs : Stable a N) : ∀ v ∈ N, (a ^ 6) v = v := by
  classical
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Fintype N := Fintype.ofFinite N
  let X : Type _ := {v : N // v ≠ 0}
  haveI : Fintype X := Fintype.ofFinite X
  let f : X → X := fun x => ⟨⟨a x.1, hs _ x.1.2⟩, fun h0 => x.2 (by
    have h1 : a (x.1 : V) = 0 := congrArg Subtype.val h0
    apply Subtype.ext
    simpa using h1)⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : a (x.1 : V) = a (y.1 : V) := congrArg (fun z : X => (z.1 : V)) hxy
    exact Subtype.ext (Subtype.ext (a.injective h1))
  let τ : Equiv.Perm X := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  have hcardN : Fintype.card N ≤ 4 := by
    have := Module.card_eq_pow_finrank (K := ZMod 2) (V := N)
    simp only [ZMod.card] at this
    rw [this]
    calc 2 ^ finrank (ZMod 2) N ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hN
      _ = 4 := by norm_num
  have hcardX : Fintype.card X ≤ 3 := by
    have h1 : Fintype.card X = Fintype.card N - 1 := by
      have h := Fintype.card_subtype_compl (fun v : N => v = 0)
      rw [Fintype.card_subtype_eq (0 : N)] at h
      convert h
    omega
  have hτ6 : τ ^ 6 = 1 := by
    have h1 : τ ^ Fintype.card (Equiv.Perm X) = 1 := pow_card_eq_one
    rw [Fintype.card_perm] at h1
    have hd : (Fintype.card X).factorial ∣ 6 := by
      interval_cases hc : Fintype.card X <;> decide
    obtain ⟨c, hc⟩ := hd
    rw [hc, pow_mul, h1, one_pow]
  have hiter : ∀ (n : ℕ) (x : X), (((τ ^ n) x : X) : N).1 = (a ^ n) (x.1 : V) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, LinearEquiv.mul_apply, ← ih x]
      rfl
  intro v hv
  by_cases h0 : v = 0
  · rw [h0]; simp
  · have := hiter 6 ⟨⟨v, hv⟩, fun h => h0 (by simpa using congrArg Subtype.val h)⟩
    rw [hτ6] at this
    simpa using this.symm


theorem orderOf_mul_ne_five {j₁ j₂ : V ≃ₗ[ZMod 2] V} (h₁ : j₁ * j₁ = 1) (h₂ : j₂ * j₂ = 1)
    (r₁ : rk j₁ = 1) (r₂ : rk j₂ = 1) : orderOf (j₁ * j₂) ≠ 5 := by
  have _ := h₁
  have _ := h₂
  set a : V ≃ₗ[ZMod 2] V := j₁ * j₂ with ha
  set N : Submodule (ZMod 2) V := LinearMap.range (nu j₁) ⊔ LinearMap.range (nu j₂) with hNdef
  have hNfin : finrank (ZMod 2) N ≤ 2 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (nu j₁))
      (LinearMap.range (nu j₂))
    unfold rk at r₁ r₂
    rw [hNdef]
    omega
  have hmem : ∀ v, a v - v ∈ N := by
    intro v
    have e : a v - v = nu j₁ (j₂ v) + nu j₂ v := by
      rw [ha, LinearEquiv.mul_apply, nu_apply, nu_apply]
      abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨_, rfl⟩) (Submodule.mem_sup_right ⟨_, rfl⟩)
  have hstab : Stable a N := fun n hn => by
    have : a n = n + (a n - n) := by abel
    rw [this]
    exact N.add_mem hn (hmem n)
  have h6 := stable_pow_six hNfin hstab
  have hpow : ∀ (i : ℕ) (v : V), (a ^ i) v - v ∈ N := by
    intro i
    induction i with
    | zero => intro v; simp
    | succ i ih =>
      intro v
      have e : (a ^ (i + 1)) v - v = a ((a ^ i) v - v) + (a v - v) := by
        rw [pow_succ', LinearEquiv.mul_apply, map_sub]
        abel
      rw [e]
      exact N.add_mem (hstab _ (ih v)) (hmem v)
  have h12 : a ^ 12 = 1 := by
    apply LinearEquiv.ext
    intro v
    have hw : (a ^ 6) v - v ∈ N := hpow 6 v
    have e1 : (a ^ 12) v = (a ^ 6) ((a ^ 6) v) := by
      rw [show (12 : ℕ) = 6 + 6 by norm_num, pow_add, LinearEquiv.mul_apply]
    have e2 : (a ^ 6) ((a ^ 6) v) = v := by
      set w : V := (a ^ 6) v - v with hwdef
      have hv : (a ^ 6) v = v + w := by rw [hwdef]; abel
      rw [hv, map_add, h6 _ hw, hv]
      calc v + w + w = v + (w + w) := by abel
        _ = v := by rw [add_self_eq_zero', add_zero]
    rw [e1, e2]
    rfl
  intro h5
  have := orderOf_dvd_of_pow_eq_one h12
  rw [h5] at this
  omega

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
