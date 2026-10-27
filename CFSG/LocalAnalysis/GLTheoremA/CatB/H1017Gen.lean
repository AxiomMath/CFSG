module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Th
public import CFSG.LocalAnalysis.PreuniquenessRankFour.BinaryRank
public import CFSG.Sporadic.Co1Patterson.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

section Rank

variable {X : Type} [Group X] [Finite X]

theorem card_le_of_involution_data_k (k : ℕ)
    (ha : ∀ t : X, orderOf t = 2 → ∀ F : Subgroup X,
      F ≤ Subgroup.centralizer ({t} : Set X) → IsElemAbelian 3 F → Nat.card F ≤ 3 ^ k)
    (hb : ∀ t : X, orderOf t = 2 → ∀ F : Subgroup X,
      F ≤ Subgroup.centralizer ({t} : Set X) → IsElemAbelian 3 F → Nat.card F = 3 ^ k →
      ∀ u : X, orderOf u = 2 → u ∈ Subgroup.centralizer (F : Set X) → u * t = t * u → u = t)
    (R E : Subgroup X) (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hER : E ≤ Subgroup.normalizer (R : Set X)) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hlt
  push Not at hlt
  have hEne : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hlt
    exact absurd hlt (not_lt.2 (Nat.one_le_pow _ _ (by norm_num)))
  have hR3 : ¬ 3 ∣ Nat.card R := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hR2
    rw [hn]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  obtain ⟨B, hB, x, hxR, hx1, hBx⟩ := exists_hyperplane_fixed_three hE hEne hR3 hR hER
  set F : Subgroup X := B.map E.subtype with hFdef
  have hFE : F ≤ E := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hFab : IsElemAbelian 3 F := CFSG.Open.IsElemAbelian.mono hE hFE
  have hFcard : Nat.card F * 3 = Nat.card E := by
    rw [hFdef, Subgroup.card_map_of_injective E.subtype_injective, ← hB]
    exact Subgroup.card_mul_index B
  set V : Subgroup X := R ⊓ Subgroup.centralizer (F : Set X) with hVdef
  have hxV : x ∈ V := by
    refine ⟨hxR, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    exact hBx b hb
  have hV2 : IsPGroup 2 V := hR2.to_le inf_le_left
  haveI : Nontrivial V := ⟨⟨⟨x, hxV⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
  have hZ := hV2.center_nontrivial
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center V) 2
    (by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hV2.to_subgroup (Subgroup.center V))
      have hn1 : n ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hn
        exact (Subgroup.nontrivial_iff_ne_bot _).1 hZ ((Subgroup.eq_bot_iff_card _).2 hn)
      rw [hn]
      exact dvd_pow_self 2 hn1)
  set u : X := ((z : V) : X) with hudef
  have hu2 : orderOf u = 2 := by
    rw [hudef, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hz
  have huV : u ∈ V := (z : V).2
  have hucent : ∀ w ∈ V, u * w = w * u := fun w hw => by
    have := congrArg Subtype.val ((Subgroup.mem_center_iff.1 z.2) ⟨w, hw⟩)
    simpa [hudef] using this.symm
  have hFu : F ≤ Subgroup.centralizer ({u} : Set X) := fun f hf =>
    Subgroup.mem_centralizer_singleton_iff.2 ((Subgroup.mem_centralizer_iff.1 huV.2) f hf)
  have hFk : Nat.card F = 3 ^ k := by
    have h1 := ha u hu2 F hFu hFab
    have hF3 : IsPGroup 3 F := fun g => ⟨1, Subtype.ext (by simpa using hFab.2 g g.2)⟩
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hF3
    rw [hm] at h1 hFcard ⊢
    have hmk : m ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
    have h2 : 3 ^ k < 3 ^ (m + 1) := by rw [pow_succ, hFcard]; exact hlt
    have hkm : k < m + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h2
    have : m = k := by omega
    rw [this]
  obtain ⟨e, heE, heF⟩ : ∃ e ∈ E, e ∉ F := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ F := hcon
    have := Subgroup.card_le_of_le hle
    omega
  have hfe : ∀ f ∈ F, f * e = e * f := fun f hf => comm_of_elemAbelian hE (hFE hf) heE
  set v : X := e * u * e⁻¹ with hvdef
  have hvR : v ∈ R := (Subgroup.le_normalizer_iff.mp hER) e heE u huV.1
  have hvC : v ∈ Subgroup.centralizer (F : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hfu : f * u = u * f := (Subgroup.mem_centralizer_iff.1 huV.2) f hf
    have h1 : f * e⁻¹ = e⁻¹ * f := by
      calc f * e⁻¹ = e⁻¹ * (e * f) * e⁻¹ := by group
        _ = e⁻¹ * (f * e) * e⁻¹ := by rw [hfe f hf]
        _ = e⁻¹ * f := by group
    calc f * v = (f * e) * u * e⁻¹ := by rw [hvdef]; group
      _ = e * (f * u) * e⁻¹ := by rw [hfe f hf]; group
      _ = e * u * (f * e⁻¹) := by rw [hfu]; group
      _ = v * f := by rw [h1, hvdef]; group
  have hvV : v ∈ V := ⟨hvR, hvC⟩
  have hv2 : orderOf v = 2 := by
    rw [hvdef, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hu2]
  have huv : v * u = u * v := (hucent v hvV).symm
  by_cases hvu : v = u
  · have heu : e ∈ Subgroup.centralizer ({u} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have : e * u * e⁻¹ = u := hvu
      calc e * u = e * u * e⁻¹ * e := by group
        _ = u * e := by rw [this]
    set E₂ : Subgroup X := F ⊔ Subgroup.zpowers e
    have hE₂E : E₂ ≤ E := sup_le hFE ((Subgroup.zpowers_le).2 heE)
    have hE₂u : E₂ ≤ Subgroup.centralizer ({u} : Set X) := sup_le hFu ((Subgroup.zpowers_le).2 heu)
    have hFE₂ : F < E₂ := lt_of_le_of_ne le_sup_left fun h =>
      heF (h ▸ (le_sup_right : Subgroup.zpowers e ≤ E₂) (Subgroup.mem_zpowers e))
    have h1 := ha u hu2 E₂ hE₂u (CFSG.Open.IsElemAbelian.mono hE hE₂E)
    have h2 := Subgroup.card_lt_of_lt hFE₂
    omega
  · exact hvu (hb u hu2 F hFu hFab hFk v hv2 hvC huv)

theorem involution_data_of_conj_k (k : ℕ) {a : X}
    (ha : ∀ F : Subgroup X, F ≤ Subgroup.centralizer ({a} : Set X) → IsElemAbelian 3 F →
      Nat.card F ≤ 3 ^ k)
    (hb : ∀ F : Subgroup X, F ≤ Subgroup.centralizer ({a} : Set X) → IsElemAbelian 3 F →
      Nat.card F = 3 ^ k → ∀ u : X, orderOf u = 2 → u ∈ Subgroup.centralizer (F : Set X) →
        u * a = a * u → u = a)
    {t : X} (ht : IsConj a t) :
    (∀ F : Subgroup X, F ≤ Subgroup.centralizer ({t} : Set X) → IsElemAbelian 3 F →
      Nat.card F ≤ 3 ^ k) ∧
    (∀ F : Subgroup X, F ≤ Subgroup.centralizer ({t} : Set X) → IsElemAbelian 3 F →
      Nat.card F = 3 ^ k → ∀ u : X, orderOf u = 2 → u ∈ Subgroup.centralizer (F : Set X) →
        u * t = t * u → u = t) := by
  obtain ⟨g, hg⟩ := isConj_iff.1 ht
  subst hg
  let c : X ≃* X := MulAut.conj g⁻¹
  have hc : ∀ w : X, c w = g⁻¹ * w * g := fun w => by simp [c, MulAut.conj_apply]
  have hmap : ∀ F : Subgroup X, F ≤ Subgroup.centralizer ({g * a * g⁻¹} : Set X) →
      F.map c.toMonoidHom ≤ Subgroup.centralizer ({a} : Set X) := by
    rintro F hF _ ⟨f, hf, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hF hf)
    show c f * a = a * c f
    rw [hc]
    calc g⁻¹ * f * g * a = g⁻¹ * (f * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * f) * g := by rw [h1]
      _ = a * (g⁻¹ * f * g) := by group
  have hEA : ∀ F : Subgroup X, IsElemAbelian 3 F → IsElemAbelian 3 (F.map c.toMonoidHom) := by
    intro F hF
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, hx, rfl⟩ := a
      obtain ⟨_, y, hy, rfl⟩ := b
      show c x * c y = c y * c x
      rw [← map_mul, ← map_mul, comm_of_elemAbelian' hF hx hy]
    · rintro _ ⟨x, hx, rfl⟩
      show c x ^ 3 = 1
      rw [← map_pow, hF.2 x hx, map_one]
  refine ⟨fun F hF hFE => ?_, fun F hF hFE hFk u hu huF hut => ?_⟩
  · have := ha _ (hmap F hF) (hEA F hFE)
    rwa [Subgroup.card_map_of_injective c.injective] at this
  · have hcard : Nat.card (F.map c.toMonoidHom) = 3 ^ k := by
      rw [Subgroup.card_map_of_injective c.injective, hFk]
    have hu' : orderOf (c u) = 2 := by rw [MulEquiv.orderOf_eq, hu]
    have huF' : c u ∈ Subgroup.centralizer ((F.map c.toMonoidHom : Subgroup X) : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨f, hf, rfl⟩
      show c f * c u = c u * c f
      rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 huF) f hf]
    have hut' : c u * a = a * c u := by
      rw [hc]
      calc g⁻¹ * u * g * a = g⁻¹ * (u * (g * a * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * a * g⁻¹) * u) * g := by rw [hut]
        _ = a * (g⁻¹ * u * g) := by group
    have := hb _ (hmap F hF) (hEA F hFE) hcard (c u) hu' huF' hut'
    rw [hc] at this
    calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      _ = g * a * g⁻¹ := by rw [this]

end Rank

@[expose] def TwoLocalBoundPow (k : ℕ) (G : Type) [Group G] : Prop :=
  ∀ R E : Subgroup G, R ≠ ⊥ → IsPGroup 2 R → E ≤ Subgroup.normalizer (R : Set G) →
    IsElemAbelian 3 E → Nat.card E ≤ 3 ^ k

theorem twoLocalBoundPow_of_mulEquiv {k : ℕ} {G H : Type} [Group G] [Group H] (φ : G ≃* H)
    (h : TwoLocalBoundPow k H) : TwoLocalBoundPow k G := by
  intro R E hR hR2 hEN hE
  have hR' : R.map φ.toMonoidHom ≠ ⊥ := fun h0 =>
    hR ((Subgroup.map_eq_bot_iff_of_injective R φ.injective).1 h0)
  have hEN' : E.map φ.toMonoidHom ≤
      Subgroup.normalizer ((R.map φ.toMonoidHom : Subgroup H) : Set H) :=
    (Subgroup.map_mono hEN).trans (Subgroup.le_normalizer_map _)
  have hE' : IsElemAbelian 3 (E.map φ.toMonoidHom) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, hx, rfl⟩ := a
      obtain ⟨_, y, hy, rfl⟩ := b
      show φ x * φ y = φ y * φ x
      rw [← map_mul, ← map_mul, comm_of_elemAbelian' hE hx hy]
    · rintro _ ⟨x, hx, rfl⟩
      show φ x ^ 3 = 1
      rw [← map_pow, hE.2 x hx, map_one]
  have := h _ _ hR' (hR2.map _) hEN' hE'
  rwa [Subgroup.card_map_of_injective φ.injective] at this

section Linear

variable {E V : Type} [CommGroup E] [Finite E] [AddCommGroup V] [Finite V] [Module (ZMod 2) V]

theorem isPGroup_of_elemAbelian3' {X : Type} [Group X] {F : Subgroup X} (hF : IsElemAbelian 3 F) :
    IsPGroup 3 F := fun g => ⟨1, Subtype.ext (by simpa using hF.2 g g.2)⟩

theorem one_apply_lin (v : V) : (1 : V ≃ₗ[ZMod 2] V) v = v := rfl

theorem add_self_zmod2 (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem neg_eq_self_zmod2 (v : V) : -v = v := by
  rw [neg_eq_iff_add_eq_zero, add_self_zmod2]

theorem false_of_invariant_subspace {k : ℕ} (hcard : Nat.card E = 3 ^ k)
    (hpow : ∀ e : E, e ^ 3 = 1) (ρ : E →* (V ≃ₗ[ZMod 2] V)) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V = 2 * k) (W : Submodule (ZMod 2) V) (hW : W ≠ ⊤)
    (hinv : ∀ e : E, ∀ w ∈ W, ρ e w ∈ W)
    (hstep : ∀ x : E, (∀ w ∈ W, ρ x w = w) → ∀ v, ρ x v - v ∈ W) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinv' : ∀ e : E, ∀ w, ρ e (ρ e⁻¹ w) = w := fun e w => by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, one_apply_lin]
  have hmap : ∀ e : E, W.map ((ρ e : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = W := fun e => by
    refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun w hw => hinv e w hw) fun w hw => ?_
    exact ⟨ρ e⁻¹ w, hinv e⁻¹ w hw, hinv' e w⟩
  let r : E →* (W ≃ₗ[ZMod 2] W) :=
    { toFun := fun e => (ρ e).ofSubmodules W W (hmap e)
      map_one' := LinearEquiv.ext fun w => Subtype.ext (by
        show ρ 1 (w : V) = w
        rw [map_one, one_apply_lin])
      map_mul' := fun a b => LinearEquiv.ext fun w => Subtype.ext (by
        show ρ (a * b) (w : V) = ρ a (ρ b w)
        rw [map_mul, LinearEquiv.mul_apply]) }
  have hr : Function.Injective r := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hfix : ∀ w ∈ W, ρ x w = w := fun w hw => by
      have := congrArg (fun φ : W ≃ₗ[ZMod 2] W => (φ ⟨w, hw⟩ : V)) hx
      exact this
    have hsq : ∀ v, ρ x (ρ x v) = v := fun v => by
      have h1 := hfix _ (hstep x hfix v)
      rw [map_sub] at h1
      have h2 : ρ x (ρ x v) = (ρ x v - v) + ρ x v := by rw [← h1]; abel
      rw [h2, sub_add_eq_add_sub, add_self_zmod2, zero_sub, neg_eq_self_zmod2]
    have h3 : ∀ v, ρ x (ρ x (ρ x v)) = v := fun v => by
      have : ρ x ^ 3 = 1 := by rw [← map_pow, hpow, map_one]
      have h := congrArg (fun φ : V ≃ₗ[ZMod 2] V => φ v) this
      simpa [pow_succ, LinearEquiv.mul_apply] using h
    apply hρ
    rw [map_one]
    refine LinearEquiv.ext fun v => ?_
    rw [one_apply_lin]
    have := h3 v
    rwa [hsq] at this
  haveI : FiniteDimensional (ZMod 2) V := inferInstance
  have hlt := Submodule.finrank_lt hW
  have hle := CFSG.PreuniquenessRankFour.Helpers.faithful_binary_elementary_linear_action_dimension_bound
    (acting := E) (space := W) 3 k (by norm_num) hcard hpow r hr
  omega

theorem false_of_fixed_vector {k : ℕ} (hcard : Nat.card E = 3 ^ k)
    (hpow : ∀ e : E, e ^ 3 = 1) (ρ : E →* (V ≃ₗ[ZMod 2] V)) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V = 2 * k) {v : V} (hv : v ≠ 0) (hfix : ∀ e, ρ e v = v) :
    False := by
  classical
  haveI := Fintype.ofFinite E
  let P : V →ₗ[ZMod 2] V := ∑ e : E, ((ρ e : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V)
  have hP : ∀ w, P w = ∑ e : E, ρ e w := fun w => by
    simp only [P, LinearMap.sum_apply, LinearEquiv.coe_coe]
  have hodd : ∀ w : V, (Fintype.card E) • w = w := fun w => by
    rw [Fintype.card_eq_nat_card, hcard]
    obtain ⟨m, hm⟩ := (show Odd 3 by decide).pow (n := k)
    rw [hm, add_smul, one_smul, mul_comm, mul_nsmul, two_nsmul, add_self_zmod2]
    simp
  have hre : ∀ x : E, ∀ w, P (ρ x w) = P w := fun x w => by
    rw [hP, hP]
    exact Fintype.sum_equiv (Equiv.mulRight x) _ _ fun e => by
      simp only [Equiv.coe_mulRight, map_mul, LinearEquiv.mul_apply]
  refine false_of_invariant_subspace hcard hpow ρ hρ hdim (LinearMap.ker P) ?_ ?_ ?_
  · intro htop
    have hvk : v ∈ LinearMap.ker P := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hP] at hvk
    simp only [hfix, Finset.sum_const, Finset.card_univ] at hvk
    rw [hodd] at hvk
    exact hv hvk
  · intro e w hw
    rw [LinearMap.mem_ker] at hw ⊢
    rw [hre, hw]
  · intro x _ w
    rw [LinearMap.mem_ker, map_sub, hre, sub_self]

theorem false_of_commuting_involution {k : ℕ} (hcard : Nat.card E = 3 ^ k)
    (hpow : ∀ e : E, e ^ 3 = 1) (ρ : E →* (V ≃ₗ[ZMod 2] V)) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V = 2 * k) (g : V ≃ₗ[ZMod 2] V) (hg1 : g ≠ 1)
    (hg2 : g * g = 1) (hcomm : ∀ e, ρ e * g = g * ρ e) : False := by
  let N : V →ₗ[ZMod 2] V := (g : V →ₗ[ZMod 2] V) - LinearMap.id
  have hN : ∀ v, N v = g v - v := fun v => rfl
  have hgg : ∀ v, g (g v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, hg2, one_apply_lin]
  have hNN : ∀ v, N (N v) = 0 := fun v => by
    rw [hN, hN, map_sub, hgg, show v - g v - (g v - v) = (v + v) - (g v + g v) by abel,
      add_self_zmod2, add_self_zmod2, sub_self]
  have hcomm' : ∀ e v, g (ρ e v) = ρ e (g v) := fun e v => by
    rw [← LinearEquiv.mul_apply, ← hcomm, LinearEquiv.mul_apply]
  refine false_of_invariant_subspace hcard hpow ρ hρ hdim (LinearMap.ker N) ?_ ?_ ?_
  · intro htop
    apply hg1
    refine LinearEquiv.ext fun v => ?_
    have hvk : v ∈ LinearMap.ker N := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hN, sub_eq_zero] at hvk
    rw [hvk, one_apply_lin]
  · intro e w hw
    rw [LinearMap.mem_ker, hN] at hw ⊢
    rw [hcomm', sub_eq_zero.1 hw, sub_self]
  · intro x hx v
    have h1 : ρ x (g v - v) = g v - v := hx _ (by rw [LinearMap.mem_ker]; exact hNN v)
    rw [map_sub] at h1
    rw [LinearMap.mem_ker, hN, map_sub, hcomm',
      show ρ x (g v) - g v - (ρ x v - v) = (ρ x (g v) - ρ x v) - (g v - v) by abel, h1, sub_self]

end Linear

open CFSG.Sporadic.Co1Patterson in
theorem typeSystem_data {n k : ℕ} (hn : n = 2 * k) {L : Type} [Group L]
    {act : L →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))} (hact : Function.Injective act)
    {qf : (Fin n → ZMod 2) → ZMod 2} {bil : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2}
    {H : Type} [Group H] [Finite H] (T : ExtraspecialTypeSystem n L act qf bil H) :
    (∀ F : Subgroup H, IsElemAbelian 3 F → Nat.card F ≤ 3 ^ k) ∧
    (∀ F : Subgroup H, IsElemAbelian 3 F → Nat.card F = 3 ^ k → ∀ u : H, u * u = 1 →
      (∀ f ∈ F, f * u = u * f) → u = 1 ∨ u = T.z) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdim : Module.finrank (ZMod 2) (Fin n → ZMod 2) = 2 * k := by
    rw [Module.finrank_fin_fun, hn]
  have hQ3 : ∀ q : H, T.φ q = 1 → q ^ 3 = 1 → q = 1 := by
    intro q hq h3
    have h4 : q ^ 4 = 1 := by
      rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (qf (T.vec q)) with h | h
      · have := (T.mul_self_eq_one_iff q hq).2 h
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, this, one_mul]
      · have := (T.mul_self_eq_z_iff q hq).2 h
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, this, T.z_mul_self]
    calc q = q ^ 4 * (q ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4, h3, inv_one, one_mul]
  have hinj : ∀ F : Subgroup H, IsElemAbelian 3 F →
      Function.Injective ((act.comp T.φ).comp F.subtype) := by
    intro F hF
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : T.φ (x : H) = 1 := hact (by rw [map_one]; exact hx)
    exact Subtype.ext (hQ3 _ h1 (hF.2 x x.2))
  refine ⟨fun F hF => ?_, fun F hF hFk u hu2 huF => ?_⟩
  · haveI := hF.1
    letI : CommGroup F := IsMulCommutative.instCommGroup
    have hpow : ∀ e : F, e ^ 3 = 1 := fun e => Subtype.ext (hF.2 e e.2)
    obtain ⟨r, hr⟩ := IsPGroup.iff_card.1 (isPGroup_of_elemAbelian3' hF)
    have hle := CFSG.PreuniquenessRankFour.Helpers.faithful_binary_elementary_linear_action_dimension_bound
      (acting := F) (space := Fin n → ZMod 2) 3 r (by norm_num) hr hpow _ (hinj F hF)
    rw [hdim] at hle
    rw [hr]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · haveI := hF.1
    letI : CommGroup F := IsMulCommutative.instCommGroup
    have hpow : ∀ e : F, e ^ 3 = 1 := fun e => Subtype.ext (hF.2 e e.2)
    by_cases hu : T.φ u = 1
    · by_cases hv : T.vec u = 0
      · exact (T.vec_eq_zero u hu).1 hv
      · exfalso
        refine false_of_fixed_vector (E := F) hFk hpow _ (hinj F hF) hdim hv fun e => ?_
        show act (T.φ (e : H)) (T.vec u) = T.vec u
        rw [← T.vec_conj (e : H) u hu]
        congr 1
        rw [huF _ e.2, mul_inv_cancel_right]
    · exfalso
      refine false_of_commuting_involution (E := F) hFk hpow _ (hinj F hF) hdim (act (T.φ u)) ?_ ?_ ?_
      · intro h
        exact hu (hact (by rw [h, map_one]))
      · rw [← map_mul, ← map_mul, hu2, map_one, map_one]
      · intro e
        show act (T.φ (e : H)) * act (T.φ u) = act (T.φ u) * act (T.φ (e : H))
        rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, huF _ e.2]

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
