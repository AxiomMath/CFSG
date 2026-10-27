module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisTorsion
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.RankThree.PartOne.OutStructure (Inn OutPNice OutPChain)

@[expose] def NoHeisAut (p : ℕ) (X : Type*) [Group X] : Prop :=
  ∀ E : Subgroup (MulAut X), Nat.card E = p ^ 3 → (∀ x ∈ E, x ^ p = 1) → IsMulCommutative E

@[expose] def OutPCyc (p : ℕ) (X : Type*) [Group X] : Prop :=
  ∀ E : Subgroup (MulAut X), IsPGroup p E → ∃ g ∈ E, E ≤ Subgroup.zpowers g ⊔ Inn X

section Chain

variable {X : Type*} [Group X] {p : ℕ}

theorem comparable_of_outPChain (h : OutPChain p X) {E : Subgroup (MulAut X)} (hE : IsPGroup p E)
    {α β : MulAut X} (hα : α ∈ E) (hβ : β ∈ E) :
    α ∈ Subgroup.zpowers β ⊔ Inn X ∨ β ∈ Subgroup.zpowers α ⊔ Inn X := by
  obtain ⟨D, Et, hID, hD2, hpE, hcmp⟩ := h
  have hpow : ∀ γ ∈ E, ∃ k : ℕ, γ ^ (p ^ k) = 1 := fun γ hγ => by
    obtain ⟨k, hk⟩ := hE ⟨γ, hγ⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hEt : ∀ γ ∈ E, γ ∈ Et := fun γ hγ => by
    obtain ⟨k, hk⟩ := hpow γ hγ
    exact hpE γ ⟨k, by rw [hk]; exact D.one_mem⟩
  have key : ∀ {γ δ : MulAut X}, γ ∈ E → δ ∈ E → ∀ m : ℤ, γ * δ ^ m ∈ D →
      γ ∈ Subgroup.zpowers δ ⊔ Inn X := by
    intro γ δ hγ hδ m hm
    have hmE : γ * δ ^ m ∈ E := E.mul_mem hγ (E.zpow_mem hδ m)
    obtain ⟨j, hj⟩ := hpow _ hmE
    have hin : γ * δ ^ m ∈ Inn X := hD2 _ hm j (by rw [hj]; exact (Inn X).one_mem)
    have : γ = (γ * δ ^ m) * (δ ^ (-m)) := by group
    rw [this, sup_comm]
    exact Subgroup.mul_mem_sup hin (Subgroup.zpow_mem_zpowers δ (-m))
  have hc := hcmp α (hEt α hα) β (hEt β hβ)
    (by obtain ⟨k, hk⟩ := hpow α hα; exact ⟨k, by rw [hk]; exact D.one_mem⟩)
    (by obtain ⟨k, hk⟩ := hpow β hβ; exact ⟨k, by rw [hk]; exact D.one_mem⟩)
  rcases hc with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact Or.inl (key hα hβ m hm)
  · exact Or.inr (key hβ hα m hm)

theorem outPCyc_of_outPChain [Finite X] (h : OutPChain p X) : OutPCyc p X := by
  intro E hE
  haveI : Finite (MulAut X) := inferInstance
  haveI : Finite E := inferInstance
  let f : E → ℕ := fun g => Nat.card (Subgroup.zpowers (g : MulAut X) ⊔ Inn X : Subgroup _)
  obtain ⟨g, hg⟩ := Finite.exists_max f
  refine ⟨g, g.2, fun α hα => ?_⟩
  rcases comparable_of_outPChain h hE hα g.2 with h1 | h1
  · exact h1
  · have hle : Subgroup.zpowers (g : MulAut X) ⊔ Inn X ≤
        Subgroup.zpowers α ⊔ Inn X := sup_le (Subgroup.zpowers_le.2 h1) le_sup_right
    have hcard : Nat.card (Subgroup.zpowers α ⊔ Inn X : Subgroup _) ≤
        Nat.card (Subgroup.zpowers (g : MulAut X) ⊔ Inn X : Subgroup _) := hg ⟨α, hα⟩
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard
    rw [heq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers α)

theorem outPCyc_of_outPNice [Finite X] (h : OutPNice p X) : OutPCyc p X :=
  outPCyc_of_outPChain h.toChain

end Chain

section Sylow

open scoped Pointwise

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

theorem exists_invariant_sylow [Fact p.Prime] (E : Subgroup (MulAut X)) (hE : IsPGroup p E) :
    ∃ S : Sylow p X, ∀ α ∈ E, ∀ x : X, x ∈ (S : Subgroup X) ↔ α x ∈ (S : Subgroup X) := by
  have h := hE.card_modEq_card_fixedPoints (Sylow p X)
  have h1 := card_sylow_modEq_one p X
  have hfp : Nat.card (MulAction.fixedPoints E (Sylow p X)) ≡ 1 [MOD p] := h.symm.trans h1
  have hne : (MulAction.fixedPoints E (Sylow p X)).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : Nat.card (MulAction.fixedPoints E (Sylow p X)) = 0 := by
      rw [hne]; simp
    rw [h0] at hfp
    have hd : p ∣ 1 := Nat.modEq_zero_iff_dvd.1 hfp.symm
    exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.1 hd)
  obtain ⟨S, hS⟩ := hne
  refine ⟨S, fun α hα x => ?_⟩
  have hfix : (⟨α, hα⟩ : E) • S = S := hS ⟨α, hα⟩
  have hsub : ((⟨α, hα⟩ : E) • (S : Subgroup X)) = (S : Subgroup X) := by
    have h3 : ((((⟨α, hα⟩ : E) • S : Sylow p X)) : Subgroup X) =
        (⟨α, hα⟩ : E) • (S : Subgroup X) := Sylow.pointwise_smul_def (α := E)
    rw [← h3, hfix]
  have hmem : ∀ y, y ∈ (S : Subgroup X) ↔ ((⟨α, hα⟩ : E)⁻¹ • y) ∈ (S : Subgroup X) := by
    intro y
    have h3 : y ∈ (⟨α, hα⟩ : E) • (S : Subgroup X) ↔
        (⟨α, hα⟩ : E)⁻¹ • y ∈ (S : Subgroup X) :=
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem (α := E)
    rw [hsub] at h3
    exact h3
  have h4 := hmem (α x)
  have h5 : (⟨α, hα⟩ : E)⁻¹ • (α x) = x := by
    change ((⟨α, hα⟩ : E)⁻¹ : E).1 (α x) = x
    simp
  rw [h5] at h4
  exact h4.symm

@[expose] def heisAutRestrict (S : Subgroup X) (α : MulAut X) (h : ∀ x, x ∈ S ↔ α x ∈ S) :
    S ≃* S where
  toFun s := ⟨α s, (h s).1 s.2⟩
  invFun s := ⟨α.symm s, by
    rw [h]
    simpa using s.2⟩
  left_inv s := by
    apply Subtype.ext
    simp
  right_inv s := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp

theorem heisAutRestrict_pow (S : Subgroup X) (α : MulAut X) (h : ∀ x, x ∈ S ↔ α x ∈ S)
    (k : ℕ) (s : S) : (((heisAutRestrict S α h) ^ k) s : X) = (α ^ k) (s : X) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, ih, pow_succ, MulAut.mul_apply]
    rfl

theorem heis_fixes_torsion_of_card_le (hp : p.Prime) (S : Subgroup X)
    (hcard : Nat.card {x : S // x ^ p = 1} ≤ p) (σ : MulAut X) (hσp : σ ^ p = 1)
    (hσ : ∀ x, x ∈ S ↔ σ x ∈ S) (x : X) (hxS : x ∈ S) (hx : x ^ p = 1) : σ x = x := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hx1 : x = 1
  · subst hx1
    simp
  have hord : orderOf x = p := by
    refine (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hx) |>.resolve_left ?_
    intro h
    exact hx1 (orderOf_eq_one_iff.1 h)
  let x' : S := ⟨x, hxS⟩
  let σx : S := ⟨σ x, (hσ x).1 hxS⟩
  have hx'ord : orderOf x' = p := (orderOf_submonoid x').symm.trans hord
  have hmem : σx ∈ Subgroup.zpowers x' := by
    by_contra hnot
    let Ω : Set {x : S // x ^ p = 1} := Set.univ
    have hxp' : x' ^ p = 1 := Subtype.ext hx
    have hσxp : σx ^ p = 1 := by
      apply Subtype.ext
      change (σ x) ^ p = 1
      rw [← map_pow, hx, map_one]
    have hz : ∀ z : Subgroup.zpowers x', (z : S) ^ p = 1 := by
      rintro ⟨z, hz⟩
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      change (x' ^ m) ^ p = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp', one_zpow]
    let f : (Subgroup.zpowers x') ⊕ Unit → {x : S // x ^ p = 1} :=
      Sum.elim (fun z => ⟨(z : S), hz z⟩) (fun _ => ⟨σx, hσxp⟩)
    have hf : Function.Injective f := by
      intro a b hab
      rcases a with z | u <;> rcases b with w | u' <;>
        simp only [f, Sum.elim_inl, Sum.elim_inr] at hab
      · have h : (z : S) = (w : S) := congrArg (fun t : {x : S // x ^ p = 1} => (t : S)) hab
        exact congrArg Sum.inl (Subtype.ext h)
      · exfalso
        have h : (z : S) = σx := congrArg (fun t : {x : S // x ^ p = 1} => (t : S)) hab
        exact hnot (h ▸ z.2)
      · exfalso
        have h : σx = (w : S) := congrArg (fun t : {x : S // x ^ p = 1} => (t : S)) hab
        exact hnot (h ▸ w.2)
      · rfl
    have hcardle := Nat.card_le_card_of_injective f hf
    have hc : Nat.card ((Subgroup.zpowers x') ⊕ Unit) = p + 1 := by
      rw [Nat.card_sum, Nat.card_zpowers, hx'ord, Nat.card_unique]
    omega
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hσk : σ x = x ^ k := congrArg Subtype.val hk.symm
  have hit : ∀ j : ℕ, (σ ^ j) x = x ^ (k ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_zpow, hσk, ← zpow_mul, pow_succ]
      ring_nf
  have h1 : x ^ (k ^ p) = x := by
    have := hit p
    rw [hσp] at this
    simpa using this.symm
  have h2 : x ^ (k ^ p - 1) = 1 := by
    rw [zpow_sub, h1, zpow_one, mul_inv_cancel]
  have h3 : (p : ℤ) ∣ k ^ p - 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.2 h2
    rwa [hord] at this
  have h4 : ((k : ZMod p)) ^ p = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h3
    push_cast at this
    exact sub_eq_zero.1 this
  have h5 : (k : ZMod p) = 1 := by
    rw [← h4]
    exact (ZMod.pow_card (k : ZMod p)).symm
  have h6 : (p : ℤ) ∣ k - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h5, sub_self]
  have h7 : x ^ (k - 1) = 1 := by
    have : (orderOf x : ℤ) ∣ k - 1 := by rw [hord]; exact h6
    exact (orderOf_dvd_iff_zpow_eq_one).1 this
  rw [hσk]
  have : x ^ k = x ^ (k - 1) * x := by
    rw [← zpow_add_one]
    simp
  rw [this, h7, one_mul]

theorem noHeisAut_of_sylow (hp : p.Prime) (hp5 : 5 ≤ p)
    (hZ : Function.Injective (MulAut.conj : X →* MulAut X)) (hCyc : OutPCyc p X)
    (hSyl : ∀ S : Sylow p X, (∀ a ∈ S, ∀ b ∈ S, a * b = b * a) ∧
      Nat.card {x : S // x ^ p = 1} ≤ p ^ 3 ∧
      ((∃ α : MulAut X, α ∉ Inn X ∧ α ^ p = 1) →
        Nat.card {x : S // x ^ p = 1} ≤ p ∨
          ∀ x ∈ (S : Subgroup X), x ^ p = 1 → ∃ y ∈ (S : Subgroup X), y ^ p = x)) :
    NoHeisAut p X := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro E hEcard hEexp
  have hEp : IsPGroup p E := IsPGroup.of_card (n := 3) hEcard
  obtain ⟨S, hSinv⟩ := exists_invariant_sylow E hEp
  obtain ⟨hab, hrk, hHP⟩ := hSyl S
  obtain ⟨g, hgE, hEg⟩ := hCyc E hEp
  have hE0 : ∀ e ∈ E, e ∈ Inn X →
      ∃ x ∈ (S : Subgroup X), MulAut.conj x = e ∧ x ^ p = 1 := by
    rintro e he ⟨x, rfl⟩
    have hxp : x ^ p = 1 := by
      apply hZ
      rw [map_pow, map_one]
      exact hEexp _ he
    have hxn0 : x ∈ Subgroup.normalizer ((S : Subgroup X) : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have := hSinv _ he y
      simpa [MulAut.conj_apply] using this
    have hxn : x ∈ Subgroup.normalizer (S : Set X) := hxn0
    have hP : IsPGroup p (Subgroup.zpowers x) := fun y => by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 y.2
      refine ⟨1, Subtype.ext ?_⟩
      have : (y : X) ^ p = 1 := by
        rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
      simpa using this
    have hx' : x ∈ Subgroup.zpowers x ⊓ Subgroup.normalizer (S : Set X) :=
      ⟨Subgroup.mem_zpowers x, hxn⟩
    rw [hP.inf_normalizer_sylow S] at hx'
    exact ⟨x, hx'.2, rfl, hxp⟩
  have hgp : g ^ p = 1 := hEexp g hgE
  have hgc : ∀ x ∈ (S : Subgroup X), x ^ p = 1 → g * MulAut.conj x = MulAut.conj x * g := by
    intro x hxS hxp
    by_cases hgI : g ∈ Inn X
    · obtain ⟨z, hzS, hz, -⟩ := hE0 g hgE hgI
      rw [← hz, ← map_mul, ← map_mul, hab z hzS x hxS]
    · rcases hHP ⟨g, hgI, hgp⟩ with hcle | hHP'
      · have hgx : g x = x := heis_fixes_torsion_of_card_le hp S hcle g hgp (hSinv g hgE) x hxS hxp
        ext y
        simp [MulAut.conj_apply, hgx]
      letI : CommGroup S :=
        { (inferInstance : Group S) with
          mul_comm := fun a b => Subtype.ext (hab a a.2 b b.2) }
      obtain ⟨n, hn⟩ := (S.isPGroup').exists_card_eq
      have hfix := heis_mul_fixes_torsion (G := S) hp hp5
        ⟨n, fun a => by rw [← hn]; exact pow_card_eq_one'⟩ hrk
        (by
          intro a ha
          obtain ⟨y, hy, hyp⟩ := hHP' a a.2 (congrArg Subtype.val ha)
          exact ⟨⟨y, hy⟩, Subtype.ext hyp⟩)
        (heisAutRestrict (S : Subgroup X) g (hSinv g hgE))
        (by
          ext a
          rw [heisAutRestrict_pow, hgp]
          simp)
        ⟨x, hxS⟩ (Subtype.ext hxp)
      have hgx : g x = x := congrArg Subtype.val hfix
      ext y
      simp [MulAut.conj_apply, hgx]
  have hdec : ∀ a ∈ E, ∃ (k : ℤ) (x : X), x ∈ (S : Subgroup X) ∧ x ^ p = 1 ∧
      a = g ^ k * MulAut.conj x := by
    intro a ha
    have hasup := hEg ha
    rw [Subgroup.mem_sup_of_normal_right] at hasup
    obtain ⟨y, hy, z, hz, hyz⟩ := hasup
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hzE : z ∈ E := by
      have : z = (g ^ k)⁻¹ * a := by rw [← hyz]; group
      rw [this]
      exact E.mul_mem (E.inv_mem (E.zpow_mem hgE k)) ha
    obtain ⟨x, hxS, hxz, hxp⟩ := hE0 z hzE hz
    exact ⟨k, x, hxS, hxp, by rw [hxz, hyz]⟩
  have hcc : ∀ x ∈ (S : Subgroup X), ∀ y ∈ (S : Subgroup X),
      MulAut.conj x * MulAut.conj y = MulAut.conj y * MulAut.conj x := by
    intro x hx y hy
    rw [← map_mul, ← map_mul, hab x hx y hy]
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨k, x, hxS, hxp, hax⟩ := hdec a a.2
  obtain ⟨l, y, hyS, hyp, hby⟩ := hdec b b.2
  apply Subtype.ext
  show (a : MulAut X) * b = b * a
  rw [hax, hby]
  have hgx : Commute g (MulAut.conj x) := hgc x hxS hxp
  have hgy : Commute g (MulAut.conj y) := hgc y hyS hyp
  have h1 : MulAut.conj x * g ^ l = g ^ l * MulAut.conj x := (hgx.zpow_left l).symm.eq
  have h2 : MulAut.conj y * g ^ k = g ^ k * MulAut.conj y := (hgy.zpow_left k).symm.eq
  calc g ^ k * MulAut.conj x * (g ^ l * MulAut.conj y)
      = g ^ k * (MulAut.conj x * g ^ l) * MulAut.conj y := by group
    _ = g ^ k * (g ^ l * MulAut.conj x) * MulAut.conj y := by rw [h1]
    _ = (g ^ k * g ^ l) * (MulAut.conj x * MulAut.conj y) := by group
    _ = (g ^ l * g ^ k) * (MulAut.conj y * MulAut.conj x) := by
        rw [← zpow_add, ← zpow_add, add_comm, hcc x hxS y hyS]
    _ = g ^ l * (g ^ k * MulAut.conj y) * MulAut.conj x := by group
    _ = g ^ l * (MulAut.conj y * g ^ k) * MulAut.conj x := by rw [h2]
    _ = g ^ l * MulAut.conj y * (g ^ k * MulAut.conj x) := by group

end Sylow

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
