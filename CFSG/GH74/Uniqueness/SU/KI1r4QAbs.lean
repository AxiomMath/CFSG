module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.Q64

open Subgroup

theorem odd_card_dvd_nine {V : Type*} [Group V] [Finite V] (V₁ V₂ : Subgroup V)
    (h1 : Nat.card V₁ = 4) (h2 : Nat.card V₂ = 4) (hsup : V₁ ⊔ V₂ = ⊤)
    (Q : Subgroup (MulAut V)) (hodd : ¬ 2 ∣ Nat.card Q)
    (hQ : ∀ φ ∈ Q, ∀ v, (v ∈ V₁ ↔ φ v ∈ V₁) ∧ (v ∈ V₂ ↔ φ v ∈ V₂)) :
    Nat.card Q ∣ 9 := by
  classical
  let θ : Q →* Equiv.Perm V₁ × Equiv.Perm V₂ :=
    { toFun := fun φ => (Equiv.Perm.subtypePerm (MulAut.toPerm V φ.1)
          (fun v => (hQ φ.1 φ.2 v).1.symm),
        Equiv.Perm.subtypePerm (MulAut.toPerm V φ.1) (fun v => (hQ φ.1 φ.2 v).2.symm))
      map_one' := by
        refine Prod.ext (Equiv.ext fun x => Subtype.ext ?_) (Equiv.ext fun x => Subtype.ext ?_) <;>
          rfl
      map_mul' := by
        intro a b
        refine Prod.ext (Equiv.ext fun x => Subtype.ext ?_) (Equiv.ext fun x => Subtype.ext ?_) <;>
          rfl }
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro φ hφ
    have hφ' := Prod.ext_iff.mp hφ
    have hfix : ∀ v, v ∈ V₁ ⊔ V₂ → φ.1 v = v := by
      intro v hv
      let F : Subgroup V :=
        { carrier := {v | φ.1 v = v}
          one_mem' := by simp
          mul_mem' := by intro a b ha hb; simp_all
          inv_mem' := by intro a ha; simp_all }
      have hV₁ : V₁ ≤ F := fun v hv => by
        have := congrArg (fun p => (p ⟨v, hv⟩ : V₁).1) hφ'.1
        show φ.1 v = v
        exact this
      have hV₂ : V₂ ≤ F := fun v hv => by
        have := congrArg (fun p => (p ⟨v, hv⟩ : V₂).1) hφ'.2
        show φ.1 v = v
        exact this
      exact sup_le hV₁ hV₂ hv
    apply Subtype.ext
    ext v
    exact hfix v (hsup ▸ Subgroup.mem_top v)
  have hdvd : Nat.card Q ∣ Nat.card (Equiv.Perm V₁ × Equiv.Perm V₂) :=
    Subgroup.card_dvd_of_injective θ hinj
  rw [Nat.card_prod, Nat.card_perm, Nat.card_perm, h1, h2] at hdvd
  have h576 : Nat.card Q ∣ 576 := by simpa [Nat.factorial] using hdvd
  have hcop : Nat.Coprime (Nat.card Q) 64 := by
    apply Nat.Coprime.symm
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two |>.mpr hodd).pow_left 6
  have : 576 = 64 * 9 := by norm_num
  rw [this] at h576
  exact hcop.dvd_of_dvd_mul_left h576

theorem exists_normalizing_conj {G : Type*} [Group G] [Finite G] (R P : Subgroup G) [R.Normal]
    (hR : IsPGroup 2 R) (hP : IsPGroup 3 P) (x : G)
    (hx : ∀ k, k ∈ R ⊔ P ↔ x * k * x⁻¹ ∈ R ⊔ P) :
    ∃ r ∈ R, ∀ p ∈ P, (r⁻¹ * x) * p * (r⁻¹ * x)⁻¹ ∈ P := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K : Subgroup G := R ⊔ P with hK
  let P' : Subgroup G := P.map (MulAut.conj x).toMonoidHom
  have hP'3 : IsPGroup 3 P' := hP.map _
  have hP'K : P' ≤ K := by
    rintro _ ⟨p, hp, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (hx p).mp (Subgroup.mem_sup_right hp)
  have hKP' : K ≤ R ⊔ P' := by
    intro k hk
    have h1 : x⁻¹ * k * x ∈ K := by
      have := (hx (x⁻¹ * k * x)).mpr (by simpa [mul_assoc] using hk)
      exact this
    obtain ⟨r, hr, p, hp, hrp⟩ := Subgroup.mem_sup_of_normal_left.mp h1
    have hk' : k = (x * r * x⁻¹) * (x * p * x⁻¹) := by
      have : x * (r * p) * x⁻¹ = k := by
        rw [hrp]; group
      rw [← this]; group
    rw [hk']
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ⟨p, hp, ?_⟩)
    · exact ‹R.Normal›.conj_mem r hr x
    · simp [MulAut.conj_apply]
  have hRK : R ≤ K := le_sup_left
  have mkSylow : ∀ (S : Subgroup G), IsPGroup 3 S → S ≤ K → K ≤ R ⊔ S →
      ∃ T : Sylow 3 K, (T : Subgroup K) = S.subgroupOf K := by
    intro S hS hSK hKS
    refine ⟨⟨S.subgroupOf K, ?_, ?_⟩, rfl⟩
    · exact hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
    · intro Q hQ hSQ
      refine le_antisymm (fun q hq => ?_) hSQ
      obtain ⟨r, hr, s, hs, hrs⟩ := Subgroup.mem_sup_of_normal_left.mp (hKS q.2)
      have hsK : (⟨s, hSK hs⟩ : K) ∈ Q := hSQ (by simpa [Subgroup.mem_subgroupOf] using hs)
      have hrQ : (⟨r, hRK hr⟩ : K) ∈ Q := by
        have : (⟨r, hRK hr⟩ : K) = q * (⟨s, hSK hs⟩ : K)⁻¹ := by
          apply Subtype.ext
          simp [← hrs]
        rw [this]
        exact Q.mul_mem hq (Q.inv_mem hsK)
      obtain ⟨n, hn⟩ := hR ⟨r, hr⟩
      obtain ⟨m, hm⟩ := hQ ⟨_, hrQ⟩
      have hn' : r ^ 2 ^ n = 1 := congrArg Subtype.val hn
      have hm' : r ^ 3 ^ m = 1 := by
        have := congrArg (fun z : Q => ((z : K) : G)) hm
        simpa using this
      have hcop : Nat.Coprime (2 ^ n) (3 ^ m) := Nat.Coprime.pow _ _ (by norm_num)
      have hr1 : r = 1 := by
        have : r ^ Nat.gcd (2 ^ n) (3 ^ m) = 1 := pow_gcd_eq_one.mpr ⟨hn', hm'⟩
        rwa [hcop, pow_one] at this
      have hq : q.1 = s := by rw [← hrs, hr1, one_mul]
      show q ∈ S.subgroupOf K
      rw [Subgroup.mem_subgroupOf, hq]
      exact hs
  obtain ⟨S₁, hS₁⟩ := mkSylow P hP le_sup_right le_rfl
  obtain ⟨S₂, hS₂⟩ := mkSylow P' hP'3 hP'K hKP'
  obtain ⟨k, hk⟩ : ∃ k : K, k • S₁ = S₂ := MulAction.exists_smul_eq K S₁ S₂
  obtain ⟨r, hr, p, hp, hrp⟩ := Subgroup.mem_sup_of_normal_left.mp k.2
  refine ⟨r, hr, fun p₀ hp₀ => ?_⟩
  have hg : x * p₀ * x⁻¹ ∈ P' := ⟨p₀, hp₀, by simp [MulAut.conj_apply]⟩
  have hgK : x * p₀ * x⁻¹ ∈ K := hP'K hg
  have h2 : (⟨x * p₀ * x⁻¹, hgK⟩ : K) ∈ (S₂ : Subgroup K) := by
    rw [hS₂]; simpa [Subgroup.mem_subgroupOf] using hg
  rw [← hk, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h2
  have h3 : k⁻¹ * ⟨x * p₀ * x⁻¹, hgK⟩ * k ∈ (S₁ : Subgroup K) := by simpa using h2
  rw [hS₁, Subgroup.mem_subgroupOf] at h3
  have h4 : p⁻¹ * (r⁻¹ * (x * p₀ * x⁻¹) * r) * p ∈ P := by
    have : ((k⁻¹ * ⟨x * p₀ * x⁻¹, hgK⟩ * k : K) : G) =
        p⁻¹ * (r⁻¹ * (x * p₀ * x⁻¹) * r) * p := by
      have hk' : (k : G) = r * p := hrp.symm
      simp [hk', mul_assoc]
    rw [← this]; exact h3
  have h5 : r⁻¹ * (x * p₀ * x⁻¹) * r ∈ P := by
    have := P.mul_mem (P.mul_mem hp h4) (P.inv_mem hp)
    simpa [mul_assoc] using this
  simpa [mul_assoc] using h5

theorem nonempty_mulEquiv_prod_of_commute {G : Type*} [Group G] (S T : Subgroup G)
    (hcomm : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) (hdisj : S ⊓ T = ⊥) :
    Nonempty (↥(S ⊔ T) ≃* ↥S × ↥T) := by
  let f : ↥S × ↥T →* G := MonoidHom.noncommCoprod S.subtype T.subtype
    (fun s t => (hcomm s s.2 t t.2))
  have hfapp : ∀ s : S, ∀ t : T, f (s, t) = (s : G) * t := fun s t => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨s, t⟩ h
    have h' : (s : G) * t = 1 := by rw [← hfapp]; exact h
    have hs : (s : G) = (t : G)⁻¹ := eq_inv_of_mul_eq_one_left h'
    have hs1 : (s : G) ∈ S ⊓ T := ⟨s.2, by rw [hs]; exact T.inv_mem t.2⟩
    rw [hdisj, Subgroup.mem_bot] at hs1
    have ht1 : (t : G) = 1 := by
      rw [hs1, one_mul] at h'
      exact h'
    exact Prod.ext (Subtype.ext hs1) (Subtype.ext ht1)
  have hrange : f.range = S ⊔ T := by
    apply le_antisymm
    · rintro _ ⟨⟨s, t⟩, rfl⟩
      rw [hfapp]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left s.2) (Subgroup.mem_sup_right t.2)
    · refine sup_le (fun s hs => ⟨(⟨s, hs⟩, 1), by simp [hfapp]⟩)
        (fun t ht => ⟨(1, ⟨t, ht⟩), by simp [hfapp]⟩)
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

theorem nonempty_mulEquiv_zmod_three {G : Type*} [Group G] (C : Subgroup G)
    (h3 : Nat.card C = 3) : Nonempty (↥C ≃* Multiplicative (ZMod 3)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic C := isCyclic_of_prime_card h3
  have := zmodCyclicMulEquiv hcyc
  rw [h3] at this
  exact ⟨this.symm⟩

@[expose] def permCongrMulEquiv {α β : Type*} (e : α ≃ β) : Equiv.Perm α ≃* Equiv.Perm β where
  toEquiv := e.permCongr
  map_mul' f g := by
    ext x
    simp [Equiv.permCongr_apply]

theorem card_sup_le_of_le_normalizer {G : Type*} [Group G] [Finite G] (S T : Subgroup G)
    (h : S ≤ normalizer (T : Set G)) : Nat.card ↥(S ⊔ T) ≤ Nat.card S * Nat.card T := by
  have hco := Subgroup.coe_mul_of_left_le_normalizer_right S T h
  let f : ↥S × ↥T → ↥(S ⊔ T) := fun p => ⟨(p.1 : G) * p.2, Subgroup.mul_mem _
    (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨g, hg⟩
    have : g ∈ (↑(S ⊔ T) : Set G) := hg
    rw [hco] at this
    obtain ⟨s, hs, t, ht, rfl⟩ := this
    exact ⟨(⟨s, hs⟩, ⟨t, ht⟩), rfl⟩
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod] at this

theorem bijective_of_perm_three {G X : Type*} [Group G] [Finite G] [Fintype X]
    [DecidableEq X] (hX : Fintype.card X = 3) (E : Subgroup G) (x y : G) (hxE : x ∈ E)
    (hyE : y ∈ E) (hEgen : E = zpowers x ⊔ zpowers y) (hx2 : x * x = 1) (hy3 : y ^ 3 = 1)
    (hxy : x * y * x⁻¹ = y⁻¹) (ρ : E →* Equiv.Perm X) (hρy : ρ ⟨y, hyE⟩ ≠ 1)
    (hρx : ρ ⟨x, hxE⟩ ≠ 1) : Function.Bijective ρ := by
  classical
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hfwd : ∀ w ∈ zpowers y, x * w * x⁻¹ ∈ zpowers y := by
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← conj_zpow, hxy]
    exact zpow_mem (inv_mem (mem_zpowers y)) k
  have hxn : zpowers x ≤ normalizer ((zpowers y : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · exact hfwd g
    · intro hk
      have := hfwd _ hk
      have h2 : x * (x * g * x⁻¹) * x⁻¹ = g := by
        calc x * (x * g * x⁻¹) * x⁻¹ = (x * x) * g * (x * x)⁻¹ := by group
          _ = g := by rw [hx2]; group
      rwa [h2] at this
  have hcardE : Nat.card E ≤ 6 := by
    rw [hEgen]
    have h1 := card_sup_le_of_le_normalizer (zpowers x) (zpowers y) hxn
    have h2 : Nat.card (zpowers x) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx2))
    have h3 : Nat.card (zpowers y) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hy3)
    calc Nat.card ↥(zpowers x ⊔ zpowers y) ≤ Nat.card (zpowers x) * Nat.card (zpowers y) := h1
      _ ≤ 2 * 3 := Nat.mul_le_mul h2 h3
  let ey : E := ⟨y, hyE⟩
  let ex : E := ⟨x, hxE⟩
  have hey3 : orderOf (ρ ey) = 3 := by
    have : ρ ey ^ 3 = 1 := by
      rw [← map_pow]
      have : ey ^ 3 = 1 := Subtype.ext (by simpa using hy3)
      rw [this, map_one]
    exact orderOf_eq_prime this hρy
  have hex2 : orderOf (ρ ex) = 2 := by
    have : ρ ex ^ 2 = 1 := by
      rw [← map_pow]
      have : ex ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hx2)
      rw [this, map_one]
    exact orderOf_eq_prime this hρx
  have hPerm : Nat.card (Equiv.Perm X) = 6 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, hX]; rfl
  have h6 : 6 ∣ Nat.card ρ.range := by
    have h2 : 2 ∣ Nat.card ρ.range := by
      have h := orderOf_dvd_natCard (⟨ρ ex, ⟨ex, rfl⟩⟩ : ρ.range)
      have e : orderOf (⟨ρ ex, ⟨ex, rfl⟩⟩ : ρ.range) = 2 := by
        rw [← Subgroup.orderOf_coe]; exact hex2
      rwa [e] at h
    have h3 : 3 ∣ Nat.card ρ.range := by
      have h := orderOf_dvd_natCard (⟨ρ ey, ⟨ey, rfl⟩⟩ : ρ.range)
      have e : orderOf (⟨ρ ey, ⟨ey, rfl⟩⟩ : ρ.range) = 3 := by
        rw [← Subgroup.orderOf_coe]; exact hey3
      rwa [e] at h
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  have hrange_le : Nat.card ρ.range ≤ 6 := hPerm ▸ Subgroup.card_le_card_group _
  have hrange6 : Nat.card ρ.range = 6 := le_antisymm hrange_le (Nat.le_of_dvd Nat.card_pos h6)
  have hsurj : Function.Surjective ρ := by
    have : ρ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hrange6, hPerm])
    exact MonoidHom.range_eq_top.mp this
  exact hsurj.bijective_of_nat_card_le (by rw [hPerm]; exact hcardE)

theorem even_order_of_swap {Γ Ω : Type*} [Group Γ] [MulAction Γ Ω] (c : Γ) (a b : Ω)
    (hab : a ≠ b) (h1 : c • a = b) (h2 : c • b = a) (m : ℕ) (hm : Odd m) (hcm : c ^ m = 1) :
    False := by
  have hc2 : c ^ 2 • a = a := by rw [pow_two, mul_smul, h1, h2]
  have hit : ∀ k : ℕ, c ^ (2 * k) • a = a := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have : c ^ (2 * (k + 1)) = c ^ (2 * k) * c ^ 2 := by rw [← pow_add]; ring_nf
      rw [this, mul_smul, hc2, ih]
  obtain ⟨k, hk⟩ := hm
  have hcc : c = c ^ (2 * (k + 1)) := by
    have : 2 * (k + 1) = m + 1 := by omega
    rw [this, pow_succ, hcm, one_mul]
  have := hit (k + 1)
  rw [← hcc, h1] at this
  exact hab this.symm

open Pointwise in
theorem map_conj_eq_of_odd {G : Type*} [Group G] (U₁ U₂ : Subgroup G) (hne : U₁ ≠ U₂) (g : G)
    (m : ℕ) (hm : Odd m) (hgm : g ^ m = 1)
    (h1 : U₁.map (MulAut.conj g).toMonoidHom = U₁ ∨ U₁.map (MulAut.conj g).toMonoidHom = U₂)
    (h2 : U₂.map (MulAut.conj g).toMonoidHom = U₁ ∨ U₂.map (MulAut.conj g).toMonoidHom = U₂) :
    U₁.map (MulAut.conj g).toMonoidHom = U₁ ∧ U₂.map (MulAut.conj g).toMonoidHom = U₂ := by
  set c : MulAut G := MulAut.conj g with hc
  have hcm : c ^ m = 1 := by
    rw [hc, ← map_pow, hgm, map_one]
  have hsm : ∀ U : Subgroup G, c • U = U.map c.toMonoidHom := fun U => rfl
  have hinj : ∀ A B : Subgroup G, A.map c.toMonoidHom = B.map c.toMonoidHom → A = B :=
    fun A B h => Subgroup.map_injective c.injective h
  have hswap : U₁.map c.toMonoidHom = U₂ → U₂.map c.toMonoidHom = U₁ := by
    intro h
    rcases h2 with h' | h'
    · exact h'
    · exact absurd (hinj _ _ (h.trans h'.symm)) hne
  have hswap' : U₂.map c.toMonoidHom = U₁ → U₁.map c.toMonoidHom = U₂ := by
    intro h
    rcases h1 with h' | h'
    · exact absurd (hinj _ _ (h'.trans h.symm)) hne
    · exact h'
  constructor
  · rcases h1 with h | h
    · exact h
    · exact (even_order_of_swap c U₁ U₂ hne (by rw [hsm]; exact h)
        (by rw [hsm]; exact hswap h) m hm hcm).elim
  · rcases h2 with h | h
    · exact (even_order_of_swap c U₂ U₁ hne.symm (by rw [hsm]; exact h)
        (by rw [hsm]; exact hswap' h) m hm hcm).elim
    · exact h

theorem eq_one_of_fixes {V : Type*} [Group V] (V₁ V₂ : Subgroup V) (hsup : V₁ ⊔ V₂ = ⊤)
    (φ : MulAut V) (h1 : ∀ v ∈ V₁, φ v = v) (h2 : ∀ v ∈ V₂, φ v = v) : φ = 1 := by
  let F : Subgroup V :=
    { carrier := {v | φ v = v}
      one_mem' := by simp
      mul_mem' := by intro a b ha hb; simp_all
      inv_mem' := by intro a ha; simp_all }
  have hle : V₁ ⊔ V₂ ≤ F := sup_le (fun v hv => h1 v hv) (fun v hv => h2 v hv)
  ext v
  have : v ∈ F := hle (hsup ▸ Subgroup.mem_top v)
  exact this

theorem not_all_inverted {V : Type*} [Group V] [Finite V] (V₁ V₂ : Subgroup V)
    (h1 : Nat.card V₁ = 4) (hsup : V₁ ⊔ V₂ = ⊤)
    (Q : Subgroup (MulAut V)) (hQ9 : Nat.card Q = 9)
    (hQ : ∀ φ ∈ Q, ∀ v, (v ∈ V₁ ↔ φ v ∈ V₁))
    (c : MulAut V) (hc : ∀ v, v ∈ V₁ ↔ c v ∈ V₂) :
    ∃ φ ∈ Q, c * φ * c⁻¹ ≠ φ⁻¹ := by
  classical
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ3 : IsPGroup 3 Q := IsPGroup.of_card (n := 2) (by rw [hQ9]; norm_num)
  let θ₁ : Q →* Equiv.Perm V₁ :=
    { toFun := fun φ => Equiv.Perm.subtypePerm (MulAut.toPerm V φ.1)
        (fun v => (hQ φ.1 φ.2 v).symm)
      map_one' := by
        refine Equiv.ext fun x => Subtype.ext ?_
        rfl
      map_mul' := by
        intro a b
        refine Equiv.ext fun x => Subtype.ext ?_
        rfl }
  have hrange3 : IsPGroup 3 θ₁.range :=
    hQ3.of_surjective θ₁.rangeRestrict θ₁.rangeRestrict_surjective
  have hrdvd : Nat.card θ₁.range ∣ 24 := by
    have := Subgroup.card_subgroup_dvd_card θ₁.range
    rw [Nat.card_perm, h1] at this
    simpa [Nat.factorial] using this
  have hrle : Nat.card θ₁.range ≤ 3 := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 3)).mp hrange3
    rw [ha] at hrdvd ⊢
    by_contra hlt
    push Not at hlt
    have ha2 : 2 ≤ a := by
      by_contra h
      push Not at h
      interval_cases a <;> simp at hlt
    have : 3 ^ 2 ∣ 3 ^ a := pow_dvd_pow 3 ha2
    have h9 : 9 ∣ 24 := by simpa using this.trans hrdvd
    omega
  have hker : 3 ≤ Nat.card θ₁.ker := by
    have h := Subgroup.card_ker_mul_card_range θ₁
    rw [hQ9] at h
    have hpos : 0 < Nat.card θ₁.ker := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have : Nat.card θ₁.ker * Nat.card θ₁.range ≤ 2 * 3 := Nat.mul_le_mul (by omega) hrle
    omega
  have hker1 : ∃ φ ∈ θ₁.ker, φ ≠ 1 := by
    by_contra hno
    push Not at hno
    have : θ₁.ker = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro φ hφ
      exact hno φ hφ
    rw [this, Subgroup.card_bot] at hker
    omega
  obtain ⟨φ, hφ, hφ1⟩ := hker1
  apply hφ1
  have hfix1 : ∀ v ∈ V₁, φ.1 v = v := by
    intro v hv
    have := congrArg (fun p => (p ⟨v, hv⟩ : V₁).1) (MonoidHom.mem_ker.mp hφ)
    exact this
  have hfix2 : ∀ w ∈ V₂, φ.1 w = w := by
    intro w hw
    have hcw : c⁻¹ w ∈ V₁ := by
      have := (hc (c⁻¹ w)).mpr (by simpa using hw)
      exact this
    have h1' : φ.1 (c⁻¹ w) = c⁻¹ w := hfix1 _ hcw
    have hinv := hcon φ.1 φ.2
    have h3 : (c * φ.1 * c⁻¹) w = w := by
      show c (φ.1 (c⁻¹ w)) = w
      rw [h1']; simp
    rw [hinv] at h3
    have h4 : φ.1 (φ.1⁻¹ w) = φ.1 w := by rw [h3]
    simpa using h4.symm
  have := eq_one_of_fixes V₁ V₂ hsup φ.1 hfix1 hfix2
  exact Subtype.ext this

theorem nonempty_mulEquiv_semidirect {H N : Type*} [Group H] [Group N] (T R : Subgroup H) (x : H)
    (hRT : R ≤ T) (hxT : x ∈ T) (hx2 : x * x = 1) (hxR : x ∉ R) (hgen : T = R ⊔ zpowers x)
    (e : ↥R ≃* N) (β : MulAut N) (ψ : Multiplicative (ZMod 2) →* MulAut N)
    (hcomp : ∀ n : N, ((e.symm (β (ψ (Multiplicative.ofAdd 1) n)) : R) : H) =
      x * ((e.symm (β n) : R) : H) * x⁻¹) :
    Nonempty (↥T ≃* N ⋊[ψ] Multiplicative (ZMod 2)) := by
  classical
  have hcases : ∀ c : Multiplicative (ZMod 2), c = 1 ∨ c = Multiplicative.ofAdd 1 := by decide
  have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  have hsq : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide
  let xT : ↥T := ⟨x, hxT⟩
  have hxT2 : xT * xT = 1 := Subtype.ext (by simpa using hx2)
  let f₁ : N →* ↥T := (Subgroup.inclusion hRT).comp (e.symm.toMonoidHom.comp β.toMonoidHom)
  have hf₁ : ∀ n, ((f₁ n : ↥T) : H) = ((e.symm (β n) : R) : H) := fun n => rfl
  let f₂ : Multiplicative (ZMod 2) →* ↥T :=
    { toFun := fun c => if c = 1 then 1 else xT
      map_one' := by simp
      map_mul' := by
        intro a b
        rcases hcases a with rfl | rfl <;> rcases hcases b with rfl | rfl
        · simp
        · simp
        · simp
        · rw [hsq]
          simp [hne, hxT2] }
  have hf₂1 : f₂ (Multiplicative.ofAdd 1) = xT := by simp [f₂, hne]
  have hcompat : ∀ c : Multiplicative (ZMod 2),
      f₁.comp (ψ c).toMonoidHom = (MulAut.conj (f₂ c)).toMonoidHom.comp f₁ := by
    intro c
    rcases hcases c with rfl | rfl
    · ext n
      simp [f₂]
    · ext n
      have h1 := hcomp n
      show ((f₁ (ψ (Multiplicative.ofAdd 1) n) : ↥T) : H) =
        ((f₂ (Multiplicative.ofAdd 1) * f₁ n * (f₂ (Multiplicative.ofAdd 1))⁻¹ : ↥T) : H)
      rw [hf₂1, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hf₁, hf₁, h1]
  let ψ' : N ⋊[ψ] Multiplicative (ZMod 2) →* ↥T := SemidirectProduct.lift f₁ f₂ hcompat
  have happ : ∀ g : N ⋊[ψ] Multiplicative (ZMod 2), ψ' g = f₁ g.left * f₂ g.right := by
    intro g
    have : g = SemidirectProduct.inl g.left * SemidirectProduct.inr g.right := by
      cases g; exact SemidirectProduct.mk_eq_inl_mul_inr _ _
    conv_lhs => rw [this]
    rw [map_mul]
    simp [ψ']
  have hinj : Function.Injective ψ' := by
    rw [injective_iff_map_eq_one]
    intro g hg
    rw [happ] at hg
    rcases hcases g.right with hr | hr
    · rw [hr, map_one, mul_one] at hg
      have hf1 : ((e.symm (β g.left) : R) : H) = 1 := by
        have := congrArg Subtype.val hg
        simpa [hf₁] using this
      have h2 : β g.left = 1 := by
        have : (e.symm (β g.left) : R) = 1 := Subtype.ext hf1
        simpa using this
      have h3 : g.left = 1 := by simpa using h2
      ext
      · exact h3
      · exact hr
    · exfalso
      rw [hr, hf₂1] at hg
      have h1 : ((f₁ g.left : ↥T) : H) * x = 1 := by
        have := congrArg Subtype.val hg
        simpa [xT] using this
      have : x = ((f₁ g.left : ↥T) : H)⁻¹ := eq_inv_of_mul_eq_one_right h1
      apply hxR
      rw [this]
      exact R.inv_mem (by rw [hf₁]; exact (e.symm (β g.left)).2)
  have hsurj : Function.Surjective ψ' := by
    have hrange : ψ'.range = ⊤ := by
      rw [eq_top_iff]
      intro t _
      have ht : (t : H) ∈ R ⊔ zpowers x := hgen ▸ t.2
      have hle : R ⊔ zpowers x ≤ ψ'.range.map T.subtype := by
        refine sup_le (fun r hr => ?_) (Subgroup.zpowers_le.mpr ?_)
        · refine ⟨⟨r, hRT hr⟩, ⟨SemidirectProduct.inl (β.symm (e ⟨r, hr⟩)), ?_⟩, rfl⟩
          rw [SemidirectProduct.lift_inl]
          apply Subtype.ext
          simp [hf₁]
        · refine ⟨xT, ⟨SemidirectProduct.inr (Multiplicative.ofAdd 1), ?_⟩, rfl⟩
          rw [SemidirectProduct.lift_inr, hf₂1]
      obtain ⟨t', ht', htt'⟩ := hle ht
      have : t' = t := Subtype.ext htt'
      rw [← this]
      exact ht'
    exact MonoidHom.range_eq_top.mp hrange
  exact ⟨(MulEquiv.ofBijective ψ' ⟨hinj, hsurj⟩).symm⟩

@[expose] def evalT {G : Type*} [Group G] (wordOf : G → List (Fin 4)) (t : Fin 4 → G) (g : G) : G :=
  ((wordOf g).map t).prod

theorem hom_eq_evalT {G : Type*} [Group G] (gen : Fin 4 → G) (wordOf : G → List (Fin 4))
    (hw : ∀ g, ((wordOf g).map gen).prod = g) (f : G →* G) (g : G) :
    f g = evalT wordOf (fun i => f (gen i)) g := by
  conv_lhs => rw [← hw g]
  rw [map_list_prod, List.map_map]
  rfl

theorem card_filter_eq {G : Type*} [Finite G] (L : List G) (hL : ∀ g, g ∈ L) (hnd : L.Nodup)
    (p : G → Prop) [DecidablePred p] : Nat.card {g : G // p g} = (L.filter p).length := by
  classical
  have : Fintype G := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h1 : (Finset.univ : Finset G) = L.toFinset := by
    ext g; simp [hL g]
  rw [h1]
  have h2 : (L.toFinset.filter p) = (L.filter p).toFinset := by
    ext g; simp
  rw [h2, List.toFinset_card_of_nodup (hnd.filter _)]

@[expose] def IsAutT {G : Type*} [Group G] [DecidableEq G] (L : List G) (gen : Fin 4 → G)
    (wordOf : G → List (Fin 4)) (t : Fin 4 → G) : Prop :=
  (∀ g ∈ L, ∀ i, evalT wordOf t (g * gen i) = evalT wordOf t g * t i) ∧
  (∀ g ∈ L, evalT wordOf t g = 1 → g = 1)

instance {G : Type*} [Group G] [DecidableEq G] (L : List G) (gen : Fin 4 → G)
    (wordOf : G → List (Fin 4)) (t : Fin 4 → G) : Decidable (IsAutT L gen wordOf t) := by
  unfold IsAutT; infer_instance

theorem exists_autEquiv {G : Type*} [Group G] [Finite G] [DecidableEq G] (gen : Fin 4 → G)
    (wordOf : G → List (Fin 4)) (hw : ∀ g, ((wordOf g).map gen).prod = g) (h1 : wordOf 1 = [])
    (L : List G) (hL : ∀ g, g ∈ L) (t : Fin 4 → G) (ht : IsAutT L gen wordOf t) :
    ∃ β : MulAut G, ∀ g, β g = evalT wordOf t g := by
  set f : G → G := evalT wordOf t with hf
  have hstep : ∀ (w : List (Fin 4)) (g : G),
      f (g * (w.map gen).prod) = f g * (w.map t).prod := by
    intro w
    induction w with
    | nil => intro g; simp
    | cons i w ih =>
      intro g
      have h : f (g * gen i) = f g * t i := ht.1 g (hL g) i
      calc f (g * ((i :: w).map gen).prod) = f ((g * gen i) * (w.map gen).prod) := by
            simp [mul_assoc]
        _ = f (g * gen i) * (w.map t).prod := ih (g * gen i)
        _ = f g * t i * (w.map t).prod := by rw [h]
        _ = f g * ((i :: w).map t).prod := by simp [mul_assoc]
  have hmul : ∀ g h, f (g * h) = f g * f h := by
    intro g h
    have h' := hstep (wordOf h) g
    rw [hw h] at h'
    rw [h']
    rfl
  have hone : f 1 = 1 := by
    simp [hf, evalT, h1]
  let φ : G →* G := MonoidHom.mk' f hmul
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact ht.2 g (hL g) hg
  have hbij : Function.Bijective φ := hinj.bijective_of_finite
  exact ⟨MulEquiv.ofBijective φ hbij, fun g => rfl⟩

theorem exists_conj_of_check {G : Type*} [Group G] [Finite G] [DecidableEq G] (gen : Fin 4 → G)
    (wordOf : G → List (Fin 4)) (hw : ∀ g, ((wordOf g).map gen).prod = g) (h1 : wordOf 1 = [])
    (hgen : ∀ i, wordOf (gen i) = [i]) (L : List G) (hL : ∀ g, g ∈ L) (hnd : L.Nodup)
    (φ : MulAut G) (cand : List (Fin 4 → G))
    (hcand : ∀ α : MulAut G, α * α = 1 → Nat.card {g // α g = g} = 8 →
      Nat.card {g // α g = g ∧ g * g = 1} = 2 → (fun i => α (gen i)) ∈ cand)
    (key : ∀ t ∈ cand, (∀ i, evalT wordOf t (evalT wordOf t (gen i)) = gen i) →
      IsAutT L gen wordOf t →
      (L.filter (fun g => evalT wordOf t g = g)).length = 8 →
      (L.filter (fun g => evalT wordOf t g = g ∧ g * g = 1)).length = 2 →
      ∃ s : Fin 4 → G, IsAutT L gen wordOf s ∧
        ∀ i, evalT wordOf s (φ (gen i)) = evalT wordOf t (s i)) :
    ∀ α : MulAut G, α * α = 1 → Nat.card {g // α g = g} = 8 →
      Nat.card {g // α g = g ∧ g * g = 1} = 2 → ∃ β : MulAut G, β * φ = α * β := by
  intro α hα hfix hfix2
  set t : Fin 4 → G := fun i => α (gen i) with ht
  have hteval : ∀ g, evalT wordOf t g = α g := fun g =>
    (hom_eq_evalT gen wordOf hw α.toMonoidHom g).symm
  have htmem := hcand α hα hfix hfix2
  have hAut : IsAutT L gen wordOf t := by
    refine ⟨fun g _ i => ?_, fun g _ hg => ?_⟩
    · rw [hteval, hteval, map_mul]
    · rw [hteval] at hg
      exact (map_eq_one_iff α α.injective).mp hg
  have hinv : ∀ g ∈ L, evalT wordOf t (evalT wordOf t g) = g := by
    intro g _
    rw [hteval, hteval]
    have := congrArg (fun m : MulAut G => m g) hα
    simpa using this
  have hlen : (L.filter (fun g => evalT wordOf t g = g)).length = 8 := by
    rw [← card_filter_eq L hL hnd]
    · simp only [hteval]
      exact hfix
  have hlen2 : (L.filter (fun g => evalT wordOf t g = g ∧ g * g = 1)).length = 2 := by
    rw [← card_filter_eq L hL hnd (fun g => evalT wordOf t g = g ∧ g * g = 1)]
    · simp only [hteval]
      exact hfix2
  obtain ⟨s, hsAut, hconj⟩ := key t htmem (fun i => hinv _ (hL _)) hAut hlen hlen2
  obtain ⟨β, hβ⟩ := exists_autEquiv gen wordOf hw h1 L hL s hsAut
  refine ⟨β, ?_⟩
  have hgens : ∀ i, (β * φ) (gen i) = (α * β) (gen i) := by
    intro i
    have e1 : (β * φ) (gen i) = evalT wordOf s (φ (gen i)) := by
      rw [MulAut.mul_apply, hβ]
    have e2 : (α * β) (gen i) = evalT wordOf t (s i) := by
      rw [MulAut.mul_apply, hβ, ← hteval]
      simp [evalT, hgen]
    rw [e1, e2]
    exact hconj i
  ext g
  have a1 := hom_eq_evalT gen wordOf hw (β * φ).toMonoidHom g
  have a2 := hom_eq_evalT gen wordOf hw (α * β).toMonoidHom g
  have : (fun i => (β * φ).toMonoidHom (gen i)) = (fun i => (α * β).toMonoidHom (gen i)) := by
    funext i; exact hgens i
  rw [this] at a1
  exact a1.trans a2.symm

end CFSG.GH74.Uniqueness.SU.K.R4.Q64
