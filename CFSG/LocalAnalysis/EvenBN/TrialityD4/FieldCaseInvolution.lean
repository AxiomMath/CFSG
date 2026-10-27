module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.FieldCaseSylow
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.FieldCasePSL3
import CFSG.GH74.Uniqueness.SU.SU2Sem
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem exists_field_involution (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hfe : Even f) (X : Subgroup G) (hXC : X ≤ centralizer ({t} : Set G)) (htX : t ∈ X)
    (hXL : X ⊓ (L ⊔ zpowers t) = zpowers t) (hX2 : IsPGroup 2 X)
    (hXφ : ∀ x : centralizer ({t} : Set G), (x : G) ∈ X → ∃ k : ℕ, h.act x = d.φ ^ k)
    (hnc : ¬ ∃ x ∈ X, X = zpowers x) :
    ∃ σ : centralizer ({t} : Set G), (σ : G) ∈ X ∧ (σ : G) * σ = 1 ∧ (σ : G) ∉ zpowers t ∧
      h.act σ = d.φ ^ (3 * f / 2) := by
  classical
  obtain ⟨-, x, hxX, hXx⟩ := fieldTwo_abelian_cyclic h d hXC htX hXL
  have htx : t ∉ zpowers x := by
    intro htx
    apply hnc
    refine ⟨x, hxX, le_antisymm ?_ ((zpowers_le).2 hxX)⟩
    rw [hXx]
    exact sup_le ((zpowers_le).2 htx) le_rfl
  obtain ⟨b, hb⟩ : ∃ b : ℕ, orderOf x = 2 ^ b := by
    obtain ⟨n, hn⟩ := hX2 ⟨x, hxX⟩
    have hdvd : orderOf x ∣ 2 ^ n :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hn)
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨b, hb⟩
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · exfalso
      rw [h0, pow_zero, orderOf_eq_one_iff] at hb
      apply hnc
      refine ⟨t, htX, le_antisymm ?_ ((zpowers_le).2 htX)⟩
      rw [hXx, hb]
      simp
    · exact h0
  set σ0 : G := x ^ 2 ^ (b - 1) with hσ0
  have hσX : σ0 ∈ X := pow_mem hxX _
  have hσ2 : σ0 * σ0 = 1 := by
    rw [hσ0, ← pow_add, ← two_mul, ← pow_succ' 2 (b - 1), Nat.sub_add_cancel hb1,
      ← hb, pow_orderOf_eq_one]
  have hσ1 : σ0 ≠ 1 := by
    refine pow_ne_one_of_lt_orderOf (by positivity) ?_
    rw [hb]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hσt : σ0 ∉ zpowers t := by
    intro hσt
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hσt
    rcases h.zpow_eq_one_or_eq k with h1 | h1
    · exact hσ1 (by rw [← hk, h1])
    · apply htx
      rw [h1] at hk
      rw [hk]
      exact pow_mem (mem_zpowers x) _
  set σ : centralizer ({t} : Set G) := ⟨σ0, hXC hσX⟩ with hσ
  have hσσ : σ * σ = 1 := Subtype.ext hσ2
  obtain ⟨k, hk⟩ := hXφ σ hσX
  have hord := d.orderOf_φ_eq_three_mul (q := 2 ^ f) (f := f) rfl
  have hk2 : d.φ ^ (k * 2) = 1 := by
    have : h.act σ * h.act σ = 1 := by rw [← map_mul, hσσ, map_one]
    rw [hk, ← pow_add, ← two_mul, mul_comm] at this
    exact this
  have hk1 : d.φ ^ k ≠ 1 := by
    intro hk1
    rw [hk1] at hk
    have hmem : (σ0 : G) ∈ centralizer (L : Set G) := (h.act_eq_one_iff σ).1 hk
    apply hσt
    rw [← h.centralizer_L_inf_of_data d]
    exact ⟨hmem, hXC hσX⟩
  have hdvd : 3 * f ∣ k * 2 := hord ▸ orderOf_dvd_of_pow_eq_one hk2
  have hndvd : ¬ 3 * f ∣ k := fun hh => hk1 (orderOf_dvd_iff_pow_eq_one.1 (hord ▸ hh))
  refine ⟨σ, hσX, hσ2, hσt, ?_⟩
  obtain ⟨e, rfl⟩ := hfe
  have h3e : 3 * e ∣ k := by
    have : 3 * e * 2 ∣ k * 2 := by
      rw [show 3 * e * 2 = 3 * (e + e) by ring]
      exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_right two_pos this
  obtain ⟨m, rfl⟩ := h3e
  have hm : Odd m := by
    by_contra hm
    rw [Nat.not_odd_iff_even] at hm
    obtain ⟨j, rfl⟩ := hm
    exact hndvd ⟨j, by ring⟩
  obtain ⟨j, rfl⟩ := hm
  have h6 : d.φ ^ (3 * (e + e)) = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  rw [hk, show 3 * (e + e) / 2 = 3 * e by omega,
    show 3 * e * (2 * j + 1) = 3 * (e + e) * j + 3 * e by ring, pow_add, pow_mul, h6, one_pow,
    one_mul]

@[expose] def LayerHypFieldAlt (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) : Prop :=
  ∃ Kc : Subgroup (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
      CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))),
    CFSG.IsComponent Kc ∧
    Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
          ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom = Kc ∧
    CFSG.Blueprint.LieModel Kc .PSL 3 2 (2 * f)

theorem sq_eq_one_of_mem_closure_commuting_pair {B : Type*} [Group B] (a b : B) (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) :
    ∀ x ∈ Subgroup.closure ({a, b} : Set B), x * x = 1 := by
  have hcomm : ∀ x ∈ Subgroup.closure ({a, b} : Set B), ∀ y ∈ Subgroup.closure ({a, b} : Set B),
      Commute x y := by
    intro x hx y hy
    refine Subgroup.closure_induction₂ (p := fun x y _ _ => Commute x y) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
    · intro x y hx hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact Commute.refl _
      · exact hab
      · exact hab.symm
      · exact Commute.refl _
    · intro x hx
      exact Commute.one_left x
    · intro x hx
      exact Commute.one_right x
    · intro x y z hx hy hz h1 h2
      exact h1.mul_left h2
    · intro y z x hy hz hx h1 h2
      exact h1.mul_right h2
    · intro x y hx hy h
      exact h.inv_left
    · intro x y hx hy h
      exact h.inv_right
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  | one => simp
  | mul x y hx hy hxx hyy =>
    have hyx : y * x = x * y := (hcomm y hy x hx).eq
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hyx]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hxx, hyy, one_mul]
  | inv x hx h =>
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by rw [mul_inv_rev]
      _ = 1 := by rw [h, inv_one]

theorem fixed_of_normalizing_involutions {Q : Type} [Group Q] [Finite Q]
    (hcomm : ∀ x y : Q, x * y = y * x) (hsq : ∀ x : Q, x * x = 1)
    (Γ : Subgroup (MulAut Q)) (hΓc : ∀ a ∈ Γ, ∀ b ∈ Γ, a * b = b * a)
    (hΓt : ∀ v w : Q, v ≠ 1 → w ≠ 1 → ∃ g ∈ Γ, g v = w)
    (a b : MulAut Q) (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a)
    (haΓ : a ∈ Subgroup.normalizer (Γ : Set (MulAut Q)))
    (hbΓ : b ∈ Subgroup.normalizer (Γ : Set (MulAut Q)))
    (ha1 : ∃ z, a z ≠ z) : ∀ z, a z = z → b z = z := by
  classical
  letI : CommGroup Q := { ‹Group Q› with mul_comm := hcomm }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 Q := fun q => ⟨1, by simpa [pow_two] using hsq q⟩
  obtain ⟨e, he⟩ := (IsPGroup.iff_card (p := 2)).1 hP
  obtain ⟨z0, hz0⟩ := ha1
  have hz01 : z0 ≠ 1 := by
    rintro rfl
    exact hz0 (map_one a)
  have he1 : 1 ≤ e := by
    by_contra h
    have h0 : e = 0 := by omega
    rw [h0, pow_zero] at he
    have : Subsingleton Q := (Nat.card_eq_one_iff_unique.1 he).1
    exact hz01 (Subsingleton.elim _ _)
  have hreg : Nat.card Γ + 1 = Nat.card Q := by
    have hpt : ∀ g : Γ, g.1 z0 ≠ 1 := fun g h => hz01 (g.1.injective (by rw [h, map_one]))
    let φ : Γ → {v : Q // v ≠ 1} := fun g => ⟨g.1 z0, hpt g⟩
    have hφinj : Function.Injective φ := by
      intro g g' h
      have h' : g.1 z0 = g'.1 z0 := congrArg Subtype.val h
      apply Subtype.ext
      apply MulEquiv.ext
      intro v
      by_cases hv : v = 1
      · rw [hv, map_one, map_one]
      · obtain ⟨d, hd, hdz⟩ := hΓt z0 v hz01 hv
        have e1 : g.1 (d z0) = d (g.1 z0) := DFunLike.congr_fun (hΓc g.1 g.2 d hd) z0
        have e2 : g'.1 (d z0) = d (g'.1 z0) := DFunLike.congr_fun (hΓc g'.1 g'.2 d hd) z0
        rw [← hdz, e1, e2, h']
    have hφsurj : Function.Surjective φ := by
      rintro ⟨v, hv⟩
      obtain ⟨d, hd, hdz⟩ := hΓt z0 v hz01 hv
      exact ⟨⟨d, hd⟩, Subtype.ext hdz⟩
    have h1 : Nat.card Γ = Nat.card {v : Q // v ≠ 1} :=
      Nat.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩)
    rw [h1]
    have := Fintype.ofFinite Q
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp only [Fintype.card_subtype_eq]
    have : 0 < Fintype.card Q := Fintype.card_pos
    omega
  let Nm : Subgroup (MulAut Q) := Subgroup.normalizer (Γ : Set (MulAut Q))
  let ρ : Nm →* MulAut Q := Nm.subtype
  let E : Subgroup Nm := Γ.subgroupOf Nm
  have hEn : E.Normal := Subgroup.normal_in_normalizer
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => Subtype.ext (hΓc x.1 hx y.1 hy)
  have hEtr : ∀ v w : Q, v ≠ 1 → w ≠ 1 → ∃ x ∈ E, ρ x v = w := by
    intro v w hv hw
    obtain ⟨g, hg, hgv⟩ := hΓt v w hv hw
    exact ⟨⟨g, Subgroup.le_normalizer hg⟩, hg, hgv⟩
  have hfaith : ∀ t : Nm, (∀ v, ρ t v = v) → t = 1 := by
    intro t ht
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    exact ht v
  have hEcard : Nat.card E + 1 = Nat.card Q := by
    rw [← hreg]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := Γ))).toEquiv
  let a' : Nm := ⟨a, haΓ⟩
  let b' : Nm := ⟨b, hbΓ⟩
  have ha2' : a' * a' = 1 := Subtype.ext ha2
  have hb2' : b' * b' = 1 := Subtype.ext hb2
  have hab' : a' * b' = b' * a' := Subtype.ext hab
  let T : Subgroup Nm := Subgroup.closure {a', b'}
  have hT : IsPGroup 2 T := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have := sq_eq_one_of_mem_closure_commuting_pair a' b' ha2' hb2' hab' x x.2
    simpa [pow_two] using this
  have hcyc : IsCyclic T :=
    CFSG.GH74.Uniqueness.SU.SU2.Sem.isCyclic_of_isPGroup_faithful hsq ρ hEc hEtr
      (fun x _ hx => hfaith x hx) hEcard he he1 hT (fun t _ ht => hfaith t ht)
  intro z hz
  have hamem : a' ∈ T := Subgroup.subset_closure (by simp)
  have hbmem : b' ∈ T := Subgroup.subset_closure (by simp)
  let A : T := ⟨a', hamem⟩
  let Bb : T := ⟨b', hbmem⟩
  have hA1 : A ≠ 1 := by
    intro h
    apply hz0
    have h1 : a' = 1 := congrArg Subtype.val h
    have h2 : a = 1 := congrArg Subtype.val h1
    rw [h2]
    rfl
  by_cases hB1 : Bb = 1
  · have h1 : b' = 1 := congrArg Subtype.val hB1
    have h2 : b = 1 := congrArg Subtype.val h1
    rw [h2]
    rfl
  · have hAB : A = Bb :=
      CFSG.LocalAnalysis.EvenBN.Common.eq_of_mul_self_eq_one_of_isCyclic hA1 hB1
        (Subtype.ext ha2') (Subtype.ext hb2')
    have h1 : a' = b' := congrArg Subtype.val hAB
    have h2 : a = b := congrArg Subtype.val h1
    rw [← h2]
    exact hz

theorem fixed_of_semilinear_involutions {M : Type} [Group M] [Finite M] {Z N : Subgroup M}
    (hZsq : ∀ z ∈ Z, z * z = 1) (hNZ : N ≤ normalizer (Z : Set M))
    (hNab : ∀ g ∈ N, ∀ g' ∈ N, ∀ z ∈ Z, g * (g' * z * g'⁻¹) * g⁻¹ = g' * (g * z * g⁻¹) * g'⁻¹)
    (hNtr : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ 1 → z' ≠ 1 → ∃ g ∈ N, g * z * g⁻¹ = z')
    (τ σ : MulAut M) (hτ2 : τ * τ = 1) (hσ2 : σ * σ = 1) (hτσ : τ * σ = σ * τ)
    (hτN : N.map τ.toMonoidHom = N) (hσN : N.map σ.toMonoidHom = N)
    (hτZ : Z.map τ.toMonoidHom = Z) (hσZ : Z.map σ.toMonoidHom = Z)
    (hτ1 : ∃ z ∈ Z, τ z ≠ z) :
    ∀ z ∈ Z, τ z = z → σ z = z := by
  classical
  have hZsq' : ∀ x : ↥Z, x * x = 1 := fun x => Subtype.ext (hZsq x x.2)
  have hZc : ∀ x y : ↥Z, x * y = y * x := by
    intro x y
    apply Subtype.ext
    have hx : (x : M) * x = 1 := hZsq _ x.2
    have hy : (y : M) * y = 1 := hZsq _ y.2
    have hxy : ((x : M) * y) * ((x : M) * y) = 1 := hZsq _ (Z.mul_mem x.2 y.2)
    have hx' : (x : M)⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    have hy' : (y : M)⁻¹ = y := inv_eq_of_mul_eq_one_right hy
    have hxy' : ((x : M) * y)⁻¹ = (x : M) * y := inv_eq_of_mul_eq_one_right hxy
    calc (x : M) * y = ((x : M) * y)⁻¹ := hxy'.symm
      _ = y * x := by rw [mul_inv_rev, hx', hy']
  let res : ∀ θ : MulAut M, Z.map θ.toMonoidHom = Z → MulAut ↥Z := fun θ h =>
    (θ.subgroupMap Z).trans (MulEquiv.subgroupCongr h)
  let ρN : ↥N →* MulAut ↥Z := Z.normalizerMonoidHom.comp (Subgroup.inclusion hNZ)
  let Γ : Subgroup (MulAut ↥Z) := ρN.range
  have hΓc : ∀ a ∈ Γ, ∀ b ∈ Γ, a * b = b * a := by
    rintro _ ⟨n, rfl⟩ _ ⟨n', rfl⟩
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    exact hNab n n.2 n' n'.2 z z.2
  have hΓt : ∀ v w : ↥Z, v ≠ 1 → w ≠ 1 → ∃ g ∈ Γ, g v = w := by
    intro v w hv hw
    obtain ⟨n, hn, hnv⟩ :=
      hNtr v v.2 w w.2 (fun h => hv (Subtype.ext h)) (fun h => hw (Subtype.ext h))
    exact ⟨ρN ⟨n, hn⟩, ⟨⟨n, hn⟩, rfl⟩, Subtype.ext hnv⟩
  have hnorm : ∀ (θ : MulAut M) (hθZ : Z.map θ.toMonoidHom = Z) (hθN : N.map θ.toMonoidHom = N),
      θ * θ = 1 → res θ hθZ ∈ normalizer (Γ : Set (MulAut ↥Z)) := by
    intro θ hθZ hθN hθ2
    have hθθ : ∀ m : M, θ (θ m) = m := fun m => DFunLike.congr_fun hθ2 m
    have hθN' : ∀ n : ↥N, θ n ∈ N := by
      intro n
      have : θ n ∈ N.map θ.toMonoidHom := Subgroup.mem_map_of_mem θ.toMonoidHom n.2
      rwa [hθN] at this
    have hrr : res θ hθZ * res θ hθZ = 1 := MulEquiv.ext fun z => Subtype.ext (hθθ z)
    have hinv : (res θ hθZ)⁻¹ = res θ hθZ := inv_eq_of_mul_eq_one_right hrr
    have key : ∀ n : ↥N, res θ hθZ * ρN n * (res θ hθZ)⁻¹ = ρN ⟨θ n, hθN' n⟩ := by
      intro n
      rw [hinv]
      apply MulEquiv.ext
      intro z
      apply Subtype.ext
      show θ ((n : M) * θ z * (n : M)⁻¹) = θ n * z * (θ n)⁻¹
      rw [map_mul, map_mul, map_inv, hθθ]
    have hfwd : ∀ h ∈ Γ, res θ hθZ * h * (res θ hθZ)⁻¹ ∈ Γ := by
      rintro _ ⟨n, rfl⟩
      rw [key n]
      exact ⟨_, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hfwd h, fun hh => ?_⟩
    have h1 := hfwd _ hh
    rw [hinv] at h1
    have e : res θ hθZ * (res θ hθZ * h * res θ hθZ) * res θ hθZ = h := by
      calc res θ hθZ * (res θ hθZ * h * res θ hθZ) * res θ hθZ
          = (res θ hθZ * res θ hθZ) * h * (res θ hθZ * res θ hθZ) := by group
        _ = h := by rw [hrr]; simp
    rwa [e] at h1
  have haΓ := hnorm τ hτZ hτN hτ2
  have hbΓ := hnorm σ hσZ hσN hσ2
  have ha2 : res τ hτZ * res τ hτZ = 1 :=
    MulEquiv.ext fun z => Subtype.ext (DFunLike.congr_fun hτ2 (z : M))
  have hb2 : res σ hσZ * res σ hσZ = 1 :=
    MulEquiv.ext fun z => Subtype.ext (DFunLike.congr_fun hσ2 (z : M))
  have hab : res τ hτZ * res σ hσZ = res σ hσZ * res τ hτZ :=
    MulEquiv.ext fun z => Subtype.ext (DFunLike.congr_fun hτσ (z : M))
  have ha1 : ∃ z : ↥Z, res τ hτZ z ≠ z := by
    obtain ⟨z, hz, hne⟩ := hτ1
    exact ⟨⟨z, hz⟩, fun h => hne (congrArg Subtype.val h)⟩
  intro z hz hτz
  have := fixed_of_normalizing_involutions hZc hZsq' Γ hΓc hΓt (res τ hτZ) (res σ hσZ) ha2 hb2
    hab haΓ hbΓ ha1 ⟨z, hz⟩ (Subtype.ext hτz)
  exact congrArg Subtype.val this

namespace FieldInvolutionAux

theorem map_eq_self_of_forall_mem {M : Type*} [Group M] [Finite M] (α : MulAut M)
    {A : Subgroup M} (h : ∀ x ∈ A, α x ∈ A) : A.map α.toMonoidHom = A :=
  Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)
    (by rw [Subgroup.card_map_of_injective α.injective])

theorem exists_isSylowOf_le {M : Type*} [Group M] [Finite M] {N A : Subgroup M}
    (hA : IsPGroup 2 A) (hAN : A ≤ N) : ∃ T : Subgroup M, IsSylowOf 2 T N ∧ A ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨B₀, hB₀⟩ := (hA.comap_subtype (K := N)).exists_le_sylow
  exact ⟨B₀.map N.subtype, ⟨B₀, rfl⟩, fun x hx => ⟨⟨x, hAN hx⟩, hB₀ (mem_subgroupOf.2 hx), rfl⟩⟩

theorem oddCore_inj {Y : Type*} [Group Y] [Finite Y] {X : Subgroup Y} (hX : IsPGroup 2 X) :
    ∀ x ∈ X, QuotientGroup.mk' (CFSG.oddCore Y) x = 1 → x = 1 := by
  intro x hx hπx
  have hxO : x ∈ CFSG.oddCore Y := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hπx
    exact hπx
  obtain ⟨k, hk⟩ := hX ⟨x, hx⟩
  exact eq_one_of_mem_oddCore_of_pow_D4 hxO (k := k) (by
    have := congrArg Subtype.val hk
    simpa using this)

theorem isSylowOf_map_oddCore {Y : Type*} [Group Y] [Finite Y] {E X : Subgroup Y}
    (hX : IsSylowOf 2 X E) :
    IsSylowOf 2 (X.map (QuotientGroup.mk' (CFSG.oddCore Y)))
      (E.map (QuotientGroup.mk' (CFSG.oddCore Y))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.oddCore Y with hO
  set π := QuotientGroup.mk' O with hπ
  have hinj : ∀ x ∈ X, π x = 1 → x = 1 := oddCore_inj hX.isPGroup
  refine CFSG.ABGLocalTools.isSylowOf_of_card (map_mono hX.le) ?_
  rw [card_map_of_injOn_D4 π hinj le_rfl, hX.card_eq]
  have hk := Subgroup.card_ker_mul_card_range (π.domRestrict E)
  rw [MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict, hπ, QuotientGroup.ker_mk'] at hk
  have hodd : Odd (Nat.card (O.subgroupOf E)) := by
    have e : Nat.card (O.subgroupOf E) = Nat.card (O ⊓ E : Subgroup Y) := by
      rw [← subgroupOf_map_subtype, card_map_of_injective E.subtype_injective]
    rw [e]
    exact Odd.of_dvd_nat (CFSG.LocalAnalysis.ComponentInitial.OddNormalCore.odd_card_oddCore Y)
      (card_dvd_of_le inf_le_left)
  rw [← hk, factorization_two_mul_of_odd_D4 hodd Nat.card_pos.ne']

theorem preserve {M : Type*} [Group M] [Finite M] (α : MulAut M) {Kc T' : Subgroup M}
    (hKc : ∀ x ∈ Kc, α x ∈ Kc) (hT : ∀ x ∈ T', α x ∈ T') :
    (Kc ⊓ normalizer (T' : Set M)).map α.toMonoidHom = Kc ⊓ normalizer (T' : Set M) ∧
    (T' ⊓ centralizer (T' : Set M)).map α.toMonoidHom = T' ⊓ centralizer (T' : Set M) := by
  have hT' : T'.map α.toMonoidHom = T' := map_eq_self_of_forall_mem α hT
  have hpre : ∀ x ∈ T', ∃ y ∈ T', α y = x := fun x hx => by
    have : x ∈ T'.map α.toMonoidHom := by rw [hT']; exact hx
    obtain ⟨y, hy, hyx⟩ := this
    exact ⟨y, hy, hyx⟩
  refine ⟨map_eq_self_of_forall_mem α fun g hg =>
      ⟨hKc g hg.1, mem_normalizer_fintype fun x hx => ?_⟩,
    map_eq_self_of_forall_mem α fun z hz => ⟨hT z hz.1, mem_centralizer_iff.2 fun x hx => ?_⟩⟩
  · obtain ⟨y, hy, rfl⟩ := hpre x hx
    have h1 : g * y * g⁻¹ ∈ T' := (mem_normalizer_iff.1 hg.2 y).1 hy
    have h2 := hT _ h1
    simpa using h2
  · obtain ⟨y, hy, rfl⟩ := hpre x hx
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hz.2 y hy]

theorem k3_ambient {M : Type} [Group M] [Finite M]
    {Kc T' : Subgroup M} {m : ℕ} (hlie : CFSG.Blueprint.LieModel Kc .PSL 3 2 m)
    (hT : IsSylowOf 2 T' Kc) :
    (∀ g ∈ Kc ⊓ normalizer (T' : Set M), ∀ g' ∈ Kc ⊓ normalizer (T' : Set M),
      ∀ z ∈ T' ⊓ centralizer (T' : Set M),
        g * (g' * z * g'⁻¹) * g⁻¹ = g' * (g * z * g⁻¹) * g'⁻¹) ∧
    (∀ z ∈ T' ⊓ centralizer (T' : Set M), ∀ z' ∈ T' ⊓ centralizer (T' : Set M), z ≠ 1 → z' ≠ 1 →
      ∃ g ∈ Kc ⊓ normalizer (T' : Set M), g * z * g⁻¹ = z') := by
  have hK3 := pslThreeSylowCenterAction
  obtain ⟨T, hTeq⟩ := hT.exists_sylow_eq_subgroupOf
  obtain ⟨-, hab, htr⟩ := hK3 ↥Kc m hlie T
  have hTK : T' ≤ Kc := hT.le
  have hmemT : ∀ x : Kc, x ∈ (T : Subgroup Kc) ↔ (x : M) ∈ T' := fun x => by
    rw [hTeq, mem_subgroupOf]
  have hn1 : ∀ (g : M) (hg : g ∈ Kc), g ∈ normalizer (T' : Set M) →
      (⟨g, hg⟩ : Kc) ∈ normalizer ((T : Subgroup Kc) : Set Kc) := by
    intro g hg hgN
    refine mem_normalizer_fintype fun x hx => ?_
    rw [SetLike.mem_coe, hmemT] at hx ⊢
    exact (mem_normalizer_iff.1 hgN _).1 hx
  have hn2 : ∀ g : Kc, g ∈ normalizer ((T : Subgroup Kc) : Set Kc) →
      (g : M) ∈ normalizer (T' : Set M) := by
    intro g hg
    refine mem_normalizer_fintype fun x hx => ?_
    have := (mem_normalizer_iff.1 hg ⟨x, hTK hx⟩).1 ((hmemT _).2 hx)
    exact (hmemT _).1 this
  have hz1 : ∀ z ∈ T' ⊓ centralizer (T' : Set M), ∃ hz : z ∈ Kc, (⟨z, hz⟩ : Kc) ∈
      (T : Subgroup Kc) ⊓ centralizer ((T : Subgroup Kc) : Set Kc) := by
    intro z hz
    refine ⟨hTK hz.1, (hmemT _).2 hz.1, mem_centralizer_iff.2 fun x hx => Subtype.ext ?_⟩
    exact mem_centralizer_iff.1 hz.2 _ ((hmemT x).1 hx)
  refine ⟨fun g hg g' hg' z hz => ?_, fun z hz z' hz' hz1' hz1'' => ?_⟩
  · obtain ⟨hzK, hzT⟩ := hz1 z hz
    exact congrArg Subtype.val (hab ⟨g, hg.1⟩ (hn1 g hg.1 hg.2) ⟨g', hg'.1⟩
      (hn1 g' hg'.1 hg'.2) ⟨z, hzK⟩ hzT)
  · obtain ⟨hzK, hzT⟩ := hz1 z hz
    obtain ⟨hzK', hzT'⟩ := hz1 z' hz'
    obtain ⟨g, hg, hgz⟩ := htr ⟨z, hzK⟩ hzT ⟨z', hzK'⟩ hzT'
      (fun e => hz1' (congrArg Subtype.val e)) (fun e => hz1'' (congrArg Subtype.val e))
    exact ⟨g, ⟨g.2, hn2 g hg⟩, congrArg Subtype.val hgz⟩

theorem abstract_core
    {Y : Type} [Group Y] [Finite Y] {m : ℕ}
    {E X : Subgroup Y} {Kc : Subgroup (Y ⧸ CFSG.oddCore Y)} {s : Y} (hs : s * s = 1)
    (hX : IsSylowOf 2 X E)
    (hEmap : E.map (QuotientGroup.mk' (CFSG.oddCore Y)) = Kc)
    (hlie : CFSG.Blueprint.LieModel Kc .PSL 3 2 m)
    (hsX : s ∈ normalizer (X : Set Y))
    (hKs : Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore Y) s)).toMonoidHom = Kc)
    (ψ : MulAut Y) (σb : MulAut (Y ⧸ CFSG.oddCore Y))
    (hσπ : ∀ y, σb (QuotientGroup.mk' (CFSG.oddCore Y) y) =
      QuotientGroup.mk' (CFSG.oddCore Y) (ψ y))
    (hψ2 : ψ * ψ = 1) (hψs : ψ s = s) (hσKc : Kc.map σb.toMonoidHom = Kc)
    (hψX : ∀ x ∈ X, ψ x ∈ X)
    (hZ2 : ∀ z ∈ X ⊓ centralizer (X : Set Y), z * z = 1)
    (hZs : ∃ z ∈ X ⊓ centralizer (X : Set Y), s * z * s⁻¹ ≠ z) :
    ∀ z ∈ X ⊓ centralizer (X : Set Y), s * z * s⁻¹ = z → ψ z = z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.oddCore Y with hO
  set π := QuotientGroup.mk' O with hπ
  set c := π s with hc
  set T' := X.map π with hT'
  have hinj : ∀ x ∈ X, π x = 1 → x = 1 := oddCore_inj hX.isPGroup
  have hsyl : IsSylowOf 2 T' Kc := hEmap ▸ isSylowOf_map_oddCore hX
  have hc2 : c * c = 1 := by rw [hc, ← map_mul, hs, map_one]
  set τ : MulAut (Y ⧸ O) := MulAut.conj c with hτ
  have hτπ : ∀ y, τ (π y) = π (s * y * s⁻¹) := fun y => by
    rw [hτ, MulAut.conj_apply, hc, map_mul, map_mul, map_inv]
  have hτ2 : τ * τ = 1 := by
    rw [hτ, ← map_mul, hc2, map_one]
  have hψψ : ∀ y, ψ (ψ y) = y := fun y => by
    have := congrArg (fun a : MulAut Y => a y) hψ2
    simpa using this
  have hσ2 : σb * σb = 1 := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    show σb (σb (π y)) = π y
    rw [hσπ, hσπ, hψψ]
  have hψc : ∀ y, ψ (s * y * s⁻¹) = s * ψ y * s⁻¹ := fun y => by
    rw [map_mul, map_mul, map_inv, hψs]
  have hτσ : τ * σb = σb * τ := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    show τ (σb (π y)) = σb (τ (π y))
    rw [hσπ, hτπ, hτπ, hσπ, hψc]
  have hKcτ : ∀ x ∈ Kc, τ x ∈ Kc := fun x hx => hKs ▸ ⟨x, hx, rfl⟩
  have hKcσ : ∀ x ∈ Kc, σb x ∈ Kc := fun x hx => hσKc ▸ ⟨x, hx, rfl⟩
  have hT'τ : ∀ x ∈ T', τ x ∈ T' := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hτπ]
    exact ⟨_, (mem_normalizer_iff.1 hsX y).1 hy, rfl⟩
  have hT'σ : ∀ x ∈ T', σb x ∈ T' := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hσπ]
    exact ⟨_, hψX y hy, rfl⟩
  obtain ⟨hNτ, hZτ⟩ := preserve τ hKcτ hT'τ
  obtain ⟨hNσ, hZσ⟩ := preserve σb hKcσ hT'σ
  obtain ⟨hab, htr⟩ := k3_ambient hlie hsyl
  have hZmem : ∀ z ∈ T' ⊓ centralizer (T' : Set (Y ⧸ O)),
      ∃ x ∈ X ⊓ centralizer (X : Set Y), π x = z := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz.1
    exact ⟨x, (map_mem_center_iff_D4 π hinj hx).1 hz, rfl⟩
  have hZmem' : ∀ x ∈ X ⊓ centralizer (X : Set Y),
      π x ∈ T' ⊓ centralizer (T' : Set (Y ⧸ O)) := fun x hx =>
    (map_mem_center_iff_D4 π hinj hx.1).2 hx
  have key := fixed_of_semilinear_involutions
    (Z := T' ⊓ centralizer (T' : Set (Y ⧸ O))) (N := Kc ⊓ normalizer (T' : Set (Y ⧸ O)))
    (fun z hz => by
      obtain ⟨x, hx, rfl⟩ := hZmem z hz
      rw [← map_mul, hZ2 x hx, map_one])
    (fun g hg => mem_normalizer_inf_D4 hg.2 (mem_normalizer_centralizer_D4 hg.2))
    hab htr τ σb hτ2 hσ2 hτσ hNτ hNσ hZτ hZσ (by
      obtain ⟨z, hz, hne⟩ := hZs
      refine ⟨π z, hZmem' z hz, fun e => hne ?_⟩
      rw [hτπ] at e
      exact eq_of_map_eq_D4 π hinj ((mem_normalizer_iff.1 hsX z).1 hz.1) hz.1 e)
  intro z hz hzt
  have h1 : τ (π z) = π z := by rw [hτπ, hzt]
  have h2 := key (π z) (hZmem' z hz) h1
  rw [hσπ] at h2
  exact eq_of_map_eq_D4 π hinj (hψX z hz.1) hz.1 h2

theorem abstract_core_of_components
    {Y : Type} [Group Y] [Finite Y] {m : ℕ}
    {E X : Subgroup Y} {Kc₀ Kc : Subgroup (Y ⧸ CFSG.oddCore Y)} {s : Y} (hs : s * s = 1)
    (hX : IsSylowOf 2 X E)
    (hEmap : E.map (QuotientGroup.mk' (CFSG.oddCore Y)) =
      Kc₀ ⊔ Kc₀.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore Y) s)).toMonoidHom)
    (hcomp : ∀ C : Subgroup (Y ⧸ CFSG.oddCore Y), CFSG.IsComponent C →
      C = Kc₀ ∨ C = Kc₀.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore Y) s)).toMonoidHom)
    (hKc : CFSG.IsComponent Kc)
    (hKct : Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore Y) s)).toMonoidHom = Kc)
    (hlie : CFSG.Blueprint.LieModel Kc .PSL 3 2 m)
    (hsX : s ∈ normalizer (X : Set Y))
    (ψ : MulAut Y) (hψ2 : ψ * ψ = 1) (hψs : ψ s = s) (hψX : ∀ x ∈ X, ψ x ∈ X)
    (hZ2 : ∀ z ∈ X ⊓ centralizer (X : Set Y), z * z = 1)
    (hZs : ∃ z ∈ X ⊓ centralizer (X : Set Y), s * z * s⁻¹ ≠ z) :
    ∀ z ∈ X ⊓ centralizer (X : Set Y), s * z * s⁻¹ = z → ψ z = z := by
  classical
  set O := CFSG.oddCore Y with hO
  set π := QuotientGroup.mk' O with hπ
  set c := π s with hc
  have hc2 : c * c = 1 := by rw [hc, ← map_mul, hs, map_one]
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hcconj : ∀ y : Y ⧸ O, c * (c * y * c⁻¹) * c⁻¹ = y := fun y => by
    rw [hcinv, ← mul_assoc, ← mul_assoc, hc2, one_mul, mul_assoc, hc2, mul_one]
  have hcc : ∀ K : Subgroup (Y ⧸ O),
      (K.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c).toMonoidHom = K := by
    intro K
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      show c * (c * y * c⁻¹) * c⁻¹ ∈ K
      rw [hcconj]
      exact hy
    · intro hx
      exact ⟨c * x * c⁻¹, ⟨x, hx, rfl⟩, hcconj x⟩
  have hKK : Kc₀ = Kc ∧ Kc₀.map (MulAut.conj c).toMonoidHom = Kc := by
    rcases hcomp Kc hKc with h1 | h1
    · refine ⟨h1.symm, ?_⟩
      rw [← h1]
      exact hKct
    · rw [h1] at hKct
      have h2 : Kc₀ = Kc₀.map (MulAut.conj c).toMonoidHom := (hcc Kc₀).symm.trans hKct
      exact ⟨h2.trans h1.symm, h1.symm⟩
  have hE : E.map π = Kc := by rw [hEmap, hKK.2, hKK.1, sup_idem]
  have hcompKc : ∀ C : Subgroup (Y ⧸ O), CFSG.IsComponent C → C = Kc := fun C hC => by
    rcases hcomp C hC with h1 | h1
    · rw [h1]
      exact hKK.1
    · rw [h1]
      exact hKK.2
  have hψO : O.map ψ.toMonoidHom = O :=
    Subgroup.characteristic_iff_map_eq.1
      (CFSG.LocalAnalysis.ComponentInitial.OddNormalCore.oddCore_characteristic Y) ψ
  set σb : MulAut (Y ⧸ O) := QuotientGroup.congr O O ψ hψO with hσb
  have hσπ : ∀ y, σb (π y) = π (ψ y) := fun y => rfl
  have hσKc : Kc.map σb.toMonoidHom = Kc :=
    hcompKc _ (CFSG.LocalCores.isComponent_map_mulEquiv σb hKc)
  exact abstract_core hs hX hE hlie hsX hKct ψ σb hσπ hψ2 hψs hσKc hψX hZ2 hZs

end FieldInvolutionAux

namespace TrialityD4Data

theorem φ_pow_mem_J₀ {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q) (k : ℕ) {y : X}
    (hy : y ∈ d.J₀) : (d.φ ^ k) y ∈ d.J₀ := by
  obtain ⟨h', rfl⟩ := hy
  refine ⟨h' ^ 2 ^ k, ?_⟩
  show d.torus ((h' ^ 2 ^ k) ^ (q - 1)) = (d.φ ^ k) (d.torus (h' ^ (q - 1)))
  rw [d.φ_pow_torus, ← pow_mul, ← pow_mul, mul_comm]

end TrialityD4Data

namespace FieldInvolutionAux

theorem sylowJ₀_map_eq {q : ℕ} (d : TrialityD4Data L q) :
    d.sylowJ₀.map L.subtype = d.S.map L.subtype ⊓
      centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) := by
  ext y
  constructor
  · rintro ⟨l, ⟨hlS, hlC⟩, rfl⟩
    exact ⟨⟨l, hlS, rfl⟩, Setup.coe_mem_centralizer_of_mem hlC⟩
  · rintro ⟨⟨l, hlS, rfl⟩, hlC⟩
    exact ⟨l, ⟨hlS, Setup.mem_centralizer_of_coe_mem hlC⟩, rfl⟩

theorem not_forall_fix (d : TrialityD4Data L (2 ^ f)) (hf : 2 ≤ f) (hfe : Even f)
    (hfix : ∀ a : d.Γ₀, a ^ 2 ^ (3 * f / 2) = a) : False := by
  obtain ⟨e, rfl⟩ := hfe
  have hq : 2 ^ (e + e) = 2 ^ (2 * e) := by ring_nf
  have h3 : 3 * (e + e) / 2 = 3 * e := by omega
  rw [h3] at hfix
  have he1 : 1 ≤ e := by omega
  have hcard := d.card_fixed_Γ₀ he1 hq
  have hcard' : Nat.card {a : d.Γ₀ // a ^ 2 ^ (3 * e) = a} = Nat.card d.Γ₀ :=
    Nat.card_congr (Equiv.subtypeUnivEquiv hfix)
  rw [hcard, d.card_Γ₀, hq] at hcard'
  have := Nat.pow_right_injective (le_refl 2) hcard'
  omega

theorem sigma_fixes_V
    (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) (hfield : LayerHypFieldAlt h d)
    (σ : centralizer ({t} : Set G)) (hσ2 : (σ : G) * σ = 1)
    (hσN : (σ : G) ∈ ncs d t ⊓
      normalizer ((d.torus.range.map L.subtype : Subgroup G) : Set G))
    (hσφ : h.act σ = d.φ ^ (3 * f / 2)) :
    ∀ v ∈ d.V.map L.subtype, (σ : G) * v * (σ : G)⁻¹ = v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσJ₀ : (σ : G) ∈ normalizer ((d.J₀.map L.subtype : Subgroup G) : Set G) := by
    refine mem_normalizer_fintype fun j hj => ?_
    obtain ⟨l, hl, rfl⟩ := hj
    refine ⟨(d.φ ^ (3 * f / 2)) l, d.φ_pow_mem_J₀ _ hl, ?_⟩
    show (((d.φ ^ (3 * f / 2)) l : L) : G) = _
    rw [← hσφ]
    exact h.coe_act_apply σ l
  have hσS : (σ : G) ∈ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) := hσN.1.2
  have hσH : (σ : G) ∈ normalizer
      ((centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_centralizer_D4 hσJ₀
  have hσE : (σ : G) ∈ normalizer ((jZeroLayer d : Subgroup G) : Set G) :=
    Setup.normalizer_le_normalizer_jZeroLayer d hσJ₀
  have hσt : (σ : G) * t = t * σ := mem_centralizer_singleton_iff.1 σ.2
  have hσP₀ : (σ : G) ∈ normalizer ((d.sylowJ₀.map L.subtype : Subgroup G) : Set G) := by
    rw [sylowJ₀_map_eq d]
    exact mem_normalizer_inf_D4 hσS (mem_normalizer_centralizer_D4 hσJ₀)
  have hP₀E : d.sylowJ₀.map L.subtype ≤ jZeroLayer d :=
    (map_mono d.sylowJ₀_le_leviJ₀).trans (h.leviJ₀_map_le_jZeroLayer d hlay)
  have htE : t ∈ normalizer ((jZeroLayer d : Subgroup G) : Set G) :=
    Setup.le_normalizer_jZeroLayer d (h.t_mem_centralizer_J₀ d)
  have hQ2 : IsPGroup 2 (d.sylowJ₀.map L.subtype ⊔ zpowers t : Subgroup G) :=
    (h.isSylowOf_sylowJ₀_sup_zpowers d).1.isPGroup
  have hzσ : IsPGroup 2 (zpowers (σ : G)) := by
    have hdvd : orderOf (σ : G) ∣ 2 ^ 1 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq]; exact hσ2)
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hb])
  have hσQ : zpowers (σ : G) ≤
      normalizer ((d.sylowJ₀.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) :=
    (zpowers_le).2 (mem_normalizer_sup hσP₀ (mem_normalizer_zpowers_of_comm_D4 hσt))
  have hA2 : IsPGroup 2 (zpowers (σ : G) ⊔ (d.sylowJ₀.map L.subtype ⊔ zpowers t) : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hzσ hQ2 hσQ
  have hAN : zpowers (σ : G) ⊔ (d.sylowJ₀.map L.subtype ⊔ zpowers t) ≤
      normalizer ((jZeroLayer d : Subgroup G) : Set G) :=
    sup_le ((zpowers_le).2 hσE) (sup_le (hP₀E.trans le_normalizer) ((zpowers_le).2 htE))
  obtain ⟨T, hT, hAT⟩ := exists_isSylowOf_le hA2 hAN
  have hXsyl : IsSylowOf 2 (T ⊓ jZeroLayer d) (jZeroLayer d) :=
    hT.inf_of_le_normalizer le_normalizer le_rfl
  have hTN : T ≤ normalizer ((T ⊓ jZeroLayer d : Subgroup G) : Set G) := by
    intro x hx
    exact mem_normalizer_fintype fun y hy => Subgroup.mem_inf.2
      ⟨mul_mem (mul_mem hx hy.1) (inv_mem hx), (mem_normalizer_iff.1 (hT.le hx) y).1 hy.2⟩
  have htT : t ∈ T := hAT (mem_sup_right (mem_sup_right (mem_zpowers t)))
  have hσT : (σ : G) ∈ T := hAT (mem_sup_left (mem_zpowers _))
  have htX : t ∈ normalizer ((T ⊓ jZeroLayer d : Subgroup G) : Set G) := hTN htT
  have hσX : (σ : G) ∈ normalizer ((T ⊓ jZeroLayer d : Subgroup G) : Set G) := hTN hσT
  have hPX : d.sylowJ₀.map L.subtype ≤ T ⊓ jZeroLayer d :=
    le_inf (le_sup_left.trans (le_sup_right.trans hAT)) hP₀E
  obtain ⟨-, hsh⟩ := h.sylowShape_of_isSylowOf_jZeroLayer d hlay hXsyl htX hPX
  have hZV := h.center_inf_centralizer_eq_V d hlay hXsyl htX hPX
  obtain ⟨Kc₀, -, -, hcomp, -, -, hEmap, -, -⟩ := id hlay
  obtain ⟨Kc, hKc, hKct, hlie⟩ := hfield
  set H : Subgroup G := centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) with hH
  set X : Subgroup G := T ⊓ jZeroLayer d with hX
  set s : H := ⟨t, h.t_mem_centralizer_J₀ d⟩ with hs
  have hXH : X ≤ H := inf_le_right.trans (map_subtype_le _)
  have hXmap : (X.subgroupOf H).map H.subtype = X := by
    rw [subgroupOf_map_subtype, inf_eq_left.2 hXH]
  have hXl : IsSylowOf 2 (X.subgroupOf H) (CFSG.layer H) := by
    have := hXsyl
    rw [← hXmap] at this
    exact (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff _).1 this
  have hs2 : s * s = 1 := Subtype.ext h.t_mul_t
  have hsXY : s ∈ normalizer ((X.subgroupOf H : Subgroup H) : Set H) :=
    mem_normalizer_fintype fun x hx => (mem_normalizer_iff.1 htX x).1 hx
  set ψ : MulAut H := H.normalizerMonoidHom ⟨σ, hσH⟩ with hψ
  have hψ2 : ψ * ψ = 1 := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    show (σ : G) * ((σ : G) * y * (σ : G)⁻¹) * (σ : G)⁻¹ = y
    have hinv : (σ : G)⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
    rw [hinv, ← mul_assoc, ← mul_assoc, hσ2, one_mul, mul_assoc, hσ2, mul_one]
  have hψs : ψ s = s := Subtype.ext (by
    show (σ : G) * t * (σ : G)⁻¹ = t
    rw [hσt, mul_inv_cancel_right])
  have hψX : ∀ x ∈ X.subgroupOf H, ψ x ∈ X.subgroupOf H := fun x hx =>
    (mem_normalizer_iff.1 hσX x).1 hx
  have hZ2 : ∀ z ∈ X.subgroupOf H ⊓ centralizer ((X.subgroupOf H : Subgroup H) : Set H),
      z * z = 1 := by
    intro z hz
    refine Subtype.ext (hsh.center_mul_self (z : G) ⟨hz.1, mem_centralizer_iff.2 fun x hx => ?_⟩)
    exact congrArg Subtype.val (mem_centralizer_iff.1 hz.2 ⟨x, hXH hx⟩ hx)
  have hZs : ∃ z ∈ X.subgroupOf H ⊓ centralizer ((X.subgroupOf H : Subgroup H) : Set H),
      s * z * s⁻¹ ≠ z := by
    by_contra hcon
    push Not at hcon
    have hle : X ⊓ centralizer (X : Set G) ≤ d.V.map L.subtype := by
      rw [← hZV]
      intro v hv
      refine ⟨hv, mem_centralizer_singleton_iff.2 ?_⟩
      have h1 := hcon ⟨v, hXH hv.1⟩ ⟨hv.1, mem_centralizer_iff.2 fun x hx =>
        Subtype.ext (mem_centralizer_iff.1 hv.2 (x : G) hx)⟩
      have h2 : t * v * t⁻¹ = v := congrArg Subtype.val h1
      calc v * t = t * v * t⁻¹ * t := by rw [h2]
        _ = t * v := by group
    have hcard := Subgroup.card_le_of_le hle
    rw [hsh.card_center, card_map_of_injective L.subtype_injective, d.card_V] at hcard
    have h2 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.one_le
    nlinarith
  have key := abstract_core_of_components hs2 hXl hEmap hcomp hKc hKct hlie hsXY ψ hψ2 hψs
    hψX hZ2 hZs
  intro v hv
  have hv' : v ∈ X ⊓ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) := by
    rw [hZV]
    exact hv
  have hvX : v ∈ X := hv'.1.1
  have hvC : v ∈ centralizer (X : Set G) := hv'.1.2
  have hvt : v ∈ centralizer ({t} : Set G) := hv'.2
  have h1 := key ⟨v, hXH hvX⟩ ⟨hvX, mem_centralizer_iff.2 fun x hx =>
    Subtype.ext (mem_centralizer_iff.1 hvC (x : G) hx)⟩ (Subtype.ext (by
      show t * v * t⁻¹ = v
      rw [← mem_centralizer_singleton_iff.1 hvt, mul_inv_cancel_right]))
  exact congrArg Subtype.val h1

end FieldInvolutionAux

theorem false_of_field_involution (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hf : 2 ≤ f) (hfe : Even f) (hlay : h.LayerHyp d) (hfield : LayerHypFieldAlt h d)
    (σ : centralizer ({t} : Set G)) (hσ2 : (σ : G) * σ = 1)
    (hσN : (σ : G) ∈ ncs d t ⊓
      normalizer ((d.torus.range.map L.subtype : Subgroup G) : Set G))
    (hσφ : h.act σ = d.φ ^ (3 * f / 2)) : False := by
  have hV := FieldInvolutionAux.sigma_fixes_V h d hlay hfield σ hσ2 hσN
    hσφ
  refine FieldInvolutionAux.not_forall_fix d hf hfe fun a => ?_
  have h1 := hV ((d.x₆ a : L) : G) ⟨d.x₆ a, d.x₆_mem_V a, rfl⟩
  have h2 : ((d.x₆ (a ^ 2 ^ (3 * f / 2)) : L) : G) = ((d.x₆ a : L) : G) := by
    rw [← d.φ_pow_x₆, ← hσφ]
    exact (h.coe_act_apply σ _).trans h1
  exact d.x₆_injective (Subtype.ext h2)

theorem isCyclic_of_layerHypFieldAlt (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hf : 2 ≤ f) (hfe : Even f) (hlay : h.LayerHyp d) (B : Subgroup G)
    (hB : IsSylowOf 2 B (normalizer ((yamadaP d t ⊔ zpowers t : Subgroup G) : Set G)))
    (hQB : yamadaP d t ⊔ zpowers t ≤ B) (hfield : LayerHypFieldAlt h d) :
    ∃ x ∈ B, B = yamadaP d t ⊔ zpowers x := by
  by_contra hncB
  obtain ⟨X, hXC, htX, hXL, hX2, hXS, hXφ⟩ := exists_fieldTwoSubgroup h d
  have hXL' : X ⊓ L = ⊥ := by
    refine le_bot_iff.1 fun x hx => ?_
    have h1 : x ∈ zpowers t := by
      have : x ∈ X ⊓ (L ⊔ zpowers t) := ⟨hx.1, mem_sup_left hx.2⟩
      rwa [hXL] at this
    have h2 : x ∈ zpowers t ⊓ L := ⟨h1, hx.2⟩
    rwa [h.zpowers_inf_L le_rfl] at h2
  obtain ⟨X', hX'B, -, hBX', ⟨ψ⟩⟩ :=
    exists_complement_of_sylow h d hlay X B (hXC.trans inf_le_left) hXL' hXS hB hQB
  have hnc : ¬ ∃ x ∈ X, X = zpowers x := by
    rintro ⟨x, hx, hXx⟩
    apply hncB
    set x' : X' := ψ.symm ⟨x, hx⟩ with hx'
    refine ⟨(x' : G), hX'B x'.2, le_antisymm ?_ ?_⟩
    · rw [hBX']
      refine sup_le_sup_left (fun y hy => ?_) _
      have hyx : (ψ ⟨y, hy⟩ : G) ∈ zpowers x :=
        (SetLike.ext_iff.1 hXx (ψ ⟨y, hy⟩ : G)).1 (ψ ⟨y, hy⟩).2
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hyx
      have h1 : ψ ⟨y, hy⟩ = (⟨x, hx⟩ : X) ^ k := Subtype.ext (by simpa using hk.symm)
      have h2 : ψ ⟨y, hy⟩ = ψ (x' ^ k) := by
        rw [map_zpow, hx', MulEquiv.apply_symm_apply, h1]
      have h3 : (⟨y, hy⟩ : X') = x' ^ k := ψ.injective h2
      exact mem_zpowers_iff.2 ⟨k, by simpa using (congrArg Subtype.val h3).symm⟩
    · exact sup_le (le_sup_left.trans hQB) ((zpowers_le).2 (hX'B x'.2))
  obtain ⟨σ, hσX, hσ2, -, hσφ⟩ :=
    exists_field_involution h d hfe X (hXC.trans (inf_le_left.trans inf_le_left)) htX hXL hX2 hXφ
      hnc
  exact false_of_field_involution h d hf hfe hlay hfield σ hσ2 (hXC hσX) hσφ

end CFSG.LocalAnalysis.EvenBN.TrialityD4
