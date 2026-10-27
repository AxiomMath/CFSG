module

public import CFSG.ClassicalInvolution.Asc77.AscE187EndB
public import CFSG.ClassicalInvolution.Q3.Q3T8Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

namespace TwinThmE

section Q8Aut

theorem q8_ord4_iff (x : QuaternionGroup 2) : orderOf x = 4 ↔ x * x ≠ 1 := by
  constructor
  · intro h h1
    have : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h1)
    rw [h] at this
    norm_num at this
  · intro h
    have hsq : ∀ y : QuaternionGroup 2, y * y * (y * y) = 1 := by decide
    have hnot : ¬ x ^ 2 ^ 1 = 1 := by simpa [pow_two] using h
    have hfin : x ^ 2 ^ (1 + 1) = 1 := by
      have := hsq x
      calc x ^ 2 ^ (1 + 1) = x * x * (x * x) := by simp [pow_succ, mul_assoc]
        _ = 1 := this
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := x) hnot hfin
    simpa using this

theorem q8_pair_claim : ∀ p q : QuaternionGroup 2, p = QuaternionGroup.a 1 ∨
    q = QuaternionGroup.xa 0 ∨ p * q = QuaternionGroup.a 1 * QuaternionGroup.xa 0 ∨
    (QuaternionGroup.a 1 * p⁻¹) * (QuaternionGroup.a 1 * p⁻¹) ≠ 1 ∨
    (QuaternionGroup.xa 0 * q⁻¹) * (QuaternionGroup.xa 0 * q⁻¹) ≠ 1 ∨
    ((QuaternionGroup.a 1 * QuaternionGroup.xa 0) * (p * q)⁻¹) *
      ((QuaternionGroup.a 1 * QuaternionGroup.xa 0) * (p * q)⁻¹) ≠ 1 := by decide

theorem q8_hom_cases (f : QuaternionGroup 2 →* QuaternionGroup 2) :
    (∃ x, orderOf x = 4 ∧ f x = x) ∨ ∃ x, orderOf x = 4 ∧ orderOf (x * (f x)⁻¹) = 4 := by
  have hi : orderOf (QuaternionGroup.a 1 : QuaternionGroup 2) = 4 :=
    (q8_ord4_iff _).2 (by decide)
  have hj : orderOf (QuaternionGroup.xa 0 : QuaternionGroup 2) = 4 :=
    (q8_ord4_iff _).2 (by decide)
  have hk : orderOf (QuaternionGroup.a 1 * QuaternionGroup.xa 0 : QuaternionGroup 2) = 4 :=
    (q8_ord4_iff _).2 (by decide)
  rcases q8_pair_claim (f (QuaternionGroup.a 1)) (f (QuaternionGroup.xa 0)) with h | h | h | h | h | h
  · exact Or.inl ⟨_, hi, h⟩
  · exact Or.inl ⟨_, hj, h⟩
  · exact Or.inl ⟨_, hk, by rw [map_mul]; exact h⟩
  · exact Or.inr ⟨_, hi, (q8_ord4_iff _).2 h⟩
  · exact Or.inr ⟨_, hj, (q8_ord4_iff _).2 h⟩
  · exact Or.inr ⟨_, hk, (q8_ord4_iff _).2 (by rw [map_mul]; exact h)⟩

variable {G : Type} [Group G]

theorem sylow_q8_cases {Q : Subgroup G} (e : ↥Q ≃* QuaternionGroup 2) {δ : G}
    (hδ : conjSub δ Q = Q) :
    (∃ x ∈ Q, orderOf x = 4 ∧ δ * x * δ⁻¹ = x) ∨
      ∃ x ∈ Q, orderOf x = 4 ∧ orderOf (x * (δ * x * δ⁻¹)⁻¹) = 4 := by
  have hmem : ∀ y ∈ Q, δ * y * δ⁻¹ ∈ Q := fun y hy => by
    have := conj_mem_conjSub (n := δ) hy
    rwa [hδ] at this
  let φ : ↥Q →* ↥Q := MonoidHom.mk' (fun y => ⟨δ * (y : G) * δ⁻¹, hmem y y.2⟩) (fun x y =>
    Subtype.ext (by
      show δ * ((x : G) * y) * δ⁻¹ = (δ * (x : G) * δ⁻¹) * (δ * (y : G) * δ⁻¹)
      group))
  let f : QuaternionGroup 2 →* QuaternionGroup 2 :=
    e.toMonoidHom.comp (φ.comp e.symm.toMonoidHom)
  have hf : ∀ x, f x = e (φ (e.symm x)) := fun x => rfl
  rcases q8_hom_cases f with ⟨x, hx4, hfx⟩ | ⟨x, hx4, hx⟩
  · left
    have h' : φ (e.symm x) = e.symm x := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply, ← hf]
      exact hfx
    refine ⟨((e.symm x : ↥Q) : G), (e.symm x).2, ?_, congrArg Subtype.val h'⟩
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hx4
  · right
    set y : ↥Q := e.symm x with hy
    refine ⟨(y : G), y.2, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe, hy, MulEquiv.orderOf_eq]
      exact hx4
    · have h1 : orderOf (y * (φ y)⁻¹) = 4 := by
        rw [← MulEquiv.orderOf_eq e, map_mul, map_inv, hy, MulEquiv.apply_symm_apply, ← hf]
        exact hx
      rw [← Subgroup.orderOf_coe] at h1
      simpa [φ] using h1

end Q8Aut

section

open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G]

theorem endgame_all [Finite G] {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {H : Subgroup G} {t : G}
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω)
    (ht : IsUniqueInvolution K₁ t) (hbad : ∀ u ∈ K₁, orderOf u = 4 → u ∉ H) {d₁ d₂ : G}
    (g₁ : GoodInv H t d₁) (g₂ : GoodInv H t d₂) (g₃ : GoodInv H t (d₁ * d₂))
    (hc : d₁ * d₂ = d₂ * d₁) (n₁ : conjSub d₁ K₁ = K₁) (n₂ : conjSub d₂ K₁ = K₁) : False := by
  classical
  set D : Subgroup G := Subgroup.zpowers d₁ ⊔ Subgroup.zpowers d₂ with hDdef
  have hD : IsPGroup 2 D := isPGroup_two_sup_zpowers g₁.ne_one g₁.sq g₂.ne_one g₂.sq hc
  have hd₁D : d₁ ∈ D := Subgroup.mem_sup_left (Subgroup.mem_zpowers d₁)
  have hd₂D : d₂ ∈ D := Subgroup.mem_sup_right (Subgroup.mem_zpowers d₂)
  have hDN : D ≤ Subgroup.normalizer (K₁ : Set G) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact mem_normalizer_iff_conjSub_eq.mpr n₁
    · rw [Subgroup.zpowers_le]
      exact mem_normalizer_iff_conjSub_eq.mpr n₂
  obtain ⟨Q, hQ, hQD⟩ := exists_sylow_normalized hD hDN
  have hQR : Q ∈ RSet Ω := mem_RSet_of_isSylow2In hK₁ hQ
  have h8 : 8 ≤ Nat.card Q := hΩ.eight_le_of_mem_RSet hQR
  have htQ : t ∈ Q := mem_of_isUniqueInvolution_of_isPGroup ht hQ.1 hQ.2.1 (by omega)
  have hQt : IsUniqueInvolution Q t :=
    ⟨htQ, ht.ne_one, ht.sq, fun y hy hy2 => ht.unique y (hQ.1 hy) hy2⟩
  have hDQ : D ≤ Subgroup.normalizer (Q : Set G) := fun d hd =>
    mem_normalizer_iff_conjSub_eq.mpr (hQD d hd)
  have hPp : IsPGroup 2 ↥(D ⊔ Q) := hD.to_sup_of_normal_right' hQ.2.1 hDQ
  have hTn : ∀ x ∈ D ⊔ Q, conjSub x Q = Q := by
    intro x hx
    have hle : D ⊔ Q ≤ Subgroup.normalizer (Q : Set G) := sup_le hDQ Subgroup.le_normalizer
    exact mem_normalizer_iff_conjSub_eq.mp (hle hx)
  obtain ⟨A, hAQ, hAcyc, hAcard, hAinv⟩ :=
    exists_invariant_cyclic_order_four hPp le_sup_right hTn hQt (by omega)
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := ↥A)
  have hu4 : orderOf (u : G) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hu, hAcard]
  have huA : (u : G) ∈ A := u.2
  have hAz : ∀ x ∈ A, x ∈ Subgroup.zpowers (u : G) := by
    intro x hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hu ⟨x, hx⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, by simpa using congrArg Subtype.val hm⟩
  have hnH : (u : G) ∉ H := hbad _ (hQ.1 (hAQ huA)) hu4
  have hact : ∀ δ ∈ D, δ * u * δ⁻¹ = u ∨ δ * u * δ⁻¹ = (u : G)⁻¹ := by
    intro δ hδ
    have hmem : δ * (u : G) * δ⁻¹ ∈ A := by
      have := conj_mem_conjSub (n := δ) huA
      rwa [hAinv δ (Subgroup.mem_sup_left hδ)] at this
    exact eq_or_eq_inv_of_orderOf_four hu4 (hAz _ hmem) (by rw [orderOf_conj_mul_inv_eq, hu4])
  have hcen : ∀ δ, GoodInv H t δ → δ * u * δ⁻¹ = (u : G) → False := by
    intro δ hg h
    apply hnH
    apply hg.cent
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  rcases hact d₁ hd₁D with h1 | h1
  · exact hcen d₁ g₁ h1
  rcases hact d₂ hd₂D with h2 | h2
  · exact hcen d₂ g₂ h2
  refine hcen (d₁ * d₂) g₃ ?_
  have e : d₁ * d₂ * (u : G) * (d₁ * d₂)⁻¹ = d₁ * (d₂ * u * d₂⁻¹) * d₁⁻¹ := by group
  rw [e, h2]
  have : d₁ * (u : G)⁻¹ * d₁⁻¹ = (d₁ * u * d₁⁻¹)⁻¹ := by group
  rw [this, h1, inv_inv]

end

section EndOne

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem twin_conj_gen (hΩ : HypOmegaGen Ω) {M : Subgroup G} {t δ : G} (hM : M ∈ Ω)
    (hMt : IsUniqueInvolution M t) (hδ : δ * t = t * δ) :
    conjSub δ M ∈ Ω ∧ IsUniqueInvolution (conjSub δ M) t := by
  refine ⟨hΩ.conjInvariant δ M hM, ?_⟩
  have := hMt.conj δ
  rwa [show δ * t * δ⁻¹ = t by rw [hδ]; group] at this

theorem conjSub_sylow_eq {K₁ S₁ R₁ : Subgroup G} (hS₁ : IsPGroup 2 S₁) (hR₁ : IsSylow2In R₁ K₁)
    (hR₁S : R₁ ≤ S₁) {δ : G} (hδS : δ ∈ S₁) (hδ : conjSub δ K₁ = K₁) :
    conjSub δ R₁ = R₁ := by
  have hKS : K₁ ⊓ S₁ = R₁ :=
    hR₁.eq_of_le (hS₁.to_le inf_le_right) inf_le_left (le_inf hR₁.1 hR₁S)
  have hle : ∀ {δ : G}, δ ∈ S₁ → conjSub δ K₁ = K₁ → conjSub δ R₁ ≤ R₁ := by
    intro δ hδS hδ x hx
    rw [mem_conjSub_iff] at hx
    have h1 : δ⁻¹ * x * δ ∈ R₁ := hx
    have hxK : x ∈ K₁ := by
      have := conj_mem_conjSub (n := δ) (hR₁.1 h1)
      rw [hδ] at this
      have e : δ * (δ⁻¹ * x * δ) * δ⁻¹ = x := by group
      rwa [e] at this
    have hxS : x ∈ S₁ := by
      have := S₁.mul_mem (S₁.mul_mem hδS (hR₁S h1)) (S₁.inv_mem hδS)
      have e : δ * (δ⁻¹ * x * δ) * δ⁻¹ = x := by group
      rwa [e] at this
    rw [← hKS]
    exact ⟨hxK, hxS⟩
  refine le_antisymm (hle hδS hδ) ?_
  have hδ' : conjSub δ⁻¹ K₁ = K₁ := by
    have := congrArg (conjSub δ⁻¹) hδ
    rw [conjSub_inv_conjSub] at this
    exact this.symm
  have := conjSub_mono (n := δ) (hle (S₁.inv_mem hδS) hδ')
  rwa [conjSub_conjSub_inv] at this

theorem endgame_one_Q8 (hΩ : HypOmegaGen Ω)
    (hq8 : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2))
    {H : Subgroup G} {t : G}
    (hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω) (ht : IsUniqueInvolution K₁ t) {S₁ R₁ : Subgroup G}
    (hS₁ : IsPGroup 2 S₁) (hR₁ : IsSylow2In R₁ K₁) (hR₁S : R₁ ≤ S₁) {δ₀ δ₁ : G}
    (hδ₀S : δ₀ ∈ S₁) (hδ₁S : δ₁ ∈ S₁)
    (g₀ : GoodInv H t δ₀) (g₁ : GoodInv H t δ₁) (g₂ : GoodInv H t (δ₀ * δ₁))
    (hc : δ₀ * δ₁ = δ₁ * δ₀) (n₀ : conjSub δ₀ K₁ = K₁) (m₁ : conjSub δ₁ K₁ ≠ K₁) : False := by
  obtain ⟨hK₂Ω, hK₂t⟩ := twin_conj_gen hΩ hK₁ ht g₁.comm_t
  have hR₁N : conjSub δ₀ R₁ = R₁ := conjSub_sylow_eq hS₁ hR₁ hR₁S hδ₀S n₀
  set R₂ : Subgroup G := conjSub δ₁ R₁ with hR₂
  have hR₂S : R₂ ≤ S₁ := by
    rintro _ ⟨x, hx, rfl⟩
    exact S₁.mul_mem (S₁.mul_mem hδ₁S (hR₁S hx)) (S₁.inv_mem hδ₁S)
  have hR₂K : R₂ ≤ conjSub δ₁ K₁ := conjSub_mono hR₁.1
  have c12 : Commutes R₁ R₂ :=
    hΩ.commutes_of_twin_of_isPGroup hK₁ hK₂Ω (Ne.symm m₁) ht hK₂t hR₁.1 hR₂K
      (hS₁.to_le (sup_le hR₁S hR₂S))
  have hφ : ∀ x ∈ R₁, δ₀ * x * δ₀⁻¹ ∈ R₁ := by
    intro x hx
    have := conj_mem_conjSub (n := δ₀) hx
    rwa [hR₁N] at this
  have key : ∀ x ∈ R₁, δ₁ * (x * (δ₀ * x * δ₀⁻¹)⁻¹) * δ₁⁻¹ ∈ H := by
    intro x hx
    have hx₂ : δ₁ * x * δ₁⁻¹ ∈ R₂ := conj_mem_conjSub hx
    have hy₂ : δ₁ * (δ₀ * x * δ₀⁻¹) * δ₁⁻¹ ∈ R₂ := conj_mem_conjSub (hφ x hx)
    have hxx₂ : x * (δ₁ * x * δ₁⁻¹) = (δ₁ * x * δ₁⁻¹) * x := c12 x hx _ hx₂
    have hxy₂ : x * (δ₁ * (δ₀ * x * δ₀⁻¹) * δ₁⁻¹) = (δ₁ * (δ₀ * x * δ₀⁻¹) * δ₁⁻¹) * x :=
      c12 x hx _ hy₂
    have n₁ : x * (δ₁ * x * δ₁⁻¹) ∈ H :=
      g₁.cent (mul_mem_centralizer_of_swap g₁.sq rfl hxx₂)
    have hswap : (δ₀ * δ₁) * x * (δ₀ * δ₁)⁻¹ = δ₁ * (δ₀ * x * δ₀⁻¹) * δ₁⁻¹ := by
      rw [hc]
      group
    have n₂ : x * (δ₁ * (δ₀ * x * δ₀⁻¹) * δ₁⁻¹) ∈ H :=
      g₂.cent (mul_mem_centralizer_of_swap g₂.sq hswap hxy₂)
    set a := δ₁ * x * δ₁⁻¹ with ha
    set b := δ₁ * (δ₀ * x * δ₀⁻¹) * δ₁⁻¹ with hb
    have e1 : x * a * (x * b)⁻¹ = a * b⁻¹ := by
      have hxi : x * b⁻¹ = b⁻¹ * x := (Commute.inv_right (show Commute x b from hxy₂)).eq
      calc x * a * (x * b)⁻¹ = x * a * b⁻¹ * x⁻¹ := by group
        _ = a * x * b⁻¹ * x⁻¹ := by rw [hxx₂]
        _ = a * (x * b⁻¹) * x⁻¹ := by group
        _ = a * (b⁻¹ * x) * x⁻¹ := by rw [hxi]
        _ = a * b⁻¹ := by group
    have e2 : δ₁ * (x * (δ₀ * x * δ₀⁻¹)⁻¹) * δ₁⁻¹ = a * b⁻¹ := by
      rw [ha, hb]
      group
    rw [e2, ← e1]
    exact H.mul_mem n₁ (H.inv_mem n₂)
  obtain ⟨e⟩ := hq8 K₁ hK₁ R₁ hR₁
  rcases sylow_q8_cases e hR₁N with ⟨x, hxQ, hx4, hfix⟩ | ⟨x, hxQ, hx4, hord⟩
  · apply hbad K₁ hK₁ ht x (hR₁.1 hxQ) hx4
    apply g₀.cent
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp hfix).symm
  · have hmemH := key x hxQ
    have hmem2 : δ₁ * (x * (δ₀ * x * δ₀⁻¹)⁻¹) * δ₁⁻¹ ∈ conjSub δ₁ K₁ :=
      conj_mem_conjSub (K₁.mul_mem (hR₁.1 hxQ) (K₁.inv_mem (hR₁.1 (hφ x hxQ))))
    have hord' : orderOf (δ₁ * (x * (δ₀ * x * δ₀⁻¹)⁻¹) * δ₁⁻¹) = 4 := by
      rw [orderOf_conj_mul_inv_eq]
      exact hord
    exact hbad _ hK₂Ω hK₂t _ hmem2 hord' hmemH
end EndOne

section Part2

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
  {R W H : Subgroup G}

theorem exists_g_hCS {z g t : G} (hSylz : IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
      (Subgroup.centralizer ({z} : Set G)))
    (ht : t = g * z * g⁻¹) (hzH : Subgroup.centralizer ({z} : Set G) ≤ H) (hg : g ∉ H) :
    ∃ g' : G, g' ∉ H ∧ t = g' * z * g'⁻¹ ∧
      ∀ x ∈ (S : Subgroup G), t * x = x * t → x ∈ conjSub g' (S : Subgroup G) := by
  set P : Subgroup G := (S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G) with hP
  have hC1 : conjSub g (Subgroup.centralizer ({z} : Set G)) = Subgroup.centralizer ({t} : Set G) := by
    ext x
    rw [mem_conjSub_iff, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff, ht]
    constructor
    · intro h
      calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
        _ = (g * z * g⁻¹) * x := by group
    · intro h
      calc (g⁻¹ * x * g) * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [h]
        _ = z * (g⁻¹ * x * g) := by group
  have hSylt : IsSylow2In (conjSub g P) (Subgroup.centralizer ({t} : Set G)) := by
    have := IsSylow2In.conj hSylz g
    rwa [hC1] at this
  set A : Subgroup G := (S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G) with hA
  have hA2 : IsPGroup 2 A := S.isPGroup'.to_le inf_le_left
  obtain ⟨Q, hQ, hAQ⟩ := IsSylow2In.exists_ge hA2 (inf_le_right : A ≤ Subgroup.centralizer ({t} : Set G))
  obtain ⟨x, hxC, hxQ⟩ := exists_conjSub_eq_of_isSylow2In hSylt hQ
  have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
  have e1 : (x * g) * z * (x * g)⁻¹ = t := by
    calc (x * g) * z * (x * g)⁻¹ = x * (g * z * g⁻¹) * x⁻¹ := by group
      _ = x * t * x⁻¹ := by rw [← ht]
      _ = t := by rw [hxt]; group
  refine ⟨x * g, ?_, e1.symm, ?_⟩
  · intro hxg
    have hwz : ((x * g)⁻¹ * g) * z * ((x * g)⁻¹ * g)⁻¹ = z := by
      calc ((x * g)⁻¹ * g) * z * ((x * g)⁻¹ * g)⁻¹ = (x * g)⁻¹ * (g * z * g⁻¹) * (x * g) := by group
        _ = (x * g)⁻¹ * t * (x * g) := by rw [← ht]
        _ = (x * g)⁻¹ * ((x * g) * z * (x * g)⁻¹) * (x * g) := by rw [e1]
        _ = z := by group
    have hw : ((x * g)⁻¹ * g) ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc ((x * g)⁻¹ * g) * z = (((x * g)⁻¹ * g) * z * ((x * g)⁻¹ * g)⁻¹) * ((x * g)⁻¹ * g) := by
            group
        _ = z * ((x * g)⁻¹ * g) := by rw [hwz]
    apply hg
    have e : g = (x * g) * ((x * g)⁻¹ * g) := by group
    rw [e]
    exact H.mul_mem hxg (hzH hw)
  · intro y hyS hyt
    have hyA : y ∈ A := ⟨hyS, Subgroup.mem_centralizer_singleton_iff.mpr hyt.symm⟩
    have hyQ : y ∈ Q := hAQ hyA
    rw [← hxQ, ← conjSub_mul] at hyQ
    exact conjSub_mono (n := x * g) (inf_le_left : P ≤ (S : Subgroup G)) hyQ

theorem endgame_cases_Q8 (hΩ : HypOmegaGen Ω)
    (hq8 : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2))
    {H : Subgroup G} {t : G}
    (hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω) (ht : IsUniqueInvolution K₁ t) {S₁ R₁ : Subgroup G}
    (hS₁ : IsPGroup 2 S₁) (hR₁ : IsSylow2In R₁ K₁) (hR₁S : R₁ ≤ S₁) {d₁ d₂ : G}
    (hd₁S : d₁ ∈ S₁) (hd₂S : d₂ ∈ S₁)
    (g₁ : GoodInv H t d₁) (g₂ : GoodInv H t d₂) (g₃ : GoodInv H t (d₁ * d₂))
    (hc : d₁ * d₂ = d₂ * d₁) :
    conjSub d₁ K₁ ≠ K₁ ∧ conjSub d₂ K₁ ≠ K₁ ∧ conjSub (d₁ * d₂) K₁ ≠ K₁ := by
  have hbadK : ∀ u ∈ K₁, orderOf u = 4 → u ∉ H := fun u hu hu4 => hbad K₁ hK₁ ht u hu hu4
  have hdd : d₁ * d₂ * d₁ = d₂ := by
    calc d₁ * d₂ * d₁ = d₁ * (d₂ * d₁) := mul_assoc _ _ _
      _ = d₁ * (d₁ * d₂) := by rw [hc]
      _ = d₂ := by rw [← mul_assoc, g₁.sq, one_mul]
  have hdd' : d₁ * (d₁ * d₂) = d₂ := by rw [← mul_assoc, g₁.sq, one_mul]
  have hd₃S : d₁ * d₂ ∈ S₁ := S₁.mul_mem hd₁S hd₂S
  by_cases n₁ : conjSub d₁ K₁ = K₁
  · by_cases n₂ : conjSub d₂ K₁ = K₁
    · exact (endgame_all hΩ hK₁ ht hbadK g₁ g₂ g₃ hc n₁ n₂).elim
    · exact (endgame_one_Q8 hΩ hq8 hbad hK₁ ht hS₁ hR₁ hR₁S hd₁S hd₂S g₁ g₂ g₃ hc n₁ n₂).elim
  · by_cases n₂ : conjSub d₂ K₁ = K₁
    · have g₃' : GoodInv H t (d₂ * d₁) := by rw [← hc]; exact g₃
      exact (endgame_one_Q8 hΩ hq8 hbad hK₁ ht hS₁ hR₁ hR₁S hd₂S hd₁S g₂ g₁ g₃' hc.symm n₂
        n₁).elim
    · by_cases n₃ : conjSub (d₁ * d₂) K₁ = K₁
      · have g₂' : GoodInv H t (d₁ * d₂ * d₁) := by rw [hdd]; exact g₂
        exact (endgame_one_Q8 hΩ hq8 hbad hK₁ ht hS₁ hR₁ hR₁S hd₃S hd₁S g₃ g₁ g₂'
          (by rw [hdd, hdd']) n₃ n₁).elim
      · exact ⟨n₁, n₂, n₃⟩

end Part2

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
