module

public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeDefs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Defs

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup CFSG.Quasithin

variable {G : Type*} [Group G] {t : G} {L U Q P : Subgroup G}

theorem card_conj_orbit_mul [Finite G] (K : Subgroup G) (x : G) :
    Nat.card {y : G // ∃ g ∈ K, g * x * g⁻¹ = y} *
      Nat.card (K ⊓ centralizer ({x} : Set G) : Subgroup G) = Nat.card K := by
  let _ : MulAction K G := MulAction.compHom G (MulAut.conj.comp K.subtype)
  have hsmul : ∀ (k : K) (y : G), k • y = (k : G) * y * (k : G)⁻¹ := fun _ _ => rfl
  have e1 : MulAction.orbit K x ≃ {y : G // ∃ g ∈ K, g * x * g⁻¹ = y} :=
    { toFun := fun y => ⟨y.1, by
        obtain ⟨k, hk⟩ := y.2
        exact ⟨k, k.2, by rw [← hsmul]; exact hk⟩⟩
      invFun := fun y => ⟨y.1, by
        obtain ⟨g, hg, hy⟩ := y.2
        exact ⟨⟨g, hg⟩, by change (⟨g, hg⟩ : K) • x = y.1; rw [hsmul]; exact hy⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e2 : MulAction.stabilizer K x ≃ (K ⊓ centralizer ({x} : Set G) : Subgroup G) :=
    { toFun := fun k => ⟨k.1.1, k.1.2, by
        have h : (k.1 : G) * x * (k.1 : G)⁻¹ = x := by rw [← hsmul]; exact k.2
        change k.1.1 ∈ centralizer ({x} : Set G)
        rw [mem_centralizer_singleton_iff]
        calc (k.1 : G) * x = (k.1 : G) * x * (k.1 : G)⁻¹ * k.1 := by group
          _ = x * k.1 := by rw [h]⟩
      invFun := fun k => ⟨⟨k.1, k.2.1⟩, by
        change (k : G) * x * (k : G)⁻¹ = x
        have h : (k : G) * x = x * k := mem_centralizer_singleton_iff.1 k.2.2
        rw [h, mul_inv_cancel_right]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e1, ← Nat.card_congr e2, ← Nat.card_prod,
    Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K x)]

theorem card_modEq_inf_centralizer [Finite G] {E : Subgroup G} {g : G}
    (hg : g ∈ normalizer (E : Set G)) {q : ℕ} [Fact q.Prime] (hgq : g ^ q = 1) :
    Nat.card E ≡ Nat.card (E ⊓ centralizer ({g} : Set G) : Subgroup G) [MOD q] := by
  classical
  have : Fintype E := Fintype.ofFinite _
  let f : Function.End E := fun x => ⟨g * x * g⁻¹, (mem_normalizer_iff.1 hg x).1 x.2⟩
  have hpow : ∀ k : ℕ, ∀ x : E, ((f ^ k) x : G) = g ^ k * x * (g ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; change ((x : E) : G) = _; simp
    | succ k ih =>
      intro x
      rw [pow_succ']
      change g * ((f ^ k) x : G) * g⁻¹ = _
      rw [ih, pow_succ', mul_inv_rev]
      group
  have hf : f ^ q ^ 1 = 1 := by
    rw [pow_one]
    funext x
    apply Subtype.ext
    rw [hpow, hgq, inv_one, one_mul, mul_one]
    rfl
  have h := Equiv.Perm.card_fixedPoints_modEq (p := q) (n := 1) hf
  have e : f.fixedPoints ≃ (E ⊓ centralizer ({g} : Set G) : Subgroup G) :=
    { toFun := fun x => ⟨x.1.1, x.1.2, by
        have hx : f x.1 = x.1 := x.2
        have hx' : g * x.1.1 * g⁻¹ = x.1.1 := congrArg Subtype.val hx
        change x.1.1 ∈ centralizer ({g} : Set G)
        rw [mem_centralizer_singleton_iff]
        calc x.1.1 * g = g * x.1.1 * g⁻¹ * g := by rw [hx']
          _ = g * x.1.1 := by group⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, by
        apply Subtype.ext
        change g * x.1 * g⁻¹ = x.1
        rw [(mem_centralizer_singleton_iff.1 x.2.2).symm, mul_inv_cancel_right]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_eq_fintype_card, ← Nat.card_congr e, Nat.card_eq_fintype_card]
  exact h

theorem exists_dvd_modEq_of_orderOf [Finite G] {E : Subgroup G} (hE : Nat.card E = 128)
    (hCE : centralizer (E : Set G) ≤ E) {g : G} (hg : g ∈ normalizer (E : Set G)) {q : ℕ}
    (hq : q.Prime) (hgq : orderOf g = q) (hq2 : q ≠ 2) :
    ∃ d, d ∣ 128 ∧ d < 128 ∧ 128 ≡ d [MOD q] := by
  have : Fact q.Prime := ⟨hq⟩
  have hmod := card_modEq_inf_centralizer hg (q := q) (by rw [← hgq, pow_orderOf_eq_one])
  set F := (E ⊓ centralizer ({g} : Set G) : Subgroup G)
  have hdvd : Nat.card F ∣ 128 := hE ▸ Subgroup.card_dvd_of_le inf_le_left
  refine ⟨Nat.card F, hdvd, lt_of_le_of_ne (Nat.le_of_dvd (by norm_num) hdvd) fun h128 => ?_,
    hE ▸ hmod⟩
  have hFE : F = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hE, h128])
  have hgC : g ∈ centralizer (E : Set G) := mem_centralizer_iff.2 fun x hx => by
    have : x ∈ F := hFE ▸ hx
    exact mem_centralizer_singleton_iff.1 this.2
  have hgE := hCE hgC
  have h1 : orderOf g ∣ 128 := hE ▸ Subgroup.orderOf_dvd_natCard E hgE
  rw [hgq, show (128 : ℕ) = 2 ^ 7 by norm_num] at h1
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h1))

theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at *
  rw [Subgroup.map_sup, hA, hB]

theorem mem_normalizer_zpowers {g x : G} (h : g * x = x * g) :
    g ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  congr 1
  change g * x * g⁻¹ = x
  rw [h, mul_inv_cancel_right]

theorem exists_mem_normalizer_not_mem [Finite G] {H T : Subgroup G} (hT : IsPGroup 2 T)
    (hHT : H < T) : ∃ n ∈ T, n ∈ normalizer (H : Set G) ∧ n ∉ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent T := hT.isNilpotent
  have hlt : H.subgroupOf T < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply (lt_iff_le_not_ge.1 hHT).2
    intro x hx
    have : (⟨x, hx⟩ : T) ∈ H.subgroupOf T := h ▸ mem_top _
    exact this
  obtain ⟨⟨n, hnT⟩, hn1, hn2⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hconj : ∀ m : T, m ∈ normalizer ((H.subgroupOf T : Subgroup T) : Set T) →
      ∀ x ∈ H, (m : G) * x * (m : G)⁻¹ ∈ H := by
    intro m hm x hx
    have hxT : x ∈ T := hHT.le hx
    have := (mem_normalizer_iff.1 hm ⟨x, hxT⟩).1 hx
    exact this
  refine ⟨n, hnT, mem_normalizer_iff.2 fun x => ⟨hconj _ hn1 x, fun hx => ?_⟩, hn2⟩
  have h2 := hconj _ (inv_mem hn1) _ hx
  simpa [mul_assoc] using h2

theorem t_mem_sup {X : Subgroup G} : t ∈ X ⊔ zpowers t := mem_sup_right (mem_zpowers t)

theorem pResidual_two_eq_top [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) : pResidual 2 G = ⊤ := by
  refine eq_top_iff.2 (le_iInf fun N => le_iInf fun hN => le_iInf fun hp => ?_)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exfalso
    have h2 : IsPGroup 2 G := fun x => by
      obtain ⟨k, hk⟩ := hp x
      rw [h, mem_bot] at hk
      exact ⟨k, hk⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc : Nontrivial (center G) := h2.center_nontrivial
    rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with hz | hz
    · rw [hz] at hc
      obtain ⟨x, y, hxy⟩ := hc
      exact hxy (Subsingleton.elim x y)
    · obtain ⟨a, b, hab⟩ := hnab
      exact hab (mem_center_iff.mp (hz ▸ mem_top a : a ∈ center G) b).symm
  · rw [h]

namespace ShapeAB

variable (hA : ShapeAB t L U Q P)
include hA

theorem mul_self : t * t = 1 := by
  rw [← pow_two, ← hA.orderOf_eq, pow_orderOf_eq_one]

theorem ne_one : t ≠ 1 := fun h => by
  have := hA.orderOf_eq
  rw [h, orderOf_one] at this
  exact absurd this (by decide)

theorem inv_eq : t⁻¹ = t := inv_eq_of_mul_eq_one_right hA.mul_self

theorem commute_of_mem {l : G} (hl : l ∈ L) : l * t = t * l :=
  mem_centralizer_singleton_iff.1 (hA.le_centralizer hl)

theorem mem_zpowers_iff {z : G} : z ∈ zpowers t ↔ z = 1 ∨ z = t := by
  constructor
  · rintro ⟨k, rfl⟩
    change t ^ k = 1 ∨ t ^ k = t
    rw [← zpow_mod_orderOf, hA.orderOf_eq]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [Nat.cast_ofNat, h]
    · exact Or.inl (zpow_zero t)
    · exact Or.inr (zpow_one t)
  · rintro (h | h) <;> rw [h]
    · exact one_mem _
    · exact mem_zpowers t

theorem conj_not_mem (hodd : InvolutionsInOddPart L) (g : G) : g * t * g⁻¹ ∉ L := by
  intro hu
  set u : L := ⟨g * t * g⁻¹, hu⟩ with hudef
  have hu2 : orderOf u = 2 := by
    rw [hudef, Subgroup.orderOf_mk, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hA.orderOf_eq]
  have hle : closure {y : L | y * u = u * y ∧ Odd (orderOf y)} ≤
      (closure {x : G | x * t = t * x ∧ Odd (orderOf x)}).comap
        (((MulAut.conj g⁻¹).toMonoidHom).comp L.subtype) := by
    rw [closure_le]
    rintro y ⟨hyu, hyo⟩
    have hyu' : (y : G) * (g * t * g⁻¹) = g * t * g⁻¹ * y := congrArg Subtype.val hyu
    refine subset_closure ⟨?_, ?_⟩
    · change g⁻¹ * y * g⁻¹⁻¹ * t = t * (g⁻¹ * y * g⁻¹⁻¹)
      rw [inv_inv]
      calc g⁻¹ * y * g * t = g⁻¹ * ((y : G) * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * t * g⁻¹ * y) * g := by rw [hyu']
        _ = t * (g⁻¹ * y * g) := by group
    · change Odd (orderOf (MulAut.conj g⁻¹ (y : G)))
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe]
      exact hyo
  have h := hle (hodd u hu2)
  rw [mem_comap, MonoidHom.coe_comp, Function.comp_apply, coe_subtype, hudef,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h
  apply hA.not_mem_closure_odd
  convert h using 1
  group

theorem commute_sup {X : Subgroup G} (hXL : X ≤ L) : ∀ u ∈ X, ∀ c ∈ zpowers t, u * c = c * u := by
  intro u hu c hc
  rcases hA.mem_zpowers_iff.1 hc with rfl | rfl
  · rw [mul_one, one_mul]
  · exact hA.commute_of_mem (hXL hu)

theorem mem_sup_iff {X : Subgroup G} (hXL : X ≤ L) {x : G} :
    x ∈ X ⊔ zpowers t ↔ ∃ u ∈ X, x = u ∨ x = u * t := by
  constructor
  · intro hx
    obtain ⟨u, hu, z, hz, rfl⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute (hA.commute_sup hXL) hx
    rcases hA.mem_zpowers_iff.1 hz with rfl | rfl
    · exact ⟨u, hu, Or.inl (mul_one u)⟩
    · exact ⟨u, hu, Or.inr rfl⟩
  · rintro ⟨u, hu, rfl | rfl⟩
    · exact mem_sup_left hu
    · exact mul_mem (mem_sup_left hu) (mem_sup_right (mem_zpowers t))

theorem isPGroup_sup {X : Subgroup G} (hXL : X ≤ L) (hU : IsPGroup 2 X) :
    IsPGroup 2 (X ⊔ zpowers t : Subgroup G) := by
  rintro ⟨x, hx⟩
  obtain ⟨u, hu, z, hz, rfl⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute (hA.commute_sup hXL) hx
  obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
  have hk' : u ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hz2 : z ^ 2 = 1 := by
    rcases hA.mem_zpowers_iff.1 hz with rfl | rfl
    · exact one_pow 2
    · rw [pow_two, hA.mul_self]
  have hc : Commute u z := hA.commute_sup hXL u hu z hz
  refine ⟨k + 1, Subtype.ext ?_⟩
  change (u * z) ^ 2 ^ (k + 1) = 1
  rw [hc.mul_pow, pow_succ, pow_mul u, hk', one_pow, one_mul, pow_mul' z, hz2, one_pow]

theorem relIndex_sup {X : Subgroup G} (hXL : X ≤ L) : X.relIndex (X ⊔ zpowers t) = 2 := by
  rw [relIndex_eq_two_iff]
  refine ⟨t, t_mem_sup, fun b hb => ?_⟩
  obtain ⟨u, hu, rfl | rfl⟩ := (hA.mem_sup_iff hXL).1 hb
  · refine Or.inr ⟨hu, fun h => hA.not_mem (hXL (by simpa using X.mul_mem (X.inv_mem hu) h))⟩
  · rw [mul_assoc, hA.mul_self, mul_one]
    refine Or.inl ⟨hu, fun h => hA.not_mem (hXL (by simpa using X.mul_mem (X.inv_mem hu) h))⟩

theorem card_sup [Finite G] {X : Subgroup G} (hXL : X ≤ L) :
    Nat.card (X ⊔ zpowers t : Subgroup G) = 2 * Nat.card X := by
  rw [← Subgroup.relIndex_mul_card (H := X) (K := X ⊔ zpowers t), hA.relIndex_sup hXL,
    inf_of_le_left le_sup_left]

theorem not_isSylow [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hodd : InvolutionsInOddPart L) (hUL : U ≤ L) (S : Sylow 2 G) :
    (S : Subgroup G) ≠ U ⊔ zpowers t := by
  intro hS
  have hUS : U ≤ (S : Subgroup G) := hS ▸ le_sup_left
  have hidx : U.relIndex (S : Subgroup G) = 2 := hS ▸ hA.relIndex_sup hUL
  have hQu : ∀ x : G, x⁻¹ * t * x ∉ U := by
    intro x hx
    apply hA.conj_not_mem hodd x⁻¹
    rw [inv_inv]
    exact hUL hx
  have h := thompson_transfer_lemma S hUS hidx hA.orderOf_eq hQu
  rw [pResidual_two_eq_top hG hnab] at h
  exact h (mem_top t)

theorem exists_conj_eq_mul [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hodd : InvolutionsInOddPart L) (hUL : U ≤ L) (hU : IsPGroup 2 U) {a : G} (haU : a ∈ U)
    (hZ : ∀ u ∈ U, (∀ x ∈ U, u * x = x * u) → u = 1 ∨ u = a) :
    ∃ n ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G), n * t * n⁻¹ = t * a := by
  set TH : Subgroup G := U ⊔ zpowers t with hTHdef
  have hTH : IsPGroup 2 TH := hA.isPGroup_sup hUL hU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hTH.exists_le_sylow
  have hlt : TH < S := lt_of_le_of_ne hS (fun h => hA.not_isSylow hG hnab hodd hUL S h.symm)
  obtain ⟨n, hnS, hnN, hnTH⟩ := exists_mem_normalizer_not_mem S.isPGroup' hlt
  have hTHC : TH ≤ centralizer ({t} : Set G) :=
    sup_le (hUL.trans hA.le_centralizer) (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  have hnt : n * t ≠ t * n := by
    intro hnt
    set V : Subgroup G := TH ⊔ zpowers n
    have hVS : V ≤ S := sup_le hS (zpowers_le.2 hnS)
    have hV : V = TH := hA.sylow V (sup_le hTHC (zpowers_le.2
      (mem_centralizer_singleton_iff.2 hnt))) (S.isPGroup'.to_le hVS) le_sup_left
    exact hnTH (hV ▸ mem_sup_right (mem_zpowers n))
  have hmem : n * t * n⁻¹ ∈ TH := (mem_normalizer_iff.1 hnN t).1 t_mem_sup
  have hcent : ∀ x ∈ TH, n * t * n⁻¹ * x = x * (n * t * n⁻¹) := by
    intro x hx
    have hx' : n⁻¹ * x * n⁻¹⁻¹ ∈ TH := (mem_normalizer_iff.1 (inv_mem hnN) x).1 hx
    rw [inv_inv] at hx'
    have hc : n⁻¹ * x * n * t = t * (n⁻¹ * x * n) :=
      (mem_centralizer_singleton_iff.1 (hTHC hx')).symm ▸ rfl
    calc n * t * n⁻¹ * x = n * (t * (n⁻¹ * x * n)) * n⁻¹ := by group
      _ = n * (n⁻¹ * x * n * t) * n⁻¹ := by rw [← hc]
      _ = x * (n * t * n⁻¹) := by group
  obtain ⟨u, hu, hcase⟩ := (hA.mem_sup_iff hUL).1 hmem
  have hu' : ∀ y ∈ U, u * y = y * u := by
    intro y hy
    have h1 := hcent y (mem_sup_left hy)
    have hty : y * t = t * y := hA.commute_of_mem (hUL hy)
    rcases hcase with h | h <;> rw [h] at h1
    · exact h1
    · have : u * y * t = y * u * t := by
        calc u * y * t = u * (y * t) := by group
          _ = u * (t * y) := by rw [hty]
          _ = u * t * y := by group
          _ = y * (u * t) := h1
          _ = y * u * t := by group
      exact mul_right_cancel this
  have hat : a * t = t * a := hA.commute_of_mem (hUL haU)
  rcases hZ u hu hu' with rfl | rfl <;> rcases hcase with h | h
  · exact absurd (by simpa using h) hA.ne_one
  · exact absurd (by
      rw [one_mul] at h
      calc n * t = n * t * n⁻¹ * n := by group
        _ = t * n := by rw [h]) hnt
  · exact absurd (h ▸ hUL haU) (hA.conj_not_mem hodd n)
  · exact ⟨n, hnN, h.trans hat⟩

end ShapeAB

end CFSG.EvenSmallLie.OmegaEight.Stage1
