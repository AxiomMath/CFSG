module

public import CFSG.LargeExtraspecial.AS35CS63Inn

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Timmesfeld CFSG.ComponentClassification

namespace S63

variable {X : Type} [Group X] {ζ : X} {F : Subgroup X}

theorem eq_one_or_eq_of_mem_zpowers_two (h2 : orderOf ζ = 2) {x : X} (hx : x ∈ zpowers ζ) :
    x = 1 ∨ x = ζ := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, h2]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [show ((2 : ℕ) : ℤ) = 2 by norm_num, h, zpow_zero]
  · right
    rw [show ((2 : ℕ) : ℤ) = 2 by norm_num, h, zpow_one]

theorem exists_mem_mul_centralizer {τ : X} (hτ : τ ∈ F ⊔ centralizer (F : Set X)) :
    ∃ f ∈ F, f⁻¹ * τ ∈ centralizer (F : Set X) := by
  let S₁ : Subgroup X :=
    { carrier := {x | ∃ f ∈ F, f⁻¹ * x ∈ centralizer (F : Set X)}
      mul_mem' := by
        rintro x y ⟨f, hf, hfx⟩ ⟨g, hg, hgy⟩
        refine ⟨f * g, mul_mem hf hg, ?_⟩
        have e : (f * g)⁻¹ * (x * y) = (g⁻¹ * (f⁻¹ * x) * g) * (g⁻¹ * y) := by group
        rw [e]
        refine mul_mem ?_ hgy
        have h1 := mem_centralizer_iff.mp hfx g hg
        rw [show g⁻¹ * (f⁻¹ * x) * g = f⁻¹ * x by rw [mul_assoc, ← h1]; group]
        exact hfx
      one_mem' := ⟨1, one_mem _, by rw [inv_one, one_mul]; exact one_mem _⟩
      inv_mem' := by
        rintro x ⟨f, hf, hfx⟩
        refine ⟨f⁻¹, inv_mem hf, ?_⟩
        have h3 := mem_centralizer_iff.mp (inv_mem hfx) f⁻¹ (inv_mem hf)
        have e : f⁻¹⁻¹ * x⁻¹ = f * (f⁻¹ * x)⁻¹ * f⁻¹ := by group
        rw [e]
        have h2 : f * (f⁻¹ * x)⁻¹ * f⁻¹ = (f⁻¹ * x)⁻¹ := by
          calc f * (f⁻¹ * x)⁻¹ * f⁻¹ = f * ((f⁻¹ * x)⁻¹ * f⁻¹) := by group
            _ = f * (f⁻¹ * (f⁻¹ * x)⁻¹) := by rw [h3]
            _ = (f⁻¹ * x)⁻¹ := by group
        rw [h2]
        exact inv_mem hfx }
  have hle : F ⊔ centralizer (F : Set X) ≤ S₁ :=
    sup_le (fun f hf => ⟨f, hf, by rw [inv_mul_cancel]; exact one_mem _⟩)
      (fun c hc => ⟨1, one_mem _, by rw [inv_one, one_mul]; exact hc⟩)
  exact hle hτ

namespace SmithConf

section Lift

variable (hC : SmithConf ζ F) (hs : IsSimpleGroup (UZ ζ))
include hC hs

theorem eq_of_piU_eq {y y' : X} (hy : IsConj ζ y) (hy' : IsConj ζ y')
    (h : piU ζ ⟨y, mem_normalClosure_of_isConj hy⟩ =
      piU ζ ⟨y', mem_normalClosure_of_isConj hy'⟩) : y = y' := by
  have hζ := not_mem_ZU_of_simple hs
  have hw : y⁻¹ * y' ∈ ZU ζ := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
    exact ⟨_, h, rfl⟩
  obtain ⟨k, rfl⟩ := isConj_iff.mp hy
  set w := k⁻¹ * ((k * ζ * k⁻¹)⁻¹ * y') * k with hwdef
  have hwZ : w ∈ ZU ζ := by
    have := conj_mem_ZU hw k⁻¹
    rwa [inv_inv] at this
  have hζU : ζ ∈ normalClosure ({ζ} : Set X) := subset_normalClosure (Set.mem_singleton ζ)
  have hwc : w * ζ = ζ * w := comm_of_mem_ZU hwZ hζU
  have hy₀ : IsConj ζ (k⁻¹ * y' * k) := hy'.trans (isConj_iff.mpr ⟨k⁻¹, by group⟩)
  have h1 := hC.star.eq_one_of_mul_mem_center hζ hy₀ hwZ (by rw [hwc, hwdef]; group)
  calc k * ζ * k⁻¹ = k * ζ * k⁻¹ * (k * w * k⁻¹) := by rw [h1]; group
    _ = y' := by rw [hwdef]; group

theorem conj_eq_of_conjAut_fix {τ x : X} (hτ : IsConj ζ τ)
    (h : SmithConf.conjAut ζ x (piU ζ ⟨τ, mem_normalClosure_of_isConj hτ⟩) =
      piU ζ ⟨τ, mem_normalClosure_of_isConj hτ⟩) : x * τ * x⁻¹ = τ := by
  have hτ' : IsConj ζ (x * τ * x⁻¹) := hτ.trans (isConj_iff.mpr ⟨x, rfl⟩)
  refine hC.eq_of_piU_eq hs hτ' hτ ?_
  rw [← h]
  rfl

omit hC in
theorem piU_ne_one {τ : X} (hτ : IsConj ζ τ) :
    piU ζ ⟨τ, mem_normalClosure_of_isConj hτ⟩ ≠ 1 := by
  intro h
  apply not_mem_ZU_of_simple hs
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  obtain ⟨k, rfl⟩ := isConj_iff.mp hτ
  have := conj_mem_ZU (⟨_, h, rfl⟩ : k * ζ * k⁻¹ ∈ ZU ζ) k⁻¹
  rwa [show k⁻¹ * (k * ζ * k⁻¹) * k⁻¹⁻¹ = ζ by group] at this

theorem orderOf_piU {τ : X} (hτ : IsConj ζ τ) :
    orderOf (piU ζ ⟨τ, mem_normalClosure_of_isConj hτ⟩) = 2 := by
  refine orderOf_eq_prime ?_ (piU_ne_one hs hτ)
  rw [← map_pow]
  have h2 : (⟨τ, mem_normalClosure_of_isConj hτ⟩ : ↥(normalClosure ({ζ} : Set X))) ^ 2 = 1 := by
    apply Subtype.ext
    obtain ⟨k, rfl⟩ := isConj_iff.mp hτ
    have hζ2 : ζ * ζ = 1 := hC.star.mul_self
    change (k * ζ * k⁻¹) ^ 2 = 1
    rw [pow_two]
    calc k * ζ * k⁻¹ * (k * ζ * k⁻¹) = k * (ζ * ζ) * k⁻¹ := by group
      _ = 1 := by rw [hζ2]; group
  rw [h2, map_one]

end Lift

section Iota

variable (hC : SmithConf ζ F) (hs : IsSimpleGroup (UZ ζ))
include hC hs

omit hC in
theorem conjAut_eq_iota (f : ↥(Finn ζ F)) (y : UZ ζ) :
    SmithConf.conjAut ζ (f : X) y = iota hs f * y * (iota hs f)⁻¹ := by
  rw [← conj_iota hs f, MulAut.conj_apply]

omit hC hs in
theorem conjAut_zeta {x : X} (hx : x * ζ = ζ * x) :
    SmithConf.conjAut ζ x (piU ζ (zetaU ζ)) = piU ζ (zetaU ζ) := by
  rw [conjAut_apply]
  congr 1
  apply Subtype.ext
  change x * ζ * x⁻¹ = ζ
  rw [hx, mul_inv_cancel_right]

theorem iota_range_props [Finite X] :
    (iota (F := F) hs).range ≤ centralizer ({piU ζ (zetaU ζ)} : Set (UZ ζ)) ∧
    (∀ c ∈ centralizer ({piU ζ (zetaU ζ)} : Set (UZ ζ)), ∀ n ∈ (iota (F := F) hs).range,
      c * n * c⁻¹ ∈ (iota (F := F) hs).range) ∧
    IsPGroup 2 (iota (F := F) hs).range ∧ piU ζ (zetaU ζ) ∈ (iota (F := F) hs).range ∧
    Nat.card (iota (F := F) hs).range = Nat.card (Finn ζ F) := by
  have hζF : ζ ∈ Finn ζ F := hC.zeta_mem_Finn
  refine ⟨?_, ?_, ?_, ⟨⟨ζ, hζF⟩, iota_of_mem_U hs ⟨ζ, hζF⟩ (zetaU ζ).2⟩, ?_⟩
  · rintro _ ⟨f, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (iota_comm_zeta hs f
      (mem_centralizer_singleton_iff.mp (hC.hyp.le_centralizer (Finn_le ζ F f.2))))
  · rintro c hc _ ⟨f, rfl⟩
    obtain ⟨u, rfl, hu⟩ := hC.exists_lift_of_comm hs (mem_centralizer_singleton_iff.mp hc)
    exact ⟨_, hC.iota_conj_mem hs hu f⟩
  · have hF2 : IsPGroup 2 ↥(Finn ζ F) := hC.hyp.extraspecial.1.to_le (Finn_le ζ F)
    exact hF2.of_surjective _ (iota (F := F) hs).rangeRestrict_surjective
  · rw [MonoidHom.range_eq_map, card_map_of_injective (hC.iota_injective hs), card_top]

end Iota

section Extraspecial

variable (hC : SmithConf ζ F)
include hC

theorem comm_zeta {f : X} (hf : f ∈ F) : f * ζ = ζ * f :=
  mem_centralizer_singleton_iff.mp (hC.hyp.le_centralizer hf)

theorem comm_eq_of_mem_E {a b : X} (ha : a ∈ F ⊔ centralizer (F : Set X))
    (hb : b ∈ F ⊔ centralizer (F : Set X)) : a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = ζ :=
  eq_one_or_eq_of_mem_zpowers_two hC.hyp.orderOf_eq (hC.hyp.elemAb a ha b hb).1

theorem sq_eq_of_mem_E {a : X} (ha : a ∈ F ⊔ centralizer (F : Set X)) : a * a = 1 ∨ a * a = ζ :=
  eq_one_or_eq_of_mem_zpowers_two hC.hyp.orderOf_eq (hC.hyp.elemAb a ha a ha).2

theorem zeta_ne_one : ζ ≠ 1 := by
  intro h
  have := hC.hyp.orderOf_eq
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem comm_of_eq_one_or_eq {c : X} (hc : c = 1 ∨ c = ζ) {f : X} (hf : f ∈ F) :
    c * f = f * c := by
  rcases hc with rfl | rfl
  · rw [one_mul, mul_one]
  · exact (hC.comm_zeta hf).symm

theorem card_le_two_mul_card_inf_centralizer [Finite X] {K : Subgroup X} (hKF : K ≤ F) {v : X}
    (hv : v ∈ F ⊔ centralizer (F : Set X)) :
    Nat.card K ≤ 2 * Nat.card (K ⊓ centralizer ({v} : Set X) : Subgroup X) := by
  have hcv : ∀ k ∈ K, k * v * k⁻¹ * v⁻¹ = 1 ∨ k * v * k⁻¹ * v⁻¹ = ζ := fun k hk =>
    hC.comm_eq_of_mem_E (le_sup_left (a := F) (hKF hk)) hv
  let φ : ↥K →* X := MonoidHom.mk' (fun k => (k : X) * v * (k : X)⁻¹ * v⁻¹) (by
    intro a b
    have hb := hcv b b.2
    have hab : (b : X) * v * (b : X)⁻¹ * v⁻¹ * ((a : X) * v * (a : X)⁻¹ * v⁻¹) =
        (a : X) * v * (a : X)⁻¹ * v⁻¹ * ((b : X) * v * (b : X)⁻¹ * v⁻¹) := by
      rcases hb with hb | hb <;> rcases hcv a a.2 with ha | ha <;> rw [hb, ha] <;> group
    have hba : (b : X) * v * (b : X)⁻¹ * v⁻¹ * a = a * ((b : X) * v * (b : X)⁻¹ * v⁻¹) :=
      hC.comm_of_eq_one_or_eq hb (hKF a.2)
    change ((a * b : ↥K) : X) * v * ((a * b : ↥K) : X)⁻¹ * v⁻¹ = _
    rw [Subgroup.coe_mul, ← hab]
    calc (a : X) * b * v * ((a : X) * b)⁻¹ * v⁻¹ =
        a * ((b : X) * v * (b : X)⁻¹ * v⁻¹) * v * (a : X)⁻¹ * v⁻¹ := by group
      _ = (b : X) * v * (b : X)⁻¹ * v⁻¹ * a * v * (a : X)⁻¹ * v⁻¹ := by rw [← hba]
      _ = _ := by group)
  have hker : φ.ker = (K ⊓ centralizer ({v} : Set X)).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    change (k : X) * v * (k : X)⁻¹ * v⁻¹ = 1 ↔ _
    rw [mem_inf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨k.2, ?_⟩
      calc (k : X) * v = (k : X) * v * (k : X)⁻¹ * v⁻¹ * (v * k) := by group
        _ = v * k := by rw [h, one_mul]
    · rintro ⟨-, h⟩
      calc (k : X) * v * (k : X)⁻¹ * v⁻¹ = v * k * (k : X)⁻¹ * v⁻¹ := by rw [h]
        _ = 1 := by group
  have hrange : Nat.card φ.range ≤ 2 := by
    have hle : φ.range ≤ zpowers ζ := by
      rintro _ ⟨k, rfl⟩
      rcases hcv k k.2 with h | h
      · change (k : X) * v * (k : X)⁻¹ * v⁻¹ ∈ _
        rw [h]
        exact one_mem _
      · change (k : X) * v * (k : X)⁻¹ * v⁻¹ ∈ _
        rw [h]
        exact mem_zpowers ζ
    calc Nat.card φ.range ≤ Nat.card (zpowers ζ) := card_le_of_le hle
      _ = 2 := by rw [Nat.card_zpowers, hC.hyp.orderOf_eq]
  have h1 := card_mul_index φ.ker
  rw [index_ker, hker] at h1
  have h2 : Nat.card ((K ⊓ centralizer ({v} : Set X)).subgroupOf K) =
      Nat.card (K ⊓ centralizer ({v} : Set X) : Subgroup X) :=
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2] at h1
  calc Nat.card K = Nat.card (K ⊓ centralizer ({v} : Set X) : Subgroup X) * Nat.card φ.range :=
        h1.symm
    _ ≤ Nat.card (K ⊓ centralizer ({v} : Set X) : Subgroup X) * 2 := Nat.mul_le_mul_left _ hrange
    _ = 2 * _ := mul_comm _ _

theorem eq_one_or_eq_of_forall_comm {c : X} (hc : c ∈ F) (h : ∀ f ∈ F, c * f = f * c) :
    c = 1 ∨ c = ζ :=
  (hC.mem_center_F_iff hc).mp (mem_center_iff.mpr fun g => Subtype.ext (h g g.2).symm)

theorem false_of_abelian [Finite X] {H : Subgroup X} (hHF : H ≤ F)
    (hab : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hcard : Nat.card F ≤ 2 * Nat.card H) : False := by
  have hwidth := hC.hyp.width
  by_cases htop : ∀ a ∈ F, a ∈ H
  ·
    have hc : center F = ⊤ := eq_top_iff.mpr fun x _ => mem_center_iff.mpr fun y =>
      Subtype.ext (hab y (htop y y.2) x (htop x x.2))
    have h2 := hC.hyp.extraspecial.2.2.2
    rw [hc, card_top] at h2
    omega
  push Not at htop
  obtain ⟨a, haF, haH⟩ := htop
  set H' := H.subgroupOf F with hH'
  have hcardH' : Nat.card H' = Nat.card H := Nat.card_congr (subgroupOfEquivOfLe hHF).toEquiv
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hidx : H'.index = 2 := by
    have h1 := card_mul_index H'
    have hne : H' ≠ ⊤ := fun h => haH (by
      have : (⟨a, haF⟩ : F) ∈ H' := h ▸ mem_top _
      exact mem_subgroupOf.mp this)
    have hlt := one_lt_index_of_ne_top hne
    rw [hcardH'] at h1
    have : H'.index ≤ 2 := by
      by_contra hlt2
      push Not at hlt2
      have : Nat.card H * 3 ≤ Nat.card H * H'.index := Nat.mul_le_mul_left _ hlt2
      omega
    omega
  have hCle : (H ⊓ centralizer ({a} : Set X) : Subgroup X) ≤ zpowers ζ := by
    rintro h ⟨hhH, hha'⟩
    have hha : h * a = a * h := mem_centralizer_singleton_iff.mp hha'
    have hc : ∀ f ∈ F, h * f = f * h := by
      intro f hf
      by_cases hfH : f ∈ H
      · exact hab h hhH f hfH
      · have h1 : (⟨a, haF⟩ : F)⁻¹ * ⟨f, hf⟩ ∈ H' := by
          rw [mul_mem_iff_of_index_two hidx, inv_mem_iff]
          exact ⟨fun h' => absurd (mem_subgroupOf.mp h') haH,
            fun h' => absurd (mem_subgroupOf.mp h') hfH⟩
        have h2 : a⁻¹ * f ∈ H := mem_subgroupOf.mp h1
        have h3 := hab h hhH _ h2
        calc h * f = h * a * (a⁻¹ * f) := by group
          _ = a * h * (a⁻¹ * f) := by rw [hha]
          _ = a * (h * (a⁻¹ * f)) := by group
          _ = a * ((a⁻¹ * f) * h) := by rw [h3]
          _ = f * h := by group
    rcases hC.eq_one_or_eq_of_forall_comm (hHF hhH) hc with h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact mem_zpowers ζ
  have h1 := hC.card_le_two_mul_card_inf_centralizer hHF (v := a) (le_sup_left (a := F) haF)
  have h2 : Nat.card (H ⊓ centralizer ({a} : Set X) : Subgroup X) ≤ 2 := by
    calc _ ≤ Nat.card (zpowers ζ) := card_le_of_le hCle
      _ = 2 := by rw [Nat.card_zpowers, hC.hyp.orderOf_eq]
  omega

theorem false_of_involutions_le [Finite X] {H : Subgroup X} (hHF : H ≤ F)
    (hcard : Nat.card F ≤ 2 * Nat.card H) {a : X} (haF : a ∈ F) (haH : a ∉ H)
    (hinv : ∀ f ∈ F, f * f = 1 → f ∈ H) : False := by
  have hsq : ∀ h ∈ H, a * h * (a * h) = ζ := by
    intro h hh
    have hahF : a * h ∈ F := mul_mem haF (hHF hh)
    rcases hC.sq_eq_of_mem_E (le_sup_left (a := F) hahF) with h1 | h1
    · exact absurd (by simpa using mul_mem (hinv _ hahF h1) (inv_mem hh)) haH
    · exact h1
  have ha2 : a * a = ζ := by simpa using hsq 1 (one_mem _)
  have hinvert : ∀ h ∈ H, a⁻¹ * h * a = h⁻¹ := by
    intro h hh
    calc a⁻¹ * h * a = a⁻¹ * (a⁻¹ * (a * h * (a * h)) * h⁻¹) := by group
      _ = a⁻¹ * (a⁻¹ * (a * a) * h⁻¹) := by rw [hsq h hh, ha2]
      _ = h⁻¹ := by group
  refine hC.false_of_abelian hHF (fun h hh k hk => ?_) hcard
  have e1 := hinvert (h * k) (mul_mem hh hk)
  have e2 : a⁻¹ * (h * k) * a = h⁻¹ * k⁻¹ := by
    calc a⁻¹ * (h * k) * a = (a⁻¹ * h * a) * (a⁻¹ * k * a) := by group
      _ = h⁻¹ * k⁻¹ := by rw [hinvert h hh, hinvert k hk]
  rw [e2, mul_inv_rev] at e1
  calc h * k = (k⁻¹ * h⁻¹)⁻¹ := by group
    _ = (h⁻¹ * k⁻¹)⁻¹ := by rw [e1]
    _ = k * h := by group

end Extraspecial

section Outer

variable [Finite X] (hC : SmithConf ζ F)
include hC

theorem Finn_eq_of_odd (hodd : Odd (Nat.card (OuterAutomorphisms.Outer (UZ ζ)))) :
    Finn ζ F = F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hC.card_le_mul_card_Finn (k := 1) (fun H hH => by
    have h2 : IsPGroup 2 H := fun h => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, pow_two]
      exact hH h h.2)⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp h2
    have hdvd : Nat.card H ∣ Nat.card (OuterAutomorphisms.Outer (UZ ζ)) :=
      card_subgroup_dvd_card H
    rw [hn] at hdvd
    rcases n with _ | n
    · rw [hn, pow_zero]
    · exfalso
      rw [pow_succ] at hdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (dvd_of_mul_left_dvd hdvd)))
  rw [one_mul] at h
  exact eq_of_le_of_card_ge (Finn_le ζ F) h

theorem card_le_two_mul_card_Finn_of_injective {C : Type*} [Group C] [IsCyclic C]
    (ψ : OuterAutomorphisms.Outer (UZ ζ) →* C) (hψ : Function.Injective ψ) :
    Nat.card F ≤ 2 * Nat.card (Finn ζ F) :=
  hC.card_le_mul_card_Finn (k := 2) fun H hH => by
    have hexp : Monoid.exponent ↥(H.map ψ) ∣ 2 := by
      refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
      obtain ⟨_, ⟨h, hh, rfl⟩⟩ := g
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, pow_two, hH h hh, map_one]
    rw [IsCyclic.exponent_eq_card, card_map_of_injective hψ] at hexp
    exact Nat.le_of_dvd (by norm_num) hexp

end Outer

section Cases

variable [Finite X] (hC : SmithConf ζ F)
include hC

omit [Finite X] in
theorem false_of_forall_fix (hs : IsSimpleGroup (UZ ζ)) {τ : X} (hτ : τ ∈ CorB.conjCent ζ)
    (hne : τ ≠ ζ)
    (h : ∀ f ∈ F, SmithConf.conjAut ζ f (piU ζ ⟨τ, mem_normalClosure_of_isConj hτ.2⟩) =
      piU ζ ⟨τ, mem_normalClosure_of_isConj hτ.2⟩) : False := by
  obtain ⟨f, hf, hfτ⟩ := hC.fusionF τ hτ hne
  rw [hC.conj_eq_of_conjAut_fix hs hτ.2 (h f hf)] at hfτ
  exact hC.zeta_ne_one (mul_eq_right.mp hfτ.symm)

theorem false_of_involutions_comm {τ : X} (hτ : τ ∈ CorB.conjCent ζ) (hne : τ ≠ ζ)
    (h : ∀ f ∈ F, f * f = 1 → f * τ * f⁻¹ = τ) : False := by
  have hτE := hC.hyp.conj_mem_E τ hτ.2 hτ.1
  obtain ⟨a, haF, haτ⟩ := hC.fusionF τ hτ hne
  refine hC.false_of_involutions_le (H := F ⊓ centralizer ({τ} : Set X)) inf_le_left
    (hC.card_le_two_mul_card_inf_centralizer le_rfl hτE) haF ?_ ?_
  · rintro ⟨-, ha⟩
    have h1 : a * τ * a⁻¹ = τ := by
      rw [mem_centralizer_singleton_iff.mp ha, mul_inv_cancel_right]
    rw [h1] at haτ
    exact hC.zeta_ne_one (mul_eq_right.mp haτ.symm)
  · intro f hf hff
    refine ⟨hf, mem_centralizer_singleton_iff.mpr ?_⟩
    calc f * τ = f * τ * f⁻¹ * f := by group
      _ = τ * f := by rw [h f hf hff]

end Cases

end SmithConf

end S63

end CFSG.LargeExtraspecial
