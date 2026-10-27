module

public import CFSG.Holt.H78.Sec4Prop46BEnd
public import CFSG.Holt.H78.Sec4Lemma48

public section


namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open CFSG.GH74.Uniqueness.Bender
open scoped Pointwise

section General


theorem eq_or_eq_of_card_eq_four {G : Type*} [Group G] {Y : Subgroup G} [Finite Y]
    (hY : Nat.card Y = 4) {a b : G} (ha : a ∈ Y) (hb : b ∈ Y) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) (hab1 : a * b ≠ 1) (haba : a * b ≠ a) (habb : a * b ≠ b) {y : G} (hy : y ∈ Y) :
    y = 1 ∨ y = a ∨ y = b ∨ y = a * b := by
  by_contra h
  push Not at h
  obtain ⟨hy1, hya, hyb, hyab⟩ := h
  have hsub : ({y, a * b, b, a, 1} : Set G) ⊆ (Y : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact hy
    · exact mul_mem ha hb
    · exact hb
    · exact ha
    · exact one_mem _
  have h5 : ({y, a * b, b, a, 1} : Set G).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem (by simp [hyab, hyb, hya, hy1]),
      Set.ncard_insert_of_notMem (by simp [habb, haba, hab1]),
      Set.ncard_insert_of_notMem (by simp [hab.symm, hb1]),
      Set.ncard_pair ha1]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hYc : (Y : Set G).ncard = 4 := by rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hY]
  omega

theorem eq_one_or_eq_of_commute_of_fix {Y : Type*} [Finite Y] {π ρ : Equiv.Perm Y}
    (hπ2 : π * π = 1) (hM : {δ | π δ ≠ δ}.ncard = 2) (hρπ : ρ * π = π * ρ)
    (hρ : ∀ δ, π δ = δ → ρ δ = δ) : ρ = 1 ∨ ρ = π := by
  obtain ⟨d, d', hdd', hM2⟩ := Set.ncard_eq_two.mp hM
  have hd : π d ≠ d := by
    have : d ∈ {δ | π δ ≠ δ} := by rw [hM2]; exact Or.inl rfl
    exact this
  have hππ : ∀ δ, π (π δ) = δ := fun δ => by rw [← Equiv.Perm.mul_apply, hπ2, Equiv.Perm.one_apply]
  have hmoved : ∀ δ, π δ ≠ δ → δ = d ∨ δ = π d := fun δ hδ => by
    have hδM : δ ∈ ({d, d'} : Set Y) := by rw [← hM2]; exact hδ
    have hπdM : π d ∈ ({d, d'} : Set Y) := by
      rw [← hM2]
      show π (π d) ≠ π d
      rw [hππ]
      exact fun h => hd h.symm
    rcases hδM with rfl | hδ'
    · exact Or.inl rfl
    · rcases hπdM with h | h
      · exact absurd h hd
      · rw [Set.mem_singleton_iff] at hδ' h
        exact Or.inr (hδ'.trans h.symm)
  have hρc : ∀ δ, ρ (π δ) = π (ρ δ) := fun δ => by
    rw [← Equiv.Perm.mul_apply, hρπ, Equiv.Perm.mul_apply]
  have hρd : ρ d = d ∨ ρ d = π d := by
    refine hmoved _ fun h => hd ?_
    have h' : ρ (π d) = ρ d := by rw [hρc, h]
    exact ρ.injective h'
  rcases hρd with h | h
  · refine Or.inl (Equiv.ext fun δ => ?_)
    rw [Equiv.Perm.one_apply]
    by_cases hδ : π δ = δ
    · exact hρ δ hδ
    · rcases hmoved δ hδ with rfl | rfl
      · exact h
      · rw [hρc, h]
  · refine Or.inr (Equiv.ext fun δ => ?_)
    by_cases hδ : π δ = δ
    · rw [hρ δ hδ, hδ]
    · rcases hmoved δ hδ with rfl | rfl
      · exact h
      · rw [hρc, h]

theorem card_le_two_of_injective {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    {Y : Type*} [Finite Y] (hY : Nat.card Y = 3) (f : Q →* Equiv.Perm Y)
    (hf : Function.Injective f) : Nat.card Q ≤ 2 := by
  have hdvd := Subgroup.card_dvd_of_injective f hf
  rw [Nat.card_perm, hY] at hdvd
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hQ)
  rw [hk] at hdvd ⊢
  have : k ≤ 1 := by
    by_contra h
    have h4 : 2 ^ 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
    have := h4.trans hdvd
    norm_num [Nat.factorial] at this
  interval_cases k <;> norm_num

theorem ncard_setOf_and_eq_one {Y : Type*} {b : Set Y} {Q : Y → Prop} {x₀ : Y} (h0 : x₀ ∈ b)
    (hQ0 : Q x₀) (hQ : ∀ x ∈ b, Q x → x = x₀) : {x | x ∈ b ∧ Q x}.ncard = 1 :=
  Set.ncard_eq_one.mpr ⟨x₀, Set.ext fun x => ⟨fun h => hQ x h.1 h.2, fun h => h ▸ ⟨h0, hQ0⟩⟩⟩

end General

section Lemma51

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β γ : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

namespace Prop46CaseB

variable (hC : Prop46CaseB G Ω α β γ v P)
include hC

theorem exists_commute_fixedBy_eq (hS : Sec4Setting G Ω) {s : G} (hs : IsConj v s)
    (hsv : Commute s v) (hsΦ : fixedBy Ω s ≠ fixedBy Ω v) {τ : G} (hτ2 : τ * τ = 1)
    (hτs : Commute τ s) (hsτ : s * τ ∈ longInv G Ω) (hτJ : τ ∉ longInv G Ω) :
    ∃ r : G, r ≠ 1 ∧ r ≠ s ∧ r * r = 1 ∧ Commute r s ∧ Commute r τ ∧
      fixedBy Ω r = fixedBy Ω s ∧ fixedBy Ω (r * s) = fixedBy Ω s := by
  classical
  obtain ⟨h4, -⟩ := hC.exists_Y_of_witness hS hs hsv hsΦ
  obtain ⟨g, rfl⟩ := isConj_iff.mp hs
  set r₀ := g⁻¹ * τ * g with hr₀
  have hτr₀ : τ = g * r₀ * g⁻¹ := by rw [hr₀]; group
  have hr₀v : Commute r₀ v := by
    have h := hτs.eq
    change g⁻¹ * τ * g * v = v * (g⁻¹ * τ * g)
    calc g⁻¹ * τ * g * v = g⁻¹ * (τ * (g * v * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * v * g⁻¹) * τ) * g := by rw [h]
      _ = v * (g⁻¹ * τ * g) := by group
  have hr₀2 : r₀ * r₀ = 1 := by
    rw [hr₀, show g⁻¹ * τ * g * (g⁻¹ * τ * g) = g⁻¹ * (τ * τ) * g by group, hτ2, mul_one,
      inv_mul_cancel]
  obtain ⟨Y, hYR, hvY, hYmem, hYr, hYz⟩ := hC.exists_Y hS hr₀v hr₀2
  have hY2 : ∀ y ∈ Y, y * y = 1 := fun y hy => (hYmem y hy).1
  have hY4 : Nat.card Y = 4 :=
    (hC.card_eq_card_rootCenter hYR hY2 hYz).trans h4
  have hv1 : v ≠ 1 := fun h => by
    have := hC.orderOf_v
    rw [h, orderOf_one] at this
    norm_num at this
  obtain ⟨u₁, hu₁, u₂, hu₂, h1, h2, h12⟩ :=
    exists_ne_one_ne_of_two_lt_card (Y := Y) (by rw [hY4]; norm_num)
  obtain ⟨y₀, hy₀, hy₀1, hy₀v⟩ : ∃ y₀ ∈ Y, y₀ ≠ 1 ∧ y₀ ≠ v := by
    by_cases h : u₁ = v
    · exact ⟨u₂, hu₂, h2, fun h' => h12 (h.trans h'.symm)⟩
    · exact ⟨u₁, hu₁, h1, h⟩
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hC.v_mul_v
  have hy₀inv : y₀⁻¹ = y₀ := inv_eq_of_mul_eq_one_right (hY2 y₀ hy₀)
  have hyv1 : y₀ * v ≠ 1 := fun h => hy₀v (by rw [mul_eq_one_iff_eq_inv, hvinv] at h; exact h)
  have hyvy : y₀ * v ≠ y₀ := fun h => hv1 (by simpa using h)
  have hyvv : y₀ * v ≠ v := fun h => hy₀1 (by simpa using h)
  have hc1 : r₀ * y₀ * r₀⁻¹ ≠ 1 := fun h => hy₀1 (by
    rw [mul_inv_eq_one, mul_eq_left] at h
    exact h)
  have hcv : r₀ * y₀ * r₀⁻¹ ≠ v := fun h => hy₀v (by
    have : y₀ = r₀⁻¹ * v * r₀ := by rw [← h]; group
    rw [this, mul_assoc, ← hr₀v.eq, ← mul_assoc, inv_mul_cancel, one_mul])
  have hfix : ∀ {y : G}, y ∈ Y → y ≠ 1 → fixedBy Ω (g * y * g⁻¹) = fixedBy Ω (g * v * g⁻¹) :=
    fun hy hy1 => by
      rw [← smul_fixedBy, ← smul_fixedBy, (hC.isConj_and_fixedBy_eq hS hYR hYmem hy hy1).2]
  have hcomm : Commute y₀ v := commute_of_forall_mul_self hY2 hy₀ hvY
  refine ⟨g * y₀ * g⁻¹, fun h => hy₀1 ?_, fun h => hy₀v ?_, ?_, ?_, ?_, hfix hy₀ hy₀1, ?_⟩
  · rw [mul_inv_eq_one, mul_eq_left] at h
    exact h
  · rw [mul_left_inj, mul_right_inj] at h
    exact h
  · rw [show g * y₀ * g⁻¹ * (g * y₀ * g⁻¹) = g * (y₀ * y₀) * g⁻¹ by group, hY2 y₀ hy₀, mul_one,
      mul_inv_cancel]
  · change g * y₀ * g⁻¹ * (g * v * g⁻¹) = g * v * g⁻¹ * (g * y₀ * g⁻¹)
    rw [show g * y₀ * g⁻¹ * (g * v * g⁻¹) = g * (y₀ * v) * g⁻¹ by group, hcomm.eq]
    group
  · rcases eq_or_eq_of_card_eq_four hY4 hy₀ hvY hy₀1 hv1 hy₀v hyv1 hyvy hyvv (hYr y₀ hy₀) with
      h | h | h | h
    · exact absurd h hc1
    · change g * y₀ * g⁻¹ * τ = τ * (g * y₀ * g⁻¹)
      rw [hτr₀]
      have h' : y₀ * r₀ = r₀ * y₀ := by
        calc y₀ * r₀ = r₀ * y₀ * r₀⁻¹ * r₀ := by rw [h]
          _ = r₀ * y₀ := by group
      calc g * y₀ * g⁻¹ * (g * r₀ * g⁻¹) = g * (y₀ * r₀) * g⁻¹ := by group
        _ = g * (r₀ * y₀) * g⁻¹ := by rw [h']
        _ = g * r₀ * g⁻¹ * (g * y₀ * g⁻¹) := by group
    · exact absurd h hcv
    ·
      exfalso
      apply hτJ
      have hJ1 : v * r₀ ∈ longInv G Ω := by
        have := conj_mem_longInv hsτ g⁻¹
        rwa [show g⁻¹ * (g * v * g⁻¹ * τ) * g⁻¹⁻¹ = v * r₀ by rw [hr₀]; group] at this
      have hJ2 : r₀ ∈ longInv G Ω := by
        have := conj_mem_longInv hJ1 y₀
        rwa [show y₀ * (v * r₀) * y₀⁻¹ = r₀ by
          have h' : r₀ * y₀ = y₀ * v * r₀ := by
            calc r₀ * y₀ = r₀ * y₀ * r₀⁻¹ * r₀ := by group
              _ = y₀ * v * r₀ := by rw [h]
          calc y₀ * (v * r₀) * y₀⁻¹ = y₀ * v * r₀ * y₀⁻¹ := by group
            _ = r₀ * y₀ * y₀⁻¹ := by rw [h']
            _ = r₀ := by group] at this
      rw [hτr₀]
      exact conj_mem_longInv hJ2 g
  · rw [show g * y₀ * g⁻¹ * (g * v * g⁻¹) = g * (y₀ * v) * g⁻¹ by group]
    exact hfix (mul_mem hy₀ hvY) hyv1

theorem pPrimeCore_centralizerImage_eq_bot (hS : Sec4Setting G Ω) {s : G} (hs : IsConj v s)
    (hsv : Commute s v) (hsΦ : fixedBy Ω s ≠ fixedBy Ω v) {τ : G} (hτ2 : τ * τ = 1)
    (hτs : Commute τ s) (hsτ : s * τ ∈ longInv G Ω) (hτJ : τ ∉ longInv G Ω)
    (hsα : s • α = α) (hτα : τ • α = α) (hFτ : ∀ ω : Ω, s • ω = ω → τ • ω = ω → ω = α)
    (h3 : 3 ≤ Nat.card (fixSet Ω (Subgroup.zpowers τ))) :
    CFSG.pPrimeCore 2 (centralizerImage Ω (Subgroup.zpowers τ)) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, -, -, hr2, hrs, hrτ, hFr, hFrs⟩ :=
    hC.exists_commute_fixedBy_eq hS hs hsv hsΦ hτ2 hτs hsτ hτJ
  have hs2 := hC.mul_self_eq_one_of_isConj hs
  set V := Subgroup.zpowers τ with hVdef
  have hV : IsPGroup 2 V := isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [pow_one, sq, hτ2])
  have hstar := hS.star_centralizerImage hV h3
  have hrC : r ∈ Subgroup.centralizer (V : Set G) := mem_centralizer_zpowers_iff_commute.mpr hrτ
  have hsC : s ∈ Subgroup.centralizer (V : Set G) :=
    mem_centralizer_zpowers_iff_commute.mpr hτs.symm
  have hmemV : ∀ {ω : Ω}, ω ∈ fixSet Ω V ↔ τ • ω = ω := fun {ω} => by
    rw [hVdef, fixSet_zpowers]; exact Iff.rfl
  set a : fixSet Ω V := ⟨α, hmemV.mpr hτα⟩ with ha
  set x : centralizerImage Ω V := centralizerImageElt hrC with hx
  set y : centralizerImage Ω V := centralizerImageElt hsC with hy
  have hxδ : ∀ δ : fixSet Ω V, ((x • δ : fixSet Ω V) : Ω) = r • (δ : Ω) := fun δ => rfl
  have hyδ : ∀ δ : fixSet Ω V, ((y • δ : fixSet Ω V) : Ω) = s • (δ : Ω) := fun δ => rfl
  have hrα : r • α = α := by
    have : α ∈ fixedBy Ω r := by rw [hFr]; exact hsα
    exact this
  have hrsα : (r * s) • α = α := by rw [mul_smul, hsα, hrα]
  have honly : ∀ {g : G}, fixedBy Ω g = fixedBy Ω s → ∀ δ : fixSet Ω V, g • (δ : Ω) = δ →
      δ = a := fun {g} hg δ hδ => by
    have hδs : s • (δ : Ω) = δ := by
      have : (δ : Ω) ∈ fixedBy Ω g := hδ
      rw [hg] at this
      exact this
    exact Subtype.ext (hFτ _ hδs (hmemV.mp δ.2))
  set N := CFSG.pPrimeCore 2 (centralizerImage Ω V) with hN
  have hNodd : Odd (Nat.card N) := odd_card_pPrimeCore_two
  have hxa : x • a = a := Subtype.ext hrα
  have hya : y • a = a := Subtype.ext hsα
  have key := ncard_fixed_orbit_mul (N := N) hNodd (γ := a) hxa hya
    (fun δ _ => Subtype.ext (by rw [hxδ, hxδ, smul_smul, hr2, one_smul]))
    (fun δ _ => Subtype.ext (by rw [hyδ, hyδ, smul_smul, hs2, one_smul]))
    (fun δ _ => Subtype.ext (by rw [hxδ, hyδ, hyδ, hxδ, smul_smul, smul_smul, hrs.eq]))
  have e1 : {δ | δ ∈ orbit N a ∧ x • δ = δ}.ncard = 1 :=
    ncard_setOf_and_eq_one (mem_orbit_self a) hxa fun δ _ hδ =>
      honly hFr δ (congrArg Subtype.val hδ)
  have e2 : {δ | δ ∈ orbit N a ∧ y • δ = δ}.ncard = 1 :=
    ncard_setOf_and_eq_one (mem_orbit_self a) hya fun δ _ hδ =>
      honly rfl δ (congrArg Subtype.val hδ)
  have e3 : {δ | δ ∈ orbit N a ∧ x • y • δ = δ}.ncard = 1 :=
    ncard_setOf_and_eq_one (mem_orbit_self a) (by rw [hya, hxa]) fun δ _ hδ =>
      honly hFrs δ (by rw [mul_smul]; exact congrArg Subtype.val hδ)
  have e4 : {δ | δ ∈ orbit N a ∧ x • δ = δ ∧ y • δ = δ}.ncard = 1 :=
    ncard_setOf_and_eq_one (mem_orbit_self a) ⟨hxa, hya⟩ fun δ _ hδ =>
      honly hFr δ (congrArg Subtype.val hδ.1)
  rw [e1, e2, e3, e4] at key
  have horb : orbit N a = {a} := by
    have h1 : (orbit N a).ncard = 1 := by simpa using key.symm
    obtain ⟨b, hb⟩ := Set.ncard_eq_one.mp h1
    rw [hb, show b = a from (Set.mem_singleton_iff.mp (hb ▸ mem_orbit_self a)).symm]
  have htr := hstar.isPretransitive
  refine (Subgroup.eq_bot_iff_forall N).mpr fun n hn => Subtype.ext (Equiv.ext fun δ => ?_)
  obtain ⟨h, rfl⟩ := exists_smul_eq (centralizerImage Ω V) a δ
  have hconj : h⁻¹ * n * h ∈ N := by
    have := (inferInstance : N.Normal).conj_mem n hn h⁻¹
    rwa [inv_inv] at this
  have hfixa : (h⁻¹ * n * h) • a = a := by
    have : (⟨_, hconj⟩ : N) • a ∈ orbit N a := MulAction.mem_orbit _ _
    rw [horb] at this
    exact this
  change (n • (h • a) : fixSet Ω V) = h • a
  calc n • (h • a) = h • ((h⁻¹ * n * h) • a) := by
        rw [smul_smul, smul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    _ = h • a := by rw [hfixa]

end Prop46CaseB

end Lemma51

section Tau

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β γ : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

namespace Prop46CaseB

variable (hC : Prop46CaseB G Ω α β γ v P)
include hC

theorem exists_Y_tau (hS : Sec4Setting G Ω) {s : G} (hs : IsConj v s) (hsv : Commute s v)
    (hsΦ : fixedBy Ω s ≠ fixedBy Ω v) (hsα : s • α = α) :
    Nat.card (rootCenter (seRadical (twoPointJ G Ω α β) ⟨γ, hC.mem_holtDelta⟩)) = 4 ∧
    ∃ Y : Subgroup G, Y ≤ caseBRad G Ω α β ⟨γ, hC.mem_holtDelta⟩ ∧ v ∈ Y ∧
      (∀ y ∈ Y, y * y = 1 ∧ Commute y v ∧ ∀ ω : Ω, v • ω = ω → y • ω = ω) ∧
      (∀ y ∈ Y, s * y * s⁻¹ ∈ Y) ∧ (¬ ∀ y ∈ Y, Commute s y) ∧
      ∃ t' ∈ longInvAt G Ω α, Commute t' s ∧ (∀ y ∈ Y, Commute t' y) ∧ Commute t' v ∧
        ∀ p ∈ P, t' • ((p • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) : _) : Ω) =
          ((p⁻¹ • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) : _) : Ω) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs2 := hC.mul_self_eq_one_of_isConj hs
  obtain ⟨h4, Y, hYR, hvY, hYmem, hYs, -, hnc⟩ := hC.exists_Y_of_witness hS hs hsv hsΦ
  have hY2 : IsPGroup 2 Y := fun y => ⟨1, Subtype.ext (by
    simp only [pow_one, sq, Subgroup.coe_mul, Subgroup.coe_one]; exact (hYmem y y.2).1)⟩
  have hYC : ∀ y ∈ Y, ∀ p ∈ P,
      y • ((p • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) : _) : Ω) =
        ((p • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) : _) : Ω) := fun y hy p _ =>
    (hYmem y hy).2.2 _ ((p • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v))).2 v
      (Subgroup.mem_zpowers v))
  obtain ⟨t', ht', ht'c⟩ := hC.exists_mem_longInvAt_centralizer_sup hS hsv hs2 hsα hY2 hYC hYs
  have ht's : Commute t' s := (Subgroup.mem_centralizer_iff.mp ht'c s
    ((le_sup_right : Subgroup.zpowers s ≤ _) (Subgroup.mem_zpowers s))).symm
  have ht'Y : ∀ y ∈ Y, Commute t' y := fun y hy => (Subgroup.mem_centralizer_iff.mp ht'c y
    ((le_sup_left : Y ≤ _) hy)).symm
  have ht'v : Commute t' v := ht'Y v hvY
  refine ⟨h4, Y, hYR, hvY, hYmem, hYs, hnc, t', ht', ht's, ht'Y, ht'v, fun p hp => ?_⟩
  refine hC.smul_eq_inv_of_fix ht'v (mul_self_eq_one_of_mem_longInv ht'.1) ht'.2
    (fun q _ hq => ?_) hp
  obtain ⟨ω, -, hω⟩ := ht'.1.2
  exact Subtype.ext ((hω _ hq).trans (hω α ht'.2).symm)


theorem exists_tau_of_smul_eq_inv (hS : Sec4Setting G Ω) {s : G} (hs : IsConj v s)
    (hsv : Commute s v) (hsΦ : fixedBy Ω s ≠ fixedBy Ω v) (hsα : s • α = α)
    {p₀ : typeLSection G Ω v} (hp₀ : p₀ ∈ P)
    (hp₀β : ((p₀ • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) : _) : Ω) = β)
    (hH : s • β = ((p₀⁻¹ • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) : _) : Ω)) :
    ∃ τ : G, τ * τ = 1 ∧ Commute τ v ∧ Commute τ s ∧ s * τ ∈ longInvAt G Ω α ∧ τ • α = α ∧
      τ • β = β ∧ τ • γ = γ ∧ (∀ ω : Ω, s • ω = ω → τ • ω = ω → ω = α) ∧
      Nat.card (holtDelta G Ω α β) = 5 ∧ twoPointSection G Ω α β = ⊤ ∧
      ∃ hτP : τ ∈ stabilizer G ({α, β} : Set Ω),
        {δ | twoPointHom G Ω α β ⟨τ, hτP⟩ δ ≠ δ}.ncard = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs2 := hC.mul_self_eq_one_of_isConj hs
  obtain ⟨h4, Y, hYR, hvY, hYmem, hYs, hnc, t', ht', ht's, ht'Y, ht'v, ht'C⟩ :=
    hC.exists_Y_tau hS hs hsv hsΦ hsα
  have ht'β : t' • β = s • β := by
    rw [hH]
    conv_lhs => rw [← hp₀β]
    exact ht'C p₀ hp₀
  have ht'2 := mul_self_eq_one_of_mem_longInv ht'.1
  set τ := s * t' with hτ
  have hτ2 : τ * τ = 1 := by
    rw [hτ, show s * t' * (s * t') = s * s * (t' * t') by
      rw [mul_assoc, ← mul_assoc t', ht's.eq]; group, hs2, ht'2, one_mul]
  have hτv : Commute τ v := hsv.mul_left ht'v
  have hτα : τ • α = α := by rw [hτ, mul_smul, ht'.2, hsα]
  have hτβ : τ • β = β := by rw [hτ, mul_smul, ht'β, smul_smul, hs2, one_smul]
  have hτP : τ ∈ stabilizer G ({α, β} : Set Ω) := stabilizer_inf_le_stabilizer_pair α β
    (Subgroup.mem_inf.mpr ⟨mem_stabilizer_iff.mpr hτα, mem_stabilizer_iff.mpr hτβ⟩)
  have hτγ : τ • γ = γ :=
    (hC.fixed_iff _ (smul_mem_holtDelta_of_mem_pair hτP hC.mem_holtDelta)).mp (by
      rw [← mul_smul, ← hτv.eq, mul_smul, hC.smul_γ])
  have hFτ : ∀ ω : Ω, s • ω = ω → τ • ω = ω → ω = α := fun ω hsω hτω => by
    have h' : t' • ω = ω := by
      rw [hτ, mul_smul, ← mul_smul, ← ht's.eq, mul_smul, hsω] at hτω
      exact hτω
    obtain ⟨ω₀, -, hω₀⟩ := ht'.1.2
    exact (hω₀ ω h').trans (hω₀ α ht'.2).symm
  push Not at hnc
  obtain ⟨y, hyY, hsy⟩ := hnc
  have hτy : ¬ Commute τ y := fun h => hsy (by
    have h1 := h.eq
    have h2 := (ht'Y y hyY).eq
    change s * y = y * s
    have : s * y * t' = y * s * t' := by
      calc s * y * t' = s * (y * t') := by group
        _ = s * (t' * y) := by rw [← h2]
        _ = s * t' * y := by group
        _ = y * (s * t') := h1
        _ = y * s * t' := by group
    exact mul_right_cancel this)
  have hxN := twoPointHom_mem_normalizer hτP
  have hxγ : twoPointHom G Ω α β ⟨τ, hτP⟩ ⟨γ, hC.mem_holtDelta⟩ = ⟨γ, hC.mem_holtDelta⟩ :=
    Subtype.ext hτγ
  have hx2 : twoPointHom G Ω α β ⟨τ, hτP⟩ * twoPointHom G Ω α β ⟨τ, hτP⟩ = 1 := by
    rw [← map_mul, show (⟨τ, hτP⟩ * ⟨τ, hτP⟩ : stabilizer G ({α, β} : Set Ω)) = 1 from
      Subtype.ext hτ2, map_one]
  obtain ⟨hyP, hyα, hyβ, hyZ⟩ := mem_caseBRad.mp (hYR hyY)
  have hxz : twoPointHom G Ω α β ⟨τ, hτP⟩ * twoPointHom G Ω α β ⟨y, hyP⟩ ≠
      twoPointHom G Ω α β ⟨y, hyP⟩ * twoPointHom G Ω α β ⟨τ, hτP⟩ := fun h => hτy (by
    have hτyY : τ * y * τ⁻¹ ∈ Y := by
      have : τ * y * τ⁻¹ = s * (t' * y * t'⁻¹) * s⁻¹ := by rw [hτ]; group
      rw [this, (ht'Y y hyY).eq, mul_inv_cancel_right]
      exact hYs y hyY
    have hcY := mul_mem hτyY (inv_mem hyY)
    have hcP : τ * y * τ⁻¹ * y⁻¹ ∈ stabilizer G ({α, β} : Set Ω) :=
      mul_mem (mul_mem (mul_mem hτP hyP) (inv_mem hτP)) (inv_mem hyP)
    have hc1 : twoPointHom G Ω α β ⟨_, hcP⟩ = 1 := by
      rw [show (⟨_, hcP⟩ : stabilizer G ({α, β} : Set Ω)) =
        ⟨τ, hτP⟩ * ⟨y, hyP⟩ * ⟨τ, hτP⟩⁻¹ * ⟨y, hyP⟩⁻¹ from rfl, map_mul, map_mul,
        map_mul, map_inv, map_inv, h, mul_inv_cancel_right, mul_inv_cancel]
    have hyα' : y⁻¹ • α = α := by rw [inv_smul_eq_iff, hyα]
    have hyβ' : y⁻¹ • β = β := by rw [inv_smul_eq_iff, hyβ]
    have hτα' : τ⁻¹ • α = α := by rw [inv_smul_eq_iff, hτα]
    have hτβ' : τ⁻¹ • β = β := by rw [inv_smul_eq_iff, hτβ]
    have hcα : (τ * y * τ⁻¹ * y⁻¹) • α = α := by
      rw [mul_smul, hyα', mul_smul, hτα', mul_smul, hyα, hτα]
    have hcβ : (τ * y * τ⁻¹ * y⁻¹) • β = β := by
      rw [mul_smul, hyβ', mul_smul, hτβ', mul_smul, hyβ, hτβ]
    have hc := hC.eq_one_of_twoPointHom_eq_one hcP hcα hcβ (hYmem _ hcY).1 hc1
    change τ * y = y * τ
    calc τ * y = τ * y * τ⁻¹ * y⁻¹ * (y * τ) := by group
      _ = y * τ := by rw [hc, one_mul])
  obtain ⟨hxL, h5, h60⟩ := hC.isNaturalSE.card_eq_five_of_not_commute hxN hxγ hx2 hyZ hxz h4
  have hG : twoPointSection G Ω α β = ⊤ := by
    have hxG := twoPointHom_mem_twoPointSection (G := G) (Ω := Ω) (α := α) (β := β) ⟨τ, hτP⟩
    have hNG := twoPointJ_le_twoPointSection (G := G) (Ω := Ω) α β
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hNG
    have hNpos : 0 < Nat.card (twoPointJ G Ω α β) := Nat.card_pos
    have hN60 : 60 ≤ Nat.card (twoPointJ G Ω α β) := Nat.le_of_dvd hNpos h60
    have hk1 : k ≠ 1 := fun h => hxL ((Subgroup.eq_of_le_of_card_ge hNG
      (by rw [hk, h, mul_one])) ▸ hxG)
    have hk0 : k ≠ 0 := fun h => by
      have : 0 < Nat.card (twoPointSection G Ω α β) := Nat.card_pos
      rw [hk, h, mul_zero] at this; omega
    have hle : Nat.card (twoPointSection G Ω α β) ≤ 120 := by
      have := Subgroup.card_le_card_group (twoPointSection G Ω α β)
      rwa [Nat.card_perm, h5] at this
    have h2N : 2 * Nat.card (twoPointJ G Ω α β) ≤ Nat.card (twoPointSection G Ω α β) := by
      rw [hk, mul_comm 2]; exact Nat.mul_le_mul_left _ (by omega)
    have h120 : Nat.card (twoPointSection G Ω α β) = 120 := by omega
    exact Subgroup.eq_top_of_card_eq _ (by rw [h120, Nat.card_perm, h5]; rfl)
  have h5' : Fintype.card (holtDelta G Ω α β) = 5 := by rwa [← Nat.card_eq_fintype_card]
  have hNA := hC.isNaturalSE.eq_alternatingGroup_of_card_eq_five h5'
  set π := twoPointHom G Ω α β ⟨τ, hτP⟩ with hπ
  have hπ2 : π ^ 2 = 1 := by rw [sq]; exact hx2
  have hπA : π ∉ alternatingGroup (holtDelta G Ω α β) := by rw [← hNA]; exact hxL
  rw [mem_alternatingGroup_iff_four_dvd_card_support hπ2] at hπA
  have hev := Equiv.Perm.two_dvd_card_support hπ2
  have hle : π.support.card ≤ 5 := h5' ▸ Finset.card_le_univ _
  have hsupp : π.support.card = 2 := by omega
  have hsτ : s * τ ∈ longInvAt G Ω α := by rw [hτ, ← mul_assoc, hs2, one_mul]; exact ht'
  refine ⟨τ, hτ2, hτv, (Commute.refl s).mul_left ht's, hsτ, hτα, hτβ, hτγ, hFτ, h5, hG, hτP, ?_⟩
  rw [← hsupp, ← Set.ncard_coe_finset]
  congr 1
  ext δ
  simp only [Set.mem_ofPred_eq, Finset.mem_coe, Equiv.Perm.mem_support, hπ]

end Prop46CaseB

end Tau

end CFSG.Holt.H78
