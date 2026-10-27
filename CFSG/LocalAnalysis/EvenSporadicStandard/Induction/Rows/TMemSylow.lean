module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemBasic

public section

namespace CFSG.EvenSporadicStandard.Induction.TMem

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
open scoped Pointwise

variable {H : Type} [Group H] [Finite H]

theorem exists_fixed_involution {Y S : Subgroup H} (hS : IsPGroup 2 ↥S) (hYS : Y ≤ S)
    (hYne : Y ≠ ⊥) (hne : S ≠ Y) :
    ∃ s ∈ S, s ∉ Y ∧ ∃ w ∈ Y, orderOf w = 2 ∧ s * w = w * s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥S := hS.isNilpotent
  set Y' : Subgroup ↥S := Y.subgroupOf S with hY'
  have hlt : Y' < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hne ?_
    refine le_antisymm (fun x hx => ?_) hYS
    have : (⟨x, hx⟩ : ↥S) ∈ Y' := by rw [h]; exact mem_top _
    exact this
  have hlt2 : Y' < normalizer (Y' : Set ↥S) := Group.normalizerCondition_of_isNilpotent Y' hlt
  obtain ⟨s', hs'B, hs'Y⟩ := IsConcreteLE.exists_of_lt hlt2
  set B : Subgroup ↥S := normalizer (Y' : Set ↥S) with hB
  have hBp : IsPGroup 2 ↥B := hS.to_subgroup B
  have hBnil : Group.IsNilpotent ↥B := hBp.isNilpotent
  have hYb : (Y'.subgroupOf B).Normal := Subgroup.normal_in_normalizer
  have hYbne : Y'.subgroupOf B ≠ ⊥ := by
    intro h
    obtain ⟨y, hy, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hYne (eq_bot_iff.2 fun y hy => mem_bot.2 (hcon y hy))
    have hmemB : (⟨y, hYS hy⟩ : ↥S) ∈ B :=
      Subgroup.le_normalizer (show (⟨y, hYS hy⟩ : ↥S) ∈ Y' from hy)
    have h1 : (⟨⟨y, hYS hy⟩, hmemB⟩ : ↥B) ∈ Y'.subgroupOf B := hy
    rw [h, mem_bot] at h1
    exact hy1 (by simpa using congrArg (fun z : ↥B => ((z : ↥S) : H)) h1)
  have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hYbne
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hcen
  have hQp : IsPGroup 2 ↥(Y'.subgroupOf B ⊓ center ↥B) := hBp.to_subgroup _
  have h2a : 2 ∣ orderOf a := hQp.dvd_orderOf ha1
  set w₀ := a ^ (orderOf a / 2) with hw₀
  have hw₀2 : orderOf w₀ = 2 := orderOf_pow_orderOf_div (orderOf_pos a).ne' h2a
  have hw₀B : ((w₀ : ↥(Y'.subgroupOf B ⊓ center ↥B)) : ↥B) ∈ Y'.subgroupOf B ⊓ center ↥B :=
    w₀.2
  have hwY' : (((w₀ : ↥(Y'.subgroupOf B ⊓ center ↥B)) : ↥B) : ↥S) ∈ Y' := hw₀B.1
  have hwc := Subgroup.mem_center_iff.1 hw₀B.2
  refine ⟨(s' : H), s'.2, fun h => hs'Y h, ((((w₀ : ↥(Y'.subgroupOf B ⊓ center ↥B)) : ↥B) :
    ↥S) : H), hwY', ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw₀2]
  · have := hwc ⟨s', hs'B⟩
    exact congrArg (fun z : ↥B => ((z : ↥S) : H)) this

theorem eq_of_le_of_isPGroup {N L K : Subgroup H} (hLN : L ≤ N) (hodd : OddCN N L)
    (hC : ∀ w ∈ L, orderOf w = 2 → (∀ k ∈ K, k * w = w * k) →
      centralizer ({w} : Set H) ≤ normalizer (L : Set H))
    (hMK : ∀ b ∈ normalizer (L : Set H), (∀ k ∈ K, b * k = k * b) →
      b ∈ L ⊔ centralizer (L : Set H))
    {Y : Subgroup H} (hYne : Y ≠ ⊥) (hYL : Y ≤ L ⊓ centralizer (K : Set H))
    (hYmax : ∀ E : Subgroup H, E ≤ L ⊓ centralizer (K : Set H) → IsPGroup 2 ↥E → Y ≤ E →
      E = Y)
    {S : Subgroup H} (hS : IsPGroup 2 ↥S) (hSNK : S ≤ N ⊓ centralizer (K : Set H))
    (hYS : Y ≤ S) : S = Y := by
  by_contra hne
  obtain ⟨s, hsS, hsY, w, hwY, hw2, hsw⟩ := exists_fixed_involution hS hYS hYne hne
  have hwL : w ∈ L := (hYL hwY).1
  have hwK : ∀ k ∈ K, k * w = w * k := fun k hk => mem_centralizer_iff.1 (hYL hwY).2 k hk
  have hsC : s ∈ centralizer ({w} : Set H) := mem_centralizer_singleton_iff.2 hsw
  have hsM : s ∈ normalizer (L : Set H) := hC w hwL hw2 hwK hsC
  have hsN : s ∈ N := (hSNK hsS).1
  have hsK : ∀ k ∈ K, s * k = k * s := fun k hk =>
    (mem_centralizer_iff.1 (hSNK hsS).2 k hk).symm
  have hsLC : s ∈ L ⊔ centralizer (L : Set H) := hMK s hsM hsK
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf (p := 2)).1 hS ⟨s, hsS⟩
  rw [Subgroup.orderOf_mk] at hj
  have hsL : s ∈ L := two_mem_of_oddCN hLN hodd hsN hsLC hj
  have hsZ : zpowers s ≤ L ⊓ centralizer (K : Set H) := by
    rw [zpowers_le]
    exact ⟨hsL, mem_centralizer_iff.2 fun k hk => (hsK k hk).symm⟩
  have hE := sup_le hYL hsZ
  have hEp : IsPGroup 2 ↥(Y ⊔ zpowers s) := hS.to_le (sup_le hYS (zpowers_le.2 hsS))
  have := hYmax _ hE hEp le_sup_left
  exact hsY (this ▸ mem_sup_right (mem_zpowers s))

theorem mem_smul_sylow {G : Type*} [Group G] {p : ℕ} (P : Sylow p G) (g x : G)
    (hx : x ∈ (g • P : Sylow p G)) : ∃ y ∈ P, g * y * g⁻¹ = x := by
  have h : ((g • P : Sylow p G) : Subgroup G) = MulAut.conj g • (P : Subgroup G) :=
    Sylow.coe_subgroup_smul
  have hx' : x ∈ ((g • P : Sylow p G) : Subgroup G) := hx
  rw [h, Subgroup.mem_smul_pointwise_iff_exists] at hx'
  obtain ⟨y, hy, rfl⟩ := hx'
  exact ⟨y, hy, rfl⟩

theorem exists_sylow_Z {N L K : Subgroup H} (hLN : L ≤ N) (hodd : OddCN N L)
    (hC : ∀ w ∈ L, orderOf w = 2 → (∀ k ∈ K, k * w = w * k) →
      centralizer ({w} : Set H) ≤ normalizer (L : Set H))
    (hMK : ∀ b ∈ normalizer (L : Set H), (∀ k ∈ K, b * k = k * b) →
      b ∈ L ⊔ centralizer (L : Set H))
    {Y : Subgroup H} (hY2 : IsPGroup 2 ↥Y) (hYne : Y ≠ ⊥)
    (hYL : Y ≤ L ⊓ centralizer (K : Set H))
    (hYmax : ∀ E : Subgroup H, E ≤ L ⊓ centralizer (K : Set H) → IsPGroup 2 ↥E → Y ≤ E →
      E = Y) :
    ∃ P : Sylow 2 ↥(N ⊓ centralizer (K : Set H)),
      (P : Subgroup ↥(N ⊓ centralizer (K : Set H))).map
        (N ⊓ centralizer (K : Set H)).subtype = Y := by
  classical
  set Z : Subgroup H := N ⊓ centralizer (K : Set H) with hZ
  have hYZ : Y ≤ Z := fun y hy => ⟨hLN (hYL hy).1, (hYL hy).2⟩
  refine ⟨{ toSubgroup := Y.subgroupOf Z
            isPGroup' := hY2.of_equiv (Subgroup.subgroupOfEquivOfLe hYZ).symm
            is_maximal' := ?_ }, ?_⟩
  · intro Q hQ hPQ
    have hle : Y ≤ Q.map Z.subtype := by
      intro y hy
      exact ⟨⟨y, hYZ hy⟩, hPQ (show (⟨y, hYZ hy⟩ : ↥Z) ∈ Y.subgroupOf Z from hy), rfl⟩
    have hEq : Q.map Z.subtype = Y :=
      eq_of_le_of_isPGroup hLN hodd hC hMK hYne hYL hYmax (S := Q.map Z.subtype)
        (hQ.map Z.subtype) (fun x hx => by obtain ⟨z, -, rfl⟩ := hx; exact z.2) hle
    apply Subgroup.map_injective Z.subtype_injective
    rw [hEq, Subgroup.map_subgroupOf_eq_of_le hYZ]
  · exact Subgroup.map_subgroupOf_eq_of_le hYZ

theorem exists_conj_mem_of_involution {N L K : Subgroup H} (hLN : L ≤ N) (hodd : OddCN N L)
    (hC : ∀ w ∈ L, orderOf w = 2 → (∀ k ∈ K, k * w = w * k) →
      centralizer ({w} : Set H) ≤ normalizer (L : Set H))
    (hMK : ∀ b ∈ normalizer (L : Set H), (∀ k ∈ K, b * k = k * b) →
      b ∈ L ⊔ centralizer (L : Set H))
    {Y : Subgroup H} (hY2 : IsPGroup 2 ↥Y) (hYne : Y ≠ ⊥)
    (hYL : Y ≤ L ⊓ centralizer (K : Set H))
    (hYmax : ∀ E : Subgroup H, E ≤ L ⊓ centralizer (K : Set H) → IsPGroup 2 ↥E → Y ≤ E →
      E = Y)
    {t' : H} (ht'Z : t' ∈ N ⊓ centralizer (K : Set H)) (ht'2 : orderOf t' = 2) :
    ∃ c ∈ N ⊓ centralizer (K : Set H), c * t' * c⁻¹ ∈ Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z : Subgroup H := N ⊓ centralizer (K : Set H) with hZ
  obtain ⟨P, hP⟩ := exists_sylow_Z hLN hodd hC hMK hY2 hYne hYL hYmax
  let t'' : ↥Z := ⟨t', ht'Z⟩
  have ht''2 : orderOf t'' = 2 := by rw [Subgroup.orderOf_mk]; exact ht'2
  obtain ⟨Q', hQ'⟩ := (isPGroup_zpowers_two ht''2).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Z P Q'
  have ht''Q : t'' ∈ (g • P : Sylow 2 ↥Z) := by rw [hg]; exact hQ' (mem_zpowers t'')
  obtain ⟨y, hy, hgy⟩ := mem_smul_sylow P g t'' ht''Q
  refine ⟨((g⁻¹ : ↥Z) : H), (g⁻¹ : ↥Z).2, ?_⟩
  have h1 : y = g⁻¹ * t'' * g := by
    rw [← hgy]; group
  have h2 : (y : H) = ((g⁻¹ : ↥Z) : H) * t' * ((g⁻¹ : ↥Z) : H)⁻¹ := by
    have := congrArg (fun z : ↥Z => (z : H)) h1
    simpa [t''] using this
  rw [← h2, ← hP]
  exact ⟨y, hy, rfl⟩

theorem card_eq_pow_twoAdic {N L K : Subgroup H} (hLN : L ≤ N) (hodd : OddCN N L)
    (hC : ∀ w ∈ L, orderOf w = 2 → (∀ k ∈ K, k * w = w * k) →
      centralizer ({w} : Set H) ≤ normalizer (L : Set H))
    (hMK : ∀ b ∈ normalizer (L : Set H), (∀ k ∈ K, b * k = k * b) →
      b ∈ L ⊔ centralizer (L : Set H))
    {Y : Subgroup H} (hY2 : IsPGroup 2 ↥Y) (hYne : Y ≠ ⊥)
    (hYL : Y ≤ L ⊓ centralizer (K : Set H))
    (hYmax : ∀ E : Subgroup H, E ≤ L ⊓ centralizer (K : Set H) → IsPGroup 2 ↥E → Y ≤ E →
      E = Y) :
    Nat.card ↥Y = 2 ^ twoAdic (N ⊓ centralizer (K : Set H)) := by
  obtain ⟨P, hP⟩ := exists_sylow_Z hLN hodd hC hMK hY2 hYne hYL hYmax
  have h := P.card_eq_multiplicity
  rw [← hP, Subgroup.card_map_of_injective (N ⊓ centralizer (K : Set H)).subtype_injective]
  exact h

omit [Finite H] in
theorem centralizer_le_normalizer_of_conj {L : Subgroup H} {u w x : H} (hx : x ∈ L)
    (hw : x * u * x⁻¹ = w) (h38 : centralizer ({u} : Set H) ≤ normalizer (L : Set H)) :
    centralizer ({w} : Set H) ≤ normalizer (L : Set H) := by
  intro g hg
  have hgw : g * w = w * g := mem_centralizer_singleton_iff.1 hg
  have hconj : x⁻¹ * g * x ∈ centralizer ({u} : Set H) := by
    rw [mem_centralizer_singleton_iff]
    rw [← hw] at hgw
    calc x⁻¹ * g * x * u = x⁻¹ * (g * (x * u * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * u * x⁻¹) * g) * x := by rw [hgw]
      _ = u * (x⁻¹ * g * x) := by group
  have h1 := h38 hconj
  have hxN : x ∈ normalizer (L : Set H) := Subgroup.le_normalizer hx
  have : g = x * (x⁻¹ * g * x) * x⁻¹ := by group
  rw [this]
  exact (normalizer (L : Set H)).mul_mem ((normalizer (L : Set H)).mul_mem hxN h1)
    ((normalizer (L : Set H)).inv_mem hxN)

omit [Finite H] in
theorem exists_sylow_Y {L K : Subgroup H} {u : H} (hu2 : orderOf u = 2) (huL : u ∈ L)
    (hKu : ∀ k ∈ K, k * u = u * k) :
    ∃ Y : Subgroup H, IsPGroup 2 ↥Y ∧ Y ≠ ⊥ ∧ Y ≤ L ⊓ centralizer (K : Set H) ∧
      ∀ E : Subgroup H, E ≤ L ⊓ centralizer (K : Set H) → IsPGroup 2 ↥E → Y ≤ E → E = Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W : Subgroup H := L ⊓ centralizer (K : Set H) with hW
  have huW : u ∈ W := ⟨huL, mem_centralizer_iff.2 fun k hk => hKu k hk⟩
  let u' : ↥W := ⟨u, huW⟩
  have hu'2 : orderOf u' = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
  obtain ⟨Q, hQ⟩ := (isPGroup_zpowers_two hu'2).exists_le_sylow
  refine ⟨(Q : Subgroup ↥W).map W.subtype, Q.isPGroup'.map W.subtype, ?_, ?_, ?_⟩
  · intro h
    have hmem : u ∈ (Q : Subgroup ↥W).map W.subtype := ⟨u', hQ (mem_zpowers u'), rfl⟩
    rw [h, mem_bot] at hmem
    rw [hmem, orderOf_one] at hu2
    omega
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · intro E hE hEp hYE
    have hQE : (Q : Subgroup ↥W) ≤ E.subgroupOf W := by
      intro x hx
      exact hYE ⟨x, hx, rfl⟩
    have hEp' : IsPGroup 2 ↥(E.subgroupOf W) :=
      hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hE).symm
    have hEq : E.subgroupOf W = (Q : Subgroup ↥W) := Q.is_maximal' hEp' hQE
    rw [← Subgroup.map_subgroupOf_eq_of_le hE, hEq]

end CFSG.EvenSporadicStandard.Induction.TMem
