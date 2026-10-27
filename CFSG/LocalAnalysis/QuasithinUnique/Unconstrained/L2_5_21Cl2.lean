module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21C1
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21A2

public section

open scoped Pointwise

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Parity

variable {G : Type} [Group G] [Finite G]

theorem even_card_sq_eq_one {L : Subgroup G} (hL : Even (Nat.card L)) :
    Even (Nat.card {g : G // g ∈ L ∧ g * g = 1}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  have : Fintype L := Fintype.ofFinite L
  let f : Function.End L := fun x => x⁻¹
  have hf : f ^ (2 ^ 1) = 1 := by
    rw [pow_one, pow_two]
    refine funext fun x => ?_
    show (x⁻¹)⁻¹ = x
    simp
  have h1 := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) hf
  have h2 : Nat.card (Function.fixedPoints f) = Nat.card {g : G // g ∈ L ∧ g * g = 1} := by
    refine Nat.card_congr (Equiv.ofBijective (fun x : Function.fixedPoints f =>
      (⟨((x : L) : G), (x : L).2, ?_⟩ : {g : G // g ∈ L ∧ g * g = 1})) ⟨?_, ?_⟩)
    · have hx : f x = x := x.2
      have : ((x : L))⁻¹ = x := hx
      have h3 : (x : L) * (x : L) = 1 := by
        calc (x : L) * (x : L) = (x : L) * ((x : L))⁻¹ := by rw [this]
          _ = 1 := mul_inv_cancel _
      exact congrArg Subtype.val h3
    · intro x y hxy
      have h1 := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h1)
    · rintro ⟨g, hgL, hg⟩
      refine ⟨⟨⟨g, hgL⟩, ?_⟩, rfl⟩
      show ((⟨g, hgL⟩ : L))⁻¹ = ⟨g, hgL⟩
      apply Subtype.ext
      show g⁻¹ = g
      exact inv_eq_of_mul_eq_one_right hg
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h2] at h1
  rw [Nat.even_iff] at hL ⊢
  have h3 := h1
  unfold Nat.ModEq at h3
  omega

theorem exists_fixed_involution {L : Subgroup G} (hL : Even (Nat.card L)) {t : G}
    (htt : t * t = 1) (htL : t ∈ Subgroup.normalizer (L : Set G)) :
    ∃ v ∈ L, v ≠ 1 ∧ v * v = 1 ∧ t * v = v * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hJ : Even (Nat.card {g : G // g ∈ L ∧ g * g = 1}) := even_card_sq_eq_one hL
  have hmem : ∀ g : G, g ∈ L → t * g * t⁻¹ ∈ L := fun g hg =>
    (Subgroup.mem_normalizer_iff.mp htL g).mp hg
  have hconj : ∀ g : G, g ∈ L ∧ g * g = 1 → t * g * t⁻¹ ∈ L ∧ (t * g * t⁻¹) * (t * g * t⁻¹) = 1 := by
    rintro g ⟨hgL, hg⟩
    refine ⟨hmem g hgL, ?_⟩
    calc (t * g * t⁻¹) * (t * g * t⁻¹) = t * (g * g) * t⁻¹ := by group
      _ = 1 := by rw [hg]; group
  let σ : Equiv.Perm {g : G // g ∈ L ∧ g * g = 1} :=
    { toFun := fun g => ⟨t * g * t⁻¹, hconj g g.2⟩
      invFun := fun g => ⟨t * g * t⁻¹, hconj g g.2⟩
      left_inv := fun g => by
        apply Subtype.ext
        show t * (t * (g : G) * t⁻¹) * t⁻¹ = g
        calc t * (t * (g : G) * t⁻¹) * t⁻¹ = (t * t) * (g : G) * (t⁻¹ * t⁻¹) := by group
          _ = g := by rw [hti, htt]; group
      right_inv := fun g => by
        apply Subtype.ext
        show t * (t * (g : G) * t⁻¹) * t⁻¹ = g
        calc t * (t * (g : G) * t⁻¹) * t⁻¹ = (t * t) * (g : G) * (t⁻¹ * t⁻¹) := by group
          _ = g := by rw [hti, htt]; group }
  have hσ : σ ^ (2 ^ 1) = 1 := by
    rw [pow_one, pow_two]
    ext g
    show t * (t * (g : G) * t⁻¹) * t⁻¹ = g
    calc t * (t * (g : G) * t⁻¹) * t⁻¹ = (t * t) * (g : G) * (t⁻¹ * t⁻¹) := by group
      _ = g := by rw [hti, htt]; group
  have hfix1 : σ ⟨1, L.one_mem, mul_one 1⟩ = ⟨1, L.one_mem, mul_one 1⟩ := by
    apply Subtype.ext
    show t * 1 * t⁻¹ = 1
    group
  have : Fintype {g : G // g ∈ L ∧ g * g = 1} := Fintype.ofFinite _
  have hdvd : 2 ∣ Fintype.card {g : G // g ∈ L ∧ g * g = 1} := by
    rw [← Nat.card_eq_fintype_card]
    exact even_iff_two_dvd.mp hJ
  obtain ⟨b, hb, hb1⟩ := Equiv.Perm.exists_fixed_point_of_prime' (p := 2) (n := 1) hdvd hσ hfix1
  refine ⟨(b : G), b.2.1, fun h => hb1 (Subtype.ext h), b.2.2, ?_⟩
  have hb' : t * (b : G) * t⁻¹ = b := congrArg Subtype.val hb
  calc t * (b : G) = t * (b : G) * t⁻¹ * t := by group
    _ = (b : G) * t := by rw [hb']

end Parity

section Rank3

variable {G : Type} [Group G] [Finite G]

theorem elemAbelian_sup_three {p : ℕ} (hp : p.Prime) {x₁ a b : G}
    (hox : orderOf x₁ = p) (hoa : orderOf a = p) (hob : orderOf b = p)
    (hxa : x₁ * a = a * x₁) (hxb : x₁ * b = b * x₁) (hab : a * b = b * a)
    (hxindep : Subgroup.zpowers x₁ ⊓ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) = ⊥)
    (hba : b ∉ Subgroup.zpowers a) :
    (∀ u ∈ Subgroup.zpowers x₁ ⊔ (Subgroup.zpowers a ⊔ Subgroup.zpowers b),
      ∀ v ∈ Subgroup.zpowers x₁ ⊔ (Subgroup.zpowers a ⊔ Subgroup.zpowers b), u * v = v * u) ∧
    (∀ w ∈ Subgroup.zpowers x₁ ⊔ (Subgroup.zpowers a ⊔ Subgroup.zpowers b), w ^ p = 1) ∧
    Nat.card ↥(Subgroup.zpowers x₁ ⊔ (Subgroup.zpowers a ⊔ Subgroup.zpowers b)) = p ^ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have hcardx : Nat.card (Subgroup.zpowers x₁) = p := by rw [Nat.card_zpowers, hox]
  have hcarda : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, hoa]
  have hcardb : Nat.card (Subgroup.zpowers b) = p := by rw [Nat.card_zpowers, hob]
  have hcab : ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ Subgroup.zpowers b, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((Commute.zpow_zpow (show Commute a b from hab) i j).eq)
  have hAB : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    by_contra hne
    have hdvd : Nat.card ↥(Subgroup.zpowers a ⊓ Subgroup.zpowers b) ∣ p := by
      rw [← hcardb]; exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact hne (Subgroup.card_eq_one.mp h1)
    · have heq : Subgroup.zpowers a ⊓ Subgroup.zpowers b = Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, hcardb])
      apply hba
      have : Subgroup.zpowers b ≤ Subgroup.zpowers a := by
        rw [← heq]; exact inf_le_left
      exact this (Subgroup.mem_zpowers b)
  obtain ⟨hY₀card, hY₀set⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (Subgroup.zpowers a) (Subgroup.zpowers b) hcab
  rw [hAB, Subgroup.card_bot, mul_one, hcarda, hcardb] at hY₀card
  have hcx : ∀ u ∈ Subgroup.zpowers x₁, ∀ v ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b,
      u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hv' : v ∈ ((Subgroup.zpowers a : Set G) * (Subgroup.zpowers b : Set G)) := by
      rw [← hY₀set]; exact hv
    obtain ⟨u', hu', v', hv', rfl⟩ := hv'
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv'
    have h1 : Commute (x₁ ^ i) (a ^ j) := Commute.zpow_zpow (show Commute x₁ a from hxa) i j
    have h2 : Commute (x₁ ^ i) (b ^ k) := Commute.zpow_zpow (show Commute x₁ b from hxb) i k
    exact (h1.mul_right h2).eq
  obtain ⟨hEcard, hEset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (Subgroup.zpowers x₁) (Subgroup.zpowers a ⊔ Subgroup.zpowers b) hcx
  rw [hxindep, Subgroup.card_bot, mul_one, hcardx, hY₀card] at hEcard
  have hmemE : ∀ w ∈ Subgroup.zpowers x₁ ⊔ (Subgroup.zpowers a ⊔ Subgroup.zpowers b),
      ∃ i j k : ℤ, w = x₁ ^ i * (a ^ j * b ^ k) := by
    intro w hw
    have hw' : w ∈ ((Subgroup.zpowers x₁ : Set G) *
        ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G)) := by
      rw [← hEset]; exact hw
    obtain ⟨u, hu, v, hv, rfl⟩ := hw'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hv' : v ∈ ((Subgroup.zpowers a : Set G) * (Subgroup.zpowers b : Set G)) := by
      rw [← hY₀set]; exact hv
    obtain ⟨u', hu', v', hv', rfl⟩ := hv'
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv'
    exact ⟨i, j, k, rfl⟩
  have hxa' : ∀ n m : ℤ, x₁ ^ n * a ^ m = a ^ m * x₁ ^ n := fun n m =>
    (Commute.zpow_zpow (show Commute x₁ a from hxa) n m).eq
  have hxb' : ∀ n m : ℤ, x₁ ^ n * b ^ m = b ^ m * x₁ ^ n := fun n m =>
    (Commute.zpow_zpow (show Commute x₁ b from hxb) n m).eq
  have hab' : ∀ n m : ℤ, a ^ n * b ^ m = b ^ m * a ^ n := fun n m =>
    (Commute.zpow_zpow (show Commute a b from hab) n m).eq
  have hxx : ∀ n m : ℤ, x₁ ^ n * x₁ ^ m = x₁ ^ m * x₁ ^ n := fun n m =>
    (Commute.zpow_zpow (Commute.refl x₁) n m).eq
  have haa : ∀ n m : ℤ, a ^ n * a ^ m = a ^ m * a ^ n := fun n m =>
    (Commute.zpow_zpow (Commute.refl a) n m).eq
  have hbb : ∀ n m : ℤ, b ^ n * b ^ m = b ^ m * b ^ n := fun n m =>
    (Commute.zpow_zpow (Commute.refl b) n m).eq
  have hcomm3 : ∀ i j k : ℤ, ∀ i' j' k' : ℤ,
      (x₁ ^ i * (a ^ j * b ^ k)) * (x₁ ^ i' * (a ^ j' * b ^ k')) =
        (x₁ ^ i' * (a ^ j' * b ^ k')) * (x₁ ^ i * (a ^ j * b ^ k)) := by
    intro i j k i' j' k'
    have e1 : (x₁ ^ i * (a ^ j * b ^ k)) * (x₁ ^ i' * (a ^ j' * b ^ k')) =
        (x₁ ^ i * x₁ ^ i') * ((a ^ j * a ^ j') * (b ^ k * b ^ k')) := by
      calc (x₁ ^ i * (a ^ j * b ^ k)) * (x₁ ^ i' * (a ^ j' * b ^ k'))
          = x₁ ^ i * (a ^ j * (b ^ k * x₁ ^ i')) * (a ^ j' * b ^ k') := by group
        _ = x₁ ^ i * (a ^ j * (x₁ ^ i' * b ^ k)) * (a ^ j' * b ^ k') := by rw [← hxb']
        _ = x₁ ^ i * ((a ^ j * x₁ ^ i') * b ^ k) * (a ^ j' * b ^ k') := by group
        _ = x₁ ^ i * ((x₁ ^ i' * a ^ j) * b ^ k) * (a ^ j' * b ^ k') := by rw [← hxa']
        _ = (x₁ ^ i * x₁ ^ i') * (a ^ j * (b ^ k * (a ^ j' * b ^ k'))) := by group
        _ = (x₁ ^ i * x₁ ^ i') * (a ^ j * ((b ^ k * a ^ j') * b ^ k')) := by group
        _ = (x₁ ^ i * x₁ ^ i') * (a ^ j * ((a ^ j' * b ^ k) * b ^ k')) := by rw [← hab']
        _ = (x₁ ^ i * x₁ ^ i') * ((a ^ j * a ^ j') * (b ^ k * b ^ k')) := by group
    have e2 : (x₁ ^ i' * (a ^ j' * b ^ k')) * (x₁ ^ i * (a ^ j * b ^ k)) =
        (x₁ ^ i' * x₁ ^ i) * ((a ^ j' * a ^ j) * (b ^ k' * b ^ k)) := by
      calc (x₁ ^ i' * (a ^ j' * b ^ k')) * (x₁ ^ i * (a ^ j * b ^ k))
          = x₁ ^ i' * (a ^ j' * (b ^ k' * x₁ ^ i)) * (a ^ j * b ^ k) := by group
        _ = x₁ ^ i' * (a ^ j' * (x₁ ^ i * b ^ k')) * (a ^ j * b ^ k) := by rw [← hxb']
        _ = x₁ ^ i' * ((a ^ j' * x₁ ^ i) * b ^ k') * (a ^ j * b ^ k) := by group
        _ = x₁ ^ i' * ((x₁ ^ i * a ^ j') * b ^ k') * (a ^ j * b ^ k) := by rw [← hxa']
        _ = (x₁ ^ i' * x₁ ^ i) * (a ^ j' * (b ^ k' * (a ^ j * b ^ k))) := by group
        _ = (x₁ ^ i' * x₁ ^ i) * (a ^ j' * ((b ^ k' * a ^ j) * b ^ k)) := by group
        _ = (x₁ ^ i' * x₁ ^ i) * (a ^ j' * ((a ^ j * b ^ k') * b ^ k)) := by rw [← hab']
        _ = (x₁ ^ i' * x₁ ^ i) * ((a ^ j' * a ^ j) * (b ^ k' * b ^ k)) := by group
    rw [e1, e2, hxx i i', haa j j', hbb k k']
  have hcommE : ∀ u ∈ Subgroup.zpowers x₁ ⊔ (Subgroup.zpowers a ⊔ Subgroup.zpowers b),
      ∀ v ∈ Subgroup.zpowers x₁ ⊔ (Subgroup.zpowers a ⊔ Subgroup.zpowers b), u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, j, k, rfl⟩ := hmemE u hu
    obtain ⟨i', j', k', rfl⟩ := hmemE v hv
    exact hcomm3 i j k i' j' k'
  have hpow : ∀ (g : G) (n : ℤ), g ^ p = 1 → (g ^ n) ^ p = 1 := by
    intro g n hg
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]
  have hxp : x₁ ^ p = 1 := by rw [← hox]; exact pow_orderOf_eq_one x₁
  have hap : a ^ p = 1 := by rw [← hoa]; exact pow_orderOf_eq_one a
  have hbp : b ^ p = 1 := by rw [← hob]; exact pow_orderOf_eq_one b
  refine ⟨hcommE, ?_, by rw [hEcard]; ring⟩
  intro w hw
  obtain ⟨i, j, k, rfl⟩ := hmemE w hw
  have hc : Commute (x₁ ^ i) (a ^ j * b ^ k) := by
    have h1 : Commute (x₁ ^ i) (a ^ j) := Commute.zpow_zpow (show Commute x₁ a from hxa) i j
    have h2 : Commute (x₁ ^ i) (b ^ k) := Commute.zpow_zpow (show Commute x₁ b from hxb) i k
    exact h1.mul_right h2
  have hc2 : Commute (a ^ j) (b ^ k) := Commute.zpow_zpow (show Commute a b from hab) j k
  rw [hc.mul_pow, hc2.mul_pow, hpow x₁ i hxp, hpow a j hap, hpow b k hbp]
  simp

end Rank3


section Claim2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK : G} {R : Subgroup ↥(autOn N.S N.K)}

omit [Finite G] in
theorem centerless_conjugate {K : Subgroup G}
    (hZ : ∀ x ∈ K, (∀ y ∈ K, x * y = y * x) → x = 1) (g : G) :
    ∀ x ∈ CFSG.conjugate K g, (∀ y ∈ CFSG.conjugate K g, x * y = y * x) → x = 1 := by
  intro x hx hc
  have hk : g * x * g⁻¹ ∈ K := BenderBranch.mem_conjugate_iff.mp hx
  have h1 : g * x * g⁻¹ = 1 := by
    refine hZ _ hk (fun y hy => ?_)
    have hy' : g⁻¹ * y * g ∈ CFSG.conjugate K g := by
      rw [BenderBranch.mem_conjugate_iff]
      have : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rw [this]; exact hy
    have h2 := hc _ hy'
    calc g * x * g⁻¹ * y = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by rw [h2]
      _ = y * (g * x * g⁻¹) := by group
  calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
    _ = 1 := by rw [h1]; group

theorem Lv2520.centerless_K (h : Lv2520 N t zK) :
    ∀ x ∈ N.K, (∀ y ∈ N.K, x * y = y * x) → x = 1 := fun _ hx hc =>
  N.center_K_trivial h.facts258.simple hx hc

theorem Lv2520.even_card_K (h : Lv2520 N t zK) : Even (Nat.card ↥N.K) := by
  obtain ⟨E, hESK, hE4⟩ := h.exists_four_SK
  have hdvd : Nat.card ↥E ∣ Nat.card ↥N.K :=
    Subgroup.card_dvd_of_le (hESK.trans N.SK_le_K)
  rw [hE4.2] at hdvd
  exact (even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 4).trans hdvd))

theorem Lv2520.exists_involution_conjugate (h : Lv2520 N t zK) (g : G) :
    ∃ e ∈ CFSG.conjugate N.K g, e ≠ 1 ∧ e * e = 1 := by
  obtain ⟨E, hESK, hE4⟩ := h.exists_four_SK
  obtain ⟨e₀, he₀E, he₀1, -⟩ := exists_ne_of_card_four hE4.2 (1 : G)
  refine ⟨g⁻¹ * e₀ * g, ?_, ?_, ?_⟩
  · rw [BenderBranch.mem_conjugate_iff]
    have : g * (g⁻¹ * e₀ * g) * g⁻¹ = e₀ := by group
    rw [this]
    exact N.SK_le_K (hESK he₀E)
  · intro h1
    apply he₀1
    calc e₀ = g * (g⁻¹ * e₀ * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · calc g⁻¹ * e₀ * g * (g⁻¹ * e₀ * g) = g⁻¹ * (e₀ * e₀) * g := by group
      _ = 1 := by rw [hE4.sq he₀E]; group

theorem Lv2520.exists_comm_involution_conjugate
    (h : Lv2520 N t zK) (hR : DS.DSData R)
    (hfam : OutFamily N.K N.H) (g : G) {s : G} (hs : s ∈ CFSG.conjugate N.K g) (hs1 : s ≠ 1)
    (hs2 : s * s = 1) :
    ∃ v ∈ CFSG.conjugate N.K g, v ≠ 1 ∧ v ≠ s ∧ v * v = 1 ∧ v * s = s * v := by
  obtain ⟨E, hESK, hE4⟩ := h.exists_four_SK
  have hzKE : zK ∈ E := h.zK_mem_four hR hESK hE4
  have hzKK : zK ∈ N.K := h.hK0 ▸ h.facts2511.zK_mem
  obtain ⟨v₀, hv₀E, hv₀1, hv₀z⟩ := exists_ne_of_card_four hE4.2 zK
  have hs' : g * s * g⁻¹ ∈ N.K := BenderBranch.mem_conjugate_iff.mp hs
  have hs'1 : g * s * g⁻¹ ≠ 1 := by
    intro h1
    apply hs1
    calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  have hs'2 : (g * s * g⁻¹) * (g * s * g⁻¹) = 1 := by
    calc (g * s * g⁻¹) * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
      _ = 1 := by rw [hs2]; group
  obtain ⟨k, hkK, hk⟩ := outOneClass G N.K N.H N.S (h.outSetting hfam) zK (g * s * g⁻¹) hzKK hs'
    h.facts2511.zK_sq hs'2 h.zK_ne_one hs'1
  have hv₀K : v₀ ∈ N.K := N.SK_le_K (hESK hv₀E)
  refine ⟨g⁻¹ * (k * v₀ * k⁻¹) * g, ?_, ?_, ?_, ?_, ?_⟩
  · rw [BenderBranch.mem_conjugate_iff]
    have : g * (g⁻¹ * (k * v₀ * k⁻¹) * g) * g⁻¹ = k * v₀ * k⁻¹ := by group
    rw [this]
    exact N.K.mul_mem (N.K.mul_mem hkK hv₀K) (N.K.inv_mem hkK)
  · intro h1
    apply hv₀1
    calc v₀ = k⁻¹ * (g * (g⁻¹ * (k * v₀ * k⁻¹) * g) * g⁻¹) * k := by group
      _ = 1 := by rw [h1]; group
  · intro h1
    apply hv₀z
    have h2 : k * v₀ * k⁻¹ = g * s * g⁻¹ := by
      calc k * v₀ * k⁻¹ = g * (g⁻¹ * (k * v₀ * k⁻¹) * g) * g⁻¹ := by group
        _ = g * s * g⁻¹ := by rw [h1]
    rw [← hk] at h2
    calc v₀ = k⁻¹ * (k * v₀ * k⁻¹) * k := by group
      _ = k⁻¹ * (k * zK * k⁻¹) * k := by rw [h2]
      _ = zK := by group
  · calc g⁻¹ * (k * v₀ * k⁻¹) * g * (g⁻¹ * (k * v₀ * k⁻¹) * g)
        = g⁻¹ * (k * (v₀ * v₀) * k⁻¹) * g := by group
      _ = 1 := by rw [hE4.sq hv₀E]; group
  · have hcomm : v₀ * zK = zK * v₀ := hE4.comm hv₀E hzKE
    have hs'' : s = g⁻¹ * (k * zK * k⁻¹) * g := by
      rw [hk]; group
    rw [hs'']
    calc g⁻¹ * (k * v₀ * k⁻¹) * g * (g⁻¹ * (k * zK * k⁻¹) * g)
        = g⁻¹ * (k * (v₀ * zK) * k⁻¹) * g := by group
      _ = g⁻¹ * (k * (zK * v₀) * k⁻¹) * g := by rw [hcomm]
      _ = g⁻¹ * (k * zK * k⁻¹) * g * (g⁻¹ * (k * v₀ * k⁻¹) * g) := by group

theorem Lv2520.claim2_exists_third
    (h : Lv2520 N t zK) (hR : DS.DSData R)
    (hfam : OutFamily N.K N.H) {i u : G} (hi : i ∈ N.SC) (hi1 : i ≠ 1) (hi2 : i * i = 1)
    (hit : i ≠ t) (hcomp : IsComponentIn N.K (Subgroup.centralizer ({i} : Set G)))
    (hu : u ∈ Subgroup.centralizer ({i} : Set G))
    (hnorm : u ∉ Subgroup.normalizer (N.K : Set G)) :
    ∃ v : G, v * v = 1 ∧ v ≠ 1 ∧ v ≠ i ∧ v ≠ t ∧ v ≠ i * t ∧ i * v = v * i ∧ t * v = v * t ∧
      ∀ k ∈ N.K, k * v = v * k := by
  have hf := h.facts2511
  have ht2 : t * t = 1 := hf.t_mul_t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hiS : i ∈ N.S := N.SC_le_S hi
  have hit' : i * t = t * i := Subgroup.mem_centralizer_iff.mp hf.t_mem_center.2 i hiS
  have htC : t ∈ Subgroup.centralizer ({i} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hit'.symm
  have hitt : i * t ≠ 1 := by
    intro h1
    apply hit
    calc i = i * t * t⁻¹ := by group
      _ = t⁻¹ := by rw [h1, one_mul]
      _ = t := hti
  have hitit : (i * t) * (i * t) = 1 := by
    calc (i * t) * (i * t) = (i * i) * (t * t) := by
          calc (i * t) * (i * t) = i * (t * i) * t := by group
            _ = i * (i * t) * t := by rw [← hit']
            _ = (i * i) * (t * t) := by group
      _ = 1 := by rw [hi2, ht2]; group
  obtain ⟨L, hLdef⟩ : ∃ L : Subgroup G, L = CFSG.conjugate N.K u := ⟨_, rfl⟩
  have hLK : L ≠ N.K := by
    intro heq
    apply hnorm
    rw [← BenderBranch.conjugate_eq_iff_mem_normalizer, ← hLdef]
    exact heq
  have hL : IsComponentIn L (Subgroup.centralizer ({i} : Set G)) := by
    rw [hLdef]
    exact Unc25G2.isComponentIn_conjugate hcomp hu
  have hKL : ⁅N.K, L⁆ = ⊥ :=
    (BenderBranch.eq_or_commute_of_isComponentIn hcomp hL).resolve_left (fun h' => hLK h'.symm)
  have hcommKL : ∀ k ∈ N.K, ∀ l ∈ L, k * l = l * k := fun k hk l hl =>
    BenderBranch.commute_of_commutator_eq_bot hKL hk hl
  have hZL : ∀ x ∈ L, (∀ y ∈ L, x * y = y * x) → x = 1 := by
    rw [hLdef]
    exact centerless_conjugate h.centerless_K u
  have hLC : ∀ y ∈ L, y * i = i * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (hL.1 hy)
  have hiL : i ∉ L := fun hiL => hi1 (hZL i hiL (fun y hy => (hLC y hy).symm))
  have hLeven : Even (Nat.card ↥L) := by
    rw [hLdef, BenderBranch.card_conjugate]
    exact h.even_card_K
  have hLconj : ∀ s ∈ L, s ≠ 1 → s * s = 1 →
      ∃ v ∈ L, v ≠ 1 ∧ v ≠ s ∧ v * v = 1 ∧ v * s = s * v := by
    intro s hs hs1 hs2
    rw [hLdef] at hs ⊢
    exact h.exists_comm_involution_conjugate hR hfam u hs hs1 hs2
  by_cases htn : t ∈ Subgroup.normalizer (L : Set G)
  · by_cases hs : t ∈ L ∨ i * t ∈ L
    · rcases hs with hs | hs
      ·
        obtain ⟨v, hvL, hv1, hvs, hv2, hvc⟩ := hLconj t hs hf.t_ne_one ht2
        refine ⟨v, hv2, hv1, fun hvi => hiL (hvi ▸ hvL), hvs, fun hv => hiL ?_,
          (hLC v hvL).symm, hvc.symm, fun k hk => hcommKL k hk v hvL⟩
        have : i = v * t⁻¹ := by rw [hv]; group
        rw [this]
        exact L.mul_mem hvL (L.inv_mem hs)
      ·
        obtain ⟨v, hvL, hv1, hvs, hv2, hvc⟩ := hLconj (i * t) hs hitt hitit
        have htL : t ∉ L := by
          intro htL
          apply hiL
          have : i = (i * t) * t⁻¹ := by group
          rw [this]
          exact L.mul_mem hs (L.inv_mem htL)
        refine ⟨v, hv2, hv1, fun hvi => hiL (hvi ▸ hvL), fun hvt => htL (hvt ▸ hvL), hvs,
          (hLC v hvL).symm, ?_, fun k hk => hcommKL k hk v hvL⟩
        have hvi' : v * i = i * v := hLC v hvL
        calc t * v = i * ((i * t) * v) := by
              calc t * v = (i * i) * t * v := by rw [hi2, one_mul]
                _ = i * ((i * t) * v) := by group
          _ = i * (v * (i * t)) := by rw [← hvc]
          _ = (i * v) * (i * t) := by group
          _ = (v * i) * (i * t) := by rw [hvi']
          _ = v * ((i * i) * t) := by group
          _ = v * t := by rw [hi2, one_mul]
    · push Not at hs
      obtain ⟨hnt, hnit⟩ := hs
      obtain ⟨v, hvL, hv1, hv2, hvt⟩ := exists_fixed_involution hLeven ht2 htn
      exact ⟨v, hv2, hv1, fun hvi => hiL (hvi ▸ hvL), fun hv => hnt (hv ▸ hvL),
        fun hv => hnit (hv ▸ hvL), (hLC v hvL).symm, hvt, fun k hk => hcommKL k hk v hvL⟩
  ·
    obtain ⟨L', hL'def⟩ : ∃ L' : Subgroup G, L' = CFSG.conjugate L t := ⟨_, rfl⟩
    have hL' : IsComponentIn L' (Subgroup.centralizer ({i} : Set G)) := by
      rw [hL'def]
      exact Unc25G2.isComponentIn_conjugate hL htC
    have hL'L : L' ≠ L := by
      intro heq
      apply htn
      rw [← BenderBranch.conjugate_eq_iff_mem_normalizer, ← hL'def]
      exact heq
    have htK : t ∈ Subgroup.normalizer (N.K : Set G) :=
      h.centralizer_t_le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
    have hL'K : L' ≠ N.K := by
      intro heq
      apply hLK
      have h1 : CFSG.conjugate L' t⁻¹ = L := by
        rw [hL'def, BenderBranch.conjugate_conjugate, mul_inv_cancel, BenderBranch.conjugate_one]
      rw [← h1, heq]
      exact BenderBranch.conjugate_eq_iff_mem_normalizer.mpr ((Subgroup.normalizer _).inv_mem htK)
    have hKL' : ⁅N.K, L'⁆ = ⊥ :=
      (BenderBranch.eq_or_commute_of_isComponentIn hcomp hL').resolve_left
        (fun h' => hL'K h'.symm)
    have hLL' : ⁅L, L'⁆ = ⊥ :=
      (BenderBranch.eq_or_commute_of_isComponentIn hL hL').resolve_left
        (fun h' => hL'L h'.symm)
    have hcommLL' : ∀ l ∈ L, ∀ l' ∈ L', l * l' = l' * l := fun l hl l' hl' =>
      BenderBranch.commute_of_commutator_eq_bot hLL' hl hl'
    have hcommKL' : ∀ k ∈ N.K, ∀ l' ∈ L', k * l' = l' * k := fun k hk l' hl' =>
      BenderBranch.commute_of_commutator_eq_bot hKL' hk hl'
    have hL'C : ∀ y ∈ L', y * i = i * y := fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hL'.1 hy)
    obtain ⟨e, heL, he1, he2⟩ : ∃ e ∈ L, e ≠ 1 ∧ e * e = 1 := by
      rw [hLdef]
      exact h.exists_involution_conjugate u
    have he'L' : t * e * t⁻¹ ∈ L' := by
      rw [hL'def, BenderBranch.mem_conjugate_iff]
      have : t * (t * e * t⁻¹) * t⁻¹ = e := by
        calc t * (t * e * t⁻¹) * t⁻¹ = (t * t) * e * (t⁻¹ * t⁻¹) := by group
          _ = e := by rw [hti, ht2]; group
      rw [this]; exact heL
    obtain ⟨e', he'⟩ : ∃ e' : G, e' = t * e * t⁻¹ := ⟨_, rfl⟩
    rw [← he'] at he'L'
    have he'2 : e' * e' = 1 := by
      rw [he']
      calc t * e * t⁻¹ * (t * e * t⁻¹) = t * (e * e) * t⁻¹ := by group
        _ = 1 := by rw [he2]; group
    have hte' : t * e' * t⁻¹ = e := by
      rw [he']
      calc t * (t * e * t⁻¹) * t⁻¹ = (t * t) * e * (t⁻¹ * t⁻¹) := by group
        _ = e := by rw [hti, ht2]; group
    have hee' : e * e' = e' * e := hcommLL' e heL e' he'L'
    have he'l : ∀ l ∈ L, e' * l = l * e' := fun l hl => (hcommLL' l hl e' he'L').symm
    have hconjL : ∀ l ∈ L, (e * e') * l * (e * e')⁻¹ ∈ L := by
      intro l hl
      have : (e * e') * l * (e * e')⁻¹ = e * l * e⁻¹ := by
        calc (e * e') * l * (e * e')⁻¹ = e * (e' * l * e'⁻¹) * e⁻¹ := by group
          _ = e * (l * e' * e'⁻¹) * e⁻¹ := by rw [he'l l hl]
          _ = e * l * e⁻¹ := by group
      rw [this]
      exact L.mul_mem (L.mul_mem heL hl) (L.inv_mem heL)
    refine ⟨e * e', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc e * e' * (e * e') = e * (e' * e) * e' := by group
        _ = e * (e * e') * e' := by rw [← hee']
        _ = (e * e) * (e' * e') := by group
        _ = 1 := by rw [he2, he'2]; group
    · intro h1
      apply he1
      have h2 : e' = e⁻¹ := by
        calc e' = e⁻¹ * (e * e') := by group
          _ = e⁻¹ := by rw [h1, mul_one]
      have h3 : e = e' := by
        calc e = e⁻¹ := inv_eq_of_mul_eq_one_right he2 |>.symm
          _ = e' := h2.symm
      have heL' : e ∈ L' := h3 ▸ he'L'
      exact hZL e heL (fun l hl => (hcommLL' l hl e heL').symm)
    · intro hvi
      apply he1
      refine hZL e heL (fun l hl => ?_)
      have h1 : l * (e * e') = (e * e') * l := by rw [hvi]; exact hLC l hl
      have h2 : l * e = e * l := by
        have h3 : l * e * e' = e * l * e' := by
          calc l * e * e' = l * (e * e') := by group
            _ = (e * e') * l := h1
            _ = e * (e' * l) := by group
            _ = e * (l * e') := by rw [he'l l hl]
            _ = e * l * e' := by group
        exact mul_right_cancel h3
      exact h2.symm
    · intro hvt
      apply htn
      refine mem_normalizer_of_forall_mem (fun l hl => ?_)
      have := hconjL l hl
      rwa [hvt] at this
    · intro hvit
      apply htn
      refine mem_normalizer_of_forall_mem (fun l hl => ?_)
      have h1 := hconjL l hl
      rw [hvit] at h1
      have hmem : t * l * t⁻¹ ∈ L' := by
        rw [hL'def, BenderBranch.mem_conjugate_iff]
        have : t * (t * l * t⁻¹) * t⁻¹ = l := by
          calc t * (t * l * t⁻¹) * t⁻¹ = (t * t) * l * (t⁻¹ * t⁻¹) := by group
            _ = l := by rw [hti, ht2]; group
        rw [this]; exact hl
      have hci : (t * l * t⁻¹) * i = i * (t * l * t⁻¹) := hL'C _ hmem
      have : t * l * t⁻¹ = (i * t) * l * (i * t)⁻¹ := by
        calc t * l * t⁻¹ = i * (i * (t * l * t⁻¹)) := by rw [← mul_assoc, hi2, one_mul]
          _ = i * ((t * l * t⁻¹) * i) := by rw [hci]
          _ = (i * t) * l * (i * t)⁻¹ := by
              calc i * ((t * l * t⁻¹) * i) = i * (t * l * t⁻¹) * i := by group
                _ = i * (t * l * t⁻¹) * i⁻¹ := by
                    rw [inv_eq_of_mul_eq_one_right hi2]
                _ = (i * t) * l * (i * t)⁻¹ := by group
      rw [this]
      exact h1
    · have h1 := hL'C e' he'L'
      have h2 := hLC e heL
      calc i * (e * e') = (i * e) * e' := by group
        _ = (e * i) * e' := by rw [← h2]
        _ = e * (i * e') := by group
        _ = e * (e' * i) := by rw [← h1]
        _ = (e * e') * i := by group
    · calc t * (e * e') = (t * e * t⁻¹) * (t * e' * t⁻¹) * t := by group
        _ = e' * e * t := by rw [← he', hte']
        _ = (e * e') * t := by rw [hee']
    · intro k hk
      calc k * (e * e') = (k * e) * e' := by group
        _ = (e * k) * e' := by rw [hcommKL k hk e heL]
        _ = e * (k * e') := by group
        _ = e * (e' * k) := by rw [hcommKL' k hk e' he'L']
        _ = (e * e') * k := by group

theorem Lv2520.claim2_false (h : Lv2520 N t zK) (hR : DS.DSData R) {i v : G} (hi : i ∈ N.SC)
    (hi1 : i ≠ 1) (hi2 : i * i = 1) (hit : i ≠ t) (hv2 : v * v = 1) (hv1 : v ≠ 1) (hvi : v ≠ i)
    (hvt : v ≠ t) (hvit : v ≠ i * t) (hiv : i * v = v * i) (htv : t * v = v * t)
    (hvK : ∀ k ∈ N.K, k * v = v * k) : False := by
  have hf := h.facts2511
  have hSB := h.sBar hR
  have ht2 : t * t = 1 := hf.t_mul_t
  have hiS : i ∈ N.S := N.SC_le_S hi
  have hit' : i * t = t * i := Subgroup.mem_centralizer_iff.mp hf.t_mem_center.2 i hiS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hoi : orderOf i = 2 := orderOf_eq_prime (by rw [pow_two]; exact hi2) hi1
  have hot : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) hf.t_ne_one
  have hov : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hv2) hv1
  have hvt_zp : v ∉ Subgroup.zpowers t := fun hmem =>
    (mem_zpowers_involution ht2 hmem).elim hv1 hvt
  have hcomm_tv : ∀ a ∈ Subgroup.zpowers t, ∀ b ∈ Subgroup.zpowers v, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow (show Commute t v from htv) m n).eq
  have hindep : Subgroup.zpowers i ⊓ (Subgroup.zpowers t ⊔ Subgroup.zpowers v) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rcases mem_zpowers_involution hi2 hx.1 with hx1 | hxi
    · exact hx1
    · exfalso
      rw [hxi] at hx
      have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm_tv).2
      have hi' : i ∈ ((Subgroup.zpowers t : Set G) * (Subgroup.zpowers v : Set G)) := by
        rw [← hset]; exact hx.2
      obtain ⟨a, ha, b, hb, hab⟩ := hi'
      rcases mem_zpowers_involution ht2 ha with ha1 | ha1 <;>
        rcases mem_zpowers_involution hv2 hb with hb1 | hb1 <;> rw [ha1, hb1] at hab
      · exact hi1 (by simpa using hab.symm)
      · exact hvi (by simpa using hab)
      · exact hit (by simpa using hab.symm)
      · apply hvit
        have hab' : t * v = i := hab
        calc v = t * (t * v) := by rw [← mul_assoc, ht2, one_mul]
          _ = t * i := by rw [hab']
          _ = i * t := hit'.symm
  obtain ⟨hEcomm, hEexp, hEcard⟩ := elemAbelian_sup_three Nat.prime_two hoi hot hov hit' hiv htv
    hindep hvt_zp
  obtain ⟨E, hEdef⟩ : ∃ E : Subgroup G,
      E = Subgroup.zpowers i ⊔ (Subgroup.zpowers t ⊔ Subgroup.zpowers v) := ⟨_, rfl⟩
  rw [← hEdef] at hEcomm hEexp hEcard
  have hEsq : ∀ w ∈ E, w * w = 1 := fun w hw => by
    have := hEexp w hw
    rwa [pow_two] at this
  have hE2 : IsPGroup 2 ↥E := IsPGroup.of_card hEcard
  have hiD : i ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hit'
  have htD : t ∈ Subgroup.centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hvD : v ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr htv.symm
  have hED : E ≤ Subgroup.centralizer ({t} : Set G) := by
    rw [hEdef]
    exact sup_le ((Subgroup.zpowers_le).mpr hiD)
      (sup_le ((Subgroup.zpowers_le).mpr htD) ((Subgroup.zpowers_le).mpr hvD))
  have hiC : i ∈ Subgroup.centralizer (N.K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk => (h.SC_commutes hi k hk).symm
  have htC : t ∈ Subgroup.centralizer (N.K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk => (h.SC_commutes hf.t_mem k hk).symm
  have hvC : v ∈ Subgroup.centralizer (N.K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk => hvK k hk
  have hEC : E ≤ Subgroup.centralizer (N.K : Set G) := by
    rw [hEdef]
    exact sup_le ((Subgroup.zpowers_le).mpr hiC)
      (sup_le ((Subgroup.zpowers_le).mpr htC) ((Subgroup.zpowers_le).mpr hvC))
  obtain ⟨S', hES', hS'⟩ := exists_isSylowTwoOf_of_le hED hE2
  obtain ⟨c, hcD, hSc⟩ := hf.sylow.exists_conj hS'
  have hcK : c ∈ Subgroup.normalizer (N.K : Set G) := h.centralizer_t_le_normalizer hcD
  have hE'S : CFSG.conjugate E c ≤ N.SC := by
    intro y hy
    rw [BenderBranch.mem_conjugate_iff] at hy
    have hyS' : c * y * c⁻¹ ∈ S' := hES' hy
    rw [hSc] at hyS'
    obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp hyS'
    have hsy' : c * s * c⁻¹ = c * y * c⁻¹ := hsy
    have hys : y = s := by
      have := mul_right_cancel hsy'
      exact (mul_left_cancel this).symm
    have hyS : y ∈ N.S := hys ▸ hs
    refine h.mem_SC_of_commutes (N.S_le_H hyS) (fun k hk => ?_)
    have hk' : c * k * c⁻¹ ∈ N.K := (Subgroup.mem_normalizer_iff.mp hcK k).mp hk
    have h1 := Subgroup.mem_centralizer_iff.mp (hEC hy) _ hk'
    have h2 : c * (y * k) * c⁻¹ = c * (k * y) * c⁻¹ := by
      calc c * (y * k) * c⁻¹ = (c * y * c⁻¹) * (c * k * c⁻¹) := by group
        _ = (c * k * c⁻¹) * (c * y * c⁻¹) := h1.symm
        _ = c * (k * y) * c⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hE''SCx : CFSG.conjugate (CFSG.conjugate E c) N.x ≤ N.SCx :=
    BenderBranch.conjugate_mono hE'S N.x
  have hE''S : CFSG.conjugate (CFSG.conjugate E c) N.x ≤ N.S := hE''SCx.trans h.SCx_le_S
  have hE''A : CFSG.conjugate (CFSG.conjugate E c) N.x ⊓ N.SC = ⊥ :=
    le_bot_iff.mp (h.SCx_inf_SC ▸ inf_le_inf_right _ hE''SCx)
  have hEelem : IsElemAbelian 2 E := isElemAbelian_of_forall hEcomm hEsq
  have hE''elem : IsElemAbelian 2 (CFSG.conjugate (CFSG.conjugate E c) N.x) :=
    isElemAbelian_conjugate (isElemAbelian_conjugate hEelem c) N.x
  have h4 := hSB.card_le_four hE''S hE''A hE''elem
  rw [BenderBranch.card_conjugate, BenderBranch.card_conjugate, hEcard] at h4
  omega

theorem caseCClaim2 : CaseCClaim2 := by
  intro G _ _ T M hs N t zK R h hfam hp hC1 i hi hi1 hi2
  by_cases hit : i = t
  · rw [hit]
    exact h.centralizer_t_le_normalizer
  intro u hu
  by_contra hnorm
  obtain ⟨v, hv2, hv1, hvi, hvt, hvit, hiv, htv, hvK⟩ :=
    h.claim2_exists_third hp.ds hfam hi hi1 hi2 hit (hC1 i hi hi1 hi2) hu hnorm
  exact h.claim2_false hp.ds hi hi1 hi2 hit hv2 hv1 hvi hvt hvit hiv htv hvK

end Claim2

end CFSG.QuasithinUnique
