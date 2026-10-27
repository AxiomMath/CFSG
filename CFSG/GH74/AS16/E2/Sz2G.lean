module

public import CFSG.GH74.AS16.E2.Data
public import CFSG.GH74.AS16.E2.TransvG
public import CFSG.GH74.E2.Action

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG CFSG.Blueprint
open CFSG.GH74.E2 hiding Hyp

theorem exists_decomp_of_inner2 {G : Type*} [Group G] {T L : Subgroup G}
    (hT : IsPGroup 2 T)
    (hZ : ∀ l ∈ L, (∀ x ∈ L, l * x = x * l) → l ^ 2 = 1)
    (hsyl : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ L → T ⊓ L ≤ P → P = T ⊓ L)
    (hinn : ∀ t ∈ T, ∃ l ∈ L, ∀ x ∈ L, t * x * t⁻¹ = l * x * l⁻¹) :
    ∀ t ∈ T, ∃ s ∈ T ⊓ L, ∃ c ∈ T ⊓ centralizer (L : Set G), t = s * c := by
  classical
  let Ts : Subgroup G :=
    { carrier := {l | l ∈ L ∧ ∃ t ∈ T, ∀ x ∈ L, t * x * t⁻¹ = l * x * l⁻¹}
      mul_mem' := by
        rintro a b ⟨haL, t1, ht1, h1⟩ ⟨hbL, t2, ht2, h2⟩
        refine ⟨L.mul_mem haL hbL, t1 * t2, T.mul_mem ht1 ht2, fun x hx => ?_⟩
        have hb : b * x * b⁻¹ ∈ L := L.mul_mem (L.mul_mem hbL hx) (L.inv_mem hbL)
        calc t1 * t2 * x * (t1 * t2)⁻¹ = t1 * (t2 * x * t2⁻¹) * t1⁻¹ := by group
          _ = t1 * (b * x * b⁻¹) * t1⁻¹ := by rw [h2 x hx]
          _ = a * (b * x * b⁻¹) * a⁻¹ := h1 _ hb
          _ = a * b * x * (a * b)⁻¹ := by group
      one_mem' := ⟨L.one_mem, 1, T.one_mem, fun x _ => by simp⟩
      inv_mem' := by
        rintro a ⟨haL, t, ht, h⟩
        refine ⟨L.inv_mem haL, t⁻¹, T.inv_mem ht, fun x hx => ?_⟩
        have hx' : a⁻¹ * x * a ∈ L := L.mul_mem (L.mul_mem (L.inv_mem haL) hx) haL
        have h1 := h _ hx'
        have h2 : t * (a⁻¹ * x * a) * t⁻¹ = x := by rw [h1]; group
        have h3 : t⁻¹ * x * t = a⁻¹ * x * a := by
          calc t⁻¹ * x * t = t⁻¹ * (t * (a⁻¹ * x * a) * t⁻¹) * t := by rw [h2]
            _ = a⁻¹ * x * a := by group
        simpa using h3 }
  have hmem : ∀ a, a ∈ Ts ↔ a ∈ L ∧ ∃ t ∈ T, ∀ x ∈ L, t * x * t⁻¹ = a * x * a⁻¹ :=
    fun a => Iff.rfl
  have hTs2 : IsPGroup 2 Ts := by
    rintro ⟨a, ha⟩
    obtain ⟨haL, t, ht, h⟩ := (hmem a).1 ha
    obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
    have hk' : t ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hpow : ∀ j : ℕ, ∀ x ∈ L, t ^ j * x * (t ^ j)⁻¹ = a ^ j * x * (a ^ j)⁻¹ := by
      intro j
      induction j with
      | zero => intro x _; simp
      | succ j ih =>
        intro x hx
        have hy : a ^ j * x * (a ^ j)⁻¹ ∈ L :=
          L.mul_mem (L.mul_mem (L.pow_mem haL j) hx) (L.inv_mem (L.pow_mem haL j))
        calc t ^ (j + 1) * x * (t ^ (j + 1))⁻¹
            = t * (t ^ j * x * (t ^ j)⁻¹) * t⁻¹ := by group
          _ = t * (a ^ j * x * (a ^ j)⁻¹) * t⁻¹ := by rw [ih x hx]
          _ = a * (a ^ j * x * (a ^ j)⁻¹) * a⁻¹ := h _ hy
          _ = a ^ (j + 1) * x * (a ^ (j + 1))⁻¹ := by group
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hcen : ∀ x ∈ L, a ^ 2 ^ k * x = x * a ^ 2 ^ k := by
      intro x hx
      have := hpow (2 ^ k) x hx
      rw [hk'] at this
      simp only [one_mul, inv_one, mul_one] at this
      calc a ^ 2 ^ k * x = (a ^ 2 ^ k * x * (a ^ 2 ^ k)⁻¹) * a ^ 2 ^ k := by group
        _ = x * a ^ 2 ^ k := by rw [← this]
    have h2 := hZ _ (L.pow_mem haL _) hcen
    show a ^ 2 ^ (k + 1) = 1
    rw [pow_succ, pow_mul]
    exact h2
  have hTsL : Ts ≤ L := fun a ha => ((hmem a).1 ha).1
  have hle : T ⊓ L ≤ Ts := fun s hs => (hmem s).2 ⟨hs.2, s, hs.1, fun x _ => rfl⟩
  have hEq : Ts = T ⊓ L := hsyl Ts hTs2 hTsL hle
  intro t ht
  obtain ⟨l, hlL, h⟩ := hinn t ht
  have hl : l ∈ T ⊓ L := hEq ▸ (hmem l).2 ⟨hlL, t, ht, h⟩
  have hc : l⁻¹ * t ∈ centralizer (L : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    have h1 := h x hx
    calc x * (l⁻¹ * t) = l⁻¹ * (l * x * l⁻¹) * t := by group
      _ = l⁻¹ * (t * x * t⁻¹) * t := by rw [h1]
      _ = l⁻¹ * t * x := by group
  exact ⟨l, hl, l⁻¹ * t, ⟨T.mul_mem (T.inv_mem hl.1) ht, hc⟩, by group⟩

section Cfg

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {z : G} {L : Subgroup G}

theorem Cfg.decomp2 (h : Cfg G T z L)
    (hZ : ∀ l ∈ L, (∀ x ∈ L, l * x = x * l) → l ^ 2 = 1)
    (hout : ∀ (φ : MulAut ↥L) (n : ℕ), φ ^ 2 ^ n = 1 → ∃ k : ↥L, ∀ x : ↥L, φ x = k * x * k⁻¹) :
    ∀ t ∈ (T : Subgroup G), ∃ s ∈ (T : Subgroup G) ⊓ L,
      ∃ c ∈ (T : Subgroup G) ⊓ centralizer (L : Set G), t = s * c := by
  refine exists_decomp_of_inner2 T.isPGroup' hZ ?_ ?_
  · intro P hP hPL hle
    exact h.isSylowOf_inf.eq_of_le hle hPL hP
  · intro t ht
    have htN := h.le_normalizer ht
    obtain ⟨n, hn⟩ := T.isPGroup' ⟨t, ht⟩
    have hn' : t ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hφn : (L.normalizerMonoidHom ⟨t, htN⟩) ^ 2 ^ n = 1 := by
      rw [← map_pow]
      have : (⟨t, htN⟩ : normalizer (L : Set G)) ^ 2 ^ n = 1 :=
        Subtype.ext (by simpa using hn')
      rw [this, map_one]
    obtain ⟨k, hk⟩ := hout _ n hφn
    refine ⟨(k : G), k.2, fun x hx => ?_⟩
    have := congrArg Subtype.val (hk ⟨x, hx⟩)
    exact this

theorem false_of_sz2 (hcfg : Cfg G T z L)
    (hdec : ∀ t ∈ (T : Subgroup G), ∃ s ∈ (T : Subgroup G) ⊓ L,
      ∃ c ∈ (T : Subgroup G) ⊓ centralizer (L : Set G), t = s * c)
    {A : Subgroup G} (hAT : A ≤ (T : Subgroup G) ⊓ L)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a * a = 1)
    (hAcard : Nat.card A = 16) (hZ2 : Nat.card ↥(L ⊓ centralizer (L : Set G)) = 2)
    (hZT : L ⊓ centralizer (L : Set G) ≤ (T : Subgroup G))
    (hZA : L ⊓ centralizer (L : Set G) ≤ A)
    (hTLA : ∀ x ∈ (T : Subgroup G) ⊓ L, ∀ a ∈ A,
      x * a * x⁻¹ * a⁻¹ ∈ L ⊓ centralizer (L : Set G))
    (hsq : ∀ s ∈ (T : Subgroup G) ⊓ L, s * s ∈ L ⊓ centralizer (L : Set G) → s ∈ A)
    (hmov : ∀ b ∈ A, b ∉ L ⊓ centralizer (L : Set G) →
      ∃ x ∈ (T : Subgroup G) ⊓ L, x * b * x⁻¹ ≠ b) : False := by
  classical
  set Zg : Subgroup G := L ⊓ centralizer (L : Set G) with hZg
  set TC : Subgroup G := (T : Subgroup G) ⊓ centralizer (L : Set G) with hTC
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hcfg.pair.orderOf_eq, pow_two] at this
  have hz1 : z ≠ 1 := by
    intro h
    have h2 := hcfg.pair.orderOf_eq
    rw [h, orderOf_one] at h2
    omega
  have hzL : ∀ l ∈ L, l * z = z * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.1 (hcfg.pair.isComp.1 hl)
  have hzTC : z ∈ TC :=
    ⟨hcfg.pair.mem_sylow, Subgroup.mem_centralizer_iff.2 fun l hl => hzL l hl⟩
  have hTC2 : IsPGroup 2 TC := T.isPGroup'.to_inf_left
  have hAT' : A ≤ (T : Subgroup G) := fun a ha => (hAT ha).1
  have hAL : A ≤ L := fun a ha => (hAT ha).2
  have : IsMulCommutative ↥A := ⟨⟨fun a b => Subtype.ext (hAcomm a a.2 b b.2)⟩⟩
  have hA2' : ∀ y : ↥A, y ^ 2 = 1 := fun y => Subtype.ext (by
    rw [pow_two]; exact hA2 y y.2)
  have hrankA : Group.rank ↥A = 4 := by
    have h := two_pow_rank_eq_card_of_exponent_two hA2'
    rw [hAcard] at h
    have h4 : 2 ^ Group.rank ↥A = 2 ^ 4 := by rw [h]; norm_num
    exact Nat.pow_right_injective le_rfl h4
  have hTCcyc : IsCyclic ↥TC := by
    apply isCyclic_of_rank_le_one
    have hcomm : ∀ q ∈ A, ∀ t ∈ TC, q * t = t * q := fun q hq t ht =>
      Subgroup.mem_centralizer_iff.1 ht.2 q (hAL hq)
    have h := gen4_rank_add_le hcfg.hyp.gen4 A TC (T.isPGroup'.to_le hAT') hTC2 hcomm
    have hle : A ⊓ TC ≤ Zg := fun x hx => ⟨hAL hx.1, hx.2.2⟩
    have hc : Nat.card ↥(A ⊓ TC) ≤ 2 := (Subgroup.card_le_of_le hle).trans hZ2.le
    have := rank_le_one_of_card_le_two hc
    omega
  have hZTC : ∀ w ∈ Zg, w ∈ TC := fun w hw => ⟨hZT hw, hw.2⟩
  have hZsq : ∀ w ∈ Zg, w * w = 1 := by
    intro w hw
    have := pow_card_eq_one' (G := ↥Zg) (x := ⟨w, hw⟩)
    rw [hZ2, pow_two] at this
    exact congrArg Subtype.val this
  have hcases : ∀ c ∈ TC, c * c = 1 → c = 1 ∨ c = z := by
    intro c hc hc2
    have hz2' : z ^ 2 = 1 := by rw [pow_two]; exact hz2
    have hc2' : c ^ 2 = 1 := by rw [pow_two]; exact hc2
    have := cyclic_pow_two_eq_one (X := ↥TC) (z := ⟨z, hzTC⟩) (c := ⟨c, hc⟩)
      (Subtype.ext hz2') (fun h => hz1 (congrArg Subtype.val h)) (Subtype.ext hc2')
    rcases this with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  have hZcases : ∀ w ∈ Zg, w = 1 ∨ w = z := fun w hw => hcases w (hZTC w hw) (hZsq w hw)
  have hzZ : z ∈ Zg := by
    have : Nontrivial ↥Zg := by
      rw [← Finite.one_lt_card_iff_nontrivial]
      omega
    obtain ⟨w, hw⟩ := exists_ne (1 : ↥Zg)
    have hw1 : (w : G) ≠ 1 := fun h => hw (Subtype.ext h)
    rcases hZcases w w.2 with h | h
    · exact absurd h hw1
    · rw [← h]; exact w.2
  have hzA : z ∈ A := hZA hzZ
  have hTL : ∀ x ∈ (T : Subgroup G) ⊓ L, ∀ c ∈ TC, x * c = c * x := fun x hx c hc =>
    Subgroup.mem_centralizer_iff.1 hc.2 x hx.2
  refine false_of_transv_fusion hcfg.hyp.simple hcfg.hyp.nonabelian hcfg.pair.orderOf_eq hAT' hzA
    hAcomm hA2 (by omega) ?_ ?_ ?_
  ·
    intro t ht ht2
    obtain ⟨s, hs, c, hc, rfl⟩ := hdec t ht
    have hcomm : Commute s c := hTL s hs c hc
    have h1 : s * s * (c * c) = 1 := by
      calc s * s * (c * c) = s * (s * c) * c := by group
        _ = s * (c * s) * c := by rw [hcomm.eq]
        _ = s * c * (s * c) := by group
        _ = 1 := ht2
    have hss : s * s ∈ Zg := by
      have h2 : s * s = (c * c)⁻¹ := eq_inv_of_mul_eq_one_left h1
      refine ⟨L.mul_mem hs.2 hs.2, ?_⟩
      rw [h2]
      exact (centralizer (L : Set G)).inv_mem ((centralizer (L : Set G)).mul_mem hc.2 hc.2)
    have hsA : s ∈ A := hsq s hs hss
    have hs2 : s * s = 1 := hA2 s hsA
    have hc2 : c * c = 1 := by rw [hs2, one_mul] at h1; exact h1
    have hcA : c ∈ A := by
      rcases hcases c hc hc2 with h | h
      · rw [h]; exact A.one_mem
      · rw [h]; exact hzA
    exact A.mul_mem hsA hcA
  ·
    intro t ht a ha
    obtain ⟨s, hs, c, hc, rfl⟩ := hdec t ht
    have hca : c * a * c⁻¹ = a := by
      have := (Subgroup.mem_centralizer_iff.1 hc.2 a (hAL ha)).symm
      calc c * a * c⁻¹ = (a * c) * c⁻¹ := by rw [this]
        _ = a := by group
    have e : s * c * a * (s * c)⁻¹ = s * a * s⁻¹ := by
      calc s * c * a * (s * c)⁻¹ = s * (c * a * c⁻¹) * s⁻¹ := by group
        _ = s * a * s⁻¹ := by rw [hca]
    rw [e]
    have hcom := hTLA s hs a ha
    rcases hZcases _ hcom with h | h
    · left
      calc s * a * s⁻¹ = (s * a * s⁻¹ * a⁻¹) * a := by group
        _ = a := by rw [h, one_mul]
    · right
      have hza : z * a = a * z := (hzL a (hAL ha)).symm
      calc s * a * s⁻¹ = (s * a * s⁻¹ * a⁻¹) * a := by group
        _ = z * a := by rw [h]
        _ = a * z := hza
  · intro b hb hb1 hbz
    have hbnZ : b ∉ Zg := fun hbZ => by
      rcases hZcases b hbZ with h | h
      · exact hb1 h
      · exact hbz h
    obtain ⟨x, hx, hxb⟩ := hmov b hb hbnZ
    exact ⟨x, hx.1, hxb⟩

end Cfg

end CFSG.GH74.AS16.E2
