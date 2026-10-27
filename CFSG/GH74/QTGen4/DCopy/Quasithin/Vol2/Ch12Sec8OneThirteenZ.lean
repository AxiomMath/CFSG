module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneThirteenZ
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneTwelve

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace L128P

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem exists_eq_mul_mul_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) {k x : G}
    (hk : k ∈ L ⊔ T) (hkN : k ∉ Subgroup.normalizer (V₁ : Set G)) (hx : x ∈ L ⊔ T)
    (hxN : x ∉ Subgroup.normalizer (V₁ : Set G)) :
    ∃ s ∈ lOne L V₁ ⊔ T, ∃ m ∈ Subgroup.normalizer (V₁ : Set G), x = s * k * m := by
  obtain ⟨-, hTV⟩ := h.hyp.le_and_normalizes_F4 h1222
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le h.hyp.irrPlus.2.2.1 hTV
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ V₁, z ≠ 1 := by
    by_contra hall
    push Not at hall
    have : V₁ = ⊥ := (Subgroup.eq_bot_iff_forall V₁).2 hall
    rw [this, Subgroup.card_bot] at hV₁2
    norm_num at hV₁2
  have hzV := hV₁.1 hz
  have ha := L1297.conj_not_mem_of_not_mem_normalizer hV₁2 hz hz1 hkN
  have hb := L1297.conj_not_mem_of_not_mem_normalizer hV₁2 hz hz1 hxN
  have haV : k * z * k⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLTV hk) z).1 hzV
  have hbV : x * z * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLTV hx) z).1 hzV
  obtain ⟨s, hs, hsab⟩ := L1297.exists_mem_sup_conj_eq_F4 h1222 h hV₁ haV hbV ha hb
  refine ⟨s, hs, k⁻¹ * s⁻¹ * x, L1297.mem_normalizer_of_conj_eq hV₁2 hz hz1 ?_, by group⟩
  calc k⁻¹ * s⁻¹ * x * z * (k⁻¹ * s⁻¹ * x)⁻¹ = k⁻¹ * s⁻¹ * (x * z * x⁻¹) * s * k := by group
    _ = k⁻¹ * s⁻¹ * (s * (k * z * k⁻¹) * s⁻¹) * s * k := by rw [hsab]
    _ = z := by group

theorem conj_centerOf_mem_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) {k : G} (hk : k ∈ L ⊔ T)
    (hkN : k ∉ Subgroup.normalizer (V₁ : Set G))
    (hkZ : ∀ z ∈ zU128 V V₁, k⁻¹ * z * k ∈ u128 V V₁) {x : G} (hx : x ∈ L ⊔ T) :
    ∀ z ∈ zU128 V V₁, x⁻¹ * z * x ∈ u128 V V₁ := by
  have hNU : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (u128 V V₁ : Set G) :=
    le_normalizer_conjClosure V _
  have hNZ : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (zU128 V V₁ : Set G) :=
    hNU.trans (normalizer_le_normalizer_centerOf _)
  have hsupN : lOne L V₁ ⊔ T ≤ Subgroup.normalizer (V₁ : Set G) :=
    sup_le ((oTwoUpper_le _).trans inf_le_right) hs.v1.2.2
  intro z hz
  by_cases hxN : x ∈ Subgroup.normalizer (V₁ : Set G)
  · have h1 : x⁻¹ * z * x⁻¹⁻¹ ∈ zU128 V V₁ :=
      (Subgroup.mem_normalizer_iff.1 (hNZ (Subgroup.inv_mem _ hxN)) z).1 hz
    rw [inv_inv] at h1
    exact h1.1
  · obtain ⟨s, hs', m, hm, rfl⟩ := exists_eq_mul_mul_F4 h1222 hs.hyp hs.v1 hk hkN hx hxN
    have hz' : s⁻¹ * z * s⁻¹⁻¹ ∈ zU128 V V₁ :=
      (Subgroup.mem_normalizer_iff.1 (hNZ (Subgroup.inv_mem _ (hsupN hs'))) z).1 hz
    rw [inv_inv] at hz'
    have h3 : m⁻¹ * (k⁻¹ * (s⁻¹ * z * s) * k) * m⁻¹⁻¹ ∈ u128 V V₁ :=
      (Subgroup.mem_normalizer_iff.1 (hNU (Subgroup.inv_mem _ hm)) _).1 (hkZ _ hz')
    rw [inv_inv] at h3
    have e : (s * k * m)⁻¹ * z * (s * k * m) = m⁻¹ * (k⁻¹ * (s⁻¹ * z * s) * k) * m := by group
    rw [e]
    exact h3

theorem lOne_le_centralizer_centerOf_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    {T L V : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂)
    {k : G} (hk : k ∈ oTwoUpper (p128 T L V)) (hkN : k ∉ Subgroup.normalizer (V₁ : Set G))
    (hkZ : ∀ z ∈ zU128 V V₁, k⁻¹ * z * k ∈ u128 V V₁) :
    lOne L V₁ ≤ Subgroup.centralizer (zU128 V V₁ : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hs.hyp
  obtain ⟨-, hTV⟩ := hyp.hyp.le_and_normalizes_F4 h1222
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.hyp.irrPlus.2.2.1
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
  have S := setting128A_F4 h1222 h12213 hs
  have hUeq := uA_eq_F4 h1222 hs
  have hUT : u128 V V₁ ≤ T := (hs.almostSpecial_F4 h1222 h12213).G22_three.1
  have hKL := oTwoUpper_p128_le hyp
  have hkL : k ∈ L := hKL hk
  have hkLT : k ∈ L ⊔ T := Subgroup.mem_sup_left hkL
  have hcomm : ∀ a ∈ u128 V V₁, ∀ b ∈ u128 V V₁, a * b * a⁻¹ * b⁻¹ ∈ V₁ := by
    intro a ha b hb
    rw [← hUeq] at ha hb
    exact S.commutator_mem ha hb
  have hZx : ∀ x ∈ L ⊔ T, ∀ z ∈ zU128 V V₁, x⁻¹ * z * x ∈ u128 V V₁ :=
    fun x hx => conj_centerOf_mem_F4 h1222 hs hkLT hkN hkZ hx

  set Y := conjClosure (zU128 V V₁) L with hYdef
  have hYU : ∀ x ∈ L, ∀ y ∈ Y, x * y * x⁻¹ ∈ u128 V V₁ := by
    intro x hx y hy
    have hle : Y ≤ (u128 V V₁).comap (MulAut.conj x).toMonoidHom :=
      conjClosure_le fun h hh z hz => by
        rw [Subgroup.mem_comap]
        show x * (h * z * h⁻¹) * x⁻¹ ∈ u128 V V₁
        have h1 := hZx (x * h)⁻¹ (Subgroup.inv_mem _ (Subgroup.mem_sup_left (L.mul_mem hx hh)))
          z hz
        have e : x * (h * z * h⁻¹) * x⁻¹ = (x * h)⁻¹⁻¹ * z * (x * h)⁻¹ := by group
        rw [e]
        exact h1
    exact hle hy

  set Q := centralizerMod V ⊤ Y with hQdef
  have hUxQ : ∀ x ∈ L, ∀ a, x * a * x⁻¹ ∈ u128 V V₁ → a ∈ Q := by
    intro x hx a ha
    refine ⟨Subgroup.mem_top a, ?_, fun y hy => ?_⟩
    · have h1 : x * a * x⁻¹ ∈ Subgroup.normalizer (V : Set G) := hTV (hUT ha)
      have e : a = x⁻¹ * (x * a * x⁻¹) * x := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hLV hx)) h1) (hLV hx)
    · have h1 := hcomm _ ha _ (hYU x hx y hy)
      have e : (x * a * x⁻¹) * (x * y * x⁻¹) * (x * a * x⁻¹)⁻¹ * (x * y * x⁻¹)⁻¹ =
          x * (a * y * a⁻¹ * y⁻¹) * x⁻¹ := by group
      rw [e] at h1
      exact (Subgroup.mem_normalizer_iff.1 (hLV hx) _).2 (hs.v1.1 h1)
  have hUQ : ∀ u ∈ u128 V V₁, u ∈ Q := fun u hu => hUxQ 1 L.one_mem u (by simpa using hu)
  have hYn : L ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_conjClosure _ L
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) := by
    intro l hl
    refine mem_normalizer_of_conj_mem_of_finite fun a ha => ?_
    obtain ⟨-, haV, hay⟩ := ha
    refine ⟨Subgroup.mem_top _, Subgroup.mul_mem _ (Subgroup.mul_mem _ (hLV hl) haV)
      (Subgroup.inv_mem _ (hLV hl)), fun y hy => ?_⟩
    have hy' : l⁻¹ * y * l⁻¹⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.1 (hYn (Subgroup.inv_mem _ hl)) y).1 hy
    rw [inv_inv] at hy'
    have h2 := (Subgroup.mem_normalizer_iff.1 (hLV hl) _).1 (hay _ hy')
    have e : l * a * l⁻¹ * y * (l * a * l⁻¹)⁻¹ * y⁻¹ =
        l * (a * (l⁻¹ * y * l) * a⁻¹ * (l⁻¹ * y * l)⁻¹) * l⁻¹ := by group
    rw [e]
    exact h2
  have hQL : L ≤ Subgroup.normalizer ((Q ⊓ L : Subgroup G) : Set G) := fun l hl =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hLQ hl, Subgroup.le_normalizer hl⟩

  obtain ⟨e⟩ := hyp.quot
  have hn3 : 3 ≤ n := by rcases hyp.n_mem with rfl | rfl | rfl <;> omega
  obtain ⟨hsimple, -⟩ := isSimpleGroup_sl_zmod_two hn3
  have hsL : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := e.isSimpleGroup
  rcases L1297.le_pCoreOf_or_le_sup hsL inf_le_right hQL with h1 | h1
  ·
    exfalso
    obtain ⟨u, hu, huC⟩ : ∃ u ∈ L128A.uA V₂ V₁, u ∉ Subgroup.centralizer (V₂ : Set G) := by
      by_contra hall
      push Not at hall
      exact S.not_le_centralizer_V hall
    have huW : u ∉ L128A.wA V₂ V₁ := fun h2 => huC h2.2
    have hgood : L128A.Good V₁ (oTwoUpper (p128 T L V)) k := ⟨hk, hkN⟩
    have huU : u ∈ u128 V V₁ := hUeq ▸ hu
    have huT : u ∈ T := hUT huU
    have hc : u * k * u⁻¹ * k⁻¹ ∈ Q ⊓ L := by
      refine ⟨?_, ?_⟩
      · have h2 : k * u⁻¹ * k⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.1 (hLQ hkL) u⁻¹).1 (hUQ _ (Subgroup.inv_mem _ huU))
        have e2 : u * k * u⁻¹ * k⁻¹ = u * (k * u⁻¹ * k⁻¹) := by group
        rw [e2]
        exact Subgroup.mul_mem _ (hUQ u huU) h2
      · have h2 : u * k * u⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.1 (hyp.hyp.normalizes huT) k).1 hkL
        exact L.mul_mem h2 (L.inv_mem hkL)
    have hcO := h1 hc
    rw [← inf_centralizer_eq_pCoreOf_F4 h1222 hyp] at hcO
    have hcV₂ : u * k * u⁻¹ * k⁻¹ ∈ Subgroup.centralizer (V₂ : Set G) :=
      Subgroup.centralizer_le hs.v2.1 hcO.2
    have hukT : u ∈ oTwoUpper (p128 T L V) ⊔ T := Subgroup.mem_sup_right huT
    have hkKT : k ∈ oTwoUpper (p128 T L V) ⊔ T := Subgroup.mem_sup_left hk
    have hcKT : u * k * u⁻¹ * k⁻¹ ∈ oTwoUpper (p128 T L V) ⊔ T :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hukT hkKT)
        (Subgroup.inv_mem _ hukT)) (Subgroup.inv_mem _ hkKT)
    have hcO2 : u * k * u⁻¹ * k⁻¹ ∈ pCoreOf 2 (oTwoUpper (p128 T L V) ⊔ T) := by
      rw [← S.centralizer]
      exact ⟨hcKT, hcV₂⟩
    have hk3 := S.pow_three_mem_pCoreOf_LT hk
    have hukO := S.mul_mul_inv_mul_mem_pCoreOf_LT hukT hkKT (S.sq_mem_pCoreOf_LT hu)
      (S.not_mem_pCoreOf_LT_of_not_mem_W hu huW) hk3 (S.not_mem_pCoreOf_LT_of_good hgood)
    have hk2 : k ^ 2 ∈ pCoreOf 2 (oTwoUpper (p128 T L V) ⊔ T) := by
      have e2 : k ^ 2 = (u * k * u⁻¹ * k⁻¹)⁻¹ * (u * k * u⁻¹ * k) := by rw [sq]; group
      rw [e2]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcO2) hukO
    apply S.not_mem_pCoreOf_LT_of_good hgood
    have e2 : k = k ^ 3 * (k ^ 2)⁻¹ := by rw [pow_three, sq]; group
    rw [e2]
    exact Subgroup.mul_mem _ hk3 (Subgroup.inv_mem _ hk2)
  ·
    have hO2 : IsPGroup 2 (pCoreOf 2 L) := pCoreOf_isPGroup 2 L
    have hO2N : pCoreOf 2 L ≤ Subgroup.normalizer ((Q ⊓ L : Subgroup G) : Set G) :=
      (pCoreOf_le 2 L).trans hQL
    have hodd : ∀ y ∈ L, Odd (orderOf y) → y ∈ Q := by
      intro y hy hy2
      obtain ⟨j, hj⟩ := exists_two_pow_mem_of_le_sup hO2 hO2N h1 hy
      exact (mem_of_odd_of_two_pow_mem hy2 hj).1
    show Subgroup.closure _ ≤ _
    refine (Subgroup.closure_le _).2 fun y hy => ?_
    obtain ⟨⟨hyL, hyN⟩, hy2⟩ := hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro z hz
    have hzY : z ∈ Y := le_conjClosure _ L hz
    have h2 := (hodd y hyL hy2).2.2 z hzY
    have hyZ : y ∈ Subgroup.normalizer (zU128 V V₁ : Set G) :=
      (le_normalizer_conjClosure V _).trans (normalizer_le_normalizer_centerOf _) hyN
    have h3 : y * z * y⁻¹ * z⁻¹ ∈ zU128 V V₁ :=
      (zU128 V V₁).mul_mem ((Subgroup.mem_normalizer_iff.1 hyZ z).1 hz)
        ((zU128 V V₁).inv_mem hz)
    have h4 : y * z * y⁻¹ * z⁻¹ ∈ V₁ := by
      rw [← lemma12_8_8_three_F4 h1222 h12213 hs]
      exact ⟨h2, h3⟩
    have h5 := conj_eq_of_odd_of_commutator_mem hV₁2 hyN h4 hy2
    calc z * y = (y * z * y⁻¹) * y := by rw [h5]
      _ = y * z := by group

theorem sup_le_normalizer_centerOf_i128_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    {T L V : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂)
    {k : G} (hk : k ∈ oTwoUpper (p128 T L V)) (hkN : k ∉ Subgroup.normalizer (V₁ : Set G))
    (hkZ : ∀ z ∈ zU128 V V₁, k⁻¹ * z * k ∈ u128 V V₁) :
    zU128 V V₁ = centerOf (i128 T L V V₁) ⊔ V₁ ∧
      Disjoint (centerOf (i128 T L V V₁)) V₁ ∧
      oTwoUpper (p128 T L V) ≤ Subgroup.centralizer (centerOf (i128 T L V V₁) : Set G) ∧
      L ⊔ T ≤ Subgroup.normalizer (centerOf (i128 T L V V₁) : Set G) := by
  have S := setting128A_F4 h1222 h12213 hs
  have hUeq := uA_eq_F4 h1222 hs
  have hgood : L128A.Good V₁ (oTwoUpper (p128 T L V)) k := ⟨hk, hkN⟩
  have hle : rconj (centerOf (L128A.uA V₂ V₁)) k ≤ L128A.uA V₂ V₁ := by
    rw [hUeq]
    intro w hw
    rw [mem_rconj] at hw
    have e : w = k⁻¹ * (k * w * k⁻¹) * k := by group
    rw [e]
    exact hkZ _ hw
  have h5 := S.ten_five hgood hle
  rw [hUeq, ← i128_eq_sup_F4 h1222 h12213 hs] at h5
  obtain ⟨hZ, hdisj, hKC⟩ := h5
  refine ⟨hZ, hdisj, hKC, ?_⟩
  set J := centerOf (i128 T L V V₁) with hJdef
  have hZ' : zU128 V V₁ = J ⊔ V₁ := hZ
  have hJZ : J ≤ zU128 V V₁ := hZ' ▸ le_sup_left
  have hCN : Subgroup.centralizer (J : Set G) ≤ Subgroup.normalizer (J : Set G) := fun c hc =>
    mem_normalizer_of_conj_mem_of_finite fun w hw => by
      rw [← Subgroup.mem_centralizer_iff.1 hc w hw, mul_inv_cancel_right]
      exact hw
  have hL₁J : lOne L V₁ ≤ Subgroup.normalizer (J : Set G) :=
    ((lOne_le_centralizer_centerOf_F4 h1222 h12213 hs hk hkN hkZ).trans
      (Subgroup.centralizer_le hJZ)).trans hCN
  have hTJ : T ≤ Subgroup.normalizer (J : Set G) :=
    (hs.v2.2.2.trans (normalizer_le_normalizer_i128_F4 h1222 hs)).trans
      (normalizer_le_normalizer_centerOf _)
  have hKLT : oTwoUpper (p128 T L V) ≤ L ⊔ T := (oTwoUpper_le _).trans inf_le_left
  have hL₁LT : lOne L V₁ ≤ L ⊔ T := ((oTwoUpper_le _).trans inf_le_left).trans le_sup_left
  have hX := L1297.sup_le_of_not_le_normalizer_F4 h1222 hs.hyp hs.v1
    (X := oTwoUpper (p128 T L V) ⊔ lOne L V₁ ⊔ T) (sup_le_sup_right le_sup_right T)
    (sup_le (sup_le hKLT hL₁LT) le_sup_right)
    (fun hle' => hkN (hle' (Subgroup.mem_sup_left (Subgroup.mem_sup_left hk))))
  exact hX.trans (sup_le (sup_le (hKC.trans hCN) hL₁J) hTJ)

end L128P

end CFSG.Quasithin.H13
