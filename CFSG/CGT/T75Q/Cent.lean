module

public import CFSG.CGT.T75P.DecD

public section

namespace CFSG.CGT.T75Q

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75P
open scoped MatrixGroups Matrix

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

section Conj

theorem isTransvection_of_card_centralizer {H : Subgroup G}
    [hN : (T.subgroupOf H).Normal] (e : ↥H ⧸ T.subgroupOf H ≃* SL(n, GaloisField 2 m))
    (φ : ↥T ≃* Multiplicative (Fin n → GaloisField 2 m))
    (hcompat : ∀ (h : ↥H) (t : ↥T) (hmem : (h : G) * t * (h : G)⁻¹ ∈ T),
      φ ⟨(h : G) * t * (h : G)⁻¹, hmem⟩ =
        Multiplicative.ofAdd (((e (QuotientGroup.mk h) : SL(n, GaloisField 2 m)) :
          Matrix (Fin n) (Fin n) (GaloisField 2 m)).mulVec (Multiplicative.toAdd (φ t))))
    {x : G} (hxH : x ∈ H) (hxN : x ∈ Subgroup.normalizer (T : Set G)) (hx2 : x * x = 1)
    (hxT : x ∉ T)
    (hcard : Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) =
      Nat.card (GaloisField 2 m) ^ (n - 1)) :
    IsTransvection (e (QuotientGroup.mk (⟨x, hxH⟩ : ↥H))) := by
  have hu2 : e (QuotientGroup.mk (⟨x, hxH⟩ : ↥H)) * e (QuotientGroup.mk (⟨x, hxH⟩ : ↥H))
      = 1 := by
    rw [← map_mul, ← QuotientGroup.mk_mul]
    have : (⟨x, hxH⟩ * ⟨x, hxH⟩ : ↥H) = 1 := Subtype.ext hx2
    rw [this, QuotientGroup.mk_one, map_one]
  have hu1 : e (QuotientGroup.mk (⟨x, hxH⟩ : ↥H)) ≠ 1 := by
    intro h
    have h' : (QuotientGroup.mk (⟨x, hxH⟩ : ↥H) : ↥H ⧸ T.subgroupOf H) = 1 :=
      e.injective (by rw [map_one]; exact h)
    exact hxT (Subgroup.mem_subgroupOf.1
      ((QuotientGroup.eq_one_iff (N := T.subgroupOf H) (⟨x, hxH⟩ : ↥H)).1 h'))
  refine isTransvection_of_card_fixed hu2 hu1 ?_
  rw [card_fixed_eq_card_centralizer e φ hcompat hxH hxN, hcard]

theorem conj_of_isTransvection {H : Subgroup G} [hN : (T.subgroupOf H).Normal]
    (hc : Sec6Ctx T T₁ n m) (h62 : Sec62) (h63 : Sec63)
    (hHN : H ≤ Subgroup.normalizer (T : Set G))
    (e : ↥H ⧸ T.subgroupOf H ≃* SL(n, GaloisField 2 m)) {x y : G} (hx : x ∈ normD T)
    (hy : y ∈ normD T) (hyT : y ∉ T) (hxH : x ∈ H) (hyH : y ∈ H)
    (hux : IsTransvection (e (QuotientGroup.mk (⟨x, hxH⟩ : ↥H))))
    (huy : IsTransvection (e (QuotientGroup.mk (⟨y, hyH⟩ : ↥H)))) :
    ∃ g ∈ Subgroup.normalizer (T : Set G), y = g * x * g⁻¹ := by
  obtain ⟨W, hW⟩ := exists_conj_of_isTransvection hux huy
  obtain ⟨q, hq⟩ := e.surjective W
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  have hmk : (QuotientGroup.mk (w * ⟨x, hxH⟩ * w⁻¹) : ↥H ⧸ T.subgroupOf H) =
      QuotientGroup.mk (⟨y, hyH⟩ : ↥H) := by
    apply e.injective
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv, hq, ← hW]
  have hmem := QuotientGroup.eq.1 hmk
  rw [Subgroup.mem_subgroupOf] at hmem
  set z : G := (w : G) * x * (w : G)⁻¹ with hz
  have hzD : z ∈ classD T := by
    have := classD_conj hx.1 (w : G)⁻¹
    rwa [inv_inv] at this
  have hzy : z = y * (z⁻¹ * y)⁻¹ := by group
  have hT' : z⁻¹ * y ∈ T := by
    have : (↑(w * ⟨x, hxH⟩ * w⁻¹ : ↥H))⁻¹ * y ∈ T := hmem
    simpa [hz] using this
  obtain ⟨s, hs, hzs⟩ := hc.eq_conj_of_mem_coset h62 h63 hy hyT hzD (T.inv_mem hT') hzy
  refine ⟨s * w, (Subgroup.normalizer (T : Set G)).mul_mem (Subgroup.le_normalizer hs)
    (hHN w.2), ?_⟩
  have hsz : s * z * s⁻¹ = y := by
    have : z = s⁻¹ * y * s := hzs
    rw [this]
    group
  rw [← hsz, hz]
  group

theorem sec67_conj_of_card (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ n m) (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) {x y : G}
    (hx : x ∈ normD T) (hxT : x ∉ T) (hy : y ∈ normD T) (hyT : y ∉ T)
    (hxc : Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card ↥(normIn T T₁))
    (hyc : Nat.card ↥(T ⊓ Subgroup.centralizer ({y} : Set G)) = Nat.card ↥(normIn T T₁)) :
    ∃ g ∈ Subgroup.normalizer (T : Set G), y = g * x * g⁻¹ := by
  have := hc.finite
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := hc.hy.card
    rw [hc.hT, pow_zero, one_pow] at this
    omega
  have hcardF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m hm0
  have hxH := hc.mem_hSub_of_card_centralizer h1 hx hxT hxc
  have hyH := hc.mem_hSub_of_card_centralizer h1 hy hyT hyc
  obtain ⟨-, hHN, -⟩ := hSub_data T T₁
  have hx2 : x * x = 1 := mul_self_eq_one_of_mem_classD hc.hy.pair.wc.1 hx.1
  have hy2 : y * y = 1 := mul_self_eq_one_of_mem_classD hc.hy.pair.wc.1 hy.1
  have hcn : Nat.card (GaloisField 2 m) ^ (n - 1) = Nat.card ↥(normIn T T₁) := by
    rw [hc.card_normIn, hcardF]
  obtain ⟨hN, e, φ, hcompat⟩ := hnat
  have hux := isTransvection_of_card_centralizer e φ hcompat hxH hx.2 hx2 hxT (hxc.trans hcn.symm)
  have huy := isTransvection_of_card_centralizer e φ hcompat hyH hy.2 hy2 hyT (hyc.trans hcn.symm)
  exact conj_of_isTransvection hc h62 h63 hHN e hx hy hyT hxH hyH hux huy

end Conj

section Fix

variable [Finite G]

theorem eq_one_of_fixed_T₁ (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63) (hc : Sec6Ctx T T₁ n 1)
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) n 1) {k : ℕ} (ch : TransvChain n k) (hn : 3 ≤ n)
    {ℓ : G} (hℓ : ℓ ∈ normIn T₁ T)
    (hfix : ∀ h ∈ hSub T (normIn T₁ T), h ∈ Subgroup.normalizer (T₁ : Set G) →
      h * ℓ * h⁻¹ = ℓ) : ℓ = 1 := by
  by_contra hℓ1
  have hcfg := hc.sec3.cfg
  have hℓT₁ : ℓ ∈ T₁ := (mem_normIn.1 hℓ).1
  have hℓsq : ℓ ^ 2 = 1 := by
    rw [pow_two]
    exact elemAbelian_mul_self hcfg.wc₁.1 hℓT₁
  have hord : orderOf ℓ = 2 := orderOf_eq_prime hℓsq hℓ1
  have hcard : 4 ≤ Nat.card (normIn T₁ T) := by
    rw [hc.card_normIn_swap, hc.card_normIn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ 1) ^ (n - 1) := by
        rw [← pow_mul, one_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨ℓ', hℓ', hℓ'1, hℓ'ne⟩ : ∃ ℓ' ∈ normIn T₁ T, ℓ' ≠ 1 ∧ ℓ' ≠ ℓ := by
    have hnle : ¬ normIn T₁ T ≤ Subgroup.zpowers ℓ := by
      intro hle
      have h2 := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers, hord] at h2
      omega
    obtain ⟨x, hx, hxn⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
    refine ⟨x, hx, ?_, ?_⟩
    · rintro rfl
      exact hxn (Subgroup.one_mem _)
    · rintro rfl
      exact hxn (Subgroup.mem_zpowers _)
  obtain ⟨hℓD, hℓN, hℓT⟩ := mem_normD_of_mem_normIn hc hℓ hℓ1
  obtain ⟨hℓ'D, hℓ'N, hℓ'T⟩ := mem_normD_of_mem_normIn hc hℓ' hℓ'1
  have hcard1 : Nat.card ↥(T ⊓ Subgroup.centralizer ({ℓ} : Set G)) =
      Nat.card ↥(normIn T T₁) := by
    rw [hcfg.inf_centralizer_eq_normIn hℓ hℓ1]
  have hcard2 : Nat.card ↥(T ⊓ Subgroup.centralizer ({ℓ'} : Set G)) =
      Nat.card ↥(normIn T T₁) := by
    rw [hcfg.inf_centralizer_eq_normIn hℓ' hℓ'1]
  obtain ⟨g, hg, hgℓ⟩ := sec67_conj_of_card h1 h62 h63 hc hnat ⟨hℓD, hℓN⟩ hℓT
    ⟨hℓ'D, hℓ'N⟩ hℓ'T hcard1 hcard2
  obtain ⟨h, hh, c, hcC, hgh⟩ := normalizer_eq_mul h62 h63 hc hnat ch hg
  have hℓH : ℓ ∈ hSub T (normIn T₁ T) := le_hSub hℓ
  have hcomm : ℓ * c = c * ℓ := Subgroup.mem_centralizer_iff.1 hcC ℓ hℓH
  have hℓ'h : ℓ' = h * ℓ * h⁻¹ := by
    rw [hgℓ, hgh]
    calc h * c * ℓ * (h * c)⁻¹ = h * (c * ℓ) * c⁻¹ * h⁻¹ := by group
      _ = h * (ℓ * c) * c⁻¹ * h⁻¹ := by rw [hcomm]
      _ = h * ℓ * h⁻¹ := by group
  have hℓ'T₁ : ℓ' ∈ T₁ := (mem_normIn.1 hℓ').1
  have hmeet : T₁ ⊓ conjSubgroup h T₁ ≠ ⊥ := by
    intro hb
    have hmem : ℓ' ∈ T₁ ⊓ conjSubgroup h T₁ := by
      refine ⟨hℓ'T₁, mem_conjSubgroup.2 ?_⟩
      have : h⁻¹ * ℓ' * h = ℓ := by rw [hℓ'h]; group
      rw [this]
      exact hℓT₁
    rw [hb, Subgroup.mem_bot] at hmem
    exact hℓ'1 hmem
  have hhN : h ∈ Subgroup.normalizer (T₁ : Set G) :=
    mem_normalizer_iff_conjSubgroup_eq.2 (hcfg.wc₁.conj_eq_of_inf_ne_bot hmeet)
  exact hℓ'ne (hℓ'h.trans (hfix h hh hhN))

theorem centralizer_hSub_le_centralizer_T₁ (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ n 1) (hnat : NaturalSL T (hSub T (normIn T₁ T)) n 1) {k : ℕ}
    (ch : TransvChain n k) (hn : 3 ≤ n) {c : G}
    (hcC : c ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G)) :
    c ∈ Subgroup.centralizer (T₁ : Set G) := by
  have hcfg := hc.sec3.cfg
  obtain ⟨-, hHN, -⟩ := hSub_data T T₁
  have hT₁ab := hcfg.wc₁.1
  have hcL : ∀ l ∈ normIn T₁ T, c * l = l * c := fun l hl =>
    (Subgroup.mem_centralizer_iff.1 hcC l (le_hSub hl)).symm
  obtain ⟨ℓ₀, hℓ₀, hℓ₀1⟩ := exists_ne_one_mem_normIn hc
  have hcN : c ∈ Subgroup.normalizer (T₁ : Set G) :=
    hcfg.wc₁.centralizer_le_normalizer (mem_normIn.1 hℓ₀).1 hℓ₀1
      (Subgroup.mem_centralizer_singleton_iff.2 (hcL ℓ₀ hℓ₀))
  have hT₁card : Nat.card T₁ = 2 ^ n := by
    obtain ⟨x, hx⟩ := hc.hy.pair.conj
    rw [hx, card_conjSubgroup, hc.hT, ← pow_mul, one_mul]
  have hL₁card : Nat.card (normIn T₁ T) = 2 ^ (n - 1) := by
    rw [hc.card_normIn_swap, hc.card_normIn, ← pow_mul, one_mul]
  have hrel : (normIn T₁ T).relIndex T₁ = 2 := by
    have h := Subgroup.relIndex_mul_card (H := normIn T₁ T) (K := T₁)
    rw [inf_eq_left.2 (normIn_le T₁ T), hL₁card, hT₁card] at h
    have hn1 : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hn1] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) _) h
  obtain ⟨a, haT₁, ha⟩ := Subgroup.relIndex_dvd_two_iff.1 (dvd_of_eq hrel)
  have haL : a ∉ normIn T₁ T := by
    intro haL
    have hle : T₁ ≤ normIn T₁ T := fun b hb => by
      rcases ha b hb with h | h
      · have := (normIn T₁ T).mul_mem h ((normIn T₁ T).inv_mem haL)
        simpa using this
      · exact h
    have := Subgroup.relIndex_eq_one.2 hle
    omega
  have haa : a * a = 1 := elemAbelian_mul_self hT₁ab haT₁
  set u : G := c * a * c⁻¹ with hu
  have huT₁ : u ∈ T₁ := (Subgroup.mem_normalizer_iff.1 hcN a).1 haT₁
  have huL : u ∉ normIn T₁ T := by
    intro huL
    apply haL
    have h1 : c⁻¹ * u * c = a := by rw [hu]; group
    have h2 : c⁻¹ * u = u * c⁻¹ := by
      have := hcL u huL
      calc c⁻¹ * u = c⁻¹ * (u * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * u) * c⁻¹ := by rw [this]
        _ = u * c⁻¹ := by group
    rw [← h1, h2, mul_assoc, inv_mul_cancel, mul_one]
    exact huL
  have hℓL : u * a ∈ normIn T₁ T := by
    rcases ha u huT₁ with h | h
    · exact h
    · exact absurd h huL
  have hfix : ∀ h ∈ hSub T (normIn T₁ T), h ∈ Subgroup.normalizer (T₁ : Set G) →
      h * (u * a) * h⁻¹ = u * a := by
    intro h hh hhN
    have hhN' : h ∈ Subgroup.normalizer (T : Set G) := hHN hh
    have hconjL : ∀ k : G, k ∈ Subgroup.normalizer (T₁ : Set G) →
        k ∈ Subgroup.normalizer (T : Set G) → ∀ x ∈ normIn T₁ T, k * x * k⁻¹ ∈ normIn T₁ T :=
      fun k hkN₁ hkN x hx =>
        mem_normIn.2 ⟨(Subgroup.mem_normalizer_iff.1 hkN₁ x).1 (mem_normIn.1 hx).1,
          Subgroup.mul_mem _ (Subgroup.mul_mem _ hkN (mem_normIn.1 hx).2)
            (Subgroup.inv_mem _ hkN)⟩
    have hhinvN : h⁻¹ ∈ Subgroup.normalizer (T₁ : Set G) := Subgroup.inv_mem _ hhN
    have hhinvN' : h⁻¹ ∈ Subgroup.normalizer (T : Set G) := Subgroup.inv_mem _ hhN'
    have hhaT₁ : h * a * h⁻¹ ∈ T₁ := (Subgroup.mem_normalizer_iff.1 hhN a).1 haT₁
    have hhaL : h * a * h⁻¹ ∉ normIn T₁ T := by
      intro hmem
      apply haL
      have h2 := hconjL h⁻¹ hhinvN hhinvN' _ hmem
      rwa [show h⁻¹ * (h * a * h⁻¹) * h⁻¹⁻¹ = a by group] at h2
    have hlamL : (h * a * h⁻¹) * a ∈ normIn T₁ T := by
      rcases ha _ hhaT₁ with h' | h'
      · exact h'
      · exact absurd h' hhaL
    set lam : G := (h * a * h⁻¹) * a with hlam
    have hlamT : lam ∈ T₁ := (normIn_le T₁ T) hlamL
    have hlamsq : lam * lam = 1 := elemAbelian_mul_self hT₁ab hlamT
    have hha : h * a * h⁻¹ = lam * a := by
      rw [hlam]
      calc h * a * h⁻¹ = (h * a * h⁻¹) * (a * a) := by rw [haa, mul_one]
        _ = (h * a * h⁻¹) * a * a := by group
    have hhc : h * c * h⁻¹ = c := by
      have : c * h = h * c := (Subgroup.mem_centralizer_iff.1 hcC h hh).symm
      calc h * c * h⁻¹ = c * h * h⁻¹ := by rw [this]
        _ = c := by group
    have hclam : c * lam * c⁻¹ = lam := by
      have := hcL lam hlamL
      calc c * lam * c⁻¹ = lam * c * c⁻¹ := by rw [this]
        _ = lam := by group
    have hulam : u * lam = lam * u := elemAbelian_mul_comm hT₁ab huT₁ hlamT
    calc h * (u * a) * h⁻¹ = (h * c * h⁻¹) * (h * a * h⁻¹) * (h * c * h⁻¹)⁻¹ *
          (h * a * h⁻¹) := by rw [hu]; group
      _ = c * (lam * a) * c⁻¹ * (lam * a) := by rw [hhc, hha]
      _ = (c * lam * c⁻¹) * (c * a * c⁻¹) * (lam * a) := by group
      _ = lam * u * (lam * a) := by rw [hclam, hu]
      _ = (u * lam) * lam * a := by rw [hulam]; group
      _ = u * (lam * lam) * a := by group
      _ = u * a := by rw [hlamsq, mul_one]
  have hℓ1 : u * a = 1 :=
    eq_one_of_fixed_T₁ h1 h62 h63 hc hnat ch hn hℓL hfix
  have hua : u = a := by
    have : u = (u * a) * a := by rw [mul_assoc, haa, mul_one]
    rw [this, hℓ1, one_mul]
  have hca : c * a = a * c := by
    have : c * a * c⁻¹ = a := by rw [← hu, hua]
    calc c * a = (c * a * c⁻¹) * c := by group
      _ = a * c := by rw [this]
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  show z * c = c * z
  rcases ha z hz with h | h
  · have hzaL : z * a ∈ normIn T₁ T := h
    have hcz : c * (z * a) = (z * a) * c := hcL _ hzaL
    have hz' : z = (z * a) * a := by rw [mul_assoc, haa, mul_one]
    calc z * c = (z * a * a) * c := by rw [← hz']
      _ = (z * a) * (a * c) := by rw [mul_assoc (z * a) a c]
      _ = (z * a) * (c * a) := by rw [← hca]
      _ = ((z * a) * c) * a := by rw [← mul_assoc]
      _ = (c * (z * a)) * a := by rw [← hcz]
      _ = c * ((z * a) * a) := by rw [mul_assoc]
      _ = c * z := by rw [← hz']
  · exact (hcL z h).symm

theorem centralizer_hSub_le_centralizer_sup (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ n 1) (hnat : NaturalSL T (hSub T (normIn T₁ T)) n 1) {k : ℕ}
    (ch : TransvChain n k) (hn : 3 ≤ n) {c : G}
    (hcC : c ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G)) :
    c ∈ Subgroup.centralizer ((hSub T (normIn T₁ T) ⊔ T₁ : Subgroup G) : Set G) := by
  have hle : hSub T (normIn T₁ T) ⊔ T₁ ≤ Subgroup.centralizer ({c} : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hcC x hx)
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1
          (centralizer_hSub_le_centralizer_T₁ h1 h62 h63 hc hnat ch hn hcC) x hx)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)

end Fix

end CFSG.CGT.T75Q
