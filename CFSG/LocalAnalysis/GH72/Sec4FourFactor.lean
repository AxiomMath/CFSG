module

public import CFSG.LocalAnalysis.GH72.Sec4FourBasic
import CFSG.LocalAnalysis.GH72.Alignment
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.LocalAnalysis.GH72.DDLocal
public import CFSG.LocalAnalysis.GH72.GWTwoExtension
public import CFSG.LocalAnalysis.GH72.RelativeZJAmbient
public import CFSG.LocalAnalysis.GH72.Sec4Bar

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools
open CFSG.GorensteinWalter (twoResidualOf)
open CFSG.CGT.Foote81L6 (mem_sup_iff_of_le_normalizer le_normalizer_of_comm
  card_sup_of_le_normalizer)
open CFSG.CGT.Foote81L6.TStruct (IsFourIn comm_of_mul_self)

section Factor

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem IsAStarFactor.isL2OrA7_or {L : Subgroup Y} (h : IsAStarFactor L) :
    IsL2OrA7 L 5 ∨ IsKleinFour L := by
  rcases h with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem two_dvd_card_of_isL2OrA7 {L : Type*} [Group L] [Finite L] (h : IsL2OrA7 L 5) :
    2 ∣ Nat.card L := by
  by_contra h2
  have hodd : Odd (Nat.card L) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h2)
  have := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hne : (⊤ : Subgroup L) ≠ ⊥ := by
    intro hb
    have h60 := sixty_le_card_of_isL2OrA7 le_rfl h
    rw [← card_top (G := L), hb, card_bot] at h60
    omega
  have hlt := Group.IsSolvable.commutator_lt_of_ne_bot hne
  rw [← _root_.commutator_def, commutator_eq_top_of_isL2OrA7 le_rfl h] at hlt
  exact lt_irrefl _ hlt

theorem oddCore_eq_bot_of_isAStarFactor {L : Subgroup Y} (h : IsAStarFactor L) :
    CFSG.oddCore L = ⊥ := by
  rcases h.isL2OrA7_or with h | h
  · have := isSimpleGroup_of_isL2OrA7 le_rfl h
    exact oddCore_eq_bot_of_isSimpleGroup (two_dvd_card_of_isL2OrA7 h)
  · have := h
    apply Subgroup.eq_bot_of_card_eq
    have hdvd : Nat.card (CFSG.oddCore L) ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = Nat.card L by rw [IsKleinFour.card_four]; norm_num]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hodd : Odd (Nat.card (CFSG.oddCore L)) := odd_card_oddCore
    rcases j with _ | j
    · simpa using hj
    · rw [hj] at hodd
      exact absurd hodd (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, j.succ_ne_zero⟩))

theorem le_of_isKleinFour_of_isSylowOf {T F : Subgroup Y} (hV : IsKleinFour F)
    (h : IsSylowOf 2 (T ⊓ F) F) : F ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hV
  have hp : IsPGroup 2 F := IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
  exact (h.eq_of_le inf_le_right le_rfl hp).le.trans inf_le_left

omit [Finite Y] in
theorem mem_of_pow_mem_of_pow_mem {H : Subgroup Y} {x : Y} {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : x ^ a ∈ H) (hb : x ^ b ∈ H) : x ∈ H := by
  have h1 : ((Nat.gcd a b : ℕ) : ℤ) = a * Nat.gcdA a b + b * Nat.gcdB a b := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one, Nat.cast_one] at h1
  have e : x = (x ^ a) ^ Nat.gcdA a b * (x ^ b) ^ Nat.gcdB a b := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h1, zpow_one]
  rw [e]
  exact mul_mem (zpow_mem ha _) (zpow_mem hb _)

omit [Finite Y] in
theorem le_centralizer_of_le_normalizer_of_inf_eq_bot {K F₁ F₂ : Subgroup Y} (h₁ : F₁ ≤ K)
    (h₂ : F₂ ≤ K) (hn₁ : K ≤ normalizer (F₁ : Set Y)) (hn₂ : K ≤ normalizer (F₂ : Set Y))
    (hi : F₁ ⊓ F₂ = ⊥) : F₁ ≤ centralizer (F₂ : Set Y) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  have hc₂ : x * y * x⁻¹ * y⁻¹ ∈ F₂ :=
    mul_mem ((mem_normalizer_iff.1 (hn₂ (h₁ hx)) y).1 hy) (inv_mem hy)
  have hc₁ : x * y * x⁻¹ * y⁻¹ ∈ F₁ := by
    have h := (mem_normalizer_iff.1 (hn₁ (h₂ hy)) x⁻¹).1 (inv_mem hx)
    rw [show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
    exact mul_mem hx h
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ F₁ ⊓ F₂ := mem_inf.2 ⟨hc₁, hc₂⟩
  rw [hi, mem_bot] at h1
  calc y * x = (x * y * x⁻¹ * y⁻¹)⁻¹ * (x * y) := by group
    _ = x * y := by rw [h1, inv_one, one_mul]

theorem le_of_isPGroup_of_odd_relIndex {K F P : Subgroup Y} (hFK : F ≤ K)
    (hFn : K ≤ normalizer (F : Set Y)) (hodd : Odd (F.relIndex K)) (hPK : P ≤ K)
    (hP : IsPGroup 2 P) : P ≤ F := by
  have : (F.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hFK).2 hFn
  have h := CFSG.GorensteinWalter.subgroup_le_of_isPGroup_coindex_odd (F.subgroupOf K)
    inferInstance hodd (P.subgroupOf K) hP.comap_subtype
  intro x hx
  exact h (show (⟨x, hPK hx⟩ : K) ∈ P.subgroupOf K from hx)

omit [Finite Y] in
theorem le_normalizer_sup_of_forall {K B T₁ : Subgroup Y} (hT₁B : T₁ ≤ normalizer (B : Set Y))
    (hD₁ : IsDih T₁) (hB : ∀ k ∈ K, ∀ b ∈ B, k * b * k⁻¹ ∈ B ⊔ T₁)
    (hs : ∀ k ∈ K, ∀ s ∈ T₁, s * s = 1 → k * s * k⁻¹ ∈ B ⊔ T₁) :
    K ≤ normalizer ((B ⊔ T₁ : Subgroup Y) : Set Y) := by
  rw [le_normalizer_iff]
  intro k hk l hl
  obtain ⟨b, hb, s, hsT, rfl⟩ := (mem_sup_iff_of_le_normalizer hT₁B).1 hl
  obtain ⟨a, ha, a', ha', ha2, ha'2, rfl⟩ := hD₁.exists_mul_eq_of_mem hsT
  have e : k * (b * (a * a')) * k⁻¹ = k * b * k⁻¹ * (k * a * k⁻¹) * (k * a' * k⁻¹) := by group
  rw [e]
  exact mul_mem (mul_mem (hB k hk b hb) (hs k hk a ha ha2)) (hs k hk a' ha' ha'2)

omit [Finite Y] in
theorem isPGroup_zpowers_of_mul_self {x : Y} (hx : x * x = 1) : IsPGroup 2 (zpowers x) := by
  rcases (Nat.dvd_prime Nat.prime_two).1
      (orderOf_dvd_of_pow_eq_one (show x ^ 2 = 1 by rw [pow_two]; exact hx)) with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem eq_one_of_conj_eq_mul {T₁ T₂ L : Subgroup Y} (hT₁₂ : T₁ ⊓ T₂ = ⊥)
    (hfus : ∀ x ∈ T₁ ⊔ T₂, ∀ y ∈ T₁ ⊔ T₂, orderOf x = 2 → IsConj x y →
      (x ∈ T₁ ↔ y ∈ T₁) ∧ (x ∈ T₂ ↔ y ∈ T₂))
    (hL : IsSylowOf 2 T₁ L) {c : Y} (hc : c ∈ T₂) (hc2 : c * c = 1) (hLc : L ≤ C c)
    {k s x : Y} (hs : s ∈ T₁) (hs2 : s * s = 1) (hx : x ∈ L) (h : k * s * k⁻¹ = x * c) :
    c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxc : x * c = c * x := mem_centralizer_singleton_iff.1 (hLc hx)
  have hx2 : x * x = 1 := by
    have h1 : k * s * k⁻¹ * (k * s * k⁻¹) = 1 := by
      calc k * s * k⁻¹ * (k * s * k⁻¹) = k * (s * s) * k⁻¹ := by group
        _ = 1 := by rw [hs2]; group
    rw [h] at h1
    calc x * x = x * x * (c * c) := by rw [hc2, mul_one]
      _ = x * (c * x) * c := by rw [← hxc]; group
      _ = x * c * (x * c) := by group
      _ = 1 := h1
  obtain ⟨g, hgL, hgx⟩ := exists_mem_conj_mem_of_isSylowOf hL hx (isPGroup_zpowers_of_mul_self hx2)
  have hgc : g * c = c * g := mem_centralizer_singleton_iff.1 (hLc hgL)
  have hy : g * k * s * (g * k)⁻¹ = g * x * g⁻¹ * c := by
    calc g * k * s * (g * k)⁻¹ = g * (k * s * k⁻¹) * g⁻¹ := by group
      _ = g * x * g⁻¹ * (g * c) * g⁻¹ := by rw [h]; group
      _ = g * x * g⁻¹ * (c * g) * g⁻¹ := by rw [hgc]
      _ = g * x * g⁻¹ * c := by group
  have hyT₁ : g * x * g⁻¹ * c ∈ T₁ := by
    by_cases hs1 : s = 1
    · rw [← hy, hs1, mul_one, mul_inv_cancel]
      exact one_mem _
    · have hs2' : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
      exact ((hfus s (mem_sup_left hs) _ (mul_mem (mem_sup_left hgx) (mem_sup_right hc)) hs2'
        (isConj_iff.2 ⟨g * k, hy⟩)).1).1 hs
  have hcT₁ : c ∈ T₁ := by
    have h1 := mul_mem (inv_mem hgx) hyT₁
    rwa [inv_mul_cancel_left] at h1
  have h1 : c ∈ T₁ ⊓ T₂ := mem_inf.2 ⟨hcT₁, hc⟩
  rwa [hT₁₂, mem_bot] at h1

theorem conj_mem_of_commutator_mem {T₁ T₂ F₂ L : Subgroup Y} (hT₁₂ : T₁ ⊓ T₂ = ⊥)
    (hfus : ∀ x ∈ T₁ ⊔ T₂, ∀ y ∈ T₁ ⊔ T₂, orderOf x = 2 → IsConj x y →
      (x ∈ T₁ ↔ y ∈ T₁) ∧ (x ∈ T₂ ↔ y ∈ T₂))
    (hL : IsSylowOf 2 T₁ L) (hLc : L ≤ centralizer (F₂ : Set Y))
    (hZj : ∀ c ∈ F₂ ⊓ centralizer (F₂ : Set Y), c ∈ T₂ ∧ c * c = 1) {k s : Y} (hs : s ∈ T₁)
    (hs2 : s * s = 1) {l c : Y} (hl : l ∈ L) (hc : c ∈ F₂ ⊓ centralizer (F₂ : Set Y))
    (h : k * s * k⁻¹ * s⁻¹ = l * c) : k * s * k⁻¹ ∈ L := by
  obtain ⟨hcT, hc2⟩ := hZj c hc
  have hLC : L ≤ C c := fun x hx =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hLc hx) c (mem_inf.1 hc).1).symm
  have hsc : s * c = c * s := mem_centralizer_singleton_iff.1 (hLC (hL.le hs))
  have heq : k * s * k⁻¹ = l * s * c := by
    calc k * s * k⁻¹ = k * s * k⁻¹ * s⁻¹ * s := by group
      _ = l * (c * s) := by rw [h, mul_assoc]
      _ = l * s * c := by rw [← hsc, mul_assoc]
  have hc1 := eq_one_of_conj_eq_mul hT₁₂ hfus hL hcT hc2 hLC hs hs2 (mul_mem hl (hL.le hs)) heq
  rw [heq, hc1, mul_one]
  exact mul_mem hl (hL.le hs)

theorem inf_twoResidualOf_le {J T₁ T₂ F₁ F₂ : Subgroup Y}
    (hKJ : twoResidualOf (⊤ : Subgroup Y) ≤ J) (hT : IsSylowOf 2 (T₁ ⊔ T₂) J)
    (hT₁₂ : T₁ ⊓ T₂ = ⊥) (hTc : T₂ ≤ centralizer (T₁ : Set Y))
    (hFK₁ : F₁ ≤ twoResidualOf ⊤) (hFK₂ : F₂ ≤ twoResidualOf ⊤)
    (hFN₁ : twoResidualOf ⊤ ≤ normalizer (F₁ : Set Y))
    (hFN₂ : twoResidualOf ⊤ ≤ normalizer (F₂ : Set Y)) (hF₁₂ : F₁ ⊓ F₂ = ⊥)
    (hFodd : Odd ((F₁ ⊔ F₂).relIndex (twoResidualOf ⊤)))
    (hW₁ : IsSylowOf 2 (T₁ ⊓ F₁) F₁) (hW₂ : IsSylowOf 2 (T₂ ⊓ F₂) F₂) :
    T₁ ⊓ twoResidualOf ⊤ ≤ F₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (twoResidualOf (⊤ : Subgroup Y)).Normal := twoResidualOf_top_normal
  have hTK : IsSylowOf 2 ((T₁ ⊔ T₂) ⊓ twoResidualOf ⊤) (twoResidualOf ⊤) :=
    hT.inf_of_le_normalizer hKJ le_normalizer_of_normal
  have hFK : F₁ ⊔ F₂ ≤ twoResidualOf ⊤ := sup_le hFK₁ hFK₂
  have hTKF : (T₁ ⊔ T₂) ⊓ twoResidualOf ⊤ ≤ F₁ ⊔ F₂ :=
    le_of_isPGroup_of_odd_relIndex hFK (le_normalizer_sup hFN₁ hFN₂) hFodd inf_le_right
      hTK.isPGroup
  have hWc : T₂ ⊓ F₂ ≤ normalizer ((T₁ ⊓ F₁ : Subgroup Y) : Set Y) :=
    le_normalizer_of_comm fun x hx y hy =>
      mem_centralizer_iff.1 (hTc (mem_inf.1 hy).1) x (mem_inf.1 hx).1
  have hWi : (T₁ ⊓ F₁) ⊓ (T₂ ⊓ F₂) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h : x ∈ T₁ ⊓ T₂ :=
      mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 hx).1).1, (mem_inf.1 (mem_inf.1 hx).2).1⟩
    rwa [hT₁₂] at h
  have hWsyl : IsSylowOf 2 ((T₁ ⊓ F₁) ⊔ (T₂ ⊓ F₂)) (F₁ ⊔ F₂) := by
    refine isSylowOf_of_card (sup_le_sup inf_le_right inf_le_right) ?_
    rw [card_sup_of_le_normalizer hWc hWi, hW₁.card_eq, hW₂.card_eq,
      card_sup_of_le_normalizer (hFK₂.trans hFN₁) hF₁₂, ← pow_add,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply]
  have hW : (T₁ ⊔ T₂) ⊓ twoResidualOf ⊤ = (T₁ ⊓ F₁) ⊔ (T₂ ⊓ F₂) :=
    hWsyl.eq_of_le (le_inf (sup_le_sup inf_le_left inf_le_left)
      (sup_le (inf_le_right.trans hFK₁) (inf_le_right.trans hFK₂))) hTKF hTK.isPGroup
  intro x hx
  have hxW : x ∈ (T₁ ⊓ F₁) ⊔ (T₂ ⊓ F₂) := by
    rw [← hW]
    exact mem_inf.2 ⟨mem_sup_left (mem_inf.1 hx).1, (mem_inf.1 hx).2⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hWc).1 hxW
  have hb1 : b = 1 := by
    have hbT₁ : b ∈ T₁ := by
      have h := mul_mem (inv_mem (mem_inf.1 ha).1) (mem_inf.1 hx).1
      rwa [inv_mul_cancel_left] at h
    have h : b ∈ T₁ ⊓ T₂ := mem_inf.2 ⟨hbT₁, (mem_inf.1 hb).1⟩
    rwa [hT₁₂, mem_bot] at h
  rw [hb1, mul_one]
  exact (mem_inf.1 ha).2

theorem le_normalizer_of_isAStarFactor {T₁ T₂ F₁ : Subgroup Y}
    (hTc : T₂ ≤ centralizer (T₁ : Set Y))
    (hFK₁ : F₁ ≤ twoResidualOf ⊤) (hFN₁ : twoResidualOf ⊤ ≤ normalizer (F₁ : Set Y))
    (hA₁ : IsAStarFactor F₁) (hW₁ : IsSylowOf 2 (T₁ ⊓ F₁) F₁)
    (hTK₁ : T₁ ⊓ twoResidualOf ⊤ ≤ F₁) : T₁ ⊔ T₂ ≤ normalizer (F₁ : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKn : (twoResidualOf (⊤ : Subgroup Y)).Normal := twoResidualOf_top_normal
  have hTT₁ : T₁ ⊔ T₂ ≤ normalizer (T₁ : Set Y) :=
    sup_le le_normalizer
      (le_normalizer_of_comm fun x hx y hy => mem_centralizer_iff.1 (hTc hy) x hx)
  have hconj : ∀ t ∈ T₁ ⊔ T₂, ∀ w ∈ T₁ ⊓ F₁, t * w * t⁻¹ ∈ F₁ := fun t ht w hw =>
    hTK₁ (mem_inf.2 ⟨(mem_normalizer_iff.1 (hTT₁ ht) w).1 (mem_inf.1 hw).1,
      hKn.conj_mem w (hFK₁ (mem_inf.1 hw).2) t⟩)
  rw [le_normalizer_iff]
  intro t ht f hf
  rcases hA₁.isL2OrA7_or with hL | hV
  · have := isSimpleGroup_of_isL2OrA7 le_rfl hL
    have hF'N : F₁ ≤ normalizer ((F₁.map (MulAut.conj t).toMonoidHom : Subgroup Y) : Set Y) := by
      rw [le_normalizer_iff]
      rintro g hg _ ⟨a, ha, rfl⟩
      have hg' : t⁻¹ * g * t ∈ twoResidualOf (⊤ : Subgroup Y) := by
        have h := hKn.conj_mem g (hFK₁ hg) t⁻¹
        rwa [inv_inv] at h
      refine ⟨_, (mem_normalizer_iff.1 (hFN₁ hg') a).1 ha, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hN : ((F₁.map (MulAut.conj t).toMonoidHom).subgroupOf F₁).Normal := ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      exact (mem_normalizer_iff.1 (hF'N g.2) n).1 hn⟩
    rcases hN.eq_bot_or_eq_top with hb | htop
    · exfalso
      have h2 := two_dvd_card_of_isL2OrA7 hL
      have hcard : 2 ≤ Nat.card (T₁ ⊓ F₁ : Subgroup Y) := by
        rw [hW₁.card_eq]
        have h1 : 1 ≤ (Nat.card F₁).factorization 2 :=
          (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').1 h2
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (Nat.card F₁).factorization 2 := Nat.pow_le_pow_right (by norm_num) h1
      rcases (T₁ ⊓ F₁).bot_or_exists_ne_one with hbot | ⟨w, hw, hw1⟩
      · rw [hbot, card_bot] at hcard
        omega
      · have h3 : (⟨t * w * t⁻¹, hconj t ht w hw⟩ : F₁) ∈
            (F₁.map (MulAut.conj t).toMonoidHom).subgroupOf F₁ :=
          show t * w * t⁻¹ ∈ F₁.map (MulAut.conj t).toMonoidHom from ⟨w, (mem_inf.1 hw).2, rfl⟩
        rw [hb, mem_bot] at h3
        apply hw1
        have h4 : t * w * t⁻¹ = 1 := congrArg Subtype.val h3
        calc w = t⁻¹ * (t * w * t⁻¹) * t := by group
          _ = 1 := by rw [h4]; group
    · have hle : F₁ ≤ F₁.map (MulAut.conj t).toMonoidHom := fun x hx => by
        have h : (⟨x, hx⟩ : F₁) ∈ (F₁.map (MulAut.conj t).toMonoidHom).subgroupOf F₁ :=
          htop ▸ mem_top _
        exact h
      have heq : F₁ = F₁.map (MulAut.conj t).toMonoidHom :=
        eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj t).injective])
      rw [heq]
      exact ⟨f, hf, rfl⟩
  · exact hconj t ht f (mem_inf.2 ⟨le_of_isKleinFour_of_isSylowOf hV hW₁ hf, hf⟩)

theorem le_centralizer_of_fusion {J T₁ T₂ F₁ : Subgroup Y} (hT : IsSylowOf 2 (T₁ ⊔ T₂) J)
    (hT₁₂ : T₁ ⊓ T₂ = ⊥) (hTc : T₂ ≤ centralizer (T₁ : Set Y)) (hD₂ : IsDih T₂)
    (hfus : ∀ x ∈ T₁ ⊔ T₂, ∀ y ∈ T₁ ⊔ T₂, orderOf x = 2 → IsConj x y →
      (x ∈ T₁ ↔ y ∈ T₁) ∧ (x ∈ T₂ ↔ y ∈ T₂))
    (hTN : T₁ ⊔ T₂ ≤ normalizer (F₁ : Set Y)) (hOF : CFSG.oddCore F₁ = ⊥)
    (hW₁ : IsSylowOf 2 (T₁ ⊓ F₁) F₁) : T₂ ≤ centralizer (F₁ : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 (T₁ ⊔ T₂ : Subgroup Y) := hT.isPGroup
  have hTF : (T₁ ⊔ T₂) ⊓ F₁ = T₁ ⊓ F₁ :=
    hW₁.eq_of_le (inf_le_inf_right _ le_sup_left) inf_le_right (hTp.to_le inf_le_left)
  apply hD₂.le_of_forall_involution
  intro t htT ht2
  have htT' : t ∈ T₁ ⊔ T₂ := mem_sup_right htT
  have hzN : zpowers t ≤ normalizer ((T₁ ⊓ F₁ : Subgroup Y) : Set Y) :=
    le_normalizer_of_comm fun x hx y hy => by
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hy
      exact Commute.zpow_right (mem_centralizer_iff.1 (hTc htT) x (mem_inf.1 hx).1) n
  have hRT : (T₁ ⊓ F₁) ⊔ zpowers t ≤ T₁ ⊔ T₂ :=
    sup_le (inf_le_left.trans le_sup_left) ((zpowers_le.2 htT).trans le_sup_right)
  have hRF : ((T₁ ⊓ F₁) ⊔ zpowers t) ⊓ F₁ = T₁ ⊓ F₁ :=
    le_antisymm ((inf_le_inf_right _ hRT).trans hTF.le) (le_inf le_sup_left inf_le_right)
  have hRsyl : IsSylowOf 2 ((T₁ ⊓ F₁) ⊔ zpowers t) (F₁ ⊔ ((T₁ ⊓ F₁) ⊔ zpowers t)) :=
    isSylowOf_sup_of_le_normalizer (hRT.trans hTN) (hTp.to_le hRT) (by rw [hRF]; exact hW₁)
  rw [← sup_assoc, sup_eq_left.2 (inf_le_right : T₁ ⊓ F₁ ≤ F₁)] at hRsyl
  have hiso : IsIsolatedIn (F₁ ⊔ zpowers t) t := by
    refine isIsolatedIn_of_forall_conj_mem hRsyl (mem_sup_right (mem_zpowers t)) ht2 ?_
    intro k _ hkR
    have hyT₂ : k * t * k⁻¹ ∈ T₂ :=
      ((hfus t htT' _ (hRT hkR) ht2 (isConj_iff.2 ⟨k, rfl⟩)).2).1 htT
    obtain ⟨w, hw, z, hz, hwz⟩ := (mem_sup_iff_of_le_normalizer hzN).1 hkR
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hz
    have hw1 : w = 1 := by
      have hwT₂ : w ∈ T₂ := by
        have h := mul_mem hyT₂ (inv_mem (zpow_mem htT n))
        rwa [hwz, mul_inv_cancel_right] at h
      have h : w ∈ T₁ ⊓ T₂ := mem_inf.2 ⟨(mem_inf.1 hw).1, hwT₂⟩
      rwa [hT₁₂, mem_bot] at h
    rw [hw1, one_mul] at hwz
    have h2 : ((orderOf t : ℕ) : ℤ) = 2 := by rw [ht2]; norm_num
    have key : t ^ n = t ^ (n % 2) := by rw [← h2, zpow_mod_orderOf]
    rcases Int.emod_two_eq_zero_or_one n with h0 | h1
    · exfalso
      rw [key, h0, zpow_zero] at hwz
      have h := orderOf_conj_eq k t
      rw [hwz, orderOf_one, ht2] at h
      norm_num at h
    · rw [hwz, key, h1, zpow_one]
  have hC := le_centralizer_of_isIsolatedIn (hTN htT') hiso hOF
  rw [mem_centralizer_iff]
  intro f hf
  exact mem_centralizer_singleton_iff.1 (hC hf)

theorem isPGroup_inf_centralizer (hO : CFSG.oddCore Y = ⊥) {J T F₁ F₂ : Subgroup Y}
    (hKJ : twoResidualOf (⊤ : Subgroup Y) ≤ J) (hT : IsSylowOf 2 T J)
    (hJN₁ : J ≤ normalizer (F₁ : Set Y)) (hJN₂ : J ≤ normalizer (F₂ : Set Y))
    (hFK₁ : F₁ ≤ twoResidualOf ⊤) (hFK₂ : F₂ ≤ twoResidualOf ⊤)
    (hFN₁ : twoResidualOf ⊤ ≤ normalizer (F₁ : Set Y))
    (hFN₂ : twoResidualOf ⊤ ≤ normalizer (F₂ : Set Y))
    (hFodd : Odd ((F₁ ⊔ F₂).relIndex (twoResidualOf ⊤))) :
    IsPGroup 2 (twoResidualOf ⊤ ⊓ centralizer (F₁ : Set Y) ⊓ centralizer (F₂ : Set Y) :
      Subgroup Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (twoResidualOf (⊤ : Subgroup Y)).Normal := twoResidualOf_top_normal
  have hZJ : twoResidualOf ⊤ ⊓ centralizer (F₁ : Set Y) ⊓ centralizer (F₂ : Set Y) ≤ J :=
    inf_le_left.trans (inf_le_left.trans hKJ)
  have hJZ : J ≤ normalizer ((twoResidualOf ⊤ ⊓ centralizer (F₁ : Set Y) ⊓
      centralizer (F₂ : Set Y) : Subgroup Y) : Set Y) := fun g hg =>
    mem_normalizer_inf_of_mem (mem_normalizer_inf_of_mem ((le_normalizer_of_normal : J ≤ _) hg)
      (mem_normalizer_centralizer_of_mem (hJN₁ hg))) (mem_normalizer_centralizer_of_mem (hJN₂ hg))
  have hP := hT.inf_of_le_normalizer hZJ hJZ
  have hPF : T ⊓ (twoResidualOf ⊤ ⊓ centralizer (F₁ : Set Y) ⊓ centralizer (F₂ : Set Y)) ≤
      F₁ ⊔ F₂ :=
    le_of_isPGroup_of_odd_relIndex (sup_le hFK₁ hFK₂) (le_normalizer_sup hFN₁ hFN₂) hFodd
      (inf_le_right.trans (inf_le_left.trans inf_le_left)) hP.isPGroup
  exact isPGroup_of_isSylowOf_le_centralizer hO hKJ hJZ hP (hPF.trans (sup_le
    (le_centralizer_iff.1 (inf_le_left.trans inf_le_right)) (le_centralizer_iff.1 inf_le_right)))

theorem exists_mul_of_mem_inf_centralizer {F₁ F₂ : Subgroup Y}
    (hFK₁ : F₁ ≤ twoResidualOf ⊤) (hFK₂ : F₂ ≤ twoResidualOf ⊤)
    (hFN₁ : twoResidualOf ⊤ ≤ normalizer (F₁ : Set Y))
    (hFN₂ : twoResidualOf ⊤ ≤ normalizer (F₂ : Set Y))
    (hFodd : Odd ((F₁ ⊔ F₂).relIndex (twoResidualOf ⊤)))
    (hF₁₂c : F₁ ≤ centralizer (F₂ : Set Y))
    (hZ : IsPGroup 2 (twoResidualOf ⊤ ⊓ centralizer (F₁ : Set Y) ⊓ centralizer (F₂ : Set Y) :
      Subgroup Y))
    {z : Y} (hz : z ∈ twoResidualOf ⊤ ⊓ centralizer (F₁ : Set Y) ⊓ centralizer (F₂ : Set Y)) :
    ∃ f ∈ F₁, ∃ c ∈ F₂ ⊓ centralizer (F₂ : Set Y), z = f * c := by
  have hzF : z ∈ F₁ ⊔ F₂ :=
    le_of_isPGroup_of_odd_relIndex (sup_le hFK₁ hFK₂) (le_normalizer_sup hFN₁ hFN₂) hFodd
      ((zpowers_le.2 hz).trans (inf_le_left.trans inf_le_left)) (hZ.to_le (zpowers_le.2 hz))
      (mem_zpowers z)
  obtain ⟨f, hf, c, hc, rfl⟩ := (mem_sup_iff_of_le_normalizer (hFK₂.trans hFN₁)).1 hzF
  refine ⟨f, hf, c, mem_inf.2 ⟨hc, ?_⟩, rfl⟩
  have h := mul_mem (inv_mem (hF₁₂c hf)) (mem_inf.1 hz).2
  rwa [inv_mul_cancel_left] at h

theorem mem_and_mul_self_of_mem_inf_centralizer {T F : Subgroup Y} (hA : IsAStarFactor F)
    (hW : IsSylowOf 2 (T ⊓ F) F) {c : Y} (hc : c ∈ F ⊓ centralizer (F : Set Y)) :
    c ∈ T ∧ c * c = 1 := by
  rcases hA.isL2OrA7_or with hL | hV
  · rw [inf_centralizer_eq_bot_of_isL2OrA7 F hL, mem_bot] at hc
    rw [hc]
    exact ⟨one_mem _, mul_one 1⟩
  · have := hV
    exact ⟨le_of_isKleinFour_of_isSylowOf hV hW (mem_inf.1 hc).1,
      congrArg Subtype.val (IsKleinFour.mul_self (⟨c, (mem_inf.1 hc).1⟩ : F))⟩

theorem exists_factor_of_isL2OrA7
    {J T₁ T₂ F₁ F₂ : Subgroup Y} (hKJ : twoResidualOf (⊤ : Subgroup Y) ≤ J)
    (hT : IsSylowOf 2 (T₁ ⊔ T₂) J) (hT₁₂ : T₁ ⊓ T₂ = ⊥) (hTc : T₂ ≤ centralizer (T₁ : Set Y))
    (hD₁ : IsDih T₁)
    (hfus : ∀ x ∈ T₁ ⊔ T₂, ∀ y ∈ T₁ ⊔ T₂, orderOf x = 2 → IsConj x y →
      (x ∈ T₁ ↔ y ∈ T₁) ∧ (x ∈ T₂ ↔ y ∈ T₂))
    (hFK₁ : F₁ ≤ twoResidualOf ⊤) (hJN₁ : J ≤ normalizer (F₁ : Set Y)) (hL₁ : IsL2OrA7 F₁ 5)
    (hW₁ : IsSylowOf 2 (T₁ ⊓ F₁) F₁) (hJN₂ : J ≤ normalizer (F₂ : Set Y))
    (hF₁₂c : F₁ ≤ centralizer (F₂ : Set Y)) (hT₁C : T₁ ≤ centralizer (F₂ : Set Y))
    (hZdec : ∀ z ∈ twoResidualOf ⊤ ⊓ centralizer (F₁ : Set Y) ⊓ centralizer (F₂ : Set Y),
      ∃ f ∈ F₁, ∃ c ∈ F₂ ⊓ centralizer (F₂ : Set Y), z = f * c)
    (hZj : ∀ c ∈ F₂ ⊓ centralizer (F₂ : Set Y), c ∈ T₂ ∧ c * c = 1) :
    ∃ L : Subgroup Y, T₁ ≤ L ∧ L ≤ J ∧ J ≤ normalizer (L : Set Y) ∧ IsSylowOf 2 T₁ L ∧
      IsL2PGL2OrA7OrV4 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKn : (twoResidualOf (⊤ : Subgroup Y)).Normal := twoResidualOf_top_normal
  have hT₁J : T₁ ≤ J := le_sup_left.trans hT.le
  have hT₁p : IsPGroup 2 T₁ := hT.isPGroup.to_le le_sup_left
  have hT₁N : T₁ ≤ normalizer (F₁ : Set Y) := hT₁J.trans hJN₁
  have hLsyl : IsSylowOf 2 T₁ (F₁ ⊔ T₁) := isSylowOf_sup_of_le_normalizer hT₁N hT₁p hW₁
  have hLc : F₁ ⊔ T₁ ≤ centralizer (F₂ : Set Y) := sup_le hF₁₂c hT₁C
  have hJL : J ≤ normalizer ((F₁ ⊔ T₁ : Subgroup Y) : Set Y) := by
    refine (le_sup_twoResidualOf_of_isSylowOf hT).trans (sup_le ?_ ?_)
    · exact le_normalizer_sup (hT.le.trans hJN₁) (sup_le le_normalizer
        (le_normalizer_of_comm fun x hx y hy => mem_centralizer_iff.1 (hTc hy) x hx))
    · refine le_normalizer_sup_of_forall hT₁N hD₁
        (fun k hk b hb => mem_sup_left ((mem_normalizer_iff.1 (hJN₁ (hKJ hk)) b).1 hb)) ?_
      intro k hk s hs hs2
      have hcomm := commutator_le_sup_inf_centralizer_of_isL2OrA7 (hFK₁.trans hKJ) hJN₁ hL₁
          (commutator_mem_commutator (hKJ hk) (hT₁J hs))
      rw [commutatorElement_def] at hcomm
      obtain ⟨f, hf, c', hc', hfc⟩ :=
        (mem_sup_iff_of_le_normalizer (inf_le_left.trans hJN₁)).1 hcomm
      have hcK : k * s * k⁻¹ * s⁻¹ ∈ twoResidualOf (⊤ : Subgroup Y) := by
        have h := mul_mem hk (hKn.conj_mem k⁻¹ (inv_mem hk) s)
        rwa [show k * (s * k⁻¹ * s⁻¹) = k * s * k⁻¹ * s⁻¹ by group] at h
      have hcC₂ : k * s * k⁻¹ * s⁻¹ ∈ centralizer (F₂ : Set Y) :=
        mul_mem ((mem_normalizer_iff.1 (mem_normalizer_centralizer_of_mem (hJN₂ (hKJ hk))) s).1
          (hT₁C hs)) (inv_mem (hT₁C hs))
      have e : c' = f⁻¹ * (k * s * k⁻¹ * s⁻¹) := by rw [hfc]; group
      have hc'Z : c' ∈ twoResidualOf ⊤ ⊓ centralizer (F₁ : Set Y) ⊓ centralizer (F₂ : Set Y) :=
        mem_inf.2 ⟨mem_inf.2 ⟨by rw [e]; exact mul_mem (inv_mem (hFK₁ hf)) hcK,
          (mem_inf.1 hc').2⟩, by rw [e]; exact mul_mem (inv_mem (hF₁₂c hf)) hcC₂⟩
      obtain ⟨f₁, hf₁, c, hc, rfl⟩ := hZdec c' hc'Z
      exact conj_mem_of_commutator_mem hT₁₂ hfus hLsyl hLc hZj hs hs2
        (mem_sup_left (mul_mem hf hf₁)) hc (by rw [hfc, mul_assoc])
  have hLN : F₁ ⊔ T₁ ≤ normalizer (F₁ : Set Y) := sup_le le_normalizer hT₁N
  have : (F₁.subgroupOf (F₁ ⊔ T₁)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).2 hLN
  have hF : IsL2OrA7 (F₁.subgroupOf (F₁ ⊔ T₁)) 5 :=
    isL2OrA7_of_mulEquiv (subgroupOfEquivOfLe le_sup_left) hL₁
  have h2 : IsPGroup 2 (↥(F₁ ⊔ T₁) ⧸ F₁.subgroupOf (F₁ ⊔ T₁)) := by
    intro q
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨f, hf, s, hs, rfl⟩ := (mem_sup_iff_of_le_normalizer hT₁N).1 hl
    have e : (QuotientGroup.mk ⟨f * s, hl⟩ : ↥(F₁ ⊔ T₁) ⧸ F₁.subgroupOf (F₁ ⊔ T₁)) =
        QuotientGroup.mk ⟨s, mem_sup_right hs⟩ := by
      rw [QuotientGroup.eq, mem_subgroupOf]
      show (f * s)⁻¹ * s ∈ F₁
      have h := (mem_normalizer_iff.1 (inv_mem (hT₁N hs)) f⁻¹).1 (inv_mem hf)
      rwa [inv_inv, show s⁻¹ * f⁻¹ * s = (f * s)⁻¹ * s by group] at h
    rw [e]
    obtain ⟨n, hn⟩ := hT₁p ⟨s, hs⟩
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow]
    have h1 : (⟨s, mem_sup_right hs⟩ : ↥(F₁ ⊔ T₁)) ^ 2 ^ n = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hn)
    rw [h1, QuotientGroup.mk_one]
  exact ⟨F₁ ⊔ T₁, le_sup_right, sup_le (hFK₁.trans hKJ) hT₁J, hJL, hLsyl,
    gw_isL2PGL2OrA7OrV4_of_isPGroup_quotient (F₁.subgroupOf (F₁ ⊔ T₁)) hF h2
      (hasDihedralSylowTwo_of_isSylowOf hLsyl hD₁)⟩

theorem exists_factor_of_four
    (hO : CFSG.oddCore Y = ⊥) {J T₁ T₂ F₁ F₂ : Subgroup Y}
    (hKJ : twoResidualOf (⊤ : Subgroup Y) ≤ J) (hT : IsSylowOf 2 (T₁ ⊔ T₂) J)
    (hT₁₂ : T₁ ⊓ T₂ = ⊥) (hTc : T₂ ≤ centralizer (T₁ : Set Y)) (hD₁ : IsDih T₁)
    (hfus : ∀ x ∈ T₁ ⊔ T₂, ∀ y ∈ T₁ ⊔ T₂, orderOf x = 2 → IsConj x y →
      (x ∈ T₁ ↔ y ∈ T₁) ∧ (x ∈ T₂ ↔ y ∈ T₂))
    (hFK₁ : F₁ ≤ twoResidualOf ⊤) (hJN₁ : J ≤ normalizer (F₁ : Set Y)) (hV : IsKleinFour F₁)
    (hW₁ : IsSylowOf 2 (T₁ ⊓ F₁) F₁) (hTK : ¬ T₁ ≤ twoResidualOf ⊤)
    (hJN₂ : J ≤ normalizer (F₂ : Set Y)) (hF₁₂ : F₁ ⊓ F₂ = ⊥)
    (hF₁₂c : F₁ ≤ centralizer (F₂ : Set Y)) (hT₁C : T₁ ≤ centralizer (F₂ : Set Y))
    (hZ : IsPGroup 2 (twoResidualOf ⊤ ⊓ centralizer (F₁ : Set Y) ⊓ centralizer (F₂ : Set Y) :
      Subgroup Y))
    (hZdec : ∀ z ∈ twoResidualOf ⊤ ⊓ centralizer (F₁ : Set Y) ⊓ centralizer (F₂ : Set Y),
      ∃ f ∈ F₁, ∃ c ∈ F₂ ⊓ centralizer (F₂ : Set Y), z = f * c)
    (hZj : ∀ c ∈ F₂ ⊓ centralizer (F₂ : Set Y), c ∈ T₂ ∧ c * c = 1)
    (hNI : ∀ x ∈ twoResidualOf ⊤ ⊓ centralizer (twoResidualOf (⊤ : Subgroup Y) : Set Y),
      x * x = 1 → x = 1) :
    ∃ L : Subgroup Y, T₁ ≤ L ∧ L ≤ J ∧ J ≤ normalizer (L : Set Y) ∧ IsSylowOf 2 T₁ L ∧
      IsL2PGL2OrA7OrV4 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKn : (twoResidualOf (⊤ : Subgroup Y)).Normal := twoResidualOf_top_normal
  have := hV
  have hT₁J : T₁ ≤ J := le_sup_left.trans hT.le
  have hT₁p : IsPGroup 2 T₁ := hT.isPGroup.to_le le_sup_left
  have hKN : twoResidualOf ⊤ ≤ normalizer (F₁ : Set Y) := hKJ.trans hJN₁
  have hF₁T₁ : F₁ ≤ T₁ := le_of_isKleinFour_of_isSylowOf hV hW₁
  have hF₁2 : ∀ x ∈ F₁, x * x = 1 := fun x hx =>
    congrArg Subtype.val (IsKleinFour.mul_self (⟨x, hx⟩ : F₁))
  have hF₁c : F₁ ≤ centralizer (F₁ : Set Y) := fun x hx =>
    mem_centralizer_iff.2 fun y hy => comm_of_mul_self hF₁2 hy hx
  have hfour : IsFourIn T₁ F₁ := ⟨hF₁T₁, hF₁2, IsKleinFour.card_four (G := ↥F₁)⟩
  have hCT : T₁ ⊓ centralizer (F₁ : Set Y) = F₁ := hD₁.inf_centralizer_four hfour
  have hF₂₁c : F₂ ≤ centralizer (F₁ : Set Y) := le_centralizer_iff.1 hF₁₂c
  have hcomm : ∀ k ∈ twoResidualOf (⊤ : Subgroup Y), ∀ s ∈ T₁,
      k * s * k⁻¹ * s⁻¹ ∈ twoResidualOf ⊤ ⊓ centralizer (F₂ : Set Y) := fun k hk s hs =>
    mem_inf.2 ⟨by
        have h := mul_mem hk (hKn.conj_mem k⁻¹ (inv_mem hk) s)
        rwa [show k * (s * k⁻¹ * s⁻¹) = k * s * k⁻¹ * s⁻¹ by group] at h,
      mul_mem ((mem_normalizer_iff.1 (mem_normalizer_centralizer_of_mem (hJN₂ (hKJ hk))) s).1
        (hT₁C hs)) (inv_mem (hT₁C hs))⟩
  obtain ⟨u, huK, hu1⟩ : ∃ u ∈ twoResidualOf (⊤ : Subgroup Y), u ∉ centralizer (F₁ : Set Y) := by
    by_contra h
    push Not at h
    have hFC : F₁ ≤ centralizer (twoResidualOf (⊤ : Subgroup Y) : Set Y) :=
      le_centralizer_iff.1 fun u hu => h u hu
    rcases F₁.bot_or_exists_ne_one with hb | ⟨f, hf, hf1⟩
    · have h4 := IsKleinFour.card_four (G := ↥F₁)
      rw [hb, card_bot] at h4
      omega
    · exact hf1 (hNI f (mem_inf.2 ⟨hFK₁ hf, hFC hf⟩) (hF₁2 f hf))
  obtain ⟨τ, hτT, hτK⟩ := SetLike.not_le_iff_exists.1 hTK
  have hτ1 : τ ∉ centralizer (F₁ : Set Y) := fun h => hτK (hFK₁ (by
    rw [← hCT]
    exact mem_inf.2 ⟨hτT, h⟩))
  have hτN : τ ∈ normalizer (F₁ : Set Y) := hJN₁ (hT₁J hτT)
  obtain ⟨n, hn⟩ := hT₁p ⟨τ, hτT⟩
  have hτ2 : τ ^ 2 ∈ centralizer (F₁ : Set Y) :=
    sq_mem_centralizer_of_pow_eq_one hτN (n := n) (by simpa using congrArg Subtype.val hn)
  have hw1 : u * τ * u⁻¹ * τ⁻¹ ∉ centralizer (F₁ : Set Y) :=
    commutator_not_mem_centralizer (hKN huK) hτN (pow_three_mem_centralizer hKN huK) hu1 hτ2 hτ1
  have hwKC := hcomm u huK τ hτT
  obtain ⟨m, hm⟩ := exists_odd_orderOf_pow (u * τ * u⁻¹ * τ⁻¹)
  set v := (u * τ * u⁻¹ * τ⁻¹) ^ 2 ^ m with hv
  have hvKC : v ∈ twoResidualOf ⊤ ⊓ centralizer (F₂ : Set Y) := pow_mem hwKC _
  have hvK : v ∈ twoResidualOf (⊤ : Subgroup Y) := (mem_inf.1 hvKC).1
  have hvC₂ : v ∈ centralizer (F₂ : Set Y) := (mem_inf.1 hvKC).2
  have hvN : v ∈ normalizer (F₁ : Set Y) := hKN hvK
  have hv3 : v ^ 3 ∈ centralizer (F₁ : Set Y) := pow_three_mem_centralizer hKN hvK
  have hv1 : v ∉ centralizer (F₁ : Set Y) := fun h => hw1 (mem_of_pow_mem_of_pow_mem
    (Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 3 2))
    (pow_three_mem_centralizer hKN (mem_inf.1 hwKC).1) h)
  have hV0 : ∀ y ∈ zpowers v, y ∈ centralizer (F₁ : Set Y) → y = 1 := by
    intro y hy hyC
    have hyKC : y ∈ twoResidualOf ⊤ ⊓ centralizer (F₂ : Set Y) := (zpowers_le.2 hvKC) hy
    exact eq_one_of_mem_of_isPGroup_of_odd hZ (by rw [Nat.card_zpowers]; exact hm)
      (mem_inf.2 ⟨mem_inf.2 ⟨(mem_inf.1 hyKC).1, hyC⟩, (mem_inf.1 hyKC).2⟩) hy
  have hvo : orderOf v = 3 := by
    have h := orderOf_dvd_of_pow_eq_one (hV0 _ (pow_mem (mem_zpowers v) 3) hv3)
    rcases (Nat.dvd_prime Nat.prime_three).1 h with h1 | h3
    · exact absurd (by rw [orderOf_eq_one_iff.1 h1]; exact one_mem _) hv1
    · exact h3
  have hdec : ∀ x ∈ twoResidualOf ⊤ ⊓ centralizer (F₂ : Set Y), ∃ e : ℕ, ∃ f ∈ F₁,
      ∃ c ∈ F₂ ⊓ centralizer (F₂ : Set Y), x = f * c * v ^ e := by
    intro x hx
    obtain ⟨hxK, hxC⟩ := mem_inf.1 hx
    obtain ⟨e, he⟩ := exists_mul_inv_pow_mem_centralizer hvN (hKN hxK) hv3 hv1
      (pow_three_mem_centralizer hKN hxK)
    obtain ⟨f, hf, c, hc, hfc⟩ := hZdec _ (mem_inf.2 ⟨mem_inf.2 ⟨mul_mem hxK
      (inv_mem (pow_mem hvK e)), he⟩, mul_mem hxC (inv_mem (pow_mem hvC₂ e))⟩)
    exact ⟨e, f, hf, c, hc, by rw [← hfc]; group⟩
  have hzN : zpowers v ≤ normalizer (F₁ : Set Y) := zpowers_le.2 hvN
  have hBK : F₁ ⊔ zpowers v ≤ twoResidualOf ⊤ := sup_le hFK₁ (zpowers_le.2 hvK)
  have hBC₂ : F₁ ⊔ zpowers v ≤ centralizer (F₂ : Set Y) := sup_le hF₁₂c (zpowers_le.2 hvC₂)
  have hB2 : ∀ y ∈ F₁ ⊔ zpowers v, ∀ k : ℕ, y ^ 2 ^ k = 1 → y ∈ F₁ := by
    intro y hy k hyk
    obtain ⟨f, hf, z, hz, rfl⟩ := (mem_sup_iff_of_le_normalizer hzN).1 hy
    have hyC : f * z ∈ centralizer (F₁ : Set Y) :=
      mem_of_pow_mem_of_pow_mem (by norm_num : Nat.Coprime 2 3)
        (sq_mem_centralizer_of_pow_eq_one (hKN (hBK hy)) hyk)
        (pow_three_mem_centralizer hKN (hBK hy))
    have hzC : z ∈ centralizer (F₁ : Set Y) := by
      have h := mul_mem (inv_mem (hF₁c hf)) hyC
      rwa [inv_mul_cancel_left] at h
    rw [hV0 z hz hzC, mul_one]
    exact hf
  have hBF₂ : ∀ y ∈ F₁ ⊔ zpowers v, y ∈ F₂ → y = 1 := by
    intro y hy hyF
    obtain ⟨f, hf, z, hz, rfl⟩ := (mem_sup_iff_of_le_normalizer hzN).1 hy
    have hzC : z ∈ centralizer (F₁ : Set Y) := by
      have h := mul_mem (inv_mem (hF₁c hf)) (hF₂₁c hyF)
      rwa [inv_mul_cancel_left] at h
    rw [hV0 z hz hzC, mul_one] at hyF ⊢
    have h : f ∈ F₁ ⊓ F₂ := mem_inf.2 ⟨hf, hyF⟩
    rwa [hF₁₂, mem_bot] at h
  have hodd : ∀ x ∈ twoResidualOf ⊤ ⊓ centralizer (F₂ : Set Y), Odd (orderOf x) →
      x ∈ F₁ ⊔ zpowers v := by
    intro x hx hxo
    obtain ⟨e, f, hf, c, hc, rfl⟩ := hdec x hx
    have hcv : c * v ^ e = v ^ e * c :=
      mem_centralizer_iff.1 (pow_mem hvC₂ e) c (mem_inf.1 hc).1
    have hcf : f * c = c * f := (mem_centralizer_iff.1 (hF₁₂c hf) c (mem_inf.1 hc).1).symm
    have hx' : f * c * v ^ e = f * v ^ e * c := by rw [mul_assoc, hcv, ← mul_assoc]
    have hbc : Commute (f * v ^ e) c := by
      show f * v ^ e * c = c * (f * v ^ e)
      rw [mul_assoc, ← hcv, ← mul_assoc, hcf, mul_assoc]
    have hb : f * v ^ e ∈ F₁ ⊔ zpowers v :=
      mul_mem (mem_sup_left hf) (mem_sup_right (pow_mem (mem_zpowers v) e))
    have hxN : (f * v ^ e * c) ^ orderOf (f * c * v ^ e) = 1 := by
      rw [← hx']
      exact pow_orderOf_eq_one _
    rw [hbc.mul_pow] at hxN
    have hcN : c ^ orderOf (f * c * v ^ e) ∈ F₁ ⊔ zpowers v := by
      rw [eq_inv_of_mul_eq_one_right hxN]
      exact inv_mem (pow_mem hb _)
    have hcN1 := hBF₂ _ hcN (pow_mem (mem_inf.1 hc).1 _)
    obtain ⟨j, hj⟩ := hxo
    rw [hj, pow_succ, pow_mul, sq, (hZj c hc).2, one_pow, one_mul] at hcN1
    rw [hx', hcN1, mul_one]
    exact hb
  have hJB : J ≤ normalizer ((F₁ ⊔ zpowers v : Subgroup Y) : Set Y) := by
    rw [le_normalizer_iff]
    intro g hg y hy
    obtain ⟨f, hf, z, hz, rfl⟩ := (mem_sup_iff_of_le_normalizer hzN).1 hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hz
    have hgv : g * v * g⁻¹ ∈ F₁ ⊔ zpowers v := by
      refine hodd _ (mem_inf.2 ⟨hKn.conj_mem v hvK g, (mem_normalizer_iff.1
        (mem_normalizer_centralizer_of_mem (hJN₂ hg)) v).1 hvC₂⟩) ?_
      rw [orderOf_conj_eq]
      exact hm
    have e : g * (f * v ^ i) * g⁻¹ = g * f * g⁻¹ * (g * v * g⁻¹) ^ i := by
      rw [conj_zpow]
      group
    rw [e]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.1 (hJN₁ hg) f).1 hf)) (zpow_mem hgv i)
  have hT₁B : T₁ ≤ normalizer ((F₁ ⊔ zpowers v : Subgroup Y) : Set Y) := hT₁J.trans hJB
  have hF₁z : F₁ ⊓ zpowers v = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    exact (mem_bot).2 (hV0 y (mem_inf.1 hy).2 (hF₁c (mem_inf.1 hy).1))
  have hBcard : Nat.card (F₁ ⊔ zpowers v : Subgroup Y) = 12 := by
    rw [card_sup_of_le_normalizer hzN hF₁z, IsKleinFour.card_four (G := ↥F₁), Nat.card_zpowers, hvo]
  have hT₁B' : T₁ ⊓ (F₁ ⊔ zpowers v) = F₁ := le_antisymm (fun y hy => by
      obtain ⟨k, hk⟩ := hT₁p ⟨y, (mem_inf.1 hy).1⟩
      exact hB2 y (mem_inf.1 hy).2 k (by simpa using congrArg Subtype.val hk))
    (le_inf hF₁T₁ le_sup_left)
  have hT₁card : Nat.card T₁ = 8 := by
    have hle := hD₁.card_inf_normalizer_le hF₁T₁ hfour le_rfl
    rw [inf_eq_left.2 (hT₁J.trans hJN₁), IsKleinFour.card_four (G := ↥F₁)] at hle
    have hdvd : Nat.card F₁ ∣ Nat.card T₁ := card_dvd_of_le hF₁T₁
    rw [IsKleinFour.card_four (G := ↥F₁)] at hdvd
    have hne : Nat.card T₁ ≠ 4 := by
      intro h4
      apply hTK
      have heq : F₁ = T₁ := eq_of_le_of_card_ge hF₁T₁ (by rw [h4, IsKleinFour.card_four (G := ↥F₁)])
      rw [← heq]
      exact hFK₁
    obtain ⟨q, hq⟩ := hdvd
    have hpos : 0 < Nat.card T₁ := Nat.card_pos
    omega
  have hLcard : Nat.card ((F₁ ⊔ zpowers v) ⊔ T₁ : Subgroup Y) = 24 := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      hT₁B
    rw [hT₁B', IsKleinFour.card_four (G := ↥F₁), hT₁card, hBcard] at h
    rw [sup_comm]
    omega
  have hLsyl : IsSylowOf 2 T₁ ((F₁ ⊔ zpowers v) ⊔ T₁) := by
    rw [isSylowOf_iff]
    refine ⟨le_sup_right, hT₁p, ?_⟩
    have h := Subgroup.relIndex_mul_card T₁ ((F₁ ⊔ zpowers v) ⊔ T₁)
    rw [inf_eq_left.2 le_sup_right, hT₁card, hLcard] at h
    have h3 : T₁.relIndex ((F₁ ⊔ zpowers v) ⊔ T₁) = 3 := by omega
    rw [h3]
    norm_num
  have hLC₂ : (F₁ ⊔ zpowers v) ⊔ T₁ ≤ centralizer (F₂ : Set Y) := sup_le hBC₂ hT₁C
  have hJL : J ≤ normalizer (((F₁ ⊔ zpowers v) ⊔ T₁ : Subgroup Y) : Set Y) := by
    refine (le_sup_twoResidualOf_of_isSylowOf hT).trans (sup_le ?_ ?_)
    · exact le_normalizer_sup (hT.le.trans hJB) (sup_le le_normalizer
        (le_normalizer_of_comm fun x hx y hy => mem_centralizer_iff.1 (hTc hy) x hx))
    · refine le_normalizer_sup_of_forall hT₁B hD₁
        (fun k hk b hb => mem_sup_left ((mem_normalizer_iff.1 (hJB (hKJ hk)) b).1 hb)) ?_
      intro k hk s hs hs2
      obtain ⟨e, f, hf, c, hc, hfc⟩ := hdec _ (hcomm k hk s hs)
      have hcv : c * v ^ e = v ^ e * c :=
        mem_centralizer_iff.1 (pow_mem hvC₂ e) c (mem_inf.1 hc).1
      exact conj_mem_of_commutator_mem hT₁₂ hfus hLsyl hLC₂ hZj hs hs2
        (mem_sup_left (mul_mem (mem_sup_left hf) (mem_sup_right (pow_mem (mem_zpowers v) e)))) hc
        (by rw [hfc, mul_assoc f c, hcv, ← mul_assoc])
  have hOL : CFSG.oddCore ((F₁ ⊔ zpowers v) ⊔ T₁ : Subgroup Y) = ⊥ := by
    have hO' : O ((F₁ ⊔ zpowers v) ⊔ T₁) = ⊥ :=
      eq_bot_of_odd_of_le_normalizer hO hKJ (le_normalizer_O_of_le_normalizer hJL) (card_O_odd _)
    exact (map_eq_bot_iff_of_injective _ ((F₁ ⊔ zpowers v) ⊔ T₁).subtype_injective).1 hO'
  exact ⟨(F₁ ⊔ zpowers v) ⊔ T₁, le_sup_right, sup_le (hBK.trans hKJ) hT₁J, hJL, hLsyl,
    isL2PGL2OrA7OrV4_of_card_eq_24 (hasDihedralSylowTwo_of_isSylowOf hLsyl hD₁) hOL hLcard⟩

theorem exists_factor_of
    (hO : CFSG.oddCore Y = ⊥) {J T₁ T₂ F₁ F₂ : Subgroup Y}
    (hKJ : twoResidualOf (⊤ : Subgroup Y) ≤ J) (hT : IsSylowOf 2 (T₁ ⊔ T₂) J)
    (hT₁₂ : T₁ ⊓ T₂ = ⊥) (hTc : T₂ ≤ centralizer (T₁ : Set Y)) (hD₁ : IsDih T₁)
    (hfus : ∀ x ∈ T₁ ⊔ T₂, ∀ y ∈ T₁ ⊔ T₂, orderOf x = 2 → IsConj x y →
      (x ∈ T₁ ↔ y ∈ T₁) ∧ (x ∈ T₂ ↔ y ∈ T₂))
    (hFK₁ : F₁ ≤ twoResidualOf ⊤) (hFK₂ : F₂ ≤ twoResidualOf ⊤)
    (hFn₁ : (F₁.subgroupOf (twoResidualOf ⊤)).Normal)
    (hFn₂ : (F₂.subgroupOf (twoResidualOf ⊤)).Normal) (hF₁₂ : F₁ ⊓ F₂ = ⊥)
    (hFodd : Odd ((F₁ ⊔ F₂).relIndex (twoResidualOf ⊤)))
    (hA₁ : IsAStarFactor F₁) (hA₂ : IsAStarFactor F₂)
    (hW₁ : IsSylowOf 2 (T₁ ⊓ F₁) F₁) (hW₂ : IsSylowOf 2 (T₂ ⊓ F₂) F₂)
    (hNI : ∀ x ∈ twoResidualOf ⊤ ⊓ centralizer (twoResidualOf (⊤ : Subgroup Y) : Set Y),
      x * x = 1 → x = 1) :
    ∃ L : Subgroup Y, T₁ ≤ L ∧ L ≤ J ∧ J ≤ normalizer (L : Set Y) ∧ IsSylowOf 2 T₁ L ∧
      IsL2PGL2OrA7OrV4 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFN₁ : twoResidualOf ⊤ ≤ normalizer (F₁ : Set Y) :=
    (normal_subgroupOf_iff_le_normalizer hFK₁).1 hFn₁
  have hFN₂ : twoResidualOf ⊤ ≤ normalizer (F₂ : Set Y) :=
    (normal_subgroupOf_iff_le_normalizer hFK₂).1 hFn₂
  have hT' : IsSylowOf 2 (T₂ ⊔ T₁) J := by rwa [sup_comm]
  have hT₁₂' : T₂ ⊓ T₁ = ⊥ := by rwa [inf_comm]
  have hTc' : T₁ ≤ centralizer (T₂ : Set Y) := le_centralizer_iff.1 hTc
  have hfus' : ∀ x ∈ T₂ ⊔ T₁, ∀ y ∈ T₂ ⊔ T₁, orderOf x = 2 → IsConj x y →
      (x ∈ T₂ ↔ y ∈ T₂) ∧ (x ∈ T₁ ↔ y ∈ T₁) := by
    intro x hx y hy hx2 hxy
    rw [sup_comm] at hx hy
    exact (hfus x hx y hy hx2 hxy).symm
  have hF₁₂' : F₂ ⊓ F₁ = ⊥ := by rwa [inf_comm]
  have hFodd' : Odd ((F₂ ⊔ F₁).relIndex (twoResidualOf ⊤)) := by rwa [sup_comm]
  have hTK₁ := inf_twoResidualOf_le hKJ hT hT₁₂ hTc hFK₁ hFK₂ hFN₁ hFN₂ hF₁₂ hFodd hW₁ hW₂
  have hTK₂ := inf_twoResidualOf_le hKJ hT' hT₁₂' hTc' hFK₂ hFK₁ hFN₂ hFN₁ hF₁₂' hFodd' hW₂ hW₁
  have hTN₁ := le_normalizer_of_isAStarFactor hTc hFK₁ hFN₁ hA₁ hW₁ hTK₁
  have hTN₂' := le_normalizer_of_isAStarFactor hTc' hFK₂ hFN₂ hA₂ hW₂ hTK₂
  have hTN₂ : T₁ ⊔ T₂ ≤ normalizer (F₂ : Set Y) := by rwa [sup_comm] at hTN₂'
  have hJN₁ : J ≤ normalizer (F₁ : Set Y) :=
    (le_sup_twoResidualOf_of_isSylowOf hT).trans (sup_le hTN₁ hFN₁)
  have hJN₂ : J ≤ normalizer (F₂ : Set Y) :=
    (le_sup_twoResidualOf_of_isSylowOf hT).trans (sup_le hTN₂ hFN₂)
  have hT₁C : T₁ ≤ centralizer (F₂ : Set Y) :=
    le_centralizer_of_fusion hT' hT₁₂' hTc' hD₁ hfus' hTN₂' (oddCore_eq_bot_of_isAStarFactor hA₂)
      hW₂
  have hF₁₂c : F₁ ≤ centralizer (F₂ : Set Y) :=
    le_centralizer_of_le_normalizer_of_inf_eq_bot hFK₁ hFK₂ hFN₁ hFN₂ hF₁₂
  have hZ := isPGroup_inf_centralizer hO hKJ hT hJN₁ hJN₂ hFK₁ hFK₂ hFN₁ hFN₂ hFodd
  have hZdec : ∀ z ∈ twoResidualOf ⊤ ⊓ centralizer (F₁ : Set Y) ⊓ centralizer (F₂ : Set Y),
      ∃ f ∈ F₁, ∃ c ∈ F₂ ⊓ centralizer (F₂ : Set Y), z = f * c := fun z hz =>
    exists_mul_of_mem_inf_centralizer hFK₁ hFK₂ hFN₁ hFN₂ hFodd hF₁₂c hZ hz
  have hZj : ∀ c ∈ F₂ ⊓ centralizer (F₂ : Set Y), c ∈ T₂ ∧ c * c = 1 := fun c hc =>
    mem_and_mul_self_of_mem_inf_centralizer hA₂ hW₂ hc
  rcases hA₁.isL2OrA7_or with hL₁ | hV
  · exact exists_factor_of_isL2OrA7 hKJ hT hT₁₂ hTc hD₁ hfus hFK₁ hJN₁ hL₁ hW₁ hJN₂ hF₁₂c hT₁C
      hZdec hZj
  · by_cases hTK : T₁ ≤ twoResidualOf ⊤
    ·
      have heq : T₁ = F₁ :=
        le_antisymm (fun x hx => hTK₁ (mem_inf.2 ⟨hx, hTK hx⟩))
          (le_of_isKleinFour_of_isSylowOf hV hW₁)
      refine ⟨T₁, le_rfl, le_sup_left.trans hT.le, by rw [heq]; exact hJN₁, ?_, ?_⟩
      · rw [isSylowOf_iff]
        exact ⟨le_rfl, hT.isPGroup.to_le le_sup_left, by rw [relIndex_self]; norm_num⟩
      · rw [heq]
        exact Or.inr (Or.inr hV)
    · exact exists_factor_of_four hO hKJ hT hT₁₂ hTc hD₁ hfus hFK₁ hJN₁ hV hW₁ hTK hJN₂ hF₁₂
        hF₁₂c hT₁C hZ hZdec hZj hNI

end Factor

end CFSG.GH72
