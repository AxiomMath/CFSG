module

public import CFSG.GH74.Uniqueness.Section4Aut
public import CFSG.GH74.Uniqueness.Section4Struct

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

namespace XDataInv

section Elementary

variable {X : Type*} [Group X]

theorem orderOf_inv_mul_mul_eq (b y : X) : orderOf (b⁻¹ * y * b) = orderOf y := by
  have h : SemiconjBy b⁻¹ y (b⁻¹ * y * b) := by
    unfold SemiconjBy
    group
  exact (SemiconjBy.orderOf_eq _ h).symm

theorem mem_normalizer_inf_centralizer {O : Subgroup X} {a g : X}
    (hg : g ∈ normalizer (O : Set X)) (hga : g * a = a * g) :
    g ∈ normalizer ((O ⊓ centralizer ({a} : Set X) : Subgroup X) : Set X) := by
  have hga' : g⁻¹ * a = a * g⁻¹ := by
    calc g⁻¹ * a = g⁻¹ * (a * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * a) * g⁻¹ := by rw [hga]
      _ = a * g⁻¹ := by group
  have hc : ∀ n : X, n * a = a * n → g * n * g⁻¹ * a = a * (g * n * g⁻¹) := by
    intro n h
    calc g * n * g⁻¹ * a = g * n * (g⁻¹ * a) := by group
      _ = g * n * (a * g⁻¹) := by rw [hga']
      _ = g * (n * a) * g⁻¹ := by group
      _ = g * (a * n) * g⁻¹ := by rw [h]
      _ = (g * a) * n * g⁻¹ := by group
      _ = (a * g) * n * g⁻¹ := by rw [hga]
      _ = a * (g * n * g⁻¹) := by group
  have hc' : ∀ n : X, g * n * g⁻¹ * a = a * (g * n * g⁻¹) → n * a = a * n := by
    intro n h
    calc n * a = g⁻¹ * (g * n * g⁻¹) * (g * a) := by group
      _ = g⁻¹ * (g * n * g⁻¹) * (a * g) := by rw [hga]
      _ = g⁻¹ * (g * n * g⁻¹ * a) * g := by group
      _ = g⁻¹ * (a * (g * n * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * a) * (g * n * g⁻¹) * g := by group
      _ = (a * g⁻¹) * (g * n * g⁻¹) * g := by rw [hga']
      _ = a * n := by group
  rw [Subgroup.mem_normalizer_iff]
  intro n
  have hO := Subgroup.mem_normalizer_iff.mp hg n
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hn, hna⟩
    exact ⟨hO.mp hn, hc n hna⟩
  · rintro ⟨hn, hna⟩
    exact ⟨hO.mpr hn, hc' n hna⟩

end Elementary

section Lift

variable {X : Type*} [Group X] [Finite X]

theorem exists_involution_coset_commuting {O D : Subgroup X} (hO : Odd (Nat.card O)) (hOD : O ≤ D)
    {a v d : X} (hv : v * v = 1) (hav : v * a = a * v) (hvO : v ∈ normalizer (O : Set X))
    (hdD : d ∈ D) (hdO : d ∈ normalizer (O : Set X)) (hda : d * a = a * d)
    (hvd : v * d * v⁻¹ * d⁻¹ ∈ O) (hd2 : d * d ∈ O) (hdn : d ∉ O) :
    ∃ y ∈ D, orderOf y = 2 ∧ y * d⁻¹ ∈ O ∧ y * a = a * y ∧ v * y = y * v := by
  obtain ⟨y₀, hy₀z, hy₀2, hy₀d⟩ := exists_involution_mem_zpowers_coset hO hd2 hdn
  have hy₀a : y₀ * a = a * y₀ := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy₀z
    exact ((show Commute d a from hda).zpow_left k).eq
  have hy₀O : y₀ ∈ normalizer (O : Set X) := (Subgroup.zpowers_le.mpr hdO) hy₀z
  have hy₀D : y₀ ∈ D := (Subgroup.zpowers_le.mpr hdD) hy₀z
  have hvy₀ : v * y₀ * v⁻¹ * y₀⁻¹ ∈ O := by
    have e : v * y₀ * v⁻¹ * y₀⁻¹ =
        (v * (y₀ * d⁻¹) * v⁻¹) * (v * d * v⁻¹ * d⁻¹) * (y₀ * d⁻¹)⁻¹ := by group
    rw [e]
    exact O.mul_mem (O.mul_mem ((Subgroup.mem_normalizer_iff.mp hvO _).mp hy₀d) hvd)
      (O.inv_mem hy₀d)
  have hN'odd : Odd (Nat.card (O ⊓ centralizer ({a} : Set X) : Subgroup X)) :=
    Odd.of_dvd_nat hO (Subgroup.card_dvd_of_le inf_le_left)
  have hvN' := mem_normalizer_inf_centralizer hvO hav
  have hyN' := mem_normalizer_inf_centralizer hy₀O hy₀a
  have hvyN' : v * y₀ * v⁻¹ * y₀⁻¹ ∈ (O ⊓ centralizer ({a} : Set X) : Subgroup X) := by
    refine Subgroup.mem_inf.mpr ⟨hvy₀, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : Commute v a := hav
    have h2 : Commute y₀ a := hy₀a
    exact (((h1.mul_left h2).mul_left h1.inv_left).mul_left h2.inv_left).eq
  obtain ⟨b, hbN', hb⟩ := exists_commuting_involution_conj hN'odd hv hy₀2 hvN' hyN' hvyN'
  obtain ⟨hbO, hba⟩ := Subgroup.mem_inf.mp hbN'
  rw [Subgroup.mem_centralizer_singleton_iff] at hba
  refine ⟨b⁻¹ * y₀ * b, ?_, ?_, ?_, ?_, hb⟩
  · exact D.mul_mem (D.mul_mem (D.inv_mem (hOD hbO)) hy₀D) (hOD hbO)
  · rw [orderOf_inv_mul_mul_eq]
    exact hy₀2
  · have e : b⁻¹ * y₀ * b * d⁻¹ = b⁻¹ * (y₀ * d⁻¹) * (d * b * d⁻¹) := by group
    rw [e]
    exact O.mul_mem (O.mul_mem (O.inv_mem hbO) hy₀d)
      ((Subgroup.mem_normalizer_iff.mp hdO b).mp hbO)
  · have h1 : Commute b a := hba
    have h2 : Commute y₀ a := hy₀a
    exact ((h1.inv_left.mul_left h2).mul_left h1).eq

end Lift

section Bender

variable {K : Type*} [Group K] [Finite K]

theorem exists_two_involutions_centralizing
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) {g : K}
    (hg : g * g = 1) :
    ∃ a b : K, orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ a * b = b * a ∧ g * a = a * g ∧
      g * b = b * g := by
  have hrank : 2 ≤ Open.pRank 2 (⊤ : Subgroup K) := two_le_twoRank_of_isBenderGroup hK
  obtain ⟨a₀, b₀, -, -, ha₀, hb₀, hne, hab⟩ := exists_commuting_involutions_of_two_le_pRank hrank
  by_cases hg1 : g = 1
  · exact ⟨a₀, b₀, ha₀, hb₀, hne, hab, by rw [hg1, one_mul, mul_one], by rw [hg1, one_mul, mul_one]⟩
  · have hg2 : orderOf g = 2 := orderOf_eq_prime (by rwa [pow_two]) hg1
    obtain ⟨x, hx⟩ := isConj_iff.mp (isConj_of_involutions_of_isBenderGroup hK ha₀ hg2)
    have hb' : orderOf (x * b₀ * x⁻¹) = 2 := by
      have := orderOf_inv_mul_mul_eq x⁻¹ b₀
      rw [inv_inv] at this
      rw [this]
      exact hb₀
    refine ⟨g, x * b₀ * x⁻¹, hg2, hb', ?_, ?_, ?_, ?_⟩
    · intro h
      apply hne
      rw [← hx] at h
      exact mul_left_cancel (mul_right_cancel h)
    · rw [← hx]
      calc x * a₀ * x⁻¹ * (x * b₀ * x⁻¹) = x * (a₀ * b₀) * x⁻¹ := by group
        _ = x * (b₀ * a₀) * x⁻¹ := by rw [hab]
        _ = x * b₀ * x⁻¹ * (x * a₀ * x⁻¹) := by group
    · rfl
    · rw [← hx]
      calc x * a₀ * x⁻¹ * (x * b₀ * x⁻¹) = x * (a₀ * b₀) * x⁻¹ := by group
        _ = x * (b₀ * a₀) * x⁻¹ := by rw [hab]
        _ = x * b₀ * x⁻¹ * (x * a₀ * x⁻¹) := by group

theorem exists_involution_of_isBenderGroup
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) :
    ∃ a : K, orderOf a = 2 := by
  have hrank : 2 ≤ Open.pRank 2 (⊤ : Subgroup K) := two_le_twoRank_of_isBenderGroup hK
  obtain ⟨a₀, -, -, -, ha₀, -⟩ := exists_commuting_involutions_of_two_le_pRank hrank
  exact ⟨a₀, ha₀⟩

theorem sq_eq_one_of_inner
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) {α : MulAut K}
    (hα2 : α * α = 1) {g : K} (hg : ∀ y : K, α y = g * y * g⁻¹) : g * g = 1 := by
  have hc : g * g ∈ center K := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h := DFunLike.congr_fun hα2 y
    simp only [MulAut.mul_apply, MulAut.one_apply, hg] at h
    calc y * (g * g) = (g * (g * y * g⁻¹) * g⁻¹) * (g * g) := by rw [h]
      _ = (g * g) * y := by group
  rw [center_eq_bot_of_isBenderGroup hK, Subgroup.mem_bot] at hc
  exact hc

end Bender

end XDataInv

namespace XDataInv

section Main

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M L D O : Subgroup X} {u : X}

theorem mem_normalizer_O_of_mem_normalizer (hD : XData Z M L D O u) {g : X}
    (hg : g ∈ normalizer (L : Set X)) : g ∈ normalizer (O : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hD.O_norm g hg x hx, fun hx => ?_⟩
  have := hD.O_norm g⁻¹ ((normalizer (L : Set X)).inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem exists_aut {K : Type*} [Group K] (hD : XData Z M L D O u) {φ : ↥D →* K}
    (hφ : Function.Surjective φ) (hker : φ.ker = O.subgroupOf D) {g : X}
    (hg : g ∈ normalizer (L : Set X)) :
    ∃ α : MulAut K, ∀ d e : ↥D, (e : X) = g * d * g⁻¹ → α (φ d) = φ e := by
  have hg' : g⁻¹ ∈ normalizer (L : Set X) := (normalizer (L : Set X)).inv_mem hg
  refine XDataAut.exists_mulAut_of_conj φ hφ hker (hD.D_norm g hg) ?_ (hD.O_norm g hg) ?_
  · intro d hd
    simpa using hD.D_norm g⁻¹ hg' d hd
  · intro o ho
    simpa using hD.O_norm g⁻¹ hg' o ho

omit [Finite X] in
theorem lift_data {K : Type*} [Group K] {φ : ↥D →* K}
    (hker : φ.ker = O.subgroupOf D) {v : X} (hvD : ∀ d ∈ D, v * d * v⁻¹ ∈ D) {α : MulAut K}
    (hα : ∀ d e : ↥D, (e : X) = v * d * v⁻¹ → α (φ d) = φ e)
    {c : ↥D} {κ : K} (hc : φ c = κ) (hκ : orderOf κ = 2) (hfix : α κ = κ) :
    (c : X) * c ∈ O ∧ (c : X) ∉ O ∧ v * c * v⁻¹ * (c : X)⁻¹ ∈ O := by
  have hκ2 : κ * κ = 1 := by rw [← pow_two, ← hκ, pow_orderOf_eq_one]
  refine ⟨?_, ?_, ?_⟩
  · refine (map_eq_one_iff_mem_of_ker hker (D.mul_mem c.2 c.2)).mp ?_
    change φ (c * c) = 1
    rw [map_mul, hc, hκ2]
  · intro hcO
    have h1 := (map_eq_one_iff_mem_of_ker hker c.2).mpr hcO
    change φ c = 1 at h1
    rw [hc] at h1
    rw [h1, orderOf_one] at hκ
    exact absurd hκ (by norm_num)
  · have h1 := hα c ⟨v * c * v⁻¹, hvD c c.2⟩ rfl
    rw [hc, hfix] at h1
    exact (map_eq_map_iff_of_ker hker (hvD c c.2) c.2).mp (h1.symm.trans hc.symm)

end Main

end XDataInv

section Final

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M L D O : Subgroup X} {u : X}

theorem XData.exists_involution_commuting
    (hB : BenderOuterInvolution) (hD : XData Z M L D O u)
    {v : X} (hvN : v ∈ normalizer (L : Set X)) (hv2 : v * v = 1) :
    ∃ d ∈ D, orderOf d = 2 ∧ v * d = d * v := by
  obtain ⟨K, instK, φ, hsurj, hker, hKB, S, hS⟩ := hD.bar
  have : Finite K := Finite.of_surjective φ hsurj
  obtain ⟨αv, hαv⟩ := XDataInv.exists_aut hD hsurj hker hvN
  have hvD := hD.D_norm v hvN
  have hαv2 : αv * αv = 1 := XDataAut.mulAut_mul_self_eq_one hsurj hvD hv2 hαv
  have hvO : v ∈ normalizer (O : Set X) := XDataInv.mem_normalizer_O_of_mem_normalizer hD hvN
  obtain ⟨κ, hκ, hfix⟩ : ∃ κ : K, orderOf κ = 2 ∧ αv κ = κ := by
    by_cases hinner : ∃ k : K, ∀ x : K, αv x = k * x * k⁻¹
    · obtain ⟨g, hg⟩ := hinner
      have hg2 := XDataInv.sq_eq_one_of_inner hKB hαv2 hg
      by_cases hg1 : g = 1
      · obtain ⟨a, ha⟩ := XDataInv.exists_involution_of_isBenderGroup hKB
        exact ⟨a, ha, by rw [hg a, hg1]; group⟩
      · exact ⟨g, orderOf_eq_prime (by rwa [pow_two]) hg1, by rw [hg g]; group⟩
    · obtain ⟨⟨y, hy1, hy2, hyfix⟩, -⟩ := hB K hKB αv hαv2 hinner
      exact ⟨y, orderOf_eq_prime (by rwa [pow_two]) hy1, hyfix⟩
  obtain ⟨d₁, hd₁⟩ := hsurj κ
  obtain ⟨hd₁2, hd₁n, hd₁v⟩ := XDataInv.lift_data hker hvD hαv hd₁ hκ hfix
  obtain ⟨y, hyD, hy2, -, -, hvy⟩ := XDataInv.exists_involution_coset_commuting hD.O_odd hD.O_le
    (a := 1) hv2 (by rw [mul_one, one_mul]) hvO d₁.2 (hD.mem_normalizer_O (hD.D_le d₁.2))
    (by rw [mul_one, one_mul]) hd₁v hd₁2 hd₁n
  exact ⟨y, hyD, hy2, hvy⟩

theorem XData.false_of_involutory
    (hB : BenderOuterInvolution) (hD : XData Z M L D O u)
    {v z : X} (hvN : v ∈ normalizer (L : Set X)) (hv2 : v * v = 1) (hzL : z ∈ L) (hz2 : z * z = 1)
    (hvz : v * z = z * v)
    (hzin : ∃ e ∈ D, ∀ d ∈ D, z * d * z⁻¹ = e * d * e⁻¹)
    (hfix : ∀ d ∈ D, (v * z) * d = d * (v * z) → d ∈ M)
    (hrank : ∀ a ∈ D, ∀ b ∈ D, orderOf a = 2 → orderOf b = 2 → a ≠ b → a * b = b * a →
      v * a = a * v → v * b = b * v → False) : False := by
  obtain ⟨K, instK, φ, hsurj, hker, hKB, S, hS⟩ := hD.bar
  have : Finite K := Finite.of_surjective φ hsurj
  have hzN : z ∈ normalizer (L : Set X) := Subgroup.le_normalizer hzL
  have hwN : v * z ∈ normalizer (L : Set X) := (normalizer (L : Set X)).mul_mem hvN hzN
  have hw2 : (v * z) * (v * z) = 1 := by
    calc v * z * (v * z) = v * (z * v) * z := by group
      _ = v * (v * z) * z := by rw [hvz]
      _ = (v * v) * (z * z) := by group
      _ = 1 := by rw [hv2, hz2, one_mul]
  obtain ⟨αv, hαv⟩ := XDataInv.exists_aut hD hsurj hker hvN
  obtain ⟨αz, hαz⟩ := XDataInv.exists_aut hD hsurj hker hzN
  obtain ⟨αw, hαw⟩ := XDataInv.exists_aut hD hsurj hker hwN
  have hvD := hD.D_norm v hvN
  have hzD := hD.D_norm z hzN
  have hwD := hD.D_norm (v * z) hwN
  have hαwvz : αw = αv * αz := XDataAut.mulAut_mul_eq hsurj hvD hzD hαv hαz hαw
  have hαw2 : αw * αw = 1 := XDataAut.mulAut_mul_self_eq_one hsurj hwD hw2 hαw
  have hαv2 : αv * αv = 1 := XDataAut.mulAut_mul_self_eq_one hsurj hvD hv2 hαv
  have hvO : v ∈ normalizer (O : Set X) := XDataInv.mem_normalizer_O_of_mem_normalizer hD hvN
  by_cases hinner : ∃ k : K, ∀ x : K, αw x = k * x * k⁻¹
  ·
    obtain ⟨k, hk⟩ := hinner
    obtain ⟨e, heD, he⟩ := hzin
    have hαz' := XDataAut.mulAut_eq_conj_of_inner hsurj heD he hαz
    have hαv' : ∀ y : K, αv y = (k * (φ ⟨e, heD⟩)⁻¹) * y * (k * (φ ⟨e, heD⟩)⁻¹)⁻¹ := by
      intro y
      have h1 := hk ((φ ⟨e, heD⟩)⁻¹ * y * φ ⟨e, heD⟩)
      rw [hαwvz, MulAut.mul_apply, hαz'] at h1
      have e1 : φ ⟨e, heD⟩ * ((φ ⟨e, heD⟩)⁻¹ * y * φ ⟨e, heD⟩) * (φ ⟨e, heD⟩)⁻¹ = y := by group
      rw [e1] at h1
      rw [h1]
      group
    obtain ⟨g, hg⟩ : ∃ g : K, ∀ y : K, αv y = g * y * g⁻¹ := ⟨_, hαv'⟩
    have hg2 : g * g = 1 := XDataInv.sq_eq_one_of_inner hKB hαv2 hg
    obtain ⟨κa, κb, hκa, hκb, hne, hκab, hgκa, hgκb⟩ :=
      XDataInv.exists_two_involutions_centralizing hKB hg2
    have hfa : αv κa = κa := by
      rw [hg]
      exact mul_inv_eq_iff_eq_mul.mpr hgκa
    have hfb : αv κb = κb := by
      rw [hg]
      exact mul_inv_eq_iff_eq_mul.mpr hgκb
    obtain ⟨a₁, ha₁⟩ := hsurj κa
    obtain ⟨ha₁2, ha₁n, ha₁v⟩ := XDataInv.lift_data hker hvD hαv ha₁ hκa hfa
    obtain ⟨a, haD, ha2, haa₁, -, hva⟩ := XDataInv.exists_involution_coset_commuting hD.O_odd
      hD.O_le (a := 1) hv2 (by rw [mul_one, one_mul]) hvO a₁.2
      (hD.mem_normalizer_O (hD.D_le a₁.2)) (by rw [mul_one, one_mul]) ha₁v ha₁2 ha₁n
    have hφa : φ ⟨a, haD⟩ = κa := by
      rw [← ha₁]
      exact (map_eq_map_iff_of_ker hker haD a₁.2).mpr haa₁
    obtain ⟨b₁, hb₁⟩ := hsurj κb
    have ha2' : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
    have hcoset : a * (b₁ : X) * a⁻¹ * (b₁ : X)⁻¹ ∈ O := by
      have hmemD : a * (b₁ : X) * a⁻¹ * (b₁ : X)⁻¹ ∈ D :=
        D.mul_mem (D.mul_mem (D.mul_mem haD b₁.2) (D.inv_mem haD)) (D.inv_mem b₁.2)
      refine (map_eq_one_iff_mem_of_ker hker hmemD).mp ?_
      change φ (⟨a, haD⟩ * b₁ * ⟨a, haD⟩⁻¹ * b₁⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hφa, hb₁]
      calc κa * κb * κa⁻¹ * κb⁻¹ = κb * κa * κa⁻¹ * κb⁻¹ := by rw [hκab]
        _ = 1 := by group
    obtain ⟨n, hnO, hfixn⟩ := exists_fixed_mem_coset hD.O_odd ha2'
      (hD.mem_normalizer_O (hD.D_le haD)) (hD.mem_normalizer_O (hD.D_le b₁.2)) hcoset
    have hcD : (b₁ : X) * n ∈ D := D.mul_mem b₁.2 (hD.O_le hnO)
    have hφc : φ ⟨(b₁ : X) * n, hcD⟩ = κb := by
      have h1 : φ ⟨n, hD.O_le hnO⟩ = 1 := (map_eq_one_iff_mem_of_ker hker _).mpr hnO
      have h2 : (⟨(b₁ : X) * n, hcD⟩ : ↥D) = b₁ * ⟨n, hD.O_le hnO⟩ := rfl
      rw [h2, map_mul, h1, mul_one, hb₁]
    have hac : a * ((b₁ : X) * n) = ((b₁ : X) * n) * a := mul_inv_eq_iff_eq_mul.mp hfixn
    obtain ⟨hc2, hcn, hcv⟩ := XDataInv.lift_data hker hvD hαv hφc hκb hfb
    obtain ⟨b, hbD, hb2, hbc, hba, hvb⟩ := XDataInv.exists_involution_coset_commuting hD.O_odd
      hD.O_le (a := a) hv2 hva hvO hcD (hD.mem_normalizer_O (hD.D_le hcD)) hac.symm hcv hc2 hcn
    have hφb : φ ⟨b, hbD⟩ = κb := by
      rw [← hφc]
      exact (map_eq_map_iff_of_ker hker hbD hcD).mpr hbc
    refine hrank a haD b hbD ha2 hb2 ?_ hba.symm hva hvb
    intro hab
    exact hne (hφa.symm.trans ((congrArg φ (Subtype.ext hab)).trans hφb))
  ·
    obtain ⟨x, hxfix, hxnot⟩ := (hB K hKB αw hαw2 hinner).2 S
    obtain ⟨d₀, rfl⟩ := hsurj x
    have hcoset : (v * z) * (d₀ : X) * (v * z)⁻¹ * (d₀ : X)⁻¹ ∈ O := by
      have h1 := hαw d₀ ⟨(v * z) * d₀ * (v * z)⁻¹, hwD d₀ d₀.2⟩ rfl
      exact (map_eq_map_iff_of_ker hker (hwD d₀ d₀.2) d₀.2).mp (h1.symm.trans hxfix)
    obtain ⟨n, hnO, hfixn⟩ := exists_fixed_mem_coset hD.O_odd hw2
      (XDataInv.mem_normalizer_O_of_mem_normalizer hD hwN)
      (hD.mem_normalizer_O (hD.D_le d₀.2)) hcoset
    have hdD : (d₀ : X) * n ∈ D := D.mul_mem d₀.2 (hD.O_le hnO)
    have hcomm : (v * z) * ((d₀ : X) * n) = ((d₀ : X) * n) * (v * z) :=
      mul_inv_eq_iff_eq_mul.mp hfixn
    have hdM := hfix _ hdD hcomm
    have hmem : φ ⟨(d₀ : X) * n, hdD⟩ ∈ (M.subgroupOf D).map φ :=
      ⟨⟨(d₀ : X) * n, hdD⟩, Subgroup.mem_subgroupOf.mpr hdM, rfl⟩
    rw [hS] at hmem
    have heq : φ ⟨(d₀ : X) * n, hdD⟩ = φ d₀ := by
      have h1 : φ ⟨n, hD.O_le hnO⟩ = 1 := (map_eq_one_iff_mem_of_ker hker _).mpr hnO
      have h2 : (⟨(d₀ : X) * n, hdD⟩ : ↥D) = d₀ * ⟨n, hD.O_le hnO⟩ := rfl
      rw [h2, map_mul, h1, mul_one]
    rw [heq] at hmem
    exact hxnot hmem

end Final

end CFSG.GH74.Uniqueness
