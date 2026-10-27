module

public import CFSG.HardMathSupport.Foote.E27.SporCentKill
public import CFSG.HardMathSupport.Foote.E27.LieTwo.SylowNormal

public section

namespace CFSG.HardMathSupport.Foote.E27

open Subgroup

section Cover

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem E27Config.false_of_torus_cover (h : E27Config X K R T z) (hz : z ∈ K)
    {J : Type*} [Group J] [Finite J] (φ : ↥K ≃* J) (S₀ : Subgroup J)
    (hS₀ : Nat.card S₀ = 3 ^ (Nat.card J).factorization 3) (B : Subgroup J)
    (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB : 81 ∣ Nat.card B)
    (hcov : ∀ s ∈ S₀, s ^ 3 = 1 → s ≠ 1 → ∃ g : J, g * s * g⁻¹ ∈ B) : False := by
  refine h.false_of_centralizer_kill hz φ S₀ hS₀ fun s hs h3 h1 => ?_
  obtain ⟨g, hg⟩ := hcov s hs h3 h1
  have hle : B.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({s} : Set J) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hc := hBab b hb _ hg
    show g⁻¹ * b * g⁻¹⁻¹ * s = s * (g⁻¹ * b * g⁻¹⁻¹)
    have e1 : g⁻¹ * b * g⁻¹⁻¹ * s = g⁻¹ * (b * (g * s * g⁻¹)) * g := by group
    have e2 : s * (g⁻¹ * b * g⁻¹⁻¹) = g⁻¹ * ((g * s * g⁻¹) * b) * g := by group
    rw [e1, e2, hc]
  have hcard : Nat.card (B.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card B :=
    Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g⁻¹))
  exact hB.trans (hcard ▸ Subgroup.card_dvd_of_le hle)

theorem E27Config.false_of_sylow_table (h : E27Config X K R T z) (hz : z ∈ K)
    {J : Type*} [Group J] [Finite J] (φ : ↥K ≃* J) (S₀ : Subgroup J)
    (hS₀ : Nat.card S₀ = 3 ^ (Nat.card J).factorization 3)
    (hprop : ∀ s ∈ S₀, orderOf s = 3 → 81 ∣ Nat.card ↥(S₀ ⊓ centralizer ({s} : Set J))) :
    False := by
  refine h.false_of_centralizer_kill hz φ S₀ hS₀ fun s hs h3 h1 => ?_
  have h3' : orderOf s = 3 := orderOf_eq_prime h3 h1
  exact (hprop s hs h3').trans (Subgroup.card_dvd_of_le inf_le_right)

theorem E27Config.false_of_torus_cover_amb (h : E27Config X K R T z) (hz : z ∈ K)
    {N : Type*} [Group N] [Finite N] (J : Subgroup N)
    (hnorm : ∀ g : N, ∀ x ∈ J, g * x * g⁻¹ ∈ J) (φ : ↥K ≃* J) (S₀ B : Subgroup N)
    (hSJ : S₀ ≤ J) (hBJ : B ≤ J) (hS₀ : Nat.card S₀ = 3 ^ (Nat.card J).factorization 3)
    (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB : 81 ∣ Nat.card B)
    (hcov : ∀ s ∈ S₀, s ^ 3 = 1 → s ≠ 1 → ∃ g : N, g * s * g⁻¹ ∈ B) : False := by
  have hcardS : Nat.card (S₀.subgroupOf J) = 3 ^ (Nat.card J).factorization 3 := by
    rw [← hS₀]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSJ).toEquiv
  refine h.false_of_centralizer_kill hz φ (S₀.subgroupOf J) hcardS fun s hs h3 h1 => ?_
  have hsS : (s : N) ∈ S₀ := Subgroup.mem_subgroupOf.mp hs
  obtain ⟨g, hg⟩ := hcov s hsS (by simpa using congrArg Subtype.val h3)
    (fun e => h1 (Subtype.ext e))
  set B' : Subgroup J := (B.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf J with hB'
  have hmapJ : B.map (MulAut.conj g⁻¹).toMonoidHom ≤ J := by
    rintro _ ⟨b, hb, rfl⟩
    exact hnorm g⁻¹ b (hBJ hb)
  have hle : B' ≤ centralizer ({s} : Set J) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    obtain ⟨b, hb, hbx⟩ := Subgroup.mem_subgroupOf.mp hx
    apply Subtype.ext
    have hc := hBab b hb _ hg
    have hx' : (x : N) = g⁻¹ * b * g := by
      rw [← hbx]; simp [MulAut.conj_apply]
    show (x : N) * s = s * x
    rw [hx']
    have e1 : g⁻¹ * b * g * (s : N) = g⁻¹ * (b * (g * s * g⁻¹)) * g := by group
    have e2 : (s : N) * (g⁻¹ * b * g) = g⁻¹ * ((g * s * g⁻¹) * b) * g := by group
    rw [e1, e2, hc]
  have hcard : Nat.card B' = Nat.card B := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmapJ).toEquiv]
    exact Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g⁻¹))
  exact hB.trans (hcard ▸ Subgroup.card_dvd_of_le hle)

theorem E27Config.exists_conj_central (h : E27Config X K R T z)
    {J : Type*} [Group J] [Finite J] (φ : ↥K ≃* J) (S₀ : Sylow 3 J) {t : X} (ht : t ∈ T)
    (ht1 : t ≠ 1) :
    ∃ k : J, k * φ ⟨t, h.T_le_K ht⟩ * k⁻¹ ∈ (S₀ : Subgroup J) ∧
      ∀ s ∈ (S₀ : Subgroup J), s * (k * φ ⟨t, h.T_le_K ht⟩ * k⁻¹) =
        (k * φ ⟨t, h.T_le_K ht⟩ * k⁻¹) * s := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := h.normal
  obtain ⟨S, hS⟩ := h.central t ht ht1
  have ht3 : t ^ 3 = 1 := h.elem.2 t (h.T_le_R ht)
  have hp : IsPGroup 3 (zpowers t) := by
    rintro ⟨x, hx⟩
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    refine ⟨1, Subtype.ext ?_⟩
    show (t ^ n) ^ 3 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht3, one_zpow]
  have htS : t ∈ (S : Subgroup X) := mem_sylow_of_centralizes S hp hS
  obtain ⟨P, hP⟩ := exists_sylow_subgroupOf_eq K S
  set tK : ↥K := ⟨t, h.T_le_K ht⟩ with htK
  have htP : tK ∈ (P : Subgroup K) := by
    rw [hP, Subgroup.mem_subgroupOf]; exact htS
  have hPc : ∀ x ∈ (P : Subgroup K), x * tK = tK * x := by
    intro x hx
    rw [hP, Subgroup.mem_subgroupOf] at hx
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hS hx))
  have hcard : Nat.card ((P : Subgroup K).map φ.toMonoidHom) =
      3 ^ (Nat.card J).factorization 3 := by
    rw [Subgroup.card_map_of_injective φ.injective, P.card_eq_multiplicity,
      Nat.card_congr φ.toEquiv]
  let P' : Sylow 3 J := Sylow.ofCard _ hcard
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq J P' S₀
  refine ⟨k, ?_, ?_⟩
  · rw [← hk, mem_smul_sylow_iff]
    show k⁻¹ * (k * φ tK * k⁻¹) * k ∈ (P' : Subgroup J)
    have : k⁻¹ * (k * φ tK * k⁻¹) * k = φ tK := by group
    rw [this]
    exact ⟨tK, htP, rfl⟩
  · intro s hs
    rw [← hk, mem_smul_sylow_iff] at hs
    obtain ⟨x, hx, hxs⟩ := hs
    have hs' : s = k * φ x * k⁻¹ := by
      have : k⁻¹ * s * k = φ x := hxs.symm
      calc s = k * (k⁻¹ * s * k) * k⁻¹ := by group
        _ = k * φ x * k⁻¹ := by rw [this]
    have hc := hPc x hx
    have hcφ : φ x * φ tK = φ tK * φ x := by rw [← map_mul, ← map_mul, hc]
    rw [hs']
    calc k * φ x * k⁻¹ * (k * φ tK * k⁻¹) = k * (φ x * φ tK) * k⁻¹ := by group
      _ = k * (φ tK * φ x) * k⁻¹ := by rw [hcφ]
      _ = k * φ tK * k⁻¹ * (k * φ x * k⁻¹) := by group

theorem E27Config.false_of_central_T (h : E27Config X K R T z)
    {J : Type*} [Group J] [Finite J] (φ : ↥K ≃* J) (S₀ : Subgroup J)
    (hS₀ : Nat.card S₀ = 3 ^ (Nat.card J).factorization 3) {β : Type*} (f : J → β)
    (hf : ∀ g x, f (g * x * g⁻¹) = f x) (C : Set β)
    (hC : ∀ c ∈ S₀, c ≠ 1 → (∀ s ∈ S₀, s * c = c * s) → f c ∈ C)
    (hno : ∀ a ∈ S₀, ∀ b ∈ S₀, a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a → a ≠ 1 →
      b ∉ zpowers a → ∃ i j : ℕ, a ^ i * b ^ j ≠ 1 ∧ f (a ^ i * b ^ j) ∉ C) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S₀' : Sylow 3 J := Sylow.ofCard S₀ hS₀
  have hS₀' : (S₀' : Subgroup J) = S₀ := rfl
  have hTK : T ≤ K := h.T_le_K
  let T' : Subgroup J := (T.subgroupOf K).map φ.toMonoidHom
  have hT'card : Nat.card T' = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective φ.injective]
    have := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv
    rw [this, h.card_T]; norm_num
  have hT'p : IsPGroup 3 T' := IsPGroup.of_card hT'card
  obtain ⟨Q, hQ⟩ := hT'p.exists_le_sylow
  obtain ⟨k₀, hk₀⟩ := MulAction.exists_smul_eq J Q S₀'
  have hconj : ∀ x ∈ T', k₀ * x * k₀⁻¹ ∈ S₀ := by
    intro x hx
    rw [← hS₀', ← hk₀, mem_smul_sylow_iff]
    have : k₀⁻¹ * (k₀ * x * k₀⁻¹) * k₀ = x := by group
    rw [this]
    exact hQ hx
  obtain ⟨a, haT, ha1⟩ : ∃ a ∈ T, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : T = ⊥ := (Subgroup.eq_bot_iff_forall T).2 hcon
    have h9 := h.card_T
    rw [hbot, Subgroup.card_bot] at h9
    omega
  have ha3 : a ^ 3 = 1 := h.elem.2 a (h.T_le_R haT)
  obtain ⟨b, hbT, hba⟩ : ∃ b ∈ T, b ∉ zpowers a := by
    by_contra hcon
    push Not at hcon
    have hle : T ≤ zpowers a := hcon
    have h1 : Nat.card T ≤ Nat.card (zpowers a) := Subgroup.card_le_of_le hle
    rw [h.card_T, Nat.card_zpowers] at h1
    have h2 : orderOf a ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) ha3
    omega
  have hb3 : b ^ 3 = 1 := h.elem.2 b (h.T_le_R hbT)
  have hab : a * b = b * a :=
    congrArg Subtype.val (h.elem.1.is_comm.comm ⟨a, h.T_le_R haT⟩ ⟨b, h.T_le_R hbT⟩)
  let aK : ↥K := ⟨a, hTK haT⟩
  let bK : ↥K := ⟨b, hTK hbT⟩
  have hmemT : ∀ u : ↥K, (u : X) ∈ T → φ u ∈ T' := fun u hu =>
    ⟨u, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  set cj : MulAut J := MulAut.conj k₀ with hcj
  have hcjapp : ∀ x, cj x = k₀ * x * k₀⁻¹ := fun x => rfl
  have haS : cj (φ aK) ∈ S₀ := by rw [hcjapp]; exact hconj _ (hmemT aK haT)
  have hbS : cj (φ bK) ∈ S₀ := by rw [hcjapp]; exact hconj _ (hmemT bK hbT)
  have haK3 : aK ^ 3 = 1 := Subtype.ext ha3
  have hbK3 : bK ^ 3 = 1 := Subtype.ext hb3
  have habK : aK * bK = bK * aK := Subtype.ext hab
  have haK1 : aK ≠ 1 := fun e => ha1 (congrArg Subtype.val e)
  have hbK : bK ∉ zpowers aK := by
    rintro ⟨n, hn⟩
    apply hba
    refine ⟨n, ?_⟩
    have := congrArg Subtype.val hn
    simpa using this
  have hcomb : ∀ i j : ℕ, cj (φ aK) ^ i * cj (φ bK) ^ j = cj (φ (aK ^ i * bK ^ j)) := by
    intro i j
    simp [map_mul, map_pow]
  obtain ⟨i, j, hne, hfC⟩ := hno (cj (φ aK)) haS (cj (φ bK)) hbS
    (by rw [← map_pow, ← map_pow, haK3, map_one, map_one])
    (by rw [← map_pow, ← map_pow, hbK3, map_one, map_one])
    (by rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, habK])
    (by
      intro e
      apply haK1
      have := (cj.injective (e.trans (map_one cj).symm))
      exact φ.injective (this.trans (map_one φ).symm))
    (by
      rintro ⟨n, hn⟩
      apply hbK
      refine ⟨n, ?_⟩
      have h1 : cj (φ aK ^ n) = cj (φ bK) := by rw [map_zpow]; exact hn
      have h2 := cj.injective h1
      apply φ.injective
      rw [map_zpow]
      exact h2)
  rw [hcomb] at hne hfC
  set uK : ↥K := aK ^ i * bK ^ j with huK
  have huT : (uK : X) ∈ T := by
    simp only [huK, Subgroup.coe_mul, Subgroup.coe_pow]
    exact T.mul_mem (T.pow_mem haT i) (T.pow_mem hbT j)
  have hu1 : (uK : X) ≠ 1 := fun e => hne (by
    have : uK = 1 := Subtype.ext e
    rw [this, map_one, map_one])
  obtain ⟨k, hkS, hkc⟩ := h.exists_conj_central φ S₀' huT hu1
  have hCk : f (k * φ ⟨(uK : X), h.T_le_K huT⟩ * k⁻¹) ∈ C := by
    refine hC _ hkS (fun e => ?_) hkc
    have h1 : φ ⟨(uK : X), h.T_le_K huT⟩ = 1 := by
      calc φ ⟨(uK : X), h.T_le_K huT⟩
          = k⁻¹ * (k * φ ⟨(uK : X), h.T_le_K huT⟩ * k⁻¹) * k := by group
        _ = k⁻¹ * 1 * k := by rw [e]
        _ = 1 := by group
    have h0 := φ.injective (h1.trans (map_one φ).symm)
    exact hu1 (congrArg Subtype.val h0)
  apply hfC
  rw [hcjapp, hf, ← hf k]
  exact hCk

end Cover

end CFSG.HardMathSupport.Foote.E27
