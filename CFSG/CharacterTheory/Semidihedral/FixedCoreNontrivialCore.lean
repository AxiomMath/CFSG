module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialLocal
public import CFSG.Walter.Transitivity.Coprime
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

variable {G : Type*} [Group G]

theorem mem_normalizer_of_conj_mem [Finite G] {H : Subgroup G} {g : G}
    (hg : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hg x, fun hx => ?_⟩
  let φ : H → H := fun y => ⟨g * y * g⁻¹, hg y y.2⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (by simpa [φ] using this)
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hφ) ⟨g * x * g⁻¹, hx⟩
  have hyx : (y : G) = x := by
    have := congrArg Subtype.val hy
    simpa [φ] using this
  exact hyx ▸ y.2

theorem isPGroup_of_isPiSubgroup_singleton [Finite G] {ℓ : Nat.Primes} {S : Subgroup G}
    (hS : IsPiSubgroup {ℓ} S) : IsPGroup (ℓ : ℕ) S := by
  have hpos : Nat.card S ≠ 0 := Nat.card_pos.ne'
  have heq := Nat.eq_prime_pow_of_unique_prime_dvd hpos (p := (ℓ : ℕ)) fun {d} hd hdvd => by
    have h2 : (⟨d, hd⟩ : Nat.Primes) = ℓ := hS ⟨d, hd⟩ hdvd
    exact congrArg Subtype.val h2
  exact IsPGroup.of_card heq

theorem isPiSubgroup_zpowers {ℓ : Nat.Primes} {u : G} (hu : orderOf u = ℓ) :
    IsPiSubgroup {ℓ} (Subgroup.zpowers u) := by
  intro p hp
  rw [Nat.card_zpowers, hu] at hp
  rw [Set.mem_singleton_iff]
  exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.2 ℓ.2).mp hp)

theorem exists_mem_normalizer_not_mem_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    {Q P : Subgroup G} (hP : IsPGroup p P) (hQP : Q ≤ P) (hne : Q ≠ P) :
    ∃ y ∈ P, y ∈ Subgroup.normalizer (Q : Set G) ∧ y ∉ Q := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt : Q.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hne ?_
    exact le_antisymm hQP (Subgroup.subgroupOf_eq_top.mp h)
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := P) _ hlt
  obtain ⟨y, hyN, hyQ⟩ := IsConcreteLE.exists_of_lt hgrow
  rw [← Subgroup.subgroupOf_normalizer_eq hQP, Subgroup.mem_subgroupOf] at hyN
  exact ⟨y, y.2, hyN, fun h => hyQ (Subgroup.mem_subgroupOf.mpr h)⟩

theorem ne_inv_of_odd {x : G} (hx : Odd (orderOf x)) (hx1 : x ≠ 1) : x⁻¹ ≠ x := by
  intro hinv
  apply hx1
  apply eq_one_of_mul_self_eq_one_of_odd hx
  calc x * x = x⁻¹ * x := by rw [hinv]
    _ = 1 := inv_mul_cancel x

variable {t s d : G} {J B W : Subgroup G}

namespace LocalData

variable (h : LocalData t s d J B W)
include h

theorem mem_V_cases {v : G} (hv : v ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers s) :
    v = 1 ∨ v = t ∨ v = s ∨ v = t * s := by
  have hcomm : ∀ a ∈ Subgroup.zpowers t, ∀ b ∈ Subgroup.zpowers s, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow h.ts i j)
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm hv
  rcases zpowers_cases_of_mul_self h.t_sq a ha with ha1 | ha1 <;>
    rcases zpowers_cases_of_mul_self h.s_sq b hb with hb1 | hb1 <;> rw [ha1, hb1]
  · left; exact one_mul 1
  · right; right; left; exact one_mul s
  · right; left; exact mul_one t
  · right; right; right; rfl

theorem inv_of_ne {v : G} (hv : v ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers s) (hv1 : v ≠ 1)
    (hvt : v ≠ t) : ∀ x ∈ B, v * x * v⁻¹ = x⁻¹ := by
  intro x hx
  have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp (h.B_le hx)
  rcases h.mem_V_cases hv with rfl | rfl | rfl | rfl
  · exact absurd rfl hv1
  · exact absurd rfl hvt
  · exact h.s_inv x hx
  · calc t * s * x * (t * s)⁻¹ = t * (s * x * s⁻¹) * t⁻¹ := by group
      _ = t * x⁻¹ * t⁻¹ := by rw [h.s_inv x hx]
      _ = x⁻¹ := by
        have : t * x⁻¹ = x⁻¹ * t := by
          rw [show t * x⁻¹ = (x * t⁻¹)⁻¹ by group, show x⁻¹ * t = (t⁻¹ * x)⁻¹ by group]
          congr 1
          have := hxt
          calc x * t⁻¹ = t⁻¹ * (t * x) * t⁻¹ := by group
            _ = t⁻¹ * (x * t) * t⁻¹ := by rw [this]
            _ = t⁻¹ * x := by group
        rw [this]
        group

theorem oddCore_inf_B_eq_bot [Finite G] (F : Subgroup G)
    (hVF : Subgroup.zpowers t ⊔ Subgroup.zpowers s ≤ F)
    (hV4 : Nat.card (Subgroup.zpowers t ⊔ Subgroup.zpowers s : Subgroup G) = 4)
    {g : G} (hgF : g ∈ F) (hgt : g * t * g⁻¹ = s)
    (hgV : g ∈ Subgroup.normalizer ((Subgroup.zpowers t ⊔ Subgroup.zpowers s :
      Subgroup G) : Set G))
    (hconf : ∀ u ∈ B, u ≠ 1 →
      Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer ({t} : Set G)) :
    (CFSG.pPrimeCore 2 F).map F.subtype ⊓ B = ⊥ := by
  classical
  set V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s with hVdef
  set X : Subgroup G := (CFSG.pPrimeCore 2 F).map F.subtype with hXdef
  have hXF : X ≤ F := Subgroup.map_subtype_le _
  have hXcard : Nat.card X = Nat.card (CFSG.pPrimeCore 2 F) :=
    Subgroup.card_map_of_injective F.subtype_injective
  have hXodd : Odd (Nat.card X) := by
    rw [hXcard]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := F))
  have hXn : ∀ f ∈ F, ∀ x ∈ X, f * x * f⁻¹ ∈ X := by
    intro f hf x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hn := (CFSG.pPrimeCore_normal (p := 2) (G := F)).conj_mem y hy ⟨f, hf⟩
    exact ⟨_, hn, rfl⟩
  have hXoddx : ∀ x ∈ X, Odd (orderOf x) := by
    intro x hx
    have h1 : orderOf x ∣ Nat.card X := by
      have := Subgroup.orderOf_dvd_natCard X hx
      exact this
    exact hXodd.of_dvd_nat h1
  have hVX : V ≤ Subgroup.normalizer (X : Set G) := fun v hv =>
    mem_normalizer_of_conj_mem fun x hx => hXn v (hVF hv) x hx
  by_contra hXB
  obtain ⟨⟨u₀, hu₀⟩, hu₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXB
  have hcardXB : 1 < Nat.card (X ⊓ B : Subgroup G) := by
    have : Nontrivial (X ⊓ B : Subgroup G) := ⟨⟨⟨u₀, hu₀⟩, 1, hu₀1⟩⟩
    exact Finite.one_lt_card
  set ℓ := (Nat.card (X ⊓ B : Subgroup G)).minFac with hℓdef
  have hℓp : ℓ.Prime := Nat.minFac_prime hcardXB.ne'
  have : Fact ℓ.Prime := ⟨hℓp⟩
  obtain ⟨⟨u, hu⟩, huo⟩ := exists_prime_orderOf_dvd_card' (G := (X ⊓ B : Subgroup G)) ℓ
    (Nat.minFac_dvd _)
  rw [Subgroup.orderOf_mk] at huo
  have huX : u ∈ X := (Subgroup.mem_inf.mp hu).1
  have huB : u ∈ B := (Subgroup.mem_inf.mp hu).2
  have hu1 : u ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at huo
    exact hℓp.one_lt.ne huo
  have hℓodd : ℓ ≠ 2 := by
    intro h2
    have := hXoddx u huX
    rw [huo, h2] at this
    exact absurd this (by decide)
  set R₀ : Subgroup G := Subgroup.zpowers u with hR₀
  set u₁ : G := g * u * g⁻¹ with hu₁
  set R₂ : Subgroup G := Subgroup.zpowers u₁ with hR₂
  have hut : u * t = t * u := Subgroup.mem_centralizer_singleton_iff.mp (h.B_le huB)
  have hVR₀ : ∀ v ∈ V, v * u * v⁻¹ = u ∨ v * u * v⁻¹ = u⁻¹ := by
    intro v hv
    rcases em (v = 1) with hv1 | hv1
    · left; rw [hv1]; group
    rcases em (v = t) with hvt | hvt
    · left; rw [hvt, ← hut]; group
    · right; exact h.inv_of_ne hv hv1 hvt u huB
  have hVR₀N : V ≤ Subgroup.normalizer (R₀ : Set G) := by
    intro v hv
    apply mem_normalizer_of_conj_mem
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    rcases hVR₀ v hv with h1 | h1 <;> rw [h1]
    · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) k
    · exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers u)) k
  have hgVinv : g⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hgV
  have hVR₂N : V ≤ Subgroup.normalizer (R₂ : Set G) := by
    intro v hv
    have hv' : g⁻¹ * v * g ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp hgVinv v).mp hv
      simpa using this
    apply mem_normalizer_of_conj_mem
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    have hconj : v * u₁ * v⁻¹ = g * ((g⁻¹ * v * g) * u * (g⁻¹ * v * g)⁻¹) * g⁻¹ := by
      rw [hu₁]; group
    rw [hconj]
    rcases hVR₀ _ hv' with h1 | h1 <;> rw [h1]
    · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers u₁) k
    · have : g * u⁻¹ * g⁻¹ = u₁⁻¹ := by rw [hu₁]; group
      rw [this]
      exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers u₁)) k
  have hR₀X : R₀ ≤ X := by
    rw [hR₀, Subgroup.zpowers_le]
    exact huX
  have hR₂X : R₂ ≤ X := by
    rw [hR₂, Subgroup.zpowers_le]
    exact hXn g hgF u huX
  have hu₁o : orderOf u₁ = ℓ := by rw [hu₁, ← MulAut.conj_apply, MulEquiv.orderOf_eq, huo]
  have hsolv : Group.IsSolvable X := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hXodd
  have hcop : Nat.Coprime (Nat.card V) (Nat.card X) := by
    rw [hV4, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact (Nat.coprime_two_left.mpr hXodd).pow_left 2
  set ℓ' : Nat.Primes := ⟨ℓ, hℓp⟩
  obtain ⟨S, hSX, hSπ, hVS, hR₀S, c, hc, hR₂S⟩ :=
    CFSG.Walter.Transitivity.exists_conjBy_of_coprime_action (π := {ℓ'}) hVX hsolv hcop hR₀X
      hR₂X (isPiSubgroup_zpowers (ℓ := ℓ') huo) (isPiSubgroup_zpowers (ℓ := ℓ') hu₁o)
      hVR₀N hVR₂N
  have hSp : IsPGroup ℓ S := isPGroup_of_isPiSubgroup_singleton hSπ
  obtain ⟨hcX, hcV⟩ := Subgroup.mem_inf.mp hc
  have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hct : c * t = t * c := (Subgroup.mem_centralizer_iff.mp hcV t htV).symm
  obtain ⟨u₂, hu₂S, hu₂eq⟩ : ∃ y ∈ S, c * y * c⁻¹ = u₁ := by
    obtain ⟨y, hy, hyu⟩ := hR₂S (Subgroup.mem_zpowers u₁)
    exact ⟨y, hy, hyu⟩
  have htu₁ : t * u₁ * t⁻¹ = u₁⁻¹ := by
    have hv : g⁻¹ * t * g ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp hgVinv t).mp htV
      simpa using this
    have hv1 : g⁻¹ * t * g ≠ 1 := by
      intro h1
      apply h.t_ne_one
      calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have hvt : g⁻¹ * t * g ≠ t := by
      intro h1
      apply h.s_ne
      rw [← hgt]
      calc g * t * g⁻¹ = g * (g⁻¹ * t * g) * g⁻¹ := by rw [h1]
        _ = t := by group
    have hinv := h.inv_of_ne hv hv1 hvt u huB
    calc t * u₁ * t⁻¹ = g * ((g⁻¹ * t * g) * u * (g⁻¹ * t * g)⁻¹) * g⁻¹ := by rw [hu₁]; group
      _ = g * u⁻¹ * g⁻¹ := by rw [hinv]
      _ = u₁⁻¹ := by rw [hu₁]; group
  have htu₂ : t * u₂ * t⁻¹ = u₂⁻¹ := by
    have : u₂ = c⁻¹ * u₁ * c := by rw [← hu₂eq]; group
    rw [this]
    have hct' : c⁻¹ * t = t * c⁻¹ := by
      calc c⁻¹ * t = c⁻¹ * (t * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * t) * c⁻¹ := by rw [hct]
        _ = t * c⁻¹ := by group
    calc t * (c⁻¹ * u₁ * c) * t⁻¹ = c⁻¹ * (t * u₁ * t⁻¹) * c := by
          rw [show t * (c⁻¹ * u₁ * c) * t⁻¹ = (t * c⁻¹) * u₁ * (c * t⁻¹) by group, ← hct']
          rw [show c * t⁻¹ = t⁻¹ * c by
            calc c * t⁻¹ = t⁻¹ * (t * c) * t⁻¹ := by group
              _ = t⁻¹ * (c * t) * t⁻¹ := by rw [hct]
              _ = t⁻¹ * c := by group]
          group
      _ = (c⁻¹ * u₁ * c)⁻¹ := by rw [htu₁]; group
  have hu₂1 : u₂ ≠ 1 := by
    intro h1
    apply hu1
    have hu₁1 : u₁ = 1 := by rw [← hu₂eq, h1]; group
    calc u = g⁻¹ * u₁ * g := by rw [hu₁]; group
      _ = 1 := by rw [hu₁1]; group
  set Q : Subgroup G := S ⊓ Subgroup.centralizer ({t} : Set G) with hQdef
  have hQS : Q ≤ S := inf_le_left
  have huQ : u ∈ Q := Subgroup.mem_inf.mpr ⟨hR₀S (Subgroup.mem_zpowers u),
    Subgroup.mem_centralizer_singleton_iff.mpr hut⟩
  have hu₂odd : Odd (orderOf u₂) := hXoddx u₂ (hSX hu₂S)
  have hQne : Q ≠ S := by
    intro hQS'
    have hu₂Q : u₂ ∈ Q := hQS' ▸ hu₂S
    have hc2 : u₂ * t = t * u₂ :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hu₂Q).2
    have : t * u₂ * t⁻¹ = u₂ := by rw [← hc2]; group
    rw [htu₂] at this
    exact ne_inv_of_odd hu₂odd hu₂1 this
  obtain ⟨y, hyS, hyN, hyQ⟩ := exists_mem_normalizer_not_mem_of_isPGroup hSp hQS hQne
  set z : G := y⁻¹ * (t * y * t⁻¹) with hzdef
  have htS : t ∈ Subgroup.normalizer (S : Set G) := hVS htV
  have htyS : t * y * t⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp htS y).mp hyS
  have hzS : z ∈ S := S.mul_mem (S.inv_mem hyS) htyS
  have htQ : t ∈ Subgroup.normalizer (Q : Set G) := by
    apply mem_normalizer_of_conj_mem
    intro x hx
    obtain ⟨hxS, hxt⟩ := Subgroup.mem_inf.mp hx
    have hxt' : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxt
    have : t * x * t⁻¹ = x := by rw [← hxt']; group
    rw [this]
    exact hx
  have htyN : t * y * t⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ htQ hyN) (Subgroup.inv_mem _ htQ)
  have hzN : z ∈ Subgroup.normalizer (Q : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hyN) htyN
  have hz1 : z ≠ 1 := by
    intro h1
    apply hyQ
    have : t * y * t⁻¹ = y := by
      have := h1
      rw [hzdef] at this
      calc t * y * t⁻¹ = y * (y⁻¹ * (t * y * t⁻¹)) := by group
        _ = y := by rw [this, mul_one]
    refine Subgroup.mem_inf.mpr ⟨hyS, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc y * t = t * y * t⁻¹ * t := by rw [this]
      _ = t * y := by group
  have ht2 := h.t_inv_eq
  have htz : t * z * t⁻¹ = z⁻¹ := by
    have e1 : t * z * t⁻¹ = t * y⁻¹ * t * y * (t⁻¹ * t⁻¹) := by rw [hzdef]; group
    have e2 : z⁻¹ = t * y⁻¹ * t⁻¹ * y := by rw [hzdef]; group
    rw [e1, e2, ht2, h.t_sq, mul_one]
  have hzodd : Odd (orderOf z) := hXoddx z (hSX hzS)
  have hzc : ∀ x ∈ Q, z * x = x * z := by
    intro x hx
    have hzx : z * x * z⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hzN x).mp hx
    have hfix : ∀ q ∈ Q, t * q * t⁻¹ = q := by
      intro q hq
      have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hq).2
      rw [← this]; group
    have h1 : t * (z * x * z⁻¹) * t⁻¹ = z⁻¹ * x * z := by
      calc t * (z * x * z⁻¹) * t⁻¹ = (t * z * t⁻¹) * (t * x * t⁻¹) * (t * z * t⁻¹)⁻¹ := by
            group
        _ = z⁻¹ * x * z := by rw [htz, hfix x hx, inv_inv]
    rw [hfix _ hzx] at h1
    have h2 : z * z * x = x * (z * z) := by
      calc z * z * x = z * (z * x * z⁻¹) * z := by group
        _ = z * (z⁻¹ * x * z) * z := by rw [h1]
        _ = x * (z * z) := by group
    have hzz : z ∈ Subgroup.zpowers (z * z) := mem_zpowers_sq_of_odd hzodd
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzz
    rw [← hk]
    exact ((Commute.zpow_left h2 k))
  have hzu : z ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hzc u huQ)
  have hzt := Subgroup.mem_centralizer_singleton_iff.mp (hconf u huB hu1 hzu)
  have : t * z * t⁻¹ = z := by rw [← hzt]; group
  rw [htz] at this
  exact ne_inv_of_odd hzodd hz1 this

theorem oddCore_le [Finite G] (W₀ : Subgroup G) (hW₀ : W₀ ≤ W) (hne : W₀ ≠ ⊥)
    (F : Subgroup G) (hFN : F ≤ Subgroup.normalizer (W₀ : Set G))
    (hVF : Subgroup.zpowers t ⊔ Subgroup.zpowers s ≤ F)
    (hV4 : Nat.card (Subgroup.zpowers t ⊔ Subgroup.zpowers s : Subgroup G) = 4)
    {g g' : G} (hgF : g ∈ F) (hg'F : g' ∈ F) (hgt : g * t * g⁻¹ = s)
    (hg't : g' * t * g'⁻¹ = t * s)
    (hgV : g ∈ Subgroup.normalizer ((Subgroup.zpowers t ⊔ Subgroup.zpowers s :
      Subgroup G) : Set G))
    (hgW : g ∈ Subgroup.normalizer (W : Set G)) (hg'W : g' ∈ Subgroup.normalizer (W : Set G))
    (hconf : ∀ u ∈ B, u ≠ 1 →
      Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer ({t} : Set G)) :
    (CFSG.pPrimeCore 2 F).map F.subtype ≤ W := by
  classical
  set V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s with hVdef
  set X : Subgroup G := (CFSG.pPrimeCore 2 F).map F.subtype with hXdef
  have hXF : X ≤ F := Subgroup.map_subtype_le _
  have hXcard : Nat.card X = Nat.card (CFSG.pPrimeCore 2 F) :=
    Subgroup.card_map_of_injective F.subtype_injective
  have hXodd : Odd (Nat.card X) := by
    rw [hXcard]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := F))
  have hXn : ∀ f ∈ F, ∀ x ∈ X, f * x * f⁻¹ ∈ X := by
    intro f hf x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hn := (CFSG.pPrimeCore_normal (p := 2) (G := F)).conj_mem y hy ⟨f, hf⟩
    exact ⟨_, hn, rfl⟩
  have hXoddx : ∀ x ∈ X, Odd (orderOf x) := fun x hx =>
    hXodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard X hx)
  have hXB := h.oddCore_inf_B_eq_bot F hVF hV4 hgF hgt hgV hconf
  have hCt : ∀ x ∈ X, x * t = t * x → x ∈ W := by
    intro x hx hxt
    have hxC : x ∈ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hxt
    have hxWB := h.mem_sup_of_odd_of_mem_normalizer W₀ hW₀ hne hxC (hFN (hXF hx)) (hXoddx x hx)
    obtain ⟨w, hw, b, hb, rfl⟩ := exists_mul_of_mem_sup (fun w hw b hb =>
      (h.B_comm_W b hb w hw).symm) hxWB
    have hsF : s ∈ F := hVF (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
    have hsx : s * (w * b) * s⁻¹ ∈ X := hXn s hsF _ hx
    have hsx' : s * (w * b) * s⁻¹ = w * b⁻¹ := by
      have hws : s * w * s⁻¹ = w := by rw [← h.W_comm_s w hw]; group
      calc s * (w * b) * s⁻¹ = (s * w * s⁻¹) * (s * b * s⁻¹) := by group
        _ = w * b⁻¹ := by rw [hws, h.s_inv b hb]
    rw [hsx'] at hsx
    have hb2 : b⁻¹ * b⁻¹ ∈ X ⊓ B := by
      refine Subgroup.mem_inf.mpr ⟨?_, B.mul_mem (B.inv_mem hb) (B.inv_mem hb)⟩
      have : b⁻¹ * b⁻¹ = (w * b)⁻¹ * (w * b⁻¹) := by group
      rw [this]
      exact X.mul_mem (X.inv_mem hx) hsx
    rw [hXB, Subgroup.mem_bot] at hb2
    have hb1 : b = 1 := by
      have : b⁻¹ = 1 := eq_one_of_mul_self_eq_one_of_odd (by rw [orderOf_inv]; exact h.B_odd b hb)
        hb2
      exact inv_eq_one.mp this
    rw [hb1, mul_one]
    exact hw
  have hconj : ∀ k ∈ F, k ∈ Subgroup.normalizer (W : Set G) → ∀ x ∈ X,
      x * (k * t * k⁻¹) = (k * t * k⁻¹) * x → x ∈ W := by
    intro k hk hkW x hx hxc
    have hy : k⁻¹ * x * k ∈ X := by
      have := hXn k⁻¹ (F.inv_mem hk) x hx
      simpa using this
    have hyt : k⁻¹ * x * k * t = t * (k⁻¹ * x * k) := by
      calc k⁻¹ * x * k * t = k⁻¹ * (x * (k * t * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * t * k⁻¹) * x) * k := by rw [hxc]
        _ = t * (k⁻¹ * x * k) := by group
    have hyW := hCt _ hy hyt
    have : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
    rw [this]
    exact (Subgroup.mem_normalizer_iff.mp hkW _).mp hyW
  have hVX : V ≤ Subgroup.normalizer (X : Set G) := fun v hv =>
    mem_normalizer_of_conj_mem fun x hx => hXn v (hVF hv) x hx
  have hpow : ∀ v : V, v ^ 2 = 1 := by
    rintro ⟨v, hv⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
    rcases h.mem_V_cases hv with rfl | rfl | rfl | rfl
    · exact one_mul 1
    · exact h.t_sq
    · exact h.s_sq
    · calc t * s * (t * s) = t * (s * t) * s := by group
        _ = t * (t * s) * s := by rw [h.ts]
        _ = (t * t) * (s * s) := by group
        _ = 1 := by rw [h.t_sq, h.s_sq, one_mul]
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    2 Nat.prime_two V X hpow (by rw [hV4]; norm_num) (fun h2 => (Nat.not_even_iff_odd.mpr hXodd)
      (even_iff_two_dvd.mpr h2)) hVX
  rw [hgen]
  refine iSup_le fun ⟨v, hv⟩ => iSup_le fun hv1 => ?_
  have hv1' : v ≠ 1 := fun h' => hv1 (Subtype.ext h')
  intro x hx
  obtain ⟨hxX, hxv⟩ := Subgroup.mem_inf.mp hx
  have hxv' : x * v = v * x := Subgroup.mem_centralizer_singleton_iff.mp hxv
  rcases h.mem_V_cases hv with rfl | rfl | rfl | rfl
  · exact absurd rfl hv1'
  · exact hCt x hxX hxv'
  · exact hconj g hgF hgW x hxX (by rw [hgt]; exact hxv')
  · exact hconj g' hg'F hg'W x hxX (by rw [hg't]; exact hxv')

end LocalData

end CFSG.Semidihedral.FixedCoreNontrivial
