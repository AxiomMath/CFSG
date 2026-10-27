module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSec5Unit
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34InvSylow
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34InvTools

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_of_mul_self_mem_centralizer {K P : Subgroup G} (hP : IsSylowTwoIn P K)
    {j : G} (hjK : j ∈ K) (hjN : j ∈ normalizer (P : Set G))
    (hj2 : j * j ∈ centralizer (K : Set G)) :
    ∃ p ∈ P, p⁻¹ * j ∈ centralizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, b, hb, hN⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos j).ne'
  have hcop : Nat.Coprime (2 ^ a) b := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hb)
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hcop (by rintro rfl; simp at hb)
  set e := j ^ (2 ^ a) with he
  have heo : Odd (orderOf e) := by
    have h1 : orderOf e ∣ b := orderOf_dvd_of_pow_eq_one (by
      rw [he, ← pow_mul, ← hN, pow_orderOf_eq_one])
    exact Odd.of_dvd_nat hb h1
  have he2 : e * e ∈ centralizer (K : Set G) := by
    rw [he, ← (Commute.refl j).mul_pow]
    exact pow_mem hj2 _
  obtain ⟨m, hm⟩ := HSFLit.L34Inv.eq_pow_mul_self_of_odd heo
  have heC : e ∈ centralizer (K : Set G) := by rw [hm]; exact pow_mem he2 m
  set p := j * (e ^ k)⁻¹ with hp
  have hjc : Commute j (e ^ k)⁻¹ := ((Commute.self_pow j (2 ^ a)).pow_right k).inv_right
  have hp2 : p ^ (2 ^ a) = 1 := by
    rw [hp, hjc.mul_pow, inv_pow, ← pow_mul, he, ← pow_mul]
    have hmod : 2 ^ a ≡ 2 ^ a * (k * 2 ^ a) [MOD orderOf j] := by
      have h0 := Nat.ModEq.mul_left' (2 ^ a) (Nat.ModEq.symm hk)
      rw [mul_one, show 2 ^ a * (2 ^ a * k) = 2 ^ a * (k * 2 ^ a) by ring, ← hN] at h0
      exact h0
    rw [(pow_eq_pow_iff_modEq.mpr hmod), mul_inv_cancel]
  have hpK : p ∈ K := mul_mem hjK (inv_mem (pow_mem (pow_mem hjK _) _))
  have hpN : p ∈ normalizer (P : Set G) :=
    mul_mem hjN (inv_mem (pow_mem (pow_mem hjN _) _))
  have hp2g : IsPGroup 2 (zpowers p) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hp2)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hi])
  have hXp : IsPGroup 2 ↥(zpowers p ⊔ P) :=
    hp2g.to_sup_of_normal_right' (GrS4.isPGroup_of_isSylowTwoIn hP) (zpowers_le.mpr hpN)
  have hpP : p ∈ P := HSFLit.L34Inv.le_of_isSylowTwoIn hP (sup_le (zpowers_le.mpr hpK) hP.1) hXp
    (le_sup_right.trans le_normalizer) (mem_sup_left (mem_zpowers p))
  refine ⟨p, hpP, ?_⟩
  rw [show p⁻¹ * j = e ^ k by rw [hp]; group]
  exact pow_mem heC k

theorem exists_commutator_involution
    {K P : Subgroup G} {x : G} (hK : ⁅K, K⁆ = K)
    (hL : IsL34Type (K ⧸ Open.fusionZStar K)) (hx : IsL34Unitary K x) (hP : IsSylowTwoIn P K)
    (hxP : x ∈ normalizer (P : Set G)) (hZ2 : Nat.card ↥(P ⊓ zStarIn K) = 2) :
    ∃ v ∈ P ⊓ centralizer (P : Set G), v⁻¹ * x⁻¹ * v * x ∈ P ∧ v⁻¹ * x⁻¹ * v * x ≠ 1 ∧
      v⁻¹ * x⁻¹ * v * x * (v⁻¹ * x⁻¹ * v * x) = 1 ∧
      v⁻¹ * x⁻¹ * v * x * x = x * (v⁻¹ * x⁻¹ * v * x) ∧
      ∀ s ∈ normalizer (P : Set G), s * x = x * s →
        s * (v⁻¹ * x⁻¹ * v * x) * s⁻¹ = v⁻¹ * x⁻¹ * v * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  have hZ : ∀ z ∈ P ⊓ zStarIn K, z * z = 1 := by
    intro z hz
    have h1 : orderOf z ∣ 2 := hZ2 ▸ Subgroup.orderOf_dvd_natCard _ hz
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hβ, hT⟩ := exists_standard hK hL hx hP hxP
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  have hk2 := ker_mul_self_of_elem hP hqker hZ
  have hx2 : x * x = 1 := hx.2.1
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxq : ∀ {y : G} (hy : y ∈ P),
      q (jq K ⟨x⁻¹ * y * x, hP.1 (conj_mem_of_mem_normalizer hxP hy)⟩) =
        r₄ * q (jq K ⟨y, hP.1 hy⟩) * r₄⁻¹ := fun hy => by
    rw [← hβ, betaHat_jq]
    rfl
  obtain ⟨v, hvP, hvK, hv⟩ := exists_over hQ hT (tg_mem_T0 8 (by norm_num))
  have hv0 : q (jq K ⟨v, hP.1 hvP⟩) ∈ Z0 := by
    rw [show (⟨v, hP.1 hvP⟩ : K) = ⟨v, hvK⟩ from rfl, hv]
    exact mem_Z0.2 ⟨8, by simp, rfl⟩
  have hvA : v ∈ P ⊓ centralizer (P : Set G) :=
    mem_inf.mpr ⟨hvP, (mem_centralizer_P_iff hP hQ hk2 hT hvP).2 hv0⟩
  set z₁ := v⁻¹ * x⁻¹ * v * x with hz₁
  have hcP : z₁ ∈ P := by
    have := P.mul_mem (P.inv_mem hvP) (conj_mem_of_mem_normalizer hxP hvP)
    rwa [show v⁻¹ * (x⁻¹ * v * x) = v⁻¹ * x⁻¹ * v * x by group] at this
  have hq8 : q (jq K ⟨z₁, hP.1 hcP⟩) = wordPerm (tg 4) := by
    have e1 : (⟨z₁, hP.1 hcP⟩ : K) = (⟨v, hvK⟩ : K)⁻¹ *
        ⟨x⁻¹ * v * x, hP.1 (conj_mem_of_mem_normalizer hxP hvP)⟩ := Subtype.ext (by
      show v⁻¹ * x⁻¹ * v * x = v⁻¹ * (x⁻¹ * v * x)
      group)
    rw [e1, map_mul, map_mul, map_inv, map_inv, hxq hvP,
      show (⟨v, hP.1 hvP⟩ : K) = ⟨v, hvK⟩ from rfl, hv, unit_parts.2.2.2]
    group
  have hz₁1 : z₁ ≠ 1 := by
    intro h
    have h1 : q (jq K ⟨z₁, hP.1 hcP⟩) = 1 := by
      rw [show (⟨z₁, hP.1 hcP⟩ : K) = 1 from Subtype.ext h, map_one, map_one]
    rw [hq8] at h1
    exact qc_ne_one h1
  set A := P ⊓ centralizer (P : Set G) with hA
  set B := A ⊓ centralizer ({x} : Set G) with hB
  have hAeq : A = pullP K P hP.1 (Z0.comap q) := by
    ext y
    rw [mem_pullP]
    constructor
    · rintro ⟨hy, hc⟩
      exact ⟨hy, (mem_centralizer_P_iff hP hQ hk2 hT hy).1 hc⟩
    · rintro ⟨hy, hyZ⟩
      exact ⟨hy, (mem_centralizer_P_iff hP hQ hk2 hT hy).2 hyZ⟩
  have hZ0T : Z0.comap q ≤ T0.comap q := comap_mono fun y hy => hy.2
  obtain ⟨ζ, -⟩ := exists_zeta hP hqker
  have hAc : Nat.card A = 8 := by
    rw [hAeq, card_pullP hP2 hT hZ0T, card_comap_eq q Z0 (fun y hy => hqsurj y (T0_le_S hy.2)),
      card_Z0, ← Nat.card_congr ζ.toEquiv, hZ2]
  have hBc : Nat.card B = 4 := by
    rw [hB, hA, (unitaryCenter G K P x hK hL hx hP hxP hZ).1, hZ2]
  have hAx : ∀ a ∈ A, x⁻¹ * a * x ∈ A := by
    intro a ha
    obtain ⟨haP, haC⟩ := mem_inf.mp ha
    refine mem_inf.mpr ⟨conj_mem_of_mem_normalizer hxP haP, mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' : x * y * x⁻¹ ∈ P := (mem_normalizer_iff.mp hxP y).mp hy
    have h1 : x * y * x⁻¹ * a = a * (x * y * x⁻¹) := mem_centralizer_iff.mp haC _ hy'
    calc y * (x⁻¹ * a * x) = x⁻¹ * (x * y * x⁻¹ * a) * x := by group
      _ = x⁻¹ * (a * (x * y * x⁻¹)) * x := by rw [h1]
      _ = x⁻¹ * a * x * y := by group
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    mem_centralizer_iff.mp (mem_inf.mp hb).2 a (mem_inf.mp ha).1
  set f : G → G := fun a => a⁻¹ * x⁻¹ * a * x with hf
  have hfA : ∀ a ∈ A, f a ∈ A := fun a ha => by
    have h1 := A.mul_mem (A.inv_mem ha) (hAx a ha)
    rwa [show a⁻¹ * (x⁻¹ * a * x) = a⁻¹ * x⁻¹ * a * x by group] at h1
  have hfmul : ∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b := by
    intro a ha b hb
    have hc1 : (x⁻¹ * a * x) * b = b * (x⁻¹ * a * x) := hAab _ (hAx a ha) b hb
    have hc2 : a⁻¹ * (x⁻¹ * b * x) = (x⁻¹ * b * x) * a⁻¹ := hAab _ (A.inv_mem ha) _ (hAx b hb)
    simp only [hf]
    calc (a * b)⁻¹ * x⁻¹ * (a * b) * x = b⁻¹ * (a⁻¹ * (x⁻¹ * a * x)) * (x⁻¹ * b * x) := by group
      _ = b⁻¹ * a⁻¹ * ((x⁻¹ * a * x) * (x⁻¹ * b * x)) := by group
      _ = a⁻¹ * (x⁻¹ * a * x) * (b⁻¹ * (x⁻¹ * b * x)) := by
          have hc3 : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := by
            rw [← mul_inv_rev, ← mul_inv_rev, hAab a ha b hb]
          have hc4 : b⁻¹ * (x⁻¹ * a * x) = (x⁻¹ * a * x) * b⁻¹ :=
            (hAab _ (hAx a ha) _ (A.inv_mem hb)).symm
          calc b⁻¹ * a⁻¹ * ((x⁻¹ * a * x) * (x⁻¹ * b * x)) =
                a⁻¹ * (b⁻¹ * (x⁻¹ * a * x)) * (x⁻¹ * b * x) := by rw [hc3]; group
            _ = a⁻¹ * ((x⁻¹ * a * x) * b⁻¹) * (x⁻¹ * b * x) := by rw [hc4]
            _ = a⁻¹ * (x⁻¹ * a * x) * (b⁻¹ * (x⁻¹ * b * x)) := by group
      _ = a⁻¹ * x⁻¹ * a * x * (b⁻¹ * x⁻¹ * b * x) := by group
  have hf1 : ∀ a ∈ A, f a = 1 ↔ a ∈ B := by
    intro a ha
    simp only [hf, hB, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨ha, ?_⟩
      have h' : x⁻¹ * a * x = a := by
        calc x⁻¹ * a * x = a * (a⁻¹ * x⁻¹ * a * x) := by group
          _ = a := by rw [h, mul_one]
      calc a * x = x * (x⁻¹ * a * x) := by group
        _ = x * a := by rw [h']
    · rintro ⟨-, h⟩
      calc a⁻¹ * x⁻¹ * a * x = a⁻¹ * x⁻¹ * (a * x) := by group
        _ = a⁻¹ * x⁻¹ * (x * a) := by rw [h]
        _ = 1 := by group
  have hvB : v ∉ B := fun h => hz₁1 ((hf1 v hvA).2 h)
  have hBA : B ≤ A := inf_le_left
  have hidx : (B.subgroupOf A).index = 2 := by
    have h1 := (B.subgroupOf A).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hBA).toEquiv, hBc, hAc] at h1
    omega
  have hfv : ∀ a ∈ A, f a = 1 ∨ f a = z₁ := by
    intro a ha
    by_cases haB : a ∈ B
    · exact Or.inl ((hf1 a ha).2 haB)
    · right
      have h1 := (mul_mem_iff_of_index_two hidx (a := (⟨a, ha⟩ : ↥A))
        (b := (⟨v, hvA⟩ : ↥A)⁻¹)).2 (by
          simp only [mem_subgroupOf, coe_inv]
          exact ⟨fun h => absurd h haB, fun h => absurd (by simpa using B.inv_mem h) hvB⟩)
      simp only [mem_subgroupOf, Subgroup.coe_mul, coe_inv] at h1
      have h2 : f (a * v⁻¹) = 1 := (hf1 _ (A.mul_mem ha (A.inv_mem hvA))).2 h1
      calc f a = f (a * v⁻¹ * v) := by rw [inv_mul_cancel_right]
        _ = f (a * v⁻¹) * f v := hfmul _ (A.mul_mem ha (A.inv_mem hvA)) v hvA
        _ = z₁ := by rw [h2, one_mul]
  have hz₁2 : z₁ * z₁ = 1 := by
    have h1 := hfmul v hvA v hvA
    rcases hfv (v * v) (A.mul_mem hvA hvA) with h | h
    · rw [h1] at h
      exact h
    · rw [h1] at h
      exact absurd (mul_left_cancel (h.trans (mul_one z₁).symm)) hz₁1
  have hz₁x : z₁ * x = x * z₁ := by
    have h1 : x * z₁ * x⁻¹ = z₁⁻¹ := by
      calc x * z₁ * x⁻¹ = x * v⁻¹ * x⁻¹ * v := by rw [hz₁]; group
        _ = x⁻¹ * v⁻¹ * x * v := by rw [hxi]
        _ = z₁⁻¹ := by rw [hz₁]; group
    calc z₁ * x = z₁⁻¹ * x := by rw [inv_eq_of_mul_eq_one_right hz₁2]
      _ = x * z₁ * x⁻¹ * x := by rw [h1]
      _ = x * z₁ := by group
  refine ⟨v, hvA, hcP, hz₁1, hz₁2, hz₁x, fun s hs hsx => ?_⟩
  have hsA : s * v * s⁻¹ ∈ A := by
    refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hs v).mp hvP, mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' : s⁻¹ * y * s ∈ P := conj_mem_of_mem_normalizer hs hy
    have h1 : s⁻¹ * y * s * v = v * (s⁻¹ * y * s) :=
      (mem_centralizer_iff.mp (mem_inf.mp hvA).2 _ hy')
    calc y * (s * v * s⁻¹) = s * (s⁻¹ * y * s * v) * s⁻¹ := by group
      _ = s * (v * (s⁻¹ * y * s)) * s⁻¹ := by rw [h1]
      _ = s * v * s⁻¹ * y := by group
  have hsx' : s * x⁻¹ = x⁻¹ * s := by rw [hxi]; exact hsx
  have hcon : s * z₁ * s⁻¹ = f (s * v * s⁻¹) := by
    simp only [hf, hz₁]
    calc s * (v⁻¹ * x⁻¹ * v * x) * s⁻¹ = s * v⁻¹ * (s⁻¹ * s) * x⁻¹ * (s⁻¹ * s) * v * x * s⁻¹ := by
          group
      _ = (s * v * s⁻¹)⁻¹ * (s * x⁻¹ * s⁻¹) * (s * v * s⁻¹) * (s * x * s⁻¹) := by group
      _ = (s * v * s⁻¹)⁻¹ * x⁻¹ * (s * v * s⁻¹) * x := by
          rw [show s * x⁻¹ * s⁻¹ = x⁻¹ by rw [hsx']; group,
            show s * x * s⁻¹ = x by rw [hsx]; group]
  rcases hfv _ hsA with h | h
  · exfalso
    apply hz₁1
    have h1 : s * z₁ * s⁻¹ = 1 := hcon.trans h
    calc z₁ = s⁻¹ * (s * z₁ * s⁻¹) * s := by group
      _ = 1 := by rw [h1]; group
  · exact hcon.trans h

end CFSG.ComponentClassification.GrSLit.L34Facts
