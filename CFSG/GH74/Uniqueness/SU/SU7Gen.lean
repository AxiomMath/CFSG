module

public import CFSG.GH74.GLS.Bg.Local.Transfer1515

public section

namespace CFSG.GH74.Uniqueness.SU.SU7.Gen

open Subgroup

section Elements

variable {X : Type*} [Group X]

theorem exists_zpow_mul_of_mem_sup {x g : X} {K : Subgroup X}
    (hK : ∀ k ∈ K, k * x = x * k) (hg : g ∈ zpowers x ⊔ K) :
    ∃ (j : ℤ), ∃ k ∈ K, g = x ^ j * k := by
  let P : Subgroup X :=
    { carrier := {g | ∃ (j : ℤ), ∃ k ∈ K, g = x ^ j * k}
      mul_mem' := by
        rintro _ _ ⟨j, k, hk, rfl⟩ ⟨j', k', hk', rfl⟩
        refine ⟨j + j', k * k', K.mul_mem hk hk', ?_⟩
        have h1 : k * x ^ j' = x ^ j' * k :=
          ((Commute.zpow_right (show Commute k x from hK k hk) j')).eq
        calc x ^ j * k * (x ^ j' * k') = x ^ j * (k * x ^ j') * k' := by group
          _ = x ^ j * (x ^ j' * k) * k' := by rw [h1]
          _ = x ^ (j + j') * (k * k') := by rw [zpow_add]; group
      one_mem' := ⟨0, 1, K.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨j, k, hk, rfl⟩
        refine ⟨-j, k⁻¹, K.inv_mem hk, ?_⟩
        calc (x ^ j * k)⁻¹ = k⁻¹ * x ^ (-j) := by group
          _ = x ^ (-j) * k⁻¹ :=
            ((Commute.zpow_right (show Commute k⁻¹ x from
              (show Commute k x from hK k hk).inv_left) (-j))).eq }
  have hle : zpowers x ⊔ K ≤ P :=
    sup_le (by rintro _ ⟨j, rfl⟩; exact ⟨j, 1, K.one_mem, by simp⟩)
      (fun k hk => ⟨0, k, hk, by simp⟩)
  exact hle hg

theorem inf_centralizer_conj {S : Subgroup X} {c : X} (hc : c ∈ S) (x : X) :
    S ⊓ centralizer ({c * x * c⁻¹} : Set X) =
      (S ⊓ centralizer ({x} : Set X)).map (MulAut.conj c).toMonoidHom := by
  ext y
  simp only [Subgroup.mem_inf, mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
    Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hyS, hy⟩
    refine ⟨c⁻¹ * y * c, ⟨?_, ?_⟩, by group⟩
    · simpa using S.mul_mem (S.mul_mem (S.inv_mem hc) hyS) hc
    · have h : c * x * c⁻¹ * y = y * (c * x * c⁻¹) := hy
      calc x * (c⁻¹ * y * c) = c⁻¹ * (c * x * c⁻¹ * y) * c := by group
        _ = c⁻¹ * (y * (c * x * c⁻¹)) * c := by rw [h]
        _ = c⁻¹ * y * c * x := by group
  · rintro ⟨y', ⟨hy'S, hy'⟩, rfl⟩
    refine ⟨S.mul_mem (S.mul_mem hc hy'S) (S.inv_mem hc), ?_⟩
    have h : x * y' = y' * x := hy'
    calc c * x * c⁻¹ * (c * y' * c⁻¹) = c * (x * y') * c⁻¹ := by group
      _ = c * (y' * x) * c⁻¹ := by rw [h]
      _ = c * y' * c⁻¹ * (c * x * c⁻¹) := by group

end Elements

section Bar

variable {X : Type*} [Group X]

theorem inf_eq_bot_of_isPGroup {P O : Subgroup X} (hP : IsPGroup 2 P) (hO : Odd (Nat.card O)) :
    P ⊓ O = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hP ⟨g, hg.1⟩
  have h1 : orderOf g = 2 ^ k := by simpa using hk
  have h2 : orderOf g ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hg.2
  have h3 : Nat.Coprime (orderOf g) (Nat.card O) := by
    rw [h1]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hO)
  have h4 : orderOf g = 1 := Nat.Coprime.eq_one_of_dvd h3 h2
  exact orderOf_eq_one_iff.1 h4

variable [Finite X] (O : Subgroup X) [O.Normal]

theorem relIndex_sup_odd {P : Subgroup X} (hP : IsPGroup 2 P) (hO : Odd (Nat.card O)) :
    P.relIndex (P ⊔ O) = Nat.card O := by
  have hPO : P ⊓ O = ⊥ := inf_eq_bot_of_isPGroup hP hO
  have h1 : O.relIndex (O ⊔ P) = Nat.card P := by
    rw [Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right, inf_comm, hPO,
      Subgroup.relIndex_bot_left]
  have h2 : Nat.card (O ⊔ P : Subgroup X) = Nat.card O * Nat.card P := by
    have := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup X) O (O ⊔ P) bot_le le_sup_left
    rw [Subgroup.relIndex_bot_left, h1, Subgroup.relIndex_bot_left] at this
    exact this.symm
  have h3 := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup X) P (P ⊔ O) bot_le le_sup_left
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, sup_comm P O, h2, mul_comm] at h3
  have hpos : 0 < Nat.card P := Nat.card_pos
  rw [sup_comm P O]
  exact Nat.eq_of_mul_eq_mul_right hpos h3

omit [Finite X] in
theorem mem_normalizer_of_conj_le {P : Subgroup X} [Finite P] {n : X}
    (h : ∀ p ∈ P, n * p * n⁻¹ ∈ P) : n ∈ normalizer (P : Set X) := by
  have hle : P.map (MulAut.conj n).toMonoidHom ≤ P := by
    rintro _ ⟨p, hp, rfl⟩
    simpa [MulAut.conj_apply] using h p hp
  have hcard : Nat.card P ≤ Nat.card (P.map (MulAut.conj n).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj n).injective]
  have heq : P.map (MulAut.conj n).toMonoidHom = P := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [mem_normalizer_iff]
  intro g
  refine ⟨fun hg => h g hg, fun hg => ?_⟩
  have : n * g * n⁻¹ ∈ P.map (MulAut.conj n).toMonoidHom := by rw [heq]; exact hg
  obtain ⟨p, hp, hpg⟩ := this
  have : p = g := by
    have := hpg
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    simpa using this
  exact this ▸ hp

theorem map_normalizer_mk_eq {P : Subgroup X} (hP : IsPGroup 2 P) (hO : Odd (Nat.card O)) :
    (normalizer (P : Set X)).map (QuotientGroup.mk' O) =
      normalizer ((P.map (QuotientGroup.mk' O) : Subgroup (X ⧸ O)) : Set (X ⧸ O)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (Subgroup.le_normalizer_map _) ?_
  intro ā hā
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective ā
  set Pt : Subgroup X := (P.map (QuotientGroup.mk' O)).comap (QuotientGroup.mk' O) with hPt
  have haPt : a ∈ normalizer (Pt : Set X) := by
    have h1 := Subgroup.comap_normalizer_eq_of_surjective (P.map (QuotientGroup.mk' O))
      (QuotientGroup.mk'_surjective O)
    have h2 : a ∈ (normalizer
        ((P.map (QuotientGroup.mk' O) : Subgroup (X ⧸ O)) : Set (X ⧸ O))).comap
        (QuotientGroup.mk' O) := hā
    rw [h1] at h2
    exact h2
  have hPPt : P ≤ Pt := Subgroup.le_comap_map _ P
  have hOPt : O ≤ Pt := fun o ho => by
    show (QuotientGroup.mk' O) o ∈ P.map (QuotientGroup.mk' O)
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff o).2 ho]
    exact one_mem _
  have hPt_eq : Pt = P ⊔ O := by
    refine le_antisymm ?_ (sup_le hPPt hOPt)
    intro t ht
    obtain ⟨p, hp, hpt⟩ := (show (QuotientGroup.mk' O) t ∈ P.map (QuotientGroup.mk' O) from ht)
    have hpo : p⁻¹ * t ∈ O := QuotientGroup.eq.1 hpt
    have : t = p * (p⁻¹ * t) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hp hpo
  have hidx : ¬ 2 ∣ P.relIndex Pt := by
    rw [hPt_eq, relIndex_sup_odd O hP hO]
    have := Nat.odd_iff.1 hO
    omega
  set K : Subgroup X := P.map (MulAut.conj a).toMonoidHom with hK
  have hKPt : K ≤ Pt := by
    rintro _ ⟨p, hp, rfl⟩
    exact (mem_normalizer_iff.1 haPt p).1 (hPPt hp)
  have hKp : IsPGroup 2 K := hP.map _
  obtain ⟨c, hcPt, hc⟩ :=
    CFSG.GH74.GLS.Bg.Thompson.exists_conj_into_sylow (p := 2) hKPt hKp hPPt hP hidx
  have hn' : c⁻¹ * a ∈ normalizer (P : Set X) := by
    apply mem_normalizer_of_conj_le
    intro p hp
    have := hc (a * p * a⁻¹) ⟨p, hp, by simp [MulAut.conj_apply]⟩
    have e : c⁻¹ * a * p * (c⁻¹ * a)⁻¹ = c⁻¹ * (a * p * a⁻¹) * c := by group
    rw [e]; exact this
  obtain ⟨p, hp, hpc⟩ := (show (QuotientGroup.mk' O) c ∈ P.map (QuotientGroup.mk' O) from hcPt)
  refine ⟨p * (c⁻¹ * a), (normalizer (P : Set X)).mul_mem (le_normalizer hp) hn', ?_⟩
  rw [map_mul, map_mul, map_inv, hpc]
  have h0 : (QuotientGroup.mk' O) a = (a : X ⧸ O) := rfl
  rw [h0]
  group

end Bar

section TwoTrans

variable {G : Type*} [Group G] [Finite G]

theorem eq_four_of_card {U : Subgroup G} (hU : Nat.card U = 4) {z u : G} (hzU : z ∈ U)
    (huU : u ∈ U) (hz1 : z ≠ 1) (hu1 : u ≠ 1) (huz : u ≠ z) (hzz : z * z = 1)
    (hc : z * u = u * z) :
    ∀ p ∈ U, p = 1 ∨ p = z ∨ p = u ∨ p = z * u := by
  classical
  have hw1 : z * u ≠ 1 := by
    intro h
    apply huz
    have : u = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]; exact (inv_eq_of_mul_eq_one_right hzz)
  have hwz : z * u ≠ z := by intro h; apply hu1; simpa using h
  have hwu : z * u ≠ u := by intro h; apply hz1; simpa using h
  set F : Finset G := {1, z, u, z * u} with hF
  have hFcard : F.card = 4 := by
    rw [hF]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simp only [Finset.mem_singleton]; intro h; exact hwu h.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨huz.symm, hwz.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hz1.symm, hu1.symm, hw1.symm⟩
  have hsub : (F : Set G) ⊆ (U : Set G) := by
    intro p hp
    simp only [hF, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact U.one_mem
    · exact hzU
    · exact huU
    · exact U.mul_mem hzU huU
  have hcard : (U : Set G).ncard ≤ (F : Set G).ncard := by
    rw [Set.ncard_coe_finset, hFcard, ← Nat.card_coe_set_eq]
    exact hU.le
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  intro p hp
  have : p ∈ (F : Set G) := heq ▸ hp
  simpa [hF] using this

theorem two_trans {U N : Subgroup G} (hU : Nat.card U = 4)
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hU2 : ∀ a ∈ U, a * a = 1)
    (hN : ∀ n ∈ N, ∀ p ∈ U, n * p * n⁻¹ ∈ U)
    {a x z : G} (ha : a ∈ N) (hx : x ∈ N) (hzU : z ∈ U) (hz1 : z ≠ 1) (hxz : x * z * x⁻¹ = z)
    (hafix : ∀ p ∈ U, p ≠ 1 → a * p * a⁻¹ ≠ p)
    (hxfix : ∀ p ∈ U, p ≠ 1 → p ≠ z → x * p * x⁻¹ ≠ p) :
    ∀ p₁ ∈ U, ∀ p₂ ∈ U, ∀ q₁ ∈ U, ∀ q₂ ∈ U, p₁ ≠ 1 → p₂ ≠ 1 → p₁ ≠ p₂ → q₁ ≠ 1 → q₂ ≠ 1 →
      q₁ ≠ q₂ → ∃ h ∈ N, h * p₁ * h⁻¹ = q₁ ∧ h * p₂ * h⁻¹ = q₂ := by
  have hca : ∀ p q : G, a * (p * q) * a⁻¹ = (a * p * a⁻¹) * (a * q * a⁻¹) := fun p q => by group
  have hcx : ∀ p q : G, x * (p * q) * x⁻¹ = (x * p * x⁻¹) * (x * q * x⁻¹) := fun p q => by group
  have hzz : z * z = 1 := hU2 z hzU
  obtain ⟨u, hu⟩ : ∃ u, u = a * z * a⁻¹ := ⟨_, rfl⟩
  have huU : u ∈ U := hu ▸ hN a ha z hzU
  have huz : u ≠ z := hu ▸ hafix z hzU hz1
  have hu1 : u ≠ 1 := by
    intro h; apply hz1
    rw [h] at hu
    have : a * z * a⁻¹ = 1 := hu.symm
    simpa using this
  have huu : u * u = 1 := hU2 u huU
  have hzu : z * u = u * z := hUc z hzU u huU
  have hall := eq_four_of_card hU hzU huU hz1 hu1 huz hzz hzu
  have hwU : z * u ∈ U := U.mul_mem hzU huU
  have hw1 : z * u ≠ 1 := by
    intro h
    apply huz
    have : u = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]; exact (inv_eq_of_mul_eq_one_right hzz)
  have hwz : z * u ≠ z := by intro h; apply hu1; simpa using h
  have hwu : z * u ≠ u := by intro h; apply hz1; simpa using h
  have hzw : z * (z * u) = u := by rw [← mul_assoc, hzz, one_mul]
  have huw : u * (z * u) = z := by
    rw [← mul_assoc, ← hzu, mul_assoc, huu, mul_one]
  have hau : a * u * a⁻¹ = z * u := by
    have h1 : a * u * a⁻¹ ∈ U := hN a ha u huU
    have h2 : a * u * a⁻¹ ≠ u := hafix u huU hu1
    have h3 : a * u * a⁻¹ ≠ 1 := by
      intro h; apply hu1
      have : a * u * a⁻¹ = 1 := h
      simpa using this
    rcases hall _ h1 with h | h | h | h
    · exact absurd h h3
    · exfalso
      have hwfix : a * (z * u) * a⁻¹ = z * u := by
        rw [hca, ← hu, h, ← hzu]
      exact hafix _ hwU hw1 hwfix
    · exact absurd h h2
    · exact h
  have haw : a * (z * u) * a⁻¹ = z := by rw [hca, ← hu, hau, huw]
  have hxu : x * u * x⁻¹ = z * u := by
    have h1 : x * u * x⁻¹ ∈ U := hN x hx u huU
    have h2 : x * u * x⁻¹ ≠ u := hxfix u huU hu1 huz
    have h3 : x * u * x⁻¹ ≠ 1 := by
      intro h; apply hu1
      have : x * u * x⁻¹ = 1 := h
      simpa using this
    have h4 : x * u * x⁻¹ ≠ z := by
      intro h; apply huz
      have h5 : x * u * x⁻¹ = x * z * x⁻¹ := by rw [h, hxz]
      exact mul_left_cancel (mul_right_cancel h5)
    rcases hall _ h1 with h | h | h | h
    · exact absurd h h3
    · exact absurd h h4
    · exact absurd h h2
    · exact h
  have hxw : x * (z * u) * x⁻¹ = u := by rw [hcx, hxz, hxu, hzw]
  have base : ∀ p₁ ∈ U, ∀ p₂ ∈ U, p₁ ≠ 1 → p₂ ≠ 1 → p₁ ≠ p₂ →
      ∃ h ∈ N, h * z * h⁻¹ = p₁ ∧ h * u * h⁻¹ = p₂ := by
    intro p₁ hp₁ p₂ hp₂ h1 h2 h12
    rcases hall p₁ hp₁ with h | h | h | h <;> rcases hall p₂ hp₂ with h' | h' | h' | h'
    · exact absurd h h1
    · exact absurd h h1
    · exact absurd h h1
    · exact absurd h h1
    · exact absurd h' h2
    · exact absurd (h.trans h'.symm) h12
    · exact ⟨1, N.one_mem, by simp [h], by simp [h']⟩
    · exact ⟨x, hx, by rw [h]; exact hxz, by rw [h']; exact hxu⟩
    · exact absurd h' h2
    · refine ⟨a * x, N.mul_mem ha hx, ?_, ?_⟩
      · rw [h]
        have : a * x * z * (a * x)⁻¹ = a * (x * z * x⁻¹) * a⁻¹ := by group
        rw [this, hxz, ← hu]
      · rw [h']
        have : a * x * u * (a * x)⁻¹ = a * (x * u * x⁻¹) * a⁻¹ := by group
        rw [this, hxu, haw]
    · exact absurd (h.trans h'.symm) h12
    · exact ⟨a, ha, by rw [h]; exact hu.symm, by rw [h']; exact hau⟩
    · exact absurd h' h2
    · refine ⟨a * a, N.mul_mem ha ha, ?_, ?_⟩
      · rw [h]
        have : a * a * z * (a * a)⁻¹ = a * (a * z * a⁻¹) * a⁻¹ := by group
        rw [this, ← hu, hau]
      · rw [h']
        have : a * a * u * (a * a)⁻¹ = a * (a * u * a⁻¹) * a⁻¹ := by group
        rw [this, hau, haw]
    · refine ⟨a * a * x, N.mul_mem (N.mul_mem ha ha) hx, ?_, ?_⟩
      · rw [h]
        have : a * a * x * z * (a * a * x)⁻¹ = a * (a * (x * z * x⁻¹) * a⁻¹) * a⁻¹ := by group
        rw [this, hxz, ← hu, hau]
      · rw [h']
        have : a * a * x * u * (a * a * x)⁻¹ = a * (a * (x * u * x⁻¹) * a⁻¹) * a⁻¹ := by group
        rw [this, hxu, haw, ← hu]
    · exact absurd (h.trans h'.symm) h12
  intro p₁ hp₁ p₂ hp₂ q₁ hq₁ q₂ hq₂ h1 h2 h12 k1 k2 k12
  obtain ⟨hp, hpN, hp1, hp2⟩ := base p₁ hp₁ p₂ hp₂ h1 h2 h12
  obtain ⟨hq, hqN, hq1, hq2⟩ := base q₁ hq₁ q₂ hq₂ k1 k2 k12
  refine ⟨hq * hp⁻¹, N.mul_mem hqN (N.inv_mem hpN), ?_, ?_⟩
  · rw [← hp1, ← hq1]; group
  · rw [← hp2, ← hq2]; group

end TwoTrans

section Thompson

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem not_exists_cyclic_quotient (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {u : G} : ¬ ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ u ∉ N := by
  rintro ⟨N, hN, hcyc, hu⟩
  have := hG
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · subst h
    have e : G ≃* (G ⧸ (⊥ : Subgroup G)) := (QuotientGroup.quotientBot).symm
    have : IsCyclic G := isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (IsCyclic.commGroup.mul_comm a b)
  · exact hu (h ▸ Subgroup.mem_top u)

theorem thompson_two (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) {S T : Subgroup G}
    (hS : IsPGroup 2 S) (hSidx : ¬ 2 ∣ S.index) (hTn : ∀ t ∈ S, ∀ q ∈ T, t * q * t⁻¹ ∈ T)
    {u : G} (huS : u ∈ S) (huT : u ∉ T) (hu2 : u * u = 1)
    (hcov : ∀ s ∈ S, s ∈ T ∨ u⁻¹ * s ∈ T) :
    ∃ g : G, g⁻¹ * u * g ∈ T ∧
      ∀ c ∈ S ⊓ centralizer ({u} : Set G),
        g⁻¹ * c * g ∈ S ⊓ centralizer ({g⁻¹ * u * g} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hres := CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) (P := S) (Q := T)
    (u := u) hS hSidx hTn ⟨u, huS, fun t ht => by
      rcases hcov t ht with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩⟩ huS huT
    (fun g k _ => by
      have : u ^ (2 * k) = 1 := by rw [pow_mul, pow_two, hu2, one_pow]
      rw [this]; simp)
    (fun g hg _ => by
      rcases hcov _ hg with h | h
      · exact Or.inl h
      · exact Or.inr h)
  rcases hres with ⟨N, hN, hcyc, -, huN⟩ | ⟨g, hgT, -, hgc⟩
  · exact absurd ⟨N, hN, hcyc, huN⟩ (not_exists_cyclic_quotient hG hnab)
  · exact ⟨g, hgT, hgc⟩

end Thompson

end CFSG.GH74.Uniqueness.SU.SU7.Gen
