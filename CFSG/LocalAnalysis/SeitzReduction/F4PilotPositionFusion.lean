module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotTransfer

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup

section Fusion

variable {G : Type*} [Group G]

theorem eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two [Finite G] {t y : G}
    (ht : orderOf t = 2) (hy : y ∈ zpowers t) : y = 1 ∨ y = t := by
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hy)
  rw [← pow_mod_orderOf, ht]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h]
  · exact Or.inl (pow_zero t)
  · exact Or.inr (pow_one t)

theorem mem_normalizer_of_le_centralizer_singleton {Y : Subgroup G} {t : G}
    (hY : Y ≤ centralizer ({t} : Set G)) : t ∈ normalizer (Y : Set G) :=
  centralizer_le_normalizer _
    (mem_centralizer_iff.2 fun _ hy => mem_centralizer_singleton_iff.1 (hY hy))

private theorem inv_mul_mul_pow (g x : G) (n : ℕ) : (g⁻¹ * x * g) ^ n = g⁻¹ * x ^ n * g := by
  simpa using conj_pow (a := g⁻¹) (b := x) (i := n)

theorem mul_conj_mem_of_forall_inner {L : Subgroup G} {t : G} (ht : orderOf t = 2)
    (hLt : L ≤ centralizer ({t} : Set G)) (hnot : ∀ g : G, g⁻¹ * t * g ∉ L)
    (hinner : ∀ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) → g⁻¹ * t * g ∈ L ⊔ zpowers t)
    {g : G} (hg : g⁻¹ * t * g ∈ centralizer ({t} : Set G)) : t * (g⁻¹ * t * g) ∈ L := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers htt
    (mem_normalizer_of_le_centralizer_singleton hLt) (hinner g hg) with h | h
  · exact absurd h (hnot g)
  · have hc : g⁻¹ * t * g * t * t = t * (g⁻¹ * t * g * t) :=
      mem_centralizer_singleton_iff.1 (hLt h)
    have e : t * (g⁻¹ * t * g) = g⁻¹ * t * g * t := by
      calc t * (g⁻¹ * t * g) = t * (g⁻¹ * t * g * t * t) := by
            rw [mul_assoc _ t t, htt, mul_one]
        _ = t * (t * (g⁻¹ * t * g * t)) := by rw [hc]
        _ = g⁻¹ * t * g * t := by rw [← mul_assoc t t, htt, one_mul]
    rw [e]
    exact h

variable [Finite G]

theorem exists_conj_eq_mul_of_two_dvd_index {L : Subgroup G} {t : G} (ht : orderOf t = 2)
    (hLt : L ≤ centralizer ({t} : Set G))
    (hA : ∀ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) → t * (g⁻¹ * t * g) ∈ L)
    (h2 : 2 ∣ (centralizer ({t} : Set G)).index) :
    ∃ g : G, ∃ z ∈ L, g⁻¹ * t * g = t * z ∧ z ≠ 1 ∧
      ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := centralizer ({t} : Set G) with hMdef
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htM : t ∈ M := mem_centralizer_singleton_iff.2 rfl
  obtain ⟨U⟩ : Nonempty (Sylow 2 L) := inferInstance
  obtain ⟨P, hUP⟩ := (U.isPGroup'.map (inclusion hLt)).exists_le_sylow
  set S : Subgroup G := (P : Subgroup M).map M.subtype with hSdef
  have hSM : S ≤ M := map_subtype_le _
  have hmemS : ∀ y : M, (y : G) ∈ S ↔ y ∈ P := fun y => mem_map_iff_mem M.subtype_injective
  have hPS : S.subgroupOf M = P := by
    rw [hSdef, ← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective]
  have hUS : ∀ u ∈ (U : Subgroup L), (u : G) ∈ S := fun u hu =>
    (hmemS (inclusion hLt u)).2 (hUP ⟨u, hu, rfl⟩)
  have hNS : ∀ x (hxM : x ∈ M), IsPGroup 2 (zpowers (⟨x, hxM⟩ : M)) →
      x ∈ normalizer (S : Set G) → x ∈ S := by
    intro x hxM hx2 hxN
    have hxN' : (⟨x, hxM⟩ : M) ∈ normalizer ((P : Subgroup M) : Set M) := by
      rw [← hPS, ← subgroupOf_normalizer_eq hSM, mem_subgroupOf]
      exact hxN
    have hxP := mem_inf.2 ⟨mem_zpowers (⟨x, hxM⟩ : M), hxN'⟩
    exact (hmemS _).2 (mem_inf.1 ((hx2.inf_normalizer_sylow P).le hxP)).2
  have htS : t ∈ S :=
    hNS t htM (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_mk, ht, pow_one]))
      (mem_normalizer_of_le_centralizer_singleton hSM)
  obtain ⟨Sst, hSS⟩ := (P.isPGroup'.map M.subtype).exists_le_sylow
  have hlt : S.subgroupOf Sst < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => ?_
    exact Sst.not_dvd_index (h2.trans (index_dvd_of_le ((subgroupOf_eq_top.1 h).trans hSM)))
  have : Group.IsNilpotent Sst := Sst.isPGroup'.isNilpotent
  obtain ⟨y, hyN, hyS⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  rw [← subgroupOf_normalizer_eq hSS, mem_subgroupOf] at hyN
  rw [mem_subgroupOf] at hyS
  set x : G := (y : G) with hxdef
  have hxtS : x⁻¹ * t * x ∈ S := (mem_normalizer_iff''.1 hyN t).1 htS
  refine ⟨x, t * (x⁻¹ * t * x), hA x (hSM hxtS), by rw [← mul_assoc, htt, one_mul], ?_, U,
    fun u hu => ?_⟩
  ·
    intro hz1
    have hxt : x⁻¹ * t * x = t := by
      rw [eq_inv_of_mul_eq_one_right hz1, inv_eq_of_mul_eq_one_right htt]
    have hxM : x ∈ M := by
      rw [hMdef, mem_centralizer_singleton_iff]
      calc x * t = x * (x⁻¹ * t * x) := by rw [hxt]
        _ = t * x := by group
    refine hyS (hNS x hxM ?_ hyN)
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 Sst.isPGroup' y
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, orderOf_mk, hxdef, orderOf_coe, hk])
  ·
    have hs := hUS u hu
    have hst : (u : G) * t = t * u := mem_centralizer_singleton_iff.1 (hSM hs)
    have h' : x * u * x⁻¹ * t = t * (x * u * x⁻¹) :=
      mem_centralizer_singleton_iff.1 (hSM ((mem_normalizer_iff.1 hyN _).1 hs))
    have hsc : (u : G) * (x⁻¹ * t * x) = x⁻¹ * t * x * u := by
      calc (u : G) * (x⁻¹ * t * x) = x⁻¹ * (x * u * x⁻¹ * t) * x := by group
        _ = x⁻¹ * (t * (x * u * x⁻¹)) * x := by rw [h']
        _ = x⁻¹ * t * x * u := by group
    calc (u : G) * (t * (x⁻¹ * t * x)) = t * (u * (x⁻¹ * t * x)) := by
          rw [← mul_assoc, hst, mul_assoc]
      _ = t * (x⁻¹ * t * x) * u := by rw [hsc]; simp only [mul_assoc]

theorem exists_normal_index_two_of_forall_inner_of_odd {L : Subgroup G} {t : G}
    (ht : orderOf t = 2) (hLt : L ≤ centralizer ({t} : Set G))
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hnot : ∀ g : G, g⁻¹ * t * g ∉ L)
    (hA : ∀ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) → t * (g⁻¹ * t * g) ∈ L)
    {x₀ : G} (hx₀ : x₀ ∈ centralizer ({t} : Set G))
    (hgen : centralizer ({t} : Set G) ≤ L ⊔ zpowers x₀ ⊔ zpowers t)
    (hlift : ∀ n : ℕ, x₀ ^ n ∈ L ⊔ zpowers t → x₀ ^ n ∈ zpowers t)
    (hodd : ¬ 2 ∣ (centralizer ({t} : Set G)).index) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := centralizer ({t} : Set G)
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htM : t ∈ M := mem_centralizer_singleton_iff.2 rfl
  have htL : t ∉ L := by simpa using hnot 1
  have : (L.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hLt).2 hCN
  set π := QuotientGroup.mk' (L.subgroupOf M) with hπdef
  have hπeq : ∀ g h (hg : g ∈ M) (hh : h ∈ M), π ⟨g, hg⟩ = π ⟨h, hh⟩ ↔ g⁻¹ * h ∈ L :=
    fun g h hg hh => by
      rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        mem_subgroupOf]
      rfl
  have hπ1 : ∀ g (hg : g ∈ M), π ⟨g, hg⟩ = 1 ↔ g ∈ L := fun g hg => by
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
  have hπpow : ∀ g (hg : g ∈ M) (n : ℕ), π ⟨g, hg⟩ ^ n = π ⟨g ^ n, pow_mem hg n⟩ :=
    fun g hg n => by rw [← map_pow]; rfl
  have hπmul : ∀ g h (hg : g ∈ M) (hh : h ∈ M),
      π ⟨g, hg⟩ * π ⟨h, hh⟩ = π ⟨g * h, mul_mem hg hh⟩ :=
    fun g h hg hh => by rw [← map_mul]; rfl
  have hx0L : ∀ n : ℕ, x₀ ^ n ∈ L → x₀ ^ n = 1 := fun n hn => by
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two ht (hlift n (mem_sup_left hn))
      with h | h
    · exact h
    · exact absurd (h ▸ hn) htL
  set w := π ⟨x₀, hx₀⟩ with hwdef
  have hw : orderOf w = orderOf x₀ := orderOf_eq_orderOf_iff.2 fun n => by
    rw [hwdef, hπpow, hπ1]
    exact ⟨hx0L n, fun h => h ▸ L.one_mem⟩
  set K := ((zpowers w).comap π).map M.subtype
  have hmemK : ∀ g (hg : g ∈ M), g ∈ K ↔ π ⟨g, hg⟩ ∈ zpowers w := fun g hg =>
    (mem_map_iff_mem M.subtype_injective (x := ⟨g, hg⟩)).trans mem_comap
  have hLK : L ⊔ zpowers x₀ ≤ K := sup_le
    (fun l hl => (hmemK l (hLt hl)).2 (by rw [(hπ1 l (hLt hl)).2 hl]; exact one_mem _))
    (zpowers_le.2 ((hmemK x₀ hx₀).2 (mem_zpowers w)))
  have hpowK : ∀ g (hg : g ∈ M), g ∈ K → ∃ k : ℕ, π ⟨g, hg⟩ = w ^ k := fun g hg hgK => by
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1
      (mem_powers_iff_mem_zpowers.2 ((hmemK g hg).1 hgK))
    exact ⟨k, hk.symm⟩
  by_cases htx : t ∈ zpowers x₀
  ·
    have hMK : M ≤ K := hgen.trans (sup_le hLK (zpowers_le.2 (hLK (mem_sup_right htx))))
    have hQ : ∀ g (hg : g ∈ M), ∃ k : ℕ, π ⟨g, hg⟩ = w ^ k := fun g hg => hpowK g hg (hMK hg)
    obtain ⟨c, m, hm, hcm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x₀).ne'
    have h2x : 2 ∣ orderOf x₀ := ht ▸ orderOf_dvd_of_mem_zpowers htx
    obtain ⟨b, rfl⟩ : ∃ b, c = b + 1 := by
      rcases c with _ | b
      · rw [hcm, pow_zero, one_mul] at h2x
        exact absurd (even_iff_two_dvd.2 h2x) (Nat.not_even_iff_odd.2 hm)
      · exact ⟨b, rfl⟩
    have hw2 : orderOf w = 2 ^ (b + 1) * m := hw.trans hcm
    have hpar : ∀ k : ℕ, w ^ k ∈ zpowers (w ^ 2) ↔ Even k := fun k => by
      constructor
      · intro hk
        obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hk)
        rw [← pow_mul] at hj
        have h1 := pow_eq_pow_iff_modEq.1 hj
        rw [hw2] at h1
        have h3 : 2 * j ≡ k [MOD 2] :=
          Nat.ModEq.of_dvd (dvd_mul_of_dvd_left (dvd_pow_self 2 (Nat.succ_ne_zero b)) m) h1
        unfold Nat.ModEq at h3
        exact Nat.even_iff.2 (by omega)
      · rintro ⟨j, rfl⟩
        rw [← two_mul, pow_mul]
        exact pow_mem (mem_zpowers _) j
    set Y := ((zpowers (w ^ 2)).comap π).map M.subtype
    have hYM : Y ≤ M := map_subtype_le _
    have hmemY : ∀ g (hg : g ∈ M), g ∈ Y ↔ π ⟨g, hg⟩ ∈ zpowers (w ^ 2) := fun g hg =>
      (mem_map_iff_mem M.subtype_injective (x := ⟨g, hg⟩)).trans mem_comap
    have hYidx : Y.relIndex M = 2 := by
      rw [relIndex_eq_two_iff_exists_notMem_and]
      refine ⟨x₀, hx₀, fun h => Nat.not_even_one ((hpar 1).1 ?_), fun g hg => ?_⟩
      · rw [pow_one]
        exact (hmemY x₀ hx₀).1 h
      · obtain ⟨k, hk⟩ := hQ g hg
        rcases Nat.even_or_odd k with hke | hko
        · exact Or.inr ((hmemY g hg).2 (by rw [hk]; exact (hpar k).2 hke))
        · refine Or.inl ((hmemY _ (mul_mem hg hx₀)).2 ?_)
          rw [← hπmul g x₀ hg hx₀, hk, ← hwdef, ← pow_succ]
          exact (hpar _).2 hko.add_one
    have hxM : x₀ ^ m ∈ M := pow_mem hx₀ m
    have hxo : orderOf (x₀ ^ m) = 2 ^ (b + 1) := by
      rw [orderOf_pow_of_dvd hm.pos.ne' (hcm ▸ dvd_mul_left m _), hcm,
        Nat.mul_div_cancel _ hm.pos]
    have hxY : x₀ ^ m ∉ Y := by
      rw [hmemY _ hxM, ← hπpow x₀ hx₀ m, ← hwdef, hpar]
      exact Nat.not_even_iff_odd.2 hm
    have hmin : ∀ y ∈ M, y ∉ Y → IsPGroup 2 (zpowers y) → orderOf (x₀ ^ m) ≤ orderOf y := by
      intro y hy hyY _
      obtain ⟨k, hk⟩ := hQ y hy
      have hko : Odd k := Nat.not_even_iff_odd.1 fun he =>
        hyY ((hmemY y hy).2 (by rw [hk]; exact (hpar k).2 he))
      have h1 : w ^ (k * orderOf y) = 1 := by
        rw [pow_mul, ← hk, hπpow, hπ1, pow_orderOf_eq_one]
        exact one_mem L
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hw2] at h2
      have h3 : 2 ^ (b + 1) ∣ orderOf y :=
        (Nat.Coprime.pow_left (b + 1) (Nat.coprime_two_left.2 hko)).dvd_of_dvd_mul_left
          ((dvd_mul_right _ m).trans h2)
      rw [hxo]
      exact Nat.le_of_dvd (orderOf_pos y) h3
    obtain ⟨k₁, hk₁⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 htx)
    have hdiv : 2 ^ b * m ∣ k₁ := by
      have h1 : x₀ ^ (2 * k₁) = 1 := by rw [pow_mul', hk₁, sq, htt]
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hcm, pow_succ', mul_assoc] at h2
      exact (Nat.mul_dvd_mul_iff_left two_pos).1 h2
    obtain ⟨i, hi⟩ := hdiv
    have htpow : t = (x₀ ^ m) ^ (2 ^ b * i) := by
      rw [← hk₁, hi, ← pow_mul]
      congr 1
      ring
    have hfus : ∀ g : G, g⁻¹ * x₀ ^ m * g ∉ Y := by
      intro g hg
      have hyM := hYM hg
      obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).1
        (mem_powers_iff_mem_zpowers.2 ((hmemY _ hyM).1 hg))
      rw [← pow_mul] at hj
      have hyo : (g⁻¹ * x₀ ^ m * g) ^ (2 ^ (b + 1)) = 1 := by
        rw [inv_mul_mul_pow, ← hxo, pow_orderOf_eq_one, mul_one, inv_mul_cancel]
      have hmj : m ∣ j := by
        have h1 : w ^ (2 * j * 2 ^ (b + 1)) = 1 := by
          rw [pow_mul, hj, hπpow, hπ1, hyo]
          exact one_mem L
        have h2 := orderOf_dvd_of_pow_eq_one h1
        rw [hw2, mul_comm (2 * j)] at h2
        exact (Nat.coprime_two_right.2 hm).dvd_of_dvd_mul_left
          ((Nat.mul_dvd_mul_iff_left (by positivity)).1 h2)
      apply hnot g
      have he : g⁻¹ * t * g = (g⁻¹ * x₀ ^ m * g) ^ (2 ^ b * i) := by
        rw [inv_mul_mul_pow, ← htpow]
      rw [he, ← hπ1 _ (pow_mem hyM _), ← hπpow _ hyM, ← hj, ← pow_mul]
      obtain ⟨j', rfl⟩ := hmj
      rw [← orderOf_dvd_iff_pow_eq_one, hw2]
      exact ⟨j' * i, by ring⟩
    exact exists_normal_index_two_of_not_fused_of_relIndex_eq_two hYidx hodd hxM hxY hxo hmin
      hfus
  ·
    set Y := L ⊔ zpowers x₀
    have hYM : Y ≤ M := sup_le hLt (zpowers_le.2 hx₀)
    have htY : t ∉ Y := by
      intro htY
      obtain ⟨k, hk⟩ := hpowK t htM (hLK htY)
      rw [hwdef, hπpow, eq_comm, hπeq] at hk
      have hk' : x₀ ^ k ∈ L ⊔ zpowers t := by
        have h := mul_mem (mem_sup_right (mem_zpowers t) : t ∈ L ⊔ zpowers t)
          (mem_sup_left (inv_mem hk) : ((x₀ ^ k)⁻¹ * t)⁻¹ ∈ L ⊔ zpowers t)
        rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at h
      rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two ht (hlift k hk') with h | h
      · rw [h, inv_one, one_mul] at hk
        exact htL hk
      · exact htx (h ▸ pow_mem (mem_zpowers x₀) k)
    have hYt : Y ⊔ zpowers t = M := le_antisymm (sup_le hYM (zpowers_le.2 htM)) hgen
    refine CFSG.SeitzReduction.exists_normal_index_two_of_not_fused ht
      (mem_normalizer_of_le_centralizer_singleton hYM) htY (by rwa [hYt]) fun g hg => htY ?_
    have h := mul_mem (mem_sup_left (hA g (hYM hg)) : t * (g⁻¹ * t * g) ∈ Y) (inv_mem hg)
    rwa [mul_inv_cancel_right] at h

end Fusion

theorem exists_conj_eq_mul_of_forall_inner {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : 2 < Nat.card G) {L : Subgroup G} {t : G} (ht : orderOf t = 2)
    (hLt : L ≤ centralizer ({t} : Set G))
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hnot : ∀ g : G, g⁻¹ * t * g ∉ L)
    (hinner : ∀ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) → g⁻¹ * t * g ∈ L ⊔ zpowers t)
    {x₀ : G} (hx₀ : x₀ ∈ centralizer ({t} : Set G))
    (hgen : centralizer ({t} : Set G) ≤ L ⊔ zpowers x₀ ⊔ zpowers t)
    (hlift : ∀ n : ℕ, x₀ ^ n ∈ L ⊔ zpowers t → x₀ ^ n ∈ zpowers t) :
    ∃ g : G, ∃ z ∈ L, g⁻¹ * t * g = t * z ∧ z ≠ 1 ∧
      ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u := by
  have hA : ∀ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) → t * (g⁻¹ * t * g) ∈ L :=
    fun _ hg => mul_conj_mem_of_forall_inner ht hLt hnot hinner hg
  by_cases h2 : 2 ∣ (centralizer ({t} : Set G)).index
  · exact exists_conj_eq_mul_of_two_dvd_index ht hLt hA h2
  · exact absurd
      (exists_normal_index_two_of_forall_inner_of_odd ht hLt hCN hnot hA hx₀ hgen hlift h2)
      (CFSG.SeitzReduction.not_exists_normal_index_two_of_simple hG)

theorem exists_gen_of_mulAut {G : Type*} [Group G] [Finite G] {L : Subgroup G} {t : G}
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hLt : L ≤ centralizer ({t} : Set G))
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hAut : ∃ φ : MulAut L, (∀ β : MulAut L, ∃ (c : L) (k : ℕ), β = MulAut.conj c * φ ^ k) ∧
      ∀ n : ℕ, φ ^ n ∈ (MulAut.conj : L →* MulAut L).range → φ ^ n = 1) :
    ∃ x₀ ∈ centralizer ({t} : Set G), centralizer ({t} : Set G) ≤ L ⊔ zpowers x₀ ⊔ zpowers t ∧
      ∀ n : ℕ, x₀ ^ n ∈ L ⊔ zpowers t → x₀ ^ n ∈ zpowers t := by
  obtain ⟨φ, hφ, hφinn⟩ := hAut
  set M := centralizer ({t} : Set G)
  have htM : t ∈ M := mem_centralizer_singleton_iff.2 rfl
  set β : M →* MulAut L := L.normalizerMonoidHom.comp (inclusion hCN)
  have hβ : ∀ (y : M) (a : L), ((β y a : L) : G) = y * a * (y : G)⁻¹ := fun y a =>
    normalizerMonoidHom_apply_apply_coe L _ a
  have hβL : ∀ c : L, β (inclusion hLt c) = MulAut.conj c := fun c => by
    ext a
    rw [hβ, MulAut.conj_apply]
    rfl
  have hβker : ∀ y : M, β y = 1 → (y : G) ∈ centralizer (L : Set G) := fun y hy => by
    rw [mem_centralizer_iff]
    intro a ha
    have h := hβ y ⟨a, ha⟩
    rw [hy, MulAut.one_apply] at h
    calc a * y = y * a * (y : G)⁻¹ * y := by rw [← h]
      _ = y * a := by group
  have hβt : β ⟨t, htM⟩ = 1 := by
    ext a
    rw [hβ, MulAut.one_apply]
    have h := mem_centralizer_singleton_iff.1 (hLt a.2)
    change t * a * t⁻¹ = a
    rw [← h, mul_inv_cancel_right]
  set Φ := zpowers φ ⊓ β.range
  have : IsCyclic Φ := isCyclic_of_le inf_le_left
  obtain ⟨ψ₀, hψ₀⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top Φ).1 inferInstance
  have hψ₀Φ : ψ₀ ∈ Φ := hψ₀ ▸ mem_zpowers ψ₀
  obtain ⟨x₀, hx₀⟩ := MonoidHom.mem_range.1 hψ₀Φ.2
  obtain ⟨k₀, hk₀⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hψ₀Φ.1)
  refine ⟨x₀, x₀.2, fun g hg => ?_, fun n hn => ?_⟩
  ·
    obtain ⟨c, k, hck⟩ := hφ (β ⟨g, hg⟩)
    have hk : φ ^ k ∈ Φ := ⟨pow_mem (mem_zpowers φ) k, ⟨(inclusion hLt c)⁻¹ * ⟨g, hg⟩, by
      rw [map_mul, map_inv, hβL, hck, inv_mul_cancel_left]⟩⟩
    rw [← hψ₀] at hk
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hk
    set y : M := (inclusion hLt c * x₀ ^ j)⁻¹ * ⟨g, hg⟩ with hydef
    have hy1 : β y = 1 := by
      rw [hydef, map_mul, map_inv, map_mul, map_zpow, hβL, hx₀, hj, ← hck, inv_mul_cancel]
    have hyt : (y : G) ∈ zpowers t := hKt ▸ ⟨hβker y hy1, y.2⟩
    have hg' : g = (c : G) * (x₀ : G) ^ j * y := by
      rw [hydef]
      simp only [coe_mul, coe_inv, coe_zpow, coe_inclusion]
      group
    rw [hg']
    exact mul_mem (mul_mem (mem_sup_left (mem_sup_left c.2))
      (mem_sup_left (mem_sup_right (zpow_mem (mem_zpowers _) j)))) (mem_sup_right hyt)
  ·
    set K₁ := ((MulAut.conj : L →* MulAut L).range.comap β).map M.subtype
    have hmemK₁ : ∀ y : M, (y : G) ∈ K₁ ↔ β y ∈ (MulAut.conj : L →* MulAut L).range :=
      fun y => (mem_map_iff_mem M.subtype_injective).trans mem_comap
    have hLK₁ : L ⊔ zpowers t ≤ K₁ :=
      sup_le (fun l hl => (hmemK₁ (inclusion hLt ⟨l, hl⟩)).2 ⟨⟨l, hl⟩, (hβL _).symm⟩)
        (zpowers_le.2 ((hmemK₁ ⟨t, htM⟩).2 ⟨1, by rw [hβt, map_one]⟩))
    have hx₀n : β (x₀ ^ n) ∈ (MulAut.conj : L →* MulAut L).range :=
      (hmemK₁ (x₀ ^ n)).1 (by simpa using hLK₁ hn)
    rw [map_pow, hx₀, ← hk₀, ← pow_mul] at hx₀n
    have hβ1 : β (x₀ ^ n) = 1 := by rw [map_pow, hx₀, ← hk₀, ← pow_mul, hφinn _ hx₀n]
    rw [← hKt]
    exact ⟨by simpa using hβker _ hβ1, by simpa using (x₀ ^ n).2⟩

end CFSG.SeitzReduction.F4Pilot
