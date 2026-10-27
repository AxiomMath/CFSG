module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import CFSG.Holt.PermFacts
public import CFSG.CharacterTheory.Burnside

public section

open Subgroup

namespace CFSG.EvenSporadicStandard.TwoHS.GH312

abbrev altSubgroup : Subgroup (DihedralGroup 4 × Equiv.Perm (Fin 5)) :=
  (⊥ : Subgroup (DihedralGroup 4)).prod (alternatingGroup (Fin 5))

abbrev dihedralSubgroup : Subgroup (DihedralGroup 4 × Equiv.Perm (Fin 5)) :=
  (⊤ : Subgroup (DihedralGroup 4)).prod ⊥

private theorem card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private theorem r2_eq_mul_or_self_or_commutator (d : DihedralGroup 4) (hd : d ≠ 1) :
    DihedralGroup.r 2 = d * d ∨ DihedralGroup.r 2 = d ∨
      DihedralGroup.r 2 = d * DihedralGroup.r 1 * d⁻¹ * (DihedralGroup.r 1)⁻¹ := by
  revert d
  decide +kernel

private theorem dvd_sixty_cases {n : ℕ} (h : n ∣ 60) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨
      n = 10 ∨ n = 12 ∨ n = 15 ∨ n = 20 ∨ n = 30 ∨ n = 60 := by
  have hle : n ≤ 60 := Nat.le_of_dvd (by norm_num) h
  interval_cases n <;> norm_num at h
  all_goals norm_num

private theorem isSolvable_of_card_pow_mul_pow {G : Type*} [Group G] [Finite G] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card G = p ^ a * q ^ b) :
    Group.IsSolvable G := by
  have := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card]; exact h)

private theorem map_centralizer_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (S : Set A) :
    (Subgroup.centralizer S).map e.toMonoidHom = Subgroup.centralizer (e '' S) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · rintro h _ ⟨x, hx, rfl⟩
    have h' := h x hx
    apply e.symm.injective
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
    exact h'
  · intro h x hx
    have h' := h (e x) ⟨x, hx, rfl⟩
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h'

theorem mem_center_dihedral_prod_perm_iff (x : DihedralGroup 4 × Equiv.Perm (Fin 5)) :
    x ∈ Subgroup.center (DihedralGroup 4 × Equiv.Perm (Fin 5)) ↔
      x = 1 ∨ x = (DihedralGroup.r 2, 1) := by
  revert x; decide +kernel

theorem eq_altSubgroup_of_isSimpleGroup (S : Subgroup (DihedralGroup 4 × Equiv.Perm (Fin 5)))
    (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) : S = altSubgroup := by
  let f : S →* DihedralGroup 4 :=
    (MonoidHom.fst (DihedralGroup 4) (Equiv.Perm (Fin 5))).comp S.subtype
  rcases hS.eq_bot_or_eq_top_of_normal f.ker with hker | hker
  ·
    have hfinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
    have hcard : Nat.card S = Nat.card ↥(f.range) :=
      Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv
    have hdvd : Nat.card S ∣ 2 ^ 3 := by
      have h1 : Nat.card ↥(f.range) ∣ Nat.card (DihedralGroup 4) :=
        Subgroup.card_subgroup_dvd_card _
      rw [DihedralGroup.nat_card] at h1
      rw [← hcard] at h1
      simpa using h1
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 S := IsPGroup.of_card_dvd_pow hdvd
    have h2 : Nat.card S = 2 := (IsPGroup.isSimpleGroup_iff_card_eq hp).mp hS
    haveI : IsCyclic S := isCyclic_of_prime_card h2
    haveI : IsMulCommutative S := IsCyclic.isMulCommutative
    obtain ⟨a, b, hab⟩ := hna
    exact (hab (mul_comm' a b)).elim
  ·
    have hle : S ≤ (⊥ : Subgroup (DihedralGroup 4)).prod
        (⊤ : Subgroup (Equiv.Perm (Fin 5))) := by
      intro x hx
      rw [Subgroup.mem_prod]
      refine ⟨?_, Subgroup.mem_top _⟩
      have hxker : (⟨x, hx⟩ : S) ∈ f.ker := hker ▸ Subgroup.mem_top _
      have hfx : f ⟨x, hx⟩ = 1 := MonoidHom.mem_ker.mp hxker
      simpa [f, Subgroup.mem_bot] using hfx
    let g : S →* Equiv.Perm (Fin 5) :=
      (MonoidHom.snd (DihedralGroup 4) (Equiv.Perm (Fin 5))).comp S.subtype
    have hg1 : ∀ x : S, (x : DihedralGroup 4 × Equiv.Perm (Fin 5)).1 = 1 := fun x =>
      Subgroup.mem_bot.mp (Subgroup.mem_prod.mp (hle x.2)).1
    have hginj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      exact Prod.ext (by rw [hg1 x, hg1 y]) hxy
    let S' : Subgroup (Equiv.Perm (Fin 5)) := g.range
    let e' : S ≃* S' := MonoidHom.ofInjective hginj
    have hS'simple : IsSimpleGroup S' := (MulEquiv.isSimpleGroup_congr e').mp hS
    haveI : IsSimpleGroup S' := hS'simple
    have hna' : ∃ a b : S', a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hna
      refine ⟨e' a, e' b, fun h => hab ?_⟩
      apply e'.injective
      rw [map_mul, map_mul]
      exact h
    have hSA : S' ≤ alternatingGroup (Fin 5) := by
      let φ : S' →* ℤˣ := (Equiv.Perm.sign (α := Fin 5)).comp S'.subtype
      have hφker : φ.ker = (alternatingGroup (Fin 5)).subgroupOf S' := by
        ext x
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Equiv.Perm.mem_alternatingGroup]
        simp [φ]
      rcases hS'simple.eq_bot_or_eq_top_of_normal φ.ker with hbot | htop
      · exfalso
        have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hbot
        obtain ⟨a, b, hab⟩ := hna'
        refine hab (hφinj ?_)
        rw [map_mul, map_mul, mul_comm]
      · intro x hx
        have hxker : (⟨x, hx⟩ : S') ∈ φ.ker := htop ▸ Subgroup.mem_top _
        have hx1 : φ ⟨x, hx⟩ = 1 := MonoidHom.mem_ker.mp hxker
        rw [Equiv.Perm.mem_alternatingGroup]
        simpa [φ] using hx1
    have hdvd : Nat.card S' ∣ 60 := by
      have := Subgroup.card_dvd_of_le hSA
      rwa [card_alternatingGroup_five] at this
    have hcontr : ∀ (_ : Group.IsSolvable S'), False := by
      intro hsolv
      obtain ⟨a, b, hab⟩ := hna'
      exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := S')).mpr hsolv a b)
    have hS'card : Nat.card S' = 60 := by
      by_contra hne60
      rcases dvd_sixty_cases hdvd with h | h | h | h | h | h | h | h | h | h | h | h
      · exact hcontr (isSolvable_of_card_pow_mul_pow (p := 2) (q := 3) (a := 0) (b := 0)
          Nat.prime_two Nat.prime_three (by norm_num) (by rw [h]; norm_num))
      · exact hcontr (isSolvable_of_card_pow_mul_pow (p := 2) (q := 3) (a := 1) (b := 0)
          Nat.prime_two Nat.prime_three (by norm_num) (by rw [h]; norm_num))
      · exact hcontr (isSolvable_of_card_pow_mul_pow (p := 2) (q := 3) (a := 0) (b := 1)
          Nat.prime_two Nat.prime_three (by norm_num) (by rw [h]; norm_num))
      · exact hcontr (isSolvable_of_card_pow_mul_pow (p := 2) (q := 3) (a := 2) (b := 0)
          Nat.prime_two Nat.prime_three (by norm_num) (by rw [h]; norm_num))
      · exact hcontr (isSolvable_of_card_pow_mul_pow (p := 2) (q := 5) (a := 0) (b := 1)
          Nat.prime_two Nat.prime_five (by norm_num) (by rw [h]; norm_num))
      · exact hcontr (isSolvable_of_card_pow_mul_pow (p := 2) (q := 3) (a := 1) (b := 1)
          Nat.prime_two Nat.prime_three (by norm_num) (by rw [h]; norm_num))
      · exact hcontr (isSolvable_of_card_pow_mul_pow (p := 2) (q := 5) (a := 1) (b := 1)
          Nat.prime_two Nat.prime_five (by norm_num) (by rw [h]; norm_num))
      · exact hcontr (isSolvable_of_card_pow_mul_pow (p := 2) (q := 3) (a := 2) (b := 1)
          Nat.prime_two Nat.prime_three (by norm_num) (by rw [h]; norm_num))
      · exact hcontr (isSolvable_of_card_pow_mul_pow (p := 3) (q := 5) (a := 1) (b := 1)
          Nat.prime_three Nat.prime_five (by norm_num) (by rw [h]; norm_num))
      · exact hcontr (isSolvable_of_card_pow_mul_pow (p := 2) (q := 5) (a := 2) (b := 1)
          Nat.prime_two Nat.prime_five (by norm_num) (by rw [h]; norm_num))
      ·
        have hcard_sub : Nat.card ↥(S'.subgroupOf (alternatingGroup (Fin 5))) = 30 := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSA).toEquiv, h]
        have hA5simple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
          alternatingGroup.isSimpleGroup_five
        have hidx : (S'.subgroupOf (alternatingGroup (Fin 5))).index = 2 := by
          have hmul := (S'.subgroupOf (alternatingGroup (Fin 5))).card_mul_index
          rw [hcard_sub, card_alternatingGroup_five] at hmul
          omega
        haveI : (S'.subgroupOf (alternatingGroup (Fin 5))).Normal :=
          Subgroup.normal_of_index_eq_two hidx
        rcases hA5simple.eq_bot_or_eq_top_of_normal
          (S'.subgroupOf (alternatingGroup (Fin 5))) with hb | ht
        · rw [hb, Subgroup.card_bot] at hcard_sub
          omega
        · rw [ht, Subgroup.card_top, card_alternatingGroup_five] at hcard_sub
          omega
      · exact hne60 h
    have hS'eq : S' = alternatingGroup (Fin 5) :=
      Subgroup.eq_of_le_of_card_ge hSA (by rw [card_alternatingGroup_five, hS'card])
    have hSle : S ≤ altSubgroup := by
      intro x hx
      rw [Subgroup.mem_prod]
      refine ⟨?_, ?_⟩
      · rw [Subgroup.mem_bot]; exact hg1 ⟨x, hx⟩
      · have hmem : g ⟨x, hx⟩ ∈ S' := MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩
        rw [hS'eq] at hmem
        simpa [g] using hmem
    have hScard : Nat.card S = 60 := by
      rw [Nat.card_congr e'.toEquiv, hS'card]
    have hAltcard : Nat.card altSubgroup = 60 := by
      show Nat.card ↥((⊥ : Subgroup (DihedralGroup 4)).prod
        (alternatingGroup (Fin 5))) = 60
      rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_bot,
        card_alternatingGroup_five]
    exact Subgroup.eq_of_le_of_card_ge hSle (by rw [hAltcard, hScard])

theorem centralizer_altSubgroup :
    Subgroup.centralizer (altSubgroup : Set (DihedralGroup 4 × Equiv.Perm (Fin 5))) =
      dihedralSubgroup := by
  ext x
  simp only [mem_centralizer_iff, SetLike.mem_coe, Subgroup.mem_prod, Subgroup.mem_bot,
    Subgroup.mem_top, true_and, Equiv.Perm.mem_alternatingGroup]
  revert x
  decide +kernel

theorem mem_or_altSubgroup_le_of_normal
    (N : Subgroup (DihedralGroup 4 × Equiv.Perm (Fin 5))) (hN : N.Normal) (hne : N ≠ ⊥) :
    (DihedralGroup.r 2, (1 : Equiv.Perm (Fin 5))) ∈ N ∨ altSubgroup ≤ N := by
  by_cases hA : ∃ d : DihedralGroup 4, d ≠ 1 ∧ (d, 1) ∈ N
  ·
    left
    obtain ⟨d, hd1, hdN⟩ := hA
    rcases r2_eq_mul_or_self_or_commutator d hd1 with h | h | h
    · have heq : (DihedralGroup.r 2, (1 : Equiv.Perm (Fin 5))) =
          (d, (1 : Equiv.Perm (Fin 5))) * (d, (1 : Equiv.Perm (Fin 5))) := by
        refine Prod.ext ?_ ?_
        · simpa using h
        · simp
      rw [heq]
      exact N.mul_mem hdN hdN
    · have heq : (DihedralGroup.r 2, (1 : Equiv.Perm (Fin 5))) =
          (d, (1 : Equiv.Perm (Fin 5))) := by
        refine Prod.ext ?_ ?_
        · simpa using h
        · simp
      rw [heq]
      exact hdN
    · have hconj : (DihedralGroup.r 1 * d * (DihedralGroup.r 1)⁻¹,
          (1 : Equiv.Perm (Fin 5))) ∈ N := by
        have := hN.conj_mem (d, (1 : Equiv.Perm (Fin 5))) hdN
          (DihedralGroup.r 1, (1 : Equiv.Perm (Fin 5)))
        simpa using this
      have hprod : (d, (1 : Equiv.Perm (Fin 5))) *
          (DihedralGroup.r 1 * d * (DihedralGroup.r 1)⁻¹,
            (1 : Equiv.Perm (Fin 5)))⁻¹ ∈ N :=
        N.mul_mem hdN (N.inv_mem hconj)
      have heq : (DihedralGroup.r 2, (1 : Equiv.Perm (Fin 5))) =
          (d, (1 : Equiv.Perm (Fin 5))) *
          (DihedralGroup.r 1 * d * (DihedralGroup.r 1)⁻¹,
            (1 : Equiv.Perm (Fin 5)))⁻¹ := by
        refine Prod.ext ?_ ?_
        · show DihedralGroup.r 2 =
            d * (DihedralGroup.r 1 * d * (DihedralGroup.r 1)⁻¹)⁻¹
          rw [h]
          group
        · simp
      rw [heq]
      exact hprod
  · by_cases hB : ∃ s : Equiv.Perm (Fin 5), s ≠ 1 ∧ (1, s) ∈ N
    ·
      right
      obtain ⟨s, hs1, hsN⟩ := hB
      let P1 : Subgroup (DihedralGroup 4 × Equiv.Perm (Fin 5)) :=
        (⊥ : Subgroup (DihedralGroup 4)).prod (⊤ : Subgroup (Equiv.Perm (Fin 5)))
      let N₀ : Subgroup (DihedralGroup 4 × Equiv.Perm (Fin 5)) := N ⊓ P1
      have hN₀mem : ((1 : DihedralGroup 4), s) ∈ N₀ := by
        rw [Subgroup.mem_inf]
        refine ⟨hsN, ?_⟩
        show ((1 : DihedralGroup 4), s) ∈ (⊥ : Subgroup (DihedralGroup 4)).prod
          (⊤ : Subgroup (Equiv.Perm (Fin 5)))
        rw [Subgroup.mem_prod]
        exact ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top _⟩
      let M : Subgroup (Equiv.Perm (Fin 5)) :=
        N₀.map (MonoidHom.snd (DihedralGroup 4) (Equiv.Perm (Fin 5)))
      have hMnormal : M.Normal := by
        haveI : N.Normal := hN
        have hN₀normal : N₀.Normal := by
          haveI : P1.Normal := by
            show ((⊥ : Subgroup (DihedralGroup 4)).prod
              (⊤ : Subgroup (Equiv.Perm (Fin 5)))).Normal
            infer_instance
          exact Subgroup.normal_inf_normal N P1
        exact hN₀normal.map _ (fun y => ⟨(1, y), rfl⟩)
      have hMne : M ≠ ⊥ := by
        intro hbot
        have hsM : s ∈ M := Subgroup.mem_map.mpr ⟨(1, s), hN₀mem, rfl⟩
        rw [hbot] at hsM
        exact hs1 (Subgroup.mem_bot.mp hsM)
      have hAM : alternatingGroup (Fin 5) ≤ M := by
        haveI : M.Normal := hMnormal
        rcases CFSG.Holt.eq_bot_or_eq_alternatingGroup_or_eq_top_of_normal
          (Λ := Fin 5) (by simp : 5 ≤ Nat.card (Fin 5)) (N := M) with hb | ha | ht
        · exact absurd hb hMne
        · exact ha.ge
        · rw [ht]; exact le_top
      intro x hx
      rw [Subgroup.mem_prod] at hx
      obtain ⟨hxbot, hxA⟩ := hx
      have hxM : x.2 ∈ M := hAM hxA
      obtain ⟨n, hnN₀, hns⟩ := Subgroup.mem_map.mp hxM
      have hns' : n.2 = x.2 := hns
      have hn1 : n.1 = 1 := by
        have := (Subgroup.mem_prod.mp (Subgroup.mem_inf.mp hnN₀).2).1
        simpa using this
      have hx1 : x.1 = 1 := by simpa using hxbot
      have hnx : n = x := by ext <;> simp [hn1, hns', hx1]
      have hnN : n ∈ N := (Subgroup.mem_inf.mp hnN₀).1
      simpa [hnx] using hnN
    ·
      exfalso
      have hA' : ∀ d : DihedralGroup 4, (d, 1) ∈ N → d = 1 := by
        intro d hd
        by_contra hd1
        exact hA ⟨d, hd1, hd⟩
      have hB' : ∀ s : Equiv.Perm (Fin 5), (1, s) ∈ N → s = 1 := by
        intro s hs
        by_contra hs1
        exact hB ⟨s, hs1, hs⟩
      let f : N →* DihedralGroup 4 :=
        (MonoidHom.fst (DihedralGroup 4) (Equiv.Perm (Fin 5))).comp N.subtype
      have hfinj : Function.Injective f := by
        intro x y hxy
        have hxy1 : (x : DihedralGroup 4 × Equiv.Perm (Fin 5)).1 =
            (y : DihedralGroup 4 × Equiv.Perm (Fin 5)).1 := hxy
        have hmem : (x : DihedralGroup 4 × Equiv.Perm (Fin 5)) *
            (y : DihedralGroup 4 × Equiv.Perm (Fin 5))⁻¹ ∈ N :=
          N.mul_mem x.2 (N.inv_mem y.2)
        have hfirst : ((x : DihedralGroup 4 × Equiv.Perm (Fin 5)) *
            (y : DihedralGroup 4 × Equiv.Perm (Fin 5))⁻¹).1 = 1 := by simp [hxy1]
        have hz : ((1 : DihedralGroup 4),
            ((x : DihedralGroup 4 × Equiv.Perm (Fin 5)) *
              (y : DihedralGroup 4 × Equiv.Perm (Fin 5))⁻¹).2) ∈ N := by
          have heq : (x : DihedralGroup 4 × Equiv.Perm (Fin 5)) *
              (y : DihedralGroup 4 × Equiv.Perm (Fin 5))⁻¹ =
              ((1 : DihedralGroup 4),
                ((x : DihedralGroup 4 × Equiv.Perm (Fin 5)) *
                  (y : DihedralGroup 4 × Equiv.Perm (Fin 5))⁻¹).2) := by
            ext <;> simp [hfirst]
          rw [← heq]
          exact hmem
        by_cases hs : ((x : DihedralGroup 4 × Equiv.Perm (Fin 5)) *
            (y : DihedralGroup 4 × Equiv.Perm (Fin 5))⁻¹).2 = 1
        · apply Subtype.ext
          have h1 : (x : DihedralGroup 4 × Equiv.Perm (Fin 5)) *
              (y : DihedralGroup 4 × Equiv.Perm (Fin 5))⁻¹ = 1 := by
            ext <;> simp [hfirst, hs]
          exact mul_inv_eq_one.mp h1
        · exact absurd (hB' _ hz) hs
      let g : N →* Equiv.Perm (Fin 5) :=
        (MonoidHom.snd (DihedralGroup 4) (Equiv.Perm (Fin 5))).comp N.subtype
      have hginj : Function.Injective g := by
        intro x y hxy
        have hxy2 : (x : DihedralGroup 4 × Equiv.Perm (Fin 5)).2 =
            (y : DihedralGroup 4 × Equiv.Perm (Fin 5)).2 := hxy
        have hmem : (x : DihedralGroup 4 × Equiv.Perm (Fin 5)) *
            (y : DihedralGroup 4 × Equiv.Perm (Fin 5))⁻¹ ∈ N :=
          N.mul_mem x.2 (N.inv_mem y.2)
        have hsecond : ((x : DihedralGroup 4 × Equiv.Perm (Fin 5)) *
            (y : DihedralGroup 4 × Equiv.Perm (Fin 5))⁻¹).2 = 1 := by simp [hxy2]
        have hz : (((x : DihedralGroup 4 × Equiv.Perm (Fin 5)) *
            (y : DihedralGroup 4 × Equiv.Perm (Fin 5))⁻¹).1,
            (1 : Equiv.Perm (Fin 5))) ∈ N := by
          have heq : (x : DihedralGroup 4 × Equiv.Perm (Fin 5)) *
              (y : DihedralGroup 4 × Equiv.Perm (Fin 5))⁻¹ =
              (((x : DihedralGroup 4 × Equiv.Perm (Fin 5)) *
                (y : DihedralGroup 4 × Equiv.Perm (Fin 5))⁻¹).1,
                (1 : Equiv.Perm (Fin 5))) := by
            ext <;> simp [hsecond]
          rw [← heq]
          exact hmem
        by_cases hd : ((x : DihedralGroup 4 × Equiv.Perm (Fin 5)) *
            (y : DihedralGroup 4 × Equiv.Perm (Fin 5))⁻¹).1 = 1
        · apply Subtype.ext
          have h1 : (x : DihedralGroup 4 × Equiv.Perm (Fin 5)) *
              (y : DihedralGroup 4 × Equiv.Perm (Fin 5))⁻¹ = 1 := by
            ext <;> simp [hd, hsecond]
          exact mul_inv_eq_one.mp h1
        · exact absurd (hA' _ hz) hd
      let M : Subgroup (Equiv.Perm (Fin 5)) :=
        N.map (MonoidHom.snd (DihedralGroup 4) (Equiv.Perm (Fin 5)))
      have hMnormal : M.Normal :=
        hN.map (MonoidHom.snd (DihedralGroup 4) (Equiv.Perm (Fin 5)))
          (fun y => ⟨(1, y), rfl⟩)
      have hrange : g.range = M := by
        ext y
        rw [MonoidHom.mem_range, Subgroup.mem_map]
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨x, x.2, rfl⟩
        · rintro ⟨x, hxN, rfl⟩
          exact ⟨⟨x, hxN⟩, rfl⟩
      have hMne : M ≠ ⊥ := by
        intro hbot
        apply hne
        rw [eq_bot_iff]
        intro x hxN
        have hgx : g ⟨x, hxN⟩ ∈ M := by
          rw [← hrange]
          exact MonoidHom.mem_range.mpr ⟨⟨x, hxN⟩, rfl⟩
        rw [hbot] at hgx
        have hg1 : g ⟨x, hxN⟩ = 1 := Subgroup.mem_bot.mp hgx
        have h1 : (⟨x, hxN⟩ : N) = 1 := hginj (by rw [hg1, map_one])
        simpa using congrArg Subtype.val h1
      have hAM : alternatingGroup (Fin 5) ≤ M := by
        haveI : M.Normal := hMnormal
        rcases CFSG.Holt.eq_bot_or_eq_alternatingGroup_or_eq_top_of_normal
          (Λ := Fin 5) (by simp : 5 ≤ Nat.card (Fin 5)) (N := M) with hb | ha | ht
        · exact absurd hb hMne
        · exact ha.ge
        · rw [ht]; exact le_top
      have h60M : 60 ≤ Nat.card M := by
        have := Subgroup.card_le_of_le hAM
        rwa [card_alternatingGroup_five] at this
      have hN8 : Nat.card N ≤ 8 := by
        have := Nat.card_le_card_of_injective f hfinj
        rwa [DihedralGroup.nat_card] at this
      have hNM : Nat.card N = Nat.card M := by
        rw [← hrange]
        exact Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv
      omega

section Transport

variable {C : Type*} [Group C] (e : C ≃* DihedralGroup 4 × Equiv.Perm (Fin 5))

theorem mem_center_iff_of_mulEquiv_dihedral_prod_perm (c : C) :
    c ∈ Subgroup.center C ↔ c = 1 ∨ c = e.symm (DihedralGroup.r 2, 1) := by
  rw [show c ∈ Subgroup.center C ↔
      e c ∈ Subgroup.center (DihedralGroup 4 × Equiv.Perm (Fin 5)) from
    (MulEquivClass.apply_mem_center_iff e).symm, mem_center_dihedral_prod_perm_iff,
    map_eq_one_iff e e.injective, ← e.eq_symm_apply]

theorem eq_comap_altSubgroup_of_isSimpleGroup (S : Subgroup C) (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) : S = altSubgroup.comap e.toMonoidHom := by
  have hS' : IsSimpleGroup (S.map (e : C →* DihedralGroup 4 × Equiv.Perm (Fin 5))) :=
    (MulEquiv.isSimpleGroup_congr (e.subgroupMap S)).mp hS
  have hna' : ∃ a b : S.map (e : C →* DihedralGroup 4 × Equiv.Perm (Fin 5)),
      a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    refine ⟨e.subgroupMap S a, e.subgroupMap S b, fun h => hab ?_⟩
    apply (e.subgroupMap S).injective
    rw [map_mul, map_mul]
    exact h
  have h := eq_altSubgroup_of_isSimpleGroup
    (S.map (e : C →* DihedralGroup 4 × Equiv.Perm (Fin 5))) hS' hna'
  rw [← Subgroup.comap_map_eq_self_of_injective
    (f := (e : C →* DihedralGroup 4 × Equiv.Perm (Fin 5))) e.injective S, h]
  rfl

theorem centralizer_comap_altSubgroup :
    Subgroup.centralizer (altSubgroup.comap e.toMonoidHom : Set C) =
      dihedralSubgroup.comap e.toMonoidHom := by
  have hset : (e.symm '' (altSubgroup : Set (DihedralGroup 4 × Equiv.Perm (Fin 5)))) =
      (altSubgroup.comap e.toMonoidHom : Set C) := by
    ext c
    rw [Set.mem_image, SetLike.mem_coe, Subgroup.mem_comap]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hc
      exact ⟨e c, hc, e.symm_apply_apply c⟩
  have hmap := map_centralizer_mulEquiv e.symm
    (altSubgroup : Set (DihedralGroup 4 × Equiv.Perm (Fin 5)))
  rw [← hset, ← hmap, centralizer_altSubgroup]
  exact Subgroup.map_equiv_eq_comap_symm e.symm dihedralSubgroup

theorem mem_or_comap_altSubgroup_le_of_normal (N : Subgroup C) (hN : N.Normal) (hne : N ≠ ⊥) :
    e.symm (DihedralGroup.r 2, 1) ∈ N ∨ altSubgroup.comap e.toMonoidHom ≤ N := by
  have hNmap : (N.map (e : C →* DihedralGroup 4 × Equiv.Perm (Fin 5))).Normal :=
    hN.map (e : C →* DihedralGroup 4 × Equiv.Perm (Fin 5)) e.surjective
  have hNmap_ne : N.map (e : C →* DihedralGroup 4 × Equiv.Perm (Fin 5)) ≠ ⊥ := by
    intro hbot
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hxmap : e x ∈ N.map (e : C →* DihedralGroup 4 × Equiv.Perm (Fin 5)) :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hbot] at hxmap
    have hx1 : e x = 1 := Subgroup.mem_bot.mp hxmap
    have h1 : x = 1 := e.injective (by rw [hx1, map_one])
    simpa using h1
  rcases mem_or_altSubgroup_le_of_normal
    (N.map (e : C →* DihedralGroup 4 × Equiv.Perm (Fin 5))) hNmap hNmap_ne with hmem | hle
  · left
    obtain ⟨n, hnN, hne'⟩ := Subgroup.mem_map.mp hmem
    have hn : n = e.symm (DihedralGroup.r 2, 1) := by
      have := congrArg e.symm hne'
      simpa using this
    rwa [hn] at hnN
  · right
    rw [← Subgroup.comap_map_eq_self_of_injective
      (f := (e : C →* DihedralGroup 4 × Equiv.Perm (Fin 5))) e.injective N]
    exact Subgroup.comap_mono hle

theorem nonempty_mulEquiv_alternatingGroup_comap_altSubgroup :
    Nonempty (↥(altSubgroup.comap e.toMonoidHom) ≃* alternatingGroup (Fin 5)) := by
  have hmap : ((altSubgroup.comap (e : C →* DihedralGroup 4 × Equiv.Perm (Fin 5))).map
      (e : C →* DihedralGroup 4 × Equiv.Perm (Fin 5))) = altSubgroup :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective altSubgroup
  refine ⟨(e.subgroupMap (altSubgroup.comap (e : C →* DihedralGroup 4 × Equiv.Perm (Fin 5)))).trans ?_⟩
  rw [hmap]
  exact (Subgroup.prodEquiv (⊥ : Subgroup (DihedralGroup 4))
      (alternatingGroup (Fin 5))).trans (MulEquiv.uniqueProd)

theorem card_comap_dihedralSubgroup :
    Nat.card ↥(dihedralSubgroup.comap e.toMonoidHom) = 8 := by
  have hmap : ((dihedralSubgroup.comap (e : C →* DihedralGroup 4 × Equiv.Perm (Fin 5))).map
      (e : C →* DihedralGroup 4 × Equiv.Perm (Fin 5))) = dihedralSubgroup :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective dihedralSubgroup
  have hcardK : Nat.card ↥(dihedralSubgroup.comap e.toMonoidHom) =
      Nat.card ↥dihedralSubgroup := by
    conv_rhs => rw [← hmap]
    exact Nat.card_congr
      (e.subgroupMap (dihedralSubgroup.comap (e : C →* DihedralGroup 4 × Equiv.Perm (Fin 5)))).toEquiv
  have hdih : Nat.card ↥dihedralSubgroup = 8 := by
    show Nat.card ↥((⊤ : Subgroup (DihedralGroup 4)).prod
      (⊥ : Subgroup (Equiv.Perm (Fin 5)))) = 8
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_top,
      Subgroup.card_bot, DihedralGroup.nat_card]
  rw [hcardK, hdih]

end Transport

end CFSG.EvenSporadicStandard.TwoHS.GH312
