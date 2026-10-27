module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.AGLEmbedding.KFactProofs.L28Local

open MulAction in
theorem card_modEq_one_of_free {S X : Type*} [Group S] [Finite S] [Finite X] [MulAction S X]
    (x₀ : X) (h₀ : ∀ s : S, s • x₀ = x₀)
    (hfree : ∀ x, x ≠ x₀ → ∀ s : S, s • x = x → s = 1) :
    Nat.card X ≡ 1 [MOD Nat.card S] := by
  classical
  have := Fintype.ofFinite S
  have := Fintype.ofFinite X
  have : Fintype (Quotient (orbitRel S X)) := Fintype.ofFinite _
  have hB := sum_card_fixedBy_eq_card_orbits_mul_card_group S X
  have hfix : ∀ s : S, s ≠ 1 → Fintype.card (fixedBy X s) = 1 := by
    intro s hs
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨x₀, h₀ s⟩, fun ⟨x, hx⟩ => ?_⟩
    by_contra hne
    exact hs (hfree x (fun h => hne (Subtype.ext h)) s hx)
  have h1 : Fintype.card (fixedBy X (1 : S)) = Fintype.card X := by
    apply Fintype.card_congr
    exact Equiv.subtypeUnivEquiv (fun x => one_smul S x)
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : S))] at hB
  rw [Finset.sum_congr rfl (fun s hs => hfix s (Finset.ne_of_mem_erase hs))] at hB
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hB
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, h1] at hB
  rw [Nat.card_eq_fintype_card (α := X), Nat.card_eq_fintype_card (α := S)]
  have hS : 0 < Fintype.card S := Fintype.card_pos
  have hX : 0 < Fintype.card X := Fintype.card_pos_iff.2 ⟨x₀⟩
  have hd : Fintype.card S ∣
      Fintype.card (Quotient (orbitRel S X)) * Fintype.card S - Fintype.card S :=
    Nat.dvd_sub (Dvd.intro_left _ rfl) dvd_rfl
  have : Fintype.card X - 1 =
      Fintype.card (Quotient (orbitRel S X)) * Fintype.card S - Fintype.card S := by
    omega
  exact ((Nat.modEq_iff_dvd' hX).2 (by rw [this]; exact hd)).symm

structure L28Data (G : Type*) [Group G] (T : Subgroup G) : Prop where
  card_group : Nat.card G = 504
  card_eq : Nat.card T = 9
  card_normalizer : Nat.card (Subgroup.normalizer (T : Set G)) = 18
  centralizer_le : ∀ t ∈ T, t ≠ 1 → ∀ g : G, g * t = t * g → g ∈ T
  inv : ∃ s ∈ Subgroup.normalizer (T : Set G), ∀ x ∈ T, s * x * s⁻¹ = x → x = 1
  aut : ∀ f : MulAut G, (∀ x ∈ T, f x = x) → ∃ t ∈ T, f = MulAut.conj t

namespace L28Data

section Transport

variable {G G' : Type*} [Group G] [Group G'] {T : Subgroup G} {T' : Subgroup G'}

theorem map (e : G ≃* G') (hT : ∀ g, g ∈ T ↔ e g ∈ T') (h : L28Data G T) : L28Data G' T' := by
  have hT' : ∀ y, y ∈ T' ↔ e.symm y ∈ T := fun y => by simpa using (hT (e.symm y)).symm
  have hnorm : ∀ n : G, n ∈ Subgroup.normalizer (T : Set G) ↔
      e n ∈ Subgroup.normalizer (T' : Set G') := by
    intro n
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro hn y
      rw [hT' y, hT' (e n * y * (e n)⁻¹)]
      simpa using hn (e.symm y)
    · intro hn x
      have h1 := hn (e x)
      have e1 : e n * e x * (e n)⁻¹ = e (n * x * n⁻¹) := by simp
      rw [e1, ← hT, ← hT] at h1
      exact h1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h.card_group]
    exact (Nat.card_congr e.toEquiv).symm
  · rw [← h.card_eq]
    refine Nat.card_congr (Equiv.symm ?_)
    exact
      { toFun := fun x => ⟨e x, (hT x).1 x.2⟩
        invFun := fun y => ⟨e.symm y, (hT' y).1 y.2⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun y => Subtype.ext (by simp) }
  · rw [← h.card_normalizer]
    refine Nat.card_congr (Equiv.symm ?_)
    exact
      { toFun := fun x => ⟨e x, (hnorm x).1 x.2⟩
        invFun := fun y => ⟨e.symm y, (hnorm _).2 (by simp)⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun y => Subtype.ext (by simp) }
  · intro t' ht' ht1 g' hg
    have ht : e.symm t' ∈ T := (hT' t').1 ht'
    have h1 : e.symm t' ≠ 1 := fun h1 => ht1 (by simpa using congrArg e h1)
    have h2 : e.symm g' * e.symm t' = e.symm t' * e.symm g' := by
      rw [← map_mul, ← map_mul, hg]
    exact (hT' g').2 (h.centralizer_le _ ht h1 _ h2)
  · obtain ⟨s, hs, hsx⟩ := h.inv
    refine ⟨e s, (hnorm s).1 hs, fun x' hx' hfix => ?_⟩
    have hx : e.symm x' ∈ T := (hT' x').1 hx'
    have h1 : s * e.symm x' * s⁻¹ = e.symm x' := by
      apply e.injective
      simpa using hfix
    simpa using congrArg e (hsx _ hx h1)
  · intro f' hf'
    let f : MulAut G := e.trans (f'.trans e.symm)
    have hf : ∀ t ∈ T, f t = t := by
      intro t ht
      show e.symm (f' (e t)) = t
      rw [hf' (e t) ((hT t).1 ht)]
      simp
    obtain ⟨t, ht, hconj⟩ := h.aut f hf
    refine ⟨e t, (hT t).1 ht, ?_⟩
    ext x'
    have h1 := congrArg (fun φ : MulAut G => φ (e.symm x')) hconj
    have h2 : f (e.symm x') = e.symm (f' x') := by
      show e.symm (f' (e (e.symm x'))) = _
      simp
    simp only [h2, MulAut.conj_apply] at h1
    simpa using congrArg e h1

end Transport

section Basic

variable {G : Type*} [Group G] [Finite G] {T : Subgroup G}

omit [Finite G] in
theorem commute (h : L28Data G T) : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hx y hy
  have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := T)
    (by rw [h.card_eq]; norm_num)
  exact congrArg Subtype.val (this.is_comm.comm (⟨x, hx⟩ : T) ⟨y, hy⟩)

theorem exists_ne_one (h : L28Data G T) : ∃ t ∈ T, t ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : Nat.card T ≤ 1 := by
    rw [Finite.card_le_one_iff_subsingleton]
    exact ⟨fun a b => Subtype.ext ((hcon a a.2).trans (hcon b b.2).symm)⟩
  rw [h.card_eq] at this
  omega

theorem mem_normalizer_of_conj_mem (h : L28Data G T) {x y : G} (hx : x ∈ T) (hx1 : x ≠ 1)
    (hy : y⁻¹ * x * y ∈ T) : y ∈ Subgroup.normalizer (T : Set G) := by
  have hx1' : y⁻¹ * x * y ≠ 1 := by
    intro h1
    apply hx1
    have h2 : y * (y⁻¹ * x * y) * y⁻¹ = y * 1 * y⁻¹ := by rw [h1]
    simpa [mul_assoc] using h2
  have key : ∀ w ∈ T, y⁻¹ * w * y ∈ T := by
    intro w hw
    refine h.centralizer_le (y⁻¹ * x * y) hy hx1' (y⁻¹ * w * y) ?_
    calc y⁻¹ * w * y * (y⁻¹ * x * y) = y⁻¹ * (w * x) * y := by group
      _ = y⁻¹ * (x * w) * y := by rw [h.commute w hw x hx]
      _ = y⁻¹ * x * y * (y⁻¹ * w * y) := by group
  have hinv : y⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.mem_normalizer_fintype (fun n hn => by simpa using key n hn)
  simpa using Subgroup.inv_mem _ hinv

omit [Finite G] in
theorem mem_of_mem_normalizer_pow (h : L28Data G T) {z : G}
    (hz : z ∈ Subgroup.normalizer (T : Set G)) (hz9 : z ^ 9 = 1) : z ∈ T := by
  set N := Subgroup.normalizer (T : Set G) with hN
  have hTN : T ≤ N := Subgroup.le_normalizer
  let H : Subgroup N := T.subgroupOf N
  have hHcard : Nat.card H = 9 := by
    rw [← h.card_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv
  have hidx : H.index = 2 := by
    have := H.index_mul_card
    rw [hHcard, h.card_normalizer] at this
    omega
  have hq2 : ∀ q : N ⧸ H, q ^ 2 = 1 := by
    intro q
    have := pow_card_eq_one' (G := N ⧸ H) (x := q)
    rwa [show Nat.card (N ⧸ H) = 2 from hidx] at this
  have hq9 : ((⟨z, hz⟩ : N) : N ⧸ H) ^ 9 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨z, hz⟩ : N) ^ 9 = 1 := Subtype.ext (by simpa using hz9)
    rw [this]
    rfl
  have hq1 : ((⟨z, hz⟩ : N) : N ⧸ H) = 1 := by
    have h1 := orderOf_dvd_of_pow_eq_one hq9
    have h2 := orderOf_dvd_of_pow_eq_one (hq2 ((⟨z, hz⟩ : N) : N ⧸ H))
    have h3 : orderOf (((⟨z, hz⟩ : N) : N ⧸ H)) ∣ Nat.gcd 9 2 := Nat.dvd_gcd h1 h2
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 (by simpa using h3))
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hq1)

omit [Finite G] in
theorem pow_nine_eq_one (h : L28Data G T) {x : G} (hx : x ∈ T) : x ^ 9 = 1 := by
  have h9 := pow_card_eq_one' (G := T) (x := (⟨x, hx⟩ : T))
  rw [h.card_eq] at h9
  simpa using congrArg Subtype.val h9

theorem maximal (h : L28Data G T) {Y : Subgroup G} (hY : Subgroup.normalizer (T : Set G) ≤ Y) :
    Y = Subgroup.normalizer (T : Set G) ∨ Y = ⊤ := by
  set N := Subgroup.normalizer (T : Set G) with hN
  have hTN : T ≤ N := Subgroup.le_normalizer
  have hTY : T ≤ Y := hTN.trans hY
  let H : Subgroup Y := N.subgroupOf Y
  let S : Subgroup Y := T.subgroupOf Y
  have hScard : Nat.card S = 9 := by
    rw [← h.card_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY).toEquiv
  have hS : ∀ s : S, ((s : Y) : G) ∈ T := fun s => Subgroup.mem_subgroupOf.1 s.2
  have hmod : Nat.card (Y ⧸ H) ≡ 1 [MOD Nat.card S] := by
    refine card_modEq_one_of_free (S := S) (X := Y ⧸ H) ((1 : Y) : Y ⧸ H) ?_ ?_
    · intro s
      change (((s : Y) * 1 : Y) : Y ⧸ H) = ((1 : Y) : Y ⧸ H)
      rw [QuotientGroup.eq]
      exact Subgroup.mem_subgroupOf.2 (by simpa using hTN (T.inv_mem (hS s)))
    · intro x hx s hsx
      by_contra hs1
      induction x using QuotientGroup.induction_on with
      | _ y =>
        change (((s : Y) * y : Y) : Y ⧸ H) = (y : Y ⧸ H) at hsx
        rw [QuotientGroup.eq] at hsx
        have hsx' : (y : G)⁻¹ * ((s : Y) : G)⁻¹ * (y : G) ∈ N := by
          have := Subgroup.mem_subgroupOf.1 hsx
          simpa [mul_assoc] using this
        have hs1' : ((s : Y) : G) ≠ 1 := fun h1 => hs1 (Subtype.ext (Subtype.ext h1))
        have hz9 : ((y : G)⁻¹ * ((s : Y) : G)⁻¹ * (y : G)) ^ 9 = 1 := by
          have h9 : (((s : Y) : G)⁻¹) ^ 9 = 1 := by
            rw [inv_pow, h.pow_nine_eq_one (hS s), inv_one]
          have := conj_pow (a := (y : G)⁻¹) (b := ((s : Y) : G)⁻¹) (i := 9)
          simp only [inv_inv] at this
          rw [this, h9]
          group
        have hzT := h.mem_of_mem_normalizer_pow hsx' hz9
        have hyN := h.mem_normalizer_of_conj_mem (T.inv_mem (hS s)) (inv_ne_one.2 hs1') hzT
        apply hx
        rw [QuotientGroup.eq]
        exact Subgroup.mem_subgroupOf.2 (by simpa using N.inv_mem hyN)
  rw [hScard] at hmod
  have hidx : N.index = 28 := by
    have := N.card_mul_index
    rw [h.card_normalizer, h.card_group] at this
    omega
  have hdvd : N.relIndex Y ∣ 28 := hidx ▸ Subgroup.relIndex_dvd_index_of_le hY
  have hn : N.relIndex Y = Nat.card (Y ⧸ H) := rfl
  rw [← hn] at hmod
  have hpos : 0 < N.relIndex Y := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hle : N.relIndex Y ≤ 28 := Nat.le_of_dvd (by norm_num) hdvd
  have hcases : N.relIndex Y = 1 ∨ N.relIndex Y = 28 := by
    unfold Nat.ModEq at hmod
    generalize N.relIndex Y = n at hdvd hpos hle hmod
    interval_cases n <;> omega
  rcases hcases with h1 | h1
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.1 h1) hY)
  · right
    have := Subgroup.relIndex_mul_index hY
    rw [h1, hidx] at this
    exact Subgroup.index_eq_one.1 (by omega)

theorem eq_bot_of_normal (h : L28Data G T) {M : Subgroup G}
    (hMN : M ≤ Subgroup.normalizer (T : Set G))
    (hM : (M.subgroupOf (Subgroup.normalizer (T : Set G))).Normal)
    (hcop : Nat.Coprime 3 (Nat.card M)) : M = ⊥ := by
  have hMT : M ⊓ T = ⊥ := by
    have h9 : Nat.Coprime 9 (Nat.card M) := by
      simpa using Nat.Coprime.pow_left 2 hcop
    have h1 : Nat.card (M ⊓ T : Subgroup G) ∣ Nat.card M := Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (M ⊓ T : Subgroup G) ∣ 9 := h.card_eq ▸ Subgroup.card_dvd_of_le inf_le_right
    have h3 : Nat.card (M ⊓ T : Subgroup G) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 h9) h1
    exact Subgroup.card_eq_one.1 h3
  have hcomm : ∀ m ∈ M, ∀ u ∈ T, m * u = u * m := by
    intro m hm u hu
    have huN : u ∈ Subgroup.normalizer (T : Set G) := Subgroup.le_normalizer hu
    have h1 : m * u * m⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hMN hm) u).1 hu
    have h2 : u * m⁻¹ * u⁻¹ ∈ M := by
      have := hM.conj_mem ⟨m⁻¹, hMN (M.inv_mem hm)⟩
        (Subgroup.mem_subgroupOf.2 (M.inv_mem hm)) ⟨u, huN⟩
      exact Subgroup.mem_subgroupOf.1 this
    have hc : m * u * m⁻¹ * u⁻¹ ∈ M ⊓ T :=
      ⟨by
        have := M.mul_mem hm h2
        simpa [mul_assoc] using this,
       T.mul_mem h1 (T.inv_mem hu)⟩
    rw [hMT, Subgroup.mem_bot] at hc
    have : m * u * m⁻¹ = u := by
      have := congrArg (· * u) hc
      simpa [mul_assoc] using this
    calc m * u = m * u * m⁻¹ * m := by group
      _ = u * m := by rw [this]
  rw [eq_bot_iff]
  intro m hm
  obtain ⟨t, ht, ht1⟩ := h.exists_ne_one
  have hmT : m ∈ T := h.centralizer_le t ht ht1 m (hcomm m hm t ht)
  have : m ∈ M ⊓ T := ⟨hm, hmT⟩
  rwa [hMT] at this

omit [Finite G] in
theorem eq_one_of_fixes_normalizer (h : L28Data G T) {f : MulAut G}
    (hf : ∀ k ∈ Subgroup.normalizer (T : Set G), f k = k) : f = 1 := by
  obtain ⟨t, htT, rfl⟩ := h.aut f (fun x hx => hf x (Subgroup.le_normalizer hx))
  obtain ⟨s, hsN, hs⟩ := h.inv
  have h1 : t * s * t⁻¹ = s := by simpa [MulAut.conj_apply] using hf s hsN
  have h2 : t * s = s * t := by
    calc t * s = t * s * t⁻¹ * t := by group
      _ = s * t := by rw [h1]
  have : t = 1 := hs t htT (by
    calc s * t * s⁻¹ = t * s * s⁻¹ := by rw [h2]
      _ = t := by group)
  rw [this, map_one]

theorem isSolvable_normalizer (h : L28Data G T) :
    Group.IsSolvable (Subgroup.normalizer (T : Set G)) := by
  set N := Subgroup.normalizer (T : Set G) with hN
  have hTN : T ≤ N := Subgroup.le_normalizer
  let H : Subgroup N := T.subgroupOf N
  have hHcard : Nat.card H = 9 := by
    rw [← h.card_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv
  have hidx : H.index = 2 := by
    have := H.index_mul_card
    rw [hHcard, h.card_normalizer] at this
    omega
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : Group.IsSolvable H :=
    haveI : IsPGroup 3 H := IsPGroup.of_card (n := 2) (by rw [hHcard]; norm_num)
    haveI := this.isNilpotent
    inferInstance
  have hQ : Group.IsSolvable (N ⧸ H) :=
    haveI : IsPGroup 2 (N ⧸ H) :=
      IsPGroup.of_card (n := 1) (by rw [show Nat.card (N ⧸ H) = 2 from hidx]; norm_num)
    haveI := this.isNilpotent
    inferInstance
  exact Group.isSolvable_of_ker_le_range H.subtype (QuotientGroup.mk' H)
    (by simp [QuotientGroup.ker_mk'])

theorem conj_injective (h : L28Data G T) : Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  have hc : ∀ x : G, g * x = x * g := fun x => by
    have := congrArg (fun α : MulAut G => α x) (MonoidHom.mem_ker.mp hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [this]
  obtain ⟨t, ht, ht1⟩ := h.exists_ne_one
  have hgT : g ∈ T := h.centralizer_le t ht ht1 g (hc t)
  obtain ⟨s, -, hs⟩ := h.inv
  rw [Subgroup.mem_bot]
  exact hs g hgT (by
    calc s * g * s⁻¹ = g * s * s⁻¹ := by rw [hc s]
      _ = g := by group)

end Basic

theorem normal_range_conj (K : Type*) [Group K] :
    (MulAut.conj : K →* MulAut K).range.Normal where
  conj_mem := by
    rintro _ ⟨k, rfl⟩ g
    refine ⟨g k, ?_⟩
    ext x
    simp [MulAut.mul_apply, MulAut.conj_apply]

theorem isPGroup_stabilizer {K : Type*} [Group K] [Finite K]
    (hdata : ∀ T : Sylow 3 K, L28Data K (T : Subgroup K))
    (hcard : Nat.card (MulAut K) = 1512) {t : K} (ht : orderOf t = 3) :
    IsPGroup 3 (MulAction.stabilizer (MulAut K) t) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, htT⟩ : ∃ T : Sylow 3 K, t ∈ (T : Subgroup K) := by
    have hp : IsPGroup 3 (Subgroup.zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; norm_num)
    obtain ⟨T, hT⟩ := hp.exists_le_sylow
    exact ⟨T, hT (Subgroup.mem_zpowers t)⟩
  have hd := hdata T
  have ht1 : t ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht; omega
  have := normal_range_conj K
  have hinj := hd.conj_injective
  have hI : (MulAut.conj : K →* MulAut K).range.index = 3 := by
    have h1 := (MulAut.conj : K →* MulAut K).range.card_mul_index
    have h2 : Nat.card (MulAut.conj : K →* MulAut K).range = 504 := by
      rw [← hd.card_group]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rw [h2, hcard] at h1
    omega
  intro f
  refine ⟨3, ?_⟩
  have hft : (f : MulAut K) t = t := by
    simpa [MulAut.smul_def] using MulAction.mem_stabilizer_iff.1 f.2
  have hfk : ∀ k : ℕ, ((f : MulAut K) ^ k) t = t := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, MulAut.mul_apply, hft, ih]
  have h3 : (f : MulAut K) ^ 3 ∈ (MulAut.conj : K →* MulAut K).range := by
    have := Subgroup.pow_index_mem (MulAut.conj : K →* MulAut K).range (f : MulAut K)
    rwa [hI] at this
  obtain ⟨n, hn⟩ := h3
  have hnt : n * t = t * n := by
    have h1 := hfk 3
    rw [← hn] at h1
    simp only [MulAut.conj_apply] at h1
    calc n * t = n * t * n⁻¹ * n := by group
      _ = t * n := by rw [h1]
  have hnT : n ∈ (T : Subgroup K) := hd.centralizer_le t htT ht1 n hnt
  have hn9 : n ^ 9 = 1 := hd.pow_nine_eq_one hnT
  apply Subtype.ext
  rw [Subgroup.coe_pow, show 3 ^ 3 = 3 * 9 by norm_num, pow_mul, ← hn, ← map_pow, hn9, map_one]
  rfl

end L28Data

end CFSG.AGLEmbedding.KFactProofs.L28Local
