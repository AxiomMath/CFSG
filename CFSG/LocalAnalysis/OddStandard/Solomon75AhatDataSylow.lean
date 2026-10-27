module

public import CFSG.LocalAnalysis.OddStandard.Solomon75CoreHyp
public import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Succ
public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataLift

public section

namespace CFSG.OddStandard.Solomon75.AhatData

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

theorem card_eq_card_map_mul_card_ker {G H : Type*} [Group G] [Group H] (f : G →* H)
    (T : Subgroup G) (hT : f.ker ≤ T) :
    Nat.card T = Nat.card (T.map f) * Nat.card f.ker := by
  let g : T →* H := f.comp T.subtype
  have h1 := Subgroup.card_mul_index g.ker
  rw [Subgroup.index_ker] at h1
  have hrange : g.range = T.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card g.ker = Nat.card f.ker := by
    have : g.ker = f.ker.subgroupOf T := (MonoidHom.comap_ker f T.subtype).symm
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv
  rw [← h1, hker, hrange, mul_comm]

theorem exists_not_mem_of_card_lt {G : Type*} [Group G] [Finite G] (E : Subgroup G) (l : List G)
    (h : l.length < Nat.card E) : ∃ x ∈ E, x ∉ l := by
  classical
  by_contra H
  push Not at H
  have hsub : (E : Set G) ⊆ (l.toFinset : Set G) := fun x hx => by simpa using H x hx
  have h1 : Nat.card E = (E : Set G).ncard := Nat.card_coe_set_eq (E : Set G)
  have h2 : (E : Set G).ncard ≤ (l.toFinset : Set G).ncard :=
    Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  have h3 : (l.toFinset : Set G).ncard = l.toFinset.card := Set.ncard_coe_finset _
  have h4 : l.toFinset.card ≤ l.length := List.toFinset_card_le l
  omega

theorem exists_conj_of_sylow {K : Type*} [Group K] [Finite K] (P Q : Subgroup K)
    (hP : IsPGroup 2 P) (hQ : IsPGroup 2 Q) (hPi : ¬ 2 ∣ P.index) (hQi : ¬ 2 ∣ Q.index) :
    ∃ k : K, ∀ x : K, x ∈ P ↔ k⁻¹ * x * k ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K (hQ.toSylow hQi) (hP.toSylow hPi)
  refine ⟨k, fun x => ?_⟩
  have h1 : ((k • hQ.toSylow hQi : Sylow 2 K) : Subgroup K) = P := by
    rw [hk]
    simp
  rw [← h1, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]

theorem isElemAbelian_of_sq {K : Type*} [Group K] {E : Subgroup K} (h : ∀ e ∈ E, e * e = 1) :
    CFSG.Open.IsElemAbelian 2 E := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => by rw [pow_two]; exact h x hx⟩
  have hxy : (a : K) * b * ((a : K) * b) = 1 := h _ (E.mul_mem a.2 b.2)
  have ha := h a a.2
  have hb := h b b.2
  have hai : (a : K)⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : (b : K)⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h' : (a : K) * b = ((a : K) * b)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
  rw [mul_inv_rev, hai, hbi] at h'
  exact h'

theorem sq_of_isElemAbelian {K : Type*} [Group K] {E : Subgroup K}
    (h : CFSG.Open.IsElemAbelian 2 E) : ∀ e ∈ E, e * e = 1 := fun e he => by
  rw [← pow_two]
  exact h.2 e he

theorem comm_of_isElemAbelian {K : Type*} [Group K] {E : Subgroup K}
    (h : CFSG.Open.IsElemAbelian 2 E) {x y : K} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x :=
  CFSG.Open.IsElemAbelian.comm h hx hy

@[expose] def kleinSub {G : Type*} [Group G] (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : Subgroup G where
  carrier := {x | x = 1 ∨ x = a ∨ x = b ∨ x = a * b}
  mul_mem' := by
    have h1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
    have h2 : b * (a * b) = a := by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]
    have h3 : (a * b) * a = b := by rw [mul_assoc, ← hab, h1]
    have h4 : (a * b) * b = a := by rw [mul_assoc, hb, mul_one]
    have h5 : (a * b) * (a * b) = 1 := by rw [mul_assoc, h2, ha]
    rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp [h1, h2, h3, h4, h5, ha, hb, hab.symm]
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro x (rfl | rfl | rfl | rfl)
    · simp
    · simp [inv_eq_of_mul_eq_one_right ha]
    · simp [inv_eq_of_mul_eq_one_right hb]
    · simp [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb, hab.symm]

theorem mem_kleinSub {G : Type*} [Group G] {a b : G} {ha : a * a = 1} {hb : b * b = 1}
    {hab : a * b = b * a} {x : G} :
    x ∈ kleinSub a b ha hb hab ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := Iff.rfl

theorem card_kleinSub {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    Nat.card (kleinSub a b ha hb hab) = 4 := by
  have hset : ((kleinSub a b ha hb hab : Subgroup G) : Set G) = {1, a, b, a * b} := by
    ext x
    simp [mem_kleinSub]
  have h1 : Nat.card (kleinSub a b ha hb hab) =
      ((kleinSub a b ha hb hab : Subgroup G) : Set G).ncard :=
    Nat.card_coe_set_eq _
  rw [h1, hset]
  have hab1 : a * b ≠ 1 := fun h => hne (by
    have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, inv_eq_of_mul_eq_one_right ha])
  have hab2 : a * b ≠ a := fun h => hb1 (by simpa using h)
  have hab3 : a * b ≠ b := fun h => ha1 (by simpa using h)
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hab3.symm]
  · simp [hne, hab2.symm]
  · simp [ha1.symm, hb1.symm, hab1.symm]

@[expose] def pairSub {G : Type*} [Group G] (a : G) (ha : a * a = 1) : Subgroup G where
  carrier := {x | x = 1 ∨ x = a}
  mul_mem' := by
    rintro x y (rfl | rfl) (rfl | rfl) <;> simp [ha]
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro x (rfl | rfl)
    · simp
    · simp [inv_eq_of_mul_eq_one_right ha]

theorem mem_pairSub {G : Type*} [Group G] {a : G} {ha : a * a = 1} {x : G} :
    x ∈ pairSub a ha ↔ x = 1 ∨ x = a := Iff.rfl

theorem card_pairSub {G : Type*} [Group G] {a : G} (ha : a * a = 1) (ha1 : a ≠ 1) :
    Nat.card (pairSub a ha) = 2 := by
  have hset : ((pairSub a ha : Subgroup G) : Set G) = {1, a} := by
    ext x
    simp [mem_pairSub]
  have h1 : Nat.card (pairSub a ha) = ((pairSub a ha : Subgroup G) : Set G).ncard :=
    Nat.card_coe_set_eq _
  rw [h1, hset, Set.ncard_pair ha1.symm]

theorem pairSub_le_kleinSub {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : pairSub a ha ≤ kleinSub a b ha hb hab := by
  rintro x (rfl | rfl)
  · exact Subgroup.one_mem _
  · exact Or.inr (Or.inl rfl)

theorem pairSub_le_of_mem {G : Type*} [Group G] {a : G} (ha : a * a = 1) {H : Subgroup G}
    (h : a ∈ H) : pairSub a ha ≤ H := by
  rintro x (rfl | rfl)
  · exact H.one_mem
  · exact h

theorem exists_indep4 {n : ℕ} {E : Subgroup (Perm (Fin n))} (hE : ∀ e ∈ E, e = 1 ∨ IsoI e)
    (hcard : 8 < Nat.card E) :
    ∃ a ∈ E, ∃ b ∈ E, ∃ c ∈ E, ∃ d ∈ E, IsoI a ∧ IsoI b ∧ IsoI c ∧ IsoI d ∧
      Indep2 a b ∧ Indep3 a b c ∧ Indep4 a b c d := by
  have hsq : ∀ e ∈ E, e * e = 1 := fun e he =>
    (hE e he).elim (fun h => by rw [h, one_mul]) (fun h => h.1)
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    comm_of_isElemAbelian (isElemAbelian_of_sq hsq) hx hy
  have hinv : ∀ x ∈ E, ∀ y, x * y = 1 → y = x := fun x hx y h => by
    rw [eq_inv_of_mul_eq_one_right h]
    exact inv_eq_of_mul_eq_one_right (hsq x hx)
  obtain ⟨a, ha, ha1⟩ := exists_not_mem_of_card_lt E [1] (by simp; omega)
  obtain ⟨b, hb, hb1⟩ := exists_not_mem_of_card_lt E [1, a] (by simp; omega)
  obtain ⟨c, hc, hc1⟩ := exists_not_mem_of_card_lt E [1, a, b, a * b] (by simp; omega)
  obtain ⟨d, hd, hd1⟩ := exists_not_mem_of_card_lt E
    [1, a, b, a * b, c, a * c, b * c, a * b * c] (by simp; omega)
  simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at ha1 hb1 hc1 hd1
  have hab := mul_mem ha hb
  have hac := mul_mem ha hc
  have hbc := mul_mem hb hc
  have habc := mul_mem hab hc
  have hiso : ∀ x ∈ E, x ≠ 1 → IsoI x := fun x hx hne => (hE x hx).resolve_left hne
  refine ⟨a, ha, b, hb, c, hc, d, hd, hiso a ha ha1, hiso b hb hb1.1, hiso c hc hc1.1,
    hiso d hd hd1.1, ⟨hcomm a ha b hb, hiso _ hab fun h => hb1.2 (hinv a ha b h)⟩,
    ⟨hcomm a ha c hc, hcomm b hb c hc, hiso _ hac fun h => hc1.2.1 (hinv a ha c h),
      hiso _ hbc fun h => hc1.2.2.1 (hinv b hb c h),
      hiso _ habc fun h => hc1.2.2.2 (hinv _ hab c h)⟩,
    ⟨hcomm a ha d hd, hcomm b hb d hd, hcomm c hc d hd,
      hiso _ (mul_mem ha hd) fun h => hd1.2.1 (hinv a ha d h),
      hiso _ (mul_mem hb hd) fun h => hd1.2.2.1 (hinv b hb d h),
      hiso _ (mul_mem hc hd) fun h => hd1.2.2.2.2.1 (hinv c hc d h),
      hiso _ (mul_mem hab hd) fun h => hd1.2.2.2.1 (hinv _ hab d h),
      hiso _ (mul_mem hac hd) fun h => hd1.2.2.2.2.2.1 (hinv _ hac d h),
      hiso _ (mul_mem hbc hd) fun h => hd1.2.2.2.2.2.2.1 (hinv _ hbc d h),
      hiso _ (mul_mem habc hd) fun h => hd1.2.2.2.2.2.2.2 (hinv _ habc d h)⟩⟩

section Cover

variable {n : ℕ} {K : Type} [Group K]

theorem CoverSetup.card_comap {n : ℕ} {K : Type} [Group K] (C : CoverSetup n K)
    {E : Subgroup (Perm (Fin n))} (hE : E ≤ alternatingGroup (Fin n)) :
    Nat.card (E.comap C.ρ) = 2 * Nat.card E := by
  have hker : C.ρ.ker ≤ E.comap C.ρ := fun x hx => by
    rw [Subgroup.mem_comap]
    have : C.ρ x = 1 := hx
    simp [this]
  have h := card_eq_card_map_mul_card_ker C.ρ (E.comap C.ρ) hker
  have hmap : (E.comap C.ρ).map C.ρ = E := by
    rw [Subgroup.map_comap_eq]
    refine inf_eq_right.2 fun q hq => ?_
    obtain ⟨x, hx⟩ := C.exists_ρ_eq (Perm.mem_alternatingGroup.1 (hE hq))
    exact ⟨x, hx⟩
  have hker2 : Nat.card C.ρ.ker = 2 := by
    have : C.ρ.ker = center K := by
      ext x
      rw [MonoidHom.mem_ker, C.ρ_eq_one_iff]
    rw [this]
    exact C.center_card
  rw [h, hmap, hker2, mul_comm]

theorem CoverSetup.card_le_two_mul_map {n : ℕ} {K : Type} [Group K] [Finite K]
    (C : CoverSetup n K) (E : Subgroup K) : Nat.card E ≤ 2 * Nat.card (E.map C.ρ) := by
  let g : E →* Perm (Fin n) := C.ρ.comp E.subtype
  have h1 := Subgroup.card_mul_index g.ker
  rw [Subgroup.index_ker] at h1
  have hrange : g.range = E.map C.ρ := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker2 : Nat.card C.ρ.ker = 2 := by
    have : C.ρ.ker = center K := by
      ext x
      rw [MonoidHom.mem_ker, C.ρ_eq_one_iff]
    rw [this]
    exact C.center_card
  have hker : Nat.card g.ker ≤ 2 := by
    have h : g.ker = C.ρ.ker.subgroupOf E := (MonoidHom.comap_ker C.ρ E.subtype).symm
    rw [h, ← hker2, ← Subgroup.card_map_of_injective E.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_le_of_le inf_le_left
  rw [hrange] at h1
  rw [← h1]
  exact Nat.mul_le_mul_right _ hker

structure CoverCtx (n : ℕ) (K : Type) [Group K] (S : Subgroup K) where
  C : CoverSetup n K
  Q : Subgroup (Perm (Fin n))
  hQA : Q ≤ alternatingGroup (Fin n)
  hS : S = Q.comap C.ρ
  good : SylowGood n Q
  hn' : n ≤ 11
  qcard : Nat.card Q = if n ≤ 9 then 64 else 128
  hI : ∀ x : K, IsoI (C.ρ x) → x * x = 1
  hD : ∀ x : K, DblI (C.ρ x) → x * x ≠ 1

namespace CoverCtx

variable {S : Subgroup K} (X : CoverCtx n K S)

theorem ρ_mem_Q {x : K} (hx : x ∈ S) : X.C.ρ x ∈ X.Q := by
  rw [X.hS] at hx
  exact hx

theorem mem_of_ρ_mem {x : K} (hx : X.C.ρ x ∈ X.Q) : x ∈ S := by
  rw [X.hS]
  exact hx

theorem exists_mem_ρ_eq {q : Perm (Fin n)} (hq : q ∈ X.Q) : ∃ x ∈ S, X.C.ρ x = q := by
  obtain ⟨x, hx⟩ := X.C.exists_ρ_eq (Perm.mem_alternatingGroup.1 (X.hQA hq))
  exact ⟨x, X.mem_of_ρ_mem (hx ▸ hq), hx⟩

include X in
theorem center_le : center K ≤ S := fun x hx =>
  X.mem_of_ρ_mem (by rw [(X.C.ρ_eq_one_iff).2 hx]; exact X.Q.one_mem)

theorem isotropic_map {E : Subgroup K} (hE : ∀ e ∈ E, e * e = 1) :
    ∀ σ ∈ E.map X.C.ρ, σ = 1 ∨ IsoI σ := by
  rintro σ ⟨e, he, rfl⟩
  have h2 : X.C.ρ e * X.C.ρ e = 1 := by rw [← map_mul, hE e he, map_one]
  by_cases h1 : X.C.ρ e = 1
  · exact Or.inl h1
  · refine Or.inr ?_
    rcases support_card_of_involution X.hn' h2 h1 (X.C.sign_ρ e) with h4 | h8
    · exact absurd (hE e he) (X.hD e ⟨h2, h4⟩)
    · exact ⟨h2, h8⟩

theorem isElemAbelian_comap {E : Subgroup (Perm (Fin n))} (hE : ∀ σ ∈ E, σ = 1 ∨ IsoI σ) :
    CFSG.Open.IsElemAbelian 2 (E.comap X.C.ρ) := by
  refine isElemAbelian_of_sq fun e he => ?_
  rcases hE _ he with h1 | h8
  · exact X.C.sq_of_mem_center (X.C.ρ_eq_one_iff.1 h1)
  · exact X.hI e h8

theorem card_comap {E : Subgroup (Perm (Fin n))} (hE : E ≤ alternatingGroup (Fin n)) :
    Nat.card (E.comap X.C.ρ) = 2 * Nat.card E := X.C.card_comap hE

end CoverCtx

namespace CoverCtx

variable {S : Subgroup K} (X : CoverCtx n K S)

theorem map_le {E : Subgroup K} (hE : E ≤ S) : E.map X.C.ρ ≤ X.Q := by
  rw [Subgroup.map_le_iff_le_comap, ← X.hS]
  exact hE

theorem card_le_two_mul_map [Finite K] (E : Subgroup K) :
    Nat.card E ≤ 2 * Nat.card (E.map X.C.ρ) := X.C.card_le_two_mul_map E

theorem card_S [Finite K] {c : ℕ} (hc : Nat.card X.Q = c) : Nat.card S = 2 * c := by
  rw [X.hS, X.card_comap X.hQA, hc]

include X in
theorem rank [Finite K] : CFSG.Open.pRank 2 S = 4 := by
  unfold CFSG.Open.pRank
  apply IsGreatest.csSup_eq
  refine ⟨?_, ?_⟩
  · obtain ⟨E₀, hE₀Q, hE₀card, hE₀iso⟩ := X.good.eightSub
    refine ⟨E₀.comap X.C.ρ, ?_, X.isElemAbelian_comap hE₀iso, ?_⟩
    · exact (Subgroup.comap_mono hE₀Q).trans X.hS.symm.le
    · rw [X.card_comap (hE₀Q.trans X.hQA), hE₀card]
      norm_num
  · rintro k ⟨E, hES, hEab, hEcard⟩
    have hiso := X.isotropic_map (sq_of_isElemAbelian hEab)
    have hmapQ := X.map_le hES
    have hle8 : Nat.card (E.map X.C.ρ) ≤ 8 := by
      by_contra H
      push Not at H
      obtain ⟨a, ha, b, hb, c, hc, d, hd, hia, hib, hic, hid, h2, h3, h4⟩ := exists_indep4 hiso H
      exact X.good.rank a (hmapQ ha) b (hmapQ hb) c (hmapQ hc) d (hmapQ hd) hia hib hic hid
        h2 h3 h4
    have h16 : 2 ^ k ≤ 16 := by
      have := X.card_le_two_mul_map E
      omega
    by_contra hk
    push Not at hk
    have : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega

include X in
theorem four_in_E8 [Finite K] {U : Subgroup K} (hUS : U ≤ S)
    (hU : CFSG.Open.IsElemAbelian 2 U) (hU4 : Nat.card U = 4) :
    ∃ E : Subgroup K, E ≤ S ∧ CFSG.Open.IsElemAbelian 2 E ∧ 8 ≤ Nat.card E ∧ U ≤ E := by
  have hiso := X.isotropic_map (sq_of_isElemAbelian hU)
  have hUQ := X.map_le hUS
  have hle := X.card_le_two_mul_map U
  have hdvd : Nat.card (U.map X.C.ρ) ∣ 4 := hU4 ▸ Subgroup.card_map_dvd U X.C.ρ
  have h24 : Nat.card (U.map X.C.ρ) = 2 ∨ Nat.card (U.map X.C.ρ) = 4 := by
    have h4 := Nat.le_of_dvd (by norm_num) hdvd
    have h2 : 2 ≤ Nat.card (U.map X.C.ρ) := by omega
    interval_cases hm : Nat.card (U.map X.C.ρ)
    · exact Or.inl rfl
    · omega
    · exact Or.inr rfl
  rcases h24 with h2 | h4
  · obtain ⟨a, haU, ha1⟩ : ∃ a ∈ U.map X.C.ρ, a ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hbot : U.map X.C.ρ = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
      rw [hbot, Subgroup.card_bot] at h2
      omega
    have hia : IsoI a := (hiso a haU).resolve_left ha1
    have haQ : a ∈ X.Q := hUQ haU
    obtain ⟨b, hbQ, hib, hadj⟩ := X.good.nbr a haQ hia
    have hKlQ : kleinSub a b hia.1 hib.1 hadj.2.1 ≤ X.Q := by
      rintro x (rfl | rfl | rfl | rfl)
      · exact X.Q.one_mem
      · exact haQ
      · exact hbQ
      · exact mul_mem haQ hbQ
    have hKliso : ∀ σ ∈ kleinSub a b hia.1 hib.1 hadj.2.1, σ = 1 ∨ IsoI σ := by
      rintro σ (rfl | rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr hia
      · exact Or.inr hib
      · exact Or.inr hadj.2.2
    have hKlcard := card_kleinSub hia.1 hib.1 hadj.2.1 ha1 hib.ne_one hadj.1
    have hUbar : U.map X.C.ρ ≤ kleinSub a b hia.1 hib.1 hadj.2.1 := by
      have hpair : pairSub a hia.1 = U.map X.C.ρ := by
        refine Subgroup.eq_of_le_of_card_ge (pairSub_le_of_mem hia.1 haU) ?_
        rw [h2, card_pairSub hia.1 ha1]
      rw [← hpair]
      exact pairSub_le_kleinSub hia.1 hib.1 hadj.2.1
    refine ⟨(kleinSub a b hia.1 hib.1 hadj.2.1).comap X.C.ρ,
      (Subgroup.comap_mono hKlQ).trans X.hS.symm.le, X.isElemAbelian_comap hKliso, ?_,
      (Subgroup.le_comap_map _ _).trans (Subgroup.comap_mono hUbar)⟩
    rw [X.card_comap (hKlQ.trans X.hQA), hKlcard]
  · refine ⟨(U.map X.C.ρ).comap X.C.ρ, (Subgroup.comap_mono hUQ).trans X.hS.symm.le,
      X.isElemAbelian_comap hiso, ?_, Subgroup.le_comap_map _ _⟩
    rw [X.card_comap (hUQ.trans X.hQA), h4]

theorem fourSub_image [Finite K] {U : Subgroup K} (hU4 : Nat.card U = 4) :
    ∃ a ∈ U.map X.C.ρ, a ≠ 1 ∧
      (Nat.card (U.map X.C.ρ) = 2 ∨ Nat.card (U.map X.C.ρ) = 4) := by
  have hle := X.card_le_two_mul_map U
  have hdvd : Nat.card (U.map X.C.ρ) ∣ 4 := hU4 ▸ Subgroup.card_map_dvd U X.C.ρ
  have h24 : Nat.card (U.map X.C.ρ) = 2 ∨ Nat.card (U.map X.C.ρ) = 4 := by
    have h4 := Nat.le_of_dvd (by norm_num) hdvd
    have h2 : 2 ≤ Nat.card (U.map X.C.ρ) := by omega
    interval_cases hm : Nat.card (U.map X.C.ρ)
    · exact Or.inl rfl
    · omega
    · exact Or.inr rfl
  obtain ⟨a, haU, ha1⟩ : ∃ a ∈ U.map X.C.ρ, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : U.map X.C.ρ = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [hbot, Subgroup.card_bot] at h24
    omega
  exact ⟨a, haU, ha1, h24⟩

@[expose] def Wsub (a : Perm (Fin n)) (h : a ∈ X.Q ∧ IsoI a) [Finite K] : FourSub S :=
  ⟨(pairSub a h.2.1).comap X.C.ρ,
    (Subgroup.comap_mono (pairSub_le_of_mem h.2.1 h.1)).trans X.hS.symm.le,
    X.isElemAbelian_comap (by
      rintro σ (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr h.2),
    by rw [X.card_comap ((pairSub_le_of_mem h.2.1 h.1).trans X.hQA), card_pairSub h.2.1 h.2.ne_one]⟩

include X in
theorem reachW [Finite K] (U : FourSub S) :
    ∃ a, ∃ h : a ∈ X.Q ∧ IsoI a, Relation.ReflTransGen (FourAdj S) U (X.Wsub a h) := by
  obtain ⟨U, hUS, hU, hU4⟩ := U
  have hiso := X.isotropic_map (sq_of_isElemAbelian hU)
  have hUQ := X.map_le hUS
  obtain ⟨a, haU, ha1, h24⟩ := X.fourSub_image hU4
  have hia : IsoI a := (hiso a haU).resolve_left ha1
  have haQ : a ∈ X.Q := hUQ haU
  refine ⟨a, ⟨haQ, hia⟩, ?_⟩
  rcases h24 with h2 | h4
  · have hpair : pairSub a hia.1 = U.map X.C.ρ := by
      refine Subgroup.eq_of_le_of_card_ge (pairSub_le_of_mem hia.1 haU) ?_
      rw [h2, card_pairSub hia.1 ha1]
    have hle : U ≤ (X.Wsub a ⟨haQ, hia⟩).1 := by
      show U ≤ (pairSub a hia.1).comap X.C.ρ
      rw [hpair]
      exact Subgroup.le_comap_map _ _
    have heq : U = (X.Wsub a ⟨haQ, hia⟩).1 := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [(X.Wsub a ⟨haQ, hia⟩).2.2.2, hU4]
    have : (⟨U, hUS, hU, hU4⟩ : FourSub S) = X.Wsub a ⟨haQ, hia⟩ := Subtype.ext heq
    rw [this]
  · refine Relation.ReflTransGen.single ⟨(U.map X.C.ρ).comap X.C.ρ,
      (Subgroup.comap_mono hUQ).trans X.hS.symm.le, X.isElemAbelian_comap hiso, ?_,
      Subgroup.le_comap_map _ _, ?_⟩
    · rw [X.card_comap (hUQ.trans X.hQA), h4]
    · show (pairSub a hia.1).comap X.C.ρ ≤ _
      exact Subgroup.comap_mono (pairSub_le_of_mem hia.1 haU)

include X in
theorem adjW [Finite K] {a b : Perm (Fin n)} (ha : a ∈ X.Q ∧ IsoI a) (hb : b ∈ X.Q ∧ IsoI b)
    (hab : AdjI a b) : FourAdj S (X.Wsub a ha) (X.Wsub b hb) := by
  have hKlQ : kleinSub a b ha.2.1 hb.2.1 hab.2.1 ≤ X.Q := by
    rintro x (rfl | rfl | rfl | rfl)
    · exact X.Q.one_mem
    · exact ha.1
    · exact hb.1
    · exact mul_mem ha.1 hb.1
  have hKliso : ∀ σ ∈ kleinSub a b ha.2.1 hb.2.1 hab.2.1, σ = 1 ∨ IsoI σ := by
    rintro σ (rfl | rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr ha.2
    · exact Or.inr hb.2
    · exact Or.inr hab.2.2
  have hKlcard := card_kleinSub ha.2.1 hb.2.1 hab.2.1 ha.2.ne_one hb.2.ne_one hab.1
  refine ⟨(kleinSub a b ha.2.1 hb.2.1 hab.2.1).comap X.C.ρ,
    (Subgroup.comap_mono hKlQ).trans X.hS.symm.le, X.isElemAbelian_comap hKliso, ?_, ?_, ?_⟩
  · rw [X.card_comap (hKlQ.trans X.hQA), hKlcard]
  · exact Subgroup.comap_mono (pairSub_le_kleinSub ha.2.1 hb.2.1 hab.2.1)
  · refine Subgroup.comap_mono ?_
    rintro x (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Or.inr (Or.inr (Or.inl rfl))

include X in
theorem connected [Finite K] (U V : FourSub S) : Relation.ReflTransGen (FourAdj S) U V := by
  have hsymm : Std.Symm (FourAdj S) :=
    ⟨fun _ _ ⟨E, hE, hEab, hE8, hU, hV⟩ => ⟨E, hE, hEab, hE8, hV, hU⟩⟩
  obtain ⟨a, ha, hUa⟩ := X.reachW U
  obtain ⟨b, hb, hVb⟩ := X.reachW V
  have hab : Relation.ReflTransGen (FourAdj S) (X.Wsub a ha) (X.Wsub b hb) := by
    have key : ∀ y, Relation.ReflTransGen (AdjIn X.Q) a y → ∀ hy : y ∈ X.Q ∧ IsoI y,
        Relation.ReflTransGen (FourAdj S) (X.Wsub a ha) (X.Wsub y hy) := by
      intro y hy
      induction hy with
      | refl => exact fun _ => Relation.ReflTransGen.refl
      | tail _ hbc ih =>
        exact fun hz => (ih ⟨hbc.1, hbc.2.2.1⟩).tail (X.adjW ⟨hbc.1, hbc.2.2.1⟩ hz hbc.2.2.2.2)
    exact key b (X.good.conn a ha.1 b hb.1 ha.2 hb.2) hb
  exact (hUa.trans hab).trans (Std.Symm.symm _ _ hVb)

include X in
theorem half [Finite K] :
    ∃ y ∈ S, orderOf y = 2 ∧ y ∉ center K ∧
      ((centralizer ({y} : Set K)).subgroupOf S).index = 2 := by
  obtain ⟨t, htQ, hit, htc, s, hsQ, hds, hst, hist⟩ := X.good.half
  obtain ⟨y, hyS, hy⟩ := X.exists_mem_ρ_eq htQ
  obtain ⟨s', hs'S, hs'⟩ := X.exists_mem_ρ_eq hsQ
  have hy2 : y * y = 1 := X.hI y (hy ▸ hit)
  have hy1 : y ≠ 1 := fun h => hit.ne_one (by rw [← hy, h, map_one])
  have hord : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  have hcen : ∀ x : K, x ∈ S → x * y * x⁻¹ * y⁻¹ ∈ center K := by
    intro x hx
    rw [← X.C.ρ_eq_one_iff]
    simp only [map_mul, map_inv]
    have h1 := htc _ (X.ρ_mem_Q hx)
    rw [hy]
    calc X.C.ρ x * t * (X.C.ρ x)⁻¹ * t⁻¹ = (t * X.C.ρ x) * (X.C.ρ x)⁻¹ * t⁻¹ := by rw [← h1]
      _ = 1 := by group
  have hc := hcen s' hs'S
  have hsq := CoverSetup.sq_mul_of_comm_central hc
  have hsy2 : (s' * y) * (s' * y) = 1 := X.hI (s' * y) (by rw [map_mul, hs', hy]; exact hist)
  have hs'2 : s' * s' ≠ 1 := X.hD s' (by rw [hs']; exact hds)
  rw [hsy2, hy2, mul_one] at hsq
  have hcne : s' * y * s'⁻¹ * y⁻¹ ≠ 1 := by
    intro h1
    rw [h1, inv_one, one_mul] at hsq
    exact hs'2 hsq.symm
  have hycen : y ∉ center K := by
    intro hyc
    apply hcne
    rw [mem_center_iff.1 hyc s']
    group
  refine ⟨y, hyS, hord, hycen, ?_⟩
  let ψ : ↥S →* ↥(center K) :=
    { toFun := fun x => ⟨(x : K) * y * (x : K)⁻¹ * y⁻¹, hcen x x.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x₁ x₂
        apply Subtype.ext
        have h2 := hcen x₂ x₂.2
        have h2' := mem_center_iff.1 h2 (x₁ : K)
        have h2'' := mem_center_iff.1 h2 ((x₁ : K) * y * (x₁ : K)⁻¹ * y⁻¹)
        set c₂ := (x₂ : K) * y * (x₂ : K)⁻¹ * y⁻¹ with hc₂
        change ((x₁ * x₂ : ↥S) : K) * y * ((x₁ * x₂ : ↥S) : K)⁻¹ * y⁻¹ =
          ((x₁ : K) * y * (x₁ : K)⁻¹ * y⁻¹) * c₂
        calc ((x₁ * x₂ : ↥S) : K) * y * ((x₁ * x₂ : ↥S) : K)⁻¹ * y⁻¹
            = ((x₁ : K) * c₂) * y * (x₁ : K)⁻¹ * y⁻¹ := by
              simp only [Subgroup.coe_mul, mul_inv_rev, hc₂]
              group
          _ = (c₂ * (x₁ : K)) * y * (x₁ : K)⁻¹ * y⁻¹ := by rw [h2']
          _ = c₂ * ((x₁ : K) * y * (x₁ : K)⁻¹ * y⁻¹) := by group
          _ = ((x₁ : K) * y * (x₁ : K)⁻¹ * y⁻¹) * c₂ := h2''.symm }
  have hker : ψ.ker = (centralizer ({y} : Set K)).subgroupOf S := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : (x : K) * y * (x : K)⁻¹ * y⁻¹ = 1 := congrArg Subtype.val h
      exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h')
    · intro h
      apply Subtype.ext
      show (x : K) * y * (x : K)⁻¹ * y⁻¹ = 1
      rw [h]
      group
  rw [← hker, Subgroup.index_ker]
  have hdvd : Nat.card ψ.range ∣ 2 := by
    have := Subgroup.card_subgroup_dvd_card ψ.range
    rwa [X.C.center_card] at this
  have hne : Nat.card ψ.range ≠ 1 := by
    intro h1
    have hbot : ψ.range = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have : ψ ⟨s', hs'S⟩ = 1 := by
      have hmem : ψ ⟨s', hs'S⟩ ∈ ψ.range := ⟨_, rfl⟩
      rw [hbot] at hmem
      exact Subgroup.mem_bot.1 hmem
    exact hcne (congrArg Subtype.val this)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact absurd h hne
  · exact h

end CoverCtx

end Cover

section Bridge

variable {n : ℕ} [NeZero n] {K : Type} [Group K]

omit [NeZero n] in
theorem card_K_eq [Finite K] (hn : 2 ≤ n) (hK : IsDoubleCoverOfAlt K n) :
    Nat.card K = n.factorial := by
  rw [CFSG.Sporadic.Recognition.LyonsSims.card_eq_two_mul_of_doubleCover hK,
    natCard_alternatingGroup_fin hn]
  have : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hn
  omega

theorem exists_conj_comap [Finite K] (hn : 8 ≤ n) (hn' : n ≤ 11) (hK : IsDoubleCoverOfAlt K n)
    (C : CoverSetup n K) (hP0 : Nat.card (P0 n) = if n ≤ 9 then 64 else 128) (S : Sylow 2 K) :
    ∃ g : Perm (Fin n), (S : Subgroup K) = (conjSub g (P0 n)).comap C.ρ := by
  have hKcard := card_K_eq (by omega) hK
  have hS₀card : Nat.card ((P0 n).comap C.ρ) = 2 * Nat.card (P0 n) :=
    C.card_comap (P0_le_alternatingGroup hn hn')
  have hpow : Nat.card ((P0 n).comap C.ρ) = 2 ^ (if n ≤ 9 then 7 else 8) := by
    rw [hS₀card, hP0]
    split_ifs <;> norm_num
  have hS₀p : IsPGroup 2 ((P0 n).comap C.ρ) := IsPGroup.of_card hpow
  have hidx : ¬ 2 ∣ ((P0 n).comap C.ρ).index := by
    have h1 := Subgroup.card_mul_index ((P0 n).comap C.ρ)
    rw [hKcard, hpow] at h1
    interval_cases n <;> norm_num [Nat.factorial] at h1 ⊢ <;> omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := exists_conj_of_sylow (S : Subgroup K) ((P0 n).comap C.ρ) S.isPGroup' hS₀p
    S.not_dvd_index hidx
  refine ⟨C.ρ k, ?_⟩
  ext x
  rw [hk x, Subgroup.mem_comap, Subgroup.mem_comap, mem_conjSub]
  simp [map_mul, map_inv, mul_assoc]

theorem nonempty_coverCtx [Finite K] (hn : 8 ≤ n) (hn' : n ≤ 11) (hK : IsDoubleCoverOfAlt K n)
    (hP0 : Nat.card (P0 n) = if n ≤ 9 then 64 else 128) (hgood : SylowGood n (P0 n))
    (S : Sylow 2 K) : Nonempty (CoverCtx n K (S : Subgroup K)) := by
  let C := CoverSetup.ofCover hK
  obtain ⟨g, hg⟩ := exists_conj_comap hn hn' hK C hP0 S
  obtain ⟨a, -, b, -, c, -, ha, hb, hc, h2, h3⟩ := hgood.eight
  refine ⟨⟨C, conjSub g (P0 n), ?_, hg, hgood.conj g, hn', ?_, ?_, ?_⟩⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := exists_conj_mem.1 hx
    have hy' := P0_le_alternatingGroup hn hn' hy
    rw [Perm.mem_alternatingGroup] at hy' ⊢
    simp [Perm.sign_mul, hy']
  · rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective, hP0]
  · exact fun x hx => C.isoI_sq_eq_one hn hn' ⟨a, b, c, ha, hb, hc, h2, h3⟩ hx
  · exact fun x hx => C.dblI_sq_ne_one hn hx

theorem coverSylowData_of_good (hn : 8 ≤ n) (hn' : n ≤ 11)
    (hP0 : Nat.card (P0 n) = if n ≤ 9 then 64 else 128) (hgood : SylowGood n (P0 n)) :
    CFSG.OddStandard.Solomon75.CoverSylowData n where
  card K _ _ hK S := by
    obtain ⟨X⟩ := nonempty_coverCtx hn hn' hK hP0 hgood S
    have := X.card_S X.qcard
    rw [this]
    split_ifs <;> rfl
  rank K _ _ hK S := by
    obtain ⟨X⟩ := nonempty_coverCtx hn hn' hK hP0 hgood S
    exact X.rank
  four_in_E8 K _ _ hK S := by
    obtain ⟨X⟩ := nonempty_coverCtx hn hn' hK hP0 hgood S
    intro U hUS hU hU4
    exact X.four_in_E8 hUS hU hU4
  connected K _ _ hK S := by
    obtain ⟨X⟩ := nonempty_coverCtx hn hn' hK hP0 hgood S
    exact X.connected
  half_centralizer K _ _ hK S := by
    obtain ⟨X⟩ := nonempty_coverCtx hn hn' hK hP0 hgood S
    exact X.half

end Bridge

theorem coverSylowData_of_check {n : ℕ} (hn : 8 ≤ n) (hn' : n ≤ 11)
    (h : sylowCheck n (if n ≤ 9 then 64 else 128) = true) :
    CFSG.OddStandard.Solomon75.CoverSylowData n := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨hP0, hgood⟩ := sylowGood_of_check hn hn' (by split_ifs <;> norm_num) h
  exact coverSylowData_of_good hn hn' hP0 hgood

end CFSG.OddStandard.Solomon75.AhatData
