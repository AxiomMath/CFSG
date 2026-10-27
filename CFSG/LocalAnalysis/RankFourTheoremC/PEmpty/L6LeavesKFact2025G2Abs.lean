module

public import CFSG.GF2Type.Aschbacher1976Full.HSGL3
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubAbstract

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KF2025.G2

open Subgroup CFSG.Open

section Facts

@[expose] def NoCentralInvolution {G : Type} [Group G] (z : G) : Prop :=
  ∀ t : G, orderOf t = 2 → z * t ≠ t * z

@[expose] def TwoRankLeThree (G : Type) [Group G] : Prop :=
  ∀ E : Subgroup G, IsElemAbelian 2 E → Nat.card E ≤ 8

@[expose] def SelfCentralizingEight (G : Type) [Group G] : Prop :=
  ∀ E : Subgroup G, IsElemAbelian 2 E → Nat.card E = 8 →
    ∀ g : G, (∀ e ∈ E, g * e = e * g) → g ∈ E

end Facts

section Transport

variable {G H : Type} [Group G] [Group H]

theorem isElemAbelian_map (e : G ≃* H) {E : Subgroup G} (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 (E.map e.toMonoidHom) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · rcases a with ⟨_, x, hx, rfl⟩
    rcases b with ⟨_, y, hy, rfl⟩
    apply Subtype.ext
    show e x * e y = e y * e x
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  · rintro _ ⟨x, hx, rfl⟩
    show e x ^ 2 = 1
    rw [← map_pow, hE.2 x hx, map_one]

theorem NoCentralInvolution.of_mulEquiv (e : G ≃* H) {z : G} (h : NoCentralInvolution (e z)) :
    NoCentralInvolution z := by
  intro t ht hc
  refine h (e t) (by rw [MulEquiv.orderOf_eq]; exact ht) ?_
  rw [← map_mul, ← map_mul, hc]

theorem TwoRankLeThree.of_mulEquiv (e : G ≃* H) (h : TwoRankLeThree H) : TwoRankLeThree G := by
  intro E hE
  have := h _ (isElemAbelian_map e hE)
  rwa [Subgroup.card_map_of_injective e.injective] at this

theorem SelfCentralizingEight.of_mulEquiv (e : G ≃* H) (h : SelfCentralizingEight H) :
    SelfCentralizingEight G := by
  intro E hE h8 g hg
  have h8' : Nat.card (E.map e.toMonoidHom) = 8 := by
    rwa [Subgroup.card_map_of_injective e.injective]
  have := h _ (isElemAbelian_map e hE) h8' (e g) (by
    rintro _ ⟨x, hx, rfl⟩
    show e g * e x = e x * e g
    rw [← map_mul, ← map_mul, hg x hx])
  obtain ⟨x, hx, hxe⟩ := this
  have : x = g := e.injective hxe
  rwa [← this]

end Transport

section Omega

variable {G : Type} [Group G]

@[expose] def omegaCenter (S : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ S ∧ (∀ s ∈ S, x * s = s * x) ∧ x * x = 1}
  mul_mem' := by
    rintro a b ⟨haS, hac, ha2⟩ ⟨hbS, hbc, hb2⟩
    refine ⟨S.mul_mem haS hbS, fun s hs => ?_, ?_⟩
    · rw [mul_assoc, hbc s hs, ← mul_assoc, hac s hs, mul_assoc]
    · have hab : a * b = b * a := hac b hbS
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
  one_mem' := ⟨S.one_mem, fun s _ => by simp, by simp⟩
  inv_mem' := by
    rintro a ⟨haS, hac, ha2⟩
    have : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    rw [this]
    exact ⟨haS, hac, ha2⟩

theorem omegaCenter_le (S : Subgroup G) : omegaCenter S ≤ S := fun _ hx => hx.1

theorem isElemAbelian_omegaCenter (S : Subgroup G) : IsElemAbelian 2 (omegaCenter S) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · exact Subtype.ext (a.2.2.1 b b.2.1)
  · rw [pow_two]
    exact hx.2.2

theorem exists_orderOf_two_mem_omegaCenter [Finite G] {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hS1 : S ≠ ⊥) : ∃ x ∈ omegaCenter S, orderOf x = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr hS1
  haveI : Nontrivial (Subgroup.center S) := hS2.center_nontrivial
  obtain ⟨c, hc⟩ := exists_ne (1 : Subgroup.center S)
  have hc' : (c : S) ≠ 1 := fun h => hc (Subtype.ext h)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS2) (c : S)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hc' (orderOf_eq_one_iff.mp (by simpa using hk))
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  set y : S := (c : S) ^ (2 ^ m) with hy
  have hdvd : 2 ^ m ∣ orderOf (c : S) := by
    rw [hk]
    exact pow_dvd_pow 2 (Nat.le_succ m)
  have hyo : orderOf y = 2 := by
    rw [hy, orderOf_pow_of_dvd (by positivity) hdvd, hk, pow_succ]
    simp
  have hyc : ∀ s : S, y * s = s * y := fun s => by
    have := Subgroup.mem_center_iff.mp (Subgroup.pow_mem (Subgroup.center S) c.2 (2 ^ m)) s
    exact this.symm
  refine ⟨(y : G), ⟨y.2, fun s hs => ?_, ?_⟩, ?_⟩
  · exact congrArg Subtype.val (hyc ⟨s, hs⟩)
  · have : y * y = 1 := by
      rw [← pow_two, ← hyo]
      exact pow_orderOf_eq_one y
    exact congrArg Subtype.val this
  · rw [Subgroup.orderOf_coe, hyo]

theorem conj_mem_omegaCenter {S : Subgroup G} {z : G} (hz : z ∈ normalizer (S : Set G)) {x : G}
    (hx : x ∈ omegaCenter S) : z * x * z⁻¹ ∈ omegaCenter S := by
  obtain ⟨hxS, hxc, hx2⟩ := hx
  have hz' : z⁻¹ ∈ normalizer (S : Set G) := inv_mem hz
  refine ⟨(Subgroup.mem_normalizer_iff.mp hz x).mp hxS, fun s hs => ?_, ?_⟩
  · have hs' : z⁻¹ * s * z ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp hz' s).mp hs
      simpa using this
    have h := hxc _ hs'
    calc z * x * z⁻¹ * s = z * (x * (z⁻¹ * s * z)) * z⁻¹ := by group
      _ = z * ((z⁻¹ * s * z) * x) * z⁻¹ := by rw [h]
      _ = s * (z * x * z⁻¹) := by group
  · calc z * x * z⁻¹ * (z * x * z⁻¹) = z * (x * x) * z⁻¹ := by group
      _ = 1 := by rw [hx2]; group

end Omega

section Count

variable {G : Type} [Group G]

@[expose] def conjPerm {S : Subgroup G} {z : G} (hz : z ∈ normalizer (S : Set G)) :
    Equiv.Perm (omegaCenter S) where
  toFun x := ⟨z * x * z⁻¹, conj_mem_omegaCenter hz x.2⟩
  invFun x := ⟨z⁻¹ * x * z, by simpa using conj_mem_omegaCenter (inv_mem hz) x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])

theorem conjPerm_apply {S : Subgroup G} {z : G} (hz : z ∈ normalizer (S : Set G))
    (x : omegaCenter S) : ((conjPerm hz x : omegaCenter S) : G) = z * x * z⁻¹ :=
  rfl

theorem conjPerm_pow_apply {S : Subgroup G} {z : G} (hz : z ∈ normalizer (S : Set G)) (k : ℕ)
    (x : omegaCenter S) :
    (((conjPerm hz) ^ k) x : G) = z ^ k * x * (z ^ k)⁻¹ := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, conjPerm_apply]
    group

theorem conjPerm_pow_eq_one {S : Subgroup G} {z : G} (hz : z ∈ normalizer (S : Set G)) {p : ℕ}
    (hzp : z ^ p = 1) : (conjPerm hz) ^ p = 1 := by
  refine Equiv.ext fun x => Subtype.ext ?_
  rw [conjPerm_pow_apply, hzp]
  simp

theorem isPGroup_two_of_isElemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E) :
    IsPGroup 2 E := fun g => ⟨1, by
  apply Subtype.ext
  simpa using hE.2 g g.2⟩

variable [Finite G]

theorem card_omegaCenter_modEq {S : Subgroup G} {z : G} {p : ℕ} [Fact p.Prime] (hzp : z ^ p = 1)
    (hz : z ∈ normalizer (S : Set G)) (ha : NoCentralInvolution z) :
    Nat.card (omegaCenter S) ≡ 1 [MOD p] := by
  classical
  haveI : Fintype (omegaCenter S) := Fintype.ofFinite _
  have hσ : (conjPerm hz) ^ p ^ 1 = 1 := by
    rw [pow_one]
    exact conjPerm_pow_eq_one hz hzp
  have h := Equiv.Perm.card_compl_support_modEq hσ
  have hc : (conjPerm hz).supportᶜ = {1} := by
    ext x
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.mem_singleton]
    constructor
    · intro hx
      by_contra hx1
      have hxg : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
      have hx2 : (x : G) ^ 2 = 1 := by rw [pow_two]; exact x.2.2.2
      have hord : orderOf (x : G) = 2 := orderOf_eq_prime hx2 hxg
      apply ha _ hord
      have := congrArg Subtype.val hx
      rw [conjPerm_apply] at this
      calc z * (x : G) = z * x * z⁻¹ * z := by group
        _ = x * z := by rw [this]
    · rintro rfl
      exact Subtype.ext (by simp [conjPerm_apply])
  rw [hc, Finset.card_singleton, ← Nat.card_eq_fintype_card] at h
  exact h.symm

theorem card_omegaCenter_eq_eight {S : Subgroup G} {z : G} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hzp : z ^ p = 1) (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥) (hz : z ∈ normalizer (S : Set G))
    (ha : NoCentralInvolution z) (hb : TwoRankLeThree G) :
    Nat.card (omegaCenter S) = 8 ∧ p = 7 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmod := card_omegaCenter_modEq hzp hz ha
  obtain ⟨n, hn⟩ := (isPGroup_two_of_isElemAbelian (isElemAbelian_omegaCenter S)).exists_card_eq
  have h8 : 2 ^ n ≤ 8 := hn ▸ hb _ (isElemAbelian_omegaCenter S)
  obtain ⟨x, hxT, hx2⟩ := exists_orderOf_two_mem_omegaCenter hS2 hS1
  have hx1 : (⟨x, hxT⟩ : omegaCenter S) ≠ 1 := fun h => by
    have : x = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at hx2
    omega
  have hcard2 : 2 ≤ Nat.card (omegaCenter S) := by
    haveI : Nontrivial (omegaCenter S) := ⟨⟨⟨x, hxT⟩, 1, hx1⟩⟩
    have : 1 < Nat.card (omegaCenter S) := Finite.one_lt_card
    omega
  rw [hn] at hcard2 hmod
  have hn3 : n ≤ 3 := by
    by_contra h
    have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hn]
  interval_cases n
  · exact absurd hcard2 (by norm_num)
  · exfalso
    have := (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 2)).mp hmod.symm
    have h1 : p ∣ 1 := by simpa using this
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  · exfalso
    have := (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 4)).mp hmod.symm
    have h3 : p ∣ 3 := by simpa using this
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  · refine ⟨by norm_num, ?_⟩
    have := (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 8)).mp hmod.symm
    have h7 : p ∣ 7 := by simpa using this
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp h7

theorem omegaCenter_eq {S : Subgroup G} (hc : SelfCentralizingEight G)
    (h8 : Nat.card (omegaCenter S) = 8) : omegaCenter S = S := by
  refine le_antisymm (omegaCenter_le S) fun s hs => ?_
  exact hc _ (isElemAbelian_omegaCenter S) h8 s fun e he => (he.2.1 s hs).symm

end Count

section Index

variable {G : Type} [Group G] [Finite G]

theorem centralizer_eq {S : Subgroup G} (hc : SelfCentralizingEight G)
    (hSelem : IsElemAbelian 2 S) (hS8 : Nat.card S = 8) : centralizer (S : Set G) = S := by
  refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
  · exact hc S hSelem hS8 g fun e he => (mem_centralizer_iff.mp hg e he).symm
  · rw [mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (hSelem.1.is_comm.comm (⟨h, hh⟩ : S) ⟨g, hg⟩)

theorem prime_dvd_card_range {S : Subgroup G} {z : G} {p : ℕ} (hp : p.Prime) (hzp : orderOf z = p)
    (hz : z ∈ normalizer (S : Set G)) (hzC : z ∉ centralizer (S : Set G)) :
    p ∣ Nat.card S.normalizerMonoidHom.range := by
  haveI : Fact p.Prime := ⟨hp⟩
  set M : ↥(normalizer (S : Set G)) := ⟨z, hz⟩ with hM
  have hne : S.normalizerMonoidHom M ≠ 1 := by
    intro h
    apply hzC
    have hk : M ∈ S.normalizerMonoidHom.ker := h
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hk
    exact hk
  have hMp : M ^ p = 1 := by
    apply Subtype.ext
    have : z ^ p = 1 := hzp ▸ pow_orderOf_eq_one z
    simpa [hM] using this
  have hpow : S.normalizerMonoidHom M ^ p = 1 := by rw [← map_pow, hMp, map_one]
  have hord : orderOf (S.normalizerMonoidHom M) = p := orderOf_eq_prime hpow hne
  have h := Subgroup.orderOf_dvd_natCard S.normalizerMonoidHom.range
    (x := S.normalizerMonoidHom M) ⟨M, rfl⟩
  rwa [hord] at h

theorem two_dvd_card_range {S : Subgroup G} (hS8 : Nat.card S = 8) (hS2 : IsPGroup 2 S)
    (hCS : centralizer (S : Set G) = S) (hd : 16 ∣ Nat.card G) :
    2 ∣ Nat.card S.normalizerMonoidHom.range := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hSP⟩ := hS2.exists_le_sylow
  have hP16 : 2 ^ 4 ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card (by simpa using hd)
  have hPgt : 8 < Nat.card (P : Subgroup G) := by
    have := Nat.le_of_dvd Nat.card_pos hP16
    omega
  have hlt : S.subgroupOf (P : Subgroup G) < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => ?_
    have hPS : (P : Subgroup G) ≤ S := fun x hx => by
      have : (⟨x, hx⟩ : (P : Subgroup G)) ∈ S.subgroupOf (P : Subgroup G) := htop ▸ mem_top _
      exact this
    have := Subgroup.card_le_of_le hPS
    omega
  haveI : Group.IsNilpotent (P : Subgroup G) := P.isPGroup'.isNilpotent
  obtain ⟨n, hnN, hnS⟩ := SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hnS' : (n : G) ∉ S := hnS
  have hnorm : ∀ s : G, s ∈ S ↔ (n : G) * s * (n : G)⁻¹ ∈ S := by
    intro s
    constructor
    · intro hs
      have := (mem_normalizer_iff.mp hnN ⟨s, hSP hs⟩).mp hs
      simpa [mem_subgroupOf] using this
    · intro hs
      have hsT : s ∈ (P : Subgroup G) := by
        have h1 : (n : G) * s * (n : G)⁻¹ ∈ (P : Subgroup G) := hSP hs
        have := (P : Subgroup G).mul_mem
          ((P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem n.2) h1) n.2
        simpa [mul_assoc] using this
      have := (mem_normalizer_iff.mp hnN ⟨s, hsT⟩).mpr (by simpa [mem_subgroupOf] using hs)
      simpa [mem_subgroupOf] using this
  have hnN' : (n : G) ∈ normalizer (S : Set G) := Subgroup.mem_normalizer_iff.mpr hnorm
  set M : ↥(normalizer (S : Set G)) := ⟨(n : G), hnN'⟩ with hM
  have hne : S.normalizerMonoidHom M ≠ 1 := by
    intro h
    have hk : M ∈ S.normalizerMonoidHom.ker := h
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf, hCS] at hk
    exact hnS' hk
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') n
  have hMo : orderOf M = 2 ^ k := by
    rw [← Subgroup.orderOf_coe M]
    show orderOf (n : G) = 2 ^ k
    rw [Subgroup.orderOf_coe n, hk]
  have hdvd : orderOf (S.normalizerMonoidHom M) ∣ 2 ^ k :=
    hMo ▸ orderOf_map_dvd S.normalizerMonoidHom M
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hne (orderOf_eq_one_iff.mp (by simpa using hj))
  have h2 : 2 ∣ orderOf (S.normalizerMonoidHom M) := by
    rw [hj]
    exact dvd_pow_self 2 hj0
  have h := Subgroup.orderOf_dvd_natCard S.normalizerMonoidHom.range
    (x := S.normalizerMonoidHom M) ⟨M, rfl⟩
  exact h2.trans h

end Index

section Assemble

theorem exists_not_comm_gl32 :
    ∃ a b : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2), a * b ≠ b * a := by
  haveI := CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  by_contra hcomm
  push Not at hcomm
  letI : CommGroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :=
    { (inferInstance : Group (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) with
      mul_comm := hcomm }
  have hprime := CommGroup.is_simple_iff_prime_card.mp
    (inferInstance : IsSimpleGroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)))
  rw [CFSG.ComponentClassification.GHarris.card_GL32_gh] at hprime
  exact absurd hprime (by norm_num)

variable {G : Type} [Group G] [Finite G]

theorem kxSection_of_facts {S : Subgroup G} {z : G} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hzp : orderOf z = p) (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥)
    (hzS : z ∈ normalizer (S : Set G)) (ha : NoCentralInvolution z) (hb : TwoRankLeThree G)
    (hc : SelfCentralizingEight G) (hd : 16 ∣ Nat.card G) :
    KxSection z (normalizer (S : Set G)) 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hz1 : z ^ p = 1 := hzp ▸ pow_orderOf_eq_one z
  obtain ⟨h8, hp7⟩ := card_omegaCenter_eq_eight hp hp5 hz1 hS2 hS1 hzS ha hb
  have hST : omegaCenter S = S := omegaCenter_eq hc h8
  have hSelem : IsElemAbelian 2 S := by
    have := isElemAbelian_omegaCenter S
    rwa [hST] at this
  have hS8 : Nat.card S = 8 := by rwa [hST] at h8
  have hCS := centralizer_eq hc hSelem hS8
  have hzC : z ∉ centralizer (S : Set G) := by
    intro hzC
    obtain ⟨t, htT, ht2⟩ := exists_orderOf_two_mem_omegaCenter hS2 hS1
    exact ha t ht2 (mem_centralizer_iff.mp hzC t htT.1).symm
  have h7 := prime_dvd_card_range hp hzp hzS hzC
  have h2 := two_dvd_card_range hS8 hS2 hCS hd
  rw [hp7] at h7
  have h14 : 14 ∣ ((centralizer (S : Set G)).subgroupOf (normalizer (S : Set G))).index := by
    rw [← Subgroup.normalizerMonoidHom_ker, Subgroup.index_ker]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 7) h2 h7
  obtain ⟨θ, hθs, hθk⟩ :=
    CFSG.GF2Type.Aschbacher1976Full.HS.exists_GL32_of_dvd_14_index hSelem hS8 h14
  haveI := CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  have hsec := S622IsSimpleSection.of_surjective (A := G) (Y := normalizer (S : Set G)) θ hθs
    exists_not_comm_gl32
  have hker : θ.ker.map (normalizer (S : Set G)).subtype = S := by
    rw [hθk, hCS]
    exact Subgroup.map_subgroupOf_eq_of_le Subgroup.le_normalizer
  rw [hker] at hsec
  refine ⟨normalizer (S : Set G), S, le_rfl, hsec, hzS, ?_, ?_⟩
  · intro hzS'
    apply hzC
    rw [hCS]
    exact hzS'
  · have hkS : θ.ker = S.subgroupOf (normalizer (S : Set G)) := by rw [hθk, hCS]
    show 3 ∣ (S.subgroupOf (normalizer (S : Set G))).index
    rw [← hkS, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hθs, Subgroup.card_top,
      CFSG.ComponentClassification.GHarris.card_GL32_gh]
    norm_num

theorem kxSection_of_facts_ambient {A : Type} [Group A] [Finite A] {L S : Subgroup A} {z : A}
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hzp : orderOf z = p) (hzL : z ∈ L) (hSL : S ≤ L)
    (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥) (hzS : z ∈ normalizer (S : Set A))
    (ha : NoCentralInvolution (⟨z, hzL⟩ : ↥L)) (hb : TwoRankLeThree ↥L)
    (hc : SelfCentralizingEight ↥L) (hd : 16 ∣ Nat.card L) :
    KxSection z (normalizer (S : Set A) ⊓ L) 3 := by
  set z' : ↥L := ⟨z, hzL⟩ with hz'
  have hS'2 : IsPGroup 2 (S.subgroupOf L) := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSL).symm
  have hS'1 : S.subgroupOf L ≠ ⊥ := by
    intro h
    apply hS1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hSL hx⟩ : ↥L) ∈ S.subgroupOf L := hx
    rw [h, Subgroup.mem_bot] at this
    exact Subtype.ext_iff.mp this
  have hz'S : z' ∈ normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have := (Subgroup.mem_normalizer_iff.mp hzS) (g : A)
    simpa [Subgroup.mem_subgroupOf, hz'] using this
  have hzp' : orderOf z' = p := by
    rw [← hzp, ← Subgroup.orderOf_coe]
  obtain ⟨H, N, hHN, hsec, hzH, hzN, hdvd⟩ :=
    kxSection_of_facts hp hp5 hzp' hS'2 hS'1 hz'S ha hb hc hd
  refine ⟨H.map L.subtype, N.map L.subtype, ?_,
    hsec.map_of_injective L.subtype L.subtype_injective, ⟨z', hzH, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨h, hh, rfl⟩
    refine ⟨?_, h.2⟩
    show (h : A) ∈ normalizer (S : Set A)
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have := ((Subgroup.mem_normalizer_iff.mp (hHN hh)) ⟨g, hSL hg⟩).mp
        (by simpa [Subgroup.mem_subgroupOf] using hg)
      simpa [Subgroup.mem_subgroupOf] using this
    · intro hg
      have hgL : g ∈ L := by
        have h1 : (h : A) * g * (h : A)⁻¹ ∈ L := hSL hg
        have := L.mul_mem (L.mul_mem (L.inv_mem h.2) h1) h.2
        simpa [mul_assoc] using this
      have := ((Subgroup.mem_normalizer_iff.mp (hHN hh)) ⟨g, hgL⟩).mpr
        (by simpa [Subgroup.mem_subgroupOf] using hg)
      simpa [Subgroup.mem_subgroupOf] using this
  · rintro ⟨n, hn, hnz⟩
    apply hzN
    have : n = z' := Subtype.ext hnz
    rwa [this] at hn
  · rwa [Subgroup.relIndex_map_map_of_injective _ _ L.subtype_injective]

end Assemble

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KF2025.G2
