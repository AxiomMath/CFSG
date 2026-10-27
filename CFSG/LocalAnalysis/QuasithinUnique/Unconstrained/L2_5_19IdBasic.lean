module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19MinBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Center
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Rank

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section TwoGroups

variable {G : Type*} [Group G]

theorem exists_fixed_ne_one [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) {i : G}
    (hi : i * i = 1) (hN : ∀ p ∈ P, i * p * i ∈ P) : ∃ p ∈ P, p ≠ 1 ∧ i * p = p * i := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  let f : Function.End ↥P := fun p => ⟨i * p * i, hN p p.2⟩
  have hf : f ^ 2 ^ 1 = 1 := by
    funext p
    apply Subtype.ext
    show i * (i * (p : G) * i) * i = p
    calc i * (i * (p : G) * i) * i = (i * i) * (p : G) * (i * i) := by group
      _ = p := by rw [hi]; group
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP1
  let _ : Fintype ↥P := Fintype.ofFinite _
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) hf
  have hcard2 : 2 ∣ Fintype.card ↥P := by
    have h1 := hP.card_eq_or_dvd
    rw [Nat.card_eq_fintype_card] at h1
    rcases h1 with h1 | h1
    · exfalso
      have : Subsingleton P := Fintype.card_le_one_iff_subsingleton.mp h1.le
      exact (not_subsingleton P) this
    · exact h1
  have hfix2 : 2 ∣ Fintype.card ↑(Function.fixedPoints f) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hcard2))
  have hone : (1 : ↥P) ∈ Function.fixedPoints f := by
    apply Subtype.ext
    show i * (1 : G) * i = 1
    simpa using hi
  have hge : 1 < Fintype.card ↑(Function.fixedPoints f) := by
    have hpos : 0 < Fintype.card ↑(Function.fixedPoints f) :=
      Fintype.card_pos_iff.mpr ⟨⟨1, hone⟩⟩
    obtain ⟨k, hk⟩ := hfix2
    omega
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := Fintype.exists_pair_of_one_lt_card hge
  have key : ∀ x : ↥P, x ≠ 1 → f x = x → ∃ p ∈ P, p ≠ 1 ∧ i * p = p * i := by
    intro x hx1 hx
    refine ⟨(x : G), x.2, fun h => hx1 (Subtype.ext h), ?_⟩
    have h2 : i * (x : G) * i = x := congrArg Subtype.val hx
    calc i * (x : G) = i * (x : G) * (i * i) := by rw [hi, mul_one]
      _ = (i * (x : G) * i) * i := by group
      _ = x * i := by rw [h2]
  by_cases ha1 : a = 1
  · refine key b (fun hb1 => hab ?_) hb
    subst ha1; subst hb1; rfl
  · exact key a ha1 ha

theorem four_le_card_of_four_distinct [Finite G] {C : Subgroup G} {a b c d : G}
    (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C) (hd : d ∈ C) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : 4 ≤ Nat.card C := by
  let f : Fin 4 → C := ![⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, Subtype.ext_iff]
  simpa using Nat.card_le_card_of_injective f hf

theorem four_le_card_centralizer_of_involution [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P)
    (h4 : 4 ≤ Nat.card P) {c : G} (hcP : c ∈ P) (hc1 : c ≠ 1) (hc : c * c = 1) :
    4 ≤ Nat.card ↥(P ⊓ Subgroup.centralizer ({c} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hcen : ∀ p ∈ P, p * c = c * p
  · have : P ⊓ Subgroup.centralizer ({c} : Set G) = P := by
      refine inf_eq_left.mpr fun p hp => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcen p hp)
    rw [this]
    exact h4
  · have hex : ∃ q ∈ P, q * c ≠ c * q := by
      by_contra h
      exact hcen fun p hp => by
        by_contra h'
        exact h ⟨p, hp, h'⟩
    obtain ⟨q, hqP, hqc⟩ := hex
    have hnt : Nontrivial P := by
      refine Finite.one_lt_card_iff_nontrivial.mp ?_
      omega
    have := hP.center_nontrivial
    obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥P))
    have hzP : (z : G) ∈ P := z.2
    have hz1' : (z : G) ≠ 1 := by
      intro h
      apply hz1
      apply Subtype.ext
      apply Subtype.ext
      exact h
    have hzc : ∀ p ∈ P, p * (z : G) = (z : G) * p := by
      intro p hp
      have := Subgroup.mem_center_iff.mp hz ⟨p, hp⟩
      exact congrArg Subtype.val this
    have hcnz : c ≠ (z : G) := by
      intro h
      apply hqc
      rw [h]
      exact (hzc q hqP)
    have hcz : c * (z : G) ≠ 1 := by
      intro h
      apply hcnz
      have : (z : G) = c⁻¹ := (mul_eq_one_iff_eq_inv'.mp h)
      rw [this]
      exact (inv_eq_of_mul_eq_one_right hc).symm
    have hmem : ∀ x ∈ P, x * c = c * x → x ∈ P ⊓ Subgroup.centralizer ({c} : Set G) := by
      intro x hx hxc
      exact ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxc⟩
    have hczc : c * (z : G) * c = c * (c * (z : G)) := by
      rw [mul_assoc, ← hzc c hcP]
    refine four_le_card_of_four_distinct (a := 1) (b := c) (c := (z : G)) (d := c * (z : G))
      (Subgroup.one_mem _) (hmem c hcP rfl) (hmem z hzP (hzc c hcP).symm)
      (hmem (c * z) (P.mul_mem hcP hzP) hczc) hc1.symm (Ne.symm hz1') (Ne.symm hcz) hcnz ?_ ?_
    · intro h
      apply hz1'
      have := congrArg (fun y => c⁻¹ * y) h
      simpa using this.symm
    · intro h
      apply hc1
      have := congrArg (fun y => y * (z : G)⁻¹) h
      simpa using this.symm

theorem exists_comm_ne_one_ne [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P)
    (h4 : 4 ≤ Nat.card P) {c : G} (hcP : c ∈ P) (hc1 : c ≠ 1) (hc : c * c = 1) :
    ∃ x ∈ P, x * c = c * x ∧ x ≠ 1 ∧ x ≠ c := by
  by_contra hcon
  have hle : 4 ≤ Nat.card ↥(P ⊓ Subgroup.centralizer ({c} : Set G)) :=
    four_le_card_centralizer_of_involution hP h4 hcP hc1 hc
  have hsub : ((P ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) ⊆ {1, c} := by
    intro x hx
    by_contra hx'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx'
    exact hcon ⟨x, hx.1, Subgroup.mem_centralizer_singleton_iff.mp hx.2, hx'.1, hx'.2⟩
  have : Nat.card ↥(P ⊓ Subgroup.centralizer ({c} : Set G)) ≤ 2 := by
    calc Nat.card ↥(P ⊓ Subgroup.centralizer ({c} : Set G))
        = ((P ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G).ncard :=
          (Nat.card_coe_set_eq _).symm
      _ ≤ ({1, c} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by
          refine (Set.ncard_insert_le 1 {c}).trans ?_
          rw [Set.ncard_singleton]
  omega

end TwoGroups

section FourSubgroup

variable {G : Type} [Group G]

theorem isFourSubgroup_closure_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    IsFourSubgroup (Subgroup.closure ({a, b} : Set G)) := by
  refine ⟨⟨?_, fun x hx => ?_⟩, card_closure_pair ha hb hab ha1 hb1 hne⟩
  · exact Subgroup.isMulCommutative_closure (by
      intro x hx y hy _
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact Commute.refl _
      · rw [Set.mem_singleton_iff.mp hy]; exact hab
      · rw [Set.mem_singleton_iff.mp hx]; exact hab.symm
      · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy])
  · have hab' : b * a = a * b := hab.symm
    rcases mem_closure_pair_of_involutions ha hb hab hx with h | h | h | h <;> rw [h]
    · simp
    · rw [sq]; exact ha
    · rw [sq]; exact hb
    · rw [sq]
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab']
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha, hb, one_mul]

end FourSubgroup

section K0

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  (N : Notation25 hs) {t zK : G}

theorem k0_eq_K_of_R_eq (h : Lv2518 N t zK) {i : G} (hi : Hyp2519 N i)
    (hR : Rgrp2519 N i = Subgroup.closure ({t, i} : Set G)) : N.K0 = N.K := by
  by_contra hne
  have hf := h.facts2511
  obtain ⟨s, hsS, hne1, hK0, hcomm⟩ := (h.facts254.shape).resolve_left hne
  set K₂ : Subgroup G := CFSG.conjugate N.K s with hK₂
  have ht2 : t * t = 1 := N.t_mul_self' hf
  have hi2 : i * i = 1 := hi.mul_self
  have hti : t * i = i * t := N.t_comm_of_mem_S hf hi.mem_S
  have hZK : ∀ x ∈ N.K, (∀ y ∈ N.K, y * x = x * y) → x = 1 :=
    Unc25Small.center_K_trivial N h.facts258.simple
  have hKK₂ : ∀ a ∈ N.K, ∀ b ∈ K₂, a * b = b * a := fun a ha b hb =>
    BenderBranch.commute_of_commutator_eq_bot hcomm ha hb
  have hZK₂ : ∀ x ∈ K₂, (∀ y ∈ K₂, y * x = x * y) → x = 1 := by
    intro x hx hxc
    have hx' : s * x * s⁻¹ ∈ N.K := BenderBranch.mem_conjugate_iff.mp hx
    have h1 : s * x * s⁻¹ = 1 := by
      apply hZK _ hx'
      intro y hy
      have hy' : s⁻¹ * y * s ∈ K₂ := by
        rw [hK₂, BenderBranch.mem_conjugate_iff]
        simpa [mul_assoc] using hy
      have := hxc _ hy'
      calc y * (s * x * s⁻¹) = s * ((s⁻¹ * y * s) * x) * s⁻¹ := by group
        _ = s * (x * (s⁻¹ * y * s)) * s⁻¹ := by rw [this]
        _ = (s * x * s⁻¹) * y := by group
    have h2 : x = s⁻¹ * (s * x * s⁻¹) * s := by group
    rw [h2, h1]; group
  have hK₂K0 : K₂ ≤ N.K0 := by rw [hK0]; exact le_sup_right
  have htK₂ : t ∉ K₂ := by
    intro ht
    apply hf.t_ne_one
    refine hZK₂ t ht fun y hy => ?_
    exact Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer hf.t_mem) y (hK₂K0 hy)
  have hK0eq : ∀ x ∈ N.K0, (∀ y ∈ N.K, y * x = x * y) → x ∈ K₂ := by
    intro x hx hxc
    rw [hK0] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (BenderBranch.mem_sup_iff_of_commute hKK₂).mp hx
    have hab : a = 1 := by
      refine hZK a ha fun y hy => ?_
      have h1 := hxc y hy
      have h2 := hKK₂ y hy b hb
      have h3 : y * a * b = a * y * b := by
        calc y * a * b = y * (a * b) := by rw [mul_assoc]
          _ = (a * b) * y := h1
          _ = a * (b * y) := by rw [mul_assoc]
          _ = a * (y * b) := by rw [h2]
          _ = a * y * b := by rw [mul_assoc]
      exact mul_right_cancel h3
    rw [hab, one_mul]
    exact hb
  have hiK : ∀ a ∈ N.K, a * i = i * a := fun a ha =>
    Subgroup.mem_centralizer_iff.mp hi.mem_centralizer_K a ha
  have hiN : ∀ x ∈ K₂, i * x * i ∈ K₂ := by
    intro x hx
    have hxK0 : x ∈ N.K0 := hK₂K0 hx
    have hi' : i * x * i⁻¹ ∈ N.K0 :=
      (Subgroup.mem_normalizer_iff.mp (N.S_le_normalizer_K0 hi.mem_S) x).mp hxK0
    have hii : i⁻¹ = i := inv_eq_of_mul_eq_one_right hi2
    rw [hii] at hi'
    refine hK0eq _ hi' fun y hy => ?_
    have hyx : y * x = x * y := hKK₂ y hy x hx
    have hyi : y * i = i * y := hiK y hy
    calc y * (i * x * i) = (y * i) * x * i := by group
      _ = i * y * x * i := by rw [hyi]
      _ = i * (y * x) * i := by group
      _ = i * (x * y) * i := by rw [hyx]
      _ = i * x * (y * i) := by group
      _ = i * x * (i * y) := by rw [hyi]
      _ = i * x * i * y := by group
  set P : Subgroup G := N.S ⊓ K₂ with hP
  have hP2 : IsPGroup 2 P := N.tuple.sylow.isPGroup.to_le inf_le_left
  have hP8 : 8 ≤ Nat.card P := by
    have hSconj : CFSG.conjugate N.S s = N.S :=
      BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hsS)
    have hPeq : CFSG.conjugate N.SK s = P := by
      rw [Notation25.SK, BenderBranch.conjugate_inf, hSconj]
    rw [← hPeq, BenderBranch.card_conjugate]
    exact eight_le_card_of_shape h.facts258.SK_shape
  have hPbot : P ≠ ⊥ := by
    intro hb
    rw [hb] at hP8
    simp at hP8
  have hiP : ∀ p ∈ P, i * p * i ∈ P := fun p hp =>
    ⟨N.S.mul_mem (N.S.mul_mem hi.mem_S hp.1) hi.mem_S, hiN p hp.2⟩
  have hRc : ∀ x ∈ Rgrp2519 N i, x = 1 ∨ x = t ∨ x = i ∨ x = t * i := fun x hx =>
    mem_closure_pair_of_involutions ht2 hi2 hti (hR ▸ hx)
  have hmemR : ∀ x ∈ P, i * x = x * i → x ∈ Rgrp2519 N i := fun x hx hxi =>
    ⟨⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr hxi.symm⟩, hx.1,
      Subgroup.mem_centralizer_iff.mpr fun a ha => hKK₂ a ha x hx.2 ▸ rfl⟩
  have htcomm : ∀ x ∈ K₂, x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer hf.t_mem) x (hK₂K0 hx)
  obtain ⟨p, hpP, hp1, hpi⟩ := exists_fixed_ne_one hP2 hPbot hi2 hiP
  rcases hRc p (hmemR p hpP hpi) with h1 | h1 | h1 | h1
  · exact hp1 h1
  · exact htK₂ (h1 ▸ hpP.2)
  ·
    have hiP' : i ∈ P := h1 ▸ hpP
    obtain ⟨x, hxP, hxi, hx1, hxne⟩ := exists_comm_ne_one_ne hP2 (by omega) hiP' hi.ne_one hi2
    rcases hRc x (hmemR x hxP hxi.symm) with h2 | h2 | h2 | h2
    · exact hx1 h2
    · exact htK₂ (h2 ▸ hxP.2)
    · exact hxne h2
    · apply htK₂
      have : t = (t * i) * i := by rw [mul_assoc, hi2, mul_one]
      rw [this]
      exact K₂.mul_mem (h2 ▸ hxP.2) hiP'.2
  ·
    have hpP' : t * i ∈ P := h1 ▸ hpP
    have hp2 : (t * i) * (t * i) = 1 := by
      calc (t * i) * (t * i) = t * (i * t) * i := by group
        _ = t * (t * i) * i := by rw [← hti]
        _ = (t * t) * (i * i) := by group
        _ = 1 := by rw [ht2, hi2, one_mul]
    have hp1' : t * i ≠ 1 := fun h => hp1 (h1 ▸ h)
    obtain ⟨x, hxP, hxp, hx1, hxne⟩ := exists_comm_ne_one_ne hP2 (by omega) hpP' hp1' hp2
    have hxt := htcomm x hxP.2
    have hxi : i * x = x * i := by
      have hi_eq : i = t * (t * i) := by rw [← mul_assoc, ht2, one_mul]
      calc i * x = (t * (t * i)) * x := by rw [← hi_eq]
        _ = t * ((t * i) * x) := by rw [mul_assoc]
        _ = t * (x * (t * i)) := by rw [← hxp]
        _ = (t * x) * (t * i) := by rw [mul_assoc]
        _ = (x * t) * (t * i) := by rw [hxt]
        _ = x * (t * (t * i)) := by rw [mul_assoc]
        _ = x * i := by rw [← hi_eq]
    rcases hRc x (hmemR x hxP hxi) with h2 | h2 | h2 | h2
    · exact hx1 h2
    · exact htK₂ (h2 ▸ hxP.2)
    · apply htK₂
      have hiK₂ : i ∈ K₂ := h2 ▸ hxP.2
      have : t = (t * i) * i := by rw [mul_assoc, hi2, mul_one]
      rw [this]
      exact K₂.mul_mem hpP'.2 hiK₂
    · exact hxne h2

end K0

end CFSG.QuasithinUnique.Id2519
