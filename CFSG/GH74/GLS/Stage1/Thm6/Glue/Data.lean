module

public import CFSG.GH74.GLS.Stage1.Thm6.Lift
public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Group

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type} [Group G] (x : G)

abbrev Cx : Subgroup G := centralizer ({x} : Set G)

theorem mem_Cx {g : G} : g ∈ Cx x ↔ g * x = x * g := by
  simp [mem_centralizer_iff, eq_comm]

abbrev Ox : Subgroup ↥(Cx x) := pPrimeCore 2 ↥(Cx x)

open Classical in
@[expose] noncomputable def pr (g : G) : CentralizerBar x :=
  if h : g ∈ Cx x then (QuotientGroup.mk ⟨g, h⟩ : CentralizerBar x) else 1

theorem pr_of_mem {g : G} (hg : g ∈ Cx x) : pr x g = (QuotientGroup.mk ⟨g, hg⟩ : CentralizerBar x) :=
  by simp [pr, hg]

theorem pr_mul {g h : G} (hg : g ∈ Cx x) (hh : h ∈ Cx x) : pr x (g * h) = pr x g * pr x h := by
  rw [pr_of_mem x (mul_mem hg hh), pr_of_mem x hg, pr_of_mem x hh]
  rfl

theorem pr_one : pr x (1 : G) = 1 := by
  rw [pr_of_mem x (one_mem _)]
  rfl

theorem pr_inv {g : G} (hg : g ∈ Cx x) : pr x g⁻¹ = (pr x g)⁻¹ := by
  rw [pr_of_mem x (inv_mem hg), pr_of_mem x hg]
  rfl

theorem pr_pow {g : G} (hg : g ∈ Cx x) (n : ℕ) : pr x (g ^ n) = (pr x g) ^ n := by
  induction n with
  | zero => simp [pr_one]
  | succ n ih => rw [pow_succ, pr_mul x (pow_mem hg n) hg, ih, pow_succ]

theorem pr_eq_one_iff {g : G} (hg : g ∈ Cx x) :
    pr x g = 1 ↔ (⟨g, hg⟩ : ↥(Cx x)) ∈ Ox x := by
  rw [pr_of_mem x hg]
  exact QuotientGroup.eq_one_iff _

theorem pr_surj (c : CentralizerBar x) : ∃ g : G, g ∈ Cx x ∧ pr x g = c := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  exact ⟨g.1, g.2, pr_of_mem x g.2⟩

section KgSec

variable (Kb : Subgroup (CentralizerBar x))

@[expose] def Kg : Subgroup G where
  carrier := {g | g ∈ Cx x ∧ pr x g ∈ Kb}
  one_mem' := ⟨one_mem _, by rw [pr_one]; exact one_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha, haK⟩ ⟨hb, hbK⟩
    exact ⟨mul_mem ha hb, by rw [pr_mul x ha hb]; exact mul_mem haK hbK⟩
  inv_mem' := by
    rintro a ⟨ha, haK⟩
    exact ⟨inv_mem ha, by rw [pr_inv x ha]; exact inv_mem haK⟩

theorem mem_Kg {g : G} : g ∈ Kg x Kb ↔ g ∈ Cx x ∧ pr x g ∈ Kb := Iff.rfl

end KgSec

section Kb

variable (Kb : Subgroup (CentralizerBar x)) [Kb.Normal]

@[expose] noncomputable def phig (g : G) : MulAut ↥Kb := MulAut.conjNormal (pr x g)

theorem phig_mul {g h : G} (hg : g ∈ Cx x) (hh : h ∈ Cx x) :
    phig x Kb (g * h) = phig x Kb g * phig x Kb h := by
  simp only [phig, pr_mul x hg hh, map_mul]

theorem phig_one : phig x Kb (1 : G) = 1 := by simp [phig, pr_one]

theorem phig_inv {g : G} (hg : g ∈ Cx x) : phig x Kb g⁻¹ = (phig x Kb g)⁻¹ := by
  simp only [phig, pr_inv x hg, map_inv]

theorem phig_pow {g : G} (hg : g ∈ Cx x) (n : ℕ) : phig x Kb (g ^ n) = (phig x Kb g) ^ n := by
  simp only [phig, pr_pow x hg, map_pow]

theorem phig_apply (g : G) (k : Kb) :
    ((phig x Kb g k : Kb) : CentralizerBar x) = pr x g * k * (pr x g)⁻¹ := by
  simp [phig, MulAut.conjNormal_apply]

@[expose] def Qg (T : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ T ∧ g ∈ Cx x ∧ phig x Kb g = 1}
  one_mem' := ⟨one_mem _, one_mem _, phig_one x Kb⟩
  mul_mem' := by
    rintro a b ⟨ha, haC, ha1⟩ ⟨hb, hbC, hb1⟩
    exact ⟨mul_mem ha hb, mul_mem haC hbC, by rw [phig_mul x Kb haC hbC, ha1, hb1, one_mul]⟩
  inv_mem' := by
    rintro a ⟨ha, haC, ha1⟩
    exact ⟨inv_mem ha, inv_mem haC, by rw [phig_inv x Kb haC, ha1, inv_one]⟩

theorem mem_Qg {T : Subgroup G} {g : G} :
    g ∈ Qg x Kb T ↔ g ∈ T ∧ g ∈ Cx x ∧ phig x Kb g = 1 := Iff.rfl

abbrev Pg (T : Subgroup G) : Subgroup G := T ⊓ Kg x Kb

@[expose] def Rdg {F : Type} [Field F] [Finite F] (e : ↥Kb ≃* IVK.L2 F) (T : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ T ∧ g ∈ Cx x ∧ phig x Kb g ∈ IVK.innDiagSub e}
  one_mem' := ⟨one_mem _, one_mem _, by rw [phig_one]; exact one_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha, haC, haD⟩ ⟨hb, hbC, hbD⟩
    exact ⟨mul_mem ha hb, mul_mem haC hbC, by rw [phig_mul x Kb haC hbC]; exact mul_mem haD hbD⟩
  inv_mem' := by
    rintro a ⟨ha, haC, haD⟩
    exact ⟨inv_mem ha, inv_mem haC, by rw [phig_inv x Kb haC]; exact inv_mem haD⟩

end Kb

theorem x_mem_Cx : x ∈ Cx x := (mem_Cx x).2 rfl

theorem x_mem_of_sylow [Finite G] {T : Subgroup G} (hT : IsSylow2In T (Cx x)) (hx : x * x = 1)
    (hx1 : x ≠ 1) : x ∈ T := by
  have hzp : IsPGroup 2 ↥(Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [card_zpowers_of_sq hx hx1]; norm_num)
  obtain ⟨T₁, hT₁, hxT₁⟩ := exists_sylow2_ge hzp (Subgroup.zpowers_le.mpr (x_mem_Cx x))
  obtain ⟨c, hc, hTc⟩ := sylow2_exists_conj hT₁ hT
  have hcx : c * x = x * c := (mem_Cx x).1 hc
  have : x ∈ Hconj c T₁ := by
    rw [mem_Hconj]
    have : c * x * c⁻¹ = x := by rw [hcx]; group
    rw [this]; exact hxT₁ (Subgroup.mem_zpowers x)
  rw [hTc]; exact this

theorem eq_one_of_pr_eq_one [Finite G] {T : Subgroup G} (hT : IsSylow2In T (Cx x)) {g : G}
    (hgT : g ∈ T) (hgC : g ∈ Cx x) (h : pr x g = 1) : g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(T.subgroupOf (Cx x)) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  have hN : ¬ 2 ∣ Nat.card (Ox x) := by
    have := pPrimeCore_coprime_card (p := 2) (G := ↥(Cx x))
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 this
  have hbot := inf_eq_bot_of_isPGroup_of_coprime (Ox x) hp hN
  have hmem : (⟨g, hgC⟩ : ↥(Cx x)) ∈ T.subgroupOf (Cx x) ⊓ Ox x :=
    ⟨(Subgroup.mem_subgroupOf).2 hgT, (pr_eq_one_iff x hgC).1 h⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem mem_sup_iff_of_comm {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : G} :
    g ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  constructor
  · intro hg
    let S : Subgroup G :=
      { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
        one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
          refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
          calc a * b * (a' * b') = a * (b * a') * b' := by simp only [mul_assoc]
            _ = a * (a' * b) * b' := by rw [← h a' ha' b hb]
            _ = a * a' * (b * b') := by simp only [mul_assoc]
        inv_mem' := by
          rintro _ ⟨a, ha, b, hb, rfl⟩
          refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
          rw [mul_inv_rev]
          have : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := by
            have := h a ha b hb
            calc b⁻¹ * a⁻¹ = (a * b)⁻¹ := by rw [mul_inv_rev]
              _ = (b * a)⁻¹ := by rw [this]
              _ = a⁻¹ * b⁻¹ := by rw [mul_inv_rev]
          exact this }
    have hAS : A ≤ S := fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩
    have hBS : B ≤ S := fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩
    exact (sup_le hAS hBS) hg
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact mul_mem (mem_sup_left ha) (mem_sup_right hb)

theorem pr_x_central (c : CentralizerBar x) : pr x x * c = c * pr x x := by
  obtain ⟨g, hgC, rfl⟩ := pr_surj x c
  rw [← pr_mul x (x_mem_Cx x) hgC, ← pr_mul x hgC (x_mem_Cx x), ((mem_Cx x).1 hgC).symm]

section Kb2

variable (Kb : Subgroup (CentralizerBar x)) [Kb.Normal]

@[expose] noncomputable def phiC : ↥(Cx x) →* MulAut ↥Kb :=
  MulAut.conjNormal.comp (QuotientGroup.mk' (Ox x))

theorem phig_of_mem {g : G} (hg : g ∈ Cx x) : phig x Kb g = phiC x Kb ⟨g, hg⟩ := by
  simp [phig, phiC, pr_of_mem x hg]

theorem phig_x_eq_one : phig x Kb x = 1 := by
  ext k
  rw [phig_apply, MulAut.one_apply, pr_x_central x (k : CentralizerBar x)]
  group

theorem phig_eq_conj {g : G} (hg : g ∈ Kg x Kb) :
    phig x Kb g = MulAut.conj (⟨pr x g, ((mem_Kg x Kb).1 hg).2⟩ : ↥Kb) := by
  rw [phig]
  exact MulAut.conjNormal_val (h := (⟨pr x g, ((mem_Kg x Kb).1 hg).2⟩ : ↥Kb))

end Kb2

section Struct

variable (Kb : Subgroup (CentralizerBar x)) [Kb.Normal] {T : Subgroup G}

theorem Qg_normal (hT : T ≤ Cx x) : NormalIn (Qg x Kb T) T := by
  refine ⟨fun g hg => hg.1, fun t ht n hn => ?_⟩
  obtain ⟨hnT, hnC, hn1⟩ := hn
  have htC := hT ht
  refine ⟨T.mul_mem (T.mul_mem ht hnT) (T.inv_mem ht), mul_mem (mul_mem htC hnC) (inv_mem htC), ?_⟩
  rw [phig_mul x Kb (mul_mem htC hnC) (inv_mem htC), phig_mul x Kb htC hnC, hn1, mul_one,
    phig_inv x Kb htC, mul_inv_cancel]

theorem Pg_normal (hT : T ≤ Cx x) : NormalIn (Pg x Kb T) T := by
  refine ⟨inf_le_left, fun t ht n hn => ?_⟩
  obtain ⟨hnT, hnK⟩ := hn
  have htC := hT ht
  have hnC : n ∈ Cx x := ((mem_Kg x Kb).1 hnK).1
  refine ⟨T.mul_mem (T.mul_mem ht hnT) (T.inv_mem ht), ?_⟩
  refine (mem_Kg x Kb).2 ⟨mul_mem (mul_mem htC hnC) (inv_mem htC), ?_⟩
  rw [pr_mul x (mul_mem htC hnC) (inv_mem htC), pr_mul x htC hnC, pr_inv x htC]
  exact (inferInstance : Kb.Normal).conj_mem _ ((mem_Kg x Kb).1 hnK).2 _

theorem Pg_comm_Qg [Finite G] (hT : IsSylow2In T (Cx x)) :
    ∀ p ∈ Pg x Kb T, ∀ q ∈ Qg x Kb T, p * q = q * p := by
  rintro p ⟨hpT, hpK⟩ q ⟨hqT, hqC, hq1⟩
  have hpC : p ∈ Cx x := ((mem_Kg x Kb).1 hpK).1
  have hcomm : pr x q * pr x p = pr x p * pr x q := by
    have h1 := phig_apply x Kb q ⟨pr x p, ((mem_Kg x Kb).1 hpK).2⟩
    rw [hq1] at h1
    simp only [MulAut.one_apply] at h1
    have h2 : pr x p = pr x q * pr x p * (pr x q)⁻¹ := h1
    calc pr x q * pr x p = (pr x q * pr x p * (pr x q)⁻¹) * pr x q := by group
      _ = pr x p * pr x q := by rw [← h2]
  have hpq : pr x (p * q) = pr x (q * p) := by
    rw [pr_mul x hpC hqC, pr_mul x hqC hpC, hcomm]
  have hc : p * q * (q * p)⁻¹ = 1 := by
    refine eq_one_of_pr_eq_one x hT (T.mul_mem (T.mul_mem hpT hqT) (T.inv_mem (T.mul_mem hqT hpT)))
      (mul_mem (mul_mem hpC hqC) (inv_mem (mul_mem hqC hpC))) ?_
    rw [pr_mul x (mul_mem hpC hqC) (inv_mem (mul_mem hqC hpC)), pr_inv x (mul_mem hqC hpC), hpq,
      mul_inv_cancel]
  exact mul_inv_eq_one.1 hc

theorem Pg_inf_Qg [Finite G] (hconj : Function.Injective (MulAut.conj : ↥Kb →* MulAut ↥Kb))
    (hT : IsSylow2In T (Cx x)) : Pg x Kb T ⊓ Qg x Kb T = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨hgT, hgK⟩, -, hgC, hg1⟩
  have hc := phig_eq_conj x Kb hgK
  rw [hg1] at hc
  have h2 : (⟨pr x g, ((mem_Kg x Kb).1 hgK).2⟩ : ↥Kb) = 1 := by
    apply hconj
    rw [← hc, map_one]
  have h3 : pr x g = 1 := congrArg Subtype.val h2
  exact eq_one_of_pr_eq_one x hT hgT hgC h3

end Struct

end CFSG.GH74.GLS.Stage1.Thm6.Glue
