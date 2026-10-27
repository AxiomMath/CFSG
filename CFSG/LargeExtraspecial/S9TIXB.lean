module

public import CFSG.LargeExtraspecial.S9TIX
public import CFSG.CGT.Timmesfeld75.StrongClosure

public section

namespace CFSG.LargeExtraspecial.S9.TIX

open CFSG.CGT.Timmesfeld75 Subgroup

variable {G : Type*} [Group G]

theorem dihedral_central_of_even_order_mem {x y : G} (hx : x * x = 1) (hy : y * y = 1) {m : ℕ}
    (hm0 : 0 < m) (hm : orderOf (x * y) = 2 * m) :
    ∃ z : G, z * z = 1 ∧ z ≠ 1 ∧ x * z = z * x ∧ y * z = z * y ∧
      ((∃ g ∈ closure ({x, y} : Set G), y * z = g⁻¹ * x * g) ∨
        ∃ g ∈ closure ({x, y} : Set G), y * z = g⁻¹ * y * g) := by
  have hw : x * y ∈ closure ({x, y} : Set G) :=
    mul_mem (subset_closure (Set.mem_insert x {y}))
      (subset_closure (Set.mem_insert_of_mem x (Set.mem_singleton y)))
  have hzz : (x * y) ^ m * (x * y) ^ m = 1 := by
    rw [← pow_add, ← two_mul, ← hm]
    exact pow_orderOf_eq_one _
  have hzinv : ((x * y) ^ m)⁻¹ = (x * y) ^ m := inv_eq_of_mul_eq_one_right hzz
  have hxz : x * (x * y) ^ m = (x * y) ^ m * x := by
    have h1 : x * (x * y) ^ m * x⁻¹ = (x * y) ^ m := by
      rw [← conj_pow, left_invol_inverts hx hy, inv_pow, hzinv]
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hxw : x * (x * y) = y := by rw [← mul_assoc, hx, one_mul]
  have hyz : y * (x * y) ^ m = (x * y) ^ m * y := by
    calc y * (x * y) ^ m = x * (x * y) * (x * y) ^ m := by rw [hxw]
      _ = x * ((x * y) * (x * y) ^ m) := mul_assoc _ _ _
      _ = x * ((x * y) ^ m * (x * y)) := by rw [(Commute.self_pow (x * y) m).eq]
      _ = (x * (x * y) ^ m) * (x * y) := (mul_assoc _ _ _).symm
      _ = ((x * y) ^ m * x) * (x * y) := by rw [hxz]
      _ = (x * y) ^ m * (x * (x * y)) := mul_assoc _ _ _
      _ = (x * y) ^ m * y := by rw [hxw]
  refine ⟨(x * y) ^ m, hzz, pow_ne_one_of_lt_orderOf hm0.ne' (by omega), hxz, hyz, ?_⟩
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · right
    refine ⟨(x * y) ^ k, pow_mem hw k, ?_⟩
    rw [inv_pow_mul_mul_pow_of_inverts (right_invol_inverts hx hy) k,
      show 2 * k = m by omega, hzinv, hyz]
  · left
    refine ⟨(x * y) ^ (k + 1), pow_mem hw (k + 1), ?_⟩
    have h1 := inv_pow_mul_mul_pow_of_inverts (left_invol_inverts hx hy) (k + 1)
    calc y * (x * y) ^ m = (x * y)⁻¹ * x * (x * y) ^ m := by rw [← invol_eq_inv_mul_mul hy]
      _ = (x * y)⁻¹ * ((x * y) ^ m * x) := by rw [mul_assoc, hxz]
      _ = (x * y)⁻¹ * (x * y) ^ m * x := (mul_assoc _ _ _).symm
      _ = ((x * y) ^ m * (x * y))⁻¹ * x := by rw [mul_inv_rev ((x * y) ^ m) (x * y), hzinv]
      _ = ((x * y) ^ (2 * (k + 1)))⁻¹ * x := by
        rw [show 2 * (k + 1) = m + 1 by omega, pow_succ]
      _ = ((x * y) ^ (k + 1))⁻¹ * x * (x * y) ^ (k + 1) := h1.symm

namespace Setup

variable {A Ab L Lb M : Subgroup G} (S : Setup A Ab L Lb M)
include S

theorem A_ne_bot : A ≠ ⊥ := fun h => S.ne_bot (le_bot_iff.mp (h ▸ S.L_le))

theorem Ab_ne_bot [Finite G] : Ab ≠ ⊥ := by
  intro h
  apply S.A_ne_bot
  rw [← card_eq_one, S.card, h, card_bot]

variable [Finite G]

theorem Lb_ne_bot : Lb ≠ ⊥ := by
  obtain ⟨⟨l, hl⟩, hl1'⟩ := ne_bot_iff_exists_ne_one.mp S.ne_bot
  have hl1 : l ≠ 1 := fun h => hl1' (Subtype.ext h)
  obtain ⟨⟨b, hb⟩, hb1'⟩ := ne_bot_iff_exists_ne_one.mp S.Ab_ne_bot
  have hb1 : b ≠ 1 := fun h => hb1' (Subtype.ext h)
  intro hbot
  have hc := S.commutator_mem_Lb hb hl
  rw [hbot, mem_bot] at hc
  have hbl : b * l = l * b := by
    calc b * l = b * l * b⁻¹ * l⁻¹ * (l * b) := by group
      _ = l * b := by rw [hc, one_mul]
  have hbLb : b ∈ Lb := S.mem_Lb_of_commute hb (S.L_le hl) hl1 hbl
  rw [hbot, mem_bot] at hbLb
  exact hb1 hbLb

theorem le_normalizer_Ab (hle : Ab ≤ normalizer (A : Set G)) :
    A ≤ normalizer (Ab : Set G) := by
  intro a ha
  by_contra haN
  have hBa : Ab ⊓ conjSubgroup a Ab = ⊥ := by
    by_contra hne
    exact haN (conjSubgroup_eq_self_iff.mp (S.tiAb a (mem_sup_left ha) hne))
  have hcon : ∀ b ∈ Ab, b * a⁻¹ * b⁻¹ * a ∈ A := fun b hb =>
    mul_mem ((mem_normalizer_iff.mp (hle hb) a⁻¹).mp (inv_mem ha)) ha
  let φ : Ab → A := fun b => ⟨(b : G) * a⁻¹ * (b : G)⁻¹ * a, hcon b b.2⟩
  have hφ : Function.Injective φ := by
    intro b b' hbb
    have h1 : (b : G) * a⁻¹ * (b : G)⁻¹ * a = (b' : G) * a⁻¹ * (b' : G)⁻¹ * a :=
      congrArg Subtype.val hbb
    have hcB : (b' : G)⁻¹ * b ∈ Ab := mul_mem (inv_mem b'.2) b.2
    have h2 : (b : G) * a⁻¹ * (b : G)⁻¹ = (b' : G) * a⁻¹ * (b' : G)⁻¹ := mul_right_cancel h1
    have hca : (b' : G)⁻¹ * b * a = a * ((b' : G)⁻¹ * b) := by
      have h3 : (b' : G)⁻¹ * b * a⁻¹ * ((b' : G)⁻¹ * b)⁻¹ = a⁻¹ := by
        calc (b' : G)⁻¹ * b * a⁻¹ * ((b' : G)⁻¹ * b)⁻¹
            = (b' : G)⁻¹ * ((b : G) * a⁻¹ * (b : G)⁻¹) * b' := by group
          _ = (b' : G)⁻¹ * ((b' : G) * a⁻¹ * (b' : G)⁻¹) * b' := by rw [h2]
          _ = a⁻¹ := by group
      have h4 : (b' : G)⁻¹ * b * a⁻¹ = a⁻¹ * ((b' : G)⁻¹ * b) := by
        calc (b' : G)⁻¹ * b * a⁻¹ = (b' : G)⁻¹ * b * a⁻¹ * ((b' : G)⁻¹ * b)⁻¹ *
            ((b' : G)⁻¹ * b) := by group
          _ = a⁻¹ * ((b' : G)⁻¹ * b) := by rw [h3]
      calc (b' : G)⁻¹ * b * a = a * (a⁻¹ * ((b' : G)⁻¹ * b)) * a := by group
        _ = a * ((b' : G)⁻¹ * b * a⁻¹) * a := by rw [h4]
        _ = a * ((b' : G)⁻¹ * b) := by group
    have hcBa : (b' : G)⁻¹ * b ∈ conjSubgroup a Ab := by
      rw [mem_conjSubgroup]
      have : a⁻¹ * ((b' : G)⁻¹ * b) * a = (b' : G)⁻¹ * b := by
        calc a⁻¹ * ((b' : G)⁻¹ * b) * a = a⁻¹ * ((b' : G)⁻¹ * b * a) := by group
          _ = a⁻¹ * (a * ((b' : G)⁻¹ * b)) := by rw [hca]
          _ = (b' : G)⁻¹ * b := by group
      rw [this]
      exact hcB
    have hc1 : (b' : G)⁻¹ * b = 1 := by
      have : (b' : G)⁻¹ * b ∈ Ab ⊓ conjSubgroup a Ab := mem_inf.mpr ⟨hcB, hcBa⟩
      rw [hBa] at this
      exact mem_bot.mp this
    apply Subtype.ext
    calc (b : G) = b' * ((b' : G)⁻¹ * b) := by group
      _ = b' := by rw [hc1, mul_one]
  obtain ⟨b, hb⟩ := (hφ.bijective_of_nat_card_le S.card.le).2 ⟨a, ha⟩
  have h1 : (b : G) * a⁻¹ * (b : G)⁻¹ * a = a := congrArg Subtype.val hb
  have ha1 : a = 1 := by
    have : (b : G) * a⁻¹ * (b : G)⁻¹ = 1 := by
      calc (b : G) * a⁻¹ * (b : G)⁻¹ = (b : G) * a⁻¹ * (b : G)⁻¹ * a * a⁻¹ := by group
        _ = 1 := by rw [h1, mul_inv_cancel]
    have h5 : a⁻¹ = 1 := by
      calc a⁻¹ = (b : G)⁻¹ * ((b : G) * a⁻¹ * (b : G)⁻¹) * b := by group
        _ = 1 := by rw [this]; group
    simpa using h5
  exact haN (ha1 ▸ one_mem _)

theorem Lb_ne : Lb ≠ Ab := by
  intro h
  have hle : Ab ≤ normalizer (A : Set G) := fun b hb => (S.mem_Lb.mp (h ▸ hb)).2
  apply S.ne
  rw [S.hL]
  exact le_antisymm inf_le_left (le_inf le_rfl (S.le_normalizer_Ab hle))

theorem symm : Setup Ab A Lb L M where
  sqA := S.sqAb
  sqAb := S.sqA
  card := S.card.symm
  tiA := fun x hx => S.tiAb x (by rwa [sup_comm] at hx)
  tiAb := fun x hx => S.tiA x (by rwa [sup_comm] at hx)
  mix := by
    intro x hx hne
    have hx' : x⁻¹ ∈ A ⊔ Ab := inv_mem (by rwa [sup_comm] at hx)
    have hne' : conjSubgroup x⁻¹ A ⊓ Ab ≠ ⊥ := by
      intro hbot
      apply hne
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨hy1, hy2⟩ := mem_inf.mp hy
      have hmem : x⁻¹ * y * x ∈ conjSubgroup x⁻¹ A ⊓ Ab := by
        refine mem_inf.mpr ⟨?_, mem_conjSubgroup.mp hy1⟩
        rw [mem_conjSubgroup, inv_inv]
        simpa [mul_assoc] using hy2
      rw [hbot, mem_bot] at hmem
      rw [mem_bot]
      calc y = x * (x⁻¹ * y * x) * x⁻¹ := by group
        _ = 1 := by rw [hmem]; group
    have h1 := S.mix x⁻¹ hx' hne'
    rw [← h1, ← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
  hL := S.hLb
  hLb := S.hL
  hM := S.hM.trans (sup_comm L Lb)
  ne_bot := S.Lb_ne_bot
  ne := S.Lb_ne

theorem conj_eq_of_commutator_mem {x a b : G} (hxX : x ∈ A ⊔ Ab) (ha : a ∈ A) (haL : a ∉ L)
    (hb : b ∈ Ab) (hbL : b ∉ Lb) (hc : (x⁻¹ * a * x) * b * (x⁻¹ * a * x)⁻¹ * b⁻¹ ∈ M) :
    conjSubgroup x⁻¹ A = Ab := by
  have hx := S.sup_le_normalizer_M hxX
  have hsuff : ∀ y, y ∈ conjSubgroup x⁻¹ A → y ∈ Ab → y ≠ 1 → conjSubgroup x⁻¹ A = Ab := by
    intro y hy1 hy2 hy
    refine S.mix x⁻¹ (inv_mem hxX) fun hbot => hy ?_
    have : y ∈ conjSubgroup x⁻¹ A ⊓ Ab := mem_inf.mpr ⟨hy1, hy2⟩
    rw [hbot, mem_bot] at this
    exact this
  have hmemx : ∀ y, x * y * x⁻¹ ∈ A → y ∈ conjSubgroup x⁻¹ A := fun y hy => by
    rw [mem_conjSubgroup, inv_inv]
    exact hy
  have ha'2 : (x⁻¹ * a * x) * (x⁻¹ * a * x) = 1 := by
    rw [show x⁻¹ * a * x * (x⁻¹ * a * x) = x⁻¹ * (a * a) * x by group, S.sqA a ha]
    group
  have hb2 : b * b = 1 := S.sqAb b hb
  have hcc := S.sq_M hc
  obtain ⟨ha'c, hcb⟩ := commute_commutator_of_involutions ha'2 hb2 rfl hcc
  have hcLb := S.symm.mem_L_of_commute_M hb hbL hc hcb.symm
  have hcL := S.conj_mem_L_of_commute_M hx ha haL hc ha'c.symm
  by_cases hc1 : (x⁻¹ * a * x) * b * (x⁻¹ * a * x)⁻¹ * b⁻¹ = 1
  ·
    have ha'b : (x⁻¹ * a * x) * b = b * (x⁻¹ * a * x) := by
      calc (x⁻¹ * a * x) * b = ((x⁻¹ * a * x) * b * (x⁻¹ * a * x)⁻¹ * b⁻¹) *
          (b * (x⁻¹ * a * x)) := by group
        _ = b * (x⁻¹ * a * x) := by rw [hc1, one_mul]
    have hb1 : b ≠ 1 := fun h => hbL (h ▸ one_mem _)
    have ha'X : x⁻¹ * a * x ∈ A ⊔ Ab :=
      mul_mem (mul_mem (inv_mem hxX) (mem_sup_left ha)) hxX
    have ha'N : x⁻¹ * a * x ∈ normalizer (Ab : Set G) :=
      mem_normalizer_of_commute_of_isTIIn S.tiAb ha'X hb hb1 ha'b
    have ha'M : x⁻¹ * a * x ∈ normalizer (M : Set G) := S.sup_le_normalizer_M ha'X
    have hLbeq : Lb = Ab ⊓ M := S.symm.inf_M.symm
    have ha'NLb : x⁻¹ * a * x ∈ normalizer (Lb : Set G) := by
      rw [hLbeq]
      exact mem_normalizer_inf' ha'N ha'M
    obtain ⟨y, hy, hy1, hya'⟩ :=
      exists_ne_one_commute (fun u hu => S.sqAb u (S.Lb_le hu)) S.Lb_ne_bot ha'NLb ha'2
    have hyL : x * y * x⁻¹ ∈ L :=
      S.conj_mem_L_of_commute_M hx ha haL (S.Lb_le_M hy) hya'.symm
    exact hsuff y (hmemx y (S.L_le hyL)) (S.Lb_le hy) hy1
  · exact hsuff _ (hmemx _ (S.L_le hcL)) (S.Lb_le hcLb) hc1

end Setup

end CFSG.LargeExtraspecial.S9.TIX
