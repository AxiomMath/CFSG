module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.ProdAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.StandardHypA
public import CFSG.Alternating.Multipliers.Main

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup CFSG.RankThree.PerfectCover CFSG.Alternating.Multipliers
open scoped commutatorElement

theorem card_ker_dvd_two_alt8 {P : Type} [Group P] (hP : commutator P = ⊤)
    {π : P →* alternatingGroup (Fin 8)} (hπs : Function.Surjective π)
    (hπk : π.ker ≤ center P) : Nat.card π.ker ∣ 2 := by
  have : Group.IsPerfect P := (Group.isPerfect_def).2 hP
  have h := Subgroup.card_map_dvd (hopfMultiplier (alternatingGroup (Fin 8))) (hopfLift π hπs hπk)
  rwa [map_hopfMultiplier_hopfLift π hπs hπk,
    card_hopfMultiplier_alternatingGroup (n := 8) le_rfl] at h

theorem alt8_simple : IsSimpleGroup (alternatingGroup (Fin 8)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem alt8_commutator : commutator (alternatingGroup (Fin 8)) = ⊤ :=
  commutator_alternatingGroup_eq_top (by simp)

theorem alt8_central {a : alternatingGroup (Fin 8)} (h : ∀ c, a * c = c * a) : a = 1 := by
  have hc : a ∈ center (alternatingGroup (Fin 8)) :=
    Subgroup.mem_center_iff.2 fun c => (h c).symm
  rcases alt8_simple.eq_bot_or_eq_top_of_normal (center (alternatingGroup (Fin 8))) with h0 | h1
  · rwa [h0, mem_bot] at hc
  · exfalso
    obtain ⟨x, y, hxy⟩ := alternatingGroup_fin_eight_not_comm
    have hx : x ∈ center (alternatingGroup (Fin 8)) := by rw [h1]; trivial
    exact hxy (Subgroup.mem_center_iff.1 hx y).symm

theorem alt8_hsimple (N : Subgroup (alternatingGroup (Fin 8))) (hN : N.Normal) :
    N = ⊥ ∨ N = ⊤ := by
  have := hN
  exact alt8_simple.eq_bot_or_eq_top_of_normal N

theorem alt8_nontrivial : ∃ s : alternatingGroup (Fin 8), s ≠ 1 := by
  obtain ⟨x, y, hxy⟩ := alternatingGroup_fin_eight_not_comm
  by_cases hx : x = 1
  · exact ⟨y, fun hy => hxy (by rw [hx, hy])⟩
  · exact ⟨x, hx⟩

theorem alt8_exists_noncomm {a : alternatingGroup (Fin 8)} (ha : a ≠ 1) :
    ∃ c : alternatingGroup (Fin 8), a * c ≠ c * a := by
  by_contra h
  push Not at h
  exact ha (alt8_central h)

theorem prod_normal_eq_top (M : Subgroup (alternatingGroup (Fin 8) × alternatingGroup (Fin 8)))
    [hM : M.Normal] {a b : alternatingGroup (Fin 8)} (ha : a ≠ 1) (hb : b ≠ 1)
    (hm : (a, b) ∈ M) : M = ⊤ := by
  obtain ⟨c, hc⟩ := alt8_exists_noncomm ha
  obtain ⟨d, hd⟩ := alt8_exists_noncomm hb
  have h1 : (a * c * a⁻¹ * c⁻¹, (1 : alternatingGroup (Fin 8))) ∈ M := by
    have h := M.mul_mem hm (hM.conj_mem _ (M.inv_mem hm) (c, 1))
    have e : (a, b) * ((c, 1) * (a, b)⁻¹ * (c, 1)⁻¹) =
        (a * c * a⁻¹ * c⁻¹, (1 : alternatingGroup (Fin 8))) := by
      ext <;> simp [mul_assoc]
    rwa [e] at h
  have h2 : ((1 : alternatingGroup (Fin 8)), b * d * b⁻¹ * d⁻¹) ∈ M := by
    have h := M.mul_mem hm (hM.conj_mem _ (M.inv_mem hm) (1, d))
    have e : (a, b) * ((1, d) * (a, b)⁻¹ * (1, d)⁻¹) =
        ((1 : alternatingGroup (Fin 8)), b * d * b⁻¹ * d⁻¹) := by
      ext <;> simp [mul_assoc]
    rwa [e] at h
  have hne1 : a * c * a⁻¹ * c⁻¹ ≠ 1 := by
    intro h
    apply hc
    calc a * c = a * c * a⁻¹ * c⁻¹ * c * a := by group
      _ = c * a := by rw [h, one_mul]
  have hne2 : b * d * b⁻¹ * d⁻¹ ≠ 1 := by
    intro h
    apply hd
    calc b * d = b * d * b⁻¹ * d⁻¹ * d * b := by group
      _ = d * b := by rw [h, one_mul]
  have hf := ProdAut.fst_of_ne_one alt8_hsimple M hne1 h1
  have hs := ProdAut.snd_of_ne_one alt8_hsimple M hne2 h2
  rw [eq_top_iff]
  rintro ⟨s, s'⟩ -
  have := M.mul_mem (hf s) (hs s')
  simpa using this

section SchurProd

variable {Q : Type} [Group Q]

@[expose] def firstSub (f : Q →* alternatingGroup (Fin 8) × alternatingGroup (Fin 8)) :
    Subgroup Q :=
  ((MonoidHom.snd _ _).comp f).ker

theorem mem_firstSub {f : Q →* alternatingGroup (Fin 8) × alternatingGroup (Fin 8)} {x : Q} :
    x ∈ firstSub f ↔ (f x).2 = 1 := by
  simp [firstSub, MonoidHom.mem_ker]

instance firstSub_normal (f : Q →* alternatingGroup (Fin 8) × alternatingGroup (Fin 8)) :
    (firstSub f).Normal := MonoidHom.normal_ker _

theorem commutatorElement_mul_central' {y y' k k' : Q} (hk : k ∈ center Q) (hk' : k' ∈ center Q) :
    ⁅y * k, y' * k'⁆ = ⁅y, y'⁆ := by
  have hc : ∀ g : Q, Commute k g := fun g => (Subgroup.mem_center_iff.1 hk g).symm
  have hc' : ∀ g : Q, Commute k' g := fun g => (Subgroup.mem_center_iff.1 hk' g).symm
  rw [commutatorElement_mul_left_eq_conj_mul, (hc _).commutator_eq, mul_one, mul_inv_cancel,
    one_mul, commutatorElement_mul_right_eq_mul_conj, ((hc' _).symm).commutator_eq, mul_one,
    mul_inv_cancel_right]

variable {f : Q →* alternatingGroup (Fin 8) × alternatingGroup (Fin 8)}

theorem exists_mem_commutator_firstSub (hf : Function.Surjective f) (c : alternatingGroup (Fin 8)) :
    ∃ y ∈ ⁅firstSub f, firstSub f⁆, f y = (c, 1) := by
  have h1 : (MonoidHom.inl (alternatingGroup (Fin 8)) (alternatingGroup (Fin 8))).range ≤
      (firstSub f).map f := by
    rintro _ ⟨c', rfl⟩
    obtain ⟨x, hx⟩ := hf (c', 1)
    exact ⟨x, mem_firstSub.2 (by rw [hx]), hx⟩
  have h2 := commutator_le_map_commutator h1 h1
  have h3 : ⁅(MonoidHom.inl (alternatingGroup (Fin 8)) (alternatingGroup (Fin 8))).range,
      (MonoidHom.inl (alternatingGroup (Fin 8)) (alternatingGroup (Fin 8))).range⁆ =
      (MonoidHom.inl (alternatingGroup (Fin 8)) (alternatingGroup (Fin 8))).range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, ← commutator_def, alt8_commutator]
  rw [h3] at h2
  obtain ⟨y, hy, hyc⟩ := h2 ⟨c, rfl⟩
  exact ⟨y, hy, hyc⟩

theorem commutator_firstSub_perfect (hf : Function.Surjective f) (hker : f.ker ≤ center Q) :
    ⁅⁅firstSub f, firstSub f⁆, ⁅firstSub f, firstSub f⁆⁆ = ⁅firstSub f, firstSub f⁆ := by
  refine le_antisymm (commutator_le_self _) ?_
  rw [commutator_le]
  intro a ha b hb
  have hdec : ∀ x ∈ firstSub f, ∃ y ∈ ⁅firstSub f, firstSub f⁆, ∃ k ∈ center Q, x = y * k := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := exists_mem_commutator_firstSub hf (f x).1
    have hfx : f x = ((f x).1, 1) := Prod.ext rfl (mem_firstSub.1 hx)
    refine ⟨y, hy, y⁻¹ * x, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, ← hfx]
    group
  obtain ⟨y, hy, k, hk, rfl⟩ := hdec a ha
  obtain ⟨y', hy', k', hk', rfl⟩ := hdec b hb
  rw [commutatorElement_mul_central' hk hk']
  exact commutator_mem_commutator hy hy'

theorem eq_one_of_mem_commutator_firstSub (hf : Function.Surjective f) (hker : f.ker ≤ center Q)
    (hodd : Odd (Nat.card f.ker)) {x : Q} (hx : x ∈ ⁅firstSub f, firstSub f⁆) (hfx : f x = 1) :
    x = 1 := by
  set K1 := ⁅firstSub f, firstSub f⁆ with hK1
  have hperf : commutator K1 = ⊤ := by
    have : Group.IsPerfect K1 := Subgroup.isPerfect_iff.2 (commutator_firstSub_perfect hf hker)
    exact Group.IsPerfect.commutator_eq_top
  let π1 : K1 →* alternatingGroup (Fin 8) :=
    (MonoidHom.fst _ _).comp (f.comp K1.subtype)
  have hπs : Function.Surjective π1 := by
    intro c
    obtain ⟨y, hy, hyc⟩ := exists_mem_commutator_firstSub hf c
    exact ⟨⟨y, hy⟩, by simp [π1, hyc]⟩
  have hK1T : K1 ≤ firstSub f := commutator_le_right _ _
  have hπk : π1.ker ≤ center K1 := by
    intro y hy
    have h1 : (f y).1 = 1 := hy
    have h2 : (f y).2 = 1 := mem_firstSub.1 (hK1T y.2)
    have hy1 : f (y : Q) = 1 := Prod.ext h1 h2
    have hyc : (y : Q) ∈ center Q := hker hy1
    exact Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_center_iff.1 hyc g.1)
  have h2 := card_ker_dvd_two_alt8 hperf hπs hπk
  have hle : π1.ker.map K1.subtype ≤ f.ker := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : (f y).1 = 1 := hy
    have h2 : (f y).2 = 1 := mem_firstSub.1 (hK1T y.2)
    exact Prod.ext h1 h2
  have h3 : Nat.card π1.ker ∣ Nat.card f.ker := by
    have := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective K1.subtype_injective] at this
  have h4 : Nat.card π1.ker = 1 := by
    have hodd' : Odd (Nat.card π1.ker) := Odd.of_dvd_nat hodd h3
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact h
    · rw [h] at hodd'
      exact absurd hodd' (by decide)
  have h5 : π1.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ h4
  have hxk : (⟨x, hx⟩ : K1) ∈ π1.ker := by
    show (f x).1 = 1
    rw [hfx]; rfl
  rw [h5] at hxk
  exact congrArg Subtype.val (Subgroup.mem_bot.1 hxk)

theorem ker_eq_bot_of_perfect_central_alt8_prod (hQ : commutator Q = ⊤)
    (f : Q →* alternatingGroup (Fin 8) × alternatingGroup (Fin 8)) (hf : Function.Surjective f)
    (hker : f.ker ≤ center Q) (hodd : Odd (Nat.card f.ker)) : f.ker = ⊥ := by
  let f' : Q →* alternatingGroup (Fin 8) × alternatingGroup (Fin 8) :=
    (MulEquiv.prodComm (M := alternatingGroup (Fin 8))
      (N := alternatingGroup (Fin 8))).toMonoidHom.comp f
  have hf'val : ∀ x, f' x = ((f x).2, (f x).1) := fun x => rfl
  have hf's : Function.Surjective f' := by
    intro p
    obtain ⟨x, hx⟩ := hf (p.2, p.1)
    exact ⟨x, by rw [hf'val, hx]⟩
  have hker' : f'.ker = f.ker := by
    ext x
    simp only [MonoidHom.mem_ker, hf'val]
    constructor
    · intro h
      exact Prod.ext (Prod.ext_iff.1 h).2 (Prod.ext_iff.1 h).1
    · intro h
      rw [h]
      exact Prod.ext rfl rfl
  have hker'c : f'.ker ≤ center Q := hker' ▸ hker
  have hodd' : Odd (Nat.card f'.ker) := hker' ▸ hodd
  set K1 := ⁅firstSub f, firstSub f⁆ with hK1
  set K2 := ⁅firstSub f', firstSub f'⁆ with hK2
  have hK1T : K1 ≤ firstSub f := commutator_le_right _ _
  have hK2T : K2 ≤ firstSub f' := commutator_le_right _ _
  have hK2N : K2.Normal := inferInstance
  have hclaimA : ∀ x : Q, ∃ q ∈ K1 ⊔ K2, ∃ k ∈ f.ker, x = q * k := by
    intro x
    obtain ⟨a, ha, hfa⟩ := exists_mem_commutator_firstSub hf (f x).1
    obtain ⟨b, hb, hfb⟩ := exists_mem_commutator_firstSub hf's (f x).2
    refine ⟨a * b, mul_mem_sup ha hb, (a * b)⁻¹ * x, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul]
    have hfb' : f b = (1, (f x).2) := by
      have := hfb
      rw [hf'val] at this
      exact Prod.ext (Prod.ext_iff.1 this).2 (Prod.ext_iff.1 this).1
    rw [hfa, hfb']
    have : ((f x).1, (1 : alternatingGroup (Fin 8))) * (1, (f x).2) = f x := by
      ext <;> simp
    rw [this]
    group
  have htop : K1 ⊔ K2 = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← hQ, commutator_def, commutator_le]
    intro x _ y _
    obtain ⟨q, hq, k, hk, rfl⟩ := hclaimA x
    obtain ⟨q', hq', k', hk', rfl⟩ := hclaimA y
    rw [commutatorElement_mul_central' (hker hk) (hker hk')]
    simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hq hq') (inv_mem hq)) (inv_mem hq')
  refine eq_bot_iff.2 fun k hk => ?_
  have hkq : k ∈ K1 ⊔ K2 := by rw [htop]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.1 hkq
  have hfk : f k = 1 := hk
  have hfa : f a = ((f a).1, 1) := Prod.ext rfl (mem_firstSub.1 (hK1T ha))
  have hfb : f b = (1, (f b).2) := by
    have h2 : (f' b).2 = 1 := mem_firstSub.1 (hK2T hb)
    rw [hf'val] at h2
    exact Prod.ext h2 rfl
  have hprod : f a * f b = 1 := by rw [← map_mul, hab, hfk]
  rw [hfa, hfb] at hprod
  have h1 : (f a).1 = 1 := by simpa using (Prod.ext_iff.1 hprod).1
  have h2 : (f b).2 = 1 := by simpa using (Prod.ext_iff.1 hprod).2
  have ha1 : a = 1 := eq_one_of_mem_commutator_firstSub hf hker hodd ha (by rw [hfa, h1]; rfl)
  have hb1 : b = 1 :=
    eq_one_of_mem_commutator_firstSub hf's hker'c hodd' hb (by
      rw [hf'val, hfb, h2]; rfl)
  rw [← hab, ha1, hb1, mul_one]
  exact one_mem _

end SchurProd

theorem card_alt8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

end CFSG.EvenSporadicStandard.M24Std.DRes
