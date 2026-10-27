module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSA6

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup
open scoped commutatorElement

section SchurProd6

variable {Q : Type} [Group Q]

@[expose] def firstSub6 (f : Q →* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) :
    Subgroup Q :=
  ((MonoidHom.snd _ _).comp f).ker

@[expose] def secondSub6 (f : Q →* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) :
    Subgroup Q :=
  ((MonoidHom.fst _ _).comp f).ker

theorem mem_firstSub6 {f : Q →* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)} {x : Q} :
    x ∈ firstSub6 f ↔ (f x).2 = 1 := by
  simp [firstSub6, MonoidHom.mem_ker]

theorem mem_secondSub6 {f : Q →* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)} {x : Q} :
    x ∈ secondSub6 f ↔ (f x).1 = 1 := by
  simp [secondSub6, MonoidHom.mem_ker]

instance firstSub6_normal (f : Q →* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) :
    (firstSub6 f).Normal := MonoidHom.normal_ker _

instance secondSub6_normal (f : Q →* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) :
    (secondSub6 f).Normal := MonoidHom.normal_ker _

theorem commutatorElement_mul_central6 {y y' k k' : Q} (hk : k ∈ center Q) (hk' : k' ∈ center Q) :
    ⁅y * k, y' * k'⁆ = ⁅y, y'⁆ := by
  have hc : ∀ g : Q, Commute k g := fun g => (Subgroup.mem_center_iff.1 hk g).symm
  have hc' : ∀ g : Q, Commute k' g := fun g => (Subgroup.mem_center_iff.1 hk' g).symm
  rw [commutatorElement_mul_left_eq_conj_mul, (hc _).commutator_eq, mul_one, mul_inv_cancel,
    one_mul, commutatorElement_mul_right_eq_mul_conj, ((hc' _).symm).commutator_eq, mul_one,
    mul_inv_cancel_right]

variable {f : Q →* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)}

theorem exists_mem_commutator_firstSub6 (hf : Function.Surjective f)
    (c : alternatingGroup (Fin 6)) :
    ∃ y ∈ ⁅firstSub6 f, firstSub6 f⁆, f y = (c, 1) := by
  have h1 : (MonoidHom.inl (alternatingGroup (Fin 6)) (alternatingGroup (Fin 6))).range ≤
      (firstSub6 f).map f := by
    rintro _ ⟨c', rfl⟩
    obtain ⟨x, hx⟩ := hf (c', 1)
    exact ⟨x, mem_firstSub6.2 (by rw [hx]), hx⟩
  have h2 := commutator_le_map_commutator h1 h1
  have h3 : ⁅(MonoidHom.inl (alternatingGroup (Fin 6)) (alternatingGroup (Fin 6))).range,
      (MonoidHom.inl (alternatingGroup (Fin 6)) (alternatingGroup (Fin 6))).range⁆ =
      (MonoidHom.inl (alternatingGroup (Fin 6)) (alternatingGroup (Fin 6))).range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, ← commutator_def, alt6_commutator]
  rw [h3] at h2
  obtain ⟨y, hy, hyc⟩ := h2 ⟨c, rfl⟩
  exact ⟨y, hy, hyc⟩

theorem commutator_firstSub_perfect6 (hf : Function.Surjective f) (hker : f.ker ≤ center Q) :
    ⁅⁅firstSub6 f, firstSub6 f⁆, ⁅firstSub6 f, firstSub6 f⁆⁆ = ⁅firstSub6 f, firstSub6 f⁆ := by
  refine le_antisymm (commutator_le_self _) ?_
  rw [commutator_le]
  intro a ha b hb
  have hdec : ∀ x ∈ firstSub6 f, ∃ y ∈ ⁅firstSub6 f, firstSub6 f⁆, ∃ k ∈ center Q, x = y * k := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := exists_mem_commutator_firstSub6 hf (f x).1
    have hfx : f x = ((f x).1, 1) := Prod.ext rfl (mem_firstSub6.1 hx)
    refine ⟨y, hy, y⁻¹ * x, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, ← hfx]
    group
  obtain ⟨y, hy, k, hk, rfl⟩ := hdec a ha
  obtain ⟨y', hy', k', hk', rfl⟩ := hdec b hb
  rw [commutatorElement_mul_central6 hk hk']
  exact commutator_mem_commutator hy hy'

theorem card_inf_ker_dvd_three6 (hf : Function.Surjective f)
    (hker : f.ker ≤ center Q) (hodd : Odd (Nat.card f.ker)) :
    Nat.card (⁅firstSub6 f, firstSub6 f⁆ ⊓ f.ker : Subgroup Q) ∣ 3 := by
  set K1 := ⁅firstSub6 f, firstSub6 f⁆ with hK1
  have hperf : commutator K1 = ⊤ := by
    have : Group.IsPerfect K1 := Subgroup.isPerfect_iff.2 (commutator_firstSub_perfect6 hf hker)
    exact Group.IsPerfect.commutator_eq_top
  let π1 : K1 →* alternatingGroup (Fin 6) := (MonoidHom.fst _ _).comp (f.comp K1.subtype)
  have hπs : Function.Surjective π1 := by
    intro c
    obtain ⟨y, hy, hyc⟩ := exists_mem_commutator_firstSub6 hf c
    exact ⟨⟨y, hy⟩, by simp [π1, hyc]⟩
  have hK1T : K1 ≤ firstSub6 f := commutator_le_right _ _
  have hπk : π1.ker ≤ center K1 := by
    intro y hy
    have h1 : (f y).1 = 1 := hy
    have h2 : (f y).2 = 1 := mem_firstSub6.1 (hK1T y.2)
    have hy1 : f (y : Q) = 1 := Prod.ext h1 h2
    have hyc : (y : Q) ∈ center Q := hker hy1
    exact Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_center_iff.1 hyc g.1)
  have h6 := card_ker_dvd_six_alt6 hperf hπs hπk
  have hle : π1.ker.map K1.subtype = K1 ⊓ f.ker := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h1 : (f y).1 = 1 := hy
      have h2 : (f y).2 = 1 := mem_firstSub6.1 (hK1T y.2)
      exact ⟨y.2, Prod.ext h1 h2⟩
    · rintro ⟨hx1, hx2⟩
      refine ⟨⟨x, hx1⟩, ?_, rfl⟩
      show (f x).1 = 1
      rw [MonoidHom.mem_ker.1 hx2]
      rfl
  have hcard : Nat.card (K1 ⊓ f.ker : Subgroup Q) = Nat.card π1.ker := by
    rw [← hle, Subgroup.card_map_of_injective K1.subtype_injective]
  rw [hcard]
  have hodd' : Odd (Nat.card π1.ker) := by
    refine Odd.of_dvd_nat hodd ?_
    rw [← hcard]
    exact Subgroup.card_dvd_of_le inf_le_right
  have h2' : ¬ 2 ∣ Nat.card π1.ker := fun hd =>
    (Nat.not_even_iff_odd.2 hodd') (even_iff_two_dvd.2 hd)
  have hcop : Nat.Coprime (Nat.card π1.ker) 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2').symm
  have h2 : Nat.card π1.ker ∣ 2 * 3 := h6
  exact hcop.dvd_of_dvd_mul_left h2

@[expose] def swapHom6 (f : Q →* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) :
    Q →* alternatingGroup (Fin 6) × alternatingGroup (Fin 6) :=
  (MulEquiv.prodComm (M := alternatingGroup (Fin 6)) (N := alternatingGroup (Fin 6))).toMonoidHom.comp
    f

theorem swapHom6_apply (x : Q) : swapHom6 f x = ((f x).2, (f x).1) := rfl

theorem swapHom6_surjective (hf : Function.Surjective f) : Function.Surjective (swapHom6 f) := by
  intro p
  obtain ⟨x, hx⟩ := hf (p.2, p.1)
  exact ⟨x, by rw [swapHom6_apply, hx]⟩

theorem swapHom6_ker : (swapHom6 f).ker = f.ker := by
  ext x
  simp only [MonoidHom.mem_ker, swapHom6_apply]
  constructor
  · intro h
    exact Prod.ext (Prod.ext_iff.1 h).2 (Prod.ext_iff.1 h).1
  · intro h
    rw [h]
    exact Prod.ext rfl rfl

theorem firstSub6_swap : firstSub6 (swapHom6 f) = secondSub6 f := by
  ext x
  rw [mem_firstSub6, mem_secondSub6, swapHom6_apply]

@[expose] def schurS1 (f : Q →* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) : Subgroup Q :=
  ⁅firstSub6 f, firstSub6 f⁆

@[expose] def schurS2 (f : Q →* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) : Subgroup Q :=
  ⁅secondSub6 f, secondSub6 f⁆

theorem schurS2_eq : schurS2 f = ⁅firstSub6 (swapHom6 f), firstSub6 (swapHom6 f)⁆ := by
  rw [firstSub6_swap]
  rfl

instance schurS1_normal : (schurS1 f).Normal := by unfold schurS1; infer_instance

instance schurS2_normal : (schurS2 f).Normal := by unfold schurS2; infer_instance

theorem schurS1_le : schurS1 f ≤ firstSub6 f := commutator_le_right _ _

theorem schurS2_le : schurS2 f ≤ secondSub6 f := commutator_le_right _ _

theorem schurS1_perfect (hf : Function.Surjective f) (hker : f.ker ≤ center Q) :
    ⁅schurS1 f, schurS1 f⁆ = schurS1 f := commutator_firstSub_perfect6 hf hker

theorem schurS2_perfect (hf : Function.Surjective f) (hker : f.ker ≤ center Q) :
    ⁅schurS2 f, schurS2 f⁆ = schurS2 f := by
  rw [schurS2_eq]
  exact commutator_firstSub_perfect6 (swapHom6_surjective hf) (swapHom6_ker (f := f) ▸ hker)

theorem exists_mem_schurS1 (hf : Function.Surjective f) (c : alternatingGroup (Fin 6)) :
    ∃ y ∈ schurS1 f, f y = (c, 1) := exists_mem_commutator_firstSub6 hf c

theorem exists_mem_schurS2 (hf : Function.Surjective f) (c : alternatingGroup (Fin 6)) :
    ∃ y ∈ schurS2 f, f y = (1, c) := by
  rw [schurS2_eq]
  obtain ⟨y, hy, hyc⟩ := exists_mem_commutator_firstSub6 (swapHom6_surjective hf) c
  exact ⟨y, hy, by
    rw [swapHom6_apply] at hyc
    exact Prod.ext (Prod.ext_iff.1 hyc).2 (Prod.ext_iff.1 hyc).1⟩

theorem card_inf_ker_schurS1 (hf : Function.Surjective f)
    (hker : f.ker ≤ center Q) (hodd : Odd (Nat.card f.ker)) :
    Nat.card (schurS1 f ⊓ f.ker : Subgroup Q) ∣ 3 := card_inf_ker_dvd_three6 hf hker hodd

theorem card_inf_ker_schurS2 (hf : Function.Surjective f)
    (hker : f.ker ≤ center Q) (hodd : Odd (Nat.card f.ker)) :
    Nat.card (schurS2 f ⊓ f.ker : Subgroup Q) ∣ 3 := by
  rw [schurS2_eq]
  have h := card_inf_ker_dvd_three6 (swapHom6_surjective hf) (swapHom6_ker (f := f) ▸ hker)
    (swapHom6_ker (f := f) ▸ hodd)
  rwa [swapHom6_ker] at h

theorem commute_schur (hf : Function.Surjective f) (hker : f.ker ≤ center Q) :
    ∀ a ∈ schurS1 f, ∀ b ∈ schurS2 f, a * b = b * a := by
  intro a ha b hb
  have hcent : ∀ b ∈ schurS2 f, ⁅a, b⁆ ∈ center Q := by
    intro b hb
    apply hker
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_inv, map_inv]
    have h1 : (f a).2 = 1 := mem_firstSub6.1 (schurS1_le ha)
    have h2 : (f b).1 = 1 := mem_secondSub6.1 (schurS2_le hb)
    refine Prod.ext ?_ ?_
    · simp [h2]
    · simp [h1]
  have hle : schurS2 f ≤ centralizer ({a} : Set Q) := by
    rw [← schurS2_perfect hf hker]
    refine commutator_le.2 fun b1 hb1 b2 hb2 => ?_
    rw [mem_centralizer_singleton_iff]
    have hc1 := hcent b1 (schurS2_perfect hf hker ▸ hb1)
    have hc2 := hcent b2 (schurS2_perfect hf hker ▸ hb2)
    have e1 : a * b1 * a⁻¹ = b1 * ⁅a, b1⁆ := by
      have := Subgroup.mem_center_iff.1 hc1 b1
      calc a * b1 * a⁻¹ = (a * b1 * a⁻¹ * b1⁻¹) * b1 := by group
        _ = ⁅a, b1⁆ * b1 := rfl
        _ = b1 * ⁅a, b1⁆ := this.symm
    have e2 : a * b2 * a⁻¹ = b2 * ⁅a, b2⁆ := by
      have := Subgroup.mem_center_iff.1 hc2 b2
      calc a * b2 * a⁻¹ = (a * b2 * a⁻¹ * b2⁻¹) * b2 := by group
        _ = ⁅a, b2⁆ * b2 := rfl
        _ = b2 * ⁅a, b2⁆ := this.symm
    have key : a * ⁅b1, b2⁆ * a⁻¹ = ⁅b1, b2⁆ := by
      have e3 : a * ⁅b1, b2⁆ * a⁻¹ = ⁅a * b1 * a⁻¹, a * b2 * a⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e3, e1, e2]
      exact commutatorElement_mul_central6 hc1 hc2
    calc ⁅b1, b2⁆ * a = a * ⁅b1, b2⁆ * a⁻¹ * a := by rw [key]
      _ = a * ⁅b1, b2⁆ := by group
  have := hle hb
  rw [mem_centralizer_singleton_iff] at this
  exact this.symm

theorem sup_schur (hQ : commutator Q = ⊤) (hf : Function.Surjective f)
    (hker : f.ker ≤ center Q) : schurS1 f ⊔ schurS2 f = ⊤ := by
  have hclaimA : ∀ x : Q, ∃ q ∈ schurS1 f ⊔ schurS2 f, ∃ k ∈ f.ker, x = q * k := by
    intro x
    obtain ⟨a, ha, hfa⟩ := exists_mem_schurS1 hf (f x).1
    obtain ⟨b, hb, hfb⟩ := exists_mem_schurS2 hf (f x).2
    refine ⟨a * b, mul_mem_sup ha hb, (a * b)⁻¹ * x, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, hfa, hfb]
    have : ((f x).1, (1 : alternatingGroup (Fin 6))) * (1, (f x).2) = f x := by
      ext <;> simp
    rw [this]
    group
  refine top_le_iff.1 ?_
  rw [← hQ, commutator_def, commutator_le]
  intro x _ y _
  obtain ⟨q, hq, k, hk, rfl⟩ := hclaimA x
  obtain ⟨q', hq', k', hk', rfl⟩ := hclaimA y
  rw [commutatorElement_mul_central6 (hker hk) (hker hk')]
  simp only [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hq hq') (inv_mem hq)) (inv_mem hq')

theorem ker_eq_mul (hQ : commutator Q = ⊤) (hf : Function.Surjective f)
    (hker : f.ker ≤ center Q) {k : Q} (hk : k ∈ f.ker) :
    ∃ a ∈ schurS1 f ⊓ f.ker, ∃ b ∈ schurS2 f ⊓ f.ker, k = a * b := by
  have hkq : k ∈ schurS1 f ⊔ schurS2 f := by rw [sup_schur hQ hf hker]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.1 hkq
  have hfk : f k = 1 := hk
  have hfa : f a = ((f a).1, 1) := Prod.ext rfl (mem_firstSub6.1 (schurS1_le ha))
  have hfb : f b = (1, (f b).2) := Prod.ext (mem_secondSub6.1 (schurS2_le hb)) rfl
  have hprod : f a * f b = 1 := by rw [← map_mul, hab, hfk]
  rw [hfa, hfb] at hprod
  have h1 : (f a).1 = 1 := by simpa using (Prod.ext_iff.1 hprod).1
  have h2 : (f b).2 = 1 := by simpa using (Prod.ext_iff.1 hprod).2
  have hak : a ∈ f.ker := by rw [MonoidHom.mem_ker, hfa, h1]; rfl
  have hbk : b ∈ f.ker := by rw [MonoidHom.mem_ker, hfb, h2]; rfl
  exact ⟨a, ⟨ha, hak⟩, b, ⟨hb, hbk⟩, hab.symm⟩

end SchurProd6

end CFSG.EvenSporadicStandard.M24Std.DRes
