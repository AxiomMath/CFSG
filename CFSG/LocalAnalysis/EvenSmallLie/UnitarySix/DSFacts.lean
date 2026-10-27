module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.DSFactsLift
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.DSFactsT46
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.WeakClosure
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.CoverAction

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.UnitarySix

open Subgroup CFSG.Quasithin
open CFSG.ComponentClassification.M12Cover.CyclicKernel (exists_mul_of_mem_sup_of_commute)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem card_le_two_mul_card_inf {F H B : Subgroup G} (hBH : B ≤ H) (hF : F.relIndex H ≤ 2) :
    Nat.card B ≤ 2 * Nat.card (F ⊓ B : Subgroup G) := by
  have h1 : Nat.card B = Nat.card (F ⊓ B : Subgroup G) * F.relIndex B := by
    rw [← relIndex_bot_left, ← relIndex_bot_left, ← inf_relIndex_right F B,
      relIndex_mul_relIndex _ _ _ bot_le inf_le_right]
  have h2 : F.relIndex B ≤ 2 :=
    (relIndex_le_of_le_right hBH (relIndex_ne_zero_of_finite _ _)).trans hF
  rw [h1, mul_comm]
  exact Nat.mul_le_mul_right _ h2

theorem card_eq_card_ker_mul_card_range {X Y : Type*} [Group X] [Group Y] [Finite X] (ψ : X →* Y) :
    Nat.card X = Nat.card ψ.ker * Nat.card ψ.range := by
  rw [← Subgroup.index_ker, Subgroup.card_mul_index]

theorem card_le_of_theta {Q : Type} [Group Q] (hQ : CFSG.Blueprint.LieModel Q .PSU 6 2 1)
    (hconj : Function.Injective (MulAut.conj : Q →* MulAut Q)) {H C : Subgroup G}
    (θ : H →* MulAut Q) (hθ1 : ∀ h : H, θ h = 1 ↔ (h : G) ∈ C)
    (hC2 : ∀ X : Subgroup G, X ≤ C → (∀ x ∈ X, x ^ 2 = 1) → Nat.card X ≤ 2) {τ : H}
    (hα : θ τ * θ τ = 1) (hout : ∀ q, θ τ ≠ MulAut.conj q) {B : Subgroup G} (hBH : B ≤ H)
    (hBτ : ∀ b ∈ B, b * τ = τ * b) (hsq : ∀ b ∈ B, b ^ 2 = 1)
    (hinner : ∀ b (hb : b ∈ B), ∃ q, θ ⟨b, hBH hb⟩ = MulAut.conj q) :
    Nat.card B ≤ 2 * 2 ^ 6 := by
  set ψ : B →* MulAut Q := θ.comp (Subgroup.inclusion hBH)
  have hψ : ∀ b : B, ψ b = θ ⟨b, hBH b.2⟩ := fun b => rfl
  rw [card_eq_card_ker_mul_card_range ψ]
  refine Nat.mul_le_mul ?_ ?_
  · have h := hC2 (ψ.ker.map B.subtype) (by
      rintro _ ⟨b, hb, rfl⟩
      exact (hθ1 _).1 hb) (by
      rintro _ ⟨b, -, rfl⟩
      exact hsq _ b.2)
    rwa [Subgroup.card_map_of_injective B.subtype_injective] at h
  · set B'' := ψ.range.comap (MulAut.conj : Q →* MulAut Q)
    have hle : ψ.range ≤ (MulAut.conj : Q →* MulAut Q).range := by
      rintro _ ⟨b, rfl⟩
      obtain ⟨q, hq⟩ := hinner b b.2
      exact ⟨q, by rw [hψ, hq]⟩
    have hcard : Nat.card ψ.range = Nat.card B'' := by
      rw [← Subgroup.card_map_of_injective hconj, Subgroup.map_comap_eq_self hle]
    rw [hcard]
    refine card_le_of_fixed hQ hα hout (fun q hq => hconj ?_) (fun q hq => hconj ?_)
    · obtain ⟨b, hb⟩ := hq
      rw [← mulAut_mul_conj_mul_inv, ← hb, hψ]
      have hbt : (τ : H) * ⟨b, hBH b.2⟩ * τ⁻¹ = ⟨b, hBH b.2⟩ := by
        refine Subtype.ext ?_
        simp only [coe_mul, coe_inv]
        rw [← hBτ _ b.2, mul_inv_cancel_right]
      rw [← map_inv, ← map_mul, ← map_mul, hbt]
    · obtain ⟨b, hb⟩ := hq
      rw [map_pow, ← hb, hψ, ← map_pow, map_one]
      have : (⟨b, hBH b.2⟩ : H) ^ 2 = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow]
        exact hsq _ b.2)
      rw [this, map_one]

section Standard

variable {t : G}

theorem std_card_le_two (hset : StandardSetting G L) (ht : orderOf t = 2)
    (htZ : t ∈ (center L).map L.subtype) {X : Subgroup G} (hX : X ≤ centralizer (L : Set G))
    (hsq : ∀ x ∈ X, x ^ 2 = 1) : Nat.card X ≤ 2 := by
  obtain ⟨-, -, -, huniq, -, -, -⟩ := std_center_facts hset ht htZ
  have hle : X ≤ zpowers t := fun x hx => by
    by_cases h1 : x = 1
    · rw [h1]
      exact one_mem _
    · rw [huniq x (hX hx) (orderOf_eq_prime (hsq x hx) h1)]
      exact mem_zpowers t
  calc Nat.card X ≤ Nat.card (zpowers t) := card_le_of_le hle
    _ = 2 := by rw [Nat.card_zpowers, ht]

theorem std_outer
    (hset : StandardSetting G L) (ht : orderOf t = 2)
    (htZ : t ∈ (center L).map L.subtype) (h2 : Nat.card (center L) = 2)
    (hQ : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1) :
    (L ⊔ centralizer (L : Set G)).relIndex (centralizer {t}) ≤ 2 := by
  obtain ⟨-, -, -, -, hN, hLt, hCt⟩ := std_center_facts hset ht htZ
  have : Group.IsPerfect L := Group.isPerfect_def.2 hset.standard.1.1
  have h := (relIndex_sup_inf_centralizer_le_two hLt hN.le h2 hQ).1
  rwa [inf_of_le_right hCt] at h

theorem std_rank
    (hset : StandardSetting G L) (ht : orderOf t = 2)
    (htZ : t ∈ (center L).map L.subtype) (h2 : Nat.card (center L) = 2)
    (hQ : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1) :
    ∀ τ ∈ centralizer {t}, orderOf τ = 2 → τ ∉ L ⊔ centralizer (L : Set G) →
      ∀ B : Subgroup G, B ≤ centralizer {t} ⊓ centralizer {τ} → (∀ b ∈ B, b ^ 2 = 1) →
        Nat.card B ≤ 2 ^ 8 := by
  intro τ hτ hτ2 hτF B hB hBsq
  obtain ⟨θ, -, hθ1, hinn⟩ := std_automizer_embedding hset ht htZ
  obtain ⟨D⟩ := nonempty_toddParabolic hQ
  have hBF := card_le_two_mul_card_inf (hB.trans inf_le_left) (std_outer hset ht htZ h2 hQ)
  have hτ' : θ ⟨τ, hτ⟩ * θ ⟨τ, hτ⟩ = 1 := by
    rw [← map_mul]
    have : (⟨τ, hτ⟩ : centralizer {t}) * ⟨τ, hτ⟩ = 1 := Subtype.ext (by
      simp only [coe_mul, coe_one]
      rw [← sq, ← hτ2, pow_orderOf_eq_one])
    rw [this, map_one]
  have h7 := card_le_of_theta hQ D.conj_injective θ hθ1
    (fun X hX hXsq => std_card_le_two hset ht htZ hX hXsq) hτ'
    (fun q hq => hτF ((hinn _).1 ⟨q, hq⟩)) (B := (L ⊔ centralizer (L : Set G)) ⊓ B)
    (inf_le_right.trans (hB.trans inf_le_left))
    (fun b hb => mem_centralizer_singleton_iff.1 ((hB hb.2).2))
    (fun b hb => hBsq b hb.2) (fun b hb => (hinn _).2 hb.1)
  calc Nat.card B ≤ 2 * Nat.card ((L ⊔ centralizer (L : Set G)) ⊓ B : Subgroup G) := hBF
    _ ≤ 2 * (2 * 2 ^ 6) := Nat.mul_le_mul_left _ h7
    _ = 2 ^ 8 := by norm_num

omit [Finite G] in
theorem isDoubleCover_mk (h2 : Nat.card (center L) = 2) (ht : orderOf t = 2)
    (htZ : t ∈ (center L).map L.subtype) (hLt : L ≤ centralizer {t}) :
    IsDoubleCover t L (QuotientGroup.mk' (center L)) := by
  obtain ⟨z, hzZ, rfl⟩ := htZ
  refine ⟨QuotientGroup.mk'_surjective _, fun y => ?_, z.2, hLt, ht⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨w, hw1, hwu⟩ := (Nat.card_eq_two_iff' (1 : center L)).1 h2
  have hz1 : (⟨z, hzZ⟩ : center L) ≠ 1 := fun h => by
    have : (z : G) = 1 := congrArg (fun u : center L => ((u : L) : G)) h
    rw [coe_subtype, this, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hzw := hwu _ hz1
  constructor
  · intro hy
    by_cases hy1 : (⟨y, hy⟩ : center L) = 1
    · exact Or.inl (congrArg (fun u : center L => ((u : L) : G)) hy1)
    · exact Or.inr (congrArg (fun u : center L => ((u : L) : G)) ((hwu _ hy1).trans hzw.symm))
  · rintro (h | h)
    · rw [show y = 1 from Subtype.ext h]
      exact (center L).one_mem
    · rw [show y = z from Subtype.ext h]
      exact hzZ

theorem std_centralizer_toddLift_le
    (hset : StandardSetting G L) (ht : orderOf t = 2)
    (htZ : t ∈ (center L).map L.subtype) (h2 : Nat.card (center L) = 2)
    (hQ : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1) {Q' : Type} [Group Q']
    {π : L →* Q'} (H : IsDoubleCover t L π) (D : ToddParabolic Q')
    (hE2 : ∀ e ∈ liftSub π D.A, e ^ 2 = 1) :
    centralizer (liftSub π D.A : Set G) ≤ liftSub π D.A ⊔ centralizer (L : Set G) := by
  set E := liftSub π D.A
  set F := L ⊔ centralizer (L : Set G)
  obtain ⟨-, -, -, -, hN, hLt, -⟩ := std_center_facts hset ht htZ
  have hEL : E ≤ L := liftSub_le π D.A
  have hcommL : ∀ l ∈ L, ∀ c ∈ centralizer (L : Set G), l * c = c * l :=
    fun l hl c hc => mem_centralizer_iff.1 hc l hl
  have stepA : ∀ y ∈ centralizer (E : Set G), y ∈ F → y ∈ E ⊔ centralizer (L : Set G) := by
    intro y hy hyF
    obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_commute hcommL hyF
    refine mul_mem_sup (H.mem_toddLift_of_commute D hl fun e he => ?_) hc
    have h1 := mem_centralizer_iff.1 hy e he
    have h2 := hcommL e (hEL he) c hc
    have h3 : e * l * c = l * e * c := by
      calc e * l * c = e * (l * c) := by group
        _ = l * c * e := h1
        _ = l * (c * e) := by group
        _ = l * (e * c) := by rw [h2]
        _ = l * e * c := by group
    exact (mul_right_cancel h3).symm
  intro x hx
  have hxt : x ∈ centralizer {t} :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hx t (H.t_mem_liftSub D.A)).symm
  by_cases hxF : x ∈ F
  · exact stepA x hx hxF
  exfalso
  have hrel : F.relIndex (centralizer {t}) = 2 := by
    have h1 : F.relIndex (centralizer {t}) ≤ 2 := std_outer hset ht htZ h2 hQ
    have h0 : F.relIndex (centralizer {t}) ≠ 0 := relIndex_ne_zero_of_finite _ _
    have h1' : F.relIndex (centralizer {t}) ≠ 1 := fun h => hxF (relIndex_eq_one.1 h hxt)
    omega
  have hx2F : x * x ∈ F := SolomonWong.mul_self_mem_of_relIndex_two hrel hxt
  obtain ⟨e₀, he₀, c₀, hc₀, hx2⟩ := exists_mul_of_mem_sup_of_commute
    (fun e he c hc => hcommL e (hEL he) c hc) (stepA _ (mul_mem hx hx) hx2F)
  have hxN : x ∈ normalizer (L : Set G) := hN ▸ hxt
  have hcomm : ∀ l ∈ normalizer (E : Set G) ⊓ L, l * e₀ = e₀ * l := by
    intro l hl
    have hdL : l * x * l⁻¹ * x⁻¹ ∈ L := by
      rw [show l * x * l⁻¹ * x⁻¹ = l * (x * l⁻¹ * x⁻¹) by group]
      exact L.mul_mem hl.2 ((mem_normalizer_iff.1 hxN _).1 (L.inv_mem hl.2))
    have hdE : l * x * l⁻¹ * x⁻¹ ∈ E := H.mem_toddLift_of_commute D hdL fun e he => by
      have h1 : l⁻¹ * e * l ∈ E := (mem_normalizer_iff''.1 hl.1 e).1 he
      have h2 : x * (l⁻¹ * e * l) = (l⁻¹ * e * l) * x := (mem_centralizer_iff.1 hx _ h1).symm
      have hxe' : x⁻¹ * e = e * x⁻¹ := by
        have := mem_centralizer_iff.1 hx e he
        calc x⁻¹ * e = x⁻¹ * (e * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * e) * x⁻¹ := by rw [this]
          _ = e * x⁻¹ := by group
      calc l * x * l⁻¹ * x⁻¹ * e = l * x * l⁻¹ * (x⁻¹ * e) := by group
        _ = l * x * l⁻¹ * (e * x⁻¹) := by rw [hxe']
        _ = l * (x * (l⁻¹ * e * l)) * l⁻¹ * x⁻¹ := by group
        _ = l * ((l⁻¹ * e * l) * x) * l⁻¹ * x⁻¹ := by rw [h2]
        _ = e * (l * x * l⁻¹ * x⁻¹) := by group
    set d := l * x * l⁻¹ * x⁻¹
    have hd2 : d * d = 1 := by rw [← sq]; exact hE2 d hdE
    have hxd : x * d = d * x := (mem_centralizer_iff.1 hx d hdE).symm
    have hlx : l * x * l⁻¹ = d * x := by simp only [d]; group
    have key : l * (x * x) * l⁻¹ = x * x := by
      calc l * (x * x) * l⁻¹ = (l * x * l⁻¹) * (l * x * l⁻¹) := by group
        _ = d * x * (d * x) := by rw [hlx]
        _ = d * (x * d) * x := by group
        _ = d * (d * x) * x := by rw [hxd]
        _ = (d * d) * (x * x) := by group
        _ = x * x := by rw [hd2, one_mul]
    rw [hx2] at key
    have hlc : l * c₀ = c₀ * l := hcommL l hl.2 c₀ hc₀
    have h3 : l * e₀ * l⁻¹ * c₀ = e₀ * c₀ := by
      calc l * e₀ * l⁻¹ * c₀ = l * e₀ * (l⁻¹ * c₀ * l) * l⁻¹ := by group
        _ = l * e₀ * c₀ * l⁻¹ := by
            rw [show l⁻¹ * c₀ * l = c₀ by rw [mul_assoc, ← hlc, inv_mul_cancel_left]]
        _ = e₀ * c₀ := by rw [← key]; group
    have h4 := mul_right_cancel h3
    calc l * e₀ = l * e₀ * l⁻¹ * l := by group
      _ = e₀ * l := by rw [h4]
  have hx2C : x * x ∈ centralizer (L : Set G) := by
    rw [hx2]
    refine mul_mem ?_ hc₀
    rcases H.eq_of_forall_commute D he₀ hcomm with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact (std_center_facts hset ht htZ).1
  obtain ⟨θ, hθ, hθ1, hinn⟩ := std_automizer_embedding hset ht htZ
  have hα : θ ⟨x, hxt⟩ * θ ⟨x, hxt⟩ = 1 := by
    rw [← map_mul]
    exact (hθ1 _).2 hx2C
  have hmk := isDoubleCover_mk h2 ht htZ hLt
  have hfix : ∀ b ∈ imgSub (QuotientGroup.mk' (center L)) E, θ ⟨x, hxt⟩ b = b := by
    rintro _ ⟨⟨e, heL⟩, he, rfl⟩
    refine hθ ⟨x, hxt⟩ ⟨e, heL⟩ ⟨e, heL⟩ ?_
    change e = x * e * x⁻¹
    rw [← mem_centralizer_iff.1 hx e he, mul_inv_cancel_right]
  have hsq : ∀ b ∈ imgSub (QuotientGroup.mk' (center L)) E, b ^ 2 = 1 := by
    rintro _ ⟨⟨e, heL⟩, he, rfl⟩
    rw [← map_pow]
    have : (⟨e, heL⟩ : L) ^ 2 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow]
      exact hE2 e he)
    rw [this, map_one]
  have h6 := card_le_of_fixed hQ hα (fun q hq => hxF ((hinn _).1 ⟨q, hq⟩)) hfix hsq
  have h10 := hmk.card_le_two_mul_imgSub hEL
  rw [H.card_toddLift D] at h10
  omega

omit [Finite G] in
theorem ker_eq_center (h2 : Nat.card (center L) = 2) (ht : orderOf t = 2)
    (htZ : t ∈ (center L).map L.subtype) {Q' : Type} [Group Q'] {π : L →* Q'}
    (H : IsDoubleCover t L π) : π.ker = center L := by
  have hmk := isDoubleCover_mk h2 ht htZ H.le_centralizer
  ext y
  rw [MonoidHom.mem_ker, H.ker y, ← hmk.ker y, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]

theorem davisSolomonFacts_toddLift
    (hset : StandardSetting G L) (ht : orderOf t = 2)
    (htZ : t ∈ (center L).map L.subtype) (h2 : Nat.card (center L) = 2)
    (hQ : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1) {Q' : Type} [Group Q']
    {π : L →* Q'} (H : IsDoubleCover t L π) (D : ToddParabolic Q') :
    DavisSolomonFacts G t L (liftSub π D.A) ∧
      centralizer (liftSub π D.A : Set G) ≤ liftSub π D.A ⊔ centralizer (L : Set G) := by
  have : Group.IsPerfect L := Group.isPerfect_def.2 hset.standard.1.1
  obtain ⟨-, -, -, -, hN, hLt, -⟩ := std_center_facts hset ht htZ
  have hker := ker_eq_center h2 ht htZ H
  have hE2 := H.toddLift_sq D hker hQ
  exact ⟨DavisSolomonFacts.of_standard hset ht htZ (liftSub_le π D.A) hE2 (H.card_toddLift D)
    (std_rank hset ht htZ h2 hQ) (H.sq_eq_one_of_sq_mem_center D hE2 hker)
    (fun _ hBL hB2 hB => H.toddLift_conj_class D hBL hB2 hB)
    (fun _ hs hs2 => H.toddLift_fuse D hs hs2) (H.toddLift_gen D) (H.toddLift_odd_index D)
    (fun _ hB hB2 hcard => H.toddLift_unique D hB hB2 hcard)
    (relIndex_sup_inf_centralizer_le_two hLt hN.le h2 hQ).1,
    std_centralizer_toddLift_le hset ht htZ h2 hQ H D hE2⟩

omit [Finite G] in
theorem exists_center_involution (h2 : Nat.card (center L) = 2) :
    ∃ t : G, orderOf t = 2 ∧ t ∈ (center L).map L.subtype := by
  obtain ⟨w, hw1, -⟩ := (Nat.card_eq_two_iff' (1 : center L)).1 h2
  refine ⟨((w : L) : G), ?_, ⟨w, w.2, rfl⟩⟩
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
  refine orderOf_eq_prime ?_ hw1
  have := pow_card_eq_one' (G := center L) (x := w)
  rwa [h2] at this

theorem std_mem_of_odd_orderOf
    (hset : StandardSetting G L) (ht : orderOf t = 2)
    (htZ : t ∈ (center L).map L.subtype) (h2 : Nat.card (center L) = 2)
    (hQ : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1) {E : Subgroup G}
    (D : DavisSolomonFacts G t L E)
    (hCE : centralizer (E : Set G) ≤ E ⊔ centralizer (L : Set G)) :
    ∀ g ∈ centralizer {t}, Odd (orderOf g) → g ∈ L := by
  intro g hg hodd
  have hF := (std_centralizer_eq_zpowers hset ht htZ D hCE).2.2
  have hout := std_outer hset ht htZ h2 hQ
  rw [hF] at hout
  have h0 : L.relIndex (centralizer {t}) ≠ 0 := relIndex_ne_zero_of_finite _ _
  rcases (show L.relIndex (centralizer {t}) = 1 ∨ L.relIndex (centralizer {t}) = 2 by omega)
    with h | h
  · exact relIndex_eq_one.1 h hg
  · exact mem_of_odd_orderOf h hg hodd

omit [Finite G] in
theorem map_comap_uA_eq_liftSub
    {p : L →* Equiv.Perm (Fin 693)} (hp : ∀ y, p y ∈ CFSG.Fischer.T46) :
    (uA.comap p).map L.subtype = liftSub (p.codRestrict CFSG.Fischer.T46 hp) toddT46.A := by
  ext g
  rw [mem_liftSub]
  simp only [mem_map, mem_comap, coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hA⟩
    exact ⟨⟨g, h⟩, hA, rfl⟩

omit [Finite G] in
theorem isDoubleCover_codRestrict
    {p : L →* Equiv.Perm (Fin 693)}
    (hp : ∀ y, p y ∈ CFSG.Fischer.T46) (hsurj : ∀ x ∈ CFSG.Fischer.T46, ∃ y, p y = x)
    (hker : ∀ y : L, p y = 1 ↔ (y : G) = 1 ∨ (y : G) = t) (htL : t ∈ L)
    (hLt : L ≤ centralizer {t}) (ht : orderOf t = 2) :
    IsDoubleCover t L (p.codRestrict CFSG.Fischer.T46 hp) := by
  refine ⟨fun x => ?_, fun y => ?_, htL, hLt, ht⟩
  · obtain ⟨y, hy⟩ := hsurj x x.2
    exact ⟨y, Subtype.ext hy⟩
  · rw [← hker y]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem davisSolomonFacts_uA
    (hset : StandardSetting G L) (ht : orderOf t = 2)
    (htZ : t ∈ (center L).map L.subtype) (h2 : Nat.card (center L) = 2)
    (hQ : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1) {p : L →* Equiv.Perm (Fin 693)}
    (hp : ∀ y, p y ∈ CFSG.Fischer.T46) (hsurj : ∀ x ∈ CFSG.Fischer.T46, ∃ y, p y = x)
    (hker : ∀ y : L, p y = 1 ↔ (y : G) = 1 ∨ (y : G) = t) :
    DavisSolomonFacts G t L ((uA.comap p).map L.subtype) ∧
      centralizer ((uA.comap p).map L.subtype : Set G) ≤
        (uA.comap p).map L.subtype ⊔ centralizer (L : Set G) ∧
      ∀ g ∈ centralizer {t}, Odd (orderOf g) → g ∈ L := by
  obtain ⟨-, -, -, -, -, hLt, -⟩ := std_center_facts hset ht htZ
  have htL : t ∈ L := by
    obtain ⟨z, -, rfl⟩ := htZ
    exact z.2
  have H := isDoubleCover_codRestrict hp hsurj hker htL hLt ht
  rw [map_comap_uA_eq_liftSub hp]
  obtain ⟨D, hCE⟩ := davisSolomonFacts_toddLift hset ht htZ h2 hQ H toddT46
  exact ⟨D, hCE, std_mem_of_odd_orderOf hset ht htZ h2 hQ D hCE⟩

open CFSG.LocalAnalysis.ComponentInitial in
theorem std_card_center_eq_two (hset : StandardSetting G L) (hZ : center L ≠ ⊥)
    (hZ2 : IsPGroup 2 (center L)) (hQ : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1) :
    Nat.card (center L) = 2 := by
  have : Group.IsPerfect L := Group.isPerfect_def.2 hset.standard.1.1
  obtain ⟨-, -, -, hcyc, -⟩ := std_center_involution hset hZ
  have hel := unitary_six_field_two_perfect_central_two_kernel_elementary
    (QuotientGroup.mk' (center L)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) (by rw [QuotientGroup.ker_mk']; exact hZ2) hQ
  rw [QuotientGroup.ker_mk'] at hel
  have hdvd : Nat.card (center L) ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 2 _
  have h1 : Nat.card (center L) ≠ 1 := fun h => hZ (Subgroup.card_eq_one.1 h)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact absurd h h1
  · exact h

end Standard

end CFSG.EvenSmallLie.UnitarySix
