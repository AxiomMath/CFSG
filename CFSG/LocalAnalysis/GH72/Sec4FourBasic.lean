module

import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import CFSG.LocalAnalysis.GH72.Sec2
public import CFSG.LocalAnalysis.GH72.GWForm
public import CFSG.LocalAnalysis.GH72.Sec4A
public import CFSG.LocalAnalysis.GH72.Sec4Residual

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools
open CFSG.GorensteinWalter (twoResidualOf HasDihedralSylowTwo IsOddPrimePower PSL2 PGL2)

section KleinFour

variable {V : Type*} [Group V]

private def kfPermHom (V : Type*) [Group V] : MulAut V →* Equiv.Perm {x : V // x ≠ 1} where
  toFun α := Equiv.Perm.subtypePerm (MulEquiv.toEquiv α) fun x => by simp
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

private theorem kfPermHom_injective : Function.Injective (kfPermHom V) := by
  intro α β h
  ext x
  by_cases hx : x = 1
  · rw [hx, map_one, map_one]
  · exact congrArg (fun σ : Equiv.Perm {x : V // x ≠ 1} => ((σ ⟨x, hx⟩ : {x : V // x ≠ 1}) : V)) h

private def permCongrMulEquiv {α β : Type*} (e : α ≃ β) : Equiv.Perm α ≃* Equiv.Perm β :=
  { e.permCongr with map_mul' := fun p q => e.permCongr_mul p q }

variable [IsKleinFour V]

private theorem card_ne_one : Nat.card {x : V // x ≠ 1} = 3 := by
  classical
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [IsKleinFour.card_four]; norm_num)
  let _ := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    ← Nat.card_eq_fintype_card, IsKleinFour.card_four]

private theorem exists_mulAut_hom :
    ∃ ψ : MulAut V →* Equiv.Perm (Fin 3), Function.Injective ψ := by
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [IsKleinFour.card_four]; norm_num)
  let e : {x : V // x ≠ 1} ≃ Fin 3 := Finite.equivFinOfCardEq card_ne_one
  exact ⟨(permCongrMulEquiv e).toMonoidHom.comp (kfPermHom V),
    (permCongrMulEquiv e).injective.comp kfPermHom_injective⟩

theorem mulAut_kleinFour_pow_six (α : MulAut V) : α ^ 6 = 1 := by
  obtain ⟨ψ, hψ⟩ := exists_mulAut_hom (V := V)
  apply hψ
  rw [map_pow, map_one]
  revert α
  have h : ∀ σ : Equiv.Perm (Fin 3), σ ^ 6 = 1 := by decide
  exact fun α => h _

theorem mulAut_kleinFour_mul_pow_three {α β : MulAut V} (hα : α ^ 3 = 1) (hβ : β ^ 3 = 1) :
    (α * β) ^ 3 = 1 := by
  obtain ⟨ψ, hψ⟩ := exists_mulAut_hom (V := V)
  have h : ∀ σ τ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → τ ^ 3 = 1 → (σ * τ) ^ 3 = 1 := by decide
  apply hψ
  rw [map_pow, map_mul, map_one]
  exact h _ _ (by rw [← map_pow, hα, map_one]) (by rw [← map_pow, hβ, map_one])

theorem mulAut_kleinFour_mul_ne_mul {α ρ : MulAut V} (hα : α ^ 3 = 1) (hα1 : α ≠ 1)
    (hρ : ρ ^ 2 = 1) (hρ1 : ρ ≠ 1) : α * ρ ≠ ρ * α := by
  obtain ⟨ψ, hψ⟩ := exists_mulAut_hom (V := V)
  have h : ∀ σ ρ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → σ ≠ 1 → ρ ^ 2 = 1 → ρ ≠ 1 →
      σ * ρ ≠ ρ * σ := by decide
  intro hc
  refine h (ψ α) (ψ ρ) (by rw [← map_pow, hα, map_one]) (fun h1 => hα1 (hψ (by rw [h1, map_one])))
    (by rw [← map_pow, hρ, map_one]) (fun h1 => hρ1 (hψ (by rw [h1, map_one]))) ?_
  rw [← map_mul, ← map_mul, hc]

theorem mulAut_kleinFour_eq_of_pow_three {α β : MulAut V} (hα : α ^ 3 = 1) (hα1 : α ≠ 1)
    (hβ : β ^ 3 = 1) : β = 1 ∨ β = α ∨ β = α ^ 2 := by
  obtain ⟨ψ, hψ⟩ := exists_mulAut_hom (V := V)
  have h : ∀ σ τ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → σ ≠ 1 → τ ^ 3 = 1 →
      τ = 1 ∨ τ = σ ∨ τ = σ ^ 2 := by decide
  rcases h (ψ α) (ψ β) (by rw [← map_pow, hα, map_one])
      (fun h1 => hα1 (hψ (by rw [h1, map_one]))) (by rw [← map_pow, hβ, map_one]) with
    h1 | h1 | h1
  · exact Or.inl (hψ (by rw [h1, map_one]))
  · exact Or.inr (Or.inl (hψ h1))
  · exact Or.inr (Or.inr (hψ (by rw [h1, map_pow])))

end KleinFour

section Generic

variable {Y : Type*} [Group Y] [Finite Y]

theorem le_sup_inf_normalizer_of_isSylowOf {p : ℕ} [Fact p.Prime] {J L P : Subgroup Y}
    (hLJ : L ≤ J) (hJL : J ≤ normalizer (L : Set Y)) (hP : IsSylowOf p P L) :
    J ≤ L ⊔ (J ⊓ normalizer (P : Set Y)) := by
  intro j hj
  have hQL : P.map (MulAut.conj j).toMonoidHom ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 (hJL hj) x).1 (hP.le hx)
  obtain ⟨l, hlL, hl⟩ := exists_mem_map_conj_le_of_isSylowOf hP hQL (hP.isPGroup.map _)
  have heq : (P.map (MulAut.conj j).toMonoidHom).map (MulAut.conj l).toMonoidHom = P := by
    apply eq_of_le_of_card_ge hl
    rw [card_map_of_injective (MulAut.conj l).injective,
      card_map_of_injective (MulAut.conj j).injective]
  have hn : l * j ∈ normalizer (P : Set Y) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 : (MulAut.conj l).toMonoidHom ((MulAut.conj j).toMonoidHom x) ∈ P := by
        rw [← heq]
        exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      simpa [mul_assoc] using h1
    · intro hx
      rw [← heq] at hx
      obtain ⟨_, ⟨y, hy, rfl⟩, hyx⟩ := hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      have e : y = x := by
        have e' : l * (j * y * j⁻¹) * l⁻¹ = l * j * x * (l * j)⁻¹ := hyx
        have := congrArg (fun w => (l * j)⁻¹ * w * (l * j)) e'
        calc y = (l * j)⁻¹ * (l * (j * y * j⁻¹) * l⁻¹) * (l * j) := by group
          _ = (l * j)⁻¹ * (l * j * x * (l * j)⁻¹) * (l * j) := this
          _ = x := by group
      rwa [← e]
  have e : j = l⁻¹ * (l * j) := by group
  rw [e]
  exact mul_mem (mem_sup_left (inv_mem hlL)) (mem_sup_right (mem_inf.2 ⟨mul_mem (hLJ hlL) hj, hn⟩))

theorem eq_bot_of_odd_of_le_normalizer (hO : CFSG.oddCore Y = ⊥) {J N : Subgroup Y}
    (hKJ : twoResidualOf (⊤ : Subgroup Y) ≤ J) (hJN : J ≤ normalizer (N : Set Y))
    (hN : Odd (Nat.card N)) : N = ⊥ := by
  have : (twoResidualOf (⊤ : Subgroup Y)).Normal := twoResidualOf_top_normal
  set K := twoResidualOf (⊤ : Subgroup Y)
  have hOK : CFSG.oddCore K = ⊥ := CFSG.ABGDGroups.oddCore_eq_bot_of_normal hO K
  have hle : (N ⊓ K).subgroupOf K ≤ CFSG.oddCore K := by
    apply le_oddCore_of_normal
    · constructor
      intro n hn k
      rw [mem_subgroupOf] at hn ⊢
      obtain ⟨hnN, hnK⟩ := mem_inf.1 hn
      exact mem_inf.2 ⟨(mem_normalizer_iff.1 (hJN (hKJ k.2)) n).1 hnN,
        mul_mem (mul_mem k.2 hnK) (inv_mem k.2)⟩
    · rw [show Nat.card ((N ⊓ K).subgroupOf K) = Nat.card (N ⊓ K : Subgroup Y) from
        Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv]
      exact Odd.of_dvd_nat hN (card_dvd_of_le inf_le_left)
  rw [hOK] at hle
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨k, hk⟩ := exists_pow_mem_twoResidualOf (mem_top x)
  have h1 : x ^ 2 ^ k = 1 := by
    have h2 : (⟨x ^ 2 ^ k, hk⟩ : K) ∈ (N ⊓ K).subgroupOf K :=
      mem_subgroupOf.2 (mem_inf.2 ⟨pow_mem hx _, hk⟩)
    have h3 := hle h2
    rw [mem_bot] at h3
    exact congrArg Subtype.val h3
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : Odd (orderOf x) := by
    have h4 := orderOf_dvd_natCard (⟨x, hx⟩ : N)
    rw [Subgroup.orderOf_mk] at h4
    exact Odd.of_dvd_nat hN h4
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact mem_bot.2 (orderOf_eq_one_iff.1 hj)
  · exfalso
    rw [hj] at h3
    exact (Nat.not_even_iff_odd.2 h3) (Nat.even_pow.2 ⟨even_two, j.succ_ne_zero⟩)

theorem le_sup_twoResidualOf_of_isSylowOf {J T : Subgroup Y} (hT : IsSylowOf 2 T J) :
    J ≤ T ⊔ twoResidualOf ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (twoResidualOf (⊤ : Subgroup Y)).Normal := twoResidualOf_top_normal
  have : ((twoResidualOf (⊤ : Subgroup Y)).subgroupOf J).Normal := normal_subgroupOf
  have h2 : IsPGroup 2 (↥J ⧸ (twoResidualOf (⊤ : Subgroup Y)).subgroupOf J) := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := exists_pow_mem_twoResidualOf (mem_top x)
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]; exact hk⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h2
  exact le_sup_of_isSylowOf_of_relIndex hT (k := n) hn

theorem isPGroup_of_isSylowOf_le_centralizer (hO : CFSG.oddCore Y = ⊥) {J C P : Subgroup Y}
    (hKJ : twoResidualOf (⊤ : Subgroup Y) ≤ J) (hJC : J ≤ normalizer (C : Set Y))
    (hP : IsSylowOf 2 P C) (hPc : P ≤ centralizer (C : Set Y)) : IsPGroup 2 C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP
  have hQc : ∀ q ∈ (Q : Subgroup C), ∀ g : C, g * q = q * g := by
    intro q hq g
    have hqP : (q : Y) ∈ P := hQ ▸ ⟨q, hq, rfl⟩
    exact Subtype.ext (mem_centralizer_iff.1 (hPc hqP) g g.2)
  have hN : normalizer (Q : Set C) ≤ centralizer (Q : Set C) := fun g _ =>
    mem_centralizer_iff.2 fun q hq => (hQc q hq g).symm
  have hNc := MonoidHom.ker_transferSylow_isComplement' Q hN
  have hNodd : ¬ 2 ∣ Nat.card (MonoidHom.transferSylow Q hN).ker :=
    MonoidHom.not_dvd_card_ker_transferSylow Q hN
  set N := (MonoidHom.transferSylow Q hN).ker
  have hNodd' : Odd (Nat.card N) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hNodd)
  have hQodd : ∀ q ∈ (Q : Subgroup C), Odd (orderOf q) → q = 1 := by
    intro q hq hodd
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 Q.isPGroup' ⟨q, hq⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [hk] at hodd
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact orderOf_eq_one_iff.1 hk
    · exact absurd hodd (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, k.succ_ne_zero⟩))
  have hodd_mem : ∀ x : C, Odd (orderOf x) → x ∈ N := by
    intro x hx
    obtain ⟨⟨⟨n, hn⟩, ⟨q, hq⟩⟩, hnq⟩ := hNc.2 x
    simp only at hnq
    have hm : x ^ Nat.card N = q ^ Nat.card N := by
      rw [← hnq, (Commute.mul_pow (hQc q hq n)), show n ^ Nat.card N = 1 by
        have h1 := pow_card_eq_one' (x := (⟨n, hn⟩ : N))
        exact congrArg Subtype.val h1, one_mul]
    have hqodd : Odd (orderOf (q ^ Nat.card N)) := by
      rw [← hm]
      exact Odd.of_dvd_nat hx (orderOf_pow_dvd _)
    have hq1 := hQodd _ (pow_mem hq _) hqodd
    have hqo : Odd (orderOf q) := by
      have h1 : orderOf q ∣ Nat.card N := orderOf_dvd_of_pow_eq_one hq1
      exact Odd.of_dvd_nat hNodd' h1
    rw [← hnq, hQodd q hq hqo, mul_one]
    exact hn
  have hNJ : J ≤ normalizer ((N.map C.subtype : Subgroup Y) : Set Y) := by
    have key : ∀ g ∈ J, ∀ y ∈ N.map C.subtype, g * y * g⁻¹ ∈ N.map C.subtype := by
      rintro g hg _ ⟨n, hn, rfl⟩
      have hgC : g * (n : Y) * g⁻¹ ∈ C := (mem_normalizer_iff.1 (hJC hg) n).1 n.2
      refine ⟨⟨_, hgC⟩, hodd_mem _ ?_, rfl⟩
      rw [Subgroup.orderOf_mk, orderOf_conj_eq, Subgroup.orderOf_coe]
      have h1 := orderOf_dvd_natCard (⟨n, hn⟩ : N)
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat hNodd' h1
    intro g hg
    rw [mem_normalizer_iff]
    intro y
    refine ⟨fun hy => key g hg y hy, fun hy => ?_⟩
    have h1 := key g⁻¹ (inv_mem hg) _ hy
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e] at h1
  have hNbot : N.map C.subtype = ⊥ := eq_bot_of_odd_of_le_normalizer hO hKJ hNJ
    (by rw [card_map_of_injective C.subtype_injective]; exact hNodd')
  have hN1 : N = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    have h1 : (n : Y) ∈ N.map C.subtype := ⟨n, hn, rfl⟩
    rw [hNbot, mem_bot] at h1
    exact (mem_bot).2 (Subtype.ext h1)
  have hcard := hNc.card_mul
  rw [hN1, card_bot, one_mul] at hcard
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 Q.isPGroup'
  exact IsPGroup.of_card (n := k) (by rw [← hcard, hk])

theorem le_centralizer_of_isIsolatedIn {Y : Type} [Group Y] [Finite Y] {F : Subgroup Y} {t : Y}
    (hFt : t ∈ normalizer (F : Set Y)) (ht : IsIsolatedIn (F ⊔ zpowers t) t)
    (hOF : CFSG.oddCore F = ⊥) : F ≤ C t := by
  set X := F ⊔ zpowers t
  have hFX : F ≤ X := le_sup_left
  have hle : (O X ⊓ F).subgroupOf F ≤ CFSG.oddCore F := by
    apply le_oddCore_of_normal
    · constructor
      intro n hn k
      rw [mem_subgroupOf] at hn ⊢
      obtain ⟨hnO, hnF⟩ := mem_inf.1 hn
      exact mem_inf.2 ⟨(mem_normalizer_iff.1 (le_normalizer_O X (hFX k.2)) n).1 hnO,
        mul_mem (mul_mem k.2 hnF) (inv_mem k.2)⟩
    · rw [show Nat.card ((O X ⊓ F).subgroupOf F) = Nat.card (O X ⊓ F : Subgroup Y) from
        Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv]
      exact Odd.of_dvd_nat (card_O_odd X) (card_dvd_of_le inf_le_left)
  rw [hOF] at hle
  intro f hf
  have h1 : f * t * f⁻¹ * t⁻¹ ∈ O X := ht.conj_mul_inv_mem_O (hFX hf)
  have h2 : f * t * f⁻¹ * t⁻¹ ∈ F := by
    have h3 : t * f⁻¹ * t⁻¹ ∈ F := (mem_normalizer_iff.1 hFt f⁻¹).1 (inv_mem hf)
    have e : f * t * f⁻¹ * t⁻¹ = f * (t * f⁻¹ * t⁻¹) := by group
    rw [e]
    exact mul_mem hf h3
  have h4 : (⟨_, h2⟩ : F) ∈ (O X ⊓ F).subgroupOf F := mem_subgroupOf.2 (mem_inf.2 ⟨h1, h2⟩)
  have h5 := hle h4
  rw [mem_bot] at h5
  have h6 : f * t * f⁻¹ * t⁻¹ = 1 := congrArg Subtype.val h5
  rw [mem_centralizer_singleton_iff]
  calc f * t = f * t * f⁻¹ * t⁻¹ * (t * f) := by group
    _ = t * f := by rw [h6, one_mul]

theorem oddCore_eq_bot_of_isSimpleGroup {F : Subgroup Y} [IsSimpleGroup F]
    (h2 : 2 ∣ Nat.card F) : CFSG.oddCore F = ⊥ := by
  rcases (CFSG.oddCore_normal F).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hodd : Odd (Nat.card (CFSG.oddCore F)) := odd_card_oddCore
    rw [h, card_top] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

end Generic

section Tools

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem mem_normalizer_sup {A B : Subgroup Y} {g : Y} (hA : g ∈ normalizer (A : Set Y))
    (hB : g ∈ normalizer (B : Set Y)) : g ∈ normalizer ((A ⊔ B : Subgroup Y) : Set Y) := by
  have key : ∀ h : Y, h ∈ normalizer (A : Set Y) → h ∈ normalizer (B : Set Y) →
      ∀ x ∈ A ⊔ B, h * x * h⁻¹ ∈ A ⊔ B := by
    intro h hA hB x hx
    have hle : (A ⊔ B).map (MulAut.conj h).toMonoidHom ≤ A ⊔ B := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        exact (mem_normalizer_iff.1 hA a).1 ha
      · rintro _ ⟨b, hb, rfl⟩
        exact (mem_normalizer_iff.1 hB b).1 hb
    exact hle ⟨x, hx, rfl⟩
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hA hB x hx, fun hx => ?_⟩
  have h1 := key g⁻¹ (inv_mem hA) (inv_mem hB) _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1

omit [Finite Y] in
theorem le_normalizer_sup {K A B : Subgroup Y} (hA : K ≤ normalizer (A : Set Y))
    (hB : K ≤ normalizer (B : Set Y)) : K ≤ normalizer ((A ⊔ B : Subgroup Y) : Set Y) :=
  fun _ hg => mem_normalizer_sup (hA hg) (hB hg)

omit [Finite Y] in
theorem mem_normalizer_inf_of_mem {A B : Subgroup Y} {g : Y} (hA : g ∈ normalizer (A : Set Y))
    (hB : g ∈ normalizer (B : Set Y)) : g ∈ normalizer ((A ⊓ B : Subgroup Y) : Set Y) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro x
  exact ⟨fun hx => ⟨(hA x).1 hx.1, (hB x).1 hx.2⟩, fun hx => ⟨(hA x).2 hx.1, (hB x).2 hx.2⟩⟩

omit [Finite Y] in
theorem mem_normalizer_centralizer_of_mem {A : Subgroup Y} {g : Y}
    (hA : g ∈ normalizer (A : Set Y)) : g ∈ normalizer (centralizer (A : Set Y) : Set Y) := by
  rw [mem_normalizer_iff]
  intro x
  simp only [SetLike.mem_coe, mem_centralizer_iff]
  constructor
  · intro hx a ha
    have ha' : g⁻¹ * a * g ∈ A := by
      have h := (mem_normalizer_iff.1 (inv_mem hA) a).1 ha
      rwa [inv_inv] at h
    have h := hx _ ha'
    calc a * (g * x * g⁻¹) = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * a := by group
  · intro hx a ha
    have h := hx _ ((mem_normalizer_iff.1 hA a).1 ha)
    have e1 : g * a * g⁻¹ * (g * x * g⁻¹) = g * (a * x) * g⁻¹ := by group
    have e2 : g * x * g⁻¹ * (g * a * g⁻¹) = g * (x * a) * g⁻¹ := by group
    rw [e1, e2] at h
    exact mul_left_cancel (mul_right_cancel h)

theorem le_normalizer_O_of_le_normalizer {J L : Subgroup Y}
    (hJL : J ≤ normalizer (L : Set Y)) : J ≤ normalizer (O L : Set Y) := by
  have hconj : ∀ h ∈ J, ∀ x ∈ O L, h * x * h⁻¹ ∈ O L := by
    intro h hh x hx
    have hL : ∀ y, y ∈ L ↔ h * y * h⁻¹ ∈ L := mem_normalizer_iff.1 (hJL hh)
    let φ : L →* L :=
      ((MulAut.conj h).toMonoidHom.comp L.subtype).codRestrict L fun y => (hL y).1 y.2
    have hφs : Function.Surjective φ := by
      intro y
      have hy : h⁻¹ * y * h ∈ L := by
        rw [hL]
        rw [show h * (h⁻¹ * (y : Y) * h) * h⁻¹ = y by group]
        exact y.2
      refine ⟨⟨h⁻¹ * y * h, hy⟩, Subtype.ext ?_⟩
      show h * (h⁻¹ * (y : Y) * h) * h⁻¹ = y
      group
    have hle : (CFSG.oddCore L).map φ ≤ CFSG.oddCore L :=
      le_oddCore_of_normal ((CFSG.oddCore_normal L).map φ hφs)
        (Odd.of_dvd_nat odd_card_oddCore (card_map_dvd _ _))
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨φ y, hle ⟨y, hy, rfl⟩, rfl⟩
  intro h hh
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hconj h hh x hx, fun hx => ?_⟩
  have h1 := hconj h⁻¹ (inv_mem hh) _ hx
  rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at h1

theorem isSylowOf_sup_of_le_normalizer {A T : Subgroup Y} (hTA : T ≤ normalizer (A : Set Y))
    (hT : IsPGroup 2 T) (h : IsSylowOf 2 (T ⊓ A) A) : IsSylowOf 2 T (A ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff] at h ⊢
  refine ⟨le_sup_right, hT, ?_⟩
  have hcard :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hTA
  rw [sup_comm] at hcard
  have h1 := Subgroup.relIndex_mul_card T (A ⊔ T)
  rw [inf_eq_left.2 le_sup_right] at h1
  have h2 := Subgroup.relIndex_mul_card (T ⊓ A) A
  rw [inf_eq_left.2 inf_le_right] at h2
  have heq : T.relIndex (A ⊔ T) = (T ⊓ A).relIndex A := by
    have hpos : 0 < Nat.card T * Nat.card (T ⊓ A : Subgroup Y) :=
      Nat.mul_pos Nat.card_pos Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc T.relIndex (A ⊔ T) * (Nat.card T * Nat.card (T ⊓ A : Subgroup Y))
        = T.relIndex (A ⊔ T) * Nat.card T * Nat.card (T ⊓ A : Subgroup Y) := by ring
      _ = Nat.card (A ⊔ T : Subgroup Y) * Nat.card (T ⊓ A : Subgroup Y) := by rw [h1]
      _ = Nat.card T * Nat.card A := hcard
      _ = Nat.card T * ((T ⊓ A).relIndex A * Nat.card (T ⊓ A : Subgroup Y)) := by rw [h2]
      _ = (T ⊓ A).relIndex A * (Nat.card T * Nat.card (T ⊓ A : Subgroup Y)) := by ring
  rw [heq]
  exact h.2.2

theorem isIsolatedIn_of_forall_conj_mem {X R : Subgroup Y} (hR : IsSylowOf 2 R X) {t : Y}
    (htR : t ∈ R) (ht2 : orderOf t = 2) (hfix : ∀ k ∈ X, k * t * k⁻¹ ∈ R → k * t * k⁻¹ = t) :
    IsIsolatedIn X t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htX : t ∈ X := hR.le htR
  have hRC : R ≤ C t := by
    intro r hr
    have h := hfix r (hR.le hr) (mul_mem (mul_mem hr htR) (inv_mem hr))
    rw [mem_centralizer_singleton_iff]
    calc r * t = r * t * r⁻¹ * r := by group
      _ = t * r := by rw [h]
  have hRsyl : IsSylowOf 2 R (X ⊓ C t) := hR.of_le (le_inf hR.le hRC) inf_le_left
  refine ⟨htX, ht2, fun h hh hc => ?_⟩
  have hu2 : orderOf (h * t * h⁻¹) = 2 := by rw [orderOf_conj_eq]; exact ht2
  have huC : h * t * h⁻¹ ∈ X ⊓ C t :=
    mem_inf.2 ⟨mul_mem (mul_mem hh htX) (inv_mem hh), mem_centralizer_singleton_iff.2 hc.eq⟩
  obtain ⟨c, hcC, hcR⟩ := exists_mem_conj_mem_of_isSylowOf hRsyl huC
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2, pow_one]))
  obtain ⟨hcX, hct⟩ := mem_inf.1 hcC
  have hk : c * h * t * (c * h)⁻¹ = c * (h * t * h⁻¹) * c⁻¹ := by group
  have h1 := hfix (c * h) (mul_mem hcX hh) (by rw [hk]; exact hcR)
  rw [hk] at h1
  have hct' : c * t = t * c := mem_centralizer_singleton_iff.1 hct
  calc h * t * h⁻¹ = c⁻¹ * (c * (h * t * h⁻¹) * c⁻¹) * c := by group
    _ = c⁻¹ * (t * c) := by rw [h1, mul_assoc]
    _ = c⁻¹ * (c * t) := by rw [hct']
    _ = t := by group

end Tools

section KleinFourAction

variable {Y : Type} [Group Y] [Finite Y] {V : Subgroup Y}

omit [Finite Y] in
private theorem normalizerMonoidHom_eq_one_iff {g : normalizer (V : Set Y)} :
    V.normalizerMonoidHom g = 1 ↔ (g : Y) ∈ centralizer (V : Set Y) := by
  rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker, mem_subgroupOf]

omit [Finite Y] in
private theorem normalizerMonoidHom_pow {g : Y} (hg : g ∈ normalizer (V : Set Y)) (n : ℕ) :
    V.normalizerMonoidHom ⟨g ^ n, pow_mem hg n⟩ = V.normalizerMonoidHom ⟨g, hg⟩ ^ n := by
  rw [← map_pow]
  congr 1

omit [Finite Y] in
private theorem mem_centralizer_iff_normalizerMonoidHom {g : Y} (hg : g ∈ normalizer (V : Set Y)) :
    g ∈ centralizer (V : Set Y) ↔ V.normalizerMonoidHom ⟨g, hg⟩ = 1 :=
  (normalizerMonoidHom_eq_one_iff (g := ⟨g, hg⟩)).symm

variable [IsKleinFour V]

theorem pow_three_mem_centralizer
    (hKV : twoResidualOf (⊤ : Subgroup Y) ≤ normalizer (V : Set Y)) {k : Y}
    (hk : k ∈ twoResidualOf (⊤ : Subgroup Y)) : k ^ 3 ∈ centralizer (V : Set Y) := by
  let Q : Subgroup Y :=
    { carrier := {g | ∃ hg : g ∈ normalizer (V : Set Y), V.normalizerMonoidHom ⟨g, hg⟩ ^ 3 = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha3⟩ ⟨hb, hb3⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have e : (⟨a * b, mul_mem ha hb⟩ : normalizer (V : Set Y)) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
        rw [e, map_mul]
        exact mulAut_kleinFour_mul_pow_three ha3 hb3
      one_mem' := ⟨one_mem _, by
        have e : (⟨1, one_mem _⟩ : normalizer (V : Set Y)) = 1 := rfl
        rw [e, map_one, one_pow]⟩
      inv_mem' := by
        rintro a ⟨ha, ha3⟩
        refine ⟨inv_mem ha, ?_⟩
        have e : (⟨a⁻¹, inv_mem ha⟩ : normalizer (V : Set Y)) = (⟨a, ha⟩)⁻¹ := rfl
        rw [e, map_inv, inv_pow, ha3, inv_one] }
  have hKQ : twoResidualOf (⊤ : Subgroup Y) ≤ Q := by
    refine twoResidualOf_le_of_forall fun x _ hx => ?_
    have hxN : x ∈ normalizer (V : Set Y) := hKV (mem_twoResidualOf_of_odd (mem_top x) hx)
    refine ⟨hxN, ?_⟩
    have h1 : orderOf (V.normalizerMonoidHom ⟨x, hxN⟩) ∣ orderOf x := by
      have h := orderOf_map_dvd V.normalizerMonoidHom ⟨x, hxN⟩
      rwa [Subgroup.orderOf_mk] at h
    have h6 : orderOf (V.normalizerMonoidHom ⟨x, hxN⟩) ∣ 3 * 2 :=
      orderOf_dvd_of_pow_eq_one (mulAut_kleinFour_pow_six _)
    have hcop : Nat.Coprime (orderOf (V.normalizerMonoidHom ⟨x, hxN⟩)) 2 :=
      (Nat.coprime_two_right).2 (Odd.of_dvd_nat hx h1)
    exact orderOf_dvd_iff_pow_eq_one.1 (hcop.dvd_of_dvd_mul_right h6)
  obtain ⟨hg, hg3⟩ := hKQ hk
  rw [mem_centralizer_iff_normalizerMonoidHom (pow_mem hg 3), normalizerMonoidHom_pow hg 3]
  exact hg3

omit [Finite Y] in
theorem sq_mem_centralizer_of_pow_eq_one {g : Y} (hg : g ∈ normalizer (V : Set Y)) {n : ℕ}
    (hgn : g ^ 2 ^ n = 1) : g ^ 2 ∈ centralizer (V : Set Y) := by
  rw [mem_centralizer_iff_normalizerMonoidHom (pow_mem hg 2), normalizerMonoidHom_pow hg 2]
  have h1 : V.normalizerMonoidHom ⟨g, hg⟩ ^ 2 ^ n = 1 := by
    rw [← normalizerMonoidHom_pow hg (2 ^ n)]
    have e : (⟨g ^ 2 ^ n, pow_mem hg _⟩ : normalizer (V : Set Y)) = 1 := Subtype.ext hgn
    rw [e, map_one]
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h1)
  have h6 := orderOf_dvd_of_pow_eq_one (mulAut_kleinFour_pow_six (V.normalizerMonoidHom ⟨g, hg⟩))
  have hj1 : j ≤ 1 := by
    by_contra h
    have h4 : 2 ^ 2 ∣ orderOf (V.normalizerMonoidHom ⟨g, hg⟩) := by
      rw [hj']
      exact pow_dvd_pow 2 (by omega)
    have := h4.trans h6
    norm_num at this
  apply orderOf_dvd_iff_pow_eq_one.1
  rw [hj']
  simpa using pow_dvd_pow 2 hj1

omit [Finite Y] in
theorem commutator_not_mem_centralizer {u τ : Y} (hu : u ∈ normalizer (V : Set Y))
    (hτ : τ ∈ normalizer (V : Set Y)) (hu3 : u ^ 3 ∈ centralizer (V : Set Y))
    (hu1 : u ∉ centralizer (V : Set Y)) (hτ2 : τ ^ 2 ∈ centralizer (V : Set Y))
    (hτ1 : τ ∉ centralizer (V : Set Y)) :
    u * τ * u⁻¹ * τ⁻¹ ∉ centralizer (V : Set Y) := by
  rw [mem_centralizer_iff_normalizerMonoidHom (pow_mem hu 3), normalizerMonoidHom_pow hu 3] at hu3
  rw [mem_centralizer_iff_normalizerMonoidHom (pow_mem hτ 2), normalizerMonoidHom_pow hτ 2] at hτ2
  rw [mem_centralizer_iff_normalizerMonoidHom hu] at hu1
  rw [mem_centralizer_iff_normalizerMonoidHom hτ] at hτ1
  have hw : u * τ * u⁻¹ * τ⁻¹ ∈ normalizer (V : Set Y) :=
    mul_mem (mul_mem (mul_mem hu hτ) (inv_mem hu)) (inv_mem hτ)
  rw [mem_centralizer_iff_normalizerMonoidHom hw]
  have e : (⟨u * τ * u⁻¹ * τ⁻¹, hw⟩ : normalizer (V : Set Y)) =
      ⟨u, hu⟩ * ⟨τ, hτ⟩ * (⟨u, hu⟩)⁻¹ * (⟨τ, hτ⟩)⁻¹ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
  intro h
  apply mulAut_kleinFour_mul_ne_mul hu3 hu1 hτ2 hτ1
  calc V.normalizerMonoidHom ⟨u, hu⟩ * V.normalizerMonoidHom ⟨τ, hτ⟩ =
      V.normalizerMonoidHom ⟨u, hu⟩ * V.normalizerMonoidHom ⟨τ, hτ⟩ *
        (V.normalizerMonoidHom ⟨u, hu⟩)⁻¹ * (V.normalizerMonoidHom ⟨τ, hτ⟩)⁻¹ *
        (V.normalizerMonoidHom ⟨τ, hτ⟩ * V.normalizerMonoidHom ⟨u, hu⟩) := by group
    _ = V.normalizerMonoidHom ⟨τ, hτ⟩ * V.normalizerMonoidHom ⟨u, hu⟩ := by rw [h, one_mul]

omit [Finite Y] in
theorem exists_mul_inv_pow_mem_centralizer {v x : Y} (hv : v ∈ normalizer (V : Set Y))
    (hx : x ∈ normalizer (V : Set Y)) (hv3 : v ^ 3 ∈ centralizer (V : Set Y))
    (hv1 : v ∉ centralizer (V : Set Y)) (hx3 : x ^ 3 ∈ centralizer (V : Set Y)) :
    ∃ e : ℕ, x * (v ^ e)⁻¹ ∈ centralizer (V : Set Y) := by
  rw [mem_centralizer_iff_normalizerMonoidHom (pow_mem hv 3), normalizerMonoidHom_pow hv 3] at hv3
  rw [mem_centralizer_iff_normalizerMonoidHom (pow_mem hx 3), normalizerMonoidHom_pow hx 3] at hx3
  rw [mem_centralizer_iff_normalizerMonoidHom hv] at hv1
  have key : ∀ e : ℕ, V.normalizerMonoidHom ⟨x, hx⟩ = V.normalizerMonoidHom ⟨v, hv⟩ ^ e →
      x * (v ^ e)⁻¹ ∈ centralizer (V : Set Y) := by
    intro e he
    have hm : x * (v ^ e)⁻¹ ∈ normalizer (V : Set Y) := mul_mem hx (inv_mem (pow_mem hv e))
    rw [mem_centralizer_iff_normalizerMonoidHom hm]
    have e' : (⟨x * (v ^ e)⁻¹, hm⟩ : normalizer (V : Set Y)) = ⟨x, hx⟩ * (⟨v, hv⟩ ^ e)⁻¹ := rfl
    rw [e', map_mul, map_inv, map_pow, he, mul_inv_cancel]
  rcases mulAut_kleinFour_eq_of_pow_three hv3 hv1 hx3 with h | h | h
  · exact ⟨0, key 0 (by rw [h, pow_zero])⟩
  · exact ⟨1, key 1 (by rw [h, pow_one])⟩
  · exact ⟨2, key 2 h⟩

end KleinFourAction

section PGL23

variable {Y : Type} [Group Y] [Finite Y]

private theorem pgl2_card_eq {q : ℕ} (hq : IsOddPrimePower q) :
    (q * (q ^ 2 - 1) = 24 → q = 3) ∧ q * (q ^ 2 - 1) ≠ 8 ∧ q * (q ^ 2 - 1) / 2 ≠ 8 ∧
      q * (q ^ 2 - 1) / 2 ≠ 24 := by
  obtain ⟨p, n, hp, hpodd, hn, rfl⟩ := hq
  have h3 : 3 ≤ p := by
    have := hp.two_le
    obtain ⟨k, hk⟩ := hpodd
    omega
  have hq3 : 3 ≤ p ^ n := le_trans h3 (Nat.le_self_pow (by omega) p)
  have hqodd : Odd (p ^ n) := hpodd.pow
  set q := p ^ n
  rcases Nat.lt_or_ge q 5 with h5 | h5
  · have hq : q = 3 := by
      obtain ⟨k, hk⟩ := hqodd
      omega
    rw [hq]
    norm_num
  · have h25 : 25 ≤ q ^ 2 := by nlinarith
    have h120 : 120 ≤ q * (q ^ 2 - 1) := by
      have : 24 ≤ q ^ 2 - 1 := by omega
      nlinarith
    refine ⟨fun h => by omega, by omega, by omega, by omega⟩

theorem isL2PGL2OrA7OrV4_of_card_eq_24
    {L : Subgroup Y} (hD : HasDihedralSylowTwo L) (hO : CFSG.oddCore L = ⊥)
    (hcard : Nat.card L = 24) : IsL2PGL2OrA7OrV4 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases CFSG.QuasiDihedralFusion.gw_cases hD hO with
    h2 | ⟨⟨e⟩⟩ | ⟨F, _, _, hF, L', hL'n, hL'idx, hL'⟩
  · exfalso
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
    rw [hcard] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 24)
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h3)) (by norm_num)
  · exfalso
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hcard
    norm_num at hcard
  · have hmul := L'.index_mul_card
    rw [hcard] at hmul
    obtain ⟨h24, h8, h8', h24'⟩ := pgl2_card_eq hF
    have hidx : L'.index = 1 ∨ L'.index = 3 := by
      have hdvd : L'.index ∣ 24 := Dvd.intro _ hmul
      obtain ⟨k, hk⟩ := hL'idx
      have : L'.index ∈ Nat.divisors 24 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
      have hd : Nat.divisors 24 = {1, 2, 3, 4, 6, 8, 12, 24} := by decide
      rw [hd] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      omega
    have hcardL' : Nat.card L' = 24 ∨ Nat.card L' = 8 := by
      rcases hidx with h | h <;> rw [h] at hmul <;> omega
    rcases hL' with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exfalso
      have hc := hcardL'
      rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.psl2_card_formula F hF] at hc
      rcases hc with h | h
      exacts [h24' h, h8' h]
    · have hc := hcardL'
      rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula F] at hc
      have hq : Nat.card F = 3 := by
        rcases hc with h | h
        · exact h24 h
        · exact absurd h h8
      have h1 : Nat.card L' = 24 := by
        rcases hcardL' with h | h
        · exact h
        · rcases hc with h' | h'
          · rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula F] at h
            omega
          · exact absurd h' h8
      have hL'top : L' = ⊤ := eq_top_of_card_eq L' (by rw [h1, ← hcard])
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨eF⟩ := nonempty_ringEquiv_galoisField (K := F) (p := 3) (n := 1) one_ne_zero
        (by rw [hq, pow_one])
      exact Or.inr (Or.inl ⟨3, 1, inferInstance, by norm_num, by norm_num,
        ⟨topEquiv.symm.trans ((MulEquiv.subgroupCongr hL'top).symm.trans
          (e.trans (CFSG.GorensteinWalter.pgl2RingEquiv eF)))⟩⟩)

end PGL23

end CFSG.GH72
