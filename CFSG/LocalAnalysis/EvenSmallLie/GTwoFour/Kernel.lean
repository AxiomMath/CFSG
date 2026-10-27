module

public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.Inner

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.GTwoFour

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.LieType.Chevalley.G2FieldFour
open scoped commutatorElement

namespace Setup

variable {G : Type} [Group G] {L : Subgroup G}

theorem commute_L_R {a b : G} (ha : a ∈ L) (hb : b ∈ centralizer (L : Set G)) : a * b = b * a :=
  mem_centralizer_iff.1 hb a ha

end Setup

namespace SeitzSetup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  (S : SeitzSetup G L K)

omit [CharP K 2] in
theorem sq_eq_t_of_mul {l r : G} (hl : l ∈ L) (hr : r ∈ centralizer (L : Set G)) (hrL : r ∉ L)
    (h2 : l * r * (l * r) = 1) : l * l = S.t ∧ r * r = S.t := by
  obtain ⟨-, huniq, -, -, -⟩ := S.center_facts
  have hlr : l * l * (r * r) = 1 := by
    rw [← h2, show l * r * (l * r) = l * (r * l) * r by group, ← Setup.commute_L_R hl hr]
    group
  have hrr : r * r = (l * l)⁻¹ := eq_inv_of_mul_eq_one_right hlr
  have hllR : l * l ∈ L ⊓ centralizer (L : Set G) :=
    ⟨mul_mem hl hl, by
      have := inv_mem (mul_mem hr hr)
      rwa [hrr, inv_inv] at this⟩
  rw [inf_centralizer_eq_center] at hllR
  obtain ⟨z, hz, hzl⟩ := hllR
  rcases (S.mem_center_iff z).1 hz with h | h
  · exfalso
    have hll : l * l = 1 := by rw [← hzl, h]; rfl
    rw [hll, inv_one] at hrr
    apply hrL
    by_cases hr1 : r = 1
    · rw [hr1]; exact one_mem _
    · rw [huniq r hr (orderOf_eq_prime (by rw [sq, hrr]) hr1)]
      exact S.t_mem
  · have hll : l * l = S.t := by rw [← hzl]; exact h
    refine ⟨hll, ?_⟩
    rw [hrr, hll]
    exact inv_eq_of_mul_eq_one_right S.t_mul_t

theorem mem_L_of_mem_sup
    {y : G} (hyLR : y ∈ L ⊔ centralizer (L : Set G)) (hy : IsConj S.t y) :
    y ∈ L := by
  have := S.finite_field
  have := S.isPerfect
  by_contra hyL
  obtain ⟨c, hc⟩ := isConj_iff.1 hy
  obtain ⟨htR, huniq, -, hLt, hRt⟩ := S.center_facts
  have hcomm : ∀ a ∈ L, ∀ b ∈ centralizer (L : Set G), a * b = b * a :=
    fun a ha b hb => Setup.commute_L_R ha hb
  obtain ⟨l, hl, r, hr, hlr⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hyLR
  have hrL : r ∉ L := fun h => hyL (hlr ▸ mul_mem hl h)
  have hy2 : y * y = 1 := by
    rw [← hc, show c * S.t * c⁻¹ * (c * S.t * c⁻¹) = c * (S.t * S.t) * c⁻¹ by group, S.t_mul_t,
      mul_one, mul_inv_cancel]
  obtain ⟨-, hrr⟩ := S.sq_eq_t_of_mul hl hr hrL (by rw [hlr]; exact hy2)
  set t₁ := c⁻¹ * S.t * c with ht₁
  set r₁ := c⁻¹ * r * c with hr₁
  have hcy : c⁻¹ * y * c = S.t := by rw [← hc]; group
  have ht₁t : t₁ ≠ S.t := fun h => hyL (by
    have : y = S.t := by
      rw [← hc]
      calc c * S.t * c⁻¹ = c * t₁ * c⁻¹ := by rw [h]
        _ = S.t := by rw [ht₁]; group
    rw [this]; exact S.t_mem)
  have ht₁L : t₁ ∉ L := fun h => ht₁t (S.eq_t_of_isConj h (isConj_iff.2 ⟨c⁻¹, by
    rw [ht₁, inv_inv]⟩))
  have hry : r * y = y * r := by
    calc r * y = r * l * r := by rw [← hlr, mul_assoc]
      _ = l * r * r := by rw [← Setup.commute_L_R hl hr]
      _ = y * r := by rw [hlr]
  have hr₁t : r₁ ∈ centralizer ({S.t} : Set G) := by
    rw [mem_centralizer_singleton_iff, ← hcy, hr₁]
    calc c⁻¹ * r * c * (c⁻¹ * y * c) = c⁻¹ * (r * y) * c := by group
      _ = c⁻¹ * (y * r) * c := by rw [hry]
      _ = c⁻¹ * y * c * (c⁻¹ * r * c) := by group
  have hr₁sq : r₁ * r₁ = t₁ := by
    rw [hr₁, ht₁, show c⁻¹ * r * c * (c⁻¹ * r * c) = c⁻¹ * (r * r) * c by group, hrr]
  have hty : S.t * y = y * S.t := by
    have : y ∈ centralizer ({S.t} : Set G) := hlr ▸ mul_mem (hLt hl) (hRt hr)
    exact (mem_centralizer_singleton_iff.1 this).symm
  have ht₁C : t₁ ∈ centralizer ({S.t} : Set G) := by
    rw [mem_centralizer_singleton_iff, ← hcy, ht₁]
    calc c⁻¹ * S.t * c * (c⁻¹ * y * c) = c⁻¹ * (S.t * y) * c := by group
      _ = c⁻¹ * (y * S.t) * c := by rw [hty]
      _ = c⁻¹ * y * c * (c⁻¹ * S.t * c) := by group
  have key : ∀ x ∈ L, x * t₁ = t₁ * x → x * r₁ = r₁ * x := by
    intro x hx hxt
    have hx' : c * x * c⁻¹ ∈ centralizer ({S.t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc c * x * c⁻¹ * S.t = c * (x * t₁) * c⁻¹ := by rw [ht₁]; group
        _ = c * (t₁ * x) * c⁻¹ := by rw [hxt]
        _ = S.t * (c * x * c⁻¹) := by rw [ht₁]; group
    exact seitz_commute_of_unique_involution (fun m hm => mem_centralizer_iff.1 htR m hm)
      (fun k hk hk2 => S.eq_one_or_eq_t hk hk2) hl hr (hlr.trans hc.symm) hrr ht₁L
      (fun m hm => S.conj_mem_L hr₁t hm) hx hxt (fun k hk => S.conj_mem_R hx' hk)
  set α := S.act ⟨r₁, hr₁t⟩ with hα
  have hαt : α * α = S.act ⟨t₁, ht₁C⟩ := by
    rw [hα, ← map_mul]
    congr 1
    exact Subtype.ext hr₁sq
  have ht₁LR : t₁ ∈ L ⊔ centralizer (L : Set G) := by
    have h := mul_self_mem_inner S.card_field α
    rw [hαt] at h
    exact (S.act_mem_inner_iff _).1 h
  obtain ⟨l', hl', r', hr', hlr'⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm ht₁LR
  have hr'L : r' ∉ L := fun h => ht₁L (hlr' ▸ mul_mem hl' h)
  have ht₁2 : t₁ * t₁ = 1 := by
    rw [ht₁, show c⁻¹ * S.t * c * (c⁻¹ * S.t * c) = c⁻¹ * (S.t * S.t) * c by group, S.t_mul_t,
      mul_one, inv_mul_cancel]
  obtain ⟨hl'2, -⟩ := S.sq_eq_t_of_mul hl' hr' hr'L (by rw [hlr']; exact ht₁2)
  let lL : L := ⟨l', hl'⟩
  have hlL2 : lL * lL = S.tL := Subtype.ext hl'2
  have hπl : S.π lL ≠ 1 := fun h => by
    rcases (S.π_eq_one_iff_tL lL).1 h with h | h
    · rw [h, mul_one] at hlL2; exact S.tL_ne_one hlL2.symm
    · rw [h] at hlL2
      exact S.tL_ne_one (by rw [← hlL2]; exact Subtype.ext S.t_mul_t)
  have hπl2 : orderOf (S.π lL) = 2 :=
    orderOf_eq_prime (by rw [sq, ← map_mul, hlL2, (S.π_eq_one_iff_tL _).2 (Or.inr rfl)]) hπl
  have hb : IsConj (S.π lL) (rootX rootV 1) := by
    rcases even_G2_involutions_conjugate_to_root_elements K (ringChar.eq K 2) _ hπl2 with h | h
    · exfalso
      have h' := S.sq_eq_one_of_isConj_c h
      rw [hlL2] at h'
      exact S.tL_ne_one h'
    · exact h
  obtain ⟨k, hk⟩ := isConj_iff.1 hb.symm
  have hl't : l' * t₁ = t₁ * l' := by
    calc l' * t₁ = l' * (l' * r') := by rw [hlr']
      _ = l' * (r' * l') := by rw [Setup.commute_L_R hl' hr']
      _ = t₁ * l' := by rw [← hlr']; group
  have hαb : α (S.π lL) = S.π lL := by
    have hm : r₁ * l' * r₁⁻¹ ∈ L := S.conj_mem_L hr₁t hl'
    rw [hα, S.act_π ⟨r₁, hr₁t⟩ lL hm]
    congr 1
    exact Subtype.ext (by
      change r₁ * l' * r₁⁻¹ = l'
      rw [← key l' hl' hl't, mul_inv_cancel_right])
  set Λ := ((rankOneA K).map (MulAut.conj k).toMonoidHom).comap S.π with hΛ
  have hΛcent : (rankOneA K).map (MulAut.conj k).toMonoidHom ≤ centralizer {S.π lL} := by
    rw [← hk, Setup.centralizer_conj]
    exact map_mono rankOneA_le_centralizer
  have hΛ' : ⁅Λ, Λ⁆ ≤ centralizer {lL} := by
    refine le_trans (commutator_mono (comap_mono hΛcent) (comap_mono hΛcent)) ?_
    exact commutator_comap_le_centralizer S.ker_le_center lL
  have hΛmap : ⁅Λ, Λ⁆.map S.π = (rankOneA K).map (MulAut.conj k).toMonoidHom := by
    rw [map_commutator, hΛ, map_comap_eq_self_of_surjective S.π_surjective, ← map_commutator,
      commutator_rankOneA S.card_field]
  have hαL : ∀ q ∈ (rankOneA K).map (MulAut.conj k).toMonoidHom, α q = q := by
    intro q hq
    rw [← hΛmap] at hq
    obtain ⟨m, hm, rfl⟩ := hq
    have hml : (m : G) * l' = l' * m :=
      congrArg Subtype.val (mem_centralizer_singleton_iff.1 (hΛ' hm))
    have hmt : (m : G) * t₁ = t₁ * m := by
      calc (m : G) * t₁ = (m : G) * l' * r' := by rw [← hlr', mul_assoc]
        _ = l' * m * r' := by rw [hml]
        _ = l' * (r' * m) := by rw [mul_assoc, Setup.commute_L_R m.2 hr']
        _ = t₁ * m := by rw [← hlr']; group
    have hmr := key m m.2 hmt
    have hm' : r₁ * m * r₁⁻¹ ∈ L := S.conj_mem_L hr₁t m.2
    rw [hα, S.act_π ⟨r₁, hr₁t⟩ m hm']
    congr 1
    exact Subtype.ext (by
      change r₁ * m * r₁⁻¹ = m
      rw [← hmr, mul_inv_cancel_right])
  have hα2 : α * α = 1 := by
    set α' := (MulAut.conj k)⁻¹ * α * MulAut.conj k with hα'
    have hv : α' (rootX rootV 1) = rootX rootV 1 := by
      change k⁻¹ * α (k * rootX rootV 1 * k⁻¹) * k = rootX rootV 1
      rw [hk, hαb, ← hk]
      group
    have hL' : ∀ l ∈ rankOneA K, α' l = l := by
      intro l hl
      change k⁻¹ * α (k * l * k⁻¹) * k = l
      rw [hαL (k * l * k⁻¹) ⟨l, hl, rfl⟩]
      group
    have h := mul_self_eq_one_of_fix S.card_field hv hL'
    rw [hα'] at h
    calc α * α = MulAut.conj k * ((MulAut.conj k)⁻¹ * α * MulAut.conj k *
          ((MulAut.conj k)⁻¹ * α * MulAut.conj k)) * (MulAut.conj k)⁻¹ := by group
      _ = 1 := by rw [h, mul_one, mul_inv_cancel]
  rw [hα2, eq_comm, S.act_eq_one_iff] at hαt
  apply ht₁t
  exact huniq t₁ hαt (orderOf_eq_prime (by rw [sq, ht₁2]) (fun h => S.t_ne_one (by
    rw [show S.t = c * t₁ * c⁻¹ by rw [ht₁]; group, h, mul_one, mul_inv_cancel])))

end SeitzSetup

end CFSG.EvenSmallLie.GTwoFour
