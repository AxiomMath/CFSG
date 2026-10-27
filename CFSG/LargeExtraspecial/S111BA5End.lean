module

public import CFSG.LargeExtraspecial.S111BA5Tv
public import CFSG.LargeExtraspecial.S111BTI

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G}
  {h k k' : G}

omit [Finite G] in
theorem inv_mul_conj_mem_ker {Y K : Type*} [Group Y] [Group K] (φ : Y →* K) {a y b : Y}
    (h : φ a = φ y * φ b * (φ y)⁻¹) : a⁻¹ * (y * b * y⁻¹) ∈ φ.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, h, inv_mul_cancel]

omit [Finite G] in
theorem conj_eq_of_inv_mul_conj_mem_ker {Y K : Type*} [Group Y] [Group K] (φ : Y →* K)
    {a y : Y} (h : a⁻¹ * (y * a * y⁻¹) ∈ φ.ker) : φ y * φ a * (φ y)⁻¹ = φ a := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, inv_mul_eq_one] at h
  exact h.symm

namespace Pair111

variable (P : Pair111 S g A h k k')
  {φ : ↥(S.Lbar k ⊔ S.Lbar k') →* alternatingGroup (Fin 5)}
include P

theorem conj_mem_normalizer_of_conj_mem_range
    (hO : φ.ker = (O2Sub (S.Lbar k ⊔ S.Lbar k')).subgroupOf (S.Lbar k ⊔ S.Lbar k'))
    {y : ↥(S.Lbar k ⊔ S.Lbar k')}
    (hcT : ∀ t ∈ (φ.comp (inclusion (le_sup_left : S.Lbar k ≤ S.Lbar k ⊔ S.Lbar k'))).range,
      φ y * t * (φ y)⁻¹ ∈
        (φ.comp (inclusion (le_sup_left : S.Lbar k ≤ S.Lbar k ⊔ S.Lbar k'))).range)
    {l : S.O} (hl : l ∈ S.Lbar k) :
    (y : S.O) * l * (y : S.O)⁻¹ ∈ normalizer (S.Lbar k : Set S.O) := by
  have hlX : l ∈ S.Lbar k ⊔ S.Lbar k' := mem_sup_left hl
  obtain ⟨l', hl'⟩ := hcT (φ ⟨l, hlX⟩) ⟨⟨l, hl⟩, rfl⟩
  have hker : (inclusion (le_sup_left : S.Lbar k ≤ S.Lbar k ⊔ S.Lbar k') l')⁻¹ *
      (y * ⟨l, hlX⟩ * y⁻¹) ∈ φ.ker := by
    rw [MonoidHom.comp_apply] at hl'
    exact inv_mul_conj_mem_ker φ hl'
  rw [hO, mem_subgroupOf] at hker
  have e : (y : S.O) * l * (y : S.O)⁻¹ = (l' : S.O) *
      (((inclusion (le_sup_left : S.Lbar k ≤ S.Lbar k ⊔ S.Lbar k') l')⁻¹ *
        (y * ⟨l, hlX⟩ * y⁻¹) : ↥(S.Lbar k ⊔ S.Lbar k')) : S.O) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, mul_inv_cancel_left,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
  rw [e]
  exact mul_mem (le_normalizer l'.2)
    (O2Sub_le_normalizer_Lbar P.hy.hyp4 P.hy.cons le_sup_left (Lbar_sup_le_Mbar S k k') hker)

theorem mem_normalizer_Kbar {y : S.O} (hyX : y ∈ S.Lbar k ⊔ S.Lbar k')
    (hyN : y ∈ normalizer (S.Lbar k : Set S.O)) : y ∈ normalizer (Kbar S A k : Set S.O) := by
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp ((Lbar_sup_le_Mbar S k k') hyX)
  have hfix := fix_of_mem_normalizer P.hy.hyp4 hyN
  rw [S.ρ_cl m P.memQ] at hfix
  have hmα : (m : G) * (k * S.z * k⁻¹) * (m : G)⁻¹ ∈ A := by
    rcases (S.cl_eq_cl_iff P.memQ (S.conj_mem_QG m.2 P.memQ)).mp hfix.symm with e | e
    · rw [e]; exact P.mem
    · rw [e]; exact mul_mem P.mem P.cfg.inc.z_mem
  exact mem_normalizer_inf hyN
    (mem_normalizer_ptFix_clSub (P.cfg.map_eq_of_conj_mem m.2 P.mem P.ne hmα))

theorem inv_mul_conj_mem_Ebar (hE : Ebar S k k' ≤ ptFix S (S.clSub A))
    (hK2 : Nat.card (Kbar S A k) = 2 * Nat.card (Ebar S k k')) {y : S.O}
    (hyX : y ∈ S.Lbar k ⊔ S.Lbar k') (hyK : y ∈ normalizer (Kbar S A k : Set S.O)) {k₀ : S.O}
    (hk₀K : k₀ ∈ Kbar S A k) (hk₀E : k₀ ∉ Ebar S k k') :
    k₀⁻¹ * (y * k₀ * y⁻¹) ∈ Ebar S k k' := by
  have hEK : Ebar S k k' ≤ Kbar S A k := fun e he => ⟨he.1, hE he⟩
  have hE0 : 0 < Nat.card (Ebar S k k') := Nat.card_pos
  have hyk₀ : y * k₀ * y⁻¹ ∈ Kbar S A k := (mem_normalizer_iff.mp hyK k₀).mp hk₀K
  have hyk₀E : y * k₀ * y⁻¹ ∉ Ebar S k k' := by
    intro hmem
    rw [← P.inf_O2Sub_eq] at hmem
    have h1 := O2Sub_normal (inv_mem hyX) hmem.2
    rw [show y⁻¹ * (y * k₀ * y⁻¹) * y⁻¹⁻¹ = k₀ by group] at h1
    rw [← P.inf_O2Sub_eq] at hk₀E
    exact hk₀E ⟨hk₀K.1, h1⟩
  have hI : ((Ebar S k k').subgroupOf (Kbar S A k)).index = 2 := by
    have h1 := ((Ebar S k k').subgroupOf (Kbar S A k)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv, hK2] at h1
    exact Nat.eq_of_mul_eq_mul_left hE0 (h1.trans (mul_comm _ _))
  have := (mul_mem_iff_of_index_two hI (a := ⟨k₀⁻¹, inv_mem hk₀K⟩)
    (b := ⟨_, hyk₀⟩)).mpr ⟨fun ha => (hk₀E (by simpa using inv_mem (mem_subgroupOf.mp ha))).elim,
      fun hb => (hyk₀E (mem_subgroupOf.mp hb)).elim⟩
  exact mem_subgroupOf.mp this

theorem false_of_finrank_two (hφs : Function.Surjective φ)
    (hφk : φ.ker = CFSG.pCore 2 ↥(S.Lbar k ⊔ S.Lbar k'))
    (hidx : 4 * Nat.card (Ebar S k k') ≤ Nat.card (S.Lbar k))
    (hE : Ebar S k k' ≤ ptFix S (S.clSub A)) (hr : finrank (ZMod 2) (S.clSub A) = 2) :
    False := by
  have hO : φ.ker = (O2Sub (S.Lbar k ⊔ S.Lbar k')).subgroupOf (S.Lbar k ⊔ S.Lbar k') :=
    hφk.trans (subgroupOf_O2Sub _).symm
  have hL4 := P.card_Lbar_eq_of_A5 hφk hidx
  have hLK := P.card_Lbar_eq_card_Kbar_mul
  rw [hr] at hLK
  have hE0 : 0 < Nat.card (Ebar S k k') := Nat.card_pos
  have hK2 : Nat.card (Kbar S A k) = 2 * Nat.card (Ebar S k k') := by
    norm_num at hLK
    omega
  have hT : Nat.card (φ.comp (inclusion (le_sup_left :
      S.Lbar k ≤ S.Lbar k ⊔ S.Lbar k'))).range = 4 := by
    have h1 := card_eq_card_inf_mul_card_range le_sup_left φ hO
    rw [P.inf_O2Sub_eq, hL4] at h1
    exact Nat.eq_of_mul_eq_mul_left hE0 (h1.symm.trans (mul_comm _ _))
  obtain ⟨c, hcT, hcfix⟩ := exists_conj_fixfree_alternating hT
  obtain ⟨y, rfl⟩ := hφs c
  have hyN : (y : S.O) ∈ normalizer (S.Lbar k : Set S.O) :=
    mem_normalizer_of_map_conj_eq (P.map_conj_eq_of_conj_mem y.2 fun l hl l₂ hl₂ =>
      mem_sup_left ((mem_normalizer_iff.mp
        (P.conj_mem_normalizer_of_conj_mem_range hO hcT hl) l₂).mp hl₂))
  have hyK := P.mem_normalizer_Kbar y.2 hyN
  obtain ⟨k₀, hk₀K, hk₀E⟩ : ∃ x ∈ Kbar S A k, x ∉ Ebar S k k' := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show Kbar S A k ≤ Ebar S k k' from hcon)
    omega
  have hprod := P.inv_mul_conj_mem_Ebar hE hK2 y.2 hyK hk₀K hk₀E
  rw [← P.inf_O2Sub_eq] at hprod hk₀E
  have hk₀X : k₀ ∈ S.Lbar k ⊔ S.Lbar k' := mem_sup_left hk₀K.1
  have hk1 : (⟨k₀, hk₀X⟩ : ↥(S.Lbar k ⊔ S.Lbar k'))⁻¹ * (y * ⟨k₀, hk₀X⟩ * y⁻¹) ∈ φ.ker := by
    rw [hO, mem_subgroupOf]
    exact hprod.2
  have hk₀1 := hcfix (φ ⟨k₀, hk₀X⟩) ⟨⟨k₀, hk₀K.1⟩, rfl⟩
    (conj_eq_of_inv_mul_conj_mem_ker φ hk1)
  have hmem : (⟨k₀, hk₀X⟩ : ↥(S.Lbar k ⊔ S.Lbar k')) ∈ φ.ker := hk₀1
  rw [hO, mem_subgroupOf] at hmem
  exact hk₀E ⟨hk₀K.1, hmem⟩

theorem false_of_A5 (hφs : Function.Surjective φ)
    (hφk : φ.ker = CFSG.pCore 2 ↥(S.Lbar k ⊔ S.Lbar k'))
    (hidx : 4 * Nat.card (Ebar S k k') ≤ Nat.card (S.Lbar k)) : False := by
  have hL4 := P.card_Lbar_eq_of_A5 hφk hidx
  have hL4' := P.card_Lbar_eq_of_A5' hφk hidx
  have hr2 := P.two_le_finrank_clSub
  have hrh := P.finrank_clSub_map
  have hsum := P.finrank_add_finrank_le hφs hφk hidx
  have hW := P.finrank_W_eq hL4
  have hW' := P.swap.finrank_W_eq hL4'
  have hWeq : Ebar S k k' ≤ ptFix S (S.clSub A) →
      finrank (ZMod 2) ↥(S.clSub A ⊓ fixSub S (Ebar S k k')) =
        finrank (ZMod 2) (S.clSub A) := fun hE => by
    rw [inf_eq_left.mpr fun v hv => (mem_fixSub S).mpr fun e he => mem_ptFix.mp (hE he) v hv]
  have hW'eq : Ebar S k' k ≤ ptFix S (S.clSub (A.map (MulAut.conj h).toMonoidHom)) →
      finrank (ZMod 2) ↥(S.clSub (A.map (MulAut.conj h).toMonoidHom) ⊓ fixSub S (Ebar S k' k)) =
        finrank (ZMod 2) (S.clSub (A.map (MulAut.conj h).toMonoidHom)) := fun hF => by
    rw [inf_eq_left.mpr fun v hv => (mem_fixSub S).mpr fun f hf => mem_ptFix.mp (hF hf) v hv]
  rcases hW with ⟨h3, -⟩ | hE <;> rcases hW' with ⟨h3', -⟩ | hF
  · omega
  · have := hW'eq hF
    omega
  · have := hWeq hE
    omega
  · have h1 := hWeq hE
    have h2 := hW'eq hF
    exact P.false_of_finrank_two hφs hφk hidx hE (by omega)

end Pair111

end CFSG.LargeExtraspecial.S11
