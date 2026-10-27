module

public import CFSG.CGT.Foote81L6.Lemma11
public import CFSG.CGT.Foote81L6.Normalizer.GroupAux
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.PLengthLemmas

public section

namespace CFSG.CGT.Foote81L6

open Subgroup CFSG.Quasithin
open scoped IsMulCommutative

namespace Normalizer.Lemma11Hyp

variable {V X : Type*} [CommGroup V] [Group X] {ρ : X →* MulAut V} {d₀ d₁ x₀ x₁ τ : X}
  {b₀ b₁ : V}

theorem d₀_fix_comm₁ [Finite V] [Finite X] (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) :
    ∀ v ∈ commV (Subgroup.zpowers (ρ x₁)), ρ d₀ v = v := by
  intro v hv
  have hmem : ρ d₀ v ∈ commV (Subgroup.zpowers (ρ x₁)) := commV_zpowers_invariant (by
    rw [← map_mul, ← map_mul, h.comm₀₁]) hv
  rcases h.tv₀.2 v with h1 | h1
  · exact h1
  · exfalso
    have hc : b₀ ∈ commV (Subgroup.zpowers (ρ x₀)) ⊓ commV (Subgroup.zpowers (ρ x₁)) := by
      refine mem_inf.2 ⟨h.comm₀_facts.2.1, ?_⟩
      have : b₀ = v⁻¹ * ρ d₀ v := by rw [h1]; group
      rw [this]
      exact mul_mem (inv_mem hv) hmem
    rw [h.comm_inf_comm, mem_bot] at hc
    exact h.tv₀.1 hc

theorem d₁_fix_comm₀ [Finite V] [Finite X] (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) :
    ∀ v ∈ commV (Subgroup.zpowers (ρ x₀)), ρ d₁ v = v := by
  intro v hv
  have hmem : ρ d₁ v ∈ commV (Subgroup.zpowers (ρ x₀)) := commV_zpowers_invariant (by
    rw [← map_mul, ← map_mul, h.comm₁₀]) hv
  rcases h.tv₁.2 v with h1 | h1
  · exact h1
  · exfalso
    have hc : b₁ ∈ commV (Subgroup.zpowers (ρ x₀)) ⊓ commV (Subgroup.zpowers (ρ x₁)) := by
      refine mem_inf.2 ⟨?_, h.comm₁_facts.2.1⟩
      have : b₁ = v⁻¹ * ρ d₁ v := by rw [h1]; group
      rw [this]
      exact mul_mem (inv_mem hv) hmem
    rw [h.comm_inf_comm, mem_bot] at hc
    exact h.tv₁.1 hc

theorem exists_decomp [Finite V] [Finite X] (h : Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁) {y : V}
    (hy₀ : ρ d₀ y = y) (hy₁ : ρ d₁ y = y) :
    ∃ v ∈ fixV (Subgroup.zpowers (ρ x₀)) ⊓ fixV (Subgroup.zpowers (ρ x₁)), ∃ β₀ β₁ : V,
      (β₀ = 1 ∨ β₀ = b₀) ∧ (β₁ = 1 ∨ β₁ = b₁) ∧ y = v * (β₀ * β₁) := by
  have hy : y ∈ (fixV (Subgroup.zpowers (ρ x₀)) ⊓ fixV (Subgroup.zpowers (ρ x₁))) ⊔
      commV (Subgroup.zpowers (ρ x₀)) ⊔ commV (Subgroup.zpowers (ρ x₁)) :=
    h.fix_sup_eq ▸ mem_top y
  obtain ⟨y', hy', u₁, hu₁, rfl⟩ := mem_sup.1 hy
  obtain ⟨v, hv, u₀, hu₀, rfl⟩ := mem_sup.1 hy'
  have hU₀fix : ∀ w ∈ commV (Subgroup.zpowers (ρ x₀)), ρ d₀ w = w → w = 1 ∨ w = b₀ := by
    intro w hw hfix
    by_contra hcon
    push Not at hcon
    have := h.d₀_apply hw hcon.1 hcon.2
    rw [hfix] at this
    exact h.tv₀.1 (mul_left_cancel (this.symm.trans (mul_one w).symm))
  have hU₁fix : ∀ w ∈ commV (Subgroup.zpowers (ρ x₁)), ρ d₁ w = w → w = 1 ∨ w = b₁ := by
    intro w hw hfix
    by_contra hcon
    push Not at hcon
    have := h.d₁_apply hw hcon.1 hcon.2
    rw [hfix] at this
    exact h.tv₁.1 (mul_left_cancel (this.symm.trans (mul_one w).symm))
  have hu₀f : ρ d₀ u₀ = u₀ := by
    rw [map_mul, map_mul, h.d₀_fix v hv, h.d₀_fix_comm₁ u₁ hu₁] at hy₀
    exact mul_left_cancel (mul_right_cancel hy₀)
  have hu₁f : ρ d₁ u₁ = u₁ := by
    rw [map_mul, map_mul, h.d₁_fix v hv, h.d₁_fix_comm₀ u₀ hu₀] at hy₁
    exact mul_left_cancel hy₁
  exact ⟨v, hv, u₀, u₁, hU₀fix u₀ hu₀ hu₀f, hU₁fix u₁ hu₁ hu₁f, by rw [mul_assoc]⟩

end Normalizer.Lemma11Hyp

section OddCent

variable {G : Type*} [Group G]

@[expose] def oddCent (F : Subgroup G) : Subgroup G where
  carrier := {v | v ∈ F ∧ ∀ k ∈ normalizer (F : Set G), Odd (orderOf k) → k * v * k⁻¹ = v}
  one_mem' := ⟨one_mem F, fun k _ _ => by group⟩
  mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, fun k hk hko => by
    calc k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) := by group
      _ = x * y := by rw [hx.2 k hk hko, hy.2 k hk hko]⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, fun k hk hko => by
    calc k * x⁻¹ * k⁻¹ = (k * x * k⁻¹)⁻¹ := by group
      _ = x⁻¹ := by rw [hx.2 k hk hko]⟩

theorem mem_oddCent {F : Subgroup G} {v : G} :
    v ∈ oddCent F ↔ v ∈ F ∧ ∀ k ∈ normalizer (F : Set G), Odd (orderOf k) → k * v * k⁻¹ = v :=
  Iff.rfl

private theorem mem_map_conj {F : Subgroup G} {g y : G} :
    y ∈ F.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ F := by
  rw [mem_map_equiv, MulAut.conj_symm_apply]

private theorem oddCent_map_conj_le (F : Subgroup G) (g : G) :
    (oddCent F).map (MulAut.conj g).toMonoidHom ≤
      oddCent (F.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨hvF, hvc⟩ := mem_oddCent.1 hv
  have hconj : (MulAut.conj g).toMonoidHom v = g * v * g⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hconj, mem_oddCent]
  refine ⟨mem_map_conj.2 (by group; exact hvF), fun k hk hko => ?_⟩
  have hk' : g⁻¹ * k * g ∈ normalizer (F : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    have h1 := (mem_normalizer_iff.1 hk) (g * x * g⁻¹)
    rw [mem_map_conj, mem_map_conj] at h1
    constructor
    · intro hx
      have := h1.1 (by group; exact hx)
      convert this using 1
      group
    · intro hx
      have := h1.2 (by convert hx using 1; group)
      convert this using 1
      group
  have hko' : Odd (orderOf (g⁻¹ * k * g)) := by
    rw [← SemiconjBy.orderOf_eq g⁻¹
      (by simp [SemiconjBy, mul_assoc] : SemiconjBy g⁻¹ k (g⁻¹ * k * g))]
    exact hko
  have := hvc _ hk' hko'
  calc k * (g * v * g⁻¹) * k⁻¹ = g * ((g⁻¹ * k * g) * v * (g⁻¹ * k * g)⁻¹) * g⁻¹ := by group
    _ = g * v * g⁻¹ := by rw [this]

theorem oddCent_map_conj (F : Subgroup G) (g : G) :
    oddCent (F.map (MulAut.conj g).toMonoidHom) =
      (oddCent F).map (MulAut.conj g).toMonoidHom := by
  refine le_antisymm ?_ (oddCent_map_conj_le F g)
  have h1 := oddCent_map_conj_le (F.map (MulAut.conj g).toMonoidHom) g⁻¹
  have hF : (F.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = F := by
    ext x
    rw [mem_map_conj, mem_map_conj]
    constructor <;> intro hx <;> convert hx using 1 <;> group
  rw [hF] at h1
  intro x hx
  have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ oddCent F := h1 ⟨x, hx, by simp [MulAut.conj_apply]⟩
  exact ⟨_, hx', by simp [MulAut.conj_apply, mul_assoc]⟩

theorem mem_oddCent_iff [Finite G] {F : Subgroup G} (hnc : HasNormalPComplement 2 (NBar.Q F))
    (v : ↥F) :
    (v : G) ∈ oddCent F ↔ ∀ o ∈ pPrimeCore 2 (NBar.Q F), NBar.ρ F o v = v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · rintro ⟨-, hv⟩ o ho
    obtain ⟨k₀, rfl⟩ := NBar.π_surjective F o
    have hoodd : Odd (orderOf (NBar.π F k₀)) := Normalizer.odd_orderOf_of_mem_pPrimeCore ho
    obtain ⟨a, M, hM, hk₀⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k₀).ne'
    have hk₁ : orderOf (k₀ ^ (2 ^ a)) = M := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨M, hk₀⟩, hk₀,
        Nat.mul_div_cancel_left _ (by positivity)]
    have hcop : Nat.Coprime (2 ^ a) (orderOf (NBar.π F k₀)) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hoodd)
    obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
    have hkodd : Odd (orderOf ((k₀ ^ (2 ^ a)) ^ j)) :=
      Odd.of_dvd_nat hM (by rw [← hk₁]; exact orderOf_pow_dvd j)
    have hπk : NBar.π F ((k₀ ^ (2 ^ a)) ^ j) = NBar.π F k₀ := by rw [map_pow, map_pow, hj]
    rw [← hπk]
    apply Subtype.ext
    rw [NBar.ρ_π]
    exact hv _ ((k₀ ^ (2 ^ a)) ^ j).2 (by rwa [Subgroup.orderOf_coe])
  · intro hv
    refine ⟨v.2, fun k hk hko => ?_⟩
    have hq := CFSG.isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 2 (NBar.Q F) hnc
    have hodd : Odd (orderOf (NBar.π F ⟨k, hk⟩)) := by
      refine Odd.of_dvd_nat (n := orderOf k) hko ?_
      rw [← Subgroup.orderOf_mk k hk]
      exact orderOf_map_dvd _ _
    have hmem : NBar.π F ⟨k, hk⟩ ∈ pPrimeCore 2 (NBar.Q F) := by
      rw [← QuotientGroup.eq_one_iff]
      obtain ⟨i, hi⟩ := hq (QuotientGroup.mk (NBar.π F ⟨k, hk⟩))
      have h1 : orderOf (QuotientGroup.mk (NBar.π F ⟨k, hk⟩) :
          NBar.Q F ⧸ pPrimeCore 2 (NBar.Q F)) ∣ 2 ^ i := orderOf_dvd_of_pow_eq_one hi
      have h2 : Odd (orderOf (QuotientGroup.mk (NBar.π F ⟨k, hk⟩) :
          NBar.Q F ⧸ pPrimeCore 2 (NBar.Q F))) :=
        Odd.of_dvd_nat hodd (orderOf_map_dvd (QuotientGroup.mk' _) _)
      obtain ⟨l, hl, hleq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
      rcases l with _ | l
      · rwa [pow_zero, orderOf_eq_one_iff] at hleq
      · rw [hleq] at h2
        exact absurd h2 (by rw [Nat.not_odd_iff_even]; exact (Nat.even_pow.2 ⟨even_two, by omega⟩))
    have := congrArg Subtype.val (hv _ hmem)
    rwa [NBar.ρ_π] at this

end OddCent

namespace FooteCore

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {n : ℕ}
  (D : FooteCore G (T : Subgroup G) 2 n)

theorem final_core (hcen : D.a ∈ center G)
    {F : Subgroup G} (hF : IsE64 (T : Subgroup G) F) [IsMulCommutative ↥F]
    {d₀ d₁ t' : G} (hd₀B₀ : d₀ ∈ D.B₀) (hd₀N : d₀ ∈ normalizer (F : Set G))
    (hd₁B₁ : d₁ ∈ D.B₁) (hd₁N : d₁ ∈ normalizer (F : Set G))
    (ht'N : t' ∈ normalizer (F : Set G)) (ht'T₁ : t' * D.t⁻¹ ∈ D.T₁) {x₀ x₁ : NBar.Q F}
    (h : Normalizer.Lemma11Hyp (NBar.ρ F) (NBar.π F ⟨d₀, hd₀N⟩) (NBar.π F ⟨d₁, hd₁N⟩) x₀ x₁
      (NBar.π F ⟨t', ht'N⟩) ⟨D.b₀, D.b₀_mem_E64 hF⟩ ⟨D.b₁, D.b₁_mem_E64 hF⟩)
    {a₁ : G} (ha₁ : a₁ ∈ D.A) (ha₁1 : a₁ ≠ 1) (ha₁a : a₁ ≠ D.a)
    (hmove : NBar.ρ F x₀ ⟨a₁, D.A_le_E64 rfl hF ha₁⟩ ≠ ⟨a₁, D.A_le_E64 rfl hF ha₁⟩) :
    (fixV (zpowers (NBar.ρ F x₀)) ⊓ fixV (zpowers (NBar.ρ F x₁))).map F.subtype = D.Astar := by
  classical
  have hF2 := hF.mul_self
  have hAF : D.A ≤ F := D.A_le_E64 rfl hF
  have haF : D.a ∈ F := hAF D.a_mem
  have hb₀F : D.b₀ ∈ F := D.b₀_mem_E64 hF
  have hb₁F : D.b₁ ∈ F := D.b₁_mem_E64 hF
  have hval : ∀ (gN : ↥(normalizer (F : Set G))) (v : ↥F),
      ((NBar.ρ F (NBar.π F gN) v : ↥F) : G) = gN * v * (gN : G)⁻¹ := NBar.ρ_π F
  have hV : ∀ v : ↥F, v * v = 1 := fun v => Subtype.ext (hF2 v v.2)
  have hinv : ∀ v : ↥F, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hV v)
  obtain ⟨ht'b₀, ht'b₁, ht'A⟩ := D.conj_of_mem_T₁t ht'T₁
  set w : ↥F := ⟨D.a, haF⟩ with hw_def
  set c₀ : ↥F := ⟨D.b₀, hb₀F⟩ with hc₀_def
  set c₁ : ↥F := ⟨D.b₁, hb₁F⟩ with hc₁_def
  set ya : ↥F := ⟨a₁, hAF ha₁⟩ with hya_def
  set τb := NBar.π F ⟨t', ht'N⟩ with hτb_def
  set A₁ := fixV (zpowers (NBar.ρ F x₀)) ⊓ fixV (zpowers (NBar.ρ F x₁)) with hA₁_def
  have hc₀c₁ : c₀ ≠ c₁ := fun h' => D.b₀_ne_b₁ (congrArg Subtype.val h')
  have hwfix : ∀ g : NBar.Q F, NBar.ρ F g w = w := by
    intro g
    obtain ⟨gN, rfl⟩ := NBar.π_surjective F g
    apply Subtype.ext
    rw [hval]
    show (gN : G) * D.a * (gN : G)⁻¹ = D.a
    rw [mem_center_iff.1 hcen, mul_inv_cancel_right]
  have hwA₁ : w ∈ A₁ := by
    refine mem_inf.2 ⟨fun y hy => ?_, fun y hy => ?_⟩
    · obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
      rw [← map_zpow]
      exact hwfix _
    · obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
      rw [← map_zpow]
      exact hwfix _
  have hBA : ∀ {β x : G}, β ∈ D.B → x ∈ D.A → β * x * β⁻¹ = x := fun hβ hx => by
    rw [← D.A_comm_B _ hx _ hβ, mul_inv_cancel_right]
  have hd₀y : NBar.ρ F (NBar.π F ⟨d₀, hd₀N⟩) ya = ya :=
    Subtype.ext (by rw [hval]; exact hBA (D.B₀_le_B hd₀B₀) ha₁)
  have hd₁y : NBar.ρ F (NBar.π F ⟨d₁, hd₁N⟩) ya = ya :=
    Subtype.ext (by rw [hval]; exact hBA (D.B₁_le_B hd₁B₁) ha₁)
  have hτy : NBar.ρ F τb ya = w * ya := Subtype.ext (by rw [hval]; exact ht'A ha₁ ha₁1 ha₁a)
  have hτw : NBar.ρ F τb w = w := hwfix τb
  have hτc₀ : NBar.ρ F τb c₀ = c₁ := Subtype.ext (by rw [hval]; exact ht'b₀)
  have hτc₁ : NBar.ρ F τb c₁ = c₀ := Subtype.ext (by rw [hval]; exact ht'b₁)
  have hA₁B : A₁ ⊓ closure ({c₀, c₁} : Set ↥F) = ⊥ := h.fix_inf_closure_eq
  have hτA₁ : ∀ v ∈ A₁, NBar.ρ F τb v ∈ A₁ := h.fix_invariant τb
  obtain ⟨v₁, hv₁A₁, β₀, β₁, hβ₀, hβ₁, hyv⟩ := h.exists_decomp hd₀y hd₁y
  have hv₁eq : v₁ = ya * (β₀ * β₁)⁻¹ := by rw [hyv]; group
  have hmemB : β₀ * β₁ ∈ closure ({c₀, c₁} : Set ↥F) := by
    refine mul_mem ?_ ?_
    · rcases hβ₀ with rfl | rfl
      · exact one_mem _
      · exact subset_closure (Set.mem_insert _ _)
    · rcases hβ₁ with rfl | rfl
      · exact one_mem _
      · exact subset_closure (Set.mem_insert_of_mem _ rfl)
  have hτmemB : NBar.ρ F τb (β₀ * β₁) ∈ closure ({c₀, c₁} : Set ↥F) := by
    rw [map_mul]
    refine mul_mem ?_ ?_
    · rcases hβ₀ with rfl | rfl
      · rw [map_one]; exact one_mem _
      · rw [hτc₀]; exact subset_closure (Set.mem_insert_of_mem _ rfl)
    · rcases hβ₁ with rfl | rfl
      · rw [map_one]; exact one_mem _
      · rw [hτc₁]; exact subset_closure (Set.mem_insert _ _)
  have hfixβ : NBar.ρ F τb (β₀ * β₁) = β₀ * β₁ := by
    set γ := β₀ * β₁
    have hτv : NBar.ρ F τb v₁ = ya * (w * (NBar.ρ F τb γ)⁻¹) := by
      rw [hv₁eq, map_mul, map_inv, hτy, mul_comm w ya, mul_assoc]
    have hm : w⁻¹ * (v₁⁻¹ * NBar.ρ F τb v₁) ∈ A₁ :=
      mul_mem (inv_mem hwA₁) (mul_mem (inv_mem hv₁A₁) (hτA₁ v₁ hv₁A₁))
    have he : w⁻¹ * (v₁⁻¹ * NBar.ρ F τb v₁) = γ * (NBar.ρ F τb γ)⁻¹ := by
      rw [hτv, hv₁eq]
      calc w⁻¹ * ((ya * γ⁻¹)⁻¹ * (ya * (w * (NBar.ρ F τb γ)⁻¹)))
          = w⁻¹ * (γ * w * (NBar.ρ F τb γ)⁻¹) := by group
        _ = γ * (NBar.ρ F τb γ)⁻¹ := by rw [mul_comm γ w]; group
    rw [he] at hm
    have h1 : γ * (NBar.ρ F τb γ)⁻¹ ∈ A₁ ⊓ closure ({c₀, c₁} : Set ↥F) :=
      mem_inf.2 ⟨hm, mul_mem hmemB (inv_mem hτmemB)⟩
    rw [hA₁B, mem_bot] at h1
    exact (mul_inv_eq_one.1 h1).symm
  have hβ : β₀ = c₀ ∧ β₁ = c₁ := by
    rcases hβ₀ with rfl | rfl <;> rcases hβ₁ with rfl | rfl
    · exfalso
      apply hmove
      have hv' : v₁ = ya := by rw [hv₁eq]; group
      have hfx : NBar.ρ F x₀ v₁ = v₁ := (mem_inf.1 hv₁A₁).1 _ (mem_zpowers _)
      rw [hv'] at hfx
      exact hfx
    · exfalso
      rw [one_mul, hτc₁] at hfixβ
      exact hc₀c₁ hfixβ
    · exfalso
      rw [mul_one, hτc₀] at hfixβ
      exact hc₀c₁ hfixβ.symm
    · exact ⟨rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := hβ
  have hv₁val : (v₁ : G) = a₁ * D.b := by
    rw [hv₁eq]
    show a₁ * (D.b₀ * D.b₁)⁻¹ = a₁ * (D.b₀ * D.b₁)
    have hbb : (D.b₀ * D.b₁) * (D.b₀ * D.b₁) = 1 := D.b_mul_b
    rw [inv_eq_of_mul_eq_one_right hbb]
  have hle : D.Astar ≤ A₁.map F.subtype := by
    rw [FooteCore.Astar, closure_le]
    rintro _ ⟨x, hx, hx2, hxa, rfl⟩
    have hx1 : x ≠ 1 := fun h' => by rw [h', orderOf_one] at hx2; exact absurd hx2 (by decide)
    rcases D.mem_A_of_two ha₁ ha₁1 ha₁a hx with h' | h' | h' | h'
    · exact absurd h' hx1
    · exact absurd h' hxa
    · exact ⟨v₁, hv₁A₁, by rw [h']; exact hv₁val⟩
    · refine ⟨w * v₁, mul_mem hwA₁ hv₁A₁, ?_⟩
      rw [h']
      show D.a * (v₁ : G) = D.a * a₁ * D.b
      rw [hv₁val, mul_assoc]
  haveI : Finite ↥(A₁.map F.subtype) := inferInstance
  have hcard : Nat.card ↥(A₁.map F.subtype) = Nat.card ↥D.Astar := by
    rw [Subgroup.card_map_of_injective F.subtype_injective, h.card_fix]
    have := D.star.card_A
    rw [star_A] at this
    rw [this]
    norm_num
  exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm

end FooteCore

end CFSG.CGT.Foote81L6
