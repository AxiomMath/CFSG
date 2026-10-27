module

public import CFSG.CGT.Timmesfeld75.Sec3L2
public import CFSG.CGT.Timmesfeld75.L2Real
public import CFSG.CGT.Timmesfeld75.Sec215Local

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

section Algebra

variable {G : Type*} [Group G]

theorem eq_one_of_conj_mul_eq_of_inf_centralizer {M : Subgroup G} (hM : IsElemAbelian 2 M)
    {a b : G} (haa : a * a = 1) (hbb : b * b = 1) (ha : ∀ m ∈ M, a * m * a⁻¹ ∈ M)
    (hC : M ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) = ⊥)
    {m : G} (hm : m ∈ M) (h : a * b * m * (a * b)⁻¹ = m) : m = 1 := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hτσ : b * m * b⁻¹ = a * m * a⁻¹ := by
    calc b * m * b⁻¹ = a⁻¹ * (a * b * m * (a * b)⁻¹) * a := by group
      _ = a⁻¹ * m * a := by rw [h]
      _ = a * m * a⁻¹ := by rw [ha']
  have hu : a * m * a⁻¹ ∈ M := ha m hm
  have hσσ : a * (a * m * a⁻¹) * a⁻¹ = m := by
    calc a * (a * m * a⁻¹) * a⁻¹ = (a * a) * m * (a * a)⁻¹ := by group
      _ = m := by rw [haa]; group
  have hττ : b * (a * m * a⁻¹) * b⁻¹ = m := by
    rw [← hτσ]
    calc b * (b * m * b⁻¹) * b⁻¹ = (b * b) * m * (b * b)⁻¹ := by group
      _ = m := by rw [hbb]; group
  have hcomm : (a * m * a⁻¹) * m = m * (a * m * a⁻¹) := elemAbelian_mul_comm hM hu hm
  have hnM : m * (a * m * a⁻¹) ∈ M := M.mul_mem hm hu
  have hna : a * (m * (a * m * a⁻¹)) * a⁻¹ = m * (a * m * a⁻¹) := by
    calc a * (m * (a * m * a⁻¹)) * a⁻¹ = (a * m * a⁻¹) * (a * (a * m * a⁻¹) * a⁻¹) := by group
      _ = (a * m * a⁻¹) * m := by rw [hσσ]
      _ = m * (a * m * a⁻¹) := hcomm
  have hnb : b * (m * (a * m * a⁻¹)) * b⁻¹ = m * (a * m * a⁻¹) := by
    calc b * (m * (a * m * a⁻¹)) * b⁻¹ = (b * m * b⁻¹) * (b * (a * m * a⁻¹) * b⁻¹) := by group
      _ = (a * m * a⁻¹) * m := by rw [hτσ, hττ]
      _ = m * (a * m * a⁻¹) := hcomm
  have hn : m * (a * m * a⁻¹) ∈ (⊥ : Subgroup G) := by
    rw [← hC]
    refine ⟨⟨hnM, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · calc m * (a * m * a⁻¹) * a = (a * (m * (a * m * a⁻¹)) * a⁻¹) * a := by rw [hna]
        _ = a * (m * (a * m * a⁻¹)) := by group
    · calc m * (a * m * a⁻¹) * b = (b * (m * (a * m * a⁻¹)) * b⁻¹) * b := by rw [hnb]
        _ = b * (m * (a * m * a⁻¹)) := by group
  rw [Subgroup.mem_bot] at hn
  have hmu : a * m * a⁻¹ = m := by
    have h1 := eq_inv_of_mul_eq_one_right hn
    rw [h1, elemAbelian_inv hM hm]
  have hmC : m ∈ M ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) := by
    refine ⟨⟨hm, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · calc m * a = (a * m * a⁻¹) * a := by rw [hmu]
        _ = a * m := by group
    · calc m * b = (b * m * b⁻¹) * b := by rw [hτσ, hmu]
        _ = b * m := by group
  rwa [hC, Subgroup.mem_bot] at hmC

end Algebra

section Card

variable {G : Type*} [Group G] {T T₁ : Subgroup G}

theorem Cfg.card_cfgM (c : Cfg T T₁) :
    Nat.card (cfgM T T₁) = Nat.card (normIn T T₁) * Nat.card (normIn T₁ T) := by
  let φ : normIn T T₁ × normIn T₁ T → cfgM T T₁ := fun p =>
    ⟨(p.1 : G) * p.2, (cfgM T T₁).mul_mem (Cfg.normIn_le_cfgM_left T T₁ p.1.2)
      (Cfg.normIn_le_cfgM_right T T₁ p.2.2)⟩
  have hinj : Function.Injective φ := by
    rintro ⟨l, x⟩ ⟨l', x'⟩ h
    have h1 : (l : G) * x = l' * x' := congrArg Subtype.val h
    have h2 : (l' : G)⁻¹ * l = x' * (x : G)⁻¹ := by
      calc (l' : G)⁻¹ * l = (l' : G)⁻¹ * (l * x) * (x : G)⁻¹ := by group
        _ = x' * (x : G)⁻¹ := by rw [h1]; group
    have hmem : (l' : G)⁻¹ * l ∈ T ⊓ T₁ :=
      ⟨T.mul_mem (T.inv_mem (normIn_le _ _ l'.2)) (normIn_le _ _ l.2), by
        rw [h2]; exact T₁.mul_mem (normIn_le _ _ x'.2) (T₁.inv_mem (normIn_le _ _ x.2))⟩
    rw [c.inf, Subgroup.mem_bot] at hmem
    have hl : l' = l := Subtype.ext (inv_mul_eq_one.1 hmem)
    have hx : x' = x := Subtype.ext (mul_inv_eq_one.1 (h2 ▸ hmem))
    rw [hl, hx]
  have hsurj : Function.Surjective φ := by
    rintro ⟨m, hm⟩
    obtain ⟨l, hl, x, hx, rfl⟩ := c.mem_cfgM_iff.1 hm
    exact ⟨(⟨l, hl⟩, ⟨x, hx⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)).symm

variable [Finite G]

theorem Sec3.card_cfgM_eq_sq (hS : Sec3 T T₁) :
    Nat.card (cfgM T T₁) = Nat.card (normIn T T₁) ^ 2 := by
  obtain ⟨x, -, hx⟩ := hS.conj
  rw [hS.cfg.card_cfgM, ← hS.cfg.card_normIn_eq ⟨x, hx⟩, pow_two]

theorem Sec3.card_normIn_eq_two_pow (hS : Sec3 T T₁) :
    ∃ n : ℕ, 0 < n ∧ Nat.card (normIn T T₁) = 2 ^ n ∧ Nat.card (normIn T₁ T) = 2 ^ n ∧
      Nat.card (cfgM T T₁) = 2 ^ (2 * n) := by
  obtain ⟨x, -, hx⟩ := hS.conj
  have hL : IsPGroup 2 (normIn T T₁) :=
    (isPGroup_two_of_isElemAbelian hS.cfg.wc.1).to_le (normIn_le T T₁)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hL
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0, pow_zero, Subgroup.card_eq_one] at hn
      exact hS.cfg.ne hn
    · exact h0
  refine ⟨n, hn0, hn, ?_, ?_⟩
  · rw [← hS.cfg.card_normIn_eq ⟨x, hx⟩, hn]
  · rw [hS.card_cfgM_eq_sq, hn, ← pow_mul, mul_comm]

end Card

section Quotient

variable {G : Type} [Group G] {T T₁ : Subgroup G}
  [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]

set_option quotPrecheck false in
local notation "XQ" => ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)

set_option quotPrecheck false in
local notation "TQ" =>
  (T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))

theorem Sec3.conj_cfgM_eq_of_map_eq (hS : Sec3 T T₁) {x y : G} (hx : x ∈ T ⊔ T₁)
    (hy : y ∈ T ⊔ T₁)
    (hxy : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨x, hx⟩ =
      QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨y, hy⟩)
    {m : G} (hm : m ∈ cfgM T T₁) : x * m * x⁻¹ = y * m * y⁻¹ := by
  have h1 : x⁻¹ * y ∈ cfgM T T₁ := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hxy)
  have hcomm : (x⁻¹ * y) * m = m * (x⁻¹ * y) :=
    elemAbelian_mul_comm hS.cfg.isElemAbelian_cfgM h1 hm
  calc x * m * x⁻¹ = x * ((x⁻¹ * y) * m * (x⁻¹ * y)⁻¹) * x⁻¹ := by rw [hcomm]; group
    _ = y * m * y⁻¹ := by group

theorem Sec3.exists_lift_involution (hS : Sec3 T T₁) {q : ℕ} (hX : IsL2Pair XQ TQ q) {ā : XQ}
    (hā : ā * ā = 1) (hā1 : ā ≠ 1) :
    ∃ x ∈ T ⊔ T₁, ∃ (a : G) (ha : a ∈ T ⊔ T₁), a ∈ conjSubgroup x T ∧ a ∉ cfgM T T₁ ∧
      a * a = 1 ∧ QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨a, ha⟩ = ā := by
  obtain ⟨gb, hgb⟩ := hX.exists_conj_mem_of_mul_self_eq_one hā
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
  obtain ⟨y, hy, hyā⟩ := mem_conjSubgroup.1 hgb
  have hyT : (y : G) ∈ T := Subgroup.mem_subgroupOf.1 hy
  have hπa : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) (g * y * g⁻¹) = ā := by
    have e : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) g = (g : XQ) := rfl
    rw [map_mul, map_mul, map_inv, e, hyā]
    group
  have hcoe : ((g * y * g⁻¹ : ↥(T ⊔ T₁)) : G) = (g : G) * (y : G) * (g : G)⁻¹ := rfl
  refine ⟨(g : G), g.2, ((g * y * g⁻¹ : ↥(T ⊔ T₁)) : G), (g * y * g⁻¹).2, ?_, ?_, ?_, hπa⟩
  · rw [mem_conjSubgroup, hcoe]
    simpa [mul_assoc] using hyT
  · intro hM
    exact hā1 (hπa ▸ (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hM))
  · have hyy : (y : G) * y = 1 := elemAbelian_mul_self hS.cfg.wc.1 hyT
    rw [hcoe]
    calc (g : G) * y * (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹)
        = (g : G) * ((y : G) * y) * (g : G)⁻¹ := by group
      _ = 1 := by rw [hyy]; group

theorem Sec3.centralizer_cfgM_eq_bot_of_odd (hS : Sec3 T T₁) {q : ℕ} (hX : IsL2Pair XQ TQ q)
    {x : G} (hxX : x ∈ T ⊔ T₁)
    (hodd : Odd (orderOf (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨x, hxX⟩)))
    (hx1 : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨x, hxX⟩ ≠ 1) :
    ∀ m ∈ cfgM T T₁, x * m * x⁻¹ = m → m = 1 := by
  intro m hm hxm
  obtain ⟨u, v, hu, hv, hu1, hv1, -, hab⟩ := hX.exists_involutions_mul_eq_of_odd_ne_one hodd hx1
  obtain ⟨-, -, a, haX, -, -, haa, hπa⟩ := hS.exists_lift_involution hX hu hu1
  obtain ⟨-, -, b, hbX, -, -, hbb, hπb⟩ := hS.exists_lift_involution hX hv hv1
  have habX : a * b ∈ T ⊔ T₁ := (T ⊔ T₁).mul_mem haX hbX
  have hπab : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨x, hxX⟩ =
      QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨a * b, habX⟩ := by
    have : (⟨a * b, habX⟩ : ↥(T ⊔ T₁)) = ⟨a, haX⟩ * ⟨b, hbX⟩ := rfl
    rw [this, map_mul, hπa, hπb, hab]
  have hno : ¬ ∃ P : Subgroup G, P ≤ T ⊔ T₁ ∧ IsPGroup 2 P ∧ a ∈ P ∧ b ∈ P := by
    rintro ⟨P, -, hP, haP, hbP⟩
    have hPsub : IsPGroup 2 (P.subgroupOf (T ⊔ T₁)) := hP.comap_subtype
    have hmem : (⟨a * b, habX⟩ : ↥(T ⊔ T₁)) ∈ P.subgroupOf (T ⊔ T₁) :=
      Subgroup.mem_subgroupOf.2 (P.mul_mem haP hbP)
    exact hx1 (hπab ▸ eq_one_of_odd_orderOf_map
      (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) hPsub hmem (hπab ▸ hodd))
  have hC := hS.cfgM_inf_centralizer_inf_centralizer_of_not_common_two_group haX haa hbX hbb hno
  have hconj := hS.conj_cfgM_eq_of_map_eq hxX habX hπab hm
  rw [hxm] at hconj
  exact eq_one_of_conj_mul_eq_of_inf_centralizer hS.cfg.isElemAbelian_cfgM haa hbb
    (fun m' hm' => hS.cfg.conj_mem_cfgM haX hm') hC hm hconj.symm

end Quotient

end CFSG.CGT.Timmesfeld75
