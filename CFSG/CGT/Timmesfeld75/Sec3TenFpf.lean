module

public import CFSG.CGT.Timmesfeld75.Sec3Eight

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open DihedralGroup

section Quotient

variable {G : Type} [Group G] {T T₁ : Subgroup G}
  [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]

set_option quotPrecheck false in
local notation "XQ" => ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)

set_option quotPrecheck false in
local notation "TQ" =>
  (T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))

theorem Sec3.exists_lift_involution' (hS : Sec3 T T₁)
    (hcov : ∀ ab : XQ, ab * ab = 1 → ab ≠ 1 → ∃ gb : XQ, ab ∈ conjSubgroup gb TQ) {ab : XQ}
    (hab : ab * ab = 1) (hab1 : ab ≠ 1) :
    ∃ x ∈ T ⊔ T₁, ∃ (a : G) (ha : a ∈ T ⊔ T₁), a ∈ conjSubgroup x T ∧ a ∉ cfgM T T₁ ∧
      a * a = 1 ∧ QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨a, ha⟩ = ab := by
  obtain ⟨gb, hgb⟩ := hcov ab hab hab1
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
  obtain ⟨y, hy, hyab⟩ := mem_conjSubgroup.1 hgb
  have hyT : (y : G) ∈ T := Subgroup.mem_subgroupOf.1 hy
  have hπa : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) (g * y * g⁻¹) = ab := by
    have e : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) g =
        (g : XQ) := rfl
    rw [map_mul, map_mul, map_inv, e, hyab]
    group
  have hcoe : ((g * y * g⁻¹ : ↥(T ⊔ T₁)) : G) = (g : G) * (y : G) * (g : G)⁻¹ := rfl
  refine ⟨(g : G), g.2, ((g * y * g⁻¹ : ↥(T ⊔ T₁)) : G), (g * y * g⁻¹).2, ?_, ?_, ?_, hπa⟩
  · rw [mem_conjSubgroup, hcoe]
    simpa [mul_assoc] using hyT
  · intro hM
    exact hab1 (hπa ▸ (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hM))
  · have hyy : (y : G) * y = 1 := elemAbelian_mul_self hS.cfg.wc.1 hyT
    rw [hcoe]
    calc (g : G) * y * (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹)
        = (g : G) * ((y : G) * y) * (g : G)⁻¹ := by group
      _ = 1 := by rw [hyy]; group

theorem Sec3.centralizer_cfgM_eq_bot_of_odd' (hS : Sec3 T T₁)
    (hcov : ∀ ab : XQ, ab * ab = 1 → ab ≠ 1 → ∃ gb : XQ, ab ∈ conjSubgroup gb TQ)
    (hprod : ∀ xb : XQ, Odd (orderOf xb) → xb ≠ 1 →
      ∃ u v : XQ, u * u = 1 ∧ v * v = 1 ∧ u ≠ 1 ∧ v ≠ 1 ∧ xb = u * v)
    {x : G} (hxX : x ∈ T ⊔ T₁)
    (hodd : Odd (orderOf (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨x, hxX⟩)))
    (hx1 : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨x, hxX⟩ ≠ 1) :
    ∀ m ∈ cfgM T T₁, x * m * x⁻¹ = m → m = 1 := by
  intro m hm hxm
  obtain ⟨u, v, hu, hv, hu1, hv1, hab⟩ := hprod _ hodd hx1
  obtain ⟨-, -, a, haX, -, -, haa, hπa⟩ := hS.exists_lift_involution' hcov hu hu1
  obtain ⟨-, -, b, hbX, -, -, hbb, hπb⟩ := hS.exists_lift_involution' hcov hv hv1
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



theorem dihedral_isConj_of_involutions {n : ℕ} [NeZero n] (hn : Odd n) {x y : DihedralGroup n}
    (hx : x * x = 1) (hx1 : x ≠ 1) (hy : y * y = 1) (hy1 : y ≠ 1) : IsConj x y := by
  have hhalf := two_mul_half_zmod hn
  have hsr : ∀ z : DihedralGroup n, z * z = 1 → z ≠ 1 → ∃ j : ZMod n, z = sr j := by
    intro z hz hz1
    rcases z with i | j
    · exfalso
      apply hz1
      rw [r_mul_r] at hz
      have h2 : i + i = 0 := by
        have := hz
        rw [← r_zero] at this
        exact DihedralGroup.r.inj this
      have hi : i = 0 := by
        calc i = (2 * (((n + 1) / 2 : ℕ) : ZMod n)) * i := by rw [hhalf, one_mul]
          _ = (((n + 1) / 2 : ℕ) : ZMod n) * (i + i) := by ring
          _ = 0 := by rw [h2, mul_zero]
      rw [hi, r_zero]
    · exact ⟨j, rfl⟩
  obtain ⟨i, rfl⟩ := hsr x hx hx1
  obtain ⟨j, rfl⟩ := hsr y hy hy1
  refine isConj_iff.2 ⟨r ((i - j) * (((n + 1) / 2 : ℕ) : ZMod n)), ?_⟩
  rw [inv_r, r_mul_sr, sr_mul_r]
  congr 1
  have : (i - j) = 2 * ((i - j) * (((n + 1) / 2 : ℕ) : ZMod n)) := by
    calc i - j = (i - j) * (2 * (((n + 1) / 2 : ℕ) : ZMod n)) := by rw [hhalf, mul_one]
      _ = 2 * ((i - j) * (((n + 1) / 2 : ℕ) : ZMod n)) := by ring
  linear_combination this


theorem dihedral_cov_prod {Q : Type} [Group Q] {n : ℕ} (hn : Odd n) (e : Q ≃* DihedralGroup n)
    {S : Subgroup Q} (hS : S ≠ ⊥) (hSsq : ∀ s ∈ S, s * s = 1) :
    (∀ u : Q, u * u = 1 → u ≠ 1 → ∃ g : Q, u ∈ conjSubgroup g S) ∧
    (∀ x : Q, Odd (orderOf x) → x ≠ 1 →
      ∃ u v : Q, u * u = 1 ∧ v * v = 1 ∧ u ≠ 1 ∧ v ≠ 1 ∧ x = u * v) := by
  have : NeZero n := ⟨hn.pos.ne'⟩
  constructor
  · intro u hu hu1
    obtain ⟨t, ht⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hS
    have htS : (t : Q) ∈ S := t.2
    have ht1 : (t : Q) ≠ 1 := fun h => ht (Subtype.ext h)
    have hconj := dihedral_isConj_of_involutions hn (x := e (t : Q)) (y := e u)
      (by rw [← map_mul, hSsq _ htS, map_one])
      (fun h => ht1 (e.injective (h.trans (map_one e).symm)))
      (by rw [← map_mul, hu, map_one]) (fun h => hu1 (e.injective (h.trans (map_one e).symm)))
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    refine ⟨e.symm c, ?_⟩
    have : e.symm c * (t : Q) * (e.symm c)⁻¹ = u := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hc
    rw [← this]
    exact conj_mem_conjSubgroup _ htS
  · intro x hx hx1
    have hrot : ∃ i : ZMod n, e x = r i := by
      rcases hxe : e x with i | k
      · exact ⟨i, rfl⟩
      · exfalso
        have h1 : orderOf (e x) = orderOf x := MulEquiv.orderOf_eq e x
        rw [hxe, orderOf_sr] at h1
        rw [← h1] at hx
        exact (Nat.not_even_iff_odd.2 hx) even_two
    obtain ⟨i, hi⟩ := hrot
    have hsr1 : ∀ k : ZMod n, (sr k : DihedralGroup n) ≠ 1 := by
      intro k h
      have : orderOf (sr k : DihedralGroup n) = 1 := by rw [h]; exact orderOf_one
      rw [orderOf_sr] at this
      omega
    refine ⟨e.symm (sr 0), e.symm (sr i), ?_, ?_, ?_, ?_, ?_⟩
    · rw [← map_mul, sr_mul_self, map_one]
    · rw [← map_mul, sr_mul_self, map_one]
    · exact fun h => hsr1 0 (e.symm.injective (h.trans (map_one e.symm).symm))
    · exact fun h => hsr1 i (e.symm.injective (h.trans (map_one e.symm).symm))
    · rw [← map_mul, sr_mul_sr, sub_zero, ← hi, MulEquiv.symm_apply_apply]

theorem Sec3.centralizer_cfgM_eq_bot_of_odd_dihedral [Finite G] (hS : Sec3 T T₁) {n : ℕ}
    (hn : Odd n) (e : XQ ≃* DihedralGroup n) {x : G} (hxX : x ∈ T ⊔ T₁)
    (hodd : Odd (orderOf (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨x, hxX⟩)))
    (hx1 : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨x, hxX⟩ ≠ 1) :
    ∀ m ∈ cfgM T T₁, x * m * x⁻¹ = m → m = 1 := by
  obtain ⟨hcov, hprod⟩ := dihedral_cov_prod hn e hS.map_ne_bot fun s hs =>
    elemAbelian_mul_self hS.isElemAbelian_map hs
  exact hS.centralizer_cfgM_eq_bot_of_odd' (fun u hu hu1 => hcov u hu hu1) hprod hxX hodd hx1

end Quotient

end CFSG.CGT.Timmesfeld75
