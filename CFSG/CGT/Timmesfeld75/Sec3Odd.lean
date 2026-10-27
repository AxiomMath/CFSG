module

public import CFSG.CGT.Timmesfeld75.Sec3Conj
public import CFSG.CGT.Timmesfeld75.Cfg214Gen

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type*} [Group G] {T T₁ : Subgroup G}

section TwoGroups

theorem isPGroup_two_zpowers_of_mul_self {b : G} (hb : b * b = 1) :
    IsPGroup 2 (Subgroup.zpowers b) := by
  intro g
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  have hb2 : b ^ 2 = 1 := by rw [pow_two]; exact hb
  rw [Subgroup.coe_pow, ← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  simp [hb2]

theorem Sec3.exists_two_group_of_mem_cfgM (hS : Sec3 T T₁) {a b : G} (ha : a ∈ cfgM T T₁)
    (hb : b ∈ T ⊔ T₁) (hbb : b * b = 1) :
    ∃ S : Subgroup G, S ≤ T ⊔ T₁ ∧ IsPGroup 2 S ∧ a ∈ S ∧ b ∈ S := by
  refine ⟨Subgroup.zpowers b ⊔ cfgM T T₁, sup_le (Subgroup.zpowers_le.2 hb) (cfgM_le_sup T T₁),
    ?_, Subgroup.mem_sup_right ha, Subgroup.mem_sup_left (Subgroup.mem_zpowers b)⟩
  exact (isPGroup_two_zpowers_of_mul_self hbb).to_sup_of_normal_right'
    (isPGroup_two_of_isElemAbelian hS.cfg.isElemAbelian_cfgM)
    (Subgroup.zpowers_le.2 (hS.cfg.le_normalizer_cfgM hb))

theorem Sec3.exists_conj_pair_of_not_common_two_group (hS : Sec3 T T₁) {a b : G}
    (ha : a ∈ T ⊔ T₁) (haa : a * a = 1) (hb : b ∈ T ⊔ T₁) (hbb : b * b = 1)
    (hno : ¬ ∃ S : Subgroup G, S ≤ T ⊔ T₁ ∧ IsPGroup 2 S ∧ a ∈ S ∧ b ∈ S) :
    ∃ x ∈ T ⊔ T₁, ∃ y ∈ T ⊔ T₁, conjSubgroup x T ≠ conjSubgroup y T ∧
      a ∈ conjSubgroup x T ∧ a ∉ cfgM T T₁ ∧ b ∈ conjSubgroup y T ∧ b ∉ cfgM T T₁ := by
  have haM : a ∉ cfgM T T₁ := fun h => by
    obtain ⟨S, h1, h2, h3, h4⟩ := hS.exists_two_group_of_mem_cfgM h hb hbb
    exact hno ⟨S, h1, h2, h3, h4⟩
  have hbM : b ∉ cfgM T T₁ := fun h => by
    obtain ⟨S, h1, h2, h3, h4⟩ := hS.exists_two_group_of_mem_cfgM h ha haa
    exact hno ⟨S, h1, h2, h4, h3⟩
  obtain ⟨x, hx, hax⟩ := hS.invol a ha haa haM
  obtain ⟨y, hy, hby⟩ := hS.invol b hb hbb hbM
  refine ⟨x, hx, y, hy, fun hxy => hno ⟨conjSubgroup x T, ?_, ?_, hax, hxy ▸ hby⟩, hax, haM, hby,
    hbM⟩
  · exact conjSubgroup_le_of_le_of_mem le_sup_left hx
  · exact isPGroup_two_of_isElemAbelian (isElemAbelian_conjSubgroup hS.cfg.wc.1 x)

end TwoGroups

section Odd

variable [Finite G]

theorem Sec3.odd_orderOf_mul (hS : Sec3 T T₁) {x y : G} (hx : x ∈ T ⊔ T₁) (hy : y ∈ T ⊔ T₁)
    (hxy : conjSubgroup x T ≠ conjSubgroup y T) {a b : G} (ha : a ∈ conjSubgroup x T)
    (haM : a ∉ cfgM T T₁) (hb : b ∈ conjSubgroup y T) (hbM : b ∉ cfgM T T₁) :
    Odd (orderOf (a * b)) := by
  have c := hS.cfg_conj hx hy hxy
  refine c.odd_orderOf_mul_gen ?_ ha ?_ hb ?_
  · have hyx : conjSubgroup (y * x⁻¹) (conjSubgroup x T) = conjSubgroup y T := by
      rw [conjSubgroup_conjSubgroup, show y * x⁻¹ * x = y by group]
    obtain ⟨w, hw, hw'⟩ := exists_mem_conj_eq_of_le c.wc
      (le_sup_left : conjSubgroup x T ≤ conjSubgroup x T ⊔ conjSubgroup y T)
      (g := y * x⁻¹) (by rw [hyx]; exact le_sup_right)
    exact ⟨w, hw, by rw [← hyx]; exact hw'⟩
  · rw [hS.normIn_conj_eq hx hy hxy]
    exact fun h => haM (hS.cfg.conjSubgroup_normIn_le_cfgM hx h)
  · rw [hS.normIn_conj_eq hy hx hxy.symm]
    exact fun h => hbM (hS.cfg.conjSubgroup_normIn_le_cfgM hy h)

theorem Sec3.odd_orderOf_mul_of_not_common_two_group (hS : Sec3 T T₁) {a b : G}
    (ha : a ∈ T ⊔ T₁) (haa : a * a = 1) (hb : b ∈ T ⊔ T₁) (hbb : b * b = 1)
    (hno : ¬ ∃ S : Subgroup G, S ≤ T ⊔ T₁ ∧ IsPGroup 2 S ∧ a ∈ S ∧ b ∈ S) :
    Odd (orderOf (a * b)) := by
  obtain ⟨x, hx, y, hy, hxy, hax, haM, hby, hbM⟩ :=
    hS.exists_conj_pair_of_not_common_two_group ha haa hb hbb hno
  exact hS.odd_orderOf_mul hx hy hxy hax haM hby hbM

end Odd

section Centralizers

theorem Sec3.cfgM_inf_centralizer_inf_centralizer (hS : Sec3 T T₁) {x y : G} (hx : x ∈ T ⊔ T₁)
    (hy : y ∈ T ⊔ T₁) (hxy : conjSubgroup x T ≠ conjSubgroup y T) {a b : G}
    (ha : a ∈ conjSubgroup x T) (haM : a ∉ cfgM T T₁) (hb : b ∈ conjSubgroup y T)
    (hbM : b ∉ cfgM T T₁) :
    cfgM T T₁ ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro m ⟨⟨hmM, hma⟩, hmb⟩
  have h1 : m ∈ cfgM T T₁ ⊓ Subgroup.centralizer ({a} : Set G) := ⟨hmM, hma⟩
  have h2 : m ∈ cfgM T T₁ ⊓ Subgroup.centralizer ({b} : Set G) := ⟨hmM, hmb⟩
  rw [hS.cfgM_inf_centralizer_conj hx ha haM] at h1
  rw [hS.cfgM_inf_centralizer_conj hy hb hbM] at h2
  have h3 : m ∈ conjSubgroup x T ⊓ conjSubgroup y T :=
    ⟨conjSubgroup_mono (normIn_le T T₁) h1, conjSubgroup_mono (normIn_le T T₁) h2⟩
  rwa [(hS.cfg_conj hx hy hxy).inf] at h3

theorem Sec3.cfgM_inf_centralizer_inf_centralizer_of_not_common_two_group (hS : Sec3 T T₁)
    {a b : G} (ha : a ∈ T ⊔ T₁) (haa : a * a = 1) (hb : b ∈ T ⊔ T₁) (hbb : b * b = 1)
    (hno : ¬ ∃ S : Subgroup G, S ≤ T ⊔ T₁ ∧ IsPGroup 2 S ∧ a ∈ S ∧ b ∈ S) :
    cfgM T T₁ ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) = ⊥ := by
  obtain ⟨x, hx, y, hy, hxy, hax, haM, hby, hbM⟩ :=
    hS.exists_conj_pair_of_not_common_two_group ha haa hb hbb hno
  exact hS.cfgM_inf_centralizer_inf_centralizer hx hy hxy hax haM hby hbM

end Centralizers

section Conjugacy

theorem exists_pow_conj_of_odd_orderOf_mul {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hodd : Odd (orderOf (a * b))) : ∃ k : ℕ, ((a * b) ^ k)⁻¹ * a * (a * b) ^ k = b := by
  obtain ⟨k, hk⟩ := hodd
  have h1 := inv_pow_mul_mul_pow_of_inverts (left_invol_inverts ha hb) (k + 1)
  have hpow : (a * b) ^ (2 * (k + 1)) = a * b := by
    rw [show 2 * (k + 1) = orderOf (a * b) + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  rw [hpow] at h1
  exact ⟨k + 1, by rw [h1]; exact (invol_eq_inv_mul_mul hb).symm⟩

variable [Finite G]

theorem Sec3.exists_conj_of_odd_pair (hS : Sec3 T T₁) {x y : G} (hx : x ∈ T ⊔ T₁)
    (hy : y ∈ T ⊔ T₁) (hxy : conjSubgroup x T ≠ conjSubgroup y T) {a b : G}
    (ha : a ∈ conjSubgroup x T) (haM : a ∉ cfgM T T₁) (hb : b ∈ conjSubgroup y T)
    (hbM : b ∉ cfgM T T₁) : ∃ z ∈ T ⊔ T₁, z * a * z⁻¹ = b := by
  have haX : a ∈ T ⊔ T₁ := conjSubgroup_le_of_le_of_mem le_sup_left hx ha
  have hbX : b ∈ T ⊔ T₁ := conjSubgroup_le_of_le_of_mem le_sup_left hy hb
  have haa := elemAbelian_mul_self (isElemAbelian_conjSubgroup hS.cfg.wc.1 x) ha
  have hbb := elemAbelian_mul_self (isElemAbelian_conjSubgroup hS.cfg.wc.1 y) hb
  obtain ⟨k, hk⟩ := exists_pow_conj_of_odd_orderOf_mul haa hbb
    (hS.odd_orderOf_mul hx hy hxy ha haM hb hbM)
  refine ⟨((a * b) ^ k)⁻¹,
    (T ⊔ T₁).inv_mem ((T ⊔ T₁).pow_mem ((T ⊔ T₁).mul_mem haX hbX) k), ?_⟩
  rw [inv_inv]
  exact hk

theorem Sec3.exists_conj_of_invol (hS : Sec3 T T₁) {a b : G} (ha : a ∈ T ⊔ T₁) (haa : a * a = 1)
    (haM : a ∉ cfgM T T₁) (hb : b ∈ T ⊔ T₁) (hbb : b * b = 1) (hbM : b ∉ cfgM T T₁) :
    ∃ z ∈ T ⊔ T₁, z * a * z⁻¹ = b := by
  obtain ⟨x, hx, hax⟩ := hS.invol a ha haa haM
  obtain ⟨y, hy, hby⟩ := hS.invol b hb hbb hbM
  by_cases hxy : conjSubgroup x T = conjSubgroup y T
  · obtain ⟨w, hw, hwx⟩ := hS.exists_conj_ne hx
    obtain ⟨c, hcw, hcM⟩ := IsConcreteLE.not_le_iff_exists.1 (hS.not_conj_le_cfgM hw)
    obtain ⟨z₁, hz₁, hz₁'⟩ := hS.exists_conj_of_odd_pair hx hw hwx.symm hax haM hcw hcM
    obtain ⟨z₂, hz₂, hz₂'⟩ := hS.exists_conj_of_odd_pair hw hy (fun h => hwx (h.trans hxy.symm))
      hcw hcM hby hbM
    refine ⟨z₂ * z₁, (T ⊔ T₁).mul_mem hz₂ hz₁, ?_⟩
    calc z₂ * z₁ * a * (z₂ * z₁)⁻¹ = z₂ * (z₁ * a * z₁⁻¹) * z₂⁻¹ := by group
      _ = b := by rw [hz₁', hz₂']
  · exact hS.exists_conj_of_odd_pair hx hy hxy hax haM hby hbM

theorem Sec3.exists_mem_normalizer_conj (hS : Sec3 T T₁) {a b : G} (ha : a ∈ T)
    (haM : a ∉ cfgM T T₁) (hb : b ∈ T) (hbM : b ∉ cfgM T T₁) :
    ∃ z ∈ T ⊔ T₁, z ∈ Subgroup.normalizer (T : Set G) ∧ z * a * z⁻¹ = b := by
  obtain ⟨z, hz, hzab⟩ := hS.exists_conj_of_invol (Subgroup.mem_sup_left ha)
    (elemAbelian_mul_self hS.cfg.wc.1 ha) haM (Subgroup.mem_sup_left hb)
    (elemAbelian_mul_self hS.cfg.wc.1 hb) hbM
  refine ⟨z, hz, ?_, hzab⟩
  have hb1 : b ≠ 1 := fun h => hbM (h ▸ (cfgM T T₁).one_mem)
  refine mem_normalizer_of_conjSubgroup_eq (hS.cfg.wc.conj_eq_of_inf_ne_bot fun hbot => ?_)
  have hbz : b ∈ conjSubgroup z T := by
    rw [mem_conjSubgroup, ← hzab]
    simpa [mul_assoc] using ha
  have hmem : b ∈ T ⊓ conjSubgroup z T := ⟨hb, hbz⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hb1 hmem

end Conjugacy

end CFSG.CGT.Timmesfeld75
