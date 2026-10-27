module

public import CFSG.LargeExtraspecial.S3bNine
public import CFSG.LargeExtraspecial.S3Fusion

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

omit [Finite G] in
theorem conj_mul_mem_QG {g h : G} (hh : h ∈ S.M) (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    (h * g) * S.z * (h * g)⁻¹ ∈ S.QG := by
  have := S.conj_mem_QG hh haQ
  rwa [show h * (g * S.z * g⁻¹) * h⁻¹ = (h * g) * S.z * (h * g)⁻¹ by group] at this

omit [Finite G] in
theorem mul_z_mul_self {b : G} (hb : b ∈ S.QG) (hb2 : b * b = 1) : b * S.z * b = S.z := by
  rw [S.z_comm_QG hb, mul_assoc, hb2, mul_one]

omit [Finite G] in
theorem conj_mul_ne_z {g h : G} (hh : h ∈ S.M) (hne : g * S.z * g⁻¹ ≠ S.z) :
    (h * g) * S.z * (h * g)⁻¹ ≠ S.z := by
  intro h1
  apply hne
  calc g * S.z * g⁻¹ = h⁻¹ * ((h * g) * S.z * (h * g)⁻¹) * h := by group
    _ = h⁻¹ * S.z * h := by rw [h1]
    _ = S.z := by rw [S.z_comm (S.M.inv_mem hh)]; group

theorem lemma_4_1 {g h x : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hh : h ∈ S.M) (hx : x ∈ S.L0 (h * g)) (hxQ : x ∉ S.QG)
    (hxa : x * (g * S.z * g⁻¹) * x⁻¹ = g * S.z * g⁻¹ ∨
      x * (g * S.z * g⁻¹) * x⁻¹ = g * S.z * g⁻¹ * S.z) :
    g * S.z * g⁻¹ * ((h * g) * S.z * (h * g)⁻¹) =
      (h * g) * S.z * (h * g)⁻¹ * (g * S.z * g⁻¹) := by
  set a := g * S.z * g⁻¹ with ha
  set b := (h * g) * S.z * (h * g)⁻¹ with hb
  have hbQ : b ∈ S.QG := S.conj_mul_mem_QG hh haQ
  have hbz : b ≠ S.z := S.conj_mul_ne_z hh hne
  have hb2 : b * b = 1 := (S.conjBy (h * g)).z_mul_z
  have hzb : S.z ∈ S.Qa (h * g) := S.z_mem_Qa hbQ hbz
  have hbQb : b ∈ S.Qa (h * g) := S.conj_z_mem_Qa (h * g)
  by_contra hab
  have hab' : a * b = S.z * (b * a) := (S.mul_comm_or haQ hbQ).resolve_left hab
  have hbab : b * a * b⁻¹ = a * S.z := by
    have e : b * a = S.z * (a * b) := by
      rw [hab', ← mul_assoc S.z S.z, S.z_mul_z, one_mul]
    rw [e, show S.z * (a * b) * b⁻¹ = S.z * a by group, ← S.z_comm_QG haQ]
  have haba : a * b * a⁻¹ = b * S.z := by
    rw [hab', show S.z * (b * a) * a⁻¹ = S.z * b by group, ← S.z_comm_QG hbQ]
  obtain ⟨x', hx'L, hx'Q, hx'a⟩ : ∃ x' ∈ S.L0 (h * g), x' ∉ S.QG ∧ x' * a = a * x' := by
    rcases hxa with h1 | h1
    · refine ⟨x, hx, hxQ, ?_⟩
      calc x * a = x * a * x⁻¹ * x := by group
        _ = a * x := by rw [h1]
    · refine ⟨x * b, mul_mem hx ⟨hbQb, S.QG_le_M hbQ⟩, fun hm => hxQ ?_, ?_⟩
      · have := S.QG.mul_mem hm (S.QG.inv_mem hbQ)
        rwa [mul_inv_cancel_right] at this
      · have e : x * b * a * (x * b)⁻¹ = a := by
          calc x * b * a * (x * b)⁻¹ = x * (b * a * b⁻¹) * x⁻¹ := by group
            _ = x * (a * S.z) * x⁻¹ := by rw [hbab]
            _ = x * a * x⁻¹ * (x * S.z * x⁻¹) := by group
            _ = a * S.z * S.z := by rw [h1, S.conj_z_of_mem_M (S.L0_le_M _ hx)]
            _ = a := by rw [mul_assoc, S.z_mul_z, mul_one]
        calc x * b * a = x * b * a * (x * b)⁻¹ * (x * b) := by group
          _ = a * (x * b) := by rw [e]
  set Tb := S.conjBy (h * g) with hTb
  have hTbz : Tb.z = b := rfl
  have hx'Qbz : x' ∈ S.Qa (a * (h * g)) := by
    have := S.conj_mem_Qa_mul (h := a) hx'L.1
    rwa [show a * x' * a⁻¹ = x' by rw [← hx'a]; group] at this
  have htQ : a * Tb.z * a⁻¹ ∈ Tb.QG := by
    rw [hTbz, haba]
    exact mul_mem hbQb hzb
  have htne : a * Tb.z * a⁻¹ ≠ Tb.z := by
    rw [hTbz, haba]
    intro h'
    exact S.z_ne_one (by simpa using h')
  have heQt : x' ∈ Tb.Qa a := by
    rw [hTb, S.Qa_conjBy]
    exact hx'Qbz
  have he : x' ∉ closure ({a * Tb.z * a⁻¹, Tb.z} : Set G) := by
    intro hm
    apply hx'Q
    have hle : closure ({a * Tb.z * a⁻¹, Tb.z} : Set G) ≤ S.QG := by
      rw [closure_le]
      rintro _ (rfl | rfl)
      · rw [hTbz, haba]
        exact S.QG.mul_mem hbQ S.z_mem_QG
      · exact hbQ
    exact hle hm
  have hab2 : Tb.z ≠ a * Tb.z * a⁻¹ * Tb.z := by
    rw [hTbz, haba]
    intro h'
    exact hbz (h'.trans (S.mul_z_mul_self hbQ hb2))
  obtain ⟨u, hu, -, hu2⟩ := Tb.lemma_3_8_2 rfl htQ htne hx'L.1 heQt he Tb.z (by simp)
    (a * Tb.z * a⁻¹ * Tb.z) (by simp) hab2
  have hux : u * x' * u⁻¹ = x' := by
    rw [mem_centralizer_singleton_iff.mp hu.2]
    group
  have hz : (u * (a * (h * g))) * S.z * (u * (a * (h * g)))⁻¹ = S.z := by
    calc (u * (a * (h * g))) * S.z * (u * (a * (h * g)))⁻¹ = u * (a * Tb.z * a⁻¹) * u⁻¹ := by
          rw [hTbz, hb]; group
      _ = a * Tb.z * a⁻¹ * Tb.z := hu2
      _ = S.z := by
          rw [hTbz, haba]
          exact S.mul_z_mul_self hbQ hb2
  have hmem := S.conj_mem_Qa_mul (h := u) hx'Qbz
  rw [hux, ← mul_assoc, S.Qa_eq_QG_of_conj_eq (by rw [mul_assoc u a (h * g)]; exact hz)] at hmem
  exact hx'Q hmem

theorem lemma_4_1_of_inf_normalizer_ne_bot (h2 : 2 ≤ S.width) {g h : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g)
    (hh : h ∈ S.M) (hL : S.Lbar (h * g) ⊓ normalizer (S.Lbar g : Set S.O) ≠ ⊥) :
    g * S.z * g⁻¹ * ((h * g) * S.z * (h * g)⁻¹) =
      (h * g) * S.z * (h * g)⁻¹ * (g * S.z * g⁻¹) := by
  obtain ⟨s, ⟨hs, hsN⟩, hs1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hL
  obtain ⟨y, hy, hys⟩ := S.mem_Lbar_iff.mp hs
  have hyQ : (y : G) ∉ S.QG := fun h' => hs1 (by rw [← hys, (S.ρ_eq_one_iff y).mpr h'])
  have h1 := S.fixes_of_mem_normalizer_Lbar h2 haQ hne hno hsN
  rw [← hys, S.ρ_cl _ haQ] at h1
  exact S.lemma_4_1 haQ hne hh hy hyQ ((S.cl_eq_cl_iff haQ (S.conj_mem_QG y.2 haQ)).mp h1.symm)

theorem lemma_3_11_weaklyClosed (h2 : 2 ≤ S.width) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g) {h : G} (hh : h ∈ S.M)
    (hle : S.Lbar (h * g) ≤ normalizer (S.Lbar g : Set S.O)) : S.Lbar (h * g) = S.Lbar g := by
  set a := g * S.z * g⁻¹ with ha
  set b := (h * g) * S.z * (h * g)⁻¹ with hb
  have hbQ : b ∈ S.QG := S.conj_mul_mem_QG hh haQ
  have hbz : b ≠ S.z := S.conj_mul_ne_z hh hne
  have hb1 : b ≠ 1 := (S.conjBy (h * g)).z_ne_one
  have hfixa : ∀ y ∈ S.L0 (h * g), y * a * y⁻¹ = a ∨ y * a * y⁻¹ = a * S.z := by
    intro y hy
    have h1 := S.fixes_of_mem_normalizer_Lbar h2 haQ hne hno (hle (S.ρ_mem_Lbar hy))
    rw [S.ρ_cl _ haQ] at h1
    exact (S.cl_eq_cl_iff haQ (S.conj_mem_QG (S.L0_le_M _ hy) haQ)).mp h1.symm
  obtain ⟨x, hx, hxQ⟩ : ∃ x ∈ S.L0 (h * g), x ∉ S.QG := by
    by_contra hcon
    push Not at hcon
    have hcard := S.card_Lbar_ge hbQ hbz
    have hbot : S.Lbar (h * g) = ⊥ := by
      rw [eq_bot_iff]
      intro s hs
      obtain ⟨y, hy, rfl⟩ := S.mem_Lbar_iff.mp hs
      exact (S.ρ_eq_one_iff y).mpr (hcon _ hy)
    rw [hbot, card_bot] at hcard
    have : 2 ^ 1 ≤ 2 ^ (S.width - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hab := S.lemma_4_1 haQ hne hh hx hxQ (hfixa x hx)
  by_cases hbQa : b ∈ S.Qa g
  · by_cases hba : b = a
    · exact S.Lbar_eq_of_conj_eq hba
    by_cases hbaz : b = a * S.z
    · exact S.Lbar_eq_of_conj_eq_mul_z haQ hne hbaz
    exfalso
    have haQb : a ∈ S.Qa (h * g) := S.mem_Qa_symm hba hbQa
    have hcl : S.cl a ≠ 0 ∧ S.cl a ≠ S.cl b := by
      refine ⟨S.cl_conj_z_ne_zero haQ hne, fun h' => ?_⟩
      rcases (S.cl_eq_cl_iff haQ hbQ).mp h' with h'' | h''
      · exact hba h''
      · exact hbaz h''
    obtain ⟨-, y, hy, hya⟩ := S.conj_L0_of_mem_QG_inf_Qa hbQ hbz ⟨haQ, haQb⟩ hcl
    rcases hfixa y hy with h1 | h1
    · rw [hya] at h1
      exact hb1 (by
        calc b = b * a * a⁻¹ := by group
          _ = 1 := by rw [h1, mul_inv_cancel])
    · rw [hya, S.z_comm_QG haQ] at h1
      exact hbz (mul_right_cancel h1)
  · exfalso
    have haQb : a ∉ S.Qa (h * g) := fun h' => hbQa (S.mem_Qa_symm (Ne.symm ?_) h')
    · obtain ⟨α, hα, hαQ, hαA⟩ := S.exists_typeA_of_involution hbQ hbz haQ
        (S.conjBy g).z_sq hab haQb hfixa
      exact hno (S.hasTypeAInL_of_mul hh (S.hasTypeAInL_of_mem_L0 hα hαQ hαA))
    · intro h'
      apply hbQa
      show (h * g) * S.z * (h * g)⁻¹ ∈ S.Qa g
      rw [h']
      exact S.conj_z_mem_Qa g

instance instFiniteMbar : Finite S.Mbar := by
  unfold Mbar
  exact (Set.finite_range S.ρ).to_subtype

theorem map_conj_Lbar_subgroupOf {g h : G} (hh : h ∈ S.M) (m : S.Mbar)
    (hm : S.ρ ⟨h, hh⟩ = m) :
    ((S.Lbar g).subgroupOf S.Mbar).map (MulAut.conj m).toMonoidHom =
      (S.Lbar (h * g)).subgroupOf S.Mbar := by
  ext x
  simp only [mem_map, mem_subgroupOf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [S.Lbar_mul hh, mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simp [hm]⟩
  · rintro ⟨s, hs, hsx⟩
    refine ⟨⟨s, S.Lbar_le_Mbar g hs⟩, hs, Subtype.ext ?_⟩
    rw [← hsx]
    simp [hm]

theorem isWeaklyClosedInNormalizer_Lbar (h2 : 2 ≤ S.width) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g) :
    IsWeaklyClosedInNormalizer ((S.Lbar g).subgroupOf S.Mbar) := by
  intro m hm
  obtain ⟨⟨h, hh⟩, hmh⟩ := MonoidHom.mem_range.mp m.2
  rw [S.map_conj_Lbar_subgroupOf hh m hmh] at hm ⊢
  have hle : S.Lbar (h * g) ≤ normalizer (S.Lbar g : Set S.O) := by
    intro s hs
    have hsM : s ∈ S.Mbar := S.Lbar_le_Mbar _ hs
    have h1 := hm (show (⟨s, hsM⟩ : S.Mbar) ∈ (S.Lbar (h * g)).subgroupOf S.Mbar from hs)
    rw [← subgroupOf_normalizer_eq (S.Lbar_le_Mbar g)] at h1
    exact h1
  rw [S.lemma_3_11_weaklyClosed h2 haQ hne hno hh hle]

theorem le_normalizer_Lbar_of_isPGroup (h2 : 2 ≤ S.width) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g)
    {P : Subgroup S.Mbar} (hP : IsPGroup 2 P) (hLP : (S.Lbar g).subgroupOf S.Mbar ≤ P) :
    P ≤ normalizer (((S.Lbar g).subgroupOf S.Mbar : Subgroup S.Mbar) : Set S.Mbar) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_normalizer_of_isWeaklyClosed (S.isWeaklyClosedInNormalizer_Lbar h2 haQ hne hno) hP hLP

end Setting

end CFSG.LargeExtraspecial
