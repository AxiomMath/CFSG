module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Glue
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Struct2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Struct4
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

namespace Setup8

theorem m4 (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    M.M4 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂ := m4_of_std hII hs.fused.std

theorem z_sq (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : z * z = 1 := by
  have h1 := pow_orderOf_eq_one z
  rw [hs.fused.std.orderOf_z] at h1
  simpa [pow_two] using h1

theorem z_ne (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : z ≠ 1 := by
  intro h1
  have h2 := hs.fused.std.orderOf_z
  rw [h1, orderOf_one] at h2
  omega

theorem z_mem_S (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : z ∈ S :=
  (hs.m4 hII).z_mem_S

theorem z_mem_P {K : Subgroup G} (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (hK : K = K₁ ∨ K = K₂) : z ∈ Pof S K :=
  ⟨(hs.m4 hII).z_mem_S, (hs.m4 hII).z_mem_comp hK⟩

theorem z_mem_Q {K : Subgroup G} (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (hK : K = K₁ ∨ K = K₂) : z ∈ Qof S K :=
  ⟨(hs.m4 hII).z_mem_S, (hs.m4 hII).z_mem_secCent_comp hK⟩

theorem S_pgroup (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : IsPGroup 2 ↥S :=
  (hs.m4 hII).S_pgroup

theorem S_le_C (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    S ≤ centralizer ({z} : Set G) := (hs.m4 hII).S_syl.1

theorem P_comm (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∀ a ∈ Pof S K₁, ∀ b ∈ Pof S K₂, a * b = b * a :=
  fun _ ha _ hb => (hs.m4 hII).comm_of_S ha.2 hb.2 ha.1 hb.1

theorem P_inf (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    Pof S K₁ ⊓ Pof S K₂ = zpowers z := by
  have hM := hs.m4 hII
  apply le_antisymm
  · rintro x ⟨⟨hxS, hxK₁⟩, ⟨-, hxK₂⟩⟩
    have hx : x ∈ S ⊓ M.ZsM (pPrimeCoreOf 2) K₁ := ⟨hxS, hxK₁, hM.cs₁ hxK₂⟩
    rw [(hM.S_inf_Zs_comp (Or.inl rfl)).2] at hx
    exact hx
  · exact zpowers_le.2 ⟨hs.z_mem_P hII (Or.inl rfl), hs.z_mem_P hII (Or.inr rfl)⟩

theorem Pz_eq_sup (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    Pz S z = Pof S K₁ ⊔ Pof S K₂ := by
  have hM := hs.m4 hII
  have e1 : M.Pm S K₁ K₂ ⊓ K₁ = Pof S K₁ := by
    unfold M.Pm Pof
    rw [inf_assoc, inf_eq_right.2 (le_sup_left : K₁ ≤ K₁ ⊔ K₂)]
  have e2 : M.Pm S K₁ K₂ ⊓ K₂ = Pof S K₂ := by
    unfold M.Pm Pof
    rw [inf_assoc, inf_eq_right.2 (le_sup_right : K₂ ≤ K₁ ⊔ K₂)]
  rw [Pz_eq hs.fused.std, hM.P_eq, e1, e2]

theorem card_P (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    Nat.card ↥(Pof S K₁) * Nat.card ↥(Pof S K₂) = 2 * Nat.card ↥(Pz S z) := by
  have hc := hs.P_comm hII
  have h1 := M.card_sup_mul_card_inf (A := Pof S K₁) (B := Pof S K₂) (M.le_normalizer_of_commute hc)
  rw [hs.Pz_eq_sup hII, ← h1, hs.P_inf hII, M.card_zpowers_of_sq hs.z_sq hs.z_ne]
  ring

theorem gq_P (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) : Basic.GQ (Pof S K) z := by
  have hstd := hs.fused.std
  obtain ⟨n, hn3, ⟨e⟩⟩ := hq G hstd.simple z hstd.orderOf_z S K hstd.sylow
    (hstd.comp_isPCompIn hK) (hstd.comp_pRank hK)
  haveI : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  have hm : 2 ≤ 2 ^ (n - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact Basic.gq_of_equiv hm e (hs.z_mem_P hII hK) hs.z_sq hs.z_ne

theorem gq_Q₁ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    Basic.GQ (Qof S K₁) z := by
  obtain ⟨n, hn3, ⟨e⟩⟩ := hs.fused.p66.1.1
  haveI : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  have hm : 2 ≤ 2 ^ (n - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact Basic.gq_of_equiv hm e (hs.z_mem_Q hII (Or.inl rfl)) hs.z_sq hs.z_ne

theorem gq_Q₂ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    Basic.GQ (Qof S K₂) z := by
  obtain ⟨n, hn3, ⟨e⟩⟩ := hs.fused.p66.1.2.1
  haveI : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  have hm : 2 ≤ 2 ^ (n - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact Basic.gq_of_equiv hm e (hs.z_mem_Q hII (Or.inr rfl)) hs.z_sq hs.z_ne

theorem norm_iff (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {x : G} (hx : x ∈ S) :
    x ∈ normalizer (K₁ : Set G) ↔ x ∈ normalizer (K₂ : Set G) := by
  have hM := hs.m4 hII
  have hxC : x ∈ centralizer ({z} : Set G) := hM.S_syl.1 hx
  have hne : K₁ ≠ K₂ := hs.fused.std.ne
  rcases hM.perm x hxC with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun _ => M.cj_eq_iff_normalizer.1 h2, fun _ => M.cj_eq_iff_normalizer.1 h1⟩
  · constructor
    · intro hn
      exfalso
      have := M.cj_eq_iff_normalizer.2 hn
      rw [h1] at this
      exact hne this.symm
    · intro hn
      exfalso
      have := M.cj_eq_iff_normalizer.2 hn
      rw [h2] at this
      exact hne this

theorem swap_of_not_mem (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {x : G}
    (hx : x ∈ S) (hn : x ∉ S1 S K₁) : conjugate K₁ x = K₂ ∧ conjugate K₂ x = K₁ := by
  have hM := hs.m4 hII
  have hxC : x ∈ centralizer ({z} : Set G) := hM.S_syl.1 hx
  have hn' : x ∉ normalizer (K₁ : Set G) := fun h' => hn ⟨hx, h'⟩
  rcases hM.perm x hxC with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd (M.cj_eq_iff_normalizer.1 h1) hn'
  · rw [← cj_eq_conjugate, ← cj_eq_conjugate]
    exact ⟨h1, h2⟩

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
