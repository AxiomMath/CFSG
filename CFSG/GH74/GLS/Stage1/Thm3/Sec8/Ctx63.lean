module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx4
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic24
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Lem510
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen5
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Final

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Basic

theorem eq_or_inv_of_cyc {G : Type*} [Group G] [Finite G] {V : Subgroup G} (hV : IsCyclic ↥V) {w w' : G}
    (hw : w ∈ V) (hw' : w' ∈ V) (h4 : orderOf w = 4) (h4' : orderOf w' = 4) :
    w' = w ∨ w' = w⁻¹ := by
  have hcard : Nat.card ↥(Subgroup.zpowers w) = 4 := by rw [Nat.card_zpowers, h4]
  have hmem : w' ∈ Subgroup.zpowers w := by
    refine mem_of_pow_four_eq_one hV (Subgroup.zpowers_le.2 hw)
      (IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num)) (by rw [hcard]) hw' ?_
    rw [← h4']; exact pow_orderOf_eq_one w'
  exact eq_or_inv_of_mem_zpowers_of_orderOf_four h4 h4' hmem

theorem isElemAbelian2_of_sq_one {G : Type*} [Group G] {E : Subgroup G} (hE : ∀ a ∈ E, a * a = 1) :
    IsElementaryAbelian 2 ↥E :=
  { is_comm := ⟨fun a b => Subtype.ext (by
      have hab := hE (a * b) (mul_mem a.2 b.2)
      have haa := hE a a.2
      have hbb := hE b b.2
      calc (a : G) * b = a * (a * b * (a * b)) * b := by rw [hab]; group
        _ = (a * a) * b * a * (b * b) := by group
        _ = b * a := by rw [haa, hbb]; group)⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
      apply Subtype.ext
      simpa [pow_two] using hE x x.2 }

theorem four_of_comm_invol {G : Type*} [Group G] [Finite G] {z u : G} (hz2 : z * z = 1)
    (hu2 : u * u = 1) (hz1 : z ≠ 1) (hu1 : u ≠ 1) (huz : u ≠ z) (hc : z * u = u * z) :
    Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers u) = 4 ∧
      (∀ y ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers u, y = 1 ∨ y = z ∨ y = u ∨ y = u * z) := by
  have hcomm : ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ Subgroup.zpowers u, a * b = b * a := by
    intro a ha b hb
    rcases (mem_zpowers_of_sq' hz2).1 ha with h1 | h1 <;>
      rcases (mem_zpowers_of_sq' hu2).1 hb with h2 | h2
    · rw [h1, h2]
    · rw [h1, h2]; simp
    · rw [h1, h2]; simp
    · rw [h1, h2]; exact hc
  have hnorm : Subgroup.zpowers u ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
    le_normalizer_of_commute' hcomm
  have hcardmul := card_sup_mul_card_inf' hnorm
  have hcz : Nat.card ↥(Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime (by simpa [pow_two] using hz2) hz1
  have hcu : Nat.card ↥(Subgroup.zpowers u) = 2 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime (by simpa [pow_two] using hu2) hu1
  have hinf : Subgroup.zpowers z ⊓ Subgroup.zpowers u = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rcases (mem_zpowers_of_sq' hz2).1 ha.1 with h1 | h1
    · rw [h1]; exact one_mem _
    · rcases (mem_zpowers_of_sq' hu2).1 ha.2 with h2 | h2
      · rw [h2]; exact one_mem _
      · exact absurd (h2.symm.trans h1) huz
  rw [hinf, Subgroup.card_bot, hcz, hcu] at hcardmul
  refine ⟨by omega, ?_⟩
  intro y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute' hcomm hy
  rcases (mem_zpowers_of_sq' hz2).1 ha with h1 | h1 <;>
    rcases (mem_zpowers_of_sq' hu2).1 hb with h2 | h2
  · left; rw [h1, h2, one_mul]
  · right; right; left; rw [h1, h2, one_mul]
  · right; left; rw [h1, h2, mul_one]
  · right; right; right; rw [h1, h2, hc]

end Basic

namespace Fused8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem m4 (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) :
    M.M4 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂ := m4_of_std hII hf.std

theorem z_sq (hf : Fused8 G z S K₁ K₂) : z * z = 1 := by
  have h1 := pow_orderOf_eq_one z
  rw [hf.std.orderOf_z] at h1
  simpa [pow_two] using h1

theorem z_ne (hf : Fused8 G z S K₁ K₂) : z ≠ 1 := by
  intro h1
  have h2 := hf.std.orderOf_z
  rw [h1, orderOf_one] at h2
  omega

theorem z_mem_S (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) : z ∈ S :=
  (hf.m4 hII).z_mem_S

theorem z_mem_P {K : Subgroup G} (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂)
    (hK : K = K₁ ∨ K = K₂) : z ∈ Pof S K :=
  ⟨(hf.m4 hII).z_mem_S, (hf.m4 hII).z_mem_comp hK⟩

theorem z_mem_Q {K : Subgroup G} (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂)
    (hK : K = K₁ ∨ K = K₂) : z ∈ Qof S K :=
  ⟨(hf.m4 hII).z_mem_S, (hf.m4 hII).z_mem_secCent_comp hK⟩

theorem S_pgroup (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) : IsPGroup 2 ↥S :=
  (hf.m4 hII).S_pgroup

theorem S_le_C (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) :
    S ≤ centralizer ({z} : Set G) := (hf.m4 hII).S_syl.1

theorem z_comm (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) {s : G} (hs : s ∈ S) :
    s * z = z * s := by
  exact mem_centralizer_singleton_iff.1 (hf.S_le_C hII hs)

theorem P_comm (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) :
    ∀ a ∈ Pof S K₁, ∀ b ∈ Pof S K₂, a * b = b * a :=
  fun _ ha _ hb => (hf.m4 hII).comm_of_S ha.2 hb.2 ha.1 hb.1

theorem P_inf (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) :
    Pof S K₁ ⊓ Pof S K₂ = zpowers z := by
  have hM := hf.m4 hII
  apply le_antisymm
  · rintro x ⟨⟨hxS, hxK₁⟩, ⟨-, hxK₂⟩⟩
    have hx : x ∈ S ⊓ M.ZsM (pPrimeCoreOf 2) K₁ := ⟨hxS, hxK₁, hM.cs₁ hxK₂⟩
    rw [(hM.S_inf_Zs_comp (Or.inl rfl)).2] at hx
    exact hx
  · exact zpowers_le.2 ⟨hf.z_mem_P hII (Or.inl rfl), hf.z_mem_P hII (Or.inr rfl)⟩

theorem Pz_eq_sup (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) :
    Pz S z = Pof S K₁ ⊔ Pof S K₂ := by
  have hM := hf.m4 hII
  have e1 : M.Pm S K₁ K₂ ⊓ K₁ = Pof S K₁ := by
    unfold M.Pm Pof
    rw [inf_assoc, inf_eq_right.2 (le_sup_left : K₁ ≤ K₁ ⊔ K₂)]
  have e2 : M.Pm S K₁ K₂ ⊓ K₂ = Pof S K₂ := by
    unfold M.Pm Pof
    rw [inf_assoc, inf_eq_right.2 (le_sup_right : K₂ ≤ K₁ ⊔ K₂)]
  rw [Pz_eq hf.std, hM.P_eq, e1, e2]

theorem gq_P (hII : II4_4_4_center) (hq : II4_4_quat) (hf : Fused8 G z S K₁ K₂)
    {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) : Basic.GQ (Pof S K) z := by
  have hstd := hf.std
  obtain ⟨n, hn3, ⟨e⟩⟩ := hq G hstd.simple z hstd.orderOf_z S K hstd.sylow
    (hstd.comp_isPCompIn hK) (hstd.comp_pRank hK)
  have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  have hm : 2 ≤ 2 ^ (n - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact Basic.gq_of_equiv hm e (hf.z_mem_P hII hK) hf.z_sq hf.z_ne

theorem gq_Q₁ (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) : Basic.GQ (Qof S K₁) z := by
  obtain ⟨n, hn3, ⟨e⟩⟩ := hf.p66.1.1
  have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  have hm : 2 ≤ 2 ^ (n - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact Basic.gq_of_equiv hm e (hf.z_mem_Q hII (Or.inl rfl)) hf.z_sq hf.z_ne

theorem gq_Q₂ (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) : Basic.GQ (Qof S K₂) z := by
  obtain ⟨n, hn3, ⟨e⟩⟩ := hf.p66.1.2.1
  have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  have hm : 2 ≤ 2 ^ (n - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact Basic.gq_of_equiv hm e (hf.z_mem_Q hII (Or.inr rfl)) hf.z_sq hf.z_ne

theorem norm_iff (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) {x : G} (hx : x ∈ S) :
    x ∈ normalizer (K₁ : Set G) ↔ x ∈ normalizer (K₂ : Set G) := by
  have hM := hf.m4 hII
  have hxC : x ∈ centralizer ({z} : Set G) := hM.S_syl.1 hx
  have hne : K₁ ≠ K₂ := hf.std.ne
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

theorem swap_of_not_mem (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) {x : G}
    (hx : x ∈ S) (hn : x ∉ S1 S K₁) : conjugate K₁ x = K₂ ∧ conjugate K₂ x = K₁ := by
  have hM := hf.m4 hII
  have hxC : x ∈ centralizer ({z} : Set G) := hM.S_syl.1 hx
  have hn' : x ∉ normalizer (K₁ : Set G) := fun h' => hn ⟨hx, h'⟩
  rcases hM.perm x hxC with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd (M.cj_eq_iff_normalizer.1 h1) hn'
  · rw [← cj_eq_conjugate, ← cj_eq_conjugate]
    exact ⟨h1, h2⟩

theorem P₁_le_Q₂ (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) : Pof S K₁ ≤ Qof S K₂ :=
  fun _ hx => ⟨hx.1, (hf.m4 hII).cs₂ hx.2⟩

theorem P₂_le_Q₁ (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) : Pof S K₂ ≤ Qof S K₁ :=
  fun _ hx => ⟨hx.1, (hf.m4 hII).cs₁ hx.2⟩

theorem S1_pgroup (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) : IsPGroup 2 ↥(S1 S K₁) :=
  (hf.S_pgroup hII).to_le inf_le_left

theorem S1_normalizes_P (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) : ∀ x ∈ S1 S K₁, ∀ p ∈ Pof S K, x * p * x⁻¹ ∈ Pof S K := by
  intro x hx p hp
  have hxK : x ∈ normalizer (K : Set G) := by
    rcases hK with rfl | rfl
    · exact hx.2
    · exact (hf.norm_iff hII hx.1).1 hx.2
  have hxS : x ∈ S := hx.1
  have hpS : p ∈ S := hp.1
  exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hxS hpS) (inv_mem hxS),
    (Subgroup.mem_normalizer_iff.1 hxK p).1 hp.2⟩

theorem S1_normalizes_Q (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) : ∀ x ∈ S1 S K₁, ∀ q ∈ Qof S K, x * q * x⁻¹ ∈ Qof S K := by
  intro x hx q hq
  have hxK : x ∈ normalizer (K : Set G) := by
    rcases hK with rfl | rfl
    · exact hx.2
    · exact (hf.norm_iff hII hx.1).1 hx.2
  exact conj_mem_Qof hx.1 hxK hq

theorem swap_P₁ (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) {t x : G} (ht : t ∈ S)
    (hn : t ∉ S1 S K₁) (hx : x ∈ Pof S K₁) : t * x * t⁻¹ ∈ Pof S K₂ := by
  obtain ⟨-, hK⟩ := hf.swap_of_not_mem hII ht hn
  have h1 : x ∈ conjugate K₂ t := by rw [hK]; exact hx.2
  have h2 : t * x * t⁻¹ ∈ K₂ := mem_conjugate_iff.1 h1
  exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem ht hx.1) (inv_mem ht), h2⟩

theorem swap_P₂ (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) {t x : G} (ht : t ∈ S)
    (hn : t ∉ S1 S K₁) (hx : x ∈ Pof S K₂) : t * x * t⁻¹ ∈ Pof S K₁ := by
  obtain ⟨hK, -⟩ := hf.swap_of_not_mem hII ht hn
  have h1 : x ∈ conjugate K₁ t := by rw [hK]; exact hx.2
  have h2 : t * x * t⁻¹ ∈ K₁ := mem_conjugate_iff.1 h1
  exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem ht hx.1) (inv_mem ht), h2⟩

theorem swap_Q₂ (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) {t x : G} (ht : t ∈ S)
    (hn : t ∉ S1 S K₁) (hx : x ∈ Qof S K₂) : t * x * t⁻¹ ∈ Qof S K₁ := by
  obtain ⟨hK, -⟩ := hf.swap_of_not_mem hII ht hn
  have h1 : x ∈ cSec (conjugate K₁ t) := by rw [hK]; exact hx.2
  have h2 : t * x * t⁻¹ ∈ cSec K₁ := mem_cSec_conjugate.1 h1
  exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem ht hx.1) (inv_mem ht), h2⟩

theorem swap_Q₁ (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) {t x : G} (ht : t ∈ S)
    (hn : t ∉ S1 S K₁) (hx : x ∈ Qof S K₁) : t * x * t⁻¹ ∈ Qof S K₂ := by
  obtain ⟨-, hK⟩ := hf.swap_of_not_mem hII ht hn
  have h1 : x ∈ cSec (conjugate K₂ t) := by rw [hK]; exact hx.2
  have h2 : t * x * t⁻¹ ∈ cSec K₂ := mem_cSec_conjugate.1 h1
  exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem ht hx.1) (inv_mem ht), h2⟩

theorem invol_P_conj (hII : II4_4_4_center) (h31 : IVK_3_1a_lifted) (hf : Fused8 G z S K₁ K₂) :
    ∀ x ∈ Pz S z, orderOf x = 2 → IsConj z x := by
  obtain ⟨u', hu'P, hu'c, hu'z⟩ := hf.fused
  have hord' : orderOf u' = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hu'c
    rw [← hc]
    have := (MulAut.conj c).orderOf_eq z
    rw [MulAut.conj_apply] at this
    rw [this, hf.std.orderOf_z]
  exact (lemma_4_2 hII h31 G z S K₁ K₂ hf.std
    ⟨u', Subgroup.mem_sup_left hu'P, hord', hu'c, hu'z⟩).1

theorem S1_norm_S (hf : Fused8 G z S K₁ K₂) (hS : ¬ ∀ t ∈ S, t ∈ S1 S K₁) :
    ∀ s ∈ S, ∀ x ∈ S1 S K₁, s * x * s⁻¹ ∈ S1 S K₁ := by
  have h2 : (S1 S K₁).relIndex S = 2 := by
    have h1 := hf.p66.2.1.1
    have h0 := Basic.relIndex_ne_zero' (S1 S K₁) S
    have h1' : (S1 S K₁).relIndex S ≠ 1 := by
      intro h
      rw [Subgroup.relIndex_eq_one] at h
      exact hS (fun t ht => h ht)
    omega
  have hN : ((S1 S K₁).subgroupOf S).Normal := by
    have : ((S1 S K₁).subgroupOf S).index = 2 := h2
    exact Subgroup.normal_of_index_eq_two this
  intro s hs x hx
  have hx' : (⟨x, hx.1⟩ : ↥S) ∈ (S1 S K₁).subgroupOf S := hx
  have := hN.conj_mem _ hx' ⟨s, hs⟩
  exact this

theorem S1_relIndex_two (hf : Fused8 G z S K₁ K₂) (hS : ¬ ∀ t ∈ S, t ∈ S1 S K₁) :
    (S1 S K₁).relIndex S = 2 := by
  have h1 := hf.p66.2.1.1
  have h0 := Basic.relIndex_ne_zero' (S1 S K₁) S
  have h1' : (S1 S K₁).relIndex S ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    exact hS (fun t ht => h ht)
  omega

omit [Finite G] in
theorem inv_not_mem {t : G} (htn : t ∉ S1 S K₁) : t⁻¹ ∉ S1 S K₁ := fun h => htn (by simpa using inv_mem h)

theorem exists_W (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) :
    ∃ W₁ W₂ : Subgroup G, IsMaxCyc W₁ (Qof S K₁) ∧ IsMaxCyc W₂ (Qof S K₂) ∧
      NormedBy W₁ (S1 S K₁) ∧ NormedBy W₂ (S1 S K₁) ∧
      2 * Nat.card ↥W₁ = Nat.card ↥(Qof S K₁) ∧ 2 * Nat.card ↥W₂ = Nat.card ↥(Qof S K₂) ∧
      (∀ t ∈ S, t ∉ S1 S K₁ → (∀ w ∈ W₁, t * w * t⁻¹ ∈ W₂) ∧ ∀ w ∈ W₂, t * w * t⁻¹ ∈ W₁) := by
  have hQ₁ := hf.gq_Q₁ hII
  have hQ₂ := hf.gq_Q₂ hII
  have hQ₁2 : IsPGroup 2 ↥(Qof S K₁) := (hf.S_pgroup hII).to_le inf_le_left
  have hQ₂2 : IsPGroup 2 ↥(Qof S K₂) := (hf.S_pgroup hII).to_le inf_le_left
  have hT := hf.S1_pgroup hII
  obtain ⟨W₁, hW₁Q, hW₁c, hW₁m, hW₁T, hW₁card⟩ := Basic.GQ.exists_invariant_maxCyclic hQ₁ hQ₁2 hT
    (hf.S1_normalizes_Q hII (Or.inl rfl))
  by_cases hS : ∀ t ∈ S, t ∈ S1 S K₁
  · obtain ⟨W₂, hW₂Q, hW₂c, hW₂m, hW₂T, hW₂card⟩ :=
      Basic.GQ.exists_invariant_maxCyclic hQ₂ hQ₂2 hT (hf.S1_normalizes_Q hII (Or.inr rfl))
    exact ⟨W₁, W₂, ⟨hW₁Q, hW₁c, hW₁m⟩, ⟨hW₂Q, hW₂c, hW₂m⟩, hW₁T, hW₂T, hW₁card, hW₂card,
      fun t ht hn => absurd (hS t ht) hn⟩
  · push Not at hS
    obtain ⟨t, htS, htn⟩ := hS
    have hS' : ¬ ∀ t ∈ S, t ∈ S1 S K₁ := fun h => htn (h t htS)
    have hN := hf.S1_norm_S hS'
    have hi := hf.S1_relIndex_two hS'
    have htiS : t⁻¹ ∈ S := inv_mem htS
    have hti : t⁻¹ ∉ S1 S K₁ := inv_not_mem htn
    set W₂ : Subgroup G := conjugate W₁ t⁻¹ with hW₂def
    have hmem₂ : ∀ x, x ∈ W₂ ↔ t⁻¹ * x * t ∈ W₁ := by
      intro x
      rw [hW₂def, mem_conjugate_iff]
      simp
    have hW₂Q : W₂ ≤ Qof S K₂ := by
      intro x hx
      have h1 := hW₁Q ((hmem₂ x).1 hx)
      have h2 := hf.swap_Q₁ hII htS htn h1
      have e : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
      rwa [e] at h2
    have hW₂c : IsCyclic ↥W₂ := by
      rw [hW₂def, conjugate_eq_comap]; exact Basic.cyclic_comap_conj _ hW₁c t⁻¹
    have hW₂W₁ : Nat.card ↥W₂ = Nat.card ↥W₁ := by
      rw [hW₂def, conjugate_eq_comap]; exact Basic.card_comap_conj _ _
    have hQQ : Nat.card ↥(Qof S K₁) = Nat.card ↥(Qof S K₂) := by
      apply le_antisymm
      · have hle : (Qof S K₁).comap (MulAut.conj t⁻¹).toMonoidHom ≤ Qof S K₂ := by
          intro x hx
          have h1 : t⁻¹ * x * t ∈ Qof S K₁ := by simpa [MulAut.conj_apply] using hx
          have h2 := hf.swap_Q₁ hII htS htn h1
          have e : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
          rwa [e] at h2
        have := Subgroup.card_le_of_le hle
        rwa [Basic.card_comap_conj] at this
      · have hle : (Qof S K₂).comap (MulAut.conj t).toMonoidHom ≤ Qof S K₁ := by
          intro x hx
          have h1 : t * x * t⁻¹ ∈ Qof S K₂ := by simpa [MulAut.conj_apply] using hx
          have h2 := hf.swap_Q₂ hII htiS hti h1
          have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
          rwa [e] at h2
        have := Subgroup.card_le_of_le hle
        rwa [Basic.card_comap_conj] at this
    have hcard₂ : 2 * Nat.card ↥W₂ = Nat.card ↥(Qof S K₂) := by rw [hW₂W₁, ← hQQ]; exact hW₁card
    have hW₂T : NormedBy W₂ (S1 S K₁) := by
      intro x hx w hw
      rw [hmem₂] at hw ⊢
      have hx' : t⁻¹ * x * t ∈ S1 S K₁ := by
        have := hN t⁻¹ htiS x hx
        simpa using this
      have := hW₁T _ hx' _ hw
      have e : (t⁻¹ * x * t) * (t⁻¹ * w * t) * (t⁻¹ * x * t)⁻¹ = t⁻¹ * (x * w * x⁻¹) * t := by group
      rwa [e] at this
    refine ⟨W₁, W₂, ⟨hW₁Q, hW₁c, hW₁m⟩, ⟨hW₂Q, hW₂c, Basic.GQ.maxCyclic_of_index_two hQ₂ hcard₂⟩,
      hW₁T, hW₂T, hW₁card, hcard₂, ?_⟩
    intro s hsS hsn
    have hsiS : s⁻¹ ∈ S := inv_mem hsS
    have hsi : s⁻¹ ∉ S1 S K₁ := inv_not_mem hsn
    constructor
    · intro w hw
      rw [hmem₂]
      have h1 : t⁻¹ * s ∈ S1 S K₁ := by
        have := Basic.mul_inv_mem_of_relIndex_two hi htiS hsiS hti hsi
        simpa using this
      have := hW₁T _ h1 _ hw
      have e : (t⁻¹ * s) * w * (t⁻¹ * s)⁻¹ = t⁻¹ * (s * w * s⁻¹) * t := by group
      rwa [e] at this
    · intro w hw
      have hw' := (hmem₂ w).1 hw
      have h1 : s * t ∈ S1 S K₁ := by
        have := Basic.mul_inv_mem_of_relIndex_two hi hsS htiS hsn hti
        simpa using this
      have := hW₁T _ h1 _ hw'
      have e : (s * t) * (t⁻¹ * w * t) * (s * t)⁻¹ = s * w * s⁻¹ := by group
      rwa [e] at this

theorem exists_w (hII : II4_4_4_center) (hq : II4_4_quat) (hf : Fused8 G z S K₁ K₂)
    {W₁ W₂ : Subgroup G} (hW₁ : IsMaxCyc W₁ (Qof S K₁)) (hW₂ : IsMaxCyc W₂ (Qof S K₂))
    (hc₁ : 2 * Nat.card ↥W₁ = Nat.card ↥(Qof S K₁))
    (hc₂ : 2 * Nat.card ↥W₂ = Nat.card ↥(Qof S K₂)) :
    (∃ w₁ ∈ W₁ ⊓ Pof S K₂, orderOf w₁ = 4) ∧ ∃ w₂ ∈ W₂ ⊓ Pof S K₁, orderOf w₂ = 4 := by
  have hrel₁ : W₁.relIndex (Qof S K₁) = 2 := by
    have h1 := Basic.card_mul_relIndex_of_le hW₁.1
    have hpos : 0 < Nat.card ↥W₁ := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (by omega)
  have hrel₂ : W₂.relIndex (Qof S K₂) = 2 := by
    have h1 := Basic.card_mul_relIndex_of_le hW₂.1
    have hpos : 0 < Nat.card ↥W₂ := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (by omega)
  have hP₁ := hf.gq_P hII hq (Or.inl rfl)
  have hP₂ := hf.gq_P hII hq (Or.inr rfl)
  have h2₂ := Basic.two_mul_card_inf (hf.P₂_le_Q₁ hII) hW₁.2.1 hrel₁ hP₂.not_isCyclic
  have h2₁ := Basic.two_mul_card_inf (hf.P₁_le_Q₂ hII) hW₂.2.1 hrel₂ hP₁.not_isCyclic
  have h8₂ := hP₂.eight_le_card
  have h8₁ := hP₁.eight_le_card
  refine ⟨Basic.exists_order_four (Basic.isCyclic_of_le inf_le_left hW₁.2.1)
    ((hf.S_pgroup hII).to_le (inf_le_right.trans inf_le_left)) (by omega),
    Basic.exists_order_four (Basic.isCyclic_of_le inf_le_left hW₂.2.1)
    ((hf.S_pgroup hII).to_le (inf_le_right.trans inf_le_left)) (by omega)⟩

omit [Finite G] in
theorem conj_u_alg {w₁ w₂ z s : G} (hz2 : z * z = 1) (hw₁ : w₁ * w₁ = z) (hw₂ : w₂ * w₂ = z)
    (hc : w₁ * w₂ = w₂ * w₁) (hz₁ : z * w₁ = w₁ * z) (hz₂ : z * w₂ = w₂ * z)
    (h : ((s * w₁ * s⁻¹ = w₁ ∨ s * w₁ * s⁻¹ = w₁⁻¹) ∧ (s * w₂ * s⁻¹ = w₂ ∨ s * w₂ * s⁻¹ = w₂⁻¹)) ∨
      ((s * w₁ * s⁻¹ = w₂ ∨ s * w₁ * s⁻¹ = w₂⁻¹) ∧ (s * w₂ * s⁻¹ = w₁ ∨ s * w₂ * s⁻¹ = w₁⁻¹))) :
    s * (w₁ * w₂) * s⁻¹ = w₁ * w₂ ∨ s * (w₁ * w₂) * s⁻¹ = (w₁ * w₂) * z := by
  have hi₁ : w₁⁻¹ = w₁ * z := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hw₁, hz2])
  have hi₂ : w₂⁻¹ = w₂ * z := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hw₂, hz2])
  have e : s * (w₁ * w₂) * s⁻¹ = (s * w₁ * s⁻¹) * (s * w₂ * s⁻¹) := by group
  have hzz : ∀ a : G, a * z * z = a := fun a => by rw [mul_assoc, hz2, mul_one]
  rw [e]
  rcases h with ⟨h1 | h1, h2 | h2⟩ | ⟨h1 | h1, h2 | h2⟩ <;> rw [h1, h2]
  · left; rfl
  · right; rw [hi₂, ← mul_assoc]
  · right; rw [hi₁]
    calc w₁ * z * w₂ = w₁ * (z * w₂) := by group
      _ = w₁ * (w₂ * z) := by rw [hz₂]
      _ = w₁ * w₂ * z := by group
  · left; rw [hi₁, hi₂]
    calc w₁ * z * (w₂ * z) = w₁ * (z * w₂) * z := by group
      _ = w₁ * (w₂ * z) * z := by rw [hz₂]
      _ = w₁ * w₂ * z * z := by group
      _ = w₁ * w₂ := hzz _
  · left; exact hc.symm
  · right; rw [hi₁]
    calc w₂ * (w₁ * z) = (w₂ * w₁) * z := by group
      _ = w₁ * w₂ * z := by rw [hc]
  · right; rw [hi₂]
    calc w₂ * z * w₁ = w₂ * (z * w₁) := by group
      _ = w₂ * (w₁ * z) := by rw [hz₁]
      _ = (w₂ * w₁) * z := by group
      _ = w₁ * w₂ * z := by rw [hc]
  · left; rw [hi₁, hi₂]
    calc w₂ * z * (w₁ * z) = w₂ * (z * w₁) * z := by group
      _ = w₂ * (w₁ * z) * z := by rw [hz₁]
      _ = w₂ * w₁ * z * z := by group
      _ = w₂ * w₁ := hzz _
      _ = w₁ * w₂ := hc.symm

structure Pre8 (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ W₁ W₂ U : Subgroup G) (u : G) :
    Prop where
  fused : Fused8 G z S K₁ K₂
  W₁_max : IsMaxCyc W₁ (Qof S K₁)
  W₂_max : IsMaxCyc W₂ (Qof S K₂)
  W₁_norm : NormedBy W₁ (S1 S K₁)
  W₂_norm : NormedBy W₂ (S1 S K₁)
  U_le : U ≤ W₁ ⊔ W₂
  U_four : IVK.IsFourSubgroup U
  U_norm : NormedBy U S
  z_mem : z ∈ U
  u_mem : u ∈ U
  u_ne : u ∉ zpowers z
  u_conj : IsConj z u

end Fused8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
