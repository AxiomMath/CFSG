module

public import CFSG.LargeExtraspecial.S3Basic
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith

theorem mul_mem_iff_of_relIndex_eq_two {G : Type*} [Group G] {H K : Subgroup G}
    (h : H.relIndex K = 2) {a b : G} (ha : a ∈ K) (hb : b ∈ K) :
    a * b ∈ H ↔ (a ∈ H ↔ b ∈ H) := by
  have := mul_mem_iff_of_index_two (H := H.subgroupOf K) h (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  simpa [mem_subgroupOf] using this

namespace Setting

variable {G : Type*} [Group G] (S : Setting G)

theorem exists_not_commute : ∃ a ∈ S.QG, ∃ b ∈ S.QG, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hbot : commutator S.Q = ⊥ := by
    rw [_root_.commutator_def, commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [mem_centralizer_iff]
    intro y _
    exact Subtype.ext (Subtype.ext (h _ (S.coe_mem_QG y) _ (S.coe_mem_QG x)))
  have h2 := S.extraspecial.2.2.2
  rw [← S.extraspecial.2.1, hbot, card_bot] at h2
  exact absurd h2 (by norm_num)

variable [Finite G]

theorem exists_sq_eq_z : ∃ y ∈ S.QG, y ^ 2 = S.z := by
  by_contra h
  push Not at h
  have h1 : ∀ y ∈ S.QG, y * y = 1 := fun y hy => by
    rw [← pow_two]
    exact (S.sq_eq_one_or_z hy).resolve_right (h y hy)
  obtain ⟨a, ha, b, hb, hab⟩ := S.exists_not_commute
  apply hab
  have hab1 := h1 _ (S.QG.mul_mem ha hb)
  calc a * b = a * (a * b * (a * b)) * b := by rw [hab1, mul_one]
    _ = (a * a) * b * a * (b * b) := by group
    _ = b * a := by rw [h1 a ha, h1 b hb]; group

omit [Finite G] in
theorem isPGroup_QG : IsPGroup 2 S.QG :=
  S.extraspecial.1.of_equiv (S.Q.equivMapOfInjective S.M.subtype S.M.subtype_injective)

theorem z_mem_of_relIndex_eq_two {F : Subgroup G} (hF : F.relIndex S.QG = 2) : S.z ∈ F := by
  obtain ⟨y, hy, hyz⟩ := S.exists_sq_eq_z
  have := (mul_mem_iff_of_relIndex_eq_two hF hy hy).mpr Iff.rfl
  rwa [← pow_two, hyz] at this

theorem mem_QG_of_sq_eq_one_of_commute {F : Subgroup G} (hFQ : F ≤ S.QG)
    (hF : F.relIndex S.QG = 2) {x : G} (hx : x ^ 2 = 1) (hxF : ∀ f ∈ F, x * f = f * x) :
    x ∈ S.QG := by
  have hxx : x * x = 1 := by rw [← pow_two, hx]
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hxM : x ∈ S.M := S.mem_M_iff.mpr (hxF _ (S.z_mem_of_relIndex_eq_two hF))
  by_contra hxQ
  obtain ⟨w, hwQ, hxw⟩ : ∃ w ∈ S.QG, x * w ≠ w * x := by
    by_contra h
    push Not at h
    exact hxQ (S.mem_QG_of_commute hxM h)
  have hwF : w ∉ F := fun h => hxw (hxF w h)
  set c := x * w * x⁻¹ * w⁻¹ with hc
  have hcQ : c ∈ S.QG := S.QG.mul_mem (S.conj_mem_QG hxM hwQ) (S.QG.inv_mem hwQ)
  have hc1 : c ≠ 1 := by
    intro h
    apply hxw
    calc x * w = c * (w * x) := by rw [hc]; group
      _ = w * x := by rw [h, one_mul]
  have hfx : ∀ f ∈ F, x * f * x⁻¹ = f := fun f hf => by rw [hxF f hf]; group
  have key : ∀ v ∈ S.QG, v ∉ F → x * v * x⁻¹ * v⁻¹ = c := by
    intro v hvQ hvF
    have hf : w⁻¹ * v ∈ F :=
      (mul_mem_iff_of_relIndex_eq_two hF (S.QG.inv_mem hwQ) hvQ).mpr
        ⟨fun h => absurd (inv_inv w ▸ F.inv_mem h) hwF, fun h => absurd h hvF⟩
    calc x * v * x⁻¹ * v⁻¹
        = x * w * x⁻¹ * (x * (w⁻¹ * v) * x⁻¹) * (w⁻¹ * v)⁻¹ * w⁻¹ := by group
      _ = c := by rw [hfx _ hf, hc]; group
  have hcF : ∀ f ∈ F, f * c = c * f := by
    intro f hf
    have hfw : f * w ∉ F := fun h =>
      hwF ((mul_mem_iff_of_relIndex_eq_two hF (hFQ hf) hwQ).mp h |>.mp hf)
    have h1 := key _ (S.QG.mul_mem (hFQ hf) hwQ) hfw
    have h2 : x * (f * w) * x⁻¹ * (f * w)⁻¹ = f * c * f⁻¹ := by
      calc x * (f * w) * x⁻¹ * (f * w)⁻¹
          = (x * f * x⁻¹) * (x * w * x⁻¹ * w⁻¹) * f⁻¹ := by group
        _ = f * c * f⁻¹ := by rw [hfx f hf]
    rw [h2] at h1
    calc f * c = f * c * f⁻¹ * f := by group
      _ = c * f := by rw [h1]
  have hxc : x * c * x⁻¹ = c⁻¹ := by
    have hxw' : x * w * x⁻¹ = c * w := by rw [hc]; group
    have h3 : w = x * c * x⁻¹ * (c * w) := by
      calc w = x * (x * w * x⁻¹) * x⁻¹ := by
            rw [show x * (x * w * x⁻¹) * x⁻¹ = (x * x) * w * (x * x)⁻¹ by group, hxx]; group
        _ = x * (c * w) * x⁻¹ := by rw [hxw']
        _ = x * c * x⁻¹ * (x * w * x⁻¹) := by group
        _ = x * c * x⁻¹ * (c * w) := by rw [hxw']
    calc x * c * x⁻¹ = x * c * x⁻¹ * (c * w) * w⁻¹ * c⁻¹ := by group
      _ = c⁻¹ := by rw [← h3]; group
  by_cases hcF' : c ∈ F
  ·
    have hcc : c⁻¹ = c := by rw [← hxc, hfx c hcF']
    have hcomm : ∀ v ∈ S.QG, c * v = v * c := by
      intro v hvQ
      by_cases hvF : v ∈ F
      · exact (hcF v hvF).symm
      · have hv2 : v * v ∈ F := (mul_mem_iff_of_relIndex_eq_two hF hvQ hvQ).mpr Iff.rfl
        have hxv : x * v * x⁻¹ = c * v := by
          calc x * v * x⁻¹ = x * v * x⁻¹ * v⁻¹ * v := by group
            _ = c * v := by rw [key v hvQ hvF]
        have h4 : c * v * (c * v) = v * v := by
          rw [← hxv]
          calc x * v * x⁻¹ * (x * v * x⁻¹) = x * (v * v) * x⁻¹ := by group
            _ = v * v := hfx _ hv2
        calc c * v = c * v * (c * v) * v⁻¹ * c⁻¹ := by group
          _ = v * c := by rw [h4, hcc]; group
    have hcz : c = S.z := (S.eq_one_or_z_of_commute hcQ hcomm).resolve_left hc1
    apply hxQ
    refine S.mem_QG_of_cl_conj hxM fun v hvQ => ?_
    by_cases hvF : v ∈ F
    · rw [hfx v hvF]
    · have hxv : x * v * x⁻¹ = v * S.z := by
        calc x * v * x⁻¹ = x * v * x⁻¹ * v⁻¹ * v := by group
          _ = S.z * v := by rw [key v hvQ hvF, hcz]
          _ = v * S.z := (S.z_comm_QG hvQ).symm
      rw [hxv, S.cl_mul_z hvQ]
  ·
    have h5 := key c hcQ hcF'
    have h6 : c ^ 3 = 1 := by
      have h7 : x * c * x⁻¹ = c * c := by
        calc x * c * x⁻¹ = x * c * x⁻¹ * c⁻¹ * c := by group
          _ = c * c := by rw [h5]
      rw [hxc] at h7
      calc c ^ 3 = c * (c * c) := pow_three c
        _ = 1 := by rw [← h7]; group
    apply hc1
    have h8 : c ^ 4 = c ^ 3 * c := pow_succ c 3
    rw [S.pow_four_eq_one hcQ, h6, one_mul] at h8
    exact h8.symm

theorem omegaOne_centralizer_le {F : Subgroup G} (hFQ : F ≤ S.QG) (hF : F.relIndex S.QG = 2) :
    closure {x | x ∈ centralizer (F : Set G) ∧ x ^ 2 = 1} ≤ S.QG := by
  rw [closure_le]
  rintro x ⟨hxc, hx2⟩
  refine S.mem_QG_of_sq_eq_one_of_commute hFQ hF hx2 fun f hf => ?_
  exact (mem_centralizer_iff.mp hxc f hf).symm

theorem omegaOne_centralizer_le_of_isCoatom {F : Subgroup G} (hFQ : F ≤ S.QG)
    (hF : IsCoatom (F.subgroupOf S.QG)) :
    closure {x | x ∈ centralizer (F : Set G) ∧ x ^ 2 = 1} ≤ S.QG := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact S.omegaOne_centralizer_le hFQ
    (CFSG.SectionRank.Ccomm.normal_and_index_eq_of_isCoatom S.isPGroup_QG hF).2

theorem centralizer_singleton_inf_QG {t : G} (ht : t ∈ S.QG) :
    S.QG ⊓ centralizer ({t} : Set G) =
      S.clPre (LinearMap.BilinForm.orthogonal S.q.polarBilin (ZMod 2 ∙ S.cl t)) := by
  ext y
  simp only [mem_inf, mem_centralizer_singleton_iff, mem_clPre,
    LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_span_singleton, polarBilin_apply_apply]
  constructor
  · rintro ⟨hy, h⟩
    refine ⟨hy, ?_⟩
    rintro _ ⟨a, rfl⟩
    rw [polar_smul_left, (S.polar_cl_eq_zero_iff ht hy).mpr h.symm, smul_zero]
  · rintro ⟨hy, h⟩
    exact ⟨hy, ((S.polar_cl_eq_zero_iff ht hy).mp (h _ ⟨1, one_smul _ _⟩)).symm⟩

theorem relIndex_centralizer_eq_two {t : G} (ht : t ∈ S.QG) (ht1 : t ≠ 1) (htz : t ≠ S.z) :
    (S.QG ⊓ centralizer ({t} : Set G)).relIndex S.QG = 2 := by
  obtain ⟨a, ha, hat⟩ : ∃ a ∈ S.QG, a * t ≠ t * a := by
    by_contra h
    push Not at h
    rcases S.eq_one_or_z_of_commute ht fun y hy => (h y hy).symm with h1 | h1
    · exact ht1 h1
    · exact htz h1
  rw [relIndex_eq_two_iff]
  refine ⟨a, ha, fun b hb => ?_⟩
  have h1 : polar S.q (S.cl a) (S.cl t) = 1 := (S.polar_cl_eq_one_iff ha ht).mpr hat
  have h2 : polar S.q (S.cl (b * a)) (S.cl t) = polar S.q (S.cl b) (S.cl t) + 1 := by
    rw [S.cl_mul hb ha, polar_add_left, h1]
  have hiff : ∀ y ∈ S.QG, y ∈ S.QG ⊓ centralizer ({t} : Set G) ↔
      polar S.q (S.cl y) (S.cl t) = 0 := fun y hy => by
    rw [mem_inf, mem_centralizer_singleton_iff, S.polar_cl_eq_zero_iff hy ht]
    exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
  rw [hiff _ (S.QG.mul_mem hb ha), hiff _ hb, h2]
  rcases zmod2_cases (polar S.q (S.cl b) (S.cl t)) with h | h <;> rw [h] <;> decide

theorem mem_centralizer_centralizer_iff {t : G} (ht : t ∈ S.QG) {x : G} :
    x ∈ S.QG ⊓ centralizer ((S.QG ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) ↔
      x = 1 ∨ x = S.z ∨ x = t ∨ x = t * S.z := by
  rw [S.centralizer_inf_QG_eq_clPre inf_le_left, S.centralizer_singleton_inf_QG ht, S.clSub_clPre,
    LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl, mem_clPre,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨hx, a, ha⟩
    rcases zmod2_cases a with rfl | rfl
    · rw [zero_smul, eq_comm, S.cl_eq_zero_iff hx] at ha
      rcases ha with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rw [one_smul, S.cl_eq_cl_iff ht hx] at ha
      rcases ha with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨S.QG.one_mem, 0, by rw [zero_smul, S.cl_one]⟩
    · exact ⟨S.z_mem_QG, 0, by rw [zero_smul, S.cl_z]⟩
    · exact ⟨ht, 1, one_smul _ _⟩
    · exact ⟨S.QG.mul_mem ht S.z_mem_QG, 1, by rw [one_smul, S.cl_mul_z ht]⟩

end Setting

end CFSG.LargeExtraspecial
