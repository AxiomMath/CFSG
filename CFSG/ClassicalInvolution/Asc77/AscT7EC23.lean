module

public import CFSG.ClassicalInvolution.Asc77.AscT7EFrame
public import CFSG.ClassicalInvolution.Asc77.AscT7BSetup23

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7E

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

omit [Finite G] in
theorem exists_mem_MGrp_of_mem_muGroup (y : ↥(muGroup Ω W)) :
    ∃ m ∈ MGrp Ω W, (y : NQuot (W ⊔ OCW W)) = Thompson.piG W m := by
  obtain ⟨m, hm, hy⟩ := Thompson.mem_muGroup_iff.mp y.2
  have hMN : MGrp Ω W ≤ Subgroup.normalizer (OCW W : Set G) :=
    (Thompson.MGrp_le_normalizer Ω W).trans (Thompson.normalizer_le_normalizer_OCW W)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right (MGrp Ω W) (OCW W) hMN] at hm
  obtain ⟨m₀, hm₀, c, hc, rfl⟩ := hm
  refine ⟨m₀, hm₀, ?_⟩
  have h0 : m₀ ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W hm₀
  have hcN : c ∈ Subgroup.normalizer (W : Set G) := Thompson.OCW_le_normalizer W hc
  rw [hy, Thompson.piG_mul h0 hcN, Thompson.piG_of_mem_sup (Subgroup.mem_sup_right hc), mul_one]

end T7E

variable (p f : ℕ) [Fact p.Prime]

theorem c23_setupSetting_proved : C23_setupSetting p f := by
  intro G _ _ _ Ω K K' z hs W hW hS4 hE hzW
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hKK' : K' ≠ K := hs.hne
  have hz : IsUniqueInvolution K z := hs.hz
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hst hW
  obtain ⟨e, F, he, hρK, hρ'K, hFz, hab, hcomm, hac, -⟩ := T7E.exists_frame4 hs hW hzW hS4
  obtain ⟨x₁, x₂, x₃, m, hm, h₁, h₂, h₃, o₁, o₂, o₃, z₁, z₂, z₃, k₁, k₂, k₃, hfix⟩ :=
    F.exists_structure c he hab hcomm hac
  rw [hρK] at k₁
  rw [hρ'K] at k₂
  rw [hFz] at z₁ z₂
  have m₁ : x₁ ∈ W := (h₁ ▸ Subgroup.mem_zpowers x₁ : x₁ ∈ F.ρ.R ⊓ W).2
  have m₂ : x₂ ∈ W := (h₂ ▸ Subgroup.mem_zpowers x₂ : x₂ ∈ F.ρ'.R ⊓ W).2
  have m₃ : x₃ ∈ W := (h₃ ▸ Subgroup.mem_zpowers x₃ : x₃ ∈ F.ρ₃.R ⊓ W).2
  have c12 : Commute x₁ x₂ := c.comm_W _ m₁ _ m₂
  have c13 : Commute x₁ x₃ := c.comm_W _ m₁ _ m₃
  have c23 : Commute x₂ x₃ := c.comm_W _ m₂ _ m₃
  have o₃' : x₃ ^ (4 * m) = 1 := by rw [← o₃]; exact pow_orderOf_eq_one x₃
  obtain ⟨hsq_e, hsq_u, hue⟩ := A3Mod.triple_facts c12 c13 c23 o₃' (z₁.trans z₂.symm)
  set e₄ := (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m with he₄
  obtain ⟨a, haE, ha1⟩ : ∃ a ∈ W ⊓ centerIn (Subgroup.normalizer (W : Set G)), a ≠ 1 := by
    by_contra hno
    push Not at hno
    exact hE (eq_bot_iff.mpr fun a ha => Subgroup.mem_bot.mpr (hno a ha))
  have hae : a = e₄ := (hfix a haE).resolve_left ha1
  have he₄E : e₄ ∈ W ⊓ centerIn (Subgroup.normalizer (W : Set G)) := hae ▸ haE
  have he₄1 : e₄ ≠ 1 := hae ▸ ha1
  set u := x₁ ^ m * (x₂ ^ m)⁻¹ with hu
  have hu4 : orderOf (x₁ ^ m) = 4 := by
    have := orderOf_pow_of_dvd (x := x₁) (n := m) (by omega) (by rw [o₁]; exact dvd_mul_left m 4)
    rwa [o₁, Nat.mul_div_cancel _ hm] at this
  have hu4' : orderOf (x₂ ^ m) = 4 := by
    have := orderOf_pow_of_dvd (x := x₂) (n := m) (by omega) (by rw [o₂]; exact dvd_mul_left m 4)
    rwa [o₂, Nat.mul_div_cancel _ hm] at this
  have hmem₁ : x₁ ^ m ∈ K := K.pow_mem k₁ m
  have hmem₂ : (x₂ ^ m)⁻¹ ∈ K' := K'.inv_mem (K'.pow_mem k₂ m)
  have huK : u ∈ K ⊔ K' := Subgroup.mul_mem_sup hmem₁ hmem₂
  have huW : u ∈ W := W.mul_mem (W.pow_mem m₁ m) (W.inv_mem (W.pow_mem m₂ m))
  have hu2 : u * u = 1 := by rw [← pow_two]; exact hsq_u
  have hu1 : u ≠ 1 := by
    intro h
    have : x₁ ^ m = x₂ ^ m := mul_inv_eq_one.mp h
    refine T7A.not_mem_inf_of_orderOf_four hΩ hK hK' hKK' hu4' (this ▸ hmem₁) (K'.pow_mem k₂ m)
  have huz : u ≠ z := by
    intro h
    have h1 : (x₂ ^ m)⁻¹ = (x₁ ^ m)⁻¹ * z := by rw [← h, hu]; group
    have h2 : (x₂ ^ m)⁻¹ ∈ K := by
      rw [h1]
      exact K.mul_mem (K.inv_mem hmem₁) hz.mem
    refine T7A.not_mem_inf_of_orderOf_four hΩ hK hK' hKK'
      (by rw [orderOf_inv]; exact hu4') h2 hmem₂
  obtain ⟨y, hy⟩ := S4.exists_conj_of_mem he (T7D.imgQ_mem F.ρ) (T7D.imgQ_mem F.ρ₃)
  obtain ⟨g, hgM, hyg⟩ := T7E.exists_mem_MGrp_of_mem_muGroup y
  have hgN : g ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W hgM
  have himg : Thompson.piG W g * F.ρ.img * (Thompson.piG W g)⁻¹ = F.ρ₃.img := by
    rw [← hyg]
    exact congrArg Subtype.val hy
  have hKg : conjSub g F.ρ.K = F.ρ₃.K :=
    c.K_eq_of_img_eq (T7D.conjRep c.hΩ hgN F.ρ) F.ρ₃ (by rw [T7D.conjRep_img, himg])
  have hzg : g * z * g⁻¹ = F.j := by
    have := F.hz.conj g
    rw [hKg] at this
    rw [hFz] at this
    exact (F.hj.eq this).symm
  have hj : u * e₄ = F.j := by rw [hue, z₃]
  refine ⟨u, e₄, g, ⟨hW, hS4, hzW, huK, huW, hu2, hu1, huz, ?_, he₄1, ?_, hgM, ?_⟩⟩
  · apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact he₄E
    · intro b hb
      rcases hfix b hb with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.subset_closure (Set.mem_singleton _)
  · rw [← pow_two]; exact hsq_e
  · rw [hzg, hj]

end CFSG.ClassicalInvolution.Asc77
