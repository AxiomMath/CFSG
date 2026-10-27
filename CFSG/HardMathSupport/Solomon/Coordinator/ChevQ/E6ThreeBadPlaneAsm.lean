module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlaneDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2Conj
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLineSum
public import CFSG.LocalAnalysis.StandardType.GGExcToralSylow


public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.ExcToralSylow

set_option linter.unusedSectionVars false

section Plane


variable {K : Type} [Field K] [Finite K]

theorem finrank_rootModule_e6Plane : Module.finrank K (RootModule Tag.E6 K) = 78 := by
  rw [Module.finrank_finsupp_self, Fintype.card_sum, Fintype.card_fin, card_isRoot]
  rfl

theorem three_ne_zero_of_cube_root {ω : Kˣ} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) : (3 : K) ≠ 0 := by
  intro h
  have hω : (ω : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
  have h2 : ((ω : K) - 1) ^ 3 = 0 := by
    calc ((ω : K) - 1) ^ 3 = (ω : K) ^ 3 - 3 * (ω : K) ^ 2 + 3 * (ω : K) - 1 := by ring
      _ = 0 := by rw [hω, h]; ring
  exact h1 (Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h2)))

theorem exists_conj_plane (hZa : E6PlaneCosetStmt) (hZb : E6PlaneToralStmt)
    (hT : E6PlaneWeylStmt) {ω : Kˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {s u : ModGL .E6 K}
    (hsG : s ∈ adjointGroup .E6 K) (huG : u ∈ adjointGroup .E6 K) (hsu : s * u = u * s)
    (hs3 : s ^ 3 = 1) (hu3 : u ^ 3 = 1)
    (hs24 : Module.finrank K (LinearMap.ker ((s : Module.End K (RootModule .E6 K)) - 1)) = 24)
    (hu30 : ∀ k : ℕ, k < 3 → Module.finrank K (LinearMap.ker
      (((s ^ k * u : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1)) = 30) :
    ∃ γ ∈ adjointGroup .E6 K,
      γ⁻¹ * rootDiagUnit .E6 (e6LineChar ω) * γ ∈ Subgroup.zpowers s ⊔ Subgroup.zpowers u ∧
      γ⁻¹ * rootDiagUnit .E6 (e6D0Char ω) * γ ∈ Subgroup.zpowers s ⊔ Subgroup.zpowers u := by
  obtain ⟨g₁, hg₁, hg₁s⟩ := exists_conj_e6Line_of_finrank hω3 hω1 hsG hs3 hs24
  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : ModGL .E6 K, h₀ = rootDiagUnit .E6 (e6LineChar ω) := ⟨_, rfl⟩
  rw [← hh₀] at hg₁s
  obtain ⟨u₁, hu₁⟩ : ∃ u₁ : ModGL .E6 K, u₁ = g₁ * u * g₁⁻¹ := ⟨_, rfl⟩
  have hu₁G : u₁ ∈ adjointGroup .E6 K := by
    rw [hu₁]
    exact mul_mem (mul_mem hg₁ huG) (inv_mem hg₁)
  have hu₁3 : u₁ ^ 3 = 1 := by rw [hu₁, conj_pow, hu3, mul_one, mul_inv_cancel]
  have hh₀3 : h₀ ^ 3 = 1 := by rw [← hg₁s, conj_pow, hs3, mul_one, mul_inv_cancel]
  have hcomm : h₀ * u₁ = u₁ * h₀ := by
    rw [← hg₁s, hu₁]
    calc g₁ * s * g₁⁻¹ * (g₁ * u * g₁⁻¹) = g₁ * (s * u) * g₁⁻¹ := by group
      _ = g₁ * (u * s) * g₁⁻¹ := by rw [hsu]
      _ = g₁ * u * g₁⁻¹ * (g₁ * s * g₁⁻¹) := by group
  have hd24 : Module.finrank K
      (LinearMap.ker ((h₀ : Module.End K (RootModule .E6 K)) - 1)) = 24 := by
    rw [← hg₁s, finrank_ker_conj_sub_one]
    exact hs24
  have hpat : ∀ k : ℕ, k < 3 → Module.finrank K (LinearMap.ker
      (((h₀ ^ k * u₁ : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1)) = 30 := by
    intro k hk
    have e : h₀ ^ k * u₁ = g₁ * (s ^ k * u) * g₁⁻¹ := by
      rw [← hg₁s, hu₁, conj_pow]
      group
    rw [e, finrank_ker_conj_sub_one]
    exact hu30 k hk
  have hdim : Module.finrank K ↥(LinearMap.ker ((u₁ : Module.End K (RootModule .E6 K)) - 1) ⊓
      LinearMap.ker ((h₀ : Module.End K (RootModule .E6 K)) - 1)) = 12 := by
    have ha : (h₀ : Module.End K (RootModule .E6 K)) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hh₀3, Units.val_one]
    have hb : (u₁ : Module.End K (RootModule .E6 K)) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hu₁3, Units.val_one]
    have hab : Commute (h₀ : Module.End K (RootModule .E6 K))
        (u₁ : Module.End K (RootModule .E6 K)) := by
      have := congrArg (fun x : ModGL .E6 K => (x : Module.End K (RootModule .E6 K))) hcomm
      rw [Units.val_mul, Units.val_mul] at this
      exact this
    have hsum := finrank_lineSum (three_ne_zero_of_cube_root hω3 hω1) ha hb hab
    have e0 := hpat 0 (by norm_num)
    have e1 := hpat 1 (by norm_num)
    have e2 := hpat 2 (by norm_num)
    have c0 : ((h₀ ^ 0 * u₁ : ModGL .E6 K) : Module.End K (RootModule .E6 K)) =
        (u₁ : Module.End K (RootModule .E6 K)) := by rw [pow_zero, one_mul]
    have c1 : ((h₀ ^ 1 * u₁ : ModGL .E6 K) : Module.End K (RootModule .E6 K)) =
        (h₀ : Module.End K (RootModule .E6 K)) * (u₁ : Module.End K (RootModule .E6 K)) := by
      rw [pow_one, Units.val_mul]
    have c2 : ((h₀ ^ 2 * u₁ : ModGL .E6 K) : Module.End K (RootModule .E6 K)) =
        (h₀ : Module.End K (RootModule .E6 K)) ^ 2 * (u₁ : Module.End K (RootModule .E6 K)) := by
      rw [Units.val_mul, Units.val_pow_eq_pow_val]
    rw [c0] at e0
    rw [c1] at e1
    rw [c2] at e2
    rw [hd24, e0, e1, e2, finrank_rootModule_e6Plane] at hsum
    rw [inf_comm]
    omega
  have hu₁X : u₁ ∈ toralCentralizer .E6 K (e6LineChar ω) := by
    refine mem_toralCentralizer.2 ⟨hu₁G, ?_⟩
    rw [← hh₀]
    calc h₀ * u₁ * h₀⁻¹ = u₁ * h₀ * h₀⁻¹ := by rw [hcomm]
      _ = u₁ := by group
  have hu₁M : u₁ ∈ toralRootGroup .E6 K (e6LineChar ω) := by
    by_contra hM
    have := hZa K ω hω3 hω1 u₁ hu₁X hM
    rw [← hh₀] at this
    omega
  obtain ⟨y, hyM, b, hb3, hy⟩ := hZb K ω hω3 hω1 u₁ hu₁M hu₁3 (by rw [← hh₀]; exact hdim)
  have hyX := toralRootGroup_le (e6LineChar ω) hyM
  obtain ⟨hyG, hyc⟩ := mem_toralCentralizer.1 hyX
  rw [← hh₀] at hyc
  have hyh₀ : y * h₀ * y⁻¹ = h₀ := by
    have : h₀ * y = y * h₀ := by
      calc h₀ * y = h₀ * y * h₀⁻¹ * h₀ := by group
        _ = y * h₀ := by rw [hyc]
    rw [← this]
    group
  have hpatb : ∀ k : ℕ, k < 3 → Module.finrank K (LinearMap.ker
      ((((rootDiagUnit .E6 (e6LineChar ω) : ModGL .E6 K) ^ k * rootDiagUnit .E6 b :
        ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1)) = 30 := by
    intro k hk
    have e : (rootDiagUnit .E6 (e6LineChar ω) : ModGL .E6 K) ^ k * rootDiagUnit .E6 b =
        y * (h₀ ^ k * u₁) * y⁻¹ := by
      rw [← hy, ← hh₀]
      have : y * (h₀ ^ k * u₁) * y⁻¹ = (y * h₀ * y⁻¹) ^ k * (y * u₁ * y⁻¹) := by
        rw [conj_pow]
        group
      rw [this, hyh₀]
    rw [e, finrank_ker_conj_sub_one]
    exact hpat k hk
  obtain ⟨g₂, hg₂, hh₂, hd₂⟩ := hT K ω hω3 hω1 b hb3 hpatb
  rw [← hh₀] at hh₂ hd₂
  obtain ⟨c, hc⟩ : ∃ c : ModGL .E6 K, c = y * g₁ := ⟨_, rfl⟩
  have hcs : c * s * c⁻¹ = h₀ := by
    rw [hc]
    calc y * g₁ * s * (y * g₁)⁻¹ = y * (g₁ * s * g₁⁻¹) * y⁻¹ := by group
      _ = h₀ := by rw [hg₁s, hyh₀]
  have hcu : c * u * c⁻¹ = rootDiagUnit .E6 b := by
    rw [hc, ← hy, hu₁]
    group
  have hPb : ∀ x ∈ Subgroup.zpowers h₀ ⊔ Subgroup.zpowers (rootDiagUnit .E6 b : ModGL .E6 K),
      c⁻¹ * x * c ∈ Subgroup.zpowers s ⊔ Subgroup.zpowers u := by
    have hle : Subgroup.zpowers h₀ ⊔ Subgroup.zpowers (rootDiagUnit .E6 b : ModGL .E6 K) ≤
        (Subgroup.zpowers s ⊔ Subgroup.zpowers u).comap (MulAut.conj c⁻¹).toMonoidHom := by
      refine sup_le ((Subgroup.zpowers_le).2 ?_) ((Subgroup.zpowers_le).2 ?_)
      · rw [Subgroup.mem_comap]
        have : (MulAut.conj c⁻¹).toMonoidHom h₀ = s := by
          change c⁻¹ * h₀ * c⁻¹⁻¹ = s
          rw [← hcs]
          group
        rw [this]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers s)
      · rw [Subgroup.mem_comap]
        have : (MulAut.conj c⁻¹).toMonoidHom (rootDiagUnit .E6 b : ModGL .E6 K) = u := by
          change c⁻¹ * rootDiagUnit .E6 b * c⁻¹⁻¹ = u
          rw [← hcu]
          group
        rw [this]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
    intro x hx
    have := hle hx
    rw [Subgroup.mem_comap] at this
    change c⁻¹ * x * c⁻¹⁻¹ ∈ _ at this
    rwa [inv_inv] at this
  have hcG : c ∈ adjointGroup .E6 K := by rw [hc]; exact mul_mem hyG hg₁
  refine ⟨g₂ * c, mul_mem hg₂ hcG, ?_, ?_⟩
  · rw [← hh₀]
    have := hPb _ hh₂
    rwa [show c⁻¹ * (g₂⁻¹ * h₀ * g₂) * c = (g₂ * c)⁻¹ * h₀ * (g₂ * c) by group] at this
  · have := hPb _ hd₂
    rwa [show c⁻¹ * (g₂⁻¹ * rootDiagUnit .E6 (e6D0Char ω) * g₂) * c =
      (g₂ * c)⁻¹ * rootDiagUnit .E6 (e6D0Char ω) * (g₂ * c) by group] at this

theorem e6ThreeNotAll24NFA_of_stmts (hZa : E6PlaneCosetStmt) (hZb : E6PlaneToralStmt)
    (hT : E6PlaneWeylStmt) (hC : E6NotAll24Census) : E6ThreeNotAll24NFA := by
  intro K _ _ hK3 hK hK4 E hE hEc hED hEi hER hA24
  obtain ⟨s, u, hsE, huE, -, hs24, hu30⟩ := hC K hK3 hK hK4 E hE hEc hED hEi hER hA24
  obtain ⟨ω, hω3, hω1⟩ := e6Line_exists_cube_root_unit hK
  refine ⟨ω, hω3, hω1, ?_⟩
  have hcomm : MulAut.conj s * MulAut.conj u = MulAut.conj u * MulAut.conj s :=
    congrArg Subtype.val (hE.1.is_comm.comm (⟨_, hsE⟩ : E) ⟨_, huE⟩)
  have hsu : s * u = u * s :=
    mulAut_conj_injective_adjoint (by simpa only [map_mul] using hcomm)
  have hs3 : s ^ 3 = 1 :=
    mulAut_conj_injective_adjoint (by rw [map_pow, map_one]; exact hE.2 _ hsE)
  have hu3 : u ^ 3 = 1 :=
    mulAut_conj_injective_adjoint (by rw [map_pow, map_one]; exact hE.2 _ huE)
  have hsu' : (s : ModGL .E6 K) * u = u * s := by
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val hsu
  have hs3' : (s : ModGL .E6 K) ^ 3 = 1 := by
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val hs3
  have hu3' : (u : ModGL .E6 K) ^ 3 = 1 := by
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val hu3
  have hu30' : ∀ k : ℕ, k < 3 → Module.finrank K (LinearMap.ker
      ((((s : ModGL .E6 K) ^ k * u : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1)) = 30 :=
    fun k hk => by simpa only [Subgroup.coe_mul, Subgroup.coe_pow] using hu30 k hk
  obtain ⟨γ, hγ, hh, hd⟩ := exists_conj_plane hZa hZb hT hω3 hω1 s.2 u.2 hsu' hs3' hu3' hs24 hu30'
  have hPmem : ∀ x ∈ Subgroup.zpowers (s : ModGL .E6 K) ⊔ Subgroup.zpowers (u : ModGL .E6 K),
      ∃ p ∈ Subgroup.zpowers s ⊔ Subgroup.zpowers u, (p : ModGL .E6 K) = x := by
    intro x hx
    have e : Subgroup.zpowers (s : ModGL .E6 K) ⊔ Subgroup.zpowers (u : ModGL .E6 K) =
        (Subgroup.zpowers s ⊔ Subgroup.zpowers u).map (adjointGroup .E6 K).subtype := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      rfl
    rw [e] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨p, hp, rfl⟩
  have hPE : ∀ p ∈ Subgroup.zpowers s ⊔ Subgroup.zpowers u, (MulAut.conj p : MulAut _) ∈ E := by
    intro p hp
    have hle : Subgroup.zpowers s ⊔ Subgroup.zpowers u ≤
        E.comap (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut ↥(adjointGroup .E6 K)) :=
      sup_le ((Subgroup.zpowers_le).2 hsE) ((Subgroup.zpowers_le).2 huE)
    exact hle hp
  obtain ⟨p₁, hp₁, hp₁c⟩ := hPmem _ hh
  obtain ⟨p₂, hp₂, hp₂c⟩ := hPmem _ hd
  obtain ⟨γ', hγ'⟩ : ∃ γ' : ↥(adjointGroup .E6 K), (γ' : ModGL .E6 K) = γ := ⟨⟨γ, hγ⟩, rfl⟩
  refine ⟨MulAut.conj γ', innerAut_le_e6Inndiag K ((CFSG.Fischer.mem_innerAut).2 ⟨γ', rfl⟩),
    ?_, ?_⟩
  · have e : e6LineElt ω = γ' * p₁ * γ'⁻¹ := by
      apply Subtype.ext
      rw [coe_e6LineElt, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hp₁c, hγ']
      group
    refine ⟨MulAut.conj p₁, hPE p₁ hp₁, ?_⟩
    rw [congr_toMonoidHom_apply, e]
    simp only [map_mul, map_inv]
  · obtain ⟨d, hdc⟩ : ∃ d : ↥(adjointGroup .E6 K), d = γ' * p₂ * γ'⁻¹ := ⟨_, rfl⟩
    have hdv : (d : ModGL .E6 K) = rootDiagUnit .E6 (e6D0Char ω) := by
      rw [hdc, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hp₂c, hγ']
      group
    refine ⟨MulAut.conj p₂, hPE p₂ hp₂, ?_⟩
    rw [← conj_eq_rootDiagAutHom hdv, congr_toMonoidHom_apply, hdc]
    simp only [map_mul, map_inv]

end Plane

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
