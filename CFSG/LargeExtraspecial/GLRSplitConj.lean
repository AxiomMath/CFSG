module

public import CFSG.LargeExtraspecial.GLRSplitLevi
public import CFSG.LargeExtraspecial.GLRSplitGL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith

variable {G : Type*} [Group G] [Finite G] {S : Setting G} (C : Config S)

namespace Config

theorem isCompl_At_Bt : IsCompl C.At C.Bt :=
  IsCompl.of_eq C.inf_eq C.sup_eq

@[expose] noncomputable def projA : S.Qt →ₗ[ZMod 2] C.At :=
  Submodule.projectionOnto C.At C.Bt C.isCompl_At_Bt

@[expose] noncomputable def projB : S.Qt →ₗ[ZMod 2] C.Bt :=
  Submodule.projectionOnto C.Bt C.At C.isCompl_At_Bt.symm

theorem projA_add_projB (v : S.Qt) : (C.projA v : S.Qt) + C.projB v = v :=
  LinearMap.congr_fun (Submodule.subtype_comp_projectionOnto_add_eq_id C.isCompl_At_Bt) v

theorem projA_of_mem_At {v : S.Qt} (hv : v ∈ C.At) : C.projA v = ⟨v, hv⟩ :=
  Submodule.projectionOnto_apply_left C.isCompl_At_Bt ⟨v, hv⟩

theorem projA_of_mem_Bt {v : S.Qt} (hv : v ∈ C.Bt) : C.projA v = 0 :=
  Submodule.projectionOnto_apply_right C.isCompl_At_Bt ⟨v, hv⟩

theorem projB_of_mem_Bt {v : S.Qt} (hv : v ∈ C.Bt) : C.projB v = ⟨v, hv⟩ :=
  Submodule.projectionOnto_apply_left C.isCompl_At_Bt.symm ⟨v, hv⟩

theorem projB_of_mem_At {v : S.Qt} (hv : v ∈ C.At) : C.projB v = 0 :=
  Submodule.projectionOnto_apply_right C.isCompl_At_Bt.symm ⟨v, hv⟩

theorem projA_apply (x : C.Xbar) (v : S.Qt) :
    C.projA (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = C.resAt x (C.projA v) := by
  conv_lhs => rw [← C.projA_add_projB v]
  rw [map_add, map_add, C.projA_of_mem_At (C.apply_At _ x.2 _ (C.projA v).2),
    C.projA_of_mem_Bt (C.apply_Bt _ x.2 _ (C.projB v).2), add_zero]
  rfl

theorem projB_apply (x : C.Xbar) (v : S.Qt) :
    C.projB (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = C.resBt x (C.projB v) := by
  conv_lhs => rw [← C.projA_add_projB v]
  rw [map_add, map_add, C.projB_of_mem_At (C.apply_At _ x.2 _ (C.projA v).2),
    C.projB_of_mem_Bt (C.apply_Bt _ x.2 _ (C.projB v).2), zero_add]
  rfl

theorem exists_coboundary {Γ : Type*} [Group Γ] (φ : Γ →* C.Xbar)
    (hφ : Function.Bijective φ) (δ : Γ → S.Qt)
    (hδ : ∀ g h, δ (g * h) = δ g + (((φ g : C.Xbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (δ h)) :
    ∃ w : S.Qt, ∀ g, δ g = (((φ g : C.Xbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w + w := by
  have hδ1 : δ 1 = 0 := by
    have h := hδ 1 1
    rw [mul_one, map_one] at h
    exact (add_eq_left.mp h.symm)
  have h4A : 4 ≤ finrank (ZMod 2) C.At := by rw [C.finrank_At]; have := C.four_le_width; omega
  have h4B : 4 ≤ finrank (ZMod 2) C.Bt := by rw [C.finrank_Bt]; have := C.four_le_width; omega
  have hinjA : Function.Injective (C.resAt.comp φ) := C.resAt_injective.comp hφ.1
  have hinjB : Function.Injective (C.resBt.comp φ) := C.resBt_injective.comp hφ.1
  obtain ⟨wA, hwA⟩ := CFSG.GroupTheory.GLnTwoSplitting.exists_eq_of_isCocycle h4A
    (C.resAt.comp φ) (fun f d h => by
      obtain ⟨x, hx⟩ := C.resAt_bijective.2 (LinearEquiv.transvection h)
      obtain ⟨g, rfl⟩ := hφ.2 x
      exact ⟨g, hx⟩)
    (fun g => C.projA (δ g)) (fun g h => by
      rw [hδ, map_add, C.projA_apply]
      rfl)
    (fun g hg => by
      have : g = 1 := hinjA (by rw [hg, map_one])
      rw [this, hδ1, map_zero])
  obtain ⟨wB, hwB⟩ := CFSG.GroupTheory.GLnTwoSplitting.exists_eq_of_isCocycle h4B
    (C.resBt.comp φ) (fun f d h => by
      obtain ⟨x, hx⟩ := C.resBt_bijective.2 (LinearEquiv.transvection h)
      obtain ⟨g, rfl⟩ := hφ.2 x
      exact ⟨g, hx⟩)
    (fun g => C.projB (δ g)) (fun g h => by
      rw [hδ, map_add, C.projB_apply]
      rfl)
    (fun g hg => by
      have : g = 1 := hinjB (by rw [hg, map_one])
      rw [this, hδ1, map_zero])
  refine ⟨(wA : S.Qt) + wB, fun g => ?_⟩
  have hA := congrArg Subtype.val (hwA g)
  have hB := congrArg Subtype.val (hwB g)
  rw [← C.projA_add_projB (δ g), hA, hB]
  simp only [Submodule.coe_add, MonoidHom.comp_apply, resAt_apply, resBt_apply, map_add]
  abel

@[expose] noncomputable def xbarHom : C.X →* C.Xbar :=
  (S.ρ.comp (Subgroup.inclusion C.X_le_M)).codRestrict C.Xbar fun x =>
    C.ρ_mem_Xbar x.2 (C.X_le_M x.2)

theorem xbarHom_coe (x : C.X) : ((C.xbarHom x : C.Xbar) : S.O) = S.ρ ⟨x, C.X_le_M x.2⟩ := rfl

end Config

namespace Levi

variable {C} (Λ : Levi C)

theorem L_le_M : Λ.L ≤ S.M := Λ.L_le_X.trans C.X_le_M

@[expose] noncomputable def toXbar : Λ.L →* C.Xbar := C.xbarHom.comp (Subgroup.inclusion Λ.L_le_X)

theorem toXbar_coe (l : Λ.L) : ((Λ.toXbar l : C.Xbar) : S.O) = S.ρ ⟨l, Λ.L_le_M l.2⟩ := rfl

theorem ρ_eq_of_mul {q g : G} (hq : q ∈ S.QG) (hg : g ∈ S.M) :
    S.ρ ⟨q * g, S.M.mul_mem (S.QG_le_M hq) hg⟩ = S.ρ ⟨g, hg⟩ := by
  have : (⟨q * g, S.M.mul_mem (S.QG_le_M hq) hg⟩ : S.M) = ⟨q, S.QG_le_M hq⟩ * ⟨g, hg⟩ := rfl
  rw [this, map_mul, (S.ρ_eq_one_iff _).mpr hq, one_mul]

theorem toXbar_bijective : Function.Bijective Λ.toXbar := by
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · have h1 : S.ρ ⟨(a : G), Λ.L_le_M a.2⟩ = S.ρ ⟨(b : G), Λ.L_le_M b.2⟩ :=
      congrArg (fun y : C.Xbar => (y : S.O)) hab
    have h2 : S.ρ ⟨(a : G) * (b : G)⁻¹, S.M.mul_mem (Λ.L_le_M a.2) (S.M.inv_mem (Λ.L_le_M b.2))⟩
        = 1 := by
      have : (⟨(a : G) * (b : G)⁻¹, S.M.mul_mem (Λ.L_le_M a.2) (S.M.inv_mem (Λ.L_le_M b.2))⟩ :
          S.M) = ⟨a, Λ.L_le_M a.2⟩ * (⟨b, Λ.L_le_M b.2⟩)⁻¹ := rfl
      rw [this, map_mul, map_inv, h1, mul_inv_cancel]
    have h3 := Λ.eq_one_of_mem_QG _ (Λ.L.mul_mem a.2 (Λ.L.inv_mem b.2))
      ((S.ρ_eq_one_iff _).mp h2)
    exact Subtype.ext (mul_inv_eq_one.mp h3)
  · obtain ⟨g, hg⟩ := C.Xbar_le x.2
    have hgX : (g : G) ∈ C.X := C.mem_X_iff.mpr ⟨g.2, by rw [hg]; exact x.2⟩
    obtain ⟨q, hq, l, hl, hql⟩ := Λ.exists_mul_eq _ hgX
    refine ⟨⟨l, hl⟩, Subtype.ext ?_⟩
    rw [toXbar_coe, ← hg, ← ρ_eq_of_mul hq (Λ.L_le_M hl)]
    congr 2

theorem isPerfect : Group.IsPerfect Λ.L := by
  have := C.isPerfect_Xbar
  exact Group.IsPerfect.ofSurjective
    (f := (MulEquiv.ofBijective Λ.toXbar Λ.toXbar_bijective).symm.toMonoidHom)
    (MulEquiv.ofBijective Λ.toXbar Λ.toXbar_bijective).symm.surjective

theorem exists_conj_mem {L₁ : Subgroup G} (hL₁X : L₁ ≤ C.X)
    (hL₁Q : ∀ l ∈ L₁, l ∈ S.QG → l = 1) (hL₁ : ∀ x ∈ C.X, ∃ q ∈ S.QG, ∃ l ∈ L₁, q * l = x) :
    ∃ q ∈ S.QG, ∀ l ∈ L₁, q * l * q⁻¹ ∈ Λ.L := by
  classical
  have huniq : ∀ {q q' l l' : G}, q ∈ S.QG → q' ∈ S.QG → l ∈ L₁ → l' ∈ L₁ →
      q * l = q' * l' → q = q' ∧ l = l' := by
    intro q q' l l' hq hq' hl hl' h
    have h1 : l' * l⁻¹ = q'⁻¹ * q := by
      calc l' * l⁻¹ = q'⁻¹ * (q' * l') * l⁻¹ := by group
        _ = q'⁻¹ * q := by rw [← h]; group
    have h2 : l' * l⁻¹ = 1 := hL₁Q _ (L₁.mul_mem hl' (L₁.inv_mem hl))
      (h1 ▸ S.QG.mul_mem (S.QG.inv_mem hq') hq)
    have hll : l = l' := (mul_inv_eq_one.mp h2).symm
    subst hll
    exact ⟨mul_right_cancel h, rfl⟩
  choose c hc l₁ hl₁ hcl using fun l : Λ.L => hL₁ l (Λ.L_le_X l.2)
  have hl₁M : ∀ g, l₁ g ∈ S.M := fun g => C.X_le_M (hL₁X (hl₁ g))
  have hcoc : ∀ g h : Λ.L, c (g * h) = c g * (l₁ g * c h * (l₁ g)⁻¹) ∧
      l₁ (g * h) = l₁ g * l₁ h := by
    intro g h
    refine huniq (hc _) (S.QG.mul_mem (hc g) (S.conj_mem_QG (hl₁M g) (hc h))) (hl₁ _)
      (L₁.mul_mem (hl₁ g) (hl₁ h)) ?_
    rw [hcl, Subgroup.coe_mul, ← hcl g, ← hcl h]
    group
  have hρ : ∀ g : Λ.L, S.ρ ⟨l₁ g, hl₁M g⟩ = S.ρ ⟨g, Λ.L_le_M g.2⟩ := fun g => by
    have := ρ_eq_of_mul (hc g) (hl₁M g)
    rw [← this]
    congr 2
    exact hcl g
  let δ : Λ.L → S.Qt := fun l => S.cl (c l)
  have hδ : ∀ g h, δ (g * h) =
      δ g + (((Λ.toXbar g : C.Xbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (δ h) := by
    intro g h
    simp only [δ]
    rw [(hcoc g h).1, S.cl_mul (hc g) (S.conj_mem_QG (hl₁M g) (hc h)),
      Config.cl_conj (hl₁M g) (hc h), hρ, toXbar_coe]
  obtain ⟨w, hw⟩ := C.exists_coboundary Λ.toXbar Λ.toXbar_bijective δ hδ
  obtain ⟨q₀, hq₀, rfl⟩ := S.exists_cl w
  have hz : ∀ g : Λ.L, q₀ * l₁ g * q₀⁻¹ * (g : G)⁻¹ = 1 ∨ q₀ * l₁ g * q₀⁻¹ * (g : G)⁻¹ = S.z := by
    intro g
    have hgM := Λ.L_le_M g.2
    have e : q₀ * l₁ g * q₀⁻¹ * (g : G)⁻¹ = q₀ * (c g)⁻¹ * ((g : G) * q₀⁻¹ * (g : G)⁻¹) := by
      have : l₁ g = (c g)⁻¹ * g := eq_inv_mul_of_mul_eq (hcl g)
      rw [this]
      group
    have hmem : q₀ * (c g)⁻¹ * ((g : G) * q₀⁻¹ * (g : G)⁻¹) ∈ S.QG :=
      S.QG.mul_mem (S.QG.mul_mem hq₀ (S.QG.inv_mem (hc g)))
        (S.conj_mem_QG hgM (S.QG.inv_mem hq₀))
    rw [e]
    refine (S.cl_eq_zero_iff hmem).mp ?_
    rw [S.cl_mul (S.QG.mul_mem hq₀ (S.QG.inv_mem (hc g))) (S.conj_mem_QG hgM (S.QG.inv_mem hq₀)),
      S.cl_mul hq₀ (S.QG.inv_mem (hc g)), S.cl_inv (hc g), Config.cl_conj hgM (S.QG.inv_mem hq₀),
      S.cl_inv hq₀]
    have h1 : S.cl (c g) = δ g := rfl
    rw [h1, hw g, toXbar_coe]
    generalize ((S.ρ ⟨g, hgM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl q₀) = u
    generalize S.cl q₀ = v
    calc v + (u + v) + u = (v + v) + (u + u) := by abel
      _ = 0 := by rw [ZModModule.add_self, ZModModule.add_self, add_zero]
  have hzc : ∀ g : Λ.L, q₀ * l₁ g * q₀⁻¹ * (g : G)⁻¹ ∈ zpowers S.z := fun g => by
    rw [Setting.mem_zpowers_iff_of_mul_self S.z_mul_z]
    exact hz g
  have hcen : ∀ (g : Λ.L) (y : G), y ∈ zpowers S.z → (g : G) * y = y * g := by
    intro g y hy
    rcases (Setting.mem_zpowers_iff_of_mul_self S.z_mul_z).mp hy with rfl | rfl
    · rw [mul_one, one_mul]
    · exact S.z_comm (Λ.L_le_M g.2)
  have hl₁1 : l₁ 1 = 1 := by
    have := huniq (hc 1) S.QG.one_mem (hl₁ 1) L₁.one_mem (by rw [hcl, mul_one]; rfl)
    exact this.2
  let ψ : Λ.L →* zpowers S.z :=
    { toFun := fun g => ⟨q₀ * l₁ g * q₀⁻¹ * (g : G)⁻¹, hzc g⟩
      map_one' := Subtype.ext (by simp [hl₁1])
      map_mul' := fun g h => Subtype.ext (by
        change q₀ * l₁ (g * h) * q₀⁻¹ * ((g * h : Λ.L) : G)⁻¹ =
          (q₀ * l₁ g * q₀⁻¹ * (g : G)⁻¹) * (q₀ * l₁ h * q₀⁻¹ * (h : G)⁻¹)
        rw [(hcoc g h).2, Subgroup.coe_mul]
        have := hcen g _ (hzc h)
        calc q₀ * (l₁ g * l₁ h) * q₀⁻¹ * ((g : G) * h)⁻¹
            = (q₀ * l₁ g * q₀⁻¹ * (g : G)⁻¹) * ((g : G) *
                (q₀ * l₁ h * q₀⁻¹ * (h : G)⁻¹)) * (g : G)⁻¹ := by group
          _ = _ := by rw [this]; group) }
  have hψ : ∀ g, ψ g = 1 := by
    intro g
    have hle := Abelianization.commutator_subset_ker ψ
    have htop : commutator Λ.L = ⊤ := Λ.isPerfect.commutator_eq_top
    rw [htop] at hle
    exact hle (mem_top g)
  refine ⟨q₀, hq₀, fun l hl => ?_⟩
  obtain ⟨q, hq, g, hg, hqg⟩ := Λ.exists_mul_eq l (hL₁X hl)
  have h1 : l = l₁ ⟨g, hg⟩ := by
    have := huniq (S.QG.inv_mem hq) (hc ⟨g, hg⟩) hl (hl₁ ⟨g, hg⟩)
      (by rw [hcl]; exact (eq_inv_mul_of_mul_eq hqg).symm)
    exact this.2
  have h2 := congrArg Subtype.val (hψ ⟨g, hg⟩)
  change q₀ * l₁ ⟨g, hg⟩ * q₀⁻¹ * g⁻¹ = 1 at h2
  rw [h1, mul_inv_eq_one.mp h2]
  exact hg

end Levi

end CFSG.LargeExtraspecial.GLR
