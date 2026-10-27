module

public import CFSG.LargeExtraspecial.S3Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

namespace Setting

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

open Classical in
@[expose] noncomputable def fixQt (x : G) : Submodule (ZMod 2) S.Qt :=
  if hx : x ∈ S.M then fixSpace (S.ρ ⟨x, hx⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) else ⊥

open Classical in
@[expose] noncomputable def commQt (x : G) : Submodule (ZMod 2) S.Qt :=
  if hx : x ∈ S.M then commSpace (S.ρ ⟨x, hx⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) else ⊥

theorem fixQt_of_mem {x : G} (hx : x ∈ S.M) :
    S.fixQt x = fixSpace (S.ρ ⟨x, hx⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  simp only [fixQt, hx, ↓reduceDIte]

theorem commQt_of_mem {x : G} (hx : x ∈ S.M) :
    S.commQt x = commSpace (S.ρ ⟨x, hx⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  simp only [commQt, hx, ↓reduceDIte]

theorem ρ_mul_self {α : G} (hαM : α ∈ S.M) (hα2 : α ^ 2 = 1) :
    (S.ρ ⟨α, hαM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) * (S.ρ ⟨α, hαM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 := by
  have h : (⟨α, hαM⟩ : S.M) * ⟨α, hαM⟩ = 1 := Subtype.ext (by
    simp only [Subgroup.coe_mul, OneMemClass.coe_one]
    rw [← pow_two, hα2])
  rw [← Subgroup.coe_mul, ← map_mul, h, map_one]
  rfl

theorem ρ_mem_O (g : S.M) : (S.ρ g : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ S.O := (S.ρ g).2

theorem cl_mem_fixQt_iff {α x : G} (hαM : α ∈ S.M) (hx : x ∈ S.QG) :
    S.cl x ∈ S.fixQt α ↔ S.cl (α * x * α⁻¹) = S.cl x := by
  rw [S.fixQt_of_mem hαM, mem_fixSpace, S.ρ_cl ⟨α, hαM⟩ hx]

theorem clSub_centralizer_le_fixQt {α : G} (hαM : α ∈ S.M) :
    S.clSub (S.QG ⊓ centralizer ({α} : Set G)) ≤ S.fixQt α := by
  intro v hv
  obtain ⟨x, hx, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv
  rw [S.cl_mem_fixQt_iff hαM hxQ]
  have : α * x = x * α := (mem_centralizer_singleton_iff.mp hx.2).symm
  rw [this]
  group

theorem cl_commutator {α y : G} (hαM : α ∈ S.M) (hy : y ∈ S.QG) :
    S.cl (α * y * α⁻¹ * y⁻¹) =
      (S.ρ ⟨α, hαM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl y) - S.cl y := by
  rw [S.cl_mul (S.conj_mem_QG hαM hy) (S.QG.inv_mem hy), S.cl_inv hy, S.ρ_cl ⟨α, hαM⟩ hy,
    sub_eq_add_vec (ZMod 2)]

theorem mem_commQt_iff {α : G} (hαM : α ∈ S.M) {v : S.Qt} :
    v ∈ S.commQt α ↔ ∃ y ∈ S.QG, S.cl (α * y * α⁻¹ * y⁻¹) = v := by
  rw [S.commQt_of_mem hαM, mem_commSpace]
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨y, hy, rfl⟩ := S.exists_cl w
    exact ⟨y, hy, S.cl_commutator hαM hy⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨S.cl y, (S.cl_commutator hαM hy).symm⟩

theorem fixQt_eq_orthogonal {α : G} (hαM : α ∈ S.M) (hα2 : α ^ 2 = 1) :
    S.fixQt α = LinearMap.BilinForm.orthogonal S.q.polarBilin (S.commQt α) := by
  rw [S.fixQt_of_mem hαM, S.commQt_of_mem hαM]
  exact fixSpace_eq_orthogonal_commSpace S.q_nondegenerate (S.ρ_mem_O _) (S.ρ_mul_self hαM hα2)

theorem commQt_eq_orthogonal {α : G} (hαM : α ∈ S.M) (hα2 : α ^ 2 = 1) :
    S.commQt α = LinearMap.BilinForm.orthogonal S.q.polarBilin (S.fixQt α) := by
  rw [S.fixQt_eq_orthogonal hαM hα2,
    LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl]

theorem commQt_le_fixQt {α : G} (hαM : α ∈ S.M) (hα2 : α ^ 2 = 1) :
    S.commQt α ≤ S.fixQt α := by
  rw [S.fixQt_of_mem hαM, S.commQt_of_mem hαM]
  exact commSpace_le_fixSpace (S.ρ_mul_self hαM hα2)

theorem index_fixQt (α : G) (hαM : α ∈ S.M) :
    (S.fixQt α).toAddSubgroup.index = 2 ^ finrank (ZMod 2) (S.commQt α) := by
  have h1 := (S.fixQt α).toAddSubgroup.card_mul_index
  have h2 := finrank_commSpace_add_finrank_fixSpace (S.ρ ⟨α, hαM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt)
  rw [← S.fixQt_of_mem hαM, ← S.commQt_of_mem hαM] at h2
  change Nat.card (S.fixQt α) * _ = _ at h1
  rw [S.card_submodule, S.card_Qt, ← h2, pow_add, mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h1

omit [Finite G] in
theorem commutator_mem_QG {α y : G} (hαM : α ∈ S.M) (hy : y ∈ S.QG) :
    α * y * α⁻¹ * y⁻¹ ∈ S.QG :=
  S.QG.mul_mem (S.conj_mem_QG hαM hy) (S.QG.inv_mem hy)

omit [Finite G] in
theorem commutator_mem_QG' {α y : G} (hαM : α ∈ S.M) (hy : y ∈ S.QG) :
    y * α * y⁻¹ * α⁻¹ ∈ S.QG := by
  have := S.QG.mul_mem hy (S.conj_mem_QG hαM (S.QG.inv_mem hy))
  rwa [show y * (α * y⁻¹ * α⁻¹) = y * α * y⁻¹ * α⁻¹ by group] at this

theorem cl_commutator' {α y : G} (hαM : α ∈ S.M) (hy : y ∈ S.QG) :
    S.cl (y * α * y⁻¹ * α⁻¹) =
      (S.ρ ⟨α, hαM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl y) - S.cl y := by
  have h1 : S.cl (α * y⁻¹ * α⁻¹) = (S.ρ ⟨α, hαM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl y) := by
    rw [← S.cl_inv hy]
    exact (S.ρ_cl ⟨α, hαM⟩ (S.QG.inv_mem hy)).symm
  rw [show y * α * y⁻¹ * α⁻¹ = y * (α * y⁻¹ * α⁻¹) by group,
    S.cl_mul hy (S.conj_mem_QG hαM (S.QG.inv_mem hy)), h1, sub_eq_add_vec (ZMod 2), add_comm]

theorem commutator_zpowers_eq_clPre {α : G} (hαM : α ∈ S.M) (hαQ : α ∉ S.QG) (hα2 : α ^ 2 = 1) :
    ⁅zpowers α, S.QG⁆ = S.clPre (S.commQt α) := by
  have hαα : α * α = 1 := by rw [← pow_two, hα2]
  have hmem : ∀ y ∈ S.QG, α * y * α⁻¹ * y⁻¹ ∈ ⁅zpowers α, S.QG⁆ := fun y hy => by
    have := commutator_mem_commutator (mem_zpowers α) hy
    rwa [commutatorElement_def] at this
  apply le_antisymm
  · rw [commutator_le]
    intro a ha y hy
    rcases (mem_zpowers_iff_of_mul_self hαα).mp ha with rfl | rfl
    · rw [commutatorElement_one_left]
      exact one_mem _
    · rw [commutatorElement_def]
      exact ⟨S.commutator_mem_QG hαM hy, (S.mem_commQt_iff hαM).mpr ⟨y, hy, rfl⟩⟩
  · have hz : S.z ∈ ⁅zpowers α, S.QG⁆ := by
      obtain ⟨y, hy, hcy⟩ : ∃ y ∈ S.QG, S.cl (α * y * α⁻¹ * y⁻¹) ≠ 0 := by
        by_contra h
        push Not at h
        refine hαQ (S.mem_QG_of_cl_conj hαM fun x hx => ?_)
        have h1 := h x hx
        rw [S.cl_commutator hαM hx, sub_eq_zero, S.ρ_cl ⟨α, hαM⟩ hx] at h1
        exact h1
      have hcQ : α * y * α⁻¹ * y⁻¹ ∈ S.QG := S.commutator_mem_QG hαM hy
      obtain ⟨x, hx, hxc⟩ : ∃ x ∈ S.QG, x * (α * y * α⁻¹ * y⁻¹) ≠ (α * y * α⁻¹ * y⁻¹) * x := by
        by_contra h
        push Not at h
        rcases S.eq_one_or_z_of_commute hcQ (fun x hx => (h x hx).symm) with h' | h'
        · exact hcy (by rw [h', S.cl_one])
        · exact hcy (by rw [h', S.cl_z])
      have hxc' : x * (α * y * α⁻¹ * y⁻¹) * x⁻¹ = (α * y * α⁻¹ * y⁻¹) * S.z := by
        rcases S.mul_comm_or hx hcQ with h | h
        · exact absurd h hxc
        · calc x * (α * y * α⁻¹ * y⁻¹) * x⁻¹ = S.z * ((α * y * α⁻¹ * y⁻¹) * x) * x⁻¹ := by
                rw [h]
            _ = S.z * (α * y * α⁻¹ * y⁻¹) := by group
            _ = (α * y * α⁻¹ * y⁻¹) * S.z := (S.z_comm_QG hcQ).symm
      have key : S.z = (α * y * α⁻¹ * y⁻¹)⁻¹ * (α * x * α⁻¹ * x⁻¹)⁻¹ *
          (α * (x * y) * α⁻¹ * (x * y)⁻¹) := by
        have h2 : α * (x * y) * α⁻¹ * (x * y)⁻¹ =
            (α * x * α⁻¹ * x⁻¹) * (x * (α * y * α⁻¹ * y⁻¹) * x⁻¹) := by group
        rw [h2, hxc']
        group
      rw [key]
      exact mul_mem (mul_mem (inv_mem (hmem y hy)) (inv_mem (hmem x hx)))
        (hmem _ (S.QG.mul_mem hx hy))
    rintro x ⟨hxQ, hxv⟩
    obtain ⟨y, hy, hyx⟩ := (S.mem_commQt_iff hαM).mp hxv
    rcases (S.cl_eq_cl_iff (S.commutator_mem_QG hαM hy) hxQ).mp hyx with rfl | rfl
    · exact hmem y hy
    · exact mul_mem (hmem y hy) hz

theorem commute_of_cl_mem_fixQt {α x : G} (hαM : α ∈ S.M)
    (hfix : S.fixQt α = S.clSub (S.QG ⊓ centralizer ({α} : Set G))) (hx : x ∈ S.QG)
    (hxv : S.cl x ∈ S.fixQt α) : α * x = x * α := by
  rw [hfix] at hxv
  obtain ⟨d, hd, hdQ, hdx⟩ := S.mem_clSub_iff.mp hxv
  have hαd : α * d = d * α := (mem_centralizer_singleton_iff.mp hd.2).symm
  rcases (S.cl_eq_cl_iff hdQ hx).mp hdx with rfl | rfl
  · exact hαd
  · calc α * (d * S.z) = (α * d) * S.z := by group
      _ = d * (α * S.z) := by rw [hαd]; group
      _ = d * (S.z * α) := by rw [S.z_comm hαM]
      _ = d * S.z * α := by group

theorem q_eq_zero_of_mem_commQt {α : G} (hαM : α ∈ S.M) (hα2 : α ^ 2 = 1)
    (hfix : S.fixQt α = S.clSub (S.QG ⊓ centralizer ({α} : Set G))) :
    ∀ v ∈ S.commQt α, S.q v = 0 := by
  have hαα : α * α = 1 := by rw [← pow_two, hα2]
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right hαα
  intro v hv
  obtain ⟨y, hy, rfl⟩ := (S.mem_commQt_iff hαM).mp hv
  have hcQ := S.commutator_mem_QG hαM hy
  have hαc := S.commute_of_cl_mem_fixQt hαM hfix hcQ (S.commQt_le_fixQt hαM hα2 hv)
  have hinv : α * (α * y * α⁻¹ * y⁻¹) * α⁻¹ = (α * y * α⁻¹ * y⁻¹)⁻¹ := by
    have e1 : α * (α * y * α⁻¹ * y⁻¹) * α⁻¹ = (α * α) * y * α⁻¹ * y⁻¹ * α⁻¹ := by group
    have e2 : (α * y * α⁻¹ * y⁻¹)⁻¹ = y * α * y⁻¹ * α⁻¹ := by group
    rw [e1, e2, hαα, one_mul, hαi]
  rw [S.q_cl_eq_zero_iff hcQ, pow_two]
  have h1 : α * (α * y * α⁻¹ * y⁻¹) * α⁻¹ = α * y * α⁻¹ * y⁻¹ := by
    rw [hαc]
    group
  rw [h1] at hinv
  calc (α * y * α⁻¹ * y⁻¹) * (α * y * α⁻¹ * y⁻¹)
      = (α * y * α⁻¹ * y⁻¹) * (α * y * α⁻¹ * y⁻¹)⁻¹ := by rw [← hinv]
    _ = 1 := mul_inv_cancel _

theorem aschbacher_3_6 {α : G} (hαM : α ∈ S.M) (hαQ : α ∉ S.QG) (hα2 : α ^ 2 = 1)
    (hfix : S.fixQt α = S.clSub (S.QG ⊓ centralizer ({α} : Set G))) {l : ℕ}
    (hl : (S.fixQt α).toAddSubgroup.index = 2 ^ l) :
    CFSG.IsElementaryAbelian 2 (⁅zpowers α, S.QG⁆ : Subgroup G) ∧
      Nat.card (⁅zpowers α, S.QG⁆ : Subgroup G) = 2 ^ (l + 1) := by
  rw [S.commutator_zpowers_eq_clPre hαM hαQ hα2]
  have hl' : finrank (ZMod 2) (S.commQt α) = l := by
    rw [S.index_fixQt α hαM] at hl
    exact Nat.pow_right_injective le_rfl hl
  have hsing := S.q_eq_zero_of_mem_commQt hαM hα2 hfix
  have hO := S.ρ_mem_O ⟨α, hαM⟩
  have htt := S.ρ_mul_self hαM hα2
  refine ⟨{ is_comm := ⟨fun c d => ?_⟩, exponent_dvd_p := ?_ }, ?_⟩
  · apply Subtype.ext
    simp only [Subgroup.coe_mul]
    refine (S.polar_cl_eq_zero_iff c.2.1 d.2.1).mp ?_
    have hc : S.cl (c : G) ∈ commSpace (S.ρ ⟨α, hαM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [← S.commQt_of_mem hαM]
      exact c.2.2
    have hd : S.cl (d : G) ∈ commSpace (S.ρ ⟨α, hαM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [← S.commQt_of_mem hαM]
      exact d.2.2
    exact polar_commSpace_eq_zero hO htt hc hd
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun c => Subtype.ext ?_
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    exact (S.q_cl_eq_zero_iff c.2.1).mp (hsing _ c.2.2)
  · rw [S.card_clPre, S.card_submodule, hl', pow_succ, mul_comm]

theorem commutator_eq_centralizer_centralizer {α : G} (hαM : α ∈ S.M) (hαQ : α ∉ S.QG)
    (hα2 : α ^ 2 = 1) (hfix : S.fixQt α = S.clSub (S.QG ⊓ centralizer ({α} : Set G))) :
    ⁅zpowers α, S.QG⁆ =
        S.QG ⊓ centralizer ((S.QG ⊓ centralizer ({α} : Set G) : Subgroup G) : Set G) ∧
      ⁅zpowers α, S.QG⁆ = (S.QG ⊓ centralizer ({α} : Set G)) ⊓
        centralizer ((S.QG ⊓ centralizer ({α} : Set G) : Subgroup G) : Set G) := by
  have h1 : ⁅zpowers α, S.QG⁆ =
      S.QG ⊓ centralizer ((S.QG ⊓ centralizer ({α} : Set G) : Subgroup G) : Set G) := by
    rw [S.centralizer_inf_QG_eq_clPre inf_le_left, ← hfix, ← S.commQt_eq_orthogonal hαM hα2,
      S.commutator_zpowers_eq_clPre hαM hαQ hα2]
  refine ⟨h1, le_antisymm (fun x hx => ?_) (fun x hx => ?_)⟩
  · have hx' := hx
    rw [S.commutator_zpowers_eq_clPre hαM hαQ hα2] at hx'
    refine ⟨⟨hx'.1, mem_centralizer_singleton_iff.mpr ?_⟩, (h1 ▸ hx).2⟩
    exact (S.commute_of_cl_mem_fixQt hαM hfix hx'.1 (S.commQt_le_fixQt hαM hα2 hx'.2)).symm
  · rw [h1]
    exact ⟨hx.1.1, hx.2⟩

omit [Finite G] in
theorem map_conj_centralizer_inf_QG {g α : G} (hg : g ∈ S.M) :
    (S.QG ⊓ centralizer ({α} : Set G)).map (MulAut.conj g).toMonoidHom =
      S.QG ⊓ centralizer ({g * α * g⁻¹} : Set G) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyQ, hyc⟩, rfl⟩
    refine ⟨S.conj_mem_QG hg hyQ, mem_centralizer_singleton_iff.mpr ?_⟩
    have := mem_centralizer_singleton_iff.mp hyc
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * y * g⁻¹ * (g * α * g⁻¹) = g * (y * α) * g⁻¹ := by group
      _ = g * (α * y) * g⁻¹ := by rw [this]
      _ = g * α * g⁻¹ * (g * y * g⁻¹) := by group
  · rintro ⟨hxQ, hxc⟩
    refine ⟨g⁻¹ * x * g, ⟨?_, ?_⟩, by simp [mul_assoc]⟩
    · have := S.conj_mem_QG (S.M.inv_mem hg) hxQ
      simpa using this
    · show g⁻¹ * x * g ∈ centralizer ({α} : Set G)
      rw [mem_centralizer_singleton_iff]
      have : x * (g * α * g⁻¹) = g * α * g⁻¹ * x := mem_centralizer_singleton_iff.mp hxc
      calc g⁻¹ * x * g * α = g⁻¹ * (x * (g * α * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * α * g⁻¹) * x) * g := by rw [this]
        _ = α * (g⁻¹ * x * g) := by group

theorem mem_commQt_iff' {α : G} (hαM : α ∈ S.M) {v : S.Qt} :
    v ∈ S.commQt α ↔ ∃ y ∈ S.QG, S.cl (y * α * y⁻¹ * α⁻¹) = v := by
  rw [S.mem_commQt_iff hαM]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by rw [S.cl_commutator hαM hy, S.cl_commutator' hαM hy]⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by rw [S.cl_commutator hαM hy, S.cl_commutator' hαM hy]⟩

theorem lemma_3_2_1 {α : G} (hαM : α ∈ S.M)
    (h : S.fixQt α ≠ S.clSub (S.QG ⊓ centralizer ({α} : Set G))) :
    ∃ y ∈ S.QG, y * α * y⁻¹ = α * S.z := by
  obtain ⟨v, hv, hvn⟩ : ∃ v ∈ S.fixQt α, v ∉ S.clSub (S.QG ⊓ centralizer ({α} : Set G)) := by
    by_contra h'
    push Not at h'
    exact h (le_antisymm h' (S.clSub_centralizer_le_fixQt hαM))
  obtain ⟨x, hx, rfl⟩ := S.exists_cl v
  rw [S.cl_mem_fixQt_iff hαM hx] at hv
  rcases (S.cl_eq_cl_iff hx (S.conj_mem_QG hαM hx)).mp hv.symm with h1 | h1
  · refine absurd (S.cl_mem_clSub (X := S.QG ⊓ centralizer ({α} : Set G))
      ⟨hx, mem_centralizer_singleton_iff.mpr ?_⟩ hx) hvn
    calc x * α = α * x * α⁻¹ * α := by rw [h1]
      _ = α * x := by group
  · refine ⟨x⁻¹, S.QG.inv_mem hx, ?_⟩
    calc x⁻¹ * α * x⁻¹⁻¹ = x⁻¹ * (α * x * α⁻¹) * α := by group
      _ = x⁻¹ * (x * S.z) * α := by rw [h1]
      _ = S.z * α := by group
      _ = α * S.z := (S.z_comm hαM).symm

theorem lemma_3_2_2 {α : G} (hαM : α ∈ S.M) (hα2 : α ^ 2 = 1)
    (hfix : S.fixQt α = S.clSub (S.QG ⊓ centralizer ({α} : Set G))) {g h : G} (hg : g ∈ S.M)
    (hh : h ∈ S.QG) (hgh : g * α * g⁻¹ = h * α) :
    (∃ y ∈ S.QG, y * α * y⁻¹ = h * α) ∨ (∃ y ∈ S.QG, y * (α * S.z) * y⁻¹ = h * α) := by
  set C := S.QG ⊓ centralizer ({α} : Set G) with hC
  set Cβ := S.QG ⊓ centralizer ({h * α} : Set G) with hCβ
  have hβM : h * α ∈ S.M := S.M.mul_mem (S.QG_le_M hh) hαM
  have hfixβ : S.fixQt (h * α) = S.fixQt α := by
    rw [S.fixQt_of_mem hβM, S.fixQt_of_mem hαM]
    have : S.ρ ⟨h * α, hβM⟩ = S.ρ ⟨α, hαM⟩ := by
      rw [show (⟨h * α, hβM⟩ : S.M) = ⟨h, S.QG_le_M hh⟩ * ⟨α, hαM⟩ from rfl, map_mul,
        (S.ρ_eq_one_iff _).mpr hh, one_mul]
    rw [this]
  have hzC : S.z ∈ C := ⟨S.z_mem_QG, mem_centralizer_singleton_iff.mpr (S.z_comm hαM).symm⟩
  have hle : Cβ ≤ C := by
    calc Cβ ≤ S.clPre (S.clSub Cβ) := S.le_clPre_clSub inf_le_left
      _ ≤ S.clPre (S.clSub C) := S.clPre_mono (by
          rw [← hfix, ← hfixβ]
          exact S.clSub_centralizer_le_fixQt hβM)
      _ = C := S.clPre_clSub inf_le_left hzC
  have hcard : Nat.card C = Nat.card Cβ := by
    rw [hCβ, ← hgh, ← S.map_conj_centralizer_inf_QG hg,
      card_map_of_injective (MulAut.conj g).injective]
  have heq : Cβ = C := eq_of_le_of_card_ge hle hcard.le
  have hhC : h ∈ S.QG ⊓ centralizer (C : Set G) := by
    refine ⟨hh, mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hx1 : x * α = α * x := mem_centralizer_singleton_iff.mp hx.2
    have hx' : x ∈ Cβ := heq ▸ hx
    have hx2 : x * (h * α) = (h * α) * x := mem_centralizer_singleton_iff.mp hx'.2
    calc x * h = x * (h * α) * α⁻¹ := by group
      _ = h * α * x * α⁻¹ := by rw [hx2]
      _ = h * (α * x) * α⁻¹ := by group
      _ = h * (x * α) * α⁻¹ := by rw [hx1]
      _ = h * x := by group
  rw [S.centralizer_inf_QG_eq_clPre inf_le_left, ← hfix, ← S.commQt_eq_orthogonal hαM hα2] at hhC
  obtain ⟨y, hy, hyh⟩ := (S.mem_commQt_iff' hαM).mp hhC.2
  rcases (S.cl_eq_cl_iff (S.commutator_mem_QG' hαM hy) hh).mp hyh with rfl | rfl
  · exact Or.inl ⟨y, hy, by group⟩
  · refine Or.inr ⟨y, hy, ?_⟩
    calc y * (α * S.z) * y⁻¹ = y * α * y⁻¹ * (y * S.z * y⁻¹) := by group
      _ = y * α * y⁻¹ * S.z := by rw [S.z_comm_QG hy]; group
      _ = y * α * y⁻¹ * α⁻¹ * (α * S.z) := by group
      _ = y * α * y⁻¹ * α⁻¹ * (S.z * α) := by rw [S.z_comm hαM]
      _ = y * α * y⁻¹ * α⁻¹ * S.z * α := by group

theorem lemma_3_2_index {α : G} (hαM : α ∈ S.M) (hα2 : α ^ 2 = 1)
    (hfix : S.fixQt α = S.clSub (S.QG ⊓ centralizer ({α} : Set G))) :
    (((S.M ⊓ centralizer ({α} : Set G)).subgroupOf S.M).map S.ρ).relIndex
      (S.Mbar ⊓ centralizer ({S.ρ ⟨α, hαM⟩} : Set S.O)) ≤ 2 := by
  set H := ((S.M ⊓ centralizer ({α} : Set G)).subgroupOf S.M).map S.ρ with hH
  set N := S.Mbar ⊓ centralizer ({S.ρ ⟨α, hαM⟩} : Set S.O) with hN
  have hρQ : ∀ y (hy : y ∈ S.QG), S.ρ ⟨y, S.QG_le_M hy⟩ = 1 := fun y hy =>
    (S.ρ_eq_one_iff _).mpr hy
  have key : ∀ x ∈ N, x ∉ H →
      ∃ a : S.M, S.ρ a = x ∧ (a : G) * α * (a : G)⁻¹ = α * S.z := by
    rintro x ⟨⟨⟨g, hgM⟩, rfl⟩, hxc⟩ hxH
    have hcomm : S.ρ ⟨g, hgM⟩ * S.ρ ⟨α, hαM⟩ = S.ρ ⟨α, hαM⟩ * S.ρ ⟨g, hgM⟩ :=
      mem_centralizer_singleton_iff.mp hxc
    set h := g * α * g⁻¹ * α⁻¹ with hhdef
    have hhM : h ∈ S.M :=
      S.M.mul_mem (S.M.mul_mem (S.M.mul_mem hgM hαM) (S.M.inv_mem hgM)) (S.M.inv_mem hαM)
    have hh : h ∈ S.QG := by
      refine (S.ρ_eq_one_iff ⟨h, hhM⟩).mp ?_
      rw [show (⟨h, hhM⟩ : S.M) = ⟨g, hgM⟩ * ⟨α, hαM⟩ * (⟨g, hgM⟩ : S.M)⁻¹ *
          (⟨α, hαM⟩ : S.M)⁻¹ from rfl, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have hgh : g * α * g⁻¹ = h * α := by rw [hhdef]; group
    have hyg : ∀ y ∈ S.QG, y⁻¹ * g ∈ S.M := fun y hy =>
      S.M.mul_mem (S.M.inv_mem (S.QG_le_M hy)) hgM
    have hρyg : ∀ y (hy : y ∈ S.QG), S.ρ ⟨y⁻¹ * g, hyg y hy⟩ = S.ρ ⟨g, hgM⟩ := fun y hy => by
      rw [show (⟨y⁻¹ * g, hyg y hy⟩ : S.M) = (⟨y, S.QG_le_M hy⟩ : S.M)⁻¹ * ⟨g, hgM⟩ from rfl,
        map_mul, map_inv, hρQ y hy, inv_one, one_mul]
    rcases S.lemma_3_2_2 hαM hα2 hfix hgM hh hgh with ⟨y, hy, hyα⟩ | ⟨y, hy, hyα⟩
    · refine absurd ⟨⟨y⁻¹ * g, hyg y hy⟩,
        ⟨hyg y hy, mem_centralizer_singleton_iff.mpr ?_⟩, hρyg y hy⟩ hxH
      calc y⁻¹ * g * α = y⁻¹ * (g * α * g⁻¹) * g := by group
        _ = y⁻¹ * (y * α * y⁻¹) * g := by rw [hgh, hyα]
        _ = α * (y⁻¹ * g) := by group
    · refine ⟨⟨y⁻¹ * g, hyg y hy⟩, hρyg y hy, ?_⟩
      calc y⁻¹ * g * α * (y⁻¹ * g)⁻¹ = y⁻¹ * (g * α * g⁻¹) * y := by group
        _ = y⁻¹ * (y * (α * S.z) * y⁻¹) * y := by rw [hgh, hyα]
        _ = α * S.z := by group
  have hprod : ∀ x ∈ N, ∀ x' ∈ N, x ∉ H → x' ∉ H → x * x' ∈ H := by
    intro x hx x' hx' hxH hx'H
    obtain ⟨a, rfl, ha⟩ := key x hx hxH
    obtain ⟨a', rfl, ha'⟩ := key x' hx' hx'H
    refine ⟨a * a', ⟨(a * a').2, mem_centralizer_singleton_iff.mpr ?_⟩, map_mul _ _ _⟩
    have hza : (a : G) * S.z * (a : G)⁻¹ = S.z := by rw [S.z_comm a.2]; group
    calc ((a * a' : S.M) : G) * α = (a : G) * ((a' : G) * α * (a' : G)⁻¹) * (a : G)⁻¹ *
          ((a * a' : S.M) : G) := by simp only [Subgroup.coe_mul]; group
      _ = (a : G) * α * (a : G)⁻¹ * ((a : G) * S.z * (a : G)⁻¹) * ((a * a' : S.M) : G) := by
          rw [ha']; group
      _ = α * ((a * a' : S.M) : G) := by rw [ha, hza, mul_assoc α, S.z_mul_z, mul_one]
  have hHN : H ≤ N := by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨⟨g, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
    have hgα : g * ⟨α, hαM⟩ = ⟨α, hαM⟩ * g :=
      Subtype.ext (mem_centralizer_singleton_iff.mp (mem_subgroupOf.mp hg).2)
    rw [← map_mul, hgα, map_mul]
  by_cases hNH : N ≤ H
  · rw [relIndex_eq_one.mpr hNH]
    norm_num
  · obtain ⟨x₀, hx₀N, hx₀H⟩ := Set.not_subset.mp hNH
    rw [relIndex_eq_two_iff.mpr ⟨x₀, hx₀N, fun b hb => ?_⟩]
    by_cases hbH : b ∈ H
    · refine Or.inr ⟨hbH, fun h => hx₀H ?_⟩
      have := H.mul_mem (H.inv_mem hbH) h
      rwa [inv_mul_cancel_left] at this
    · exact Or.inl ⟨hprod b hb x₀ hx₀N hbH hx₀H, hbH⟩

end Setting

end CFSG.LargeExtraspecial
