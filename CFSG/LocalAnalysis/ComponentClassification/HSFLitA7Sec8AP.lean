module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8AData

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup
open scoped Pointwise

namespace Sec8

open Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

omit [Finite X] in
theorem conj_eq_on_closure {g h : X} {s : Set X} (hs : ∀ x ∈ s, g * x * g⁻¹ = h * x * h⁻¹)
    {x : X} (hx : x ∈ closure s) : g * x * g⁻¹ = h * x * h⁻¹ := by
  induction hx using closure_induction with
  | mem x hx => exact hs x hx
  | one => group
  | mul a b _ _ ha hb =>
    calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      _ = (h * a * h⁻¹) * (h * b * h⁻¹) := by rw [ha, hb]
      _ = h * (a * b) * h⁻¹ := by group
  | inv a _ ha =>
    calc g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      _ = (h * a * h⁻¹)⁻¹ := by rw [ha]
      _ = h * a⁻¹ * h⁻¹ := by group

omit [Finite X] in
theorem inv_mul_mem_centralizer {g h : X} {H : Subgroup X}
    (hc : ∀ x ∈ H, g * x * g⁻¹ = h * x * h⁻¹) : h⁻¹ * g ∈ centralizer (H : Set X) := by
  rw [mem_centralizer_iff]
  intro x hx
  have := hc x hx
  calc x * (h⁻¹ * g) = h⁻¹ * (h * x * h⁻¹) * g := by group
    _ = h⁻¹ * (g * x * g⁻¹) * g := by rw [this]
    _ = h⁻¹ * g * x := by group

theorem exists_conj_of_max {K P Q : Subgroup X} (hPK : P ≤ K) (hQK : Q ≤ K)
    (hP : IsPGroup 2 P) (hQ : IsPGroup 2 Q)
    (hmax : ∀ R : Subgroup X, IsPGroup 2 R → P ≤ R → R ≤ K → R = P)
    (hcard : Nat.card Q = Nat.card P) :
    ∃ k ∈ K, ∀ x, x ∈ Q ↔ k⁻¹ * x * k ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P' : Sylow 2 K :=
    { toSubgroup := P.subgroupOf K
      isPGroup' := hP.comap_subtype
      is_maximal' := fun {R} hR hle => by
        have hR' : IsPGroup 2 (R.map K.subtype) := hR.map _
        have hPR : P ≤ R.map K.subtype := fun x hx => ⟨⟨x, hPK hx⟩, hle hx, rfl⟩
        have h := hmax _ hR' hPR (map_subtype_le R)
        ext x
        constructor
        · intro hx
          have : (x : X) ∈ R.map K.subtype := ⟨x, hx, rfl⟩
          rw [h] at this
          exact this
        · intro hx
          exact hle hx }
  obtain ⟨Q', hQ'⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  have hcP : Nat.card (P' : Subgroup K) = Nat.card P :=
    Nat.card_congr (subgroupOfEquivOfLe hPK).toEquiv
  have hcQ : Nat.card (Q.subgroupOf K) = Nat.card Q :=
    Nat.card_congr (subgroupOfEquivOfLe hQK).toEquiv
  have hcQ' : Nat.card (Q' : Subgroup K) = Nat.card (P' : Subgroup K) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have hQeq : Q.subgroupOf K = Q' :=
    Subgroup.eq_of_le_of_card_ge hQ' (by rw [hcQ', hcP, hcQ, hcard])
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K P' Q'
  refine ⟨k, k.2, fun x => ?_⟩
  have hmem : ∀ y : K, y ∈ (Q' : Subgroup K) ↔ k⁻¹ * y * k ∈ (P' : Subgroup K) := by
    intro y
    rw [← hk, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rw [MulAut.smul_def, MulAut.conj_apply, show k⁻¹ * (k * b * k⁻¹) * k = b by group]
      exact hb
    · intro hy
      refine ⟨k⁻¹ * y * k, hy, ?_⟩
      rw [MulAut.smul_def, MulAut.conj_apply]
      group
  constructor
  · intro hx
    have h1 : (⟨x, hQK hx⟩ : K) ∈ (Q' : Subgroup K) := hQeq ▸ (show (⟨x, hQK hx⟩ : K) ∈
      Q.subgroupOf K from hx)
    exact (hmem _).mp h1
  · intro hx
    have hxK : x ∈ K := by
      have := mul_mem (mul_mem k.2 (hPK hx)) (inv_mem k.2)
      rwa [show (k : X) * ((k : X)⁻¹ * x * k) * (k : X)⁻¹ = x by group] at this
    have h1 : k⁻¹ * (⟨x, hxK⟩ : K) * k ∈ (P' : Subgroup K) := hx
    have h2 := (hmem ⟨x, hxK⟩).mpr h1
    rw [← hQeq] at h2
    exact h2

omit [Finite X] in
theorem isPGroup_zpowers_of_pow {g : X} {a : ℕ} (h : g ^ 2 ^ a = 1) : IsPGroup 2 (zpowers g) := by
  rintro ⟨x, hx⟩
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
  refine ⟨a, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

namespace AData

variable (A : AData S F T₁)

include A in
theorem T_le_T₁ : S.data.T ≤ T₁ := ISide.T_le_T₁ A.V₁

theorem ι_mem_T₁_gens : A.ι MA.u ∈ T₁ ∧ A.ι MA.w₁ ∈ T₁ ∧ A.ι MA.v ∈ T₁ ∧ A.ι MA.z ∈ T₁ ∧
    A.ι MA.y ∈ T₁ ∧ A.ι MA.t ∈ T₁ ∧ A.ι MA.k ∈ T₁ := by
  rw [A.ι_u, A.ι_w₁, A.ι_v, A.ι_z, A.ι_y, A.ι_t, A.ι_k]
  exact ⟨A.T_le_T₁ A.V₁.u_mem_T, A.V₁.w₁N_mem_T₁, A.V₁.vN_mem_T₁, A.T_le_T₁ z_mem_T,
    A.T_le_T₁ (yF_mem_T F), A.T_le_T₁ S.data.t_mem_T, A.T_le_T₁ (S.B_le_T (kF_mem_B F))⟩

theorem T₁_eq : T₁ = MA.T1.map A.ι := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := A.ι_mem_T₁_gens
  have hle : MA.T1.map A.ι ≤ T₁ := by
    rintro _ ⟨x, hx, rfl⟩
    refine map_mem_of_inSpan A.ι (MA.T1_span x hx) fun g hg => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h1, h2, h3, h4, h5, h6, h7]
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [A.h4.card, S.card_T, card_map_of_injective A.ι_injective, MA.card_T1]

theorem mem_T₁_iff {g : X} : g ∈ T₁ ↔ ∃ x : MA, MA.inT1 x = true ∧ A.ι x = g :=
  SetLike.ext_iff.mp A.T₁_eq g

theorem T₁_le_S₁ : T₁ ≤ A.D₁.S₁ := A.D₁.T₁_le

theorem w₂₂_conj_t : A.D₂.w₂ * S.t * A.D₂.w₂⁻¹ = S.t * A.D₁.u := by
  rw [A.hu₁]; exact A.V₂.w₂_conj_t

theorem w₂₂_conj_u : A.D₂.w₂ * A.D₁.u * A.D₂.w₂⁻¹ = A.D₁.u := by
  rw [A.hu₁]; exact A.V₂.w₂_conj_E0 (yi_mem_E0 (F.xF * F.yF) (S.z * F.kF))

theorem w₂₂_conj_z : A.D₂.w₂ * S.z * A.D₂.w₂⁻¹ = S.z := A.V₂.w₂_conj_E0 (z_mem_E0 _ _)

theorem w₂₂_conj_zk : A.D₂.w₂ * (S.z * F.kF) * A.D₂.w₂⁻¹ = S.z * F.kF :=
  A.V₂.w₂_conj_E0 (ki_mem_E0 _ _)

theorem w₂₂_conj_k : A.D₂.w₂ * F.kF * A.D₂.w₂⁻¹ = F.kF := by
  have h := A.w₂₂_conj_zk
  rw [show A.D₂.w₂ * (S.z * F.kF) * A.D₂.w₂⁻¹ = (A.D₂.w₂ * S.z * A.D₂.w₂⁻¹) *
    (A.D₂.w₂ * F.kF * A.D₂.w₂⁻¹) by group, A.w₂₂_conj_z] at h
  exact mul_left_cancel h

theorem w₂₂_conj_y : A.D₂.w₂ * F.yF * A.D₂.w₂⁻¹ = F.yF * A.V₂.w₁N := by
  have hy : F.yF = S.z * A.D₂.u := by rw [A.hu₂, ← mul_assoc, z_mul_z, one_mul]
  have h := A.V₂.w₂_conj_u
  change A.D₂.w₂ * A.D₂.u * A.D₂.w₂⁻¹ = A.D₂.u * A.V₂.w₁N at h
  calc A.D₂.w₂ * F.yF * A.D₂.w₂⁻¹ = A.D₂.w₂ * (S.z * A.D₂.u) * A.D₂.w₂⁻¹ :=
        congrArg (fun q => A.D₂.w₂ * q * A.D₂.w₂⁻¹) hy
    _ = (A.D₂.w₂ * S.z * A.D₂.w₂⁻¹) * (A.D₂.w₂ * A.D₂.u * A.D₂.w₂⁻¹) := by group
    _ = S.z * A.D₂.u * A.V₂.w₁N := by rw [A.w₂₂_conj_z, h, mul_assoc]
    _ = F.yF * A.V₂.w₁N := by rw [← hy]

theorem exists_c : ∃ c ∈ MA.ZList, A.V₂.w₁N = A.ι (MA.w₁ * c) := by
  obtain ⟨c, hc, hw⟩ := A.P₂.exists_w₁W_same (A.hq₂.trans A.hq₁.symm)
  have e1 : A.P₂.V.w₁c = A.V₂.w₁N := ISide.w₁c_of_elem _ A.hq₂
  have e2 : A.P₂.W.w₁c = A.V₁.w₁N := ISide.w₁c_of_elem _ A.hq₁
  change A.V₂.w₁c = A.V₁.w₁c * c at hw
  rw [show A.V₂.w₁c = A.V₂.w₁N from e1, show A.V₁.w₁c = A.V₁.w₁N from e2] at hw
  change c ∈ (zpowers S.z ⊔ zpowers F.kF : Subgroup X) at hc
  rcases A.V₁.eq_of_mem_zk hc with rfl | rfl | rfl | rfl
  · exact ⟨1, by simp [MA.ZList], by rw [hw, mul_one, mul_one, A.ι_w₁]⟩
  · exact ⟨MA.z, by simp [MA.ZList], by rw [hw, map_mul, A.ι_w₁, A.ι_z]⟩
  · exact ⟨MA.k, by simp [MA.ZList], by rw [hw, map_mul, A.ι_w₁, A.ι_k]; rfl⟩
  · exact ⟨MA.z * MA.k, by simp [MA.ZList], by
      rw [hw, map_mul, map_mul, A.ι_w₁, A.ι_z, A.ι_k]; rfl⟩

theorem w₂₂_conj_w₁ : A.D₂.w₂ * A.V₁.w₁N * A.D₂.w₂⁻¹ = A.V₁.w₁N := by
  obtain ⟨c, hc, hw⟩ := A.P₁.exists_w₁W_same (A.hq₁.trans A.hq₂.symm)
  have e1 : A.P₁.V.w₁c = A.V₁.w₁N := ISide.w₁c_of_elem _ A.hq₁
  have e2 : A.P₁.W.w₁c = A.V₂.w₁N := ISide.w₁c_of_elem _ A.hq₂
  change A.V₁.w₁c = A.V₂.w₁c * c at hw
  rw [show A.V₁.w₁c = A.V₁.w₁N from e1, show A.V₂.w₁c = A.V₂.w₁N from e2] at hw
  rw [hw, show A.D₂.w₂ * (A.V₂.w₁N * c) * A.D₂.w₂⁻¹ =
    (A.D₂.w₂ * A.V₂.w₁N * A.D₂.w₂⁻¹) * (A.D₂.w₂ * c * A.D₂.w₂⁻¹) by group]
  change A.V₂.D.w₂ * A.V₂.w₁N * A.V₂.D.w₂⁻¹ * (A.V₂.D.w₂ * c * A.V₂.D.w₂⁻¹) = A.V₂.w₁N * c
  rw [A.V₂.w₂_comm_w₁N, mul_inv_cancel_right, A.V₂.w₂_conj_E0 (A.V₂.zk_le_E0 hc)]

theorem w₂₂_conj_v : A.D₂.w₂ * A.V₁.vN * A.D₂.w₂⁻¹ = A.V₁.vN := by
  obtain ⟨c, hc, hv⟩ := A.P₁.exists_vW_zk
  have e1 : A.P₁.V.w₁c = A.V₁.w₁N := ISide.w₁c_of_elem _ A.hq₁
  change A.V₁.vN * A.V₁.w₁c = A.V₂.vN * c at hv
  rw [show A.V₁.w₁c = A.V₁.w₁N from e1] at hv
  have : A.V₁.vN = A.V₂.vN * c * A.V₁.w₁N⁻¹ := by rw [← hv]; group
  have hw := A.w₂₂_conj_w₁
  have hvW' : A.V₂.D.w₂ * A.V₂.vN = A.V₂.vN * A.V₂.D.w₂ := (A.P₂.option_of_elem A.hq₂).1
  have hvW : A.V₂.D.w₂ * A.V₂.vN * A.V₂.D.w₂⁻¹ = A.V₂.vN := by
    rw [hvW', mul_inv_cancel_right]
  rw [this, show A.D₂.w₂ * (A.V₂.vN * c * A.V₁.w₁N⁻¹) * A.D₂.w₂⁻¹ =
    (A.D₂.w₂ * A.V₂.vN * A.D₂.w₂⁻¹) * (A.D₂.w₂ * c * A.D₂.w₂⁻¹) *
      (A.D₂.w₂ * A.V₁.w₁N * A.D₂.w₂⁻¹)⁻¹ by group, hw]
  change A.V₂.D.w₂ * A.V₂.vN * A.V₂.D.w₂⁻¹ * (A.V₂.D.w₂ * c * A.V₂.D.w₂⁻¹) * A.V₁.w₁N⁻¹ =
    A.V₂.vN * c * A.V₁.w₁N⁻¹
  rw [hvW, A.V₂.w₂_conj_E0 (A.V₂.zk_le_E0 hc)]

@[expose] def ActsW (c : MA) (g : X) : Prop :=
  g * A.ι MA.t * g⁻¹ = A.ι (MA.t * MA.u) ∧ g * A.ι MA.u * g⁻¹ = A.ι MA.u ∧
    g * A.ι MA.y * g⁻¹ = A.ι (MA.y * MA.w₁ * c) ∧ g * A.ι MA.z * g⁻¹ = A.ι MA.z ∧
      g * A.ι MA.k * g⁻¹ = A.ι MA.k ∧ g * A.ι MA.w₁ * g⁻¹ = A.ι MA.w₁ ∧
        g * A.ι MA.v * g⁻¹ = A.ι MA.v

theorem actsW_w₂₂ : ∃ c ∈ MA.ZList, A.ActsW c A.D₂.w₂ := by
  obtain ⟨c, hc, hw⟩ := A.exists_c
  refine ⟨c, hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [A.ι_t, map_mul, A.ι_t, A.ι_u, A.w₂₂_conj_t]
  · rw [A.ι_u, A.w₂₂_conj_u]
  · rw [A.ι_y, A.w₂₂_conj_y, hw, mul_assoc MA.y, map_mul A.ι MA.y, A.ι_y]
  · rw [A.ι_z, A.w₂₂_conj_z]
  · rw [A.ι_k, A.w₂₂_conj_k]
  · rw [A.ι_w₁, A.w₂₂_conj_w₁]
  · rw [A.ι_v, A.w₂₂_conj_v]

@[expose] noncomputable def gensT : Set X :=
  {A.ι MA.u, A.ι MA.w₁, A.ι MA.v, A.ι MA.z, A.ι MA.y, A.ι MA.t, A.ι MA.k}

theorem T₁_le_closure : T₁ ≤ closure A.gensT := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := A.mem_T₁_iff.mp hg
  refine map_mem_of_inSpan A.ι (MA.T1_span x hx) fun g hg => subset_closure ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  simp only [gensT, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ι_mem_of_T1 {x : MA} (hx : MA.inT1 x = true) : A.ι x ∈ T₁ :=
  A.mem_T₁_iff.mpr ⟨x, hx, rfl⟩

theorem conj_mem_T₁_of_actsW {c : MA} (hc : c ∈ MA.ZList) {g : X} (hg : A.ActsW c g) {τ : X}
    (hτ : τ ∈ T₁) : g * τ * g⁻¹ ∈ T₁ := by
  have hle : closure A.gensT ≤ T₁.comap (MulAut.conj g).toMonoidHom := by
    rw [closure_le]
    intro x hx
    simp only [gensT, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have hcT : MA.inT1 c = true := by
      simp only [MA.ZList, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> decide +kernel
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hg
    simp only [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h2]; exact A.ι_mem_of_T1 (by decide +kernel)
    · rw [h6]; exact A.ι_mem_of_T1 (by decide +kernel)
    · rw [h7]; exact A.ι_mem_of_T1 (by decide +kernel)
    · rw [h4]; exact A.ι_mem_of_T1 (by decide +kernel)
    · rw [h3]
      exact A.ι_mem_of_T1 (MA.T1.mul_mem (show MA.inT1 (MA.y * MA.w₁) = true by decide +kernel)
        hcT)
    · rw [h1]; exact A.ι_mem_of_T1 (by decide +kernel)
    · rw [h5]; exact A.ι_mem_of_T1 (by decide +kernel)
  exact hle (A.T₁_le_closure hτ)

@[expose] noncomputable def gensW (c : MA) : Set X :=
  {A.ι (MA.t * MA.u), A.ι MA.u, A.ι (MA.y * MA.w₁ * c), A.ι MA.z, A.ι MA.k, A.ι MA.w₁, A.ι MA.v}

theorem T₁_le_closure_W {c : MA} (hc : c ∈ MA.ZList) : T₁ ≤ closure (A.gensW c) := by
  have hz : A.ι MA.z ∈ closure (A.gensW c) := subset_closure (by simp [gensW])
  have hk : A.ι MA.k ∈ closure (A.gensW c) := subset_closure (by simp [gensW])
  have hw : A.ι MA.w₁ ∈ closure (A.gensW c) := subset_closure (by simp [gensW])
  have hu : A.ι MA.u ∈ closure (A.gensW c) := subset_closure (by simp [gensW])
  have hcm : A.ι c ∈ closure (A.gensW c) := by
    simp only [MA.ZList, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · rw [map_one]; exact one_mem _
    · exact hz
    · exact hk
    · rw [map_mul]; exact mul_mem hz hk
  refine (A.T₁_le_closure).trans ((closure_le _).mpr fun x hx => ?_)
  simp only [gensT, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hu
  · exact hw
  · exact subset_closure (by simp [gensW])
  · exact hz
  · have : A.ι MA.y = A.ι (MA.y * MA.w₁ * c) * (A.ι c)⁻¹ * (A.ι MA.w₁)⁻¹ := by
      rw [map_mul, map_mul]; group
    rw [this]
    exact mul_mem (mul_mem (subset_closure (by simp [gensW])) (inv_mem hcm)) (inv_mem hw)
  · have : A.ι MA.t = A.ι (MA.t * MA.u) * (A.ι MA.u)⁻¹ := by rw [map_mul]; group
    rw [this]
    exact mul_mem (subset_closure (by simp [gensW])) (inv_mem hu)
  · exact hk

theorem conj_w₂_of_actsW {c : MA} (hc : c ∈ MA.ZList) {g : X} (hg : A.ActsW c g) {τ : X}
    (hτ : τ ∈ T₁) :
    (g * A.ι MA.w₂ * g⁻¹) * τ * (g * A.ι MA.w₂ * g⁻¹)⁻¹ =
      A.ι (MA.condWit c) * τ * (A.ι (MA.condWit c))⁻¹ := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := MA.condW_wit c hc
  refine conj_eq_on_closure (fun x hx => ?_) (A.T₁_le_closure_W hc hτ)
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hg
  have key : ∀ a : MA, (g * A.ι MA.w₂ * g⁻¹) * (g * A.ι a * g⁻¹) * (g * A.ι MA.w₂ * g⁻¹)⁻¹ =
      g * A.ι (MA.w₂ * a * MA.w₂⁻¹) * g⁻¹ := by
    intro a; rw [map_mul, map_mul, map_inv]; group
  have hconj : ∀ a b : MA, g * A.ι (a * b) * g⁻¹ = (g * A.ι a * g⁻¹) * (g * A.ι b * g⁻¹) := by
    intro a b; rw [map_mul]; group
  have hι : ∀ a b : MA, A.ι b * A.ι a * (A.ι b)⁻¹ = A.ι (b * a * b⁻¹) := by
    intro a b; rw [map_mul, map_mul, map_inv]
  simp only [gensW, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [← g1, key, show MA.w₂ * MA.t * MA.w₂⁻¹ = MA.y * MA.t by decide +kernel, hconj, g3, g1,
      hι, c1, ← map_mul]
  · rw [← g2, key, show MA.w₂ * MA.u * MA.w₂⁻¹ = MA.u * MA.w₁ by decide +kernel, hconj, g2, g6,
      hι, c2, ← map_mul]
  · rw [← g3, key, show MA.w₂ * MA.y * MA.w₂⁻¹ = MA.y by decide +kernel, g3, hι, c3]
  · rw [← g4, key, show MA.w₂ * MA.z * MA.w₂⁻¹ = MA.z by decide +kernel, g4, hι, c4]
  · rw [← g5, key, show MA.w₂ * MA.k * MA.w₂⁻¹ = MA.k by decide +kernel, g5, hι, c5]
  · rw [← g6, key, show MA.w₂ * MA.w₁ * MA.w₂⁻¹ = MA.w₁ by decide +kernel, g6, hι, c6]
  · rw [← g7, key, show MA.w₂ * MA.v * MA.w₂⁻¹ = MA.v by decide +kernel, g7, hι, c7]

theorem conj_mem_T₁_of_mem_S₁ {s τ : X} (hs : s ∈ A.D₁.S₁) (hτ : τ ∈ T₁) : s * τ * s⁻¹ ∈ T₁ := by
  obtain ⟨x, rfl⟩ := A.mem_range_of_mem_S₁ hs
  obtain ⟨y, hy, rfl⟩ := A.mem_T₁_iff.mp hτ
  rw [← map_inv, ← map_mul, ← map_mul]
  exact A.ι_mem_of_T1 (MA.T1_normal x y hy)

theorem S₁_le_normalizer_C : A.D₁.S₁ ≤ normalizer (centralizer (T₁ : Set X)) := by
  intro s hs
  rw [mem_normalizer_iff]
  have key : ∀ s ∈ A.D₁.S₁, ∀ c ∈ centralizer (T₁ : Set X),
      s * c * s⁻¹ ∈ centralizer (T₁ : Set X) := by
    intro s hs c hc
    rw [mem_centralizer_iff]
    intro τ hτ
    have h1 := mem_centralizer_iff.mp hc _ (A.conj_mem_T₁_of_mem_S₁ (inv_mem hs) hτ)
    calc τ * (s * c * s⁻¹) = s * ((s⁻¹ * τ * s⁻¹⁻¹) * c) * s⁻¹ := by group
      _ = s * (c * (s⁻¹ * τ * s⁻¹⁻¹)) * s⁻¹ := by rw [h1]
      _ = s * c * s⁻¹ * τ := by group
  intro c
  refine ⟨key s hs c, fun h => ?_⟩
  have := key s⁻¹ (inv_mem hs) _ h
  rwa [show s⁻¹ * (s * c * s⁻¹) * s⁻¹⁻¹ = c by group] at this

noncomputable def K₁ : Subgroup X := centralizer (T₁ : Set X) ⊔ A.D₁.S₁

theorem mem_K₁ {k : X} (hk : k ∈ A.K₁) : ∃ c ∈ centralizer (T₁ : Set X), ∃ s ∈ A.D₁.S₁,
    k = c * s := by
  have h : k ∈ ((centralizer (T₁ : Set X) : Set X) * (A.D₁.S₁ : Set X)) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ A.S₁_le_normalizer_C]; exact hk
  obtain ⟨c, hc, s, hs, rfl⟩ := h
  exact ⟨c, hc, s, hs, rfl⟩

include A in
theorem E₁_le_T₁ : S.E F.yF ≤ T₁ := (isRefl_yF F).E_le_T.trans A.T_le_T₁

include A in
theorem centralizer_T₁_le : centralizer (T₁ : Set X) ≤ normalizer (S.E F.yF : Set X) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro e
  have hcomm : ∀ e ∈ S.E F.yF, c * e * c⁻¹ = e := fun e he => by
    rw [(mem_centralizer_iff.mp hc e (A.E₁_le_T₁ he)).symm, mul_inv_cancel_right]
  constructor
  · intro he; rw [hcomm e he]; exact he
  · intro he
    have := hcomm _ he
    have h2 : e = c * e * c⁻¹ := by
      calc e = c⁻¹ * (c * e * c⁻¹) * c := by group
        _ = c⁻¹ * (c * (c * e * c⁻¹) * c⁻¹) * c := by rw [this]
        _ = c * e * c⁻¹ := by group
    rw [h2]; exact he

theorem K₁_le : A.K₁ ≤ normalizer (S.E F.yF : Set X) := sup_le A.centralizer_T₁_le A.D₁.S₁_le

theorem S₁_le_K₁ : A.D₁.S₁ ≤ A.K₁ := le_sup_right

theorem conj_S₁_le_K₁ : A.D₁.S₁.map (MulAut.conj A.D₂.w₂).toMonoidHom ≤ A.K₁ := by
  obtain ⟨c, hc, hW⟩ := A.actsW_w₂₂
  rw [← A.range_ι, MonoidHom.range_eq_map, map_map, ← MonoidHom.range_eq_map]
  refine MA.range_le _ fun g hg => ?_
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  simp only [MA.gens, List.mem_cons, List.not_mem_nil, or_false] at hg
  have hT : ∀ x : MA, MA.inT1 x = true → A.D₂.w₂ * A.ι x * A.D₂.w₂⁻¹ ∈ A.K₁ := fun x hx =>
    A.S₁_le_K₁ (A.T₁_le_S₁ (A.conj_mem_T₁_of_actsW hc hW (A.ι_mem_of_T1 hx)))
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    have hC := inv_mul_mem_centralizer (H := T₁) (fun τ hτ => A.conj_w₂_of_actsW hc hW hτ)
    have : A.D₂.w₂ * A.ι MA.w₂ * A.D₂.w₂⁻¹ = A.ι (MA.condWit c) *
        ((A.ι (MA.condWit c))⁻¹ * (A.D₂.w₂ * A.ι MA.w₂ * A.D₂.w₂⁻¹)) := by group
    rw [this]
    exact mul_mem (A.S₁_le_K₁ (A.ι_mem_S₁ _)) (mem_sup_left hC)
  all_goals exact hT _ (by decide +kernel)

theorem conj_S₁_card : Nat.card (A.D₁.S₁.map (MulAut.conj A.D₂.w₂).toMonoidHom) =
    Nat.card A.D₁.S₁ := card_map_of_injective (MulAut.conj A.D₂.w₂).injective

theorem S₁_max_K₁ : ∀ R : Subgroup X, IsPGroup 2 R → A.D₁.S₁ ≤ R → R ≤ A.K₁ → R = A.D₁.S₁ :=
  fun R hR hle hRK => A.D₁.S₁_maximal R hR hle (hRK.trans A.K₁_le)

theorem exists_p₀ : ∃ c ∈ MA.ZList, ∃ p₀ : X, p₀ ∈ normalizer (A.D₁.S₁ : Set X) ∧
    A.ActsW c p₀ ∧ ∀ τ ∈ T₁, p₀ * τ * p₀⁻¹ = A.D₂.w₂ * τ * A.D₂.w₂⁻¹ := by
  obtain ⟨c, hc, hW⟩ := A.actsW_w₂₂
  have hS' : IsPGroup 2 (A.D₁.S₁.map (MulAut.conj A.D₂.w₂).toMonoidHom) := A.D₁.isPGroup_S₁.map _
  obtain ⟨k, hk, hkS⟩ := exists_conj_of_max A.S₁_le_K₁ A.conj_S₁_le_K₁ A.D₁.isPGroup_S₁ hS'
    A.S₁_max_K₁ A.conj_S₁_card
  obtain ⟨c', hc', s, hs, rfl⟩ := A.mem_K₁ hk
  refine ⟨c, hc, c'⁻¹ * A.D₂.w₂, ?_, ?_, ?_⟩
  · refine mem_normalizer_of_map_eq (Subgroup.eq_of_le_of_card_ge ?_ ?_)
    · rintro _ ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have h1 : A.D₂.w₂ * x * A.D₂.w₂⁻¹ ∈ A.D₁.S₁.map (MulAut.conj A.D₂.w₂).toMonoidHom :=
        ⟨x, hx, rfl⟩
      have h2 := (hkS _).mp h1
      have h3 := mul_mem (mul_mem hs h2) (inv_mem hs)
      rwa [show s * ((c' * s)⁻¹ * (A.D₂.w₂ * x * A.D₂.w₂⁻¹) * (c' * s)) * s⁻¹ =
        c'⁻¹ * A.D₂.w₂ * x * (c'⁻¹ * A.D₂.w₂)⁻¹ by group] at h3
    · rw [card_map_of_injective (MulAut.conj _).injective]
  · have hτ : ∀ τ ∈ T₁, (c'⁻¹ * A.D₂.w₂) * τ * (c'⁻¹ * A.D₂.w₂)⁻¹ = A.D₂.w₂ * τ * A.D₂.w₂⁻¹ := by
      intro τ hτ
      have h1 := A.conj_mem_T₁_of_actsW hc hW hτ
      have h2 := mem_centralizer_iff.mp hc' _ h1
      calc (c'⁻¹ * A.D₂.w₂) * τ * (c'⁻¹ * A.D₂.w₂)⁻¹ =
          c'⁻¹ * ((A.D₂.w₂ * τ * A.D₂.w₂⁻¹) * c') := by group
        _ = c'⁻¹ * (c' * (A.D₂.w₂ * τ * A.D₂.w₂⁻¹)) := by rw [h2]
        _ = A.D₂.w₂ * τ * A.D₂.w₂⁻¹ := by group
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hW
    obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := A.ι_mem_T₁_gens
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hτ _ g6, h1]
    · rw [hτ _ g1, h2]
    · rw [hτ _ g5, h3]
    · rw [hτ _ g4, h4]
    · rw [hτ _ g7, h5]
    · rw [hτ _ g2, h6]
    · rw [hτ _ g3, h7]
  · intro τ hτ
    have h1 := A.conj_mem_T₁_of_actsW hc hW hτ
    have h2 := mem_centralizer_iff.mp hc' _ h1
    calc (c'⁻¹ * A.D₂.w₂) * τ * (c'⁻¹ * A.D₂.w₂)⁻¹ =
        c'⁻¹ * ((A.D₂.w₂ * τ * A.D₂.w₂⁻¹) * c') := by group
      _ = c'⁻¹ * (c' * (A.D₂.w₂ * τ * A.D₂.w₂⁻¹)) := by rw [h2]
      _ = A.D₂.w₂ * τ * A.D₂.w₂⁻¹ := by group

end AData

end Sec8

end CFSG.ComponentClassification.HSFLit
