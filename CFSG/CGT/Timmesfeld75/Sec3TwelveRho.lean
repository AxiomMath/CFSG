module

public import CFSG.CGT.Timmesfeld75.Sec3TwelveCard

public section

namespace CFSG.CGT.Timmesfeld75

open scoped MatrixGroups
open CFSG.Open

section Generic

variable {G : Type} [Group G]

theorem inf_centralizer_conj_mem {X M : Subgroup G} (hM : IsElemAbelian 2 M)
    (hXM : ∀ x ∈ X, ∀ m ∈ M, x * m * x⁻¹ ∈ M) {b : G}
    (hb : ∀ x ∈ X, x⁻¹ * (b * x * b⁻¹) ∈ M) {x n : G} (hx : x ∈ X)
    (hn : n ∈ M ⊓ Subgroup.centralizer ({b} : Set G)) :
    x * n * x⁻¹ ∈ M ⊓ Subgroup.centralizer ({b} : Set G) := by
  obtain ⟨hnM, hnb⟩ := hn
  have hnb' : n * b = b * n := Subgroup.mem_centralizer_singleton_iff.1 hnb
  have hν := hb x hx
  refine ⟨hXM x hx n hnM, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  obtain ⟨ν, hνdef⟩ : ∃ ν : G, ν = x⁻¹ * (b * x * b⁻¹) := ⟨_, rfl⟩
  rw [← hνdef] at hν
  have hcomm : ν * n = n * ν := elemAbelian_mul_comm hM hν hnM
  have hbx : b * x = x * ν * b := by rw [hνdef]; group
  calc x * n * x⁻¹ * b = x * n * (ν * b * x⁻¹) := by rw [hνdef]; group
    _ = x * (n * ν) * b * x⁻¹ := by group
    _ = x * (ν * n) * b * x⁻¹ := by rw [hcomm]
    _ = x * ν * (n * b) * x⁻¹ := by group
    _ = x * ν * (b * n) * x⁻¹ := by rw [hnb']
    _ = (x * ν * b) * n * x⁻¹ := by group
    _ = (b * x) * n * x⁻¹ := by rw [hbx]
    _ = b * (x * n * x⁻¹) := by group

theorem Cfg.inf_centralizer_eq_normIn {T U : Subgroup G} (c : Cfg T U) {y : G}
    (hy : y ∈ normIn U T) (hy1 : y ≠ 1) :
    T ⊓ Subgroup.centralizer ({y} : Set G) = normIn T U := by
  ext x
  constructor
  · rintro ⟨hxT, hxC⟩
    exact mem_normIn.2 ⟨hxT, c.wc₁.centralizer_le_normalizer (mem_normIn.1 hy).1 hy1 hxC⟩
  · intro hx
    exact ⟨normIn_le _ _ hx, Subgroup.mem_centralizer_singleton_iff.2 (c.comm_L_L₁ hx hy)⟩

end Generic

section Rho

variable {G : Type} [Group G] {T T₁ X M : Subgroup G} [hN : (M.subgroupOf X).Normal]
  {F : Type} [Field F] {a : G}

theorem Data312.conj_X (D : Data312 T T₁ X M F a) {b : G} (hbT : conjSubgroup b T = T)
    (hbT₁ : conjSubgroup b T₁ = T₁) : conjSubgroup b X = X := by
  rw [← D.hX, conjSubgroup_sup_eq_sup, hbT, hbT₁]

theorem Data312.conj_M (D : Data312 T T₁ X M F a) {b : G} (hbT : conjSubgroup b T = T)
    (hbT₁ : conjSubgroup b T₁ = T₁) : conjSubgroup b M = M := by
  have h := cfgM_conj b T T₁
  rw [hbT, hbT₁] at h
  rw [← D.hM]
  exact h.symm

@[expose] noncomputable def Data312.rho (D : Data312 T T₁ X M F a) {b : G}
    (hbT : conjSubgroup b T = T) (hbT₁ : conjSubgroup b T₁ = T₁) : SL(2, F) ≃* SL(2, F) :=
  D.e.symm.trans ((quotConjAut X M b (D.conj_X hbT hbT₁) (D.conj_M hbT hbT₁)).trans D.e)

theorem Data312.rho_apply_e (D : Data312 T T₁ X M F a) {b : G} (hbT : conjSubgroup b T = T)
    (hbT₁ : conjSubgroup b T₁ = T₁) (z : ↥X ⧸ M.subgroupOf X) :
    D.rho hbT hbT₁ (D.e z) =
      D.e (quotConjAut X M b (D.conj_X hbT hbT₁) (D.conj_M hbT hbT₁) z) := by
  simp [Data312.rho]

theorem Data312.map_phi_eq (D : Data312 T T₁ X M F a) {b : G} (hbT : conjSubgroup b T = T)
    (hbT₁ : conjSubgroup b T₁ = T₁) :
    ((T.subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X))).map
      (quotConjAut X M b (D.conj_X hbT hbT₁) (D.conj_M hbT hbT₁)).toMonoidHom =
      (T.subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X)) := by
  have h := map_subgroupOf_conjSubgroup_eq X M b (D.conj_X hbT hbT₁) (D.conj_M hbT hbT₁) T
  rw [hbT] at h
  exact h.symm

theorem Data312.map_phi_eq₁ (D : Data312 T T₁ X M F a) {b : G} (hbT : conjSubgroup b T = T)
    (hbT₁ : conjSubgroup b T₁ = T₁) :
    ((T₁.subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X))).map
      (quotConjAut X M b (D.conj_X hbT hbT₁) (D.conj_M hbT hbT₁)).toMonoidHom =
      (T₁.subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X)) := by
  have h := map_subgroupOf_conjSubgroup_eq X M b (D.conj_X hbT hbT₁) (D.conj_M hbT hbT₁) T₁
  rw [hbT₁] at h
  exact h.symm

theorem Data312.rho_mem_utri_iff (D : Data312 T T₁ X M F a) {b : G}
    (hbT : conjSubgroup b T = T) (hbT₁ : conjSubgroup b T₁ = T₁) (x : SL(2, F)) :
    D.rho hbT hbT₁ x ∈ utri F ↔ x ∈ utri F := by
  obtain ⟨z, rfl⟩ := D.e.surjective x
  rw [D.rho_apply_e hbT hbT₁]
  have h1 := mem_iff_of_map_mulEquiv_eq D.e D.eT
    (quotConjAut X M b (D.conj_X hbT hbT₁) (D.conj_M hbT hbT₁) z)
  have h2 := mem_iff_of_map_mulEquiv_eq
    (quotConjAut X M b (D.conj_X hbT hbT₁) (D.conj_M hbT hbT₁)) (D.map_phi_eq hbT hbT₁) z
  have h3 := mem_iff_of_map_mulEquiv_eq D.e D.eT z
  exact h1.trans (h2.trans h3.symm)

theorem Data312.rho_mem_ltri_iff (D : Data312 T T₁ X M F a) {b : G}
    (hbT : conjSubgroup b T = T) (hbT₁ : conjSubgroup b T₁ = T₁) (x : SL(2, F)) :
    D.rho hbT hbT₁ x ∈ ltri F ↔ x ∈ ltri F := by
  obtain ⟨z, rfl⟩ := D.e.surjective x
  rw [D.rho_apply_e hbT hbT₁]
  have h1 := mem_iff_of_map_mulEquiv_eq D.e D.eT₁
    (quotConjAut X M b (D.conj_X hbT hbT₁) (D.conj_M hbT hbT₁) z)
  have h2 := mem_iff_of_map_mulEquiv_eq
    (quotConjAut X M b (D.conj_X hbT hbT₁) (D.conj_M hbT hbT₁)) (D.map_phi_eq₁ hbT hbT₁) z
  have h3 := mem_iff_of_map_mulEquiv_eq D.e D.eT₁ z
  exact h1.trans (h2.trans h3.symm)

theorem Data312.rho_rho (D : Data312 T T₁ X M F a) {b : G} (hbT : conjSubgroup b T = T)
    (hbT₁ : conjSubgroup b T₁ = T₁) (hb : b * b = 1) (x : SL(2, F)) :
    D.rho hbT hbT₁ (D.rho hbT hbT₁ x) = x := by
  obtain ⟨z, rfl⟩ := D.e.surjective x
  rw [D.rho_apply_e, D.rho_apply_e,
    quotConjAut_quotConjAut_of_mul_self X M b _ _ hb]

theorem Data312.rho_comm (D : Data312 T T₁ X M F a) {b b' : G} (hbT : conjSubgroup b T = T)
    (hbT₁ : conjSubgroup b T₁ = T₁) (hbT' : conjSubgroup b' T = T)
    (hbT₁' : conjSubgroup b' T₁ = T₁) (hcomm : b * b' = b' * b) (x : SL(2, F)) :
    D.rho hbT hbT₁ (D.rho hbT' hbT₁' x) = D.rho hbT' hbT₁' (D.rho hbT hbT₁ x) := by
  obtain ⟨z, rfl⟩ := D.e.surjective x
  rw [D.rho_apply_e, D.rho_apply_e, D.rho_apply_e, D.rho_apply_e,
    quotConjAut_comm X M b b' _ _ _ _ hcomm]

theorem Data312.triv_of_rho_eq_self (D : Data312 T T₁ X M F a) {b : G}
    (hbT : conjSubgroup b T = T) (hbT₁ : conjSubgroup b T₁ = T₁)
    (h : ∀ x, D.rho hbT hbT₁ x = x) : ∀ y ∈ X, y⁻¹ * (b * y * b⁻¹) ∈ M := by
  intro y hy
  have h1 := h (D.e (QuotientGroup.mk (⟨y, hy⟩ : ↥X)))
  rw [D.rho_apply_e] at h1
  exact mem_of_quotConjAut_mk_eq X M b _ _ ⟨y, hy⟩ (D.e.injective h1)

theorem Data312.triv_mul_of_rho_eq (D : Data312 T T₁ X M F a) {b b' : G}
    (hbT : conjSubgroup b T = T) (hbT₁ : conjSubgroup b T₁ = T₁)
    (hbT' : conjSubgroup b' T = T) (hbT₁' : conjSubgroup b' T₁ = T₁) (hb : b * b = 1)
    (h : ∀ x, D.rho hbT hbT₁ x = D.rho hbT' hbT₁' x) :
    ∀ y ∈ X, y⁻¹ * (b * b' * y * (b * b')⁻¹) ∈ M := by
  intro y hy
  have hbb' : conjSubgroup (b * b') T = T := by
    rw [← conjSubgroup_conjSubgroup, hbT', hbT]
  have hbb'₁ : conjSubgroup (b * b') T₁ = T₁ := by
    rw [← conjSubgroup_conjSubgroup, hbT₁', hbT₁]
  have hφ : ∀ z, quotConjAut X M b (D.conj_X hbT hbT₁) (D.conj_M hbT hbT₁) z =
      quotConjAut X M b' (D.conj_X hbT' hbT₁') (D.conj_M hbT' hbT₁') z := fun z => by
    apply D.e.injective
    rw [← D.rho_apply_e hbT hbT₁, ← D.rho_apply_e hbT' hbT₁']
    exact h _
  have hz : quotConjAut X M b (D.conj_X hbT hbT₁) (D.conj_M hbT hbT₁)
      (quotConjAut X M b' (D.conj_X hbT' hbT₁') (D.conj_M hbT' hbT₁')
        (QuotientGroup.mk (⟨y, hy⟩ : ↥X))) = QuotientGroup.mk (⟨y, hy⟩ : ↥X) := by
    rw [← hφ (QuotientGroup.mk (⟨y, hy⟩ : ↥X))]
    exact quotConjAut_quotConjAut_of_mul_self X M b _ _ hb _
  rw [quotConjAut_mk, quotConjAut_mk] at hz
  have h3 := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hz.symm)
  have e : y⁻¹ * (b * b' * y * (b * b')⁻¹) = y⁻¹ * (b * (b' * y * b'⁻¹) * b⁻¹) := by group
  rw [e]
  exact h3

end Rho

end CFSG.CGT.Timmesfeld75
