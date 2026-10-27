module

public import CFSG.CGT.Stroth77.WeakType
public import CFSG.CGT.Stroth77.Extension22FourComm

public section

namespace CFSG.CGT.Stroth77

section Conj

variable {S : Type*} [Group S] {C : Subgroup S}

theorem conjAutOfMemNormalizer_mul {g h : S} (hg : g ∈ Subgroup.normalizer C)
    (hh : h ∈ Subgroup.normalizer C) :
    conjAutOfMemNormalizer (g * h) (mul_mem hg hh) =
      conjAutOfMemNormalizer g hg * conjAutOfMemNormalizer h hh := by
  ext x
  show (g * h) * (x : S) * (g * h)⁻¹ = g * (h * (x : S) * h⁻¹) * g⁻¹
  group

theorem conjAutOfMemNormalizer_eq_one {g : S} (hg : g ∈ Subgroup.normalizer C)
    (h : g ∈ Subgroup.centralizer (C : Set S)) : conjAutOfMemNormalizer g hg = 1 := by
  ext x
  have := (Subgroup.mem_centralizer_iff.mp h) x x.2
  show g * (x : S) * g⁻¹ = x
  rw [← this]
  group

theorem conjAutOfMemNormalizer_symm_apply {g : S} (hg : g ∈ Subgroup.normalizer C) (x : C) :
    (((conjAutOfMemNormalizer g hg).symm x : C) : S) = g⁻¹ * x * g := rfl

end Conj

section Aux

variable {S : Type*} [Group S] {B C : Subgroup S} {τ : StrothTypeIndex}

namespace StrothWeakTypeData

variable (D : StrothWeakTypeData B τ) (hL : D.L ≤ Subgroup.normalizer C)

@[expose] noncomputable def auxL : Subgroup (MulAut C) :=
  Subgroup.closure {conjAutOfMemNormalizer D.uv (hL D.uv_mem_L),
    conjAutOfMemNormalizer D.t (hL D.t_mem_L), conjAutOfMemNormalizer D.u (hL D.u_mem_L),
    conjAutOfMemNormalizer D.ρ (hL D.ρ_mem_L)}

abbrev AuxGroup : Type _ := C ⋊[(D.auxL hL).subtype] D.auxL hL

@[expose] noncomputable def auxSub (X : Subgroup S) : Subgroup (D.AuxGroup hL) :=
  (X.subgroupOf C).map SemidirectProduct.inl

@[expose] noncomputable def auxGen (g : S) (hg : g ∈ Subgroup.normalizer C)
    (h : conjAutOfMemNormalizer g hg ∈ D.auxL hL) : D.AuxGroup hL :=
  SemidirectProduct.inr ⟨_, h⟩

theorem uv_mem_auxL : conjAutOfMemNormalizer D.uv (hL D.uv_mem_L) ∈ D.auxL hL :=
  Subgroup.subset_closure (by simp)
theorem t_mem_auxL : conjAutOfMemNormalizer D.t (hL D.t_mem_L) ∈ D.auxL hL :=
  Subgroup.subset_closure (by simp)
theorem u_mem_auxL : conjAutOfMemNormalizer D.u (hL D.u_mem_L) ∈ D.auxL hL :=
  Subgroup.subset_closure (by simp)
theorem ρ_mem_auxL : conjAutOfMemNormalizer D.ρ (hL D.ρ_mem_L) ∈ D.auxL hL :=
  Subgroup.subset_closure (by simp)

@[expose] noncomputable def auxUV : D.AuxGroup hL := D.auxGen hL D.uv _ (D.uv_mem_auxL hL)
@[expose] noncomputable def auxT : D.AuxGroup hL := D.auxGen hL D.t _ (D.t_mem_auxL hL)
@[expose] noncomputable def auxU : D.AuxGroup hL := D.auxGen hL D.u _ (D.u_mem_auxL hL)
@[expose] noncomputable def auxRho : D.AuxGroup hL := D.auxGen hL D.ρ _ (D.ρ_mem_auxL hL)

theorem auxGen_mul {g h : S} (hg : g ∈ Subgroup.normalizer C) (hh : h ∈ Subgroup.normalizer C)
    (h1 : conjAutOfMemNormalizer g hg ∈ D.auxL hL) (h2 : conjAutOfMemNormalizer h hh ∈ D.auxL hL) :
    D.auxGen hL g hg h1 * D.auxGen hL h hh h2 =
      D.auxGen hL (g * h) (mul_mem hg hh)
        (by rw [conjAutOfMemNormalizer_mul hg hh]; exact mul_mem h1 h2) := by
  rw [auxGen, auxGen, auxGen, ← map_mul]
  congr 1
  apply Subtype.ext
  exact (conjAutOfMemNormalizer_mul hg hh).symm

theorem auxGen_congr {g h : S} (hgh : g = h) (hg : g ∈ Subgroup.normalizer C)
    (hh : h ∈ Subgroup.normalizer C) (h1 : conjAutOfMemNormalizer g hg ∈ D.auxL hL)
    (h2 : conjAutOfMemNormalizer h hh ∈ D.auxL hL) :
    D.auxGen hL g hg h1 = D.auxGen hL h hh h2 := by
  subst hgh
  rfl

theorem auxGen_eq_one {g : S} (hg : g ∈ Subgroup.normalizer C)
    (h1 : conjAutOfMemNormalizer g hg ∈ D.auxL hL) (hc : g ∈ Subgroup.centralizer (C : Set S)) :
    D.auxGen hL g hg h1 = 1 := by
  rw [auxGen, ← map_one SemidirectProduct.inr]
  congr 1
  apply Subtype.ext
  exact conjAutOfMemNormalizer_eq_one hg hc

theorem auxGen_conj_inl {g : S} (hg : g ∈ Subgroup.normalizer C)
    (h1 : conjAutOfMemNormalizer g hg ∈ D.auxL hL) (n : C) :
    (D.auxGen hL g hg h1)⁻¹ * SemidirectProduct.inl n * D.auxGen hL g hg h1 =
      SemidirectProduct.inl ⟨g⁻¹ * n * g,
        (Subgroup.mem_normalizer_iff''.mp hg (n : S)).mp n.2⟩ := by
  rw [auxGen, ← map_inv, ← SemidirectProduct.inl_aut_inv]
  congr 1

theorem auxGen_conj_inl' {g : S} (hg : g ∈ Subgroup.normalizer C)
    (h1 : conjAutOfMemNormalizer g hg ∈ D.auxL hL) (n : C) :
    D.auxGen hL g hg h1 * SemidirectProduct.inl n * (D.auxGen hL g hg h1)⁻¹ =
      SemidirectProduct.inl ⟨g * n * g⁻¹,
        (Subgroup.mem_normalizer_iff.mp hg (n : S)).mp n.2⟩ := by
  rw [auxGen, ← map_inv, ← SemidirectProduct.inl_aut]
  rfl

theorem mem_auxSub {X : Subgroup S} {z : D.AuxGroup hL} :
    z ∈ D.auxSub hL X ↔ ∃ n : C, (n : S) ∈ X ∧ SemidirectProduct.inl n = z := by
  simp [auxSub, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem inl_mem_auxSub {X : Subgroup S} {n : C} :
    SemidirectProduct.inl n ∈ D.auxSub hL X ↔ (n : S) ∈ X := by
  rw [mem_auxSub]
  constructor
  · rintro ⟨n', hn', hnn'⟩
    rwa [← SemidirectProduct.inl_injective hnn']
  · intro hn
    exact ⟨n, hn, rfl⟩

theorem auxGen_mem_normalizer {X : Subgroup S} (hXC : X ≤ C) {g : S}
    (hg : g ∈ Subgroup.normalizer C) (h1 : conjAutOfMemNormalizer g hg ∈ D.auxL hL)
    (hgX : g ∈ Subgroup.normalizer X) :
    D.auxGen hL g hg h1 ∈ Subgroup.normalizer (D.auxSub hL X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    obtain ⟨n, hn, rfl⟩ := (D.mem_auxSub hL).mp hz
    rw [D.auxGen_conj_inl' hL hg h1, D.inl_mem_auxSub hL]
    exact (Subgroup.mem_normalizer_iff.mp hgX _).mp hn
  · intro hz
    obtain ⟨n, hn, hnz⟩ := (D.mem_auxSub hL).mp hz
    have hz' : z = (D.auxGen hL g hg h1)⁻¹ * SemidirectProduct.inl n * D.auxGen hL g hg h1 := by
      rw [hnz]; group
    rw [hz', D.auxGen_conj_inl hL hg h1, D.inl_mem_auxSub hL]
    exact (Subgroup.mem_normalizer_iff''.mp hgX _).mp hn

theorem auxUV_mem_normalizer {X : Subgroup S} (hXC : X ≤ C) (h : D.uv ∈ Subgroup.normalizer X) :
    D.auxUV hL ∈ Subgroup.normalizer (D.auxSub hL X) := D.auxGen_mem_normalizer hL hXC _ _ h
theorem auxT_mem_normalizer {X : Subgroup S} (hXC : X ≤ C) (h : D.t ∈ Subgroup.normalizer X) :
    D.auxT hL ∈ Subgroup.normalizer (D.auxSub hL X) := D.auxGen_mem_normalizer hL hXC _ _ h
theorem auxU_mem_normalizer {X : Subgroup S} (hXC : X ≤ C) (h : D.u ∈ Subgroup.normalizer X) :
    D.auxU hL ∈ Subgroup.normalizer (D.auxSub hL X) := D.auxGen_mem_normalizer hL hXC _ _ h
theorem auxRho_mem_normalizer {X : Subgroup S} (hXC : X ≤ C) (h : D.ρ ∈ Subgroup.normalizer X) :
    D.auxRho hL ∈ Subgroup.normalizer (D.auxSub hL X) := D.auxGen_mem_normalizer hL hXC _ _ h

@[expose] noncomputable def auxSubEquiv {X : Subgroup S} (hXC : X ≤ C) : D.auxSub hL X ≃* X :=
  ((X.subgroupOf C).equivMapOfInjective SemidirectProduct.inl
    SemidirectProduct.inl_injective).symm.trans (Subgroup.subgroupOfEquivOfLe hXC)

theorem inl_auxSubEquiv_symm {X : Subgroup S} (hXC : X ≤ C) (x : X) :
    (((D.auxSubEquiv hL hXC).symm x : D.auxSub hL X) : D.AuxGroup hL) =
      SemidirectProduct.inl ⟨x, hXC x.2⟩ := rfl

theorem card_auxSub {X : Subgroup S} (hXC : X ≤ C) : Nat.card (D.auxSub hL X) = Nat.card X :=
  Nat.card_congr (D.auxSubEquiv hL hXC).toEquiv

theorem auxSubEquiv_conjBy {X : Subgroup S} (hXC : X ≤ C) {g : S}
    (hg : g ∈ Subgroup.normalizer C) (h1 : conjAutOfMemNormalizer g hg ∈ D.auxL hL)
    (hgX : g ∈ Subgroup.normalizer X) {g' : D.AuxGroup hL} (hg' : g' = D.auxGen hL g hg h1)
    (hgX' : g' ∈ Subgroup.normalizer (D.auxSub hL X)) (x : X) :
    D.auxSubEquiv hL hXC (conjBy hgX' ((D.auxSubEquiv hL hXC).symm x)) = conjBy hgX x := by
  subst hg'
  apply (D.auxSubEquiv hL hXC).symm.injective
  rw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [inl_auxSubEquiv_symm]
  change (D.auxGen hL g hg h1)⁻¹ * (((D.auxSubEquiv hL hXC).symm x : D.auxSub hL X) :
    D.AuxGroup hL) * D.auxGen hL g hg h1 = _
  rw [inl_auxSubEquiv_symm, D.auxGen_conj_inl hL hg h1]
  rfl

@[expose] noncomputable def toAux (hBC : B ≤ C) (hρ : D.ρ ^ 3 ∈ Subgroup.centralizer (C : Set S)) :
    StrothTypeData (D.auxSub hL B) τ where
  e := (MulEquiv.toAdditive (D.auxSubEquiv hL hBC)).trans D.e
  uv := D.auxUV hL
  t := D.auxT hL
  u := D.auxU hL
  ρ := D.auxRho hL
  uv_sq := by
    rw [auxUV, D.auxGen_mul]
    exact D.auxGen_eq_one hL _ _ (by rw [D.uv_sq]; exact Subgroup.one_mem _)
  t_sq := by
    rw [auxT, D.auxGen_mul]
    exact D.auxGen_eq_one hL _ _ (by rw [D.t_sq]; exact Subgroup.one_mem _)
  uv_comm_t := by
    rw [auxUV, auxT, D.auxGen_mul, D.auxGen_mul]
    exact D.auxGen_congr hL D.uv_comm_t _ _ _ _
  rho_cube := by
    rw [auxRho, D.auxGen_mul, D.auxGen_mul]
    exact D.auxGen_eq_one hL _ _ (by rw [← pow_three', pow_three]; simpa [pow_three] using hρ)
  u_sq := by
    rw [auxU, D.auxGen_mul]
    exact D.auxGen_eq_one hL _ _ (by rw [D.u_sq]; exact Subgroup.one_mem _)
  u_rho := by
    rw [auxU, auxRho, D.auxGen_mul, D.auxGen_mul, D.auxGen_mul]
    exact D.auxGen_eq_one hL _ _ (by rw [D.u_rho]; exact Subgroup.one_mem _)
  uv_rho := by
    rw [auxUV, auxRho, auxT, D.auxGen_mul, D.auxGen_mul]
    exact D.auxGen_congr hL D.uv_rho _ _ _ _
  t_rho := by
    rw [auxUV, auxRho, auxT, D.auxGen_mul, D.auxGen_mul, D.auxGen_mul]
    exact D.auxGen_congr hL D.t_rho _ _ _ _
  uv_comm_u := by
    rw [auxUV, auxU, D.auxGen_mul, D.auxGen_mul]
    exact D.auxGen_congr hL D.uv_comm_u _ _ _ _
  t_u := by
    rw [auxUV, auxU, auxT, D.auxGen_mul, D.auxGen_mul, D.auxGen_mul]
    exact D.auxGen_congr hL D.t_u _ _ _ _
  uv_mem := D.auxUV_mem_normalizer hL hBC D.uv_mem
  t_mem := D.auxT_mem_normalizer hL hBC D.t_mem
  u_mem := D.auxU_mem_normalizer hL hBC D.u_mem
  ρ_mem := D.auxRho_mem_normalizer hL hBC D.ρ_mem
  uv_conj := fun z => by
    obtain ⟨x, rfl⟩ := (D.auxSubEquiv hL hBC).symm.surjective z
    simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul]
    rw [D.auxSubEquiv_conjBy hL hBC _ _ D.uv_mem (g' := D.auxUV hL) rfl, MulEquiv.apply_symm_apply]
    exact D.uv_conj x
  t_conj := fun z => by
    obtain ⟨x, rfl⟩ := (D.auxSubEquiv hL hBC).symm.surjective z
    simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul]
    rw [D.auxSubEquiv_conjBy hL hBC _ _ D.t_mem (g' := D.auxT hL) rfl, MulEquiv.apply_symm_apply]
    exact D.t_conj x
  u_conj := fun z => by
    obtain ⟨x, rfl⟩ := (D.auxSubEquiv hL hBC).symm.surjective z
    simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul]
    rw [D.auxSubEquiv_conjBy hL hBC _ _ D.u_mem (g' := D.auxU hL) rfl, MulEquiv.apply_symm_apply]
    exact D.u_conj x
  ρ_conj := fun z => by
    obtain ⟨x, rfl⟩ := (D.auxSubEquiv hL hBC).symm.surjective z
    simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul]
    rw [D.auxSubEquiv_conjBy hL hBC _ _ D.ρ_mem (g' := D.auxRho hL) rfl, MulEquiv.apply_symm_apply]
    exact D.ρ_conj x


theorem toAux_uv (hBC : B ≤ C) (hρ : D.ρ ^ 3 ∈ Subgroup.centralizer (C : Set S)) :
    (D.toAux hL hBC hρ).uv = D.auxUV hL := rfl
theorem toAux_t (hBC : B ≤ C) (hρ : D.ρ ^ 3 ∈ Subgroup.centralizer (C : Set S)) :
    (D.toAux hL hBC hρ).t = D.auxT hL := rfl
theorem toAux_u (hBC : B ≤ C) (hρ : D.ρ ^ 3 ∈ Subgroup.centralizer (C : Set S)) :
    (D.toAux hL hBC hρ).u = D.auxU hL := rfl
theorem toAux_ρ (hBC : B ≤ C) (hρ : D.ρ ^ 3 ∈ Subgroup.centralizer (C : Set S)) :
    (D.toAux hL hBC hρ).ρ = D.auxRho hL := rfl

theorem toAux_L_le (hBC : B ≤ C) (hρ : D.ρ ^ 3 ∈ Subgroup.centralizer (C : Set S)) :
    (D.toAux hL hBC hρ).L ≤ Subgroup.normalizer (D.auxSub hL C) := by
  rw [StrothTypeData.L, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact D.auxUV_mem_normalizer hL le_rfl (hL D.uv_mem_L)
  · exact D.auxT_mem_normalizer hL le_rfl (hL D.t_mem_L)
  · exact D.auxU_mem_normalizer hL le_rfl (hL D.u_mem_L)
  · exact D.auxRho_mem_normalizer hL le_rfl (hL D.ρ_mem_L)

theorem auxSub_mono {X Y : Subgroup S} (h : X ≤ Y) : D.auxSub hL X ≤ D.auxSub hL Y := by
  intro z hz
  obtain ⟨n, hn, rfl⟩ := (D.mem_auxSub hL).mp hz
  exact (D.inl_mem_auxSub hL).mpr (h hn)

theorem auxSub_le_centralizer {X Y : Subgroup S}
    (h : X ≤ Subgroup.centralizer (Y : Set S)) :
    D.auxSub hL X ≤ Subgroup.centralizer (D.auxSub hL Y : Set (D.AuxGroup hL)) := by
  intro z hz
  obtain ⟨n, hn, rfl⟩ := (D.mem_auxSub hL).mp hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨m, hm, rfl⟩ := (D.mem_auxSub hL).mp hw
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp (h hn) _ hm)

theorem mem_normalizer_of_auxGen {X : Subgroup S} (hXC : X ≤ C) {g : S}
    (hg : g ∈ Subgroup.normalizer C) (h1 : conjAutOfMemNormalizer g hg ∈ D.auxL hL)
    (hgX' : D.auxGen hL g hg h1 ∈ Subgroup.normalizer (D.auxSub hL X)) :
    g ∈ Subgroup.normalizer X := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  by_cases hy : y ∈ C
  · have := (Subgroup.mem_normalizer_iff.mp hgX') (SemidirectProduct.inl ⟨y, hy⟩)
    rw [D.auxGen_conj_inl' hL hg h1, D.inl_mem_auxSub hL, D.inl_mem_auxSub hL] at this
    exact this
  · constructor
    · intro h
      exact absurd (hXC h) hy
    · intro h
      exact absurd ((Subgroup.mem_normalizer_iff.mp hg y).mpr (hXC h)) hy

@[expose] noncomputable def ofAux {X : Subgroup S} (hXC : X ≤ C) {τ' : StrothTypeIndex}
    (D' : StrothTypeData (D.auxSub hL X) τ') (huv : D'.uv = D.auxUV hL) (ht : D'.t = D.auxT hL)
    (hu : D'.u = D.auxU hL) (hρ : D'.ρ = D.auxRho hL) : StrothWeakTypeData X τ' :=
  have huvX : D.uv ∈ Subgroup.normalizer X :=
    D.mem_normalizer_of_auxGen hL hXC _ (D.uv_mem_auxL hL)
      (huv ▸ D'.uv_mem : D.auxUV hL ∈ Subgroup.normalizer (D.auxSub hL X))
  have htX : D.t ∈ Subgroup.normalizer X :=
    D.mem_normalizer_of_auxGen hL hXC _ (D.t_mem_auxL hL)
      (ht ▸ D'.t_mem : D.auxT hL ∈ Subgroup.normalizer (D.auxSub hL X))
  have huX : D.u ∈ Subgroup.normalizer X :=
    D.mem_normalizer_of_auxGen hL hXC _ (D.u_mem_auxL hL)
      (hu ▸ D'.u_mem : D.auxU hL ∈ Subgroup.normalizer (D.auxSub hL X))
  have hρX : D.ρ ∈ Subgroup.normalizer X :=
    D.mem_normalizer_of_auxGen hL hXC _ (D.ρ_mem_auxL hL)
      (hρ ▸ D'.ρ_mem : D.auxRho hL ∈ Subgroup.normalizer (D.auxSub hL X))
  { e := (MulEquiv.toAdditive (D.auxSubEquiv hL hXC).symm).trans D'.e
    uv := D.uv
    t := D.t
    u := D.u
    ρ := D.ρ
    uv_sq := D.uv_sq
    t_sq := D.t_sq
    uv_comm_t := D.uv_comm_t
    rho_odd := D.rho_odd
    u_sq := D.u_sq
    u_rho := D.u_rho
    uv_rho := D.uv_rho
    t_rho := D.t_rho
    uv_comm_u := D.uv_comm_u
    t_u := D.t_u
    uv_mem := huvX
    t_mem := htX
    u_mem := huX
    ρ_mem := hρX
    uv_conj := fun x => by
      simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul]
      have h := D.auxSubEquiv_conjBy hL hXC _ (D.uv_mem_auxL hL) huvX huv D'.uv_mem x
      rw [← h, MulEquiv.symm_apply_apply]
      exact D'.uv_conj _
    t_conj := fun x => by
      simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul]
      have h := D.auxSubEquiv_conjBy hL hXC _ (D.t_mem_auxL hL) htX ht D'.t_mem x
      rw [← h, MulEquiv.symm_apply_apply]
      exact D'.t_conj _
    u_conj := fun x => by
      simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul]
      have h := D.auxSubEquiv_conjBy hL hXC _ (D.u_mem_auxL hL) huX hu D'.u_mem x
      rw [← h, MulEquiv.symm_apply_apply]
      exact D'.u_conj _
    ρ_conj := fun x => by
      simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul]
      have h := D.auxSubEquiv_conjBy hL hXC _ (D.ρ_mem_auxL hL) hρX hρ D'.ρ_mem x
      rw [← h, MulEquiv.symm_apply_apply]
      exact D'.ρ_conj _ }

theorem ofAux_uv {X : Subgroup S} (hXC : X ≤ C) {τ' : StrothTypeIndex}
    (D' : StrothTypeData (D.auxSub hL X) τ') (huv : D'.uv = D.auxUV hL) (ht : D'.t = D.auxT hL)
    (hu : D'.u = D.auxU hL) (hρ : D'.ρ = D.auxRho hL) :
    (D.ofAux hL hXC D' huv ht hu hρ).uv = D.uv := rfl
theorem ofAux_t {X : Subgroup S} (hXC : X ≤ C) {τ' : StrothTypeIndex}
    (D' : StrothTypeData (D.auxSub hL X) τ') (huv : D'.uv = D.auxUV hL) (ht : D'.t = D.auxT hL)
    (hu : D'.u = D.auxU hL) (hρ : D'.ρ = D.auxRho hL) :
    (D.ofAux hL hXC D' huv ht hu hρ).t = D.t := rfl
theorem ofAux_u {X : Subgroup S} (hXC : X ≤ C) {τ' : StrothTypeIndex}
    (D' : StrothTypeData (D.auxSub hL X) τ') (huv : D'.uv = D.auxUV hL) (ht : D'.t = D.auxT hL)
    (hu : D'.u = D.auxU hL) (hρ : D'.ρ = D.auxRho hL) :
    (D.ofAux hL hXC D' huv ht hu hρ).u = D.u := rfl
theorem ofAux_ρ {X : Subgroup S} (hXC : X ≤ C) {τ' : StrothTypeIndex}
    (D' : StrothTypeData (D.auxSub hL X) τ') (huv : D'.uv = D.auxUV hL) (ht : D'.t = D.auxT hL)
    (hu : D'.u = D.auxU hL) (hρ : D'.ρ = D.auxRho hL) :
    (D.ofAux hL hXC D' huv ht hu hρ).ρ = D.ρ := rfl

theorem ofAux_L {X : Subgroup S} (hXC : X ≤ C) {τ' : StrothTypeIndex}
    (D' : StrothTypeData (D.auxSub hL X) τ') (huv : D'.uv = D.auxUV hL) (ht : D'.t = D.auxT hL)
    (hu : D'.u = D.auxU hL) (hρ : D'.ρ = D.auxRho hL) :
    (D.ofAux hL hXC D' huv ht hu hρ).L = D.L := rfl

theorem noInvolutionsCentralizing_auxSub {S' : Subgroup S} (hBC : B ≤ C)
    (h : NoInvolutionsCentralizing S' B) (hCS' : C ≤ S') :
    NoInvolutionsCentralizing (D.auxSub hL C) (D.auxSub hL B) := by
  intro z hz hzz hzc
  obtain ⟨n, -, rfl⟩ := (D.mem_auxSub hL).mp hz
  have hnn : (n : S) * n = 1 := by
    have h1 : (SemidirectProduct.inl (n * n) : D.AuxGroup hL) = SemidirectProduct.inl (1 : C) := by
      rw [map_mul, map_one]; exact hzz
    exact congrArg Subtype.val (SemidirectProduct.inl_injective h1)
  have hnc : (n : S) ∈ Subgroup.centralizer (B : Set S) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 := Subgroup.mem_centralizer_iff.mp hzc (SemidirectProduct.inl ⟨b, hBC hb⟩)
      ((D.inl_mem_auxSub hL).mpr hb)
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (SemidirectProduct.inl_injective h1)
  exact (D.inl_mem_auxSub hL).mpr (h _ (hCS' n.2) hnn hnc)

end StrothWeakTypeData

theorem cube_mem_centralizer_of_index_le_four {B C : Subgroup S} {g : S} [Finite C]
    (hBC : B ≤ C) (hp : IsPGroup 2 C) (hcard : Nat.card C ≤ 4 * Nat.card B)
    (hgB : g ∈ Subgroup.normalizer B) (hgC : g ∈ Subgroup.normalizer C) (hodd : Odd (orderOf g))
    (hg3 : g ^ 3 ∈ Subgroup.centralizer (B : Set S)) :
    g ^ 3 ∈ Subgroup.centralizer (C : Set S) := by
  classical
  have hconjC : ∀ (k : ℕ) (c : S), c ∈ C → (g ^ k)⁻¹ * c * g ^ k ∈ C := fun k c hc =>
    (Subgroup.mem_normalizer_iff''.mp (pow_mem hgC k) c).mp hc
  have hconjB : ∀ (k : ℕ) (c : S), c ∈ B → (g ^ k)⁻¹ * c * g ^ k ∈ B := fun k c hc =>
    (Subgroup.mem_normalizer_iff''.mp (pow_mem hgB k) c).mp hc
  let κ : ℕ → ↥C → ↥C := fun k c => ⟨(g ^ k)⁻¹ * c * g ^ k, hconjC k c c.2⟩
  have hκ : ∀ (k : ℕ) (a b : ↥C), QuotientGroup.leftRel (B.subgroupOf C) a b →
      QuotientGroup.leftRel (B.subgroupOf C) (κ k a) (κ k b) := by
    intro k a b hab
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab ⊢
    have h1 := hconjB k _ hab
    convert h1 using 1
    simp only [κ, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  let β : Equiv.Perm (↥C ⧸ B.subgroupOf C) :=
    { toFun := Quotient.map' (κ 1) (hκ 1)
      invFun := Quotient.map' (fun c : ↥C => (⟨g * c * g⁻¹,
          (Subgroup.mem_normalizer_iff.mp hgC c).mp c.2⟩ : ↥C)) (by
        intro a b hab
        rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab ⊢
        have h1 := (Subgroup.mem_normalizer_iff.mp hgB _).mp hab
        convert h1 using 1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group)
      left_inv := by
        intro ω
        induction ω using Quotient.inductionOn' with
        | h c =>
          rw [Quotient.map'_mk'', Quotient.map'_mk'']
          congr 1
          apply Subtype.ext
          simp only [κ, pow_one]
          group
      right_inv := by
        intro ω
        induction ω using Quotient.inductionOn' with
        | h c =>
          rw [Quotient.map'_mk'', Quotient.map'_mk'']
          congr 1
          apply Subtype.ext
          simp only [κ, pow_one]
          group }
  have hβk : ∀ (k : ℕ) (c : ↥C), (β ^ k) (Quotient.mk'' c) = Quotient.mk'' (κ k c) := by
    intro k
    induction k with
    | zero => intro c; simp [κ]
    | succ k ih =>
      intro c
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      show Quotient.mk'' (κ 1 (κ k c)) = Quotient.mk'' (κ (k + 1) c)
      congr 1
      apply Subtype.ext
      simp only [κ, pow_succ]
      group
  have hβr : β ^ orderOf g = 1 := by
    ext ω
    induction ω using Quotient.inductionOn' with
    | h c =>
      rw [hβk]
      show Quotient.mk'' (κ (orderOf g) c) = Quotient.mk'' c
      congr 1
      apply Subtype.ext
      simp [κ, pow_orderOf_eq_one]
  have hidx : Nat.card (↥C ⧸ B.subgroupOf C) ≤ 4 := by
    have h1 := Subgroup.card_mul_index (B.subgroupOf C)
    have h2 : Nat.card (B.subgroupOf C) = Nat.card B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv
    rw [h2] at h1
    rw [← Subgroup.index_eq_card]
    haveI : Finite B := Finite.of_injective (fun x : B => (⟨x, hBC x.2⟩ : C)) (by
      intro x y hxy
      have h := congrArg (fun z : C => (z : S)) hxy
      exact Subtype.ext h)
    have hB : 0 < Nat.card B := Nat.card_pos
    nlinarith
  have hβ24 : orderOf β ∣ 24 := by
    have h1 := orderOf_dvd_natCard β
    rw [Nat.card_perm] at h1
    exact h1.trans ((Nat.factorial_dvd_factorial hidx).trans (by decide))
  have hβ3 : β ^ 3 = 1 := by
    have hodd' : Odd (orderOf β) := Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one hβr)
    have h3 : orderOf β ∣ 3 := by
      have hcop : Nat.Coprime (orderOf β) 8 := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
        exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd')
      exact hcop.dvd_of_dvd_mul_left (show orderOf β ∣ 8 * 3 by simpa using hβ24)
    exact orderOf_dvd_iff_pow_eq_one.mp h3
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  have h1 : (Quotient.mk'' (κ 3 ⟨c, hc⟩) : ↥C ⧸ B.subgroupOf C) = Quotient.mk'' ⟨c, hc⟩ := by
    rw [← hβk, hβ3, Equiv.Perm.one_apply]
  have h2 := Quotient.exact' h1
  rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h2
  obtain ⟨b, hb⟩ : ∃ b : S, b = ((g ^ 3)⁻¹ * c * g ^ 3)⁻¹ * c := ⟨_, rfl⟩
  have hbB : b ∈ B := by
    rw [hb]; simpa [κ] using h2
  have hbinv : b⁻¹ ∈ B := inv_mem hbB
  have hstep : (g ^ 3)⁻¹ * c * g ^ 3 = c * b⁻¹ := by
    rw [hb]; group
  have hhB : ∀ x ∈ B, (g ^ 3)⁻¹ * x * g ^ 3 = x := fun x hx => by
    have := (Subgroup.mem_centralizer_iff.mp hg3) x hx
    rw [mul_assoc, this, ← mul_assoc, inv_mul_cancel, one_mul]
  have hk : ∀ k : ℕ, ((g ^ 3) ^ k)⁻¹ * c * (g ^ 3) ^ k = c * b⁻¹ ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc ((g ^ 3) ^ (k + 1))⁻¹ * c * (g ^ 3) ^ (k + 1)
          = (g ^ 3)⁻¹ * (((g ^ 3) ^ k)⁻¹ * c * (g ^ 3) ^ k) * g ^ 3 := by
            rw [pow_succ]; group
        _ = (g ^ 3)⁻¹ * c * g ^ 3 * ((g ^ 3)⁻¹ * b⁻¹ ^ k * g ^ 3) := by rw [ih]; group
        _ = c * b⁻¹ * b⁻¹ ^ k := by rw [hstep, hhB _ (pow_mem hbinv k)]
        _ = c * b⁻¹ ^ (k + 1) := by rw [pow_succ', mul_assoc]
  have hord : Odd (orderOf (g ^ 3)) := Odd.of_dvd_nat hodd (orderOf_pow_dvd 3)
  have hbr : b⁻¹ ^ orderOf (g ^ 3) = 1 := by
    have := hk (orderOf (g ^ 3))
    rw [pow_orderOf_eq_one, inv_one, one_mul, mul_one] at this
    exact (mul_eq_left.mp this.symm)
  have hb1 : b⁻¹ = 1 := by
    obtain ⟨j, hj⟩ := hp ⟨b⁻¹, hBC hbinv⟩
    have hj' : b⁻¹ ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have hd := Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hord))
      (orderOf_dvd_of_pow_eq_one hj') (orderOf_dvd_of_pow_eq_one hbr)
    exact orderOf_eq_one_iff.mp hd
  have hfix : (g ^ 3)⁻¹ * c * g ^ 3 = c := by rw [hstep, hb1, mul_one]
  calc c * g ^ 3 = g ^ 3 * ((g ^ 3)⁻¹ * c * g ^ 3) := by group
    _ = g ^ 3 * c := by rw [hfix]

namespace StrothWeakTypeData

variable (D : StrothWeakTypeData B τ)

theorem rho_cube_mem_of_card_le (hL : D.L ≤ Subgroup.normalizer C) [Finite C] (hBC : B ≤ C)
    (hp : IsPGroup 2 C)
    (hcard : Nat.card C ≤ 4 * Nat.card B) : D.ρ ^ 3 ∈ Subgroup.centralizer (C : Set S) :=
  cube_mem_centralizer_of_index_le_four hBC hp hcard D.ρ_mem (hL D.ρ_mem_L) D.rho_odd
    D.rho_cube_mem

end StrothWeakTypeData

end Aux

end CFSG.CGT.Stroth77
