module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Basic
public import CFSG.ClassicalInvolution.SL2Facts

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg.Sp (blockMat)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

section Standard

variable (K n) in
@[expose] noncomputable def longRootSp2 (k : Fin n) : Subgroup (StatedSp n K) :=
  (longBlock K n k).range

theorem longInv_mem_longRootSp2 (k : Fin n) : longInv K n k ∈ longRootSp2 K n k :=
  ⟨-1, rfl⟩

theorem isClassicalSL2_longRootSp2 (h2 : (2 : K) ≠ 0) (k : Fin n) :
    CFSG.ClassicalInvolution.IsClassicalSL2 K (longRootSp2 K n k) (longInv K n k) where
  nonempty_mulEquiv := ⟨(MonoidHom.ofInjective (longBlock_injective k)).symm⟩
  mem := longInv_mem_longRootSp2 k
  orderOf_eq_two := by
    rw [longInv, orderOf_injective (longBlock K n k) (longBlock_injective k) (-1)]
    exact CFSG.Semidihedral.OddFieldSL2.minusIdentity_orderOf K h2
  le_centralizer := by
    rintro _ ⟨A, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, longInv, ← map_mul, ← map_mul, mul_neg, mul_one,
      neg_mul, one_mul]
  centralizer_le_normalizer := by
    intro c hc
    have hc' : c * longInv K n k = longInv K n k * c :=
      Subgroup.mem_centralizer_singleton_iff.1 hc
    have hcinv : c⁻¹ * longInv K n k = longInv K n k * c⁻¹ :=
      (Commute.inv_left (show Commute c (longInv K n k) from hc')).eq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have e : (longRootSp2 K n k : Set (StatedSp n K)) = longRootGroup (longInv K n k) := by
      ext y
      exact (SetLike.ext_iff.1 (range_longBlock_eq_longRootGroup h2 k)) y
    change x ∈ longRootSp2 K n k ↔ c * x * c⁻¹ ∈ longRootSp2 K n k
    rw [longRootSp2, range_longBlock_eq_longRootGroup h2 k]
    constructor
    · exact conj_mem_longRootGroup hc'
    · intro hx
      have := conj_mem_longRootGroup hcinv hx
      have e3 : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
      rwa [e3] at this

theorem longBlock_surjective_one : Function.Surjective (longBlock K 1 0) := by
  intro x
  have hx : x ∈ suppGroup (coords (0 : Fin 1)) := by
    intro r t hrt
    exfalso
    apply hrt
    have h : ∀ a : Fin 1 ⊕ Fin 1, a ∈ coords (0 : Fin 1) := fun a => by
      rcases a with a | a
      · rw [Subsingleton.elim a 0]
        exact inl_mem_coords 0
      · rw [Subsingleton.elim a 0]
        exact inr_mem_coords 0
    exact ⟨h r, h t⟩
  rw [← range_longBlock] at hx
  exact hx

variable (K) in
@[expose] noncomputable def longBlockEquivOne : SL(2, K) ≃* StatedSp 1 K :=
  MulEquiv.ofBijective (longBlock K 1 0) ⟨longBlock_injective 0, longBlock_surjective_one⟩

end Standard

section Complementary

theorem commute_suppGroup_compl {S : Set (Fin n ⊕ Fin n)} {x y : StatedSp n K}
    (hx : x ∈ suppGroup S) (hy : y ∈ suppGroup Sᶜ) : Commute x y := by
  have hx' : IsSupp S (mat n K x) := hx
  have hy' : IsSupp Sᶜ (mat n K y) := hy
  have h1 : (mat n K x - 1) * (mat n K y - 1) = 0 := by
    ext r s
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : t ∈ S
    · have := hy' t s (fun h => h.1 ht)
      simp only [Matrix.sub_apply]
      rw [this, sub_self, mul_zero]
    · have := hx' r t (fun h => ht h.2)
      simp only [Matrix.sub_apply]
      rw [this, sub_self, zero_mul]
  have h2 : (mat n K y - 1) * (mat n K x - 1) = 0 := by
    ext r s
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : t ∈ S
    · have := hy' r t (fun h => h.2 ht)
      simp only [Matrix.sub_apply]
      rw [this, sub_self, zero_mul]
    · have := hx' t s (fun h => ht h.1)
      simp only [Matrix.sub_apply]
      rw [this, sub_self, mul_zero]
  have h3 : mat n K x * mat n K y - mat n K y * mat n K x = 0 := by
    have e : mat n K x * mat n K y - mat n K y * mat n K x =
        (mat n K x - 1) * (mat n K y - 1) - (mat n K y - 1) * (mat n K x - 1) := by
      noncomm_ring
    rw [e, h1, h2, sub_zero]
  refine mat_injective ?_
  rw [map_mul, map_mul]
  exact sub_eq_zero.1 h3

theorem disjoint_suppGroup_compl (S : Set (Fin n ⊕ Fin n)) :
    Disjoint (suppGroup S : Subgroup (StatedSp n K)) (suppGroup Sᶜ) := by
  rw [Subgroup.disjoint_def]
  intro x hx hy
  have hx' : IsSupp S (mat n K x) := hx
  have hy' : IsSupp Sᶜ (mat n K x) := hy
  refine mat_injective ?_
  rw [map_one]
  ext r t
  by_cases h : r ∈ S ∧ t ∈ S
  · exact hy' r t (fun h' => h'.1 h.1)
  · exact hx' r t h

end Complementary

section Conj

theorem mulVec_eq_iff (g : StatedSp n K) (u w : Fin n ⊕ Fin n → K) :
    mat n K g *ᵥ u = w ↔ u = mat n K g⁻¹ *ᵥ w := by
  constructor
  · rintro rfl
    rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
  · rintro rfl
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]

theorem mem_fixSpace_conj {i g : StatedSp n K} {w : Fin n ⊕ Fin n → K} :
    w ∈ fixSpace (g * i * g⁻¹) ↔ mat n K g⁻¹ *ᵥ w ∈ fixSpace i := by
  rw [mem_fixSpace, mem_fixSpace, map_mul, map_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, mulVec_eq_iff]

theorem mem_minusSpace_conj {i g : StatedSp n K} {w : Fin n ⊕ Fin n → K} :
    w ∈ minusSpace (g * i * g⁻¹) ↔ mat n K g⁻¹ *ᵥ w ∈ minusSpace i := by
  rw [mem_minusSpace, mem_minusSpace, map_mul, map_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, mulVec_eq_iff, Matrix.mulVec_neg]

theorem mulVec_inv_mulVec (g : StatedSp n K) (v : Fin n ⊕ Fin n → K) :
    mat n K g⁻¹ *ᵥ (mat n K g *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]

theorem mulVec_mulVec_inv (g : StatedSp n K) (v : Fin n ⊕ Fin n → K) :
    mat n K g *ᵥ (mat n K g⁻¹ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]

theorem mem_fixing_conj {W W' : Set (Fin n ⊕ Fin n → K)} (g x : StatedSp n K)
    (hW : ∀ w, w ∈ W' ↔ mat n K g⁻¹ *ᵥ w ∈ W) : x ∈ fixing W' ↔ g⁻¹ * x * g ∈ fixing W := by
  constructor
  · intro hx v hv
    have hw : mat n K g *ᵥ v ∈ W' := (hW _).2 (by rw [mulVec_inv_mulVec]; exact hv)
    have e : mat n K (g⁻¹ * x * g) *ᵥ v =
        mat n K g⁻¹ *ᵥ (mat n K x *ᵥ (mat n K g *ᵥ v)) := by
      simp only [map_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [e, hx _ hw, mulVec_inv_mulVec]
  · intro hx w hw
    have hv := hx _ ((hW w).1 hw)
    have e : mat n K (g⁻¹ * x * g) *ᵥ (mat n K g⁻¹ *ᵥ w) =
        mat n K g⁻¹ *ᵥ (mat n K x *ᵥ w) := by
      have h1 : mat n K g * mat n K g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      simp only [map_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rw [h1, Matrix.mul_one]
    rw [e] at hv
    calc mat n K x *ᵥ w = mat n K g *ᵥ (mat n K g⁻¹ *ᵥ (mat n K x *ᵥ w)) :=
          (mulVec_mulVec_inv g _).symm
      _ = mat n K g *ᵥ (mat n K g⁻¹ *ᵥ w) := by rw [hv]
      _ = w := mulVec_mulVec_inv g w

theorem fixing_eq_map_conj {W W' : Set (Fin n ⊕ Fin n → K)} (g : StatedSp n K)
    (hW : ∀ w, w ∈ W' ↔ mat n K g⁻¹ *ᵥ w ∈ W) :
    fixing W' = (fixing W).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  exact mem_fixing_conj g x hW

theorem longRootGroup_conj (i g : StatedSp n K) :
    longRootGroup (g * i * g⁻¹) = (longRootGroup i).map (MulAut.conj g).toMonoidHom :=
  fixing_eq_map_conj g fun _ => mem_fixSpace_conj

theorem complGroup_conj (i g : StatedSp n K) :
    complGroup (g * i * g⁻¹) = (complGroup i).map (MulAut.conj g).toMonoidHom :=
  fixing_eq_map_conj g fun _ => mem_minusSpace_conj

theorem mem_centralizer_conj {c g i : StatedSp n K} :
    c ∈ Subgroup.centralizer ({g * i * g⁻¹} : Set (StatedSp n K)) ↔
      g⁻¹ * c * g ∈ Subgroup.centralizer ({i} : Set (StatedSp n K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g⁻¹ * c * g * i = g⁻¹ * (c * (g * i * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * i * g⁻¹) * c) * g := by rw [h]
      _ = i * (g⁻¹ * c * g) := by group
  · intro h
    calc c * (g * i * g⁻¹) = g * (g⁻¹ * c * g * i) * g⁻¹ := by group
      _ = g * (i * (g⁻¹ * c * g)) * g⁻¹ := by rw [h]
      _ = (g * i * g⁻¹) * c := by group

end Conj

section LongRoot

@[expose] def IsLongRootSp2 (L : Subgroup (StatedSp n K)) (i : StatedSp n K) : Prop :=
  ∃ (k : Fin n) (g : StatedSp n K),
    L = (longRootSp2 K n k).map (MulAut.conj g).toMonoidHom ∧ i = g * longInv K n k * g⁻¹

theorem isLongRootSp2_standard (k : Fin n) :
    IsLongRootSp2 (longRootSp2 K n k) (longInv K n k) :=
  ⟨k, 1, by ext x; simp, by simp⟩

theorem IsLongRootSp2.conj {L : Subgroup (StatedSp n K)} {i : StatedSp n K}
    (h : IsLongRootSp2 L i) (g : StatedSp n K) :
    IsLongRootSp2 (L.map (MulAut.conj g).toMonoidHom) (g * i * g⁻¹) := by
  obtain ⟨k, g₀, rfl, rfl⟩ := h
  refine ⟨k, g * g₀, ?_, by group⟩
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem IsLongRootSp2.eq_longRootGroup (h2 : (2 : K) ≠ 0) {L : Subgroup (StatedSp n K)}
    {i : StatedSp n K} (h : IsLongRootSp2 L i) : L = longRootGroup i := by
  obtain ⟨k, g, rfl, rfl⟩ := h
  rw [longRootSp2, range_longBlock_eq_longRootGroup h2, longRootGroup_conj]

theorem IsLongRootSp2.mem_iff (h2 : (2 : K) ≠ 0) {L : Subgroup (StatedSp n K)}
    {i : StatedSp n K} (h : IsLongRootSp2 L i) {x : StatedSp n K} :
    x ∈ L ↔ ∀ v ∈ fixSpace i, mat n K x *ᵥ v = v := by
  rw [h.eq_longRootGroup h2]
  exact mem_longRootGroup

theorem IsLongRootSp2.isClassicalSL2 (h2 : (2 : K) ≠ 0) {L : Subgroup (StatedSp n K)}
    {i : StatedSp n K} (h : IsLongRootSp2 L i) :
    CFSG.ClassicalInvolution.IsClassicalSL2 K L i := by
  obtain ⟨k, g, rfl, rfl⟩ := h
  exact (isClassicalSL2_longRootSp2 h2 k).conj g

theorem IsLongRootSp2.eq_of_orderOf_eq_two (h2 : (2 : K) ≠ 0) {L : Subgroup (StatedSp n K)}
    {i : StatedSp n K} (h : IsLongRootSp2 L i) {t : StatedSp n K} (htL : t ∈ L)
    (ht : orderOf t = 2) : t = i := by
  have hc := h.isClassicalSL2 h2
  obtain ⟨e⟩ := hc.nonempty_mulEquiv
  have key : ∀ s : L, orderOf s = 2 → e s = -1 := fun s hs =>
    (CFSG.Semidihedral.OddFieldSL2.orderOf_eq_two_iff K h2 (e s)).mp
      (by rw [MulEquiv.orderOf_eq]; exact hs)
  have h1 := key ⟨t, htL⟩ (by rwa [Subgroup.orderOf_mk])
  have h2' := key ⟨i, hc.mem⟩ (by rw [Subgroup.orderOf_mk]; exact hc.orderOf_eq_two)
  exact congrArg Subtype.val (e.injective (h1.trans h2'.symm))

theorem IsLongRootSp2.involution_unique (h2 : (2 : K) ≠ 0) {L : Subgroup (StatedSp n K)}
    {i i' : StatedSp n K} (h : IsLongRootSp2 L i) (h' : IsLongRootSp2 L i') : i = i' :=
  (h.eq_of_orderOf_eq_two h2 (h'.isClassicalSL2 h2).mem
    ((h'.isClassicalSL2 h2).orderOf_eq_two)).symm

theorem IsLongRootSp2.normal_subgroupOf_centralizer (h2 : (2 : K) ≠ 0)
    {L : Subgroup (StatedSp n K)} {i : StatedSp n K} (h : IsLongRootSp2 L i) :
    (L.subgroupOf (Subgroup.centralizer ({i} : Set (StatedSp n K)))).Normal := by
  have hc := h.isClassicalSL2 h2
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hc.le_centralizer]
  exact hc.centralizer_le_normalizer

end LongRoot

section Centralizer

theorem mulVec_mem_minusSpace {i c : StatedSp n K} (hc : c * i = i * c) {v : Fin n ⊕ Fin n → K}
    (hv : v ∈ minusSpace i) : mat n K c *ᵥ v ∈ minusSpace i := by
  rw [mem_minusSpace, Matrix.mulVec_mulVec, ← map_mul, ← hc, map_mul, ← Matrix.mulVec_mulVec,
    mem_minusSpace.1 hv, Matrix.mulVec_neg]

theorem exists_mul_of_commute_longInv (h2 : (2 : K) ≠ 0) (k : Fin n) {c : StatedSp n K}
    (hc : c * longInv K n k = longInv K n k * c) :
    ∃ a ∈ longRootSp2 K n k, ∃ b ∈ complGroup (longInv K n k), c = a * b := by
  have hpq : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k := Sum.inl_ne_inr
  have hoff : ∀ r t, r ∉ coords k → t ∈ coords k → mat n K c r t = 0 := by
    intro r t hr ht
    have hv : (Pi.single t (1 : K) : Fin n ⊕ Fin n → K) ∈ minusSpace (longInv K n k) := by
      rw [mem_minusSpace_longInv h2]
      intro u hu
      have : u ≠ t := fun e => hu (e ▸ ht)
      simp [this]
    have := (mem_minusSpace_longInv h2 k).1 (mulVec_mem_minusSpace hc hv) r hr
    rwa [mulVec_single_one_apply] at this
  have hdet : (stdBlock k (mat n K c)).det = 1 :=
    det_stdBlock_eq_one c k fun r hr => hoff r _ hr (inl_mem_coords k)
  set a : StatedSp n K := longBlock K n k (mkSL (stdBlock k (mat n K c)) hdet) with ha
  have hcol : ∀ u t, t ∈ coords k → mat n K c u t = mat n K a u t := by
    intro u t ht
    by_cases hu : u ∈ coords k
    · rw [ha, mat_longBlock, coe_mkSL]
      rcases mem_coords.1 hu with rfl | rfl <;> rcases mem_coords.1 ht with rfl | rfl <;>
        simp [stdBlock, blockMat, hpq.symm]
    · rw [hoff u t hu ht, ha, mat_longBlock, coe_mkSL,
        blockMat_apply_of_not_mem k _ (fun h => hu h.1)]
      exact (Matrix.one_apply_ne (fun e => hu (by rw [e]; exact ht))).symm
  refine ⟨a, ⟨_, rfl⟩, a⁻¹ * c, ?_, by group⟩
  rw [complGroup_longInv h2, mem_suppGroup_iff (parClosed_coords k).compl]
  intro t ht r
  have ht' : t ∈ coords k := by simpa using ht
  rw [map_mul, Matrix.mul_apply, Finset.sum_congr rfl (fun u _ => by rw [hcol u t ht']),
    ← Matrix.mul_apply, ← map_mul, inv_mul_cancel, map_one]

end Centralizer

section Product

variable {L : Subgroup (StatedSp n K)} {i : StatedSp n K}

theorem longRootSp2_eq_suppGroup (k : Fin n) :
    longRootSp2 K n k = suppGroup (coords k) := range_longBlock k

theorem mem_map_conj_iff {H : Subgroup (StatedSp n K)} {g x : StatedSp n K} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem mem_complGroup_conj {i g x : StatedSp n K} :
    x ∈ complGroup (g * i * g⁻¹) ↔ g⁻¹ * x * g ∈ complGroup i := by
  rw [complGroup_conj, mem_map_conj_iff]

theorem IsLongRootSp2.commute_of_mem_complGroup (h2 : (2 : K) ≠ 0) (h : IsLongRootSp2 L i)
    {x y : StatedSp n K} (hx : x ∈ L) (hy : y ∈ complGroup i) : Commute x y := by
  obtain ⟨k, g, rfl, rfl⟩ := h
  rw [mem_map_conj_iff, longRootSp2_eq_suppGroup] at hx
  rw [mem_complGroup_conj, complGroup_longInv h2] at hy
  have hc : Commute (g⁻¹ * x * g) (g⁻¹ * y * g) := commute_suppGroup_compl hx hy
  have e := hc.map (MulAut.conj g).toMonoidHom
  simpa [MulAut.conj_apply, mul_assoc] using e

theorem IsLongRootSp2.disjoint_complGroup (h2 : (2 : K) ≠ 0) (h : IsLongRootSp2 L i) :
    Disjoint L (complGroup i) := by
  obtain ⟨k, g, rfl, rfl⟩ := h
  rw [Subgroup.disjoint_def]
  intro x hx hy
  rw [mem_map_conj_iff, longRootSp2_eq_suppGroup] at hx
  rw [mem_complGroup_conj, complGroup_longInv h2] at hy
  have h1 : g⁻¹ * x * g = 1 :=
    Subgroup.disjoint_def.1 (disjoint_suppGroup_compl (coords k)) hx hy
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem IsLongRootSp2.exists_mul_of_mem_centralizer (h2 : (2 : K) ≠ 0) (h : IsLongRootSp2 L i)
    {c : StatedSp n K} (hc : c ∈ Subgroup.centralizer ({i} : Set (StatedSp n K))) :
    ∃ a ∈ L, ∃ b ∈ complGroup i, c = a * b := by
  obtain ⟨k, g, rfl, rfl⟩ := h
  obtain ⟨a, ha, b, hb, e⟩ := exists_mul_of_commute_longInv h2 k
    (Subgroup.mem_centralizer_singleton_iff.1 (mem_centralizer_conj.1 hc))
  refine ⟨g * a * g⁻¹, mem_map_conj_iff.2 (by rwa [show g⁻¹ * (g * a * g⁻¹) * g = a by group]),
    g * b * g⁻¹,
    mem_complGroup_conj.2 (by rwa [show g⁻¹ * (g * b * g⁻¹) * g = b by group]), ?_⟩
  calc c = g * (g⁻¹ * c * g) * g⁻¹ := by group
    _ = g * (a * b) * g⁻¹ := by rw [e]
    _ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group

theorem IsLongRootSp2.centralizer_eq (h2 : (2 : K) ≠ 0) (h : IsLongRootSp2 L i) :
    Subgroup.centralizer ({i} : Set (StatedSp n K)) = L ⊔ complGroup i := by
  apply le_antisymm
  · intro c hc
    obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul_of_mem_centralizer h2 hc
    exact Subgroup.mul_mem_sup ha hb
  · refine sup_le (h.isClassicalSL2 h2).le_centralizer fun b hb => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (h.commute_of_mem_complGroup h2 (h.isClassicalSL2 h2).mem hb).symm.eq

theorem IsLongRootSp2.nonempty_mulEquiv_centralizer (h2 : (2 : K) ≠ 0) (h : IsLongRootSp2 L i) :
    Nonempty ((SL(2, K) × complGroup i) ≃*
      Subgroup.centralizer ({i} : Set (StatedSp n K))) := by
  obtain ⟨k, g, rfl, rfl⟩ := h
  have h' : IsLongRootSp2 ((longRootSp2 K n k).map (MulAut.conj g).toMonoidHom)
      (g * longInv K n k * g⁻¹) := ⟨k, g, rfl, rfl⟩
  let ψ : SL(2, K) →* StatedSp n K := (MulAut.conj g).toMonoidHom.comp (longBlock K n k)
  have hψ : ∀ A, ψ A ∈ (longRootSp2 K n k).map (MulAut.conj g).toMonoidHom := fun A =>
    ⟨longBlock K n k A, ⟨A, rfl⟩, rfl⟩
  have hcomm : ∀ (A : SL(2, K)) (b : complGroup (g * longInv K n k * g⁻¹)),
      Commute (ψ A) ((complGroup (g * longInv K n k * g⁻¹)).subtype b) := fun A b =>
    h'.commute_of_mem_complGroup h2 (hψ A) b.2
  let Φ := MonoidHom.noncommCoprod ψ (complGroup (g * longInv K n k * g⁻¹)).subtype hcomm
  have hΦ' : ∀ (A : SL(2, K)) (b : complGroup (g * longInv K n k * g⁻¹)),
      Φ (A, b) = ψ A * (b : StatedSp n K) := fun A b => by
    simp [Φ, MonoidHom.noncommCoprod_apply]
  have hΦ : ∀ p, Φ p ∈ Subgroup.centralizer ({g * longInv K n k * g⁻¹} : Set (StatedSp n K)) := by
    rintro ⟨A, b⟩
    rw [hΦ']
    exact mul_mem ((h'.isClassicalSL2 h2).le_centralizer (hψ A))
      (by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (h'.commute_of_mem_complGroup h2 (h'.isClassicalSL2 h2).mem b.2).symm.eq)
  refine ⟨MulEquiv.ofBijective (Φ.codRestrict _ hΦ) ⟨?_, ?_⟩⟩
  · rintro ⟨A, b⟩ ⟨A', b'⟩ hAb
    have e : ψ A * (b : StatedSp n K) = ψ A' * (b' : StatedSp n K) := by
      have h0 : Φ (A, b) = Φ (A', b') := congrArg Subtype.val hAb
      rwa [hΦ', hΦ'] at h0
    have e' : (ψ A')⁻¹ * ψ A = (b' : StatedSp n K) * (b : StatedSp n K)⁻¹ := by
      calc (ψ A')⁻¹ * ψ A = (ψ A')⁻¹ * (ψ A * (b : StatedSp n K)) * (b : StatedSp n K)⁻¹ := by
            group
        _ = (ψ A')⁻¹ * (ψ A' * (b' : StatedSp n K)) * (b : StatedSp n K)⁻¹ := by rw [e]
        _ = (b' : StatedSp n K) * (b : StatedSp n K)⁻¹ := by group
    have hL : (ψ A')⁻¹ * ψ A ∈ (longRootSp2 K n k).map (MulAut.conj g).toMonoidHom :=
      mul_mem (inv_mem (hψ A')) (hψ A)
    have hR : (b' : StatedSp n K) * (b : StatedSp n K)⁻¹ ∈
        complGroup (g * longInv K n k * g⁻¹) := mul_mem b'.2 (inv_mem b.2)
    have h1 : (ψ A')⁻¹ * ψ A = 1 :=
      Subgroup.disjoint_def.1 (h'.disjoint_complGroup h2) hL (e' ▸ hR)
    have hA : A = A' := by
      have : ψ A = ψ A' := by
        calc ψ A = ψ A' * ((ψ A')⁻¹ * ψ A) := by group
          _ = ψ A' := by rw [h1, mul_one]
      exact longBlock_injective k ((MulAut.conj g).injective this)
    subst hA
    have hb : (b : StatedSp n K) = b' := mul_left_cancel e
    exact Prod.ext rfl (Subtype.ext hb)
  · rintro ⟨c, hc⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := h'.exists_mul_of_mem_centralizer h2 hc
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨A, rfl⟩ := ha'
    exact ⟨(A, ⟨b, hb⟩), Subtype.ext (hΦ' A ⟨b, hb⟩)⟩

end Product

end CFSG.ClassicalInvolution.Models.SymplecticPairs
