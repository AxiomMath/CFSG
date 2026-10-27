module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Lemma213

open CFSG CFSG.LocalCores Subgroup

section Coord

variable {K : Type*} [Group K] [Finite K]

theorem layerMul_injective (hZ : ∀ C : ComponentIndex K, center C.1 = ⊥) :
    Function.Injective (layerMul K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have h := layerMul_ker_le hx
  rw [Subgroup.mem_bot]
  funext C
  have hC : x C ∈ center C.1 := ((Subgroup.mem_pi Set.univ).1 h) C (Set.mem_univ C)
  rw [hZ C, Subgroup.mem_bot] at hC
  exact hC

@[expose] noncomputable def layerEquiv (hZ : ∀ C : ComponentIndex K, center C.1 = ⊥) :
    (∀ C : ComponentIndex K, C.1) ≃* layer K :=
  MulEquiv.ofBijective (layerMulOnto K)
    ⟨fun x y h => layerMul_injective hZ (congrArg Subtype.val h), layerMulOnto_surjective⟩

@[expose] noncomputable def coord (hZ : ∀ C : ComponentIndex K, center C.1 = ⊥)
    (C : ComponentIndex K) : layer K →* C.1 :=
  (Pi.evalMonoidHom (fun C : ComponentIndex K => C.1) C).comp (layerEquiv hZ).symm.toMonoidHom

variable (hZ : ∀ C : ComponentIndex K, center C.1 = ⊥)

@[expose] noncomputable def π (C : ComponentIndex K) (x : K) (hx : x ∈ layer K) : K :=
  ((coord hZ C ⟨x, hx⟩ : C.1) : K)

variable {hZ}

theorem coord_layerMulOnto (C : ComponentIndex K) (x : ∀ C : ComponentIndex K, C.1) :
    coord hZ C (layerMulOnto K x) = x C := by
  have h : layerEquiv hZ x = layerMulOnto K x := rfl
  have h2 : (layerEquiv hZ).symm (layerMulOnto K x) = x := by
    rw [← h]
    exact (layerEquiv hZ).symm_apply_apply x
  show ((layerEquiv hZ).symm (layerMulOnto K x)) C = x C
  rw [h2]

theorem π_layerMul (C : ComponentIndex K) (x : ∀ C : ComponentIndex K, C.1)
    (hx : layerMul K x ∈ layer K) : π hZ C (layerMul K x) hx = x C := by
  have := coord_layerMulOnto (hZ := hZ) C x
  exact congrArg Subtype.val this

theorem π_mem (C : ComponentIndex K) (x : K) (hx : x ∈ layer K) : π hZ C x hx ∈ C.1 :=
  (coord hZ C ⟨x, hx⟩).2

theorem π_mul (C : ComponentIndex K) {x y : K} (hx : x ∈ layer K) (hy : y ∈ layer K) :
    π hZ C (x * y) (mul_mem hx hy) = π hZ C x hx * π hZ C y hy := by
  have := map_mul (coord hZ C) ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem π_one (C : ComponentIndex K) : π hZ C 1 (one_mem _) = 1 := by
  have := map_one (coord hZ C)
  exact congrArg Subtype.val this

theorem π_inv (C : ComponentIndex K) {x : K} (hx : x ∈ layer K) :
    π hZ C x⁻¹ (inv_mem hx) = (π hZ C x hx)⁻¹ := by
  have := map_inv (coord hZ C) ⟨x, hx⟩
  exact congrArg Subtype.val this

theorem π_pow (C : ComponentIndex K) {x : K} (hx : x ∈ layer K) (n : ℕ) :
    π hZ C (x ^ n) (pow_mem hx n) = (π hZ C x hx) ^ n := by
  have := map_pow (coord hZ C) ⟨x, hx⟩ n
  exact congrArg Subtype.val this

theorem π_zpow (C : ComponentIndex K) {x : K} (hx : x ∈ layer K) (n : ℤ) :
    π hZ C (x ^ n) (zpow_mem hx n) = (π hZ C x hx) ^ n := by
  have := map_zpow (coord hZ C) ⟨x, hx⟩ n
  exact congrArg Subtype.val this

theorem π_of_mem (C : ComponentIndex K) {c : K} (hc : c ∈ C.1) :
    π hZ C c (component_le_layer C.2 hc) = c := by
  have h1 : layerMulOnto K (Pi.mulSingle C ⟨c, hc⟩) = ⟨c, component_le_layer C.2 hc⟩ :=
    Subtype.ext (layerMul_mulSingle C ⟨c, hc⟩)
  have := coord_layerMulOnto (hZ := hZ) C (Pi.mulSingle C ⟨c, hc⟩)
  rw [h1] at this
  have h2 := congrArg Subtype.val this
  rw [Pi.mulSingle_eq_same] at h2
  unfold π
  exact h2

theorem π_of_mem_of_ne {C C' : ComponentIndex K} (hne : C' ≠ C) {c : K} (hc : c ∈ C'.1) :
    π hZ C c (component_le_layer C'.2 hc) = 1 := by
  have h1 : layerMulOnto K (Pi.mulSingle C' ⟨c, hc⟩) = ⟨c, component_le_layer C'.2 hc⟩ :=
    Subtype.ext (layerMul_mulSingle C' ⟨c, hc⟩)
  have := coord_layerMulOnto (hZ := hZ) C (Pi.mulSingle C' ⟨c, hc⟩)
  rw [h1] at this
  have h2 := congrArg Subtype.val this
  rw [Pi.mulSingle_eq_of_ne (Ne.symm hne)] at h2
  unfold π
  exact h2

theorem π_eq_one_iff (C : ComponentIndex K) {x : K} (hx : x ∈ layer K) :
    π hZ C x hx = 1 ↔ x ∈ centralizer (C.1 : Set K) := by
  obtain ⟨y, hy⟩ := layerMulOnto_surjective (G := K) ⟨x, hx⟩
  have hxy : layerMul K y = x := congrArg Subtype.val hy
  subst hxy
  rw [π_layerMul C y hx, mem_centralizer_iff]
  constructor
  · intro h k hk
    have := (commute_layerMul_iff y C hk).2 (by rw [h]; exact Commute.one_right _)
    exact this.eq
  · intro h
    have hcomm : ∀ k ∈ C.1, Commute k (layerMul K y) := fun k hk => h k hk
    have hc : y C ∈ center C.1 := by
      rw [mem_center_iff]
      intro g
      apply Subtype.ext
      have := (commute_layerMul_iff y C g.2).1 (hcomm g g.2)
      exact this.eq
    rw [hZ C, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc

theorem eq_one_of_π_eq_one {x : K} (hx : x ∈ layer K)
    (h : ∀ C : ComponentIndex K, π hZ C x hx = 1) : x = 1 := by
  obtain ⟨y, hy⟩ := layerMulOnto_surjective (G := K) ⟨x, hx⟩
  have hxy : layerMul K y = x := congrArg Subtype.val hy
  subst hxy
  have hy1 : y = 1 := by
    funext C
    apply Subtype.ext
    have := h C
    rwa [π_layerMul C y hx] at this
  rw [hy1, map_one]

theorem π_ext {x y : K} (hx : x ∈ layer K) (hy : y ∈ layer K)
    (h : ∀ C : ComponentIndex K, π hZ C x hx = π hZ C y hy) : x = y := by
  have hxy : x * y⁻¹ ∈ layer K := mul_mem hx (inv_mem hy)
  have : x * y⁻¹ = 1 := by
    refine eq_one_of_π_eq_one (hZ := hZ) hxy fun C => ?_
    rw [π_mul C hx (inv_mem hy), π_inv C hy, h C]
    simp
  exact mul_inv_eq_one.1 this

theorem commute_of_π {x y : K} (hx : x ∈ layer K) (hy : y ∈ layer K)
    (h : ∀ C : ComponentIndex K, Commute (π hZ C x hx) (π hZ C y hy)) : Commute x y := by
  have h1 : x * y = y * x := by
    refine π_ext (hZ := hZ) (mul_mem hx hy) (mul_mem hy hx) fun C => ?_
    rw [π_mul C hx hy, π_mul C hy hx]
    exact (h C).eq
  exact h1

theorem exists_eq_π_mul (C : ComponentIndex K) {x : K} (hx : x ∈ layer K) :
    ∃ u : K, u ∈ layer K ∧ u ∈ centralizer (C.1 : Set K) ∧ x = π hZ C x hx * u := by
  have hc : π hZ C x hx ∈ layer K := component_le_layer C.2 (π_mem C x hx)
  have hu : (π hZ C x hx)⁻¹ * x ∈ layer K := mul_mem (inv_mem hc) hx
  refine ⟨(π hZ C x hx)⁻¹ * x, hu, ?_, by group⟩
  rw [← π_eq_one_iff (hZ := hZ) C hu, π_mul C (inv_mem hc) hx, π_inv C hc,
    π_of_mem C (π_mem C x hx)]
  simp

@[expose] noncomputable def cjComp (g : K) (C : ComponentIndex K) : ComponentIndex K :=
  ⟨C.1.map (MulAut.conj g).toMonoidHom, isComponent_map_mulEquiv (MulAut.conj g) C.2⟩

theorem mem_cjComp_of_mem (g : K) (C : ComponentIndex K) {c : K} (hc : c ∈ C.1) :
    g * c * g⁻¹ ∈ (cjComp g C).1 :=
  ⟨c, hc, rfl⟩

theorem mem_cjComp_iff (g : K) (C : ComponentIndex K) {c : K} :
    c ∈ (cjComp g C).1 ↔ g⁻¹ * c * g ∈ C.1 := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    show g⁻¹ * (g * d * g⁻¹) * g ∈ C.1
    rw [show g⁻¹ * (g * d * g⁻¹) * g = d by group]
    exact hd
  · intro h
    exact ⟨g⁻¹ * c * g, h, by show g * (g⁻¹ * c * g) * g⁻¹ = c; group⟩

theorem cjComp_one (C : ComponentIndex K) : cjComp 1 C = C := by
  apply Subtype.ext
  ext c
  rw [mem_cjComp_iff]
  simp

theorem cjComp_mul (g h : K) (C : ComponentIndex K) :
    cjComp (g * h) C = cjComp g (cjComp h C) := by
  apply Subtype.ext
  ext c
  rw [mem_cjComp_iff, mem_cjComp_iff, mem_cjComp_iff]
  simp [mul_assoc]

theorem cjComp_inj (g : K) {C C' : ComponentIndex K} (h : cjComp g C = cjComp g C') : C = C' := by
  apply Subtype.ext
  ext c
  constructor
  · intro hc
    have h1 : g * c * g⁻¹ ∈ (cjComp g C).1 := mem_cjComp_of_mem g C hc
    rw [h] at h1
    simpa [mem_cjComp_iff, mul_assoc] using h1
  · intro hc
    have h1 : g * c * g⁻¹ ∈ (cjComp g C').1 := mem_cjComp_of_mem g C' hc
    rw [← h] at h1
    simpa [mem_cjComp_iff, mul_assoc] using h1

theorem layer_normal (K : Type*) [Group K] [Finite K] : (layer K).Normal := by
  haveI : (layer K).Characteristic := LocalCores.layer_characteristic
  infer_instance

theorem conj_mem_layer (g : K) {x : K} (hx : x ∈ layer K) : g * x * g⁻¹ ∈ layer K :=
  (layer_normal K).conj_mem x hx g

theorem π_conj (g : K) (C : ComponentIndex K) {x : K} (hx : x ∈ layer K) :
    π hZ (cjComp g C) (g * x * g⁻¹) (conj_mem_layer g hx) = g * π hZ C x hx * g⁻¹ := by
  obtain ⟨u, hu, hCu, hxu⟩ := exists_eq_π_mul (hZ := hZ) C hx
  have hc : π hZ C x hx ∈ layer K := component_le_layer C.2 (π_mem C x hx)
  have hgc : g * π hZ C x hx * g⁻¹ ∈ (cjComp g C).1 := mem_cjComp_of_mem g C (π_mem C x hx)
  have hgu : g * u * g⁻¹ ∈ layer K := conj_mem_layer g hu
  have hgu' : g * u * g⁻¹ ∈ centralizer ((cjComp g C).1 : Set K) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    have := mem_centralizer_iff.1 hCu d hd
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * d * g⁻¹ * (g * u * g⁻¹) = g * (d * u) * g⁻¹ := by group
      _ = g * (u * d) * g⁻¹ := by rw [this]
      _ = g * u * g⁻¹ * (g * d * g⁻¹) := by group
  have hxe : g * x * g⁻¹ = (g * π hZ C x hx * g⁻¹) * (g * u * g⁻¹) := by
    conv_lhs => rw [hxu]
    group
  have hgcl : g * π hZ C x hx * g⁻¹ ∈ layer K := component_le_layer (cjComp g C).2 hgc
  have key : π hZ (cjComp g C) (g * x * g⁻¹) (conj_mem_layer g hx) =
      π hZ (cjComp g C) ((g * π hZ C x hx * g⁻¹) * (g * u * g⁻¹)) (mul_mem hgcl hgu) := by
    congr 1
  rw [key, π_mul _ hgcl hgu, π_of_mem _ hgc,
    (π_eq_one_iff (hZ := hZ) (cjComp g C) hgu).2 hgu', mul_one]

theorem conj_eq_π (C : ComponentIndex K) {x : K} (hx : x ∈ layer K) {c : K} (hc : c ∈ C.1) :
    x * c * x⁻¹ = π hZ C x hx * c * (π hZ C x hx)⁻¹ := by
  obtain ⟨u, hu, hCu, hxu⟩ := exists_eq_π_mul (hZ := hZ) C hx
  have hxu' : u * c = c * u := (mem_centralizer_iff.1 hCu c hc).symm
  conv_lhs => rw [hxu]
  calc π hZ C x hx * u * c * (π hZ C x hx * u)⁻¹
      = π hZ C x hx * (u * c) * u⁻¹ * (π hZ C x hx)⁻¹ := by group
    _ = π hZ C x hx * (c * u) * u⁻¹ * (π hZ C x hx)⁻¹ := by rw [hxu']
    _ = π hZ C x hx * c * (π hZ C x hx)⁻¹ := by group

theorem mem_centralizer_layer_of_forall (g : K)
    (h : ∀ C : ComponentIndex K, ∀ c ∈ C.1, g * c = c * g) :
    g ∈ centralizer (layer K : Set K) := by
  have hle : layer K ≤ centralizer ({g} : Set K) := by
    refine sSup_le fun C hC c hc => ?_
    rw [mem_centralizer_singleton_iff]
    exact (h ⟨C, hC⟩ c hc).symm
  exact mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (hle hx)

end Coord

end CFSG.LocalAnalysis.RankFourTheoremC.Lemma213
