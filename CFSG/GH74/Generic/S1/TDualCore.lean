module

public import CFSG.GH74.Generic.S1.RQ3Odd
public import CFSG.GH74.Generic.S1.TExoticLin
public import CFSG.GH74.Generic.S1.Front

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic Matrix

section Q8

theorem card_q8 : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem eq_one_of_odd_orderOf_q8 {g : QuaternionGroup 2} {d : ℕ} (hd : d ∣ orderOf g) (hodd : Odd d) :
    d = 1 := by
  have h1 : orderOf g ∣ 8 := by
    have := orderOf_dvd_natCard g
    rwa [card_q8] at this
  have h2 : d ∣ 8 := hd.trans h1
  have h3 : d ∈ Nat.divisors 8 := Nat.mem_divisors.2 ⟨h2, by norm_num⟩
  have : Nat.divisors 8 = {1, 2, 4, 8} := by decide
  rw [this] at h3
  simp only [Finset.mem_insert, Finset.mem_singleton] at h3
  rcases h3 with h | h | h | h
  · exact h
  all_goals (rw [h] at hodd; exact absurd hodd (by decide))


end Q8

section Layer

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] {S : Subgroup (GL (Fin 4) F)}

theorem image_block_le_layer {x : G} (D : LayerData x S) (blk : Subgroup ↥S) {y : G}
    {K' : Subgroup (CentralizerBar y)} (hfront' : S1Front G y K')
    (hgood : ⁅blk, blk⁆ = blk ∨ (OddGenerated blk ∧ ThreeModel ↥K'))
    (hy : ∀ s ∈ blk, D.ι s * y = y * D.ι s) :
    ∀ (s : ↥S) (hs : s ∈ blk), proj y ⟨D.ι s, mem_centralizer_singleton_iff.2 (hy s hs)⟩ ∈ K' := by
  intro s hs
  set P : Subgroup G := blk.map D.ι with hP
  have hPy : P ≤ centralizer ({y} : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    exact mem_centralizer_singleton_iff.2 (hy t ht)
  set Pc : Subgroup ↥(centralizer ({y} : Set G)) := P.subgroupOf (centralizer ({y} : Set G)) with hPc
  have hgoodP : GoodSub (ThreeModel ↥K') (Pc.map (proj y)) := by
    rcases hgood with hperf | ⟨hodd, hT⟩
    · left
      have hPperf : ⁅P, P⁆ = P := by
        rw [hP, ← Subgroup.map_commutator, hperf]
      have hPcperf : ⁅Pc, Pc⁆ = Pc := by
        apply Subgroup.map_injective (centralizer ({y} : Set G)).subtype_injective
        rw [Subgroup.map_commutator, hPc, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPy, hPperf]
      rw [← Subgroup.map_commutator, hPcperf]
    · right
      refine ⟨?_, hT⟩
      have hPodd : OddGenerated P := oddGenerated_map D.ι hodd
      have hPcodd : OddGenerated Pc := by
        refine oddGenerated_comap (centralizer ({y} : Set G)).subtype_injective hPodd ?_
        rw [Subgroup.range_subtype]
        exact hPy
      exact oddGenerated_map (proj y) hPcodd
  have hle := hfront'.good_le _ hgoodP
  have hmemP : D.ι s ∈ P := ⟨s, hs, rfl⟩
  have hmemPc : (⟨D.ι s, mem_centralizer_singleton_iff.2 (hy s hs)⟩ : ↥(centralizer ({y} : Set G))) ∈ Pc :=
    Subgroup.mem_subgroupOf.2 hmemP
  exact hle (Subgroup.mem_map_of_mem _ hmemPc)


theorem exists_fixed_q8 {x : G} (D : LayerData x S) (blk : Subgroup ↥S) {y : G}
    {K' : Subgroup (CentralizerBar y)} [K'.Normal] (hfront' : S1Front G y K')
    (hgood : ⁅blk, blk⁆ = blk ∨ (OddGenerated blk ∧ ThreeModel ↥K'))
    (q8 : QuaternionGroup 2 →* ↥S) (hq8 : Function.Injective q8) (hq8blk : ∀ g, q8 g ∈ blk)
    (hy : ∀ s ∈ blk, D.ι s * y = y * D.ι s)
    {v : G} (hv : v ∈ centralizer ({y} : Set G)) (hvc : ∀ s ∈ blk, D.ι s * v = v * D.ι s)
    (e' : ↥K' ≃* ↥S) :
    ∃ Φ : QuaternionGroup 2 →* ↥S, Function.Injective Φ ∧
      ∀ g, MulAut.congr e' (MulAut.conjNormal (barOf hv) : MulAut ↥K') (Φ g) = Φ g := by
  let ιs : QuaternionGroup 2 →* G := D.ι.comp q8
  have hιs_inj : Function.Injective ιs := D.ι_injective.comp hq8
  have hmem : ∀ g, ιs g ∈ centralizer ({y} : Set G) := fun g =>
    mem_centralizer_singleton_iff.2 (hy _ (hq8blk g))
  let ψ : QuaternionGroup 2 →* ↥(centralizer ({y} : Set G)) := ιs.codRestrict _ hmem
  have hK : ∀ g, proj y (ψ g) ∈ K' := fun g =>
    image_block_le_layer D blk hfront' hgood hy (q8 g) (hq8blk g)
  let φ' : QuaternionGroup 2 →* ↥K' := ((proj y).comp ψ).codRestrict K' hK
  refine ⟨e'.toMonoidHom.comp φ', ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : φ' g = 1 := by
      apply e'.injective
      exact hg.trans (map_one e').symm
    have h2 : proj y (ψ g) = 1 := congrArg Subtype.val h1
    have h3 := proj_odd y (ψ g) h2
    have h4 : orderOf (ψ g) ∣ orderOf g := orderOf_map_dvd ψ g
    have h5 : orderOf (ψ g) = 1 := eq_one_of_odd_orderOf_q8 h4 h3
    have h6 : ψ g = 1 := orderOf_eq_one_iff.1 h5
    have h7 : ιs g = 1 := congrArg Subtype.val h6
    exact hιs_inj (h7.trans (map_one ιs).symm)
  · intro g
    have hcomm : ψ g * (⟨v, hv⟩ : ↥(centralizer ({y} : Set G))) = ⟨v, hv⟩ * ψ g :=
      Subtype.ext (hvc _ (hq8blk g))
    have hb : barOf hv * proj y (ψ g) = proj y (ψ g) * barOf hv := by
      have := congrArg (proj y) hcomm
      rw [map_mul, map_mul] at this
      exact this.symm
    have key : (MulAut.conjNormal (barOf hv) : MulAut ↥K') (φ' g) = φ' g := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      change barOf hv * proj y (ψ g) * (barOf hv)⁻¹ = proj y (ψ g)
      rw [hb]
      group
    show MulAut.congr e' (MulAut.conjNormal (barOf hv) : MulAut ↥K') (e' (φ' g)) = e' (φ' g)
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, key]


end Layer

section Linear

variable {F : Type} [Field F]

theorem fixed_isometry {g k : GL (Fin 4) F}
    (h : k = g * Matrix.GeneralLinearGroup.inverseTranspose k * g⁻¹) :
    (k : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
      (k : Matrix (Fin 4) (Fin 4) F)ᵀ = (g : Matrix (Fin 4) (Fin 4) F) := by
  have h1 : k * g = g * Matrix.GeneralLinearGroup.inverseTranspose k := by
    have := congrArg (fun m => m * g) h
    simpa [mul_assoc] using this
  have h2 := congrArg (fun m : GL (Fin 4) F => (m : Matrix (Fin 4) (Fin 4) F)) h1
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_inverseTranspose] at h2
  have hkk : ((k⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (k : Matrix (Fin 4) (Fin 4) F) = 1 :=
    Units.inv_mul k
  calc (k : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
        (k : Matrix (Fin 4) (Fin 4) F)ᵀ
      = (g : Matrix (Fin 4) (Fin 4) F) * ((k⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ *
        (k : Matrix (Fin 4) (Fin 4) F)ᵀ := by rw [h2]
    _ = (g : Matrix (Fin 4) (Fin 4) F) * ((k : Matrix (Fin 4) (Fin 4) F) *
        ((k⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))ᵀ := by
        rw [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (g : Matrix (Fin 4) (Fin 4) F) := by
        rw [Units.mul_inv, Matrix.transpose_one, Matrix.mul_one]

open QuaternionGroup in
theorem q8_rel1 : (a 1 : QuaternionGroup 2) * a 1 = a 2 := by decide
open QuaternionGroup in
theorem q8_rel2 : (xa 0 : QuaternionGroup 2) * xa 0 = a 2 := by decide
open QuaternionGroup in
theorem q8_rel3 : (a 2 : QuaternionGroup 2) * a 2 = 1 := by decide
open QuaternionGroup in
theorem q8_rel4 : (xa 0 : QuaternionGroup 2) * a 1 = a 2 * (a 1 * xa 0) := by decide
open QuaternionGroup in
theorem q8_ne : (a 2 : QuaternionGroup 2) ≠ 1 := by decide

theorem mat_mul_coe {S : Subgroup (GL (Fin 4) F)} (s t : ↥S) :
    (((s * t : ↥S) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  rw [Subgroup.coe_mul, Units.val_mul]

theorem no_exotic_of_fixed_q8_lin (h2 : (2 : F) ≠ 0) (β : MulAut ↥(StatedSL 4 F))
    (Φ : QuaternionGroup 2 →* ↥(StatedSL 4 F)) (hΦ : Function.Injective Φ)
    (hfix : ∀ g, β (Φ g) = Φ g) : ¬ IsExoticLin (StatedSL 4 F) β := by
  rintro ⟨g, hgs, hgd, hβ⟩
  have hiso : ∀ s : QuaternionGroup 2,
      ((Φ s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
        ((Φ s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = (g : Matrix (Fin 4) (Fin 4) F) := by
    intro s
    apply fixed_isometry
    have := hβ (Φ s)
    rw [hfix s] at this
    exact this
  set I : Matrix (Fin 4) (Fin 4) F := ((Φ (QuaternionGroup.a 1) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hI
  set J : Matrix (Fin 4) (Fin 4) F := ((Φ (QuaternionGroup.xa 0) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hJ
  set Z : Matrix (Fin 4) (Fin 4) F := ((Φ (QuaternionGroup.a 2) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hZ
  have cm : ∀ s t : ↥(StatedSL 4 F), s = t → ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := fun s t h => by rw [h]
  have rII : I * I = Z := by
    have h := cm (Φ (QuaternionGroup.a 1) * Φ (QuaternionGroup.a 1)) (Φ (QuaternionGroup.a 2))
      (by rw [← map_mul, q8_rel1])
    rw [mat_mul_coe] at h
    exact h
  have rJJ : J * J = Z := by
    have h := cm (Φ (QuaternionGroup.xa 0) * Φ (QuaternionGroup.xa 0)) (Φ (QuaternionGroup.a 2))
      (by rw [← map_mul, q8_rel2])
    rw [mat_mul_coe] at h
    exact h
  have rZZ : Z * Z = 1 := by
    have h := cm (Φ (QuaternionGroup.a 2) * Φ (QuaternionGroup.a 2)) 1
      (by rw [← map_mul, q8_rel3, map_one])
    rw [mat_mul_coe] at h
    exact h
  have rJI : J * I = Z * (I * J) := by
    have h := cm (Φ (QuaternionGroup.xa 0) * Φ (QuaternionGroup.a 1))
      (Φ (QuaternionGroup.a 2) * (Φ (QuaternionGroup.a 1) * Φ (QuaternionGroup.xa 0)))
      (by rw [← map_mul, ← map_mul, ← map_mul, q8_rel4])
    rw [mat_mul_coe, mat_mul_coe, mat_mul_coe] at h
    exact h
  have rZ1 : Z ≠ 1 := by
    intro h
    apply q8_ne
    apply hΦ
    rw [map_one]
    apply Subtype.ext
    apply Units.ext
    exact h
  have hZI : Z * I = I * Z := by rw [← rII, Matrix.mul_assoc]
  have hZJ : Z * J = J * Z := by rw [← rJJ, Matrix.mul_assoc]
  have hiI : I * (g : Matrix (Fin 4) (Fin 4) F) * Iᵀ = (g : Matrix (Fin 4) (Fin 4) F) := hiso _
  have hiJ : J * (g : Matrix (Fin 4) (Fin 4) F) * Jᵀ = (g : Matrix (Fin 4) (Fin 4) F) := hiso _
  refine no_q8_isometry (G := (g : Matrix (Fin 4) (Fin 4) F)) (a := Iᵀ) (b := Jᵀ) (z := Zᵀ) h2 hgs hgd
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa using hiI
  · simpa using hiJ
  · rw [← Matrix.transpose_mul, rII]
  · rw [← Matrix.transpose_mul, rJJ]
  · rw [← Matrix.transpose_mul, rZZ, Matrix.transpose_one]
  · intro h
    apply rZ1
    have := congrArg Matrix.transpose h
    simpa using this
  ·
    have hc : Z * (I * J) = (I * J) * Z := by
      rw [← Matrix.mul_assoc, hZI, Matrix.mul_assoc, hZJ, ← Matrix.mul_assoc]
    calc Iᵀ * Jᵀ = (J * I)ᵀ := by rw [Matrix.transpose_mul]
      _ = (Z * (I * J))ᵀ := by rw [rJI]
      _ = ((I * J) * Z)ᵀ := by rw [hc]
      _ = Zᵀ * (Jᵀ * Iᵀ) := by rw [Matrix.transpose_mul, Matrix.transpose_mul]


end Linear

end CFSG.GH74.Generic.S1
