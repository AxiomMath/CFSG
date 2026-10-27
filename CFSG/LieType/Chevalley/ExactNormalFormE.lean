module

public import CFSG.LieType.Chevalley.IntrinsicDiagramPermutation
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.LieType.Chevalley.GraphFixedBruhatEquivariance
public import CFSG.LieType.Chevalley.DiagramGeneratorConjugation

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def exactE (τ : Tag) : ℕ :=
  match τ with
  | .E6 => 2
  | .G2 | .F4 | .D4 | .E7 | .E8 => 1

@[expose] def exactPerm (τ : Tag) (ε : ℕ) : Equiv.Perm (Fin τ.rank) :=
  match τ with
  | .E6 => (TwistTag.E6.perm : Equiv.Perm (Fin Tag.E6.rank)) ^ ε
  | .G2 | .F4 | .D4 | .E7 | .E8 => 1

@[expose] def exactQ (τ : Tag) (K : Type) [Field K] (ε : ℕ) : ModGL τ K :=
  match τ with
  | .E6 => (diagramMap .E6 K : ModGL Tag.E6 K) ^ ε
  | .G2 | .F4 | .D4 | .E7 | .E8 => 1

section Diagram

variable (t : TwistTag) (K : Type) [Field K]

theorem conj_diagramMap_eq_twistHom :
    (MulAut.conj (diagramMap t K)).toMonoidHom = twistHom t K (RingHom.id K) := by
  refine MonoidHom.ext fun g => ?_
  rw [twistHom_apply, show Units.map (entrywiseHom (RingHom.id K)) g = g from
    Units.ext (entrywise_id _)]
  rfl

theorem diagramMap_mul_xUnit_mul_inv
    (i : Fin t.tag.rank) (c : K) :
    diagramMap t K * xUnit t.tag K i c * (diagramMap t K)⁻¹ = xUnit t.tag K (t.perm i) c :=
  (congrArg (fun φ : ModGL t.tag K →* ModGL t.tag K => φ (xUnit t.tag K i c))
    (conj_diagramMap_eq_twistHom t K)).trans
      ((diagram_generator_conjugation t K (RingEquiv.refl K)).1 i c)

theorem diagramMap_mul_yUnit_mul_inv
    (i : Fin t.tag.rank) (c : K) :
    diagramMap t K * yUnit t.tag K i c * (diagramMap t K)⁻¹ = yUnit t.tag K (t.perm i) c :=
  (congrArg (fun φ : ModGL t.tag K →* ModGL t.tag K => φ (yUnit t.tag K i c))
    (conj_diagramMap_eq_twistHom t K)).trans
      ((diagram_generator_conjugation t K (RingEquiv.refl K)).2.1 i c)

theorem diagramMap_pow_mul_xUnit_mul_inv
    (n : ℕ) (i : Fin t.tag.rank) (c : K) :
    diagramMap t K ^ n * xUnit t.tag K i c * (diagramMap t K ^ n)⁻¹ =
      xUnit t.tag K ((t.perm ^ n) i) c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' (diagramMap t K), pow_succ' t.perm, Equiv.Perm.mul_apply,
      ← diagramMap_mul_xUnit_mul_inv, ← ih, mul_inv_rev]
    simp only [mul_assoc]

theorem diagramMap_pow_mul_yUnit_mul_inv
    (n : ℕ) (i : Fin t.tag.rank) (c : K) :
    diagramMap t K ^ n * yUnit t.tag K i c * (diagramMap t K ^ n)⁻¹ =
      yUnit t.tag K ((t.perm ^ n) i) c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' (diagramMap t K), pow_succ' t.perm, Equiv.Perm.mul_apply,
      ← diagramMap_mul_yUnit_mul_inv, ← ih, mul_inv_rev]
    simp only [mul_assoc]

theorem map_conj_diagramMap
    {H : Subgroup (ModGL t.tag K)}
    (hH : H = adjointGroup t.tag K ∨ H = posUnipotent t.tag K ∨ H = negUnipotent t.tag K) :
    H.map (MulAut.conj (diagramMap t K)).toMonoidHom = H := by
  have h := diagram_field_Bruhat_equivariance t K (RingEquiv.refl K)
  rw [conj_diagramMap_eq_twistHom]
  rcases hH with rfl | rfl | rfl
  · exact map_twistHom_adjointGroup t K (RingHom.id K) Function.surjective_id
  · exact h.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.1

end Diagram

section MulAut

variable {G : Type*} [Group G]

theorem map_toMonoidHom_mul_mulAut (f g : MulAut G) (H : Subgroup G) :
    H.map (f * g).toMonoidHom = (H.map g.toMonoidHom).map f.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem map_inv_toMonoidHom_of_map_eq {f : MulAut G} {H H' : Subgroup G}
    (h : H.map f.toMonoidHom = H') : H'.map f⁻¹.toMonoidHom = H := by
  rw [← h, ← map_toMonoidHom_mul_mulAut, inv_mul_cancel]
  exact map_mulAut_one H

theorem map_conj_pow_of_map_conj (g : G) {H : Subgroup G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) (n : ℕ) :
    H.map (MulAut.conj (g ^ n)).toMonoidHom = H := by
  induction n with
  | zero =>
    rw [pow_zero, map_one]
    exact map_mulAut_one H
  | succ n ih => rw [pow_succ', map_mul, map_toMonoidHom_mul_mulAut, ih, h]

end MulAut

section General

variable {τ : Tag} {K : Type} [Field K]

theorem exactQ_mul_xUnit_mul_inv
    (ε : ℕ) (i : Fin τ.rank) (c : K) :
    exactQ τ K ε * xUnit τ K i c * (exactQ τ K ε)⁻¹ = xUnit τ K (exactPerm τ ε i) c := by
  cases τ
  case E6 => exact diagramMap_pow_mul_xUnit_mul_inv .E6 K ε i c
  all_goals
    change (1 : ModGL _ K) * xUnit _ K i c * 1⁻¹ = xUnit _ K i c
    rw [one_mul, inv_one, mul_one]

theorem exactQ_mul_yUnit_mul_inv
    (ε : ℕ) (i : Fin τ.rank) (c : K) :
    exactQ τ K ε * yUnit τ K i c * (exactQ τ K ε)⁻¹ = yUnit τ K (exactPerm τ ε i) c := by
  cases τ
  case E6 => exact diagramMap_pow_mul_yUnit_mul_inv .E6 K ε i c
  all_goals
    change (1 : ModGL _ K) * yUnit _ K i c * 1⁻¹ = yUnit _ K i c
    rw [one_mul, inv_one, mul_one]

theorem map_conj_exactQ
    {H : Subgroup (ModGL τ K)}
    (hH : H = adjointGroup τ K ∨ H = posUnipotent τ K ∨ H = negUnipotent τ K) (ε : ℕ) :
    H.map (MulAut.conj (exactQ τ K ε)).toMonoidHom = H := by
  cases τ
  case E6 => exact map_conj_pow_of_map_conj (diagramMap .E6 K) (map_conj_diagramMap .E6 K hH) ε
  all_goals
    change H.map (MulAut.conj (1 : ModGL _ K)).toMonoidHom = H
    rw [map_one]
    exact map_mulAut_one H

theorem exactEntrywiseAut_left_inv (σ : K ≃+* K) (g : ModGL τ K) :
    Units.map (entrywiseHom σ.symm.toRingHom) (Units.map (entrywiseHom σ.toRingHom) g) = g := by
  ext1
  simp only [Units.coe_map]
  refine (entrywise_entrywise _ _ _).trans ?_
  rw [RingEquiv.symm_toRingHom_comp_toRingHom]
  exact entrywise_id _

theorem exactEntrywiseAut_right_inv (σ : K ≃+* K) (g : ModGL τ K) :
    Units.map (entrywiseHom σ.toRingHom) (Units.map (entrywiseHom σ.symm.toRingHom) g) = g := by
  ext1
  simp only [Units.coe_map]
  refine (entrywise_entrywise _ _ _).trans ?_
  rw [RingEquiv.toRingHom_comp_symm_toRingHom]
  exact entrywise_id _

variable (τ) in
@[expose] def exactEntrywiseAut (σ : K ≃+* K) : MulAut (ModGL τ K) where
  toFun := Units.map (entrywiseHom σ.toRingHom)
  invFun := Units.map (entrywiseHom σ.symm.toRingHom)
  left_inv := exactEntrywiseAut_left_inv σ
  right_inv := exactEntrywiseAut_right_inv σ
  map_mul' := map_mul _

theorem exactEntrywiseAut_apply (σ : K ≃+* K) (g : ModGL τ K) :
    exactEntrywiseAut τ σ g = Units.map (entrywiseHom σ.toRingHom) g :=
  rfl

theorem units_map_entrywiseHom_xUnit
    (σ : K →+* K) (i : Fin τ.rank) (c : K) :
    Units.map (entrywiseHom σ) (xUnit τ K i c) = xUnit τ K i (σ c) :=
  Units.ext (by
    rw [Units.coe_map, coe_xUnit, coe_xUnit]
    exact entrywise_xOp σ i c)

theorem units_map_entrywiseHom_yUnit
    (σ : K →+* K) (i : Fin τ.rank) (c : K) :
    Units.map (entrywiseHom σ) (yUnit τ K i c) = yUnit τ K i (σ c) :=
  Units.ext (by
    rw [Units.coe_map, coe_yUnit, coe_yUnit]
    exact entrywise_yOp σ i c)

theorem map_exactEntrywiseAut
    (σ : K ≃+* K) {H : Subgroup (ModGL τ K)}
    (hH : H = adjointGroup τ K ∨ H = posUnipotent τ K ∨ H = negUnipotent τ K) :
    H.map (exactEntrywiseAut τ σ).toMonoidHom = H := by
  have h := (chevalley_root_character_and_field_conjugation τ K).2.2.2.2.1 σ
  have e : (exactEntrywiseAut τ σ).toMonoidHom = Units.map (entrywiseHom σ.toRingHom) :=
    MonoidHom.ext fun _ => rfl
  rw [e]
  rcases hH with rfl | rfl | rfl
  exacts [h.1, h.2.1, h.2.2]

variable (τ K) in
@[expose] def exactNormalAutGL (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) :
    MulAut (ModGL τ K) :=
  MulAut.conj (rootDiagUnit τ a) * MulAut.conj (exactQ τ K ε) * exactEntrywiseAut τ σ

theorem exactNormalAutGL_apply (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) (g : ModGL τ K) :
    exactNormalAutGL τ K a σ ε g = rootDiagUnit τ a * exactQ τ K ε *
      Units.map (entrywiseHom σ.toRingHom) g * (exactQ τ K ε)⁻¹ * (rootDiagUnit τ a)⁻¹ := by
  simp only [exactNormalAutGL, MulAut.mul_apply, MulAut.conj_apply, exactEntrywiseAut_apply,
    mul_assoc]

theorem exactNormalAutGL_xUnit
    (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) (i : Fin τ.rank)
    (c : K) :
    exactNormalAutGL τ K a σ ε (xUnit τ K i c) =
      xUnit τ K (exactPerm τ ε i) ((a (exactPerm τ ε i) : K) * σ c) := by
  rw [exactNormalAutGL_apply, units_map_entrywiseHom_xUnit,
    ← (root_diagonal_conjugation τ K a).1, ← exactQ_mul_xUnit_mul_inv ε i]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, mul_assoc]

theorem exactNormalAutGL_yUnit
    (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) (i : Fin τ.rank)
    (c : K) :
    exactNormalAutGL τ K a σ ε (yUnit τ K i c) =
      yUnit τ K (exactPerm τ ε i) ((((a (exactPerm τ ε i))⁻¹ : Kˣ) : K) * σ c) := by
  rw [exactNormalAutGL_apply, units_map_entrywiseHom_yUnit,
    ← (root_diagonal_conjugation τ K a).2.1, ← exactQ_mul_yUnit_mul_inv ε i]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, mul_assoc]

theorem map_exactNormalAutGL
    (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ)
    {H : Subgroup (ModGL τ K)}
    (hH : H = adjointGroup τ K ∨ H = posUnipotent τ K ∨ H = negUnipotent τ K) :
    H.map (exactNormalAutGL τ K a σ ε).toMonoidHom = H := by
  have hd := (chevalley_root_character_and_field_conjugation τ K).2.2.2.1 a
  have hda : H.map (MulAut.conj (rootDiagUnit τ a)).toMonoidHom = H := by
    rcases hH with rfl | rfl | rfl
    exacts [hd.1, hd.2.1, hd.2.2]
  rw [exactNormalAutGL, map_toMonoidHom_mul_mulAut, map_toMonoidHom_mul_mulAut,
    map_exactEntrywiseAut σ hH, map_conj_exactQ hH, hda]

variable (τ K) in
@[expose] def exactNormalAut
    (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) :
    MulAut (adjointGroup τ K) :=
  mulAutRestrict (adjointGroup τ K) (exactNormalAutGL τ K a σ ε)
    (map_exactNormalAutGL a σ ε (Or.inl rfl))

theorem coe_exactNormalAut
    (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) (h : adjointGroup τ K) :
    (exactNormalAut τ K a σ ε h : ModGL τ K) = rootDiagUnit τ a * exactQ τ K ε *
      Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * (exactQ τ K ε)⁻¹ *
        (rootDiagUnit τ a)⁻¹ :=
  exactNormalAutGL_apply a σ ε h

theorem exactNormalAut_mem
    (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) :
    exactNormalAut τ K a σ ε ∈ unipotentPairAut τ K :=
  ⟨map_subgroupOf_mulAutRestrict _ (map_exactNormalAutGL a σ ε (Or.inr (Or.inl rfl))),
    map_subgroupOf_mulAutRestrict _ (map_exactNormalAutGL a σ ε (Or.inr (Or.inr rfl)))⟩

theorem exactNormalAut_adjX
    (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) (i : Fin τ.rank)
    (c : K) :
    exactNormalAut τ K a σ ε (adjX τ K i c) =
      adjX τ K (exactPerm τ ε i) ((a (exactPerm τ ε i) : K) * σ c) :=
  Subtype.ext (exactNormalAutGL_xUnit a σ ε i c)

theorem exactNormalAut_adjY
    (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) (i : Fin τ.rank)
    (c : K) :
    exactNormalAut τ K a σ ε (adjY τ K i c) =
      adjY τ K (exactPerm τ ε i) ((((a (exactPerm τ ε i))⁻¹ : Kˣ) : K) * σ c) :=
  Subtype.ext (exactNormalAutGL_yUnit a σ ε i c)

theorem map_simplePosSubgroup_of_adjX
    {β : MulAut (adjointGroup τ K)} {i j : Fin τ.rank}
    {f : K → K} (hf : Function.Surjective f) (h : ∀ c, β (adjX τ K i c) = adjX τ K j (f c)) :
    (simplePosSubgroup τ K i).map β.toMonoidHom = simplePosSubgroup τ K j := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc⟩ := mem_simplePosSubgroup.1 hy
    rw [show y = adjX τ K i c from Subtype.ext hc]
    exact mem_simplePosSubgroup.2 ⟨f c, congrArg Subtype.val (h c)⟩
  · intro hx
    obtain ⟨d, hd⟩ := mem_simplePosSubgroup.1 hx
    obtain ⟨c, rfl⟩ := hf d
    exact ⟨adjX τ K i c, mem_simplePosSubgroup.2 ⟨c, rfl⟩, (h c).trans (Subtype.ext hd.symm)⟩

theorem map_simpleNegSubgroup_of_adjY
    {β : MulAut (adjointGroup τ K)} {i j : Fin τ.rank}
    {f : K → K} (hf : Function.Surjective f) (h : ∀ c, β (adjY τ K i c) = adjY τ K j (f c)) :
    (simpleNegSubgroup τ K i).map β.toMonoidHom = simpleNegSubgroup τ K j := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc⟩ := mem_simpleNegSubgroup.1 hy
    rw [show y = adjY τ K i c from Subtype.ext hc]
    exact mem_simpleNegSubgroup.2 ⟨f c, congrArg Subtype.val (h c)⟩
  · intro hx
    obtain ⟨d, hd⟩ := mem_simpleNegSubgroup.1 hx
    obtain ⟨c, rfl⟩ := hf d
    exact ⟨adjY τ K i c, mem_simpleNegSubgroup.2 ⟨c, rfl⟩, (h c).trans (Subtype.ext hd.symm)⟩

theorem map_simplePosSubgroup_exactNormalAut
    (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ)
    (i : Fin τ.rank) :
    (simplePosSubgroup τ K i).map (exactNormalAut τ K a σ ε).toMonoidHom =
      simplePosSubgroup τ K (exactPerm τ ε i) :=
  map_simplePosSubgroup_of_adjX (f := fun c => (a (exactPerm τ ε i) : K) * σ c)
    (fun d => ⟨σ.symm ((((a (exactPerm τ ε i))⁻¹ : Kˣ) : K) * d), by simp⟩)
    (exactNormalAut_adjX a σ ε i)

theorem map_simpleNegSubgroup_exactNormalAut
    (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ)
    (i : Fin τ.rank) :
    (simpleNegSubgroup τ K i).map (exactNormalAut τ K a σ ε).toMonoidHom =
      simpleNegSubgroup τ K (exactPerm τ ε i) :=
  map_simpleNegSubgroup_of_adjY (f := fun c => (((a (exactPerm τ ε i))⁻¹ : Kˣ) : K) * σ c)
    (fun d => ⟨σ.symm ((a (exactPerm τ ε i) : K) * d), by simp⟩)
    (exactNormalAut_adjY a σ ε i)

theorem mulAut_ext_adjX_adjY
    {α β : MulAut (adjointGroup τ K)}
    (hx : ∀ i c, α (adjX τ K i c) = β (adjX τ K i c))
    (hy : ∀ i c, α (adjY τ K i c) = β (adjY τ K i c)) : α = β := by
  have h : β⁻¹ * α = 1 :=
    mulAut_eq_one_of_fix (fun i c => by rw [MulAut.mul_apply, hx, MulAut.inv_apply_self])
      fun i c => by rw [MulAut.mul_apply, hy, MulAut.inv_apply_self]
  exact (inv_mul_eq_one.1 h).symm

theorem exactPerm_E6_injective :
    ∀ ε ε' : Fin 2, exactPerm .E6 ε ⟨0, by decide⟩ = exactPerm .E6 ε' ⟨0, by decide⟩ →
      ε = ε' := by
  decide

theorem exactPerm_injective (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {ε ε' : Fin (exactE τ)}
    (h : exactPerm τ ε = exactPerm τ ε') : ε = ε' := by
  rcases hτ with rfl | rfl | rfl
  · exact exactPerm_E6_injective ε ε' (congrArg (fun π => π ⟨0, by decide⟩) h)
  · exact Subsingleton.elim (α := Fin 1) ε ε'
  · exact Subsingleton.elim (α := Fin 1) ε ε'

theorem exists_exactPerm_map_simple
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {β : MulAut (adjointGroup τ K)} (hβ : β ∈ unipotentPairAut τ K) :
    ∃ ε : Fin (exactE τ), ∀ i,
      (simplePosSubgroup τ K i).map β.toMonoidHom = simplePosSubgroup τ K (exactPerm τ ε i) ∧
      (simpleNegSubgroup τ K i).map β.toMonoidHom = simpleNegSubgroup τ K (exactPerm τ ε i) := by
  obtain ⟨π, hπ⟩ := exists_perm_map_simple hβ
  obtain ⟨-, h6, h7, h8⟩ := exceptional_E_intrinsic_diagram_permutation K
  rcases hτ with rfl | rfl | rfl
  · rcases h6 β hβ π hπ with rfl | rfl
    · refine ⟨⟨0, by decide⟩, fun i => ?_⟩
      rw [show exactPerm Tag.E6 ((⟨0, by decide⟩ : Fin (exactE Tag.E6)) : ℕ) = 1 from
        pow_zero _]
      exact hπ i
    · refine ⟨⟨1, by decide⟩, fun i => ?_⟩
      rw [show exactPerm Tag.E6 ((⟨1, by decide⟩ : Fin (exactE Tag.E6)) : ℕ) =
        TwistTag.E6.perm from pow_one _]
      exact hπ i
  · obtain rfl := h7 β hβ π hπ
    exact ⟨⟨0, by decide⟩, hπ⟩
  · obtain rfl := h8 β hβ π hπ
    exact ⟨⟨0, by decide⟩, hπ⟩

theorem exists_exactNormalAut_eq
    [Finite K] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {β : MulAut (adjointGroup τ K)} (hβ : β ∈ unipotentPairAut τ K) :
    ∃ (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (ε : Fin (exactE τ)),
      β = exactNormalAut τ K a σ ε := by
  obtain ⟨ε, hε⟩ := exists_exactPerm_map_simple hτ hβ
  have hγx : ∀ i c, exactNormalAut τ K 1 (RingEquiv.refl K) ε (adjX τ K i c) =
      adjX τ K (exactPerm τ ε i) c := fun i c => by
    rw [exactNormalAut_adjX, Pi.one_apply, Units.val_one, one_mul, RingEquiv.refl_apply]
  have hγy : ∀ i c, exactNormalAut τ K 1 (RingEquiv.refl K) ε (adjY τ K i c) =
      adjY τ K (exactPerm τ ε i) c := fun i c => by
    rw [exactNormalAut_adjY, Pi.one_apply, inv_one, Units.val_one, one_mul, RingEquiv.refl_apply]
  have hζ : β * (exactNormalAut τ K 1 (RingEquiv.refl K) ε)⁻¹ ∈ rootPairAut τ K := by
    refine mem_rootPairAut.2 fun i => ?_
    obtain ⟨j, rfl⟩ := (exactPerm τ ε).surjective i
    refine ⟨?_, ?_⟩
    · rw [map_toMonoidHom_mul_mulAut, map_inv_toMonoidHom_of_map_eq
        (map_simplePosSubgroup_exactNormalAut 1 (RingEquiv.refl K) ε j), (hε j).1]
    · rw [map_toMonoidHom_mul_mulAut, map_inv_toMonoidHom_of_map_eq
        (map_simpleNegSubgroup_exactNormalAut 1 (RingEquiv.refl K) ε j), (hε j).2]
  obtain ⟨p, hp, -⟩ := (ordinary_Chevalley_root_pair_common_field_parameter τ K).1 _ hζ
  refine ⟨p.1, p.2, ε, mulAut_ext_adjX_adjY (fun i c => ?_) fun i c => ?_⟩
  · rw [← inv_mul_cancel_right β (exactNormalAut τ K 1 (RingEquiv.refl K) ε), MulAut.mul_apply,
      hγx, (hp _).1, exactNormalAut_adjX]
  · rw [← inv_mul_cancel_right β (exactNormalAut τ K 1 (RingEquiv.refl K) ε), MulAut.mul_apply,
      hγy, (hp _).2.1, exactNormalAut_adjY]

theorem exactNormalAut_injective
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {a a' : Fin τ.rank → Kˣ} {σ σ' : K ≃+* K} {ε ε' : Fin (exactE τ)}
    (h : exactNormalAut τ K a σ ε = exactNormalAut τ K a' σ' ε') : (a, σ, ε) = (a', σ', ε') := by
  have hε : ε = ε' := exactPerm_injective hτ
    (perm_map_simple_unique (α := exactNormalAut τ K a σ ε)
      (fun i => map_simplePosSubgroup_exactNormalAut a σ ε i)
      fun i => by rw [h]; exact map_simplePosSubgroup_exactNormalAut a' σ' ε' i)
  subst hε
  have e : ∀ j c, (a j : K) * σ c = a' j * σ' c := fun j c => by
    obtain ⟨i, rfl⟩ := (exactPerm τ ε).surjective j
    have := congrArg (fun φ : MulAut (adjointGroup τ K) => φ (adjX τ K i c)) h
    simp only [exactNormalAut_adjX] at this
    exact adjX_injective _ this
  have ha : a = a' := funext fun j => Units.ext (by simpa using e j 1)
  subst ha
  have hσ : σ = σ' :=
    RingEquiv.ext fun c => mul_left_cancel₀ (a ⟨0, τ.rank_pos⟩).ne_zero (e _ c)
  subst hσ
  rfl

theorem ordinary_E_exact_automorphism_normal_form
    (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : Type) [Field K] [Finite K] :
    (∀ β ∈ unipotentPairAut τ K, ∃! p : (Fin τ.rank → Kˣ) × (K ≃+* K) × Fin (exactE τ),
      ∀ h : adjointGroup τ K, (β h : ModGL τ K) =
        rootDiagUnit τ p.1 * exactQ τ K p.2.2 *
          Units.map (entrywiseHom p.2.1.toRingHom) (h : ModGL τ K) * (exactQ τ K p.2.2)⁻¹ *
            (rootDiagUnit τ p.1)⁻¹) ∧
    (∀ (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (ε : Fin (exactE τ)),
      ∃ β ∈ unipotentPairAut τ K, ∀ h : adjointGroup τ K, (β h : ModGL τ K) =
        rootDiagUnit τ a * exactQ τ K ε * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) *
          (exactQ τ K ε)⁻¹ * (rootDiagUnit τ a)⁻¹) ∧
    ∀ α : MulAut (adjointGroup τ K), ∃ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ)
      (σ : K ≃+* K) (ε : Fin (exactE τ)), ∀ h : adjointGroup τ K, (α h : ModGL τ K) =
        (g : ModGL τ K) * rootDiagUnit τ a * exactQ τ K ε *
          Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * (exactQ τ K ε)⁻¹ *
            (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹ := by
  refine ⟨fun β hβ => ?_, fun a σ ε =>
    ⟨exactNormalAut τ K a σ ε, exactNormalAut_mem a σ ε, coe_exactNormalAut a σ ε⟩, fun α => ?_⟩
  · obtain ⟨a, σ, ε, rfl⟩ := exists_exactNormalAut_eq hτ hβ
    refine ⟨(a, σ, ε), coe_exactNormalAut a σ ε, fun p hp => ?_⟩
    have e : exactNormalAut τ K p.1 p.2.1 p.2.2 = exactNormalAut τ K a σ ε :=
      MulEquiv.ext fun h => Subtype.ext ((coe_exactNormalAut _ _ _ h).trans (hp h).symm)
    exact exactNormalAut_injective hτ e
  · have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
    obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem τ).length
    obtain ⟨c, β, hU, hV, rfl⟩ :=
      (exceptional_ordinary_Sylow_opposition τ K (ringChar K) w₀ hw₀).2.2.2.2.2 α
    obtain ⟨a, σ, ε, rfl⟩ := exists_exactNormalAut_eq hτ (show β ∈ unipotentPairAut τ K from
      ⟨hU, hV⟩)
    refine ⟨c, a, σ, ε, fun h => ?_⟩
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_exactNormalAut, Subgroup.coe_inv]
    simp only [mul_assoc]

end General

end CFSG.LieType.Chevalley
