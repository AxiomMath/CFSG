module

public import CFSG.Adapters.TauCetiExceptional.BigCellQuadratic
public import CFSG.Adapters.TauCetiExceptional.BigCellNormal
public import CFSG.LieType.Chevalley.LangFrobeniusFixedDerived
public import CFSG.LieType.Chevalley.OddF4G2AutomorphismNormalForm
public import CFSG.Adapters.TauCetiExceptional.BigCellTail

public noncomputable section

namespace CFSG.TauCetiBridge.BigCell

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti Polynomial

variable {τ : Tag}

@[expose] def InnerFieldNormalForm (τ : Tag) (E : Type) [Field E] : Prop :=
  ∀ α : MulAut (adjointGroup τ E), ∃ (g : adjointGroup τ E) (σ : E ≃+* E),
    ∀ x : adjointGroup τ E, (α x : ModGL τ E) =
      (g : ModGL τ E) * Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ E) *
        (g : ModGL τ E)⁻¹

theorem map_baseChangeGL_adjointGroup_le
    {k K : Type} [Field k] [Field K] (f : k →+* K) :
    (adjointGroup τ k).map (baseChangeGL f) ≤ adjointGroup τ K := by
  rw [map_baseChangeGL_adjointGroup, Subgroup.closure_le]
  rintro _ ⟨i, c, rfl | rfl⟩
  · exact xUnit_mem_adjointGroup i _
  · exact yUnit_mem_adjointGroup i _

section Fields

variable {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [CharP L p] [Algebra (ZMod p) L]
  [Algebra.IsAlgebraic (ZMod p) L]

theorem exists_frobeniusFixedSubfield_of_finset (S : Finset L) {k₀ : ℕ} (hk₀ : k₀ ≠ 0) :
    ∃ k, k ≠ 0 ∧ k₀ ∣ k ∧ ∀ x ∈ S, x ∈ frobeniusFixedSubfield L p k := by
  classical
  choose n hn hx using fun x : L => exists_mem_frobeniusFixedSubfield L p x
  refine ⟨k₀ * ∏ x ∈ S, n x, mul_ne_zero hk₀ (Finset.prod_ne_zero_iff.2 fun x _ => hn x),
    dvd_mul_right _ _, fun x hxS => ?_⟩
  exact frobeniusFixedSubfield_le_of_dvd
    (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem n hxS) _) (hx x)

theorem isAlgClosure_frobeniusFixedSubfield [IsAlgClosed L] (k : ℕ) :
    IsAlgClosure (frobeniusFixedSubfield L p k) L := by
  refine ⟨inferInstance, ⟨fun y => ?_⟩⟩
  obtain ⟨n, hn, hy⟩ := exists_mem_frobeniusFixedSubfield L p y
  refine ⟨X ^ p ^ n - X, FiniteField.X_pow_card_pow_sub_X_ne_zero _ hn
    (Fact.out : p.Prime).one_lt, ?_⟩
  rw [map_sub, map_pow, aeval_X, mem_frobeniusFixedSubfield.1 hy, sub_self]

theorem exists_unit_zpow_ne_one (E : Type) [Field E] [Finite E] (B : ℕ)
    (hE : B + 1 < Nat.card E) : ∃ t : Eˣ, ∀ m : ℤ, m ≠ 0 → m.natAbs ≤ B → t ^ m ≠ 1 := by
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := Eˣ)
  refine ⟨t, fun m hm hB h1 => ?_⟩
  have hord : orderOf t = Nat.card Eˣ := orderOf_eq_card_of_forall_mem_zpowers ht
  rw [Nat.card_units] at hord
  have hd : orderOf t ∣ m.natAbs := Int.natCast_dvd.1 (orderOf_dvd_iff_zpow_eq_one.2 h1)
  have hle := Nat.le_of_dvd (Int.natAbs_pos.2 hm) hd
  omega

end Fields

theorem exists_mulAut_of_conj
    {E K : Type} [Field E] [Field K] (f : E →+* K) (h : ModGL τ K)
    (hHE : ((adjointGroup τ E).map (baseChangeGL f)).map (MulAut.conj h : ModGL τ K →* ModGL τ K) =
      (adjointGroup τ E).map (baseChangeGL f)) :
    ∃ α : MulAut (adjointGroup τ E), ∀ x : adjointGroup τ E,
      baseChangeGL f (α x : ModGL τ E) = h * baseChangeGL f (x : ModGL τ E) * h⁻¹ := by
  have hinj : Function.Injective (baseChangeGL (τ := τ) f) := baseChangeGL_injective f
  refine ⟨(((adjointGroup τ E).equivMapOfInjective _ hinj).trans
    (((MulAut.conj h).subgroupMap _).trans (MulEquiv.subgroupCongr hHE))).trans
      ((adjointGroup τ E).equivMapOfInjective _ hinj).symm, fun x => ?_⟩
  rw [← Subgroup.coe_equivMapOfInjective_apply (adjointGroup τ E) _ hinj]
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulEquiv.subgroupCongr_apply,
    MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply, Subgroup.coe_equivMapOfInjective_apply]

theorem mem_adjointGroup_of_inner_entrywise
    {L : Type} [Field L] [IsAlgClosed L]
    (hτ : HasQuadraticNode τ) (h2 : (2 : L) ≠ 0) (E : Subfield L) (σ : E ≃+* E) (t : Eˣ)
    (ht : ∀ m : ℤ, m ≠ 0 → m.natAbs ≤ pairBound τ → t ^ m ≠ 1) {H : Subgroup (ModGL τ L)}
    (hCH : adjointGroup τ L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (h : Module.End L (RootModule τ L))) P = 0)
    {h : ModGL τ L} (hh : h ∈ H) (g : adjointGroup τ E) (α : MulAut (adjointGroup τ E))
    (hα : ∀ x : adjointGroup τ E,
      baseChangeGL E.subtype (α x : ModGL τ E) = h * baseChangeGL E.subtype (x : ModGL τ E) * h⁻¹)
    (hgσ : ∀ x : adjointGroup τ E, (α x : ModGL τ E) =
      (g : ModGL τ E) * Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ E) *
        (g : ModGL τ E)⁻¹) :
    h ∈ adjointGroup τ L := by
  have hgL : baseChangeGL E.subtype (g : ModGL τ E) ∈ adjointGroup τ L :=
    map_baseChangeGL_adjointGroup_le E.subtype (Subgroup.mem_map.2 ⟨(g : ModGL τ E), g.2, rfl⟩)
  have hh' : (baseChangeGL E.subtype (g : ModGL τ E))⁻¹ * h ∈ H :=
    H.mul_mem (H.inv_mem (hCH hgL)) hh
  have hσ : ∀ x ∈ adjointGroup τ E,
      (baseChangeGL E.subtype (g : ModGL τ E))⁻¹ * h * baseChangeGL E.subtype x *
        ((baseChangeGL E.subtype (g : ModGL τ E))⁻¹ * h)⁻¹ =
      baseChangeGL E.subtype (Units.map (entrywiseHom σ.toRingHom) x) := by
    intro x hx
    have e : (baseChangeGL E.subtype (g : ModGL τ E))⁻¹ * h * baseChangeGL E.subtype x *
        ((baseChangeGL E.subtype (g : ModGL τ E))⁻¹ * h)⁻¹ =
        (baseChangeGL E.subtype (g : ModGL τ E))⁻¹ *
          (h * baseChangeGL E.subtype x * h⁻¹) * baseChangeGL E.subtype (g : ModGL τ E) := by
      group
    rw [e, ← hα ⟨x, hx⟩, hgσ ⟨x, hx⟩, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  obtain ⟨i₀, hA3⟩ := hτ
  have hmem := mem_adjointGroup_of_conj_entrywise_of h2 i₀ (hA3 L) E σ t ht _ (hH _ hh') hσ
  have e : h = baseChangeGL E.subtype (g : ModGL τ E) *
      ((baseChangeGL E.subtype (g : ModGL τ E))⁻¹ * h) := by group
  rw [e]
  exact mul_mem hgL hmem

theorem innerFieldNormalForm_F4
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {f : ℕ} (hf : 1 ≤ f)
    (E : Type) [Field E] (hE : Nat.card E = p ^ f) : InnerFieldNormalForm .F4 E := fun α => by
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := (odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 hf E
    hE .F4 (Or.inl rfl)).1 α
  exact ⟨g, σ, hgσ⟩

section Endgame

variable {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [IsAlgClosed L] [CharP L p]
  [Algebra (ZMod p) L] [Algebra.IsAlgebraic (ZMod p) L]

omit [IsAlgClosed L] [Algebra (ZMod p) L] [Algebra.IsAlgebraic (ZMod p) L] in
theorem two_ne_zero_of_charP (hp2 : p ≠ 2) : (2 : L) ≠ 0 := by
  intro h0
  have h0' : ((2 : ℕ) : L) = 0 := by exact_mod_cast h0
  have := (CharP.cast_eq_zero_iff L p 2).1 h0'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)

theorem exists_conj_mulAut
    (hp2 : p ≠ 2) (H : Subgroup (ModGL τ L))
    (hCH : adjointGroup τ L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (h : Module.End L (RootModule τ L))) P = 0)
    {h : ModGL τ L} (hh : h ∈ H) :
    ∃ k, k ≠ 0 ∧ (∃ t : (frobeniusFixedSubfield L p k)ˣ,
      ∀ m : ℤ, m ≠ 0 → m.natAbs ≤ pairBound τ → t ^ m ≠ 1) ∧
      ∃ α : MulAut (adjointGroup τ (frobeniusFixedSubfield L p k)),
        ∀ x : adjointGroup τ (frobeniusFixedSubfield L p k),
          baseChangeGL (frobeniusFixedSubfield L p k).subtype
              (α x : ModGL τ (frobeniusFixedSubfield L p k)) =
            h * baseChangeGL (frobeniusFixedSubfield L p k).subtype
              (x : ModGL τ (frobeniusFixedSubfield L p k)) * h⁻¹ := by
  classical
  set S : Finset L := Finset.univ.image (fun ij : Fin (nLab τ) × Fin (nLab τ) =>
      natMat τ L (h : Module.End L (RootModule τ L)) ij.1 ij.2) ∪
    Finset.univ.image (fun ij : Fin (nLab τ) × Fin (nLab τ) =>
      natMat τ L ((h⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) ij.1 ij.2) with hSdef
  obtain ⟨k, hk, hk₀, hS⟩ := exists_frobeniusFixedSubfield_of_finset (p := p) S
    (k₀ := pairBound τ + 2) (by omega)
  have : Finite (frobeniusFixedSubfield L p k) := finite_frobeniusFixedSubfield L p k hk
  have hcard : Nat.card (frobeniusFixedSubfield L p k) = p ^ k :=
    card_frobeniusFixedSubfield L p k hk
  have := isAlgClosure_frobeniusFixedSubfield (p := p) (L := L) k
  set E := frobeniusFixedSubfield L p k with hEdef
  have hbig : pairBound τ + 1 < Nat.card E := by
    rw [hcard]
    have hk' : pairBound τ + 2 ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hk₀
    calc pairBound τ + 1 < 2 ^ (pairBound τ + 1) := Nat.lt_two_pow_self
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ p ^ k := Nat.pow_le_pow_left (Fact.out : p.Prime).two_le k
  obtain ⟨t, ht⟩ := exists_unit_zpow_ne_one E (pairBound τ) hbig
  set Fr : L →+* L := iterateFrobenius L p k with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card E := fun c => by
    rw [hcard]
    rfl
  have hodd : Odd (Nat.card E) := by
    rw [hcard]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  obtain ⟨-, -, -, hder⟩ :=
    exceptional_Lang_Frobenius_fixed_derived_root_group τ E hodd L Fr hFr
  set F : ModGL τ L →* ModGL τ L := Units.map (entrywiseHom Fr) with hFdef
  set R := adjointGroup τ L ⊓ F.eqLocus (MonoidHom.id _) with hRdef
  set ι : ModGL τ E →* ModGL τ L := baseChangeGL (algebraMap E L) with hιdef
  have hFix : ∀ g : ModGL τ L, (∀ i j, natMat τ L (g : Module.End L (RootModule τ L)) i j ∈ E) →
      F g = g := by
    intro g hg
    refine Units.ext ?_
    change entrywise Fr (g : Module.End L (RootModule τ L)) = g
    refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => ?_)
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rw [entrywise_single, Finsupp.mapRange_apply]
    have hx := hg (posEquiv τ a) (posEquiv τ b)
    rw [natMat_apply_posEquiv] at hx
    exact mem_frobeniusFixedSubfield.1 hx
  have hFh : F h = h := hFix h fun i j =>
    hS _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩))
  have hFh' : F h⁻¹ = h⁻¹ := by rw [map_inv, hFh]
  have hRconj : ∀ g : ModGL τ L, g ∈ H → F g = g → ∀ r ∈ R, g * r * g⁻¹ ∈ R := by
    intro g hg hFg r hr
    refine ⟨(Subgroup.mem_normalizer_iff.1
      (le_normalizer_adjointGroup H hCH hH hg) r).1 hr.1, ?_⟩
    have hr2 : F r = r := hr.2
    change F (g * r * g⁻¹) = g * r * g⁻¹
    rw [map_mul, map_mul, map_inv, hFg, hr2]
  have hRmap : R.map (MulAut.conj h : ModGL τ L →* ModGL τ L) = R := by
    refine le_antisymm ?_ fun r hr => ?_
    · rintro _ ⟨r, hr, rfl⟩
      exact hRconj h hh hFh r hr
    · refine ⟨h⁻¹ * r * h⁻¹⁻¹, hRconj h⁻¹ (H.inv_mem hh) hFh' r hr, ?_⟩
      change h * (h⁻¹ * r * h⁻¹⁻¹) * h⁻¹ = r
      group
  have hHE : ((adjointGroup τ E).map ι).map (MulAut.conj h : ModGL τ L →* ModGL τ L) =
      (adjointGroup τ E).map ι := by
    rw [← hder, Subgroup.map_commutator, hRmap]
  obtain ⟨α, hα⟩ := exists_mulAut_of_conj (algebraMap E L) h hHE
  rw [Subfield.algebraMap_ofSubfield] at hα
  exact ⟨k, hk, ⟨t, ht⟩, α, hα⟩

theorem le_adjointGroup_of_normalForm
    (hτ : HasQuadraticNode τ) (hp2 : p ≠ 2)
    (hNF : ∀ k, k ≠ 0 → InnerFieldNormalForm τ (frobeniusFixedSubfield L p k))
    (H : Subgroup (ModGL τ L)) (hCH : adjointGroup τ L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (h : Module.End L (RootModule τ L))) P = 0) :
    H ≤ adjointGroup τ L := by
  intro h hh
  obtain ⟨k, hk, ⟨t, ht⟩, α, hα⟩ := exists_conj_mulAut hp2 H hCH hH hh
  obtain ⟨g, σ, hgσ⟩ := hNF k hk α
  exact mem_adjointGroup_of_inner_entrywise hτ (two_ne_zero_of_charP hp2) _ σ t ht hCH hH hh g
    α hα hgσ

theorem le_adjointGroup_F4
    (hp2 : p ≠ 2) (H : Subgroup (ModGL .F4 L))
    (hCH : adjointGroup .F4 L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat .F4 P →
      evalMat (natMat .F4 L (h : Module.End L (RootModule .F4 L))) P = 0) :
    H ≤ adjointGroup .F4 L :=
  le_adjointGroup_of_normalForm (hasQuadraticNode_of_ne_G2 (by decide)) hp2
    (fun k hk => innerFieldNormalForm_F4 Fact.out hp2 (Nat.one_le_iff_ne_zero.2 hk) _
      (card_frobeniusFixedSubfield L p k hk)) H hCH hH

end Endgame

end CFSG.TauCetiBridge.BigCell
