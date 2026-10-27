module

public import CFSG.Quasithin.Vol2.Ch1Lem125
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Open CFSG.LieType.BorelTits
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot lemma_1_2_5_exists lemma_1_2_5
  lemma_1_2_5_of_relIndex_eq_two
open scoped commutatorElement

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem lemma_1_2_5_exists_of_a3 {H S R L : Subgroup G} (hS : IsSylowTwoOf S H) (hRS : R ≤ S)
    (hidx : R.relIndex S ≤ 2) (hL : quasithinIsLocal R L) (hLH : L ≤ H)
    (h37H : A37Statement (↥H ⧸ CFSG.pCore 2 ↥H))
    (h37M : A37Statement (↥(L ⊔ R) ⧸ CFSG.pCore 2 ↥(L ⊔ R)))
    (hEcore : cCompSpan H = perfectCore H) : ∃ K ∈ cComp H, L ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLc : L ∈ cComp (L ⊔ R) := cComp_of_isLocal hL
  have hRsyl : IsSylowTwoOf R (L ⊔ R) := ⟨le_sup_right, hL.1, hL.2.2.1⟩
  have hRH : R ≤ H := hRS.trans hS.1
  have hLE : L ≤ cCompSpan H := by
    rw [hEcore]; exact le_perfectCore_of_perfect hLH (perfect_of_mem_cComp hLc)
  have hEH : cCompSpan H ≤ H := by rw [hEcore]; exact perfectCore_le H
  have hEnorm : H ≤ Subgroup.normalizer (cCompSpan H : Set G) := by
    rw [hEcore]; exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore H)
  have hO2n : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hpick : ∃ K ∈ cComp H, ¬ L ≤ sSup (cComp H \ {K}) := by
    by_contra hcon
    push Not at hcon
    have hcomm : ∀ K ∈ cComp H, ⁅L, K⁆ ≤ pCoreOf 2 H := by
      intro K hK
      have h1 : ⁅sSup (cComp H \ {K}), K⁆ ≤ pCoreOf 2 H := by
        rw [Subgroup.commutator_comm]
        refine commutator_sSup_le hO2n (fun K' hK' => le_of_mem_cComp hK'.1) (fun K' hK' => ?_)
        exact commutator_le_pCoreOf_of_ne h37H hK hK'.1 (fun h => hK'.2 h.symm)
      exact (Subgroup.commutator_mono (hcon K hK) le_rfl).trans h1
    have h2 : ⁅L, cCompSpan H⁆ ≤ pCoreOf 2 H :=
      commutator_sSup_le hO2n (fun K hK => le_of_mem_cComp hK) hcomm
    have h3 : L ≤ pCoreOf 2 H :=
      calc L = ⁅L, L⁆ := (perfect_of_mem_cComp hLc).symm
        _ ≤ ⁅L, cCompSpan H⁆ := Subgroup.commutator_mono le_rfl hLE
        _ ≤ pCoreOf 2 H := h2
    have : Group.IsNilpotent ↥L :=
      (((pCoreOf_isPGroup 2 H).to_le h3)).isNilpotent
    exact not_isSolvable_of_mem_cComp hLc inferInstance
  obtain ⟨K, hK, hLK'⟩ := hpick
  set K' := sSup (cComp H \ {K}) with hK'def
  obtain ⟨hKE, hKn⟩ := cComp_normal_span_of_le hK
  have hK'E : K' ≤ cCompSpan H := sSup_le_sSup Set.sdiff_subset
  have hKK'sup : K ⊔ K' = cCompSpan H := by
    have h1 : insert K (cComp H \ {K}) = cComp H := by
      rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hK]
    calc K ⊔ K' = sSup (insert K (cComp H \ {K})) := sSup_insert.symm
      _ = cCompSpan H := by rw [h1]; rfl
  have hEK' : cCompSpan H ≤ Subgroup.normalizer (K' : Set G) := by
    have key : ∀ e ∈ cCompSpan H, ∀ x ∈ K', e * x * e⁻¹ ∈ K' := fun e he x hx =>
      conj_mem_sSup (fun K'' hK'' => cComp_normal_span_of_le hK''.1) he hx
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key e he x hx, fun hx => ?_⟩
    have := key e⁻¹ (Subgroup.inv_mem _ he) _ hx
    simpa [mul_assoc] using this
  have hLcL : L ∈ cComp L := by
    rw [cComp_self_eq_singleton hLc]; exact Set.mem_singleton L
  have hTwo : TwoCosets R S := twoCosets_of_relIndex_le_two hidx
  have hD : IsSylowTwoOf (R ⊓ L) L :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hLc) hRsyl
  have hS₁ : IsSylowTwoOf ((S ⊓ cCompSpan H).subgroupOf (cCompSpan H)) ⊤ :=
    isSylowTwoOf_top_subgroupOf (A4.isSylowTwoOf_inf_normal hS hEH hEnorm)
  have hΛ : L.subgroupOf (cCompSpan H) ∈ cComp (L.subgroupOf (cCompSpan H)) :=
    subgroupOf_mem_cComp_of_le hLE hLcL
  have hΛK' : ¬ L.subgroupOf (cCompSpan H) ≤ K'.subgroupOf (cCompSpan H) := fun h =>
    hLK' fun l hl => h (show (⟨l, hLE hl⟩ : ↥(cCompSpan H)) ∈ L.subgroupOf (cCompSpan H) from hl)
  have hR₁ : (R ⊓ cCompSpan H).subgroupOf (cCompSpan H) ≤
      (S ⊓ cCompSpan H).subgroupOf (cCompSpan H) := fun x hx => by
    have hx' : (x : G) ∈ R ⊓ cCompSpan H := hx
    exact (⟨hRS hx'.1, hx'.2⟩ : (x : G) ∈ S ⊓ cCompSpan H)
  have h2 : TwoCosets ((R ⊓ cCompSpan H).subgroupOf (cCompSpan H))
      ((S ⊓ cCompSpan H).subgroupOf (cCompSpan H)) := (hTwo.inf (cCompSpan H)).subgroupOf' _
  have hD' : IsSylowTwoOf ((R ⊓ cCompSpan H).subgroupOf (cCompSpan H) ⊓
      L.subgroupOf (cCompSpan H)) (L.subgroupOf (cCompSpan H)) := by
    have e : (R ⊓ cCompSpan H).subgroupOf (cCompSpan H) ⊓ L.subgroupOf (cCompSpan H) =
        (R ⊓ L).subgroupOf (cCompSpan H) := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, x.2⟩, h.2⟩⟩
    rw [e]
    exact isSylowTwoOf_subgroupOf_of_le hD hLE
  have hZ : IsPGroup 2 ((pCoreOf 2 (L ⊔ R) ⊓ cCompSpan H).subgroupOf (cCompSpan H)) :=
    A4.isPGroup_subgroupOf_of_le inf_le_right (pCoreOf_isPGroup 2 (L ⊔ R)).to_inf_left
  have hKL : ∀ r ∈ (R ⊓ cCompSpan H).subgroupOf (cCompSpan H),
      (L.subgroupOf (cCompSpan H)).map (MulAut.conj r).toMonoidHom = L.subgroupOf (cCompSpan H) ∨
        ⁅L.subgroupOf (cCompSpan H), (L.subgroupOf (cCompSpan H)).map (MulAut.conj r).toMonoidHom⁆ ≤
          (pCoreOf 2 (L ⊔ R) ⊓ cCompSpan H).subgroupOf (cCompSpan H) := by
    intro r hr
    have hr' : (r : G) ∈ R ⊓ cCompSpan H := hr
    have hr'M : (r : G) ∈ L ⊔ R := (le_sup_right : R ≤ L ⊔ R) hr'.1
    have hLr : L.map (MulAut.conj (r : G)).toMonoidHom ∈ cComp (L ⊔ R) :=
      map_conj_mem_cComp hLc hr'M
    have hconj : (L.subgroupOf (cCompSpan H)).map (MulAut.conj r).toMonoidHom =
        (L.map (MulAut.conj (r : G)).toMonoidHom).subgroupOf (cCompSpan H) := by
      ext y
      rw [A38.mem_map_conj, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, A38.mem_map_conj]
      rfl
    have hLrE : L.map (MulAut.conj (r : G)).toMonoidHom ≤ cCompSpan H := by
      rintro _ ⟨x, hx, rfl⟩
      exact (cCompSpan H).mul_mem ((cCompSpan H).mul_mem hr'.2 (hLE hx))
        ((cCompSpan H).inv_mem hr'.2)
    by_cases hne : L.map (MulAut.conj (r : G)).toMonoidHom = L
    · left
      rw [hconj, hne]
    · right
      rw [hconj, commutator_subgroupOf hLE hLrE]
      have h1 := commutator_le_pCoreOf_of_ne h37M hLc hLr (Ne.symm hne)
      intro x hx
      exact ⟨h1 hx, x.2⟩
  have hProj := le_of_projection (X := ↥(cCompSpan H))
    (K := K.subgroupOf (cCompSpan H)) (K' := K'.subgroupOf (cCompSpan H))
    (Λ := L.subgroupOf (cCompSpan H))
    (S₁ := (S ⊓ cCompSpan H).subgroupOf (cCompSpan H))
    (R₁ := (R ⊓ cCompSpan H).subgroupOf (cCompSpan H))
    (Z := (pCoreOf 2 (L ⊔ R) ⊓ cCompSpan H).subgroupOf (cCompSpan H))
    hKn ((Subgroup.normal_subgroupOf_iff_le_normalizer hK'E).mpr hEK')
    (by rw [← Subgroup.subgroupOf_sup hKE hK'E, hKK'sup, Subgroup.subgroupOf_self])
    hΛ hΛK' hS₁ hR₁ h2 hD' hZ hKL
  exact ⟨K, hK, fun l hl =>
    hProj (show (⟨l, hLE hl⟩ : ↥(cCompSpan H)) ∈ L.subgroupOf (cCompSpan H) from hl)⟩

theorem lemma_1_2_5_exists (hK : LocalSQTK G) (h37 : A37ForSQTKCat) (h39 : A39ForSQTKCat)
    {H S R L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf S H) (hRS : R ≤ S)
    (hidx : R.relIndex S ≤ 2) (hL : quasithinIsLocal R L) (hLH : L ≤ H) :
    ∃ K ∈ cComp H, L ≤ K :=
  lemma_1_2_5_exists_of_a3 hS hRS hidx hL hLH
    (h37 _ (sqtkHypCat_quotient_of_pCoreOf_ne_bot hK hH))
    (h37 _ (sqtkHypCat_quotient_of_pCoreOf_ne_bot hK hL.2.2.2)) (lemma_1_2_1_one hK h39 hH)

theorem lemma_1_2_5 (hK : LocalSQTK G) (h37 : A37ForSQTKCat) (h39 : A39ForSQTKCat)
    {H S R L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf S H) (hRS : R ≤ S)
    (hidx : R.relIndex S ≤ 2) (hL : quasithinIsLocal R L) (hLH : L ≤ H) :
    ∃! K, K ∈ cComp H ∧ L ≤ K := by
  obtain ⟨K, hK', hLK⟩ := lemma_1_2_5_exists hK h37 h39 hH hS hRS hidx hL hLH
  refine ⟨K, ⟨hK', hLK⟩, fun K' hK'' => ?_⟩
  exact CFSG.Quasithin.lemma_1_2_4_unique
    (h37 _ (sqtkHypCat_quotient_of_pCoreOf_ne_bot hK hH)) (mem_lFamily_of_isLocal hL) hK''.1 hK'
    hK''.2 hLK

theorem lemma_1_2_5_of_relIndex_eq_two (hK : LocalSQTK G) (h37 : A37ForSQTKCat)
    (h39 : A39ForSQTKCat) {H S R L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf S H)
    (hRS : R ≤ S) (hidx : R.relIndex S = 2) (hL : quasithinIsLocal R L) (hLH : L ≤ H) :
    ∃! K, K ∈ cComp H ∧ L ≤ K :=
  lemma_1_2_5 hK h37 h39 hH hS hRS hidx.le hL hLH

end Ambient

end CFSG.QuasithinUnique.Vol2Native
