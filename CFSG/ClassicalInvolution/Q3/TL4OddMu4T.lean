module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu4D
public import CFSG.ClassicalInvolution.Q3.TL4OddMu9L

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight

section Q8

theorem q8_facts : ∀ q : QuaternionGroup 2, q * q = QuaternionGroup.a 2 →
    (∃ p : QuaternionGroup 2, p * q * p⁻¹ = q⁻¹) ∧ ∃ p : QuaternionGroup 2, p * q ≠ q * p := by
  decide

theorem q8_a_one_sq : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
    QuaternionGroup.a 2 := by
  decide

theorem q8_a_two_sq : (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 := by
  decide

theorem q8_a_two_ne : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by
  decide

variable {Y : Type} [Group Y] {T : Subgroup Y} {z : Y}

theorem q8_exists_sq (e : ↥T ≃* QuaternionGroup 2) (hz : IsUniqueInvolution T z) :
    ∃ y ∈ T, y * y = z := by
  refine ⟨(e.symm (QuaternionGroup.a 1) : Y), (e.symm _).2, ?_⟩
  have h1 : ((e.symm (QuaternionGroup.a 1) : ↥T) : Y) * (e.symm (QuaternionGroup.a 1) : ↥T) =
      (e.symm (QuaternionGroup.a 2) : ↥T) := by
    rw [← Subgroup.coe_mul, ← map_mul, q8_a_one_sq]
  rw [h1]
  have h2 : ((e.symm (QuaternionGroup.a 2) : ↥T) : Y) * (e.symm (QuaternionGroup.a 2) : ↥T) =
      1 := by
    rw [← Subgroup.coe_mul, ← map_mul, q8_a_two_sq, map_one, Subgroup.coe_one]
  rcases hz.unique _ (e.symm _).2 h2 with h3 | h3
  · exfalso
    apply q8_a_two_ne
    have h4 : e.symm (QuaternionGroup.a 2) = 1 := Subtype.ext h3
    simpa using congrArg e h4
  · exact h3

theorem q8_exists_inv (e : ↥T ≃* QuaternionGroup 2) (hz : IsUniqueInvolution T z) {y : Y}
    (hy : y ∈ T) (hyy : y * y = z) :
    (∃ b ∈ T, b * y * b⁻¹ = y⁻¹) ∧ ∃ b ∈ T, b * y ≠ y * b := by
  set q := e ⟨y, hy⟩ with hq
  have hqq : q * q = QuaternionGroup.a 2 := by
    have hz2 : e ⟨z, hz.mem⟩ = QuaternionGroup.a 2 := by
      have h1 : e.symm (QuaternionGroup.a 2) * e.symm (QuaternionGroup.a 2) = 1 := by
        rw [← map_mul, q8_a_two_sq, map_one]
      rcases hz.unique _ (e.symm (QuaternionGroup.a 2)).2 (congrArg Subtype.val h1) with h3 | h3
      · exfalso
        apply q8_a_two_ne
        have h4 : e.symm (QuaternionGroup.a 2) = 1 := Subtype.ext h3
        simpa using congrArg e h4
      · have h4 : e.symm (QuaternionGroup.a 2) = ⟨z, hz.mem⟩ := Subtype.ext h3
        rw [← h4, MulEquiv.apply_symm_apply]
    rw [hq, ← map_mul, ← hz2]
    congr 1
    exact Subtype.ext hyy
  obtain ⟨⟨p, hp⟩, ⟨p', hp'⟩⟩ := q8_facts q hqq
  refine ⟨⟨(e.symm p : Y), (e.symm p).2, ?_⟩, ⟨(e.symm p' : Y), (e.symm p').2, ?_⟩⟩
  · have h1 : e.symm p * ⟨y, hy⟩ * (e.symm p)⁻¹ = (⟨y, hy⟩ : ↥T)⁻¹ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply, ← hq]
      exact hp
    exact congrArg Subtype.val h1
  · intro h1
    apply hp'
    have h2 : e.symm p' * ⟨y, hy⟩ = ⟨y, hy⟩ * e.symm p' := Subtype.ext h1
    have h3 := congrArg e h2
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, ← hq] at h3

end Q8

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem isSylow2In_of_inf {M C Q P : Subgroup G} (hQ : IsSylow2In Q (M ⊓ C))
    (hP : IsSylow2In P M) (hPC : P ≤ C) : IsSylow2In Q M := by
  refine ⟨hQ.1.trans inf_le_left, hQ.2.1, fun Q' hQ'M hQ'2 hle => ?_⟩
  obtain ⟨V', hV', hQ'V'⟩ := IsSylow2In.exists_ge hQ'2 hQ'M
  obtain ⟨V'', hV'', hPV''⟩ := IsSylow2In.exists_ge hP.2.1 (le_inf hP.1 hPC)
  have h1 : Nat.card Q' ≤ Nat.card Q := by
    calc Nat.card Q' ≤ Nat.card V' := Subgroup.card_le_of_le hQ'V'
      _ = Nat.card P := hV'.natCard_eq hP
      _ ≤ Nat.card V'' := Subgroup.card_le_of_le hPV''
      _ = Nat.card Q := hV''.natCard_eq hQ
  exact (Subgroup.eq_of_le_of_card_ge hle h1).symm

end Sylow

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem exists_commuting_sylow_triple (hL : TightLargeHypR r n Y R S t) {J K' : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hK'K : K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hK'J : K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J) {u : Y}
    (hu : IsUniqueInvolution J u) (hK'u : IsUniqueInvolution K' (t * u)) :
    ∃ T₀ T T' : Subgroup Y, IsSylow2In T₀ (tightCore R) ∧ IsSylow2In T J ∧ IsSylow2In T' K' ∧
      Commutes T₀ T ∧ Commutes T₀ T' ∧ Commutes T T' := by
  have h := TightLargeHypR.typeRFam hL
  have hΩ := hL.datum.hypOmegaGen
  have ht := hL.datum.isUniqueInvolution_core
  have hK₀ : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ hu
  have htu : t ≠ u := fun e => hJ.2.1 (eq_core_of_isUniqueInvolution hL hJ.1 (e ▸ hu))
  have hKJ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK₀ hJ.1 hJ
  have hKK' := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK₀ hK'K.1 hK'K
  have hJK' := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ.1 hK'K.1 hK'J
  have hu1 : u ≠ t * u := fun e => ht.ne_one (by
    calc t = t * u * u⁻¹ := by group
      _ = u * u⁻¹ := by rw [← e]
      _ = 1 := mul_inv_cancel u)
  have ht1 : t ≠ t * u := fun e => hu.ne_one (by
    calc u = t⁻¹ * (t * u) := by group
      _ = t⁻¹ * t := by rw [← e]
      _ = 1 := inv_mul_cancel t)
  have cutu : u * (t * u) = t * u * u := by rw [← mul_assoc, ← ctu]
  have cttu : t * (t * u) = t * u * t := by rw [mul_assoc, ctu, ← mul_assoc]
  obtain ⟨P₀, hP₀, hP₀t, hP₀u, -⟩ := exists_isSylow2In_member_le_centralizer hL hK₀ ht hJ hK'K hu
    hK'u hu1 cutu
  obtain ⟨P₁, hP₁, hP₁u, hP₁t, -⟩ := exists_isSylow2In_member_le_centralizer hL hJ.1 hu hKJ hK'J
    ht hK'u ht1 cttu
  obtain ⟨P₂, hP₂, -, hP₂t, hP₂u⟩ := exists_isSylow2In_member_le_centralizer hL hK'K.1 hK'u hKK'
    hJK' ht hu htu ctu
  set C := Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.centralizer ({u} : Set Y) with hC
  have hCtu : C ≤ Subgroup.centralizer ({t * u} : Set Y) := fun c hc => by
    obtain ⟨hct, hcu⟩ := Subgroup.mem_inf.mp hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hct hcu ⊢
    rw [← mul_assoc, hct, mul_assoc, hcu, ← mul_assoc]
  have hnorm : ∀ {M : Subgroup Y}, C ≤ Subgroup.normalizer (M : Set Y) →
      C ≤ Subgroup.normalizer ((M ⊓ C : Subgroup Y) : Set Y) := by
    intro M hM c hc
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have h1 := (Subgroup.mem_normalizer_iff.mp (hM hc)) w
    constructor
    · rintro ⟨hw1, hw2⟩
      exact ⟨h1.mp hw1, C.mul_mem (C.mul_mem hc hw2) (C.inv_mem hc)⟩
    · rintro ⟨hw1, hw2⟩
      refine ⟨h1.mpr hw1, ?_⟩
      have e : w = c⁻¹ * (c * w * c⁻¹) * c := by group
      rw [e]
      exact C.mul_mem (C.mul_mem (C.inv_mem hc) hw2) hc
  have hC0 : C ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) := fun c hc =>
    h.tight _ hK₀ t ht (Subgroup.mem_inf.mp hc).1
  have hC1 : C ≤ Subgroup.normalizer ((J : Subgroup Y) : Set Y) := fun c hc =>
    h.tight _ hJ.1 u hu (Subgroup.mem_inf.mp hc).2
  have hC2 : C ≤ Subgroup.normalizer ((K' : Subgroup Y) : Set Y) := fun c hc =>
    h.tight _ hK'K.1 (t * u) hK'u (hCtu hc)
  obtain ⟨V, hV⟩ := Disconnected.AschTight.Sec7.exists_isSylow2In C
  have hT₀ : IsSylow2In (V ⊓ (tightCore R ⊓ C)) (tightCore R) := isSylow2In_of_inf
    (S1916.isSylow2In_inf_of_le_normalizer hV inf_le_right (hnorm hC0)) hP₀ (le_inf hP₀t hP₀u)
  have hT₁ : IsSylow2In (V ⊓ (J ⊓ C)) J := isSylow2In_of_inf
    (S1916.isSylow2In_inf_of_le_normalizer hV inf_le_right (hnorm hC1)) hP₁ (le_inf hP₁t hP₁u)
  have hT₂ : IsSylow2In (V ⊓ (K' ⊓ C)) K' := isSylow2In_of_inf
    (S1916.isSylow2In_inf_of_le_normalizer hV inf_le_right (hnorm hC2)) hP₂ (le_inf hP₂t hP₂u)
  obtain ⟨S', hS'⟩ := hV.2.1.exists_le_sylow
  have hR₀ := mem_RSet_of_isSylow2In hK₀ hT₀
  have hR₁ := mem_RSet_of_isSylow2In hJ.1 hT₁
  have hR₂ := mem_RSet_of_isSylow2In hK'K.1 hT₂
  have h8₀ := Sec6Gen.eight_le_of_mem_RSet h.hyp hR₀
  have h8₁ := Sec6Gen.eight_le_of_mem_RSet h.hyp hR₁
  have h8₂ := Sec6Gen.eight_le_of_mem_RSet h.hyp hR₂
  have htT₀ : t ∈ V ⊓ (tightCore R ⊓ C) := T3.mem_of_isPGroup ht hT₀.1 hT₀.2.1 (by omega)
  have huT₁ : u ∈ V ⊓ (J ⊓ C) := T3.mem_of_isPGroup hu hT₁.1 hT₁.2.1 (by omega)
  have htuT₂ : t * u ∈ V ⊓ (K' ⊓ C) := T3.mem_of_isPGroup hK'u hT₂.1 hT₂.2.1 (by omega)
  have hne : ∀ {M : Subgroup Y} {a b : Y} {A B : Subgroup Y}, IsUniqueInvolution M b →
      a ∈ A → A = B → B ≤ M → a ≠ 1 → a * a = 1 → a ≠ b → False := by
    intro M a b A B hb haA hAB hBM ha1 ha2 hab
    rcases hb.unique a (hBM (hAB ▸ haA)) ha2 with h1 | h1
    · exact ha1 h1
    · exact hab h1
  refine ⟨_, _, _, hT₀, hT₁, hT₂, ?_, ?_, ?_⟩
  · exact Q3CP.l67Gen Y _ hΩ S' _ hR₀ _ hR₁ (inf_le_left.trans hS') (inf_le_left.trans hS')
      (fun e => hne hu htT₀ e hT₁.1 ht.ne_one ht.sq htu)
  · exact Q3CP.l67Gen Y _ hΩ S' _ hR₀ _ hR₂ (inf_le_left.trans hS') (inf_le_left.trans hS')
      (fun e => hne hK'u htT₀ e hT₂.1 ht.ne_one ht.sq ht1)
  · exact Q3CP.l67Gen Y _ hΩ S' _ hR₁ _ hR₂ (inf_le_left.trans hS') (inf_le_left.trans hS')
      (fun e => hne hK'u huT₁ e hT₂.1 hu.ne_one hu.sq hu1)

theorem noGNbr_of_linkE4 (hL : TightLargeHypR r n Y R S t) (hcase : LinkE4 R t)
    (hA : ¬ TriNbrAll R t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    NoGNbr R t J := by
  have h := TightLargeHypR.typeRFam hL
  obtain ⟨J₀, hJ₀, hbad⟩ := exists_noGNbr_of_not_triNbrAll hA
  obtain ⟨gb, hgb⟩ := hcase.1 _ (subgroupOf_mem_linkRestrict (t := t) hJ₀) _
    (subgroupOf_mem_linkRestrict (t := t) hJ)
  rw [Generic.conjSub_subgroupOf] at hgb
  have hle : conjSub (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t)
      (secImg (CoreAssembly.conjClass (tightCore R)) t J₀) ≤ linkGrp R t := by
    have h1 := conjSub_mono (n := (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t))
      (le_linkGrp (t := t) hJ₀)
    rwa [conjSub_eq_self_of_mem gb.2] at h1
  have h1 := Subgroup.subgroupOf_inj.mp hgb
  rw [inf_of_le_left hle, inf_of_le_left (le_linkGrp (t := t) hJ)] at h1
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective
    (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t)
  have hg₀C : (g₀ : Y) ∈ Subgroup.centralizer ({t} : Set Y) := layerY_le_centralizer g₀.2
  have h2 : secImg (CoreAssembly.conjClass (tightCore R)) t (conjSub (g₀ : Y) J₀) =
      secImg (CoreAssembly.conjClass (tightCore R)) t J := by
    rw [← conjSub_secImg]
    show conjSub (QuotientGroup.mk g₀) _ = _
    rw [hg₀]
    exact h1
  have hJ₀g := conjSub_mem_omegaNbr_core hL hJ₀ hg₀C
  obtain ⟨ν, -, hJeq⟩ := exists_conj_of_secImg_eq h (xMem_of_mem_omegaNbr_core hL hJ₀g)
    (xMem_of_mem_omegaNbr_core hL hJ) h2
  have hc : (ν : Y) * g₀ ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mul_mem _ (layerY_le_centralizer ν.2) hg₀C
  rw [hJeq, ← conjSub_mul]
  exact noGNbr_conj hL hbad hc

theorem exists_commonNbr_of_linkE4 (hL : TightLargeHypR r n Y R S t) (hcase : LinkE4 R t)
    {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    ∃ K' : Subgroup Y, K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) ∧
      K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J := by
  have h := TightLargeHypR.typeRFam hL
  have hcl := h.hyp.conjInvariant
  have hΦ := (typeRFam_coreLinkFam hL).restrict (linkGrp R t)
  obtain ⟨L, hLΦ, L', hL'⟩ := hcase.2.1
  obtain ⟨gb, hgb⟩ := hcase.1 L hLΦ _ (subgroupOf_mem_linkRestrict (t := t) hJ)
  have h1 := omegaNbr_conj hΦ.hyp.conjInvariant hL' gb
  rw [hgb] at h1
  obtain ⟨_, ⟨K'', hK'', rfl⟩, -, hK''eq⟩ := h1.1
  rw [hK''eq] at h1
  have hnbr := omegaNbr_secFam_of_link hL hJ hK'' h1
  obtain ⟨ν, -, hK''J⟩ := exists_conj_omegaNbr_of_secImg h (xMem_of_mem_omegaNbr_core hL hJ)
    (xMem_of_mem_omegaNbr_core hL hK'') hnbr
  have hνC : ((ν : Y))⁻¹ ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.inv_mem _ (layerY_le_centralizer ν.2)
  refine ⟨conjSub ((ν : Y))⁻¹ K'', conjSub_mem_omegaNbr_core hL hK'' hνC, ?_⟩
  have h2 := omegaNbr_conj hcl hK''J ((ν : Y))⁻¹
  rwa [conjSub_inv_conjSub] at h2

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
