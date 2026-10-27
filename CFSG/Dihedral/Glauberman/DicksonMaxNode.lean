module

public import CFSG.Dihedral.Glauberman.DicksonMaxConditions

public section

namespace CFSG.Glauberman.Dickson.MaxNode

open BenderSuzuki.MatrixGroups CFSG.PSL2Table CFSG.GorensteinWalter
open CFSG.Glauberman.Dickson.MaxStructure CFSG.Glauberman.Dickson.MaxUp
open CFSG.Glauberman.Dickson.MaxDown CFSG.Glauberman.Dickson.MaxSubfield
open CFSG.Glauberman.Dickson.MaxCases
open scoped MatrixGroups LinearAlgebra.Projectivization

section Semidirect

variable {H : Type*} [Group H]

theorem exists_semidirect {E C : Subgroup H} [E.Normal] (hdisj : Disjoint E C)
    (hsup : E ⊔ C = ⊤) (hfaith : ∀ c ∈ C, (∀ x ∈ E, c * x = x * c) → c = 1) :
    ∃ φ : C →* MulAut E, Function.Injective φ ∧ Nonempty (H ≃* E ⋊[φ] C) := by
  have hcomp : E.IsComplement' C := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
    rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top]
  refine ⟨_, ?_, ⟨(SemidirectProduct.mulEquivSubgroup hcomp).symm⟩⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro c hc
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
    Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_iff] at hc
  simp only [Subgroup.coe_inclusion] at hc
  rw [Subgroup.mem_bot]
  exact Subtype.ext (hfaith c c.2 (fun e he => (hc e he).symm))

theorem semidirect_of_mulEquiv {K : Type*} [Group K] {p a t : ℕ} [Fact p.Prime] (e : H ≃* K)
    {E C : Subgroup K} (hEn : E.Normal) (hEel : IsElementaryAbelian p E) (hEcard : Nat.card E = a)
    (hC : IsCyclic C) (hCcard : Nat.card C = t) (hdisj : Disjoint E C) (hsup : E ⊔ C = ⊤)
    (hfaith : ∀ c ∈ C, (∀ x ∈ E, c * x = x * c) → c = 1) :
    ∃ E C : Subgroup H, E.Normal ∧ IsElementaryAbelian p E ∧ Nat.card E = a ∧ IsCyclic C ∧
      Nat.card C = t ∧ Disjoint E C ∧ E ⊔ C = ⊤ ∧
      (∀ c ∈ C, (∀ x ∈ E, c * x = x * c) → c = 1) ∧
      ∃ φ : C →* MulAut E, Function.Injective φ ∧ Nonempty (H ≃* E ⋊[φ] C) := by
  let ψ : K →* H := e.symm.toMonoidHom
  have hψ : Function.Injective ψ := e.symm.injective
  have hψs : Function.Surjective ψ := e.symm.surjective
  have hEn' : (E.map ψ).Normal := Subgroup.Normal.map hEn ψ hψs
  have hdisj' : Disjoint (E.map ψ) (C.map ψ) := by
    rw [disjoint_iff, ← Subgroup.map_inf_eq _ _ _ hψ, disjoint_iff.mp hdisj, Subgroup.map_bot]
  have hsup' : E.map ψ ⊔ C.map ψ = ⊤ := by
    rw [← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective _ hψs]
  have hfaith' : ∀ c ∈ C.map ψ, (∀ x ∈ E.map ψ, c * x = x * c) → c = 1 := by
    rintro _ ⟨c, hc, rfl⟩ hcx
    have : c = 1 := hfaith c hc (fun x hx => by
      have := hcx (ψ x) ⟨x, hx, rfl⟩
      rw [← map_mul, ← map_mul] at this
      exact hψ this)
    rw [this, map_one]
  refine ⟨E.map ψ, C.map ψ, hEn', IsElementaryAbelian.map ψ, ?_, ?_, ?_, hdisj', hsup', hfaith',
    exists_semidirect hdisj' hsup' hfaith'⟩
  · rw [Subgroup.card_map_of_injective hψ, hEcard]
  · exact isCyclic_of_surjective _ (ψ.subgroupMap_surjective C)
  · rw [Subgroup.card_map_of_injective hψ, hCcard]

end Semidirect

section Borel

variable {F : Type} [Field F]

theorem unipotent_le_borel : unipotent F ≤ borel F := by
  rintro x ⟨A, ⟨h1, -, -⟩, rfl⟩
  exact ⟨A, h1, rfl⟩

theorem splitTorus_le_borel : splitTorus F ≤ borel F := by
  rintro x ⟨A, ⟨-, h2⟩, rfl⟩
  exact ⟨A, h2, rfl⟩

theorem unip_pow (t : F) (n : ℕ) : unip t ^ n = unip ((n : F) * t) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, unip_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← unip_add]
    congr 1
    push_cast
    ring

theorem isElementaryAbelian_unipotent {p : ℕ} [CharP F p] : IsElementaryAbelian p (unipotent F) :=
  { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (unipotent_mul_comm a.2 b.2)⟩⟩
    exponent_dvd_p := by
      refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => Subtype.ext ?_
      obtain ⟨t, ht⟩ := (mem_unipotent_iff_exists (x : PSL(2, F))).mp x.2
      rw [Subgroup.coe_pow, ht, ← map_pow, unip_pow, CharP.cast_eq_zero, zero_mul, unip_zero,
        map_one, Subgroup.coe_one] }

theorem unipotent_subgroupOf_normal (h2 : (2 : F) ≠ 0) :
    ((unipotent F).subgroupOf (borel F)).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  change (g : PSL(2, F)) * n * (g : PSL(2, F))⁻¹ ∈ unipotent F
  by_cases h1 : (n : PSL(2, F)) = 1
  · rw [h1, mul_one, mul_inv_cancel]
    exact (unipotent F).one_mem
  · exact (unipotent_conj_mem_iff h2 hn h1 g).mpr g.2

variable [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem borel_structure (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) :
    ∃ E C : Subgroup (borel F), E.Normal ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ f ∧
      IsCyclic C ∧ Nat.card C = (p ^ f - 1) / 2 ∧ Disjoint E C ∧ E ⊔ C = ⊤ ∧
      (∀ c ∈ C, (∀ x ∈ E, c * x = x * c) → c = 1) := by
  let : Fintype F := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (by simpa using hF)
  have hp' := hp.out
  have hF2 := ringChar_ne_two hF hp2
  have h2 := Ring.two_ne_zero hF2
  have hq : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  have hodd : Odd (p ^ f) := (hp'.odd_of_ne_two hp2).pow
  have hEcard : Nat.card ((unipotent F).subgroupOf (borel F)) = p ^ f := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe unipotent_le_borel).toEquiv,
      card_unipotent h2, hq]
  have hCcard : Nat.card ((splitTorus F).subgroupOf (borel F)) = (p ^ f - 1) / 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe splitTorus_le_borel).toEquiv,
      card_splitTorus_eq hF2, hq]
  have hBcard : Nat.card (borel F) = p ^ f * ((p ^ f - 1) / 2) := by
    have h := card_borel h2 (F := F)
    rw [hq] at h
    obtain ⟨j, hj⟩ := hodd
    rw [hj, show 2 * j + 1 - 1 = 2 * j by omega] at h ⊢
    rw [show 2 * j / 2 = j by omega]
    nlinarith
  have hcop : Nat.Coprime (Nat.card ((unipotent F).subgroupOf (borel F)))
      (Nat.card ((splitTorus F).subgroupOf (borel F))) := by
    rw [hEcard, hCcard]
    exact (coprime_half_sub hp2 hf0).pow_left f
  have hcomp := Subgroup.isComplement'_of_coprime (by rw [hEcard, hCcard, hBcard]) hcop
  have := isElementaryAbelian_unipotent (F := F) (p := p)
  have := splitTorus_isCyclic (F := F)
  refine ⟨_, _, unipotent_subgroupOf_normal h2, IsElementaryAbelian.subgroupOf unipotent_le_borel,
    hEcard, isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe splitTorus_le_borel).symm
      (MulEquiv.surjective _), hCcard, hcomp.disjoint, hcomp.sup_eq_top, ?_⟩
  intro c hc hcx
  have hx : mk (unip (1 : F)) ∈ borel F := unipotent_le_borel (mk_unip_mem_unipotent 1)
  have hcomm := hcx ⟨_, hx⟩ (show mk (unip (1 : F)) ∈ unipotent F from mk_unip_mem_unipotent 1)
  have hc' : (c : PSL(2, F)) ∈ splitTorus F := hc
  have hcop' : Nat.Coprime (orderOf (c : PSL(2, F))) p := by
    have h1 : orderOf (c : PSL(2, F)) ∣ (p ^ f - 1) / 2 := by
      have := Subgroup.orderOf_dvd_natCard (splitTorus F) hc'
      rwa [card_splitTorus_eq hF2, hq] at this
    exact Nat.Coprime.coprime_dvd_left h1 (coprime_half_sub hp2 hf0).symm
  have hxp : mk (unip (1 : F)) ^ p = 1 := by
    rw [← map_pow, unip_pow, CharP.cast_eq_zero, zero_mul, unip_zero, map_one]
  have hx1 : mk (unip (1 : F)) ≠ 1 := fun h => one_ne_zero ((mk_unip_eq_one_iff h2 1).mp h)
  exact Subtype.ext (CFSG.Glauberman.Dickson.psl2_eq_one_of_commute hF
    (congrArg Subtype.val hcomm) hcop' hxp hx1)

theorem borel_shape (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) {M : Subgroup (PSL2MatrixGroup F)}
    {g : PSL2MatrixGroup F} (hM : M = (borel F).map (MulAut.conj g).toMonoidHom) :
    ∃ E C : Subgroup M, E.Normal ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ f ∧ IsCyclic C ∧
      Nat.card C = (p ^ f - 1) / 2 ∧ Disjoint E C ∧ E ⊔ C = ⊤ ∧
      (∀ c ∈ C, (∀ x ∈ E, c * x = x * c) → c = 1) ∧
      ∃ φ : C →* MulAut E, Function.Injective φ ∧ Nonempty (M ≃* E ⋊[φ] C) := by
  subst hM
  obtain ⟨E, C, hEn, hEel, hEcard, hC, hCcard, hdisj, hsup, hfaith⟩ := borel_structure hF hp2
  exact semidirect_of_mulEquiv
    (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).symm hEn hEel hEcard hC
    hCcard hdisj hsup hfaith

theorem splitTorus_shape (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ f)
    {M : Subgroup (PSL2MatrixGroup F)} {g : PSL2MatrixGroup F}
    (hM : M = (Subgroup.normalizer (splitTorus F : Set (PSL2MatrixGroup F))).map
      (MulAut.conj g).toMonoidHom) :
    Nonempty (M ≃* DihedralGroup ((p ^ f - 1) / 2)) := by
  let : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  obtain ⟨e⟩ := normalizer_splitTorus_mulEquiv (ringChar_ne_two hF hp2) (by omega)
  rw [hq] at e
  subst hM
  exact ⟨(Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).symm.trans e⟩

theorem nonsplitTorus_shape (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ f) {ν : F}
    (hν : ¬ IsSquare ν) {M : Subgroup (PSL2MatrixGroup F)} {g : PSL2MatrixGroup F}
    (hM : M = (Subgroup.normalizer (nonsplitTorus ν : Set (PSL2MatrixGroup F))).map
      (MulAut.conj g).toMonoidHom) :
    Nonempty (M ≃* DihedralGroup ((p ^ f + 1) / 2)) := by
  let : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  obtain ⟨e⟩ := normalizer_nonsplitTorus_mulEquiv (ringChar_ne_two hF hp2) (by omega) hν
  rw [hq] at e
  subst hM
  exact ⟨(Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).symm.trans e⟩

end Borel

section Maximal

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem isCoatom_cases
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ f) {ν : F}
    (hν : ¬ IsSquare ν) {M : Subgroup (PSL2MatrixGroup F)} (hM : IsCoatom M) :
    (∃ g : PSL2MatrixGroup F, M = (borel F).map (MulAut.conj g).toMonoidHom) ∨
    (13 ≤ p ^ f ∧ ∃ g : PSL2MatrixGroup F,
      M = (Subgroup.normalizer (splitTorus F : Set (PSL2MatrixGroup F))).map
        (MulAut.conj g).toMonoidHom) ∨
    (p ^ f ≠ 7 ∧ p ^ f ≠ 9 ∧ ∃ g : PSL2MatrixGroup F,
      M = (Subgroup.normalizer (nonsplitTorus ν : Set (PSL2MatrixGroup F))).map
        (MulAut.conj g).toMonoidHom) ∨
    (∃ m, f = 2 * m ∧ Nonempty (M ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) ∨
    (∃ m r, r.Prime ∧ r ≠ 2 ∧ f = m * r ∧ Nonempty (M ≃* PSL2MatrixGroup (GaloisField p m))) ∨
    (((f = 1 ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) ∨
        (f = 2 ∧ (p ≡ 3 [MOD 10] ∨ p ≡ 7 [MOD 10]))) ∧
      Nonempty (M ≃* alternatingGroup (Fin 5))) ∨
    ((f = 1 ∧ (p ≡ 3 [MOD 8] ∨ p ≡ 5 [MOD 8]) ∧ ¬ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) ∧
      Nonempty (M ≃* alternatingGroup (Fin 4))) ∨
    ((f = 1 ∧ (p ≡ 1 [MOD 8] ∨ p ≡ 7 [MOD 8])) ∧ Nonempty (M ≃* Equiv.Perm (Fin 4))) := by
  classical
  have hp' := hp.out
  have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 := by
    rw [hF]
    exact Nat.gcd_eq_right (two_dvd_pow_sub_one (hp'.odd_of_ne_two hp2) f)
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield
      hF M with
    hel | ⟨z, -, -, hcyc⟩ | ⟨z, hz, hcard, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨h16, ⟨e⟩⟩ | ⟨h5, ⟨e⟩⟩ |
      ⟨m, t, -, -, N, C, hN, hNel, -, hCcyc, -, -, hsup⟩ | ⟨m, hm, hmf, ⟨e⟩, ⟨W⟩⟩ |
      ⟨m, hm, hmf, ⟨e⟩, ⟨W⟩⟩
  · exact (not_isPGroup_of_isCoatom hF hp2 hq5 hM
      (haveI := hel; IsElementaryAbelian.isPGroup p M)).elim
  · exact (not_isCyclic_of_isCoatom hF hp2 hq5 hν hM hcyc).elim
  · rw [hgcd, hF] at hz
    have hz2 : 2 ≤ z := by
      by_contra hz2
      have hpos := Nat.card_pos (α := M)
      have hz1 : z = 1 := by omega
      subst hz1
      exact not_isCyclic_of_isCoatom hF hp2 hq5 hν hM
        (isCyclic_of_prime_card (p := 2) (by omega))
    rcases isCoatom_dihedral_cases hF hp2 hq5 hν hM e hz2 hz.symm with ⟨g, hg⟩ | ⟨g, hg⟩
    · right
      left
      refine ⟨?_, g, hg⟩
      by_contra h13
      rw [hg, isCoatom_map_conj_iff] at hM
      exact not_isCoatom_normalizer_splitTorus_of_lt hF hp2 hq5 (by omega) hM
    · right
      right
      left
      rw [hg, isCoatom_map_conj_iff] at hM
      exact ⟨fun h => not_isCoatom_normalizer_nonsplitTorus_of hF hp2 hν (Or.inl h) hM,
        fun h => not_isCoatom_normalizer_nonsplitTorus_of hF hp2 hν (Or.inr h) hM, g, hg⟩
  · rcases alternatingFour_case hF hp2 hq5 hM e with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, ⟨e⟩⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases permFour_case hF hp2 hq5 hM e h16 with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, ⟨e⟩⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases alternatingFive_case hF hp2 hM e h5 with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, ⟨e⟩⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · left
    by_cases hN1 : N = ⊥
    · exfalso
      rw [hN1, bot_sup_eq] at hsup
      subst hsup
      exact not_isCyclic_of_isCoatom hF hp2 hq5 hν hM
        (isCyclic_of_surjective Subgroup.topEquiv.toMonoidHom Subgroup.topEquiv.surjective)
    · have := hN
      exact isCoatom_semidirect_eq hF hp2 hq5 hM N
        (haveI := hNel; IsElementaryAbelian.isPGroup p N) hN1
  · obtain ⟨r, hr, hr2, hfr⟩ := psl2_case hF hp2 hM hm hmf e W
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, r, hr, hr2, hfr, ⟨e⟩⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, pgl2_case hF hp2 hM hm hmf e W, ⟨e⟩⟩)))

theorem isCoatom_iff
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ f) {ν : F}
    (hν : ¬ IsSquare ν) (M : Subgroup (PSL2MatrixGroup F)) :
    IsCoatom M ↔
      (∃ x : ℙ F (Fin 2 → F), M = MulAction.stabilizer (PSL2MatrixGroup F) x) ∨
      (13 ≤ p ^ f ∧ ∃ g : PSL2MatrixGroup F,
        M = (Subgroup.normalizer (splitTorus F : Set (PSL2MatrixGroup F))).map
          (MulAut.conj g).toMonoidHom) ∨
      (p ^ f ≠ 7 ∧ p ^ f ≠ 9 ∧ ∃ g : PSL2MatrixGroup F,
        M = (Subgroup.normalizer (nonsplitTorus ν : Set (PSL2MatrixGroup F))).map
          (MulAut.conj g).toMonoidHom) ∨
      (∃ m, f = 2 * m ∧ Nonempty (M ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) ∨
      (∃ m r, r.Prime ∧ r ≠ 2 ∧ f = m * r ∧
        Nonempty (M ≃* PSL2MatrixGroup (GaloisField p m))) ∨
      (((f = 1 ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) ∨
          (f = 2 ∧ (p ≡ 3 [MOD 10] ∨ p ≡ 7 [MOD 10]))) ∧
        Nonempty (M ≃* alternatingGroup (Fin 5))) ∨
      ((f = 1 ∧ (p ≡ 3 [MOD 8] ∨ p ≡ 5 [MOD 8]) ∧ ¬ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) ∧
        Nonempty (M ≃* alternatingGroup (Fin 4))) ∨
      ((f = 1 ∧ (p ≡ 1 [MOD 8] ∨ p ≡ 7 [MOD 8])) ∧ Nonempty (M ≃* Equiv.Perm (Fin 4))) := by
  constructor
  · intro hM
    rcases isCoatom_cases hF hp2 hq5 hν hM with ⟨g, hg⟩ | h | h | h | h | h | h | h
    · exact Or.inl ((exists_stabilizer_eq_iff M).mpr ⟨g, hg⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  · rintro (⟨x, rfl⟩ | ⟨h13, g, rfl⟩ | ⟨h7, h9, g, rfl⟩ | ⟨m, hf, ⟨e⟩⟩ |
      ⟨m, r, hr, hr2, hf, ⟨e⟩⟩ | ⟨hc, ⟨e⟩⟩ | ⟨⟨hf, h8, h10⟩, ⟨e⟩⟩ | ⟨⟨hf, -⟩, ⟨e⟩⟩)
    · exact isCoatom_stabilizer x
    · rw [isCoatom_map_conj_iff]
      exact isCoatom_normalizer_splitTorus hF hp2 h13
    · rw [isCoatom_map_conj_iff]
      exact isCoatom_normalizer_nonsplitTorus hF hp2 hq5 h7 h9 hν
    · exact isCoatom_of_mulEquiv_pgl2 hF hp2 hf e
    · exact isCoatom_of_mulEquiv_psl2 hF hp2 hr hr2 hf e
    · exact isCoatom_of_mulEquiv_alternatingFive hF hp2 hc e
    · exact isCoatom_of_mulEquiv_alternatingFour hF hp2 hq5 hf h8 h10 e
    · exact isCoatom_of_mulEquiv_permFour hF hp2 hq5 hf e

theorem isCoatom_isomorphism_types
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ f)
    {M : Subgroup (PSL2MatrixGroup F)} (hM : IsCoatom M) :
    (∃ E C : Subgroup M, E.Normal ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ f ∧
      IsCyclic C ∧ Nat.card C = (p ^ f - 1) / 2 ∧ Disjoint E C ∧ E ⊔ C = ⊤ ∧
      (∀ c ∈ C, (∀ x ∈ E, c * x = x * c) → c = 1) ∧
      ∃ φ : C →* MulAut E, Function.Injective φ ∧ Nonempty (M ≃* E ⋊[φ] C)) ∨
    (13 ≤ p ^ f ∧ Nonempty (M ≃* DihedralGroup ((p ^ f - 1) / 2))) ∨
    (p ^ f ≠ 7 ∧ p ^ f ≠ 9 ∧ Nonempty (M ≃* DihedralGroup ((p ^ f + 1) / 2))) ∨
    (∃ m, f = 2 * m ∧ Nonempty (M ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) ∨
    (∃ m r, r.Prime ∧ r ≠ 2 ∧ f = m * r ∧ Nonempty (M ≃* PSL2MatrixGroup (GaloisField p m))) ∨
    (((f = 1 ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) ∨
        (f = 2 ∧ (p ≡ 3 [MOD 10] ∨ p ≡ 7 [MOD 10]))) ∧
      Nonempty (M ≃* alternatingGroup (Fin 5))) ∨
    ((f = 1 ∧ (p ≡ 3 [MOD 8] ∨ p ≡ 5 [MOD 8]) ∧ ¬ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) ∧
      Nonempty (M ≃* alternatingGroup (Fin 4))) ∨
    ((f = 1 ∧ (p ≡ 1 [MOD 8] ∨ p ≡ 7 [MOD 8])) ∧ Nonempty (M ≃* Equiv.Perm (Fin 4))) := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare (ringChar_ne_two hF hp2)
  rcases isCoatom_cases hF hp2 hq5 hν hM with ⟨g, hg⟩ | ⟨h13, g, hg⟩ | ⟨h7, h9, g, hg⟩ | h | h |
      h | h | h
  · exact Or.inl (borel_shape hF hp2 hg)
  · exact Or.inr (Or.inl ⟨h13, splitTorus_shape hF hp2 hq5 hg⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h7, h9, nonsplitTorus_shape hF hp2 hq5 hν hg⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

theorem exists_isCoatom
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ f) :
    (∃ M : Subgroup (PSL2MatrixGroup F), IsCoatom M ∧
      ∃ E C : Subgroup M, E.Normal ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ f ∧
        IsCyclic C ∧ Nat.card C = (p ^ f - 1) / 2 ∧ Disjoint E C ∧ E ⊔ C = ⊤ ∧
        (∀ c ∈ C, (∀ x ∈ E, c * x = x * c) → c = 1) ∧
        ∃ φ : C →* MulAut E, Function.Injective φ ∧ Nonempty (M ≃* E ⋊[φ] C)) ∧
    (13 ≤ p ^ f → ∃ M : Subgroup (PSL2MatrixGroup F), IsCoatom M ∧
      Nonempty (M ≃* DihedralGroup ((p ^ f - 1) / 2))) ∧
    (p ^ f ≠ 7 → p ^ f ≠ 9 → ∃ M : Subgroup (PSL2MatrixGroup F), IsCoatom M ∧
      Nonempty (M ≃* DihedralGroup ((p ^ f + 1) / 2))) ∧
    (∀ m, f = 2 * m → ∃ M : Subgroup (PSL2MatrixGroup F), IsCoatom M ∧
      Nonempty (M ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) ∧
    (∀ m r, r.Prime → r ≠ 2 → f = m * r → ∃ M : Subgroup (PSL2MatrixGroup F), IsCoatom M ∧
      Nonempty (M ≃* PSL2MatrixGroup (GaloisField p m))) ∧
    (((f = 1 ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) ∨
        (f = 2 ∧ (p ≡ 3 [MOD 10] ∨ p ≡ 7 [MOD 10]))) →
      ∃ M : Subgroup (PSL2MatrixGroup F), IsCoatom M ∧
        Nonempty (M ≃* alternatingGroup (Fin 5))) ∧
    ((f = 1 ∧ (p ≡ 3 [MOD 8] ∨ p ≡ 5 [MOD 8]) ∧ ¬ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) →
      ∃ M : Subgroup (PSL2MatrixGroup F), IsCoatom M ∧
        Nonempty (M ≃* alternatingGroup (Fin 4))) ∧
    ((f = 1 ∧ (p ≡ 1 [MOD 8] ∨ p ≡ 7 [MOD 8])) →
      ∃ M : Subgroup (PSL2MatrixGroup F), IsCoatom M ∧ Nonempty (M ≃* Equiv.Perm (Fin 4))) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hp' := hp.out
  have hF2 := ringChar_ne_two hF hp2
  have hq : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  have hB := CFSG.Glauberman.Dickson.dickson_psl2_subgroup_existence hF
  refine ⟨?_, fun h13 => ?_, fun h7 h9 => ?_, fun m hf => ?_, fun m r hr hr2 hf => ?_,
    fun hc => ?_, fun hc => ?_, fun hc => ?_⟩
  · refine ⟨borel F, ?_, ?_⟩
    · rw [← stabilizer_lineZero]
      exact isCoatom_stabilizer _
    · obtain ⟨E, C, hEn, hEel, hEcard, hC, hCcard, hdisj, hsup, hfaith⟩ := borel_structure hF hp2
      exact ⟨E, C, hEn, hEel, hEcard, hC, hCcard, hdisj, hsup, hfaith,
        exists_semidirect hdisj hsup hfaith⟩
  · refine ⟨_, isCoatom_normalizer_splitTorus hF hp2 h13, ?_⟩
    obtain ⟨e⟩ := normalizer_splitTorus_mulEquiv hF2 (by omega)
    rw [hq] at e
    exact ⟨e⟩
  · obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hF2
    refine ⟨_, isCoatom_normalizer_nonsplitTorus hF hp2 hq5 h7 h9 hν, ?_⟩
    obtain ⟨e⟩ := normalizer_nonsplitTorus_mulEquiv hF2 (by omega) hν
    rw [hq] at e
    exact ⟨e⟩
  · obtain ⟨H, ⟨e⟩⟩ := hB.2.2.2.2.1 m (hf ▸ dvd_refl _)
    exact ⟨H, isCoatom_of_mulEquiv_pgl2 hF hp2 hf e, ⟨e⟩⟩
  · obtain ⟨H, ⟨e⟩⟩ := hB.2.2.2.1 m (hf ▸ dvd_mul_right m r)
    exact ⟨H, isCoatom_of_mulEquiv_psl2 hF hp2 hr hr2 hf e, ⟨e⟩⟩
  · have h5 : (p ^ f) ^ 2 ≡ 1 [MOD 5] := by
      unfold Nat.ModEq
      rcases hc with ⟨rfl, h10⟩ | ⟨rfl, h10⟩
      · rw [pow_one]
        exact sq_mod_five_of_mod_ten' (by unfold Nat.ModEq at h10; omega)
      · have h4 : p ^ 2 % 5 = 4 := by
          have h := Nat.pow_mod p 2 5
          have hlt : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
          have h5' : p % 5 = (p % 10) % 5 := (Nat.mod_mod_of_dvd _ (by norm_num)).symm
          unfold Nat.ModEq at h10
          rw [h]
          interval_cases hr : p % 5 <;> omega
        rw [Nat.pow_mod, h4]
    obtain ⟨H, ⟨e⟩⟩ := hB.2.2.2.2.2.2.2 (Or.inr h5)
    exact ⟨H, isCoatom_of_mulEquiv_alternatingFive hF hp2 hc e, ⟨e⟩⟩
  · obtain ⟨hf, h8, h10⟩ := hc
    obtain ⟨H, ⟨e⟩⟩ := hB.2.2.2.2.2.1 (Or.inl (hp'.odd_of_ne_two hp2))
    exact ⟨H, isCoatom_of_mulEquiv_alternatingFour hF hp2 hq5 hf h8 h10 e, ⟨e⟩⟩
  · obtain ⟨hf, h8⟩ := hc
    have h16 : (p ^ f) ^ 2 ≡ 1 [MOD 16] := by
      unfold Nat.ModEq
      subst hf
      rw [pow_one]
      exact sq_mod_sixteen_of_mod_eight' (by unfold Nat.ModEq at h8; omega)
    obtain ⟨H, ⟨e⟩⟩ := hB.2.2.2.2.2.2.1 h16
    exact ⟨H, isCoatom_of_mulEquiv_permFour hF hp2 hq5 hf e, ⟨e⟩⟩

end Maximal

end CFSG.Glauberman.Dickson.MaxNode

namespace CFSG.Glauberman.Dickson

open BenderSuzuki.MatrixGroups CFSG.PSL2Table
open CFSG.Glauberman.Dickson.MaxNode
open scoped MatrixGroups LinearAlgebra.Projectivization

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem dickson_psl2_subgroups_and_maximal_subgroups
    (hF : Nat.card F = p ^ f) :
    (∀ H : Subgroup (PSL2MatrixGroup F),
      (∃ m, m ≤ f ∧ Nat.card H = p ^ m ∧ IsElementaryAbelian p H) ∨
      (∃ z, (z ∣ (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) ∨
          z ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1)) ∧
        Nat.card H = z ∧ IsCyclic H) ∨
      (∃ z, 2 ≤ z ∧
        (z ∣ (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) ∨ z ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1)) ∧
        Nonempty (H ≃* DihedralGroup z)) ∨
      ((Odd p ∨ Even f) ∧ Nonempty (H ≃* alternatingGroup (Fin 4))) ∨
      ((p ^ f) ^ 2 ≡ 1 [MOD 16] ∧ Nonempty (H ≃* Equiv.Perm (Fin 4))) ∨
      ((p = 5 ∨ (p ^ f) ^ 2 ≡ 1 [MOD 5]) ∧ Nonempty (H ≃* alternatingGroup (Fin 5))) ∨
      (∃ m t, 1 ≤ m ∧ m ≤ f ∧ t ∣ p ^ m - 1 ∧ t ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1) ∧
        ∃ E C : Subgroup H, E.Normal ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ m ∧
          IsCyclic C ∧ Nat.card C = t ∧ Disjoint E C ∧ E ⊔ C = ⊤ ∧
          (∀ c ∈ C, (∀ e ∈ E, c * e = e * c) → c = 1) ∧
          ∃ φ : C →* MulAut E, Function.Injective φ ∧ Nonempty (H ≃* E ⋊[φ] C)) ∨
      (∃ m, m ∣ f ∧ Nonempty (H ≃* PSL2MatrixGroup (GaloisField p m))) ∨
      (∃ m, 2 * m ∣ f ∧ Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)))) ∧
    ((∀ m ≤ f, ∃ H : Subgroup (PSL2MatrixGroup F),
      Nat.card H = p ^ m ∧ IsElementaryAbelian p H) ∧
    (∀ z, (z ∣ (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) ∨ z ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1)) →
      ∃ H : Subgroup (PSL2MatrixGroup F), Nat.card H = z ∧ IsCyclic H) ∧
    (∀ z, 2 ≤ z →
      (z ∣ (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) ∨ z ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1)) →
      ∃ H : Subgroup (PSL2MatrixGroup F), Nonempty (H ≃* DihedralGroup z)) ∧
    (∀ m, m ∣ f → ∃ H : Subgroup (PSL2MatrixGroup F),
      Nonempty (H ≃* PSL2MatrixGroup (GaloisField p m))) ∧
    (∀ m, 2 * m ∣ f → ∃ H : Subgroup (PSL2MatrixGroup F),
      Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) ∧
    ((Odd p ∨ Even f) →
      ∃ H : Subgroup (PSL2MatrixGroup F), Nonempty (H ≃* alternatingGroup (Fin 4))) ∧
    ((p ^ f) ^ 2 ≡ 1 [MOD 16] →
      ∃ H : Subgroup (PSL2MatrixGroup F), Nonempty (H ≃* Equiv.Perm (Fin 4))) ∧
    ((p = 5 ∨ (p ^ f) ^ 2 ≡ 1 [MOD 5]) →
      ∃ H : Subgroup (PSL2MatrixGroup F), Nonempty (H ≃* alternatingGroup (Fin 5)))) ∧
    (p ≠ 2 → 5 ≤ p ^ f →
      (∀ ν : F, ¬ IsSquare ν → ∀ M : Subgroup (PSL2MatrixGroup F), IsCoatom M ↔
        (∃ x : ℙ F (Fin 2 → F), M = MulAction.stabilizer (PSL2MatrixGroup F) x) ∨
        (13 ≤ p ^ f ∧ ∃ g : PSL2MatrixGroup F,
          M = (Subgroup.normalizer (splitTorus F : Set (PSL2MatrixGroup F))).map
            (MulAut.conj g).toMonoidHom) ∨
        (p ^ f ≠ 7 ∧ p ^ f ≠ 9 ∧ ∃ g : PSL2MatrixGroup F,
          M = (Subgroup.normalizer (nonsplitTorus ν : Set (PSL2MatrixGroup F))).map
            (MulAut.conj g).toMonoidHom) ∨
        (∃ m, f = 2 * m ∧ Nonempty (M ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) ∨
        (∃ m r, r.Prime ∧ r ≠ 2 ∧ f = m * r ∧
          Nonempty (M ≃* PSL2MatrixGroup (GaloisField p m))) ∨
        (((f = 1 ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) ∨
            (f = 2 ∧ (p ≡ 3 [MOD 10] ∨ p ≡ 7 [MOD 10]))) ∧
          Nonempty (M ≃* alternatingGroup (Fin 5))) ∨
        ((f = 1 ∧ (p ≡ 3 [MOD 8] ∨ p ≡ 5 [MOD 8]) ∧ ¬ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) ∧
          Nonempty (M ≃* alternatingGroup (Fin 4))) ∨
        ((f = 1 ∧ (p ≡ 1 [MOD 8] ∨ p ≡ 7 [MOD 8])) ∧ Nonempty (M ≃* Equiv.Perm (Fin 4)))) ∧
      (∀ M : Subgroup (PSL2MatrixGroup F), IsCoatom M →
        (∃ E C : Subgroup M, E.Normal ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ f ∧
          IsCyclic C ∧ Nat.card C = (p ^ f - 1) / 2 ∧ Disjoint E C ∧ E ⊔ C = ⊤ ∧
          (∀ c ∈ C, (∀ x ∈ E, c * x = x * c) → c = 1) ∧
          ∃ φ : C →* MulAut E, Function.Injective φ ∧ Nonempty (M ≃* E ⋊[φ] C)) ∨
        (13 ≤ p ^ f ∧ Nonempty (M ≃* DihedralGroup ((p ^ f - 1) / 2))) ∨
        (p ^ f ≠ 7 ∧ p ^ f ≠ 9 ∧ Nonempty (M ≃* DihedralGroup ((p ^ f + 1) / 2))) ∨
        (∃ m, f = 2 * m ∧ Nonempty (M ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) ∨
        (∃ m r, r.Prime ∧ r ≠ 2 ∧ f = m * r ∧
          Nonempty (M ≃* PSL2MatrixGroup (GaloisField p m))) ∨
        (((f = 1 ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) ∨
            (f = 2 ∧ (p ≡ 3 [MOD 10] ∨ p ≡ 7 [MOD 10]))) ∧
          Nonempty (M ≃* alternatingGroup (Fin 5))) ∨
        ((f = 1 ∧ (p ≡ 3 [MOD 8] ∨ p ≡ 5 [MOD 8]) ∧ ¬ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) ∧
          Nonempty (M ≃* alternatingGroup (Fin 4))) ∨
        ((f = 1 ∧ (p ≡ 1 [MOD 8] ∨ p ≡ 7 [MOD 8])) ∧ Nonempty (M ≃* Equiv.Perm (Fin 4)))) ∧
      ((∃ M : Subgroup (PSL2MatrixGroup F), IsCoatom M ∧
        ∃ E C : Subgroup M, E.Normal ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ f ∧
          IsCyclic C ∧ Nat.card C = (p ^ f - 1) / 2 ∧ Disjoint E C ∧ E ⊔ C = ⊤ ∧
          (∀ c ∈ C, (∀ x ∈ E, c * x = x * c) → c = 1) ∧
          ∃ φ : C →* MulAut E, Function.Injective φ ∧ Nonempty (M ≃* E ⋊[φ] C)) ∧
      (13 ≤ p ^ f → ∃ M : Subgroup (PSL2MatrixGroup F), IsCoatom M ∧
        Nonempty (M ≃* DihedralGroup ((p ^ f - 1) / 2))) ∧
      (p ^ f ≠ 7 → p ^ f ≠ 9 → ∃ M : Subgroup (PSL2MatrixGroup F), IsCoatom M ∧
        Nonempty (M ≃* DihedralGroup ((p ^ f + 1) / 2))) ∧
      (∀ m, f = 2 * m → ∃ M : Subgroup (PSL2MatrixGroup F), IsCoatom M ∧
        Nonempty (M ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) ∧
      (∀ m r, r.Prime → r ≠ 2 → f = m * r → ∃ M : Subgroup (PSL2MatrixGroup F), IsCoatom M ∧
        Nonempty (M ≃* PSL2MatrixGroup (GaloisField p m))) ∧
      (((f = 1 ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) ∨
          (f = 2 ∧ (p ≡ 3 [MOD 10] ∨ p ≡ 7 [MOD 10]))) →
        ∃ M : Subgroup (PSL2MatrixGroup F), IsCoatom M ∧
          Nonempty (M ≃* alternatingGroup (Fin 5))) ∧
      ((f = 1 ∧ (p ≡ 3 [MOD 8] ∨ p ≡ 5 [MOD 8]) ∧ ¬ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) →
        ∃ M : Subgroup (PSL2MatrixGroup F), IsCoatom M ∧
          Nonempty (M ≃* alternatingGroup (Fin 4))) ∧
      ((f = 1 ∧ (p ≡ 1 [MOD 8] ∨ p ≡ 7 [MOD 8])) →
        ∃ M : Subgroup (PSL2MatrixGroup F), IsCoatom M ∧
          Nonempty (M ≃* Equiv.Perm (Fin 4))))) :=
  ⟨dickson_psl2_subgroup_list hF, dickson_psl2_subgroup_existence hF,
    fun hp2 hq5 => ⟨fun _ hν M => isCoatom_iff hF hp2 hq5 hν M,
      fun _ hM => isCoatom_isomorphism_types hF hp2 hq5 hM, exists_isCoatom hF hp2 hq5⟩⟩

end CFSG.Glauberman.Dickson
