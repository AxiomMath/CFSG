module

public import CFSG.Holt.H78.DataTransport
import CFSG.Holt.H78.SEModelFive

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt
open scoped Pointwise

section Alternating

theorem toPermHom_mem_longInv {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]
    [FaithfulSMul G Ω] {t : G} (ht : t ∈ longInv G Ω) :
    MulAction.toPermHom G Ω t ∈ longInv (Equiv.Perm Ω) Ω :=
  (mem_longInv_map_iff (e := Equiv.refl Ω) (f := MulAction.toPermHom G Ω)
    MulAction.toPerm_injective (fun _ _ => rfl) t).mpr ht

theorem isHoltFactor_alternatingGroup {Δ : Type*} [Fintype Δ] [DecidableEq Δ]
    (h5 : 5 ≤ Fintype.card Δ) (hodd : Odd (Fintype.card Δ)) :
    IsHoltFactor (alternatingGroup Δ) := by
  rcases (show Fintype.card Δ = 5 ∨ 7 ≤ Fintype.card Δ by obtain ⟨k, hk⟩ := hodd; omega)
    with h | h
  · exact Or.inr (isNaturalSE_alternatingGroup_five h)
  · exact Or.inl ⟨rfl, h⟩

theorem jOddCore_eq_bot_of_pPrimeCore_eq_bot {G : Type*} [Group G] [Finite G] {Ω : Type*}
    [MulAction G Ω] (hO : CFSG.pPrimeCore 2 G = ⊥) : jOddCore G Ω = ⊥ :=
  eq_bot_iff.mpr (hO ▸ jOddCore_le_pPrimeCore)

variable {G : Type*} [Group G] {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

theorem comap_alternatingGroup_sup_zpowers {t : G} (ht : t ∈ longInv G Ω)
    (hH : jHull G Ω = ⊤) :
    (alternatingGroup Ω).comap (MulAction.toPermHom G Ω) ⊔ Subgroup.zpowers t = jHull G Ω := by
  refine le_antisymm (sup_le (hH ▸ le_top)
    (Subgroup.zpowers_le.mpr (mem_jHull_of_mem_longInv ht))) (jHull_le_iff.mpr fun u hu => ?_)
  have hs := sign_eq_of_mem_longInv_perm (toPermHom_mem_longInv hu) (toPermHom_mem_longInv ht)
  have hut : u * t⁻¹ ∈ (alternatingGroup Ω).comap (MulAction.toPermHom G Ω) := by
    rw [Subgroup.mem_comap, Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, map_mul,
      map_inv, hs, mul_inv_cancel]
  rw [show u = u * t⁻¹ * t by rw [inv_mul_cancel_right]]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hut)
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))

omit [FaithfulSMul G Ω] in
theorem factorImage_comap_alternatingGroup (hH : jHull G Ω = ⊤)
    (hA : alternatingGroup Ω ≤ (MulAction.toPermHom G Ω).range) :
    factorImage G Ω ((alternatingGroup Ω).comap (MulAction.toPermHom G Ω))
      ((MulAction.toPermHom G Ω).comp (jHull G Ω).subtype) = alternatingGroup Ω := by
  rw [factorImage_toPermHom (hH ▸ le_top), Subgroup.map_comap_eq_self hA]

theorem five_le_card_of_alternatingGroup_le {t : G} (ht : t ∈ longInv G Ω)
    (hO : CFSG.pPrimeCore 2 G = ⊥) (hA : alternatingGroup Ω ≤ (MulAction.toPermHom G Ω).range) :
    5 ≤ Fintype.card Ω := by
  have hσ := toPermHom_mem_longInv ht
  have hodd := odd_card_of_mem_longInv_perm hσ
  have h3 := three_le_card_of_mem_longInv_perm hσ
  by_contra h
  have h3' : Fintype.card Ω = 3 := by obtain ⟨k, hk⟩ := hodd; omega
  have : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hcard : Nat.card ((alternatingGroup Ω).comap (MulAction.toPermHom G Ω)) = 3 := by
    rw [← Subgroup.card_map_of_injective (f := MulAction.toPermHom G Ω) MulAction.toPerm_injective,
      Subgroup.map_comap_eq_self hA, nat_card_alternatingGroup, Nat.card_eq_fintype_card, h3']
    rfl
  have hbot := CFSG.pPrimeCore_eq_bot_iff.mp hO _ inferInstance (by rw [hcard]; norm_num)
  rw [hbot, Subgroup.card_bot] at hcard
  omega

end Alternating

section AlternatingData

variable {G : Type*} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

@[expose] noncomputable def HoltData.ofAlternatingGroupLe {t : G} (ht : t ∈ longInv G Ω)
    (hH : jHull G Ω = ⊤) (hO : CFSG.pPrimeCore 2 G = ⊥)
    (hA : alternatingGroup Ω ≤ (MulAction.toPermHom G Ω).range) : HoltData G Ω :=
  .ofFactor ht (jOddCore_eq_bot_of_pPrimeCore_eq_bot hO)
    ((alternatingGroup Ω).comap (MulAction.toPermHom G Ω)) (hH ▸ le_top)
    (by rw [Subgroup.normalizer_eq_top]; exact le_top) (comap_alternatingGroup_sup_zpowers ht hH)
    (by
      rw [factorImage_comap_alternatingGroup hH hA]
      exact isHoltFactor_alternatingGroup (five_le_card_of_alternatingGroup_le ht hO hA)
        (odd_card_of_mem_longInv_perm (toPermHom_mem_longInv ht)))
    fun hn => (mem_alternatingGroup_iff_not_isOuterFactor (toPermHom_mem_longInv ht)).mpr
      (by rwa [factorImage_comap_alternatingGroup hH hA] at hn)

section Lemmas

variable {t : G} (ht : t ∈ longInv G Ω) (hH : jHull G Ω = ⊤) (hO : CFSG.pPrimeCore 2 G = ⊥)
  (hA : alternatingGroup Ω ≤ (MulAction.toPermHom G Ω).range)

@[simp] theorem HoltData.ofAlternatingGroupLe_ι : (HoltData.ofAlternatingGroupLe ht hH hO hA).ι =
    Unit := rfl

@[simp] theorem HoltData.ofAlternatingGroupLe_Ψc
    (i : (HoltData.ofAlternatingGroupLe ht hH hO hA).ι) :
    (HoltData.ofAlternatingGroupLe ht hH hO hA).Ψc i = Ω := rfl

end Lemmas

theorem holtStructure_of_alternatingGroup_le (hJ : (longInv G Ω).Nonempty)
    (hH : jHull G Ω = ⊤) (hO : CFSG.pPrimeCore 2 G = ⊥)
    (hA : alternatingGroup Ω ≤ (MulAction.toPermHom G Ω).range) : HoltStructure G Ω :=
  let ⟨_, ht⟩ := hJ
  ⟨.ofAlternatingGroupLe ht hH hO hA⟩

end AlternatingData

section SE

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω] {q e : ℕ}

theorem isSimpleGroup_of_isBenderNormal_top (h : IsBenderNormal Ω (⊤ : Subgroup G) q e) :
    IsSimpleGroup G := by
  obtain ⟨n, e', -, hB⟩ := IsBenderNormal.benderType h
  have := hB.isSimple
  exact Subgroup.topEquiv.symm.isSimpleGroup

theorem jHull_eq_top_of_isBenderNormal_top (h : IsBenderNormal Ω (⊤ : Subgroup G) q e) {t : G}
    (ht : t ∈ longInv G Ω) : jHull G Ω = ⊤ := by
  have := isSimpleGroup_of_isBenderNormal_top h
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (jHull G Ω)).resolve_left fun hbot => ?_
  have h1 := mem_jHull_of_mem_longInv ht
  rw [hbot, Subgroup.mem_bot] at h1
  have h2 := ht.1
  rw [h1, orderOf_one] at h2
  omega

theorem pPrimeCore_eq_bot_of_isBenderNormal_top
    (h : IsBenderNormal Ω (⊤ : Subgroup G) q e) {t : G} (ht : orderOf t = 2) :
    CFSG.pPrimeCore 2 G = ⊥ := by
  have := isSimpleGroup_of_isBenderNormal_top h
  have : (CFSG.pPrimeCore 2 G).Normal := CFSG.pPrimeCore_normal
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pPrimeCore 2 G)).resolve_right
    fun htop => ?_
  have hcop : Nat.Coprime 2 (Nat.card (CFSG.pPrimeCore 2 G)) := CFSG.pPrimeCore_coprime_card
  rw [htop, Subgroup.card_top] at hcop
  exact Nat.not_coprime_of_dvd_of_dvd (by norm_num) dvd_rfl (ht ▸ orderOf_dvd_natCard t) hcop

theorem longInv_nonempty_of_isBenderNormal_top
    (h : IsBenderNormal Ω (⊤ : Subgroup G) q e) : (longInv G Ω).Nonempty := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 G) := inferInstance
  obtain ⟨-, h2, h1, -⟩ := h.params
  have hdvd : 2 ∣ Nat.card G := ((dvd_pow h2 (by omega : e ≠ 0)).trans
    (h.card_sylow S).symm.dvd).trans (Subgroup.card_subgroup_dvd_card _)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  exact ⟨x, (IsBenderNormal.mem_longInv_iff h).mpr hx⟩

end SE

section SEData

variable {G : Type*} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {q e : ℕ}

@[expose] noncomputable def HoltData.ofIsBenderNormalTop (h : IsBenderNormal Ω (⊤ : Subgroup G) q e)
    {t : G} (ht : t ∈ longInv G Ω) : HoltData G Ω :=
  .ofFactor ht
    (jOddCore_eq_bot_of_pPrimeCore_eq_bot (pPrimeCore_eq_bot_of_isBenderNormal_top h ht.1)) ⊤
    (jHull_eq_top_of_isBenderNormal_top h ht).ge
    (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    (by rw [top_sup_eq, jHull_eq_top_of_isBenderNormal_top h ht])
    (isHoltFactor_factorImage_of_isBenderNormal h (jHull_eq_top_of_isBenderNormal_top h ht).ge)
    fun _ => Subgroup.mem_top t

@[simp] theorem HoltData.ofIsBenderNormalTop_ι (h : IsBenderNormal Ω (⊤ : Subgroup G) q e) {t : G}
    (ht : t ∈ longInv G Ω) : (HoltData.ofIsBenderNormalTop h ht).ι = Unit := rfl

theorem holtStructure_of_isBenderNormal_top (h : IsBenderNormal Ω (⊤ : Subgroup G) q e) :
    HoltStructure G Ω :=
  let ⟨_, ht⟩ := longInv_nonempty_of_isBenderNormal_top h
  ⟨.ofIsBenderNormalTop h ht⟩

theorem holtStructure_of_alternatingGroup_le_or_isBenderNormal (hJ : (longInv G Ω).Nonempty)
    (hH : jHull G Ω = ⊤) (hO : CFSG.pPrimeCore 2 G = ⊥)
    (h : alternatingGroup Ω ≤ (MulAction.toPermHom G Ω).range ∨
      ∃ q e : ℕ, IsBenderNormal Ω (⊤ : Subgroup G) q e) : HoltStructure G Ω := by
  rcases h with hA | ⟨q, e, hB⟩
  · exact holtStructure_of_alternatingGroup_le hJ hH hO hA
  · exact holtStructure_of_isBenderNormal_top hB

end SEData

section Converse

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

namespace HoltData

variable (D : HoltData G Ω)

theorem isBlock_coord_fibre (hH : jHull G Ω = ⊤) (i : D.ι) (b : D.Ψc i) :
    IsBlock G {ω | D.coord ω i = b} := by
  rw [isBlock_iff_smul_eq_or_disjoint]
  intro g
  have hg : g ∈ jHull G Ω := by
    rw [hH]
    exact Subgroup.mem_top g
  have hset : g • {ω | D.coord ω i = b} = {ω | D.coord ω i = D.ρ i ⟨g, hg⟩ b} := by
    ext ω
    rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
    have hω : D.coord ω i = D.ρ i ⟨g, hg⟩ (D.coord (g⁻¹ • ω) i) := by
      rw [← D.coord_smul]
      change D.coord ω i = D.coord (g • g⁻¹ • ω) i
      rw [smul_inv_smul]
    rw [hω, (D.ρ i ⟨g, hg⟩).injective.eq_iff]
  rw [hset]
  by_cases hb : D.ρ i ⟨g, hg⟩ b = b
  · exact Or.inl (by rw [hb])
  · exact Or.inr (Set.disjoint_left.mpr fun ω h1 h2 => hb (h1.symm.trans h2))

theorem map_permCongrHom_map_L {i : D.ι} (c : Ω ≃ D.Ψc i)
    (hc : ∀ (h : jHull G Ω) (ω : Ω), c ((h : G) • ω) = D.ρ i h (c ω)) :
    ((D.L i).map (MulAction.toPermHom G Ω)).map
      (c.permCongrHom : Equiv.Perm Ω →* Equiv.Perm (D.Ψc i)) = D.M i := by
  have key : ∀ h : jHull G Ω,
      (c.permCongrHom : Equiv.Perm Ω →* Equiv.Perm (D.Ψc i)) (MulAction.toPermHom G Ω h) =
        D.ρ i h := fun h => Equiv.ext fun b => by
    rw [MonoidHom.coe_ofClass, Equiv.permCongrHom_coe, Equiv.permCongr_apply,
      MulAction.toPermHom_apply, MulAction.toPerm_apply, hc, Equiv.apply_symm_apply]
  ext x
  rw [Subgroup.mem_map, mem_M]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨⟨g, D.L_le i hg⟩, hg, (key _).symm⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨_, ⟨h, hh, rfl⟩, key h⟩

end HoltData

end Converse

end CFSG.Holt.H78
