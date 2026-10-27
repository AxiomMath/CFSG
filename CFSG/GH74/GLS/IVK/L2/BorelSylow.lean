module

public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.CharacterTheory.PSL2Table.Tori

public section

namespace CFSG.GH74.GLS.IVK.L2Borel

open CFSG.PSL2Table
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem psl2UpperUnipotentSubgroup_eq :
    CFSG.GorensteinWalter.psl2UpperUnipotentSubgroup F = unipotent F := by
  ext x
  rw [CFSG.GorensteinWalter.mem_psl2UpperUnipotentSubgroup_iff, mem_unipotent_iff_exists]
  rfl

theorem exists_sylow_unipotent {p n : ℕ} [Fact p.Prime] [Finite F] (hF : Nat.card F = p ^ n) :
    ∃ Q : Sylow p (PSL(2, F)), (Q : Subgroup (PSL(2, F))) = unipotent F := by
  obtain ⟨Q, hQ⟩ := CFSG.GorensteinWalter.psl2UpperUnipotent_isSylow F hF
  exact ⟨Q, hQ.trans psl2UpperUnipotentSubgroup_eq⟩

theorem exists_conj_eq_unipotent {p n : ℕ} [Fact p.Prime] [Finite F] (hF : Nat.card F = p ^ n)
    (W : Sylow p (PSL(2, F))) :
    ∃ c : PSL(2, F), (W : Subgroup (PSL(2, F))) =
      (unipotent F).map (MulAut.conj c).toMonoidHom := by
  obtain ⟨Q, hQ⟩ := exists_sylow_unipotent (F := F) hF
  obtain ⟨c, hc⟩ := MulAction.IsPretransitive.exists_smul_eq (M := PSL(2, F)) Q W
  refine ⟨c, ?_⟩
  rw [← hc, ← hQ]
  rfl

theorem borel_conj_mem_unipotent {g x : PSL(2, F)} (hg : g ∈ borel F) (hx : x ∈ unipotent F) :
    g * x * g⁻¹ ∈ unipotent F := by
  obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists x).1 hx
  obtain ⟨a, ha⟩ := borel_conj_unip hg t
  rw [ha]
  exact (mem_unipotent_iff_exists _).2 ⟨_, rfl⟩

theorem normalizer_unipotent_eq (h2 : (2 : F) ≠ 0) :
    Subgroup.normalizer ((unipotent F : Subgroup (PSL(2, F))) : Set (PSL(2, F))) = borel F := by
  ext g
  constructor
  · intro hg
    have hx : mk (unip (1 : F)) ∈ unipotent F := mk_unip_mem_unipotent 1
    have hx1 : mk (unip (1 : F)) ≠ 1 := fun h => one_ne_zero ((mk_unip_eq_one_iff h2 1).1 h)
    exact (unipotent_conj_mem_iff h2 hx hx1 g).1 ((Subgroup.mem_normalizer_iff.1 hg _).1 hx)
  · intro hg
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => borel_conj_mem_unipotent hg hh, ?_⟩
    intro hh
    have := borel_conj_mem_unipotent ((borel F).inv_mem hg) hh
    simpa [mul_assoc] using this

theorem unipotent_le_borel : unipotent F ≤ borel F := by
  rintro x ⟨A, hA, rfl⟩
  exact ⟨A, ((mem_unipSL_iff A).1 hA).1, rfl⟩

theorem splitTorus_le_borel : splitTorus F ≤ borel F := by
  rintro x ⟨A, hA, rfl⟩
  exact ⟨A, ((mem_splitSL_iff A).1 hA).2, rfl⟩

theorem unipotent_sup_splitTorus : unipotent F ⊔ splitTorus F = borel F := by
  apply le_antisymm
  · exact sup_le unipotent_le_borel splitTorus_le_borel
  · rintro x ⟨A, hA, rfl⟩
    have h10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hA
    have hdet := det_entries A
    rw [h10, mul_zero, sub_zero] at hdet
    have h0 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have h11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = ((A : Matrix (Fin 2) (Fin 2) F) 0 0)⁻¹ :=
      eq_inv_of_mul_eq_one_right hdet
    have hA' : A = unip ((A : Matrix (Fin 2) (Fin 2) F) 0 1 * (A : Matrix (Fin 2) (Fin 2) F) 0 0) *
        diag (Units.mk0 _ h0) := by
      apply SL_ext <;> simp [mul_apply_SL, h10, h11]
      field_simp
    rw [hA', map_mul]
    exact Subgroup.mul_mem_sup (mk_unip_mem_unipotent _) (mk_diag_mem_splitTorus _)

theorem unipotent_inf_splitTorus : unipotent F ⊓ splitTorus F = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro x ⟨hxU, hxT⟩
  obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists x).1 hxU
  obtain ⟨a, ha⟩ := (mem_splitTorus_iff_exists _).1 hxT
  rw [mk_eq_mk_iff] at ha
  have ht : t = 0 := by
    rcases ha with h | h
    · have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
      simpa using this.symm
    · have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
      simpa [neg_apply_SL] using this.symm
  rw [ht, unip_zero, map_one]

theorem isFrobeniusSplit_unipotent (h2 : (2 : F) ≠ 0) :
    IsFrobeniusSplit (unipotent F) (splitTorus F) (borel F) := by
  refine ⟨unipotent_le_borel, splitTorus_le_borel, ?_, unipotent_sup_splitTorus,
    unipotent_inf_splitTorus, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer unipotent_le_borel,
      normalizer_unipotent_eq h2]
  · intro d hd hd1 w hw hdw
    obtain ⟨a, rfl⟩ := (mem_splitTorus_iff_exists d).1 hd
    obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists w).1 hw
    have ha : (a : F) ^ 2 ≠ 1 := fun h => hd1 ((mk_diag_eq_one_iff a).2 h)
    have h1 : mk (diag a) * mk (unip t) * (mk (diag a))⁻¹ = mk (unip ((a : F) ^ 2 * t)) := by
      rw [mk_conj, diag_conj_unip]
    have h3 : mk (unip ((a : F) ^ 2 * t)) = mk (unip t) := by
      rw [← h1, hdw, mul_inv_cancel_right]
    rw [mk_unip_eq_mk_unip_iff h2] at h3
    have h4 : ((a : F) ^ 2 - 1) * t = 0 := by linear_combination h3
    have ht : t = 0 := (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 ha)
    rw [ht, unip_zero, map_one]

theorem card_splitTorus_eq [Finite F] (h2 : (2 : F) ≠ 0) :
    Nat.card (splitTorus F) = (Nat.card F - 1) / 2 := by
  have := Fintype.ofFinite F
  have h := card_splitTorus h2 (F := F)
  rw [Nat.card_eq_fintype_card (α := F)]
  omega

theorem normalizer_map_equiv {G H : Type*} [Group G] [Group H] (ψ : G ≃* H) (S : Subgroup G) :
    Subgroup.normalizer ((S.map ψ.toMonoidHom : Subgroup H) : Set H) =
      (Subgroup.normalizer (S : Set G)).map ψ.toMonoidHom := by
  ext x
  obtain ⟨y, rfl⟩ := ψ.surjective x
  simp only [Subgroup.mem_normalizer_iff, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply,
    map_mul, map_inv]
  exact ⟨fun h g => by simpa using h (ψ g), fun h h' => h (ψ.symm h')⟩

theorem IsFrobeniusSplit.map_equiv {G H : Type} [Group G] [Group H] (ψ : G ≃* H)
    {W D N : Subgroup G} (h : IsFrobeniusSplit W D N) :
    IsFrobeniusSplit (W.map ψ.toMonoidHom) (D.map ψ.toMonoidHom) (N.map ψ.toMonoidHom) := by
  obtain ⟨hWN, hDN, hnorm, hsup, hinf, hfrob⟩ := h
  refine ⟨Subgroup.map_mono hWN, Subgroup.map_mono hDN, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hWN), normalizer_map_equiv]
    exact Subgroup.map_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer hWN).1 hnorm)
  · rw [← Subgroup.map_sup, hsup]
  · rw [← Subgroup.map_inf_eq _ _ _ ψ.injective, hinf, Subgroup.map_bot]
  · rintro d ⟨d', hd', rfl⟩ hd1 w ⟨w', hw', rfl⟩ hcomm
    have hw1 : w' = 1 := hfrob d' hd' (fun h => hd1 (by simp [h])) w' hw'
      (ψ.injective (by simpa using hcomm))
    simp [hw1]

end CFSG.GH74.GLS.IVK.L2Borel
