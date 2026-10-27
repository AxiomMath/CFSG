module

public import CFSG.LieType.Multipliers.U43Bridge
public import CFSG.LieType.Multipliers.U43Cover
public import CFSG.LieType.Multipliers.U43Relations
public import CFSG.LieType.Multipliers.CentralKernel
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.LieType.Multipliers.U43

open CFSG.Assembly.LowTwoRank CFSG.CosetTable CFSG.Sporadic.Bridge.TwoGen Subgroup

theorem nonempty_mulEquiv_X₀ {X : Type} [Group X] (h : CFSG.Blueprint.LieModel X .PSU 4 3 1) :
    Nonempty (X ≃* X₀) := by
  rcases h with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have : Fintype K := Fintype.ofFinite K
    have hc : Fintype.card K = Fintype.card F9 := by
      rw [← Nat.card_eq_fintype_card, hK, F9.card_eq]; norm_num
    exact ⟨e.trans (CFSG.Fischer.Classification.Recognition.statedProjSUEquiv
      (FiniteField.ringEquivOfCardEq hc) 4 (3 ^ 1))⟩
  all_goals exact absurd h0 (by norm_num)

noncomputable def crtEquiv : ZMod 12 × ZMod 3 ≃+ ZMod 4 × ZMod 3 × ZMod 3 :=
  ((ZMod.chineseRemainder (m := 4) (n := 3) (by norm_num)).toAddEquiv.prodCongr
    (AddEquiv.refl (ZMod 3))).trans
    { Equiv.prodAssoc (ZMod 4) (ZMod 3) (ZMod 3) with map_add' := fun _ _ => rfl }

theorem mem_relImages {x : PG 2 coverWs}
    (hx : x ∈ PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk} ''
      wordSet rels) : ∃ k < 7, x = zk k := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hv
  exact ⟨k, hk, by rw [zk, List.getD_eq_getElem _ _ hk]⟩

theorem zk_mem_relImages {k : ℕ} (hk : k < 7) :
    zk k ∈ PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk} ''
      wordSet rels :=
  ⟨FreeGroup.mk (rels.getD k []), List.mem_map_of_mem (by
    have hk' : k < rels.length := hk
    rw [List.getD_eq_getElem _ _ hk']
    exact List.getElem_mem _), rfl⟩

theorem multiplier_PSU_four_three
    (X : Type) [Group X] (h : CFSG.Blueprint.LieModel X .PSU 4 3 1) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃* Multiplicative (ZMod 4 × ZMod 3 × ZMod 3)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_X₀ h
  have hP := isPresentation_X₀.mulEquiv e.symm
  have hwg : ∀ i, FreeGroup.lift (fun j => e.symm (img2 xElt yElt (j : Fin 2).val))
      (FreeGroup.mk (commWords (coverPairs i))) = e.symm (img2 xElt yElt i.val) := fun i => by
    rw [lift_mulEquiv, commWord_eval]
  have hw : ∀ i, FreeGroup.mk (commWords (coverPairs i)) ∈ commutator (FreeGroup (Fin 2)) :=
    fun i => mk_commWords_mem_commutator _
  have hperf := isPerfect_of_isPresentation hP hw hwg
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [Nat.card_congr e.toEquiv, card_X₀]; norm_num)
  obtain ⟨E, _, ψ, τ, hτ, h5, h6⟩ := kernel_model
  obtain ⟨hfin, hcard⟩ := card_closure_zk fun x hx => mem_relImages hx
  have hK₀ : Nat.card τ.range = 36 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hτ).toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hK : τ.range ≤ (closure (PresentedGroup.mk
      {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk} '' wordSet rels)).map ψ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨i, -, j, -, hx⟩ := generate_twelve_three (Multiplicative.toAdd x)
    have hx' : x = Multiplicative.ofAdd ((4, 0) : ZMod 12 × ZMod 3) ^ i *
        Multiplicative.ofAdd ((9, 1) : ZMod 12 × ZMod 3) ^ j := by
      rw [← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_add, ← hx]
      rfl
    rw [hx', map_mul, map_pow, map_pow, ← h5, ← h6, ← map_pow, ← map_pow, ← map_mul]
    exact mem_map_of_mem ψ (mul_mem (pow_mem (subset_closure (zk_mem_relImages (by omega))) i)
      (pow_mem (subset_closure (zk_mem_relImages (by omega))) j))
  obtain ⟨hM⟩ := multiplier_of_kernel' hP hw hwg
    (coverRelators_wordSet rels fun i => commWords (coverPairs i)) hfin hcard ψ τ.range hK₀ hK
  exact ⟨hperf.commutator_eq_top, ⟨hM.trans ((MonoidHom.ofInjective hτ).symm.trans
    (AddEquiv.toMultiplicative crtEquiv))⟩⟩

end CFSG.LieType.Multipliers.U43
