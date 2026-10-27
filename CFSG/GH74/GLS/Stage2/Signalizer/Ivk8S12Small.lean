module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Gen2
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Hat
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoCov
public import CFSG.GH74.KGroups.CoverM11
public import CFSG.GH74.KGroups.L28Tables

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage2.Signalizer.Odd87

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}

theorem AFrame.false_of_order' (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J)
    (hZ : center ↥J = ⊥) (hu : ∀ K : Subgroup A, IsComponent K → K = J)
    (hord : ¬ 2 ^ 8 ∣ Nat.card (MulAut (↥J ⧸ center ↥J))) : False := by
  obtain ⟨φ, hinj, -⟩ := hfr.embed_aut hJ hZ hu
  have h1 : Nat.card ↥Sb ∣ Nat.card (MulAut ↥J) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hfr.card] at h1
  let e : (↥J ⧸ center ↥J) ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have h2 : Nat.card (MulAut (↥J ⧸ center ↥J)) = Nat.card (MulAut ↥J) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  exact hord (h2 ▸ h1)

omit [Finite A] in
theorem exists_isFourSubgroup_le_of_quot {J : Subgroup A} (hZ : center ↥J = ⊥)
    (hU : ∃ U : Subgroup (↥J ⧸ center ↥J), IVK.IsFourSubgroup U) :
    ∃ U : Subgroup A, U ≤ J ∧ IVK.IsFourSubgroup U := by
  obtain ⟨U, hU⟩ := hU
  let eJ : (↥J ⧸ center ↥J) ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let f : (↥J ⧸ center ↥J) →* A := J.subtype.comp eJ.toMonoidHom
  have hf : Function.Injective f := J.subtype_injective.comp eJ.injective
  refine ⟨U.map f, ?_, hat_isFourSubgroup_map hU f hf⟩
  rintro _ ⟨u, -, rfl⟩
  exact (eJ u).2

theorem exists_isFourSubgroup_of_mem {G : Type} [Group G] {P : Subgroup G} {a b : G}
    (haP : a ∈ P) (hbP : b ∈ P) (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) : ∃ V : Subgroup ↥P, IVK.IsFourSubgroup V := by
  refine hat_exists_isFourSubgroup_of_involutions (a := (⟨a, haP⟩ : ↥P)) (b := ⟨b, hbP⟩)
    ?_ ?_ ?_ ?_ ?_ ?_
  · exact Subtype.ext ha
  · exact Subtype.ext hb
  · exact Subtype.ext hab
  · exact fun h => ha1 (congrArg Subtype.val h)
  · exact fun h => hb1 (congrArg Subtype.val h)
  · exact fun h => hne (congrArg Subtype.val h)

section M11

open CFSG.GH74.KGroups.M11 CFSG.Certificates CFSG.Sporadic.Schreier

theorem exists_four_M11 {Y : Type}
    [Group Y] (h : NativeSporadic.IsSporadic Y .M11) : ∃ U : Subgroup Y, IVK.IsFourSubgroup U := by
  obtain ⟨e⟩ := equiv_of_sporadic h
  obtain ⟨h8, h2, hc, hfree⟩ := sd16_rels
  have hsR : sR ∈ Q.originalSubgroup := QS_le (by
    rw [QS_closure]
    exact Subgroup.subset_closure (Set.mem_insert _ _))
  have hsT : sT ∈ Q.originalSubgroup := QS_le (by
    rw [QS_closure]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  have hsR4 : sR ^ 4 ∈ Q.originalSubgroup := Subgroup.pow_mem _ hsR 4
  have hsq4 : sR ^ 4 * sR ^ 4 = 1 := by rw [← pow_add]; exact h8
  have hsqT : sT * sT = 1 := by rw [← pow_two]; exact h2
  have hcomm : sR ^ 4 * sT = sT * sR ^ 4 := by
    have h1 : sT * sR ^ 4 * sT⁻¹ = sR ^ 4 := by
      rw [← conj_pow, hc, ← pow_mul]
      calc sR ^ (3 * 4) = sR ^ 8 * sR ^ 4 := by rw [← pow_add]
        _ = sR ^ 4 := by rw [h8, one_mul]
    calc sR ^ 4 * sT = sT * sR ^ 4 * sT⁻¹ * sT := by rw [h1]
      _ = sT * sR ^ 4 := by group
  have hne4 : sR ^ 4 ≠ 1 := fun h' => by
    have := (hfree ⟨4, by norm_num⟩ ⟨0, by norm_num⟩ (by simpa using h')).1
    simp [Fin.ext_iff] at this
  have hneT : sT ≠ 1 := fun h' => by
    have := (hfree ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ (by simpa using h')).2
    simp at this
  have hne : sR ^ 4 ≠ sT := fun h' => by
    have := (hfree ⟨4, by norm_num⟩ ⟨1, by norm_num⟩ (by
      show sR ^ 4 * sT ^ 1 = 1
      rw [pow_one]
      nth_rewrite 1 [h']
      exact hsqT)).1
    simp [Fin.ext_iff] at this
  obtain ⟨V, hV⟩ := exists_isFourSubgroup_of_mem hsR4 hsT hsq4 hsqT hcomm hne4 hneT hne
  exact ⟨V.map e.symm.toMonoidHom, hat_isFourSubgroup_map hV _ e.symm.injective⟩

theorem AFrame.false_of_M11
    (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J)
    (h : NativeSporadic.IsSporadic (↥J ⧸ center ↥J) .M11) : False := by
  have hZ : center ↥J = ⊥ :=
    noTwoCover_M11 (↥J ⧸ center ↥J) h ↥J hJ.1 (hfr.isPGroup_center_two hJ) ⟨MulEquiv.refl _⟩
  obtain ⟨U, hUJ, hU⟩ := exists_isFourSubgroup_le_of_quot hZ ⟨_, (exists_four_M11 h).choose_spec⟩
  have hu := hfr.comp_unique_of_four hJ hUJ hU
  refine hfr.false_of_order' hJ hZ hu ?_
  rw [card_mulAut h]
  norm_num

end M11

section L28

open CFSG.GH74.KGroups.L28 CFSG.Certificates CFSG.Sporadic.Schreier

theorem l28_QS_closure : QS.originalSubgroup = Subgroup.closure {sy0, sy1, sy2} := by
  rw [QS, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem exists_four_L28 {Y : Type}
    [Group Y] (h : LieModel Y .PSL 2 2 3) : ∃ U : Subgroup Y, IVK.IsFourSubgroup U := by
  obtain ⟨e⟩ := equiv_of_lieModel h
  have hs0 : sy0 ∈ QP.originalSubgroup := QS_le (by
    rw [l28_QS_closure]
    exact Subgroup.subset_closure (Set.mem_insert _ _))
  have hs1 : sy1 ∈ QP.originalSubgroup := QS_le (by
    rw [l28_QS_closure]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have hq0 : sy0 * sy0 = 1 := by decide +kernel
  have hq1 : sy1 * sy1 = 1 := by decide +kernel
  have hq01 : sy0 * sy1 = sy1 * sy0 := by decide +kernel
  have hn0 : sy0 ≠ 1 := by decide +kernel
  have hn1 : sy1 ≠ 1 := by decide +kernel
  have hn01 : sy0 ≠ sy1 := by decide +kernel
  obtain ⟨V, hV⟩ := exists_isFourSubgroup_of_mem hs0 hs1 hq0 hq1 hq01 hn0 hn1 hn01
  exact ⟨V.map e.symm.toMonoidHom, hat_isFourSubgroup_map hV _ e.symm.injective⟩

theorem AFrame.false_of_L28
    (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J) (h : LieModel (↥J ⧸ center ↥J) .PSL 2 2 3) :
    False := by
  have hZ : center ↥J = ⊥ := center_eq_bot_psl2_even hJ.1 (Or.inl rfl) h
  obtain ⟨U, hUJ, hU⟩ := exists_isFourSubgroup_le_of_quot hZ ⟨_, (exists_four_L28 h).choose_spec⟩
  have hu := hfr.comp_unique_of_four hJ hUJ hU
  refine hfr.false_of_order' hJ hZ hu ?_
  rw [card_mulAut h]
  norm_num

end L28

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
