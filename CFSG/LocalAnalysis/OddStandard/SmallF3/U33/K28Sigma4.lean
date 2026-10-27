module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.K28Cent
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3S4Rec

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.K28

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Sporadic.Schreier CFSG.Certificates

@[expose] def eList : List Pm := [1, fy, fz, fy * fz]

@[expose] def eTabs : List (List ℕ) := eList.map permTab

theorem eList_nodup : eList.Nodup := by decide +kernel

theorem e_tab_fix : ∀ t ∈ eTabs, conjTab t (permTab frho) = t → t = List.range 28 := by
  decide +kernel

private theorem e_tab_inv : ∀ t ∈ eTabs, invTab 28 t ∈ eTabs := by decide +kernel

private theorem e_tab_mul : ∀ t ∈ eTabs, ∀ u ∈ eTabs, compTab t u ∈ eTabs := by decide +kernel

private theorem e_tab_comm : ∀ t ∈ eTabs, ∀ u ∈ eTabs, compTab t u = compTab u t := by
  decide +kernel

private theorem eList_mul_closed : ∀ a ∈ eList, ∀ b ∈ eList, a * b ∈ eList := by
  intro a ha b hb
  have ha' : permTab a ∈ eTabs := List.mem_map_of_mem ha
  have hb' : permTab b ∈ eTabs := List.mem_map_of_mem hb
  have h := e_tab_mul (permTab a) ha' (permTab b) hb'
  have h' : permTab (a * b) ∈ eList.map permTab := by
    simp only [permTab_mul]
    simpa [eTabs] using h
  exact (List.mem_map_of_injective permTab_injective).mp h'

private theorem eList_inv_closed : ∀ a ∈ eList, a⁻¹ ∈ eList := by
  intro a ha
  have ha' : permTab a ∈ eTabs := List.mem_map_of_mem ha
  have h := e_tab_inv (permTab a) ha'
  have h' : permTab a⁻¹ ∈ eList.map permTab := by
    simp only [permTab_inv]
    simpa [eTabs] using h
  exact (List.mem_map_of_injective permTab_injective).mp h'

private theorem eList_comm : ∀ a ∈ eList, ∀ b ∈ eList, a * b = b * a := by
  intro a ha b hb
  apply permTab_injective
  simp only [permTab_mul]
  exact e_tab_comm (permTab a) (List.mem_map_of_mem ha) (permTab b)
    (List.mem_map_of_mem hb)

private def eC : Subgroup Pm := QP.originalSubgroup ⊓ Subgroup.centralizer ({ftau} : Set Pm)

private def eK : Subgroup Pm := Subgroup.closure {fy, fz}

private theorem fz_sq : fz * fz = 1 := by
  apply permTab_injective
  simp only [permTab_mul, permTab_one]
  decide +kernel

private theorem flam_conj_fz : flam * fz * flam⁻¹ = fz := by
  apply permTab_injective
  simp only [permTab_mul, permTab_inv]
  decide +kernel

private theorem fz_mul_fy_fz : fz * (fy * fz) = fy := by
  rw [← mul_assoc, ← fy_fz_comm, mul_assoc, fz_sq, mul_one]

private theorem fz_ne_one : fz ≠ 1 := by
  intro h
  have h1 : permTab fz = List.range 28 := by rw [h, permTab_one]
  have h2 : permTab fz ≠ List.range 28 := by decide +kernel
  exact h2 h1

private theorem conj_frho_eK : eK.map (MulAut.conj frho) = eK := by
  rw [eK, MonoidHom.map_closure]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl
    · change frho * fy * frho⁻¹ ∈ Subgroup.closure {fy, fz}
      rw [frho_conj_fy_fz.1]
      exact Subgroup.subset_closure (by simp)
    · change frho * fz * frho⁻¹ ∈ Subgroup.closure {fy, fz}
      rw [frho_conj_fy_fz.2]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  · rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · have h1 : MulAut.conj frho fy = fz := by rw [MulAut.conj_apply, frho_conj_fy_fz.1]
      have h2 : MulAut.conj frho fz = fy * fz := by
        rw [MulAut.conj_apply, frho_conj_fy_fz.2]
      have hm1 : fz ∈ Subgroup.closure ((MulAut.conj frho) '' {fy, fz}) :=
        Subgroup.subset_closure ⟨fy, by simp, h1⟩
      have hm2 : fy * fz ∈ Subgroup.closure ((MulAut.conj frho) '' {fy, fz}) :=
        Subgroup.subset_closure ⟨fz, by simp, h2⟩
      have hm := Subgroup.mul_mem _ hm1 hm2
      rwa [fz_mul_fy_fz] at hm
    · have h1 : MulAut.conj frho fy = fz := by rw [MulAut.conj_apply, frho_conj_fy_fz.1]
      exact Subgroup.subset_closure ⟨fy, by simp, h1⟩

private theorem conj_flam_eK : eK.map (MulAut.conj flam) = eK := by
  rw [eK, MonoidHom.map_closure]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl
    · change flam * fy * flam⁻¹ ∈ Subgroup.closure {fy, fz}
      rw [flam_conj_fy]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · change flam * fz * flam⁻¹ ∈ Subgroup.closure {fy, fz}
      rw [flam_conj_fz]
      exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · have h1 : MulAut.conj flam fy = fy * fz := by rw [MulAut.conj_apply, flam_conj_fy]
      have h2 : MulAut.conj flam fz = fz := by rw [MulAut.conj_apply, flam_conj_fz]
      have hm1 : fy * fz ∈ Subgroup.closure ((MulAut.conj flam) '' {fy, fz}) :=
        Subgroup.subset_closure ⟨fy, by simp, h1⟩
      have hm2 : fz ∈ Subgroup.closure ((MulAut.conj flam) '' {fy, fz}) :=
        Subgroup.subset_closure ⟨fz, by simp, h2⟩
      have hm := Subgroup.mul_mem _ hm2 hm1
      rwa [fz_mul_fy_fz] at hm
    · have h2 : MulAut.conj flam fz = fz := by rw [MulAut.conj_apply, flam_conj_fz]
      exact Subgroup.subset_closure ⟨fz, by simp, h2⟩

theorem mem_closure_fy_fz_iff (g : Pm) : g ∈ Subgroup.closure {fy, fz} ↔ g ∈ eList := by
  constructor
  · intro hg
    refine Subgroup.closure_induction (p := fun x _ => x ∈ eList) ?_ ?_ ?_ ?_ hg
    · intro x hx
      rcases hx with rfl | rfl <;> simp [eList]
    · simp [eList]
    · intro x y hx hy ihx ihy
      exact eList_mul_closed x ihx y ihy
    · intro x hx ih
      exact eList_inv_closed x ih
  · intro hg
    simp only [eList, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

theorem cent_ftau_perm_four :
    Nonempty (↥(QP.originalSubgroup ⊓ Subgroup.centralizer ({ftau} : Set Pm)) ≃*
      Equiv.Perm (Fin 4)) := by
  change Nonempty (↥eC ≃* Equiv.Perm (Fin 4))
  have hfyC : fy ∈ eC := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [fy_def]
      exact pow_mem fx₁_mem 2
    · exact Subgroup.mem_centralizer_singleton_iff.mpr d8_comm_ftau.1
  have hfzC : fz ∈ eC := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [fz_eq.1]
      exact Subgroup.mul_mem _ (pow_mem fx₁_mem 2) (pow_mem fx₂_mem 2)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr d8_comm_ftau.2.1
  have hfrhoC : frho ∈ eC := by
    exact Subgroup.mem_inf.mpr ⟨frho_mem, Subgroup.mem_centralizer_singleton_iff.mpr
      ftau_frho.symm⟩
  have hflamC : flam ∈ eC := by
    exact Subgroup.mem_inf.mpr ⟨flam_mem, Subgroup.mem_centralizer_singleton_iff.mpr
      ftau_flam⟩
  have hfyK : fy ∈ eK := by rw [eK]; exact Subgroup.subset_closure (by simp)
  have hfzK : fz ∈ eK := by rw [eK]; exact Subgroup.subset_closure (by simp)
  have hKC : eK ≤ eC := by
    rw [eK, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hfyC
    · exact hfzC
  have hCeq : eC = Subgroup.closure {fy, fz, frho, flam} := by
    simpa [eC] using cent_ftau_eq
  refine CFSG.Quasithin.Fan86.Sigma3.Klein24.nonempty_perm_four
    (G := ↥eC) (N := eK.subgroupOf eC) (x := ⟨frho, hfrhoC⟩) (t := ⟨flam, hflamC⟩) ?_
  refine
    { card := by simpa [eC] using card_cent_ftau
      normal := ?_
      card_N := ?_
      comm := ?_
      ord := ?_
      fix := ?_
      sq := ?_
      moved := ?_ }
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).2 (by
      rw [hCeq, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact Subgroup.le_normalizer hfyK
      · exact Subgroup.le_normalizer hfzK
      · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr conj_frho_eK
      · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr conj_flam_eK)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv]
    have hset : (eK : Set Pm) = {g | g ∈ eList} := by
      ext g
      rw [eK]
      exact mem_closure_fy_fz_iff g
    calc Nat.card ↥eK = (eK : Set Pm).ncard := by
          simpa using Nat.card_coe_set_eq (eK : Set Pm)
      _ = ({g | g ∈ eList} : Set Pm).ncard := by rw [hset]
      _ = 4 := by
          rw [show ({g | g ∈ eList} : Set Pm) = (eList.toFinset : Set Pm) by
            ext g; simp]
          rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup eList_nodup]
          simp [eList]
  · intro a ha b hb
    apply Subtype.ext
    have haK : (a : Pm) ∈ eK := Subgroup.mem_subgroupOf.mp ha
    have hbK : (b : Pm) ∈ eK := Subgroup.mem_subgroupOf.mp hb
    rw [eK] at haK hbK
    exact eList_comm _ ((mem_closure_fy_fz_iff _).1 haK) _
      ((mem_closure_fy_fz_iff _).1 hbK)
  · rw [Subgroup.orderOf_mk]
    exact frho_ord
  · intro n hn hfix
    have hnK : (n : Pm) ∈ eK := Subgroup.mem_subgroupOf.mp hn
    rw [eK] at hnK
    have hne : (n : Pm) ∈ eList := (mem_closure_fy_fz_iff _).1 hnK
    have hval : frho * (n : Pm) * frho⁻¹ = (n : Pm) := by
      have := congrArg Subtype.val hfix
      simpa using this
    have htab : conjTab (permTab (n : Pm)) (permTab frho) = permTab (n : Pm) := by
      have h := congrArg permTab hval
      simp only [permTab_mul, permTab_inv] at h
      simpa [conjTab] using h
    have hrange := e_tab_fix (permTab (n : Pm)) (List.mem_map_of_mem hne) htab
    have hn1 : (n : Pm) = 1 := by
      apply permTab_injective
      rw [hrange, permTab_one]
    exact Subtype.ext hn1
  · exact Subtype.ext (by simpa [pow_two] using flam_pow.1)
  · refine ⟨⟨fy, hfyC⟩, Subgroup.mem_subgroupOf.mpr hfyK, ?_⟩
    intro h
    have hval : flam * fy * flam⁻¹ = fy := by
      have := congrArg Subtype.val h
      simpa using this
    have hfz : fz = 1 := by
      have h1 : fy * fz = fy * 1 := by rw [← flam_conj_fy, hval, mul_one]
      exact mul_left_cancel h1
    exact fz_ne_one hfz

end CFSG.OddStandard.SmallF3.HarrisU33.K28
