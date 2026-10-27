module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.M24Ref
public import CFSG.Quasithin.Vol2.KGFactC31M24Frame
public import CFSG.Quasithin.Vol2.KGFactC31M24Lat

public section

namespace CFSG.SectionRank.QTK.Insp443.M24

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.M24 CFSG.Certificates
  _root_.Certificates

open CFSG.Sporadic.Schreier (commT_iff mem_centralizerIn centralizerIn)

@[expose] def gE : G₀ := elt gW

@[expose] def lE : G₀ := elt lW

@[expose] def zE : G₀ := gE * d6⁻¹

@[expose] def xE : G₀ := elt xW

@[expose] def nE : G₀ := elt nW

private theorem eElt_fin_append {α : Type*} [Group α] {m n : ℕ} (f : Fin m → α) (g : Fin n → α)
    (c₁ : Fin m → ZMod 2) (c₂ : Fin n → ZMod 2) :
    eElt (Fin.append f g) (Fin.append c₁ c₂) = eElt f c₁ * eElt g c₂ := by
  have hfun : (fun i : Fin (m + n) => Fin.append f g i ^ (Fin.append c₁ c₂ i).val) =
      Fin.append (fun i : Fin m => f i ^ (c₁ i).val)
        (fun i : Fin n => g i ^ (c₂ i).val) := by
    funext i
    refine Fin.addCases (m := m) (n := n) (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left, Fin.append_left, Fin.append_left]
    · rw [Fin.append_right, Fin.append_right, Fin.append_right]
  unfold eElt
  rw [hfun, List.ofFn_fin_append, List.prod_append]

private theorem closure_range_fin_append {α : Type*} [Group α] {m n : ℕ} (f : Fin m → α)
    (g : Fin n → α) :
    Subgroup.closure (Set.range (Fin.append f g)) =
      Subgroup.closure (Set.range f) ⊔ Subgroup.closure (Set.range g) := by
  rw [← Subgroup.closure_union]
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.addCases (m := m) (n := n)
      (motive := fun i => Fin.append f g i ∈ Set.range f ∪ Set.range g)
      (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact Or.inl ⟨j, rfl⟩
    · rw [Fin.append_right]; exact Or.inr ⟨j, rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd n i, Fin.append_left f g i⟩
    · exact ⟨Fin.natAdd m j, Fin.append_right f g j⟩

private theorem forall₂_append {α β : Type*} {R : α → β → Prop} {l₁ l₂ : List α}
    {m₁ m₂ : List β} (h₁ : List.Forall₂ R l₁ m₁) (h₂ : List.Forall₂ R l₂ m₂) :
    List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h ih

theorem conj_gE_t :
    (eSub basis_t).map (MulAut.conj gE).toMonoidHom = eSub basis_et := by
  have hci : Rep 24 (invT 24 gT) ((gE : G₀) : Equiv.Perm (Fin 24))⁻¹ :=
    Rep.inv_of_invOK (rep_elt gW) k_g_inv
  have hforall : List.Forall₂ (Rep 24) (conjAll gT tT)
      (List.ofFn fun i => ((gE * vT i * gE⁻¹ : G₀) : Equiv.Perm (Fin 24))) :=
    forall₂_conjTab forall₂_t (rep_elt gW) hci
  have hle : (eSub basis_t).map (MulAut.conj gE).toMonoidHom ≤ eSub basis_et := by
    rw [← eSub_conj basis_t gE, eSub_eq_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨b, hb, hbi⟩ := exists_tab_of_mem hforall (List.mem_ofFn.mpr ⟨i, rfl⟩)
    exact (mem_eSub_iff_inSpan basis_et forall₂_et hbi).mpr
      (List.all_eq_true.mp k_g_conj b hb)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [show Nat.card ↥(eSub basis_et) = 64 from by rw [card_eSub]; norm_num,
    show Nat.card ↥((eSub basis_t).map (MulAut.conj gE).toMonoidHom) = 64 from by
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj gE).toMonoidHom)
        (MulAut.conj gE).injective, card_eSub]
      norm_num]

theorem cent_et :
    Subgroup.centralizer (eSub basis_et : Set G₀) = eSub basis_et := by
  rw [← conj_gE_t]
  rw [centralizer_map_conj, cent_t]

theorem lE_mem : lE ∈ Lq := by
  refine mem_conjGenOf_of_sift (Q := lqChain) ?_ c_lq_check ?_
  · rw [lqChain, certificate_originalSubgroup]
    rfl
  · exact k_l_sift

theorem nE_mem : nE ∈ eNorm basis_et :=
  mem_eNorm_of_masksOK basis_et forall₂_et (rep_elt nW) k_n_masks

theorem Nq_le_eNorm_et : Nq ≤ eNorm basis_et :=
  genOf_le_eNorm (by decide) basis_et forall₂_et k_nq_masks

theorem y7_mem_eNorm_et : y7 ∈ eNorm basis_et :=
  mem_eNorm_of_masksOK basis_et forall₂_et (rep_elt y7W) k_y7_masks

theorem mj_mem_eNorm_et :
    ∀ w ∈ mjW, elt w ∈ eNorm basis_et :=
  words_mem_eNorm (by decide) basis_et forall₂_et k_mj_masks

theorem Lq_le_eNorm_et : Lq ≤ eNorm basis_et :=
  conjGenOf_le fun w hw => (eNorm basis_et).mul_mem
    ((eNorm basis_et).mul_mem (mj_mem_eNorm_et w hw) y7_mem_eNorm_et)
    ((eNorm basis_et).inv_mem (mj_mem_eNorm_et w hw))

theorem Lq_le_sectionCent :
    Lq ≤ sectionCent (eSub basis_et) nE_mem := by
  refine conjGenOf_le fun w hw => ⟨?_, ?_⟩
  · exact Lq_le_eNorm_et (Subgroup.subset_closure ⟨w, hw, rfl⟩)
  · set k : Equiv.Perm (Fin 24) :=
      tab (wordG gensG w * wordG gensG y7W * (wordG gensG w)⁻¹) with hk
    have hkgen : k ∈ lqGen := List.mem_map.mpr ⟨w, hw, hk⟩
    have h1 := List.all_eq_true.mp k_n_comm _ hkgen
    rw [Bool.and_eq_true] at h1
    obtain ⟨hinv, hspan⟩ := h1
    have hkrep : Rep 24 (toTable k) ((elt w * y7 * (elt w)⁻¹ : G₀) : Equiv.Perm (Fin 24)) := by
      have hkk : k = ((elt w * y7 * (elt w)⁻¹ : G₀) : Equiv.Perm (Fin 24)) := by
        rw [hk, tab_eq]
        rfl
      rw [hkk]
      exact rep_toTable hn24 _
    have hnrep : Rep 24 nT ((nE : G₀) : Equiv.Perm (Fin 24)) := rep_elt nW
    have hrep : Rep 24 (compT 24 (conjTab 24 (toTable k) (invT 24 (toTable k)) nT)
        (invT 24 nT))
        ((elt w * y7 * (elt w)⁻¹ * nE * (elt w * y7 * (elt w)⁻¹)⁻¹ * nE⁻¹ : G₀) :
          Equiv.Perm (Fin 24)) :=
      Rep.compT (Rep.compT (Rep.compT hkrep hnrep) (Rep.inv_of_invOK hkrep hinv))
        (Rep.inv_of_invOK hnrep k_n_inv)
    exact (mem_eSub_iff_inSpan basis_et forall₂_et hrep).mpr hspan

theorem conj_zE_u6_le :
    (eSub basis_u6).map (MulAut.conj zE).toMonoidHom ≤ eSub basis_et := by
  have hz : Rep 24 zT ((zE : G₀) : Equiv.Perm (Fin 24)) :=
    Rep.compT (rep_elt gW) (Rep.inv_of_invOK (rep_elt d6W) c_d6_inv)
  have hzi : Rep 24 (invT 24 zT) ((zE : G₀) : Equiv.Perm (Fin 24))⁻¹ :=
    Rep.inv_of_invOK hz k_z_inv
  have hforall : List.Forall₂ (Rep 24) (conjAll zT u6T)
      (List.ofFn fun i => ((zE * vU6 i * zE⁻¹ : G₀) : Equiv.Perm (Fin 24))) :=
    forall₂_conjTab forall₂_u6 hz hzi
  rw [← eSub_conj basis_u6 zE, eSub_eq_closure]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨i, rfl⟩
  obtain ⟨b, hb, hbi⟩ := exists_tab_of_mem hforall (List.mem_ofFn.mpr ⟨i, rfl⟩)
  exact (mem_eSub_iff_inSpan basis_et forall₂_et hbi).mpr
    (List.all_eq_true.mp k_six_span b (List.mem_append_left _ hb))

theorem cent_conj_zE_u6 :
    Subgroup.centralizer
      (((eSub basis_u6).map (MulAut.conj zE).toMonoidHom : Subgroup G₀) : Set G₀) =
      eSub basis_et := by
  have hconj : (MulAut.conj zE : MulAut G₀).toMonoidHom.comp
      (MulAut.conj d6 : MulAut G₀).toMonoidHom =
      (MulAut.conj (zE * d6) : MulAut G₀).toMonoidHom := by
    ext x
    rw [MonoidHom.comp_apply,
      show (MulAut.conj zE : MulAut G₀).toMonoidHom
          ((MulAut.conj d6 : MulAut G₀).toMonoidHom x) = MulAut.conj zE (MulAut.conj d6 x)
        from rfl,
      show (MulAut.conj (zE * d6) : MulAut G₀).toMonoidHom x = MulAut.conj (zE * d6) x
        from rfl,
      MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
    group
  have hzd : zE * d6 = gE := by rw [zE]; group
  rw [centralizer_map_conj, cent_u6, Subgroup.map_map, hconj, hzd, ← conj_gE_t]

private def sixV : Fin 6 → G₀ :=
  Fin.append (fun i : Fin 3 => zE * vU6 i * zE⁻¹)
    (fun i : Fin 3 => lE * (zE * vU6 i * zE⁻¹) * lE⁻¹)

private theorem ofFn_sixV :
    (List.ofFn fun i : Fin 6 => ((sixV i : G₀) : Equiv.Perm (Fin 24))) =
      (List.ofFn fun i : Fin 3 => ((zE * vU6 i * zE⁻¹ : G₀) : Equiv.Perm (Fin 24))) ++
      (List.ofFn fun i : Fin 3 => ((lE * (zE * vU6 i * zE⁻¹) * lE⁻¹ : G₀) :
        Equiv.Perm (Fin 24))) := by
  rw [show sixV = Fin.append (fun i : Fin 3 => zE * vU6 i * zE⁻¹)
    (fun i : Fin 3 => lE * (zE * vU6 i * zE⁻¹) * lE⁻¹) from rfl, ← List.ofFn_fin_append]
  congr 1
  funext i
  refine Fin.addCases (m := 3) (n := 3) (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left, Fin.append_left]
  · rw [Fin.append_right, Fin.append_right]

private theorem forall₂_six :
    List.Forall₂ (Rep 24) sixT
      (List.ofFn fun i : Fin 6 => ((sixV i : G₀) : Equiv.Perm (Fin 24))) := by
  have hz : Rep 24 zT ((zE : G₀) : Equiv.Perm (Fin 24)) :=
    Rep.compT (rep_elt gW) (Rep.inv_of_invOK (rep_elt d6W) c_d6_inv)
  have hzi : Rep 24 (invT 24 zT) ((zE : G₀) : Equiv.Perm (Fin 24))⁻¹ :=
    Rep.inv_of_invOK hz k_z_inv
  have hl : Rep 24 lT ((lE : G₀) : Equiv.Perm (Fin 24)) := rep_elt lW
  have hli : Rep 24 (invT 24 lT) ((lE : G₀) : Equiv.Perm (Fin 24))⁻¹ :=
    Rep.inv_of_invOK hl k_l_inv
  have h1 : List.Forall₂ (Rep 24) (conjAll zT u6T)
      (List.ofFn fun i : Fin 3 => ((zE * vU6 i * zE⁻¹ : G₀) : Equiv.Perm (Fin 24))) :=
    forall₂_conjTab forall₂_u6 hz hzi
  have h2 : List.Forall₂ (Rep 24) (conjAll lT (conjAll zT u6T))
      (List.ofFn fun i : Fin 3 => ((lE * (zE * vU6 i * zE⁻¹) * lE⁻¹ : G₀) :
        Equiv.Perm (Fin 24))) :=
    forall₂_conjTab h1 hl hli
  rw [ofFn_sixV, sixT]
  exact forall₂_append h1 h2

private theorem six_basis : EBasis sixV :=
  basis_of_ok forall₂_six k_six_eb

private theorem eSub_six :
    eSub six_basis = (eSub basis_u6).map (MulAut.conj zE).toMonoidHom ⊔
      (eSub basis_u6).map (MulAut.conj (lE * zE)).toMonoidHom := by
  have h1 : (eSub basis_u6).map (MulAut.conj zE).toMonoidHom =
      Subgroup.closure (Set.range fun i : Fin 3 => zE * vU6 i * zE⁻¹) := by
    rw [← eSub_conj basis_u6 zE]
    exact eSub_eq_closure _
  have hr2 : Set.range (fun i : Fin 3 => (lE * zE) * vU6 i * (lE * zE)⁻¹) =
      Set.range (fun i : Fin 3 => lE * (zE * vU6 i * zE⁻¹) * lE⁻¹) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, by group⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, by group⟩
  have h2 : (eSub basis_u6).map (MulAut.conj (lE * zE)).toMonoidHom =
      Subgroup.closure (Set.range fun i : Fin 3 => lE * (zE * vU6 i * zE⁻¹) * lE⁻¹) := by
    rw [← eSub_conj basis_u6 (lE * zE), eSub_eq_closure, hr2]
  have hsix : eSub six_basis =
      Subgroup.closure (Set.range fun i : Fin 3 => zE * vU6 i * zE⁻¹) ⊔
      Subgroup.closure (Set.range fun i : Fin 3 => lE * (zE * vU6 i * zE⁻¹) * lE⁻¹) := by
    rw [eSub_eq_closure]
    rw [show sixV = Fin.append (fun i : Fin 3 => zE * vU6 i * zE⁻¹)
      (fun i : Fin 3 => lE * (zE * vU6 i * zE⁻¹) * lE⁻¹) from rfl,
      closure_range_fin_append]
  rw [hsix, ← h1, ← h2]

theorem sup_six_eq_et :
    (eSub basis_u6).map (MulAut.conj zE).toMonoidHom ⊔
      (eSub basis_u6).map (MulAut.conj (lE * zE)).toMonoidHom = eSub basis_et := by
  have hle : (eSub basis_u6).map (MulAut.conj zE).toMonoidHom ⊔
      (eSub basis_u6).map (MulAut.conj (lE * zE)).toMonoidHom ≤ eSub basis_et := by
    refine sup_le conj_zE_u6_le ?_
    have he : (eSub basis_u6).map (MulAut.conj (lE * zE)).toMonoidHom =
        ((eSub basis_u6).map (MulAut.conj zE).toMonoidHom).map
          (MulAut.conj lE).toMonoidHom := by
      rw [show (MulAut.conj (lE * zE) : MulAut G₀).toMonoidHom =
          (MulAut.conj lE : MulAut G₀).toMonoidHom.comp
            (MulAut.conj zE : MulAut G₀).toMonoidHom from ?_]
      · rw [Subgroup.map_map]
      · ext x
        rw [MonoidHom.comp_apply,
          show (MulAut.conj lE : MulAut G₀).toMonoidHom
              ((MulAut.conj zE : MulAut G₀).toMonoidHom x) = MulAut.conj lE (MulAut.conj zE x)
            from rfl,
          show (MulAut.conj (lE * zE) : MulAut G₀).toMonoidHom x = MulAut.conj (lE * zE) x
            from rfl,
          MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
        group
    have hlE : lE ∈ eNorm basis_et := Lq_le_eNorm_et lE_mem
    have hmap : (eSub basis_et).map (MulAut.conj lE).toMonoidHom = eSub basis_et :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hlE
    rw [he]
    exact (Subgroup.map_mono conj_zE_u6_le).trans (le_of_eq hmap)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [← eSub_six]
  rw [show Nat.card ↥(eSub basis_et) = 64 from by rw [card_eSub]; norm_num,
    show Nat.card ↥(eSub six_basis) = 64 from by rw [card_eSub]; norm_num]

theorem orderOf_xE : orderOf xE = 7 :=
  orderOf_elt (q := 7) (by norm_num) k_x_ord

theorem xE_mem_CB0 :
    xE ∈ CB0 := by
  rw [CB0, Subgroup.mem_comap, ← centralizerIn_b0, mem_centralizerIn]
  exact ⟨xE.2, (commT_iff rep_b0 (rep_elt xW)).mp k_x_comm |>.symm⟩

theorem cj_mem_CB0 :
    ∀ w ∈ cjW, elt w ∈ CB0 := by
  intro w hw
  have hT : wordT 24 gensT w ∈ cjT := by
    simp only [cjT, List.mem_map]
    exact ⟨w, hw, rfl⟩
  have hc := List.all_eq_true.mp k_cj_comm _ hT
  rw [CB0, Subgroup.mem_comap, ← centralizerIn_b0, mem_centralizerIn]
  exact ⟨(elt w).2, (commT_iff rep_b0 (rep_elt w)).mp hc |>.symm⟩

theorem conjGenOf_cj :
    conjGenOf cjW xW = CB0 := by
  have hle : conjGenOf cjW xW ≤ CB0 :=
    conjGenOf_le fun w hw => CB0.mul_mem (CB0.mul_mem (cj_mem_CB0 w hw) xE_mem_CB0)
      (CB0.inv_mem (cj_mem_CB0 w hw))
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_CB0, card_conjGenOf (Q := cbChain) ?_ k_cb_check, k_cb_order]
  rw [cbChain, certificate_originalSubgroup]
  rfl

theorem u5_le_et : eSub basis_u5 ≤ eSub basis_et := by
  rw [eSub_eq_closure basis_u5]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨i, rfl⟩
  obtain ⟨b, hb, hbi⟩ := exists_tab_of_mem forall₂_u5 (List.mem_ofFn.mpr ⟨i, rfl⟩)
  exact (mem_eSub_iff_inSpan basis_et forall₂_et hbi).mpr
    (List.all_eq_true.mp k_u5_span b hb)

@[expose] def u5nV : Fin 6 → G₀ :=
  Fin.append vU5 (fun i : Fin 3 => nE * vU5 i * nE⁻¹)

private theorem ofFn_u5nV :
    (List.ofFn fun i : Fin 6 => ((u5nV i : G₀) : Equiv.Perm (Fin 24))) =
      (List.ofFn fun i : Fin 3 => ((vU5 i : G₀) : Equiv.Perm (Fin 24))) ++
      (List.ofFn fun i : Fin 3 => ((nE * vU5 i * nE⁻¹ : G₀) : Equiv.Perm (Fin 24))) := by
  rw [show u5nV = Fin.append vU5 (fun i : Fin 3 => nE * vU5 i * nE⁻¹) from rfl,
    ← List.ofFn_fin_append]
  congr 1
  funext i
  refine Fin.addCases (m := 3) (n := 3) (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left, Fin.append_left]
  · rw [Fin.append_right, Fin.append_right]

private theorem forall₂_u5nV :
    List.Forall₂ (Rep 24) (u5T ++ conjAll nT u5T)
      (List.ofFn fun i : Fin 6 => ((u5nV i : G₀) : Equiv.Perm (Fin 24))) := by
  have hn : Rep 24 nT ((nE : G₀) : Equiv.Perm (Fin 24)) := rep_elt nW
  have hni : Rep 24 (invT 24 nT) ((nE : G₀) : Equiv.Perm (Fin 24))⁻¹ :=
    Rep.inv_of_invOK hn k_n_inv
  have h1 : List.Forall₂ (Rep 24) u5T
      (List.ofFn fun i : Fin 3 => ((vU5 i : G₀) : Equiv.Perm (Fin 24))) := forall₂_u5
  have h2 : List.Forall₂ (Rep 24) (conjAll nT u5T)
      (List.ofFn fun i : Fin 3 => ((nE * vU5 i * nE⁻¹ : G₀) : Equiv.Perm (Fin 24))) :=
    forall₂_conjTab forall₂_u5 hn hni
  rw [ofFn_u5nV]
  exact forall₂_append h1 h2

theorem u5n_basis : EBasis u5nV :=
  basis_of_ok forall₂_u5nV k_n_eb

private theorem eSub_u5n :
    eSub u5n_basis = eSub basis_u5 ⊔ (eSub basis_u5).map (MulAut.conj nE).toMonoidHom := by
  have h2 : (eSub basis_u5).map (MulAut.conj nE).toMonoidHom =
      Subgroup.closure (Set.range fun i : Fin 3 => nE * vU5 i * nE⁻¹) := by
    rw [← eSub_conj basis_u5 nE]
    exact eSub_eq_closure _
  have hu : eSub basis_u5 = Subgroup.closure (Set.range vU5) := eSub_eq_closure basis_u5
  have hu5n : eSub u5n_basis =
      Subgroup.closure (Set.range vU5) ⊔
        Subgroup.closure (Set.range fun i : Fin 3 => nE * vU5 i * nE⁻¹) := by
    rw [eSub_eq_closure]
    rw [show u5nV = Fin.append vU5 (fun i : Fin 3 => nE * vU5 i * nE⁻¹) from rfl,
      closure_range_fin_append]
  rw [hu5n, ← hu, ← h2]

theorem u5_sup_conj_nE :
    eSub basis_u5 ⊔ (eSub basis_u5).map (MulAut.conj nE).toMonoidHom = eSub basis_et := by
  have hle : eSub basis_u5 ⊔ (eSub basis_u5).map (MulAut.conj nE).toMonoidHom ≤
      eSub basis_et := by
    refine sup_le u5_le_et ?_
    rw [← Subgroup.mem_normalizer_iff_map_conj_eq.mp nE_mem]
    exact Subgroup.map_mono u5_le_et
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [← eSub_u5n]
  rw [show Nat.card ↥(eSub basis_et) = 64 from by rw [card_eSub]; norm_num,
    show Nat.card ↥(eSub u5n_basis) = 64 from by rw [card_eSub]; norm_num]

theorem eSub_u5n_basis :
    eSub u5n_basis = eSub basis_et := by
  rw [eSub_u5n, u5_sup_conj_nE]

theorem eElt_u5nV (c₁ c₂ : Fin 3 → ZMod 2) :
    eElt u5nV (Fin.append c₁ c₂) = eElt vU5 c₁ * eElt (fun i : Fin 3 => nE * vU5 i * nE⁻¹) c₂ :=
  eElt_fin_append _ _ c₁ c₂

private theorem eElt_u5nV_left (c : Fin 3 → ZMod 2) :
    eElt u5nV (Fin.append c (0 : Fin 3 → ZMod 2)) = eElt vU5 c := by
  rw [show u5nV = Fin.append vU5 (fun i : Fin 3 => nE * vU5 i * nE⁻¹) from rfl,
    eElt_fin_append, eElt_zero, mul_one]

private theorem eElt_u5nV_right (c : Fin 3 → ZMod 2) :
    eElt u5nV (Fin.append (0 : Fin 3 → ZMod 2) c) =
      eElt (fun i : Fin 3 => nE * vU5 i * nE⁻¹) c := by
  rw [show u5nV = Fin.append vU5 (fun i : Fin 3 => nE * vU5 i * nE⁻¹) from rfl,
    eElt_fin_append, eElt_zero, one_mul]

theorem u5_inf_conj_nE :
    eSub basis_u5 ⊓ (eSub basis_u5).map (MulAut.conj nE).toMonoidHom = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  rw [← eSub_conj basis_u5 nE] at hx2
  obtain ⟨c₁, hc₁⟩ := (mem_eSub_iff basis_u5 x).mp hx1
  obtain ⟨c₂, hc₂⟩ := (mem_eSub_iff (basis_conj basis_u5 nE) x).mp hx2
  have h1 : eElt u5nV (Fin.append c₁ (0 : Fin 3 → ZMod 2)) = x := by
    rw [eElt_u5nV_left, hc₁]
  have h2 : eElt u5nV (Fin.append (0 : Fin 3 → ZMod 2) c₂) = x := by
    rw [eElt_u5nV_right]; exact hc₂
  have heq : Fin.append c₁ (0 : Fin 3 → ZMod 2) = Fin.append (0 : Fin 3 → ZMod 2) c₂ :=
    eElt_injective u5n_basis (by rw [h1, h2])
  have hc0 : c₁ = 0 := by
    funext i
    have h := congrFun heq (Fin.castAdd 3 i)
    simpa [Fin.append_left] using h
  rw [← hc₁, hc0, eElt_zero]

theorem nE_not_mem_Nq : nE ∉ Nq := by
  intro h
  have hmap : (eSub basis_u5).map (MulAut.conj nE).toMonoidHom = eSub basis_u5 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Nq_le h)
  have hbot : eSub basis_u5 = ⊥ := by
    have h' := u5_inf_conj_nE
    rw [hmap, inf_idem] at h'
    exact h'
  have hc : Nat.card ↥(eSub basis_u5) = 1 := by rw [hbot, Subgroup.card_bot]
  rw [card_eSub] at hc
  norm_num at hc

private theorem m24Mems_order (m : CFSG.QuasithinUnique.Ch1.SporLat.Mem)
    (hm : m ∈ CFSG.QuasithinUnique.Ch1.SporLat.M24.m24Mems) (h1 : 21504 ∣ m.order)
    (h2 : 64 ≤ m.o2) (h3 : m.order ≠ 21504) : m.order = 64512 := by
  simp only [CFSG.QuasithinUnique.Ch1.SporLat.M24.m24Mems, List.mem_cons, List.not_mem_nil,
    or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (revert h1 h2 h3; decide)

theorem card_eNorm_et :
    Nat.card (eNorm basis_et) = 64512 := by
  have hE2 : IsPGroup 2 ↥(eSub basis_et) :=
    IsPGroup.of_card (n := 6) (by rw [card_eSub])
  have hcore : eSub basis_et ≤ CFSG.Open.pCoreOf 2 (eNorm basis_et) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer
      (le_refl (eNorm basis_et)) hE2
  have hge : 64 ≤ Nat.card ↥(CFSG.Open.pCoreOf 2 (eNorm basis_et)) := by
    have h := Subgroup.card_le_of_le hcore
    rwa [show Nat.card ↥(eSub basis_et) = 64 from by rw [card_eSub]; norm_num] at h
  have hdvd : 21504 ∣ Nat.card ↥(eNorm basis_et) := by
    rw [← card_Nq]
    exact Subgroup.card_dvd_of_le Nq_le_eNorm_et
  have hne : Nat.card ↥(eNorm basis_et) ≠ 21504 := by
    intro hc
    have heq : eNorm basis_et = Nq :=
      (Subgroup.eq_of_le_of_card_ge Nq_le_eNorm_et (by rw [hc, card_Nq])).symm
    exact nE_not_mem_Nq (heq ▸ nE_mem)
  haveI : IsSimpleGroup G₀ := CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  have hR1 : eSub basis_et ≠ ⊥ := by
    intro h
    have hc := card_eSub (h := basis_et)
    rw [h, Subgroup.card_bot] at hc
    norm_num at hc
  have hRt : eSub basis_et ≠ ⊤ := by
    intro h
    have hc := card_eSub (h := basis_et)
    rw [h, Subgroup.card_top, m24_card] at hc
    norm_num at hc
  have hY : eNorm basis_et ≠ ⊤ := normalizer_ne_top hR1 hRt
  have h1024 : 1024 ∣ Nat.card ↥(eNorm basis_et) :=
    Nat.dvd_trans (by norm_num) hdvd
  obtain ⟨T, hT, hTY⟩ := exists_sylow_le (A := G₀) m24_card (X := eNorm basis_et) h1024
  rcases CFSG.QuasithinUnique.Ch1.SporLat.M24.m24_overgroups (X := G₀) ⟨MulEquiv.refl G₀⟩ hT hTY
    with htop | ⟨m, hm, hord, ho2, -⟩
  · exact absurd htop hY
  have hdvd' : 21504 ∣ m.order := by rw [← hord]; exact hdvd
  have hge' : 64 ≤ m.o2 := by rw [← ho2]; exact hge
  have hne' : m.order ≠ 21504 := by rw [← hord]; exact hne
  exact hord.trans (m24Mems_order m hm hdvd' hge' hne')

theorem relIndex_Nq_eNorm_et :
    Nq.relIndex (eNorm basis_et) = 3 := by
  have h := Subgroup.relIndex_mul_card Nq (eNorm basis_et)
  rw [inf_eq_left.mpr Nq_le_eNorm_et, card_Nq, card_eNorm_et] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h.trans (by norm_num))

end CFSG.SectionRank.QTK.Insp443.M24

end
