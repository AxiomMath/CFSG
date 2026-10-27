module

public import CFSG.ClassicalInvolution.RouteD.TypeCLayers

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane
  isHyperbolicPlane_stdPlane longBlock planeTorus longInv suppGroup coords pairPlanes form)
open scoped MatrixGroups commutatorElement

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {z : G}

section LL

theorem perfect_subgroupOf {H : Type*} [Group H] {Y A : Subgroup H} (hA : A ≤ Y)
    (hAp : A ≤ ⁅A, A⁆) : A.subgroupOf Y ≤ ⁅A.subgroupOf Y, A.subgroupOf Y⁆ := by
  apply (Subgroup.map_le_map_iff_of_injective Y.subtype_injective).mp
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA]
  exact hAp

theorem isPerfect_subgroupOf {H : Type*} [Group H] {Y A : Subgroup H} (hA : A ≤ Y)
    (hAp : A ≤ ⁅A, A⁆) : Group.IsPerfect ↥(A.subgroupOf Y) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => ?_)
    (perfect_subgroupOf hA hAp)
  rw [commutatorElement_def]
  exact (A.subgroupOf Y).mul_mem ((A.subgroupOf Y).mul_mem ((A.subgroupOf Y).mul_mem h₁ h₂)
    ((A.subgroupOf Y).inv_mem h₁)) ((A.subgroupOf Y).inv_mem h₂)

theorem commutes_of_commutes_locImg_perfect {x : G} (hP1 : LocalOddCentral Ω {x})
    {A B : Subgroup G} (hA : A ≤ locLayer Ω x) (hB : B ≤ locLayer Ω x) (hAp : A ≤ ⁅A, A⁆)
    (h : Commutes (locImg Ω x A) (locImg Ω x B)) : Commutes A B := by
  have hperf := isPerfect_subgroupOf hA hAp
  have := commutes_of_commutes_oddQuotient hP1 hperf (L := B.subgroupOf (locLayer Ω x)) h
  intro a ha b hb
  exact congrArg Subtype.val (this ⟨a, hA ha⟩ (Subgroup.mem_subgroupOf.mpr ha) ⟨b, hB hb⟩
    (Subgroup.mem_subgroupOf.mpr hb))

theorem commutes_elem_of_commutes_locImg {x : G} (hΩ : InClass p f Ω) (hP1 : LocalOddCentral Ω {x})
    {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x}) {y : G} (hy : y ∈ locLayer Ω x)
    (h : ∀ w ∈ locImg Ω x L, w * QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x))
      ⟨y, hy⟩ = QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨y, hy⟩ * w) :
    ∀ a ∈ L, a * y = y * a := by
  obtain ⟨z', hz'⟩ := hΩ.classical L hL.1
  have hperf := (hz'.subgroupOf p f (le_centralizingLayer hL)).perfect
  have hc : Commutes (L.subgroupOf (locLayer Ω x))
      (Subgroup.zpowers (⟨y, hy⟩ : ↥(locLayer Ω x))) := by
    refine commutes_of_commutes_oddQuotient hP1 hperf ?_
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have h1 := h _ ⟨u, hu, rfl⟩
    rw [map_zpow]
    exact (Commute.zpow_right (show Commute (QuotientGroup.mk' _ u)
      (QuotientGroup.mk' _ ⟨y, hy⟩) from h1) n).eq
  intro a ha
  exact congrArg Subtype.val (hc ⟨a, le_centralizingLayer hL ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
    ⟨y, hy⟩ (Subgroup.mem_zpowers _))

end LL

section Components

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem range_commute_of_ne (D : LieSystemData p f X Φ) {c c' : Fin D.card} (h : c ≠ c') :
    Commutes (D.hom c).range (D.hom c').range := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact D.commute c c' h a b

theorem range_inf_le_center (D : LieSystemData p f X Φ) {c c' : Fin D.card} (h : c ≠ c') :
    (D.hom c).range ⊓ (D.hom c').range ≤ Subgroup.center X := by
  rintro x ⟨hxi, hxj⟩
  have key : ∀ k, (D.hom k).range ≤ Subgroup.centralizer ({x} : Set X) := by
    intro k y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases hki : k = c
    · subst hki
      exact range_commute_of_ne D h y hy x hxj
    · exact range_commute_of_ne D hki y hy x hxi
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ (⨆ k, (D.hom k).range : Subgroup X) := by rw [D.generate]; trivial
  exact Subgroup.mem_centralizer_singleton_iff.mp ((iSup_le key) hg)

theorem exists_range_of_mem (D : LieSystemData p f X Φ) {L : Subgroup X} (hL : L ∈ Φ) :
    ∃ c, L ≤ (D.hom c).range := by
  obtain ⟨c, R, -, rfl⟩ := D.fundamental L hL
  exact ⟨c, Subgroup.map_le_range _ _⟩

theorem exists_fundamental_of_le_range (D : LieSystemData p f X Φ) {L : Subgroup X} (hL : L ∈ Φ)
    {c : Fin D.card} (hc : L ≤ (D.hom c).range) (hnc : ¬ L ≤ Subgroup.center X) :
    ∃ R ∈ fundamentalSubgroups (D.tag c)
      (modelUniv (D.tag c) (D.rank c) p (D.exp c) Fact.out).D, L = R.map (D.hom c) := by
  obtain ⟨c', R, hR, hLR⟩ := D.fundamental L hL
  by_cases hcc : c' = c
  · subst hcc
    exact ⟨R, hR, hLR⟩
  · exfalso
    apply hnc
    have h1 := range_inf_le_center D hcc
    refine le_trans (le_inf ?_ hc) h1
    rw [hLR]
    exact Subgroup.map_le_range _ _

end Components

section FrameFacts

variable [Finite G]

theorem exists_local_pair (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z) {i j : Fin (m + 1)}
    (hij : i ≠ j) : ∃ (l : Fin (m + 1)) (a b : Fin m), a ≠ b ∧ l.succAbove a = i ∧
      l.succAbove b = j ∧ Nonempty (LocalFrame Fr l) := by
  obtain ⟨l, hli, hlj⟩ := Models.SymplecticPairs.exists_ne_ne
    (show 3 ≤ m + 1 by have := S.three; omega) i j
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq (Ne.symm hli)
  obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq (Ne.symm hlj)
  refine ⟨l, a, b, ?_, ha, hb, exists_localFrame S Fr l⟩
  rintro rfl
  exact hij (ha.symm.trans hb)

theorem commutator_le_center_of_commutes_map {F : Type} [Field F] {n : ℕ} {X : Type*} [Group X]
    (ψ : StatedSp n F →* X) (hψ : ψ.ker ≤ Subgroup.center (StatedSp n F))
    {A B : Subgroup (StatedSp n F)} (h : Commutes (A.map ψ) (B.map ψ)) :
    ⁅A, B⁆ ≤ Subgroup.center (StatedSp n F) := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  apply hψ
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, mul_inv_eq_one,
    mul_inv_eq_iff_eq_mul]
  exact h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩

theorem longInv_mul_self (F : Type) [Field F] (n : ℕ) (k : Fin n) :
    longInv F n k * longInv F n k = 1 := by
  rw [longInv, ← map_mul]
  simp

theorem Frame.zf_ne (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z) {i j : Fin (m + 1)}
    (hij : i ≠ j) : Fr.zf i ≠ Fr.zf j := by
  obtain ⟨l, a, b, hab, rfl, rfl, ⟨LF⟩⟩ := exists_local_pair S Fr hij
  intro h
  have h1 := LF.mk_zf S a
  have h2 := LF.mk_zf S b
  have e : (⟨Fr.zf (l.succAbove a), Fr.Kf_le_locLayer S _ l (Frame.zf_mem S _)⟩ :
      ↥(locLayer Ω (Fr.zf l))) =
      ⟨Fr.zf (l.succAbove b), Fr.Kf_le_locLayer S _ l (Frame.zf_mem S _)⟩ := Subtype.ext h
  rw [e, h2] at h1
  have hc : longInv (GaloisField p f) m a * longInv (GaloisField p f) m b ∈
      Subgroup.center (StatedSp m (GaloisField p f)) := by
    apply LF.d.ker_le
    rw [MonoidHom.mem_ker, map_mul, ← h1, ← map_mul, longInv_mul_self, map_one]
  refine Models.SymplecticPairs.not_forall_commutator_longInv_mul_mem_center S.two_ne_zero
    S.four_le S.three hab fun g => ?_
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hc g).symm]
  exact Subgroup.one_mem _

theorem exists_noncommuting_member (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z)
    {i j : Fin (m + 1)} (hij : i ≠ j) :
    ∃ L₀ ∈ memberSet Fr i j, ¬ Commutes L₀ (Fr.Kf i) ∧ ¬ Commutes L₀ (Fr.Kf j) := by
  obtain ⟨l, a, b, hab, rfl, rfl, ⟨LF⟩⟩ := exists_local_pair S Fr hij
  obtain ⟨H, hH, h1, h2⟩ := Models.SymplecticPairs.exists_pair_plane_not_commute S.two_ne_zero
    S.hex S.two_le hab
  obtain ⟨L, hL, hLH⟩ := LF.exists_mem_of_plane S hab hH
  refine ⟨L, hL, fun hc => h1 ?_, fun hc => h2 ?_⟩
  · have := commutes_locImg_of_commutes (Ω := Ω) (x := Fr.zf l) hc
    rw [hLH, LF.locImg_Kf a] at this
    exact commutator_le_center_of_commutes_map LF.d.ψ LF.d.ker_le this
  · have := commutes_locImg_of_commutes (Ω := Ω) (x := Fr.zf l) hc
    rw [hLH, LF.locImg_Kf b] at this
    exact commutator_le_center_of_commutes_map LF.d.ψ LF.d.ker_le this

theorem not_commutes_both (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z) {i j : Fin (m + 1)}
    (hij : i ≠ j) {L : Subgroup G} (hL : L ∈ memberSet Fr i j) :
    ¬ (Commutes L (Fr.Kf i) ∧ Commutes L (Fr.Kf j)) := by
  obtain ⟨l, a, b, hab, rfl, rfl, ⟨LF⟩⟩ := exists_local_pair S Fr hij
  rintro ⟨hLi, hLj⟩
  obtain ⟨P, hP, hLP⟩ := LF.exists_plane_of_mem S hab hL
  have hcent := LocalFrame.mem_cent_of_mem S hL
  exact false_of_pairPlane_orth hab hP.1 hP.2 (LF.orth_of_commutes S hP.1 hcent hLP hLi)
    (LF.orth_of_commutes S hP.1 hcent hLP hLj)

theorem memberSet_subset_cent (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z)
    {i j : Fin (m + 1)} (hij : i ≠ j) {L : Subgroup G} (hL : L ∈ memberSet Fr i j) :
    L ∈ centralizingMembers Ω {Fr.zf i * Fr.zf j} := by
  obtain ⟨l, a, b, hab, rfl, rfl, ⟨LF⟩⟩ := exists_local_pair S Fr hij
  obtain ⟨P, hP, hLP⟩ := LF.exists_plane_of_mem S hab hL
  have hcent := LocalFrame.mem_cent_of_mem S hL
  have hxY : Fr.zf (l.succAbove a) * Fr.zf (l.succAbove b) ∈ locLayer Ω (Fr.zf l) :=
    (locLayer Ω (Fr.zf l)).mul_mem (Fr.Kf_le_locLayer S _ l (Frame.zf_mem S _))
      (Fr.Kf_le_locLayer S _ l (Frame.zf_mem S _))
  refine ⟨hL.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  refine commutes_elem_of_commutes_locImg S.inClass (Fr.p1 S l) hcent hxY ?_ y hy
  intro w hw
  have hmk : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω (Fr.zf l)))
      ⟨Fr.zf (l.succAbove a) * Fr.zf (l.succAbove b), hxY⟩ =
      LF.d.ψ (longInv (GaloisField p f) m a * longInv (GaloisField p f) m b) := by
    rw [map_mul, ← LF.mk_zf S a, ← LF.mk_zf S b, ← map_mul]
    rfl
  rw [hmk]
  rw [hLP] at hw
  obtain ⟨s, hs, rfl⟩ := hw
  have hs' : s ∈ suppGroup (coords a ∪ coords b) :=
    Models.SymplecticPairs.planeGroup_le_suppGroup_pair hab hP.2 hs
  rw [← map_mul, ← map_mul]
  congr 1
  exact (Models.SymplecticPairs.commute_longInv_mul_longInv hab hs').eq.symm

end FrameFacts

section RankTwo

theorem ker_comp_conj_le_center {F : Type} [Field F] {n : ℕ} {X : Type*} [Group X]
    (ν : StatedSp n F →* X) (hν : ν.ker ≤ Subgroup.center (StatedSp n F)) (g : StatedSp n F) :
    (ν.comp (MulAut.conj g).toMonoidHom).ker ≤ Subgroup.center (StatedSp n F) := by
  intro x hx
  refine Models.SymplecticPairs.mem_center_of_conj_mem_center (g := g) ?_
  have hx' : ν (g * x * g⁻¹) = 1 := MonoidHom.mem_ker.mp hx
  exact hν (MonoidHom.mem_ker.mpr hx')

theorem eq_two_of_central_involutions {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (h4 : 4 ≤ Nat.card F) {r : ℕ} (hr : 2 ≤ r) {X : Type*} [Group X] (ν : StatedSp r F →* X)
    (hν : ν.ker ≤ Subgroup.center (StatedSp r F)) {Pa Pb : Submodule F (Fin r ⊕ Fin r → F)}
    (hPa : IsHyperbolicPlane Pa) (hPb : IsHyperbolicPlane Pb)
    (horth : ∀ x ∈ Pa, ∀ y ∈ Pb, form x y = 0) (βa βb : SL(2, F) →* X)
    (hβa : Function.Injective βa) (hβb : Function.Injective βb)
    (hra : βa.range = (planeGroup Pa).map ν) (hrb : βb.range = (planeGroup Pb).map ν)
    (hc : βa (-1) * βb (-1) ∈ Subgroup.center X) : r = 2 := by
  obtain ⟨u₁, w₁, h₁, rfl⟩ := hPa
  obtain ⟨u₂, w₂, h₂, rfl⟩ := hPb
  have hs : ∀ x ∈ (Submodule.span F {u₁, w₁} : Submodule F (Fin r ⊕ Fin r → F)), ∀ y ∈
      (Submodule.span F {u₂, w₂} : Submodule F (Fin r ⊕ Fin r → F)), form x y = 0 := horth
  have o₁ : form u₁ u₂ = 0 := hs _ (Submodule.subset_span (by simp)) _
    (Submodule.subset_span (by simp))
  have o₂ : form u₁ w₂ = 0 := hs _ (Submodule.subset_span (by simp)) _
    (Submodule.subset_span (by simp))
  have o₃ : form w₁ u₂ = 0 := hs _ (Submodule.subset_span (by simp)) _
    (Submodule.subset_span (by simp))
  have o₄ : form w₁ w₂ = 0 := hs _ (Submodule.subset_span (by simp)) _
    (Submodule.subset_span (by simp))
  have hk01 : (⟨0, by omega⟩ : Fin r) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  obtain ⟨g, hg1, hg2, hg3, hg4⟩ := Models.SymplecticPairs.exists_sp_apply_eq_two_at hk01
    u₁ w₁ u₂ w₂ h₁ h₂ o₁ o₂ o₃ o₄
  have e1 : planeGroup (Submodule.span F {u₁, w₁}) =
      (longBlock F r ⟨0, by omega⟩).range.map (MulAut.conj g).toMonoidHom := by
    rw [← hg1, ← hg2, Models.SymplecticPairs.planeGroup_span_conj]
    exact congrArg _ (Models.SymplecticPairs.planeGroup_stdPlane _)
  have e2 : planeGroup (Submodule.span F {u₂, w₂}) =
      (longBlock F r ⟨1, by omega⟩).range.map (MulAut.conj g).toMonoidHom := by
    rw [← hg3, ← hg4, Models.SymplecticPairs.planeGroup_span_conj]
    exact congrArg _ (Models.SymplecticPairs.planeGroup_stdPlane _)
  have hker := ker_comp_conj_le_center ν hν g
  have ha := map_neg_one_eq_of_range_eq hr h2 (ν.comp (MulAut.conj g).toMonoidHom) hker
    ⟨0, by omega⟩ βa hβa (by rw [hra, e1, Subgroup.map_map])
  have hb := map_neg_one_eq_of_range_eq hr h2 (ν.comp (MulAut.conj g).toMonoidHom) hker
    ⟨1, by omega⟩ βb hβb (by rw [hrb, e2, Subgroup.map_map])
  refine Models.SymplecticPairs.eq_two_of_central_image h2 h4 hr ν hν g hk01 ?_
  have : ν (g * (longInv F r ⟨0, by omega⟩ * longInv F r ⟨1, by omega⟩) * g⁻¹) =
      βa (-1) * βb (-1) := by
    rw [ha, hb, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul]
    congr 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [this]
  exact hc

end RankTwo

section Involution

theorem Frame.zf_sq (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z) (i : Fin (m + 1)) :
    Fr.zf i * Fr.zf i = 1 := by
  rw [← sq, ← (Fr.cls S i).orderOf_eq_two]
  exact pow_orderOf_eq_one _

theorem Frame.orderOf_zf_mul [Finite G] (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z)
    {i j : Fin (m + 1)} (hij : i ≠ j) : orderOf (Fr.zf i * Fr.zf j) = 2 := by
  have hcomm : Commute (Fr.zf j) (Fr.zf i) := (Fr.zf_comm S j i)
  refine orderOf_eq_prime ?_ ?_
  · rw [sq, hcomm.mul_mul_mul_comm, Fr.zf_sq S, Fr.zf_sq S, mul_one]
  · intro h
    apply Fr.zf_ne S hij
    have h1 : Fr.zf i = (Fr.zf j)⁻¹ := mul_eq_one_iff_eq_inv.mp h
    rw [h1]
    exact inv_eq_of_mul_eq_one_right (Fr.zf_sq S j)

theorem commute_zf_mul {Fr : Frame p f m Ω K z} {i j : Fin (m + 1)} {y : G}
    (hi : y * Fr.zf i = Fr.zf i * y) (hj : y * Fr.zf j = Fr.zf j * y) :
    y * (Fr.zf i * Fr.zf j) = (Fr.zf i * Fr.zf j) * y := by
  rw [← mul_assoc, hi, mul_assoc, hj, mul_assoc]

theorem Frame.Kf_mem_cent_mul (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z)
    (i j k : Fin (m + 1)) :
    Fr.Kf k ∈ centralizingMembers Ω {Fr.zf i * Fr.zf j} :=
  ⟨Fr.mem k, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
    (commute_zf_mul (Fr.commute_zf S k i y hy) (Fr.commute_zf S k j y hy))⟩

theorem mem_cent_mul_of_commutes (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z)
    {i j : Fin (m + 1)} {L : Subgroup G} (hL : L ∈ Ω) (hLi : Commutes L (Fr.Kf i))
    (hLj : Commutes L (Fr.Kf j)) : L ∈ centralizingMembers Ω {Fr.zf i * Fr.zf j} :=
  ⟨hL, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
    (commute_zf_mul (hLi y hy _ (Frame.zf_mem S i)) (hLj y hy _ (Frame.zf_mem S j)))⟩

end Involution

section BlockMain

variable [Finite G]

theorem same_comp_of_not_commutes (hΩ : InClass p f Ω) {x : G} (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) {L₁ L₂ : Subgroup G}
    (h₁ : L₁ ∈ centralizingMembers Ω {x}) (h₂ : L₂ ∈ centralizingMembers Ω {x})
    (hn : ¬ Commutes L₁ L₂) {c₁ c₂ : Fin D.card} (hc₁ : locImg Ω x L₁ ≤ (D.hom c₁).range)
    (hc₂ : locImg Ω x L₂ ≤ (D.hom c₂).range) : c₁ = c₂ := by
  by_contra hne
  apply hn
  refine commutes_of_commutes_locImg hΩ hP1 h₁ h₂ ?_
  intro a ha b hb
  exact range_commute_of_ne D hne a (hc₁ ha) b (hc₂ hb)

theorem exists_comp_of_pair (S : CSetup p f m Ω K z) (hP1 : AllLocalOddCentral Ω)
    (Fr : Frame p f m Ω K z) {i j : Fin (m + 1)} (hij : i ≠ j)
    (D : LieSystemData p f (locQuot Ω (Fr.zf i * Fr.zf j)) (locFamily Ω (Fr.zf i * Fr.zf j))) :
    ∃ c : Fin D.card, locImg Ω (Fr.zf i * Fr.zf j) (Fr.Kf i) ≤ (D.hom c).range ∧
      locImg Ω (Fr.zf i * Fr.zf j) (Fr.Kf j) ≤ (D.hom c).range := by
  have hP1x := hP1 _ (Fr.orderOf_zf_mul S hij)
  have hKi := Fr.Kf_mem_cent_mul S i j i
  have hKj := Fr.Kf_mem_cent_mul S i j j
  obtain ⟨c, hc⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨_, hKi, rfl⟩)
  obtain ⟨cj, hcj⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨_, hKj, rfl⟩)
  obtain ⟨L₀, hL₀, hn1, hn2⟩ := exists_noncommuting_member S Fr hij
  have hL₀x := memberSet_subset_cent S Fr hij hL₀
  obtain ⟨c₀, hc₀⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨_, hL₀x, rfl⟩)
  have e1 : c₀ = c := same_comp_of_not_commutes S.inClass hP1x D hL₀x hKi hn1 hc₀ hc
  have e2 : c₀ = cj := same_comp_of_not_commutes S.inClass hP1x D hL₀x hKj hn2 hc₀ hcj
  have e3 : cj = c := e2.symm.trans e1
  rw [e3] at hcj
  exact ⟨c, hc, hcj⟩

theorem tag_eq_psp (S : CSetup p f m Ω K z) (hP1 : AllLocalOddCentral Ω)
    (hNO : NoOtherComponents p f Ω) (Fr : Frame p f m Ω K z) {i j : Fin (m + 1)}
    (hij : i ≠ j)
    (D : LieSystemData p f (locQuot Ω (Fr.zf i * Fr.zf j)) (locFamily Ω (Fr.zf i * Fr.zf j)))
    {c : Fin D.card} (hci : locImg Ω (Fr.zf i * Fr.zf j) (Fr.Kf i) ≤ (D.hom c).range)
    (hcj : locImg Ω (Fr.zf i * Fr.zf j) (Fr.Kf j) ≤ (D.hom c).range) : D.tag c = .PSp := by
  have hxord := Fr.orderOf_zf_mul S hij
  have hP1x := hP1 _ hxord
  have hKi := Fr.Kf_mem_cent_mul S i j i
  have hKj := Fr.Kf_mem_cent_mul S i j j
  rcases hNO _ hxord D c with hA | hB
  · exfalso
    obtain ⟨ψ₀, -, hrange₀, -⟩ := exists_psl_hom D c hA.1 (k := 1) hA.2
    have hcard : Nat.card (D.hom c).range ≤ Nat.card SL(2, GaloisField p f) := by
      rw [← hrange₀]
      exact Nat.card_le_card_of_surjective ψ₀.rangeRestrict ψ₀.rangeRestrict_surjective
    have e1 : locImg Ω (Fr.zf i * Fr.zf j) (Fr.Kf i) = (D.hom c).range :=
      Subgroup.eq_of_le_of_card_ge hci (by rw [card_locImg S.inClass S.exact hKi]; exact hcard)
    have e2 : locImg Ω (Fr.zf i * Fr.zf j) (Fr.Kf j) = (D.hom c).range :=
      Subgroup.eq_of_le_of_card_ge hcj (by rw [card_locImg S.inClass S.exact hKj]; exact hcard)
    exact Fr.ne_of_ne S hij (locImg_injOn S.inClass hP1x hKi hKj (e1.trans e2.symm))
  · exact hB

theorem rank_two_contradiction {F : Type} [Field F] {r : ℕ} (hr : r = 2)
    {Pi Pj H : Submodule F (Fin r ⊕ Fin r → F)} (hPi : IsHyperbolicPlane Pi)
    (hPj : IsHyperbolicPlane Pj) (hH : IsHyperbolicPlane H)
    (hPiPj : ∀ x ∈ Pi, ∀ y ∈ Pj, form x y = 0) (hHi : ∀ x ∈ H, ∀ y ∈ Pi, form x y = 0)
    (hHj : ∀ x ∈ H, ∀ y ∈ Pj, form x y = 0) : False := by
  subst hr
  exact Models.SymplecticPairs.false_of_orth_planes_rank_two hPi hPj hH hPiPj hHi hHj

theorem not_le_range_of_commutes (S : CSetup p f m Ω K z) (hP1 : AllLocalOddCentral Ω)
    (hNO : NoOtherComponents p f Ω) (Fr : Frame p f m Ω K z)
    {i j : Fin (m + 1)} (hij : i ≠ j)
    (D : LieSystemData p f (locQuot Ω (Fr.zf i * Fr.zf j)) (locFamily Ω (Fr.zf i * Fr.zf j)))
    {c : Fin D.card} (hci : locImg Ω (Fr.zf i * Fr.zf j) (Fr.Kf i) ≤ (D.hom c).range)
    (hcj : locImg Ω (Fr.zf i * Fr.zf j) (Fr.Kf j) ≤ (D.hom c).range) {L : Subgroup G}
    (hL : L ∈ Ω) (hLi : Commutes L (Fr.Kf i)) (hLj : Commutes L (Fr.Kf j)) :
    ¬ locImg Ω (Fr.zf i * Fr.zf j) L ≤ (D.hom c).range := by
  intro hLc
  have hxord := Fr.orderOf_zf_mul S hij
  have hP1x := hP1 _ hxord
  have hKi := Fr.Kf_mem_cent_mul S i j i
  have hKj := Fr.Kf_mem_cent_mul S i j j
  have hLx := mem_cent_mul_of_commutes S Fr hL hLi hLj
  have hB := tag_eq_psp S hP1 hNO Fr hij D hci hcj
  have hr2 : 2 ≤ D.rank c := by
    have := D.admissible c
    rw [hB] at this
    exact this.2.2.1
  obtain ⟨ν, hν, hrange, hfund⟩ := exists_psp_hom D c hB (m := D.rank c) rfl
  have hcls : ∀ L' ∈ centralizingMembers Ω {Fr.zf i * Fr.zf j},
      ∃ z', IsClassicalMember p f L' z' := fun L' hL' => S.inClass.classical L' hL'.1
  have hplane : ∀ L' ∈ centralizingMembers Ω {Fr.zf i * Fr.zf j},
      locImg Ω (Fr.zf i * Fr.zf j) L' ≤ (D.hom c).range →
      ∃ P, IsHyperbolicPlane P ∧ locImg Ω (Fr.zf i * Fr.zf j) L' = (planeGroup P).map ν := by
    intro L' hL'x hL'c
    have hnc : ¬ locImg Ω (Fr.zf i * Fr.zf j) L' ≤
        Subgroup.center (locQuot Ω (Fr.zf i * Fr.zf j)) := by
      intro hcen
      obtain ⟨z', hz'⟩ := hcls L' hL'x
      refine not_commutes_self_of_isClassicalMember hz'
        (commutes_of_commutes_locImg S.inClass hP1x hL'x hL'x ?_)
      intro a ha b hb
      exact Subgroup.mem_center_iff.mp (hcen hb) a
    obtain ⟨R, hR, hLR⟩ := exists_fundamental_of_le_range D
      (mem_locFamily_iff.mpr ⟨L', hL'x, rfl⟩) hL'c hnc
    exact (hfund _).mp ⟨R, hR, hLR⟩
  obtain ⟨Pi, hPi, hKiPi⟩ := hplane _ hKi hci
  obtain ⟨Pj, hPj, hKjPj⟩ := hplane _ hKj hcj
  obtain ⟨H, hH, hLH⟩ := hplane _ hLx hLc
  have hne_ij : (planeGroup Pi).map ν ≠ (planeGroup Pj).map ν := by
    intro h
    exact Fr.ne_of_ne S hij (locImg_injOn S.inClass hP1x hKi hKj (by rw [hKiPi, hKjPj, h]))
  have horth_ij : ∀ u ∈ Pi, ∀ v ∈ Pj, form u v = 0 := by
    refine orth_of_commute_map S.two_ne_zero S.hex ν hν hPi hPj hne_ij ?_
    have := commutes_locImg_of_commutes (Ω := Ω) (x := Fr.zf i * Fr.zf j) (Fr.commute i j hij)
    rw [hKiPi, hKjPj] at this
    exact this
  have horth_H : ∀ (k : Fin (m + 1)) (P : Submodule (GaloisField p f)
      (Fin (D.rank c) ⊕ Fin (D.rank c) → GaloisField p f)), IsHyperbolicPlane P →
      Fr.Kf k ∈ centralizingMembers Ω {Fr.zf i * Fr.zf j} →
      locImg Ω (Fr.zf i * Fr.zf j) (Fr.Kf k) = (planeGroup P).map ν →
      Commutes L (Fr.Kf k) → ∀ u ∈ H, ∀ v ∈ P, form u v = 0 := by
    intro k P hP hKk hKkP hLk
    refine orth_of_commute_map S.two_ne_zero S.hex ν hν hH hP ?_ ?_
    · intro h
      have : L = Fr.Kf k := locImg_injOn S.inClass hP1x hLx hKk (by rw [hLH, hKkP, h])
      rw [this] at hLk
      exact not_commutes_self_of_isClassicalMember (Fr.cls S k) hLk
    · have := commutes_locImg_of_commutes (Ω := Ω) (x := Fr.zf i * Fr.zf j) hLk
      rw [hLH, hKkP] at this
      exact this
  have hle : ∀ k : Fin (m + 1), Fr.Kf k ∈ centralizingMembers Ω {Fr.zf i * Fr.zf j} →
      ∀ a, Fr.ι k a ∈ locLayer Ω (Fr.zf i * Fr.zf j) := fun k hk a =>
    le_centralizingLayer hk (by rw [← Fr.range_ι k]; exact ⟨a, rfl⟩)
  have hβ : ∀ (k : Fin (m + 1)) (hk : Fr.Kf k ∈ centralizingMembers Ω {Fr.zf i * Fr.zf j}),
      Function.Injective (locHom Ω (Fr.zf i * Fr.zf j) (Fr.ι k) (hle k hk)) := fun k hk =>
    locHom_injective S.exact hk (Fr.ι_inj k) (by rw [Fr.range_ι]) (hle k hk)
  have hzk : ∀ (k : Fin (m + 1)) (hk : Fr.Kf k ∈ centralizingMembers Ω {Fr.zf i * Fr.zf j}),
      locHom Ω (Fr.zf i * Fr.zf j) (Fr.ι k) (hle k hk) (-1) =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω (Fr.zf i * Fr.zf j)))
          ⟨Fr.zf k, le_centralizingLayer hk (Frame.zf_mem S k)⟩ := by
    intro k hk
    rw [locHom_apply]
    exact congrArg _ (Subtype.ext (Fr.ι_neg_one S k))
  have hcentral : locHom Ω (Fr.zf i * Fr.zf j) (Fr.ι i) (hle i hKi) (-1) *
      locHom Ω (Fr.zf i * Fr.zf j) (Fr.ι j) (hle j hKj) (-1) ∈
        Subgroup.center (locQuot Ω (Fr.zf i * Fr.zf j)) := by
    rw [hzk i hKi, hzk j hKj, ← map_mul]
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨w', rfl⟩ := QuotientGroup.mk'_surjective _ w
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {Fr.zf i * Fr.zf j} w'.2)
  have hr : D.rank c = 2 := by
    refine eq_two_of_central_involutions S.two_ne_zero S.four_le hr2 ν hν hPi hPj horth_ij
      (locHom Ω (Fr.zf i * Fr.zf j) (Fr.ι i) (hle i hKi))
      (locHom Ω (Fr.zf i * Fr.zf j) (Fr.ι j) (hle j hKj)) (hβ i hKi) (hβ j hKj) ?_ ?_ hcentral
    · rw [range_locHom, Fr.range_ι, hKiPi]
    · rw [range_locHom, Fr.range_ι, hKjPj]
  exact rank_two_contradiction hr hPi hPj hH horth_ij (horth_H i Pi hPi hKi hKiPi hLi)
    (horth_H j Pj hPj hKj hKjPj hLj)

theorem block_lemma (S : CSetup p f m Ω K z) (hP1 : AllLocalOddCentral Ω)
    (hNO : NoOtherComponents p f Ω) (Fr : Frame p f m Ω K z) {i j : Fin (m + 1)}
    (hij : i ≠ j) {L : Subgroup G} (hL : L ∈ Ω) (hLi : Commutes L (Fr.Kf i))
    (hLj : Commutes L (Fr.Kf j)) : Commutes L (Mf Fr i j) := by
  have hxord := Fr.orderOf_zf_mul S hij
  have hP1x := hP1 _ hxord
  obtain ⟨D⟩ := S.exists_lieSystemData hxord
  obtain ⟨c, hci, hcj⟩ := exists_comp_of_pair S hP1 Fr hij D
  have hLx := mem_cent_mul_of_commutes S Fr hL hLi hLj
  have hKi := Fr.Kf_mem_cent_mul S i j i
  have hKj := Fr.Kf_mem_cent_mul S i j j
  have hMx : ∀ L' : memberSet Fr i j,
      (L' : Subgroup G) ≤ locLayer Ω (Fr.zf i * Fr.zf j) := fun L' =>
    le_centralizingLayer (memberSet_subset_cent S Fr hij L'.2)
  have hMimg : locImg Ω (Fr.zf i * Fr.zf j) (Mf Fr i j) ≤ (D.hom c).range := by
    rw [Mf, locImg_iSup _ hMx]
    refine iSup_le fun L' => ?_
    have hL'x := memberSet_subset_cent S Fr hij L'.2
    obtain ⟨c', hc'⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨_, hL'x, rfl⟩)
    by_cases hcc : c' = c
    · rw [hcc] at hc'
      exact hc'
    · exfalso
      refine not_commutes_both S Fr hij L'.2 ⟨?_, ?_⟩
      · refine commutes_of_commutes_locImg S.inClass hP1x hL'x hKi ?_
        intro a ha b hb
        exact range_commute_of_ne D hcc a (hc' ha) b (hci hb)
      · refine commutes_of_commutes_locImg S.inClass hP1x hL'x hKj ?_
        intro a ha b hb
        exact range_commute_of_ne D hcc a (hc' ha) b (hcj hb)
  obtain ⟨c', hc'⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨_, hLx, rfl⟩)
  have hcc : c' ≠ c := fun h =>
    not_le_range_of_commutes S hP1 hNO Fr hij D hci hcj hL hLi hLj (by rw [h] at hc'; exact hc')
  obtain ⟨z', hz'⟩ := S.inClass.classical L hL
  refine commutes_of_commutes_locImg_perfect hP1x (le_centralizingLayer hLx) (iSup_le hMx)
    (commutator_eq_of_isClassicalMember hz').ge ?_
  intro a ha b hb
  exact range_commute_of_ne D hcc a (hc' ha) b (hMimg hb)

end BlockMain

section LayerCommute

variable {ι : Type*}

theorem commutes_iSup_left_of_forall (A : ι → Subgroup G) (B : Subgroup G)
    (h : ∀ i, Commutes (A i) B) : Commutes (⨆ i, A i) B := by
  intro y hy b hb
  have : (⨆ i, A i) ≤ Subgroup.centralizer (B : Set G) :=
    iSup_le fun i y hy => Subgroup.mem_centralizer_iff.mpr fun b hb => (h i y hy b hb).symm
  exact (Subgroup.mem_centralizer_iff.mp (this hy) b hb).symm

theorem commutes_Mf_Kf (Fr : Frame p f m Ω K z) {i j k : Fin (m + 1)} (hki : k ≠ i)
    (hkj : k ≠ j) : Commutes (Mf Fr i j) (Fr.Kf k) :=
  commutes_iSup_left_of_forall _ _ fun L => L.2.2 k hki hkj

theorem commutes_Mf_Mf [Finite G] (S : CSetup p f m Ω K z) (hP1 : AllLocalOddCentral Ω)
    (hNO : NoOtherComponents p f Ω) (Fr : Frame p f m Ω K z)
    {i j k l : Fin (m + 1)} (hkl : k ≠ l) (hki : k ≠ i) (hkj : k ≠ j)
    (hli : l ≠ i) (hlj : l ≠ j) : Commutes (Mf Fr i j) (Mf Fr k l) :=
  commutes_iSup_left_of_forall _ _ fun L => by
    have := block_lemma S hP1 hNO Fr hkl L.2.1 (L.2.2 k hki hkj) (L.2.2 l hli hlj)
    exact this

@[expose] def LayersCommute (Fr : Frame p f m Ω K z) : Prop :=
  ∀ {i j k l : Fin (m + 1)}, i ≠ j → k ≠ l → k ≠ i → k ≠ j → l ≠ i → l ≠ j →
    Commutes (Mf Fr i j) (Mf Fr k l)

theorem layersCommute_of_block [Finite G] (S : CSetup p f m Ω K z) (hP1 : AllLocalOddCentral Ω)
    (hNO : NoOtherComponents p f Ω) (Fr : Frame p f m Ω K z) : LayersCommute Fr :=
  fun _ hkl hki hkj hli hlj => commutes_Mf_Mf S hP1 hNO Fr hkl hki hkj hli hlj

theorem exists_fifth_index (hm : 4 ≤ m) (i j k l : Fin (m + 1)) :
    ∃ q : Fin (m + 1), q ≠ i ∧ q ≠ j ∧ q ≠ k ∧ q ≠ l := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin (m + 1))) ⊆ {i, j, k, l} := by
    intro q _
    by_cases h1 : q = i
    · simp [h1]
    by_cases h2 : q = j
    · simp [h2]
    by_cases h3 : q = k
    · simp [h3]
    have h4 := h q h1 h2 h3
    simp [h4]
  have hcard := Finset.card_le_card hsub
  have h5 : ({i, j, k, l} : Finset (Fin (m + 1))).card ≤ 4 := by
    refine (Finset.card_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    simp
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  omega

theorem eq_of_mem_coords {n : ℕ} {x : Fin n ⊕ Fin n} {u v : Fin n} (hu : x ∈ coords u)
    (hv : x ∈ coords v) : u = v := by
  rcases Models.SymplecticPairs.mem_coords.1 hu with rfl | rfl <;>
    rcases Models.SymplecticPairs.mem_coords.1 hv with h | h <;> simp_all

theorem coords_union_subset_compl {n : ℕ} {a b c d : Fin n} (hca : c ≠ a) (hcb : c ≠ b)
    (hda : d ≠ a) (hdb : d ≠ b) : coords c ∪ coords d ⊆ (coords a ∪ coords b)ᶜ := by
  intro x hx hx'
  rcases hx with hx | hx <;> rcases hx' with hx' | hx'
  · exact hca (eq_of_mem_coords hx hx')
  · exact hcb (eq_of_mem_coords hx hx')
  · exact hda (eq_of_mem_coords hx hx')
  · exact hdb (eq_of_mem_coords hx hx')

theorem layersCommute_of_five [Finite G] (S : CSetup p f m Ω K z) (hm : 4 ≤ m)
    (Fr : Frame p f m Ω K z) : LayersCommute Fr := by
  intro i j k l hij hkl hki hkj hli hlj
  obtain ⟨q, hqi, hqj, hqk, hql⟩ := exists_fifth_index hm i j k l
  obtain ⟨LF⟩ := exists_localFrame S Fr q
  obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hqi)
  obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hqj)
  obtain ⟨c, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hqk)
  obtain ⟨d, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hql)
  have hab : a ≠ b := fun h => hij (by rw [h])
  have hcd : c ≠ d := fun h => hkl (by rw [h])
  have hca : c ≠ a := fun h => hki (by rw [h])
  have hcb : c ≠ b := fun h => hkj (by rw [h])
  have hda : d ≠ a := fun h => hli (by rw [h])
  have hdb : d ≠ b := fun h => hlj (by rw [h])
  refine commutes_of_commutes_locImg_perfect (Fr.p1 S q)
    (LocalFrame.Mf_le_locLayer S a b) (LocalFrame.Mf_le_locLayer S c d)
    (Mf_perfect Fr S _ _).ge ?_
  rw [LF.locImg_Mf S hab, LF.locImg_Mf S hcd]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact (Models.SymplecticPairs.commute_suppGroup_compl hx
    (Models.SymplecticPairs.suppGroup_mono (coords_union_subset_compl hca hcb hda hdb) hy)).eq

end LayerCommute

end CFSG.ClassicalInvolution.RouteD
