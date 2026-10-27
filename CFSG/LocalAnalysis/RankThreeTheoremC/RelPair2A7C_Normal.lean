module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Defs
import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltThreeCover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup Equiv
  CFSG.RankThree.PartTwo.KFacts.KP2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem a7n_map_conj_le_a7J (H Y₁ : Subgroup G) {h : G} (hh : h ∈ H) :
    Y₁.map (MulAut.conj h).toMonoidHom ≤ a7J H Y₁ :=
  le_iSup₂ (f := fun (h : G) (_ : h ∈ H) => Y₁.map (MulAut.conj h).toMonoidHom) h hh

omit [Finite G] in
theorem a7n_le_a7J (H Y₁ : Subgroup G) : Y₁ ≤ a7J H Y₁ := fun y hy =>
  a7n_map_conj_le_a7J H Y₁ H.one_mem ⟨y, hy, by simp⟩

omit [Finite G] in
theorem a7n_a7J_le {H Y₁ : Subgroup G} (hY : Y₁ ≤ H) : a7J H Y₁ ≤ H :=
  iSup₂_le fun h hh => by
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using H.mul_mem (H.mul_mem hh (hY hy)) (H.inv_mem hh)

omit [Finite G] in
theorem a7n_map_conj_a7J_le (H Y₁ : Subgroup G) {g : G} (hg : g ∈ H) :
    (a7J H Y₁).map (MulAut.conj g).toMonoidHom ≤ a7J H Y₁ := by
  rw [a7J, Subgroup.map_iSup]
  refine iSup_le fun h => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hh => ?_
  rw [map_map]
  have : (MulAut.conj g).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
      (MulAut.conj (g * h)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [this]
  exact a7n_map_conj_le_a7J H Y₁ (H.mul_mem hg hh)

omit [Finite G] in
theorem a7n_le_normalizer (H Y₁ : Subgroup G) : H ≤ normalizer (a7J H Y₁ : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact a7n_map_conj_a7J_le H Y₁ hg ⟨x, hx, rfl⟩
  · intro hx
    have := a7n_map_conj_a7J_le H Y₁ (H.inv_mem hg) ⟨_, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using this

omit [Finite G] in
theorem a7n_isPerfect {H Y₁ : Subgroup G} (hY : Group.IsPerfect Y₁) :
    Group.IsPerfect (a7J H Y₁) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (commutator_le.mpr fun a ha b hb => ?_) (iSup₂_le fun h hh => ?_)
  · rw [commutatorElement_def]
    exact (a7J H Y₁).mul_mem ((a7J H Y₁).mul_mem ((a7J H Y₁).mul_mem ha hb)
      ((a7J H Y₁).inv_mem ha)) ((a7J H Y₁).inv_mem hb)
  · have : Group.IsPerfect (Y₁.map (MulAut.conj h).toMonoidHom) := Group.IsPerfect.map _
    rw [← Subgroup.commutator_eq_self (H := Y₁.map (MulAut.conj h).toMonoidHom)]
    exact commutator_mono (a7n_map_conj_le_a7J H Y₁ hh) (a7n_map_conj_le_a7J H Y₁ hh)

omit [Finite G] in
theorem a7n_le_normalizer_a7K (H : Subgroup G) : H ≤ normalizer (a7K H : Set G) := by
  have h := Subgroup.le_normalizer_map (H := primeComplementCore (G := H) 3) H.subtype
  rwa [normalizer_eq_top_iff.mpr inferInstance, ← MonoidHom.range_eq_map, range_subtype] at h

omit [Finite G] in
theorem a7n_mem_a7K_iff {H : Subgroup G} (h : ↥H) :
    (h : G) ∈ a7K H ↔ h ∈ primeComplementCore (G := H) 3 :=
  Subgroup.mem_map_iff_mem H.subtype_injective

omit [Finite G] in
theorem a7n_commutator_mem {H Y S K : Subgroup G} (hYH : Y ≤ H)
    (hS : H ≤ normalizer (S : Set G)) (hK : H ≤ normalizer (K : Set G))
    (hY : ∀ y ∈ Y, ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ S) :
    ∀ j ∈ a7J H Y, ∀ k ∈ K, j * k * j⁻¹ * k⁻¹ ∈ S := by
  have hKconj : ∀ h ∈ H, ∀ k ∈ K, h⁻¹ * k * h ∈ K := fun h hh k hk => by
    simpa using (mem_normalizer_iff.mp (hK (H.inv_mem hh)) k).mp hk
  let C : Subgroup G :=
    { carrier := {g | g ∈ H ∧ ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ S}
      one_mem' := ⟨H.one_mem, fun k _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, hak⟩ ⟨hb, hbk⟩
        refine ⟨H.mul_mem ha hb, fun k hk => ?_⟩
        have h1 := (mem_normalizer_iff.mp (hS ha) _).mp (hbk k hk)
        have h2 := S.mul_mem h1 (hak k hk)
        convert h2 using 1
        group
      inv_mem' := by
        rintro a ⟨ha, hak⟩
        refine ⟨H.inv_mem ha, fun k hk => ?_⟩
        have h1 := S.inv_mem (hak _ (hKconj a ha k hk))
        convert h1 using 1
        group }
  have hYC : ∀ h ∈ H, Y.map (MulAut.conj h).toMonoidHom ≤ C := by
    rintro h hh _ ⟨y, hy, rfl⟩
    refine ⟨?_, fun k hk => ?_⟩
    · simpa [MulAut.conj_apply] using H.mul_mem (H.mul_mem hh (hYH hy)) (H.inv_mem hh)
    · have h1 := (mem_normalizer_iff.mp (hS hh) _).mp (hY y hy _ (hKconj h hh k hk))
      convert h1 using 1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  intro j hj k hk
  exact ((iSup₂_le hYC : a7J H Y ≤ C) hj).2 k hk

theorem a7n_cTwo_mem : cTwo ∈ a7Five :=
  mem_a7Five_iff.mpr ⟨eNine_le_alternatingGroup cTwo_mem_eNine, by decide, by decide⟩

theorem a7n_cTwo_ne : cTwo ≠ 1 := by decide

omit [Finite G] in
theorem a7n_map_eq {H J Y : Subgroup G} {ι : ↥H →* Perm (Fin 7)}
    (hA : alternatingGroup (Fin 7) ≤ ι.range) (hJH : J ≤ H) [Group.IsPerfect J]
    (hHJ : H ≤ normalizer (J : Set G)) (hYJ : Y ≤ J) (hY : (Y.subgroupOf H).map ι = a7Five) :
    (J.subgroupOf H).map ι = alternatingGroup (Fin 7) := by
  classical
  set φ : ↥J →* Perm (Fin 7) := ι.comp (Subgroup.inclusion hJH) with hφ
  have hrange : φ.range = (J.subgroupOf H).map ι := by
    rw [hφ, MonoidHom.range_comp, Subgroup.inclusion_range]
  rw [← hrange]
  have hle : φ.range ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨j, rfl⟩
    have h1 : j ∈ (Perm.sign.comp φ).ker :=
      Abelianization.commutator_subset_ker _ Group.IsPerfect.mem_commutator
    exact Equiv.Perm.mem_alternatingGroup.mpr h1
  set φ' : ↥J →* alternatingGroup (Fin 7) :=
    φ.codRestrict (alternatingGroup (Fin 7)) (fun j => hle ⟨j, rfl⟩) with hφ'
  have hN : (φ'.range).Normal := by
    constructor
    rintro _ ⟨j, rfl⟩ g
    obtain ⟨h, hh⟩ := hA g.2
    have hj : (h : G) * (j : G) * (h : G)⁻¹ ∈ J := (mem_normalizer_iff.mp (hHJ h.2) _).mp j.2
    refine ⟨⟨_, hj⟩, Subtype.ext ?_⟩
    have e1 : Subgroup.inclusion hJH ⟨_, hj⟩ = h * Subgroup.inclusion hJH j * h⁻¹ := rfl
    simp only [hφ', hφ, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, e1, map_mul, map_inv,
      hh, Subgroup.coe_mul, Subgroup.coe_inv]
  have hne : φ'.range ≠ ⊥ := by
    intro hbot
    have hc := a7n_cTwo_mem
    rw [← hY] at hc
    obtain ⟨y, hy, hyc⟩ := hc
    have hmem : φ' ⟨y, hYJ hy⟩ ∈ φ'.range := ⟨_, rfl⟩
    rw [hbot, mem_bot] at hmem
    have h2 := congrArg Subtype.val hmem
    have e2 : Subgroup.inclusion hJH ⟨(y : G), hYJ hy⟩ = y := rfl
    simp only [hφ', hφ, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, e2, hyc,
      OneMemClass.coe_one] at h2
    exact a7n_cTwo_ne h2
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (α := Fin 7) (by simp)
    (N := φ'.range) with h | h
  · exact absurd h hne
  · refine le_antisymm hle fun σ hσ => ?_
    obtain ⟨j, hj⟩ : (⟨σ, hσ⟩ : alternatingGroup (Fin 7)) ∈ φ'.range := h ▸ mem_top _
    exact ⟨j, congrArg Subtype.val hj⟩

theorem a7n_card_eq_card_map_mul {A : Type*} [Group A] (N X : Subgroup A) [N.Normal]
    (hNX : N ≤ X) : Nat.card X = Nat.card (X.map (QuotientGroup.mk' N)) * Nat.card N := by
  let f : ↥X →* A ⧸ N := (QuotientGroup.mk' N).comp X.subtype
  have h1 := Subgroup.card_ker_mul_card_range f
  have hker : f.ker = N.subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (x : A)
  have hrange : f.range = X.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [hker, hrange, Nat.card_congr (subgroupOfEquivOfLe hNX).toEquiv] at h1
  rw [← h1, mul_comm]

theorem a7n_inf_le {H J K S : Subgroup G}
    {ι : ↥H →* Perm (Fin 7)} (hJH : J ≤ H) [Group.IsPerfect J]
    (hJι : (J.subgroupOf H).map ι = alternatingGroup (Fin 7))
    (hker : ∀ h : ↥H, ι h = 1 ↔ (h : G) ∈ K)
    (hJK : ∀ j ∈ J, ∀ k ∈ K, j * k * j⁻¹ * k⁻¹ ∈ S) (hSK : S ≤ K)
    (hHS : H ≤ normalizer (S : Set G)) (hKH : K ≤ H) (hodd : ¬ 2 ∣ S.relIndex K)
    (h3 : Nat.Coprime 3 (Nat.card K)) : J ⊓ K ≤ S := by
  classical
  set φ : ↥J →* Perm (Fin 7) := ι.comp (Subgroup.inclusion hJH) with hφ
  have hrange : φ.range = alternatingGroup (Fin 7) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.inclusion_range, hJι]
  set φ' : ↥J →* alternatingGroup (Fin 7) :=
    φ.codRestrict (alternatingGroup (Fin 7)) (fun j => hrange ▸ ⟨j, rfl⟩) with hφ'
  have hsurj : Function.Surjective φ' := by
    rintro ⟨σ, hσ⟩
    rw [← hrange] at hσ
    obtain ⟨j, hj⟩ := hσ
    exact ⟨j, Subtype.ext hj⟩
  have hkerφ : φ'.ker = K.subgroupOf J := by
    ext j
    rw [MonoidHom.ker_codRestrict, MonoidHom.mem_ker, mem_subgroupOf]
    exact hker _
  set N : Subgroup ↥J := S.subgroupOf J with hN
  have hNn : N.Normal := ⟨fun n hn g => by
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ S
    exact (mem_normalizer_iff.mp (hHS (hJH g.2)) _).mp hn⟩
  have hNK : N ≤ φ'.ker := by
    rw [hkerφ]
    exact fun x hx => hSK hx
  set π := QuotientGroup.lift N φ' hNK with hπ
  have hπs : Function.Surjective π := QuotientGroup.lift_surjective_of_surjective _ _ hsurj _
  have hπker : π.ker = (K.subgroupOf J).map (QuotientGroup.mk' N) := by
    rw [hπ, QuotientGroup.ker_lift, hkerφ]
  have hcen : π.ker ≤ center (↥J ⧸ N) := by
    rw [hπker]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ K := hx
    rw [mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 := S.inv_mem (hJK _ (J.inv_mem y.2) _ (K.inv_mem hx'))
    show ((y : G) * (x : G))⁻¹ * ((x : G) * (y : G)) ∈ S
    convert h1 using 1
    group
  have hP : commutator (↥J ⧸ N) = ⊤ := Group.IsPerfect.commutator_eq_top
  have h6 := CFSG.ComponentClassification.RankTwoAlt.Three.card_ker_dvd_six hP (Or.inr rfl)
    hπs hcen
  have hNKJ : N ≤ K.subgroupOf J := fun x hx => hSK hx
  have hc1 : Nat.card (K.subgroupOf J) = Nat.card π.ker * Nat.card N := by
    rw [hπker]
    exact a7n_card_eq_card_map_mul N (K.subgroupOf J) hNKJ
  have hc2 : N.relIndex (K.subgroupOf J) * Nat.card N = Nat.card (K.subgroupOf J) := by
    have := relIndex_mul_card N (K.subgroupOf J)
    rwa [inf_eq_left.mpr hNKJ] at this
  have hc3 : N.relIndex (K.subgroupOf J) = S.relIndex (J ⊓ K) := by
    rw [hN, ← inf_subgroupOf_left K J]
    exact relIndex_subgroupOf inf_le_left
  have hcard : Nat.card π.ker = S.relIndex (J ⊓ K) := by
    rw [← hc3]
    have hpos : 0 < Nat.card N := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (hc1.symm.trans hc2.symm)
  have hSKn : (S.subgroupOf K).Normal :=
    (normal_subgroupOf_iff_le_normalizer hSK).mpr (hKH.trans hHS)
  have hdvd : S.relIndex (J ⊓ K) ∣ S.relIndex K := by
    rw [← relIndex_subgroupOf (inf_le_right : J ⊓ K ≤ K)]
    exact relIndex_dvd_index_of_normal _ _
  have hcop : Nat.Coprime (S.relIndex (J ⊓ K)) 6 := by
    have h2 : Nat.Coprime 2 (S.relIndex K) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
    have h3' : Nat.Coprime 3 (S.relIndex K) := h3.coprime_dvd_right (relIndex_dvd_card S K)
    exact (Nat.Coprime.coprime_dvd_right hdvd (Nat.Coprime.mul_left h2 h3')).symm
  have h1 : S.relIndex (J ⊓ K) = 1 := Nat.Coprime.eq_one_of_dvd hcop (hcard ▸ h6)
  exact relIndex_eq_one.mp h1

omit [Finite G] in
theorem a7n_le_of_mem_mul {H J D K : Subgroup G} (hDH : D ≤ H) (hD : IsPGroup 3 D)
    (hJH : J ≤ H) (hHJ : H ≤ normalizer (J : Set G)) (hKH : K ≤ H)
    (h3 : Nat.Coprime 3 (Nat.card K)) (hDJK : ∀ d ∈ D, ∃ j ∈ J, j⁻¹ * d ∈ K) : D ≤ J := by
  intro d hd
  obtain ⟨j, hj, hjd⟩ := hDJK d hd
  set J' : Subgroup ↥H := J.subgroupOf H with hJ'
  have hJ'n : J'.Normal := (normal_subgroupOf_iff_le_normalizer hJH).mpr hHJ
  set q := QuotientGroup.mk' J' ⟨d, hDH hd⟩ with hq
  have hq' : q = QuotientGroup.mk' J' ⟨j⁻¹ * d, hKH hjd⟩ := by
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    show d⁻¹ * (j⁻¹ * d) ∈ J
    have := (mem_normalizer_iff.mp (hHJ (H.inv_mem (hDH hd))) j⁻¹).mp (J.inv_mem hj)
    simpa [mul_assoc] using this
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hD) ⟨d, hd⟩
  have h1 : orderOf q ∣ 3 ^ n := by
    have := orderOf_map_dvd (QuotientGroup.mk' J') ⟨d, hDH hd⟩
    rwa [Subgroup.orderOf_mk, ← Subgroup.orderOf_mk (H := D) d hd, hn] at this
  have h2 : orderOf q ∣ Nat.card K := by
    rw [hq']
    refine (orderOf_map_dvd _ _).trans ?_
    rw [Subgroup.orderOf_mk]
    exact K.orderOf_dvd_natCard hjd
  have h4 : orderOf q = 1 :=
    Nat.Coprime.eq_one_of_dvd ((Nat.Coprime.pow_left n h3).coprime_dvd_left h1) h2
  have h5 : q = 1 := orderOf_eq_one_iff.mp h4
  rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h5
  exact h5

theorem A7Frame.exists_J_core {D H V : Subgroup G}
    {ι : ↥H →* Perm (Fin 7)} (hF : A7Frame D H V ι) {Y₁ : Subgroup G}
    (hY₁I : Y₁ ≤ a7I H ι) (hperf : Group.IsPerfect Y₁)
    (hι : (Y₁.subgroupOf H).map ι = a7Five)
    (hYK : ∀ y ∈ Y₁, ∀ k ∈ a7K H, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H)
    (hVY : V ≤ Y₁ ⊔ pCoreOf 2 H) :
    a7J H Y₁ ≤ H ∧ H ≤ normalizer (a7J H Y₁ : Set G) ∧ Group.IsPerfect (a7J H Y₁) ∧
      ((a7J H Y₁).subgroupOf H).map ι = alternatingGroup (Fin 7) ∧
      (∀ j ∈ a7J H Y₁, ∀ k ∈ a7K H, j * k * j⁻¹ * k⁻¹ ∈ pCoreOf 2 H) ∧
      a7J H Y₁ ⊓ a7K H ≤ pCoreOf 2 H ∧ D ≤ a7J H Y₁ ∧ V ≤ a7J H Y₁ ⊔ pCoreOf 2 H ∧
      Y₁ ≤ a7J H Y₁ := by
  have hYH : Y₁ ≤ H := hY₁I.trans (a7I_le H ι)
  have hJH : a7J H Y₁ ≤ H := a7n_a7J_le hYH
  have hHJ : H ≤ normalizer (a7J H Y₁ : Set G) := a7n_le_normalizer H Y₁
  have hYJ : Y₁ ≤ a7J H Y₁ := a7n_le_a7J H Y₁
  have hJP : Group.IsPerfect (a7J H Y₁) := a7n_isPerfect hperf
  have hHS : H ≤ normalizer (pCoreOf 2 H : Set G) := hF.H_norm.ge
  have hker : ∀ h : ↥H, ι h = 1 ↔ (h : G) ∈ a7K H := fun h => by
    rw [← MonoidHom.mem_ker, hF.ker_eq, a7n_mem_a7K_iff]
  have hJι := a7n_map_eq hF.A7_le hJH hHJ hYJ hι
  have hJK := a7n_commutator_mem hYH hHS (a7n_le_normalizer_a7K H) hYK
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ¬ 2 ∣ (pCoreOf 2 H).relIndex (a7K H) :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hF.sylow).2.2
  have hcore := a7n_inf_le hJH hJι hker hJK hF.sylow.le hHS (a7K_le H) hodd hF.K_coprime
  have hDJ : D ≤ a7J H Y₁ := by
    refine a7n_le_of_mem_mul hF.D_le hF.D_three hJH hHJ (a7K_le H) hF.K_coprime ?_
    intro d hd
    have hmem : ι ⟨d, hF.D_le hd⟩ ∈ ((a7J H Y₁).subgroupOf H).map ι := by
      rw [hJι]
      apply eNine_le_alternatingGroup
      rw [← hF.D_img]
      exact ⟨⟨d, hF.D_le hd⟩, hd, rfl⟩
    obtain ⟨j, hj, hjd⟩ := hmem
    refine ⟨j, hj, (hker (j⁻¹ * ⟨d, hF.D_le hd⟩)).mp ?_⟩
    rw [map_mul, map_inv, hjd, inv_mul_cancel]
  exact ⟨hJH, hHJ, hJP, hJι, hJK, hcore, hDJ, hVY.trans (sup_le_sup_right hYJ _), hYJ⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
