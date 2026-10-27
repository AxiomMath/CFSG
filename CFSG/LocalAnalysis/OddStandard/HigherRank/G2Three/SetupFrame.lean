module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Setting3
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.SetupCenter
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.G23Facts

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

namespace Setup

private lemma ker_conj_eq_center (Q : Type*) [Group Q] :
    (MulAut.conj : Q →* MulAut Q).ker = Subgroup.center Q := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h g
    have hg : MulAut.conj x g = (1 : MulAut Q) g := by rw [h]
    rw [MulAut.conj_apply, MulAut.one_apply] at hg
    exact (mul_inv_eq_iff_eq_mul.mp hg).symm
  · intro h
    ext g
    rw [MulAut.conj_apply, MulAut.one_apply]
    rw [← h g]
    group

private lemma eq_of_isSylowIn_of_le {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {P Q V : Subgroup G} (hP : IsSylowIn p V P) (hPQ : P ≤ Q) (hQV : Q ≤ V)
    (hQ : IsPGroup p Q) : Q = P := by
  have hPg : IsPGroup p (P.subgroupOf V) := hP.2.1.comap_subtype
  have hPidx : ¬ p ∣ (P.subgroupOf V).index := hP.2.2
  let SP : Sylow p ↥V := hPg.toSylow hPidx
  have hSP : (SP : Subgroup ↥V) = P.subgroupOf V := IsPGroup.toSylow_coe hPg hPidx
  have hQg : IsPGroup p (Q.subgroupOf V) := hQ.comap_subtype
  have hle : (SP : Subgroup ↥V) ≤ Q.subgroupOf V := by
    intro x hx
    exact hPQ (Subgroup.mem_subgroupOf.mp hx)
  have hmax : Q.subgroupOf V = (SP : Subgroup ↥V) := SP.is_maximal' hQg hle
  have hsub : Q.subgroupOf V = P.subgroupOf V := by rw [hmax, hSP]
  refine le_antisymm ?_ hPQ
  intro x hx
  have hx' : (⟨x, hQV hx⟩ : ↥V) ∈ Q.subgroupOf V := hx
  rw [hsub] at hx'
  simpa using (Subgroup.mem_subgroupOf.mp hx')

private lemma mem_sylow_of_mul_mem_center {L : Type*} [Group L] [Finite L]
    (hZ : Odd (Nat.card (Subgroup.center L))) (S : Sylow 2 L)
    {s w : L} (hs : s ∈ S) (hz : s⁻¹ * w ∈ Subgroup.center L)
    (hw : ∃ k : ℕ, w ^ 2 ^ k = 1) : w ∈ S := by
  set z : L := s⁻¹ * w with hzdef
  have hzmem : z ∈ Subgroup.center L := hz
  have hwz : w = s * z := by rw [hzdef, ← mul_assoc, mul_inv_cancel, one_mul]
  have hsz : Commute s z := (commute_iff_eq s z).mpr ((Subgroup.mem_center_iff.mp hzmem) s)
  have hcomm : Commute s⁻¹ w := by
    have hsw : Commute s w := by
      rw [hwz]
      exact (Commute.refl s).mul_right hsz
    exact hsw.inv_left
  have hdvd : orderOf z ∣ orderOf s * orderOf w := by
    have h1 := hcomm.orderOf_mul_dvd_mul_orderOf
    rw [orderOf_inv] at h1
    rwa [← hzdef] at h1
  obtain ⟨m, hm⟩ := S.isPGroup'.exists_pow_pow_eq_one ⟨s, hs⟩
  have hsm : orderOf s ∣ 2 ^ m := by
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg (Subtype.val) hm
    simpa using this
  obtain ⟨k, hk⟩ := hw
  have hwk : orderOf w ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hz2 : orderOf z ∣ 2 ^ (m + k) := by
    calc orderOf z ∣ orderOf s * orderOf w := hdvd
      _ ∣ 2 ^ m * 2 ^ k := Nat.mul_dvd_mul hsm hwk
      _ = 2 ^ (m + k) := (pow_add 2 m k).symm
  have hzodd : Odd (orderOf z) := by
    have h := orderOf_dvd_natCard (⟨z, hzmem⟩ : Subgroup.center L)
    rw [← Subgroup.orderOf_coe (⟨z, hzmem⟩ : Subgroup.center L)] at h
    exact Odd.of_dvd_nat hZ h
  have hz1 : orderOf z = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hz2
    cases j with
    | zero => simpa using hj
    | succ j =>
        exfalso
        exact (Nat.not_even_iff_odd.mpr hzodd)
          (by rw [hj]; exact Even.pow_of_ne_zero even_two (Nat.succ_ne_zero j))
  have hz_eq_one : z = 1 := orderOf_eq_one_iff.mp hz1
  rw [hwz, hz_eq_one, mul_one]
  exact hs

private lemma actsAs_conj_mk {G : Type} [Group G] (L : Subgroup G) (y : ↥L) :
    ActsAs L (y : G)
      ((MulAut.conj : (↥L ⧸ center ↥L) →* MulAut (↥L ⧸ center ↥L))
        (QuotientGroup.mk' (center ↥L) y)) := by
  intro x
  refine ⟨y * x * y⁻¹, ?_, ?_⟩
  · simp
  · rw [MulAut.conj_apply]
    simp

theorem exists_frame_lift (hF : G23Facts) {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hqs : CFSG.IsQuasisimple ↥L) (hZ : Odd (Nat.card (center ↥L)))
    (hL : HRG23 (↥L ⧸ center ↥L)) (S₀ : Sylow 2 ↥L) :
    ∃ (fr : SFrame G) (fr' : Frame (MulAut (↥L ⧸ center ↥L))),
      fr'.Facts (innerAut (↥L ⧸ center ↥L)) ∧ fr.IsLift L fr'.toSFrame ∧
        fr.S = (S₀ : Subgroup ↥L).map L.subtype ∧ IsSylowIn 2 L fr.S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q := ↥L ⧸ center ↥L
  let π : ↥L →* Q := QuotientGroup.mk' (center ↥L)
  let c : Q →* MulAut Q := MulAut.conj
  let ι : ↥L →* MulAut Q := c.comp π
  let Inn : Subgroup (MulAut Q) := innerAut Q
  haveI hperf : Group.IsPerfect ↥L := hqs.1
  have hcenterQ : center Q = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot ↥L
  have hkerConj : (MulAut.conj : Q →* MulAut Q).ker = center Q := ker_conj_eq_center Q
  have hconj_inj : Function.Injective (MulAut.conj : Q →* MulAut Q) :=
    (MonoidHom.ker_eq_bot_iff _).mp (by rw [hkerConj, hcenterQ])
  have hInndef : Inn = innerAut Q := rfl
  have hιker : ι.ker = center ↥L := by
    change ((MulAut.conj : Q →* MulAut Q).comp (QuotientGroup.mk' (center ↥L))).ker = center ↥L
    rw [MonoidHom.ker_comp_of_injective _ _ hconj_inj, QuotientGroup.ker_mk']
  have hιrange : ι.range = Inn := by
    change (((MulAut.conj : Q →* MulAut Q).comp
      (QuotientGroup.mk' (center ↥L))).range) = innerAut Q
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
      Subgroup.map_top]
    rfl
  have hcard_Inn : Nat.card Inn = Nat.card (↥L ⧸ center ↥L) := by
    rw [hInndef, innerAut, MonoidHom.range_eq_map]
    have h := Subgroup.card_map_of_injective (K := (⊤ : Subgroup Q))
      (f := (MulAut.conj : Q →* MulAut Q)) hconj_inj
    simpa using h
  let S₁ : Subgroup (MulAut Q) := (S₀ : Subgroup ↥L).map ι
  have hS1def : S₁ = (S₀ : Subgroup ↥L).map ι := rfl
  have hS1pgroup : IsPGroup 2 S₁ := by
    rw [hS1def]
    exact S₀.isPGroup'.map ι
  have hS1leInn : S₁ ≤ Inn := by
    rw [hS1def, hInndef]
    exact (Subgroup.map_le_range ι (S₀ : Subgroup ↥L)).trans (le_of_eq hιrange)
  have hfacL : (Nat.card ↥L).factorization 2 = (Nat.card (↥L ⧸ center ↥L)).factorization 2 := by
    have hQnz : Nat.card (↥L ⧸ center ↥L) ≠ 0 := (Nat.card_pos (α := ↥L ⧸ center ↥L)).ne'
    have hCnz : Nat.card (center ↥L) ≠ 0 := (Nat.card_pos (α := center ↥L)).ne'
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥L),
      Nat.factorization_mul hQnz hCnz]
    simp [Nat.factorization_eq_zero_of_not_dvd hZ.not_two_dvd_nat]
  have hcard_S1 : Nat.card S₁ = Nat.card S₀ := by
    have hinj : Function.Injective (ι.domRestrict (S₀ : Subgroup ↥L)) :=
      (MonoidHom.ker_eq_bot_iff _).mp (by
        rw [MonoidHom.ker_domRestrict, hιker, Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_comm]
        exact inf_center_eq_bot hZ S₀)
    have h := Subgroup.card_map_of_injective (K := (⊤ : Subgroup ↥(S₀ : Subgroup ↥L)))
      (f := ι.domRestrict (S₀ : Subgroup ↥L)) hinj
    rw [Subgroup.map_top, MonoidHom.domRestrict_range, Subgroup.card_top] at h
    rw [hS1def]
    simpa using h
  obtain ⟨P, hS1leP⟩ := IsPGroup.exists_le_sylow hS1pgroup
  obtain ⟨fr', hSσP, hfacts⟩ := hF Q hL P
  have hSylS : IsSylowIn 2 Inn fr'.S := hfacts.1.2.1
  have hK1leInn : fr'.K₁ ≤ Inn := (hfacts.2.2.2.2.2.1.2.2.2.2.1).1.trans inf_le_left
  have hK2leInn : fr'.K₂ ≤ Inn := (hfacts.2.2.2.2.2.1.2.2.2.2.2.1).1.trans inf_le_left
  have hSSσ : fr'.S ≤ fr'.Sσ := by
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hfrS_le_P : fr'.S ≤ (P : Subgroup (MulAut Q)) := hSSσ.trans (le_of_eq hSσP)
  let Pinn : Subgroup (MulAut Q) := (P : Subgroup (MulAut Q)) ⊓ Inn
  have hfrS_le_Pinf : fr'.S ≤ Pinn := le_inf hfrS_le_P hSylS.1
  have hPinf_pgroup : IsPGroup 2 Pinn :=
    P.isPGroup'.to_le (inf_le_left : Pinn ≤ (P : Subgroup (MulAut Q)))
  have hPinf_eq : Pinn = fr'.S :=
    eq_of_isSylowIn_of_le hSylS hfrS_le_Pinf inf_le_right hPinf_pgroup
  have hS1_le_frS : S₁ ≤ fr'.S := (le_inf hS1leP hS1leInn).trans (le_of_eq hPinf_eq)
  have hfacInn : (Nat.card Inn).factorization 2 = (Nat.card ↥L).factorization 2 := by
    rw [hcard_Inn, ← hfacL]
  have hcard_frS : Nat.card fr'.S = 2 ^ (Nat.card Inn).factorization 2 := by
    have hPg : IsPGroup 2 (fr'.S.subgroupOf Inn) := hSylS.2.1.comap_subtype
    have hPidx : ¬ 2 ∣ (fr'.S.subgroupOf Inn).index := hSylS.2.2
    let SP : Sylow 2 ↥Inn := hPg.toSylow hPidx
    have hcard_sub : Nat.card fr'.S = Nat.card (fr'.S.subgroupOf Inn) := by
      have hmap : (fr'.S.subgroupOf Inn).map Inn.subtype = fr'.S :=
        Subgroup.map_subgroupOf_eq_of_le hSylS.1
      conv_lhs => rw [← hmap]
      exact Subgroup.card_map_of_injective Inn.subtype_injective
    rw [hcard_sub]
    simpa [SP] using Sylow.card_eq_multiplicity SP
  have hcardS : Nat.card S₁ = Nat.card fr'.S := by
    rw [hcard_S1, hcard_frS, Sylow.card_eq_multiplicity S₀, hfacInn]
  have hfrS_eq_S1 : fr'.S = S₁ :=
    (Subgroup.eq_of_le_of_card_ge hS1_le_frS hcardS.ge).symm
  have memK₁ : ∀ x ∈ ({fr'.u₁, fr'.b₁} : Set (MulAut Q)), x ∈ fr'.K₁ :=
    fun x hx => Subgroup.subset_closure hx
  have memK₂ : ∀ x ∈ ({fr'.u₂, fr'.b₂} : Set (MulAut Q)), x ∈ fr'.K₂ :=
    fun x hx => Subgroup.subset_closure hx
  have memS : ∀ x ∈ ({fr'.a₁, fr'.b₁, fr'.a₂, fr'.b₂, fr'.h₀} : Set (MulAut Q)), x ∈ fr'.S :=
    fun x hx => Subgroup.subset_closure hx
  have hιu₁ : fr'.u₁ ∈ ι.range := by
    rw [hιrange]
    exact hK1leInn (memK₁ fr'.u₁ (by simp))
  obtain ⟨υ₁, hυ₁⟩ := MonoidHom.mem_range.mp hιu₁
  have hιu₂ : fr'.u₂ ∈ ι.range := by
    rw [hιrange]
    exact hK2leInn (memK₂ fr'.u₂ (by simp))
  obtain ⟨υ₂, hυ₂⟩ := MonoidHom.mem_range.mp hιu₂
  have hb₁S1 : fr'.b₁ ∈ S₁ := hfrS_eq_S1 ▸ memS fr'.b₁ (by simp)
  obtain ⟨β₁, hβ₁S, hβ₁⟩ := Subgroup.mem_map.mp hb₁S1
  have hb₂S1 : fr'.b₂ ∈ S₁ := hfrS_eq_S1 ▸ memS fr'.b₂ (by simp)
  obtain ⟨β₂, hβ₂S, hβ₂⟩ := Subgroup.mem_map.mp hb₂S1
  have hηS1 : fr'.h₀ ∈ S₁ := hfrS_eq_S1 ▸ memS fr'.h₀ (by simp)
  obtain ⟨η, hηS, hιη⟩ := Subgroup.mem_map.mp hηS1
  let fr : SFrame G := ⟨(υ₁ : G), (β₁ : G), (υ₂ : G), (β₂ : G), (η : G)⟩
  let w₁ : ↥L := υ₁ * β₁ ^ 3 * υ₁⁻¹
  let w₂ : ↥L := υ₂ * β₂ ^ 3 * υ₂⁻¹
  have hιw₁ : ι w₁ = fr'.a₁ := by
    show ι (υ₁ * β₁ ^ 3 * υ₁⁻¹) = fr'.u₁ * fr'.b₁ ^ 3 * fr'.u₁⁻¹
    simp only [map_mul, map_pow, map_inv, hυ₁, hβ₁]
  have hιw₂ : ι w₂ = fr'.a₂ := by
    show ι (υ₂ * β₂ ^ 3 * υ₂⁻¹) = fr'.u₂ * fr'.b₂ ^ 3 * fr'.u₂⁻¹
    simp only [map_mul, map_pow, map_inv, hυ₂, hβ₂]
  have hw₁pow : ∃ k : ℕ, w₁ ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := S₀.isPGroup'.exists_pow_pow_eq_one ⟨β₁, hβ₁S⟩
    refine ⟨k, ?_⟩
    have hk' : β₁ ^ 2 ^ k = 1 := by
      have := congrArg (Subtype.val) hk
      simpa using this
    rw [show w₁ = (MulAut.conj υ₁) (β₁ ^ 3) by simp [w₁, MulAut.conj_apply]]
    rw [← map_pow, ← pow_mul, mul_comm 3 (2 ^ k), pow_mul, hk']
    simp
  have hw₂pow : ∃ k : ℕ, w₂ ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := S₀.isPGroup'.exists_pow_pow_eq_one ⟨β₂, hβ₂S⟩
    refine ⟨k, ?_⟩
    have hk' : β₂ ^ 2 ^ k = 1 := by
      have := congrArg (Subtype.val) hk
      simpa using this
    rw [show w₂ = (MulAut.conj υ₂) (β₂ ^ 3) by simp [w₂, MulAut.conj_apply]]
    rw [← map_pow, ← pow_mul, mul_comm 3 (2 ^ k), pow_mul, hk']
    simp
  have hw₁S0 : w₁ ∈ S₀ := by
    have ha₁S1 : fr'.a₁ ∈ S₁ := hfrS_eq_S1 ▸ memS fr'.a₁ (by simp)
    obtain ⟨s₁, hs₁S, hs₁⟩ := Subgroup.mem_map.mp ha₁S1
    have hz₁ : s₁⁻¹ * w₁ ∈ center ↥L := by
      rw [← hιker, MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hs₁, hιw₁, inv_mul_cancel]
    exact mem_sylow_of_mul_mem_center hZ S₀ hs₁S hz₁ hw₁pow
  have hw₂S0 : w₂ ∈ S₀ := by
    have ha₂S1 : fr'.a₂ ∈ S₁ := hfrS_eq_S1 ▸ memS fr'.a₂ (by simp)
    obtain ⟨s₂, hs₂S, hs₂⟩ := Subgroup.mem_map.mp ha₂S1
    have hz₂ : s₂⁻¹ * w₂ ∈ center ↥L := by
      rw [← hιker, MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hs₂, hιw₂, inv_mul_cancel]
    exact mem_sylow_of_mul_mem_center hZ S₀ hs₂S hz₂ hw₂pow
  have mem_frS : ∀ x ∈ ({fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀} : Set G), x ∈ fr.S :=
    fun x hx => Subgroup.subset_closure hx
  have hfrS_le : fr.S ≤ (S₀ : Subgroup ↥L).map L.subtype := by
    show closure {fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀} ≤ (S₀ : Subgroup ↥L).map L.subtype
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact Subgroup.mem_map.mpr ⟨w₁, hw₁S0, rfl⟩
    · exact Subgroup.mem_map.mpr ⟨β₁, hβ₁S, rfl⟩
    · exact Subgroup.mem_map.mpr ⟨w₂, hw₂S0, rfl⟩
    · exact Subgroup.mem_map.mpr ⟨β₂, hβ₂S, rfl⟩
    · exact Subgroup.mem_map.mpr ⟨η, hηS, rfl⟩
  let F : Subgroup ↥L := closure {w₁, β₁, w₂, β₂, η}
  have hF_le_S0 : F ≤ S₀ := by
    show closure {w₁, β₁, w₂, β₂, η} ≤ S₀
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact hw₁S0
    · exact hβ₁S
    · exact hw₂S0
    · exact hβ₂S
    · exact hηS
  have hFmapι : F.map ι = fr'.S := by
    show (closure {w₁, β₁, w₂, β₂, η}).map ι = fr'.S
    rw [MonoidHom.map_closure, SFrame.S]
    congr 1
    simp only [Set.image_insert_eq, Set.image_singleton, Set.image_empty]
    rw [hιw₁, hβ₁, hιw₂, hβ₂, hιη]
  have hFmap_le_frS : F.map L.subtype ≤ fr.S := by
    show (closure {w₁, β₁, w₂, β₂, η}).map L.subtype ≤ fr.S
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy | hy | hy
    · rw [hy]
      change (w₁ : G) ∈ fr.S
      rw [show (w₁ : G) = fr.a₁ by rfl]
      exact mem_frS fr.a₁ (by simp)
    · rw [hy]
      exact mem_frS fr.b₁ (by simp)
    · rw [hy]
      change (w₂ : G) ∈ fr.S
      rw [show (w₂ : G) = fr.a₂ by rfl]
      exact mem_frS fr.a₂ (by simp)
    · rw [hy]
      exact mem_frS fr.b₂ (by simp)
    · rw [hy]
      exact mem_frS fr.h₀ (by simp)
  have hS0_le_frS : (S₀ : Subgroup ↥L).map L.subtype ≤ fr.S := by
    intro x hx
    obtain ⟨s, hsS, rfl⟩ := Subgroup.mem_map.mp hx
    have hιs : ι s ∈ fr'.S := by
      rw [hfrS_eq_S1]
      exact Subgroup.mem_map.mpr ⟨s, hsS, rfl⟩
    have hιs' : ι s ∈ F.map ι := by rw [hFmapι]; exact hιs
    obtain ⟨f, hfF, hfs⟩ := Subgroup.mem_map.mp hιs'
    have hz : s⁻¹ * f ∈ center ↥L := by
      rw [← hιker, MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hfs, inv_mul_cancel]
    have hzs : s⁻¹ * f ∈ S₀ := S₀.mul_mem (S₀.inv_mem hsS) (hF_le_S0 hfF)
    have hbot : s⁻¹ * f = 1 := by
      have : s⁻¹ * f ∈ (⊥ : Subgroup ↥L) := by
        rw [← inf_center_eq_bot hZ S₀]
        exact ⟨hzs, hz⟩
      simpa using this
    have hsf : s = f := inv_mul_eq_one.mp hbot
    have hmem : (f : G) ∈ F.map L.subtype := Subgroup.mem_map.mpr ⟨f, hfF, rfl⟩
    rw [hsf]
    exact hFmap_le_frS hmem
  have hfrS_eq : fr.S = (S₀ : Subgroup ↥L).map L.subtype := le_antisymm hfrS_le hS0_le_frS
  have hsylow : IsSylowIn 2 L fr.S := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hfrS_eq]
      exact Subgroup.map_subtype_le (S₀ : Subgroup ↥L)
    · rw [hfrS_eq]
      exact S₀.isPGroup'.map L.subtype
    · rw [hfrS_eq]
      have hrel : ((S₀ : Subgroup ↥L).map L.subtype).relIndex L = S₀.index := by
        have h := Subgroup.relIndex_map_map_of_injective (f := L.subtype)
          (S₀ : Subgroup ↥L) (⊤ : Subgroup ↥L) L.subtype_injective
        rw [Subgroup.map_top, Subgroup.range_subtype, Subgroup.relIndex_top_right] at h
        exact h
      rw [hrel]
      haveI : S₀.FiniteIndex := ⟨by
        intro h
        have := S₀.index_mul_card
        rw [h, zero_mul] at this
        exact (Nat.card_pos (α := ↥L)).ne' this.symm⟩
      exact S₀.not_dvd_index
  have hLift : fr.IsLift L fr'.toSFrame := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · show (υ₁ : G) ∈ L
      exact υ₁.2
    · show ActsAs L (υ₁ : G) fr'.u₁
      rw [← hυ₁]
      exact actsAs_conj_mk L υ₁
    · show (β₁ : G) ∈ L
      exact β₁.2
    · show ActsAs L (β₁ : G) fr'.b₁
      rw [← hβ₁]
      exact actsAs_conj_mk L β₁
    · show (υ₂ : G) ∈ L
      exact υ₂.2
    · show ActsAs L (υ₂ : G) fr'.u₂
      rw [← hυ₂]
      exact actsAs_conj_mk L υ₂
    · show (β₂ : G) ∈ L
      exact β₂.2
    · show ActsAs L (β₂ : G) fr'.b₂
      rw [← hβ₂]
      exact actsAs_conj_mk L β₂
    · show (η : G) ∈ L
      exact η.2
    · show ActsAs L (η : G) fr'.h₀
      rw [← hιη]
      exact actsAs_conj_mk L η
  exact ⟨fr, fr', hfacts, hLift, hfrS_eq, hsylow⟩

end Setup

end CFSG.OddStandard.HigherRank.G2Three
