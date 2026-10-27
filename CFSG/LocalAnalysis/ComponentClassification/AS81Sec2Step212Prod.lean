module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2P
public import CFSG.LocalAnalysis.ComponentClassification.AS81NXKernelCover
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step41
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.Quasithin

namespace Sec2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sec2K_le_normalizer (E : Subgroup G) :
    sec2K E ≤ normalizer (sec2P E : Set G) :=
  (closure_le _).mpr fun _ hx => hx.1

theorem natCard_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

omit [Finite G] in
theorem exists_mul_of_mem_E {A R E : Subgroup G} (hRA : R ≤ centralizer (A : Set G))
    (hRE : R ≤ E) (hEAR : E ≤ A ⊔ R) {e : G} (he : e ∈ E) :
    ∃ a ∈ E ⊓ A, ∃ r ∈ R, e = a * r := by
  have he' : e ∈ ((A ⊔ R : Subgroup G) : Set G) := hEAR he
  rw [coe_mul_of_right_le_normalizer_left A R
    (hRA.trans (Subgroup.centralizer_le_normalizer _))] at he'
  obtain ⟨a, ha, r, hr, rfl⟩ := he'
  refine ⟨a, ⟨?_, ha⟩, r, hr, rfl⟩
  have := E.mul_mem he (E.inv_mem (hRE hr))
  rwa [mul_inv_cancel_right] at this

theorem sec2P_le_centralizer_oddCoreIn {E : Subgroup G} (hPK : sec2P E ≤ sec2K E) :
    sec2P E ≤ centralizer (AS76b.oddCoreIn (sec2K E) : Set G) := by
  have hKP : sec2K E ≤ normalizer (sec2P E : Set G) := sec2K_le_normalizer E
  have hKO := AS76b.le_normalizer_oddCoreIn (sec2K E)
  intro p hp
  rw [mem_centralizer_iff]
  intro o ho
  have h1 : o * p * o⁻¹ * p⁻¹ ∈ sec2P E := by
    have := (mem_normalizer_iff.mp (hKP (AS76b.oddCoreIn_le _ ho)) p).mp hp
    exact (sec2P E).mul_mem this ((sec2P E).inv_mem hp)
  have h2 : o * p * o⁻¹ * p⁻¹ ∈ AS76b.oddCoreIn (sec2K E) := by
    have := (mem_normalizer_iff.mp (hKO (hPK hp)) o⁻¹).mp (inv_mem ho)
    have e : o * p * o⁻¹ * p⁻¹ = o * (p * o⁻¹ * p⁻¹) := by group
    rw [e]
    exact mul_mem ho this
  have h3 : o * p * o⁻¹ * p⁻¹ ∈ sec2P E ⊓ AS76b.oddCoreIn (sec2K E) := ⟨h1, h2⟩
  rw [NXKernel.inf_eq_bot_of_two_odd (isPGroup_sec2P E) (AS76b.odd_card_oddCoreIn _),
    mem_bot] at h3
  calc o * p = o * p * o⁻¹ * p⁻¹ * (p * o) := by group
    _ = p * o := by rw [h3, one_mul]

omit [Finite G] in
theorem map_subgroupOf_eq_bot {K N : Subgroup G} (hNK : N ≤ K)
    (hKN : K ≤ normalizer (N : Set G)) {φ : ↥K →* alternatingGroup (Fin 6)}
    (hφs : Function.Surjective φ) (hN : ¬ 360 ∣ Nat.card N) : (N.subgroupOf K).map φ = ⊥ := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hn : ((N.subgroupOf K).map φ).Normal :=
    ((normal_subgroupOf_iff_le_normalizer hNK).mpr hKN).map φ hφs
  rcases hn.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    apply hN
    have h1 : Nat.card ((N.subgroupOf K).map φ) ∣ Nat.card N := by
      refine (Subgroup.card_map_dvd _ _).trans ?_
      rw [NXKernel.card_subgroupOf, inf_eq_left.mpr hNK]
    rwa [h, Subgroup.card_top, natCard_alternatingGroup_six] at h1

theorem sup_oddCoreIn_le_ker {A E : Subgroup G}
    (hPOK : sec2P E ⊔ AS76b.oddCoreIn (sec2K E) ≤ sec2K E)
    {φ : ↥(sec2K E) →* alternatingGroup (Fin 6)} (hφs : Function.Surjective φ)
    (hφker : φ.ker = (sec2K E ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G)).subgroupOf (sec2K E)) :
    sec2P E ⊔ AS76b.oddCoreIn (sec2K E) ≤
      sec2K E ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G) := by
  have hPK : sec2P E ≤ sec2K E := le_sup_left.trans hPOK
  have hOK := AS76b.oddCoreIn_le (sec2K E)
  have hP1 := map_subgroupOf_eq_bot hPK (sec2K_le_normalizer E) hφs (fun h => by
    obtain ⟨m, hm⟩ := (isPGroup_sec2P E).exists_card_eq
    rw [hm] at h
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three ((by norm_num : 3 ∣ 360).trans h))
      (by norm_num))
  have hO1 := map_subgroupOf_eq_bot hOK (AS76b.le_normalizer_oddCoreIn _) hφs (fun h =>
    absurd ((AS76b.odd_card_oddCoreIn (sec2K E)).of_dvd_nat ((by norm_num : 2 ∣ 360).trans h))
      (by decide))
  intro x hx
  obtain ⟨p, hp, o, ho, hxpo, -⟩ :=
    NXKernel.exists_mul_of_mem_sup (sec2P_le_centralizer_oddCoreIn hPK) hx
  have e : (⟨x, hPOK hx⟩ : ↥(sec2K E)) = ⟨p, hPK hp⟩ * ⟨o, hOK ho⟩ := Subtype.ext hxpo
  have hφp : φ ⟨p, hPK hp⟩ = 1 := by
    have h1 : φ ⟨p, hPK hp⟩ ∈ ((sec2P E).subgroupOf (sec2K E)).map φ := ⟨⟨p, hPK hp⟩, hp, rfl⟩
    rwa [hP1, mem_bot] at h1
  have hφo : φ ⟨o, hOK ho⟩ = 1 := by
    have h1 : φ ⟨o, hOK ho⟩ ∈ ((AS76b.oddCoreIn (sec2K E)).subgroupOf (sec2K E)).map φ :=
      ⟨⟨o, hOK ho⟩, ho, rfl⟩
    rwa [hO1, mem_bot] at h1
  have h1 : (⟨x, hPOK hx⟩ : ↥(sec2K E)) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, e, map_mul, hφp, hφo, mul_one]
  rw [hφker, mem_subgroupOf] at h1
  exact h1

theorem relIndex_sup_oddCoreIn {A E : Subgroup G}
    (hPOK : sec2P E ⊔ AS76b.oddCoreIn (sec2K E) ≤ sec2K E)
    (hidx : (sec2P E ⊔ AS76b.oddCoreIn (sec2K E)).relIndex (sec2K E) = 1080)
    {φ : ↥(sec2K E) →* alternatingGroup (Fin 6)} (hφs : Function.Surjective φ)
    (hφker : φ.ker = (sec2K E ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G)).subgroupOf (sec2K E)) :
    (sec2P E ⊔ AS76b.oddCoreIn (sec2K E)).relIndex
      (sec2K E ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G)) = 3 := by
  have hC360 : (sec2K E ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G)).relIndex (sec2K E) =
      360 := by
    rw [Subgroup.relIndex, ← hφker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφs,
      Subgroup.card_top, natCard_alternatingGroup_six]
  have h1 := Subgroup.relIndex_mul_relIndex _ _ (sec2K E) (sup_oddCoreIn_le_ker hPOK hφs hφker)
    inf_le_left
  rw [hidx, hC360] at h1
  omega

theorem step212Prod_of'
    (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h21 : Step21) (h211 : Step211)
    {A R : Subgroup G} {g : G} {E F : Subgroup G} (hS : Sec2Setting G A R g E F)
    (hFK : F ≤ sec2K E) :
    ∃ I : Subgroup G, sec2P E ≤ I ∧ I ⊓ AS76b.oddCoreIn (sec2K E) = ⊥ ∧
      I ⊔ AS76b.oddCoreIn (sec2K E) = sec2K E ∧
      AS76b.oddCoreIn (sec2K E) ≤ centralizer (I : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := hS.frame
  set K := sec2K E with hKdef
  set P := sec2P E with hPdef
  set O := AS76b.oddCoreIn K with hOdef
  set V := E ⊓ A with hVdef
  obtain ⟨hPOK, hidx, hperf, -, -, -, -, ⟨φ, hφs, hφker⟩, -⟩ := h211 G A R g E F hS
  have hKP : K ≤ normalizer (P : Set G) := sec2K_le_normalizer E
  have hP2 : IsPGroup 2 P := isPGroup_sec2P E
  have hPK : P ≤ K := le_sup_left.trans hPOK
  have hOK : O ≤ K := AS76b.oddCoreIn_le K
  have hOodd : Odd (Nat.card O) := AS76b.odd_card_oddCoreIn K
  have hKO : K ≤ normalizer (O : Set G) := AS76b.le_normalizer_oddCoreIn K
  have hKPO : K ≤ normalizer ((P ⊔ O : Subgroup G) : Set G) := NXKernel.le_normalizer_sup hKP hKO
  have hPO : P ≤ centralizer (O : Set G) := sec2P_le_centralizer_oddCoreIn hPK
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 6) (by rw [hF.cardE]; norm_num)
  have hEP : E ≤ P := le_sec2P hE2 le_normalizer le_rfl
  have hRP : R ≤ P := hF.R_le_E.trans hEP
  have hEO : E ≤ normalizer (O : Set G) := (hEP.trans hPK).trans hKO
  have hOA : O ≤ centralizer (A : Set G) := by
    by_cases hO1 : O = ⊥
    · rw [hO1]
      exact bot_le
    obtain ⟨X₀, hOX₀, hX₀⟩ := Finite.exists_le_maximal
      (p := fun Y : Subgroup G => Odd (Nat.card Y) ∧ E ≤ normalizer (Y : Set G)) ⟨hOodd, hEO⟩
    have hX₀ne : X₀ ≠ ⊥ := fun h => hO1 (le_bot_iff.mp (h ▸ hOX₀))
    obtain ⟨hconj, -, -, -⟩ := step17a_of_frame h4 h34 hE16 hF hS.type X₀ hX₀ hX₀ne
    have h1 := hconj 1 (one_mem _)
    rw [rightConjugate_one] at h1
    exact hOX₀.trans (h1.le.trans (AS76b.oddCoreIn_le _))
  have hAO : A ≤ centralizer (O : Set G) := Subgroup.le_centralizer_iff.mp hOA
  have hRO : R ≤ centralizer (O : Set G) := hRP.trans hPO
  have hFO : F ≤ centralizer (O : Set G) := hF.F_le.trans (sup_le hAO hRO)
  have hFV : ¬ F ≤ centralizer (V : Set G) := by
    intro hFV
    have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
    have hFE : F ≤ centralizer (E : Set G) := by
      intro f hf
      rw [mem_centralizer_iff]
      intro e he
      obtain ⟨a, ha, r, hr, rfl⟩ := exists_mul_of_mem_E hRA hF.R_le_E hF.E_le he
      have h1 : a * f = f * a := mem_centralizer_iff.mp (hFV hf) a ha
      have h2 : r * f = f * r := congrArg Subtype.val
        (hF.elemF.1.is_comm.comm ⟨r, hF.R_le_F hr⟩ ⟨f, hf⟩)
      calc a * r * f = a * (r * f) := by group
        _ = a * (f * r) := by rw [h2]
        _ = (a * f) * r := by group
        _ = f * a * r := by rw [h1]
        _ = f * (a * r) := by group
    have hFE' : F ≤ E := by
      have h1 := (h21 G A R g E F hS).1
      intro f hf
      rw [← h1]
      exact ⟨mem_sup_right hf, hFE hf⟩
    exact hF.ne (Subgroup.eq_of_le_of_card_ge hFE' (by rw [hF.cardE, hF.cardF])).symm
  obtain ⟨f₀, hf₀F, hf₀V⟩ := Set.not_subset.mp hFV
  set C := K ⊓ centralizer (V : Set G) with hCdef
  have hφker' : ∀ k : ↥K, φ k = 1 ↔ (k : G) ∈ C := fun k => by
    rw [← MonoidHom.mem_ker, hφker, mem_subgroupOf]
  have hs : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hPOC : P ⊔ O ≤ C := sup_oddCoreIn_le_ker hPOK hφs hφker
  have hCK : C ≤ K := inf_le_left
  have hCn : ∀ n ∈ K, ∀ c ∈ C, n * c * n⁻¹ ∈ C := by
    intro n hn c hc
    have h1 : ((⟨n, hn⟩ : ↥K) * ⟨c, hc.1⟩ * (⟨n, hn⟩ : ↥K)⁻¹ : ↥K) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, (hφker' ⟨c, hc.1⟩).mpr hc, mul_one, map_inv,
        mul_inv_cancel]
    exact (hφker' _).mp h1
  have hC3 : (P ⊔ O).relIndex C = 3 := relIndex_sup_oddCoreIn hPOK hidx hφs hφker
  have hcent : ∀ n ∈ K, ∀ κ ∈ C, n * κ * n⁻¹ * κ⁻¹ ∈ P ⊔ O :=
    (centralizes_of_relIndex_three hPOC hCK
      (fun n hn c hc => (mem_normalizer_iff.mp (hKPO hn) c).mp hc) hCn hC3 le_rfl hperf).2
  set N' : Subgroup ↥K := normalClosure ((F.subgroupOf K : Subgroup ↥K) : Set ↥K) with hN'
  set NF : Subgroup G := N'.map K.subtype with hNF
  have hNFK : NF ≤ K := map_subtype_le _
  have hNFn : K ≤ normalizer (NF : Set G) := by
    have : N'.Normal := inferInstance
    exact ABGTheoremB.le_normalizer_map_subtype _ _
  have hNFO : NF ≤ centralizer (O : Set G) := by
    have hCO : ((centralizer (O : Set G)).subgroupOf K).Normal := ⟨fun x hx k => by
      rw [mem_subgroupOf] at hx ⊢
      exact NXKernel.conj_mem_centralizer_of_mem_normalizer (hKO k.2) hx⟩
    have hle : N' ≤ (centralizer (O : Set G)).subgroupOf K :=
      normalClosure_le_normal fun x hx => hFO (mem_subgroupOf.mp hx)
    rintro _ ⟨x, hx, rfl⟩
    exact mem_subgroupOf.mp (hle hx)
  have hφNF : N'.map φ = ⊤ := by
    have hnorm : (N'.map φ).Normal := (inferInstance : N'.Normal).map φ hφs
    rcases hnorm.eq_bot_or_eq_top with h | h
    · exfalso
      apply hf₀V
      have h1 : φ ⟨f₀, hFK hf₀F⟩ ∈ N'.map φ :=
        ⟨⟨f₀, hFK hf₀F⟩, subset_normalClosure (show (⟨f₀, hFK hf₀F⟩ : ↥K) ∈
          (F.subgroupOf K : Set ↥K) from hf₀F), rfl⟩
      rw [h, mem_bot] at h1
      exact ((hφker' _).mp h1).2
    · exact h
  have hNFC : NF ⊔ C = K := by
    refine le_antisymm (sup_le hNFK hCK) fun k hk => ?_
    obtain ⟨n, hn, hnk⟩ : φ ⟨k, hk⟩ ∈ N'.map φ := by rw [hφNF]; exact mem_top _
    have h1 : (n⁻¹ * ⟨k, hk⟩ : ↥K) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hnk, inv_mul_cancel]
    have h2 : (k : G) = (n : G) * (((n⁻¹ * ⟨k, hk⟩ : ↥K)) : G) := by simp
    rw [h2]
    exact mul_mem (mem_sup_left ⟨n, hn, rfl⟩) (mem_sup_right ((hφker' _).mp h1))
  have hNFPO : NF ⊔ (P ⊔ O) = K := by
    refine le_antisymm (sup_le hNFK hPOK) ?_
    calc K = ⁅K, K⁆ ⊔ (P ⊔ O) := hperf.symm
      _ ≤ NF ⊔ (P ⊔ O) := by
        refine sup_le ?_ le_sup_right
        have hCC : ⁅C, C⁆ ≤ P ⊔ O := by
          rw [commutator_le]
          intro a ha b hb
          rw [commutatorElement_def]
          exact hcent a (hCK ha) b hb
        have h1 := NXKernel.commutator_sup_le (K := C) (C := NF) (fun c hc => hNFn (hCK hc))
        rw [sup_comm C NF, hNFC] at h1
        exact h1.trans (sup_le (hCC.trans le_sup_right) le_sup_left)
  set J := NF ⊔ P with hJ
  have hJK : J ≤ K := sup_le hNFK hPK
  have hJO : J ≤ centralizer (O : Set G) := sup_le hNFO hPO
  have hKJ : K ≤ normalizer (J : Set G) := NXKernel.le_normalizer_sup hNFn hKP
  have hJPO : J ⊔ (P ⊔ O) = K := by
    rw [hJ, sup_assoc, ← sup_assoc P P O, sup_idem, hNFPO]
  set I₀ := perfectCore J with hI₀
  have hI₀J : I₀ ≤ J := perfectCore_le J
  have hI₀PO : I₀ ⊔ (P ⊔ O) = K := NXKernel.perfectCore_sup_eq hJPO hperf hKPO
  have hI₀O : I₀ ⊓ O = ⊥ := by
    refine NXKernel.inf_eq_bot_of_perfect (N := K) (T := P) (O := O) (K := C) (L := K)
      (P := I₀) (Ω := Fin 6) (by simp) ((alternatingGroup (Fin 6)).subtype.comp φ) hP2 hOodd hKP
      hKO hPO (fun n => ?_) hCK hPOC hC3 (fun n => ?_) le_rfl ?_ hcent (perfectCore_perfect J)
      (hI₀J.trans hJK) (hI₀J.trans hJO) hI₀PO
    · rw [MonoidHom.comp_apply, ← hφker' n]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    · exact ⟨fun _ => (φ n).2, fun _ => n.2⟩
    · rintro σ hσ
      obtain ⟨k, hk⟩ := hφs ⟨σ, hσ⟩
      exact ⟨k, by rw [MonoidHom.comp_apply, hk]; rfl⟩
  have hKI₀ : K ≤ normalizer (I₀ : Set G) := fun k hk =>
    normalizer_le_normalizer_perfectCore J (hKJ hk)
  have hI₀O' : I₀ ≤ centralizer (O : Set G) := hI₀J.trans hJO
  refine ⟨I₀ ⊔ P, le_sup_right, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxI, hxO⟩ := hx
    have hx' : x ∈ ((I₀ ⊔ P : Subgroup G) : Set G) := hxI
    rw [coe_mul_of_right_le_normalizer_left I₀ P (hPK.trans hKI₀)] at hx'
    obtain ⟨i, hi, p, hp, rfl⟩ := hx'
    have hcomm : Commute i⁻¹ (i * p) :=
      (mem_centralizer_iff.mp (hI₀O' (I₀.inv_mem hi)) _ hxO).symm
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    have hp1 : (i⁻¹ * (i * p)) ^ 2 ^ k = 1 := by
      rw [inv_mul_cancel_left, ← hk]
      have h1 : (⟨p, hp⟩ : ↥P) ^ Nat.card ↥P = 1 := pow_card_eq_one'
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val h1
    exact (mem_bot).mpr (NXKernel.eq_one_of_mul_pow hI₀O hOodd (I₀.inv_mem hi) hxO hcomm hp1)
  · rw [sup_assoc]
    exact hI₀PO
  · rw [Subgroup.le_centralizer_iff]
    exact sup_le hI₀O' hPO

theorem step212Prod_of
    (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h21 : Step21) (h211 : Step211)
    (h212 : Step212) {A R : Subgroup G} {g : G} {E F : Subgroup G}
    (hS : Sec2Setting G A R g E F) :
    ∃ I : Subgroup G, sec2P E ≤ I ∧ I ⊓ AS76b.oddCoreIn (sec2K E) = ⊥ ∧
      I ⊔ AS76b.oddCoreIn (sec2K E) = sec2K E ∧
      AS76b.oddCoreIn (sec2K E) ≤ centralizer (I : Set G) := by
  obtain ⟨⟨T₀, hT₀, hT₀s⟩, h212b⟩ := h212 G A R g E F hS
  refine step212Prod_of' h4 h34 hE16 h21 h211 hS fun f hf => ?_
  exact ((h212b T₀ hT₀ hT₀s).2.1 (mem_sup_right (mem_sup_left hf))).2

end Sec2

end CFSG.ComponentClassification.AS81
