module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YLemma415
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma25
public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26Lemma29

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem eq_of_isSylowOf_of_le {K P P' S : Subgroup G} (hS : IsPGroup 2 S)
    (hP : IsSylowOf 2 P K) (hP' : IsSylowOf 2 P' K) (hPS : P ≤ S) (hP'S : P' ≤ S) :
    P = P' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM : IsPGroup 2 ↥(S ⊓ K) := hS.to_le inf_le_left
  have h1 := hP.eq_of_le (le_inf hPS hP.le) inf_le_right hM
  have h2 := hP'.eq_of_le (le_inf hP'S hP'.le) inf_le_right hM
  exact h1.symm.trans h2

theorem frattini_ne_bot_of_mul_self {P : Subgroup G} (hP : IsPGroup 2 P) {x : G} (hx : x ∈ P)
    (hxx : x * x ≠ 1) : frattini P ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 P) := ⟨hP⟩
  intro h
  have h1 := CFSG.pth_power_mem_frattini_of_isPGroup (R := P) (p := 2) ⟨x, hx⟩
  rw [h, mem_bot] at h1
  apply hxx
  have := congrArg Subtype.val h1
  simpa [pow_two] using this

theorem Assumption41.frattini_ne_bot (hΩ : Assumption41 Ω) {K R : Subgroup G} (hK : K ∈ Ω)
    (hR : IsSylowOf 2 R K) : frattini R ≠ ⊥ := by
  obtain ⟨U, hU⟩ := Assumption41.exists_rot hΩ hK hR
  obtain ⟨ρ, hρ, hρo⟩ := hU.exists_gen
  exact frattini_ne_bot_of_mul_self hU.isPGroup (hU.le (hρ ▸ mem_zpowers ρ))
    (hU.gen_mul_self_ne_one hρo)

omit [Finite G] in
theorem rightConjugate_le_of_mem {S P : Subgroup G} (hPS : P ≤ S) {s : G} (hs : s ∈ S) :
    AschbacherTightEmbedding.rightConjugate P s ≤ S := by
  intro x hx
  rw [mem_rightConjugate_iff] at hx
  have : x = s⁻¹ * (s * x * s⁻¹) * s := by group
  rw [this]
  exact mul_mem (mul_mem (inv_mem hs) (hPS hx)) hs

theorem commute_of_sylow (hΩ : Assumption41 Ω) {S T₁ T₂ J₁ J₂ : Subgroup G} (hS : IsPGroup 2 S)
    (hJ₁ : J₁ ∈ Ω) (hJ₂ : J₂ ∈ Ω) (hT₁ : IsSylowOf 2 T₁ J₁) (hT₂ : IsSylowOf 2 T₂ J₂)
    (hT₁S : T₁ ≤ S) (hT₂S : T₂ ≤ S) (hne : T₁ ≠ T₂) : ⁅T₁, T₂⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Δ : Set (Subgroup G) := {T | T ≤ S ∧ ∃ J ∈ Ω, IsSylowOf 2 T J}
  refine CFSG.ComponentClassification.Asc76X.lemma25 (Δ := Δ) hS (fun T hT => hT.1) ?_ ?_ ?_
    ?_ T₁ ⟨hT₁S, J₁, hJ₁, hT₁⟩ T₂ ⟨hT₂S, J₂, hJ₂, hT₂⟩ hne
  · rintro T ⟨hTS, J, hJ, hT⟩ s hs
    exact ⟨rightConjugate_le_of_mem hTS hs, _, hΩ.conj_mem J hJ s, isSylowOf_rightConjugate hT s⟩
  · rintro T ⟨-, J, hJ, hT⟩ T' ⟨-, J', hJ', hT'⟩
    exact Assumption41.card_sylow_eq hΩ hJ hJ' hT hT'
  · rintro T ⟨-, J, hJ, hT⟩
    exact Assumption41.frattini_ne_bot hΩ hJ hT
  · rintro T ⟨hTS, J, hJ, hT⟩ T' ⟨hT'S, J', hJ', hT'⟩ hTT'
    by_cases hJJ' : J = J'
    · subst hJJ'
      exact absurd (eq_of_isSylowOf_of_le hS hT hT' hTS hT'S) hTT'
    · exact Assumption41.inf_eq_bot hΩ hJ hJ' hJJ' hT.isPGroup hT.le hT'.le

@[expose] def IsRot (Ω : Set (Subgroup G)) (U : Subgroup G) : Prop :=
  ∃ K ∈ Ω, ∃ R : Subgroup G, IsSylowOf 2 R K ∧ U ≤ R ∧ IsCyclic U ∧ U.relIndex R = 2

omit [Finite G] in
theorem isRot_of {K R U : Subgroup G} (hK : K ∈ Ω) (hR : IsSylowOf 2 R K)
    (hU : IsDihedralRot U R) : IsRot Ω U :=
  ⟨K, hK, R, hR, hU.le, hU.isCyclic, hU.relIndex_eq⟩

theorem IsRot.exists_isDihedralRot (hΩ : Assumption41 Ω) {U : Subgroup G} (hU : IsRot Ω U) :
    ∃ K ∈ Ω, ∃ R : Subgroup G, IsSylowOf 2 R K ∧ IsDihedralRot U R := by
  obtain ⟨K, hK, R, hR, hUR, hUc, hUi⟩ := hU
  obtain ⟨U', hU'⟩ := Assumption41.exists_rot hΩ hK hR
  exact ⟨K, hK, R, hR, (hU'.eq_of_isCyclic hUR hUc hUi) ▸ hU'⟩

theorem eq_rot_of_le (hΩ : Assumption41 Ω) {K R R'' V U'' : Subgroup G} (hK : K ∈ Ω)
    (hR : IsSylowOf 2 R K) (hV : IsDihedralRot V R) (hR'' : IsSylowOf 2 R'' K)
    (hU'' : IsDihedralRot U'' R'') (hVR'' : V ≤ R'') : V = U'' := by
  refine hU''.eq_of_isCyclic hVR'' hV.isCyclic ?_
  have h1 := Subgroup.relIndex_mul_card V R''
  rw [inf_eq_left.mpr hVR'', ← Assumption41.card_sylow_eq hΩ hK hK hR hR'', hV.card_eq] at h1
  have := hV.four_le
  have h2 : 0 < Nat.card V := by omega
  exact Nat.eq_of_mul_eq_mul_right h2 (by rw [h1])

theorem eq_of_isRot_of_le (hΩ : Assumption41 Ω) {S K R R' V V' : Subgroup G} (hS : IsPGroup 2 S)
    (hK : K ∈ Ω) (hR : IsSylowOf 2 R K) (hV : IsDihedralRot V R) (hR' : IsSylowOf 2 R' K)
    (hV' : IsDihedralRot V' R') (hVS : V ≤ S) (hV'S : V' ≤ S) : V = V' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R'', hR'', hle⟩ := exists_isSylowOf_le (hS.to_le inf_le_left : IsPGroup 2 ↥(S ⊓ K))
    inf_le_right
  obtain ⟨U'', hU''⟩ := Assumption41.exists_rot hΩ hK hR''
  have h1 := eq_rot_of_le hΩ hK hR hV hR'' hU'' ((le_inf hVS (hV.le.trans hR.le)).trans hle)
  have h2 := eq_rot_of_le hΩ hK hR' hV' hR'' hU'' ((le_inf hV'S (hV'.le.trans hR'.le)).trans hle)
  exact h1.trans h2.symm

theorem commute_of_rot (hΩ : Assumption41 Ω) {S U U' : Subgroup G} (hS : IsPGroup 2 S)
    (hU : IsRot Ω U) (hU' : IsRot Ω U') (hUS : U ≤ S) (hU'S : U' ≤ S) {u u' : G} (hu : u ∈ U)
    (hu' : u' ∈ U') : u * u' = u' * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hUU : U = U'
  · subst hUU
    obtain ⟨K, -, R, -, hrot⟩ := hU.exists_isDihedralRot hΩ
    exact hrot.commute_of_mem hu hu'
  set Δ : Set (Subgroup G) := {V | V ≤ S ∧ IsRot Ω V}
  have h := CFSG.ComponentClassification.Asc76X.lemma25 (Δ := Δ) hS (fun V hV => hV.1) ?_ ?_ ?_
    ?_ U ⟨hUS, hU⟩ U' ⟨hU'S, hU'⟩ hUU
  · rw [commutator_eq_bot_iff_le_centralizer] at h
    exact (mem_centralizer_iff.mp (h hu) u' hu').symm
  · rintro V ⟨hVS, hV⟩ s hs
    obtain ⟨K, hK, R, hR, hrot⟩ := hV.exists_isDihedralRot hΩ
    exact ⟨rightConjugate_le_of_mem hVS hs,
      isRot_of (hΩ.conj_mem K hK s) (isSylowOf_rightConjugate hR s) (hrot.rightConjugate s)⟩
  · rintro V ⟨-, hV⟩ V' ⟨-, hV'⟩
    obtain ⟨K, hK, R, hR, hrot⟩ := hV.exists_isDihedralRot hΩ
    obtain ⟨K', hK', R', hR', hrot'⟩ := hV'.exists_isDihedralRot hΩ
    have h1 := hrot.card_eq
    have h2 := hrot'.card_eq
    rw [Assumption41.card_sylow_eq hΩ hK hK' hR hR'] at h1
    omega
  · rintro V ⟨-, hV⟩
    obtain ⟨K, -, R, -, hrot⟩ := hV.exists_isDihedralRot hΩ
    obtain ⟨ρ, hρ, hρo⟩ := hrot.exists_gen
    exact frattini_ne_bot_of_mul_self (hrot.isPGroup.to_le hrot.le) (hρ ▸ mem_zpowers ρ)
      (hrot.gen_mul_self_ne_one hρo)
  · rintro V ⟨hVS, hV⟩ V' ⟨hV'S, hV'⟩ hVV'
    obtain ⟨K, hK, R, hR, hrot⟩ := hV.exists_isDihedralRot hΩ
    obtain ⟨K', hK', R', hR', hrot'⟩ := hV'.exists_isDihedralRot hΩ
    by_cases hKK : K = K'
    · subst hKK
      exact absurd (eq_of_isRot_of_le hΩ hS hK hR hrot hR' hrot' hVS hV'S) hVV'
    · exact Assumption41.inf_eq_bot hΩ hK hK' hKK (hrot.isPGroup.to_le hrot.le)
        (hrot.le.trans hR.le) (hrot'.le.trans hR'.le)

omit [Finite G] in
theorem le_sec4W {S U : Subgroup G} (hUS : U ≤ S) (hU : IsRot Ω U) : U ≤ sec4W Ω S :=
  le_iSup_of_le U (le_iSup_of_le hUS (le_iSup_of_le hU le_rfl))

omit [Finite G] in
theorem sec4W_le (S : Subgroup G) : sec4W Ω S ≤ S :=
  iSup_le fun _ => iSup_le fun hUS => iSup_le fun _ => hUS

theorem isMulCommutative_sec4W (hΩ : Assumption41 Ω) {S : Subgroup G} (hS : IsPGroup 2 S) :
    IsMulCommutative (sec4W Ω S) := by
  have h : sec4W Ω S ≤ centralizer (sec4W Ω S : Set G) := by
    refine iSup_le fun U => iSup_le fun hUS => iSup_le fun hU => ?_
    rw [le_centralizer_iff]
    refine iSup_le fun U' => iSup_le fun hU'S => iSup_le fun hU' => ?_
    intro u' hu'
    rw [mem_centralizer_iff]
    intro u hu
    exact commute_of_rot hΩ hS hU hU' hUS hU'S hu hu'
  exact ⟨⟨fun a b => Subtype.ext ((mem_centralizer_iff.mp (h a.2)) b b.2).symm⟩⟩

omit [Finite G] in
theorem rightConjugate_le_iff {A B : Subgroup G} {g : G} :
    AschbacherTightEmbedding.rightConjugate A g ≤ B ↔
      A ≤ AschbacherTightEmbedding.rightConjugate B g⁻¹ := by
  constructor
  · intro h a ha
    rw [mem_rightConjugate_iff, inv_inv]
    apply h
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using ha
  · intro h x hx
    rw [mem_rightConjugate_iff] at hx
    have := h hx
    rw [mem_rightConjugate_iff, inv_inv] at this
    simpa [mul_assoc] using this

theorem rightConjugate_sec4W_le (hΩ : ∀ K ∈ Ω, ∀ g : G, rightConjugate K g ∈ Ω) (S : Subgroup G)
    (g : G) : AschbacherTightEmbedding.rightConjugate (sec4W Ω S) g ≤
      sec4W Ω (AschbacherTightEmbedding.rightConjugate S g) := by
  rw [rightConjugate_le_iff]
  refine iSup_le fun U => iSup_le fun hUS => iSup_le fun hU => ?_
  rw [← rightConjugate_le_iff]
  obtain ⟨K, hK, R, hR, hUR, hUc, hUi⟩ := hU
  refine le_sec4W (rightConjugate_le_rightConjugate hUS g) ⟨rightConjugate K g, hΩ K hK g,
    rightConjugate R g, ?_, rightConjugate_le_rightConjugate hUR g, ?_, ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isSylowOf_rightConjugate hR g
  · obtain ⟨ρ, hρ⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top U).mp hUc
    rw [← hρ, AschbacherTightEmbedding.rightConjugate, MonoidHom.map_zpowers]
    infer_instance
  · rw [relIndex_rightConjugate, hUi]

theorem rightConjugate_sec4W (hΩ : ∀ K ∈ Ω, ∀ g : G, rightConjugate K g ∈ Ω) (S : Subgroup G)
    (g : G) : AschbacherTightEmbedding.rightConjugate (sec4W Ω S) g =
      sec4W Ω (AschbacherTightEmbedding.rightConjugate S g) := by
  refine le_antisymm (rightConjugate_sec4W_le hΩ S g) ?_
  have h := rightConjugate_sec4W_le hΩ (AschbacherTightEmbedding.rightConjugate S g) g⁻¹
  rw [rightConjugate_rightConjugate_inv, rightConjugate_le_iff, inv_inv] at h
  exact h

theorem le_normalizer_sec4W (hΩ : ∀ K ∈ Ω, ∀ g : G, rightConjugate K g ∈ Ω) (S : Subgroup G) :
    S ≤ normalizer (sec4W Ω S : Set G) := by
  intro s hs
  rw [← rightConjugate_eq_self_iff, rightConjugate_sec4W hΩ S s,
    (rightConjugate_eq_self_iff S s).mpr (le_normalizer hs)]

theorem rot_le_sec4W (hΩ : Assumption41 Ω) {S J T V : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (hJ : J ∈ Ω) (hT : IsSylowOf 2 T J) (hV : IsDihedralRot V T)
    (hTW : T ≤ normalizer (sec4W Ω S : Set G)) : V ≤ sec4W Ω S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := sec4W Ω S
  have hSN : IsSylowOf 2 S (normalizer (W : Set G)) :=
    hS.of_le (le_normalizer_sec4W hΩ.conj_mem S) le_top
  obtain ⟨P, hP, hTP⟩ := exists_isSylowOf_le hT.isPGroup hTW
  obtain ⟨k, hkN, hk⟩ := CFSG.ComponentClassification.Asc76.L26.IsSylowOf.exists_conj_mem hSN hP
  have hVk : AschbacherTightEmbedding.rightConjugate V k ≤ S := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have := (hk _).mp (hTP (hV.le hx))
    simpa [mul_assoc] using this
  have hVkW : AschbacherTightEmbedding.rightConjugate V k ≤ W :=
    le_sec4W hVk (isRot_of (hΩ.conj_mem J hJ k) (isSylowOf_rightConjugate hT k)
      (hV.rightConjugate k))
  intro v hv
  have h1 : k⁻¹ * v * k ∈ W := hVkW (by rw [mem_rightConjugate_iff]; group; exact hv)
  have h2 := (mem_normalizer_iff.mp hkN _).mp h1
  simpa [mul_assoc] using h2

theorem isSylowOf_inf_of_isSubnormal {S N M : Subgroup G} (hN : CFSG.Assembly.IsSubnormal N M)
    (hS : IsSylowOf 2 (S ⊓ M) M) : IsSylowOf 2 (S ⊓ N) N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction hN with
  | refl => exact hS
  | step hHM hn _ ih =>
    have h := (ih hS).inf_of_le_normalizer hHM
      ((normal_subgroupOf_iff_le_normalizer hHM).mp hn)
    rwa [inf_assoc, inf_eq_right.mpr hHM] at h

theorem normal_of_isSubnormal (hΩ : Assumption41 Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hKs : CFSG.Assembly.IsSubnormal K ⊤) : K.Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJN : ∀ J ∈ Ω, J ≤ normalizer (K : Set G) := by
    intro J hJ
    by_cases hJK : J = K
    · rw [hJK]
      exact le_normalizer
    rw [← hΩ.perfect J hJ]
    refine (closure_le _).mpr ?_
    rintro x ⟨hxJ, k, hxk⟩
    have hx2 : IsPGroup 2 (zpowers x) := isPGroup_zpowers_of_pow_eq_one hxk
    obtain ⟨T, hT, hxT⟩ := exists_isSylowOf_le hx2 ((zpowers_le).mpr hxJ)
    obtain ⟨S, hS, hTS⟩ := exists_isSylowOf_le hT.isPGroup (le_top : T ≤ ⊤)
    have hS' : IsSylowOf 2 (S ⊓ ⊤) ⊤ := by rwa [inf_top_eq]
    have hP := isSylowOf_inf_of_isSubnormal hKs hS'
    obtain ⟨U, hU⟩ := Assumption41.exists_rot hΩ hK hP
    have hTP : T ≠ S ⊓ K := by
      intro h
      apply hU.ne_bot
      have h1 := Assumption41.inf_eq_bot hΩ hJ hK hJK hT.isPGroup hT.le hP.le
      rwa [h, inf_idem] at h1
    have hc := commute_of_sylow hΩ hS.isPGroup hJ hK hT hP hTS inf_le_left hTP
    rw [commutator_eq_bot_iff_le_centralizer] at hc
    exact centralizer_two_subgroup_le K (S ⊓ K) (Assumption41.tightlyEmbedded hΩ hK)
      hP.isPGroup inf_le_right hU.ne_bot (hc (hxT (mem_zpowers x)))
  have htop : normalizer (K : Set G) = ⊤ := by
    rw [eq_top_iff, ← hΩ.generates]
    exact sSup_le hJN
  exact normalizer_eq_top_iff.mp htop

end CFSG.ComponentClassification.Asc76.Sec4
