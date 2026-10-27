module

public import CFSG.CGT.PushingUpLit.Defs
public import CFSG.CGT.PushingUp.PartTwo
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellThompson
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBaumannTools
import CFSG.Quasithin.SteinbergBQThompsonSeedBaumannCentralizer
public import CFSG.CGT.PushingUp.TwoLocals

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2 CFSG.QuasithinUnique.Setup.Campbell
  CFSG.RankThree.PartOne CFSG.CGT.PushingUp

variable {G : Type} [Group G]

theorem jIn_eq_elemThompsonIn (P : Subgroup G) : jIn P = elemThompsonIn 2 P := rfl

theorem jIn_le (P : Subgroup G) : jIn P ≤ P := map_subtype_le _

theorem isPGroup_jIn {P : Subgroup G} (hP : IsPGroup 2 P) : IsPGroup 2 (jIn P) :=
  hP.to_le (jIn_le P)

theorem jIn_jIn [Finite G] (P : Subgroup G) : jIn (jIn P) = jIn P :=
  SteinbergBQ.map_elemThompson_subtype_eq_of_le (p := 2) (jIn_le P) le_rfl

namespace Nine

theorem pRank_map_injective {H H' : Type*} [Group H] [Group H'] (f : H →* H')
    (hf : Function.Injective f) (A : Subgroup H) (p : ℕ) : pRank p ↥(A.map f) = pRank p ↥A :=
  (pRank_eq_of_mulEquiv (A.equivMapOfInjective f hf) p).symm

theorem pRank_bot [Finite G] : pRank 2 ↥(⊥ : Subgroup G) = 0 := by
  obtain ⟨A, -, hc⟩ := exists_card_eq_pow_pRank (↥(⊥ : Subgroup G)) 2
  have h1 : Nat.card A ≤ Nat.card ↥(⊥ : Subgroup G) := A.card_le_card_group
  rw [Subgroup.card_bot, hc] at h1
  by_contra h
  have : 1 < 2 ^ pRank 2 ↥(⊥ : Subgroup G) := Nat.one_lt_two_pow h
  omega

theorem card_lt_of_lt [Finite G] {P Q : Subgroup G} (h : P < Q) : Nat.card P < Nat.card Q :=
  lt_of_le_of_ne (Subgroup.card_le_of_le h.le) fun heq =>
    h.ne (Subgroup.eq_of_le_of_card_ge h.le heq.ge)

theorem map_map_equiv_symm (c : G ≃* G) (X : Subgroup G) :
    (X.map c.symm.toMonoidHom).map c.toMonoidHom = X := by
  rw [Subgroup.map_map]
  have h : c.toMonoidHom.comp c.symm.toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [h, Subgroup.map_id]

theorem map_map_symm_equiv (c : G ≃* G) (X : Subgroup G) :
    (X.map c.toMonoidHom).map c.symm.toMonoidHom = X := by
  rw [Subgroup.map_map]
  have h : c.symm.toMonoidHom.comp c.toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [h, Subgroup.map_id]

theorem centralizer_map_equiv (c : G ≃* G) (A : Subgroup G) :
    Subgroup.centralizer ((A.map c.toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.centralizer (A : Set G)).map c.toMonoidHom := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    apply c.injective
    simpa using h (c a) (Subgroup.mem_map_of_mem c.toMonoidHom ha)
  · rintro h _ ⟨a, ha, rfl⟩
    simpa using congrArg c (h a ha)

theorem characteristic_map_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {N : Subgroup X} (hN : N.Characteristic) : (N.map e.toMonoidHom).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have h := Subgroup.mem_comap.mp
    ((Subgroup.characteristic_iff_le_comap.mp hN) ((e.trans φ).trans e.symm) hx)
  exact ⟨_, h, by simp⟩

theorem characteristic_subgroupOf_map_equiv (c : G ≃* G) {B S : Subgroup G}
    (h : (B.subgroupOf S).Characteristic) :
    ((B.map c.toMonoidHom).subgroupOf (S.map c.toMonoidHom)).Characteristic := by
  let e : ↥S ≃* ↥(S.map c.toMonoidHom) := S.equivMapOfInjective c.toMonoidHom c.injective
  have hmap : (B.subgroupOf S).map e.toMonoidHom =
      (B.map c.toMonoidHom).subgroupOf (S.map c.toMonoidHom) := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    refine (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).trans ?_
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_map_iff_mem (f := c.toMonoidHom) c.injective).symm
  rw [← hmap]
  exact characteristic_map_equiv e h

theorem exists_isSylowOf_ge [Finite G] {K Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQK : Q ≤ K) :
    ∃ S : Subgroup G, IsSylowOf 2 S K ∧ Q ≤ S := by
  obtain ⟨S₀, hS₀⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(S₀ : Subgroup K).map K.subtype, ⟨Subgroup.map_subtype_le _, S₀.isPGroup'.map _, ?_⟩,
    fun x hx => ⟨⟨x, hQK hx⟩, hS₀ (show (⟨x, hQK hx⟩ : K) ∈ Q.subgroupOf K from hx), rfl⟩⟩
  have h : ((S₀ : Subgroup K).map K.subtype).subgroupOf K = (S₀ : Subgroup K) :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have := S₀.not_dvd_index
  rwa [← h] at this

theorem le_of_isSylowOf_of_le [Finite G] {T N R : Subgroup G} (hT : IsSylowOf 2 T N)
    (hR : IsPGroup 2 R) (hTR : T ≤ R) (hRN : R ≤ N) : R ≤ T := by
  obtain ⟨k, hk⟩ := hR.index (T.subgroupOf R)
  have hk' : T.relIndex R = 2 ^ k := hk
  have h1 := Subgroup.relIndex_mul_relIndex T R N hTR hRN
  by_contra hRT
  have hne : T.relIndex R ≠ 1 := fun h => hRT (Subgroup.relIndex_eq_one.mp h)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (by rw [hk', pow_zero])
  exact hT.2.2 (h1 ▸ dvd_mul_of_dvd_left (hk' ▸ dvd_pow_self 2 hk0) _)

theorem le_of_isSylowOf_of_normal [Finite G] {K S N : Subgroup G} (hS : IsSylowOf 2 S K)
    (hN : IsPGroup 2 N) (hNK : N ≤ K) (hn : K ≤ Subgroup.normalizer (N : Set G)) : N ≤ S := by
  have : (Subgroup.comap K.subtype N).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hn
  have hS' : IsPGroup 2 (S.subgroupOf K) := hS.2.1.comap_subtype (K := K)
  have hidx : ¬ 2 ∣ (S.subgroupOf K).index := hS.2.2
  have hle := (hN.comap_subtype (K := K)).le_sylow_of_normal (hS'.toSylow hidx)
  intro x hx
  exact hle (show (⟨x, hNK hx⟩ : K) ∈ N.subgroupOf K from hx)

theorem eq_of_inf_normalizer_le [Finite G] {P Q : Subgroup G} (hQ : IsPGroup 2 Q) (hPQ : P ≤ Q)
    (h : Q ⊓ Subgroup.normalizer (P : Set G) ≤ P) : P = Q := by
  by_contra hne
  obtain ⟨x, hxQ, hxN, hxP⟩ := exists_mem_normalizer_not_mem hQ hPQ hne
  exact hxP (h ⟨hxQ, hxN⟩)

theorem isSylowOf_top_or_exists_gt [Finite G] {S : Subgroup G} (hS : IsPGroup 2 S) :
    IsSylowOf 2 S ⊤ ∨
      ∃ P : Subgroup G, IsPGroup 2 P ∧ P ≤ Subgroup.normalizer (S : Set G) ∧ S < P := by
  obtain ⟨S', hS'top, hSS'⟩ := exists_isSylowOf_ge (K := ⊤) hS le_top
  by_cases heq : S = S'
  · left
    rw [heq]
    exact hS'top
  · right
    obtain ⟨x, hxS', hxN, hxS⟩ := exists_mem_normalizer_not_mem hS'top.2.1 hSS' heq
    refine ⟨S ⊔ Subgroup.zpowers x,
      hS'top.2.1.to_le (sup_le hSS' (Subgroup.zpowers_le.mpr hxS')),
      sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hxN),
      lt_of_le_of_ne le_sup_left fun h => hxS ?_⟩
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

theorem exists_isMaximalTwoLocal_ge_of_isCharacteristicP [Finite G] {K : Subgroup G}
    (hK : IsCharacteristicP 2 ↥K) (hK1 : K ≠ ⊥) :
    ∃ H : Subgroup G, K ≤ H ∧ IsMaximalTwoLocal H := by
  have hQ1 : oTwoIn K ≠ ⊥ := by
    intro h
    have hp : pCore 2 ↥K = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp h
    apply hK1
    rw [eq_bot_iff]
    intro k hk
    have hkc : (⟨k, hk⟩ : ↥K) ∈ Subgroup.centralizer ((pCore 2 ↥K : Subgroup ↥K) : Set ↥K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [SetLike.mem_coe, hp, Subgroup.mem_bot] at hz
      subst hz
      simp
    have := hK hkc
    rw [hp, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
  have hQ2 : IsPGroup 2 (oTwoIn K) := (pCore_isPGroup (p := 2) (G := ↥K)).map K.subtype
  have hKN : K ≤ Subgroup.normalizer (oTwoIn K : Set G) := by
    intro k hk
    have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hk
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => conj_mem_oTwoIn hkN hh, fun hh => ?_⟩
    have := conj_mem_oTwoIn (inv_mem hkN) hh
    have e : k⁻¹ * (k * h * k⁻¹) * k⁻¹⁻¹ = h := by group
    rwa [e] at this
  obtain ⟨H, hH, hmax⟩ := exists_isMaximalTwoLocal_ge (isPLocal_normalizer_of_isPGroup hQ2 hQ1)
  exact ⟨H, hKN.trans hH, hmax⟩

end Nine

open Nine

theorem pRank_jIn [Finite G] (P : Subgroup G) : pRank 2 ↥(jIn P) = pRank 2 ↥P :=
  (pRank_map_injective P.subtype P.subtype_injective (elemThompson ↥P 2) 2).trans
    (pRank_eq_of_elemThompson_le (p := 2) (Y := elemThompson ↥P 2) le_rfl)

theorem jIn_mono_of_pRank_eq [Finite G] {I P : Subgroup G} (hIP : I ≤ P)
    (hr : pRank 2 ↥I = pRank 2 ↥P) : jIn I ≤ jIn P := by
  rw [jIn_eq_elemThompsonIn, jIn_eq_elemThompsonIn, elemThompsonIn_eq]
  refine sSup_le fun A hA => le_elemThompsonIn (mem_elemFamilyIn.mpr ?_)
  obtain ⟨hAI, hAe, hAc⟩ := mem_elemFamilyIn.mp hA
  exact ⟨hAI.trans hIP, hAe, by rw [hAc, hr]⟩

theorem isElementaryAbelian_omegaOneCenterIn (P : Subgroup G) :
    IsElementaryAbelian 2 (omegaOneCenterIn P) :=
  isElementaryAbelian_iff.mpr ⟨fun a ha _ hb =>
    (mem_omegaOneCenterIn_iff.mp hb).2.1 a (mem_omegaOneCenterIn_iff.mp ha).1,
    fun _ ha => (mem_omegaOneCenterIn_iff.mp ha).2.2⟩

theorem omegaOneCenterIn_le_of_mem_elemFamilyIn [Finite G] {P A : Subgroup G}
    (hA : A ∈ elemFamilyIn 2 P) : omegaOneCenterIn P ≤ A := by
  obtain ⟨hAP, hAe, hAc⟩ := mem_elemFamilyIn.mp hA
  have hE := isElementaryAbelian_omegaOneCenterIn P
  have hcomm : omegaOneCenterIn P ≤ Subgroup.centralizer (A : Set G) := fun z hz =>
    Subgroup.mem_centralizer_iff.mpr fun a ha => (mem_omegaOneCenterIn_iff.mp hz).2.1 a (hAP ha)
  have hsup := isElementaryAbelian_sup_of_le_centralizer hAe hE hcomm
  have hle : Nat.card ↥(A ⊔ omegaOneCenterIn P) ≤ Nat.card ↥A := by
    rw [hAc]
    exact card_le_pow_pRank_of_le (sup_le hAP (omegaOneCenterIn_le P)) hsup
  have heq : A = A ⊔ omegaOneCenterIn P := Subgroup.eq_of_le_of_card_ge le_sup_left hle
  exact le_sup_right.trans heq.ge

theorem exists_mem_elemFamilyIn [Finite G] (P : Subgroup G) : ∃ A, A ∈ elemFamilyIn 2 P := by
  obtain ⟨A, hA⟩ := elemThompsonFamily_nonempty (↥P) 2
  exact ⟨A.map P.subtype, A, hA, rfl⟩

theorem omegaOneCenterIn_le_jIn [Finite G] (P : Subgroup G) : omegaOneCenterIn P ≤ jIn P := by
  obtain ⟨A, hA⟩ := exists_mem_elemFamilyIn P
  exact (omegaOneCenterIn_le_of_mem_elemFamilyIn hA).trans (le_elemThompsonIn hA)

theorem jIn_ne_bot [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) : jIn P ≠ ⊥ :=
  fun h => omegaOneCenterIn_ne_bot hP hP1
    (le_bot_iff.mp ((omegaOneCenterIn_le_jIn P).trans h.le))

theorem Nine.one_le_pRank [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) :
    1 ≤ pRank 2 ↥P := by
  have hE := isElementaryAbelian_omegaOneCenterIn P
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hP.to_le (omegaOneCenterIn_le P))
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hn
    exact omegaOneCenterIn_ne_bot hP hP1 hn
  exact Nat.one_le_iff_ne_zero.mpr hn0 |>.trans (pRank_le_of_card_le (omegaOneCenterIn_le P) hE hn)

theorem characteristic_jIn_subgroupOf [Finite G] (P : Subgroup G) :
    ((jIn P).subgroupOf P).Characteristic := by
  have h : (jIn P).subgroupOf P = elemThompson ↥P 2 :=
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  rw [h]
  exact elemThompson_characteristic ↥P 2

theorem normalizer_le_normalizer_jIn [Finite G] (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (jIn P : Set G) :=
  normalizer_le_normalizer_of_characteristic' (jIn_le P) (characteristic_jIn_subgroupOf P)

theorem eq_of_jIn_eq_of_inf_normalizer_le [Finite G] {T P I : Subgroup G} (hT : IsPGroup 2 T)
    (hPT : P ≤ T) (hJ : jIn P = I) (hN : T ⊓ Subgroup.normalizer (I : Set G) ≤ P) : P = T := by
  by_contra hne
  obtain ⟨x, hxT, hxN, hxP⟩ := exists_mem_normalizer_not_mem hT hPT hne
  refine hxP (hN ⟨hxT, ?_⟩)
  rw [← hJ]
  exact normalizer_le_normalizer_jIn P hxN

theorem omegaOneCenterIn_le_omegaOneCenterIn {P Q : Subgroup G} (hPQ : P ≤ Q)
    (hE : omegaOneCenterIn Q ≤ P) : omegaOneCenterIn Q ≤ omegaOneCenterIn P := fun z hz => by
  obtain ⟨-, hzc, hz2⟩ := mem_omegaOneCenterIn_iff.mp hz
  exact mem_omegaOneCenterIn_iff.mpr ⟨hE hz, fun k hk => hzc k (hPQ hk), hz2⟩

theorem jIn_le_pushingUpS [Finite G] (P : Subgroup G) : jIn P ≤ pushingUpS P := by
  intro x hx
  refine Subgroup.mem_inf.mpr ⟨jIn_le P hx, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  have hz' : z ∈ (elemThompsonCenterTorsion ↥P 2).map P.subtype := hz
  exact ((SteinbergBQ.mem_map_elemThompsonCenterTorsion_iff (p := 2)).mp hz').2.2 x hx |>.symm

theorem jIn_pushingUpS [Finite G] (P : Subgroup G) : jIn (pushingUpS P) = jIn P :=
  SteinbergBQ.map_elemThompson_subtype_eq_of_le (p := 2) (pushingUpS_le P) (jIn_le_pushingUpS P)

theorem characteristic_jIn_subgroupOf_pushingUpS [Finite G] (P : Subgroup G) :
    ((jIn P).subgroupOf (pushingUpS P)).Characteristic := by
  rw [← jIn_pushingUpS P]
  exact characteristic_jIn_subgroupOf _

theorem centralizer_le_characteristicCoreStar (T : Subgroup G) :
    Subgroup.centralizer (omegaOneCenterIn T : Set G) ≤ characteristicCoreStar T :=
  le_sup_left

theorem le_characteristicCoreStar (T : Subgroup G) : T ≤ characteristicCoreStar T :=
  (le_centralizer_of_le_omegaOneCenterIn le_rfl).trans le_sup_left

theorem normalizer_le_characteristicCoreStar {T B : Subgroup G} (hB1 : B ≠ ⊥)
    (hBS : B ≤ pushingUpS T) (hBc : (B.subgroupOf (pushingUpS T)).Characteristic) :
    Subgroup.normalizer (B : Set G) ≤ characteristicCoreStar T :=
  le_sup_of_le_right (le_iSup₂_of_le B ⟨hB1, hBS, hBc⟩ le_rfl)

theorem characteristicCoreStar_le {T M : Subgroup G}
    (h1 : Subgroup.centralizer (omegaOneCenterIn T : Set G) ≤ M)
    (h2 : ∀ B : Subgroup G, B ≠ ⊥ → B ≤ pushingUpS T →
      (B.subgroupOf (pushingUpS T)).Characteristic → Subgroup.normalizer (B : Set G) ≤ M) :
    characteristicCoreStar T ≤ M :=
  sup_le h1 (iSup₂_le fun B hB => h2 B hB.1 hB.2.1 hB.2.2)

theorem normalizer_jIn_le_characteristicCoreStar [Finite G] {T : Subgroup G} (hT : IsPGroup 2 T)
    (hT1 : T ≠ ⊥) : Subgroup.normalizer (jIn T : Set G) ≤ characteristicCoreStar T :=
  normalizer_le_characteristicCoreStar (jIn_ne_bot hT hT1) (jIn_le_pushingUpS T)
    (characteristic_jIn_subgroupOf_pushingUpS T)

theorem jIn_map_equiv [Finite G] (c : G ≃* G) (P : Subgroup G) :
    jIn (P.map c.toMonoidHom) = (jIn P).map c.toMonoidHom := by
  let e : ↥P ≃* ↥(P.map c.toMonoidHom) := P.equivMapOfInjective c.toMonoidHom c.injective
  have hcomp : (P.map c.toMonoidHom).subtype.comp e.toMonoidHom =
      c.toMonoidHom.comp P.subtype := by
    ext x
    rfl
  show (elemThompson ↥(P.map c.toMonoidHom) 2).map (P.map c.toMonoidHom).subtype =
    ((elemThompson ↥P 2).map P.subtype).map c.toMonoidHom
  rw [← SteinbergBQ.map_elemThompson_mulEquiv e 2, Subgroup.map_map, hcomp, ← Subgroup.map_map]

theorem omegaOneCenterIn_map_equiv (c : G ≃* G) (P : Subgroup G) :
    omegaOneCenterIn (P.map c.toMonoidHom) = (omegaOneCenterIn P).map c.toMonoidHom := by
  ext z
  constructor
  · intro hz
    obtain ⟨hzP, hzc, hz2⟩ := mem_omegaOneCenterIn_iff.mp hz
    obtain ⟨y, hy, rfl⟩ := hzP
    refine ⟨y, mem_omegaOneCenterIn_iff.mpr ⟨hy, fun k hk => ?_, ?_⟩, rfl⟩
    · apply c.injective
      simpa using hzc (c k) ⟨k, hk, rfl⟩
    · apply c.injective
      simpa using hz2
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyP, hyc, hy2⟩ := mem_omegaOneCenterIn_iff.mp hy
    refine mem_omegaOneCenterIn_iff.mpr ⟨⟨y, hyP, rfl⟩, ?_, ?_⟩
    · rintro _ ⟨k, hk, rfl⟩
      rw [← map_mul, ← map_mul, hyc k hk]
    · rw [← map_pow, hy2, map_one]

theorem pushingUpS_map_equiv [Finite G] (c : G ≃* G) (P : Subgroup G) :
    pushingUpS (P.map c.toMonoidHom) = (pushingUpS P).map c.toMonoidHom := by
  have hE : inSubgroup (fun K _ => elemThompsonCenterTorsion K 2) (P.map c.toMonoidHom) =
      (inSubgroup (fun K _ => elemThompsonCenterTorsion K 2) P).map c.toMonoidHom := by
    let e : ↥P ≃* ↥(P.map c.toMonoidHom) := P.equivMapOfInjective c.toMonoidHom c.injective
    have hcomp : (P.map c.toMonoidHom).subtype.comp e.toMonoidHom =
        c.toMonoidHom.comp P.subtype := by
      ext x
      rfl
    show (elemThompsonCenterTorsion ↥(P.map c.toMonoidHom) 2).map (P.map c.toMonoidHom).subtype =
      ((elemThompsonCenterTorsion ↥P 2).map P.subtype).map c.toMonoidHom
    rw [← elemThompsonCenterTorsion_map_mulEquiv e 2, Subgroup.map_map, hcomp,
      ← Subgroup.map_map]
  unfold pushingUpS
  rw [Subgroup.map_inf_eq _ _ c.toMonoidHom c.injective, hE, centralizer_map_equiv]

theorem characteristicCoreStar_map_le [Finite G] (c : G ≃* G) (T : Subgroup G) :
    characteristicCoreStar (T.map c.toMonoidHom) ≤
      (characteristicCoreStar T).map c.toMonoidHom := by
  refine characteristicCoreStar_le ?_ fun B hB1 hBS hBc => ?_
  · rw [omegaOneCenterIn_map_equiv, centralizer_map_equiv]
    exact Subgroup.map_mono (centralizer_le_characteristicCoreStar T)
  · have hS : (pushingUpS (T.map c.toMonoidHom)).map c.symm.toMonoidHom = pushingUpS T := by
      rw [pushingUpS_map_equiv, map_map_symm_equiv]
    have hBS' : B.map c.symm.toMonoidHom ≤ pushingUpS T := by
      rw [← hS]
      exact Subgroup.map_mono hBS
    have hBc' := characteristic_subgroupOf_map_equiv c.symm hBc
    rw [hS] at hBc'
    have hB1' : B.map c.symm.toMonoidHom ≠ ⊥ := fun h =>
      hB1 ((Subgroup.map_eq_bot_iff_of_injective B c.symm.injective).mp h)
    have h := normalizer_le_characteristicCoreStar hB1' hBS' hBc'
    have hN := Subgroup.map_equiv_normalizer_eq (B.map c.symm.toMonoidHom) c
    rw [map_map_equiv_symm] at hN
    rw [← hN]
    exact Subgroup.map_mono h

end CFSG.CGT.PushingUpLit
