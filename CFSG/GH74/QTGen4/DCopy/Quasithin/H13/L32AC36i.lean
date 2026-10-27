module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A770k
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC36e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC36g
public import CFSG.Quasithin.Background.H16TwoM22
public import CFSG.Quasithin.H13.L32AC36b
public import CFSG.Quasithin.H13.L32AC36f
public import CFSG.Quasithin.H13.L32AC36h
public import CFSG.Quasithin.H13.L32AC50h

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H K : Subgroup G}

theorem false_of_m22_core_F4
    (hIrr : MathieuSmallIrr22) (hA21 : AsA21SQTKSection) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h56 : AsB56) (hD310 : D310) (hD391 : D391)
    (hI4 : Insp4) (hFine : F918Fine4) (h16 : CFSG.Quasithin.H.Mathieu.StmtH16_2_1M22)
    (S : Setting147 G T L V H) (hF : HypF918 T V L (fsuV1 T V) V H K)
    (hK₀ : conjClosure K T = K) (hHeq : H = conjClosure K T ⊔ T) (hl1K : l1 T L V ≤ K)
    (hM : IsSporadic .M22 (cStar K)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨I, hV₁I, hIU, hirrT, hHI, hVI⟩ :=
    exists_I_m22_F4 h1222 h1332 h1334 h56 hD310 hD391 hI4 hFine S hF hK₀ hHeq hl1K hM
  have := factElem hF hIU
  have hcode := code_m22 hIrr hA21 S hF hK₀ hM hV₁I hIU hirrT hHI
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hKnH : H ≤ Subgroup.normalizer (K : Set G) := hK₀ ▸ hF.K₀_normal
  have hTH : T ≤ H := hF.T_le_H
  set Ψ := psiI hF hIU hV₁I hHI with hΨ

  have hker : (pCoreOf 2 K).subgroupOf K ≤ (Ψ.comp (Subgroup.inclusion hKH)).ker := by
    intro k hk
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact psiI_eq_one_of_mem_pCoreOf hF hIU hV₁I hHI
      (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hF.K_cComp)
        (Subgroup.mem_subgroupOf.mp hk))
  set ψb : cStar K →* MulAut ↥(subM (fsuV1 T V) (conjClosure I H) I) :=
    QuotientGroup.lift _ (Ψ.comp (Subgroup.inclusion hKH)) hker with hψb
  have hψmk : ∀ k : ↥K, ψb (QuotientGroup.mk k) = Ψ (Subgroup.inclusion hKH k) := fun k => rfl
  have hrange : ψb.range =
      autSub (autIH (fsuV1 T V) I H K) (subM (fsuV1 T V) (conjClosure I H) I) := by
    rw [← map_psiI hF hIU hV₁I hHI hKH]
    ext φ
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨Subgroup.inclusion hKH k, k.2, (hψmk k).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨QuotientGroup.mk ⟨(x : G), hx⟩, hψmk _⟩

  have hirr' : subM (fsuV1 T V) (conjClosure I H) I ∈
      IrrPlusOn (autIH (fsuV1 T V) I H (conjClosure K T))
        (orbSup (autIH (fsuV1 T V) I H T) (subM (fsuV1 T V) (conjClosure I H) I))
        (autIH (fsuV1 T V) I H T) := hirrT
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  have hne : autIH (fsuV1 T V) I H K ≠ ⊥ := by
    rw [autIH_eq_map hF hKH]
    exact map_K_ne_bot hF hIU hnt
  have e2 := autSubEquivOfFaithful (autIH_le_stabSub hF hIU hV₁I hHI hKH)
    (autIH_inf_centSub hHI K)
  have hS := isSimpleGroup_of_m22 hM
  have hψinj : Function.Injective ψb := by
    refine injective_of_isSimpleGroup ψb ?_
    obtain ⟨⟨g, hg⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    have hφ : ((e2 ⟨g, hg⟩ : ↥(autSub (autIH (fsuV1 T V) I H K)
        (subM (fsuV1 T V) (conjClosure I H) I))) :
          MulAut ↥(subM (fsuV1 T V) (conjClosure I H) I)) ∈ ψb.range := by
      rw [hrange]
      exact (e2 ⟨g, hg⟩).2
    obtain ⟨s, hs⟩ := hφ
    refine ⟨s, fun h1 => hg1 ?_⟩
    have h2 : e2 ⟨g, hg⟩ = 1 := Subtype.ext (hs.symm.trans h1)
    exact e2.injective (h2.trans (map_one e2).symm)

  have hTK : IsSylowTwoOf (T ⊓ K) K := B6.isSylowTwoOf_inf_normal hF.sylow_H hKH hKnH
  set φK : ↥K →* cStar K := QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K) with hφK
  have hφs : Function.Surjective φK := QuotientGroup.mk'_surjective _
  have hSst : IsSylowTwoOf (((T ⊓ K).subgroupOf K).map φK) ⊤ := by
    have h1 : IsSylowTwoOf ((T ⊓ K).subgroupOf K) (⊤ : Subgroup ↥K) :=
      (A312.isSylowTwoOf_top_iff_map K ((T ⊓ K).subgroupOf K)).mpr
        (by rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_right])
    exact A312.isSylowTwoOf_top_map φK hφs h1
  set X := l1 T L V ⊔ (T ⊓ K) with hX
  have hXK : X ≤ K := sup_le hl1K inf_le_right
  have hO2TK : pCoreOf 2 K ≤ T ⊓ K := pCoreOf_le_of_isSylowTwoOf hTK
  have hSP : ((T ⊓ K).subgroupOf K).map φK ≤ (X.subgroupOf K).map φK :=
    Subgroup.map_mono fun _ hk => Subgroup.mem_subgroupOf.mpr
      ((le_sup_right : T ⊓ K ≤ X) (Subgroup.mem_subgroupOf.mp hk))
  have hidx : (((T ⊓ K).subgroupOf K).map φK).relIndex ((X.subgroupOf K).map φK) = 3 := by
    rw [Subgroup.relIndex_map_map, QuotientGroup.ker_mk']
    have h1 : (T ⊓ K).subgroupOf K ⊔ (pCoreOf 2 K).subgroupOf K = (T ⊓ K).subgroupOf K :=
      sup_eq_left.mpr fun _ hk =>
        Subgroup.mem_subgroupOf.mpr (hO2TK (Subgroup.mem_subgroupOf.mp hk))
    have h2 : X.subgroupOf K ⊔ (pCoreOf 2 K).subgroupOf K = X.subgroupOf K :=
      sup_eq_left.mpr fun _ hk => Subgroup.mem_subgroupOf.mpr
        ((le_sup_right : T ⊓ K ≤ X) (hO2TK (Subgroup.mem_subgroupOf.mp hk)))
    rw [h1, h2, Subgroup.relIndex_subgroupOf hXK]
    exact relIndex_TK_F4 h1222 h1332 h1334 S hl1K
  obtain ⟨Nst, hPN, hNcard, -⟩ := M22Hex.exists_hexad hM hSst hSP hidx

  set NK : Subgroup G := (Nst.comap φK).map K.subtype with hNK
  have hXNK : X ≤ NK := fun g hg =>
    ⟨⟨g, hXK hg⟩, hPN ⟨⟨g, hXK hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩, rfl⟩
  have hNKK : NK ≤ K := Subgroup.map_subtype_le _
  have hTKNK : IsSylowTwoOf (T ⊓ K) NK := by
    refine ⟨le_sup_right.trans hXNK, hTK.2.1, fun h2 => hTK.2.2 ?_⟩
    have hm := Subgroup.relIndex_mul_relIndex (T ⊓ K) NK K (le_sup_right.trans hXNK) hNKK
    exact h2.trans (Dvd.intro _ hm)
  have hTN := Setting147.T_le_N_l1_F4 S h1332
  have hTKn : T ≤ Subgroup.normalizer (K : Set G) := hTH.trans hKnH
  have hXN : l1 T L V ⊔ T ≤ Subgroup.normalizer (X : Set G) :=
    sup_le (le_sup_left.trans Subgroup.le_normalizer) fun t ht => mem_normalizer_sup'' (hTN ht)
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hTKn ht⟩)
  have hO2NK : pCoreOf 2 NK ≤ pCoreOf 2 (l1 T L V ⊔ T) := by
    have h1 : pCoreOf 2 NK ≤ T ⊓ K := pCoreOf_le_of_isSylowTwoOf hTKNK
    have h2 : pCoreOf 2 NK ≤ pCoreOf 2 X :=
      le_pCoreOf_of_le_normalizer 2 (h1.trans le_sup_right)
        (hXNK.trans (le_normalizer_pCoreOf 2 NK)) (pCoreOf_isPGroup 2 NK)
    exact h2.trans (le_pCoreOf_of_le_normalizer 2
      ((pCoreOf_le 2 X).trans (sup_le le_sup_left (inf_le_left.trans le_sup_right)))
      (hXN.trans (normalizer_le_normalizer_pCoreOf 2 X)) (pCoreOf_isPGroup 2 X))

  set Nc := Nst.map ψb with hNc
  have hNcL : Nc ≤ autSub (autIH (fsuV1 T V) I H K) (subM (fsuV1 T V) (conjClosure I H) I) :=
    hrange ▸ Subgroup.map_le_range ψb Nst
  have hNcard' : Nat.card Nc = 5760 := by rw [Subgroup.card_map_of_injective hψinj, hNcard]
  set R₁ := pCoreOf 2 (l1 T L V ⊔ T) with hR₁
  have hO2R : pCoreOf 2 Nc ≤ (R₁.subgroupOf H).map Ψ := by
    intro y hy
    obtain ⟨n, hn, rfl⟩ := pCoreOf_le 2 Nc hy

    set P₀ := (pCoreOf 2 Nc).comap ψb ⊓ Nst with hP₀
    have hP₀2 : IsPGroup 2 P₀ :=
      ((pCoreOf_isPGroup 2 Nc).comap_of_injective ψb hψinj).to_le inf_le_left
    have hP₀N : Nst ≤ Subgroup.normalizer (P₀ : Set (cStar K)) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro p
      have hgN : ψb g ∈ Subgroup.normalizer (pCoreOf 2 Nc : Set _) :=
        le_normalizer_pCoreOf 2 Nc ⟨g, hg, rfl⟩
      constructor
      · rintro ⟨hp1, hp2⟩
        refine ⟨?_, Nst.mul_mem (Nst.mul_mem hg hp2) (Nst.inv_mem hg)⟩
        show ψb (g * p * g⁻¹) ∈ pCoreOf 2 Nc
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp hgN _).mp hp1
      · rintro ⟨hp1, hp2⟩
        refine ⟨?_, ?_⟩
        · have h1 : ψb (g * p * g⁻¹) ∈ pCoreOf 2 Nc := hp1
          rw [map_mul, map_mul, map_inv] at h1
          exact (Subgroup.mem_normalizer_iff.mp hgN _).mpr h1
        · have := Nst.mul_mem (Nst.mul_mem (Nst.inv_mem hg) hp2) hg
          simpa [mul_assoc] using this
    have hnP : n ∈ pCoreOf 2 Nst :=
      le_pCoreOf_of_le_normalizer 2 inf_le_right hP₀N hP₀2 ⟨hy, hn⟩

    obtain ⟨k, rfl⟩ := hφs n
    set Pk : Subgroup G := ((pCoreOf 2 Nst).comap φK).map K.subtype with hPk
    have hker2 : IsPGroup 2 φK.ker := by
      rw [QuotientGroup.ker_mk']
      exact (pCoreOf_isPGroup 2 K).comap_of_injective K.subtype K.subtype_injective
    have hPk2 : IsPGroup 2 Pk :=
      (((pCoreOf_isPGroup 2 Nst).comap_of_ker_isPGroup φK hker2)).map K.subtype
    have hPkNK : Pk ≤ NK := fun g ⟨k', hk', hk'g⟩ => ⟨k', pCoreOf_le 2 Nst hk', hk'g⟩
    have hNKPk : NK ≤ Subgroup.normalizer (Pk : Set G) := by
      rintro _ ⟨g', hg', rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      have hgN : φK g' ∈ Subgroup.normalizer (pCoreOf 2 Nst : Set (cStar K)) :=
        le_normalizer_pCoreOf 2 Nst hg'
      intro p
      constructor
      · rintro ⟨p', hp', rfl⟩
        refine ⟨g' * p' * g'⁻¹, ?_, by simp⟩
        show φK (g' * p' * g'⁻¹) ∈ pCoreOf 2 Nst
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp hgN _).mp hp'
      · rintro ⟨q', hq', hq'e⟩
        have hq'e' : (q' : G) = (g' : G) * p * (g' : G)⁻¹ := hq'e
        have hpK : p ∈ K := by
          have := K.mul_mem (K.mul_mem (K.inv_mem g'.2) q'.2) g'.2
          rw [hq'e'] at this
          simpa [mul_assoc] using this
        refine ⟨⟨p, hpK⟩, ?_, rfl⟩
        have hq'' : g' * ⟨p, hpK⟩ * g'⁻¹ = q' := Subtype.ext (by rw [hq'e']; rfl)
        show φK ⟨p, hpK⟩ ∈ pCoreOf 2 Nst
        have h1 : φK q' ∈ pCoreOf 2 Nst := hq'
        rw [← hq'', map_mul, map_mul, map_inv] at h1
        exact (Subgroup.mem_normalizer_iff.mp hgN _).mpr h1
    have hkR : (k : G) ∈ R₁ :=
      hO2NK (le_pCoreOf_of_le_normalizer 2 hPkNK hNKPk hPk2 ⟨k, hnP, rfl⟩)
    exact ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr hkR, (hψmk k).symm⟩

  have hup := CFSG.Quasithin.H.Mathieu.card_fixMod_le_of_pCoreOf_le h16 hcode hNcL hNcard' hO2R

  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨hVe, hV8, -, hV12, -⟩ := hMod G T L V S.hyp.hyp S.hyp.fsu
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => isElemAbelian_comm hVe ha hb
  have hV4 : (fsuV1 T V).relIndex V = 4 := by
    have h1 := Subgroup.relIndex_mul_card (fsuV1 T V) V
    rw [inf_eq_left.mpr (inf_le_left : fsuV1 T V ≤ V), hV8, hV12] at h1
    omega
  have hR1triv : R₁ ≤ L32NSet14.trivSub V (fsuV1 T V) := by
    rw [hR₁, ← Setting147.T_trivSub_eq_F4 S h1222 h1332 h1334]
    exact inf_le_right
  obtain ⟨x, hxL1, -, hfpf⟩ := exists_l1_fpf_F4 S.hyp hMod h1222 h1332 h1334
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := by rw [L₁Of, oTwoRes_eq_oTwoUpper]
  have hxK : x ∈ K := hl1K (hl1eq ▸ hxL1)
  have hlow := four_mul_card_le_fixMod hF hIU hV₁I hHI hVI hK₀
    (fun r hr v hv => (hR1triv hr).2.2 v hv) (fun r hr => (hR1triv hr).1) hxK hfpf hV4 hVc
  have hCpos : 0 < Nat.card ↥((subM (fsuV1 T V) (conjClosure I H) I ⊓
      fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf
        (subM (fsuV1 T V) (conjClosure I H) I)) := Nat.card_pos
  have h42 := hlow.trans hup
  omega

end CFSG.Quasithin.H13.L32A.C
