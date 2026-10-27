module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Config
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PrimeDefs
public import CFSG.Quasithin.H13.StatementsVocabMap
public import CFSG.Quasithin.Vol2.GoldschmidtF431AGTrans
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E16Shape
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E17Trans
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E14Iso

public section

namespace CFSG.SectionRank.QTK.Insp443.Hyp

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.A4 CFSG.Quasithin.H13
  CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.E443 CFSG.QuasithinUnique
  CFSG.Quasithin.C2Nine CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L B Tp VB K : Subgroup G}

omit [Finite G] in
private theorem centralizer_singleton_map_subtype (K : Subgroup G) (z : ↥K) :
    (Subgroup.centralizer ({z} : Set ↥K)).map K.subtype =
      K ⊓ Subgroup.centralizer ({(z : G)} : Set G) := by
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, ?_⟩
    change (c : G) ∈ Subgroup.centralizer ({(z : G)} : Set G)
    change c ∈ Subgroup.centralizer ({z} : Set ↥K) at hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    have hyz : y = (z : G) := by simpa using hy
    rw [hyz]
    exact congrArg Subtype.val (hc z (by simp))
  · rintro ⟨hxK, hxC⟩
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    change (⟨x, hxK⟩ : ↥K) ∈ Subgroup.centralizer ({z} : Set ↥K)
    change x ∈ Subgroup.centralizer ({(z : G)} : Set G) at hxC
    rw [Subgroup.mem_centralizer_iff] at hxC ⊢
    intro y hy
    have hyz : y = z := by simpa using hy
    rw [hyz]
    exact Subtype.ext (hxC z (by simp))

omit [Finite G] in
private theorem isSylowTwoOf_subgroupOf {S L K : Subgroup G} (hS : IsSylowTwoOf S L)
    (hLK : L ≤ K) : IsSylowTwoOf (S.subgroupOf K) (L.subgroupOf K) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hS.1 (Subgroup.mem_subgroupOf.mp hx))
  · exact hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe (hS.1.trans hLK)).symm
  · change ¬ 2 ∣ (S.subgroupOf K).relIndex (L.subgroupOf K)
    rw [Subgroup.relIndex_subgroupOf hLK]
    exact hS.2.2

omit [Finite G] in
private theorem autOn_congr {H V V' : Subgroup G} (h : V = V') :
    (autOn H V).map (MulAut.congr (MulEquiv.subgroupCongr h)).toMonoidHom = autOn H V' := by
  subst h
  have hrefl : MulEquiv.subgroupCongr (rfl : V = V) = MulEquiv.refl _ := by
    ext x
    rfl
  rw [hrefl]
  have hcongr : MulAut.congr (MulEquiv.refl ↥V) = 1 := by
    ext x
    rfl
  rw [hcongr]
  change (autOn H V).map (MonoidHom.id _) = autOn H V
  rw [Subgroup.map_id]

omit [Finite G] in
private theorem map_mulAutCongr_trans {V W W' : Type*} [Group V] [Group W] [Group W']
    (e : V ≃* W) (f : W ≃* W') (H : Subgroup (MulAut V)) :
    (H.map (MulAut.congr e).toMonoidHom).map (MulAut.congr f).toMonoidHom =
      H.map (MulAut.congr (e.trans f)).toMonoidHom := by
  change (H.map (MulAut.congr e).toMonoidHom).map (MulAut.congr f).toMonoidHom =
    H.map (((MulAut.congr f).toMonoidHom).comp ((MulAut.congr e).toMonoidHom))
  rw [Subgroup.map_map]

private theorem autOn_map_subtype_eq {K : Subgroup G} {H : Subgroup ↥K} {VB : Subgroup G}
    (hVB : VB ≤ K) :
    (autOn H (VB.subgroupOf K)).map
        (MulAut.congr (Subgroup.subgroupOfEquivOfLe hVB)).toMonoidHom =
      autOn (H.map K.subtype) VB := by
  let eV : ↥(VB.subgroupOf K) ≃* ↥VB := Subgroup.subgroupOfEquivOfLe hVB
  let eVk : ↥(VB.subgroupOf K) ≃* ↥((VB.subgroupOf K).map K.subtype) :=
    (VB.subgroupOf K).equivMapOfInjective K.subtype K.subtype_injective
  have hmap : (VB.subgroupOf K).map K.subtype = VB := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVB]
  have hcomp : eVk.trans (MulEquiv.subgroupCongr hmap) = eV := by
    ext x
    rfl
  have h1 := CFSG.Quasithin.SimsD1.TransMod.autOn_map K.subtype K.subtype_injective
    H (VB.subgroupOf K)
  have h2 := autOn_congr (H := H.map K.subtype) hmap
  have htrans := map_mulAutCongr_trans eVk (MulEquiv.subgroupCongr hmap)
    (autOn H (VB.subgroupOf K))
  change (autOn H (VB.subgroupOf K)).map (MulAut.congr eV).toMonoidHom =
    autOn (H.map K.subtype) VB
  rw [← hcomp, ← htrans, ← h1, h2]

theorem concl443BWith_of_conclKWith (h : Hyp G T M L B Tp VB K) {b b' : Prop} (hb : b → b')
    (hc : ConclKWith b ↥K
      ((perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))).subgroupOf K)
      (VB.subgroupOf K) (M.subgroupOf K)) :
    Concl443BWith b' G T M L K (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)))
      VB := by
  unfold Concl443BWith
  unfold ConclKWith at hc
  set LB := perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) with hLB
  set Lk := LB.subgroupOf K with hLk
  set Vk := VB.subgroupOf K with hVk
  set Mk := M.subgroupOf K with hMk
  haveI : IsMulCommutative ↥VB := VB_comm h
  letI : CommGroup ↥VB := IsMulCommutative.instCommGroup
  have hLBmap : Lk.map K.subtype = LB := by
    rw [hLk, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h.LB_le]
  have hVBmap : Vk.map K.subtype = VB := by
    rw [hVk, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h.VB_le]
  let eL : ↥Lk ≃* ↥LB := Subgroup.subgroupOfEquivOfLe h.LB_le
  let ψ : (↥Lk ⧸ CFSG.pCore 2 ↥Lk) ≃* (↥LB ⧸ CFSG.pCore 2 ↥LB) :=
    QuotientGroup.congr _ _ eL (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 eL)
  rcases hc with ⟨hqk, hshapek, hcase⟩ | hJ
  · refine Or.inl ⟨?_, ?_, ?_⟩
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv ψ hqk
    · exact E443.shape443_of_mulEquiv ψ hshapek
    · rcases hcase with ⟨hFF, hnat3, hnat4, h3A6, hPSUfun⟩ | ⟨m, hm, hLie2, hBO⟩ | ⟨hLie3, hFano⟩
      · refine Or.inl ⟨⟨VB_comm h, ?_⟩, ?_, ?_, ?_, ?_⟩
        · obtain ⟨hcommVk, hFFk⟩ := hFF
          haveI : IsMulCommutative ↥Vk := hcommVk
          letI : CommGroup ↥Vk := IsMulCommutative.instCommGroup
          have hFFk' : IsFFModule (V := ↥(VB.subgroupOf K))
              (autOn (Subgroup.normalizer (VB.subgroupOf K : Set ↥K))
                (VB.subgroupOf K)) := hFFk
          have hFFmap := CFSG.Quasithin.E3.isFFModule_map_congr
            (Subgroup.subgroupOfEquivOfLe h.VB_le) hFFk'
          rw [autOn_map_subtype_eq (K := K)
            (H := Subgroup.normalizer (VB.subgroupOf K : Set ↥K)) (VB := VB) h.VB_le] at hFFmap
          have hNle : (Subgroup.normalizer (VB.subgroupOf K : Set ↥K)).map K.subtype ≤
              Subgroup.normalizer (VB : Set G) := by
            rintro x hx
            obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
            have hn' : (n : G) ∈
                Subgroup.normalizer ((Vk.map K.subtype : Subgroup G) : Set G) :=
              (CFSG.Quasithin.H13.F431.AG.mem_normalizer_map_iff K.subtype
                K.subtype_injective Vk n).mpr hn
            rwa [hVBmap] at hn'
          have hle : (Subgroup.normalizer (VB.subgroupOf K : Set ↥K)).map K.subtype ≤
              M ⊓ Subgroup.normalizer (VB : Set G) :=
            le_inf (hNle.trans (h.setting.normalizer_VB_le h.unique)) hNle
          exact E443.isFFModule_of_le (E443.autOn_mono' hle) hFFmap
        · intro hLie
          have hLiek : CFSG.Blueprint.LieModel (↥Lk ⧸ CFSG.pCore 2 ↥Lk) .PSL 3 2 1 :=
            E443.lieModel_of_mulEquiv' ψ hLie
          have hnat := hnat3 hLiek
          have hnat' := IsNaturalSumUnder.map K.subtype K.subtype_injective hnat
          rwa [hLBmap, hVBmap] at hnat'
        · intro hLie
          have hLiek : CFSG.Blueprint.LieModel (↥Lk ⧸ CFSG.pCore 2 ↥Lk) .PSL 4 2 1 :=
            E443.lieModel_of_mulEquiv' ψ hLie
          rcases hnat4 hLiek with hnat | ⟨hcommVk, hSLk⟩
          · left
            have hnat' := IsNaturalSumUnder.map K.subtype K.subtype_injective hnat
            rwa [hLBmap, hVBmap] at hnat'
          · right
            haveI : IsMulCommutative ↥Vk := hcommVk
            letI : CommGroup ↥Vk := IsMulCommutative.instCommGroup
            refine ⟨VB_comm h, ?_⟩
            unfold SLExteriorTwo at hSLk
            have hSLk' : (FFModel.extSq (ZMod 2) 4).Realizes
                (autOn Lk (VB.subgroupOf K)) ⊤ ⊥ := hSLk
            have hReal := CFSG.Quasithin.H.LU.realizes_map (FFModel.extSq (ZMod 2) 4)
              (Subgroup.subgroupOfEquivOfLe h.VB_le) hSLk'
            rw [autOn_map_subtype_eq (K := K) (H := Lk) (VB := VB) h.VB_le] at hReal
            rw [hLBmap] at hReal
            exact hReal
        · exact hb h3A6
        · intro hPSU hcard
          have hPSUk : CFSG.Blueprint.LieModel (↥Lk ⧸ CFSG.pCore 2 ↥Lk) .PSU 3 3 1 :=
            E443.lieModel_of_mulEquiv' ψ hPSU
          have hcardk : Nat.card Vk = 2 ^ 6 := by
            rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.VB_le).toEquiv]
            exact hcard
          let S : Subgroup ↥K := (T ⊓ LB).subgroupOf K
          have hS : IsSylowTwoOf S Lk :=
            isSylowTwoOf_subgroupOf (isSylowTwoOf_inf h) h.LB_le
          obtain ⟨V₃, hV₃V, hV₃card, hV₃norm, hV₃not⟩ := hPSUfun hPSUk hcardk S hS
          refine ⟨V₃.map K.subtype, ?_, ?_, ?_, ?_⟩
          · rw [← hVBmap]
            exact Subgroup.map_mono hV₃V
          · rw [Subgroup.card_map_of_injective K.subtype_injective]
            exact hV₃card
          · rw [inf_conjClosure_eq h]
            refine sup_le ?_ ?_
            · intro x hx
              have hxK : x ∈ K := h.LB_le hx.2
              have hxS : (⟨x, hxK⟩ : ↥K) ∈ S := Subgroup.mem_subgroupOf.mpr hx
              have hxN : (⟨x, hxK⟩ : ↥K) ∈
                  Subgroup.normalizer (V₃ : Set ↥K) := hV₃norm hxS
              have hxN' : x ∈ Subgroup.normalizer
                  ((V₃.map K.subtype : Subgroup G) : Set G) :=
                (CFSG.Quasithin.H13.F431.AG.mem_normalizer_map_iff K.subtype
                  K.subtype_injective V₃ ⟨x, hxK⟩).mpr hxN
              simpa using hxN'
            · have hQle : pCoreOf 2 (conjClosure L T) ≤
                  Subgroup.centralizer (VB : Set G) :=
                E443.VB_le_centralizer_pCoreOf_Mp h.setting
              have hV₃VB : V₃.map K.subtype ≤ VB := by
                rw [← hVBmap]
                exact Subgroup.map_mono hV₃V
              exact hQle.trans ((Subgroup.centralizer_le hV₃VB).trans
                (Subgroup.centralizer_le_normalizer _))
          · intro hKM
            apply hV₃not
            intro c hc
            have hcK : (c : G) ∈ K := c.2
            have hcC : (c : G) ∈
                Subgroup.centralizer ((V₃.map K.subtype : Subgroup G) : Set G) := by
              rw [Subgroup.mem_centralizer_iff]
              intro v hv
              obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.mp hv
              exact congrArg (fun x : ↥K => (x : G))
                ((Subgroup.mem_centralizer_iff.mp hc) v₀ hv₀)
            exact Subgroup.mem_subgroupOf.mpr (hKM ⟨hcK, hcC⟩)
      · refine Or.inr (Or.inl ⟨m, hm, ?_, ?_⟩)
        · exact E443.lieModel_of_mulEquiv' ψ.symm hLie2
        · refine ⟨VB_comm h, ?_⟩
          obtain ⟨hcommVk, hBOk⟩ := hBO
          haveI : IsMulCommutative ↥Vk := hcommVk
          letI : CommGroup ↥Vk := IsMulCommutative.instCommGroup
          unfold BinaryOrthogonalFour TwistedTensorSL at hBOk
          obtain ⟨K', hK'field, hK'finite, hK'char, hK'card, hReal⟩ := hBOk
          refine ⟨K', hK'field, hK'finite, hK'char, hK'card, ?_⟩
          have hReal' : (FFModel.twistTensor m (CFSG.Assembly.LowTwoRank.StatedSL 2 K')).Realizes
              (autOn Lk (VB.subgroupOf K)) ⊤ ⊥ := hReal
          have hReal'' := CFSG.Quasithin.H.LU.realizes_map
            (FFModel.twistTensor m (CFSG.Assembly.LowTwoRank.StatedSL 2 K'))
            (Subgroup.subgroupOfEquivOfLe h.VB_le) hReal'
          rw [autOn_map_subtype_eq (K := K) (H := Lk) (VB := VB) h.VB_le] at hReal''
          rw [hLBmap] at hReal''
          exact hReal''
      · refine Or.inr (Or.inr ⟨?_, ?_⟩)
        · exact E443.lieModel_of_mulEquiv' ψ.symm hLie3
        · refine ⟨VB_comm h, ?_⟩
          obtain ⟨hcommVk, hFanok⟩ := hFano
          haveI : IsMulCommutative ↥Vk := hcommVk
          letI : CommGroup ↥Vk := IsMulCommutative.instCommGroup
          unfold FanoCoreModule at hFanok
          have hFanok' : fanoCoreModel.Realizes (autOn Lk (VB.subgroupOf K)) ⊤ ⊥ := hFanok
          have hReal := CFSG.Quasithin.H.LU.realizes_map fanoCoreModel
            (Subgroup.subgroupOfEquivOfLe h.VB_le) hFanok'
          rw [autOn_map_subtype_eq (K := K) (H := Lk) (VB := VB) h.VB_le] at hReal
          rw [hLBmap] at hReal
          exact hReal
  · refine Or.inr ⟨?_, ?_⟩
    · exact hJ.1
    · rcases hJ.2 with hM24 | hPSL5
      · left
        exact CFSG.Quasithin.IsSporadic.of_mulEquiv ψ hM24
      · right
        exact E443.lieModel_of_mulEquiv' ψ.symm hPSL5

private theorem not_le_pCoreOf_of_conclK (h : Hyp G T M L B Tp VB K)
    (h3A6 : (Group.IsPerfect (↥((perfectCore (conjClosure L T ⊓
          Subgroup.centralizer (B : Set G))).subgroupOf K) ⧸
          CFSG.pCore 2 ↥((perfectCore (conjClosure L T ⊓
            Subgroup.centralizer (B : Set G))).subgroupOf K)) ∧
        Nat.card (Subgroup.center (↥((perfectCore (conjClosure L T ⊓
          Subgroup.centralizer (B : Set G))).subgroupOf K) ⧸
          CFSG.pCore 2 ↥((perfectCore (conjClosure L T ⊓
            Subgroup.centralizer (B : Set G))).subgroupOf K))) = 3 ∧
        Nonempty ((↥((perfectCore (conjClosure L T ⊓
          Subgroup.centralizer (B : Set G))).subgroupOf K) ⧸
          CFSG.pCore 2 ↥((perfectCore (conjClosure L T ⊓
            Subgroup.centralizer (B : Set G))).subgroupOf K)) ⧸
          Subgroup.center (↥((perfectCore (conjClosure L T ⊓
            Subgroup.centralizer (B : Set G))).subgroupOf K) ⧸
            CFSG.pCore 2 ↥((perfectCore (conjClosure L T ⊓
              Subgroup.centralizer (B : Set G))).subgroupOf K)) ≃* alternatingGroup (Fin 6))) →
      ∀ S : Subgroup ↥K, IsSylowTwoOf S
        ((perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))).subgroupOf K) →
        ∀ z ∈ VB.subgroupOf K ⊓ Subgroup.centralizer (S : Set ↥K), orderOf z = 2 →
          ¬ VB.subgroupOf K ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set ↥K))) :
    (Group.IsPerfect (↥(perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))) ⧸
          CFSG.pCore 2 ↥(perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)))) ∧
        Nat.card (Subgroup.center
          (↥(perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))) ⧸
            CFSG.pCore 2 ↥(perfectCore (conjClosure L T ⊓
              Subgroup.centralizer (B : Set G))))) = 3 ∧
        Nonempty ((↥(perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))) ⧸
          CFSG.pCore 2 ↥(perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)))) ⧸
          Subgroup.center (↥(perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))) ⧸
            CFSG.pCore 2 ↥(perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)))) ≃*
          alternatingGroup (Fin 6))) →
      ∀ z ∈ VB ⊓ Subgroup.centralizer ((T ⊓ conjClosure L T : Subgroup G) : Set G),
        orderOf z = 2 →
        ¬ VB ≤ pCoreOf 2 (K ⊓ Subgroup.centralizer ({z} : Set G)) := by
  set LB := perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) with hLB
  set Lk := LB.subgroupOf K with hLk
  set Vk := VB.subgroupOf K with hVk
  have hVBmap : Vk.map K.subtype = VB := by
    rw [hVk, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h.VB_le]
  let eL : ↥Lk ≃* ↥LB := Subgroup.subgroupOfEquivOfLe h.LB_le
  let ψ : (↥Lk ⧸ CFSG.pCore 2 ↥Lk) ≃* (↥LB ⧸ CFSG.pCore 2 ↥LB) :=
    QuotientGroup.congr _ _ eL (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 eL)
  intro h3A6B z hz hz2
  have h3A6k := h3A6 (E443.threeA6_of_mulEquiv ψ.symm h3A6B)
  obtain ⟨hzVB, hzC⟩ := Subgroup.mem_inf.mp hz
  have hzK : z ∈ K := h.VB_le hzVB
  let zK : ↥K := ⟨z, hzK⟩
  let S : Subgroup ↥K := (T ⊓ LB).subgroupOf K
  have hS : IsSylowTwoOf S Lk :=
    isSylowTwoOf_subgroupOf (isSylowTwoOf_inf h) h.LB_le
  have hzVk : zK ∈ Vk := Subgroup.mem_subgroupOf.mpr hzVB
  have hzCk : zK ∈ Subgroup.centralizer (S : Set ↥K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hsTL : (s : G) ∈ T ⊓ LB := Subgroup.mem_subgroupOf.mp hs
    have hsTMp : (s : G) ∈ T ⊓ conjClosure L T :=
      ⟨hsTL.1, (E443.LB_le L T B) hsTL.2⟩
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hzC) (s : G) hsTMp)
  have hz2k : orderOf zK = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hz2
  have hnot := h3A6k S hS zK ⟨hzVk, hzCk⟩ hz2k
  intro hVB
  apply hnot
  have hCmap : (Subgroup.centralizer ({zK} : Set ↥K)).map K.subtype =
      K ⊓ Subgroup.centralizer ({z} : Set G) := by
    simpa using centralizer_singleton_map_subtype K zK
  have hle : Vk.map K.subtype ≤
      (pCoreOf 2 (Subgroup.centralizer ({zK} : Set ↥K))).map K.subtype := by
    rw [hVBmap]
    rw [← hCmap, CFSG.Quasithin.H13.F431.AG.pCoreOf_map_injective
      K.subtype K.subtype_injective
      (Subgroup.centralizer ({zK} : Set ↥K))] at hVB
    exact hVB
  exact (Subgroup.map_le_map_iff_of_injective K.subtype_injective).mp hle

theorem concl443B_of_conclK (h : Hyp G T M L B Tp VB K)
    (hc : ConclK ↥K
      ((perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))).subgroupOf K)
      (VB.subgroupOf K) (M.subgroupOf K)) :
    Concl443B G T M L K (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))) VB :=
  concl443BWith_of_conclKWith h (not_le_pCoreOf_of_conclK h) hc

theorem concl443B'_of_conclK' (h : Hyp G T M L B Tp VB K)
    (hc : ConclK' ↥K
      ((perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))).subgroupOf K)
      (VB.subgroupOf K) (M.subgroupOf K)) :
    Concl443B' G T M L K (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))) VB :=
  concl443BWith_of_conclKWith h (fun hb h3A6B hcard => not_le_pCoreOf_of_conclK h
    (fun h3A6 => hb h3A6
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.VB_le).toEquiv]; exact hcard))
    h3A6B) hc

end CFSG.SectionRank.QTK.Insp443.Hyp
