module

public import CFSG.GH74.Generic.BProg.B1.PilotS1
public import CFSG.GH74.Generic.BProg.B1.PilotS1ThreeFacts

public section

namespace CFSG.GH74.Generic.BProg.B1.PilotS1

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg
  CFSG.Blueprint CFSG.GH74.L5U5 Subgroup
open CFSG.GH74.Generic.BProg.B1.PilotS5 CFSG.GH74.Generic.BProg.B1.PilotS3
open scoped MatrixGroups commutatorElement

section Aux

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_imgBar_pair {x y : G} (hx : orderOf x = 2) (hy2 : orderOf y = 2) (hxy : x * y = y * x)
    (hxyne : x ≠ y) (hyC : y ∈ centralizer ({x} : Set G)) {e : CentralizerBar x}
    (he : e ∈ imgBar x (closure ({x, y} : Set G))) :
    e = 1 ∨ e = xbar x ∨ e = bar x y ∨ e = xbar x * bar x y := by
  obtain ⟨hcl, -, -⟩ := closure_pair_facts hx hy2 hxy hxyne
  obtain ⟨g, hg, rfl⟩ := mem_imgBar.1 he
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  rw [hcl] at hg
  rcases mem_sup_zpowers_of_two hx (Subgroup.zpowers_le.2 hyC) hg with ⟨l, hl, hgl⟩ | ⟨l, hl, hgl⟩
  · rcases mem_zpowers_of_two hy2 hl with h | h
    · left
      have : g = 1 := Subtype.ext (by rw [hgl, h]; rfl)
      rw [this, map_one]
    · right; right; left
      have : g = ⟨y, hyC⟩ := Subtype.ext (by rw [hgl, h])
      rw [this, bar_of_mem hyC]
  · rcases mem_zpowers_of_two hy2 hl with h | h
    · right; left
      have : g = ⟨x, hxC⟩ := Subtype.ext (by rw [hgl, h, mul_one])
      rw [this]
      rfl
    · right; right; right
      have : g = ⟨x, hxC⟩ * ⟨y, hyC⟩ := Subtype.ext (by rw [hgl, h]; rfl)
      rw [this, map_mul, bar_of_mem hyC]
      rfl

end Aux

theorem pPrimeCore_eq_bot_of_quasisimple {S : Type*} [Group S] [Finite S] (hq : IsQuasisimple S)
    (hZ : Nat.card ↥(center S) = 2) : pPrimeCore 2 S = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq
    (CFSG.pPrimeCore_normal : (pPrimeCore 2 S).Normal) with htop | hcen
  · exfalso
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center S)) 2 (by rw [hZ])
    have hzO : (z : S) ∈ pPrimeCore 2 S := by rw [htop]; trivial
    have hodd := odd_orderOf_of_mem_pPrimeCore hzO
    rw [Subgroup.orderOf_coe, hz] at hodd
    exact absurd hodd (by decide)
  · rw [eq_bot_iff]
    intro m hm
    have hmc : m ∈ center S := hcen hm
    have h1 : orderOf m ∣ 2 := by
      have := Subgroup.orderOf_dvd_natCard (center S) hmc
      rwa [hZ] at this
    have h2 := odd_orderOf_of_mem_pPrimeCore hm
    have : orderOf m = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
      · exact h
      · rw [h] at h2; exact absurd h2 (by decide)
    rw [orderOf_eq_one_iff.1 this]
    exact Subgroup.one_mem _

theorem not_isSolv2CompIn_of_quasisimple {X : Type} [Group X] [Finite X] {S L : Subgroup X}
    (hq : IsQuasisimple ↥S) (hZ : Nat.card ↥(center ↥S) = 2) : ¬ IsSolv2CompIn S L := by
  classical
  rintro ⟨Lb, hsub, ⟨e⟩, -⟩
  have hO : pPrimeCore 2 ↥S = ⊥ := pPrimeCore_eq_bot_of_quasisimple hq hZ
  let eQ : (↥S ⧸ pPrimeCore 2 ↥S) ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have hQq : IsQuasisimple (↥S ⧸ pPrimeCore 2 ↥S) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eQ.symm hq
  have hQtop : IsComponent (⊤ : Subgroup (↥S ⧸ pPrimeCore 2 ↥S)) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hQq,
      Subgroup.IsSubnormal.top⟩
  have hsl : Group.IsSolvable SL(2, ZMod 3) := isSolvable_sl2_three (F := ZMod 3) (by simp)
  rcases CFSG.LocalCores.component_subnormal_subgroup hQtop hsub with htop | hcomm
  · let φ : (↥S ⧸ pPrimeCore 2 ↥S) →* ↥Lb :=
      MonoidHom.codRestrict (MonoidHom.id _) Lb (fun q => htop (Subgroup.mem_top q))
    have hφ : Function.Injective φ := fun a b hab => congrArg Subtype.val hab
    have hsolv : Group.IsSolvable (↥S ⧸ pPrimeCore 2 ↥S) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom.comp φ) (e.injective.comp hφ)
    have : Nontrivial (↥S ⧸ pPrimeCore 2 ↥S) := CFSG.LocalCores.isQuasisimple_nontrivial hQq
    have : Group.IsPerfect (↥S ⧸ pPrimeCore 2 ↥S) := hQq.1
    exact (Group.IsPerfect.not_isSolvable (↥S ⧸ pPrimeCore 2 ↥S)) hsolv
  · have hcent : (⊤ : Subgroup (↥S ⧸ pPrimeCore 2 ↥S)) ≤
        centralizer (Lb : Set (↥S ⧸ pPrimeCore 2 ↥S)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    obtain ⟨s, t, hst⟩ := sl2_not_comm (ZMod 3)
    apply hst
    apply e.symm.injective
    have h1 := Subgroup.mem_centralizer_iff.1 (hcent (Subgroup.mem_top ((e.symm s : ↥Lb) :
      ↥S ⧸ pPrimeCore 2 ↥S))) ((e.symm t : ↥Lb) : ↥S ⧸ pPrimeCore 2 ↥S) (e.symm t).2
    apply Subtype.ext
    rw [map_mul, map_mul]
    exact h1.symm

theorem mem_oPrimeResidualOf_of_two {X : Type*} [Group X] {J : Subgroup X} {g : X} (hgJ : g ∈ J)
    (hg : g * g = 1) : g ∈ oPrimeResidualOf 2 J := by
  refine ⟨⟨g, hgJ⟩, Subgroup.subset_closure ⟨1, ?_⟩, rfl⟩
  apply Subtype.ext
  simpa [pow_two] using hg

section GLevel3

variable {G : Type} [Group G] [Finite G]

theorem exists_adm_of_split1_three {x : G} {K A : Subgroup G} {F' : Type} [Field F'] [Finite F']
    (hF3 : Nat.card F' = 3) (hx : orderOf x = 2)
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hY : Split1Like F' (imgBar x K) (xbar x))
    (hCY : ∀ w ∈ centralizer ((imgBar x K : Subgroup (CentralizerBar x)) : Set (CentralizerBar x)),
      w = 1 ∨ w = xbar x)
    (he8 : ∀ E : Subgroup (CentralizerBar x), E ≤ imgBar x K → CFSG.IsElementaryAbelian 2 ↥E →
      Nat.card ↥E = 8 → xbar x ∈ E)
    (hSq : IsQuasisimple ↥(imgBar x K)) (hSZ : Nat.card ↥(center ↥(imgBar x K)) = 2)
    (hAK : A ≤ K) (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hA8 : Nat.card ↥A = 8) :
    ∃ (y : G) (Lb : Subgroup (CentralizerBar x)), IsAdmPair x K A y Lb := by
  classical
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  obtain ⟨hxA, y, hyA, hyK, hyC, hy2, hxy, hxyne, hbmem, hb2, hyne⟩ :=
    exists_y_of_e8 hx hK he8 hAK hAel hA8
  obtain ⟨J₁, J₂, hS⟩ := hY.split (bar x y) hbmem hb2 (fun h => hyne (h ▸ Subgroup.mem_zpowers _))
  obtain ⟨hDA, hDC, hDel, hDrank, hDcomm⟩ := D_facts hx hy2 hxy hxyne hxA hyA (hAK.trans hKC)
  have hLD := centralizes_Dbar hyC (fun l hl => (hS.le₁ hl).1)
  have hsolv := hS.isSolv2CompIn₁ hF3
  have hPL := hS.pLayerOf_eq_bot_three hF3
  have hbb : bar x y * bar x y = 1 := by
    have h := pow_orderOf_eq_one (bar x y)
    rw [hb2, pow_two] at h
    exact h
  have hJ₁S : J₁ ≤ imgBar x K := fun l hl => (hS.le₁ hl).2
  have hJ₁ne : J₁ ≠ ⊥ := by
    intro hbot
    have h1 := hS.u_mem
    rw [hbot, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hb2
    exact absurd hb2 (by norm_num)
  have hsetup : Setup1E x y (closure ({x, y} : Set G)) :=
    ⟨hyC, hy2, hyne, hDC, hDel, fun d hd => Subgroup.le_normalizer hd, by
      rw [inf_eq_left.2 hDcomm]; exact hDrank⟩
  have hyD : y ∈ closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hcentE : ∀ e ∈ closure ({x, y} : Set G), e * y = y * e := fun e he =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥(closure ({x, y} : Set G)))).comm
      ⟨e, he⟩ ⟨y, hyD⟩)
  have hlayer : extLayer2 (centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ imgBar x K) ≠ ⊥ := by
    intro hbot
    have h1 : J₁ ≤ extLayer2 (centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ imgBar x K) :=
      le_sup_of_le_right (le_iSup₂_of_le J₁ hsolv le_rfl)
    rw [hbot, le_bot_iff] at h1
    exact hJ₁ne h1
  have hinvL : ∀ e ∈ imgBar x (closure ({x, y} : Set G)),
      e ∈ normalizer (J₁ : Set (CentralizerBar x)) := fun e he =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun l hl =>
      (Subgroup.mem_centralizer_iff.1 (hLD hl) e he).symm)
  have hsolvI : IsSolv2CompIn (extLayer2 (centralizer ((imgBar x (closure ({x, y} : Set G)) :
      Subgroup (CentralizerBar x)) : Set (CentralizerBar x)) ⊓ J₁)) J₁ := by
    rw [inf_eq_right.2 hLD, hS.extLayer2_eq_three hF3]
    exact hS.isSolv2CompIn_self hF3
  have hSx : centralizer ({xbar x} : Set (CentralizerBar x)) ⊓ imgBar x K = imgBar x K :=
    inf_eq_right.2 fun g _ => Subgroup.mem_centralizer_singleton_iff.2 (xbar_comm x g)
  have hSpc : IsPCompIn 2 (imgBar x K) (imgBar x K) := by
    have hO := pPrimeCore_eq_bot_of_quasisimple hSq hSZ
    refine ⟨le_rfl, ?_⟩
    rw [Subgroup.subgroupOf_self]
    exact isPComponent_of_pPrimeCore_eq_bot hO inferInstance
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hSq)
  have hres_le : oPrimeResidualOf 2 J₁ ≤ J₁ := Subgroup.map_subtype_le _
  have hexists : ∀ e ∈ imgBar x (closure ({x, y} : Set G)), e ≠ 1 → ∃ Ie : Subgroup (CentralizerBar x),
      IsQuasi2CompIn (centralizer ({e} : Set (CentralizerBar x)) ⊓ imgBar x K) Ie ∧
        oPrimeResidualOf 2 J₁ ≤ Ie := by
    intro e he hne
    rcases mem_imgBar_pair hx hy2 hxy hxyne hyC he with h | h | h | h
    · exact absurd h hne
    · refine ⟨imgBar x K, Or.inl ?_, hres_le.trans hJ₁S⟩
      rw [h, hSx]
      exact hSpc
    · exact ⟨J₁, Or.inr (by rw [h]; exact hsolv), hres_le⟩
    · exact ⟨J₁, Or.inr (by rw [h, hY.centralizer_mul_eq]; exact hsolv), hres_le⟩
  have hcond6 : ∀ e ∈ imgBar x (closure ({x, y} : Set G)), e ≠ 1 →
      ∀ Ie : Subgroup (CentralizerBar x),
        IsQuasi2CompIn (centralizer ({e} : Set (CentralizerBar x)) ⊓ imgBar x K) Ie →
          oPrimeResidualOf 2 J₁ ≤ Ie →
            IsSolv2CompIn (centralizer ({e} : Set (CentralizerBar x)) ⊓ imgBar x K) Ie →
              (∃ l ∈ Ie, orderOf l = 2 ∧ ∀ k ∈ imgBar x K, e * k * e⁻¹ = l * k * l⁻¹) ∨
                NotDirectFactor6b (centralizer ({e} : Set (CentralizerBar x)) ⊓ imgBar x K) Ie := by
    intro e he hne Ie _ hres hIe
    have hlmem : bar x y ∈ Ie := hres (mem_oPrimeResidualOf_of_two hS.u_mem hbb)
    rcases mem_imgBar_pair hx hy2 hxy hxyne hyC he with h | h | h | h
    · exact absurd h hne
    · exfalso
      rw [h, hSx] at hIe
      exact not_isSolv2CompIn_of_quasisimple hSq hSZ hIe
    · exact Or.inl ⟨bar x y, hlmem, hb2, fun k _ => by rw [h]⟩
    · refine Or.inl ⟨bar x y, hlmem, hb2, fun k _ => ?_⟩
      rw [h]
      have hc := xbar_comm x (bar x y * k * (bar x y)⁻¹)
      calc xbar x * bar x y * k * (xbar x * bar x y)⁻¹
          = xbar x * (bar x y * k * (bar x y)⁻¹) * (xbar x)⁻¹ := by group
        _ = bar x y * k * (bar x y)⁻¹ := mul_inv_eq_iff_eq_mul.2 hc.symm
  exact ⟨y, J₁, ⟨⟨hyC, hy2, hyne, hY.subtermRel_three hF3 hCY hbmem hS,
    fun hne => absurd hPL hne⟩, closure ({x, y} : Set G), J₁, ⟨hDA, hDel, hDrank⟩,
    Or.inr ⟨hsetup, Subgroup.le_normalizer hyK, hcentE, hlayer, Or.inr hsolv, hinvL, hsolvI,
      hexists, hcond6⟩⟩⟩

theorem QShape1Three.qShape1 {Kt : Type} [Group Kt] (h : QShape1Three Kt) : QShape1 Kt := by
  obtain ⟨F, _, _, hF3, e⟩ := h
  exact Or.inl ⟨F, inferInstance, inferInstance, by omega, e⟩

theorem exists_grpS1_of_three {Kt : Type} [Group Kt] (h : QShape1Three Kt) :
    ∃ (P : Type) (_ : Group P) (F' : Type) (_ : Field F') (_ : Finite F') (z : P),
      Nonempty (Kt ≃* P) ∧ Nat.card F' = 3 ∧ GrpS1 F' P z := by
  obtain ⟨F, _, _, hF3, ⟨e⟩⟩ := h
  obtain ⟨z, hz⟩ := grpS1_lin (F := F) (by omega)
  exact ⟨_, inferInstance, F, inferInstance, inferInstance, z, ⟨e⟩, hF3, hz⟩

theorem exists_adm_of_shape1_three {x : G} {K A : Subgroup G} (hG : Gen4 G) (hx : orderOf x = 2)
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (h1 : QShape1Three (↥K ⧸ pPrimeCore 2 ↥K))
    (hA : IsSource2 x K A) :
    ∃ (y : G) (Lb : Subgroup (CentralizerBar x)), IsAdmPair x K A y Lb := by
  obtain ⟨P, _, F', _, _, z₀, ⟨eP⟩, hF3, hP⟩ := exists_grpS1_of_three h1
  obtain ⟨hxK, hSq, hSZ, hY, hCY, he8⟩ := shape1_data hG hx hK eP hP h1.qShape1
  obtain ⟨hAK, hAel, hA8⟩ := source_le hxK hA
  exact exists_adm_of_split1_three hF3 hx hK hY hCY he8 hSq hSZ hAK hAel hA8

end GLevel3

end CFSG.GH74.Generic.BProg.B1.PilotS1

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup

theorem admissibleExistsFor_shape1_three : AdmissibleExistsFor PilotS1.QShape1Three := by
  intro G _ _ hyp _noAlt x K hcirc h1 A hA
  exact PilotS1.exists_adm_of_shape1_three hyp.gen4 hcirc.1.1.1.1 hcirc.1.1.1.2.2 h1 hA

theorem admissibleExistsFor_shape1_of_three (h3 : AdmissibleExistsFor PilotS1.QShape1Three) :
    AdmissibleExistsFor QShape1 := by
  intro G _ _ hyp noAlt x K hcirc h1 A hA
  rcases PilotS1.qShape1_split h1 with h | h
  · exact admissibleExistsFor_shape1_big G hyp noAlt x K hcirc h A hA
  · exact h3 G hyp noAlt x K hcirc h A hA

theorem admissibleExistsFor_shape1 : AdmissibleExistsFor QShape1 :=
  admissibleExistsFor_shape1_of_three admissibleExistsFor_shape1_three

end CFSG.GH74.Generic.BProg.B1
