module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdStep2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdFour
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdOdd
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_18

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Shape

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}

structure Shape (N : Notation25 hs) (t i : G) (Ki KP : Subgroup G) : Prop where
  comp : IsComponentIn Ki (Subgroup.centralizer ({i} : Set G))
  canon : KP = ⨆ g ∈ oddLayer (Subgroup.centralizer ({i} : Set G)), CFSG.conjugate N.K g
  K_le : N.K ≤ KP
  KP_le : KP ≤ Subgroup.centralizer ({i} : Set G)
  case1 : Ki ≠ CFSG.conjugate Ki t → KP = Ki ⊔ CFSG.conjugate Ki t ∧
    ⁅Ki, CFSG.conjugate Ki t⁆ = ⊥ ∧ Nonempty ((↥Ki ⧸ Subgroup.center ↥Ki) ≃* ↥N.K)
  case2 : Ki = CFSG.conjugate Ki t → KP = Ki ∧ ⁅Ki, Subgroup.zpowers t⁆ = Ki

theorem Shape.isQuasisimple {N : Notation25 hs} {t i : G} {Ki KP : Subgroup G}
    (h : Shape N t i Ki KP) : CFSG.IsQuasisimple ↥Ki :=
  BenderBranch.isQuasisimple_of_isComponentIn h.comp

theorem Shape.mem_normalizer {N : Notation25 hs} {t i : G} {Ki KP : Subgroup G}
    (h : Shape N t i Ki KP) {c : G} (hc : c ∈ Subgroup.centralizer ({i} : Set G))
    (hcK : c ∈ Subgroup.normalizer (N.K : Set G)) : c ∈ Subgroup.normalizer (KP : Set G) := by
  rw [h.canon]
  exact mem_normalizer_iSup_oddLayer hc hcK

omit [Finite G] in
theorem commutator_zpowers_eq_of_not_comp [Finite G] {J K : Subgroup G} {i t : G}
    (hJ : IsComponentIn J (Subgroup.centralizer ({i} : Set G)))
    (hvJ : t ∈ Subgroup.normalizer (J : Set G)) (hKJ : K ≤ J)
    (hK : IsComponentIn K (Subgroup.centralizer ({i} : Set G) ⊓ Subgroup.centralizer ({t} : Set G)))
    (hnc : ¬ IsComponentIn K (Subgroup.centralizer ({i} : Set G))) :
    ⁅J, Subgroup.zpowers t⁆ = J := by
  have hqJ : CFSG.IsQuasisimple ↥J := BenderBranch.isQuasisimple_of_isComponentIn hJ
  have hW : ⁅J, Subgroup.zpowers t⁆ ≤ J :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr hvJ)
  have hWn : (⁅J, Subgroup.zpowers t⁆.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hW).mpr
      (Subgroup.normalizer_commutator_ge_left _ _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hqJ hWn with h1 | h1
  · exact le_antisymm hW (Subgroup.subgroupOf_eq_top.mp h1)
  · exfalso
    have hcen : ⁅⁅J, Subgroup.zpowers t⁆, J⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      have hxJ : x ∈ J := hW hx
      have hxc := Subgroup.mem_center_iff.mp (h1 (show (⟨x, hxJ⟩ : ↥J) ∈
        ⁅J, Subgroup.zpowers t⁆.subgroupOf J from hx))
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      exact congrArg Subtype.val (hxc ⟨y, hy⟩)
    have hbot : ⁅J, Subgroup.zpowers t⁆ = ⊥ :=
      CFSG.LocalCores.perfect_double_commutator hqJ.1 hcen
    have hJt : J ≤ Subgroup.centralizer ({t} : Set G) := by
      have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
      refine this.trans (Subgroup.centralizer_le ?_)
      simp only [Set.singleton_subset_iff, SetLike.mem_coe]
      exact Subgroup.mem_zpowers t
    have hJX : IsComponentIn J (Subgroup.centralizer ({i} : Set G) ⊓ Subgroup.centralizer ({t} : Set G)) :=
      BenderBranch.isComponentIn_of_le hJ (le_inf hJ.1 hJt) inf_le_left
    rcases BenderBranch.eq_or_commute_of_isComponentIn hK hJX with hKJ' | hcomm
    · exact hnc (hKJ' ▸ hJ)
    · have hqK : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn hK
      have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hqK.1
      have hKbot : K = ⊥ := by
        rw [← hperf]
        exact le_bot_iff.mp (hcomm ▸ Subgroup.commutator_mono le_rfl hKJ)
      have := CFSG.LocalCores.isQuasisimple_nontrivial hqK
      exact (Subgroup.nontrivial_iff_ne_bot K).mp this hKbot

theorem exists_shape (hI32 : LemmaI32) (h3 : Prop121Three) (h5 : Prop121Five)
    (N : Notation25 hs) {t zK : G} (h : Lv2518 N t zK) {i : G} (hi : Hyp2519 N i) :
    ∃ Ki KP : Subgroup G, Shape N t i Ki KP := by
  have hf := h.facts2511
  have hti : t * i = i * t := N.t_comm_of_mem_S hf hi.mem_S
  have hiK : ∀ a ∈ N.K, a * i = i * a := fun a ha =>
    Subgroup.mem_centralizer_iff.mp hi.mem_centralizer_K a ha
  have hKi : N.K ≤ Subgroup.centralizer ({i} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hiK x hx)
  have hKt : IsComponentIn N.K (Subgroup.centralizer ({t} : Set G)) := h.concl2518.1
  have hX : IsComponentIn N.K
      (Subgroup.centralizer ({i} : Set G) ⊓ Subgroup.centralizer ({t} : Set G)) :=
    BenderBranch.isComponentIn_of_le hKt (le_inf hKi hKt.1) inf_le_right
  have hXe : 2 ∣ Nat.card N.K := N.two_dvd_card_K h.facts258
  have hX4 : ∃ E : Subgroup G, E ≤ N.K ∧ IsElemAbelian 2 E ∧ Nat.card E = 4 := by
    obtain ⟨E, hE, hE4⟩ := exists_four_of_shape (N.tuple.sylow.isPGroup.to_le N.SK_le_S)
      h.facts258.SK_shape
    exact ⟨E, hE.trans N.SK_le_K, hE4.1, hE4.2⟩
  have hsimple := hs.setting.simple
  have hnonab := hs.setting.nonabelian
  have hq := hs.setting.qtke
  obtain ⟨hKY, hcase⟩ := step2 hI32 h3 h5 hsimple hnonab hq hi.ne_one hi.sq_eq_one hf.t_ne_one
    hf.t_sq hti.symm hX hXe hX4
  rcases hcase with ⟨J, hJ, hYJ, hvJ⟩ | ⟨J, hJ, hJne, hYJ, hcomm, hiso⟩
  · have hKJ : N.K ≤ J := hYJ ▸ hKY
    have hJt : CFSG.conjugate J t = J := BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hvJ
    refine ⟨J, J, ⟨hJ, hYJ.symm, hKJ, hJ.1, fun hne => absurd hJt.symm hne, fun _ => ⟨rfl, ?_⟩⟩⟩
    exact commutator_zpowers_eq_of_not_comp hJ hvJ hKJ hX hi.not_comp
  · have hKJ : N.K ≤ J ⊔ CFSG.conjugate J t := hYJ ▸ hKY
    have hZK : Subgroup.center ↥N.K = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
      have := Unc25Small.center_K_trivial N h.facts258.simple x.1 x.2 (fun y hy =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨y, hy⟩))
      exact Subtype.ext this
    have hKK : ↥N.K ⧸ Subgroup.center ↥N.K ≃* ↥N.K :=
      (QuotientGroup.quotientMulEquivOfEq hZK).trans QuotientGroup.quotientBot
    refine ⟨J, J ⊔ CFSG.conjugate J t, ⟨hJ, hYJ.symm, hKJ, ?_, fun _ => ⟨rfl, hcomm, ?_⟩, fun h' =>
      absurd h' hJne⟩⟩
    · exact sup_le hJ.1 (by
        have := Unc25G2.isComponentIn_conjugate hJ (Subgroup.mem_centralizer_singleton_iff.mpr hti)
        exact this.1)
    · obtain ⟨e⟩ := hiso
      exact ⟨e.trans hKK⟩

end Shape

end CFSG.QuasithinUnique.Id2519
