module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdList
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdShape

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Case2Struct

variable {G : Type} [Group G]

structure Case2 (K Ki : Subgroup G) (t i : G) : Prop where
  t_sq : t * t = 1
  comp : IsComponentIn Ki (Subgroup.centralizer ({i} : Set G))
  K_le : K ≤ Ki
  K_compC : IsComponentIn K (Subgroup.centralizer ({t} : Set G))
  tN : t ∈ Subgroup.normalizer (Ki : Set G)
  comm : ⁅Ki, Subgroup.zpowers t⁆ = Ki
  lem : ∃ z : G, Lemma115Cases Ki z
  z2 : IsPGroup 2 (Subgroup.center ↥Ki)
  K_eq : K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
    (Ki ⊓ Subgroup.centralizer ({t} : Set G))
  type : IsKType K
  nbig : ¬ IsL2pBig K
  pat32 : IsL32 K → PatA Ki K t ∨ PatB Ki K t
  pat6 : IsA6 K → PatSp4 Ki K ∨ PatL5 Ki K ∨ PatHS Ki K t ∨ PatA8 Ki K t

end Case2Struct

section Case2Lemmas

variable {G : Type} [Group G] [Finite G] {K Ki : Subgroup G} {t i : G}

namespace Case2

variable (c : Case2 K Ki t i)

include c

omit [Finite G] in
theorem quasisimple : CFSG.IsQuasisimple ↥Ki := BenderBranch.isQuasisimple_of_isComponentIn c.comp

omit [Finite G] in
theorem compK : IsComponentIn K (Ki ⊓ Subgroup.centralizer ({t} : Set G)) :=
  BenderBranch.isComponentIn_of_le c.K_compC (le_inf c.K_le c.K_compC.1) inf_le_right

omit [Finite G] in
theorem pat : (IsL32 K ∧ (PatA Ki K t ∨ PatB Ki K t)) ∨
    (IsA6 K ∧ (PatSp4 Ki K ∨ PatL5 Ki K ∨ PatHS Ki K t ∨ PatA8 Ki K t)) := by
  rcases c.type with hbig | h32 | h6
  · exact absurd hbig c.nbig
  · exact Or.inl ⟨h32, c.pat32 h32⟩
  · exact Or.inr ⟨h6, c.pat6 h6⟩

omit [Finite G] in
theorem patAll : PatA Ki K t ∨ PatB Ki K t ∨ PatSp4 Ki K ∨ PatL5 Ki K ∨ PatHS Ki K t ∨
    PatA8 Ki K t := by
  rcases c.pat with ⟨-, h | h⟩ | ⟨-, h | h | h | h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

omit [Finite G] in
theorem caseGroup : IsCaseGroup Ki := isCaseGroup_of_pat c.patAll

omit [Finite G] in
theorem ne_bot : Ki ≠ ⊥ := Unc25G2.isComponentIn_ne_bot c.comp

omit [Finite G] in
theorem not_le_centralizer : ¬ Ki ≤ Subgroup.centralizer ({t} : Set G) := by
  intro h
  have := commutator_zpowers_eq_bot_of_commute (A := Ki) (t := t) fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mp (h ha)
  rw [c.comm] at this
  exact c.ne_bot this

theorem three_rank (hTR : TabThreeRank) :
    ∃ A : Subgroup G, A ≤ Ki ∧ IsElemAbelian 3 A ∧ Nat.card A = 9 :=
  hTR.nine G Ki c.quasisimple c.z2 c.caseGroup

theorem hasE9_quotient (hTR : TabThreeRank) : HasElemAb 3 9 (↥Ki ⧸ Subgroup.center ↥Ki) := by
  obtain ⟨A, hAK, hA3, hA9⟩ := c.three_rank hTR
  exact HasElemAb.quotient_two _ c.z2 (HasElemAb.of_subgroup hAK hA3 hA9)

omit [Finite G] in
theorem center_three {x : G} (hx : x ∈ centerOf Ki) (h3 : x ^ 3 = 1) : x = 1 := by
  have hmem : (⟨x, hx.1⟩ : ↥Ki) ∈ Subgroup.center ↥Ki := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 g g.2)
  have := eq_one_of_isPGroup_two_of_pow_three c.z2 hmem (Subtype.ext (by simpa using h3))
  exact congrArg Subtype.val this

end Case2

end Case2Lemmas

section Case2Build

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK i : G} {Ki KP : Subgroup G}

theorem case2_of_shape (hI : Inputs2519) (h : Lv2518 N t zK) (hi : Hyp2519 N i)
    (hsh : Shape N t i Ki KP) (heq : Ki = CFSG.conjugate Ki t) :
    KP = Ki ∧ Case2 N.K Ki t i := by
  have hf := h.facts2511
  have hsimple := hs.setting.simple
  have hnonab := hs.setting.nonabelian
  have hq := hs.setting.qtke
  obtain ⟨hKP, hcomm⟩ := hsh.case2 heq
  have htN : t ∈ Subgroup.normalizer (Ki : Set G) :=
    BenderBranch.conjugate_eq_iff_mem_normalizer.mp heq.symm
  have hKiq := hsh.isQuasisimple
  have hKle : N.K ≤ Ki := by rw [← hKP]; exact hsh.K_le
  have hKtype : IsKType N.K := by
    rcases h.concl2516 with ⟨p, hp, h7, hm⟩ | ⟨hm, -⟩ | ⟨hA6, -⟩
    · exact Or.inl ⟨p, hp, h7, hm⟩
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr hA6)
  have hKcomp : IsComponentIn N.K (Ki ⊓ Subgroup.centralizer ({t} : Set G)) :=
    BenderBranch.isComponentIn_of_le h.concl2518.1 (le_inf hKle h.concl2518.1.1) inf_le_right
  obtain ⟨z, hz⟩ := exists_lemma115Cases hI.list115 hsimple hnonab hq hi.ne_one hi.mul_self hsh.comp
  obtain ⟨hZ2, hKeq, hnbig, hp32, hp6⟩ := hI.ident G Ki N.K t hKiq ⟨z, hz⟩ htN
    (N.t_mul_self' hf) hcomm hKcomp hKtype
  exact ⟨hKP, N.t_mul_self' hf, hsh.comp, hKle, h.concl2518.1, htN, hcomm, ⟨z, hz⟩, hZ2, hKeq,
    hKtype, hnbig, hp32, hp6⟩

end Case2Build

end CFSG.QuasithinUnique.Id2519
