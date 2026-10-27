module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharBase
public import CFSG.GH74.Exceptional.UnitaryFourTwo
public import CFSG.LieType.Multipliers.U42Data
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.AGLEmbedding.OffCharU42

open CFSG.GH74.Exceptional CFSG.LieType.Multipliers.U42
open CFSG.Open (GLBCore IsElemAbelian)

noncomputable def W (l : List (Fin 45)) : PSp43 := (l.map s43).prod

theorem W_nil : W [] = 1 := by simp [W]

theorem W_cons (i : Fin 45) (l : List (Fin 45)) : W (i :: l) = s43 i * W l := by
  simp [W]

theorem W_append (l₁ l₂ : List (Fin 45)) : W (l₁ ++ l₂) = W l₁ * W l₂ := by
  simp [W, List.prod_append]

theorem W_mem (l : List (Fin 45)) : W l ∈ Y43 := by
  induction l with
  | nil => exact one_mem _
  | cons i l ih => rw [W_cons]; exact mul_mem (s43_mem_Y43 i) ih

theorem sigma43_W (l : List (Fin 45)) (j : Fin 45) :
    sigma43 ⟨W l, W_mem l⟩ j = seqFun l j := by
  induction l generalizing j with
  | nil =>
    have h : (⟨W [], W_mem []⟩ : Y43) = 1 := Subtype.ext W_nil
    rw [h, map_one]
    rfl
  | cons i l ih =>
    have h : (⟨W (i :: l), W_mem _⟩ : Y43) = ⟨s43 i, s43_mem_Y43 i⟩ * ⟨W l, W_mem l⟩ :=
      Subtype.ext (W_cons i l)
    rw [h, map_mul, Equiv.Perm.mul_apply, ih, sigma43_s43]
    rfl

theorem sigma43_injective : Function.Injective sigma43 :=
  fun _ _ hab => sigma43_rangeRestrict_bijective.1 (Subtype.ext hab)

theorem W_eq_of_seqFun {l₁ l₂ : List (Fin 45)} (h : ∀ j, seqFun l₁ j = seqFun l₂ j) :
    W l₁ = W l₂ := by
  have := @sigma43_injective ⟨W l₁, W_mem l₁⟩ ⟨W l₂, W_mem l₂⟩
    (Equiv.ext fun j => by rw [sigma43_W, sigma43_W, h j])
  exact congrArg Subtype.val this

theorem W_ne_one {l : List (Fin 45)} (h : ¬ ∀ j, seqFun l j = j) : W l ≠ 1 := by
  intro h1
  apply h
  intro j
  have h2 : (⟨W l, W_mem l⟩ : Y43) = ⟨W [], W_mem []⟩ := Subtype.ext (h1.trans W_nil.symm)
  rw [← sigma43_W, h2, sigma43_W]
  rfl

theorem s43_sigma43 (g : Y43) (j : Fin 45) : s43 (sigma43 g j) = g * s43 j * (g : PSp43)⁻¹ :=
  s43_s43Idx (conj_mem_range g.2 j).1

@[expose] def tauChunks : List ℕ :=
  [327200374047354451798858254400999362968936424459926242211215586474545738965668916105344,
    3334709849340747702250465078356377433778774376963971047592657585189690395718022438898954,
    9798424836201807235126584648121226087760105048216893184328085742769686754489515413845143,
    5450754154899653180146529114830184456004190811642764919390775350403624202843656242125152,
    9124323921901692090024206864483686334791741861027007105059620087081557490934584745793125,
    801431158437812662976174936125710656295865564243572626681601354334257973547408660395023,
    2206559061525991772973907658097815052902834965967241259350038627955173334094988761120543,
    5687032350102348689858598071232145703838515452046352558265463537666455402383048955961564,
    2519968788800262394422247118781426713599236664597180524685637005729383763531897969435571,
    1513896156562058041688647371980755933377439811235950225361548590802687311190607196426370,
    7971981508233282275286177789522395031804257825029128907400639104164705315787296537484278,
    815208415850665533031559500860483891920467000662711602829346894951264821790238026932403,
    7316248891266393264517757323412279578226006695463125436053639972689593831097805959166621,
    9386085355289326604531756587333298938860126748440727830797780753495347009928418584919868,
    7189746392110384900607873935922495586904466420460173080999812357332034612216057745527244,
    5216971708241621747119050875006694112938659449810252536040659142438662905069766971798138,
    8919377289321975711211130234139576880623502173331887664563322522893828488945858310558540,
    6919110360412712611768976341772934421007064561259630414595635874620013075094483137324723,
    499552714567610407519955513517341091244225827413209310269893072759440504153238351518539,
    405790072985843525475129570108291987947301610182632884947366939225927878653677276694482,
    7732221705697070510439148518889368317130071746630183751562056003190189321948285343865806,
    9683422373681477078660848172061420584179424680294355908749959430153584391596061059597126,
    5501088520955553989936729212789731239806446098134765009937581877897488556878440531900881,
    5417424043445661862011448932333007941406845994176636765785107888541870142194384914374902,
    608784821364740209326938516356678818286676722447547142202206220817090758176503781436081,
    7525424090498414276790958177110135194468865665600350285614040972383606372987284545447802,
    691016118906269323557720770032360136832362005512923863649993396651892200089035366905988,
    5627306639310651874784147377620623142187385257845310391076565208087046716625420396469804,
    8543526713469560124521550842136943745756987580951320393566124776893311005955970861250894,
    3893227099473413056655372905171396408618027496236231147562222979901440281140035351802894,
    6025032558526970288346568796023705320581400417901025716966156628961941599419545037509377,
    3212483763812568077892277986046342290592017925805778244573156433904927138732851745000746,
    6157779386818549801057304764510230089146267373541629233830252113468191057788659755390619,
    2264220640013374525781617671456425922782114563235183249485906960204107056917079603287422,
    5423536152319630791383265810988005223385361138106025792271578796919792109324489279710464,
    5521125661729236033820308460773544550220487346705358172785425981547376542329268023151762,
    6711904404539752523970534979289689226346053054062360196173246469977525466983699492165996,
    1037018240063777449712677257501381832822058731458391593749543307725410650114813194934340,
    9236512895844535053798071010848824909667750044264644908439184106264396361611355441544595,
    6421974776219161599358865083541333507376425094265094240049276887522781504777420045014804,
    5516416720343745045099535178193062351780274116185966111523413554483206213113334817875487,
    22816714642046693572048410908728188684193999986869]

@[expose] def tauNat : ℕ := tauChunks.foldr (fun c a => c + 10 ^ 88 * a) 0

@[expose] def tauL (i j : Fin 45) : Fin 45 :=
  ⟨(tauNat / 64 ^ (45 * i.val + j.val)) % 64 % 45, Nat.mod_lt _ (by norm_num)⟩

theorem tauFun_eq_tauL : ∀ i j : Fin 45, tauFun i j = tauL i j := by decide +kernel

@[expose] def seqL (l : List (Fin 45)) (j : Fin 45) : Fin 45 := l.foldr tauL j

theorem seqFun_eq_seqL (l : List (Fin 45)) (j : Fin 45) : seqFun l j = seqL l j := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [seqFun, seqL, List.foldr_cons] at ih ⊢; rw [ih, tauFun_eq_tauL]

theorem W_eq_of_seqL {l₁ l₂ : List (Fin 45)} (h : ∀ j, seqL l₁ j = seqL l₂ j) : W l₁ = W l₂ :=
  W_eq_of_seqFun fun j => by rw [seqFun_eq_seqL, seqFun_eq_seqL, h j]

theorem W_ne_one_of_seqL {l : List (Fin 45)} (h : ¬ ∀ j, seqL l j = j) : W l ≠ 1 :=
  W_ne_one fun h' => h fun j => by rw [← seqFun_eq_seqL]; exact h' j

@[expose] def wx1 : List (Fin 45) := [38, 23]

@[expose] def wx2 : List (Fin 45) := [38, 36, 13, 6]

@[expose] def wg : List (Fin 45) := [16, 13, 4, 1]

theorem wx1_pow : ∀ j, seqL (wx1 ++ wx1 ++ wx1) j = j := by decide +kernel

theorem wx2_pow : ∀ j, seqL (wx2 ++ wx2 ++ wx2) j = j := by decide +kernel

theorem wx1_ne : ¬ ∀ j, seqL wx1 j = j := by decide +kernel

theorem wx2_ne : ¬ ∀ j, seqL wx2 j = j := by decide +kernel

theorem wx12_comm : ∀ j, seqL (wx1 ++ wx2) j = seqL (wx2 ++ wx1) j := by decide +kernel

theorem wt_comm : ∀ j, seqL ([2] ++ wx1) j = seqL (wx1 ++ [2]) j := by decide +kernel

theorem wg_comm : ∀ j, seqL (wg ++ wx2) j = seqL (wx2 ++ wg) j := by decide +kernel

theorem W_pow_three {l : List (Fin 45)} (h : ∀ j, seqL (l ++ l ++ l) j = j) :
    W l ^ 3 = 1 := by
  have h1 : W (l ++ l ++ l) = W [] := W_eq_of_seqL fun j => by rw [h j]; rfl
  rw [W_append, W_append, W_nil] at h1
  rw [pow_three']
  exact h1

noncomputable def EU : Subgroup PSp43 := Subgroup.closure {W wx1, W wx2}

theorem EU_elem : IsElemAbelian 3 EU := by
  refine isElemAbelian_closure ?_ ?_
  · have h12 : W wx1 * W wx2 = W wx2 * W wx1 := by
      rw [← W_append, ← W_append]
      exact W_eq_of_seqL wx12_comm
    rintro x (rfl | rfl) y (rfl | rfl)
    · rfl
    · exact h12
    · exact h12.symm
    · rfl
  · rintro x (rfl | rfl)
    · exact W_pow_three wx1_pow
    · exact W_pow_three wx2_pow

theorem s2_mem : W [2] ∈ GLBCore 3 1 EU := by
  refine mem_glbCore_of_commute Nat.prime_three EU_elem
    (Subgroup.subset_closure (by simp)) (W_ne_one_of_seqL wx1_ne) ?_
  rw [← W_append, ← W_append]
  exact W_eq_of_seqL wt_comm

theorem wg_mem : W wg ∈ GLBCore 3 1 EU := by
  refine mem_glbCore_of_commute Nat.prime_three EU_elem
    (Subgroup.subset_closure (by simp)) (W_ne_one_of_seqL wx2_ne) ?_
  rw [← W_append, ← W_append]
  exact W_eq_of_seqL wg_comm

@[expose] def reach : ℕ → Finset (Fin 45)
  | 0 => {2}
  | k + 1 => reach k ∪ (reach k).image (seqL [2]) ∪ (reach k).image (seqL wg)

theorem reach_all : ∀ i : Fin 45, i ∈ reach 11 := by decide +kernel

theorem s43_mem_closure (i : Fin 45) :
    s43 i ∈ Subgroup.closure ({W [2], W wg} : Set PSp43) := by
  set H : Subgroup PSp43 := Subgroup.closure ({W [2], W wg} : Set PSp43) with hH
  have hmove : ∀ l : List (Fin 45), W l ∈ H → ∀ j, s43 j ∈ H → s43 (seqL l j) ∈ H := by
    intro l hl j hj
    rw [← seqFun_eq_seqL, ← sigma43_W l j, s43_sigma43]
    exact mul_mem (mul_mem hl hj) (inv_mem hl)
  have h2 : W [2] ∈ H := Subgroup.subset_closure (by simp)
  have hg : W wg ∈ H := Subgroup.subset_closure (by simp)
  have hreach : ∀ k, ∀ j ∈ reach k, s43 j ∈ H := by
    intro k
    induction k with
    | zero =>
      intro j hj
      rw [reach, Finset.mem_singleton] at hj
      subst hj
      have : s43 2 = W [2] := by simp [W]
      rw [this]
      exact h2
    | succ k ih =>
      intro j hj
      simp only [reach, Finset.mem_union, Finset.mem_image] at hj
      rcases hj with (hj | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩
      · exact ih j hj
      · exact hmove [2] h2 a (ih a ha)
      · exact hmove wg hg a (ih a ha)
  exact hreach 11 i (reach_all i)

theorem glbCore_EU : GLBCore 3 1 EU = ⊤ := by
  have hH : Subgroup.closure ({W [2], W wg} : Set PSp43) ≤ GLBCore 3 1 EU := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact s2_mem
    · exact wg_mem
  rw [eq_top_iff, ← Y43_eq_top]
  refine le_trans ?_ hH
  rw [Y43, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact s43_mem_closure i

section Model

open CFSG.Assembly.LowTwoRank

theorem nonempty_mulEquiv_psp43 {G : Type} [Group G] (h : StatedClassicalModel G .PSp 2 3 1) :
    Nonempty (G ≃* PSp43) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, hF, ZMod.card]
    norm_num
  let φ : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hc
  let e₁ : StatedProj (StatedSp 2 F) ≃* PSp43 :=
    CFSG.Adapters.RankTwoModelTransports.statedProjCongr
      (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
      (CFSG.ClassicalInvolution.Upgrade.glCongr_statedSp φ 2)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  exact ⟨e.trans e₁⟩

theorem glbCore_eq_top_of_stated_u42 {K : Type} [Group K] [Finite K]
    (h : StatedClassicalModel K .PSU 4 2 1) (T : Sylow 3 K) :
    GLBCore 3 1 (T : Subgroup K) = ⊤ := by
  obtain ⟨e⟩ := nonempty_mulEquiv_psp43 (statedClassicalModel_PSp_two_three_of_PSU_four_two h)
  exact glbCore_eq_top_of_mulEquiv Nat.prime_three e (isPGroup_of_isElemAbelian EU_elem)
    glbCore_EU T

end Model

end CFSG.AGLEmbedding.OffCharU42
