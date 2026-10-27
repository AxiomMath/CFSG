module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Chief
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Data
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Inputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OrthCase
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16SettingConj
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Unitary
public import CFSG.Yardstones.M9cbf837c48cf.Definitions
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Setup

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_of_isPGroup_of_le_normalizer {T M N : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hNM : N ≤ M)
    (hMN : M ≤ normalizer (N : Set G)) (hN : IsPGroup 2 ↥N) : N ≤ T := by
  have hsup := hT.isPGroup.to_sup_of_normal_right' hN (hT.le.trans hMN)
  have h := hT.eq_of_le le_sup_left (sup_le hT.le hNM) hsup
  exact (le_sup_right : N ≤ T ⊔ N).trans h.le

omit [Finite G] in
theorem le_normalizer_commutator {M V L : Subgroup G} (hV : M ≤ normalizer (V : Set G))
    (hL : M ≤ normalizer (L : Set G)) : M ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
  intro m hm
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hV hm), mem_normalizer_iff_map_conj_eq.mp (hL hm)]

omit [Finite G] in
theorem commutator_le_of_le_normalizer {V L : Subgroup G} (hL : L ≤ normalizer (V : Set G)) :
    ⁅V, L⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv l hl
  have h1 : l * v * l⁻¹ ∈ V := (mem_normalizer_iff.mp (hL hl) v).mp hv
  have h2 : l * v * l⁻¹ * v⁻¹ ∈ V := V.mul_mem h1 (V.inv_mem hv)
  have : ⁅v, l⁆ = (l * v * l⁻¹ * v⁻¹)⁻¹ := by rw [commutatorElement_def]; group
  rw [this]
  exact V.inv_mem h2

theorem matrix_eq_one_of_forall_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*}
    [Field F] (A : Matrix ι ι F) (h : ∀ v : ι → F, A.mulVec v = v) : A = 1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using this

theorem LocalSetting.of_normal {p : ℕ} {M V U : Subgroup G} (hS : LocalSetting p M V)
    (hmax : rankThreeIsMaxTwoLocal M) (hUV : U ≤ V) (hU1 : U ≠ ⊥)
    (hMU : M ≤ normalizer (U : Set G)) : LocalSetting p M U where
  elemAbelian := isElemAbelian_two_of_le hS.elemAbelian hUV
  ne_bot := hU1
  normalizer_eq := normalizer_eq_of_isMaxTwoLocal hmax hU1
    (elementary_isPGroup 2 U (isElemAbelian_two_of_le hS.elemAbelian hUV)) hMU
  self_normalizing := hS.self_normalizing
  spe := hS.spe
  u2 := hS.u2

theorem pow_two_pow_eq_one_of_centralizes {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
    [Field F] {H : Subgroup (GL ι F)} {L U : Subgroup G} (ε : ↥L →* ↥H)
    (φ : ↥U →* Multiplicative (ι → F)) (hφ : Function.Surjective φ)
    (hε : ε.ker = CFSG.pCore 2 ↥L)
    (hequiv : ∀ (l : ↥L) (u u' : ↥U), (l : G) * (u : G) * (l : G)⁻¹ = (u' : G) →
      φ u' = Multiplicative.ofAdd
        (((ε l : GL ι F) : Matrix ι ι F).mulVec (Multiplicative.toAdd (φ u)))) :
    ∀ l ∈ L, l ∈ centralizer (U : Set G) → ∃ k : ℕ, l ^ 2 ^ k = 1 := by
  intro l hl hlc
  have hA : ((ε ⟨l, hl⟩ : GL ι F) : Matrix ι ι F) = 1 := by
    apply matrix_eq_one_of_forall_mulVec
    intro w
    obtain ⟨u, hu⟩ := hφ (Multiplicative.ofAdd w)
    have hc : l * (u : G) * l⁻¹ = (u : G) := by
      have h1 : (u : G) * l = l * (u : G) := mem_centralizer_iff.mp hlc u u.2
      rw [← h1]
      group
    have h2 := hequiv ⟨l, hl⟩ u u hc
    rw [hu] at h2
    simpa using h2.symm
  have hε1 : ε ⟨l, hl⟩ = 1 := Subtype.ext (Units.ext hA)
  have hker : (⟨l, hl⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := hε ▸ MonoidHom.mem_ker.mpr hε1
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hker⟩
  exact ⟨k, congrArg (fun y : ↥(CFSG.pCore 2 ↥L) => ((y : ↥L) : G)) hk⟩

theorem inf_centralizer_V_eq_bot_of_chief {p : ℕ} {M T V L Q : Subgroup G} {x : G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hSetV : LocalSetting p M V) (hT2 : IsPGroup 2 ↥T)
    (hTM : T ≤ M) (hVT : V ≤ T)
    (hZV : CFSG.RankThree.PartOne.omegaOneCenterIn T ≤ V)
    (hN : ¬ normalizer (T : Set G) ≤ M) (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G))
    (hL2 : 2 ≤ CFSG.Open.pRank p L) (hQT : Q ≤ T) (hxL : x ∈ L)
    (hxQ : x ∈ normalizer (Q : Set G)) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hP : ∀ u ∈ ⁅V, L⁆, (∀ s ∈ Q, ⁅s, u⁆ ∈ centralizer (L : Set G)) →
      ⁅x, u⁆ ∈ centralizer (L : Set G)) :
    V ⊓ centralizer (L : Set G) = ⊥ := by
  have hMV : M ≤ normalizer (V : Set G) := le_of_eq hSetV.normalizer_eq.symm
  have hZc := pElement_centralizes_Z hp hp2 hSetV.elemAbelian hZV hLM hMV hQT hxL hxQ hx1 hxp hP
  have hZ1 := inf_centralizer_eq_bot hp hSetV hT2 hN hLM hL2 (hLM hxL) hx1 hxp hZc
  exact inf_centralizer_V_eq_bot hT2 hTM hVT hMV hML hSetV.elemAbelian hZ1

theorem unitary_branch {p n : ℕ} {P : Sylow p G} {M T V L : Subgroup G}
    (hUf : U4ModuleFacts) (hUc : U4ChiefFacts) (hS : Standing G) (hp : p ∈ rankThreeSigmaA G)
    (hw : IsWitness p P M) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hΓ : rankThreeGamma 1 p (P : Subgroup G) ≤ M) (hV1 : V ≠ ⊥)
    (hVdef : V = uCore M T) (hLdef : L = CFSG.RankThree.PartOne.pElementSubgroup p M)
    (hn : 1 ≤ n) (hpq : p ∣ 2 ^ n + 1) (hnc : ¬ L ≤ centralizer (V : Set G))
    (dC : U4ChiefData G n L ⁅V, L⁆) : normalizer (T : Set G) ≤ M := by
  by_contra hN
  have hprime := sigmaA_prime p hp
  have hp2 := sigmaA_odd p hp
  have hSetV : LocalSetting p M V := hVdef ▸ localSetting_of_witness hS hp hw hT hΓ (hVdef ▸ hV1)
  have hTM : T ≤ M := hT.le
  have hT2 : IsPGroup 2 ↥T := hT.isPGroup
  have hVab := hSetV.elemAbelian
  have hMV : M ≤ normalizer (V : Set G) := le_of_eq hSetV.normalizer_eq.symm
  have hVM : V ≤ M := le_trans Subgroup.le_normalizer (le_of_eq hSetV.normalizer_eq)
  have hVT : V ≤ T := le_of_isPGroup_of_le_normalizer hT hVM hMV (elementary_isPGroup 2 V hVab)
  have hLM : L ≤ M := hLdef ▸ pElementSubgroup_le p M
  have hML : M ≤ normalizer (L : Set G) := hLdef ▸ le_normalizer_pElementSubgroup p M
  have hL2 : 2 ≤ CFSG.Open.pRank p L := by
    have h3 := (hw.pRank_eq_three hS hp).2
    have := pRank_le_pElementSubgroup hprime M
    rw [hLdef]
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L) L := hT.inf_of_le_normalizer hLM hML
  obtain ⟨Q, hQS, x, hxQ', hx1, hxp, hP⟩ := hUc G p n L ⁅V, L⁆ dC hprime hpq hn
    (hLM.trans (le_normalizer_commutator hMV hML)) (T ⊓ L) hS'
  have hQT : Q ≤ T := hQS.trans inf_le_left
  have hZV : CFSG.RankThree.PartOne.omegaOneCenterIn T ≤ V :=
    hVdef ▸ omegaOneCenterIn_le_uCore M T
  have hxL : x ∈ L := (Subgroup.mem_inf.mp hxQ').1
  have hV0 := inf_centralizer_V_eq_bot_of_chief hprime hp2 hSetV hT2 hTM hVT hZV hN hLM hML hL2
    hQT hxL (Subgroup.mem_inf.mp hxQ').2 hx1 hxp hP
  have hUV : ⁅V, L⁆ ≤ V := commutator_le_of_le_normalizer (hLM.trans hMV)
  have hCU : ⁅V, L⁆ ⊓ centralizer (L : Set G) = ⊥ := by
    refine eq_bot_iff.mpr fun y hy => ?_
    have h : y ∈ V ⊓ centralizer (L : Set G) := ⟨hUV hy.1, hy.2⟩
    rw [hV0] at h
    exact h
  have hU1 : ⁅V, L⁆ ≠ ⊥ := by
    intro hbot
    apply hnc
    exact Subgroup.le_centralizer_iff.mpr (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
  let dN : U4NatData G n L ⁅V, L⁆ := dC.toNat hCU
  have hMU : M ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := le_normalizer_commutator hMV hML
  have hSetU : LocalSetting p M ⁅V, L⁆ := hSetV.of_normal hw.maxLocal hUV hU1 hMU
  have hUM : ⁅V, L⁆ ≤ M := hUV.trans hVM
  have hFU := hUf G p n M L ⁅V, L⁆ dN hprime hpq hn hLM hUM hML hMU
  have hFg : ∀ g : G, U4LocalFacts p n (cj g M) (cj g L) (cj g ⁅V, L⁆)
      (fun x => dN.sing (g⁻¹ * x * g)) := by
    intro g
    have h := hUf G p n (cj g M) (cj g L) (cj g ⁅V, L⁆) (dN.conj g) hprime hpq hn
      (Subgroup.map_mono hLM) (Subgroup.map_mono hUM)
      (by rw [cj_normalizer]; exact Subgroup.map_mono hML)
      (by rw [cj_normalizer]; exact Subgroup.map_mono hMU)
    rwa [U4NatData.sing_conj] at h
  have hW : ∀ g : G, cj g ⁅V, L⁆ ≤ M → cj g ⁅V, L⁆ ≤ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
    intro g hgU
    by_cases hg : g ∈ M
    · have h : cj g ⁅V, L⁆ = ⁅V, L⁆ := mem_normalizer_iff_map_conj_eq.mp (hMU hg)
      rw [h]
      exact Subgroup.le_centralizer_iff_isMulCommutative.mpr
        (isElemAbelian_two_of_le hVab hUV).1
    · exact unitary_commute hprime hn hSetU hFU (hSetU.conj g) (hFg g) hg hgU
  have hCL : L ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) ≤ T := by
    refine le_of_isPGroup_of_le_normalizer hT (inf_le_left.trans hLM) ?_ ?_
    · intro m hm
      rw [mem_normalizer_iff_map_conj_eq]
      show cj m (L ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G)) =
        L ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G)
      have h1 : cj m L = L := mem_normalizer_iff_map_conj_eq.mp (hML hm)
      have h2 : cj m ⁅V, L⁆ = ⁅V, L⁆ := mem_normalizer_iff_map_conj_eq.mp (hMU hm)
      have h3 : cj m (centralizer ((⁅V, L⁆ : Subgroup G) : Set G)) =
          centralizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
        rw [← cj_centralizer, h2]
      rw [cj_inf, h1, h3]
    · intro y
      obtain ⟨k, hk⟩ := pow_two_pow_eq_one_of_centralizes dN.ε dN.φ dN.φ_bij.2 dN.ε_ker
        dN.equiv y y.2.1 y.2.2
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hLN : L ≤ normalizer (weakClosureIn ⁅V, L⁆ T : Set G) :=
    le_normalizer_weakClosureIn_of_conj_le_centralizer hLM hML hTM hCL hW
  have hUT : ⁅V, L⁆ ≤ T := hUV.trans hVT
  have h2 : 2 ≤ CFSG.Open.pRank p (M ⊓ normalizer (weakClosureIn ⁅V, L⁆ T : Set G)) :=
    hL2.trans (CFSG.SectionRank.pRank_mono hprime.one_lt (le_inf hLM hLN))
  exact hN (hw.normalizer_le_of_weakClosure hT2 hUT hU1 h2)

theorem orth_branch {p n : ℕ} {P : Sylow p G} {M T V L : Subgroup G}
    (hOf : O6ModuleFacts) (hOc : O6ChiefFacts) (hS : Standing G) (hp : p ∈ rankThreeSigmaA G)
    (hw : IsWitness p P M) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hΓ : rankThreeGamma 1 p (P : Subgroup G) ≤ M) (hV1 : V ≠ ⊥)
    (hVdef : V = uCore M T) (hLdef : L = CFSG.RankThree.PartOne.pElementSubgroup p M)
    (hn : 1 ≤ n) (hpq : p ∣ 2 ^ n + 1) (hnc : ¬ L ≤ centralizer (V : Set G))
    (dC : O6ChiefData G n L ⁅V, L⁆) : normalizer (T : Set G) ≤ M := by
  by_contra hN
  have hprime := sigmaA_prime p hp
  have hp2 := sigmaA_odd p hp
  have hSetV : LocalSetting p M V := hVdef ▸ localSetting_of_witness hS hp hw hT hΓ (hVdef ▸ hV1)
  have hTM : T ≤ M := hT.le
  have hT2 : IsPGroup 2 ↥T := hT.isPGroup
  have hVab := hSetV.elemAbelian
  have hMV : M ≤ normalizer (V : Set G) := le_of_eq hSetV.normalizer_eq.symm
  have hVM : V ≤ M := le_trans Subgroup.le_normalizer (le_of_eq hSetV.normalizer_eq)
  have hVT : V ≤ T := le_of_isPGroup_of_le_normalizer hT hVM hMV (elementary_isPGroup 2 V hVab)
  have hLM : L ≤ M := hLdef ▸ pElementSubgroup_le p M
  have hML : M ≤ normalizer (L : Set G) := hLdef ▸ le_normalizer_pElementSubgroup p M
  have hL2 : 2 ≤ CFSG.Open.pRank p L := by
    have h3 := (hw.pRank_eq_three hS hp).2
    have := pRank_le_pElementSubgroup hprime M
    rw [hLdef]
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L) L := hT.inf_of_le_normalizer hLM hML
  obtain ⟨Q, hQS, x, hxQ', hx1, hxp, hP⟩ := hOc G p n L ⁅V, L⁆ dC hprime hpq hn
    (hLM.trans (le_normalizer_commutator hMV hML)) (T ⊓ L) hS'
  have hQT : Q ≤ T := hQS.trans inf_le_left
  have hZV : CFSG.RankThree.PartOne.omegaOneCenterIn T ≤ V :=
    hVdef ▸ omegaOneCenterIn_le_uCore M T
  have hxL : x ∈ L := (Subgroup.mem_inf.mp hxQ').1
  have hV0 := inf_centralizer_V_eq_bot_of_chief hprime hp2 hSetV hT2 hTM hVT hZV hN hLM hML hL2
    hQT hxL (Subgroup.mem_inf.mp hxQ').2 hx1 hxp hP
  have hUV : ⁅V, L⁆ ≤ V := commutator_le_of_le_normalizer (hLM.trans hMV)
  have hCU : ⁅V, L⁆ ⊓ centralizer (L : Set G) = ⊥ := by
    refine eq_bot_iff.mpr fun y hy => ?_
    have h : y ∈ V ⊓ centralizer (L : Set G) := ⟨hUV hy.1, hy.2⟩
    rw [hV0] at h
    exact h
  have hU1 : ⁅V, L⁆ ≠ ⊥ := by
    intro hbot
    apply hnc
    exact Subgroup.le_centralizer_iff.mpr (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
  let dN : O6NatData G n L ⁅V, L⁆ := dC.toNat hCU
  have hMU : M ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := le_normalizer_commutator hMV hML
  have hSetU : LocalSetting p M ⁅V, L⁆ := hSetV.of_normal hw.maxLocal hUV hU1 hMU
  have hUM : ⁅V, L⁆ ≤ M := hUV.trans hVM
  have hFU := hOf G p n M L ⁅V, L⁆ dN hprime hpq hn hLM hUM hML hMU
  have hFg : ∀ g : G, O6LocalFacts p n (cj g M) (cj g L) (cj g ⁅V, L⁆)
      (fun x => dN.sing (g⁻¹ * x * g)) := by
    intro g
    have h := hOf G p n (cj g M) (cj g L) (cj g ⁅V, L⁆) (dN.conj g) hprime hpq hn
      (Subgroup.map_mono hLM) (Subgroup.map_mono hUM)
      (by rw [cj_normalizer]; exact Subgroup.map_mono hML)
      (by rw [cj_normalizer]; exact Subgroup.map_mono hMU)
    rwa [O6NatData.sing_conj] at h
  obtain ⟨Pp, hPL, hP2, hPN⟩ :=
    orth_normalizes hprime hn hSetU hFU (fun g => hSetU.conj g) hFg hT
  have hUT : ⁅V, L⁆ ≤ T := hUV.trans hVT
  have h2 : 2 ≤ CFSG.Open.pRank p (M ⊓ normalizer (weakClosureIn ⁅V, L⁆ T : Set G)) :=
    hP2.trans (CFSG.SectionRank.pRank_mono hprime.one_lt (le_inf (hPL.trans hLM) hPN))
  exact hN (hw.normalizer_le_of_weakClosure hT2 hUT hU1 h2)

theorem agl81Residual7U4_of_facts (hK : KFactAGL81I54U4) (hUf : U4ModuleFacts)
    (hUc : U4ChiefFacts) (hOf : O6ModuleFacts) (hOc : O6ChiefFacts) {G : Type} [Group G]
    [Finite G] (hS : Standing G) : AGL81Residual7U4 G := by
  intro hUC p hp P M hw hshape T hT H1 H2 H3 H4 hcon H6 H7 H8 H9 H10
  have hprime := sigmaA_prime p hp
  have hp2 := sigmaA_odd p hp
  have hV1 : uCore M T ≠ ⊥ := uCore_ne_bot_of_thompsonJ H2
  have hZ1 : CFSG.RankThree.PartOne.omegaOneCenterIn T ≠ ⊥ :=
    CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_ne_bot hT.isPGroup
      (ne_bot_of_isSylowOf_two hw.maxLocal.1 hT)
  have hM2 : 2 ≤ CFSG.Open.pRank p M := by
    have := (hw.pRank_eq_three hS hp).2
    omega
  have hnc : ¬ CFSG.RankThree.PartOne.pElementSubgroup p M ≤ centralizer (uCore M T : Set G) := by
    intro h
    exact not_le_centralizer_omegaOneCenterIn hprime hM2 hZ1 H4
      (h.trans (centralizer_le (omegaOneCenterIn_le_uCore M T)))
  obtain ⟨n, hshapeAt⟩ := hshape.exists_shapeAt
  obtain ⟨d, ⟨q, hq2, hqn, hd, hpq⟩, hiso⟩ := hshapeAt
  have hn : 1 ≤ n := hqn ▸ q.exponent_pos
  have hqcard : q.card = 2 ^ n := by rw [TauCeti.PrimePower.card_def, hq2, hqn]
  have hpq' : p ∣ 2 ^ n + 1 := hqcard ▸ hpq
  have hFstar : M ⊓ centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    hS.charTwo M hw.maxLocal.1
  have hconc := hK G p n M T hprime hp2 hFstar hT ⟨d, ⟨q, hq2, hqn, hd, hpq⟩, hiso⟩ hnc H9
  rcases hconc with ⟨F, instF, instFin, hcard, ε, φ, hεs, hφs, hεk, hφk, heqv⟩ |
      ⟨F, instF, instFin, b, c, hcard, hirr, ε, φ, hεs, hφs, hεk, hφk, heqv⟩
  · exact unitary_branch hUf hUc hS hp hw hT H10 hV1 rfl rfl hn hpq' hnc
      { F := F, instField := instF, instFinite := instFin, card_F := hcard, ε := ε, φ := φ,
        ε_surj := hεs, φ_surj := hφs, ε_ker := hεk, φ_ker := hφk, equiv := heqv }
  · exact orth_branch hOf hOc hS hp hw hT H10 hV1 rfl rfl hn hpq' hnc
      { F := F, instField := instF, instFinite := instFin, card_F := hcard, b := b, c := c,
        irred := hirr, ε := ε, φ := φ, ε_surj := hεs, φ_surj := hφs, ε_ker := hεk,
        φ_ker := hφk, equiv := heqv }

end CFSG.LocalAnalysis.RankThreeUC

namespace CFSG.Yardstones.M9cbf837c48cf

open CFSG.LocalAnalysis.RankThreeUC

theorem agl81TheoremDSection16_of_facts (hK : KFactAGL81I54U4) (hUf : U4ModuleFacts)
    (hUc : U4ChiefFacts) (hOf : O6ModuleFacts) (hOc : O6ChiefFacts) :
    AGL81TheoremDSection16Statement := by
  intro G _ _ _ hnonab hKP hchar he
  exact agl81Residual7U4_of_facts hK hUf hUc hOf hOc
    ⟨inferInstance, hnonab, hKP, hchar, he⟩

end CFSG.Yardstones.M9cbf837c48cf
