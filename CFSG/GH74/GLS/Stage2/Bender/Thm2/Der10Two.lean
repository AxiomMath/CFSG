module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Der10One

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section C2a

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}

theorem exists_mem_S_not_mem_O2 (ctx : Stage2Ctx G z k S) {M : Subgroup G} (hCM : Cen z ≤ M)
    (hO2 : O2Of M ≠ M) : ∃ a ∈ S, a ∉ O2Of M := by
  by_contra hno
  push Not at hno
  have hSle : S ≤ O2Of M := hno
  have hSM : S ≤ M := ctx.S_le_Cen.trans hCM
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 S M := ctx.sylow_top.of_le hSM le_top
  have hM : M ≤ O2Of M := le_O2Of_of_sylow_le le_rfl hS hSle
  exact hO2 (le_antisymm (Subgroup.map_subtype_le _) hM)

theorem exists_conj_le_S_of_isPGroup {P : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z))
    (hP2 : IsPGroup 2 ↥P) (hPC : P ≤ Cen z) : ∃ kk ∈ Cen z, ∀ w ∈ P, kk⁻¹ * w * kk ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 ↥(P.subgroupOf (Cen z)) := hP2.comap_subtype
  obtain ⟨Q, hPQ⟩ := hP'.exists_le_sylow
  have hQ' : CFSG.ABGLocalTools.IsSylowOf 2 ((Q : Subgroup ↥(Cen z)).map (Cen z).subtype) (Cen z) :=
    ⟨Q, rfl⟩
  obtain ⟨kk, hkk, hconj⟩ := hS.exists_mem_conj hQ'
  exact ⟨kk, hkk, fun w hw => (hconj w).mp ⟨⟨w, hPC hw⟩, hPQ (Subgroup.mem_subgroupOf.mpr hw), rfl⟩⟩

theorem caseC_of_not_typeOne (ctx : Stage2Ctx G z k S) (hnot : ¬ TypeOneCase G k) : CaseC z S := by
  have hd := ctx.data
  clear ctx
  cases hd with
  | g2 h => exact absurd (Or.inl h.one_class) hnot
  | m12 h => exact absurd (Or.inr rfl) hnot
  | psp4 h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    obtain ⟨x, hx⟩ := h.two
    exact ⟨q, L₁, L₂, x, h.pair, hx⟩
  | l4 ε h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    rcases h.fusion with ⟨-, h1⟩ | ⟨-, x, hx, -⟩
    · exact absurd (Or.inl h1) hnot
    · exact ⟨q, L₁, L₂, x, h.pair, hx⟩
  | mcl h =>
    obtain ⟨n, -, h⟩ := h
    exact absurd (Or.inl h.one_class) hnot
  | ly h =>
    obtain ⟨n, -, h⟩ := h
    exact absurd (Or.inl h.one_class) hnot

theorem exists_admissible_swapper (h34 : Leaf_Prop34) (ctx9 : Ctx9 G z k S M p) {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} {x : G} (hpair : Stage1Pair G z S q L₁ L₂)
    (htwo : TwoClassData G z S L₁ L₂ q x) :
    ∃ t ∈ S, IsConj z t ∧ Swaps z t L₁ L₂ ∧ (z ∈ zStar M ∨ t ∉ O2Of M) := by
  have ctx := ctx9.ctx
  by_cases hz : z ∈ zStar M
  · obtain ⟨t, htS, htc, hts⟩ := htwo.swap_exists
    exact ⟨t, htS, htc, hts, Or.inl hz⟩
  · rcases h34 G z k S ctx M ctx9.cen_le ctx9.coatom.1 with
      hcov | hd | ⟨ε, q', L₁', L₂', hk, hL4, -, -, -, -, -, -, hO2, -⟩
    · exact absurd (mem_zStar_of_cover ctx9.z_mem hcov) hz
    · exact absurd hd (CFSG.GH74.GLS.Stage2.Final.Thm4.not_isDihedral_S ctx)
    · have hSC : S ≤ Cen z := ctx.S_le_Cen
      have hCM : Cen z ≤ M := ctx9.cen_le
      have hLK : LC z ≤ O2Of M := LC_le_O2Of hCM
      obtain ⟨a, haS, haK⟩ := exists_mem_S_not_mem_O2 ctx hCM hO2
      obtain ⟨t₀, ht₀S, -, ht₀sw⟩ := htwo.swap_exists
      obtain ⟨s, hsS, hsK, hssw⟩ := exists_swapper_not_mem hpair hSC haS haK ht₀S ht₀sw
      obtain ⟨l, hl, hsl⟩ := htwo.coset s (Subgroup.mem_sup_right hsS)
      have hlK : l ∈ O2Of M := hLK hl
      have hwC : s * l ∈ Cen z := Subgroup.mul_mem _ (hSC hsS) (LC_le_Cen z hl)
      have hwsw : Swaps z (s * l) L₁ L₂ := swaps_mul_LC hpair hssw hl
      have hwK : s * l ∉ O2Of M := fun h => hsK (by
        have := (O2Of M).mul_mem h ((O2Of M).inv_mem hlK)
        simpa using this)
      have hw2 : orderOf (s * l) = 2 := by
        obtain ⟨c, hc⟩ := isConj_iff.1 hsl
        rw [← hc, orderOf_conj_eq]
        exact ctx9.orderOf_z
      obtain ⟨kk, hkk, hyS⟩ := exists_conj_mem_S ctx.sylow hwC hw2
      have hyc : IsConj z (kk⁻¹ * (s * l) * kk) := hsl.trans (isConj_iff.2 ⟨kk⁻¹, by group⟩)
      have hysw : Swaps z (kk⁻¹ * (s * l) * kk) L₁ L₂ := by
        have := swaps_conj hpair (Subgroup.inv_mem _ hkk) hwsw
        rwa [inv_inv] at this
      have hyK : kk⁻¹ * (s * l) * kk ∉ O2Of M := fun h => hwK (by
        have := conj_mem_O2Of (hCM hkk) h
        have e : kk * (kk⁻¹ * (s * l) * kk) * kk⁻¹ = s * l := by group
        rwa [e] at this)
      exact ⟨_, hyS, hyc, hysw, Or.inr hyK⟩

theorem sylow_T_of_max (ctx : Stage2Ctx G z k S) (hCM : Cen z ≤ M) {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} (hpair : Stage1Pair G z S q L₁ L₂)
    {t : G} (htS : t ∈ S) (htc : IsConj z t) (hts : Swaps z t L₁ L₂)
    (htz : z ∈ zStar M ∨ t ∉ O2Of M)
    (hmax : ∀ t' : G, t' ∈ S → IsConj z t' → Swaps z t' L₁ L₂ → (z ∈ zStar M ∨ t' ∉ O2Of M) →
      Nat.card ↥(S ⊓ centralizer ({t'} : Set G)) ≤ Nat.card ↥(S ⊓ centralizer ({t} : Set G)))
    (hU : IVK.IsFourSubgroup (zpowers z ⊔ zpowers t)) :
    CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ centralizer ((zpowers z ⊔ zpowers t : Subgroup G) : Set G))
      (centralizer ((zpowers z ⊔ zpowers t : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U : Subgroup G := zpowers z ⊔ zpowers t with hUdef
  set X : Subgroup G := centralizer (U : Set G) with hX
  have hzU : z ∈ U := Subgroup.mem_sup_left (mem_zpowers z)
  have htU : t ∈ U := Subgroup.mem_sup_right (mem_zpowers t)
  have hSC : S ≤ Cen z := ctx.S_le_Cen
  have hzt : z * t = t * z := mul_comm_of_isFour hU hzU htU
  have hXC : X ≤ Cen z := fun x hx => by
    have := Subgroup.mem_centralizer_iff.mp hx z hzU
    exact Subgroup.mem_centralizer_singleton_iff.mpr this.symm
  have hSXt : S ⊓ X = S ⊓ centralizer ({t} : Set G) := by
    ext x
    constructor
    · rintro ⟨hxS, hxX⟩
      exact ⟨hxS, Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hxX t htU).symm⟩
    · rintro ⟨hxS, hxt⟩
      refine ⟨hxS, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp (hSC hxS)
      exact comm_of_mem_zpowers_sup hxz (Subgroup.mem_centralizer_singleton_iff.mp hxt) hzt hu
  have hUT : U ≤ S ⊓ X := by
    refine le_inf ?_ ?_
    · exact sup_le (Subgroup.zpowers_le.mpr ctx.z_mem) (Subgroup.zpowers_le.mpr htS)
    · intro u hu
      exact Subgroup.mem_centralizer_iff.mpr fun v hv => mul_comm_of_isFour hU hv hu
  have hT2 : IsPGroup 2 ↥((S ⊓ X).subgroupOf X) :=
    (ctx.sylow.isPGroup.to_le (inf_le_left : S ⊓ X ≤ S)).comap_subtype
  obtain ⟨P0, hTP0⟩ := hT2.exists_le_sylow
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 2 ((P0 : Subgroup ↥X).map X.subtype) X := ⟨P0, rfl⟩
  set P : Subgroup G := (P0 : Subgroup ↥X).map X.subtype with hPdef
  have hPX : P ≤ X := Subgroup.map_subtype_le _
  have hTP : S ⊓ X ≤ P := by
    intro x hx
    exact ⟨⟨x, hx.2⟩, hTP0 (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  obtain ⟨kk, hkk, hkkS⟩ := exists_conj_le_S_of_isPGroup ctx.sylow hPsyl.isPGroup (hPX.trans hXC)
  have htP : t ∈ P := hTP (hUT htU)
  set t' : G := kk⁻¹ * t * kk with ht'
  have ht'S : t' ∈ S := hkkS t htP
  have ht'c : IsConj z t' := htc.trans (isConj_iff.2 ⟨kk⁻¹, by rw [ht']; group⟩)
  have ht'sw : Swaps z t' L₁ L₂ := by
    have := swaps_conj hpair (Subgroup.inv_mem _ hkk) hts
    rwa [inv_inv] at this
  have ht'z : z ∈ zStar M ∨ t' ∉ O2Of M := by
    rcases htz with h | h
    · exact Or.inl h
    · right
      intro h'
      apply h
      have := conj_mem_O2Of (hCM hkk) h'
      have e : kk * (kk⁻¹ * t * kk) * kk⁻¹ = t := by group
      rwa [ht', e] at this
  have hle := hmax t' ht'S ht'c ht'sw ht'z
  have hconj : conjugate P kk ≤ S ⊓ centralizer ({t'} : Set G) := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    have hxS : x ∈ S := by
      have := hkkS _ hx
      have e : kk⁻¹ * (kk * x * kk⁻¹) * kk = x := by group
      rwa [e] at this
    refine ⟨hxS, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hw : (kk * x * kk⁻¹) * t = t * (kk * x * kk⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp (hPX hx) t htU).symm
    calc x * t' = kk⁻¹ * ((kk * x * kk⁻¹) * t) * kk := by rw [ht']; group
      _ = kk⁻¹ * (t * (kk * x * kk⁻¹)) * kk := by rw [hw]
      _ = t' * x := by rw [ht']; group
  have hcard1 : Nat.card ↥P ≤ Nat.card ↥(S ⊓ centralizer ({t'} : Set G)) := by
    rw [← card_conjugate P kk]
    exact Subgroup.card_le_of_le hconj
  have hcard2 : Nat.card ↥P ≤ Nat.card ↥(S ⊓ X) := by
    rw [hSXt]
    exact hcard1.trans hle
  have hPT : S ⊓ X = P := Subgroup.eq_of_le_of_card_ge hTP hcard2
  rw [hPT]
  exact hPsyl

end C2a

section C2d

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}

theorem Iof_ne_bot (ctx : Stage2Ctx G z k S) {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)} {x : G}
    (hpair : Stage1Pair G z S q L₁ L₂) (htwo : TwoClassData G z S L₁ L₂ q x)
    {t : G} (htS : t ∈ S) (htc : IsConj z t) (hts : Swaps z t L₁ L₂)
    (hU : IVK.IsFourSubgroup (zpowers z ⊔ zpowers t)) :
    Iof (zpowers z ⊔ zpowers t) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U : Subgroup G := zpowers z ⊔ zpowers t with hUdef
  set X : Subgroup G := centralizer (U : Set G) with hX
  have hzU : z ∈ U := Subgroup.mem_sup_left (mem_zpowers z)
  have htU : t ∈ U := Subgroup.mem_sup_right (mem_zpowers t)
  have hSC : S ≤ Cen z := ctx.S_le_Cen
  have htC : t ∈ Cen z := hSC htS
  have hzt : z * t = t * z := mul_comm_of_isFour hU hzU htU
  have hXC : X ≤ Cen z := fun x hx => by
    have := Subgroup.mem_centralizer_iff.mp hx z hzU
    exact Subgroup.mem_centralizer_singleton_iff.mpr this.symm
  set tC : ↥(Cen z) := ⟨t, htC⟩ with htCdef
  have ht2 : t * t = 1 := sq_eq_one_of_isFour hU htU
  have htC2 : ∃ n : ℕ, tC ^ 2 ^ n = 1 := ⟨1, by
    apply Subtype.ext
    simpa [pow_two] using ht2⟩
  have hcen : (centralizer ({tC} : Set ↥(Cen z))).map (toBar z) =
      centralizer ({toBar z tC} : Set (CentralizerBar z)) :=
    CFSG.ComponentClassification.LBalance.Quot.map_centralizer_eq (H := ↥(Cen z)) (p := 2) htC2
  set tb : CentralizerBar z := toBar z tC with htb
  set Y : Subgroup (CentralizerBar z) := centralizer ({tb} : Set (CentralizerBar z)) with hY
  have hXcen : ∀ y : ↥X, (⟨(y : G), hXC y.2⟩ : ↥(Cen z)) ∈ centralizer ({tC} : Set ↥(Cen z)) := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp y.2 t htU).symm
  let f0 : ↥X →* CentralizerBar z := (toBar z).comp (Subgroup.inclusion hXC)
  have hf0Y : ∀ y : ↥X, f0 y ∈ Y := by
    intro y
    have hmem : f0 y ∈ (centralizer ({tC} : Set ↥(Cen z))).map (toBar z) := ⟨_, hXcen y, rfl⟩
    rw [hcen] at hmem
    exact hmem
  let f : ↥X →* ↥Y := f0.codRestrict Y hf0Y
  have hfsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    have hmem : y ∈ (centralizer ({tC} : Set ↥(Cen z))).map (toBar z) := by rw [hcen]; exact hy
    obtain ⟨c, hc, rfl⟩ := hmem
    have hcz : (c : G) * z = z * (c : G) := Subgroup.mem_centralizer_singleton_iff.mp c.2
    have hct : (c : G) * t = t * (c : G) := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)
    have hcX : (c : G) ∈ X :=
      Subgroup.mem_centralizer_iff.mpr fun u hu => comm_of_mem_zpowers_sup hcz hct hzt hu
    exact ⟨⟨(c : G), hcX⟩, Subtype.ext rfl⟩
  have hker : ¬ 2 ∣ Nat.card f.ker := by
    have hle : f.ker.map (Subgroup.inclusion hXC) ≤ (toBar z).ker := by
      rintro _ ⟨y, hy, rfl⟩
      have : f y = 1 := hy
      have h2 : f0 y = 1 := congrArg Subtype.val this
      exact h2
    have hcard : Nat.card f.ker = Nat.card (f.ker.map (Subgroup.inclusion hXC)) :=
      (Subgroup.card_map_of_injective (Subgroup.inclusion_injective hXC)).symm
    have hdvd : Nat.card f.ker ∣ Nat.card (toBar z).ker := by
      rw [hcard]
      exact Subgroup.card_dvd_of_le hle
    have hodd : Odd (Nat.card f.ker) := Odd.of_dvd_nat (odd_card_ker_toBar z) hdvd
    exact fun h2 => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hmap := CFSG.ComponentClassification.UnbalancingLocal.Correspondence.map_pLayer_of_coprime_kernel
    (p := 2) f hfsurj hker
  obtain ⟨-, hL2, -⟩ := htwo.swap_conseq t htS htc hts
  obtain ⟨F₀, _, _, hF₀, ⟨e⟩⟩ := hL2
  have hF₀' : Nat.card F₀ = q := hF₀
  have hF : IVK.L2Field F₀ := ⟨by rw [hF₀']; exact hpair.odd, by rw [hF₀']; exact hpair.gt3⟩
  have hsimple : IsSimpleGroup ↥(layer ↥(CL z t)) := by
    have h4 : 4 ≤ Nat.card F₀ := by
      obtain ⟨-, h3⟩ := hF
      omega
    have : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 F₀) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    exact (IVK.toPSL e).isSimpleGroup
  have hneW : layer ↥(CL z t) ≠ ⊥ := by
    have := hsimple.toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this
  have hbarmem : tb ∈ barOf z (zpowers t) := ⟨tC, Subgroup.mem_subgroupOf.mpr (mem_zpowers t), rfl⟩
  have hcentbar : centralizer ((barOf z (zpowers t) : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) = Y := by
    ext c
    constructor
    · intro hc
      exact Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_centralizer_iff.mp hc tb hbarmem).symm)
    · intro hc
      refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
      obtain ⟨n, rfl⟩ := exists_zpow_of_mem_barOf htC hb
      have hc' : c * tb = tb * c := Subgroup.mem_centralizer_singleton_iff.mp hc
      exact ((Commute.zpow_left (show Commute tb c from hc'.symm) n).eq)
  have hCL : CL z t = LBar z ⊓ Y := by
    unfold CL
    rw [hcentbar]
  have hWY : CL z t ≤ Y := by rw [hCL]; exact inf_le_right
  have hnorm : ((CL z t).subgroupOf Y).Normal := by
    rw [hCL, Subgroup.inf_subgroupOf_right]
    exact (LBar_normal z).subgroupOf Y
  have hLY : layer ↥Y ≠ ⊥ := layer_ne_bot_of_normal_sub hWY hnorm hneW
  have hpLY : pLayer ↥Y 2 ≠ ⊥ := fun h =>
    hLY (le_bot_iff.mp (h ▸ CFSG.GH74.GLS.Stage2.Final.Thm4.layer_le_pLayer))
  have hpLX : pLayer ↥X 2 ≠ ⊥ := fun h => by
    apply hpLY
    rw [← hmap, h, Subgroup.map_bot]
  show pLayerOf 2 X ≠ ⊥
  rw [CFSG.GH74.GLS.Stage2.Final.Thm4.pLayerOf_eq_map]
  intro h
  exact hpLX ((Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp h)

end C2d

section C2e

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}

theorem choice10_typeTwo (h34 : Leaf_Prop34) (ctx9 : Ctx9 G z k S M p) (hnot : ¬ TypeOneCase G k) :
    ∃ (T U : Subgroup G) (t g : G), Choice10 G z k S M T U t g := by
  have ctx := ctx9.ctx
  obtain ⟨q, L₁, L₂, x, hpair, htwo⟩ := caseC_of_not_typeOne ctx hnot
  have hz2 : z * z = 1 := ctx9.z_mul_z
  have hz1 : z ≠ 1 := fun h => by
    have := ctx9.orderOf_z
    rw [h, orderOf_one] at this
    omega
  obtain ⟨t₀, ht₀⟩ := exists_admissible_swapper h34 ctx9 hpair htwo
  let 𝒢 : Set G := {t | t ∈ S ∧ IsConj z t ∧ Swaps z t L₁ L₂ ∧ (z ∈ zStar M ∨ t ∉ O2Of M)}
  obtain ⟨t, ⟨htS, htc, hts, htz⟩, hmax⟩ := Set.exists_max_image 𝒢
    (fun t : G => Nat.card ↥(S ⊓ centralizer ({t} : Set G))) (Set.toFinite 𝒢) ⟨t₀, ht₀⟩
  have hmax' : ∀ t' : G, t' ∈ S → IsConj z t' → Swaps z t' L₁ L₂ → (z ∈ zStar M ∨ t' ∉ O2Of M) →
      Nat.card ↥(S ⊓ centralizer ({t'} : Set G)) ≤ Nat.card ↥(S ⊓ centralizer ({t} : Set G)) :=
    fun t' h1 h2 h3 h4 => hmax t' ⟨h1, h2, h3, h4⟩
  have ht2o : orderOf t = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 htc
    rw [← hc, orderOf_conj_eq]
    exact ctx9.orderOf_z
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2o, pow_two] at this
  have ht1 : t ≠ 1 := fun h => by
    rw [h, orderOf_one] at ht2o
    omega
  have htne : t ≠ z := by
    intro htz'
    apply hpair.ne
    obtain ⟨htC', h1, h2⟩ := hts
    have hcen : toBar z ⟨t, htC'⟩ ∈ Subgroup.center (CentralizerBar z) := by
      have : (⟨t, htC'⟩ : ↥(Cen z)) = ⟨z, mem_Cen_self z⟩ := Subtype.ext htz'
      rw [this]
      exact toBar_z_mem_center z
    exact (h1.symm.trans (conjugate_of_center hcen L₁)).symm
  have hzt : z * t = t * z := (ctx.S_comm_z htS).symm
  have hU : IVK.IsFourSubgroup (zpowers z ⊔ zpowers t) :=
    isFour_zpowers_sup hz2 ht2 hz1 ht1 (Ne.symm htne) hzt
  have hzU : z ∈ zpowers z ⊔ zpowers t := Subgroup.mem_sup_left (mem_zpowers z)
  have htU : t ∈ zpowers z ⊔ zpowers t := Subgroup.mem_sup_right (mem_zpowers t)
  have hzS : z ∈ zStar M ∨ (zpowers z ⊔ zpowers t) ⊓ O2Of M = zpowers z := by
    rcases htz with h | h
    · exact Or.inl h
    · right
      have hzO : z ∈ O2Of M := LC_le_O2Of ctx9.cen_le (z_mem_LC_of_pair hpair ctx9.orderOf_z)
      apply le_antisymm
      · rintro w ⟨hwU, hwO⟩
        have hcomm : ∀ a ∈ zpowers z, ∀ b ∈ zpowers t, a * b = b * a := by
          intro a ha b hb
          obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
          exact (Commute.zpow_zpow (show Commute z t from hzt) m n).eq
        obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hwU
        rcases eq_one_or_eq_of_mem_zpowers hz2 ha with rfl | rfl <;>
          rcases eq_one_or_eq_of_mem_zpowers ht2 hb with rfl | rfl
        · simp
        · exact absurd (by simpa using hwO) h
        · simp
        · exact absurd (by
            have := (O2Of M).mul_mem ((O2Of M).inv_mem hzO) hwO
            simpa using this) h
      · exact le_inf (Subgroup.zpowers_le.mpr hzU) (Subgroup.zpowers_le.mpr hzO)
  obtain ⟨c, hc⟩ := isConj_iff.1 htc
  refine ⟨S ⊓ centralizer ((zpowers z ⊔ zpowers t : Subgroup G) : Set G), zpowers z ⊔ zpowers t, t, c⁻¹, ?_⟩
  exact
    { U_le := sup_le (Subgroup.zpowers_le.mpr ctx.z_mem) (Subgroup.zpowers_le.mpr htS)
      U_four := hU
      U_gen := rfl
      t_conj := by rw [inv_inv]; exact hc.symm
      t_out := fun m hm h => false_of_move_M hU hz2 hzU htU htne ht1 hzS (M.inv_mem hm) (by simpa using h)
      T_one := fun h => absurd h hnot
      T_two := fun _ => ⟨rfl, ⟨L₁, L₂, hpair.ne, hpair.comps, hts⟩,
        sylow_T_of_max ctx ctx9.cen_le hpair htS htc hts htz hmax' hU,
        Iof_ne_bot ctx hpair htwo htS htc hts hU,
        Subgroup.commutator_mono (LC_le_Cen z) le_rfl (ctx.prop22x q L₁ L₂ hpair t htS htc hts)⟩
      trans := fun h => absurd h hnot
      z_star := hzS
      z_star_one := fun h => absurd h hnot }

theorem choice10_exists_of (h34 : Leaf_Prop34) : Choice10_exists := by
  intro G _ _ z k S M p ctx9
  by_cases hone : TypeOneCase G k
  · exact choice10_typeOne h34 ctx9 hone
  · exact choice10_typeTwo h34 ctx9 hone

end C2e

end CFSG.GH74.GLS.Stage2.Bender.Thm2
