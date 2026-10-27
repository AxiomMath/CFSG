module

public import CFSG.ClassicalInvolution.Q3.TL4Thm5Bridge
public import CFSG.ClassicalInvolution.Q3.TL4MF164Dat
public import CFSG.ClassicalInvolution.Q3.TL4E3C269Sec
public import CFSG.Goldschmidt.Steps.Rank2List
public import CFSG.ClassicalInvolution.Q3.TL4Res2FOLie
public import CFSG.ClassicalInvolution.Q3.TL4Res2FOAut

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint
open scoped commutatorElement

namespace Outer

section Alpha

variable {X : Type} [Group X]

theorem alphaOf_eq_bot_of_oddCoreOf {A : Subgroup X} (hA : ∃ a ∈ A, a ≠ 1)
    (h : ∀ a ∈ A, a ≠ 1 → oddCoreOf (Subgroup.centralizer ({a} : Set X)) = ⊥) :
    alphaOf A = ⊥ := by
  obtain ⟨a₀, ha₀, ha₀1⟩ := hA
  refine le_bot_iff.mp (sup_le ?_ ?_)
  · refine iSup₂_le fun a ha => iSup_le fun ha1 => ?_
    rw [h a ha ha1, Subgroup.commutator_bot_left]
  · exact (iInf₂_le a₀ ha₀).trans ((iInf_le _ ha₀1).trans (h a₀ ha₀ ha₀1).le)

theorem mem_closure_pair {z t g : X} (hz : z * z = 1) (ht : t * t = 1) (hzt : z * t = t * z)
    (hg : g ∈ Subgroup.closure ({z, t} : Set X)) : g = 1 ∨ g = z ∨ g = t ∨ g = z * t := by
  have c : t * z = z * t := hzt.symm
  have s1 : ∀ b, z * (z * b) = b := fun b => by rw [← mul_assoc, hz, one_mul]
  have c' : ∀ b, t * (z * b) = z * (t * b) := fun b => by rw [← mul_assoc, c, mul_assoc]
  have i1 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have i2 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  refine Subgroup.closure_induction
    (p := fun g _ => g = 1 ∨ g = z ∨ g = t ∨ g = z * t) ?_ ?_ ?_ ?_ hg
  · intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with hu | hu <;> subst hu <;> simp
  · simp
  · rintro a b - - (ha | ha | ha | ha) (hb | hb | hb | hb) <;> subst ha <;> subst hb <;>
      simp [mul_assoc, hz, ht, s1, c, c']
  · rintro a - (ha | ha | ha | ha) <;> subst ha <;> simp [i1, i2, c]

theorem alphaOf_pair_eq_bot {z t : X} (hz : z * z = 1) (ht : t * t = 1) (hzt : z * t = t * z)
    (hz1 : z ≠ 1) (h : ∀ a, (a = z ∨ a = t ∨ a = z * t) → a ≠ 1 →
      oddCoreOf (Subgroup.centralizer ({a} : Set X)) = ⊥) :
    alphaOf (Subgroup.closure ({z, t} : Set X)) = ⊥ := by
  refine alphaOf_eq_bot_of_oddCoreOf ⟨z, Subgroup.subset_closure (by simp), hz1⟩ fun a ha ha1 => ?_
  rcases mem_closure_pair hz ht hzt ha with rfl | rfl | rfl | rfl
  · exact absurd rfl ha1
  · exact h _ (Or.inl rfl) ha1
  · exact h _ (Or.inr (Or.inl rfl)) ha1
  · exact h _ (Or.inr (Or.inr rfl)) ha1

end Alpha

section Sec

variable {X : Type} [Group X] [Finite X]

theorem fstar_le_of_normal (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) {N : Subgroup X} (hN : N.Normal)
    (hN1 : N ≠ ⊥) : genFittingFStar X ≤ N := by
  have hFn := genFittingFStar_normal X
  have := hN.subgroupOf (genFittingFStar X)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (genFittingFStar X)) with h | h
  · exfalso
    apply hN1
    have hdis : Disjoint N (genFittingFStar X) := Subgroup.subgroupOf_eq_bot.mp h
    rw [eq_bot_iff]
    intro x hx
    have hxc : x ∈ Subgroup.centralizer (genFittingFStar X : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.commute_of_normal_of_disjoint _ _ hN hFn hdis x y hx hy).eq.symm
    rw [centralizer_genFittingFStar_eq_bot hnab] at hxc
    exact hxc
  · exact Subgroup.subgroupOf_eq_top.mp h

theorem fstar_le_omegaGen (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) {r : ℕ} {Φ : Set (Subgroup X)}
    (hΦ : TypeRFam r Φ) {K : Subgroup X} (hK : K ∈ Φ) : genFittingFStar X ≤ omegaGen Φ := by
  refine fstar_le_of_normal hs hnab (omegaGen_normal hΦ.hyp.conjInvariant) fun h0 => ?_
  obtain ⟨⟨z, hz⟩, -⟩ := hΦ.hyp.omega1 K hK
  have hzm : z ∈ omegaGen Φ := le_omegaGen hK hz.mem
  rw [h0, Subgroup.mem_bot] at hzm
  exact hz.ne_one hzm

variable {Y : Subgroup X}

theorem centralizer_fstar_sec_eq_bot (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) (hFY : genFittingFStar X ≤ Y) :
    Subgroup.centralizer (((genFittingFStar X).subgroupOf Y : Subgroup ↥Y) : Set ↥Y) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxc : (x : X) ∈ Subgroup.centralizer (genFittingFStar X : Set X) := by
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    exact congrArg Subtype.val (hx ⟨y, hFY hy⟩ (Subgroup.mem_subgroupOf.mpr hy))
  rw [centralizer_genFittingFStar_eq_bot hnab, Subgroup.mem_bot] at hxc
  exact (Subgroup.mem_bot).mpr (Subtype.ext hxc)

omit [Finite X] in
theorem isSimpleGroup_fstar_sec (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hFY : genFittingFStar X ≤ Y) : IsSimpleGroup ↥((genFittingFStar X).subgroupOf Y) :=
  (Subgroup.subgroupOfEquivOfLe hFY).isSimpleGroup

omit [Finite X] in
theorem nonabelian_fstar_sec (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a)
    (hFY : genFittingFStar X ≤ Y) :
    ∃ a b : ↥((genFittingFStar X).subgroupOf Y), a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hnab
  set e := Subgroup.subgroupOfEquivOfLe hFY
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have h1 := congrArg e h
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1

theorem fstar_sec_eq (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) (hFY : genFittingFStar X ≤ Y) :
    genFittingFStar ↥Y = (genFittingFStar X).subgroupOf Y := by
  have : ((genFittingFStar X).subgroupOf Y).Normal := (genFittingFStar_normal X).subgroupOf Y
  have := isSimpleGroup_fstar_sec hs hFY
  exact genFittingFStar_eq_of_normal_simple _ (nonabelian_fstar_sec hnab hFY)
    (centralizer_fstar_sec_eq_bot hs hnab hFY)

theorem center_sec_eq_bot (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) (hFY : genFittingFStar X ≤ Y) :
    Subgroup.center ↥Y = ⊥ :=
  le_bot_iff.mp ((centralizer_fstar_sec_eq_bot hs hnab hFY) ▸
    Subgroup.center_le_centralizer _)

theorem oddCore_sec_eq_bot (hO : classicalInvolutionOddCore X = ⊥)
    (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) (hFY : genFittingFStar X ≤ Y) :
    classicalInvolutionOddCore ↥Y = ⊥ := by
  set F' : Subgroup ↥Y := (genFittingFStar X).subgroupOf Y with hF'
  have hF'n : F'.Normal := (genFittingFStar_normal X).subgroupOf Y
  have := isSimpleGroup_fstar_sec hs hFY
  have hOn := classicalInvolutionOddCore_normal ↥Y
  have := hOn.subgroupOf F'
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((classicalInvolutionOddCore ↥Y).subgroupOf F') with h | h
  · have hdis : Disjoint (classicalInvolutionOddCore ↥Y) F' := Subgroup.subgroupOf_eq_bot.mp h
    rw [eq_bot_iff, ← centralizer_fstar_sec_eq_bot hs hnab hFY]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.commute_of_normal_of_disjoint _ _ hOn hF'n hdis x y hx hy).eq.symm
  · exfalso
    have hle : F' ≤ classicalInvolutionOddCore ↥Y := Subgroup.subgroupOf_eq_top.mp h
    have hodd : Odd (Nat.card ↥(genFittingFStar X)) := by
      have h1 : Odd (Nat.card ↥(classicalInvolutionOddCore ↥Y)) :=
        CFSG.ComponentClassification.OddCore.odd_card ↥Y
      have h2 : Nat.card ↥F' ∣ Nat.card ↥(classicalInvolutionOddCore ↥Y) :=
        Subgroup.card_dvd_of_le hle
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFY).toEquiv] at h2
      exact h1.of_dvd_nat h2
    have hFO : genFittingFStar X ≤ classicalInvolutionOddCore X :=
      le_sSup ⟨genFittingFStar_normal X, hodd⟩
    rw [hO, le_bot_iff] at hFO
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a = 1 := Subtype.ext (by simpa [hFO] using a.2)
    exact hab (by rw [ha, one_mul, mul_one])

omit [Finite X] in
theorem conjSub_le_of_mem {H : Subgroup X} (hHY : H ≤ Y) {g : X} (hg : g ∈ Y) :
    conjSub g H ≤ Y := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rw [e]
  exact Y.mul_mem (Y.mul_mem hg (hHY hx)) (Y.inv_mem hg)

theorem natCard_sec_lt (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) {r : ℕ} {Φ : Set (Subgroup X)}
    (hΦ : TypeRFam r Φ) {K : Subgroup X} (hK : K ∈ Φ) (hgen : omegaGen Φ ≠ ⊤) :
    Nat.card ↥(K ⊔ genFittingFStar X) < Nat.card X := by
  have hle : K ⊔ genFittingFStar X ≤ omegaGen Φ :=
    sup_le (le_omegaGen hK) (fstar_le_omegaGen hs hnab hΦ hK)
  have hlt := Subgroup.card_lt_of_lt (lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hgen))
  rwa [Subgroup.card_top] at hlt

theorem iSup_conjSub_sec (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) {K : Subgroup X} {z : X}
    (hz : IsUniqueInvolution K z) :
    (⨆ g : ↥(K ⊔ genFittingFStar X), conjSub (g : X) K) = K ⊔ genFittingFStar X := by
  set Y := K ⊔ genFittingFStar X with hY
  set N := ⨆ g : ↥Y, conjSub (g : X) K with hN
  have hKY : K ≤ Y := le_sup_left
  have hFY : genFittingFStar X ≤ Y := le_sup_right
  have hFn := genFittingFStar_normal X
  have hKN : K ≤ N := by
    have h1 := le_iSup (fun g : ↥Y => conjSub (g : X) K) 1
    rwa [OneMemClass.coe_one, conjSub_one] at h1
  have hNn : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N := by
    intro y hy n hn
    have h1 : conjSub y N ≤ N := by
      show (⨆ g : ↥Y, conjSub (g : X) K).map (MulAut.conj y).toMonoidHom ≤ N
      rw [Subgroup.map_iSup]
      refine iSup_le fun g => ?_
      show conjSub y (conjSub (g : X) K) ≤ N
      rw [← conjSub_mul]
      exact le_iSup (fun g : ↥Y => conjSub (g : X) K) ⟨y * g, Y.mul_mem hy g.2⟩
    exact h1 (conj_mem_conjSub hn)
  refine le_antisymm (iSup_le fun g => conjSub_le_of_mem hKY g.2) (sup_le hKN ?_)
  have hNF : (N.subgroupOf (genFittingFStar X)).Normal := by
    refine ⟨fun a ha f => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact hNn f (hFY f.2) a ha
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (genFittingFStar X)) with h | h
  · exfalso
    have hdis : Disjoint N (genFittingFStar X) := Subgroup.subgroupOf_eq_bot.mp h
    have hzc : z ∈ Subgroup.centralizer (genFittingFStar X : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 : z * y * z⁻¹ * y⁻¹ ∈ N := by
        have h2 := hNn y (hFY hy) z⁻¹ (N.inv_mem (hKN hz.mem))
        simpa [mul_assoc] using N.mul_mem (hKN hz.mem) h2
      have h2 : z * y * z⁻¹ * y⁻¹ ∈ genFittingFStar X :=
        (genFittingFStar X).mul_mem (hFn.conj_mem y hy z) ((genFittingFStar X).inv_mem hy)
      have hc : z * y * z⁻¹ = y := mul_inv_eq_one.mp (Subgroup.disjoint_def.mp hdis h1 h2)
      calc y * z = z * y * z⁻¹ * z := by rw [hc]
        _ = z * y := by group
    rw [centralizer_genFittingFStar_eq_bot hnab, Subgroup.mem_bot] at hzc
    exact hz.ne_one hzc
  · exact Subgroup.subgroupOf_eq_top.mp h

omit [Finite X] in
theorem tightCore_sec {r : ℕ} {Φ : Set (Subgroup X)} (hΦ : TypeRFam r Φ) {K : Subgroup X}
    (hK : K ∈ Φ) (hKY : K ≤ Y) : tightCore (K.subgroupOf Y) = K.subgroupOf Y := by
  rw [tightCore_subgroupOf ((tightCore_le K).trans hKY)]
  congr 1
  exact hΦ.closure_twoElts hK

theorem tightCls_sec (hO : classicalInvolutionOddCore X = ⊥)
    (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) {Φ : Set (Subgroup X)}
    (hΦ : TypeRFam 3 Φ) {K : Subgroup X} (hK : K ∈ Φ) {z : X} (hz : IsUniqueInvolution K z) :
    ∃ S' : Sylow 2 ↥(K.subgroupOf (K ⊔ genFittingFStar X)),
      TightDatum (K.subgroupOf (K ⊔ genFittingFStar X)) S'
          ⟨z, (le_sup_left : K ≤ K ⊔ genFittingFStar X) hz.mem⟩ ∧
        TightCls ↥(K ⊔ genFittingFStar X) (K.subgroupOf (K ⊔ genFittingFStar X)) S'
          ⟨z, (le_sup_left : K ≤ K ⊔ genFittingFStar X) hz.mem⟩ := by
  set Y := K ⊔ genFittingFStar X with hY
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥K))
  have hd := Vtx.tightDatum_of_mem hΦ hK hz S
  have hKY : K ≤ Y := le_sup_left
  obtain ⟨S', hd', ⟨e⟩⟩ := hd.restrict (H := Y) ((Subgroup.map_subtype_le _).trans hKY)
  refine ⟨S', hd', ⟨e.trans (Vtx.nonempty_sylow_equiv hΦ hK S).some⟩, ?_,
    oddCore_sec_eq_bot hO hs hnab le_sup_right⟩
  show (⨆ g : ↥Y, conjSub g (tightCore (K.subgroupOf Y))) = ⊤
  rw [tightCore_sec hΦ hK hKY]
  apply Subgroup.map_injective Y.subtype_injective
  rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have e2 : ∀ g : ↥Y, (conjSub g (K.subgroupOf Y)).map Y.subtype = conjSub (g : X) K := by
    intro g
    rw [conjSub_subgroupOf, Subgroup.map_subgroupOf_eq_of_le]
    exact conjSub_le_of_mem hKY g.2
  simp_rw [e2]
  exact iSup_conjSub_sec hs hnab hz

theorem not_tightInO2_sec (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) (hFY : genFittingFStar X ≤ Y)
    {t : ↥Y} (ht : t ≠ 1) : ¬ TightInO2 t := by
  have hs' : IsSimpleGroup ↥(genFittingFStar ↥Y) := by
    rw [fstar_sec_eq hs hnab hFY]
    exact isSimpleGroup_fstar_sec hs hFY
  have hnab' : ∃ a b : ↥(genFittingFStar ↥Y), a * b ≠ b * a := by
    rw [fstar_sec_eq hs hnab hFY]
    exact nonabelian_fstar_sec hnab hFY
  exact not_tightInO2_of_fstar_simple hs' hnab' ht

theorem not_tightTwisted_sec (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) (hFY : genFittingFStar X ≤ Y)
    (t : ↥Y) : ¬ TightTwisted ↥Y t := by
  rintro ⟨L, -, -, -, -, -, hFZ, hFL⟩
  rw [center_sec_eq_bot hs hnab hFY] at hFZ
  exact hFL (hFZ.trans bot_le)

end Sec

section Members

variable {X : Type} [Group X] {r : ℕ} {Φ : Set (Subgroup X)} {K : Subgroup X} {z : X}

theorem eq_conjSub_of_conj (hΦ : TypeRFam r Φ) (hK : K ∈ Φ) (hz : IsUniqueInvolution K z)
    {J : Subgroup X} (hJ : J ∈ Φ) {t : X} (ht : IsUniqueInvolution J t) {c : X}
    (hc : c * z * c⁻¹ = t) : J = conjSub c K := by
  have h1 := hz.conj c
  rw [hc] at h1
  exact hΦ.noTwins _ (hΦ.hyp.conjInvariant c K hK) J ⟨hJ, t, h1, ht⟩

theorem exists_conj_of_trans (htr : ∀ L ∈ Φ, ∀ M ∈ Φ, ∃ g : X, conjSub g L = M) (hK : K ∈ Φ)
    (hz : IsUniqueInvolution K z) {J : Subgroup X} (hJ : J ∈ Φ) {t : X}
    (ht : IsUniqueInvolution J t) : ∃ g : X, g * z * g⁻¹ = t := by
  obtain ⟨g, rfl⟩ := htr K hK J hJ
  exact ⟨g, (hz.conj g).eq ht⟩

theorem ne_and_commute_of_mem_omegaNbr [Finite X] (hΦ : TypeRFam r Φ) (hK : K ∈ Φ)
    (hz : IsUniqueInvolution K z) {J : Subgroup X} (hJ : J ∈ omegaNbr Φ K) {t : X}
    (ht : IsUniqueInvolution J t) : t ≠ z ∧ z * t = t * z := by
  obtain ⟨hJΦ, hne, T, hT, hTJ, hTN⟩ := hJ
  refine ⟨fun h => hne (hΦ.noTwins K hK J ⟨hJΦ, z, hz, h ▸ ht⟩), ?_⟩
  have hTsyl : IsSylow2In T J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΦ.hyp hJΦ hT hTJ
  have htT : t ∈ T := Q3CP.mem_of_isSylow2In_of_isUniqueInvolution ht hTsyl
  have h1 : t * z * t⁻¹ = z := hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hTN htT))
  calc z * t = t * z * t⁻¹ * t := by rw [h1]
    _ = t * z := by group

theorem mem_omegaNbr_sec [Finite X] (hΩ : HypOmegaGen Φ) {Y : Subgroup X} (hKY : K ≤ Y)
    {J : Subgroup X} (hJ : J ∈ omegaNbr Φ K) {c : X} (hc : c ∈ Y) (hJc : J = conjSub c K) :
    J.subgroupOf Y ∈ omegaNbr (CoreAssembly.conjClass (K.subgroupOf Y)) (K.subgroupOf Y) := by
  obtain ⟨hJΦ, hne, T, hT, hTJ, hTN⟩ := hJ
  have hJY : J ≤ Y := hJc ▸ conjSub_le_of_mem hKY hc
  have hTsyl : IsSylow2In T J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΦ hT hTJ
  have hJ' : J.subgroupOf Y ∈ CoreAssembly.conjClass (K.subgroupOf Y) :=
    ⟨⟨c, hc⟩, by show conjSub _ _ = _; rw [conjSub_subgroupOf, ← hJc]⟩
  refine ⟨hJ', subgroupOf_ne_of_ne hKY hJY hne, T.subgroupOf Y,
    mem_RSet_of_isSylow2In hJ' (hTsyl.subgroupOf hJY), Subgroup.subgroupOf_mono Y hTJ,
    fun x hx => ?_⟩
  exact (mem_normalizer_subgroupOf_iff hKY).mp (hTN (Subgroup.mem_subgroupOf.mp hx))

end Members

section Exits

theorem invConj_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : ∀ a b : B, orderOf a = 2 → orderOf b = 2 → IsConj a b) :
    ∀ a b : A, orderOf a = 2 → orderOf b = 2 → IsConj a b := by
  intro a b ha hb
  have h1 := MonoidHom.map_isConj e.symm.toMonoidHom
    (h (e a) (e b) (by rwa [MulEquiv.orderOf_eq]) (by rwa [MulEquiv.orderOf_eq]))
  simpa using h1

variable {Y : Type} [Group Y]

theorem invConj_fstar_psl2 (hs : IsSimpleGroup ↥(genFittingFStar Y)) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hL : LieModel (FStarQuot Y) .PSL 2 p f) :
    ∀ a b : ↥(genFittingFStar Y), orderOf a = 2 → orderOf b = 2 → IsConj a b := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := MF164.exists_fstar_equiv_psl2 hs hL
  have : Fact p.Prime := ⟨hp⟩
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · have h1 : 1 < Nat.card F := Finite.one_lt_card
      rw [hF, h0, pow_zero] at h1
      exact absurd h1 (lt_irrefl _)
    · exact h0
  exact invConj_of_mulEquiv e fun a b ha hb =>
    Walter.psl2_isConj_of_orderOf_eq_two F hF (hp.odd_of_ne_two hp2) hf0 ha hb

theorem invConj_fstar_psl3 [IsSimpleGroup ↥(genFittingFStar Y)] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hL : LieModel (FStarQuot Y) .PSL 3 p f) :
    ∀ a b : ↥(genFittingFStar Y), orderOf a = 2 → orderOf b = 2 → IsConj a b := by
  obtain ⟨K, _, _, hK, ⟨e⟩, -⟩ := E3C269.exists_psl3_equiv hL
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  refine invConj_of_mulEquiv
    (e.trans (LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
      3 K).symm) fun a b ha hb => ?_
  exact (Goldschmidt.Rank2List.psl3_isConj hodd ha).trans
    (Goldschmidt.Rank2List.psl3_isConj hodd hb).symm

theorem invConj_fstar_psu3 (hs : IsSimpleGroup ↥(genFittingFStar Y))
    (hnab : ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hL : LieModel (FStarQuot Y) .PSU 3 p f) :
    ∀ a b : ↥(genFittingFStar Y), orderOf a = 2 → orderOf b = 2 → IsConj a b := by
  obtain ⟨-, hf, K, _, _, hK, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hL
  have h : LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  have hZ : Subgroup.center ↥(genFittingFStar Y) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(genFittingFStar Y)) with
      h0 | h0
    · exact h0
    · obtain ⟨a, b, hab⟩ := hnab
      exact absurd ((Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top b)) a) hab
  obtain ⟨eF⟩ := MFMuZ2.nonempty_fstar_equiv hZ
  refine invConj_of_mulEquiv ((eF.trans e₀).trans
    (ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (n := 3) (by norm_num)).symm)
    fun a b ha hb => ?_
  exact (RankThree.Classical.isConj_unitaryProj_unitaryInvT h hp2 ha).trans
    (RankThree.Classical.isConj_unitaryProj_unitaryInvT h hp2 hb).symm

variable {X : Type} [Group X] [Finite X]

theorem exists_sq_eq_of_typeR {Φ : Set (Subgroup X)} (hΦ : TypeRFam 3 Φ) {K : Subgroup X}
    (hK : K ∈ Φ) {z : X} (hz : IsUniqueInvolution K z) : ∃ w ∈ K, w * w = z ∧ w ^ 4 = 1 := by
  obtain ⟨P, hP⟩ := Sec7.exists_isSylow2In K
  obtain ⟨e⟩ := hΦ.quat K hK P hP
  have h11 : (QuaternionGroup.a 1 : QuaternionGroup (2 ^ (3 - 2))) * QuaternionGroup.a 1 =
      QuaternionGroup.a 2 := by decide
  have h22 : (QuaternionGroup.a 2 : QuaternionGroup (2 ^ (3 - 2))) * QuaternionGroup.a 2 = 1 := by
    decide
  have h21 : (QuaternionGroup.a 2 : QuaternionGroup (2 ^ (3 - 2))) ≠ 1 := by decide
  have h14 : (QuaternionGroup.a 1 : QuaternionGroup (2 ^ (3 - 2))) ^ 4 = 1 := by decide
  set w : ↥P := e.symm (QuaternionGroup.a 1) with hw
  set v : ↥P := e.symm (QuaternionGroup.a 2) with hv
  have hww : w * w = v := by rw [hw, hv, ← map_mul, h11]
  have hvv : (v : X) * v = 1 := by
    rw [← Subgroup.coe_mul, hv, ← map_mul, h22, map_one, OneMemClass.coe_one]
  have hv1 : (v : X) ≠ 1 := by
    intro h
    apply h21
    have h1 : v = 1 := Subtype.ext h
    rw [hv] at h1
    simpa using congrArg e h1
  have hvz : (v : X) = z := (hz.unique v (hP.1 v.2) hvv).resolve_left hv1
  refine ⟨w, hP.1 w.2, ?_, ?_⟩
  · rw [← Subgroup.coe_mul, hww, hvz]
  · rw [← Subgroup.coe_pow, hw, ← map_pow, h14, map_one, OneMemClass.coe_one]

omit [Finite X] in
theorem mul_self_mem_of_index_dvd_six {N : Subgroup X} [N.Normal] (hN : N.index ∣ 6) {w : X}
    (hw : w ^ 4 = 1) : w * w ∈ N := by
  obtain ⟨k, hk⟩ := hN
  have h1 : w ^ 6 ∈ N := by
    rw [hk, pow_mul]
    exact N.pow_mem (N.pow_index_mem w) k
  have h2 : w ^ 6 = w * w := by
    calc w ^ 6 = w ^ 4 * w ^ 2 := by rw [← pow_add]
      _ = w * w := by rw [hw, one_mul, pow_two]
  rwa [h2] at h1

theorem false_of_exit (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) {Φ : Set (Subgroup X)}
    (hΦ : TypeRFam 3 Φ) (htr : ∀ L ∈ Φ, ∀ M ∈ Φ, ∃ g : X, conjSub g L = M) {K : Subgroup X}
    (hK : K ∈ Φ) {z : X} (hz : IsUniqueInvolution K z) {J : Subgroup X}
    (hJ : J ∈ omegaNbr Φ K) {t : X} (ht : IsUniqueInvolution J t)
    (hed : TightEdgeless (K.subgroupOf (K ⊔ genFittingFStar X)))
    (hidx : (genFittingFStar ↥(K ⊔ genFittingFStar X)).index ∣ 6)
    (hconj : ∀ a b : ↥(genFittingFStar ↥(K ⊔ genFittingFStar X)), orderOf a = 2 →
      orderOf b = 2 → IsConj a b) : False := by
  set Y := K ⊔ genFittingFStar X with hY
  have hKY : K ≤ Y := le_sup_left
  have hFY : genFittingFStar X ≤ Y := le_sup_right
  have hFe := fstar_sec_eq hs hnab hFY
  have : (genFittingFStar ↥Y).Normal := genFittingFStar_normal ↥Y
  obtain ⟨w, hwK, hww, hw4⟩ := exists_sq_eq_of_typeR hΦ hK hz
  have hw' : (⟨w, hKY hwK⟩ : ↥Y) ^ 4 = 1 := Subtype.ext (by simp [hw4])
  have hz'F : (⟨z, hKY hz.mem⟩ : ↥Y) ∈ genFittingFStar ↥Y := by
    have h1 := mul_self_mem_of_index_dvd_six hidx hw'
    have e1 : (⟨w, hKY hwK⟩ : ↥Y) * ⟨w, hKY hwK⟩ = ⟨z, hKY hz.mem⟩ := Subtype.ext hww
    rwa [e1] at h1
  have hzF : z ∈ genFittingFStar X := by
    rw [hFe] at hz'F
    exact Subgroup.mem_subgroupOf.mp hz'F
  obtain ⟨g, hg⟩ := exists_conj_of_trans htr hK hz hJ.1 ht
  have htF : t ∈ genFittingFStar X := hg ▸ (genFittingFStar_normal X).conj_mem z hzF g
  have ht'F : (⟨t, hFY htF⟩ : ↥Y) ∈ genFittingFStar ↥Y := by
    rw [hFe]
    exact Subgroup.mem_subgroupOf.mpr htF
  have hz2 : orderOf (⟨⟨z, hKY hz.mem⟩, hz'F⟩ : ↥(genFittingFStar ↥Y)) = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have ht2 : orderOf (⟨⟨t, hFY htF⟩, ht'F⟩ : ↥(genFittingFStar ↥Y)) = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact ht.sq) ht.ne_one
  obtain ⟨c, hc⟩ := isConj_iff.mp (hconj _ _ hz2 ht2)
  have hcX : ((c : ↥Y) : X) * z * ((c : ↥Y) : X)⁻¹ = t := by
    have h1 := congrArg (fun x : ↥(genFittingFStar ↥Y) => ((x : ↥Y) : X)) hc
    simpa using h1
  have hmem := mem_omegaNbr_sec hΦ.hyp hKY hJ (c : ↥Y).2 (eq_conjSub_of_conj hΦ hK hz hJ.1 ht hcX)
  have hed' : Disconnected.DEdgeless (CoreAssembly.conjClass (K.subgroupOf Y)) := by
    have h1 : Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore (K.subgroupOf Y))) := hed
    rwa [tightCore_sec hΦ hK hKY] at h1
  exact hed' _ (CoreAssembly.mem_conjClass_self _) _ hmem.1 (Or.inl hmem)

end Exits

section OddFree

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem orderOf_eq_two_of_mem_pair {z t a : X} (hz : z * z = 1) (ht : t * t = 1)
    (hzt : z * t = t * z) (ha : a = z ∨ a = t ∨ a = z * t) (ha1 : a ≠ 1) : orderOf a = 2 := by
  refine orderOf_eq_prime ?_ ha1
  rw [pow_two]
  rcases ha with rfl | rfl | rfl
  · exact hz
  · exact ht
  · calc z * t * (z * t) = z * (t * z) * t := by group
      _ = z * (z * t) * t := by rw [← hzt]
      _ = 1 := by rw [← mul_assoc, hz, one_mul, ht]

theorem oddCoreOf_eq_bot_of_m12 (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a)
    (hS : Nonempty (↥(genFittingFStar X) ≃* NativeSporadic.M12)) {a : X} (ha : orderOf a = 2) :
    oddCoreOf (Subgroup.centralizer ({a} : Set X)) = ⊥ := by
  have : (genFittingFStar X).Normal := genFittingFStar_normal X
  obtain ⟨ψ⟩ := hS
  have h := CFSG.Sporadic.Schreier.oddCore_centralizer_eq_bot_of_normal
    CFSG.Sporadic.Schreier.m12_inner_oddCore CFSG.Sporadic.Schreier.m12_mulAut_card
    CFSG.Sporadic.Schreier.m12_outer_oddCore (genFittingFStar X) ψ
    (centralizer_genFittingFStar_eq_bot hnab) a ha
  show (classicalInvolutionOddCore ↥(Subgroup.centralizer ({a} : Set X))).map _ = ⊥
  rw [show classicalInvolutionOddCore ↥(Subgroup.centralizer ({a} : Set X)) =
    CFSG.oddCore ↥(Subgroup.centralizer ({a} : Set X)) from rfl, h, Subgroup.map_bot]

variable {Y : Subgroup X}

theorem nonempty_fstar_equiv_sec (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) (hFY : genFittingFStar X ≤ Y) :
    Nonempty (↥(genFittingFStar X) ≃* FStarQuot ↥Y) := by
  have hFe := fstar_sec_eq hs hnab hFY
  have hsY : IsSimpleGroup ↥(genFittingFStar ↥Y) := by
    rw [hFe]
    exact isSimpleGroup_fstar_sec hs hFY
  have hnY : ∃ a b : ↥(genFittingFStar ↥Y), a * b ≠ b * a := by
    rw [hFe]
    exact nonabelian_fstar_sec hnab hFY
  obtain ⟨e3⟩ := MFMuZ2.nonempty_fstar_equiv (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnY).2
  exact ⟨((Subgroup.subgroupOfEquivOfLe hFY).symm.trans (MulEquiv.subgroupCongr hFe.symm)).trans e3⟩

theorem nonempty_fstar_equiv_of_quot (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) (hFY : genFittingFStar X ≤ Y)
    {Q : Type} [Group Q] [IsSimpleGroup Q] (e : ↥Y ⧸ Subgroup.center ↥Y ≃* Q) :
    Nonempty (↥(genFittingFStar X) ≃* Q) := by
  have hZ := center_sec_eq_bot hs hnab hFY
  let e0 : ↥Y ≃* ↥Y ⧸ Subgroup.center ↥Y :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have : IsSimpleGroup ↥Y := (e0.trans e).isSimpleGroup
  have : ((genFittingFStar X).subgroupOf Y).Normal := (genFittingFStar_normal X).subgroupOf Y
  have htop : (genFittingFStar X).subgroupOf Y = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((genFittingFStar X).subgroupOf Y) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := nonabelian_fstar_sec hnab hFY
      have h1 : ∀ x : ↥((genFittingFStar X).subgroupOf Y), x = 1 := fun x =>
        Subtype.ext (((Subgroup.eq_bot_iff_forall _).mp h) x.1 x.2)
      exact hab (by rw [h1 a, h1 b])
    · exact h
  exact ⟨(Subgroup.subgroupOfEquivOfLe hFY).symm.trans
    ((MulEquiv.subgroupCongr htop).trans (Subgroup.topEquiv.trans (e0.trans e)))⟩

omit [Finite X] in
theorem layer_eq_fstar (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) :
    CFSG.IsComponent (genFittingFStar X) ∧ layer X = genFittingFStar X := by
  have hFc : CFSG.IsComponent (genFittingFStar X) :=
    ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1,
      (genFittingFStar_normal X).isSubnormal⟩
  refine ⟨hFc, le_antisymm ?_ (CFSG.LocalCores.component_le_layer hFc)⟩
  rw [← genFittingLayer_eq_layer]
  exact le_sup_right

theorem alphaOf_eq_bot_of_autOddFreeInner (hO : classicalInvolutionOddCore X = ⊥)
    (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a)
    (hA : Q3NM.AutOddFreeInner ↥(genFittingFStar X)) {z t : X} (hzF : z ∈ genFittingFStar X)
    (htF : t ∈ genFittingFStar X) (hz : z * z = 1) (ht : t * t = 1) (hzt : z * t = t * z)
    (hz1 : z ≠ 1) : alphaOf (Subgroup.closure ({z, t} : Set X)) = ⊥ := by
  obtain ⟨hFc, hlay⟩ := layer_eq_fstar hs hnab
  refine alphaOf_pair_eq_bot hz ht hzt hz1 fun a ha ha1 => ?_
  have haF : a ∈ genFittingFStar X := by
    rcases ha with rfl | rfl | rfl
    · exact hzF
    · exact htF
    · exact (genFittingFStar X).mul_mem hzF htF
  exact oddCoreImg_eq_bot_of_autOddFreeInner hO hFc hlay haF
    (orderOf_eq_two_of_mem_pair hz ht hzt ha ha1) hA

theorem lie_sec (hO : classicalInvolutionOddCore X = ⊥) (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) {K : Subgroup X} {z : X}
    (hz : IsUniqueInvolution K z)
    (hlie : SecIdLie3 (K.subgroupOf (K ⊔ genFittingFStar X))
      ⟨z, (le_sup_left : K ≤ K ⊔ genFittingFStar X) hz.mem⟩) :
    Q3NM.AutOddFreeInner ↥(genFittingFStar X) ∧ z ∈ genFittingFStar X := by
  set Y := K ⊔ genFittingFStar X with hY
  have hFY : genFittingFStar X ≤ Y := le_sup_right
  obtain ⟨L', -, hcl, -, hsys⟩ := hlie
  have hO' := oddCore_sec_eq_bot hO hs hnab hFY
  have hZ := center_sec_eq_bot hs hnab hFY
  set z' : ↥Y := ⟨z, (le_sup_left : K ≤ K ⊔ genFittingFStar X) hz.mem⟩ with hz'
  have hz'1 : z' ≠ 1 := fun h => hz.ne_one (congrArg Subtype.val h)
  have hnc : ∀ M ∈ CoreAssembly.conjClass L', ¬ M ≤ Subgroup.center ↥Y := by
    rintro M ⟨g, rfl⟩ hle
    rw [hZ, le_bot_iff] at hle
    have hle' : conjSub g L' = ⊥ := hle
    have h1 : g * z' * g⁻¹ ∈ conjSub g L' := conj_mem_conjSub hcl.mem
    rw [hle', Subgroup.mem_bot] at h1
    apply hz'1
    have h2 := congrArg (fun x => g⁻¹ * x * g) h1
    simpa [mul_assoc] using h2
  set F' : Subgroup ↥Y := (genFittingFStar X).subgroupOf Y with hF'
  have hF'n : F'.Normal := (genFittingFStar_normal X).subgroupOf Y
  have := isSimpleGroup_fstar_sec hs hFY
  have hnF' := nonabelian_fstar_sec hnab hFY
  have hQ : CFSG.IsComponent F' :=
    ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnF').1, hF'n.isSubnormal⟩
  have hA := Q3CH.autOddFreeInner_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFY)
    (autOddFreeInner_of_lieSystemMod3 hO' hsys hnc hQ)
  refine ⟨hA, ?_⟩
  obtain ⟨ι, _, ⟨D⟩⟩ := lieSystem3_of_lieSystemMod3_corefree hO' hsys
  have hrange : (MonoidHom.id ↥Y).range.Normal := by
    rw [MonoidHom.range_eq_top.mpr fun y => ⟨y, rfl⟩]
    infer_instance
  rcases Q3CH.eq_range_or_commutes ModelFacts.modelClauseZero m11Facts D (MonoidHom.id ↥Y)
      (fun _ _ h => h) hnc hrange ((CFSG.isComponent_iff_open F').mp hQ) with ⟨i₀, hi₀⟩ | hcomm
  · obtain ⟨i, R₀, -, hL'⟩ := D.fundamental L' (CoreAssembly.mem_conjClass_self L')
    have hzL := hcl.mem
    rw [hL'] at hzL
    obtain ⟨r, -, hr⟩ := hzL
    by_cases hi : i = i₀
    · subst hi
      have hz'F : z' ∈ F' := by
        rw [hi₀]
        exact ⟨r, hr⟩
      exact Subgroup.mem_subgroupOf.mp hz'F
    · exfalso
      have hzc : z' ∈ Subgroup.centralizer (F' : Set ↥Y) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [hi₀] at hy
        obtain ⟨g, rfl⟩ := hy
        rw [← hr]
        exact (D.commute i i₀ hi r g).symm
      rw [centralizer_fstar_sec_eq_bot hs hnab hFY, Subgroup.mem_bot] at hzc
      exact hz'1 hzc
  · exfalso
    obtain ⟨a, b, hab⟩ := hnF'
    exact hab (Subtype.ext (hcomm a a.2 b ⟨b, rfl⟩))

end OddFree

end Outer

theorem thm5OuterR_three_of {n : ℕ} (hA : CIT3Below n) (hP : TightBelowRPlus 3 n) :
    ∀ (X : Type) [Group X] [Finite X], Nat.card X = n → ∀ Φ : Set (Subgroup X), TypeRFam 3 Φ →
      classicalInvolutionOddCore X = ⊥ → IsSimpleGroup ↥(genFittingFStar X) →
      (∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) →
      (∀ L ∈ Φ, ∀ M ∈ Φ, ∃ g : X, conjSub g L = M) → omegaGen Φ ≠ ⊤ →
      ∀ K ∈ Φ, ∀ J ∈ omegaNbr Φ K, ∀ z t : X, IsUniqueInvolution K z → IsUniqueInvolution J t →
        alphaOf (Subgroup.closure ({z, t} : Set X)) = ⊥ := by
  intro X _ _ hXn Φ hΦ hO hs hnab htr hgen K hK J hJ z t hz ht
  set Y := K ⊔ genFittingFStar X with hY
  have hFY : genFittingFStar X ≤ Y := le_sup_right
  obtain ⟨-, hzt⟩ := Outer.ne_and_commute_of_mem_omegaNbr hΦ hK hz hJ ht
  obtain ⟨S', hd', hc'⟩ := Outer.tightCls_sec hO hs hnab hΦ hK hz
  have hYlt : Nat.card ↥Y < n := hXn ▸ Outer.natCard_sec_lt hs hnab hΦ hK hgen
  have hz'1 : (⟨z, (le_sup_left : K ≤ Y) hz.mem⟩ : ↥Y) ≠ 1 :=
    fun h => hz.ne_one (congrArg Subtype.val h)
  obtain ⟨g, hg⟩ := Outer.exists_conj_of_trans htr hK hz hJ.1 ht
  have htF : z ∈ genFittingFStar X → t ∈ genFittingFStar X := fun hzF =>
    hg ▸ (genFittingFStar_normal X).conj_mem z hzF g
  have hsY : IsSimpleGroup ↥(genFittingFStar ↥Y) := by
    rw [Outer.fstar_sec_eq hs hnab hFY]
    exact Outer.isSimpleGroup_fstar_sec hs hFY
  have hnY : ∃ a b : ↥(genFittingFStar ↥Y), a * b ≠ b * a := by
    rw [Outer.fstar_sec_eq hs hnab hFY]
    exact Outer.nonabelian_fstar_sec hnab hFY
  have hm12 : Nonempty (↥(genFittingFStar X) ≃* NativeSporadic.M12) →
      alphaOf (Subgroup.closure ({z, t} : Set X)) = ⊥ := fun hS =>
    Outer.alphaOf_pair_eq_bot hz.sq ht.sq hzt hz.ne_one fun a ha ha1 =>
      Outer.oddCoreOf_eq_bot_of_m12 hs hnab hS
        (Outer.orderOf_eq_two_of_mem_pair hz.sq ht.sq hzt ha ha1)
  rcases secIdentDatum3_of hP hA ↥Y hYlt _ S' _ hd' hc' with
    hE2 | ⟨hed, -, hx⟩ | ⟨hed, ⟨e12⟩⟩ | ⟨hZ, -⟩ | hLie
  · exact absurd hE2 (Outer.not_tightInO2_sec hs hnab hFY hz'1)
  · rcases hx with hx | htw
    · rcases hx with ⟨p, f, hp, hp2, ⟨-, hl, hi⟩ | ⟨hl | hl, hi⟩⟩ | ⟨hm, -⟩
      · have hi6 : (genFittingFStar ↥Y).index ∣ 6 := by
          have h0 : (genFittingFStar ↥Y).index ≠ 0 := Subgroup.index_ne_zero_of_finite
          rcases (show (genFittingFStar ↥Y).index = 1 ∨ (genFittingFStar ↥Y).index = 2 by
            omega) with h1 | h1 <;> rw [h1] <;> norm_num
        exact (Outer.false_of_exit hs hnab hΦ htr hK hz hJ ht hed hi6
          (Outer.invConj_fstar_psl2 hsY hp hp2 hl)).elim
      · exact (Outer.false_of_exit hs hnab hΦ htr hK hz hJ ht hed hi
          (Outer.invConj_fstar_psl3 hp hp2 hl)).elim
      · exact (Outer.false_of_exit hs hnab hΦ htr hK hz hJ ht hed hi
          (Outer.invConj_fstar_psu3 hsY hnY hp hp2 hl)).elim
      · obtain ⟨e⟩ := Outer.nonempty_fstar_equiv_sec hs hnab hFY
        exact hm12 ⟨e.trans hm.some⟩
    · exact absurd htw (Outer.not_tightTwisted_sec hs hnab hFY _)
  · have : IsSimpleGroup ↥NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    exact hm12 (Outer.nonempty_fstar_equiv_of_quot hs hnab hFY e12)
  · exact absurd (Outer.center_sec_eq_bot hs hnab hFY) hZ
  · obtain ⟨hAI, hzF⟩ := Outer.lie_sec hO hs hnab hz hLie
    exact Outer.alphaOf_eq_bot_of_autOddFreeInner hO hs hnab hAI hzF (htF hzF) hz.sq ht.sq hzt
      hz.ne_one

end CFSG.ClassicalInvolution.Q3.TL4
