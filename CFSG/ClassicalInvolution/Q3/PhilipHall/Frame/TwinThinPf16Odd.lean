module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf16Bal
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf7Frat
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf7Basic
public import CFSG.ClassicalInvolution.Q3.Q3T6DConj
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2AEM
public import CFSG.ClassicalInvolution.Q3.TL3T26
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

section Four

variable {G : Type} [Group G]

theorem mem_closure_pair_of_comm {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) {x : G} (hx : x ∈ Subgroup.closure ({a, b} : Set G)) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have h1 : ∀ y, a * (a * y) = y := fun y => by rw [← mul_assoc, ha, one_mul]
  have h3 : ∀ y, b * (a * y) = a * (b * y) := fun y => by rw [← mul_assoc, ← hab, mul_assoc]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp only [mul_assoc, h1, h3, ← hab, ha, hb, mul_one, one_mul, true_or, or_true]
  | inv x _ hx =>
    rcases hx with rfl | rfl | rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr (Or.inl hainv)
    · exact Or.inr (Or.inr (Or.inl hbinv))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [mul_inv_rev, hainv, hbinv]
      exact hab.symm

theorem isElemAbelian_closure_pair [Finite G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    IsElemAbelian 2 (Subgroup.closure ({a, b} : Set G)) ∧
      2 ^ 2 ≤ Nat.card ↥(Subgroup.closure ({a, b} : Set G)) := by
  classical
  set A := Subgroup.closure ({a, b} : Set G) with hA
  have hc : Commute a b := hab
  have key : ∀ x : G, (x = 1 ∨ x = a ∨ x = b ∨ x = a * b) → Commute x a ∧ Commute x b := by
    intro x hx
    rcases hx with h | h | h | h <;> rw [h]
    · exact ⟨Commute.one_left a, Commute.one_left b⟩
    · exact ⟨Commute.refl a, hc⟩
    · exact ⟨hc.symm, Commute.refl b⟩
    · exact ⟨(Commute.refl a).mul_left hc.symm, hc.mul_left (Commute.refl b)⟩
  have hcomm : ∀ x y : G, (x = 1 ∨ x = a ∨ x = b ∨ x = a * b) →
      (y = 1 ∨ y = a ∨ y = b ∨ y = a * b) → x * y = y * x := by
    intro x y hx hy
    obtain ⟨hxa, hxb⟩ := key x hx
    rcases hy with rfl | rfl | rfl | rfl
    · exact (Commute.one_right x).eq
    · exact hxa.eq
    · exact hxb.eq
    · exact (hxa.mul_right hxb).eq
  have hab1 : a * b ≠ 1 := fun h =>
    hne (by rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right hb])
  have haab : a ≠ a * b := fun h => hb1 (by
    calc b = a⁻¹ * (a * b) := by group
      _ = a⁻¹ * a := by rw [← h]
      _ = 1 := by group)
  have hbab : b ≠ a * b := fun h => ha1 (by
    calc a = a * b * b⁻¹ := by group
      _ = b * b⁻¹ := by rw [← h]
      _ = 1 := by group)
  refine ⟨⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · exact hcomm _ _ (mem_closure_pair_of_comm ha hb hab x.2) (mem_closure_pair_of_comm ha hb hab y.2)
  · rw [sq]
    rcases mem_closure_pair_of_comm ha hb hab hx with rfl | rfl | rfl | rfl
    · exact one_mul 1
    · exact ha
    · exact hb
    · calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha, hb, one_mul]
  · have hsub : (({1, a, b, a * b} : Finset G) : Set G) ⊆ (A : Set G) := by
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact A.one_mem
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact A.mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    have hcard : ({1, a, b, a * b} : Finset G).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hbab]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hne, haab⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨ha1.symm, hb1.symm, hab1.symm⟩
    calc 2 ^ 2 = ({1, a, b, a * b} : Finset G).card := by rw [hcard]; norm_num
      _ = (({1, a, b, a * b} : Finset G) : Set G).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ (A : Set G).ncard := Set.ncard_le_ncard hsub
      _ = Nat.card ↥A := by rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]

theorem exists_finset_pair_inter_two {m : ℕ} (hm : 6 ≤ m) :
    ∃ α β : Finset (Fin m), α.card = 4 ∧ β.card = 4 ∧ (α ∩ β).card = 2 := by
  let f : Fin 6 ↪ Fin m := ⟨fun i => ⟨i.val, by omega⟩, fun i j hij => Fin.ext (by
    have := congrArg Fin.val hij
    simpa using this)⟩
  refine ⟨({0, 1, 2, 3} : Finset (Fin 6)).map f, ({0, 1, 4, 5} : Finset (Fin 6)).map f, ?_, ?_, ?_⟩
  · rw [Finset.card_map]
    decide
  · rw [Finset.card_map]
    decide
  · rw [← Finset.map_inter, Finset.card_map]
    decide

end Four

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem le_of_mem_fam' {L : Subgroup G} (hL : L ∈ fam K (conjSub g (piGen π))) :
    L ≤ conjSub g (piGen π) := by
  obtain ⟨x, rfl⟩ := hL
  have := conjSub_mono (n := (x : G)) S.hKX
  rwa [conjSub_eq_self_of_mem x.2] at this

theorem conjSub_mem_fam' {x : G} (hx : x ∈ conjSub g (piGen π)) {L : Subgroup G}
    (hL : L ∈ fam K (conjSub g (piGen π))) : conjSub x L ∈ fam K (conjSub g (piGen π)) := by
  obtain ⟨y, rfl⟩ := hL
  exact ⟨⟨x * y, (conjSub g (piGen π)).mul_mem hx y.2⟩, conjSub_mul _ _ _⟩

theorem mem_of_mem_pi {J : Subgroup G} (hJ : J ∈ π) : J ∈ CoreAssembly.conjClass K₀ :=
  (adj_of_mem_isMaxOrb S.hos.graph S.hπ hJ).2.1

theorem conj_inv_mem_pi {L : Subgroup G} (hL : L ∈ fam K (conjSub g (piGen π))) :
    conjSub g⁻¹ L ∈ π := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := hL
  obtain ⟨M, hM, hMK⟩ := S.hos.mem_conj_image_of_mem S.hπ S.hg
  have hx' : g⁻¹ * x * g ∈ piGen π := by
    rw [mem_conjSub_iff] at hx
    simpa using hx
  have heq : conjSub g⁻¹ (conjSub x K) = conjSub (g⁻¹ * x * g) M := by
    rw [← hMK, ← conjSub_mul, ← conjSub_mul]
  rw [heq]
  exact stable_of_maxOrb S.hos.graph S.hπ _ hx' M hM

theorem zpowers_mem_USet {L : Subgroup G} (hL : L ∈ CoreAssembly.conjClass K₀) {x : G}
    (hxL : x ∈ L) (hx2 : x * x ≠ 1) : Subgroup.zpowers x ∈ USet (CoreAssembly.conjClass K₀) := by
  have h8 := S.card8 L hL
  have hxord : orderOf x = 4 := by
    have hdvd : orderOf x ∣ 8 := by
      rw [← h8]
      exact Subgroup.orderOf_dvd_natCard L hxL
    have hx1 : x ≠ 1 := fun h => hx2 (by rw [h, one_mul])
    have hne2 : orderOf x ≠ 2 := fun h => hx2 (by rw [← pow_two, ← h, pow_orderOf_eq_one])
    have hne1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
    have hne8 : orderOf x ≠ 8 := by
      intro h
      obtain ⟨-, P, hPN, hPnc⟩ := S.hs.hyp.omega1 L hL
      have hzN : Subgroup.zpowers x = L := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxL) ?_
        rw [Nat.card_zpowers, h, h8]
      apply hPnc
      refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      have ha : (a : G) ∈ Subgroup.zpowers x := hzN ▸ hPN.1 a.2
      have hb : (b : G) ∈ Subgroup.zpowers x := hzN ▸ hPN.1 b.2
      obtain ⟨i, hi⟩ := ha
      obtain ⟨j, hj⟩ := hb
      show (a : G) * b = b * a
      rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
    have : orderOf x ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hdiv] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  have hUcard : Nat.card ↥(Subgroup.zpowers x) = 4 := by rw [Nat.card_zpowers, hxord]
  have hLR : L ∈ RSet (CoreAssembly.conjClass K₀) := mem_RSet_of_isPGroup hL (S.hs.two L hL)
  refine ⟨L, hLR, Subgroup.zpowers_le.mpr hxL, inferInstance, ?_⟩
  have h1 := Subgroup.relIndex_mul_card (Subgroup.zpowers x) L
  rw [inf_eq_left.mpr (Subgroup.zpowers_le.mpr hxL), hUcard, h8] at h1
  omega

theorem exists_star_edge {m : ℕ} (hm : 6 ≤ m) (J : AEIdent (fam K (conjSub g (piGen π))) m) :
    ∃ L₁ ∈ fam K (conjSub g (piGen π)), ∃ L₂ ∈ fam K (conjSub g (piGen π)),
      L₂ ∈ omegaStarNbr (CoreAssembly.conjClass K₀) L₁ ∧
        L₂ ∉ omegaNbr (CoreAssembly.conjClass K₀) L₁ := by
  have hm5 : 5 ≤ m := by omega
  obtain ⟨α, β, hα, hβ, h2⟩ := exists_finset_pair_inter_two hm
  obtain ⟨L₁, hL₁, hlab₁⟩ := J.label_surj α hα true
  obtain ⟨L₂, hL₂, hlab₂⟩ := J.label_surj β hβ true
  have hαβ : α ≠ β := by
    rintro rfl
    rw [Finset.inter_self, hα] at h2
    norm_num at h2
  have hL₁Ω := S.fam_mem hL₁
  have hL₂Ω := S.fam_mem hL₂
  obtain ⟨z₁, hz₁⟩ := (S.hs.hyp.omega1 L₁ hL₁Ω).1
  have hnc : ∃ y ∈ L₂, z₁ * y ≠ y * z₁ := by
    by_contra hall
    push Not at hall
    have hne : (α ∩ β).Nonempty := Finset.card_pos.mp (by rw [h2]; norm_num)
    refine Finset.not_disjoint_iff_nonempty_inter.mpr hne
      (AE.disjoint_of_zBar_comm (h := hα) (h' := hβ) hαβ (c := true) fun y hy => ?_)
    rw [← hlab₂] at hy
    obtain ⟨l, hl, rfl⟩ := J.exists_of_mem_map hL₂ hy
    rw [← J.map_eq_zBar hm5 hL₁ (S.card8 L₁ hL₁Ω) hlab₁ hz₁, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hall l hl)
  obtain ⟨y, hyL₂, hyz⟩ := hnc
  have hne : L₂ ≠ L₁ := by
    rintro rfl
    exact hyz (hz₁.commute_of_mem hyL₂)
  refine ⟨L₁, hL₁, L₂, hL₂, ?_, fun h =>
    hyz (comm_of_mem_omegaNbr S.hs.hyp S.hs.two hL₁Ω h z₁ hz₁.mem y hyL₂)⟩
  obtain ⟨v, hv, hvv, hvn⟩ := TL4.SecIdE2.exists_normalizing_memBar hm5 hα hβ h2
  rw [← hlab₂] at hv
  obtain ⟨x, hxL₂, rfl⟩ := J.exists_of_mem_map hL₂ hv
  have hxX : x ∈ conjSub g (piGen π) := S.le_of_mem_fam' hL₂ hxL₂
  have hconj : conjSub x L₁ ∈ fam K (conjSub g (piGen π)) := S.conjSub_mem_fam' hxX hL₁
  have heq : conjSub x L₁ = L₁ := by
    refine S.eq_of_map_le hm5 J hconj hL₁ ?_
    rintro _ ⟨⟨w, hwP⟩, hw, rfl⟩
    have hw' : x⁻¹ * w * x ∈ L₁ := mem_conjSub_iff.mp (Subgroup.mem_subgroupOf.mp hw)
    rw [hlab₁]
    have hl : J.φ ⟨x⁻¹ * w * x, le_pSpan hL₁ hw'⟩ ∈ AE.memBar α hα true := by
      rw [← hlab₁]
      exact J.mem_map hL₁ hw'
    have hkey : J.φ ⟨w, hwP⟩ = J.φ ⟨x, le_pSpan hL₂ hxL₂⟩ * J.φ ⟨x⁻¹ * w * x, le_pSpan hL₁ hw'⟩ *
        (J.φ ⟨x, le_pSpan hL₂ hxL₂⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show w = x * (x⁻¹ * w * x) * x⁻¹
      group
    rw [hkey]
    exact hvn _ hl
  have hx2 : x * x ≠ 1 := fun h1 => hvv (by
    rw [← map_mul, ← map_one J.φ]
    exact congrArg J.φ (Subtype.ext h1))
  exact ⟨hL₂Ω, hne, Subgroup.zpowers x, S.zpowers_mem_USet hL₂Ω hxL₂ hx2,
    Subgroup.zpowers_le.mpr hxL₂,
    Subgroup.zpowers_le.mpr (mem_normalizer_iff_conjSub_eq.mpr heq)⟩

theorem inf_centralizer_eq_bot_of_mem_pi
    (hodd : ∀ L ∈ CoreAssembly.conjClass K₀, ∀ t : G, IsUniqueInvolution L t →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set G)) = ⊥)
    {u : G} (huO : u ∈ pCoreOf 2 (conjSub g (piGen π))) (huX : ∀ x ∈ piGen π, x * u = u * x)
    {O : Subgroup G} (hOodd : Odd (Nat.card ↥O)) (hOu : O ≤ Subgroup.centralizer ({u} : Set G))
    (hOn : ∀ c ∈ Subgroup.centralizer ({u} : Set G), ∀ o ∈ O, c * o * c⁻¹ ∈ O)
    {J' : Subgroup G} (hJ' : J' ∈ π) {t : G} (ht : IsUniqueInvolution J' t) :
    O ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ := by
  obtain ⟨x, hx, hxJ⟩ := S.trans_pi _ S.hg J' hJ'
  have ht' : t = x * (g * z * g⁻¹) * x⁻¹ := by
    have h1 := (S.hz.conj g).conj x
    rw [hxJ] at h1
    exact ht.eq h1
  have hN := (isNormalTwoIn_pCore S.le_cent S.normal_cent).conj x
  rw [← ht'] at hN
  have hu : u ∈ conjSub x (pCoreOf 2 (conjSub g (piGen π))) := by
    have h1 : x * u * x⁻¹ ∈ conjSub x (pCoreOf 2 (conjSub g (piGen π))) := conj_mem_conjSub huO
    rwa [huX x hx, mul_inv_cancel_right] at h1
  exact inf_centralizer_eq_bot_of_balance (hodd J' (S.mem_of_mem_pi hJ') t ht) hN.2.1 hN.1 hN.2.2
    hu hOodd hOu hOn

theorem oddCore_centLayer_eq_bot {m : ℕ} (hm : 6 ≤ m)
    (J : AEIdent (fam K (conjSub g (piGen π))) m)
    (hodd : ∀ L ∈ CoreAssembly.conjClass K₀, ∀ t : G, IsUniqueInvolution L t →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set G)) = ⊥)
    {u : G} (huO : u ∈ pCoreOf 2 (conjSub g (piGen π))) (huX : ∀ x ∈ piGen π, x * u = u * x) :
    classicalInvolutionOddCore ↥(centLayer (CoreAssembly.conjClass K₀) u) = ⊥ := by
  classical
  have hΩ := S.hs.hyp
  have hOodd : Odd (Nat.card ↥(oddCoreOf (centLayer (CoreAssembly.conjClass K₀) u))) := by
    have h2 : Nat.card ↥(oddCoreOf (centLayer (CoreAssembly.conjClass K₀) u)) =
        Nat.card (classicalInvolutionOddCore ↥(centLayer (CoreAssembly.conjClass K₀) u)) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _
        (centLayer (CoreAssembly.conjClass K₀) u).subtype_injective).symm.toEquiv
    rw [h2]
    exact CFSG.ComponentClassification.OddCore.odd_card _
  have hYu : centLayer (CoreAssembly.conjClass K₀) u ≤ Subgroup.centralizer ({u} : Set G) :=
    centLayer_le fun L hL => hL.2
  have hOu : oddCoreOf (centLayer (CoreAssembly.conjClass K₀) u) ≤
      Subgroup.centralizer ({u} : Set G) := (oddCoreOf_le_self _).trans hYu
  have hYc : ∀ c ∈ Subgroup.centralizer ({u} : Set G),
      conjSub c (centLayer (CoreAssembly.conjClass K₀) u) = centLayer (CoreAssembly.conjClass K₀) u := by
    intro c hc
    rw [conjSub_centLayer hΩ.conjInvariant c u]
    congr 1
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    rw [hc, mul_inv_cancel_right]
  have hOn : ∀ c ∈ Subgroup.centralizer ({u} : Set G),
      ∀ o ∈ oddCoreOf (centLayer (CoreAssembly.conjClass K₀) u),
        c * o * c⁻¹ ∈ oddCoreOf (centLayer (CoreAssembly.conjClass K₀) u) := by
    intro c hc o ho
    have h1 : c * o * c⁻¹ ∈ conjSub c (oddCoreOf (centLayer (CoreAssembly.conjClass K₀) u)) :=
      conj_mem_conjSub ho
    rwa [← AscE184Sect.oddCoreOf_conjSub, hYc c hc] at h1
  have hbal := fun {J' : Subgroup G} (hJ' : J' ∈ π) {t : G} (ht : IsUniqueInvolution J' t) =>
    S.inf_centralizer_eq_bot_of_mem_pi hodd huO huX hOodd hOu hOn hJ' ht
  obtain ⟨L₁, hL₁, L₂, hL₂, hstar, hnot⟩ := S.exists_star_edge hm J
  have hL₁Ω := S.fam_mem hL₁
  have hL₂Ω := S.fam_mem hL₂
  obtain ⟨z₁, hz₁⟩ := (hΩ.omega1 L₁ hL₁Ω).1
  obtain ⟨z₂, hz₂⟩ := (hΩ.omega1 L₂ hL₂Ω).1
  obtain ⟨r, hrL₁, -, hrz₂⟩ := Q3T6D.exists_mem_conj_eq_mul hΩ hL₁Ω hL₂Ω hz₁ hz₂ hstar hnot
  have hz₁₂ : z₁ * z₂ = z₂ * z₁ := Q3T6D.commute_of_mem_omegaStarNbr hΩ hstar hz₁ hz₂
  have hL₃ : conjSub r L₂ ∈ fam K (conjSub g (piGen π)) :=
    S.conjSub_mem_fam' (S.le_of_mem_fam' hL₁ hrL₁) hL₂
  have hz₃ : IsUniqueInvolution (conjSub r L₂) (z₁ * z₂) := by
    have := hz₂.conj r
    rwa [hrz₂] at this
  have hz12 : z₁ ≠ z₂ := by
    intro h
    apply hz₂.ne_one
    have h1 : r * z₂ * r⁻¹ = 1 := by rw [hrz₂, h, hz₂.sq]
    calc z₂ = r⁻¹ * (r * z₂ * r⁻¹) * r := by group
      _ = 1 := by rw [h1]; group
  have hc₁ : IsUniqueInvolution (conjSub g⁻¹ L₁) (g⁻¹ * z₁ * g) := by
    have := hz₁.conj g⁻¹
    rwa [inv_inv] at this
  have hc₂ : IsUniqueInvolution (conjSub g⁻¹ L₂) (g⁻¹ * z₂ * g) := by
    have := hz₂.conj g⁻¹
    rwa [inv_inv] at this
  have hc₃ : IsUniqueInvolution (conjSub g⁻¹ (conjSub r L₂)) (g⁻¹ * z₁ * g * (g⁻¹ * z₂ * g)) := by
    have := hz₃.conj g⁻¹
    rw [inv_inv] at this
    convert this using 1
    group
  set a₁ := g⁻¹ * z₁ * g with ha₁
  set a₂ := g⁻¹ * z₂ * g with ha₂
  have hcomm : a₁ * a₂ = a₂ * a₁ := by
    rw [ha₁, ha₂]
    calc g⁻¹ * z₁ * g * (g⁻¹ * z₂ * g) = g⁻¹ * (z₁ * z₂) * g := by group
      _ = g⁻¹ * (z₂ * z₁) * g := by rw [hz₁₂]
      _ = g⁻¹ * z₂ * g * (g⁻¹ * z₁ * g) := by group
  have hne : a₁ ≠ a₂ := by
    intro h
    apply hz12
    calc z₁ = g * a₁ * g⁻¹ := by rw [ha₁]; group
      _ = g * a₂ * g⁻¹ := by rw [h]
      _ = z₂ := by rw [ha₂]; group
  obtain ⟨hA, hrank⟩ := isElemAbelian_closure_pair hc₁.sq hc₂.sq hcomm hc₁.ne_one hc₂.ne_one hne
  have hcu : Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.normalizer (oddCoreOf (centLayer (CoreAssembly.conjClass K₀) u) : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro o
    refine ⟨fun ho => hOn c hc o ho, fun ho => ?_⟩
    have := hOn c⁻¹ (Subgroup.inv_mem _ hc) _ ho
    simpa [mul_assoc] using this
  have hmemu : ∀ {J' : Subgroup G}, J' ∈ π → ∀ {t : G}, IsUniqueInvolution J' t →
      t ∈ Subgroup.centralizer ({u} : Set G) := by
    intro J' hJ' t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact huX t (le_piGen hJ' ht.mem)
  have hAN : Subgroup.closure ({a₁, a₂} : Set G) ≤
      Subgroup.normalizer (oddCoreOf (centLayer (CoreAssembly.conjClass K₀) u) : Set G) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hcu (hmemu (S.conj_inv_mem_pi hL₁) hc₁)
    · exact hcu (hmemu (S.conj_inv_mem_pi hL₂) hc₂)
  have hcop : Nat.Coprime 2 (Nat.card ↥(oddCoreOf (centLayer (CoreAssembly.conjClass K₀) u))) :=
    Nat.coprime_two_left.mpr hOodd
  have hgen := SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_two hA hrank
    hAN hcop
  have hbot : oddCoreOf (centLayer (CoreAssembly.conjClass K₀) u) = ⊥ := by
    rw [← hgen, eq_bot_iff]
    refine iSup_le fun a => iSup_le fun haA => iSup_le fun ha1 => ?_
    rcases mem_closure_pair_of_comm hc₁.sq hc₂.sq hcomm haA with h | h | h | h
    · exact absurd h ha1
    · rw [h]; exact (hbal (S.conj_inv_mem_pi hL₁) hc₁).le
    · rw [h]; exact (hbal (S.conj_inv_mem_pi hL₂) hc₂).le
    · rw [h]; exact (hbal (S.conj_inv_mem_pi hL₃) hc₃).le
  exact (Subgroup.map_eq_bot_iff_of_injective _
    (centLayer (CoreAssembly.conjClass K₀) u).subtype_injective).mp hbot

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
