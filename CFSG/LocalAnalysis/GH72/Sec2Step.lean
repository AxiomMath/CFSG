module

public import CFSG.LocalAnalysis.GH72.Sec2
import CFSG.GroupTheory.ABGLocalTools.OddInvolution
import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorNontrivial
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.PLengthLemmas

public section

namespace CFSG.GH72

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)
open scoped Pointwise

universe u

section Generation

variable {A₀ G : Type*} [Group A₀] [Group G] {X₀ Y₀ : Subgroup A₀}
  {Kxy : A₀ → A₀ → Subgroup G}

theorem IsKxyGen.le_xySupOf_of_le {F S : Subgroup G} (hS : IsKxyGen X₀ Y₀ Kxy S) (hSF : S ≤ F) :
    S ≤ xySupOf X₀ Y₀ fun x y => F ⊓ Kxy x y :=
  hS.trans (xySupOf_mono (f := fun x y => S ⊓ Kxy x y) (g := fun x y => F ⊓ Kxy x y)
    fun _ _ _ _ _ _ => inf_le_inf_right _ hSF)

theorem isKxyGen_of_le_sup {F S T : Subgroup G} (hFST : F ≤ S ⊔ T) (hSF : S ≤ F) (hTF : T ≤ F)
    (hS : IsKxyGen X₀ Y₀ Kxy S) (hT : IsKxyGen X₀ Y₀ Kxy T) : IsKxyGen X₀ Y₀ Kxy F :=
  hFST.trans (sup_le (hS.le_xySupOf_of_le hSF) (hT.le_xySupOf_of_le hTF))

theorem isKxyGen_of_le_iSup {ι : Sort*} {F : Subgroup G} {S : ι → Subgroup G}
    (hFS : F ≤ ⨆ i, S i) (hSF : ∀ i, S i ≤ F) (hS : ∀ i, IsKxyGen X₀ Y₀ Kxy (S i)) :
    IsKxyGen X₀ Y₀ Kxy F :=
  hFS.trans (iSup_le fun i => (hS i).le_xySupOf_of_le (hSF i))

theorem isKxyGen_of_le_Kxy {S : Subgroup G} {x y : A₀} (hx : x ∈ X₀) (hx1 : x ≠ 1)
    (hy : y ∈ Y₀) (hy1 : y ≠ 1) (hS : S ≤ Kxy x y) : IsKxyGen X₀ Y₀ Kxy S :=
  (le_inf le_rfl hS).trans (le_xySupOf (f := fun x y => S ⊓ Kxy x y) hx hx1 hy hy1)

theorem xySupOf_swap (f : A₀ → A₀ → Subgroup G) :
    xySupOf Y₀ X₀ (fun y x => f x y) = xySupOf X₀ Y₀ f := by
  apply le_antisymm
  · exact xySupOf_le (f := fun y x => f x y) fun y hy hy1 x hx hx1 =>
      le_xySupOf (f := f) hx hx1 hy hy1
  · exact xySupOf_le (f := f) fun x hx hx1 y hy hy1 =>
      le_xySupOf (f := fun y x => f x y) hy hy1 hx hx1

theorem isKxyGen_swap_iff {F : Subgroup G} :
    IsKxyGen Y₀ X₀ (fun y x => Kxy x y) F ↔ IsKxyGen X₀ Y₀ Kxy F := by
  unfold IsKxyGen
  rw [xySupOf_swap (fun x y => F ⊓ Kxy x y)]

theorem xySupOf_eq_iSup (f : A₀ → A₀ → Subgroup G) :
    xySupOf X₀ Y₀ f =
      ⨆ i : {p : A₀ × A₀ // p.1 ∈ X₀ ∧ p.1 ≠ 1 ∧ p.2 ∈ Y₀ ∧ p.2 ≠ 1}, f i.1.1 i.1.2 := by
  apply le_antisymm
  · exact xySupOf_le (f := f) fun x hx hx1 y hy hy1 =>
      le_iSup (fun i : {p : A₀ × A₀ // p.1 ∈ X₀ ∧ p.1 ≠ 1 ∧ p.2 ∈ Y₀ ∧ p.2 ≠ 1} =>
        f i.1.1 i.1.2) ⟨(x, y), hx, hx1, hy, hy1⟩
  · exact iSup_le fun i => le_xySupOf (f := f) i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2

theorem commutator_xySupOf_le {H : Subgroup G} {f : A₀ → A₀ → Subgroup G}
    (hf : ∀ x ∈ X₀, x ≠ 1 → ∀ y ∈ Y₀, y ≠ 1 → f x y ≤ normalizer (H : Set G)) :
    ⁅H, xySupOf X₀ Y₀ f⁆ ≤ xySupOf X₀ Y₀ fun x y => ⁅H, f x y⁆ := by
  rw [xySupOf_eq_iSup f, xySupOf_eq_iSup (fun x y => ⁅H, f x y⁆),
    commutator_iSup_eq_of_le_normalizer fun i => hf _ i.2.1 i.2.2.1 _ i.2.2.2.1 i.2.2.2.2]

end Generation

section FourGroups

variable {A₀ G : Type*} [Group A₀] [Group G]

theorem commutator_sup_le_of_abelian {S T U W : Subgroup G} (hS : U ≤ normalizer (S : Set G))
    (hT : U ≤ normalizer (T : Set G)) (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hSW : S ≤ W)
    (hTW : T ≤ W) : ⁅S ⊔ T, U⁆ ≤ ⁅S, U⁆ ⊔ ⁅T, U⁆ := by
  have hcomm : ∀ i j : Bool, cond i S T ≤ centralizer ((cond j S T : Subgroup G) : Set G) := by
    have hle : ∀ i : Bool, cond i S T ≤ W := fun i => by cases i <;> assumption
    intro i j a ha
    rw [mem_centralizer_iff]
    intro b hb
    exact hW b (hle j hb) a (hle i ha)
  have h := iSup_commutator_eq_of_commute (H := fun b : Bool => cond b S T) (K := U)
    (fun b => by cases b <;> assumption) hcomm
  simp only [iSup_bool_eq, cond_true, cond_false] at h
  exact h.le

theorem isKleinFour_map {Z₀ : Subgroup A₀} (hZ : IsKleinFour Z₀) {ι : A₀ →* G}
    (hι : Function.Injective ι) : IsKleinFour (Z₀.map ι) := by
  let e : Z₀ ≃* Z₀.map ι := Z₀.equivMapOfInjective ι hι
  exact ⟨by rw [← Nat.card_congr e.toEquiv, hZ.card_four],
    by rw [← Monoid.exponent_eq_of_mulEquiv e, hZ.exponent_two]⟩

variable [Finite G]

theorem le_iSup_centralizers {W : Subgroup G} (hW : Odd (Nat.card W)) {Z₀ : Subgroup A₀}
    (hZ : IsKleinFour Z₀) {ι : A₀ →* G} (hι : Function.Injective ι)
    (hWn : Z₀.map ι ≤ normalizer (W : Set G)) :
    W ≤ ⨆ z : {z : A₀ // z ∈ Z₀ ∧ z ≠ 1}, W ⊓ C (ι z) := by
  haveI := isKleinFour_map hZ hι
  obtain ⟨z₁, hz₁, hz₁1⟩ : ∃ z₁ ∈ Z₀, z₁ ≠ 1 := by
    by_contra h
    push Not at h
    have hle : Z₀ ≤ ⊥ := fun z hz => (mem_bot).mpr (h z hz)
    have h4 := hZ.card_four
    rw [le_bot_iff.mp hle, card_bot] at h4
    omega
  obtain ⟨z₂, hz₂, hz₂z⟩ := exists_mem_not_mem_zpowers_of_isKleinFour hZ hz₁ hz₁1
  have hz₂1 : z₂ ≠ 1 := fun h => hz₂z (h ▸ one_mem _)
  have hz₁₂ : z₁ ≠ z₂ := fun h => hz₂z (h ▸ mem_zpowers z₁)
  have hz₃ : z₁ * z₂ ∈ Z₀ := mul_mem hz₁ hz₂
  have hz₃1 : z₁ * z₂ ≠ 1 := by
    intro h
    apply hz₂z
    rw [← mul_eq_one_iff_inv_eq.mp h]
    exact inv_mem (mem_zpowers z₁)
  have hz₁₃ : z₁ ≠ z₁ * z₂ := fun h => hz₂1 (by
    have := congrArg (z₁⁻¹ * ·) h
    simpa using this.symm)
  have hz₂₃ : z₂ ≠ z₁ * z₂ := fun h => hz₁1 (by
    have := congrArg (· * z₂⁻¹) h
    simpa using this.symm)
  have hset := CFSG.ABGLocalTools.four_group_odd_eq_mul_centralizers (T := Z₀.map ι) hW hWn
    (mem_map_of_mem ι hz₁) (mem_map_of_mem ι hz₂) (mem_map_of_mem ι hz₃)
    (fun h => hz₁1 (hι (h.trans (map_one ι).symm)))
    (fun h => hz₂1 (hι (h.trans (map_one ι).symm)))
    (fun h => hz₃1 (hι (h.trans (map_one ι).symm)))
    (fun h => hz₁₂ (hι h)) (fun h => hz₁₃ (hι h)) (fun h => hz₂₃ (hι h))
  set T : Subgroup G := ⨆ z : {z : A₀ // z ∈ Z₀ ∧ z ≠ 1}, W ⊓ C (ι z) with hT
  have hle : ∀ z : {z : A₀ // z ∈ Z₀ ∧ z ≠ 1}, W ⊓ C (ι z) ≤ T := fun z =>
    le_iSup (fun z : {z : A₀ // z ∈ Z₀ ∧ z ≠ 1} => W ⊓ C (ι z)) z
  intro w hw
  have hw' : w ∈ (W : Set G) := hw
  rw [hset] at hw'
  obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩ := hw'
  exact mul_mem (mul_mem (hle ⟨z₁, hz₁, hz₁1⟩ ha) (hle ⟨z₂, hz₂, hz₂1⟩ hb))
    (hle ⟨z₁ * z₂, hz₃, hz₃1⟩ hc)

theorem eq_one_or_inverts_of_isKleinFour {Z₀ : Subgroup A₀} (hZ : IsKleinFour Z₀)
    (ι : A₀ →* G) {z z' : A₀} (hz : z ∈ Z₀) (hz1 : z ≠ 1) (hz' : z' ∈ Z₀) (hz'1 : z' ≠ 1)
    {W : Subgroup G} (hW : Odd (Nat.card W)) {u : G} (hu : u ∈ W)
    (hc : ι z' * u * (ι z')⁻¹ = u) (hi : ι z * u * (ι z)⁻¹ = u⁻¹) :
    u = 1 ∨ ∀ w ∈ Z₀, w ∉ zpowers z' → ι w * u * (ι w)⁻¹ = u⁻¹ := by
  by_cases hzz : z ∈ zpowers z'
  · left
    rcases eq_one_or_eq_of_mem_zpowers (orderOf_eq_two_of_isKleinFour hZ hz' hz'1) hzz with
      h | h
    · exact absurd h hz1
    · rw [h] at hi
      exact eq_one_of_conj_eq_self_of_conj_eq_inv hW hu hc hi
  · right
    exact inverts_of_isKleinFour hZ ι hz' hz'1 hz hzz hc hi

end FourGroups

namespace Prop22Hyp

variable {A₀ G : Type*} [Group A₀] [Group G] {X₀ Y₀ : Subgroup A₀} {ι : A₀ →* G}
  {K : Subgroup G} {Kxy : A₀ → A₀ → Subgroup G}

theorem swap (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) : Prop22Hyp Y₀ X₀ ι K fun y x => Kxy x y where
  kleinX := hyp.kleinY
  kleinY := hyp.kleinX
  inf_eq := by rw [inf_comm]; exact hyp.inf_eq
  comm := le_centralizer_iff.mp hyp.comm
  sup_eq := by rw [sup_comm]; exact hyp.sup_eq
  inj := hyp.inj
  odd := hyp.odd
  normalizes := hyp.normalizes
  le := fun y hy hy1 x hx hx1 => by
    rw [inf_right_comm]
    exact hyp.le x hx hx1 y hy hy1
  normal := fun y hy hy1 x hx hx1 => by
    rw [inf_right_comm]
    exact hyp.normal x hx hx1 y hy hy1
  inv := fun y hy hy1 x hx hx1 => hyp.inv x hx hx1 y hy hy1
  gen := by rw [xySupOf_swap]; exact hyp.gen
  a := fun y hy hy1 y' hy' hy'1 x hx hx1 x' hx' hx'1 =>
    ⟨(hyp.a x hx hx1 x' hx' hx'1 y hy hy1 y' hy' hy'1).2,
      (hyp.a x hx hx1 x' hx' hx'1 y hy hy1 y' hy' hy'1).1⟩
  b := fun y hy hy1 x hx hx1 u hu hY hX => by
    rw [inf_right_comm] at hu
    exact hyp.b x hx hx1 y hy hy1 u hu hX hY
  c := fun y hy hy1 x hx hx1 => ⟨(hyp.c x hx hx1 y hy hy1).2, (hyp.c x hx hx1 y hy hy1).1⟩
  d := fun p P hp hPp hPK hPA hPgen Q hQP hQA => isKxyGen_swap_iff.mpr
    (hyp.d p P hp hPp hPK hPA (isKxyGen_swap_iff.mp hPgen) Q hQP hQA)

theorem orderOf_ι_X (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) {x : A₀} (hx : x ∈ X₀) (hx1 : x ≠ 1) :
    orderOf (ι x) = 2 := by
  rw [orderOf_injective ι hyp.inj, orderOf_eq_two_of_isKleinFour hyp.kleinX hx hx1]

theorem orderOf_ι_Y (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) {y : A₀} (hy : y ∈ Y₀) (hy1 : y ≠ 1) :
    orderOf (ι y) = 2 :=
  hyp.swap.orderOf_ι_X hy hy1

end Prop22Hyp

namespace Prop22Hyp

variable {A₀ G : Type*} [Group A₀] [Group G] [Finite G] {X₀ Y₀ : Subgroup A₀} {ι : A₀ →* G}
  {K : Subgroup G} {Kxy : A₀ → A₀ → Subgroup G} {V : Subgroup G}

private theorem mem_normalizer_pieces (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) (hKV : K ≤ normalizer (V : Set G))
    (hVA : ι.range ≤ normalizer (V : Set G)) {x y : A₀} (hx : x ∈ X₀) (hx1 : x ≠ 1) (hy : y ∈ Y₀)
    (hy1 : y ≠ 1) {g : G} (hg : g ∈ Kxy x y ∨ g ∈ ι.range) :
    g ∈ normalizer ((V ⊓ C (ι x) ⊓ C (ι y) : Subgroup G) : Set G) ∧
      g ∈ normalizer ((⁅V ⊓ C (ι x), zpowers (ι y)⁆ : Subgroup G) : Set G) ∧
      g ∈ normalizer ((⁅V ⊓ C (ι y), zpowers (ι x)⁆ : Subgroup G) : Set G) ∧
      g ∈ normalizer ((⁅V, zpowers (ι x)⁆ ⊓ ⁅V, zpowers (ι y)⁆ : Subgroup G) : Set G) := by
  rcases hg with hg | ⟨c, rfl⟩
  · obtain ⟨⟨hgK, hgx⟩, hgy⟩ := hyp.le x hx hx1 y hy hy1 hg
    exact mem_normalizer_fourGroup (hKV hgK) (mem_centralizer_singleton_iff.mp hgx)
      (mem_centralizer_singleton_iff.mp hgy)
  · exact mem_normalizer_fourGroup (hVA ⟨c, rfl⟩) (hyp.commute_range c x) (hyp.commute_range c y)

private theorem isKxyGen_commutator_V₀ (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) (hVK : V ≤ K) {x y : A₀}
    (hx : x ∈ X₀) (hx1 : x ≠ 1) (hy : y ∈ Y₀) (hy1 : y ≠ 1) :
    IsKxyGen X₀ Y₀ Kxy ⁅V ⊓ C (ι x) ⊓ C (ι y), Kxy x y⁆ := by
  refine isKxyGen_of_le_Kxy hx hx1 hy hy1 ?_
  rw [commutator_le]
  intro v hv k hk
  obtain ⟨hvxV, hvy⟩ := mem_inf.mp hv
  obtain ⟨hvV, hvx⟩ := mem_inf.mp hvxV
  have hvN : v ∈ normalizer (Kxy x y : Set G) :=
    hyp.le_normalizer_Kxy hx hx1 hy hy1 (mem_inf.mpr ⟨mem_inf.mpr ⟨hVK hvV, hvx⟩, hvy⟩)
  rw [commutatorElement_def]
  exact mul_mem ((mem_normalizer_iff.mp hvN k).mp hk) (inv_mem hk)

private theorem isKxyGen_commutator_V₃ (hyp : Prop22Hyp X₀ Y₀ ι K Kxy)
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hVK : V ≤ K) (hKV : K ≤ normalizer (V : Set G))
    (hVA : ι.range ≤ normalizer (V : Set G)) {q : ℕ} (hq : q.Prime) (hVq : IsPGroup q V)
    {x y : A₀} (hx : x ∈ X₀) (hx1 : x ≠ 1) (hy : y ∈ Y₀) (hy1 : y ≠ 1) :
    IsKxyGen X₀ Y₀ Kxy ⁅⁅V, zpowers (ι x)⁆ ⊓ ⁅V, zpowers (ι y)⁆, Kxy x y⁆ := by
  have hVodd : Odd (Nat.card V) := hyp.odd.of_dvd_nat (card_dvd_of_le hVK)
  have hx2 := hyp.orderOf_ι_X hx hx1
  have hy2 := hyp.orderOf_ι_Y hy hy1
  have hxy := hyp.commute_range x y
  have hxV : ι x ∈ normalizer (V : Set G) := hVA ⟨x, rfl⟩
  have hyV : ι y ∈ normalizer (V : Set G) := hVA ⟨y, rfl⟩
  set V₃ : Subgroup G := ⁅V, zpowers (ι x)⁆ ⊓ ⁅V, zpowers (ι y)⁆ with hV₃
  have hmem := fun h => mem_fourGroup₃_iff (h := h) hVab hVodd hx2 hy2 hxy hxV hyV
  have hV₃V : V₃ ≤ V := fun h hh => ((hmem h).mp hh).1
  have hV₃odd : Odd (Nat.card V₃) := hVodd.of_dvd_nat (card_dvd_of_le hV₃V)
  have hV₃A : ι.range ≤ normalizer (V₃ : Set G) := fun g hg =>
    (mem_normalizer_pieces hyp hKV hVA hx hx1 hy hy1 (Or.inr hg)).2.2.2
  have hV₃gen : IsKxyGen X₀ Y₀ Kxy V₃ := by
    refine isKxyGen_of_le_iSup (le_iSup_centralizers hV₃odd hyp.kleinX hyp.inj
      ((map_le_range ι X₀).trans hV₃A)) (fun _ => inf_le_left) ?_
    rintro ⟨x', hx', hx'1⟩
    have hWodd : Odd (Nat.card (V₃ ⊓ C (ι x') : Subgroup G)) :=
      hV₃odd.of_dvd_nat (card_dvd_of_le inf_le_left)
    have hWn : Y₀.map ι ≤ normalizer ((V₃ ⊓ C (ι x') : Subgroup G) : Set G) := by
      rintro _ ⟨c, -, rfl⟩
      exact inf_normalizer_le_normalizer_inf ⟨hV₃A ⟨c, rfl⟩, hyp.ι_mem_normalizer_C c x'⟩
    refine isKxyGen_of_le_iSup (le_iSup_centralizers hWodd hyp.kleinY hyp.inj hWn)
      (fun _ => inf_le_left) ?_
    rintro ⟨y', hy', hy'1⟩
    refine isKxyGen_of_le_Kxy hx' hx'1 hy' hy'1 ?_
    intro u hu
    obtain ⟨huW, huy'⟩ := mem_inf.mp hu
    obtain ⟨huV₃, hux'⟩ := mem_inf.mp huW
    obtain ⟨huV, hxu, hyu⟩ := (hmem u).mp huV₃
    rcases eq_one_or_inverts_of_isKleinFour hyp.kleinX ι hx hx1 hx' hx'1 hVodd huV
      (conj_eq_of_mem_C hux') hxu with h1 | hX
    · rw [h1]
      exact one_mem _
    rcases eq_one_or_inverts_of_isKleinFour hyp.kleinY ι hy hy1 hy' hy'1 hVodd huV
      (conj_eq_of_mem_C huy') hyu with h1 | hY
    · rw [h1]
      exact one_mem _
    exact hyp.b x' hx' hx'1 y' hy' hy'1 u (mem_inf.mpr ⟨mem_inf.mpr ⟨hVK huV, hux'⟩, huy'⟩) hX hY
  have hle : ⁅V₃, Kxy x y⁆ ≤ V₃ := le_normalizer_iff_commutator_le_left.mp fun k hk =>
    (mem_normalizer_pieces hyp hKV hVA hx hx1 hy hy1 (Or.inl hk)).2.2.2
  have hA : ι.range ≤ normalizer ((⁅V₃, Kxy x y⁆ : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_commutator' (hV₃A hg) (hyp.inv x hx hx1 y hy hy1 hg)
  exact hyp.d q V₃ hq (hVq.to_le hV₃V) (hV₃V.trans hVK) hV₃A hV₃gen _ hle hA

theorem isKxyGen_commutator_V₁ (hyp : Prop22Hyp X₀ Y₀ ι K Kxy)
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hVK : V ≤ K) (hKV : K ≤ normalizer (V : Set G))
    (hVA : ι.range ≤ normalizer (V : Set G)) {x y : A₀} (hx : x ∈ X₀) (hx1 : x ≠ 1)
    (hy : y ∈ Y₀) (hy1 : y ≠ 1) :
    IsKxyGen X₀ Y₀ Kxy ⁅⁅V ⊓ C (ι x), zpowers (ι y)⁆, Kxy x y⁆ := by
  have hVodd : Odd (Nat.card V) := hyp.odd.of_dvd_nat (card_dvd_of_le hVK)
  have hx2 := hyp.orderOf_ι_X hx hx1
  have hy2 := hyp.orderOf_ι_Y hy hy1
  have hxy := hyp.commute_range x y
  have hxV : ι x ∈ normalizer (V : Set G) := hVA ⟨x, rfl⟩
  have hyV : ι y ∈ normalizer (V : Set G) := hVA ⟨y, rfl⟩
  set V₁ : Subgroup G := ⁅V ⊓ C (ι x), zpowers (ι y)⁆ with hV₁
  have hmem := fun h => mem_fourGroup₁_iff (h := h) hVab hVodd hx2 hy2 hxy hxV hyV
  have hV₁V : V₁ ≤ V := fun h hh => ((hmem h).mp hh).1
  have hV₁odd : Odd (Nat.card V₁) := hVodd.of_dvd_nat (card_dvd_of_le hV₁V)
  have hKxyV₁ : Kxy x y ≤ normalizer (V₁ : Set G) := fun k hk =>
    (mem_normalizer_pieces hyp hKV hVA hx hx1 hy hy1 (Or.inl hk)).2.1
  have hAV₁ : ι.range ≤ normalizer (V₁ : Set G) := fun g hg =>
    (mem_normalizer_pieces hyp hKV hVA hx hx1 hy hy1 (Or.inr hg)).2.1
  set YA : Subgroup G := Y₀.map ι with hYA
  have hYAA : YA ≤ ι.range := map_le_range ι Y₀
  set KY₀ : Subgroup G := Kxy x y ⊓ centralizer (YA : Set G) with hKY₀
  set KY₁ : Subgroup G := ⁅Kxy x y, YA⁆ with hKY₁
  have hKxyK : Kxy x y ≤ K := (hyp.le x hx hx1 y hy hy1).trans (inf_le_left.trans inf_le_left)
  have hKxyodd : Odd (Nat.card (Kxy x y)) := hyp.odd.of_dvd_nat (card_dvd_of_le hKxyK)
  have hfact : KY₁ ⊔ KY₀ = Kxy x y :=
    CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2 Nat.prime_two
      YA (Kxy x y) (hyp.isPGroup_range.to_le hYAA)
      (hYAA.trans (hyp.inv x hx hx1 y hy hy1)) (Nat.coprime_two_left.mpr hKxyodd)
  have hKY₁le : KY₁ ≤ Kxy x y := hfact ▸ le_sup_left
  have hKY₀le : KY₀ ≤ Kxy x y := inf_le_left
  have hsplit : ⁅V₁, Kxy x y⁆ = ⁅V₁, KY₁⁆ ⊔ ⁅V₁, KY₀⁆ := by
    conv_lhs => rw [← hfact]
    exact commutator_sup_eq_of_le_normalizer (hKY₁le.trans hKxyV₁) (hKY₀le.trans hKxyV₁)
  have hgen₀ : IsKxyGen X₀ Y₀ Kxy ⁅V₁, KY₀⁆ := by
    have hV₁n : YA ≤ normalizer (V₁ : Set G) := hYAA.trans hAV₁
    have hcov := le_iSup_centralizers hV₁odd hyp.kleinY hyp.inj hV₁n
    have hle : ⁅V₁, KY₀⁆ ≤ ⨆ z : {z : A₀ // z ∈ Y₀ ∧ z ≠ 1}, ⁅V₁ ⊓ C (ι z), KY₀⁆ := by
      refine (commutator_mono hcov le_rfl).trans (iSup_commutator_eq_of_commute ?_ ?_).le
      · intro z k hk
        exact inf_normalizer_le_normalizer_inf ⟨hKxyV₁ (hKY₀le hk), mem_normalizer_C_of_commute
          ((mem_centralizer_iff.mp (mem_inf.mp hk).2) (ι z) (mem_map_of_mem ι z.2.1)).symm⟩
      · intro i j a ha
        rw [mem_centralizer_iff]
        intro b hb
        exact hVab b (hV₁V (mem_inf.mp hb).1) a (hV₁V (mem_inf.mp ha).1)
    refine isKxyGen_of_le_iSup hle (fun _ => commutator_mono inf_le_left le_rfl) ?_
    rintro ⟨y', hy', hy'1⟩
    refine isKxyGen_of_le_Kxy hx hx1 hy' hy'1 ?_
    rw [commutator_le]
    intro c hc k hk
    obtain ⟨hcV₁, hcy'⟩ := mem_inf.mp hc
    obtain ⟨hcV, hxc, -⟩ := (hmem c).mp hcV₁
    obtain ⟨hkK, hkY⟩ := mem_inf.mp hk
    have hky' : k ∈ C (ι y') := mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp hkY) (ι y') (mem_map_of_mem ι hy')).symm
    have hk' : k ∈ Kxy x y' := (hyp.a x hx hx1 x hx hx1 y hy hy1 y' hy' hy'1).2
      (mem_inf.mpr ⟨hkK, hky'⟩)
    have hcx : c ∈ C (ι x) := mem_centralizer_singleton_iff.mpr (commute_of_conj_eq hxc)
    have hcN : c ∈ normalizer (Kxy x y' : Set G) := hyp.le_normalizer_Kxy hx hx1 hy' hy'1
      (mem_inf.mpr ⟨mem_inf.mpr ⟨hVK hcV, hcx⟩, hcy'⟩)
    rw [commutatorElement_def]
    exact mul_mem ((mem_normalizer_iff.mp hcN k).mp hk') (inv_mem hk')
  have hgen₁ : IsKxyGen X₀ Y₀ Kxy ⁅V₁, KY₁⁆ := by
    set E : Subgroup G := ⁅V₁, KY₁⁆ with hE
    have hEV₁ : E ≤ V₁ := le_normalizer_iff_commutator_le_left.mp (hKY₁le.trans hKxyV₁)
    have hEodd : Odd (Nat.card E) := hV₁odd.of_dvd_nat (card_dvd_of_le hEV₁)
    have hEn : YA ≤ normalizer (E : Set G) := by
      intro g hg
      have hgA := hYAA hg
      exact mem_normalizer_commutator' (hAV₁ hgA) (mem_normalizer_commutator'
        (hyp.inv x hx hx1 y hy hy1 hgA) (le_normalizer hg))
    set L₁ : Subgroup G := ⁅K ⊓ C (ι x), YA⁆ with hL₁
    have hEL : E ≤ ⁅L₁, L₁⁆ := by
      refine commutator_mono (commutator_mono (inf_le_inf_right _ hVK) ?_) (commutator_mono ?_ le_rfl)
      · exact (zpowers_le).mpr (mem_map_of_mem ι hy)
      · exact (hyp.le x hx hx1 y hy hy1).trans inf_le_left
    refine isKxyGen_of_le_iSup (le_iSup_centralizers hEodd hyp.kleinY hyp.inj hEn)
      (fun _ => inf_le_left) ?_
    rintro ⟨y', hy', hy'1⟩
    refine isKxyGen_of_le_Kxy hx hx1 hy' hy'1 ?_
    intro u hu
    obtain ⟨huE, huy'⟩ := mem_inf.mp hu
    obtain ⟨huV, -, hyu⟩ := (hmem u).mp (hEV₁ huE)
    rcases eq_one_or_inverts_of_isKleinFour hyp.kleinY ι hy hy1 hy' hy'1 hVodd huV
      (conj_eq_of_mem_C huy') hyu with h1 | hY
    · rw [h1]
      exact one_mem _
    exact (hyp.c x hx hx1 y' hy' hy'1).1 u (mem_inf.mpr ⟨hEL huE, huy'⟩) hY
  rw [hsplit]
  exact isKxyGen_of_le_sup le_rfl le_sup_left le_sup_right hgen₁ hgen₀

theorem isKxyGen_commutator_Kxy (hyp : Prop22Hyp X₀ Y₀ ι K Kxy)
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hVK : V ≤ K) (hKV : K ≤ normalizer (V : Set G))
    (hVA : ι.range ≤ normalizer (V : Set G)) {q : ℕ} (hq : q.Prime) (hVq : IsPGroup q V)
    {x y : A₀} (hx : x ∈ X₀) (hx1 : x ≠ 1) (hy : y ∈ Y₀) (hy1 : y ≠ 1) :
    IsKxyGen X₀ Y₀ Kxy ⁅V, Kxy x y⁆ := by
  have hVodd : Odd (Nat.card V) := hyp.odd.of_dvd_nat (card_dvd_of_le hVK)
  have hx2 := hyp.orderOf_ι_X hx hx1
  have hy2 := hyp.orderOf_ι_Y hy hy1
  have hxy := hyp.commute_range x y
  have hxV : ι x ∈ normalizer (V : Set G) := hVA ⟨x, rfl⟩
  have hyV : ι y ∈ normalizer (V : Set G) := hVA ⟨y, rfl⟩
  set V₀ : Subgroup G := V ⊓ C (ι x) ⊓ C (ι y) with hV₀
  set V₁ : Subgroup G := ⁅V ⊓ C (ι x), zpowers (ι y)⁆ with hV₁
  set V₂ : Subgroup G := ⁅V ⊓ C (ι y), zpowers (ι x)⁆ with hV₂
  set V₃ : Subgroup G := ⁅V, zpowers (ι x)⁆ ⊓ ⁅V, zpowers (ι y)⁆ with hV₃
  have hdec : V₀ ⊔ V₁ ⊔ V₂ ⊔ V₃ = V := fourGroup_sup_eq hVab hVodd hx2 hy2 hxy hxV hyV
  have hpieces := fun k (hk : k ∈ Kxy x y) =>
    mem_normalizer_pieces hyp hKV hVA hx hx1 hy hy1 (Or.inl hk)
  have hn₀ : Kxy x y ≤ normalizer (V₀ : Set G) := fun k hk => (hpieces k hk).1
  have hn₁ : Kxy x y ≤ normalizer (V₁ : Set G) := fun k hk => (hpieces k hk).2.1
  have hn₂ : Kxy x y ≤ normalizer (V₂ : Set G) := fun k hk => (hpieces k hk).2.2.1
  have hn₃ : Kxy x y ≤ normalizer (V₃ : Set G) := fun k hk => (hpieces k hk).2.2.2
  have hV₀V : V₀ ≤ V := hdec ▸ le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hV₁V : V₁ ≤ V := hdec ▸ le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hV₂V : V₂ ≤ V := hdec ▸ le_sup_right.trans le_sup_left
  have hV₃V : V₃ ≤ V := hdec ▸ le_sup_right
  have hsup : ∀ S T : Subgroup G, Kxy x y ≤ normalizer (S : Set G) →
      Kxy x y ≤ normalizer (T : Set G) → Kxy x y ≤ normalizer ((S ⊔ T : Subgroup G) : Set G) :=
    fun S T hS hT k hk => ABGTheoremB.normalizer_inf_normalizer_le_normalizer_sup S T
      (mem_inf.mpr ⟨hS hk, hT hk⟩)
  have hle : ⁅V, Kxy x y⁆ ≤ ⁅V₀, Kxy x y⁆ ⊔ ⁅V₁, Kxy x y⁆ ⊔ ⁅V₂, Kxy x y⁆ ⊔ ⁅V₃, Kxy x y⁆ := by
    conv_lhs => rw [← hdec]
    refine (commutator_sup_le_of_abelian (hsup _ _ (hsup _ _ hn₀ hn₁) hn₂) hn₃ hVab
      (sup_le (sup_le hV₀V hV₁V) hV₂V) hV₃V).trans (sup_le_sup_right ?_ _)
    refine (commutator_sup_le_of_abelian (hsup _ _ hn₀ hn₁) hn₂ hVab (sup_le hV₀V hV₁V)
      hV₂V).trans (sup_le_sup_right ?_ _)
    exact commutator_sup_le_of_abelian hn₀ hn₁ hVab hV₀V hV₁V
  have h₀ := isKxyGen_commutator_V₀ hyp hVK hx hx1 hy hy1
  have h₁ := hyp.isKxyGen_commutator_V₁ hVab hVK hKV hVA hx hx1 hy hy1
  have h₂ : IsKxyGen X₀ Y₀ Kxy ⁅V₂, Kxy x y⁆ :=
    isKxyGen_swap_iff.mp (hyp.swap.isKxyGen_commutator_V₁ hVab hVK hKV hVA hy hy1 hx hx1)
  have h₃ := isKxyGen_commutator_V₃ hyp hVab hVK hKV hVA hq hVq hx hx1 hy hy1
  have hm : ∀ {S : Subgroup G}, S ≤ V → ⁅S, Kxy x y⁆ ≤ ⁅V, Kxy x y⁆ :=
    fun hS => commutator_mono hS le_rfl
  exact hle.trans (sup_le (sup_le (sup_le (h₀.le_xySupOf_of_le (hm hV₀V))
    (h₁.le_xySupOf_of_le (hm hV₁V))) (h₂.le_xySupOf_of_le (hm hV₂V)))
    (h₃.le_xySupOf_of_le (hm hV₃V)))

theorem isKxyGen_commutator (hyp : Prop22Hyp X₀ Y₀ ι K Kxy)
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hVK : V ≤ K) (hKV : K ≤ normalizer (V : Set G))
    (hVA : ι.range ≤ normalizer (V : Set G)) {q : ℕ} (hq : q.Prime) (hVq : IsPGroup q V) :
    IsKxyGen X₀ Y₀ Kxy ⁅V, K⁆ := by
  have h1 : ⁅V, K⁆ ≤ xySupOf X₀ Y₀ fun x y => ⁅V, Kxy x y⁆ :=
    (commutator_mono le_rfl hyp.gen).trans (commutator_xySupOf_le fun x hx hx1 y hy hy1 =>
      ((hyp.le x hx hx1 y hy hy1).trans (inf_le_left.trans inf_le_left)).trans hKV)
  refine h1.trans (xySupOf_le (f := fun x y => ⁅V, Kxy x y⁆) fun x hx hx1 y hy hy1 => ?_)
  exact (hyp.isKxyGen_commutator_Kxy hVab hVK hKV hVA hq hVq hx hx1 hy hy1).le_xySupOf_of_le
    (commutator_mono le_rfl ((hyp.le x hx hx1 y hy hy1).trans (inf_le_left.trans inf_le_left)))

end Prop22Hyp

section Cores

variable {G : Type*} [Group G]

private theorem exists_pCore_ne_bot {M : Type*} [Group M] [Finite M] [Group.IsSolvable M]
    (hM : (⊤ : Subgroup M) ≠ ⊥) : ∃ p : ℕ, p.Prime ∧ pCore p M ≠ ⊥ := by
  classical
  have hex : ∃ n, derivedSeries M n = ⊥ := Group.IsSolvable.solvable
  have hk : derivedSeries M (Nat.find hex) = ⊥ := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, derivedSeries_zero] at hk
    exact hM hk
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := Nat.exists_eq_succ_of_ne_zero hk0
  set D : Subgroup M := derivedSeries M m with hD
  have hD1 : D ≠ ⊥ := Nat.find_min hex (by omega)
  have hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
    intro a ha b hb
    have h := commutator_mem_commutator ha hb
    rw [← derivedSeries_succ, ← hm, hk, mem_bot] at h
    exact commutatorElement_eq_one_iff_mul_comm.mp h
  have hcard : Nat.card D ≠ 1 := fun h => hD1 (card_eq_one.mp h)
  obtain ⟨p, hp, hpD⟩ := Nat.exists_prime_and_dvd hcard
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S⟩ : Nonempty (Sylow p D) := inferInstance
  have hSn : (S : Subgroup D).Normal := ⟨fun n hn g => by
    have e : g * n * g⁻¹ = n := by
      have := hDab g g.2 n n.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      rw [this, mul_inv_cancel_right]
    rw [e]
    exact hn⟩
  haveI : (S : Subgroup D).Characteristic := Sylow.characteristic_of_normal S hSn
  haveI : D.Normal := derivedSeries_normal M m
  have hSnM : ((S : Subgroup D).map D.subtype).Normal := inferInstance
  have hle : (S : Subgroup D).map D.subtype ≤ pCore p M := le_sSup ⟨hSnM, S.isPGroup'.map _⟩
  refine ⟨p, hp, fun h => S.ne_bot_of_dvd_card hpD ?_⟩
  rw [h, le_bot_iff, map_eq_bot_iff_of_injective _ D.subtype_injective] at hle
  exact hle

private theorem pPrimeCore_eq_bot_of_forall {M : Type*} [Group M] [Finite M] [Group.IsSolvable M]
    {q : ℕ} [Fact q.Prime] (h : ∀ p : ℕ, p.Prime → p ≠ q → pCore p M = ⊥) :
    pPrimeCore q M = ⊥ := by
  by_contra hne
  set N : Subgroup M := pPrimeCore q M with hN
  have hNtop : (⊤ : Subgroup N) ≠ ⊥ := by
    intro htop
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx⟩ : N) ∈ (⊤ : Subgroup N) := mem_top _
    rw [htop, mem_bot] at this
    exact (mem_bot).mpr (congrArg Subtype.val this)
  obtain ⟨p, hp, hpN⟩ := exists_pCore_ne_bot (M := N) hNtop
  haveI : Fact p.Prime := ⟨hp⟩
  have hpq : p ≠ q := by
    intro hpq
    rw [hpq] at hpN
    rcases (pCore_isPGroup (p := q) (G := N)).card_eq_or_dvd with h1 | hdvd
    · exact hpN (card_eq_one.mp h1)
    · have hdvd' : q ∣ Nat.card N := hdvd.trans (card_subgroup_dvd_card _)
      exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).mp pPrimeCore_coprime_card hdvd'
  haveI : N.Normal := pPrimeCore_normal
  have hle : (pCore p N).map N.subtype ≤ pCore p M :=
    le_sSup ⟨inferInstance, (pCore_isPGroup (p := p) (G := N)).map _⟩
  rw [h p hp hpq, le_bot_iff, map_eq_bot_iff_of_injective _ N.subtype_injective] at hle
  exact hpN hle

private theorem mem_normalizer_centralizer {R : Subgroup G} {g : G}
    (hg : g ∈ normalizer (R : Set G)) :
    g ∈ normalizer ((centralizer (R : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro c
  simp only [SetLike.mem_coe, mem_centralizer_iff]
  constructor
  · intro hc r hr
    have hr' : g⁻¹ * r * g ∈ R := by
      have := (mem_normalizer_iff.mp (inv_mem hg) r).mp hr
      simpa using this
    have hcr := hc _ hr'
    calc r * (g * c * g⁻¹) = g * (g⁻¹ * r * g * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * r * g)) * g⁻¹ := by rw [hcr]
      _ = g * c * g⁻¹ * r := by group
  · intro hc r hr
    have hr' : g * r * g⁻¹ ∈ R := (mem_normalizer_iff.mp hg r).mp hr
    have hcr := hc _ hr'
    have e1 : g * r * g⁻¹ * (g * c * g⁻¹) = g * (r * c) * g⁻¹ := by group
    have e2 : g * c * g⁻¹ * (g * r * g⁻¹) = g * (c * r) * g⁻¹ := by group
    rw [e1, e2] at hcr
    exact mul_left_cancel (mul_right_cancel hcr)

variable [Finite G] {K : Subgroup G}

private theorem inf_centralizer_le_pCore [Group.IsSolvable K] {q : ℕ} [Fact q.Prime]
    (hO : pPrimeCore q K = ⊥) :
    K ⊓ centralizer (((pCore q K).map K.subtype : Subgroup G) : Set G) ≤
      (pCore q K).map K.subtype := by
  have hcon := CFSG.ABGLocalTools.isPConstrained_of_isSolvable (p := q) (H := K) inferInstance
  have hOp : Op_p'p q K = pCore q K := Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (p := q) hO
  have hsyl : IsSylowOf q (pCore q K) (Op_p'p q K) := by
    rw [hOp, isSylowOf_iff, relIndex_self]
    exact ⟨le_rfl, pCore_isPGroup, (Fact.out : q.Prime).not_dvd_one⟩
  have h := hcon _ hsyl
  rw [hOp] at h
  intro g hg
  obtain ⟨hgK, hgC⟩ := mem_inf.mp hg
  have hgC' : (⟨g, hgK⟩ : K) ∈ centralizer (pCore q K : Set K) := by
    rw [mem_centralizer_iff]
    intro r hr
    apply Subtype.ext
    exact (mem_centralizer_iff.mp hgC) r (mem_map_of_mem K.subtype hr)
  exact mem_map_of_mem K.subtype (h hgC')

end Cores

theorem prop22Step (A₀ : Type*) [Group A₀] (X₀ Y₀ : Subgroup A₀) : Prop22Step.{u} A₀ X₀ Y₀ := by
  intro G _ _ ι K Kxy hyp hnpow ih
  have hK1 : K ≠ ⊥ := fun h => hnpow 2 Nat.prime_two (h ▸ IsPGroup.of_bot)
  haveI hsolv : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hyp.odd
  have hKtop : (⊤ : Subgroup K) ≠ ⊥ := by
    intro htop
    apply hK1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx⟩ : K) ∈ (⊤ : Subgroup K) := mem_top _
    rw [htop, mem_bot] at this
    exact (mem_bot).mpr (congrArg Subtype.val this)
  obtain ⟨q, hq, hRq⟩ := exists_pCore_ne_bot (M := K) hKtop
  haveI : Fact q.Prime := ⟨hq⟩
  have hA := hyp.isPGroup_range
  have hcore : ∀ r : ℕ, ((pCore r K).map K.subtype ≤ K) ∧
      IsPGroup r ((pCore r K).map K.subtype) ∧
      K ≤ normalizer (((pCore r K).map K.subtype : Subgroup G) : Set G) ∧
      ι.range ≤ normalizer (((pCore r K).map K.subtype : Subgroup G) : Set G) ∧
      (((pCore r K).map K.subtype).subgroupOf K).Normal := by
    intro r
    have hsub : ((pCore r K).map K.subtype).subgroupOf K = pCore r K :=
      comap_map_eq_self_of_injective K.subtype_injective _
    have hn : (((pCore r K).map K.subtype).subgroupOf K).Normal := by
      rw [hsub]
      infer_instance
    refine ⟨map_subtype_le _, pCore_isPGroup.map _,
      (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp hn,
      hyp.normalizes.trans (normalizer_le_normalizer_image_of_characteristic K (pCore r K)), hn⟩
  have hsylow : ∀ (r : ℕ) [Fact r.Prime] (P : Subgroup G), IsSylowOf r P K →
      (pCore r K).map K.subtype ≤ P := by
    intro r _ P hP
    obtain ⟨S, rfl⟩ := hP
    exact map_mono ((pCore_isPGroup (p := r) (G := K)).le_sylow_of_normal S)
  set R : Subgroup G := (pCore q K).map K.subtype with hR
  obtain ⟨hRK, hRq', hKR, hAR, hRn⟩ := hcore q
  have hR1 : R ≠ ⊥ := fun h => hRq ((map_eq_bot_iff_of_injective _ K.subtype_injective).mp h)
  set V : Subgroup G := R ⊓ centralizer (R : Set G) with hV
  have hVR : V ≤ R := inf_le_left
  have hVK : V ≤ K := hVR.trans hRK
  have hVq : IsPGroup q V := hRq'.to_le hVR
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp (mem_inf.mp hb).2) a (mem_inf.mp ha).1
  have hKV : K ≤ normalizer (V : Set G) := fun g hg =>
    inf_normalizer_le_normalizer_inf ⟨hKR hg, mem_normalizer_centralizer (hKR hg)⟩
  have hAV : ι.range ≤ normalizer (V : Set G) := fun g hg =>
    inf_normalizer_le_normalizer_inf ⟨hAR hg, mem_normalizer_centralizer (hAR hg)⟩
  have hVn : (V.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hVK).mpr hKV
  have hV1 : V ≠ ⊥ := by
    haveI : Nontrivial R := (nontrivial_iff_ne_bot R).mpr hR1
    have hcen := (hRq'.bot_lt_center).ne'
    intro hV0
    apply hcen
    have h := center_map_subtype_eq_inf_centralizer R
    rw [← hV, hV0] at h
    exact (map_eq_bot_iff_of_injective _ R.subtype_injective).mp h
  by_cases hVK1 : ⁅V, K⁆ = ⊥
  swap
  ·
    have hle : ⁅V, K⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp hKV
    refine ⟨⁅V, K⁆, q, hq, hVq.to_le hle, hVK1, hle.trans hVK, ?_, ?_,
      hyp.isKxyGen_commutator hVab hVK hKV hAV hq hVq⟩
    · exact (normal_subgroupOf_iff_le_normalizer (hle.trans hVK)).mpr fun g hg =>
        mem_normalizer_commutator' (hKV hg) (le_normalizer hg)
    · exact fun g hg => mem_normalizer_commutator' (hAV hg) (hyp.normalizes hg)
  have hVcen : V ≤ centralizer (K : Set G) := commutator_eq_bot_iff_le_centralizer.mp hVK1
  by_cases hp : ∃ p : ℕ, p.Prime ∧ p ≠ q ∧ pCore p K ≠ ⊥
  ·
    obtain ⟨p, hp, hpq, hRp⟩ := hp
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨hRpK, hRpp, -, hARp, hRpn⟩ := hcore p
    obtain ⟨P, hP, hPA⟩ := ABGTheoremB.exists_isSylowOf_normalized_of_odd hp hA hyp.normalizes
      hyp.odd
    have hPK : P ≤ K := hP.le
    have hQ := hyp.le_xySupOf_sup ih hV1 hVK hVn hAV hPK hPA
    have hPgen := hyp.isKxyGen_of_coprime hp hq hpq hVq hVK hVn hAV hP.isPGroup hPK hPA hQ
    refine ⟨(pCore p K).map K.subtype, p, hp, hRpp,
      fun h => hRp ((map_eq_bot_iff_of_injective _ K.subtype_injective).mp h), hRpK, hRpn, hARp,
      hyp.d p P hp hP.isPGroup hPK hPA hPgen _ (hsylow p P hP) hARp⟩
  push Not at hp
  have hO : pPrimeCore q K = ⊥ := pPrimeCore_eq_bot_of_forall fun r hr hrq => hp r hr hrq
  have hHH := inf_centralizer_le_pCore (K := K) hO
  obtain ⟨Q, hQ, hQA⟩ := ABGTheoremB.exists_isSylowOf_normalized_of_odd hq hA hyp.normalizes
    hyp.odd
  have hQK : Q ≤ K := hQ.le
  have hRQ : R ≤ Q := hsylow q Q hQ
  have hVQ : V ≤ Q := hVR.trans hRQ
  have hZQ : Q ⊓ centralizer (Q : Set G) ≤ V := by
    intro z hz
    obtain ⟨hzQ, hzC⟩ := mem_inf.mp hz
    have hzR : z ∈ centralizer (R : Set G) := centralizer_le hRQ hzC
    exact mem_inf.mpr ⟨hHH (mem_inf.mpr ⟨hQK hzQ, hzR⟩), hzR⟩
  set P₁ : Subgroup G := xySupOf X₀ Y₀ fun x y => Q ⊓ Kxy x y with hP₁
  have hP₁Q : P₁ ≤ Q := xySupOf_le (f := fun x y => Q ⊓ Kxy x y) fun _ _ _ _ _ _ => inf_le_left
  have hQP₁ : Q ≤ P₁ ⊔ V := by
    have h := hyp.le_xySupOf_sup ih hV1 hVK hVn hAV hQK hQA
    rwa [sup_eq_left.mpr hVQ] at h
  by_cases hP₁1 : P₁ = ⊥
  · exfalso
    rw [hP₁1, bot_sup_eq] at hQP₁
    have hKC : K ≤ centralizer (R : Set G) :=
      le_centralizer_iff.mp ((hRQ.trans hQP₁).trans hVcen)
    have hKR' : K ≤ R := fun g hg => hHH (mem_inf.mpr ⟨hg, hKC hg⟩)
    exact hnpow q hq (hRq'.to_le hKR')
  have hP₁A : ι.range ≤ normalizer (P₁ : Set G) := fun g hg =>
    mem_normalizer_xySupOf (f := fun x y => Q ⊓ Kxy x y) fun x hx hx1 y hy hy1 =>
      inf_normalizer_le_normalizer_inf ⟨hQA hg, hyp.inv x hx hx1 y hy hy1 hg⟩
  have hP₁gen : IsKxyGen X₀ Y₀ Kxy P₁ :=
    xySupOf_mono (f := fun x y => Q ⊓ Kxy x y) (g := fun x y => P₁ ⊓ Kxy x y)
      fun x hx hx1 y hy hy1 => le_inf (le_xySupOf (f := fun x y => Q ⊓ Kxy x y) hx hx1 hy hy1)
        inf_le_right
  have hP₁q : IsPGroup q P₁ := hQ.isPGroup.to_le hP₁Q
  set H₁ : Subgroup G := P₁ ⊓ centralizer (Q : Set G) with hH₁
  have hH₁V : H₁ ≤ V := fun h hh =>
    hZQ (mem_inf.mpr ⟨hP₁Q (mem_inf.mp hh).1, (mem_inf.mp hh).2⟩)
  have hH₁K : H₁ ≤ K := hH₁V.trans hVK
  have hH₁1 : H₁ ≠ ⊥ := by
    have hQn : Q ≤ normalizer (P₁ : Set G) := hQP₁.trans (sup_le le_normalizer
      ((le_centralizer_iff.mp ((hP₁Q.trans hQK).trans (le_centralizer_iff.mp hVcen))).trans
        (centralizer_le_normalizer _)))
    haveI hN : (P₁.subgroupOf Q).Normal := (normal_subgroupOf_iff_le_normalizer hP₁Q).mpr hQn
    haveI : Group.IsNilpotent Q := hQ.isPGroup.isNilpotent
    have hN1 : P₁.subgroupOf Q ≠ ⊥ := by
      intro h
      apply hP₁1
      rw [← map_subgroupOf_eq_of_le hP₁Q, h, Subgroup.map_bot]
    have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hN1
    intro hH0
    apply h
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzP, hzZ⟩ := mem_inf.mp hz
    have hzH : (z : G) ∈ H₁ := by
      refine mem_inf.mpr ⟨hzP, ?_⟩
      rw [mem_centralizer_iff]
      intro w hw
      exact congrArg Subtype.val ((mem_center_iff.mp hzZ) ⟨w, hw⟩)
    rw [hH0, mem_bot] at hzH
    exact (mem_bot).mpr (Subtype.ext hzH)
  have hH₁A : ι.range ≤ normalizer (H₁ : Set G) := fun g hg =>
    inf_normalizer_le_normalizer_inf ⟨hP₁A hg, mem_normalizer_centralizer (hQA hg)⟩
  have hH₁n : (H₁.subgroupOf K).Normal := by
    refine (normal_subgroupOf_iff_le_normalizer hH₁K).mpr ?_
    exact (le_centralizer_iff.mp (hH₁V.trans hVcen)).trans (centralizer_le_normalizer _)
  exact ⟨H₁, q, hq, hP₁q.to_le inf_le_left, hH₁1, hH₁K, hH₁n, hH₁A,
    hyp.d q P₁ hq hP₁q (hP₁Q.trans hQK) hP₁A hP₁gen H₁ inf_le_left hH₁A⟩

theorem prop_2_2 {G : Type u} [Group G] [Finite G] {K X Y : Subgroup G}
    (hK : Odd (Nat.card K)) (hX : IsKleinFour X) (hY : IsKleinFour Y) (hXY : X ⊓ Y = ⊥)
    (hYX : Y ≤ centralizer (X : Set G)) (hAK : X ⊔ Y ≤ normalizer (K : Set G))
    (Kxy : G → G → Subgroup G)
    (hle : ∀ x ∈ X, x ≠ 1 → ∀ y ∈ Y, y ≠ 1 → Kxy x y ≤ K ⊓ C x ⊓ C y)
    (hnormal : ∀ x ∈ X, x ≠ 1 → ∀ y ∈ Y, y ≠ 1 →
      ((Kxy x y).subgroupOf (K ⊓ C x ⊓ C y)).Normal)
    (hinv : ∀ x ∈ X, x ≠ 1 → ∀ y ∈ Y, y ≠ 1 → X ⊔ Y ≤ normalizer (Kxy x y : Set G))
    (hgen : K = xySup X Y Kxy)
    (ha : ∀ x ∈ X, x ≠ 1 → ∀ x' ∈ X, x' ≠ 1 → ∀ y ∈ Y, y ≠ 1 → ∀ y' ∈ Y, y' ≠ 1 →
      Kxy x y ⊓ C x' ≤ Kxy x' y ∧ Kxy x y ⊓ C y' ≤ Kxy x y')
    (hb : ∀ x ∈ X, x ≠ 1 → ∀ y ∈ Y, y ≠ 1 → ∀ u ∈ K ⊓ C x ⊓ C y,
      (∀ x' ∈ X, x' ∉ zpowers x → x' * u * x'⁻¹ = u⁻¹) →
      (∀ y' ∈ Y, y' ∉ zpowers y → y' * u * y'⁻¹ = u⁻¹) → u ∈ Kxy x y)
    (hc : ∀ x ∈ X, x ≠ 1 → ∀ y ∈ Y, y ≠ 1 →
      (∀ u ∈ ⁅⁅K ⊓ C x, Y⁆, ⁅K ⊓ C x, Y⁆⁆ ⊓ C y,
        (∀ y' ∈ Y, y' ∉ zpowers y → y' * u * y'⁻¹ = u⁻¹) → u ∈ Kxy x y) ∧
      (∀ u ∈ ⁅⁅K ⊓ C y, X⁆, ⁅K ⊓ C y, X⁆⁆ ⊓ C x,
        (∀ x' ∈ X, x' ∉ zpowers x → x' * u * x'⁻¹ = u⁻¹) → u ∈ Kxy x y))
    (hd : ∀ (p : ℕ) (P : Subgroup G), p.Prime → IsPGroup p P → P ≤ K →
      X ⊔ Y ≤ normalizer (P : Set G) → P = xySup X Y (fun x y => P ⊓ Kxy x y) →
      ∀ Q ≤ P, X ⊔ Y ≤ normalizer (Q : Set G) → Q = xySup X Y (fun x y => Q ⊓ Kxy x y)) :
    ∀ F ≤ K, X ⊔ Y ≤ normalizer (F : Set G) → F = xySup X Y (fun x y => F ⊓ Kxy x y) :=
  prop_2_2_of_step (prop22Step _ _ _) hK hX hY hXY hYX hAK Kxy hle hnormal hinv hgen ha hb hc hd

section Prop23

variable {G : Type*} [Group G] [Finite G] {X Y : Subgroup G}

private theorem xySup_le' {f : G → G → Subgroup G} {N : Subgroup G}
    (h : ∀ x ∈ X, x ≠ 1 → ∀ y ∈ Y, y ≠ 1 → f x y ≤ N) : xySup X Y f ≤ N :=
  xySupOf_le (X₀ := X) (Y₀ := Y) (f := f) h

private theorem le_xySup' {f : G → G → Subgroup G} {x y : G} (hx : x ∈ X) (hx1 : x ≠ 1)
    (hy : y ∈ Y) (hy1 : y ≠ 1) : f x y ≤ xySup X Y f :=
  le_xySupOf (X₀ := X) (Y₀ := Y) (f := f) hx hx1 hy hy1

private theorem xySup_mono' {f g : G → G → Subgroup G}
    (h : ∀ x ∈ X, x ≠ 1 → ∀ y ∈ Y, y ≠ 1 → f x y ≤ g x y) : xySup X Y f ≤ xySup X Y g :=
  xySupOf_mono (X₀ := X) (Y₀ := Y) (f := f) (g := g) h

private theorem inf_Kxy_eq {F K : Subgroup G} (hFK : F ≤ K) :
    (fun x y => F ⊓ (K ⊓ O (C x) ⊓ O (C y))) = fun x y => F ⊓ O (C x) ⊓ O (C y) := by
  funext x y
  rw [← inf_assoc, ← inf_assoc, inf_eq_left.mpr hFK]

private theorem mem_normalizer_O_C {g z : G} (h : g * z = z * g) :
    g ∈ normalizer ((O (C z) : Subgroup G) : Set G) :=
  ProperTwoGeneratedCore.LocalCriterionDenominator.normalizer_normalizes_oddCore_image (C z)
    (mem_normalizer_C_of_commute h)

private theorem commutator_self_le (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

private theorem odd_card_O (H : Subgroup G) : Odd (Nat.card (O H)) := by
  rw [card_map_of_injective H.subtype_injective]
  exact CFSG.ABGLocalTools.odd_card_oddCore

theorem prop_2_3 (hX : IsKleinFour X) (hY : IsKleinFour Y) (hXY : X ⊓ Y = ⊥)
    (hYX : Y ≤ centralizer (X : Set G)) (hbal : IsXYBalanced X Y) :
    (∀ a ∈ X ⊔ Y, a ≠ 1 → theta X Y a ≤ centralizer {a}) ∧
    (∀ a ∈ X ⊔ Y, a ≠ 1 → Odd (Nat.card (theta X Y a))) ∧
    (∀ a ∈ X ⊔ Y, a ≠ 1 → X ⊔ Y ≤ normalizer (theta X Y a : Set G)) ∧
    (∀ a ∈ X ⊔ Y, a ≠ 1 → ∀ b ∈ X ⊔ Y, b ≠ 1 →
      theta X Y a ⊓ centralizer {b} ≤ theta X Y b) := by
  have hXab : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
    haveI := hX
    intro a ha b hb
    exact congrArg Subtype.val
      ((IsKleinFour.isMulCommutative (G := X)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hYab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
    haveI := hY
    intro a ha b hb
    exact congrArg Subtype.val
      ((IsKleinFour.isMulCommutative (G := Y)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcX : X ⊔ Y ≤ centralizer (X : Set G) := sup_le
    (fun a ha => mem_centralizer_iff.mpr fun b hb => hXab b hb a ha) hYX
  have hcY : X ⊔ Y ≤ centralizer (Y : Set G) := sup_le (le_centralizer_iff.mp hYX)
    (fun a ha => mem_centralizer_iff.mpr fun b hb => hYab b hb a ha)
  have hcA : X ⊔ Y ≤ centralizer ((X ⊔ Y : Subgroup G) : Set G) :=
    sup_le (le_centralizer_iff.mp hcX) (le_centralizer_iff.mp hcY)
  have hcomm : ∀ a ∈ X ⊔ Y, ∀ b ∈ X ⊔ Y, a * b = b * a := fun a ha b hb =>
    ((mem_centralizer_iff.mp (hcA hb)) a ha)
  have hnotY : ∀ x ∈ X, x ≠ 1 → x ∉ Y := fun x hx hx1 hxY => hx1 (by
    have h : x ∈ X ⊓ Y := mem_inf.mpr ⟨hx, hxY⟩
    rwa [hXY, mem_bot] at h)
  have hnotX : ∀ y ∈ Y, y ≠ 1 → y ∉ X := fun y hy hy1 hyX => hy1 (by
    have h : y ∈ X ⊓ Y := mem_inf.mpr ⟨hyX, hy⟩
    rwa [hXY, mem_bot] at h)
  have hAθ : ∀ a ∈ X ⊔ Y, X ⊔ Y ≤ normalizer (theta X Y a : Set G) := by
    intro a ha g hg
    exact mem_normalizer_xySupOf (X₀ := X) (Y₀ := Y)
      (f := fun x y => C a ⊓ O (C x) ⊓ O (C y)) fun x hx _ y hy _ =>
        inf_normalizer_le_normalizer_inf ⟨inf_normalizer_le_normalizer_inf
          ⟨mem_normalizer_C_of_commute (hcomm g hg a ha),
            mem_normalizer_O_C (hcomm g hg x (mem_sup_left hx))⟩,
          mem_normalizer_O_C (hcomm g hg y (mem_sup_right hy))⟩
  have hθC : ∀ a : G, theta X Y a ≤ C a := fun a =>
    xySup_le' fun _ _ _ _ _ _ => inf_le_left.trans inf_le_left
  have hθO : ∀ a ∈ X ⊔ Y, a ≠ 1 → theta X Y a ≤ O (C a) := by
    intro a ha ha1
    refine xySup_le' fun x hx hx1 y hy hy1 => ?_
    by_cases haY : a ∈ Y
    · have haX : a ∉ X := hnotX a haY ha1
      intro g hg
      obtain ⟨⟨hga, -⟩, hgy⟩ := hg
      exact hbal.a₂ y hy hy1 a ha haX (mem_inf.mpr ⟨hgy, hga⟩)
    · intro g hg
      obtain ⟨⟨hga, hgx⟩, -⟩ := hg
      exact hbal.a₁ x hx hx1 a ha haY (mem_inf.mpr ⟨hgx, hga⟩)
  have hθodd : ∀ a ∈ X ⊔ Y, a ≠ 1 → Odd (Nat.card (theta X Y a)) := fun a ha ha1 =>
    (odd_card_O (C a)).of_dvd_nat (card_dvd_of_le (hθO a ha ha1))
  refine ⟨fun a _ _ => hθC a, hθodd, fun a ha _ => hAθ a ha, ?_⟩
  intro a ha ha1 b hb _
  set K : Subgroup G := theta X Y a with hK
  have hKodd := hθodd a ha ha1
  have hKA := hAθ a ha
  have hOC : ∀ z : G, O (C z) ≤ C z := fun z => map_subtype_le _
  have hDodd : ∀ D : Subgroup G, D ≤ K → Odd (Nat.card D) := fun D hD =>
    hKodd.of_dvd_nat (card_dvd_of_le hD)
  have hAC : ∀ z ∈ X ⊔ Y, X ⊔ Y ≤ normalizer ((C z : Subgroup G) : Set G) := fun z hz g hg =>
    mem_normalizer_C_of_commute (hcomm g hg z hz)
  have hAO : ∀ z ∈ X ⊔ Y, X ⊔ Y ≤ normalizer ((O (C z) : Subgroup G) : Set G) := fun z hz g hg =>
    mem_normalizer_O_C (hcomm g hg z hz)
  have hAKC : ∀ z ∈ X ⊔ Y, X ⊔ Y ≤ normalizer ((K ⊓ C z : Subgroup G) : Set G) := fun z hz g hg =>
    inf_normalizer_le_normalizer_inf ⟨hKA hg, hAC z hz hg⟩
  have hinvcomm : ∀ (D : Subgroup G), D ≤ K → ∀ {t u : G}, u ∈ D → t * u * t⁻¹ = u⁻¹ →
      u ∈ ⁅D, zpowers t⁆ := fun D hD _ _ hu h =>
    mem_commutator_zpowers_of_conj_eq_inv (hDodd D hD) hu h
  have h22 := prop_2_2 (K := K) (X := X) (Y := Y) hKodd hX hY hXY hYX hKA
    (fun x y => K ⊓ O (C x) ⊓ O (C y))
    (fun x _ _ y _ _ => inf_le_inf (inf_le_inf_left _ (hOC x)) (hOC y))
    (fun x hx _ y hy _ => by
      refine (normal_subgroupOf_iff_le_normalizer
        (inf_le_inf (inf_le_inf_left _ (hOC x)) (hOC y))).mpr ?_
      intro g hg
      obtain ⟨⟨hgK, hgx⟩, hgy⟩ := hg
      exact inf_normalizer_le_normalizer_inf ⟨inf_normalizer_le_normalizer_inf
        ⟨le_normalizer hgK, mem_normalizer_O_C (mem_centralizer_singleton_iff.mp hgx)⟩,
        mem_normalizer_O_C (mem_centralizer_singleton_iff.mp hgy)⟩)
    (fun x hx _ y hy _ g hg => inf_normalizer_le_normalizer_inf
      ⟨inf_normalizer_le_normalizer_inf ⟨hKA hg, hAO x (mem_sup_left hx) hg⟩,
        hAO y (mem_sup_right hy) hg⟩)
    (by
      refine le_antisymm ?_ (xySup_le' fun _ _ _ _ _ _ => inf_le_left.trans inf_le_left)
      refine xySup_mono' fun x hx hx1 y hy hy1 => ?_
      exact le_inf (le_inf (le_xySup' (f := fun x y => C a ⊓ O (C x) ⊓ O (C y)) hx hx1 hy hy1)
        (inf_le_left.trans inf_le_right)) inf_le_right)
    (fun x hx hx1 x' hx' hx'1 y hy hy1 y' hy' hy'1 => by
      constructor
      · rintro g ⟨⟨⟨hgK, hgx⟩, hgy⟩, hgx'⟩
        exact ⟨⟨hgK, hbal.a₁ x hx hx1 x' (mem_sup_left hx') (hnotY x' hx' hx'1)
          (mem_inf.mpr ⟨hgx, hgx'⟩)⟩, hgy⟩
      · rintro g ⟨⟨⟨hgK, hgx⟩, hgy⟩, hgy'⟩
        exact ⟨⟨hgK, hgx⟩, hbal.a₂ y hy hy1 y' (mem_sup_right hy') (hnotX y' hy' hy'1)
          (mem_inf.mpr ⟨hgy, hgy'⟩)⟩)
    (fun x hx hx1 y hy hy1 u hu hXinv hYinv => by
      obtain ⟨x', hx', hx'z⟩ := exists_mem_not_mem_zpowers_of_isKleinFour hX hx hx1
      obtain ⟨y', hy', hy'z⟩ := exists_mem_not_mem_zpowers_of_isKleinFour hY hy hy1
      set D : Subgroup G := K ⊓ C x ⊓ C y with hD
      have hDK : D ≤ K := inf_le_left.trans inf_le_left
      have hDA : X ⊔ Y ≤ normalizer (D : Set G) := fun g hg =>
        inf_normalizer_le_normalizer_inf ⟨hAKC x (mem_sup_left hx) hg,
          hAC y (mem_sup_right hy) hg⟩
      have h1 := hbal.b₁ x hx hx1 D (inf_le_left.trans inf_le_right) (hDodd D hDK) hDA
      have h2 := hbal.b₂ y hy hy1 D inf_le_right (hDodd D hDK) hDA
      have hux : u ∈ O (C x) := h1 (mem_sup_left (commutator_mono le_rfl
        ((zpowers_le).mpr hx') (hinvcomm D hDK hu (hXinv x' hx' hx'z))))
      have huy : u ∈ O (C y) := h2 (mem_sup_left (commutator_mono le_rfl
        ((zpowers_le).mpr hy') (hinvcomm D hDK hu (hYinv y' hy' hy'z))))
      exact ⟨⟨hDK hu, hux⟩, huy⟩)
    (fun x hx hx1 y hy hy1 => by
      constructor
      · intro u hu hYinv
        obtain ⟨y', hy', hy'z⟩ := exists_mem_not_mem_zpowers_of_isKleinFour hY hy hy1
        obtain ⟨huL, huy⟩ := mem_inf.mp hu
        have hKx := hAKC x (mem_sup_left hx)
        have hL1 : ⁅K ⊓ C x, Y⁆ ≤ K ⊓ C x :=
          le_normalizer_iff_commutator_le_left.mp (le_sup_right.trans hKx)
        have huKx : u ∈ K ⊓ C x := hL1 (commutator_self_le _ huL)
        have hux : u ∈ O (C x) := hbal.b₁ x hx hx1 (K ⊓ C x) inf_le_right
          (hDodd _ inf_le_left) hKx (mem_sup_right huL)
        have hKy := hAKC y (mem_sup_right hy)
        have huKy : u ∈ K ⊓ C y := mem_inf.mpr ⟨(mem_inf.mp huKx).1, huy⟩
        have huy' : u ∈ O (C y) := hbal.b₂ y hy hy1 (K ⊓ C y) inf_le_right
          (hDodd _ inf_le_left) hKy (mem_sup_left (commutator_mono le_rfl
            ((zpowers_le).mpr hy') (hinvcomm _ inf_le_left huKy (hYinv y' hy' hy'z))))
        exact ⟨⟨(mem_inf.mp huKx).1, hux⟩, huy'⟩
      · intro u hu hXinv
        obtain ⟨x', hx', hx'z⟩ := exists_mem_not_mem_zpowers_of_isKleinFour hX hx hx1
        obtain ⟨huL, hux⟩ := mem_inf.mp hu
        have hKy := hAKC y (mem_sup_right hy)
        have hL1 : ⁅K ⊓ C y, X⁆ ≤ K ⊓ C y :=
          le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans hKy)
        have huKy : u ∈ K ⊓ C y := hL1 (commutator_self_le _ huL)
        have huy : u ∈ O (C y) := hbal.b₂ y hy hy1 (K ⊓ C y) inf_le_right
          (hDodd _ inf_le_left) hKy (mem_sup_right huL)
        have hKx := hAKC x (mem_sup_left hx)
        have huKx : u ∈ K ⊓ C x := mem_inf.mpr ⟨(mem_inf.mp huKy).1, hux⟩
        have hux' : u ∈ O (C x) := hbal.b₁ x hx hx1 (K ⊓ C x) inf_le_right
          (hDodd _ inf_le_left) hKx (mem_sup_left (commutator_mono le_rfl
            ((zpowers_le).mpr hx') (hinvcomm _ inf_le_left huKx (hXinv x' hx' hx'z))))
        exact ⟨⟨(mem_inf.mp huKy).1, hux'⟩, huy⟩)
    (fun p P hp hPp hPK hPA hPgen Q hQP hQA => by
      have hQK : Q ≤ K := hQP.trans hPK
      by_cases hp2 : p = 2
      · subst hp2
        have hPbot : P = ⊥ := by
          rcases hPp.card_eq_or_dvd with h1 | h2
          · exact card_eq_one.mp h1
          · exact absurd (h2.trans (card_dvd_of_le hPK)) (Nat.two_dvd_ne_zero.mpr
              (Nat.odd_iff.mp hKodd))
        have hQbot : Q = ⊥ := le_bot_iff.mp (hPbot ▸ hQP)
        subst hQbot
        exact le_antisymm bot_le (xySup_le' fun _ _ _ _ _ _ => inf_le_left)
      · rw [inf_Kxy_eq hPK] at hPgen
        rw [inf_Kxy_eq hQK]
        exact hbal.c p P hp hp2 hPp hPA hPgen Q hQP hQA)
  have hF := h22 (K ⊓ C b) inf_le_left fun g hg =>
    inf_normalizer_le_normalizer_inf ⟨hKA hg, hAC b hb hg⟩
  rw [hF]
  exact xySup_mono' fun x _ _ y _ _ =>
    le_inf (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans (inf_le_left.trans
      inf_le_right))) (inf_le_right.trans inf_le_right)

end Prop23

end CFSG.GH72
