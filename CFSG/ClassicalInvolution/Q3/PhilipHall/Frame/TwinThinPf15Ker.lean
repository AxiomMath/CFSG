module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf15Pair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf13Abel
public import CFSG.ClassicalInvolution.Q3.TL4AECoverM
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Final

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThinPf15

open CFSG.ClassicalInvolution.Q3.AE

theorem memBar_inj {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8) {α β : Finset (Fin n)} {h : α.card = 4}
    {hβ : β.card = 4} {b c : Bool} (he : memBar β hβ c = memBar α h b) : β = α ∧ c = b := by
  have hz : zBar β hβ ∈ memBar α h b := he ▸ zBar_mem_memBar β hβ c
  rcases eq_of_mem_memBar_mul_self hn hz (zBar_mul_self β hβ) with h1 | h1
  · exact absurd h1 (zBar_ne_one hn β hβ)
  · have hβα : β = α := eq_of_zBar_eq hn8 h1
    subst hβα
    refine ⟨rfl, ?_⟩
    by_contra hcb
    have : c = !b := by cases b <;> cases c <;> simp_all
    subst this
    exact memBar_ne_not hn β h b he.symm

end TwinThinPf15

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem twin_label_conj {m : ℕ} (hm : 5 ≤ m) (hm8 : m ≠ 8)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) {a : G} (ha : a ∈ conjSub g (piGen π)) :
    ∃ (β : Finset (Fin m)) (hβ : β.card = 4) (c : Bool),
      ((conjSub a K).subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ =
        AE.memBar β hβ c ∧
      ((conjSub a K').subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ =
        AE.memBar β hβ (!c) := by
  obtain ⟨α, h, b, hlab⟩ := J.label K S.mem_fam_self
  have hlab' := S.map_twin_eq hm hm8 J hlab
  have hap : a ∈ pSpan (fam K (conjSub g (piGen π))) := by rw [S.fam_gen]; exact ha
  have e1 := TL4.AECov.map_conjSub_eq J K ⟨a, hap⟩
  have e2 := TL4.AECov.map_conjSub_eq J K' ⟨a, hap⟩
  rw [hlab] at e1
  rw [hlab'] at e2
  have hx : J.φ ⟨a, hap⟩ ∈ TwinThinPf8.Hn m := by
    have : J.φ ⟨a, hap⟩ ∈ J.φ.range := ⟨_, rfl⟩
    rw [J.range_eq] at this
    exact this
  obtain ⟨β, hβ, c, h1, h2⟩ := TwinThinPf15.pairPres_of_mem hm hx α h b
  exact ⟨β, hβ, c, e1.trans h1, e2.trans h2⟩

theorem aeCoverHyp {m : ℕ} (hm : 5 ≤ m) (hm8 : m ≠ 8)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) : TL4.AECoverHyp J := by
  have hlinj : ∀ L ∈ fam K (conjSub g (piGen π)), ∀ L' ∈ fam K (conjSub g (piGen π)),
      (L.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ =
        (L'.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ → L = L' :=
    fun L hL L' hL' he => S.eq_of_map_le hm J hL hL' (le_of_eq he)
  have key : ∀ (α : Finset (Fin m)) (h : α.card = 4) (L L' : Subgroup G),
      L ∈ fam K (conjSub g (piGen π)) → L' ∈ fam K (conjSub g (piGen π)) →
      (L.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h true →
      (L'.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h false →
      ∃ a : G, a ∈ conjSub g (piGen π) ∧ L = conjSub a K ∧ L' = conjSub a K' := by
    intro α h L L' hL hL' hl hl'
    obtain ⟨⟨a, ha⟩, rfl⟩ := hL
    obtain ⟨β, hβ, c, h1, h2⟩ := S.twin_label_conj hm hm8 J ha
    rw [hl] at h1
    obtain ⟨rfl, rfl⟩ := TwinThinPf15.memBar_inj hm hm8 h1.symm
    refine ⟨a, ha, rfl, ?_⟩
    have hK'a : conjSub a K' ∈ fam K (conjSub g (piGen π)) := fam_inv K' S.twin_mem_fam a ha
    exact hlinj L' hL' _ hK'a (by rw [hl', h2]; rfl)
  exact
    { ker_two := J.isPGroup_ker S.hOdd
      card := fun L hL => S.card8 L (S.fam_mem hL)
      conj_mem := fun L hL x hx => fam_inv L hL x (by rwa [S.fam_gen] at hx)
      label_inj := hlinj
      twin_comm := fun α h L hL L' hL' hl hl' x hx y hy => by
        obtain ⟨a, ha, rfl, rfl⟩ := key α h L L' hL hL' hl hl'
        have hx' := mem_conjSub_iff.mp hx
        have hy' := mem_conjSub_iff.mp hy
        have hc := OddQuot.commutes_of_twin_pgroup S.hs.hyp S.hs.two S.hK S.hK'.1 S.hne.symm S.hz
          S.hz' _ hx' _ hy'
        calc x * y = a * ((a⁻¹ * x * a) * (a⁻¹ * y * a)) * a⁻¹ := by group
          _ = a * ((a⁻¹ * y * a) * (a⁻¹ * x * a)) * a⁻¹ := by rw [hc]
          _ = y * x := by group
      twin_z := fun α h L hL L' hL' hl hl' u u' hu hu' => by
        obtain ⟨a, ha, rfl, rfl⟩ := key α h L L' hL hL' hl hl'
        rw [← (S.hz.conj a).eq hu, ← (S.hz'.conj a).eq hu'] }

theorem ker_eq_bot_of_odd {m : ℕ} (hm : 5 ≤ m) (hm8 : m ≠ 8) (hodd : m % 2 = 1)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) : J.φ.ker = ⊥ :=
  TL4.aeCoverOddKer_proved G _ m J hm (Nat.odd_iff.mpr hodd) (S.aeCoverHyp hm hm8 J)

theorem twelve_eight_small' (h117 : TL4.Model117) {n : ℕ} (hn5 : 5 ≤ n) (hn7 : n ≤ 7)
    (J : AEIdent (fam K (conjSub g (piGen π))) n) {α : Finset (Fin n)} {h : α.card = 4}
    {b : Bool}
    (hlab : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h b) :
    betaOf (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) π = {K, K'} ∧
      ∃ y : ↥(pSpan (fam K (conjSub g (piGen π)))), J.φ y = AE.yBar α h ∧
        (∃ a : ℕ, y ^ 3 ^ a = 1) ∧ (y : G) * z = z * (y : G) ∧
        ∀ x ∈ piGen π, (y : G) * x = x * (y : G) :=
  S.twelve_eight_small h117 hn5 hn7 J hlab
    (fun h7 => S.ker_eq_bot_of_odd hn5 (by omega) (by omega) J)

end Setting

theorem thinKerOddN (IH : Prop) :
    IH → ∀ (G : Type) [Group G] [Finite G] (K₀ K K' : Subgroup G) (z : G) (π : Set (Subgroup G))
      (g : G), Setting K₀ K K' z π g → IsSimpleGroup ↥(genFittingFStar G) →
        (∃ a b : ↥(genFittingFStar G), a * b ≠ b * a) →
        ∀ m : ℕ, 5 ≤ m → m % 2 = 1 → ∀ J : AEIdent (fam K (conjSub g (piGen π))) m, J.φ.ker = ⊥ :=
  fun _ G _ _ _ K K' z π g S _ _ m hm hmodd J =>
    TL4.aeCoverOddKer_proved G _ m J hm (Nat.odd_iff.mpr hmodd)
      (S.aeCoverHyp hm (by omega) J)

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
