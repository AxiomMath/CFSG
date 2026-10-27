module

public import CFSG.ClassicalInvolution.RouteD.TypeE8TorGlueNodes
public import CFSG.ClassicalInvolution.RouteD.TypeE8Block
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternExcl

public section

namespace CFSG.ClassicalInvolution.RouteD.ETCtx

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld
open CFSG.ClassicalInvolution.RouteD.Gaps (commutes_symm)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem torusFixedE7_of_node_system (hB1 : TypeE8.E7PairFrame p f)
    (hB5 : TypeE8.E7TorusFixedModel p f) (c : ETCtx p f .E7 0 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeT p f 1 .E7 0 Ω z)
    {j : Fin 7 → Subgroup G} (hj : NodeSystem p f (edgeE 7) Ω K z j)
    (hjimg : ∀ a, locImg Ω z (j a) =
      (rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup a).map c.d.ψ)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (htβ : IsClassicalMember p f β t)
    (hKβ : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β)
    (hβ0 : Commutes β (j 0)) (ht : t * z * t⁻¹ = z) : TorusFixedE7 c ht := by
  classical
  have hΩ := c.hΩ
  have hp : p.Prime := Fact.out
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have hadm : StatedLieAdmissible .E7 0 p f := ⟨hp, Nat.one_le_iff_ne_zero.mpr c.hf, rfl⟩
  obtain ⟨W, hW⟩ := hKβ
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [htβ.orderOf_eq_two, pow_two] at this
  have hKt : conjSub t K = K := Gaps.conjSub_eq_of_standardPair h2 hW htβ.mem htβ.orderOf_eq_two
  have hMz : j 0 ∈ centralizingMembers Ω {z} := hj.mem 0
  obtain ⟨xM, hxM⟩ := hΩ.classical (j 0) hMz.1
  obtain ⟨j', hj', hj'5, hj'6⟩ := c.exists_nodeSystem_E7_of_pair hB1 hsingle hshape hβ htβ ⟨W, hW⟩
    hMz.1 hxM (hj.commK 0) hβ0
  have hKc : ∀ n : Fin 7, n.val ≤ 3 → Commutes K (j' n) := by
    rintro ⟨n, hn7⟩ hn
    have hn' : n ≤ 3 := hn
    have key : ∀ m : Fin 7, (5 : Fin 7) ≠ m → ¬ edgeE 7 5 m → ¬ edgeE 7 m 5 →
        Commutes K (j' m) := fun m h h1 h2' => by
      have := hj'.comm 5 m h h1 h2'
      rwa [hj'5] at this
    interval_cases n
    · exact key 0 (by decide) (by decide) (by decide)
    · exact key 1 (by decide) (by decide) (by decide)
    · exact key 2 (by decide) (by decide) (by decide)
    · exact key 3 (by decide) (by decide) (by decide)
  have hβc : ∀ n : Fin 7, n.val ≤ 3 → Commutes β (j' n) := by
    rintro ⟨n, hn7⟩ hn
    have hn' : n ≤ 3 := hn
    have key : ∀ m : Fin 7, (6 : Fin 7) ≠ m → ¬ edgeE 7 6 m → ¬ edgeE 7 m 6 →
        Commutes β (j' m) := fun m h h1 h2' => by
      have := hj'.comm 6 m h h1 h2'
      rwa [hj'6] at this
    interval_cases n
    · exact key 0 (by decide) (by decide) (by decide)
    · exact key 1 (by decide) (by decide) (by decide)
    · exact key 2 (by decide) (by decide) (by decide)
    · exact key 3 (by decide) (by decide) (by decide)
  have hz : ∀ n : Fin 7, n.val ≤ 3 → j' n ∈ centralizingMembers Ω {z} := fun n hn =>
    mem_centralizingMembers_of_commutes (hj'.mem n).1 c.hz.mem (commutes_symm (hKc n hn))
  have hnbr : ∀ n : Fin 7, n.val ≤ 3 →
      ∃ n' : Fin 7, n'.val ≤ 3 ∧ (edgeE 7 n n' ∨ edgeE 7 n' n) := by
    intro n hn
    fin_cases n <;> first
      | exact ⟨2, by decide, Or.inl (by decide)⟩
      | exact ⟨3, by decide, Or.inl (by decide)⟩
      | exact ⟨2, by decide, Or.inr (by decide)⟩
      | exact absurd hn (by decide)
  have hpair : ∀ a b : Fin 7, (edgeE 7 a b ∨ edgeE 7 b a) →
      ∃ W₁ : Subgroup G, LinearBlockStandardPair (GaloisField p f) W₁ (j' a) (j' b) := by
    rintro a b (h | h)
    · exact hj'.pair a b h
    · obtain ⟨W₁, hW₁⟩ := hj'.pair b a h
      exact ⟨W₁, CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_symm hW₁⟩
  have hlayer : ∀ n : Fin 7, n.val ≤ 3 → IsLayerMember c (j' n) := by
    intro n hn
    obtain ⟨n', hn', hadj⟩ := hnbr n hn
    obtain ⟨W₁, hW₁⟩ := hpair n n' hadj
    exact IsLayerMember.of_not_commutes c (hz n hn) (hz n' hn')
      (ne_of_linearBlockStandardPair hW₁) (not_commutes_of_linearBlockStandardPair hW₁)
  have hex : ∀ n : Fin 7, ∃ R : Subgroup (modelUniv .E7 0 p f Fact.out).K, n.val ≤ 3 →
      R ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 p f Fact.out).D ∧
        locImg Ω z (j' n) = R.map c.d.ψ := by
    intro n
    by_cases hn : n.val ≤ 3
    · obtain ⟨R, hR, hlR⟩ := (hlayer n hn).exists_fund
      exact ⟨R, fun _ => ⟨hR, hlR⟩⟩
    · exact ⟨⊥, fun h => absurd h hn⟩
  choose Rn hRn using hex
  have hcl : ∀ n : Fin 7, ∃ w : G, IsClassicalMember p f (j' n) w := fun n =>
    hΩ.classical _ (hj'.mem n).1
  choose w hw using hcl
  have hrel : ∀ a b : Fin 7, a.val ≤ 3 → b.val ≤ 3 → (edgeE 7 a b ∨ edgeE 7 b a) →
      Gaps.ModelAdj (Subgroup.center (modelUniv .E7 0 p f Fact.out).K) (Rn a) (Rn b) ∧
        ∃ W₁, LinearBlockStandardPair (GaloisField p f) W₁ (Rn a) (Rn b) := by
    intro a b ha hb hab
    obtain ⟨W₁, hW₁⟩ := hpair a b hab
    obtain ⟨hne, hnc, hcw, hnw⟩ := TypeEPattern.stdPair_data h2 (hw a) (hw b) ⟨W₁, hW₁⟩
    refine ⟨c.modelAdj_of_adj (hz a ha) (hz b hb) (hRn a ha).1 (hRn b hb).1 (hRn a ha).2
      (hRn b hb).2 (hw a) (hw b) hne hnc hcw hnw, ?_⟩
    obtain ⟨W₂, hW₂⟩ := Gaps.linearBlockStandardPair_locImg_of_members c.hP1 (hz a ha) (hz b hb) hW₁
    rw [(hRn a ha).2, (hRn b hb).2] at hW₂
    exact TypeEPattern.layerGeom_lift_E7 c.hq c.d.ψ c.d.ker_le (hRn a ha).1 (hRn b hb).1
      ⟨W₂, hW₂⟩
  have hcomm : ∀ a b : Fin 7, a.val ≤ 3 → b.val ≤ 3 → a ≠ b → ¬ edgeE 7 a b → ¬ edgeE 7 b a →
      Commutes (Rn a) (Rn b) := fun a b ha hb hab h1 h2' =>
    (c.commutes_iff_fund (hz a ha) (hz b hb) (hRn a ha).1 (hRn a ha).2 (hRn b hb).2).mp
      (hj'.comm a b hab h1 h2')
  have hl := ModelFacts.isLongestRoot_single .E7 0 p f hp trivial hadm
  have hRM : rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup
      ((0 : Fin 7) : Fin (modelUniv .E7 0 p f Fact.out).D.rank) ∈
      fundamentalSubgroups .E7 (modelUniv .E7 0 p f Fact.out).D :=
    rankOne_mem_fundamental _ (hl _ trivial)
  have hch : ∀ i : Fin 4, ((![0, 2, 3, 1] : Fin 4 → Fin 7) i).val ≤ 3 := by decide
  have hgen := TypeEPattern.range_le_iSup_fund_simplyLaced (p := p) (f := f) (t := .E7) (n := 0)
    trivial hadm (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) c.d.ψ
  have hσ2 := Gaps.locAut_locAut c.hΩ.conjInvariant ht h2t
  have hσr := fun k => c.locAut_mem_range ht h2t hKt hgen k
  obtain ⟨k₀, hk₀, hT⟩ := hB5 (locQuot Ω z) c.d.ψ c.d.ker_le
    (Gaps.locAut c.hΩ.conjInvariant ht) hσ2 hσr (fun i => Rn ((![0, 2, 3, 1] : Fin 4 → Fin 7) i))
    (rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup
      ((0 : Fin 7) : Fin (modelUniv .E7 0 p f Fact.out).D.rank))
    (fun i => (hRn _ (hch i)).1) hRM
    (fun i j h => by
      fin_cases i <;> fin_cases j <;> first
        | exact absurd h (by decide)
        | exact hrel _ _ (by decide) (by decide) (Or.inl (by decide))
        | exact hrel _ _ (by decide) (by decide) (Or.inr (by decide)))
    (fun i j h => by
      fin_cases i <;> fin_cases j <;> first
        | exact absurd h (by decide)
        | exact hcomm _ _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun i => (c.commutes_iff_fund hMz (hz _ (hch i)) hRM (hjimg 0) (hRn _ (hch i)).2).mp
      (hj'.commK _))
    (fun i y hy => c.fixed_of_commutes ht htβ (hz _ (hch i)) (hβc _ (hch i)) (c.d.ψ y) (by
      rw [(hRn _ (hch i)).2]
      exact ⟨y, hy, rfl⟩))
    (fun y hy => c.fixed_of_commutes ht htβ hMz hβ0 (c.d.ψ y) (by
      rw [hjimg 0]
      exact ⟨y, hy, rfl⟩))
  exact ⟨k₀, hk₀, hT⟩

end CFSG.ClassicalInvolution.RouteD.ETCtx
