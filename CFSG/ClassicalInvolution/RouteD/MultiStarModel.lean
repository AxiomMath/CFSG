module

public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectBridge
public import CFSG.ClassicalInvolution.RouteD.MultiD4
public import CFSG.ClassicalInvolution.RouteD.MultiStarWeak

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.NonClassical
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

section Chains

variable {X : Type*} [Group X]

@[expose] def CommFamilyConnected (F : Set (Subgroup X)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, Relation.ReflTransGen
    (fun U V : Subgroup X => U ∈ F ∧ V ∈ F ∧ Commutes U V) A B

@[expose] def LinkedIn (F : Set (Subgroup X)) (R : Subgroup X) : Subgroup X → Subgroup X → Prop :=
  Relation.ReflTransGen
    (fun U V : Subgroup X => U ∈ F ∧ V ∈ F ∧ Commutes U R ∧ Commutes V R ∧ ¬ Commutes U V)


theorem commFamilyConnected_of_stable {M : Type} [Group M] [Finite M] {F : Set (Subgroup M)}
    (hF : ∀ A ∈ F, ∀ g : M, conjSub g A ∈ F) (htrans : ∀ A ∈ F, ∀ B ∈ F, ∃ g : M, B = conjSub g A)
    {X : Set M} (hX : Subgroup.closure X = ⊤) {R₀ : Subgroup M} (hR₀ : R₀ ∈ F)
    (hx : ∀ x ∈ X, conjSub x R₀ = R₀ ∨ ∃ R' ∈ F, Commutes R₀ R' ∧ conjSub x R' = R') :
    CommFamilyConnected F := by
  let r : Subgroup M → Subgroup M → Prop := fun U V => U ∈ F ∧ V ∈ F ∧ Commutes U V
  let D : Set (Subgroup M) := {R | Relation.ReflTransGen r R₀ R}
  have hDF : ∀ R ∈ D, R ∈ F := by
    intro R hR
    have hR' : Relation.ReflTransGen r R₀ R := hR
    induction hR' with
    | refl => exact hR₀
    | tail _ hbc _ => exact hbc.2.1
  have hstab : ∀ x ∈ X, ∀ R ∈ D, conjSub x R ∈ D := by
    intro x hxX R hR
    have h0 : conjSub x R₀ ∈ D := by
      rcases hx x hxX with hfix | ⟨R', hR'F, hcomm, hnorm⟩
      · rw [hfix]
        exact Relation.ReflTransGen.refl
      · have h1 : Relation.ReflTransGen r R₀ R' :=
          Relation.ReflTransGen.single ⟨hR₀, hR'F, hcomm⟩
        have h2 : Commutes (conjSub x R₀) R' := by
          have := (commutes_conjSub_iff x).mpr hcomm
          rwa [hnorm] at this
        exact h1.tail ⟨hR'F, hF R₀ hR₀ x, Gaps.commutes_symm h2⟩
    have hR' : Relation.ReflTransGen r R₀ R := hR
    induction hR' with
    | refl => exact h0
    | @tail b c hb hbc ih =>
      have hbD : b ∈ D := hb
      exact (ih hbD).tail ⟨hF b (hDF b hbD) x, hF c hbc.2.1 x,
        (commutes_conjSub_iff x).mpr hbc.2.2⟩
  have hinv : ∀ g : M, (∀ R ∈ D, conjSub g R ∈ D) → ∀ R ∈ D, conjSub g⁻¹ R ∈ D := by
    intro g hg R hR
    have hbij := (Set.Finite.injOn_iff_bijOn_of_mapsTo (Set.toFinite D)
      (fun A hA => hg A hA)).mp (fun A _ B _ h => conjSub_injective g h)
    obtain ⟨R'', hR'', hR''eq⟩ := hbij.surjOn hR
    rw [← hR''eq, conjSub_inv_conjSub]
    exact hR''
  have hall : ∀ g : M, ∀ R ∈ D, conjSub g R ∈ D := by
    intro g R hR
    have hg : g ∈ Subgroup.closure X := by rw [hX]; exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction generalizing R with
    | mem x hxX => exact hstab x hxX R hR
    | one => rw [conjSub_one]; exact hR
    | mul a b _ _ ha hb =>
      rw [conjSub_mul]
      exact ha _ (hb R hR)
    | inv a _ ha =>
      exact hinv a (fun R' hR' => ha R' hR') R hR
  have hFD : ∀ B ∈ F, B ∈ D := by
    intro B hB
    obtain ⟨g, hg⟩ := htrans R₀ hR₀ B hB
    rw [hg]
    exact hall g R₀ Relation.ReflTransGen.refl
  intro A hA B hB
  have h1 : Relation.ReflTransGen r R₀ A := hFD A hA
  have h2 : Relation.ReflTransGen r R₀ B := hFD B hB
  have hsymm : ∀ {U V : Subgroup M}, Relation.ReflTransGen r U V → Relation.ReflTransGen r V U := by
    intro U V h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, Gaps.commutes_symm hbc.2.2⟩ ih
  exact (hsymm h1).trans h2

end Chains

section Lift

variable [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem members_chain_of_commConnected (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {x}) (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    {i : Fin D.card}
    (hsc : FundamentalSingleClass (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    (hperf : Gaps.FundPerfect (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    (hcc : CommFamilyConnected (Gaps.compFund D i)) :
    ∀ A ∈ Gaps.compMembers Ω x D i, ∀ B ∈ Gaps.compMembers Ω x D i, Relation.ReflTransGen
      (fun U V : Subgroup G => U ∈ Gaps.compMembers Ω x D i ∧ V ∈ Gaps.compMembers Ω x D i ∧
        Commutes U V) A B := by
  intro A hA B hB
  obtain ⟨R_A, hRA⟩ := Gaps.exists_corr_left hΩ hex D hA
  obtain ⟨R_B, hRB⟩ := Gaps.exists_corr_left hΩ hex D hB
  have key : ∀ X, Relation.ReflTransGen
      (fun U V : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K =>
        U ∈ Gaps.compFund D i ∧ V ∈ Gaps.compFund D i ∧ Commutes U V) R_A X →
      ∃ N, Gaps.Corr Ω x D i N X ∧ Relation.ReflTransGen
        (fun U V : Subgroup G => U ∈ Gaps.compMembers Ω x D i ∧
          V ∈ Gaps.compMembers Ω x D i ∧ Commutes U V) A N := by
    intro X hX
    induction hX with
    | refl => exact ⟨A, hRA, Relation.ReflTransGen.refl⟩
    | @tail U V _ huv ih =>
      obtain ⟨N, hN, hlink⟩ := ih
      obtain ⟨N', hN'⟩ := Gaps.exists_corr_right hΩ D hsc huv.2.1
      have hNm : N ∈ Gaps.compMembers Ω x D i := ⟨hN.1, hN.2.2 ▸ Subgroup.map_le_range _ _⟩
      have hN'm : N' ∈ Gaps.compMembers Ω x D i := ⟨hN'.1, hN'.2.2 ▸ Subgroup.map_le_range _ _⟩
      exact ⟨N', hN', hlink.tail ⟨hNm, hN'm,
        (Gaps.corr_commutes hΩ hP1 hperf hN hN').mpr huv.2.2⟩⟩
  obtain ⟨N, hN, hlink⟩ := key R_B (hcc R_A hRA.2.1 R_B hRB.2.1)
  have : N = B := Gaps.corr_unique_right hΩ hP1 hN hRB
  rwa [this] at hlink

theorem linked_of_linkedIn (hΩ : InClass p f Ω) (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) {i : Fin D.card}
    (hsc : FundamentalSingleClass (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    (hperf : Gaps.FundPerfect (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    {K N N' : Subgroup G} {R_K R_N R_N' : Subgroup
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K} {z : G} (hz : z ∈ K)
    (hK : Gaps.Corr Ω x D i K R_K) (hN : Gaps.Corr Ω x D i N R_N)
    (hN' : Gaps.Corr Ω x D i N' R_N') (hlink : LinkedIn (Gaps.compFund D i) R_K R_N R_N') :
    Linked Ω z N N' := by
  have key : ∀ X, LinkedIn (Gaps.compFund D i) R_K R_N X →
      ∃ M, Gaps.Corr Ω x D i M X ∧ Linked Ω z N M := by
    intro X hX
    induction hX with
    | refl => exact ⟨N, hN, Relation.ReflTransGen.refl⟩
    | @tail U V _ huv ih =>
      obtain ⟨M, hM, hlinkM⟩ := ih
      obtain ⟨M', hM'⟩ := Gaps.exists_corr_right hΩ D hsc huv.2.1
      have hMK : Commutes M K := (Gaps.corr_commutes hΩ hP1 hperf hM hK).mpr huv.2.2.1
      have hM'K : Commutes M' K := (Gaps.corr_commutes hΩ hP1 hperf hM' hK).mpr huv.2.2.2.1
      have hMz : M ∈ centralizingMembers Ω {z} :=
        mem_centralizingMembers_of_commutes hM.1.1 hz hMK
      have hM'z : M' ∈ centralizingMembers Ω {z} :=
        mem_centralizingMembers_of_commutes hM'.1.1 hz hM'K
      have hnc : ¬ Commutes M M' := fun hc =>
        huv.2.2.2.2 ((Gaps.corr_commutes hΩ hP1 hperf hM hM').mp hc)
      exact ⟨M', hM', hlinkM.trans (Linked.single ⟨hMz, hM'z, hnc⟩)⟩
  obtain ⟨M, hM, hlinkM⟩ := key R_N' hlink
  have : M = N' := Gaps.corr_unique_right hΩ hP1 hM hN'
  rwa [this] at hlinkM

end Lift


section Nbhd

theorem exists_nc_pair_of_block {Ω : Set (Subgroup G)} {y : G} {A : Subgroup G}
    (h : ∃ B ∈ ncBlock Ω y A, B ≠ A) :
    ∃ b₁ ∈ ncBlock Ω y A, ∃ b₂ ∈ ncBlock Ω y A, b₁ ≠ b₂ ∧ ¬ Commutes b₁ b₂ := by
  obtain ⟨B, hB, hne⟩ := h
  have hB' : Linked Ω y A B := hB
  have key : ∀ C, Linked Ω y A C → C = A ∨ ∃ b₁ b₂, Linked Ω y A b₁ ∧ Linked Ω y A b₂ ∧
      b₁ ≠ b₂ ∧ ¬ Commutes b₁ b₂ := by
    intro C hC
    induction hC with
    | refl => exact Or.inl rfl
    | @tail b c hab hbc ih =>
      by_cases hbc' : b = c
      · subst hbc'
        exact ih
      · exact Or.inr ⟨b, c, hab, hab.tail hbc, hbc', hbc.2.2⟩
  rcases key B hB' with h | ⟨b₁, b₂, h₁, h₂, hne', hnc⟩
  · exact (hne h).elim
  · exact ⟨b₁, h₁, b₂, h₂, hne', hnc⟩

end Nbhd


section MaxBlock

variable [Finite G] [IsSimpleGroup G]

theorem exists_nc_pair_in_block_nbr (hnab : ∃ a b : G, a * b ≠ b * a) {K : Subgroup G} {z : G}
    (h : RouteDSetup p f K z)
    (D : LieSystemData p f (locQuot (conjClass K) z) (locFamily (conjClass K) z))
    {A₀ : Subgroup G} {i₀ i' : Fin D.card} {a₂ q c : Subgroup G}
    (hA₀ : A₀ ∈ centralizingMembers (conjClass K) {z})
    (hblock : ncBlock (conjClass K) z A₀ = Gaps.compMembers (conjClass K) z D i₀)
    (hi₀na : ¬ IsA1Comp D i₀) (hi'na : ¬ IsA1Comp D i') (hi'ne : i' ≠ i₀)
    (ha₂ : a₂ ∈ Gaps.compMembers (conjClass K) z D i')
    (hKc : ∀ B ∈ Gaps.compMembers (conjClass K) z D i₀, Commutes K B ∧ Commutes a₂ B)
    (hqΩ : q ∈ conjClass K)
    (hqcl : ∀ x ∈ conjClass K, (∀ B ∈ Gaps.compMembers (conjClass K) z D i₀, Commutes x B) →
      ¬ Commutes q x)
    (hc : c ∈ Gaps.compMembers (conjClass K) z D i₀) (hqc : Commutes q c) :
    ∃ b₁ ∈ Gaps.compMembers (conjClass K) z D i₀, ∃ b₂ ∈ Gaps.compMembers (conjClass K) z D i₀,
      Commutes c b₁ ∧ Commutes c b₂ ∧ ¬ Commutes b₁ b₂ := by
  have hΩ := h.inClass
  have hex := h.exact
  have hP1 := h.p1
  have hf : 0 < f := pos_of_five_le h.five
  have hcΩ : c ∈ conjClass K := hc.1.1
  have hKz : K ∈ centralizingMembers (conjClass K) {z} :=
    ⟨mem_conjClass_self K, le_centralizer_of_isClassicalMember h.cls⟩
  obtain ⟨g, hg⟩ := single_class K c hcΩ
  have hyc : IsClassicalMember p f c (g * z * g⁻¹) := by
    rw [hg]
    exact h.cls.conj g
  set y : G := g * z * g⁻¹ with hy
  have hP1y : LocalOddCentral (conjClass K) {y} :=
    Balance.localOddCentral_of_classicalMember h.odd hf hΩ
      ⟨K, mem_conjClass_self K, single_class K⟩ (mem_conjClass_self K) h.cls hP1 c hcΩ y hyc
  have hync : ¬ ({y} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    have hyc' : y ∈ Subgroup.center G := hsub rfl
    rw [center_eq_bot hnab, Subgroup.mem_bot] at hyc'
    have h2 := hyc.orderOf_eq_two
    rw [hyc', orderOf_one] at h2
    omega
  obtain ⟨Dy⟩ := NonClassical.exists_lieSystemData h.ih hync
  have hcy : c ∈ centralizingMembers (conjClass K) {y} :=
    ⟨hcΩ, le_centralizer_of_isClassicalMember hyc⟩
  have hcp : ∀ L ∈ centralizingMembers (conjClass K) {y}, L ≠ c → Commutes c L := fun L hL hne =>
    (Gaps.commutes_or_eq_of_involution (Gaps.fundNoncentral p) hΩ hex hP1y Dy hcy hL
      hyc).resolve_right hne
  set V := Gaps.compMembers (conjClass K) z D i₀ with hV
  have hcent : ∀ x ∈ conjClass K, (∀ B ∈ V, Commutes x B) →
      x ∈ centralizingMembers (conjClass K) {y} := by
    intro x hx hxV
    refine ⟨hx, fun u hu => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hxV c hc u hu y hyc.mem
  have hqy : q ∈ centralizingMembers (conjClass K) {y} := by
    refine ⟨hqΩ, fun u hu => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hqc u hu y hyc.mem
  have hblk : ∀ x ∈ conjClass K, (∀ B ∈ V, Commutes x B) → x ∈ ncBlock (conjClass K) y q :=
    fun x hx hxV => Linked.single ⟨hqy, hcent x hx hxV, hqcl x hx hxV⟩
  have hKV : ∀ B ∈ V, Commutes K B := fun B hB => (hKc B hB).1
  have hKy : K ∈ centralizingMembers (conjClass K) {y} := hcent K (mem_conjClass_self K) hKV
  have hKblk : Linked (conjClass K) y q K := hblk K (mem_conjClass_self K) hKV
  have hout : ∀ x' ∈ centralizingMembers (conjClass K) {y}, x' ∉ ncBlock (conjClass K) y q →
      x' ∈ V := by
    intro x' hx'y hx'
    have hx'K : Commutes x' K := by
      by_contra hnc
      exact hx' (hKblk.trans (Linked.single ⟨hKy, hx'y, fun hc' =>
        hnc (Gaps.commutes_symm hc')⟩))
    have hx'z : x' ∈ centralizingMembers (conjClass K) {z} :=
      mem_centralizingMembers_of_commutes hx'y.1 h.cls.mem hx'K
    obtain ⟨j, hj, -⟩ := Gaps.exists_unique_comp hΩ hex D hx'z
    by_cases hji : j = i₀
    · rw [hji] at hj
      exact hj
    · exact absurd (hblk x' hx'y.1 fun B hB => Gaps.commutes_of_ne_comp hΩ hP1 D hji hj hB) hx'
  have hcblock : ∀ w, Linked (conjClass K) y c w → w = c := by
    intro w hw
    induction hw with
    | refl => rfl
    | @tail b d _ hbd ih =>
      rw [ih] at hbd
      by_contra hdc
      exact hbd.2.2 (hcp d hbd.2.1 hdc)
  have hsize : ∀ i : Fin D.card, ¬ IsA1Comp D i →
      1 < (Gaps.compMembers (conjClass K) z D i).ncard := by
    intro i hi
    obtain ⟨N, N', hN, hN', hne⟩ := exists_ne_of_not_isA1Comp hΩ hex hi
    exact (Set.one_lt_ncard (Set.toFinite _)).mpr ⟨N, hN, N', hN', hne⟩
  have hVcard : 1 < V.ncard := hsize i₀ hi₀na
  have hconj : ∀ A ∈ centralizingMembers (conjClass K) {z},
      conjSub g A ∈ centralizingMembers (conjClass K) {y} := by
    intro A hA
    have := centralizingMembers_conj hΩ.conjInvariant g z
    rw [hy, this]
    exact ⟨A, hA, rfl⟩
  have hA'C : conjSub g A₀ ∈ ncBlock (conjClass K) y q := by
    by_contra hA'
    have hA'y := hconj A₀ hA₀
    have hsub : ncBlock (conjClass K) y (conjSub g A₀) ⊆ V := by
      intro w hw
      have hw' : Linked (conjClass K) y (conjSub g A₀) w := hw
      have hwy := hw'.mem_centralizingMembers hA'y
      refine hout w hwy fun hwq => hA' ?_
      exact (show Linked (conjClass K) y q w from hwq).trans hw'.symm
    have hXcard : (ncBlock (conjClass K) y (conjSub g A₀)).ncard = V.ncard := by
      rw [ncard_ncBlock_conj hΩ.conjInvariant g z A₀, hblock]
    have heq : ncBlock (conjClass K) y (conjSub g A₀) = V :=
      Set.eq_of_subset_of_ncard_le hsub hXcard.ge (Set.toFinite _)
    have hcX0 : c ∈ ncBlock (conjClass K) y (conjSub g A₀) := by
      rw [heq]
      exact hc
    have hcX : Linked (conjClass K) y (conjSub g A₀) c := hcX0
    have hAc : conjSub g A₀ = c := hcblock _ hcX.symm
    have h1 : (ncBlock (conjClass K) y (conjSub g A₀)).ncard ≤ 1 := by
      rw [Set.ncard_le_one_iff (Set.toFinite _)]
      intro a b ha hb
      have ha' : Linked (conjClass K) y c a := by rw [← hAc]; exact ha
      have hb' : Linked (conjClass K) y c b := by rw [← hAc]; exact hb
      rw [hcblock a ha', hcblock b hb']
    omega
  have hXVC : ncBlock (conjClass K) y (conjSub g A₀) = ncBlock (conjClass K) y q := by
    ext w
    have h1 : Linked (conjClass K) y q (conjSub g A₀) := hA'C
    constructor
    · intro hw
      exact h1.trans hw
    · intro hw
      exact h1.symm.trans hw
  have hblock' : ncBlock (conjClass K) z a₂ = Gaps.compMembers (conjClass K) z D i' := by
    ext B
    exact linked_iff_mem_compMembers hΩ hex hP1 ha₂
  have hA''y := hconj a₂ ha₂.1
  have hA''C : conjSub g a₂ ∉ ncBlock (conjClass K) y q := by
    intro hA''
    have h2 : ncBlock (conjClass K) y (conjSub g a₂) =
        ncBlock (conjClass K) y (conjSub g A₀) := by
      rw [hXVC]
      ext w
      have h1 : Linked (conjClass K) y q (conjSub g a₂) := hA''
      constructor
      · intro hw
        exact h1.trans hw
      · intro hw
        exact h1.symm.trans hw
    rw [ncBlock_conj hΩ.conjInvariant, ncBlock_conj hΩ.conjInvariant] at h2
    have h3 : ncBlock (conjClass K) z a₂ = ncBlock (conjClass K) z A₀ :=
      Set.image_injective.mpr (conjSub_injective g) h2
    have h4 : a₂ ∈ V := by
      rw [← hblock, ← h3]
      exact Relation.ReflTransGen.refl
    exact hi'ne (Gaps.eq_of_locImg_le_range hΩ hex D ha₂.1 ha₂.2 h4.2)
  have hsubV' : ncBlock (conjClass K) y (conjSub g a₂) ⊆ V := by
    intro w hw
    have hw' : Linked (conjClass K) y (conjSub g a₂) w := hw
    have hwy := hw'.mem_centralizingMembers hA''y
    refine hout w hwy fun hwq => hA''C ?_
    exact (show Linked (conjClass K) y q w from hwq).trans hw'.symm
  have hV'card : 1 < (ncBlock (conjClass K) y (conjSub g a₂)).ncard := by
    rw [ncard_ncBlock_conj hΩ.conjInvariant g z a₂, hblock']
    exact hsize i' hi'na
  obtain ⟨B₁, hB₁, B₂, hB₂, hne⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp hV'card
  obtain ⟨B, hB, hBne⟩ : ∃ B ∈ ncBlock (conjClass K) y (conjSub g a₂), B ≠ conjSub g a₂ := by
    by_cases h1 : B₁ = conjSub g a₂
    · exact ⟨B₂, hB₂, fun h2 => hne (h1.trans h2.symm)⟩
    · exact ⟨B₁, hB₁, h1⟩
  obtain ⟨b₁, hb₁, b₂, hb₂, hbne, hbnc⟩ := exists_nc_pair_of_block ⟨B, hB, hBne⟩
  have hbc : ∀ b ∈ ncBlock (conjClass K) y (conjSub g a₂), b ≠ c := by
    intro b hb hbc
    have hb' : Linked (conjClass K) y (conjSub g a₂) c := by rw [← hbc]; exact hb
    have hAc : conjSub g a₂ = c := hcblock _ hb'.symm
    have h1 : (ncBlock (conjClass K) y (conjSub g a₂)).ncard ≤ 1 := by
      rw [Set.ncard_le_one_iff (Set.toFinite _)]
      intro a b ha hb
      have ha' : Linked (conjClass K) y c a := by rw [← hAc]; exact ha
      have hb' : Linked (conjClass K) y c b := by rw [← hAc]; exact hb
      rw [hcblock a ha', hcblock b hb']
    omega
  exact ⟨b₁, hsubV' hb₁, b₂, hsubV' hb₂,
    hcp b₁ (hb₁.mem_centralizingMembers hA''y) (hbc b₁ hb₁),
    hcp b₂ (hb₂.mem_centralizingMembers hA''y) (hbc b₂ hb₂), hbnc⟩

end MaxBlock


section Reduction

abbrev ModelFund (p : ℕ) [Fact p.Prime] (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n e : ℕ) :
    Set (Subgroup (modelUniv t n p e Fact.out).K) :=
  fundamentalSubgroups t (modelUniv t n p e Fact.out).D

@[expose] def ModelConnFact (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n e : ℕ), IsFundTag t →
    StatedLieAdmissible t n p e → p ≠ 2 → 5 ≤ p ^ e → t ≠ .G2 → t ≠ .trialityD4 →
    ∀ R ∈ ModelFund p t n e, ∀ R₁ ∈ ModelFund p t n e, ∀ R₂ ∈ ModelFund p t n e,
      Commutes R R₁ → Commutes R R₂ → ¬ Commutes R₁ R₂ → CommFamilyConnected (ModelFund p t n e)

@[expose] def ModelStarFact (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n e : ℕ), IsFundTag t →
    StatedLieAdmissible t n p e → p ≠ 2 → 5 ≤ p ^ e → t ≠ .G2 → t ≠ .trialityD4 →
    ∀ R ∈ ModelFund p t n e, ∀ R₁ ∈ ModelFund p t n e, ∀ R₂ ∈ ModelFund p t n e,
      ∀ R_q ∈ ModelFund p t n e, Commutes R R₁ → Commutes R R₂ → Commutes R₁ R₂ →
      ¬ LinkedIn (ModelFund p t n e) R R₁ R₂ → ¬ Commutes R_q R → ¬ Commutes R_q R₁ →
      ¬ Commutes R_q R₂ →
        ∃ R_β ∈ ModelFund p t n e, ∃ R₁' ∈ ModelFund p t n e, ∃ R₂' ∈ ModelFund p t n e,
          LinkedIn (ModelFund p t n e) R R₁ R₁' ∧ LinkedIn (ModelFund p t n e) R R₂ R₂' ∧
          (∃ W, LinearBlockStandardPair (GaloisField p e) W R R_β) ∧
          (∃ W, LinearBlockStandardPair (GaloisField p e) W R₁' R_β) ∧
          (∃ W, LinearBlockStandardPair (GaloisField p e) W R₂' R_β)

@[expose] def NoG2D4 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      ∀ (L : Subgroup G) (w : G), L ∈ conjClass K → IsClassicalMember p f L w →
        ∀ D : LieSystemData p f (locQuot (conjClass K) w) (locFamily (conjClass K) w),
          ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4

theorem linearBlockStandardPair_congr_field {X : Type} [Group X] {e e' : ℕ} (hee : e = e')
    {W U V : Subgroup X} (h : LinearBlockStandardPair (GaloisField p e) W U V) :
    LinearBlockStandardPair (GaloisField p e') W U V := by
  subst hee
  exact h


theorem multiStar_of_modelFacts (hconn : ModelConnFact p) (hstar : ModelStarFact p)
    (hno : NoG2D4 p f) : MultiStar p f := by
  intro G _ _ _ hnab K z h D hmulti
  have hΩ := h.inClass
  have hex := h.exact
  have hP1 := h.p1
  have hf : 0 < f := pos_of_five_le h.five
  have hq4 : 4 ≤ p ^ f := by have := h.five; omega
  obtain ⟨A₀, i₀, i', a₂, hA₀, hmax, hblock, hi₀na, hi'na, hi'ne, ha₂, hKV, hKc, hKa₂⟩ :=
    exists_maximal_block h D hmulti
  have hne : ∀ L ∈ conjClass K, L ≠ ⊥ := by
    intro L hL hbot
    obtain ⟨w, hw⟩ := hΩ.classical L hL
    have := hw.mem
    rw [hbot, Subgroup.mem_bot] at this
    have h2 := hw.orderOf_eq_two
    rw [this, orderOf_one] at h2
    omega
  have hconn' : ∀ X ∈ conjClass K, ∀ Y ∈ conjClass K, Relation.ReflTransGen
      (fun A B : Subgroup G => A ∈ conjClass K ∧ B ∈ conjClass K ∧ Commutes A B) X Y := by
    intro X hX Y hY
    have hreach := h.conn.preconnected ⟨X, hX⟩ ⟨Y, hY⟩
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    have key : ∀ v : conjClass K, Relation.ReflTransGen
        (CFSG.ClassicalInvolution.Models.commGraph (conjClass K)).Adj ⟨X, hX⟩ v →
        Relation.ReflTransGen
          (fun A B : Subgroup G => A ∈ conjClass K ∧ B ∈ conjClass K ∧ Commutes A B) X
          (v : Subgroup G) := by
      intro v hv
      induction hv with
      | refl => exact Relation.ReflTransGen.refl
      | @tail b c _ hbc ih =>
        exact ih.tail ⟨b.2, c.2, (CFSG.ClassicalInvolution.Models.commGraph_adj.mp hbc).2⟩
    exact key ⟨Y, hY⟩ hreach
  obtain ⟨q, hqΩ, hqV, ⟨a₁₀, ha₁₀V, hqa₁₀⟩, ⟨c₀, hc₀V, hqc₀⟩, hqK, hqcl⟩ :=
    exists_not_commuting_nbr_of_max hnab hΩ.conjInvariant hΩ.generated hne (mem_conjClass_self K)
      h.cls.mem (single_class K) hconn' hA₀ hmax (hblock ▸ hKV)
      (fun B hB => (hKc B (hblock ▸ hB)).1)
  rw [hblock] at ha₁₀V hc₀V hqcl
  obtain ⟨b₁, hb₁, b₂, hb₂, hcb₁, hcb₂, hb₁₂⟩ :=
    exists_nc_pair_in_block_nbr hnab h D hA₀ hblock hi₀na hi'na hi'ne ha₂ hKc hqΩ hqcl hc₀V hqc₀
  have hD0 := hno G hnab K z h K z (mem_conjClass_self K) h.cls D
  have hsc₀ := Gaps.fundamentalSingleClass_of_ne D i₀ (hD0 i₀).1 (hD0 i₀).2
  have hperf₀ : Gaps.FundPerfect (D.tag i₀)
      (modelUniv (D.tag i₀) (D.rank i₀) p (D.exp i₀) Fact.out).D :=
    D.fundPerfect h.odd hq4 (fun i hi => absurd hi (hD0 i).2) i₀
  have hexp₀ : D.exp i₀ = f :=
    (D.exp_eq i₀).resolve_right (fun hh => (hD0 i₀).2 hh.1)
  obtain ⟨R_c, hRc⟩ := Gaps.exists_corr_left hΩ hex D hc₀V
  obtain ⟨R_b₁, hRb₁⟩ := Gaps.exists_corr_left hΩ hex D hb₁
  obtain ⟨R_b₂, hRb₂⟩ := Gaps.exists_corr_left hΩ hex D hb₂
  have hcc : CommFamilyConnected (Gaps.compFund D i₀) :=
    hconn (D.tag i₀) (D.rank i₀) (D.exp i₀) (D.isFundTag i₀) (D.admissible i₀) h.odd
      (by rw [hexp₀]; exact h.five) (hD0 i₀).1 (hD0 i₀).2 R_c hRc.2.1 R_b₁ hRb₁.2.1 R_b₂ hRb₂.2.1
      ((Gaps.corr_commutes hΩ hP1 hperf₀ hRc hRb₁).mp hcb₁)
      ((Gaps.corr_commutes hΩ hP1 hperf₀ hRc hRb₂).mp hcb₂)
      (fun hc => hb₁₂ ((Gaps.corr_commutes hΩ hP1 hperf₀ hRb₁ hRb₂).mpr hc))
  have hconnV := members_chain_of_commConnected hΩ hex hP1 D hsc₀ hperf₀ hcc
  obtain ⟨c, hcV, a₁, ha₁V, hca₁, hqc, hqa₁⟩ :=
    exists_commuting_pair_of_chain hconnV hc₀V hqc₀ ha₁₀V hqa₁₀
  have hcΩ : c ∈ conjClass K := hcV.1.1
  obtain ⟨y, hyc⟩ := hΩ.classical c hcΩ
  have hP1y : LocalOddCentral (conjClass K) {y} :=
    Balance.localOddCentral_of_classicalMember h.odd hf hΩ
      ⟨K, mem_conjClass_self K, single_class K⟩ (mem_conjClass_self K) h.cls hP1 c hcΩ y hyc
  have hync : ¬ ({y} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    have hyc' : y ∈ Subgroup.center G := hsub rfl
    rw [center_eq_bot hnab, Subgroup.mem_bot] at hyc'
    have h2 := hyc.orderOf_eq_two
    rw [hyc', orderOf_one] at h2
    omega
  obtain ⟨Dy⟩ := NonClassical.exists_lieSystemData h.ih hync
  have hKa₁ : Commutes K a₁ := (hKc a₁ ha₁V).1
  have ha₁a₂ : Commutes a₁ a₂ := Gaps.commutes_symm (hKc a₁ ha₁V).2
  have hKy : K ∈ centralizingMembers (conjClass K) {y} :=
    mem_centralizingMembers_of_commutes (mem_conjClass_self K) hyc.mem (hKc c hcV).1
  have ha₁y : a₁ ∈ centralizingMembers (conjClass K) {y} :=
    mem_centralizingMembers_of_commutes ha₁V.1.1 hyc.mem (Gaps.commutes_symm hca₁)
  have ha₂y : a₂ ∈ centralizingMembers (conjClass K) {y} :=
    mem_centralizingMembers_of_commutes ha₂.1.1 hyc.mem (hKc c hcV).2
  have hqy : q ∈ centralizingMembers (conjClass K) {y} :=
    mem_centralizingMembers_of_commutes hqΩ hyc.mem hqc
  have hqa₂ : ¬ Commutes q a₂ := hqcl a₂ ha₂.1.1 (fun B hB => (hKc B hB).2)
  obtain ⟨iq, hq_iq, -⟩ := Gaps.exists_unique_comp hΩ hex Dy hqy
  have hsame : ∀ {N : Subgroup G}, N ∈ centralizingMembers (conjClass K) {y} → ¬ Commutes q N →
      N ∈ Gaps.compMembers (conjClass K) y Dy iq := by
    intro N hN hnc
    obtain ⟨j, hj, -⟩ := Gaps.exists_unique_comp hΩ hex Dy hN
    have := NonClassical.eq_of_not_commutes hΩ hP1y Dy hq_iq hj hnc
    rw [this]
    exact hj
  have hK_iq := hsame hKy hqK
  have ha₁_iq := hsame ha₁y hqa₁
  have ha₂_iq := hsame ha₂y hqa₂
  have hDy := hno G hnab K z h c y hcΩ hyc Dy
  have hsc := Gaps.fundamentalSingleClass_of_ne Dy iq (hDy iq).1 (hDy iq).2
  have hperf : Gaps.FundPerfect (Dy.tag iq)
      (modelUniv (Dy.tag iq) (Dy.rank iq) p (Dy.exp iq) Fact.out).D :=
    Dy.fundPerfect h.odd hq4 (fun i hi => absurd hi (hDy i).2) iq
  have hexp : Dy.exp iq = f := (Dy.exp_eq iq).resolve_right (fun hh => (hDy iq).2 hh.1)
  obtain ⟨R_K, hRK⟩ := Gaps.exists_corr_left hΩ hex Dy hK_iq
  obtain ⟨R_a₁, hRa₁⟩ := Gaps.exists_corr_left hΩ hex Dy ha₁_iq
  obtain ⟨R_a₂, hRa₂⟩ := Gaps.exists_corr_left hΩ hex Dy ha₂_iq
  obtain ⟨R_q, hRq⟩ := Gaps.exists_corr_left hΩ hex Dy hq_iq
  have hnlink : ¬ LinkedIn (Gaps.compFund Dy iq) R_K R_a₁ R_a₂ := by
    intro hlink
    have hl := linked_of_linkedIn hΩ hP1y Dy hsc hperf h.cls.mem hRK hRa₁ hRa₂ hlink
    have ha₂V : a₂ ∈ Gaps.compMembers (conjClass K) z D i₀ :=
      (linked_iff_mem_compMembers hΩ hex hP1 ha₁V).mp hl
    exact hi'ne (Gaps.eq_of_locImg_le_range hΩ hex D ha₂.1 ha₂.2 ha₂V.2)
  obtain ⟨R_β, hRβF, R₁', hR₁'F, R₂', hR₂'F, hl₁, hl₂, hp₀, hp₁, hp₂⟩ :=
    hstar (Dy.tag iq) (Dy.rank iq) (Dy.exp iq) (Dy.isFundTag iq) (Dy.admissible iq) h.odd
      (by rw [hexp]; exact h.five) (hDy iq).1 (hDy iq).2 R_K hRK.2.1 R_a₁ hRa₁.2.1 R_a₂ hRa₂.2.1
      R_q hRq.2.1 ((Gaps.corr_commutes hΩ hP1y hperf hRK hRa₁).mp hKa₁)
      ((Gaps.corr_commutes hΩ hP1y hperf hRK hRa₂).mp hKa₂)
      ((Gaps.corr_commutes hΩ hP1y hperf hRa₁ hRa₂).mp ha₁a₂) hnlink
      (fun hc => hqK ((Gaps.corr_commutes hΩ hP1y hperf hRq hRK).mpr hc))
      (fun hc => hqa₁ ((Gaps.corr_commutes hΩ hP1y hperf hRq hRa₁).mpr hc))
      (fun hc => hqa₂ ((Gaps.corr_commutes hΩ hP1y hperf hRq hRa₂).mpr hc))
  obtain ⟨β, hβ⟩ := Gaps.exists_corr_right hΩ Dy hsc hRβF
  obtain ⟨a₁', ha₁'⟩ := Gaps.exists_corr_right hΩ Dy hsc hR₁'F
  obtain ⟨a₂', ha₂'⟩ := Gaps.exists_corr_right hΩ Dy hsc hR₂'F
  have ha₁'V : a₁' ∈ Gaps.compMembers (conjClass K) z D i₀ :=
    (linked_iff_mem_compMembers hΩ hex hP1 ha₁V).mp
      (linked_of_linkedIn hΩ hP1y Dy hsc hperf h.cls.mem hRK hRa₁ ha₁' hl₁)
  have ha₂'V : a₂' ∈ Gaps.compMembers (conjClass K) z D i' :=
    (linked_iff_mem_compMembers hΩ hex hP1 ha₂).mp
      (linked_of_linkedIn hΩ hP1y Dy hsc hperf h.cls.mem hRK hRa₂ ha₂' hl₂)
  have hstd : ∀ {N : Subgroup G} {R_N : Subgroup
      (modelUniv (Dy.tag iq) (Dy.rank iq) p (Dy.exp iq) Fact.out).K},
      Gaps.Corr (conjClass K) y Dy iq N R_N →
      (∃ W, LinearBlockStandardPair (GaloisField p (Dy.exp iq)) W R_N R_β) →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W N β := by
    intro N R_N hN hpair
    obtain ⟨W, hW⟩ := hpair
    exact NonClassical.linearBlockStandardPair_of_corr h.five hΩ hP1y hN hβ
      ⟨W, linearBlockStandardPair_congr_field hexp hW⟩
  exact ⟨i₀, i', a₁', a₂', β, fun e => hi'ne e.symm, hi₀na, hi'na, ha₁'V, ha₂'V, hβ.1.1,
    hstd hRK hp₀, hstd ha₁' hp₁, hstd ha₂' hp₂⟩

theorem multiPiece_of_modelFacts (hconn : ModelConnFact p) (hstar : ModelStarFact p)
    (hno : NoG2D4 p f) : MultiPiece p f :=
  multiPiece_of_multiStar (multiStar_of_modelFacts hconn hstar hno)

@[expose] def MultiModelFacts (p f : ℕ) [Fact p.Prime] : Prop :=
  ModelConnFact p ∧ ModelStarFact p ∧ NoG2D4 p f

theorem multiPiece_of_multiModelFacts (h : MultiModelFacts p f) : MultiPiece p f :=
  multiPiece_of_modelFacts h.1 h.2.1 h.2.2

end Reduction

end CFSG.ClassicalInvolution.RouteD
