module

public import CFSG.ClassicalInvolution.Q3.TL3C4

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Graph

open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {A : Subgroup G → Subgroup G → Prop}
variable {Ω : Set (Subgroup G)} (hF : GraphFam Ω A)
include hF

theorem orbOf_eq_of_ne_maxOrbs {K : Subgroup G} {P P' : Set (Subgroup G)}
    (hP : P ∈ maxOrbs A K) (hP' : P' ∈ maxOrbs A K) (hne : P ≠ P') {J L : Subgroup G}
    (hJ : J ∈ P) (hL : L ∈ P') : orbOf A J K = orbOf A L K := by
  have hKJ : A K J := adj_of_mem_isMaxOrb hF hP hJ
  have hKL : A K L := adj_of_mem_isMaxOrb hF hP' hL
  have hPJ : orbOf A K J = P := orbOf_eq_of_mem_isMaxOrb hP hJ
  have hP'L : orbOf A K L = P' := orbOf_eq_of_mem_isMaxOrb hP' hL
  have hLJ : L ∉ orbOf A K J := by
    intro h
    apply hne
    rw [← hPJ, ← orbOf_eq_of_mem h, hP'L]
  have hJL : A J L := hF.graph.sep hKJ hKL hLJ
  have hP'J : P' ∈ maxOrbs A J := mem_maxOrbs_of_ne hF hKJ hP' (by rw [hPJ]; exact hne.symm)
  have hJLo : orbOf A J L = P' := orbOf_eq_of_mem_isMaxOrb hP'J hL
  have hML := maxOrbs_eq_insert hF hJL (by rw [hJLo]; exact hP'J)
  have hQJ : orbOf A J K ∈ maxOrbs A J := orbOf_mem_maxOrbs hF hKJ (by rw [hPJ]; exact hP)
  have hQne : orbOf A J K ≠ orbOf A J L := by
    intro h
    have : K ∈ orbOf A J L := h ▸ mem_orbOf_self J K
    rw [hJLo] at this
    exact not_mem_of_isMaxOrb hF hP' this
  have hQL : orbOf A J K ∈ maxOrbs A L := by
    rw [hML]
    exact Set.mem_insert_of_mem _ ⟨hQJ, hQne⟩
  rw [maxOrbs_eq_insert hF hKL (by rw [hP'L]; exact hP')] at hQL
  rcases hQL with h | h
  · exact h
  · exact absurd h.1 (orbOf_not_mem_maxOrbs hF K J)

theorem maxOrb_unique {K₀ : Subgroup G} (hK₀ : K₀ ∈ Ω) {P₁ P₂ : Set (Subgroup G)}
    (hP₁ : P₁ ∈ maxOrbs A K₀) (hP₂ : P₂ ∈ maxOrbs A K₀) : P₁ = P₂ := by
  by_contra hne
  obtain ⟨⟨J₁, hKJ₁, hJ₁P⟩, -⟩ := id hP₁
  obtain ⟨⟨J₂, hKJ₂, hJ₂P⟩, -⟩ := id hP₂
  have hJ₁ : J₁ ∈ P₁ := hJ₁P ▸ mem_orbOf_self K₀ J₁
  have hJ₂ : J₂ ∈ P₂ := hJ₂P ▸ mem_orbOf_self K₀ J₂
  set Q : Set (Subgroup G) := orbOf A J₁ K₀ with hQdef
  have hQ : ∀ P ∈ maxOrbs A K₀, ∀ J ∈ P, orbOf A J K₀ = Q := by
    intro P hP J hJ
    by_cases hPP : P = P₁
    · subst hPP
      rw [orbOf_eq_of_ne_maxOrbs hF hP hP₂ hne hJ hJ₂,
        ← orbOf_eq_of_ne_maxOrbs hF hP hP₂ hne hJ₁ hJ₂]
    · exact orbOf_eq_of_ne_maxOrbs hF hP hP₁ hPP hJ hJ₁
  have hQmax : ∀ P ∈ maxOrbs A K₀, ∀ J ∈ P, Q ∈ maxOrbs A J := by
    intro P hP J hJ
    rw [← hQ P hP J hJ]
    exact orbOf_mem_maxOrbs hF (adj_of_mem_isMaxOrb hF hP hJ)
      (by rw [orbOf_eq_of_mem_isMaxOrb hP hJ]; exact hP)
  have hK₀Q : K₀ ∈ Q := mem_orbOf_self J₁ K₀
  have hQnot : Q ∉ maxOrbs A K₀ := fun h => not_mem_of_isMaxOrb hF h hK₀Q
  have hd : ∀ K' ∈ Q, maxOrbs A K' = maxOrbs A K₀ := by
    intro K' hK'
    have hK'Ω : K' ∈ Ω := by
      have h1 : A J₁ K' := adj_of_mem_orbOf hF.graph (hF.graph.symm hKJ₁) hK'
      exact hF.mem (hF.graph.symm h1)
    have hsub : maxOrbs A K₀ ⊆ maxOrbs A K' := by
      intro P hP
      have key : ∀ (Pi : Set (Subgroup G)) (hPi : Pi ∈ maxOrbs A K₀) (Ji : Subgroup G)
          (hJi : Ji ∈ Pi), P ≠ Pi → P ∈ maxOrbs A K' := by
        intro Pi hPi Ji hJi hPne
        have hKJi : A K₀ Ji := adj_of_mem_isMaxOrb hF hPi hJi
        have hPiJ : orbOf A K₀ Ji = Pi := orbOf_eq_of_mem_isMaxOrb hPi hJi
        have hPJi : P ∈ maxOrbs A Ji := mem_maxOrbs_of_ne hF hKJi hP (by rw [hPiJ]; exact hPne)
        have hQi : orbOf A Ji K₀ = Q := hQ Pi hPi Ji hJi
        have hJiK' : A Ji K' :=
          adj_of_mem_orbOf hF.graph (hF.graph.symm hKJi) (by rw [hQi]; exact hK')
        have hoK' : orbOf A Ji K' = Q := by
          rw [orbOf_eq_of_mem (by rw [hQi]; exact hK' : K' ∈ orbOf A Ji K₀), hQi]
        refine mem_maxOrbs_of_ne hF hJiK' hPJi ?_
        rw [hoK']
        intro h
        exact hQnot (h ▸ hP)
      by_cases h1 : P = P₁
      · exact key P₂ hP₂ J₂ hJ₂ (by rw [h1]; exact hne)
      · exact key P₁ hP₁ J₁ hJ₁ h1
    exact (Set.eq_of_subset_of_ncard_le hsub (ncard_maxOrbs_eq hF hK₀ hK'Ω).le
      (Set.toFinite _)).symm
  have hdisj : ∀ P ∈ maxOrbs A K₀, ∀ M, M ∈ Q → M ∉ P := by
    intro P hP M hMQ hMP
    have h1 : P ∈ maxOrbs A M := by rw [hd M hMQ]; exact hP
    exact not_mem_of_isMaxOrb hF h1 hMP
  have he₂ : ∀ P ∈ maxOrbs A K₀, ∀ v ∈ P, maxOrbs A v = insert Q (maxOrbs A K₀ \ {P}) := by
    intro P hP v hv
    have hKv : A K₀ v := adj_of_mem_isMaxOrb hF hP hv
    have hPv : orbOf A K₀ v = P := orbOf_eq_of_mem_isMaxOrb hP hv
    rw [maxOrbs_eq_insert hF hKv (by rw [hPv]; exact hP), hQ P hP v hv, hPv]
  set U : Set (Subgroup G) := {M | M ∈ Q ∨ ∃ P ∈ maxOrbs A K₀, M ∈ P} with hU
  have hf : ∀ v ∈ U, ∀ w, A v w → w ∈ U := by
    rintro v (hvQ | ⟨P, hP, hvP⟩) w hvw
    · have hMv := hd v hvQ
      by_cases hw : orbOf A v w ∈ maxOrbs A v
      · exact Or.inr ⟨_, hMv ▸ hw, mem_orbOf_self v w⟩
      · have hMw : maxOrbs A w = maxOrbs A K₀ := by
          rw [maxOrbs_eq_of_nonmax hF hvw hw, hMv]
        have hP₁v : P₁ ∈ maxOrbs A v := by rw [hMv]; exact hP₁
        have hvJ₁ : A v J₁ := adj_of_mem_isMaxOrb hF hP₁v hJ₁
        have hoJ₁ : orbOf A v J₁ = P₁ := orbOf_eq_of_mem_isMaxOrb hP₁v hJ₁
        have hwJ₁ : w ∉ orbOf A v J₁ := by
          rw [hoJ₁]
          intro h
          exact hw (by rw [orbOf_eq_of_mem_isMaxOrb hP₁v h]; exact hP₁v)
        have hJ₁w : A J₁ w := hF.graph.sep hvJ₁ hvw hwJ₁
        by_cases hw' : orbOf A J₁ w ∈ maxOrbs A J₁
        · rw [he₂ P₁ hP₁ J₁ hJ₁] at hw'
          rcases hw' with h | ⟨h, -⟩
          · exact Or.inl (h ▸ mem_orbOf_self J₁ w)
          · exfalso
            have h2 : orbOf A J₁ w ∈ maxOrbs A v := by rw [hMv]; exact h
            exact hw (by rw [orbOf_eq_of_mem_isMaxOrb h2 (mem_orbOf_self J₁ w)]; exact h2)
        · exfalso
          have h1 := maxOrbs_eq_of_nonmax hF hJ₁w hw'
          have h2 : Q ∈ maxOrbs A w := by rw [h1]; exact hQmax P₁ hP₁ J₁ hJ₁
          rw [hMw] at h2
          exact hQnot h2
    · have hMv := he₂ P hP v hvP
      by_cases hw : orbOf A v w ∈ maxOrbs A v
      · rw [hMv] at hw
        rcases hw with h | ⟨h, -⟩
        · exact Or.inl (h ▸ mem_orbOf_self v w)
        · exact Or.inr ⟨_, h, mem_orbOf_self v w⟩
      · have hMw : maxOrbs A w = maxOrbs A v := maxOrbs_eq_of_nonmax hF hvw hw
        have hKv : A K₀ v := adj_of_mem_isMaxOrb hF hP hvP
        have hvK : A v K₀ := hF.graph.symm hKv
        have hoK : orbOf A v K₀ = Q := hQ P hP v hvP
        have hQv : Q ∈ maxOrbs A v := hQmax P hP v hvP
        have hwK : w ∉ orbOf A v K₀ := by
          rw [hoK]
          intro h
          exact hw (by rw [orbOf_eq_of_mem_isMaxOrb hQv h]; exact hQv)
        have hKw : A K₀ w := hF.graph.sep hvK hvw hwK
        by_cases hw' : orbOf A K₀ w ∈ maxOrbs A K₀
        · exact Or.inr ⟨_, hw', mem_orbOf_self K₀ w⟩
        · exfalso
          have h1 := maxOrbs_eq_of_nonmax hF hKw hw'
          have h2 : Q ∈ maxOrbs A w := by rw [hMw]; exact hQv
          rw [h1] at h2
          exact hQnot h2
  have hg0 : ∀ M, Relation.ReflTransGen A K₀ M → M ∈ U := by
    intro M hr
    induction hr with
    | refl => exact Or.inl hK₀Q
    | tail _ hab ih => exact hf _ ih _ hab
  have hg : ∀ M ∈ Ω, M ∈ U := fun M hM => hg0 M (hF.conn K₀ hK₀ M hM)
  have hh : ∀ L ∈ Ω, ∀ g ∈ L, ∀ M ∈ Q, conjSub g M ∈ Q := by
    intro L hL g hg' M hMQ
    rcases hg L hL with hLQ | ⟨P, hP, hLP⟩
    · by_cases hML : M = L
      · rw [hML, conjSub_eq_self_of_mem hg']
        exact hML ▸ hMQ
      by_cases hA : A L M
      · rw [hF.graph.fix (hF.graph.symm hA) g hg']
        exact hMQ
      · have hMΩ : M ∈ Ω := by
          have h1 : A J₁ M := adj_of_mem_orbOf hF.graph (hF.graph.symm hKJ₁) hMQ
          exact hF.mem (hF.graph.symm h1)
        rcases hg _ (hF.conjMem M hMΩ g) with h | ⟨P, hP, hM'P⟩
        · exact h
        · exfalso
          have hPL : P ∈ maxOrbs A L := by rw [hd L hLQ]; exact hP
          have hLM' : A L (conjSub g M) := adj_of_mem_isMaxOrb hF hPL hM'P
          have hfix := hF.graph.fix (hF.graph.symm hLM') g hg'
          have hMM : M = conjSub g M := conjSub_injective g hfix.symm
          exact hdisj P hP M hMQ (hMM ▸ hM'P)
    · have hQL : Q ∈ maxOrbs A L := hQmax P hP L hLP
      have hLM : A L M := adj_of_mem_isMaxOrb hF hQL hMQ
      rw [hF.graph.fix (hF.graph.symm hLM) g hg']
      exact hMQ
  have hstab : (⨆ L ∈ Ω, L) ≤ setStab Q := by
    refine iSup₂_le fun L hL g hg' M => ⟨fun h => ?_, fun h => hh L hL g hg' M h⟩
    have h1 := hh L hL g⁻¹ (L.inv_mem hg') _ h
    rwa [conjSub_inv_conjSub] at h1
  have hJ₁Ω : J₁ ∈ Ω := hF.mem (hF.graph.symm hKJ₁)
  obtain ⟨g, hgΩ, hgK⟩ := hF.trans K₀ hK₀ J₁ hJ₁Ω
  have h1 : conjSub g K₀ ∈ Q := (hstab hgΩ K₀).mpr hK₀Q
  rw [hgK] at h1
  exact hdisj P₁ hP₁ J₁ h1 hJ₁

theorem maxOrbs_eq_singleton {K : Subgroup G} (hK : K ∈ Ω) {P : Set (Subgroup G)}
    (hP : P ∈ maxOrbs A K) : maxOrbs A K = {P} :=
  Set.eq_singleton_iff_unique_mem.mpr ⟨hP, fun _ hP' => maxOrb_unique hF hK hP' hP⟩

theorem le_iSup_of_maxOrb {K J : Subgroup G} (hKJ : A K J) (hP : orbOf A K J ∈ maxOrbs A K) :
    ∀ L ∈ Ω, L ≤ ⨆ M ∈ orbOf A K J ∪ orbOf A J K, M := by
  set H : Subgroup G := ⨆ M ∈ orbOf A K J ∪ orbOf A J K, M with hH
  have hleH : ∀ M ∈ orbOf A K J ∪ orbOf A J K, M ≤ H := fun M hM => le_biSup (fun M => M) hM
  let S : Set (Subgroup G) := {L | L ∈ Ω ∧ ∀ P ∈ maxOrbs A L, ∀ M ∈ P, M ≤ H}
  let I : Subgroup G → Prop := fun L => L ∈ S ∧ ∀ P ∈ maxOrbs A L, ∃ M ∈ P, M ∈ S
  have hK : K ∈ Ω := hF.mem hKJ
  have hJ : J ∈ Ω := hF.mem (hF.graph.symm hKJ)
  have hQJ : orbOf A J K ∈ maxOrbs A J := orbOf_mem_maxOrbs hF hKJ hP
  have hJS : J ∈ S := by
    refine ⟨hJ, fun P hP' M hM => ?_⟩
    rw [maxOrbs_eq_singleton hF hJ hQJ, Set.mem_singleton_iff] at hP'
    rw [hP'] at hM
    exact hleH M (Or.inr hM)
  have hKS : K ∈ S := by
    refine ⟨hK, fun P hP' M hM => ?_⟩
    rw [maxOrbs_eq_singleton hF hK hP, Set.mem_singleton_iff] at hP'
    rw [hP'] at hM
    exact hleH M (Or.inl hM)
  have hIK : I K := by
    refine ⟨hKS, fun P hP' => ?_⟩
    rw [maxOrbs_eq_singleton hF hK hP, Set.mem_singleton_iff] at hP'
    exact ⟨J, by rw [hP']; exact mem_orbOf_self K J, hJS⟩
  have hstep : ∀ L L', I L → A L L' → I L' := by
    rintro L L' ⟨hLS, hLI⟩ hLL'
    have hL'Ω : L' ∈ Ω := hF.mem (hF.graph.symm hLL')
    by_cases hmx : orbOf A L L' ∈ maxOrbs A L
    · obtain ⟨M, hMP, hMS⟩ := hLI _ hmx
      have hoLM : orbOf A L M = orbOf A L L' := orbOf_eq_of_mem hMP
      have hML' : L' ∈ orbOf A L M := by rw [hoLM]; exact mem_orbOf_self L L'
      have hLM : A L M := adj_of_mem_orbOf hF.graph hLL' hMP
      obtain ⟨x, hx, hxM⟩ := orbOf_subset_gen hF.graph hLM hML'
      have hxH : x ∈ H := by
        have : (⨆ I ∈ orbOf A L M, I) ≤ H := iSup₂_le fun I hI =>
          hLS.2 (orbOf A L M) (by rw [hoLM]; exact hmx) I hI
        exact this hx
      have hL'S : L' ∈ S := by
        refine ⟨hL'Ω, fun P hP' N hN => ?_⟩
        rw [← hxM, maxOrbs_conj hF] at hP'
        obtain ⟨P₀, hP₀, rfl⟩ := hP'
        obtain ⟨N₀, hN₀, rfl⟩ := hN
        have h2 := conjSub_mono (n := x) (hMS.2 P₀ hP₀ N₀ hN₀)
        rwa [conjSub_eq_self_of_mem hxH] at h2
      refine ⟨hL'S, fun P hP' => ?_⟩
      have hQL' : orbOf A L' L ∈ maxOrbs A L' := orbOf_mem_maxOrbs hF hLL' hmx
      rw [maxOrbs_eq_singleton hF hL'Ω hQL', Set.mem_singleton_iff] at hP'
      exact ⟨L, by rw [hP']; exact mem_orbOf_self L' L, hLS⟩
    · have hMeq := maxOrbs_eq_of_nonmax hF hLL' hmx
      exact ⟨⟨hL'Ω, fun P hP' => hLS.2 P (hMeq ▸ hP')⟩, fun P hP' => hLI P (hMeq ▸ hP')⟩
  have hall : ∀ L, Relation.ReflTransGen A K L → I L := by
    intro L hr
    induction hr with
    | refl => exact hIK
    | tail _ hab ih => exact hstep _ _ ih hab
  intro L hL
  obtain ⟨g, -, rfl⟩ := hF.trans K hK L hL
  obtain ⟨P, hP'⟩ := exists_isMaxOrb (hF.graph.conj g hKJ)
  obtain ⟨⟨N, hLN, rfl⟩, -⟩ := id hP'
  have hNΩ : N ∈ Ω := hF.mem (hF.graph.symm hLN)
  have hIN := hall N (hF.conn K hK N hNΩ)
  have hQN : orbOf A N (conjSub g K) ∈ maxOrbs A N := orbOf_mem_maxOrbs hF hLN hP'
  exact hIN.1.2 _ hQN _ (mem_orbOf_self N _)

@[expose] def MaxAdj (A : Subgroup G → Subgroup G → Prop) (M N : Subgroup G) : Prop :=
  A M N ∧ orbOf A M N ∈ maxOrbs A M

theorem reach_maxAdj {K : Subgroup G} (hK : K ∈ Ω) :
    ∀ L ∈ Ω, Relation.ReflTransGen (MaxAdj A) K L := by
  have hstep : ∀ M N, A M N → Relation.ReflTransGen (MaxAdj A) M N := by
    intro M N hMN
    by_cases hmx : orbOf A M N ∈ maxOrbs A M
    · exact Relation.ReflTransGen.single ⟨hMN, hmx⟩
    · obtain ⟨P, hP⟩ := exists_isMaxOrb hMN
      obtain ⟨⟨y, hMy, rfl⟩, -⟩ := id hP
      have hMeq := maxOrbs_eq_of_nonmax hF hMN hmx
      have hPN : orbOf A M y ∈ maxOrbs A N := by rw [hMeq]; exact hP
      have hNy : A N y := adj_of_mem_isMaxOrb hF hPN (mem_orbOf_self M y)
      have hoNy : orbOf A N y ∈ maxOrbs A N := by
        rw [orbOf_eq_of_mem_isMaxOrb hPN (mem_orbOf_self M y)]
        exact hPN
      have hoyN : orbOf A y N ∈ maxOrbs A y := orbOf_mem_maxOrbs hF hNy hoNy
      exact Relation.ReflTransGen.head ⟨hMy, hP⟩
        (Relation.ReflTransGen.single ⟨hF.graph.symm hNy, hoyN⟩)
  have hall : ∀ L, Relation.ReflTransGen A K L → Relation.ReflTransGen (MaxAdj A) K L := by
    intro L hr
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hab ih => exact ih.trans (hstep _ _ hab)
  exact fun L hL => hall L (hF.conn K hK L hL)

end CFSG.ClassicalInvolution.Q3.TC.Graph
