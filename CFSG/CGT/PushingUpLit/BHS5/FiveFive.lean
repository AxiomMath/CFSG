module

public import CFSG.CGT.PushingUpLit.BHS5.FiveA
public import CFSG.CGT.PushingUpLit.BHS5.Indep
public import CFSG.CGT.PushingUpLit.BHS.FourSixB

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS
  CFSG.LieType.BorelTits

section General

variable {G : Type*} [Group G]

theorem conjSub_eq_of_mem_normalizer' {g : G} {H : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : conjSub g H = H := by
  ext x
  rw [mem_conjSub_iff]
  have := Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) x
  simpa using this.symm

theorem nonComm_conjSub {H K : Subgroup G} (g : G)
    (h : ∃ a ∈ H, ∃ b ∈ K, a * b ≠ b * a) :
    ∃ a ∈ conjSub g H, ∃ b ∈ conjSub g K, a * b ≠ b * a := by
  obtain ⟨a, ha, b, hb, hne⟩ := h
  refine ⟨g * a * g⁻¹, mem_conjSub_of_mem ha, g * b * g⁻¹, mem_conjSub_of_mem hb, fun heq => hne ?_⟩
  have h1 : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
    calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      _ = (g * b * g⁻¹) * (g * a * g⁻¹) := heq
      _ = g * (b * a) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h1)

end General

variable {V : Type} [CommGroup V] [Finite V]

section Conj

variable {P' M' : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}

omit [Finite V] in
theorem ncOut_conjSub (hout : dOut P' D M' = D) {g : MulAut V} (hg : ∀ A ∈ D, conjSub g A ∈ D)
    {B C : Subgroup (MulAut V)} (h : NCOut P' D M' B C) :
    NCOut P' D M' (conjSub g B) (conjSub g C) := by
  obtain ⟨hB, hC, hBC⟩ := h
  rw [hout] at hB hC
  refine ⟨?_, ?_, nonComm_conjSub g hBC⟩
  · rw [hout]; exact hg B hB
  · rw [hout]; exact hg C hC

omit [Finite V] in
theorem mem_compOf_conjSub (hout : dOut P' D M' = D) {g : MulAut V}
    (hg : ∀ A ∈ D, conjSub g A ∈ D) {A B : Subgroup (MulAut V)} (h : B ∈ compOf P' D M' A) :
    conjSub g B ∈ compOf P' D M' (conjSub g A) :=
  Relation.ReflTransGen.lift (conjSub g) (fun _ _ hBC => ncOut_conjSub hout hg hBC) _ _ h

omit [Finite V] in
theorem conjSub_compGen (hout : dOut P' D M' = D) {g : MulAut V}
    (hg : ∀ A ∈ D, conjSub g A ∈ D) (hg' : ∀ A ∈ D, conjSub g⁻¹ A ∈ D)
    {A : Subgroup (MulAut V)} :
    conjSub g (compGen P' D M' A) = compGen P' D M' (conjSub g A) := by
  apply le_antisymm
  · rw [compGen, conjSub, Subgroup.map_iSup]
    refine iSup_le fun B => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hB => ?_
    exact le_iSup₂_of_le (f := fun (X : Subgroup (MulAut V)) (_ : X ∈ compOf P' D M' (conjSub g A))
      => X) _ (mem_compOf_conjSub hout hg hB) le_rfl
  · rw [compGen]
    refine iSup₂_le fun B hB => ?_
    have h1 := mem_compOf_conjSub hout hg' hB
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one] at h1
    have h2 : B = conjSub g (conjSub g⁻¹ B) := by
      rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
    rw [h2]
    exact conjSub_mono g (le_iSup₂_of_le (f := fun (X : Subgroup (MulAut V))
      (_ : X ∈ compOf P' D M' A) => X) _ h1 le_rfl)

end Conj

@[expose] def genD (P : Subgroup (MulAut V)) : Subgroup (MulAut V) := ⨆ A ∈ Hyp51.offSet P, A

@[expose] def compSet (P M : Subgroup (MulAut V)) : Set (Subgroup (MulAut V)) :=
  {E | ∃ A ∈ Hyp51.offSet P, E = compGen (genD P) (Hyp51.offSet P) (genD P ⊓ M) A}

section Basic

variable {P T M : Subgroup (MulAut V)} (h : Hyp51 P T M)
  (hV : ∀ v : V, v ^ 2 = 1)

include h hV

theorem genD_le : genD P ≤ P := iSup₂_le fun B hB => (h.hyp43 hV).le B hB

theorem le_normalizer_genD : P ≤ Subgroup.normalizer ((genD P : Subgroup (MulAut V)) :
    Set (MulAut V)) :=
  iSup_normalized (h.hyp43 hV).toHyp41

theorem dCore_genD : dCore (genD P) (Hyp51.offSet P) (genD P ⊓ M) = ∅ := by
  have hTN : T ≤ Subgroup.normalizer ((genD P : Subgroup (MulAut V)) : Set (MulAut V)) :=
    h.minpar.syl.1.trans (le_normalizer_genD h hV)
  ext A
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hA
  have hcore : A ∈ dCore P (Hyp51.offSet P) M := by
    refine ⟨hA.1, fun g hg => ?_⟩
    have hg' : g ∈ genD P ⊔ T := by rw [genD, sup_eq h hV]; exact hg
    obtain ⟨a, ha, t, ht, rfl⟩ := exists_mul_of_mem_sup hTN hg'
    have h1 : A ≤ conjSub a (genD P ⊓ M) := hA.2 a ha
    rw [conjSub_mul, conjSub_eq_of_mem_normalizer' (Subgroup.le_normalizer (h.minpar.le_M ht))]
    exact h1.trans (conjSub_mono a inf_le_right)
  rw [dCore_eq_empty h hV] at hcore
  exact hcore

theorem dOut_genD : dOut (genD P) (Hyp51.offSet P) (genD P ⊓ M) = Hyp51.offSet P := by
  ext A
  refine ⟨fun hA => hA.1, fun hA => ⟨hA, ?_⟩⟩
  rw [dCore_genD h hV]
  exact Set.notMem_empty A

theorem conjSub_mem_compSet {E : Subgroup (MulAut V)} (hE : E ∈ compSet P M) {g : MulAut V}
    (hg : g ∈ P) : conjSub g E ∈ compSet P M := by
  obtain ⟨A, hA, rfl⟩ := hE
  refine ⟨conjSub g A, hA.conj hg, ?_⟩
  exact conjSub_compGen (dOut_genD h hV) (fun B hB => hB.conj hg)
    (fun B hB => hB.conj (P.inv_mem hg))

theorem not_le_M_of_mem {F A : Subgroup (MulAut V)} (hFP : F ≤ P)
    (hFn : P ≤ Subgroup.normalizer (F : Set (MulAut V))) (hA : A ∈ Hyp51.offSet P)
    (hAF : A ≤ F) : ¬ F ≤ M := by
  intro hFM
  have h43 := h.hyp43 hV
  exact h43.ne_bot A hA (Hyp51.eq_bot_of_normal_le_M h hFP hFn hFM hAF
    (isPGroup_of_isElemAbelian2 (h43.elemAb A hA)))

omit hV in
theorem false_of_opResidual_le_bot (hres : opResidual 2 P ≤ ⊥) : False := by
  have hP2 : IsPGroup 2 ↥P := by
    intro x
    obtain ⟨k, hk⟩ := exists_pow_mem_opResidual (p := 2) (A := P) x.2
    refine ⟨k, Subtype.ext ?_⟩
    have := hres hk
    simpa using this
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP2
  have hTP : T ≤ P := h.minpar.T_le
  have hrel := Subgroup.relIndex_mul_card (H := T) (K := P)
  rw [inf_eq_left.2 hTP, hn] at hrel
  have hdvd : T.relIndex P ∣ 2 ^ n := ⟨Nat.card T, hrel.symm⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hi0 : i = 0 := by
    by_contra hne
    exact h.minpar.syl.2.2 (hi ▸ dvd_pow_self 2 hne)
  rw [hi0, pow_zero] at hi
  have hPT : P ≤ T := Subgroup.relIndex_eq_one.1 hi
  exact h.minpar.not_normal (hPT.trans Subgroup.le_normalizer)

theorem trans_of_indep {ℰ : Set (Subgroup (MulAut V))}
    (hconj : ∀ E ∈ ℰ, ∀ g ∈ P, conjSub g E ∈ ℰ) (hiSup : (⨆ E ∈ ℰ, E) = genD P)
    (hcomm : ∀ E ∈ ℰ, ∀ E' ∈ ℰ, E ≠ E' → ∀ x ∈ E, ∀ y ∈ E', x * y = y * x)
    (hindep : ∀ E ∈ ℰ, Disjoint E (⨆ E' ∈ {E' | E' ∈ ℰ ∧ E' ≠ E}, E'))
    (hsub : ∀ E ∈ ℰ, ∃ A ∈ Hyp51.offSet P, A ≤ E) (hne : ℰ.Nonempty) :
    ∀ E ∈ ℰ, ∀ E' ∈ ℰ, ∃ t ∈ T, conjSub t E = E' := by
  classical
  obtain ⟨E₀, hE₀⟩ := hne
  have hTN : T ≤ Subgroup.normalizer ((genD P : Subgroup (MulAut V)) : Set (MulAut V)) :=
    h.minpar.syl.1.trans (le_normalizer_genD h hV)
  set 𝒪 : Set (Subgroup (MulAut V)) := {E | ∃ t ∈ T, E = conjSub t E₀} with h𝒪
  have h𝒪ℰ : 𝒪 ⊆ ℰ := by
    rintro E ⟨t, ht, rfl⟩
    exact hconj E₀ hE₀ t (h.minpar.T_le ht)
  have hleP' : ∀ E ∈ ℰ, E ≤ genD P := fun E hE => hiSup ▸ le_iSup₂_of_le E hE le_rfl
  have hP'n : ∀ E ∈ ℰ, genD P ≤ Subgroup.normalizer (E : Set (MulAut V)) := by
    intro E hE
    rw [← hiSup]
    refine iSup₂_le fun E' hE' => ?_
    by_cases hEE : E' = E
    · rw [hEE]
      exact Subgroup.le_normalizer
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hcomm E' hE' E hE hEE x hx y hy).symm
  have hPconj : ∀ E ∈ 𝒪, ∀ g ∈ P, conjSub g E ∈ 𝒪 := by
    rintro E ⟨t, ht, rfl⟩ g hg
    have hg' : g ∈ genD P ⊔ T := by rw [genD, sup_eq h hV]; exact hg
    obtain ⟨a, ha, t', ht', rfl⟩ := exists_mul_of_mem_sup hTN hg'
    refine ⟨t' * t, T.mul_mem ht' ht, ?_⟩
    have hmem : conjSub (t' * t) E₀ ∈ ℰ := hconj E₀ hE₀ _ (P.mul_mem (h.minpar.T_le ht')
      (h.minpar.T_le ht))
    rw [conjSub_mul a t', conjSub_mul t' t, conjSub_eq_of_mem_normalizer' (hP'n _ ?_ ha)]
    rw [← conjSub_mul]
    exact hmem
  have hcompl : ∀ E ∈ ℰ \ 𝒪, ∀ g ∈ P, conjSub g E ∈ ℰ \ 𝒪 := by
    rintro E ⟨hE, hE𝒪⟩ g hg
    refine ⟨hconj E hE g hg, fun hmem => hE𝒪 ?_⟩
    have := hPconj _ hmem g⁻¹ (P.inv_mem hg)
    rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this
  have hfin : ℰ.Finite := Set.toFinite _
  have hall : ∀ E ∈ ℰ, E ∈ 𝒪 := by
    intro E₁ hE₁
    by_contra hE₁𝒪
    set F₁ : Subgroup (MulAut V) := ⨆ E ∈ 𝒪, E with hF₁
    set F₂ : Subgroup (MulAut V) := ⨆ E ∈ ℰ \ 𝒪, E with hF₂
    have hF₁P : F₁ ≤ P := (iSup₂_le fun E hE => (hleP' E (h𝒪ℰ hE)).trans (genD_le h hV))
    have hF₂P : F₂ ≤ P := (iSup₂_le fun E hE => (hleP' E hE.1).trans (genD_le h hV))
    have hF₁n : P ≤ Subgroup.normalizer (F₁ : Set (MulAut V)) := le_normalizer_iSup hPconj
    have hF₂n : P ≤ Subgroup.normalizer (F₂ : Set (MulAut V)) := le_normalizer_iSup hcompl
    obtain ⟨A₀, hA₀, hA₀E⟩ := hsub E₀ hE₀
    obtain ⟨A₁, hA₁, hA₁E⟩ := hsub E₁ hE₁
    have hE₀𝒪 : E₀ ∈ 𝒪 := ⟨1, T.one_mem, (conjSub_one E₀).symm⟩
    have hA₀F₁ : A₀ ≤ F₁ := hA₀E.trans (le_iSup₂_of_le (f := fun (E : Subgroup (MulAut V))
      (_ : E ∈ 𝒪) => E) E₀ hE₀𝒪 le_rfl)
    have hA₁F₂ : A₁ ≤ F₂ := hA₁E.trans (le_iSup₂_of_le (f := fun (E : Subgroup (MulAut V))
      (_ : E ∈ ℰ \ 𝒪) => E) E₁ ⟨hE₁, hE₁𝒪⟩ le_rfl)
    have h1 := three_three_b h.minpar.syl h.minpar.max hF₁P hF₁n
      (not_le_M_of_mem h hV hF₁P hF₁n hA₀ hA₀F₁)
    have h2 := three_three_b h.minpar.syl h.minpar.max hF₂P hF₂n
      (not_le_M_of_mem h hV hF₂P hF₂n hA₁ hA₁F₂)
    have hdisj : Disjoint F₁ F₂ := disjoint_biSup_biSup_of_comm hfin hcomm hindep h𝒪ℰ
      Set.sdiff_subset Set.disjoint_sdiff_right
    have hbot : opResidual 2 P ≤ ⊥ := by
      rw [← hdisj.eq_bot]
      exact le_inf h1 h2
    exact false_of_opResidual_le_bot h hbot
  intro E hE E' hE'
  obtain ⟨t, ht, rfl⟩ := hall E hE
  obtain ⟨t', ht', rfl⟩ := hall E' hE'
  refine ⟨t' * t⁻¹, T.mul_mem ht' (T.inv_mem ht), ?_⟩
  rw [conjSub_mul t' t⁻¹, ← conjSub_mul t⁻¹ t, inv_mul_cancel, conjSub_one]

end Basic

@[expose] def SLType2 (D : Set (Subgroup (MulAut V))) (E : Subgroup (MulAut V)) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ IsSLNatSection E (commV E) (commV E ⊓ fixV E) n ∧ commV E ⊔ fixV E = ⊤ ∧
    ∀ B, B ∈ dInter D E ↔ IsSylowOf 2 B E

omit [Finite V] in
theorem SLType2.commV_sup_fixV {D : Set (Subgroup (MulAut V))} {E : Subgroup (MulAut V)}
    (h : SLType2 D E) : commV E ⊔ fixV E = ⊤ := by
  obtain ⟨n, -, -, htop, -⟩ := h
  exact htop

@[expose] def BHSSymType : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (P : Subgroup (MulAut V))
    (D : Set (Subgroup (MulAut V))) (T M : Subgroup (MulAut V)),
    Hyp43 P D T M → (∀ v : V, v ^ 2 = 1) → P = ⨆ A ∈ D, A →
    ∀ A ∈ dOut P D M, Nat.card A = 2 → SymType M D (compGen P D M A)

theorem BHSSymType.toSymCase (h : BHSSymType) : BHSSymCase :=
  fun V _ _ P D T M h43 hV hP A hA hA2 => Or.inr (h V P D T M h43 hV hP A hA hA2)

theorem slType2_of_card_ge_three {P : Subgroup (MulAut V)}
    {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)} (h : Hyp43 P D T M)
    (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)} (hA : A ∈ dOut P D M)
    (h3 : 3 ≤ Nat.card A) : SLType2 D (compGen P D M A) := by
  have hL := compGen_mem_lamSet h hV hA h3
  have hL' := hL
  obtain ⟨-, ⟨n, hn1, hSL⟩, hΛ2, -⟩ := hL'
  have htop := hSL.commV_sup_fixV hn1 (h.toHyp41.sylowGood_of_lamSet hL)
  have hinv : ∀ x ∈ compGen P D M A, ∀ p ∈ commV (compGen P D M A),
      x p ∈ commV (compGen P D M A) := by
    intro x hx p hp
    have h1 : (commV (compGen P D M A)).map x.toMonoidHom = commV (compGen P D M A) := by
      rw [← B19.commV_map_conj]
      congr 1
      exact conjSub_self_of_mem hx
    have : x p ∈ (commV (compGen P D M A)).map x.toMonoidHom := ⟨p, hp, rfl⟩
    rwa [h1] at this
  have hAsyl : IsSylowOf 2 A (compGen P D M A) := (hΛ2 A).1 ⟨hA.1, le_compGen⟩
  have hcard : Nat.card A = 2 ^ n := hSL.sylow_card hn1 hAsyl
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have : n = 1 := by omega
    rw [this] at hcard
    omega
  exact ⟨n, hn2, hSL.of_sup_eq_top hinv htop, htop, hΛ2⟩

structure FiveFive (P T M : Subgroup (MulAut V)) (ℰ : Set (Subgroup (MulAut V))) : Prop where
  sup_eq : genD P ⊔ T = P
  iSup_eq : (⨆ E ∈ ℰ, E) = genD P
  nonempty : ℰ.Nonempty
  conj_mem : ∀ E ∈ ℰ, ∀ g ∈ P, conjSub g E ∈ ℰ
  trans : ∀ E ∈ ℰ, ∀ E' ∈ ℰ, ∃ t ∈ T, conjSub t E = E'
  cover : ∀ A ∈ Hyp51.offSet P, ∃ E ∈ ℰ, A ≤ E
  contains : ∀ E ∈ ℰ, ∃ A ∈ Hyp51.offSet P, A ≤ E
  comm : ∀ E ∈ ℰ, ∀ E' ∈ ℰ, E ≠ E' → ∀ x ∈ E, ∀ y ∈ E', x * y = y * x
  indep : ∀ E ∈ ℰ, Disjoint E (⨆ E' ∈ {E' | E' ∈ ℰ ∧ E' ≠ E}, E')
  commV_le : ∀ E ∈ ℰ, ∀ E' ∈ ℰ, E ≠ E' → commV E ≤ fixV E'
  decomp : fixV (genD P) ⊔ (⨆ E ∈ ℰ, commV E) = ⊤
  type : ∀ E ∈ ℰ, SLType2 (Hyp51.offSet P) E ∨ SymType (genD P ⊓ M) (Hyp51.offSet P) E

section Main

variable {P T M : Subgroup (MulAut V)}

omit [Finite V] in
theorem SymType.commV_sup_fixV {M : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}
    {E : Subgroup (MulAut V)} (h : SymType M D E) : commV E ⊔ fixV E = ⊤ := by
  obtain ⟨m, θ, β, -, -, -, -, -, -, htop, -⟩ := h
  exact htop

theorem five_five (hsym : BHSSymType) (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1) :
    FiveFive P T M (compSet P M) := by
  have h43 := h.hyp43 hV
  have hsup : genD P ⊔ T = P := sup_eq h hV
  have h43' : Hyp43 (genD P) (Hyp51.offSet P) (genD P ⊓ T) (genD P ⊓ M) :=
    hyp43_gen h43 hsup.symm
  obtain ⟨-, -, hSup, hComm, -, hDisj, hV7, -⟩ := four_eighteen hsym.toSymCase h43' hV rfl
  have hcore : dCore (genD P) (Hyp51.offSet P) (genD P ⊓ M) = ∅ := dCore_genD h hV
  have hout : dOut (genD P) (Hyp51.offSet P) (genD P ⊓ M) = Hyp51.offSet P := dOut_genD h hV
  rw [hout] at hComm hDisj hV7 hSup
  rw [hcore] at hSup hDisj
  simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, bot_sup_eq] at hSup hDisj
  have hSup' : genD P = ⨆ A ∈ Hyp51.offSet P,
      compGen (genD P) (Hyp51.offSet P) (genD P ⊓ M) A := hSup
  have hiSup : (⨆ E ∈ compSet P M, E) = genD P := by
    rw [hSup']
    apply le_antisymm
    · refine iSup₂_le fun E hE => ?_
      obtain ⟨A, hA, rfl⟩ := hE
      exact le_iSup₂_of_le (f := fun (A : Subgroup (MulAut V)) (_ : A ∈ Hyp51.offSet P) =>
        compGen (genD P) (Hyp51.offSet P) (genD P ⊓ M) A) A hA le_rfl
    · refine iSup₂_le fun A hA => ?_
      exact le_iSup₂_of_le (f := fun (E : Subgroup (MulAut V)) (_ : E ∈ compSet P M) => E)
        (compGen (genD P) (Hyp51.offSet P) (genD P ⊓ M) A) ⟨A, hA, rfl⟩ le_rfl
  obtain ⟨A₀, hA₀⟩ := h.exists_mem_dInter
  have hne : (compSet P M).Nonempty :=
    ⟨_, A₀, hA₀.1, rfl⟩
  have hcomm : ∀ E ∈ compSet P M, ∀ E' ∈ compSet P M, E ≠ E' →
      ∀ x ∈ E, ∀ y ∈ E', x * y = y * x := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hne x hx y hy
    exact hComm A hA B hB hne x hx y hy
  have hindep : ∀ E ∈ compSet P M, Disjoint E (⨆ E' ∈ {E' | E' ∈ compSet P M ∧ E' ≠ E}, E') := by
    rintro _ ⟨A, hA, rfl⟩
    refine (hDisj A hA).mono_right (iSup₂_le fun E' hE' => ?_)
    obtain ⟨⟨B, hB, rfl⟩, hne⟩ := hE'
    exact le_iSup₂_of_le (f := fun (B : Subgroup (MulAut V))
      (_ : B ∈ {B | B ∈ Hyp51.offSet P ∧
        compGen (genD P) (Hyp51.offSet P) (genD P ⊓ M) B ≠
          compGen (genD P) (Hyp51.offSet P) (genD P ⊓ M) A}) =>
      compGen (genD P) (Hyp51.offSet P) (genD P ⊓ M) B) B ⟨hB, hne⟩ le_rfl
  have htype : ∀ A ∈ Hyp51.offSet P, SLType2 (Hyp51.offSet P)
      (compGen (genD P) (Hyp51.offSet P) (genD P ⊓ M) A) ∨
      SymType (genD P ⊓ M) (Hyp51.offSet P) (compGen (genD P) (Hyp51.offSet P) (genD P ⊓ M) A) := by
    intro A hA
    have hAout : A ∈ dOut (genD P) (Hyp51.offSet P) (genD P ⊓ M) := by
      rw [hout]
      exact hA
    by_cases h3 : 3 ≤ Nat.card A
    · exact Or.inl (slType2_of_card_ge_three h43' hV hAout h3)
    · right
      have hA2 : IsPGroup 2 A := isPGroup_of_isElemAbelian2 (h43.elemAb A hA)
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hA2
      have hbot : A ≠ ⊥ := h43.ne_bot A hA
      have hcard : Nat.card A = 2 := by
        rcases k with _ | _ | k
        · exact absurd (Subgroup.card_eq_one.1 (by simpa using hk)) hbot
        · simpa using hk
        · exfalso
          apply h3
          rw [hk]
          calc 3 ≤ 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact hsym V (genD P) (Hyp51.offSet P) (genD P ⊓ T) (genD P ⊓ M) h43' hV rfl A hAout hcard
  have hsub : ∀ E ∈ compSet P M, ∃ A ∈ Hyp51.offSet P, A ≤ E := by
    rintro _ ⟨A, hA, rfl⟩
    exact ⟨A, hA, le_compGen⟩
  have hconj := fun E (hE : E ∈ compSet P M) g (hg : g ∈ P) => conjSub_mem_compSet h hV hE hg
  have htop : ∀ E ∈ compSet P M, commV E ⊔ fixV E = ⊤ := by
    rintro _ ⟨A, hA, rfl⟩
    exact (htype A hA).elim (fun hSL => SLType2.commV_sup_fixV hSL)
      (fun hSym => SymType.commV_sup_fixV hSym)
  have hcommV : ∀ E ∈ compSet P M, ∀ E' ∈ compSet P M, E ≠ E' → commV E ≤ fixV E' := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hne
    exact hV7 A hA B hB hne
  refine
  { sup_eq := hsup
    iSup_eq := hiSup
    nonempty := hne
    conj_mem := hconj
    trans := trans_of_indep h hV hconj hiSup hcomm hindep hsub hne
    cover := fun A hA => ⟨_, ⟨A, hA, rfl⟩, le_compGen⟩
    contains := hsub
    comm := hcomm
    indep := hindep
    commV_le := hcommV
    decomp := ?_
    type := ?_ }
  · have := fixV_sup_iSup_commV (Set.toFinite (compSet P M)) hcommV htop
    rwa [hiSup] at this
  · rintro _ ⟨A, hA, rfl⟩
    exact htype A hA

end Main

namespace FiveFive

variable {P T M : Subgroup (MulAut V)}
  {ℰ : Set (Subgroup (MulAut V))}

omit [Finite V] in
theorem le_genD (hF : FiveFive P T M ℰ) {E : Subgroup (MulAut V)} (hE : E ∈ ℰ) : E ≤ genD P :=
  hF.iSup_eq ▸ le_iSup₂_of_le E hE le_rfl

omit [Finite V] in
theorem genD_le_normalizer (hF : FiveFive P T M ℰ) {E : Subgroup (MulAut V)} (hE : E ∈ ℰ) :
    genD P ≤ Subgroup.normalizer (E : Set (MulAut V)) := by
  rw [← hF.iSup_eq]
  refine iSup₂_le fun E' hE' => ?_
  by_cases hEE : E' = E
  · rw [hEE]
    exact Subgroup.le_normalizer
  · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hF.comm E' hE' E hE hEE x hx y hy).symm

theorem isSubnormal (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1) (hF : FiveFive P T M ℰ)
    {E : Subgroup (MulAut V)} (hE : E ∈ ℰ) : CFSG.Open.IsSubnormal E P :=
  CFSG.Open.IsSubnormal.step (hF.le_genD hE)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (hF.le_genD hE)).2 (hF.genD_le_normalizer hE))
    (CFSG.Open.IsSubnormal.step (genD_le h hV)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (genD_le h hV)).2
        (le_normalizer_genD h hV)) (CFSG.Open.IsSubnormal.refl P))

theorem le_P (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1) (hF : FiveFive P T M ℰ)
    {E : Subgroup (MulAut V)} (hE : E ∈ ℰ) : E ≤ P :=
  (hF.le_genD hE).trans (genD_le h hV)

end FiveFive

end CFSG.CGT.PushingUpLit.BHS5
