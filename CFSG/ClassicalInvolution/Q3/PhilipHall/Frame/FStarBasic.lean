module

public import CFSG.ClassicalInvolution.Q3.Q3TMFSBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.Q3T.MFS

section NormalSimple

variable {G : Type} [Group G] {T : Subgroup G} [hTn : T.Normal] [IsSimpleGroup T]

theorem le_of_normal_of_ne_bot (hC : Subgroup.centralizer (T : Set G) = ⊥) {N : Subgroup G}
    (hN : N.Normal) (hN1 : N ≠ ⊥) : T ≤ N := by
  rcases (hN.subgroupOf T).eq_bot_or_eq_top with h | h
  · exfalso
    apply hN1
    have hinf : N ⊓ T = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxN, hxT⟩
      have hx : (⟨x, hxT⟩ : T) ∈ N.subgroupOf T := Subgroup.mem_subgroupOf.mpr hxN
      rw [h, Subgroup.mem_bot] at hx
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx)
    have hcomm : ⁅N, T⁆ = ⊥ := le_bot_iff.mp (hinf ▸ Subgroup.commutator_le_inf N T)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, hC] at hcomm
    exact le_bot_iff.mp hcomm
  · exact Subgroup.subgroupOf_eq_top.mp h

theorem not_commutes_of_le (hnab : ∃ a b : T, a * b ≠ b * a) {H₁ H₂ : Subgroup G}
    (h₁ : T ≤ H₁) (h₂ : T ≤ H₂) : ¬ Commutes H₁ H₂ := by
  intro hc
  obtain ⟨a, b, hab⟩ := hnab
  exact hab (Subtype.ext (hc a (h₁ a.2) b (h₂ b.2)))

theorem oddCore_eq_bot_of_normal_simple [Finite G] (hnab : ∃ a b : T, a * b ≠ b * a)
    (hC : Subgroup.centralizer (T : Set G) = ⊥) : classicalInvolutionOddCore G = ⊥ := by
  by_contra hne
  have hle : T ≤ classicalInvolutionOddCore G := le_of_normal_of_ne_bot hC inferInstance hne
  have hodd : Odd (Nat.card T) :=
    Odd.of_dvd_nat (CFSG.ComponentClassification.OddCore.odd_card G)
      (Subgroup.card_dvd_of_le hle)
  have hsolv : Group.IsSolvable T := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  obtain ⟨a, b, hab⟩ := hnab
  exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 hsolv a b)

theorem nonCommConnected_of_normal_simple (hnab : ∃ a b : T, a * b ≠ b * a)
    (hC : Subgroup.centralizer (T : Set G) = ⊥) {Λ : Set (Subgroup G)} (hne : Λ.Nonempty)
    (hinv : ConjInvariant Λ) (hgen : ⨆ L ∈ Λ, L = ⊤) (hnt : ∀ L ∈ Λ, L ≠ ⊥) :
    NonCommConnected Λ := by
  by_contra hnc
  obtain ⟨Λ₁, Λ₂, hU, ⟨L, hL⟩, ⟨M, hM⟩, hinv₁, hinv₂, hcomm⟩ := exists_split hne hinv hgen hnc
  have hLΛ : L ∈ Λ := hU ▸ Or.inl hL
  have hMΛ : M ∈ Λ := hU ▸ Or.inr hM
  have h₁ : (⨆ L ∈ Λ₁, L) ≠ ⊥ := fun h =>
    hnt L hLΛ (le_bot_iff.mp (h ▸ le_iSup₂_of_le L hL le_rfl))
  have h₂ : (⨆ M ∈ Λ₂, M) ≠ ⊥ := fun h =>
    hnt M hMΛ (le_bot_iff.mp (h ▸ le_iSup₂_of_le M hM le_rfl))
  exact not_commutes_of_le hnab (le_of_normal_of_ne_bot hC (normal_biSup hinv₁) h₁)
    (le_of_normal_of_ne_bot hC (normal_biSup hinv₂) h₂) (commutes_biSup hcomm)

end NormalSimple

section FStar

variable {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup (genFittingFStar Y)]

theorem fstar_normal : (genFittingFStar Y).Normal := genFittingFStar_normal Y

theorem centralizer_fstar_eq_bot (hnab : ∃ a b : genFittingFStar Y, a * b ≠ b * a) :
    Subgroup.centralizer (genFittingFStar Y : Set Y) = ⊥ :=
  CFSG.ClassicalInvolution.centralizer_genFittingFStar_eq_bot hnab

theorem isComponentOf_fstar (hnab : ∃ a b : genFittingFStar Y, a * b ≠ b * a) :
    IsComponentOf (genFittingFStar Y) ⊤ :=
  have : (genFittingFStar Y).Normal := fstar_normal
  isComponentOf_top_of_normal_simple _ hnab

theorem oddCore_eq_bot_of_fstar (hnab : ∃ a b : genFittingFStar Y, a * b ≠ b * a) :
    classicalInvolutionOddCore Y = ⊥ :=
  have : (genFittingFStar Y).Normal := fstar_normal
  oddCore_eq_bot_of_normal_simple hnab (centralizer_fstar_eq_bot hnab)

theorem fstar_le_of_normal (hnab : ∃ a b : genFittingFStar Y, a * b ≠ b * a) {N : Subgroup Y}
    (hN : N.Normal) (hN1 : N ≠ ⊥) : genFittingFStar Y ≤ N :=
  have : (genFittingFStar Y).Normal := fstar_normal
  le_of_normal_of_ne_bot (centralizer_fstar_eq_bot hnab) hN hN1

theorem nonCommConnected_conjClass (hnab : ∃ a b : genFittingFStar Y, a * b ≠ b * a) {z : Y}
    {K : Subgroup Y} (hK : IsClassicalMember3 K z)
    (hgen : Subgroup.normalClosure (K : Set Y) = ⊤) : NonCommConnected (Q3B.conjClass K) := by
  have : (genFittingFStar Y).Normal := fstar_normal
  refine nonCommConnected_of_normal_simple hnab (centralizer_fstar_eq_bot hnab)
    ⟨K, Q3B.mem_conjClass_self K⟩ (Q3B.conjInvariant_conjClass K) (Q3B.conjClass_generated hgen) ?_
  rintro _ ⟨g, rfl⟩ h
  have h' : conjSub g K = ⊥ := h
  apply (hK.conj g).ne_one
  have hmem := (hK.conj g).mem
  rw [h'] at hmem
  exact Subgroup.mem_bot.mp hmem

end FStar

section Family

variable {Y : Type} [Group Y]

theorem normalClosure_eq_top_of_transitive {Ω : Set (Subgroup Y)} {K : Subgroup Y}
    (htrans : ∀ J ∈ Ω, ∃ g : Y, conjSub g K = J) (hgen : (⨆ J ∈ Ω, J) = ⊤) :
    Subgroup.normalClosure (K : Set Y) = ⊤ := by
  rw [eq_top_iff, ← hgen]
  refine iSup₂_le fun J hJ => ?_
  obtain ⟨g, rfl⟩ := htrans J hJ
  rintro _ ⟨x, hx, rfl⟩
  have hxN : x ∈ Subgroup.normalClosure (K : Set Y) := Subgroup.subset_normalClosure hx
  simpa using (Subgroup.normalClosure_normal (s := (K : Set Y))).conj_mem x hxN g

variable [Finite Y] [IsSimpleGroup (genFittingFStar Y)]

theorem setting_of_fstar (hnab : ∃ a b : genFittingFStar Y, a * b ≠ b * a) {z : Y}
    {K : Subgroup Y} (hK : IsClassicalMember3 K z)
    (hgen : Subgroup.normalClosure (K : Set Y) = ⊤) (hsup : genFittingFStar Y ⊔ K = ⊤) :
    Setting z K (genFittingFStar Y) where
  oddCore := oddCore_eq_bot_of_fstar hnab
  member := hK
  comp := isComponentOf_fstar hnab
  sup := hsup
  gen := hgen
  conn := nonCommConnected_conjClass hnab hK hgen
  normal := fstar_normal
  cent := centralizer_fstar_eq_bot hnab

end Family

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
