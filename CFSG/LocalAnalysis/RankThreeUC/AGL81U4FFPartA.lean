module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFP42

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.Quasithin Subgroup

variable {V : Type} [CommGroup V] [Finite V]

theorem xInv_fixV {L A : Subgroup (MulAut V)}
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V))) : XInv L A (fixV L) := by
  refine ⟨fun g hg => mem_stabSub_of_inv (fun z hz => ?_) (fun z hz => ?_),
    fun a ha => mem_stabSub_of_inv (fun z hz => ?_) (fun z hz => ?_)⟩
  · rw [hz g hg]; exact hz
  · rw [hz g⁻¹ (L.inv_mem hg)]; exact hz
  · intro l hl
    have hmem : a⁻¹ * l * a ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem (hAL ha)) l).mp hl
      simpa using this
    have e : (l * a : MulAut V) = a * (a⁻¹ * l * a) := by group
    have := hz _ hmem
    calc l (a z) = (l * a : MulAut V) z := rfl
      _ = (a * (a⁻¹ * l * a) : MulAut V) z := by rw [e]
      _ = a z := by
        show a ((a⁻¹ * l * a : MulAut V) z) = a z
        rw [this]
  · intro l hl
    have hmem : a * l * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hAL ha) l).mp hl
    have e : (l * a⁻¹ : MulAut V) = a⁻¹ * (a * l * a⁻¹) := by group
    have := hz _ hmem
    calc l (a⁻¹ z) = (l * a⁻¹ : MulAut V) z := rfl
      _ = (a⁻¹ * (a * l * a⁻¹) : MulAut V) z := by rw [e]
      _ = a⁻¹ z := by
        show a⁻¹ ((a * l * a⁻¹ : MulAut V) z) = a⁻¹ z
        rw [this]

theorem abstract_of_natN {n : ℕ} {L : Subgroup (MulAut V)} (hs : IsSimpleGroup ↥L)
    {M₀ : Subgroup V} (hM₀U : M₀ ≤ commV L) (hLU : L ≤ stabSub (commV L))
    (hLM₀ : L ≤ stabSub M₀) (hker : M₀ = commV L ⊓ fixV L) (hnc : ¬ LTrivOn L M₀ (commV L))
    (hN : NatN n (autSec L (commV L) M₀)) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
      ∃ (ε : ↥L ≃* ↥(StatedSU 4 (2 ^ n) F)) (φ : ↥(commV L) →* Multiplicative (Fin 4 → F)),
        Function.Surjective φ ∧ φ.ker = (fixV L).subgroupOf (commV L) ∧
        ∀ (l : ↥L) (u u' : ↥(commV L)), (l : MulAut V) (u : V) = (u' : V) →
          φ u' = Multiplicative.ofAdd
            (((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec
              (Multiplicative.toAdd (φ u)))) := by
  obtain ⟨F, hF1, hF2, hF, ε', ψ, hψ⟩ := hN
  refine ⟨F, hF1, hF2, hF, (secIso hs hM₀U hLU hLM₀ hnc).trans ε',
    ψ.toMonoidHom.comp (QuotientGroup.mk' (M₀.subgroupOf (commV L))), ?_, ?_, ?_⟩
  · exact ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show ψ (QuotientGroup.mk u) = 1 ↔ (u : V) ∈ fixV L
    rw [map_eq_one_iff ψ ψ.injective, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hker]
    simp [u.2]
  · intro l u u' hlu
    have h1 := hψ (secIso hs hM₀U hLU hLM₀ hnc l) (QuotientGroup.mk u)
    rw [secIso_apply hs hM₀U hLU hLM₀ hnc l, secAct_mk] at h1
    have h2 : (QuotientGroup.mk (⟨(l : MulAut V) (u : V), (hLU l.2 (u : V)).2 u.2⟩ : ↥(commV L)) :
        Sec (commV L) M₀) = QuotientGroup.mk u' := by
      congr 1
      exact Subtype.ext hlu
    rw [h2] at h1
    simpa using h1

theorem abstract_of_natO {n : ℕ} {L : Subgroup (MulAut V)} (hs : IsSimpleGroup ↥L)
    {M₀ : Subgroup V} (hM₀U : M₀ ≤ commV L) (hLU : L ≤ stabSub (commV L))
    (hLM₀ : L ≤ stabSub M₀) (hker : M₀ = commV L ⊓ fixV L) (hnc : ¬ LTrivOn L M₀ (commV L))
    (hO : NatO n (autSec L (commV L) M₀)) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (b c : F), Nat.card F = 2 ^ n ∧
      (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
      ∃ (ε : ↥L ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
        (φ : ↥(commV L) →* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)),
        Function.Surjective φ ∧ φ.ker = (fixV L).subgroupOf (commV L) ∧
        ∀ (l : ↥L) (u u' : ↥(commV L)), (l : MulAut V) (u : V) = (u' : V) →
          φ u' = Multiplicative.ofAdd
            (((ε l : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
              Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).mulVec
              (Multiplicative.toAdd (φ u)))) := by
  obtain ⟨F, hF1, hF2, b, c, hF, hirr, ε', ψ, hψ⟩ := hO
  refine ⟨F, hF1, hF2, b, c, hF, hirr, (secIso hs hM₀U hLU hLM₀ hnc).trans ε',
    ψ.toMonoidHom.comp (QuotientGroup.mk' (M₀.subgroupOf (commV L))), ?_, ?_, ?_⟩
  · exact ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show ψ (QuotientGroup.mk u) = 1 ↔ (u : V) ∈ fixV L
    rw [map_eq_one_iff ψ ψ.injective, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hker]
    simp [u.2]
  · intro l u u' hlu
    have h1 := hψ (secIso hs hM₀U hLU hLM₀ hnc l) (QuotientGroup.mk u)
    rw [secIso_apply hs hM₀U hLU hLM₀ hnc l, secAct_mk] at h1
    have h2 : (QuotientGroup.mk (⟨(l : MulAut V) (u : V), (hLU l.2 (u : V)).2 u.2⟩ : ↥(commV L)) :
        Sec (commV L) M₀) = QuotientGroup.mk u' := by
      congr 1
      exact Subtype.ext hlu
    rw [h2] at h1
    simpa using h1

theorem partA_core (hC : U4FFNatural) (hBN : PartBNStmt) (hBO : PartBOStmt)
    (hBO4 : PartBO4Stmt) (hTN : TorusStepN) (hTO : TorusStepO) : PartAAbstract := by
  intro V _ _ hV n L A h
  have hYinv := xInv_Y h
  have hYD : commV L ⊓ fixV (cenD L A) ≤ fixV (cenD L A) := inf_le_right
  obtain ⟨M₀, M₁, hM₀, hM₁, -, hlt, hM₁Y, hmax, hnc, htriv⟩ :=
    exists_noncentral_chief h.perfect h.normalizes (XInv.bot L A) hYinv bot_le
      (not_ltrivOn_Y h hV)
  have hch : IsXChief L A M₀ M₁ := ⟨hM₀, hM₁, hlt, hmax⟩
  obtain ⟨e, hetype, hB, -, -⟩ :=
    chief_numerics hC hBN hBO hBO4 hV h hch hnc (hM₁Y.trans hYD)
  have htop := ltrivOn_top_of_chief hC hBN hBO hBO4 hV h hch hnc hM₁Y
  have hcount := prop51 h hlt.le hM₁Y hM₁.2 hB
  have hsetting : TorusSetting L (cenD L A) M₀ M₁ :=
    ⟨h.simple, h.nonabelian,
      fun d hd e he => h.comm d (cenD_le L A hd) e (cenD_le L A he),
      fun d hd => h.sq d (cenD_le L A hd),
      fun d hd l hl => (cenD_comm hd hl).symm,
      hlt.le, hM₁Y, hM₁.1, htriv, htop, hnc⟩
  have hUle : commV L ≤ fixV (cenD L A) := by
    rcases hetype with ⟨rfl, hN⟩ | ⟨rfl, hO⟩
    · exact hTN hV hsetting hN (by simpa using hcount)
    · exact hTO hV hsetting hO hcount
  have hYU : commV L ⊓ fixV (cenD L A) = commV L := inf_eq_left.mpr hUle
  have hM₁U : M₁ = commV L := by
    refine le_antisymm (by rw [← hYU]; exact hM₁Y) ?_
    rw [← commSub_commV h.perfect]
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨g, hg, y, hy, rfl⟩
    exact htop g hg y (by rw [hYU]; exact hy)
  subst hM₁U
  have hM₀eq : M₀ = commV L ⊓ fixV L := by
    have hM₀fix : M₀ ≤ fixV L := fun z hz g hg => by
      have := htriv g hg z hz
      rwa [Subgroup.mem_bot, mul_inv_eq_one] at this
    have hWinv : XInv L A (commV L ⊓ fixV L) :=
      (xInv_commV h.normalizes).inf (xInv_fixV h.normalizes)
    rcases hmax _ hWinv (le_inf hlt.le hM₀fix) inf_le_left with hW | hW
    · exact hW.symm
    · exfalso
      refine h.not_ltriv_commV fun g hg z hz => ?_
      have : commV L ≤ fixV L := hW ▸ inf_le_right
      rw [Subgroup.mem_bot, mul_inv_eq_one]
      exact this hz g hg
  rcases hetype with ⟨-, hN⟩ | ⟨-, hO⟩
  · exact Or.inl (abstract_of_natN h.simple hlt.le hM₁.1 hM₀.1 hM₀eq hnc hN)
  · exact Or.inr (abstract_of_natO h.simple hlt.le hM₁.1 hM₀.1 hM₀eq hnc hO)

end CFSG.LocalAnalysis.RankThreeUC
