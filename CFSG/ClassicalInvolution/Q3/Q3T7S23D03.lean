module

public import CFSG.ClassicalInvolution.Q3.Q3T7S23D02
public import CFSG.ClassicalInvolution.Q3.Q3T7S23Chain
public import CFSG.ClassicalInvolution.Q3.Q3T7S23Y03

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T7S23

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair diagConj2)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair)
open scoped commutatorElement MatrixGroups

section Perfect

theorem commutator_top_eq_top_of_le {G : Type*} [Group G] {L : Subgroup G} (hL : L ≤ ⁅L, L⁆) :
    ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ := by
  rw [eq_top_iff]
  have h : (⊤ : Subgroup ↥L).map L.subtype ≤
      (⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆).map L.subtype := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hL
  exact (Subgroup.map_le_map_iff_of_injective L.subtype_injective).mp h

theorem eq_one_of_perfect_of_solvable {L A : Type*} [Group L] [Group A] [Group.IsSolvable A]
    (hL : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤) (ψ : L →* A) (ℓ : L) : ψ ℓ = 1 := by
  have hP : ⁅ψ.range, ψ.range⁆ = ψ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hL]
  have hsP : Group.IsSolvable ψ.range :=
    Group.isSolvable_of_isSolvable_injective ψ.range.subtype_injective
  have hbot : ψ.range = ⊥ := by
    by_contra hne
    have hnt : Nontrivial ψ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ψ.range)
    have hcP : commutator ψ.range = ⊤ := by
      apply Subgroup.map_injective ψ.range.subtype_injective
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype, hP]
    rw [hcP] at hlt
    exact lt_irrefl _ hlt
  have h1 : ψ ℓ ∈ ψ.range := ⟨ℓ, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  exact h1

theorem isSolvable_mulAut_of_equiv_sl2Three {K : Type*} [Group K] (e : K ≃* SL(2, ZMod 3)) :
    Group.IsSolvable (MulAut K) := by
  have hs : Group.IsSolvable (MulAut SL(2, ZMod 3)) :=
    CFSG.GroupTheory.groups_order_below_sixty_solvable
      (by rw [Q3T6.sl2Three_card_mulAut]; norm_num)
  exact Group.isSolvable_of_isSolvable_injective (f := (MulAut.congr e).toMonoidHom)
    (MulAut.congr e).injective

end Perfect

section Commutes

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {z u e g : G}


theorem commutes_of_perfect_centralizer3 (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z)
    (hex : ExactMembers Ω) {L : Subgroup G} (hLz : L ≤ Subgroup.centralizer ({z} : Set G))
    (hL : L ≤ ⁅L, L⁆) : Commutes K L := by
  classical
  have hst := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hPow : Q3W.Pow3 L := fun l hl => hL (L.pow_mem hl 3)
  obtain ⟨zK, hzK⟩ := hΩ.classical K hKΩ
  obtain ⟨eK⟩ := (hzK.toQ3 (by norm_num)).nonempty_equiv_sl2 (hex K hKΩ)
  have hdich : ∀ ℓ ∈ L, (conjSub ℓ K = K ∧ conjSub ℓ K' = K') ∨
      (conjSub ℓ K = K' ∧ conjSub ℓ K' = K) := by
    intro ℓ hℓ
    have hℓz : ℓ * z * ℓ⁻¹ = z := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hLz hℓ)
      calc ℓ * z * ℓ⁻¹ = z * ℓ * ℓ⁻¹ := by rw [this]
        _ = z := by group
    have h1 : conjSub ℓ K ∈ twinSet Ω K :=
      ⟨hΩ.conjInvariant ℓ K hKΩ, z, hs.hz, hℓz ▸ hs.hz.conj ℓ⟩
    have h2 : conjSub ℓ K' ∈ twinSet Ω K :=
      ⟨hΩ.conjInvariant ℓ K' hK'Ω, z, hs.hz, hℓz ▸ hzK'.conj ℓ⟩
    rw [hs.twinSet_eq] at h1 h2
    have hne : conjSub ℓ K ≠ conjSub ℓ K' := fun h => hs.hne (conjSub_injective ℓ h).symm
    rcases Set.mem_insert_iff.mp h1 with h1 | h1 <;> rcases Set.mem_insert_iff.mp h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · exact Or.inl ⟨h1, Set.mem_singleton_iff.mp h2⟩
    · exact Or.inr ⟨Set.mem_singleton_iff.mp h1, h2⟩
    · exact absurd ((Set.mem_singleton_iff.mp h1).trans (Set.mem_singleton_iff.mp h2).symm) hne
  have hfixK : ∀ w ∈ L, conjSub w K = K ∧ conjSub w K' = K' :=
    fix_of_pow3_two (fun w S => conjSub w S) (fun x y S => conjSub_mul x y S)
      (fun S => conjSub_one S) hPow hdich
  have hLN : L ≤ Subgroup.normalizer (K : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have := conj_mem_conjSub (n := w) hh
      rwa [(hfixK w hw).1] at this
    · intro hh
      have hh' : w * h * w⁻¹ ∈ conjSub w K := by rwa [(hfixK w hw).1]
      rw [mem_conjSub_iff] at hh'
      have e1 : w⁻¹ * (w * h * w⁻¹) * w = h := by group
      rwa [e1] at hh'
  let ψ : ↥L →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hLN)
  have hψ : ∀ (ℓ : ↥L) (k : ↥K), ((ψ ℓ k : ↥K) : G) = (ℓ : G) * k * (ℓ : G)⁻¹ := fun ℓ k => rfl
  have := isSolvable_mulAut_of_equiv_sl2Three eK
  have hψ1 : ∀ ℓ : ↥L, ψ ℓ = 1 :=
    eq_one_of_perfect_of_solvable (commutator_top_eq_top_of_le hL) ψ
  intro x hx y hy
  have h := congrArg (fun φ : MulAut ↥K => ((φ ⟨x, hx⟩ : ↥K) : G)) (hψ1 ⟨y, hy⟩)
  simp only [hψ, MulAut.one_apply] at h
  calc x * y = (y * x * y⁻¹) * y := by rw [h]
    _ = y * x := by group

end Commutes

section Assembly


@[expose] def D4YSide : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Q3T8.Asc77.Hyp23b Ω K K' W z u e g →
      (alphaOf (Subgroup.closure {u, z}) = ⊥ ∧
        Q3T8.Asc77.ExactLayer.exactLayer Ω e ⊔ Q3T8.Asc77.ExactLayer.exactLayer Ω u = ⊤) →
      Q3T8.Asc77.LayerOrthType Ω e 6 (piSign 3 1) →
      Q3T8.Asc77.LayerOrthType Ω u 6 (!piSign 3 1) → ExactMembers Ω →
      classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω e) = ⊥ →
        ∃ (K₁ : Subgroup G) (z₁ : G), K₁ ∈ Ω ∧ IsUniqueInvolution K₁ z₁ ∧
          K₁ ≤ Q3T8.Asc77.ExactLayer.exactLayer Ω u ∧
          (∃ W', LinearBlockStandardPair (GaloisField 3 1) W' K₁ (conjSub g K)) ∧
          Q3T8.Asc77.ExactLayer.exactLayer Ω u ≤ conjSub g K' ⊔ K₁ ⊔ conjSub g K ∧
          z₁ * e = e * z₁ ∧
          (∃ θ : SL(2, GaloisField 3 1) →* G, θ.range = conjSub g K ∧
            ∀ s, z₁ * θ s * z₁⁻¹ = θ (diagConj2 (-1) 1 s)) ∧
          (∃ θ : SL(2, GaloisField 3 1) →* G, θ.range = conjSub g K' ∧
            ∀ s, z₁ * θ s * z₁⁻¹ = θ (diagConj2 (-1) 1 s)) ∧
          (∀ a : G, a * u = u * a → (∀ x ∈ conjSub g K, a * x = x * a) →
            (∀ x ∈ conjSub g K', a * x = x * a) → a * z₁ = z₁ * a)

theorem d4Chain23_of_yside
    (hO : OddCoreLayer23Neg3) (hY : D4YSide) : D4Chain23 := by
  intro G _ _ _ Ω K K' W z u e g h hα hE hY6
  classical
  have hs : Q3T8.Asc77.Hyp23Setting Ω K K' z := Q3T8.Asc77.Hyp23.setting h.std
  have hd : Q3T8.Asc77.Hyp23bData Ω K K' W z u e g := Q3T8.Asc77.Hyp23b.data h
  have hst := hs.stand
  have hπ : piSign 3 1 = false := by decide
  have hE0 : Q3T8.Asc77.LayerOrthType Ω e 6 false := by simpa [hπ] using hE
  have hOE : classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω e) = ⊥ :=
    hO G Ω K K' W z u e g h hα hE
  have hKΩ : K ∈ Ω := hst.mem
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨R, R', a, b, r, hR, hR', -, hRN, hR'N, haR, hbR', -, -, hu, haa, hbb, -, -⟩ :=
    Q3T8.Asc77.T7K.exists_decomp hs hd
  have hKe : K ≤ Subgroup.centralizer ({e} : Set G) :=
    Q3T8.Asc77.T7Y.le_centralizer_e hs hd hα.1 hKΩ hs.hz hR hRN
  have hKtq : K ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω e :=
    Q3NL.mem_tqMembers3_of_le_centralizer hKΩ hKe
  have hex : ExactMembers Ω :=
    Q3T8.Asc77.B3C.exactMembers_of_twin_layer hst hKΩ hs.hz hKtq hd.he2
      (Q3T8.Asc77.B3C.alphaOf_ze_eq_bot3 hs hd hα.1) hOE hE0
  obtain ⟨K₁, z₁, hK₁Ω, hz₁, hK₁Y, hpair, hYgen, hz₁e, ⟨θ, hθ, hθτ⟩, ⟨θ', hθ', hθ'τ⟩, hfix⟩ :=
    hY G Ω K K' W z u e g h hα hE hY6 hex hOE
  have hz₁Y : z₁ ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω u := hK₁Y hz₁.mem
  have hz₁u : z₁ * u = u * z₁ :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω u hz₁Y)
  obtain ⟨K₃, hTw, hK₃z, hK₃perf, hK₃E, hEgen, hJE, hJ'E⟩ :=
    Q3T8.Asc77.D4C.eSideD4_3 hs hd hα.1 hex hOE hE0 hz₁.sq hz₁e hz₁u θ θ' hθ hθ' hθτ hθ'τ hfix
  obtain ⟨h₁, hh₁⟩ := hst.trans K₁ hK₁Ω
  have hK₁eq : K₁ = conjSub h₁ K := hh₁.symm
  subst hK₁eq
  have hz₁eq : h₁ * z * h₁⁻¹ = z₁ := (hs.hz.conj h₁).eq hz₁
  have hs₁ : Q3T8.Asc77.Hyp23Setting Ω (conjSub h₁ K) (conjSub h₁ K') z₁ := hz₁eq ▸ hs.conj h₁
  have hcomm : Commutes (conjSub h₁ K) K₃ :=
    commutes_of_perfect_centralizer3 hs₁ hex hK₃z hK₃perf
  refine ⟨![conjSub h₁ K, conjSub g K, K₃], hK₁Ω, hcomm, hpair, hTw, ?_⟩
  have hsup : (⨆ k, (![conjSub h₁ K, conjSub g K, K₃] : Fin 3 → Subgroup G) k) =
      conjSub h₁ K ⊔ conjSub g K ⊔ K₃ := by
    refine le_antisymm (iSup_le fun k => ?_) (sup_le (sup_le ?_ ?_) ?_)
    · fin_cases k
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
    · exact le_iSup (fun k => (![conjSub h₁ K, conjSub g K, K₃] : Fin 3 → Subgroup G) k) 0
    · exact le_iSup (fun k => (![conjSub h₁ K, conjSub g K, K₃] : Fin 3 → Subgroup G) k) 1
    · exact le_iSup (fun k => (![conjSub h₁ K, conjSub g K, K₃] : Fin 3 → Subgroup G) k) 2
  have hJH : conjSub g K ≤ conjSub h₁ K ⊔ conjSub g K ⊔ K₃ := le_sup_right.trans le_sup_left
  have hK₁H : conjSub h₁ K ≤ conjSub h₁ K ⊔ conjSub g K ⊔ K₃ := le_sup_left.trans le_sup_left
  have hK₃H : K₃ ≤ conjSub h₁ K ⊔ conjSub g K ⊔ K₃ := le_sup_right
  have hEH : Q3T8.Asc77.ExactLayer.exactLayer Ω e ≤ conjSub h₁ K ⊔ conjSub g K ⊔ K₃ :=
    hEgen.trans (sup_le hJH hK₃H)
  have hYH : Q3T8.Asc77.ExactLayer.exactLayer Ω u ≤ conjSub h₁ K ⊔ conjSub g K ⊔ K₃ :=
    hYgen.trans (sup_le (sup_le (hJ'E.trans hEH) hK₁H) hJH)
  rw [hsup]
  refine eq_top_iff.mpr ?_
  rw [← hα.2]
  exact sup_le hEH hYH

end Assembly

end CFSG.ClassicalInvolution.Q3.Q3T7S23
