module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.HYs

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin
  CFSG.HardMathSupport.RichardWeiss.Proving Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G]

theorem Cs_conj {S L : Subgroup G} {m c : G} (hm : m ∈ L ⊔ S)
    (hML : ∀ m ∈ L ⊔ S, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hc : c ∈ pCoreOf 2 (L ⊔ S) ⊓ Subgroup.centralizer (L : Set G)) :
    m * c * m⁻¹ ∈ pCoreOf 2 (L ⊔ S) ⊓ Subgroup.centralizer (L : Set G) := by
  have hMQ : L ⊔ S ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ S) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (L ⊔ S)
  refine ⟨(Subgroup.mem_normalizer_iff.1 (hMQ hm) c).1 hc.1, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
  have hl' : m⁻¹ * l * m ∈ L := by
    have := hML m⁻¹ (Subgroup.inv_mem _ hm) l hl
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.1 hc.2 _ hl'
  calc l * (m * c * m⁻¹) = m * ((m⁻¹ * l * m) * c) * m⁻¹ := by group
    _ = m * (c * (m⁻¹ * l * m)) * m⁻¹ := by rw [h1]
    _ = (m * c * m⁻¹) * l := by group

theorem Cs_Qs_conj {S L : Subgroup G} {y c : G} (hy : y ∈ Qs S L)
    (hc : c ∈ pCoreOf 2 (L ⊔ S) ⊓ Subgroup.centralizer (L : Set G)) :
    y * c * y⁻¹ ∈ pCoreOf 2 (L ⊔ S) ⊓ Subgroup.centralizer (L : Set G) := by
  refine ⟨(pCoreOf 2 (L ⊔ S)).mul_mem ((pCoreOf 2 (L ⊔ S)).mul_mem hy.1 hc.1)
    ((pCoreOf 2 (L ⊔ S)).inv_mem hy.1), Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
  have hyi : y⁻¹ ∈ Qs S L := (Qs S L).inv_mem hy
  obtain ⟨v, hv, hve⟩ : ∃ v ∈ blockV S L, y⁻¹ * l * y * l⁻¹ = v := ⟨⁅y⁻¹, l⁆, hyi.2 l hl, by simp [commutatorElement_def]⟩
  have hconj : y⁻¹ * l * y = v * l := by
    calc y⁻¹ * l * y = (y⁻¹ * l * y * l⁻¹) * l := by group
      _ = v * l := by rw [hve]
  have hcv : c * v = v * c := blockV_comm S L hc.1 hv
  have hcl : l * c = c * l := Subgroup.mem_centralizer_iff.1 hc.2 l hl
  have hcvl : c * (v * l) = (v * l) * c := by
    calc c * (v * l) = (c * v) * l := by group
      _ = (v * c) * l := by rw [hcv]
      _ = v * (c * l) := by group
      _ = v * (l * c) := by rw [hcl]
      _ = (v * l) * c := by group
  calc l * (y * c * y⁻¹) = y * ((y⁻¹ * l * y) * c) * y⁻¹ := by group
    _ = y * (c * (y⁻¹ * l * y)) * y⁻¹ := by rw [hconj, hcvl]
    _ = (y * c * y⁻¹) * l := by
        calc y * (c * (y⁻¹ * l * y)) * y⁻¹ = (y * c * y⁻¹) * l * (y * y⁻¹) := by group
          _ = (y * c * y⁻¹) * l := by group

@[expose] def Qt (S L : Subgroup G) : Subgroup G where
  carrier := {y | y ∈ Qs S L ∧ ∀ q ∈ pCoreOf 2 (L ⊔ S),
    ⁅q, y⁆ ∈ pCoreOf 2 (L ⊔ S) ⊓ Subgroup.centralizer (L : Set G)}
  one_mem' := ⟨(Qs S L).one_mem, fun q _ => by
    have e : ⁅q, (1 : G)⁆ = 1 := by simp [commutatorElement_def]
    rw [e]
    exact (pCoreOf 2 (L ⊔ S) ⊓ Subgroup.centralizer (L : Set G)).one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(Qs S L).mul_mem ha hb, fun q hq => ?_⟩
    have e : ⁅q, a * b⁆ = ⁅q, a⁆ * (a * ⁅q, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (pCoreOf 2 (L ⊔ S) ⊓ Subgroup.centralizer (L : Set G)).mul_mem (ha' q hq)
      (Cs_Qs_conj ha (hb' q hq))
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(Qs S L).inv_mem ha, fun q hq => ?_⟩
    have e : ⁅q, a⁻¹⁆ = a⁻¹ * ⁅q, a⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [e]
    have := Cs_Qs_conj ((Qs S L).inv_mem ha)
      ((pCoreOf 2 (L ⊔ S) ⊓ Subgroup.centralizer (L : Set G)).inv_mem (ha' q hq))
    simpa using this

theorem Qt_le_Qs (S L : Subgroup G) : Qt S L ≤ Qs S L := fun _ h => h.1

theorem shortData_Qt [Finite G] {X S L : Subgroup G} (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    ShortData (Qt S L) L (blockV S L) S := by
  have D := shortData_Qs hA hL hSL
  have hMQ : L ⊔ S ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ S) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (L ⊔ S)
  refine ⟨fun y hy => D.hQM hy.1, fun y hy => D.hQS hy.1, ?_, D.hML, D.hMV, ?_, ?_, D.hV2,
    D.hperf, ?_⟩
  · intro m hm y hy
    refine ⟨D.hMQ m hm y hy.1, fun q hq => ?_⟩
    have hq' : m⁻¹ * q * m ∈ pCoreOf 2 (L ⊔ S) := by
      have := (Subgroup.mem_normalizer_iff.1 (hMQ (Subgroup.inv_mem _ hm)) q).1 hq
      simpa using this
    have e : ⁅q, m * y * m⁻¹⁆ = m * ⁅m⁻¹ * q * m, y⁆ * m⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Cs_conj hm D.hML (hy.2 _ hq')
  · intro v hv
    refine ⟨D.hVQ hv, fun q hq => ?_⟩
    have h := blockV_comm S L hq hv
    have e : ⁅q, v⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h
    rw [e]
    exact (pCoreOf 2 (L ⊔ S) ⊓ Subgroup.centralizer (L : Set G)).one_mem
  · intro q hq v hv
    exact D.hQV q hq.1 v hv
  · rw [Subgroup.commutator_le]
    intro q hq l hl
    exact hq.1.2 l hl

theorem OmPhi_le_Qt {S L : Subgroup G} (hYt : ∀ y ∈ Phi S, y ^ 2 = 1 → y ∈ Qt S L) :
    OmPhi S ≤ Qt S L := by
  rw [OmPhi_eq_closure]
  exact (Subgroup.closure_le _).2 fun y hy => hYt y hy.1 hy.2

theorem false_of_E0_HYt [Finite G] {X S L : Subgroup G} (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (hSL : S ≤ Subgroup.normalizer (L : Set G)) {N : ℕ} (hN : 10 ≤ N)
    {θ : ↥(L ⊔ S) →* Perm (Fin N)} (hNS : NaturalSectionTheta S L N θ)
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    {Δ₀ : Finset (Fin N)} {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)}
    (hshape : E0Shape P ω Δ₀)
    (hθ : (S.subgroupOf (L ⊔ S)).map θ =
      P ⊔ Subgroup.closure {τ | ∃ x, x ∉ Δ₀ ∧ τ = swap x (ω x)})
    (hYt : ∀ y ∈ Phi S, y ^ 2 = 1 → y ∈ Qt S L) : False := by
  have D := shortData_Qt hA hL hSL
  have hθQ : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ pCoreOf 2 (L ⊔ S) := by
    obtain ⟨π, hπ, hπker, hAθ, hequiv, hf⟩ := hNS
    exact fun m hm => inf_centralizer_blockV_le_twoCore hA hL hSL ⟨hθS m hm, hf m hm⟩
  refine false_of_E0_core hA hL hSL hN hNS hθS hshape hθ (Qt S L) D (Qt_le_Qs S L)
    (OmPhi S) (OmPhi_le_S S) (OmPhi_characteristic S)
    (fun s hs v hv => comm_blockV_mem_OmPhi hA hL hSL hs (D.commutator_le hv)) (OmPhi_le_Qt hYt) ?_
  intro m hm y hy
  exact ⟨(Qt S L).mul_mem (D.hMQ m m.2 y hy) ((Qt S L).inv_mem hy), (hy.2 _ (hθQ m hm)).2⟩

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
