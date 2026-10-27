module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerComponentDvd
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LieType.Simplicity.Basic
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123C

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly.LowTwoRank

theorem nontrivial_of_lie_A {S : Type} [Group S] (r : ℕ) (qq : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r qq).Valid)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A r qq, hv⟩) : Nontrivial S := by
  have hm := CFSG.Models.lieModel_A r qq hv e
  have hs : StatedClassicalModel S .PSL (r + 1) qq.p qq.exponent :=
    hm.2.resolve_right (fun h => absurd h.1 (Nat.succ_ne_zero r))
  exact (CFSG.LieType.Simplicity.fam_PSL_simplicity S _ _ _ hs).1

theorem nontrivial_of_lie_twistedA {S : Type} [Group S] (r : ℕ) (qq : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r qq).Valid)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r qq, hv⟩) : Nontrivial S := by
  have hm := CFSG.Models.lieModel_twistedA r qq hv e
  have hs := hm.2.resolve_right (fun h => absurd h.1 (Nat.succ_ne_zero r))
  exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity S _ _ _ hs).1

theorem nontrivial_of_onLie_isLnEps {S : Type} [Group S] {m q : ℕ} {ε : Bool}
    (h : ∃ i : TauCeti.CFSGIndex, onLie (isLnEps m q ε) i ∧ Nonempty (S ≃* i.Group)) : Nontrivial S := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => simp [onLie] at hi
  | alternating _ _ => simp [onLie] at hi
  | sporadic _ => simp [onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | A r qq =>
      exact nontrivial_of_lie_A r qq hv e
    | twistedA r qq =>
      exact nontrivial_of_lie_twistedA r qq hv e
    | _ => simp [onLie, isLnEps] at hi; (try cases ε <;> simp [isLnEps] at hi)

theorem nontrivial_of_isAltN {S : Type} [Group S] {n : ℕ} {i : TauCeti.CFSGIndex} (hi : isAltN n i)
    (e : S ≃* i.Group) : Nontrivial S := by
  cases i with
  | cyclic _ _ => simp [isAltN] at hi
  | sporadic _ => simp [isAltN] at hi
  | lie _ => simp [isAltN] at hi
  | alternating k hk =>
    have hk5 : 5 ≤ k := hk
    exact (CFSG.LieType.Simplicity.fam_alternating_converse S ⟨k, hk5, ⟨e⟩⟩).2.1

theorem nontrivial_of_catalogIs_isLnA {S : Type} [Group S] {m q : ℕ} (h : catalogIs S (isLnA m q)) :
    Nontrivial S := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with hi | ⟨-, -, hi⟩ | ⟨-, -, hi⟩ | ⟨-, -, hi⟩ | ⟨-, -, hi⟩
  · exact nontrivial_of_onLie_isLnEps ⟨i, hi, ⟨e⟩⟩
  · exact nontrivial_of_isAltN hi e
  · exact nontrivial_of_isAltN hi e
  · exact nontrivial_of_onLie_isLnEps ⟨i, hi, ⟨e⟩⟩
  · exact nontrivial_of_isAltN hi e

theorem nontrivial_of_catalogIs_isUnA {S : Type} [Group S] {m q : ℕ} (h : catalogIs S (isUnA m q)) :
    Nontrivial S := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with hi | ⟨-, hi⟩
  · exact nontrivial_of_onLie_isLnEps ⟨i, hi, ⟨e⟩⟩
  · exact nontrivial_of_catalogIs_isLnA ⟨i, hi, ⟨e⟩⟩

section Layer

variable {G : Type} [Group G] [Finite G]

theorem nontrivial_pSimple_of_type172 {p : ℕ} {L K J K₁ KE : Subgroup G} (h : Type172 p L K J K₁ KE) :
    Nontrivial (PSimple p KE) := by
  rcases h with ⟨hp3, n, -, -, -, -, -, hKE⟩ | ⟨hp3, n, -, -, -, -, -, hKE⟩ | ⟨n, k, -, -, -, -, -, -, -, hKE⟩
  · subst hp3
    exact nontrivial_of_catalogIs_isLnA hKE
  · subst hp3
    exact nontrivial_of_catalogIs_isUnA hKE
  · exact nontrivial_of_catalogIs_isUnA hKE

theorem dvd_card_of_nontrivial_pSimple {p : ℕ} (hp : p.Prime) {X : Subgroup G} (h : Nontrivial (PSimple p X)) :
    p ∣ Nat.card X := by
  by_contra hndvd
  have hcop : Nat.Coprime p (Nat.card (⊤ : Subgroup ↥X)) := by
    rw [Subgroup.card_top]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hndvd
  have htop : (⊤ : Subgroup ↥X) ≤ GLAPPrimeCore p ↥X := le_sSup ⟨inferInstance, hcop⟩
  obtain ⟨a, b, hab⟩ := h.exists_pair_ne
  apply hab
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨a'', rfl⟩ := QuotientGroup.mk_surjective a'
  obtain ⟨b'', rfl⟩ := QuotientGroup.mk_surjective b'
  have hq : (QuotientGroup.mk a'' : PQuot p X) = QuotientGroup.mk b'' :=
    QuotientGroup.eq.2 (htop (Subgroup.mem_top _))
  rw [hq]

theorem exists_pComponent_of_layer_ne_bot {p : ℕ} {X : Subgroup G} (hne : GLAPLayer p X ≠ ⊥) :
    ∃ P : Subgroup G, GLAPComponent p X P := by
  by_contra hcon
  push Not at hcon
  apply hne
  have : {L' | GLAPComponent p X L'} = (∅ : Set (Subgroup G)) :=
    Set.eq_empty_iff_forall_notMem.2 fun J hJ => hcon J hJ
  unfold GLAPLayer
  rw [this, sSup_empty]

theorem cs_sup_eq (D D₁ : Subgroup G) : cs (D ⊔ D₁) = cs D₁ ⊓ cs D := by
  apply le_antisymm
  · intro g hg
    exact ⟨Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_right) hg,
      Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hg⟩
  · intro g hg
    have hle : D ⊔ D₁ ≤ Subgroup.centralizer ({g} : Set G) := sup_le
      (fun d hd => Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hg.2 d hd))
      (fun d hd => Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hg.1 d hd))
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hd)

theorem exists_pComponent_L₁_cs_D {m p : ℕ} {B : Subgroup G} {x : G} {L D K D₁ K₁ KE J L₁ : Subgroup G}
    (h : Cfg12 G m p B x L D K) (h₁ : Cfg12 G m p B x L D₁ K₁) (hcom : CommonInputs G p)
    (hKE : KE = GLALayer (L ⊓ cs (D ⊔ D₁))) (hT172 : Type172 p L K J K₁ KE)
    (hK₁ : GLAPComponent p (L₁ ⊓ cx x) K₁) : ∃ P : Subgroup G, GLAPComponent p (L₁ ⊓ cs D) P := by
  have hp := h.prime
  have hdvd : p ∣ Nat.card (GLALayer (L ⊓ cs (D ⊔ D₁))) := by
    rw [← hKE]
    exact dvd_card_of_nontrivial_pSimple hp (nontrivial_pSimple_of_type172 hT172)
  obtain ⟨Q, hQ, -⟩ := CFSG.exists_glaPComponent_dvd_card_of_dvd_card_glaLayer hp hdvd
  rw [cs_sup_eq D D₁] at hQ
  have hxD₁ : cs D₁ ⊓ cs D ≤ cx x :=
    inf_le_left.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 h₁.xD))
  have hsub : IsSubnormal (L ⊓ (cs D₁ ⊓ cs D)) (cs D₁ ⊓ cs D) := h.tri.comp.2.1.inf_of_le hxD₁
  have hQ' : GLAPComponent p (cs D₁ ⊓ cs D) Q := glaPComponent_of_isSubnormal' hp hsub hQ
  have hQle : Q ≤ GLAPLayer p (cs D₁ ⊓ cs D) := le_sSup hQ'
  have hbal := hcom.bal hp h.ctx.ctx.ctx.kProper D₁ D (isPGroup_of_isElemAbelian h₁.elem)
    (isPGroup_of_isElemAbelian h.elem)
    (fun d hd e he => isElemAbelian_commute h.tri.bmax.1 (h₁.DB hd) (h.DB he))
  rw [S12.std_layer h₁ hcom] at hbal
  have hne : GLAPLayer p (K₁ ⊓ cs D) ≠ ⊥ := by
    rw [hbal]
    intro h0
    exact glaPComponent_ne_bot' hQ' (le_bot_iff.1 (h0 ▸ hQle))
  obtain ⟨P, hP⟩ := exists_pComponent_of_layer_ne_bot hne
  have hcsx : cs D ≤ cx x := Subgroup.centralizer_le (Set.singleton_subset_iff.2 h.xD)
  have hle : L₁ ⊓ cs D ≤ L₁ ⊓ cx x := inf_le_inf_left L₁ hcsx
  have hsub2 := hK₁.2.1.inf_of_le hle
  have heq : K₁ ⊓ (L₁ ⊓ cs D) = K₁ ⊓ cs D := by
    rw [← inf_assoc, inf_eq_left.2 (hK₁.1.trans inf_le_left)]
  rw [heq] at hsub2
  exact ⟨P, glaPComponent_of_isSubnormal' hp hsub2 hP⟩

end Layer

end CFSG.LocalAnalysis.GLTheoremA.T123C

end
