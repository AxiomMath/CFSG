module

public import CFSG.CGT.PushingUpLit.T2KSW.Defs
public import CFSG.CGT.PushingUpLit.T2KSW.StrongEmb

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2KSW
open CFSG.RankThree.PartOne (omegaOneCenterIn)
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def TwoClosed (N : Subgroup G) : Prop :=
  ∃ S : Subgroup G, IsSylowOf 2 S N ∧ N ≤ Subgroup.normalizer (S : Set G)

@[expose] def GomiH (H : Subgroup G) : Prop :=
  H ≠ ⊥ ∧ ¬ TwoClosed (Subgroup.normalizer (H : Set G)) ∧
    oTwoIn (Subgroup.normalizer (H : Set G)) = H

@[expose] def StronglyEmbeddedMod (H : Subgroup G) : Prop :=
  ∃ K : Subgroup (↥(Subgroup.normalizer (H : Set G)) ⧸
      H.subgroupOf (Subgroup.normalizer (H : Set G))), CFSG.Open.fusionStronglyEmbedded K

@[expose] def GomiH0 (H : Subgroup G) : Prop :=
  GomiH H ∧ StronglyEmbeddedMod H

@[expose] def GomiHIn (P H : Subgroup G) : Prop :=
  GomiH H ∧ H ≤ P

@[expose] def GomiH0In (P H : Subgroup G) : Prop :=
  GomiH0 H ∧ H ≤ P

@[expose] def GomiD (P D : Subgroup G) : Prop :=
  Maximal (GomiHIn P) D

@[expose] def IsTameIntersection (P Q : Subgroup G) : Prop :=
  IsSylowOf 2 (P ⊓ Subgroup.normalizer ((P ⊓ Q : Subgroup G) : Set G))
      (Subgroup.normalizer ((P ⊓ Q : Subgroup G) : Set G)) ∧
    IsSylowOf 2 (Q ⊓ Subgroup.normalizer ((P ⊓ Q : Subgroup G) : Set G))
      (Subgroup.normalizer ((P ⊓ Q : Subgroup G) : Set G))

@[expose] def GomiE (P D₁ D₂ : Subgroup G) : Prop :=
  GomiD P D₁ ∧ GomiD P D₂ ∧ D₁ ≠ D₂ ∧
    P ⊓ Subgroup.normalizer (D₁ : Set G) = P ⊓ Subgroup.normalizer (D₂ : Set G) ∧
    ((P ≤ Subgroup.normalizer (D₁ : Set G) ∧ P ≤ Subgroup.normalizer (D₂ : Set G)) ∨
      ∃ u ∈ P, D₁.map (MulAut.conj u).toMonoidHom = D₂ ∧
        D₂.map (MulAut.conj u).toMonoidHom = D₁)

@[expose] def IsOtherSylow (P D Q : Subgroup G) : Prop :=
  IsSylowOf 2 Q (Subgroup.normalizer (D : Set G)) ∧ Q ≠ P ⊓ Subgroup.normalizer (D : Set G)

@[expose] def GomiE' (P D₁ D₂ : Subgroup G) : Prop :=
  GomiE P D₁ D₂ ∧ ∀ Q₁ Q₂ : Subgroup G, IsOtherSylow P D₁ Q₁ → IsOtherSylow P D₂ Q₂ →
    ¬ omegaOneCenterIn Q₁ ≤ D₂ ∧ ¬ omegaOneCenterIn Q₂ ≤ D₁

section Elementary

theorem classLETwo_of_le {R S : Subgroup G} (h : ClassLETwo R) (hS : S ≤ R) : ClassLETwo S :=
  fun a ha b hb c hc => h a (hS ha) b (hS hb) c (hS hc)

theorem assembly_pCoreOf_two_eq_oTwoIn (N : Subgroup G) :
    CFSG.Assembly.pCoreOf 2 N = oTwoIn N := by
  simp only [CFSG.Assembly.pCoreOf, oTwoIn, inSubgroup]

theorem le_oTwoIn_of_normal {N K : Subgroup G} (hKN : K ≤ N)
    (hn : N ≤ Subgroup.normalizer (K : Set G)) (hK : IsPGroup 2 K) : K ≤ oTwoIn N := by
  have hnorm : (K.subgroupOf N).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).2 hn
  have hp : IsPGroup 2 (K.subgroupOf N) := hK.comap_subtype
  have hle : K.subgroupOf N ≤ CFSG.pCore 2 ↥N := le_sSup ⟨hnorm, hp⟩
  intro x hx
  exact ⟨⟨x, hKN hx⟩, hle hx, rfl⟩

theorem le_normalizer_oTwoIn (N : Subgroup G) :
    N ≤ Subgroup.normalizer (oTwoIn N : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoIn N)

variable {H : Subgroup G}

theorem GomiH.ne_bot (h : GomiH H) : H ≠ ⊥ := h.1

theorem GomiH.not_twoClosed (h : GomiH H) : ¬ TwoClosed (Subgroup.normalizer (H : Set G)) :=
  h.2.1

theorem GomiH.oTwoIn_eq (h : GomiH H) : oTwoIn (Subgroup.normalizer (H : Set G)) = H := h.2.2

theorem GomiH.isPGroup (h : GomiH H) : IsPGroup 2 H := h.oTwoIn_eq ▸ isPGroup_oTwoIn _

theorem GomiH.isTwoLocal (h : GomiH H) :
    CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (H : Set G)) :=
  ⟨H, h.ne_bot, h.isPGroup, rfl⟩

theorem GomiH.centralizer_le (hc : CFSG.Assembly.IsCharTwoType G) (h : GomiH H) :
    Subgroup.centralizer (H : Set G) ≤ H := by
  intro x hx
  have h1 := hc _ h.isTwoLocal
  rw [assembly_pCoreOf_two_eq_oTwoIn, h.oTwoIn_eq] at h1
  exact h1 (Subgroup.mem_inf.2 ⟨Subgroup.centralizer_le_normalizer _ hx, hx⟩)

theorem GomiH.le_normalizer_of_classLETwo (hc : CFSG.Assembly.IsCharTwoType G) (h : GomiH H)
    {R : Subgroup G} (hR : ClassLETwo R) (hHR : H ≤ R) :
    R ≤ Subgroup.normalizer (H : Set G) := by
  have key : ∀ r ∈ R, ∀ x ∈ H, r * x * r⁻¹ ∈ H := by
    intro r hr x hx
    have hcomm : ⁅r, x⁆ ∈ Subgroup.centralizer (H : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 : ⁅⁅r, x⁆, y⁆ = 1 := hR r hr x (hHR hx) y (hHR hy)
      exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
    have h2 : ⁅r, x⁆ ∈ H := h.centralizer_le hc hcomm
    have h3 : r * x * r⁻¹ = ⁅r, x⁆ * x := by simp [commutatorElement_def, mul_assoc]
    rw [h3]
    exact H.mul_mem h2 hx
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key r hr x, fun hx => ?_⟩
  have := key r⁻¹ (R.inv_mem hr) _ hx
  simpa [mul_assoc] using this

theorem GomiH.center_le (hc : CFSG.Assembly.IsCharTwoType G) (h : GomiH H) {R : Subgroup G}
    (hHR : H ≤ R) : R ⊓ Subgroup.centralizer (R : Set G) ≤ H :=
  inf_le_right.trans ((Subgroup.centralizer_le (fun _ hx => hHR hx)).trans
    (h.centralizer_le hc))

theorem conj_comp_conj_inv (g : G) :
    (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id G := by
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem conj_inv_comp_conj (g : G) :
    (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
  simpa using conj_comp_conj_inv g⁻¹

theorem map_conj_map_conj_inv (g : G) (H : Subgroup G) :
    (H.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = H := by
  rw [Subgroup.map_map, conj_comp_conj_inv, Subgroup.map_id]

theorem map_conj_inv_map_conj (g : G) (H : Subgroup G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [Subgroup.map_map, conj_inv_comp_conj, Subgroup.map_id]

end Elementary

section TwoClosedLemmas

variable [Finite G]

theorem isSylowOf_map_conj_iff {A B : Subgroup G} (g : G) :
    IsSylowOf 2 (A.map (MulAut.conj g).toMonoidHom) (B.map (MulAut.conj g).toMonoidHom) ↔
      IsSylowOf 2 A B := by
  have hker : (MulAut.conj g).toMonoidHom.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff _).2 (MulAut.conj g).injective
  rw [isSylowOf_iff, isSylowOf_iff, Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective,
    Subgroup.relIndex_map_map, hker, sup_bot_eq, sup_bot_eq]
  constructor
  · rintro ⟨hle, hA, hdvd⟩
    exact ⟨hle, hA.of_equiv (Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm, hdvd⟩
  · rintro ⟨hle, hA, hdvd⟩
    exact ⟨hle, hA.map _, hdvd⟩

theorem twoClosed_iff_forall_eq {N : Subgroup G} :
    TwoClosed N ↔ ∀ S₁ S₂ : Subgroup G, IsSylowOf 2 S₁ N → IsSylowOf 2 S₂ N → S₁ = S₂ := by
  constructor
  · rintro ⟨S, hS, hN⟩ S₁ S₂ h₁ h₂
    have hle : ∀ S' : Subgroup G, IsSylowOf 2 S' N → S' = S := by
      intro S' hS'
      obtain ⟨m, hm, hmS⟩ := exists_mem_conj_mem_of_isSylowOf hS hS'.le hS'.isPGroup
      have hSS : S' ≤ S := by
        intro y hy
        have h1 := (Subgroup.mem_normalizer_iff.1 (hN hm) (m⁻¹ * y * m)).1 (hmS y hy)
        have h2 : m * (m⁻¹ * y * m) * m⁻¹ = y := by group
        rwa [h2] at h1
      exact (hS'.eq_of_le hSS hS.le hS.isPGroup).symm
    rw [hle S₁ h₁, hle S₂ h₂]
  · intro h
    obtain ⟨S, hS⟩ := exists_isSylowOf 2 N
    refine ⟨S, hS, fun n hn => ?_⟩
    have hNn : N.map (MulAut.conj n).toMonoidHom = N :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hn)
    have h1 : IsSylowOf 2 (S.map (MulAut.conj n).toMonoidHom) N := by
      have := (isSylowOf_map_conj_iff (A := S) (B := N) n).2 hS
      rwa [hNn] at this
    have h2 := h _ _ h1 hS
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 h2

omit [Finite G] in
theorem exists_isSylowOf_ge {N T : Subgroup G} (hTN : T ≤ N) (hT : IsPGroup 2 T) :
    ∃ S : Subgroup G, IsSylowOf 2 S N ∧ T ≤ S := by
  obtain ⟨Q, hQ⟩ := (hT.comap_subtype (K := N)).exists_le_sylow
  refine ⟨(Q : Subgroup N).map N.subtype, ⟨Q, rfl⟩, fun x hx => ⟨⟨x, hTN hx⟩, hQ hx, rfl⟩⟩

theorem TwoClosed.mono {N K : Subgroup G} (h : TwoClosed N) (hK : K ≤ N) : TwoClosed K := by
  have h' := twoClosed_iff_forall_eq.1 h
  refine twoClosed_iff_forall_eq.2 fun T₁ T₂ h₁ h₂ => ?_
  obtain ⟨S₁, hS₁, hT₁⟩ := exists_isSylowOf_ge (h₁.le.trans hK) h₁.isPGroup
  obtain ⟨S₂, hS₂, hT₂⟩ := exists_isSylowOf_ge (h₂.le.trans hK) h₂.isPGroup
  have hS : S₁ = S₂ := h' _ _ hS₁ hS₂
  subst hS
  have hp : IsPGroup 2 ↥(S₁ ⊓ K : Subgroup G) := hS₁.isPGroup.to_inf_left
  have e₁ := h₁.eq_of_le (le_inf hT₁ h₁.le) inf_le_right hp
  have e₂ := h₂.eq_of_le (le_inf hT₂ h₂.le) inf_le_right hp
  rw [← e₁, ← e₂]

theorem TwoClosed.map_conj {N : Subgroup G} (h : TwoClosed N) (g : G) :
    TwoClosed (N.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨S, hS, hN⟩ := h
  refine ⟨S.map (MulAut.conj g).toMonoidHom, (isSylowOf_map_conj_iff g).2 hS, ?_⟩
  have := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hN
  rwa [Subgroup.map_equiv_normalizer_eq S (MulAut.conj g)] at this

theorem twoClosed_map_conj_iff {N : Subgroup G} (g : G) :
    TwoClosed (N.map (MulAut.conj g).toMonoidHom) ↔ TwoClosed N := by
  refine ⟨fun h => ?_, fun h => h.map_conj g⟩
  have := h.map_conj g⁻¹
  rwa [map_conj_inv_map_conj] at this

end TwoClosedLemmas

section Conj

variable [Finite G] {H : Subgroup G}

theorem GomiH.map_conj (h : GomiH H) (g : G) : GomiH (H.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hbot
    exact h.ne_bot ((Subgroup.map_eq_bot_iff_of_injective H (MulAut.conj g).injective).1 hbot)
  · rw [← Subgroup.map_equiv_normalizer_eq H (MulAut.conj g), twoClosed_map_conj_iff]
    exact h.not_twoClosed
  · rw [← Subgroup.map_equiv_normalizer_eq H (MulAut.conj g)]
    have := oTwoIn_map_equiv (MulAut.conj g) (Subgroup.normalizer (H : Set G))
    rw [h.oTwoIn_eq] at this
    exact this

theorem GomiHIn.map_conj {P : Subgroup G} (h : GomiHIn P H) (g : G) :
    GomiHIn (P.map (MulAut.conj g).toMonoidHom) (H.map (MulAut.conj g).toMonoidHom) :=
  ⟨h.1.map_conj g, Subgroup.map_mono h.2⟩

theorem GomiD.map_conj {P D : Subgroup G} (h : GomiD P D) (g : G) :
    GomiD (P.map (MulAut.conj g).toMonoidHom) (D.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨h.1.map_conj g, fun y hy hDy => ?_⟩
  have hy' : GomiHIn P (y.map (MulAut.conj g⁻¹).toMonoidHom) := by
    have := hy.map_conj g⁻¹
    rwa [map_conj_inv_map_conj] at this
  have hDy' : D ≤ y.map (MulAut.conj g⁻¹).toMonoidHom := by
    have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hDy
    rwa [map_conj_inv_map_conj] at this
  have := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) (h.2 hy' hDy')
  rwa [map_conj_map_conj_inv] at this

end Conj

end CFSG.CGT.PushingUpLit.C2L
