module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Defs
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.HFactsNative
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.HFactsSylow
public import Certificates.Certificate320015

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7.HFactsAux

open CFSG.Open CFSG.GH74.QTGen4.Recog.G23 CFSG.GH74.QTGen4.Recog.G23.HFactsData

@[expose] def aX : Fin 6 → ↥Hc := ![gA 0, gA 1, gA 2, gA 3, gA 4, 1]

theorem aX_zero : aX 0 = gA 0 := rfl

theorem aX_two : aX 2 = gA 2 := rfl

theorem aX_four : aX 4 = gA 4 := rfl

theorem zOf_aX : zOf aX = zA := rfl

theorem Psub_aX : Psub aX = clsub sP :=
  closure_eq_clsub (by intro x; simp [aX, sP])

theorem Esub_aX : Esub aX = clsub [gA 4, zA] := by
  refine closure_eq_clsub ?_
  intro x
  show x ∈ ({gA 4, zA} : Set ↥Hc) ↔ x ∈ [gA 4, zA]
  simp

section Model


theorem cent_eq_clsub {u : ↥Hc} {ss : List ↥Hc} (h : CentOK u ss) :
    Subgroup.centralizer ({u} : Set ↥Hc) = clsub ss :=
  eq_clsub_of ss (fun s hs => (mem_cent_iff u s).2 (h.2 s hs))
    (fun x hx => h.1 _ (Lx_mem_elts x) ((mem_cent_iff u x).1 hx))

theorem norm_eq_clsub {sA ss : List ↥Hc} (hc : ClosedAt sA) (h : NormSetOK sA ss) :
    Subgroup.normalizer (clsub sA : Set ↥Hc) = clsub ss :=
  eq_clsub_of ss (fun s hs => (mem_normalizer_clsub_iff hc s).2 (h.2 s hs))
    (fun x hx => h.1 _ (Lx_mem_elts x) ((mem_normalizer_clsub_iff hc x).1 hx))

theorem model_card_P (hc : ClosedAt sP) (h : PFacts) : Nat.card ↥(Psub aX) = 9 := by
  rw [Psub_aX, card_clsub hc h.2.1]
  exact h.1

theorem model_elem_P (hc : ClosedAt sP) (h : PFacts) : IsElemAbelian 3 (Psub aX) := by
  rw [Psub_aX]
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    have := h.2.2.2 (Lx a.1) (mem_cl_of_mem_clsub hc a.2) (Lx b.1) (mem_cl_of_mem_clsub hc b.2)
    rw [← Lx_mul, ← Lx_mul] at this
    exact Lx_inj this
  · have h3 := h.2.2.1 (Lx x) (mem_cl_of_mem_clsub hc hx)
    apply Lx_inj
    rw [pow_three, Lx_mul, Lx_mul, Lx_one]
    exact h3

theorem model_cent₁ (h : CentOK (gA 0) sC1) :
    Subgroup.centralizer ({aX 0} : Set ↥Hc) ⊓ (⊤ : Subgroup ↥Hc) =
      Subgroup.zpowers (aX 0) ⊔ clsub sH2 := by
  rw [inf_top_eq, aX_zero, ← clsub_cons]
  exact cent_eq_clsub h

theorem model_cent₂ (h : CentOK (gA 2) sC2) :
    Subgroup.centralizer ({aX 2} : Set ↥Hc) ⊓ (⊤ : Subgroup ↥Hc) =
      Subgroup.zpowers (aX 2) ⊔ clsub sH1 := by
  rw [inf_top_eq, aX_two, ← clsub_cons]
  exact cent_eq_clsub h

theorem eq_bot_of_cl {a : ↥Hc} {ss : List ↥Hc} (hc1 : ClosedAt [a]) (hc2 : ClosedAt ss)
    (h : DisjOK a ss) : Subgroup.zpowers a ⊓ clsub ss = ⊥ := by
  rw [← clsub_singleton]
  refine eq_bot_iff.mpr fun x hx => ?_
  have h1 := mem_cl_of_mem_clsub hc1 hx.1
  have h2 := mem_cl_of_mem_clsub hc2 hx.2
  have : Lx x = idL := h _ h2 h1
  rw [← Lx_one] at this
  exact Subgroup.mem_bot.2 (Lx_inj this)

theorem model_disj₁ (hc1 : ClosedAt [gA 0]) (hc2 : ClosedAt sH2) (h : DisjOK (gA 0) sH2) :
    Subgroup.zpowers (aX 0) ⊓ clsub sH2 = ⊥ := by
  rw [aX_zero]
  exact eq_bot_of_cl hc1 hc2 h

theorem model_disj₂ (hc1 : ClosedAt [gA 2]) (hc2 : ClosedAt sH1) (h : DisjOK (gA 2) sH1) :
    Subgroup.zpowers (aX 2) ⊓ clsub sH1 = ⊥ := by
  rw [aX_two]
  exact eq_bot_of_cl hc1 hc2 h

theorem model_norm₁ (hc : ClosedAt [gA 0]) (h : NormSetOK [gA 0] sN1) :
    Subgroup.normalizer (Subgroup.zpowers (aX 0) : Set ↥Hc) ⊓ (⊤ : Subgroup ↥Hc) =
      (Subgroup.zpowers (aX 0) ⊔ clsub sH2) ⊔ Subgroup.zpowers (aX 4) := by
  have e : (Subgroup.zpowers (gA 0) ⊔ clsub sH2) ⊔ Subgroup.zpowers (gA 4) = clsub sN1 := by
    rw [← clsub_cons, ← clsub_singleton, ← clsub_append]
    rfl
  rw [inf_top_eq, aX_zero, aX_four, e, ← clsub_singleton]
  exact norm_eq_clsub hc h

theorem model_norm₂ (hc : ClosedAt [gA 2]) (h : NormSetOK [gA 2] sN2) :
    Subgroup.normalizer (Subgroup.zpowers (aX 2) : Set ↥Hc) ⊓ (⊤ : Subgroup ↥Hc) =
      (Subgroup.zpowers (aX 2) ⊔ clsub sH1) ⊔ Subgroup.zpowers (aX 4) := by
  have e : (Subgroup.zpowers (gA 2) ⊔ clsub sH1) ⊔ Subgroup.zpowers (gA 4) = clsub sN2 := by
    rw [← clsub_cons, ← clsub_singleton, ← clsub_append]
    rfl
  rw [inf_top_eq, aX_two, aX_four, e, ← clsub_singleton]
  exact norm_eq_clsub hc h

theorem Psub_sup_zpowers : Psub aX ⊔ Subgroup.zpowers (zOf aX) = clsub sPZ := by
  rw [Psub_aX, zOf_aX, ← clsub_singleton, ← clsub_append]
  rfl

theorem Psub_sup_Esub : Psub aX ⊔ Esub aX = clsub sPE := by
  rw [Psub_aX, Esub_aX, ← clsub_append]
  rfl

theorem model_centP (h : Cent2OK (gA 0) (gA 2) sPZ) :
    Subgroup.centralizer (Psub aX : Set ↥Hc) ⊓ (⊤ : Subgroup ↥Hc) =
      Psub aX ⊔ Subgroup.zpowers (zOf aX) := by
  rw [inf_top_eq, Psub_sup_zpowers]
  apply eq_clsub_of
  · intro s hs
    rw [Psub_aX, clsub, Subgroup.centralizer_closure]
    intro y hy
    obtain ⟨h1, h2⟩ := h.2 s hs
    have hy' : y = gA 0 ∨ y = gA 2 := by simpa [sP] using hy
    rcases hy' with rfl | rfl
    · exact ((comm_iff _ _).2 h1).symm
    · exact ((comm_iff _ _).2 h2).symm
  · intro x hx
    rw [Psub_aX, clsub, Subgroup.centralizer_closure] at hx
    refine h.1 _ (Lx_mem_elts x) ?_ ?_
    · exact (comm_iff _ _).1 (hx (gA 0) (by simp [sP])).symm
    · exact (comm_iff _ _).1 (hx (gA 2) (by simp [sP])).symm

theorem model_normP (hc : ClosedAt sP) (h : NormSetOK sP sPE) :
    Subgroup.normalizer (Psub aX : Set ↥Hc) ⊓ (⊤ : Subgroup ↥Hc) = Psub aX ⊔ Esub aX := by
  rw [inf_top_eq, Psub_sup_Esub, Psub_aX]
  exact norm_eq_clsub hc h

theorem model_centYp (h : CentOK (gA 0 * gA 2) sPZ) :
    Subgroup.centralizer ({aX 0 * aX 2} : Set ↥Hc) ⊓ (⊤ : Subgroup ↥Hc) =
      Psub aX ⊔ Subgroup.zpowers (zOf aX) := by
  rw [inf_top_eq, Psub_sup_zpowers, aX_zero, aX_two]
  exact cent_eq_clsub h

theorem model_centYm (h : CentOK (gA 0 * (gA 2)⁻¹) sPZ) :
    Subgroup.centralizer ({aX 0 * (aX 2)⁻¹} : Set ↥Hc) ⊓ (⊤ : Subgroup ↥Hc) =
      Psub aX ⊔ Subgroup.zpowers (zOf aX) := by
  rw [inf_top_eq, Psub_sup_zpowers, aX_zero, aX_two]
  exact cent_eq_clsub h

theorem model_normYp (hc : ClosedAt [gA 0 * gA 2]) (h : NormSetOK [gA 0 * gA 2] sPE) :
    Subgroup.normalizer (Subgroup.zpowers (aX 0 * aX 2) : Set ↥Hc) ⊓ (⊤ : Subgroup ↥Hc) =
      Psub aX ⊔ Esub aX := by
  rw [inf_top_eq, Psub_sup_Esub, aX_zero, aX_two, ← clsub_singleton]
  exact norm_eq_clsub hc h

theorem model_normYm (hc : ClosedAt [gA 0 * (gA 2)⁻¹]) (h : NormSetOK [gA 0 * (gA 2)⁻¹] sPE) :
    Subgroup.normalizer (Subgroup.zpowers (aX 0 * (aX 2)⁻¹) : Set ↥Hc) ⊓ (⊤ : Subgroup ↥Hc) =
      Psub aX ⊔ Esub aX := by
  rw [inf_top_eq, Psub_sup_Esub, aX_zero, aX_two, ← clsub_singleton]
  exact norm_eq_clsub hc h

theorem model_invert {u v : ↥Hc} (h : InvertOK u v) :
    ∀ c ∈ Subgroup.centralizer ({u} : Set ↥Hc) ⊓ (⊤ : Subgroup ↥Hc), c * v * c⁻¹ ≠ v⁻¹ := by
  intro c hc heq
  refine h (Lx c) (Lx_mem_elts c) ((mem_cent_iff u c).1 hc.1) ?_
  rw [← Lx_mul, ← Lx_mul]
  exact congrArg Lx (mul_inv_eq_iff_eq_mul.mp heq)

theorem model_conj {ss : List ↥Hc} (h : ConjOK ss) :
    ∃ g ∈ clsub ss, g * gA 4 * g⁻¹ = gA 4 * zA := by
  obtain ⟨l, hl, hlg⟩ := h
  obtain ⟨g, hg, rfl⟩ := cl_sound ss l hl
  refine ⟨g, hg, mul_inv_eq_iff_eq_mul.mpr (Lx_inj ?_)⟩
  rw [Lx_mul, Lx_mul, Lx_mul]
  exact hlg

theorem model_conj₂ (h : ConjOK sT2) :
    ∃ g ∈ clsub sH2 ⊔ Subgroup.zpowers (aX 4), g * aX 4 * g⁻¹ = aX 4 * zOf aX := by
  have e : clsub sH2 ⊔ Subgroup.zpowers (gA 4) = clsub sT2 := by
    rw [← clsub_singleton, ← clsub_append]
    rfl
  rw [aX_four, zOf_aX, e]
  exact model_conj h

theorem model_conj₁ (h : ConjOK sT1) :
    ∃ g ∈ clsub sH1 ⊔ Subgroup.zpowers (aX 4), g * aX 4 * g⁻¹ = aX 4 * zOf aX := by
  have e : clsub sH1 ⊔ Subgroup.zpowers (gA 4) = clsub sT1 := by
    rw [← clsub_singleton, ← clsub_append]
    rfl
  rw [aX_four, zOf_aX, e]
  exact model_conj h

theorem model_centL {a : ↥Hc} {sA : List ↥Hc} (hc : ClosedAt sA) (h : CentInOK a sA [a, zA]) :
    Subgroup.centralizer ({a} : Set ↥Hc) ⊓ clsub sA =
      Subgroup.zpowers a ⊔ Subgroup.zpowers zA := by
  have e : Subgroup.zpowers a ⊔ Subgroup.zpowers zA = clsub [a, zA] := by
    rw [clsub_cons, clsub_singleton]
  rw [e]
  refine le_antisymm (fun x hx => ?_) ?_
  · exact mem_clsub_of_mem_cl
      (h.1 _ (mem_cl_of_mem_clsub hc hx.2) ((mem_cent_iff a x).1 hx.1))
  · refine (Subgroup.closure_le _).2 fun s hs => ?_
    exact ⟨(mem_cent_iff a s).2 (h.2 s hs).1, mem_clsub_of_mem_cl (h.2 s hs).2⟩

theorem model_centL₁ (hc : ClosedAt sH1) (h : CentInOK (gA 0) sH1 sL1) :
    Subgroup.centralizer ({aX 0} : Set ↥Hc) ⊓ clsub sH1 =
      Subgroup.zpowers (aX 0) ⊔ Subgroup.zpowers (zOf aX) := by
  rw [aX_zero, zOf_aX]
  exact model_centL hc h

theorem model_centL₂ (hc : ClosedAt sH2) (h : CentInOK (gA 2) sH2 sL2) :
    Subgroup.centralizer ({aX 2} : Set ↥Hc) ⊓ clsub sH2 =
      Subgroup.zpowers (aX 2) ⊔ Subgroup.zpowers (zOf aX) := by
  rw [aX_two, zOf_aX]
  exact model_centL hc h

theorem model_invK (hc : ClosedAt sK) (h : InvKOK) :
    ∀ u ∈ clsub sH1 ⊔ clsub sH2, orderOf u = 2 → u ≠ zOf aX →
      ∀ u' ∈ clsub sH1 ⊔ clsub sH2, orderOf u' = 2 → u' ≠ zOf aX →
        ∃ g ∈ (⊤ : Subgroup ↥Hc), g * u * g⁻¹ = u' := by
  have hK : clsub sH1 ⊔ clsub sH2 = clsub sK := by
    rw [← clsub_append]
    rfl
  have inv_of : ∀ u : ↥Hc, orderOf u = 2 → u ≠ zA →
      (mulL (Lx u) (Lx u) = idL ∧ Lx u ≠ idL ∧ Lx u ≠ Lx zA) := by
    intro u hord huz
    have h2 : u ^ 2 = 1 := by
      have := pow_orderOf_eq_one u
      rwa [hord] at this
    have hu1 : u ≠ 1 := by
      rintro rfl
      simp at hord
    refine ⟨?_, ?_, fun h' => huz (Lx_inj h')⟩
    · rw [← Lx_mul, ← pow_two, h2, Lx_one]
    · intro h'
      apply hu1
      apply Lx_inj
      rw [h', Lx_one]
  intro u hu hord huz u' hu' hord' hu'z
  rw [hK] at hu hu'
  rw [zOf_aX] at huz hu'z
  obtain ⟨l, hl, hlu⟩ := h (Lx u) (mem_cl_of_mem_clsub hc hu) (inv_of u hord huz) (Lx u')
    (mem_cl_of_mem_clsub hc hu') (inv_of u' hord' hu'z)
  obtain ⟨g, rfl⟩ := exists_Lx hl
  refine ⟨g, Subgroup.mem_top _, mul_inv_eq_iff_eq_mul.mpr (Lx_inj ?_)⟩
  rw [Lx_mul, Lx_mul]
  exact hlu

theorem model_card_cent_t (h : CardCentT) :
    Nat.card ↥(Subgroup.centralizer ({aX 4} : Set ↥Hc) ⊓ (⊤ : Subgroup ↥Hc)) = 8 := by
  rw [aX_four, card_eq_filter _
    (fun l => decide (mulL (Lx (gA 4)) l = mulL l (Lx (gA 4)))) ?_]
  · exact h
  · intro x
    simp only [Subgroup.mem_inf, Subgroup.mem_top, and_true, decide_eq_true_eq]
    exact mem_cent_iff (gA 4) x

end Model

section Certificate


theorem hf_checks : F5Eq ∧ ClosedAt sH1 ∧ ClosedAt sH2 ∧ ClosedAt sK ∧ ClosedAt sP ∧ PFacts ∧
    ClosedAt [gA 0] ∧ ClosedAt [gA 2] ∧ ClosedAt [gA 0 * gA 2] ∧ ClosedAt [gA 0 * (gA 2)⁻¹] ∧
    CentOK (gA 0) sC1 ∧ CentOK (gA 2) sC2 ∧ DisjOK (gA 0) sH2 ∧ DisjOK (gA 2) sH1 ∧
    NormSetOK [gA 0] sN1 ∧ NormSetOK [gA 2] sN2 ∧ Cent2OK (gA 0) (gA 2) sPZ ∧
    NormSetOK sP sPE ∧ CentOK (gA 0 * gA 2) sPZ ∧ NormSetOK [gA 0 * gA 2] sPE ∧
    CentOK (gA 0 * (gA 2)⁻¹) sPZ ∧ NormSetOK [gA 0 * (gA 2)⁻¹] sPE ∧
    InvertOK (gA 0) (gA 2) ∧ InvertOK (gA 2) (gA 0) ∧ ConjOK sT2 ∧ ConjOK sT1 ∧
    CentInOK (gA 0) sH1 sL1 ∧ CentInOK (gA 2) sH2 sL2 ∧ InvKOK ∧ CardCentT :=
  Certificates.certificate320015

theorem hf_f5_eq : F5Eq := hf_checks.1


theorem hfacts_model : HFacts (⊤ : Subgroup ↥Hc) (clsub sH1) (clsub sH2) aX := by
  obtain ⟨-, cH1, cH2, cK, cP, pF, cs1, cs2, cyp, cym, ce1, ce2, di1, di2, no1, no2, cep, nop,
    ceyp, noyp, ceym, noym, inv1, inv2, cj2, cj1, cl1, cl2, ik, ct⟩ := hf_checks
  have cardP := model_card_P cP pF
  have elemP := model_elem_P cP pF
  exact
    { card_H := card_top_Hc
      card_P := cardP
      elem_P := elemP
      cent₁ := model_cent₁ ce1
      disj₁ := model_disj₁ cs1 cH2 di1
      cent₂ := model_cent₂ ce2
      disj₂ := model_disj₂ cs2 cH1 di2
      norm₁ := model_norm₁ cs1 no1
      norm₂ := model_norm₂ cs2 no2
      centP := model_centP cep
      normP := model_normP cP nop
      centYp := model_centYp ceyp
      normYp := model_normYp cyp noyp
      centYm := model_centYm ceym
      normYm := model_normYm cym noym
      invert₁ := model_invert inv1
      invert₂ := model_invert inv2
      conj_t₂ := model_conj₂ cj2
      conj_t₁ := model_conj₁ cj1
      centL₁ := model_centL₁ cH1 cl1
      centL₂ := model_centL₂ cH2 cl2
      invK := model_invK cK ik
      card_cent_t := model_card_cent_t ct
      odd_sub := fun S hS ho => odd_sub_of_card card_top_Hc le_top cardP S hS ho
      order3 := fun x hx h3 _ => exists_conj_into_of_pow_three card_top_Hc le_top cardP hx h3 }

end Certificate

end CFSG.GH74.QTGen4.Recog.G23.P7.HFactsAux
