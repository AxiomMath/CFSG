module

public import CFSG.CGT.PushingUpLit.T2KR.Asc78Gen
public import CFSG.CGT.PushingUpLit.T2KR.Sec47
public import CFSG.CGT.PushingUpLit.T2KR.Sec47Struct
public import CFSG.CGT.PushingUpLit.T2K.FiveFour
public import CFSG.CGT.PushingUpLit.T2K.FourSevenB

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_map_conj (B : Subgroup G) (a b : G) :
    (B.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      B.map (MulAut.conj (a * b)).toMonoidHom := by
  ext y
  rw [mem_map_conj_iff, mem_map_conj_iff, mem_map_conj_iff]
  have e : (a * b)⁻¹ * y * (a * b) = b⁻¹ * (a⁻¹ * y * a) * b := by group
  rw [e]

omit [Finite G] in
theorem map_conj_one (B : Subgroup G) : B.map (MulAut.conj (1 : G)).toMonoidHom = B := by
  ext y
  rw [mem_map_conj_iff]
  simp

theorem Sit47.false_of_gen {L M T : Subgroup G} {n : ℕ} {g : G} {D : Subgroup G}
    (hsit : Sit47 G L M T n g D) (hE1 : FooteNonsolvableSimple) (hE8 : SolomonTimmesfeldTight)
    (h25 : Asc76Lemma25) (hE5 : Aschbacher78OneGen) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, hT, hS, -, hnG4, hg, hgM, hD, hDg, hDgP⟩ := hsit
  obtain ⟨-, -, hSM⟩ := h.four_four hE1 hE8 h25 hT
  have hSn : T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := fun t ht => hSM (hT.le ht)
  have hAnt : ¬ D.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer (blockU L : Set G) :=
    fun hc => hDgP (le_inf hDg.1 hc)
  have H : Hyp45 L M T (D.map (MulAut.conj g).toMonoidHom) n :=
    ⟨h.natBlock, h.le, h.normal hE1, hT, hDg, hAnt⟩
  set S : Subgroup G := T ⊓ Subgroup.centralizer (L : Set G) with hSdef
  set B : Subgroup G := Hyp45.bGrp L (D.map (MulAut.conj g).toMonoidHom) with hBdef
  have hBP : IsMaxElemAbelian (T ⊓ Subgroup.centralizer (blockU L : Set G)) B :=
    H.isMaxElemAbelian_B_P
  have hBS : B = S ⊔ blockU L := H.bGrp_eq hS
  have hB0 : B ≠ ⊥ := fun hbot =>
    h.blockU_ne_bot (le_bot_iff.1 (hbot ▸ (hBS ▸ (le_sup_right : blockU L ≤ S ⊔ blockU L))))
  have hBM : M ≤ Subgroup.normalizer (B : Set G) := by
    intro m hm
    apply mem_normalizer_of_map_conj_eq
    have h1 : S.map (MulAut.conj m).toMonoidHom = S := map_conj_eq_of_mem_normalizer (hSM hm)
    have h2 : (blockU L).map (MulAut.conj m).toMonoidHom = blockU L :=
      map_conj_eq_of_mem_normalizer (H.M_le_normalizer_V hm)
    rw [hBS, Subgroup.map_sup, h1, h2]
  have hNB : Subgroup.normalizer (B : Set G) ≤ M := by
    intro x hx
    refine h.mem_of_normalized (X := B) hB0 (hT.isPGroup.to_le H.B_le_T) (h.le.trans hBM) ?_
    rintro _ ⟨l, hl, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx (hBM (h.le hl))) (Subgroup.inv_mem _ hx)
  set Γ : Subgroup G := Subgroup.normalizer (thompsonJ T : Set G) with hΓ
  have hTΓ : T ≤ Γ := Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)
  have hBconj : ∀ δ ∈ Γ, δ ∉ M →
      IsMaxElemAbelian T (B.map (MulAut.conj δ).toMonoidHom) ∧
        ¬ B.map (MulAut.conj δ).toMonoidHom ≤ Subgroup.centralizer (blockU L : Set G) := by
    intro δ hδ hδM
    have hBδ := h.isMaxElemAbelian_T_map_conj hE1 hT hδ hBP
    refine ⟨hBδ, fun hc => hδM ?_⟩
    have hX := T2Hyp.isMaxElemAbelian_P_of_le hBδ (le_inf hBδ.1 hc)
    refine h.mem_of_normalized (X := B.map (MulAut.conj δ).toMonoidHom) ?_
      (hT.isPGroup.to_le hBδ.1) (H.le_normalizer_of_isMaxElemAbelian_P hX)
      (T2Hyp.normalizer_map_conj_of_le (H.le_normalizer_of_isMaxElemAbelian_P hBP))
    intro hbot
    apply hB0
    refine Subgroup.eq_bot_of_card_eq _ ?_
    rw [← card_map_conj B δ, hbot, Subgroup.card_bot]
  let K : Subgroup G := Γ ⊓ ⨅ δ : ↥Γ,
    Subgroup.normalizer ((B.map (MulAut.conj (δ : G)).toMonoidHom : Subgroup G) : Set G)
  have hKmem : ∀ x : G, x ∈ K ↔ x ∈ Γ ∧ ∀ δ ∈ Γ,
      x ∈ Subgroup.normalizer ((B.map (MulAut.conj δ).toMonoidHom : Subgroup G) : Set G) := by
    intro x
    simp only [K, Subgroup.mem_inf, Subgroup.mem_iInf, Subtype.forall]
  have hKΓ : K ≤ Γ := inf_le_left
  have hKM : K ≤ M := by
    intro x hx
    have := ((hKmem x).1 hx).2 1 (Γ.one_mem)
    rw [map_conj_one] at this
    exact hNB this
  have hKnorm : Γ ≤ Subgroup.normalizer (K : Set G) := by
    have key : ∀ γ ∈ Γ, ∀ x ∈ K, γ * x * γ⁻¹ ∈ K := by
      intro γ hγ x hx
      rw [hKmem] at hx ⊢
      refine ⟨Γ.mul_mem (Γ.mul_mem hγ hx.1) (Γ.inv_mem hγ), fun δ hδ => ?_⟩
      have h1 := hx.2 (γ⁻¹ * δ) (Γ.mul_mem (Γ.inv_mem hγ) hδ)
      rw [← map_conj_map_conj B γ⁻¹ δ] at h1
      have h2 := (mem_normalizer_conj_iff' (X := B.map (MulAut.conj δ).toMonoidHom)
        (g := γ⁻¹) (t := x)).2 h1
      simpa using h2
    intro γ hγ
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key γ hγ x hx, fun hx => ?_⟩
    have := key γ⁻¹ (Γ.inv_mem hγ) _ hx
    simpa [mul_assoc] using this
  have hT₁T : (T ⊓ L) ⊔ (T ⊓ Subgroup.centralizer (blockU L : Set G)) ≤ T :=
    sup_le inf_le_left inf_le_left
  have hT₁K : (T ⊓ L) ⊔ (T ⊓ Subgroup.centralizer (blockU L : Set G)) ≤ K := by
    intro t ht
    have htT : t ∈ T := hT₁T ht
    rw [hKmem]
    refine ⟨hTΓ htT, fun δ hδ => ?_⟩
    by_cases hδM : δ ∈ M
    · have e : B.map (MulAut.conj δ).toMonoidHom = B := map_conj_eq_of_mem_normalizer (hBM hδM)
      rw [e]
      exact hBM (hT.le htT)
    · obtain ⟨hBδ, hBδnt⟩ := hBconj δ hδ hδM
      have H' : Hyp45 L M T (B.map (MulAut.conj δ).toMonoidHom) n :=
        ⟨h.natBlock, h.le, h.normal hE1, hT, hBδ, hBδnt⟩
      exact H'.T₁_le_normalizer hS hSn ht
  have hTΓM : CFSG.ABGLocalTools.IsSylowOf 2 T (Γ ⊓ M) := hT.of_le (le_inf hTΓ hT.le) inf_le_right
  have hKΓM : K ≤ Γ ⊓ M := le_inf hKΓ hKM
  have hTc : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K) K :=
    hTΓM.inf_of_le_normalizer hKΓM (inf_le_left.trans hKnorm)
  obtain ⟨y, hy, m, ⟨hmΓ, hmN⟩, hym⟩ := frattini_ambient hKΓ hKnorm hTc g hg
  have hNc : Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤ M :=
    (hE5 G L M n h (h.normal hE1) T (T ⊓ K) hT inf_le_left (le_inf hT₁T hT₁K)).resolve_right hnG4
  exact hgM (hym ▸ M.mul_mem (hKM hy) (hNc hmN))

theorem print47Campbell_of_gen (hE1 : FooteNonsolvableSimple) (hE8 : SolomonTimmesfeldTight)
    (h25 : Asc76Lemma25) (hE5 : Aschbacher78OneGen) : Print47Campbell :=
  fun _ _ _ _ _ _ _ _ _ hsit _ => (hsit.false_of_gen hE1 hE8 h25 hE5).elim

theorem print47Final_of_gen (hE1 : FooteNonsolvableSimple) (hE8 : SolomonTimmesfeldTight)
    (h25 : Asc76Lemma25) (hE5 : Aschbacher78OneGen) : Print47Final :=
  fun _ _ _ _ _ _ _ _ _ hsit _ => hsit.false_of_gen hE1 hE8 h25 hE5

end CFSG.CGT.PushingUpLit.T2K
