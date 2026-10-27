module

public import CFSG.ClassicalInvolution.RouteD.MultiModelShortF4

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section TwistedComm

theorem group_comm_pair {G : Type*} [Group G] {A1 A2 B1 B2 X Y : G} (h21 : Commute A2 B1)
    (h12 : Commute A1 B2) (hY1 : Commute Y A1) (hYB : Commute Y B1) (hX : ⁅A1, B1⁆ = X)
    (hY : ⁅A2, B2⁆ = Y) : ⁅A1 * A2, B1 * B2⁆ = X * Y := by
  have hX' : A1 * B1 = X * B1 * A1 := by
    rw [← hX, commutatorElement_def]; group
  have hY' : A2 * B2 = Y * B2 * A2 := by
    rw [← hY, commutatorElement_def]; group
  have key : A1 * A2 * (B1 * B2) = X * Y * (B1 * B2) * (A1 * A2) := by
    calc A1 * A2 * (B1 * B2) = A1 * (A2 * B1) * B2 := by group
      _ = A1 * (B1 * A2) * B2 := by rw [h21.eq]
      _ = (A1 * B1) * (A2 * B2) := by group
      _ = (X * B1 * A1) * (Y * B2 * A2) := by rw [hX', hY']
      _ = X * B1 * (A1 * Y) * B2 * A2 := by group
      _ = X * B1 * (Y * A1) * B2 * A2 := by rw [hY1.eq.symm]
      _ = X * (B1 * Y) * A1 * B2 * A2 := by group
      _ = X * (Y * B1) * A1 * B2 * A2 := by rw [hYB.eq.symm]
      _ = X * Y * B1 * (A1 * B2) * A2 := by group
      _ = X * Y * B1 * (B2 * A1) * A2 := by rw [h12.eq]
      _ = X * Y * (B1 * B2) * (A1 * A2) := by group
  rw [commutatorElement_def]
  calc A1 * A2 * (B1 * B2) * (A1 * A2)⁻¹ * (B1 * B2)⁻¹
      = (A1 * A2 * (B1 * B2)) * (A1 * A2)⁻¹ * (B1 * B2)⁻¹ := by group
    _ = (X * Y * (B1 * B2) * (A1 * A2)) * (A1 * A2)⁻¹ * (B1 * B2)⁻¹ := by rw [key]
    _ = X * Y := by group

variable {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

theorem rho_add (a b : Fin (Tag.rank .E6) → ℤ) : rho (a + b) = rho a + rho b :=
  rhoHom.map_add a b

theorem xFixed_mem_of_pairs (h2 : (2 : k) ≠ 0) (hne : ∃ w : k, θ w ≠ w)
    {a b c : Fin (Tag.rank .E6) → ℤ} (ha : IsRoot .E6 a) (hb : IsRoot .E6 b) (hc : IsRoot .E6 c)
    (hρa : rho a ≠ a) (hρb : rho b ≠ b) (hρc : rho c = c) (hab : a + b = c)
    (n1 : ¬ IsRoot .E6 (rho a + b)) (n1' : rho a + b ≠ 0) (n2 : ¬ IsRoot .E6 (a + rho b))
    (n2' : a + rho b ≠ 0) (n3 : ¬ IsRoot .E6 (c + a)) (n3' : c + a ≠ 0)
    (n4 : ¬ IsRoot .E6 (c + b)) (n4' : c + b ≠ 0) {S : Subgroup (fixedGroup k θ)}
    (hS₁ : ∀ s, xPair θ hθ ha hρa s ∈ S) (hS₂ : ∀ t, xPair θ hθ hb hρb t ∈ S) (v : k)
    (hv : θ v = v) : xFixed θ hc hρc v hv ∈ S := by
  have hab0 : a + b ≠ 0 := by rw [hab]; exact hc.ne_zero
  have habr : IsRoot .E6 (a + b) := hab ▸ hc
  have hrab : rho a + rho b = c := by rw [← rho_add, hab, hρc]
  have hρab0 : rho a + rho b ≠ 0 := by rw [hrab]; exact hc.ne_zero
  have hρabr : IsRoot .E6 (rho a + rho b) := hrab ▸ hc
  set N₁ : ℤ := e6Data_valid.commSign k a b with hN₁
  set N₂ : ℤ := e6Data_valid.commSign k (rho a) (rho b) with hN₂
  have hsN₁ : N₁ = 1 ∨ N₁ = -1 := e6Data_valid.commSign_eq_one_or k a b
  have hsN₂ : N₂ = 1 ∨ N₂ = -1 := e6Data_valid.commSign_eq_one_or k (rho a) (rho b)
  have hsa := twistSign_eq_one_or a
  have hsb := twistSign_eq_one_or b
  set u : k → k → k := fun s t => (N₁ : k) * s * t +
    (N₂ : k) * ((twistSign a : k) * θ s) * ((twistSign b : k) * θ t) with hu
  have hform : ∀ s t : k,
      ((⁅xPair θ hθ ha hρa s, xPair θ hθ hb hρb t⁆ : fixedGroup k θ) : e6Data_valid.minGroup k) =
        e6Data_valid.xm k c (u s t) := by
    intro s t
    have e1 : ((⁅xPair θ hθ ha hρa s, xPair θ hθ hb hρb t⁆ : fixedGroup k θ) :
        e6Data_valid.minGroup k) =
        ⁅(xPair θ hθ ha hρa s : e6Data_valid.minGroup k),
          (xPair θ hθ hb hρb t : e6Data_valid.minGroup k)⁆ := rfl
    rw [e1, xPair_val, xPair_val]
    have hX := e6Data_valid.commutator_xm_commSign k ha hb hab0 habr s t
    have hY := e6Data_valid.commutator_xm_commSign k (isRoot_rho ha) (isRoot_rho hb) hρab0 hρabr
      ((twistSign a : k) * θ s) ((twistSign b : k) * θ t)
    rw [hab] at hX
    rw [hrab] at hY
    rw [group_comm_pair (commute_xm (isRoot_rho ha) hb n1' n1 _ _)
      (commute_xm ha (isRoot_rho hb) n2' n2 _ _) (commute_xm hc ha n3' n3 _ _)
      (commute_xm hc hb n4' n4 _ _) hX hY, ← e6Data_valid.xm_add]
  have hfix : ∀ s t : k, θ (u s t) = u s t := by
    intro s t
    have hg := (mem_fixedGroup θ).1 (⁅xPair θ hθ ha hρa s, xPair θ hθ hb hρb t⁆ :
      fixedGroup k θ).2
    rw [hform, sigma_xm θ hc, hρc, twistSign_of_rho_eq hc hρc, Int.cast_one, one_mul] at hg
    exact e6Data_valid.xm_injective k hc hg
  have hθsign : ∀ x : ℤ, (x = 1 ∨ x = -1) → θ (x : k) = x := fun x hx => by
    rcases hx with rfl | rfl <;> simp
  set M : k := (N₂ : k) * (twistSign a : k) * (twistSign b : k) with hM
  have hθM : θ M = M := by
    rw [hM, map_mul, map_mul, hθsign _ hsN₂, hθsign _ hsa, hθsign _ hsb]
  have hMM : M * M = 1 := by
    rcases hsN₂ with h | h <;> rcases hsa with h' | h' <;> rcases hsb with h'' | h'' <;>
      simp [hM, h, h', h'']
  have hNN : (N₁ : k) * N₁ = 1 := by rcases hsN₁ with h | h <;> simp [h]
  have hθN : θ (N₁ : k) = N₁ := hθsign _ hsN₁
  have hu1 : ∀ s : k, u s 1 = (N₁ : k) * s + M * θ s := by
    intro s
    simp only [hu, hM, map_one]
    ring
  have hNM : (N₁ : k) = M := by
    by_contra hneq
    obtain ⟨w, hw⟩ := hne
    have h := hfix w 1
    rw [hu1, map_add, map_mul, map_mul, hθN, hθM, hθ] at h
    have h' : ((N₁ : k) - M) * (θ w - w) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h' with h0 | h0
    · exact hneq (sub_eq_zero.1 h0)
    · exact hw (sub_eq_zero.1 h0)
  have h2θ : θ (2 : k) = 2 := map_ofNat θ 2
  set s : k := (N₁ : k) * v / 2 with hs
  have hθs : θ s = s := by
    rw [hs, map_div₀, map_mul, hθN, hv, h2θ]
  have hus : u s 1 = v := by
    rw [hu1, hθs, ← hNM, hs]
    field_simp
    linear_combination (2 * v) * hNN
  have hmem := S.mul_mem (S.mul_mem (S.mul_mem (hS₁ s) (hS₂ 1)) (S.inv_mem (hS₁ s)))
    (S.inv_mem (hS₂ 1))
  have hmem' : (⁅xPair θ hθ ha hρa s, xPair θ hθ hb hρb 1⁆ : fixedGroup k θ) ∈ S := by
    rw [commutatorElement_def]
    exact hmem
  have : (⁅xPair θ hθ ha hρa s, xPair θ hθ hb hρb 1⁆ : fixedGroup k θ) =
      xFixed θ hc hρc v hv := by
    apply Subtype.ext
    rw [hform, xFixed_val, hus]
  rwa [this] at hmem'

end TwistedComm

section Generation

variable {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

@[expose] def shortSetE6 : Set (Fin 4 → ℤ) := {![1, 0, 0, 0], ![-1, 0, 0, 0]} ∪ shortSetF4

theorem not_isRoot_E6_of_false {v : Fin (Tag.rank .E6) → ℤ}
    (h : RootOps.isRootB .E6 v = false) : ¬ IsRoot .E6 v := fun hr => by
  have := RootOps.isRootB_iff.2 hr
  rw [h] at this
  exact Bool.noConfusion this

abbrev e6a : Fin (Tag.rank .E6) → ℤ := Pi.single (nd 2) 1 + Pi.single (nd 3) 1

abbrev e6b : Fin (Tag.rank .E6) → ℤ := -Pi.single (nd 2) 1

abbrev e6c : Fin (Tag.rank .E6) → ℤ := Pi.single (nd 3) 1

theorem iSup_shortSetE6_eq_top (hθ : ∀ c, θ (θ c) = c) (h2 : (2 : k) ≠ 0)
    (hne : ∃ w : k, θ w ≠ w) :
    (⨆ γ ∈ shortSetE6, (twistedDatum k θ).rootGroup γ) = ⊤ := by
  set T : Subgroup (fixedGroup k θ) := ⨆ γ ∈ shortSetE6, (twistedDatum k θ).rootGroup γ with hT
  have hle : ∀ γ ∈ shortSetE6, twistedRootGroup k θ γ ≤ T := fun γ hγ =>
    le_iSup₂_of_le γ hγ le_rfl
  have mshort : ∀ i : Fin 8, shortF4 i ∈ shortSetE6 := fun i => Or.inr ⟨i, rfl⟩
  have mp : (![1, 0, 0, 0] : Fin 4 → ℤ) ∈ shortSetE6 := Or.inl (Or.inl rfl)
  have mn : (![-1, 0, 0, 0] : Fin 4 → ℤ) ∈ shortSetE6 := Or.inl (Or.inr rfl)
  have hrootc : IsRoot .E6 e6c := RootOps.isRootB_iff.1 (by decide)
  have hrootc' : IsRoot .E6 (-e6c) := RootOps.isRootB_iff.1 (by decide)
  have hfixc : rho e6c = e6c := by funext i; fin_cases i <;> decide
  have hfixc' : rho (-e6c) = -e6c := by funext i; fin_cases i <;> decide
  have h1p : twistedRootGroup k θ (Pi.single (1 : Fin 4) 1) ≤ T := by
    have ha : IsRoot .E6 e6a := RootOps.isRootB_iff.1 (by decide)
    have hb : IsRoot .E6 e6b := RootOps.isRootB_iff.1 (by decide)
    have hρa : rho e6a ≠ e6a := fun h => by
      have := congrFun h (nd 4); revert this; decide
    have hρb : rho e6b ≠ e6b := fun h => by
      have := congrFun h (nd 4); revert this; decide
    have hab : e6a + e6b = e6c := by funext i; fin_cases i <;> decide
    have hpa : proj e6a = shortF4 2 := by funext i; fin_cases i <;> decide
    have hpb : proj e6b = shortF4 5 := by funext i; fin_cases i <;> decide
    have hpc : proj e6c = Pi.single (1 : Fin 4) 1 := by funext i; fin_cases i <;> decide
    intro g hg
    obtain ⟨v, hv, hgv⟩ := (mem_twistedRootGroup_iff_of_fixed θ hrootc hpc hfixc g).1 hg
    have : g = xFixed θ hrootc hfixc v hv := Subtype.ext hgv
    rw [this]
    exact xFixed_mem_of_pairs θ hθ h2 hne ha hb hrootc hρa hρb hfixc hab
      (not_isRoot_E6_of_false (by decide)) (fun h => by
        have := congrFun h (nd 4); revert this; decide)
      (not_isRoot_E6_of_false (by decide)) (fun h => by
        have := congrFun h (nd 4); revert this; decide)
      (not_isRoot_E6_of_false (by decide)) (fun h => by
        have := congrFun h (nd 3); revert this; decide)
      (not_isRoot_E6_of_false (by decide)) (fun h => by
        have := congrFun h (nd 3); revert this; decide)
      (fun s => by
        have := hle (shortF4 2) (mshort 2) (hpa ▸ xPair_mem θ hθ ha hρa s)
        exact this)
      (fun t => by
        have := hle (shortF4 5) (mshort 5) (hpb ▸ xPair_mem θ hθ hb hρb t)
        exact this) v hv
  have h1n : twistedRootGroup k θ (-Pi.single (1 : Fin 4) 1) ≤ T := by
    have ha : IsRoot .E6 (-e6a) := RootOps.isRootB_iff.1 (by decide)
    have hb : IsRoot .E6 (-e6b) := RootOps.isRootB_iff.1 (by decide)
    have hρa : rho (-e6a) ≠ -e6a := fun h => by
      have := congrFun h (nd 4); revert this; decide
    have hρb : rho (-e6b) ≠ -e6b := fun h => by
      have := congrFun h (nd 4); revert this; decide
    have hab : -e6a + -e6b = -e6c := by funext i; fin_cases i <;> decide
    have hpa : proj (-e6a) = shortF4 3 := by funext i; fin_cases i <;> decide
    have hpb : proj (-e6b) = shortF4 4 := by funext i; fin_cases i <;> decide
    have hpc : proj (-e6c) = -Pi.single (1 : Fin 4) 1 := by funext i; fin_cases i <;> decide
    intro g hg
    obtain ⟨v, hv, hgv⟩ := (mem_twistedRootGroup_iff_of_fixed θ hrootc' hpc hfixc' g).1 hg
    have : g = xFixed θ hrootc' hfixc' v hv := Subtype.ext hgv
    rw [this]
    exact xFixed_mem_of_pairs θ hθ h2 hne ha hb hrootc' hρa hρb hfixc' hab
      (not_isRoot_E6_of_false (by decide)) (fun h => by
        have := congrFun h (nd 4); revert this; decide)
      (not_isRoot_E6_of_false (by decide)) (fun h => by
        have := congrFun h (nd 4); revert this; decide)
      (not_isRoot_E6_of_false (by decide)) (fun h => by
        have := congrFun h (nd 3); revert this; decide)
      (not_isRoot_E6_of_false (by decide)) (fun h => by
        have := congrFun h (nd 3); revert this; decide)
      (fun s => by
        have := hle (shortF4 3) (mshort 3) (hpa ▸ xPair_mem θ hθ ha hρa s)
        exact this)
      (fun t => by
        have := hle (shortF4 4) (mshort 4) (hpb ▸ xPair_mem θ hθ hb hρb t)
        exact this) v hv
  have hsimple : ∀ i : Fin 4, twistedRootGroup k θ (Pi.single i 1) ≤ T ∧
      twistedRootGroup k θ (-Pi.single i 1) ≤ T := by
    intro i
    fin_cases i
    · have e1 : (Pi.single (0 : Fin 4) 1 : Fin 4 → ℤ) = ![1, 0, 0, 0] := by
        funext j; fin_cases j <;> rfl
      have e2 : (-Pi.single (0 : Fin 4) 1 : Fin 4 → ℤ) = ![-1, 0, 0, 0] := by
        funext j; fin_cases j <;> rfl
      exact ⟨(congrArg (twistedRootGroup k θ) e1).le.trans (hle _ mp),
        (congrArg (twistedRootGroup k θ) e2).le.trans (hle _ mn)⟩
    · exact ⟨h1p, h1n⟩
    · have e1 : (Pi.single (2 : Fin 4) 1 : Fin 4 → ℤ) = shortF4 4 := by
        funext j; fin_cases j <;> rfl
      have e2 : (-Pi.single (2 : Fin 4) 1 : Fin 4 → ℤ) = shortF4 5 := by
        funext j; fin_cases j <;> rfl
      exact ⟨(congrArg (twistedRootGroup k θ) e1).le.trans (hle _ (mshort 4)),
        (congrArg (twistedRootGroup k θ) e2).le.trans (hle _ (mshort 5))⟩
    · have e1 : (Pi.single (3 : Fin 4) 1 : Fin 4 → ℤ) = shortF4 6 := by
        funext j; fin_cases j <;> rfl
      have e2 : (-Pi.single (3 : Fin 4) 1 : Fin 4 → ℤ) = shortF4 7 := by
        funext j; fin_cases j <;> rfl
      exact ⟨(congrArg (twistedRootGroup k θ) e1).le.trans (hle _ (mshort 6)),
        (congrArg (twistedRootGroup k θ) e2).le.trans (hle _ (mshort 7))⟩
  have hct := twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ)
  refine eq_top_iff.mpr ?_
  rw [← iSup_rankOne_eq_top hct]
  exact iSup_le fun i => sup_le (hsimple i).1 (hsimple i).2

end Generation

section Criterion

theorem isRoot_F4_of_mem_shortSetE6 {γ : Fin 4 → ℤ} (h : γ ∈ shortSetE6) : IsRoot .F4 γ := by
  rcases h with (rfl | rfl) | h
  · exact RootOps.isRootB_iff.1 (by decide)
  · exact RootOps.isRootB_iff.1 (by decide)
  · exact isRoot_of_mem_shortSetF4 h

variable {p : ℕ} [Fact p.Prime]

theorem commFamilyConnected_twistedE6 {e : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .twistedE6 0 p e) :
    CommFamilyConnected (ModelFund p .twistedE6 0 e) := by
  refine commFamilyConnected_modelFund_of_short hp2 trivial hadm (by decide) (by decide) ?_
  have hf : 1 ≤ e := hadm.2.1
  have hlong := ModelFacts.isLongestRoot_single .twistedE6 0 p e Fact.out trivial hadm
    ⟨0, (by decide : 0 < 4)⟩ (by show 0 < 2; omega)
  have hθ := Exceptional.frobQ_frobQ p e hf
  have hne : ∃ w : GaloisField p (2 * e), Exceptional.frobQ p e w ≠ w := by
    obtain ⟨a, ha⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_ne (K := GaloisField p (2 * e))
      (p := p) (f := e) (card_galoisField_two_mul p e hf)
    exact ⟨a, by rw [Exceptional.frobQ_apply]; exact ha⟩
  have hεroot : IsRoot .F4 (![1, 2, 2, 2] : Fin (Tag.rank .F4) → ℤ) :=
    RootOps.isRootB_iff.1 (by decide)
  have hlongε : ModelFacts.IsLongestRoot (modelUniv .twistedE6 0 p e Fact.out).D
      (![1, 2, 2, 2] : Fin (Tag.rank .F4) → ℤ) := by
    refine ⟨?_, fun ε' hε' => ?_⟩
    · show _ ∈ (twistedDatum (GaloisField p (2 * e)) (Exceptional.frobQ p e)).roots
      rw [twistedDatum_roots]
      exact hεroot
    have h1 := hlong.2 ε' hε'
    have e1 : ModelFacts.lenSq (modelUniv .twistedE6 0 p e Fact.out).D.isFiniteType
        (![1, 2, 2, 2] : Fin 4 → ℤ) =
        ModelFacts.lenSq (modelUniv .twistedE6 0 p e Fact.out).D.isFiniteType
          (Pi.single (0 : Fin 4) 1 : Fin 4 → ℤ) := by
      refine (lenSq_F4 _ rfl _).trans ?_
      refine Eq.trans ?_ (lenSq_F4 _ rfl _).symm
      rw [bF4_eps_eps]
    exact h1.trans_eq e1.symm
  refine ⟨Pi.single ⟨0, (by decide : 0 < 4)⟩ 1, shortSetE6, hlong, fun γ hγ => ?_,
    iSup_shortSetE6_eq_top (Exceptional.frobQ p e) hθ
      (ModelFacts.two_ne_zero_galoisField (2 * e) hp2) hne, fun γ hγ => ?_⟩
  · show γ ∈ (twistedDatum (GaloisField p (2 * e)) (Exceptional.frobQ p e)).roots
    rw [twistedDatum_roots]
    exact isRoot_F4_of_mem_shortSetE6 hγ
  · rcases hγ with (rfl | rfl) | ⟨k, rfl⟩
    · refine Or.inl ?_
      funext j; fin_cases j <;> rfl
    · refine Or.inr (Or.inl ?_)
      funext j; fin_cases j <;> rfl
    · by_cases hk : k.val < 4
      · exact Or.inr (Or.inr (Or.inr ⟨![1, 2, 2, 2], hlongε,
          form_F4_eq_zero _ rfl bF4_alpha_eps, form_F4_eq_zero _ rfl (bF4_eps_short k hk)⟩))
      · exact Or.inr (Or.inr (Or.inl (form_F4_eq_zero _ rfl (bF4_alpha_short k (by omega)))))

end Criterion

end CFSG.ClassicalInvolution.RouteD
