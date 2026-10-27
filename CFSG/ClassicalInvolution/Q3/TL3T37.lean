module

public import CFSG.ClassicalInvolution.Q3.TL3T36

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.TL4

section Model

variable {n : ℕ}

theorem zBar_congr {α β : Finset (Fin n)} (e : α = β) (h : α.card = 4) (h' : β.card = 4) :
    zBar α h = zBar β h' := by
  subst e
  rfl

theorem aut_vec_eq_conj (hn : 5 ≤ n) (θ : MulAut ↥(TL4.aeModel n)) {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ τ : alternatingGroup (Fin n), (autAlt hn θ τ : Equiv.Perm (Fin n)) = σ * τ * σ⁻¹)
    {γ : Finset (Fin n)} (hγ : γ.card = 4) (hσγ : γ.map σ.toEmbedding = γ)
    (hz : θ ⟨zBar γ hγ, zBar_mem_aeModel γ hγ⟩ = ⟨zBar γ hγ, zBar_mem_aeModel γ hγ⟩)
    (v : ↥(TL4.aeModel n)) (hv : permQ n v = 1) :
    ((θ v : ↥(TL4.aeModel n)) : AEQ n) = mkQ n (ofPerm σ) * v * (mkQ n (ofPerm σ))⁻¹ := by
  classical
  set s : AEQ n := mkQ n (ofPerm σ) with hs
  have hpθ : ∀ x : ↥(TL4.aeModel n), permQ n (θ x) = σ * permQ n x * σ⁻¹ := fun x => by
    rw [permQ_aut_apply hn θ x, ← autAlt_apply hn θ, hσ]
  have hps : permQ n s = σ := by rw [hs, permQ_mkQ]; rfl
  have hconj : ∀ x w : ↥(TL4.aeModel n), permQ n w = 1 →
      ((θ (x * w * x⁻¹) : ↥(TL4.aeModel n)) : AEQ n) =
        (s * x * s⁻¹) * θ w * (s * x * s⁻¹)⁻¹ := by
    intro x w hw
    set e : AEQ n := (s * x * s⁻¹)⁻¹ * θ x with he
    have hpe : permQ n e = 1 := by
      rw [he, map_mul, map_inv, map_mul, map_mul, map_inv, hpθ x, hps]
      group
    have hpw : permQ n ((θ w : ↥(TL4.aeModel n)) : AEQ n) = 1 := by
      rw [hpθ, hw]
      group
    have hc := comm_of_mem_ker_permQ hpe hpw
    have hθx : ((θ x : ↥(TL4.aeModel n)) : AEQ n) = (s * x * s⁻¹) * e := by
      rw [he]
      group
    rw [map_mul, map_mul, map_inv]
    push_cast
    rw [hθx]
    calc s * x * s⁻¹ * e * (θ w : AEQ n) * (s * x * s⁻¹ * e)⁻¹ =
        s * x * s⁻¹ * (e * (θ w : AEQ n)) * e⁻¹ * (s * x * s⁻¹)⁻¹ := by group
      _ = s * x * s⁻¹ * ((θ w : AEQ n) * e) * e⁻¹ * (s * x * s⁻¹)⁻¹ := by rw [hc]
      _ = s * x * s⁻¹ * (θ w : AEQ n) * (s * x * s⁻¹)⁻¹ := by group
  have hsz : s⁻¹ * zBar γ hγ * s = zBar γ hγ := by
    have h1 : s * zBar γ hγ * s⁻¹ = zBar γ hγ := by
      rw [hs, conj_zBar_ofPerm σ γ hγ (by rw [Finset.card_map]; exact hγ)]
      exact zBar_congr hσγ _ _
    conv_lhs => rw [← h1]
    group
  have hzδ : ∀ (δ : Finset (Fin n)) (hδ : δ.card = 4),
      ((θ ⟨zBar δ hδ, zBar_mem_aeModel δ hδ⟩ : ↥(TL4.aeModel n)) : AEQ n) =
        s * zBar δ hδ * s⁻¹ := by
    intro δ hδ
    obtain ⟨τ, hτ, hτδ⟩ := exists_alt_map_eq hγ hδ
    subst hτδ
    set x : ↥(TL4.aeModel n) := ⟨mkQ n (ofPerm τ), mem_aeModel_ofPerm hτ⟩ with hx
    have hz' : (⟨zBar (γ.map τ.toEmbedding) hδ, zBar_mem_aeModel _ hδ⟩ : ↥(TL4.aeModel n)) =
        x * ⟨zBar γ hγ, zBar_mem_aeModel γ hγ⟩ * x⁻¹ := by
      apply Subtype.ext
      push_cast
      exact (conj_zBar_ofPerm τ γ hγ hδ).symm
    have hpz : permQ n (zBar γ hγ) = 1 := by rw [zBar, permQ_mkQ, zOf_perm]
    rw [hz', hconj x _ hpz, hz]
    push_cast
    calc s * (x : AEQ n) * s⁻¹ * zBar γ hγ * (s * x * s⁻¹)⁻¹ =
        s * x * (s⁻¹ * zBar γ hγ * s) * (x : AEQ n)⁻¹ * s⁻¹ := by group
      _ = s * (x * zBar γ hγ * (x : AEQ n)⁻¹) * s⁻¹ := by rw [hsz]; group
      _ = s * zBar (γ.map τ.toEmbedding) hδ * s⁻¹ := by
        rw [show (x : AEQ n) * zBar γ hγ * (x : AEQ n)⁻¹ = zBar _ hδ from
          conj_zBar_ofPerm τ γ hγ hδ]
  set F : Subgroup (AEQ n) := (MonoidHom.eqLocus ((TL4.aeModel n).subtype.comp θ.toMonoidHom)
    ((MulAut.conj s).toMonoidHom.comp (TL4.aeModel n).subtype)).map (TL4.aeModel n).subtype
    with hF
  have hmem : ∀ (δ : Finset (Fin n)) (hδ : δ.card = 4), zBar δ hδ ∈ F := fun δ hδ =>
    ⟨⟨zBar δ hδ, zBar_mem_aeModel δ hδ⟩, by
      show ((θ ⟨zBar δ hδ, zBar_mem_aeModel δ hδ⟩ : ↥(TL4.aeModel n)) : AEQ n) =
        MulAut.conj s (zBar δ hδ)
      rw [MulAut.conj_apply]
      exact hzδ δ hδ, rfl⟩
  obtain ⟨a, ha, hav⟩ := v.2
  have hap : a.perm = 1 := by rw [← permQ_mkQ, hav]; exact hv
  have ha' : a = ofVec a.vec := Wr.ext rfl hap
  have hsum : ∑ i, a.vec i = 0 := ha.1
  have := mem_of_zBar_mem hn hmem hsum
  rw [← ha', hav] at this
  obtain ⟨w, hw, hwv⟩ := this
  have hw' : w = v := Subtype.ext hwv
  subst hw'
  have e : ((θ w : ↥(TL4.aeModel n)) : AEQ n) = MulAut.conj s (w : AEQ n) := hw
  rw [e, MulAut.conj_apply]

theorem embed_ofVec (ι : Fin 4 ↪ Fin n) (w : Fin 4 → ZMod 2) :
    embed ι (ofVec w) = ofVec (embedVec ι w) :=
  Wr.ext rfl (embedPerm_one ι)

theorem actV_embedVec_of_fix {ι : Fin 4 ↪ Fin n} {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ i, σ (ι i) = ι i) (w : Fin 4 → ZMod 2) : actV σ (embedVec ι w) = embedVec ι w := by
  funext x
  simp only [actV]
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    rw [show σ.symm (ι i) = ι i by rw [Equiv.symm_apply_eq, hσ]]
  · have hx' : σ.symm x ∉ Set.range ι := by
      rintro ⟨i, hi⟩
      apply hx
      refine ⟨i, ?_⟩
      have := congrArg σ hi
      rwa [Equiv.apply_symm_apply, hσ] at this
    rw [embedVec_of_not_mem ι w hx, embedVec_of_not_mem ι w hx']

theorem map_eq_of_fix {σ : Equiv.Perm (Fin n)} {γ : Finset (Fin n)} (hσ : ∀ x ∈ γ, σ x = x) :
    γ.map σ.toEmbedding = γ := by
  ext y
  rw [Finset.mem_map_equiv]
  constructor
  · intro h
    have e := hσ _ h
    rw [Equiv.apply_symm_apply] at e
    rw [e]
    exact h
  · intro h
    rwa [show σ.symm y = y by rw [Equiv.symm_apply_eq, hσ y h]]

theorem exists_mem_list_of_mem_memBar {γ : Finset (Fin n)} {hγ : γ.card = 4} {c : Bool}
    {x : AEQ n} (hx : x ∈ memBar γ hγ c) :
    ∃ k ∈ (bif c then kList else kStarList), x = mkQ n (embed (emb γ hγ) k) := by
  obtain ⟨a, ha, rfl⟩ := hx
  cases c
  · obtain ⟨k, hk, rfl⟩ := ha
    exact ⟨k, hk, rfl⟩
  · obtain ⟨k, hk, rfl⟩ := ha
    exact ⟨k, hk, rfl⟩

theorem mkQ_embed_mem_memBar {γ : Finset (Fin n)} {hγ : γ.card = 4} {c : Bool} {k : Wr 4}
    (hk : k ∈ (bif c then kList else kStarList)) : mkQ n (embed (emb γ hγ) k) ∈ memBar γ hγ c := by
  refine ⟨embed (emb γ hγ) k, ?_, rfl⟩
  cases c
  · exact ⟨k, hk, rfl⟩
  · exact ⟨k, hk, rfl⟩

theorem exists_twin_list : ∀ c : Bool, ∀ k ∈ (bif !c then kList else kStarList),
    ∃ k' ∈ (bif c then kList else kStarList), k'.perm = k.perm := by
  decide +kernel

theorem aut_fix_twin (hn : 5 ≤ n) (θ : MulAut ↥(TL4.aeModel n)) (hθ : ∃ k : ℕ, θ ^ 3 ^ k = 1)
    {γ : Finset (Fin n)} (hγ : γ.card = 4) {b : Bool}
    (hcγ : ∀ x (hx : x ∈ memBar γ hγ b),
      θ ⟨x, memBar_le_aeModel γ hγ b hx⟩ = ⟨x, memBar_le_aeModel γ hγ b hx⟩) :
    ∀ x (hx : x ∈ memBar γ hγ (!b)),
      θ ⟨x, memBar_le_aeModel γ hγ (!b) hx⟩ = ⟨x, memBar_le_aeModel γ hγ (!b) hx⟩ := by
  classical
  obtain ⟨σ, hσk, hσ⟩ := exists_perm_of_aut hn θ hθ
  have hfix := fix_of_cent hn θ hσk hσ hcγ
  have hfixι : ∀ i, σ (emb γ hγ i) = emb γ hγ i := fun i => hfix _ (by
    have : emb γ hγ i ∈ Set.range (emb γ hγ) := Set.mem_range_self i
    rw [range_emb] at this
    exact_mod_cast this)
  have hvec := aut_vec_eq_conj hn θ hσ hγ (map_eq_of_fix hfix) (hcγ _ (zBar_mem_memBar γ hγ b))
  intro x hx
  obtain ⟨k, hk, rfl⟩ := exists_mem_list_of_mem_memBar hx
  obtain ⟨k', hk', hkk'⟩ := exists_twin_list b k hk
  have hx' := mkQ_embed_mem_memBar (γ := γ) (hγ := hγ) hk'
  set w : Fin 4 → ZMod 2 := (k * k'⁻¹).vec with hw
  have hkw : k * k'⁻¹ = ofVec w := Wr.ext rfl (by rw [mul_perm, inv_perm, hkk', mul_inv_cancel]; rfl)
  have hv : mkQ n (embed (emb γ hγ) k) =
      mkQ n (ofVec (embedVec (emb γ hγ) w)) * mkQ n (embed (emb γ hγ) k') := by
    rw [← embed_ofVec, ← hkw, ← map_mul, ← map_mul, inv_mul_cancel_right]
  have hvm : mkQ n (ofVec (embedVec (emb γ hγ) w)) ∈ TL4.aeModel n := by
    have h1 := memBar_le_aeModel γ hγ (!b) hx
    have h2 := memBar_le_aeModel γ hγ b hx'
    have e : mkQ n (ofVec (embedVec (emb γ hγ) w)) =
        mkQ n (embed (emb γ hγ) k) * (mkQ n (embed (emb γ hγ) k'))⁻¹ := by
      rw [hv, mul_inv_cancel_right]
    rw [e]
    exact (TL4.aeModel n).mul_mem h1 ((TL4.aeModel n).inv_mem h2)
  have hθv : θ ⟨_, hvm⟩ = ⟨_, hvm⟩ := by
    apply Subtype.ext
    rw [hvec ⟨_, hvm⟩ (by rw [permQ_mkQ]; rfl)]
    show mkQ n (ofPerm σ) * vbar n (embedVec (emb γ hγ) w) * (mkQ n (ofPerm σ))⁻¹ =
      vbar n (embedVec (emb γ hγ) w)
    rw [conj_vbar (permBar_mkQ (ofPerm σ))]
    exact congrArg (vbar n) (actV_embedVec_of_fix hfixι w)
  have e : (⟨mkQ n (embed (emb γ hγ) k), memBar_le_aeModel γ hγ (!b) hx⟩ : ↥(TL4.aeModel n)) =
      ⟨_, hvm⟩ * ⟨_, memBar_le_aeModel γ hγ b hx'⟩ := Subtype.ext hv
  rw [e, map_mul, hθv, hcγ _ hx']

theorem embedVec_pairVec (ι : Fin 4 ↪ Fin n) (i j : Fin 4) :
    embedVec ι (pairVec i j) = pairVec (ι i) (ι j) := by
  funext x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨l, rfl⟩ := hx
    rw [embedVec_apply, pairVec_apply, pairVec_apply]
    simp only [ι.injective.eq_iff]
  · rw [embedVec_of_not_mem ι _ hx, pairVec_apply]
    have h1 : x ≠ ι i := fun h => hx ⟨i, h.symm⟩
    have h2 : x ≠ ι j := fun h => hx ⟨j, h.symm⟩
    simp [h1, h2]

theorem pair_mem_twins : ∀ c : Bool, ∀ i j : Fin 4, i ≠ j →
    ∃ k ∈ (bif c then kList else kStarList), ∃ k' ∈ (bif !c then kList else kStarList),
      k * k' = ofVec (pairVec i j) := by
  decide +kernel

theorem mem_range_iff_of_comm {ι : Fin 4 ↪ Fin n} {σ : Equiv.Perm (Fin n)}
    (h1 : σ * embedPerm ι d₁ = embedPerm ι d₁ * σ) (x : Fin n) :
    σ x ∈ Set.range ι ↔ x ∈ Set.range ι := by
  have hsupp : ∀ x, x ∈ Set.range ι ↔ embedPerm ι d₁ x ≠ x := by
    intro x
    constructor
    · rintro ⟨i, rfl⟩
      rw [embedPerm_apply]
      intro h
      exact (by decide : ∀ i : Fin 4, d₁ i ≠ i) i (ι.injective h)
    · intro h
      by_contra hx
      exact h (embedPerm_of_not_mem ι d₁ hx)
  have hc : embedPerm ι d₁ (σ x) = σ (embedPerm ι d₁ x) := by
    have := congrArg (fun f : Equiv.Perm (Fin n) => f x) h1
    simpa [Equiv.Perm.mul_apply] using this.symm
  rw [hsupp, hsupp, hc]
  exact σ.injective.ne_iff

theorem map_eq_of_comm_d₁ {α : Finset (Fin n)} {hα : α.card = 4} {σ : Equiv.Perm (Fin n)}
    (h1 : σ * embedPerm (emb α hα) d₁ = embedPerm (emb α hα) d₁ * σ) :
    α.map σ.toEmbedding = α := by
  ext y
  rw [Finset.mem_map_equiv]
  have hr : ∀ z, z ∈ α ↔ z ∈ Set.range (emb α hα) := fun z => by rw [range_emb]; rfl
  rw [hr, hr, ← mem_range_iff_of_comm h1 (σ.symm y), Equiv.apply_symm_apply]

theorem comm_embedPerm_of_fix {ι : Fin 4 ↪ Fin n} {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ i, σ (ι i) = ι i) (τ : Equiv.Perm (Fin 4)) :
    σ * embedPerm ι τ = embedPerm ι τ * σ := by
  have hσ' : ∀ x, x ∉ Set.range ι → σ x ∉ Set.range ι := by
    rintro x hx ⟨i, hi⟩
    apply hx
    refine ⟨i, ?_⟩
    rw [← Equiv.symm_apply_apply σ x, ← hi, Equiv.eq_symm_apply, hσ]
  refine Equiv.ext fun x => ?_
  simp only [Equiv.Perm.mul_apply]
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    rw [embedPerm_apply, hσ, hσ, embedPerm_apply]
  · rw [embedPerm_of_not_mem ι τ hx, embedPerm_of_not_mem ι τ (hσ' x hx)]

theorem yBar_comm_of_comm_memBar (hn : 5 ≤ n) {α : Finset (Fin n)} {hα : α.card = 4} {b : Bool}
    {u : Fin n → ZMod 2} (hu : ∀ x ∈ memBar α hα b, vbar n u * x = x * vbar n u) :
    yBar α hα * vbar n u = vbar n u * yBar α hα := by
  classical
  set ι := emb α hα with hι
  have hlt : α.card < (Finset.univ : Finset (Fin n)).card := by
    rw [hα, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨x₀, -, hx₀⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hx₀ι : x₀ ∉ Set.range ι := by rw [hι, range_emb]; exact_mod_cast hx₀
  have hd : ∀ d ∈ [d₁, d₂, d₃], actV (embedPerm ι d) u = u := by
    intro d hdm
    obtain ⟨k, hk, hkd⟩ := exists_kList_perm b d hdm
    have hx := mkQ_embed_mem_memBar (γ := α) (hγ := hα) hk
    have h2 : mkQ n (embed ι k) * vbar n u * (mkQ n (embed ι k))⁻¹ = vbar n u := by
      rw [← hu _ hx, mul_inv_cancel_right]
    rw [conj_vbar (permBar_mkQ _)] at h2
    have h3 := vbar_eq_iff.mp h2
    rw [embed_perm, hkd] at h3
    rcases h3 with h3 | h3
    · exact h3
    · exfalso
      have := congrFun h3 x₀
      simp only [actV, Pi.add_apply, Pi.one_apply] at this
      rw [embedPerm_symm_of_not_mem ι d hx₀ι] at this
      revert this
      generalize u x₀ = c
      revert c
      decide
  have hfix : ∀ d ∈ [d₁, d₂, d₃], ∀ i, u (ι (d.symm i)) = u (ι i) := by
    intro d hdm i
    have := congrFun (hd d hdm) (ι i)
    simp only [actV] at this
    rwa [embedPerm_symm_apply] at this
  have e1 := hfix d₁ (by simp) 1
  have e2 := hfix d₂ (by simp) 2
  have e3 := hfix d₃ (by simp) 3
  rw [show d₁.symm 1 = 0 by decide] at e1
  rw [show d₂.symm 2 = 0 by decide] at e2
  rw [show d₃.symm 3 = 0 by decide] at e3
  have hconst : ∀ i, u (ι i) = u (ι 0) := by
    intro i
    fin_cases i
    · rfl
    · exact e1.symm
    · exact e2.symm
    · exact e3.symm
  have hact : actV (embedPerm ι yQ.perm) u = u := by
    funext x
    simp only [actV]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [embedPerm_symm_apply, hconst]
      exact (hconst i).symm
    · rw [embedPerm_symm_of_not_mem ι _ hx]
  have h4 : yBar α hα * vbar n u * (yBar α hα)⁻¹ = vbar n u := by
    rw [yBar, conj_vbar (permBar_mkQ _)]
    exact congrArg (vbar n) hact
  calc yBar α hα * vbar n u = yBar α hα * vbar n u * (yBar α hα)⁻¹ * yBar α hα := by group
    _ = vbar n u * yBar α hα := by rw [h4]

theorem aut_fix_yBar (hn : 5 ≤ n) (hn6 : n ≠ 6) (θ : MulAut ↥(TL4.aeModel n))
    {α : Finset (Fin n)} (hα : α.card = 4) {b : Bool}
    (hc : ∀ x (hx : x ∈ memBar α hα b),
      θ ⟨x, memBar_le_aeModel α hα b hx⟩ = ⟨x, memBar_le_aeModel α hα b hx⟩)
    (hc' : ∀ x (hx : x ∈ memBar α hα (!b)),
      θ ⟨x, memBar_le_aeModel α hα (!b) hx⟩ = ⟨x, memBar_le_aeModel α hα (!b) hx⟩) :
    θ ⟨yBar α hα, yBar_mem α hα⟩ = ⟨yBar α hα, yBar_mem α hα⟩ := by
  classical
  set ι := emb α hα with hι
  obtain ⟨σ, hσ'⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6).2 (autAlt hn θ)
  have hσ : ∀ τ : alternatingGroup (Fin n),
      (autAlt hn θ τ : Equiv.Perm (Fin n)) = σ * τ * σ⁻¹ := fun τ => by
    rw [← hσ', MulAut.conjNormal_apply]
  have hpθ : ∀ x : ↥(TL4.aeModel n), permQ n (θ x) = σ * permQ n x * σ⁻¹ := fun x => by
    rw [permQ_aut_apply hn θ x, ← autAlt_apply hn θ, hσ]
  have hσα : α.map σ.toEmbedding = α :=
    map_eq_of_comm_d₁ (comm_embedPerm_of_cent hn θ hσ hc (by simp))
  have hvec := aut_vec_eq_conj hn θ hσ hα hσα (hc _ (zBar_mem_memBar α hα b))
  have hpair : ∀ i j : Fin 4, i ≠ j →
      ModPi (pairVec (σ (ι i)) (σ (ι j))) (pairVec (ι i) (ι j)) := by
    intro i j hij
    obtain ⟨k, hk, k', hk', hkk'⟩ := pair_mem_twins b i j hij
    have hx := mkQ_embed_mem_memBar (γ := α) (hγ := hα) hk
    have hx' := mkQ_embed_mem_memBar (γ := α) (hγ := hα) hk'
    have e : vbar n (pairVec (ι i) (ι j)) = mkQ n (embed ι k) * mkQ n (embed ι k') := by
      rw [← map_mul, ← map_mul, hkk', embed_ofVec, embedVec_pairVec]
      rfl
    have hm : vbar n (pairVec (ι i) (ι j)) ∈ TL4.aeModel n := by
      rw [e]
      exact (TL4.aeModel n).mul_mem (memBar_le_aeModel α hα b hx)
        (memBar_le_aeModel α hα (!b) hx')
    have hθ1 : θ ⟨_, hm⟩ = ⟨_, hm⟩ := by
      have e' : (⟨_, hm⟩ : ↥(TL4.aeModel n)) =
          ⟨_, memBar_le_aeModel α hα b hx⟩ * ⟨_, memBar_le_aeModel α hα (!b) hx'⟩ :=
        Subtype.ext e
      rw [e', map_mul, hc _ hx, hc' _ hx']
    have h2 := congrArg Subtype.val hθ1
    rw [hvec ⟨_, hm⟩ rfl] at h2
    change mkQ n (ofPerm σ) * vbar n (pairVec (ι i) (ι j)) * (mkQ n (ofPerm σ))⁻¹ =
      vbar n (pairVec (ι i) (ι j)) at h2
    rw [conj_vbar (permBar_mkQ (ofPerm σ))] at h2
    have h3 := vbar_eq_iff.mp h2
    rwa [show (ofPerm σ).perm = σ from rfl, actV_pairVec] at h3
  have hfixι : ∀ i, σ (ι i) = ι i := by
    intro i
    obtain ⟨j, hij, l, hil, hjl⟩ : ∃ j, i ≠ j ∧ ∃ l, i ≠ l ∧ j ≠ l := by
      revert i
      decide
    have h1 := (pair_eq_of_modPi hn (ι.injective.ne hij) (hpair i j hij)).1
    have h2 := (pair_eq_of_modPi hn (ι.injective.ne hil) (hpair i l hil)).1
    rcases h1 with h1 | h1
    · exact h1
    rcases h2 with h2 | h2
    · exact h2
    exact absurd (ι.injective (h1.symm.trans h2)) hjl
  set y : ↥(TL4.aeModel n) := ⟨yBar α hα, yBar_mem α hα⟩ with hy
  set v : ↥(TL4.aeModel n) := θ y * y⁻¹ with hv
  have hpy : permQ n (y : AEQ n) = embedPerm ι yQ.perm := rfl
  have hpv : permQ n (v : AEQ n) = 1 := by
    rw [hv]
    push_cast
    rw [map_mul, map_inv, hpθ, hpy, comm_embedPerm_of_fix hfixι]
    group
  obtain ⟨u, hu⟩ := exists_vbar_of_permBar_eq_one (n := n) (g := v) (by rw [permBar_eq_permQ, hpv])
  have hvc : ∀ x ∈ memBar α hα b, vbar n u * x = x * vbar n u := by
    intro x hx
    have hy3 := yBar_pow_three α hα
    have hyi : (yBar α hα)⁻¹ = yBar α hα * yBar α hα := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [mul_assoc, ← pow_three]
      exact hy3
    have hx₀ : (yBar α hα)⁻¹ * x * yBar α hα ∈ memBar α hα b := by
      have h2 := yBar_conj_mem_memBar α hα b _ (yBar_conj_mem_memBar α hα b x hx)
      have e : (yBar α hα)⁻¹ * x * yBar α hα =
          yBar α hα * (yBar α hα * x * (yBar α hα)⁻¹) * (yBar α hα)⁻¹ := by
        calc (yBar α hα)⁻¹ * x * yBar α hα =
            (yBar α hα * yBar α hα) * x * (yBar α hα * yBar α hα)⁻¹ := by
              rw [← hyi, inv_inv]
          _ = yBar α hα * (yBar α hα * x * (yBar α hα)⁻¹) * (yBar α hα)⁻¹ := by group
      rw [e]
      exact h2
    set X₀ : ↥(TL4.aeModel n) := ⟨_, memBar_le_aeModel α hα b hx₀⟩ with hX₀
    set X : ↥(TL4.aeModel n) := ⟨x, memBar_le_aeModel α hα b hx⟩ with hX
    have hXe : X = y * X₀ * y⁻¹ := Subtype.ext (by
      rw [hX, hX₀, hy]
      push_cast
      group)
    have hθX₀ : θ X₀ = X₀ := hc _ hx₀
    have hθX : θ X = X := hc _ hx
    have h1 : θ X = v * X * v⁻¹ := by
      rw [hXe, map_mul, map_mul, map_inv, hθX₀, hv]
      group
    rw [hθX] at h1
    have h2 : x = vbar n u * x * (vbar n u)⁻¹ := by
      have := congrArg Subtype.val h1
      push_cast at this
      rw [hu] at this
      exact this
    calc vbar n u * x = vbar n u * x * (vbar n u)⁻¹ * vbar n u := by group
      _ = x * vbar n u := by rw [← h2]
  have hcomm : Commute v y := Subtype.ext (by
    show (v : AEQ n) * yBar α hα = yBar α hα * v
    rw [hu]
    exact (yBar_comm_of_comm_memBar hn hvc).symm)
  have hθy : θ y = v * y := by rw [hv]; group
  have hy3 : y ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact yBar_pow_three α hα)
  have hvv : v * v = 1 := Subtype.ext (mul_self_of_mem_ker_permQ hpv)
  have h3 : θ y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  rw [hθy, hcomm.mul_pow, hy3, mul_one, pow_three, hvv, mul_one] at h3
  rw [hθy, h3, one_mul]

theorem vbar_pairVec_mem_aeModel (a b : Fin n) : vbar n (pairVec a b) ∈ TL4.aeModel n := by
  rw [TL4.aeModel_eq]
  exact vbar_mem_aeBarOver (sum_pairVec a b)

theorem aut_eq_one_of_cent_pair (hn7 : n = 7) (θ : MulAut ↥(TL4.aeModel n))
    (hθ : ∃ k : ℕ, θ ^ 3 ^ k = 1) {γ : Finset (Fin n)} (hγ : γ.card = 4) {b₀ : Bool}
    (hcγ : ∀ x (hx : x ∈ memBar γ hγ b₀),
      θ ⟨x, memBar_le_aeModel γ hγ b₀ hx⟩ = ⟨x, memBar_le_aeModel γ hγ b₀ hx⟩)
    {a b : Fin n} (hab : a ≠ b) (ha : a ∉ γ) (hb : b ∉ γ)
    (hw : θ ⟨vbar n (pairVec a b), vbar_pairVec_mem_aeModel a b⟩ =
      ⟨vbar n (pairVec a b), vbar_pairVec_mem_aeModel a b⟩) : θ = 1 := by
  classical
  have hn : 5 ≤ n := by omega
  obtain ⟨σ, hσk, hσ⟩ := exists_perm_of_aut hn θ hθ
  have hfix := fix_of_cent hn θ hσk hσ hcγ
  have hvec := aut_vec_eq_conj hn θ hσ hγ (map_eq_of_fix hfix) (hcγ _ (zBar_mem_memBar γ hγ b₀))
  have h2 := congrArg Subtype.val hw
  rw [hvec _ rfl] at h2
  change mkQ n (ofPerm σ) * vbar n (pairVec a b) * (mkQ n (ofPerm σ))⁻¹ =
    vbar n (pairVec a b) at h2
  rw [conj_vbar (permBar_mkQ (ofPerm σ))] at h2
  have h3 := vbar_eq_iff.mp h2
  rw [show (ofPerm σ).perm = σ from rfl, actV_pairVec] at h3
  obtain ⟨hσa, hσb⟩ := pair_eq_of_modPi hn hab h3
  have hσab : σ a ≠ σ b := fun e => hab (σ.injective e)
  have hσσa : σ (σ a) = a := by
    rcases hσa with h | h
    · rw [h, h]
    · rw [h]
      rcases hσb with h' | h'
      · exact h'
      · exact absurd (h.trans h'.symm) hσab
  have hσσb : σ (σ b) = b := by
    rcases hσb with h | h
    · rw [h]
      rcases hσa with h' | h'
      · exact absurd (h'.trans h.symm) hσab
      · exact h'
    · rw [h, h]
  have hcard : ((γᶜ.erase a).erase b).card ≤ 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_compl.mpr hb⟩),
      Finset.card_erase_of_mem (Finset.mem_compl.mpr ha), Finset.card_compl, hγ,
      Fintype.card_fin]
    omega
  have hsq : σ ^ 2 = 1 := by
    refine Equiv.ext fun x => ?_
    rw [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    by_cases hx : x ∈ γ
    · rw [hfix x hx, hfix x hx]
    by_cases hxa : x = a
    · rw [hxa, hσσa]
    by_cases hxb : x = b
    · rw [hxb, hσσb]
    have hσxγ : σ x ∉ γ := fun h => hx (σ.injective (hfix _ h) ▸ h)
    have hσxa : σ x ≠ a := by
      intro e
      rcases hσa with h | h
      · exact hxa (σ.injective (e.trans h.symm))
      · rcases hσb with h' | h'
        · exact hxb (σ.injective (e.trans h'.symm))
        · exact hσab (h.trans h'.symm)
    have hσxb : σ x ≠ b := by
      intro e
      rcases hσb with h | h
      · rcases hσa with h' | h'
        · exact hσab (h'.trans h.symm)
        · exact hxa (σ.injective (e.trans h'.symm))
      · exact hxb (σ.injective (e.trans h.symm))
    have hmem : ∀ y, y ∉ γ → y ≠ a → y ≠ b → y ∈ (γᶜ.erase a).erase b := fun y h1 h2 h3 =>
      Finset.mem_erase.mpr ⟨h3, Finset.mem_erase.mpr ⟨h2, Finset.mem_compl.mpr h1⟩⟩
    have e := Finset.card_le_one.mp hcard _ (hmem _ hσxγ hσxa hσxb) _ (hmem _ hx hxa hxb)
    rw [e, e]
  have hσ1 : σ = 1 := by
    obtain ⟨k, hk⟩ := hσk
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 2 3)) (orderOf_dvd_of_pow_eq_one hsq)
      (orderOf_dvd_of_pow_eq_one hk))
  have hperm : ∀ x : ↥(TL4.aeModel n), permQ n (θ x) = permQ n x := by
    intro x
    rw [permQ_aut_apply hn θ, ← autAlt_apply hn θ, hσ, hσ1, one_mul, inv_one, mul_one]
  exact aut_eq_one_of_fix hn θ hθ hperm hγ (hcγ _ (zBar_mem_memBar γ hγ b₀))

theorem vbar_pairVec_comm_memBar {γ : Finset (Fin n)} {hγ : γ.card = 4} {c : Bool} {p q : Fin n}
    (hp : p ∉ γ) (hq : q ∉ γ) :
    ∀ x ∈ memBar γ hγ c, x * vbar n (pairVec p q) = vbar n (pairVec p q) * x := by
  intro x hx
  obtain ⟨k, -, rfl⟩ := exists_mem_list_of_mem_memBar hx
  have hpι : p ∉ Set.range (emb γ hγ) := by rw [range_emb]; exact_mod_cast hp
  have hqι : q ∉ Set.range (emb γ hγ) := by rw [range_emb]; exact_mod_cast hq
  have h1 : mkQ n (embed (emb γ hγ) k) * vbar n (pairVec p q) *
      (mkQ n (embed (emb γ hγ) k))⁻¹ = vbar n (pairVec p q) := by
    rw [conj_vbar (permBar_mkQ _), embed_perm, actV_pairVec, embedPerm_of_not_mem _ _ hpι,
      embedPerm_of_not_mem _ _ hqι]
  calc mkQ n (embed (emb γ hγ) k) * vbar n (pairVec p q) =
      mkQ n (embed (emb γ hγ) k) * vbar n (pairVec p q) * (mkQ n (embed (emb γ hγ) k))⁻¹ *
        mkQ n (embed (emb γ hγ) k) := by group
    _ = vbar n (pairVec p q) * mkQ n (embed (emb γ hγ) k) := by rw [h1]

end Model

section Transfer

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)} {n : ℕ}

omit [Finite G] in
theorem AEIdent.eq_of_map_eq_of_pow (I : AEIdent P n) (hk : IsPGroup 2 I.φ.ker)
    {u v : ↥(pSpan P)} {a : ℕ} (hu : u ^ 3 ^ a = 1) (hv : v ^ 3 ^ a = 1) (h : I.φ u = I.φ v) :
    u = v := by
  set c := v⁻¹ * u with hc
  have hck : c ∈ I.φ.ker := by rw [MonoidHom.mem_ker, hc, map_mul, map_inv, h, inv_mul_cancel]
  have hcomm : Commute v c := Subgroup.mem_center_iff.mp (I.ker_le hck) v
  have hu' : u = v * c := by rw [hc]; group
  have h1 : c ^ 3 ^ a = 1 := by
    have := hu
    rwa [hu', hcomm.mul_pow, hv, one_mul] at this
  obtain ⟨m, hm⟩ := hk ⟨c, hck⟩
  have h2 : c ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  have h3 : c = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow m a (by norm_num : Nat.Coprime 2 3)) (orderOf_dvd_of_pow_eq_one h2)
    (orderOf_dvd_of_pow_eq_one h1))
  rw [hu', h3, mul_one]

end Transfer

namespace CHyp

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}
  {K J : Subgroup G} (hS : CHyp 3 IH Ω K J)
include hS

theorem y_comm_seven (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) 7) {g : G} {Ks : Subgroup G} {y : G}
    (hD : Data128 Ω K J g Ks y) {α : Finset (Fin 7)} {h : α.card = 4} {b : Bool}
    {y₀ : ↥(pSpan (orbOf (TC.nbrAdj Ω) K J))} (hy₀ : I.φ y₀ = AE.yBar α h)
    (hy₀y : (y₀ : G) = g⁻¹ * y * g)
    (hlab₀ : ((conjSub g⁻¹ K).subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ =
      AE.memBar α h b)
    (hlab₁ : ((conjSub g⁻¹ Ks).subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ =
      AE.memBar α h (!b)) :
    ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), y * x = x * y := by
  classical
  have hn : 5 ≤ 7 := by norm_num
  have hF := hS.graphFam'
  have hK : K ∈ Ω := hS.adj.1
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hJΩ : J ∈ Ω := hS.orb_subset_omega hJπ
  have h8 : ∀ L ∈ Ω, Nat.card L = 8 := fun L hL => by rw [hS.card L hL]; norm_num
  have hPΩ := hS.orb_subset_omega
  have hk : IsPGroup 2 I.φ.ker := I.toLabel.isPGroup_ker hS.oddCore_orb_eq_bot
  have hinv : ∀ L ∈ orbOf (TC.nbrAdj Ω) K J, ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J),
      conjSub x L ∈ orbOf (TC.nbrAdj Ω) K J := fun L hL x hx =>
    CSetting.conjSub_mem_orb hK (hS.pSpan_orb_le hx) hL
  have hyN := hS.mem_normalizer_orb_of_conjSub hD.y_K
  have hperm : ∀ M ∈ orbOf (TC.nbrAdj Ω) K J, conjSub y M ∈ orbOf (TC.nbrAdj Ω) K J :=
    fun M hM => by
      rw [← hS.conjSub_orb_of_mem_normalizer hD.y_K]
      exact ⟨M, hM, rfl⟩
  set θ := I.inducedAut hn hyN with hθ
  obtain ⟨a, ha⟩ := hD.y_pow
  have hθk : θ ^ 3 ^ a = 1 := I.inducedAut_pow_eq_one hn hyN ha
  obtain ⟨γ, hγ, c, hlabJ⟩ := I.label J hJπ
  have hJK : TC.nbrAdj Ω J K := hF.graph.symm hS.adj
  have horbg : conjSub g '' orbOf (TC.nbrAdj Ω) K J = orbOf (TC.nbrAdj Ω) J K := by
    rw [hS.conj_orb_eq (by rw [hD.hg]; exact hJπ), hD.hg]
  have hKsJ : TC.nbrAdj Ω J Ks := adj_of_mem_orbOf hF.graph hJK (horbg ▸ hD.Ks_mem)
  have hJKs : J ≠ Ks := fun e => hKsJ.2.2.1 e.symm
  have hθJ : ∀ x (hx : x ∈ AE.memBar γ hγ c),
      θ ⟨x, memBar_le_aeModel γ hγ c hx⟩ = ⟨x, memBar_le_aeModel γ hγ c hx⟩ := fun x hx =>
    I.inducedAut_fix_of_comm hn hyN (hD.y_perp J hJπ (Set.mem_insert _ _) hJKs) x
      (by rw [hlabJ]; exact hx) _
  have hθJ' := aut_fix_twin hn θ ⟨a, hθk⟩ hγ hθJ
  have hKsπ : Ks ∉ orbOf (TC.nbrAdj Ω) K J := by
    intro hKsπ
    apply hD.y_not_Ks
    obtain ⟨β, hβ, c', hlabKs⟩ := I.label Ks hKsπ
    have hcJKs := comm_of_mem_omegaNbr hS.hyp hS.two hJΩ hKsJ.2
    have hc : ∀ x ∈ AE.memBar β hβ c', ∀ z ∈ AE.memBar γ hγ c, x * z = z * x := by
      rw [← hlabKs, ← hlabJ]
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcJKs _ (Subgroup.mem_subgroupOf.mp hv) _
        (Subgroup.mem_subgroupOf.mp hu)).symm
    have hβγ : β = γ := by
      rcases eq_or_disjoint_of_comm hc with e | hd
      · exact e
      · exfalso
        have h1 := Finset.card_union_of_disjoint hd
        have h2 := Finset.card_le_univ (β ∪ γ)
        rw [h1, hβ, hγ, Fintype.card_fin] at h2
        omega
    subst hβγ
    have hfixKs : ∀ x (hx : x ∈ AE.memBar β hβ c'),
        θ ⟨x, memBar_le_aeModel β hβ c' hx⟩ = ⟨x, memBar_le_aeModel β hβ c' hx⟩ := by
      have hcc : c' = c ∨ c' = !c := by cases c <;> cases c' <;> simp
      rcases hcc with rfl | rfl
      · exact hθJ
      · exact hθJ'
    exact I.comm_of_inducedAut_fix hS.hyp hS.two h8 hPΩ hn hk hyN hKsπ
      (by rw [hD.y_Ks]; exact hKsπ) fun x hx _ => hfixKs x (by rw [← hlabKs]; exact hx)
  obtain ⟨-, hKsX⟩ := hS.ks_comm_of_not_mem hD hKsπ
  have hKX : pSpan (orbOf (TC.nbrAdj Ω) K J) ≤ Subgroup.centralizer (K : Set G) :=
    hS.pSpan_orb_le.trans (pSpan_omegaNbr_le_centralizer hS.hyp hS.two hK)
  obtain ⟨p, hp, q, hq, hpq⟩ : ∃ p ∈ γᶜ, ∃ q ∈ γᶜ, p ≠ q := by
    refine Finset.one_lt_card.mp ?_
    rw [Finset.card_compl, hγ, Fintype.card_fin]
    norm_num
  rw [Finset.mem_compl] at hp hq
  obtain ⟨w₀, hw₀⟩ : vbar 7 (pairVec p q) ∈ I.φ.range := by
    rw [I.range_eq]
    exact vbar_pairVec_mem_aeModel p q
  have hw₀J : conjSub (w₀ : G) J = J := by
    have hmem : conjSub (w₀ : G) J ∈ orbOf (TC.nbrAdj Ω) K J := hinv J hJπ w₀ w₀.2
    have hle : (J.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ ≤
        ((conjSub (w₀ : G) J).subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ := by
      intro x hx
      have h1 := I.map_conjSub w₀ x hx
      rw [hlabJ] at hx
      rwa [hw₀, ← vbar_pairVec_comm_memBar hp hq x hx, mul_inv_cancel_right] at h1
    exact (TL4.eq_of_map_le_memBar hS.hyp hS.two hn I.φ hk (hPΩ hJπ) (hPΩ hmem) (le_pSpan hJπ)
      (le_pSpan hmem) hlabJ hle).symm
  set w' : G := g⁻¹ * w₀ * g with hw'
  have hw'K : conjSub w' K = K := by
    rw [hw', conjSub_mul, conjSub_mul, hD.hg, hw₀J, ← hD.hg, conjSub_inv_conjSub]
  have hw'N := hS.mem_normalizer_orb_of_conjSub hw'K
  have hcomm' : ∀ L : Subgroup G, (∀ l ∈ L, (w₀ : G) * l = l * w₀) →
      ∀ m ∈ conjSub g⁻¹ L, w' * m = m * w' := by
    intro L hL m hm
    have hm' : g * m * g⁻¹ ∈ L := by
      have := mem_conjSub_iff.mp hm
      simpa using this
    have e := hL _ hm'
    calc w' * m = g⁻¹ * ((w₀ : G) * (g * m * g⁻¹)) * g := by rw [hw']; group
      _ = g⁻¹ * ((g * m * g⁻¹) * (w₀ : G)) * g := by rw [e]
      _ = m * w' := by rw [hw']; group
  have hw'L₀ := hcomm' K fun l hl => (Subgroup.mem_centralizer_iff.mp (hKX w₀.2) l hl).symm
  have hw'L₁ := hcomm' Ks fun l hl => hKsX _ w₀.2 l hl
  set θ' := I.inducedAut hn hw'N with hθ'
  have hθ'y := aut_fix_yBar hn (by norm_num) θ' h
    (fun x hx => I.inducedAut_fix_of_comm hn hw'N hw'L₀ x (by rw [hlab₀]; exact hx) _)
    (fun x hx => I.inducedAut_fix_of_comm hn hw'N hw'L₁ x (by rw [hlab₁]; exact hx) _)
  have hy₀3 : y₀ ^ 3 ^ a = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one, hy₀y]
    have : g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹ := by rw [inv_inv]
    rw [this, conj_pow, ha, mul_one, mul_inv_cancel])
  have hcw' : w' * y₀ * w'⁻¹ = y₀ := by
    have e1 : I.toModel y₀ = ⟨AE.yBar α h, yBar_mem α h⟩ := Subtype.ext hy₀
    have e2 := I.inducedAut_apply hn hw'N y₀
    rw [← hθ', e1, hθ'y, ← e1] at e2
    have e3 : I.φ (conjSpan hw'N y₀) = I.φ y₀ := (congrArg Subtype.val e2).symm
    have hpow : conjSpan hw'N y₀ ^ 3 ^ a = 1 := by
      rw [← map_pow, hy₀3, map_one]
    have := I.eq_of_map_eq_of_pow hk hpow hy₀3 e3
    exact congrArg Subtype.val this
  have hcw₀ : y * w₀ * y⁻¹ = w₀ := by
    rw [hy₀y, hw'] at hcw'
    have e : (w₀ : G) * y * (w₀ : G)⁻¹ = y := by
      have := congrArg (fun t => g * t * g⁻¹) hcw'
      calc (w₀ : G) * y * (w₀ : G)⁻¹ =
          g * (g⁻¹ * w₀ * g * (g⁻¹ * y * g) * (g⁻¹ * w₀ * g)⁻¹) * g⁻¹ := by group
        _ = y := by rw [this]; group
    have e' : (w₀ : G) * y = y * w₀ := by
      calc (w₀ : G) * y = (w₀ : G) * y * (w₀ : G)⁻¹ * w₀ := by group
        _ = y * w₀ := by rw [e]
    calc y * w₀ * y⁻¹ = w₀ * y * y⁻¹ := by rw [e']
      _ = w₀ := by group
  have hθw : θ ⟨vbar 7 (pairVec p q), vbar_pairVec_mem_aeModel p q⟩ =
      ⟨vbar 7 (pairVec p q), vbar_pairVec_mem_aeModel p q⟩ := by
    have e1 : I.toModel w₀ = ⟨vbar 7 (pairVec p q), vbar_pairVec_mem_aeModel p q⟩ :=
      Subtype.ext hw₀
    rw [← e1, hθ, I.inducedAut_apply hn hyN]
    congr 1
    apply Subtype.ext
    rw [conjSpan_apply]
    exact hcw₀
  have hθ1 : θ = 1 := aut_eq_one_of_cent_pair rfl θ ⟨a, hθk⟩ hγ hθJ hpq hp hq hθw
  exact I.comm_of_inducedAut_eq_one hS.hyp hS.two h8 hPΩ hn hk hyN hperm hθ1

theorem exists_twin {n : ℕ} (hn : 5 ≤ n) (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n) :
    ∃ g : G, ∃ Ks : Subgroup G, ∃ y : G, Data128 Ω K J g Ks y ∧
      (∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), y * x = x * y) ∧
      Ks ∈ omegaNbr Ω K ∧ Ks ∉ orbOf (TC.nbrAdj Ω) K J ∧
      (∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ k ∈ Ks, x * k = k * x) ∧
      ∀ z zs : G, IsUniqueInvolution K z → IsUniqueInvolution Ks zs → zs = z := by
  obtain ⟨g, Ks, y, hD, α, h, b, y₀, hy₀, hy₀y, -, -, hlab₀, hlab₁⟩ := hS.exists_data128 hn I
  have hy : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), y * x = x * y := by
    rcases eq_or_ne n 7 with rfl | hn7
    · exact hS.y_comm_seven I hD hy₀ hy₀y hlab₀ hlab₁
    · exact hS.y_comm_of_rigid hn I (ae3Rigid hn hn7) hD
  obtain ⟨hKsK, hKsπ, hKs⟩ := hS.ks_comm_of_y_comm hD hy
  exact ⟨g, Ks, y, hD, hy, hKsK, hKsπ, hKs, fun z zs hz hzs => hS.z_eq_of_ks_comm hD hKs hz hzs⟩

end CHyp

end CFSG.ClassicalInvolution.Q3.TC.Thin
