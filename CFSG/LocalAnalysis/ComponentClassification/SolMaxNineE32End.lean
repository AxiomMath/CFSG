module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineE32Fusion
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxEightE
public import Certificates.Certificate22258

public section

namespace CFSG.ComponentClassification.SolMax.NineE32

open Equiv Subgroup

variable {X : Type} [Group X] {H : Subgroup X} {φ : ↥H →* A9 × Multiplicative (ZMod 2)}
  {t : X}

theorem additive_sum5 (f : W → W) (hf : ∀ v w, f (v + w) = f v + f w) (b : ℕ → Bool)
    (c : ℕ → W) :
    f ((if b 0 then c 0 else 0) + (if b 1 then c 1 else 0) + (if b 2 then c 2 else 0) +
      (if b 3 then c 3 else 0) + (if b 4 then c 4 else 0)) =
      (if b 0 then f (c 0) else 0) + (if b 1 then f (c 1) else 0) +
      (if b 2 then f (c 2) else 0) + (if b 3 then f (c 3) else 0) +
      (if b 4 then f (c 4) else 0) := by
  have h0 : f 0 = 0 := by
    have h := hf 0 0
    rw [add_zero] at h
    have h2 : f 0 + f 0 = f 0 + 0 := by rw [add_zero, ← h]
    exact add_left_cancel h2
  have hite : ∀ (b : Bool) (x : W), f (if b then x else 0) = if b then f x else 0 := by
    intro b x
    cases b <;> simp [h0]
  rw [hf, hf, hf, hf, hite, hite, hite, hite, hite]

namespace Frame

variable {F : Frame H φ t}

theorem false_of_orbit {n : X} {ψ : W → W} (hn : F.Acts n ψ) {s₁ : W} (hs₁ : ψ s₁ = tW)
    (O : W → Prop) [DecidablePred O] (hO : ∀ y, y ∈ F.orbitT ↔ O y)
    (hne : nO O tW ≠ nO O s₁) : False := by
  let ψe : W ≃+ W := AddEquiv.ofBijective (AddMonoidHom.mk' ψ hn.add) hn.bijective
  have hψ : ∀ y, O (ψe y) ↔ O y := fun y => by
    rw [← hO, ← hO]
    exact hn.mem_orbitT_iff y
  have h := nO_eq O ψe hψ s₁
  have h' : ψe s₁ = tW := hs₁
  rw [h'] at h
  exact hne h

theorem exists_index {x : ℕ} (hx : x ∈ oListN) : ∃ i < 10, oListN.getD i 0 = x := by
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
  refine ⟨i, by simpa [oListN] using hi, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hix]

theorem false_of_Otm [Finite X] (hφ : Function.Surjective φ)
    (hCt : centralizer ({t} : Set X) ≤ H) {n : X} {ψ : W → W} (hn : F.Acts n ψ)
    (hs : ψ sW = tW) (hO : ∀ y, y ∈ F.orbitT ↔ Otm y) : False := by
  have hψO : ∀ y, Otm (ψ y) ↔ Otm y := fun y => by
    rw [← hO, ← hO]
    exact hn.mem_orbitT_iff y
  have hidx : ∀ j < 5, ∃ i < 10, oListN.getD i 0 = mask (ψ (betaW j)) := fun j hj =>
    exists_index ((Otm_iff_mem _).mp ((hψO _).mpr (Otm_betaW j hj)))
  obtain ⟨i₁, hi₁, he₁⟩ := hidx 1 (by decide)
  obtain ⟨i₂, hi₂, he₂⟩ := hidx 2 (by decide)
  obtain ⟨i₃, hi₃, he₃⟩ := hidx 3 (by decide)
  obtain ⟨i₄, hi₄, he₄⟩ := hidx 4 (by decide)
  set u : List ℕ := [i₁, i₂, i₃, i₄] with hu
  have himgs : t₀N :: u.map (fun i => oListN.getD i 0) =
      [mask (ψ (betaW 0)), mask (ψ (betaW 1)), mask (ψ (betaW 2)), mask (ψ (betaW 3)),
        mask (ψ (betaW 4))] := by
    rw [hu, betaW_zero, hs, mask_tW]
    simp only [List.map_cons, List.map_nil, he₁, he₂, he₃, he₄]
  have hcol : ∀ k < 5, applyCols (t₀N :: u.map (fun i => oListN.getD i 0)) (bInvN.getD k 0) =
      mask (ψ (eW k)) := by
    intro k hk
    rw [himgs, applyCols_eq (fun j => ψ (betaW j)), ← additive_sum5 ψ hn.add, ← eW_eq_sum k hk]
  have hcols : uCols u = [mask (ψ (eW 0)), mask (ψ (eW 1)), mask (ψ (eW 2)), mask (ψ (eW 3)),
      mask (ψ (eW 4))] := by
    have h0 := hcol 0 (by decide)
    have h1 := hcol 1 (by decide)
    have h2 := hcol 2 (by decide)
    have h3 := hcol 3 (by decide)
    have h4 := hcol 4 (by decide)
    simp only [bInvN, List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2 h3 h4
    simp only [uCols, bInvN, List.map_cons, List.map_nil]
    rw [h0, h1, h2, h3, h4]
  set cols := uCols u with hcolsdef
  have hψlin : ψ = linW cols := by
    rw [hcols]
    exact hn.eq_linW
  have hcolslt : ∀ k < 5, cols.getD k 0 < 32 := by
    intro k hk
    rw [hcols]
    interval_cases k <;> simp only [List.getD_cons_zero, List.getD_cons_succ] <;>
      exact mask_lt _
  have happ : ∀ o ∈ oListN, applyCols cols o = mask (ψ (ofMask o)) := by
    intro o ho
    rw [hψlin, linW, mask_ofMask_lt (applyCols_lt hcolslt _), mask_ofMask_lt (oListN_lt o ho)]
  have hcand : candOK u = true := by
    simp only [candOK, ← hcolsdef, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
      List.contains_iff_mem]
    refine ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
      rw [happ o ho, ← Otm_iff_mem, hψO, Otm_iff_mem, mask_ofMask_lt (oListN_lt o ho)]
      exact ho
    · refine List.Nodup.map_on (fun o ho o' ho' h => ?_) oListN_nodup
      rw [happ o ho, happ o' ho'] at h
      have h1 : ψ (ofMask o) = ψ (ofMask o') := by
        rw [← ofMask_mask (ψ (ofMask o)), h, ofMask_mask]
      have h2 := hn.injective h1
      rw [← mask_ofMask_lt (oListN_lt o ho), h2, mask_ofMask_lt (oListN_lt o' ho')]
  have hcheck := (Certificates.certificate22258 : check () = true)
  simp only [check, List.all_eq_true, List.mem_range] at hcheck
  have hone := hcheck (i₁ + 10 * i₂ + 100 * i₃ + 1000 * i₄) (by omega)
  simp only [checkOne, digits_code i₁ i₂ i₃ i₄ hi₁ hi₂ hi₃ hi₄, ← hu, hcand, Bool.not_true,
    Bool.false_or] at hone
  obtain ⟨hwlt, hjlt⟩ := lookup_lt u
  set e := lookup u with he
  simp only [entryOK, ← hcolsdef, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at hone
  obtain ⟨ht₀, hodd⟩ := hone
  have hn' : F.Acts n (linW cols) := by rw [← hψlin]; exact hn
  obtain ⟨y, hy⟩ := acts_evalWordW hφ hn' e.1 hwlt
  have hyt : evalWordW cols e.1 tW = tW := by
    rw [← ofMask_mask (evalWordW cols e.1 tW), mask_evalWordW hcolslt, mask_tW, ht₀]
    decide
  have hyC : y ∈ centralizer ({t} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    have h1 := hy.conj_t
    rw [hyt, F.ht] at h1
    have := congrArg (· * y) h1
    simpa [mul_assoc] using this
  have hyH := hCt hyC
  have hyi : ∀ i : Fin 4, evalWordW cols e.1 (eW i) = ofMask ((oddColsN.getD e.2 []).getD i 0) := by
    intro i
    rw [← ofMask_mask (evalWordW cols e.1 (eW i)), mask_evalWordW hcolslt, mask_eW,
      hodd i i.2]
  set q := φ ⟨y, hyH⟩ with hq
  have hconj : ∀ v : W, ((q.1 : A9) : Perm (Fin 9)) * encPerm v * ((q.1 : A9) : Perm (Fin 9))⁻¹ =
      encPerm (evalWordW cols e.1 v) := by
    intro v
    have h1 : (⟨y * F.κ (Multiplicative.ofAdd v) * y⁻¹,
        mul_mem (mul_mem hyH (F.mem _)) (inv_mem hyH)⟩ : ↥H) =
        ⟨F.κ (Multiplicative.ofAdd (evalWordW cols e.1 v)), F.mem _⟩ := Subtype.ext (hy v)
    have h2 := congrArg φ h1
    rw [phi_conj hyH (F.mem _), F.phi, F.phi] at h2
    have h3 := congrArg (fun p : A9 × Multiplicative (ZMod 2) => ((p.1 : A9) : Perm (Fin 9))) h2
    simpa [enc_apply_fst] using h3
  set j : Fin 36 := ⟨e.2, hjlt⟩
  have hcomm : ∀ i : Fin 4, (oddP j)⁻¹ * ((q.1 : A9) : Perm (Fin 9)) * aPerm i =
      aPerm i * ((oddP j)⁻¹ * ((q.1 : A9) : Perm (Fin 9))) := by
    intro i
    have h1 := hconj (eW i)
    rw [encPerm_eW, hyi i, ← oddPerm_conj j i] at h1
    have h2 := congrArg (fun p => (oddP j)⁻¹ * p * (q.1 : Perm (Fin 9))) h1
    rw [show (oddP j)⁻¹ * (((q.1 : A9) : Perm (Fin 9)) * aPerm i *
        ((q.1 : A9) : Perm (Fin 9))⁻¹) * ((q.1 : A9) : Perm (Fin 9)) =
        (oddP j)⁻¹ * ((q.1 : A9) : Perm (Fin 9)) * aPerm i by group] at h2
    rw [h2]
    group
  have hsign := sign_eq_one_of_commute _ hcomm
  rw [map_mul, map_inv, sign_oddP j] at hsign
  have hq1 : Perm.sign ((q.1 : A9) : Perm (Fin 9)) = 1 := (Perm.mem_alternatingGroup).mp q.1.2
  rw [hq1] at hsign
  exact absurd hsign (by decide)

end Frame

end CFSG.ComponentClassification.SolMax.NineE32

namespace CFSG.ComponentClassification.SolMax

open Equiv Subgroup NineE32

theorem signalizerNineEightFusionInput_holds :
    SignalizerNineEightFusionInput := by
  intro X _ _ H φ hφ hodd t htH ht2 hφt hCt hfour s g hsH hgs h8
  obtain ⟨F⟩ := exists_frame hφ hodd htH ht2 hφt
  have hφt' : ∀ h : t ∈ H, φ ⟨t, h⟩ = (1, Multiplicative.ofAdd 1) := fun _ => hφt
  have hs2 : s * s = 1 := by
    rw [← hgs, show g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, ht2]
    group
  obtain ⟨c, hcH, hc⟩ := F.exists_conj_coord hφ hsH hs2 h8
  obtain ⟨s₁, hs₁, hcs⟩ : ∃ s₁ : W, (s₁ = mW ∨ s₁ = sW) ∧
      c * s * c⁻¹ = F.κ (Multiplicative.ofAdd s₁) := by
    rcases hc with h | h
    · exact ⟨mW, Or.inl rfl, h⟩
    · exact ⟨sW, Or.inr rfl, h⟩
  set g₁ := g * c⁻¹ with hg₁def
  have hg₁ : g₁ * F.κ (Multiplicative.ofAdd s₁) * g₁⁻¹ = t := by
    rw [← hcs, ← hgs, hg₁def]
    group
  set B : Subgroup X := F.κ.range.map (MulAut.conj g₁).toMonoidHom with hB
  have hcommA : ∀ v w : W, F.κ (Multiplicative.ofAdd v) * F.κ (Multiplicative.ofAdd w) =
      F.κ (Multiplicative.ofAdd w) * F.κ (Multiplicative.ofAdd v) := by
    intro v w
    rw [← map_mul F.κ, ← map_mul F.κ, mul_comm (Multiplicative.ofAdd v)]
  have hBC : B ≤ centralizer ({t} : Set X) := by
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have key : g₁ * F.κ (Multiplicative.ofAdd s₁) * g₁⁻¹ * (g₁ * F.κ v * g₁⁻¹) =
        g₁ * F.κ v * g₁⁻¹ * (g₁ * F.κ (Multiplicative.ofAdd s₁) * g₁⁻¹) := by
      rw [show g₁ * F.κ (Multiplicative.ofAdd s₁) * g₁⁻¹ * (g₁ * F.κ v * g₁⁻¹) =
        g₁ * (F.κ (Multiplicative.ofAdd s₁) * F.κ v) * g₁⁻¹ by group,
        show g₁ * F.κ v * g₁⁻¹ * (g₁ * F.κ (Multiplicative.ofAdd s₁) * g₁⁻¹) =
        g₁ * (F.κ v * F.κ (Multiplicative.ofAdd s₁)) * g₁⁻¹ by group]
      congr 2
      exact hcommA s₁ (Multiplicative.toAdd v)
    rw [hg₁] at key
    exact key.symm
  have hBH := hBC.trans hCt
  have hB2 : ∀ b ∈ B, b * b = 1 := by
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g₁ * F.κ v * g₁⁻¹ * (g₁ * F.κ v * g₁⁻¹) = g₁ * (F.κ v * F.κ v) * g₁⁻¹ by group,
      ← map_mul, show v * v = 1 from Multiplicative.toAdd.injective (by
        simp only [toAdd_mul, toAdd_one]
        generalize Multiplicative.toAdd v = x
        revert x
        decide), map_one]
    group
  have hBcard : Nat.card B = 32 := by
    rw [hB, ← F.card_range]
    exact Nat.card_congr ((MulAut.conj g₁).subgroupMap F.κ.range).toEquiv.symm
  have htB : t ∈ B := ⟨F.κ (Multiplicative.ofAdd s₁), ⟨_, rfl⟩, by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hg₁⟩
  obtain ⟨c₂, hc₂H, hc₂B, hc₂t⟩ := F.exists_conj_of_elem hφ hodd hφt' hBH hB2 hBcard htB
  set n := c₂ * g₁ with hndef
  have hnA : ∀ v : W, ∃ w : W, n * F.κ (Multiplicative.ofAdd v) * n⁻¹ =
      F.κ (Multiplicative.ofAdd w) := by
    intro v
    have hmem : n * F.κ (Multiplicative.ofAdd v) * n⁻¹ ∈ F.κ.range := by
      rw [← hc₂B]
      refine ⟨g₁ * F.κ (Multiplicative.ofAdd v) * g₁⁻¹, ⟨_, ⟨_, rfl⟩, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hndef]
      group
    obtain ⟨w, hw⟩ := hmem
    exact ⟨Multiplicative.toAdd w, hw.symm⟩
  choose ψ hψ using hnA
  have hn : F.Acts n ψ := hψ
  have hψs : ψ s₁ = tW := by
    have h1 := hψ s₁
    rw [show n * F.κ (Multiplicative.ofAdd s₁) * n⁻¹ =
      c₂ * (g₁ * F.κ (Multiplicative.ofAdd s₁) * g₁⁻¹) * c₂⁻¹ by rw [hndef]; group, hg₁,
      hc₂t] at h1
    have h2 : F.κ (Multiplicative.ofAdd tW) = F.κ (Multiplicative.ofAdd (ψ s₁)) := by
      rw [F.ht]
      exact h1
    exact Multiplicative.ofAdd.injective (F.inj h2).symm
  have hs₁O : s₁ ∈ F.orbitT := (hn.mem_orbitT_iff s₁).mp (by rw [hψs]; exact F.tW_mem_orbitT)
  have hcases := fun {v : W} (hv : v ∈ F.orbitT) => F.orbitT_cases hφt' hfour hv
  rcases hs₁ with rfl | rfl
  ·
    have hM : ∀ v, isM v → v ∈ F.orbitT := fun v hv => F.isM_mem_orbitT hφ hs₁O isM_mW hv
    by_cases hTM : ∃ v ∈ F.orbitT, isTM v
    · obtain ⟨v, hv, hvTM⟩ := hTM
      have hO : ∀ y, y ∈ F.orbitT ↔ O₃ y := fun y =>
        ⟨fun hy => hcases hy, fun hy => by
          rcases hy with rfl | h | h
          · exact F.tW_mem_orbitT
          · exact hM y h
          · exact F.isTM_mem_orbitT hφ hv hvTM h⟩
      exact Frame.false_of_orbit hn hψs O₃ hO (by rw [nO₃_tW, nO₃_mW]; decide)
    · push Not at hTM
      have hO : ∀ y, y ∈ F.orbitT ↔ Om y := fun y =>
        ⟨fun hy => by
          rcases hcases hy with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h (hTM y hy), fun hy => by
          rcases hy with rfl | h
          · exact F.tW_mem_orbitT
          · exact hM y h⟩
      exact Frame.false_of_orbit hn hψs Om hO (by rw [nOm_tW, nOm_mW]; decide)
  ·
    have hTM : ∀ v, isTM v → v ∈ F.orbitT := fun v hv => F.isTM_mem_orbitT hφ hs₁O isTM_sW hv
    by_cases hM : ∃ v ∈ F.orbitT, isM v
    · obtain ⟨v, hv, hvM⟩ := hM
      have hO : ∀ y, y ∈ F.orbitT ↔ O₃ y := fun y =>
        ⟨fun hy => hcases hy, fun hy => by
          rcases hy with rfl | h | h
          · exact F.tW_mem_orbitT
          · exact F.isM_mem_orbitT hφ hv hvM h
          · exact hTM y h⟩
      exact Frame.false_of_orbit hn hψs O₃ hO (by rw [nO₃_tW, nO₃_sW]; decide)
    · push Not at hM
      have hO : ∀ y, y ∈ F.orbitT ↔ Otm y := fun y =>
        ⟨fun hy => by
          rcases hcases hy with h | h | h
          · exact Or.inl h
          · exact absurd h (hM y hy)
          · exact Or.inr h, fun hy => by
          rcases hy with rfl | h
          · exact F.tW_mem_orbitT
          · exact hTM y h⟩
      exact Frame.false_of_Otm hφ hCt hn hψs hO

end CFSG.ComponentClassification.SolMax
