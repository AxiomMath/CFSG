module

public import Certificates.Certificate550841
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf63E64AutBase

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E64F

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Q3.E64Data Certificates.AE117 Certificates.E64Aut
  Certificates.E64Facts CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.E64Aut

@[expose] def CentMem (a : ↥e64Sub) (α : Finset (Fin 7)) (h : α.card = 4) (b : Bool) : Prop :=
  ∀ x ∈ memBar α h b, (a : AEQ 7) * x = x * a

@[expose] def CentPair (a : ↥e64Sub) (α : Finset (Fin 7)) (h : α.card = 4) : Prop :=
  CentMem a α h true ∧ CentMem a α h false

theorem centMem_iff {a : ↥e64Sub} {x : Wr 7} (hx : mkQ 7 x = (a : AEQ 7)) (α : Finset (Fin 7))
    (h : α.card = 4) (b : Bool) :
    CentMem a α h b ↔ ∀ s ∈ memAtL α b, eqPi (x * s) (s * x) = true := by
  unfold CentMem
  constructor
  · intro hc s hs
    rw [TL4.Mdl117.eqPi_iff, map_mul, map_mul, hx]
    exact hc _ ((TL4.Mdl117.mem_memBar_iff α h b _).2 ⟨s, hs, rfl⟩)
  · intro hc y hy
    obtain ⟨s, hs, rfl⟩ := (TL4.Mdl117.mem_memBar_iff α h b y).1 hy
    have := (TL4.Mdl117.eqPi_iff _ _).1 (hc s hs)
    rwa [map_mul, map_mul, hx] at this

theorem centPair_iff {a : ↥e64Sub} {x : Wr 7} (hx : mkQ 7 x = (a : AEQ 7)) (ℓ : Finset (Fin 7))
    (h : ℓᶜ.card = 4) : CentPair a ℓᶜ h ↔ commAll (memS ℓ) x = true := by
  unfold CentPair commAll memS
  rw [centMem_iff hx, centMem_iff hx, List.all_eq_true]
  constructor
  · rintro ⟨h1, h2⟩ s hs
    rcases List.mem_append.1 hs with hs | hs
    · exact h1 s hs
    · exact h2 s hs
  · intro hc
    exact ⟨fun s hs => hc s (List.mem_append_left _ hs),
      fun s hs => hc s (List.mem_append_right _ hs)⟩

theorem nodup_map_mkQ {C : List (Wr 7)} (h : distinctPi C = true) : (C.map (mkQ 7)).Nodup := by
  unfold distinctPi at h
  rw [decide_eq_true_eq] at h
  refine List.Pairwise.map _ (fun c d hcd he => ?_) h
  rw [← TL4.Mdl117.eqPi_iff] at he
  rw [he] at hcd
  exact Bool.noConfusion hcd

theorem centOK_spec' {S C : List (Wr 7)} (h : centOK (l32Fin ()) (evenFin ()) S C = true) :
    (∀ c ∈ C, inM c = true ∧ commAll S c = true) ∧
      ∀ x ∈ aeSubOver l32, commAll S x = true → ∃ c ∈ C, eqPi x c = true := by
  unfold centOK at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hC, hF⟩ := h
  refine ⟨fun c hc => by simpa only [Bool.and_eq_true] using hC c hc, fun x hx hcomm => ?_⟩
  obtain ⟨hav, hap⟩ := vec_perm_mem hx
  have h1 := (finAll_iff.1 hF) x.perm hap
  have hperm : (S.all fun s => decide (x.perm * s.perm = s.perm * x.perm)) = true := by
    unfold commAll at hcomm
    rw [List.all_eq_true] at hcomm ⊢
    intro s hs
    rw [decide_eq_true_eq]
    exact eqPi_perm (hcomm s hs)
  rw [hperm, Bool.not_true, Bool.false_or] at h1
  have h2 := (finAll_iff.1 h1) x.vec hav
  have hx' : (⟨x.vec, x.perm⟩ : Wr 7) = x := rfl
  rw [hx', hcomm, Bool.not_true, Bool.false_or] at h2
  exact List.any_eq_true.1 h2

section Checks

theorem g1_spec {ℓ : Finset (Fin 7)} (hℓ : ℓ ∈ fanoLines) :
    centOK (l32Fin ()) (evenFin ()) (memS ℓ) (centAt ℓ) = true ∧ (centAt ℓ).length = 8 ∧
      distinctPi (centAt ℓ) = true ∧ (∀ c ∈ centAt ℓ, c * c = 1) ∧
        ∀ c ∈ centAt ℓ, ∀ d ∈ centAt ℓ, c * d = d * c := by
  have h : g1Check () = true := Certificates.certificate550841.1
  unfold g1Check at h
  dsimp only at h
  have h1 := List.all_eq_true.1 h ℓ hℓ
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h1
  obtain ⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩ := h1
  exact ⟨hA, hB, hC, hD, hE⟩

theorem g2_spec :
    (∀ ℓ ∈ fanoLines, ∀ ℓ' ∈ fanoLines, ℓ ≠ ℓ' → ∀ c ∈ centAt ℓ, commAll (memS ℓ') c = true →
      eqPi c 1 = true ∨ ∃ a ∈ a7 (), eqPi c a = true) ∧ distinctPi (a7 ()) = true ∧
      ∀ a ∈ a7 (), inM a = true ∧ a * a = 1 ∧ eqPi a 1 = false ∧
        (fanoLines.filter fun ℓ => commAll (memS ℓ) a).length = 3 := by
  have h : g2Check () = true := Certificates.certificate550841.2.1
  unfold g2Check at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hA, hB⟩, hC⟩ := h
  refine ⟨fun ℓ hℓ ℓ' hℓ' hne c hc hcomm => ?_, hB, fun a ha => ?_⟩
  · have h1 := hA ℓ hℓ ℓ' hℓ'
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
      List.any_eq_true] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 hne
    · rcases h1 c hc with (h2 | h2) | h2
      · rw [hcomm] at h2
        exact Bool.noConfusion h2
      · exact Or.inl h2
      · exact Or.inr h2
  · have h1 := hC a ha
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    obtain ⟨⟨⟨h2, h3⟩, h4⟩, h5⟩ := h1
    exact ⟨h2, h3, h4, h5⟩

end Checks

section G1

theorem centPair_iff_mem {ℓ : Finset (Fin 7)} (hℓ : ℓ ∈ fanoLines) (h : ℓᶜ.card = 4)
    (a : ↥e64Sub) : CentPair a ℓᶜ h ↔ ∃ c ∈ centAt ℓ, mkQ 7 c = (a : AEQ 7) := by
  have hok := centOK_spec' (g1_spec hℓ).1
  constructor
  · intro ha
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨c, hc, hxc⟩ := hok.2 x hx ((centPair_iff hxa ℓ h).1 ha)
    exact ⟨c, hc, ((TL4.Mdl117.eqPi_iff x c).1 hxc).symm.trans hxa⟩
  · rintro ⟨c, hc, hca⟩
    exact (centPair_iff hca ℓ h).2 (hok.1 c hc).2

theorem mkQ_centAt_mem {ℓ : Finset (Fin 7)} (hℓ : ℓ ∈ fanoLines) {c : Wr 7} (hc : c ∈ centAt ℓ) :
    mkQ 7 c ∈ e64Sub :=
  mkQ_mem_e64Sub ((centOK_spec' (g1_spec hℓ).1).1 c hc).1

theorem ncard_centPair {α : Finset (Fin 7)} (hα : α ∈ e64Sets) (h : α.card = 4) :
    {c : ↥e64Sub | CentPair c α h}.ncard = 8 := by
  classical
  obtain ⟨ℓ, hℓ, rfl⟩ := hα
  obtain ⟨-, hlen, hdist, -, -⟩ := g1_spec hℓ
  have himg : Subtype.val '' {c : ↥e64Sub | CentPair c ℓᶜ h} =
      ↑((centAt ℓ).map (mkQ 7)).toFinset := by
    ext y
    simp only [Set.mem_image, Set.mem_setOf_eq, List.coe_toFinset, List.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (centPair_iff_mem hℓ h a).1 ha
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨mkQ 7 c, mkQ_centAt_mem hℓ hc⟩, (centPair_iff_mem hℓ h _).2 ⟨c, hc, rfl⟩, rfl⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (nodup_map_mkQ hdist), List.length_map, hlen]

end G1

@[expose] def centPairSub (α : Finset (Fin 7)) (h : α.card = 4) : Subgroup ↥e64Sub where
  carrier := {c | CentPair c α h}
  mul_mem' {c d} hc hd := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [Subgroup.coe_mul, mul_assoc, hd.1 x hx, ← mul_assoc, hc.1 x hx, mul_assoc]
    · rw [Subgroup.coe_mul, mul_assoc, hd.2 x hx, ← mul_assoc, hc.2 x hx, mul_assoc]
  one_mem' := ⟨fun x _ => by rw [Subgroup.coe_one, one_mul, mul_one],
    fun x _ => by rw [Subgroup.coe_one, one_mul, mul_one]⟩
  inv_mem' {c} hc := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [Subgroup.coe_inv]
      exact (Commute.inv_left (hc.1 x hx) :)
    · rw [Subgroup.coe_inv]
      exact (Commute.inv_left (hc.2 x hx) :)

theorem natCard_centPairSub {α : Finset (Fin 7)}
    (hα : α ∈ e64Sets) (h : α.card = 4) : Nat.card (centPairSub α h) = 8 := by
  rw [← ncard_centPair hα h]
  rfl

theorem card_compl_fanoLines : ∀ ℓ ∈ fanoLines, ℓᶜ.card = 4 := by
  decide +kernel

theorem nodup_fanoLines : fanoLines.Nodup := by
  decide +kernel

section G2

theorem mkQ_a7_mem {a : Wr 7} (ha : a ∈ a7 ()) : mkQ 7 a ∈ e64Sub :=
  mkQ_mem_e64Sub (g2_spec.2.2 a ha).1

theorem twinInv_iff (a : ↥e64Sub) :
    (a * a = 1 ∧ a ≠ 1 ∧ ∃ α ∈ e64Sets, ∃ β ∈ e64Sets, α ≠ β ∧
      ∃ (hα : α.card = 4) (hβ : β.card = 4), CentPair a α hα ∧ CentPair a β hβ) ↔
      ∃ x ∈ a7 (), mkQ 7 x = (a : AEQ 7) := by
  constructor
  · rintro ⟨-, ha1, α, ⟨ℓ, hℓ, rfl⟩, β, ⟨ℓ', hℓ', rfl⟩, hne, hα, hβ, hcα, hcβ⟩
    obtain ⟨c, hc, hca⟩ := (centPair_iff_mem hℓ hα a).1 hcα
    have hne' : ℓ ≠ ℓ' := fun h' => hne (by rw [h'])
    rcases g2_spec.1 ℓ hℓ ℓ' hℓ' hne' c hc ((centPair_iff hca ℓ' hβ).1 hcβ) with h1 | ⟨x, hx, h1⟩
    · exfalso
      apply ha1
      apply Subtype.ext
      rw [← hca, (TL4.Mdl117.eqPi_iff c 1).1 h1, map_one, Subgroup.coe_one]
    · exact ⟨x, hx, ((TL4.Mdl117.eqPi_iff c x).1 h1).symm.trans hca⟩
  · rintro ⟨x, hx, hxa⟩
    obtain ⟨-, hsq, h1, hlen⟩ := g2_spec.2.2 x hx
    refine ⟨Subtype.ext (by rw [Subgroup.coe_mul, ← hxa, ← map_mul, hsq, map_one,
      Subgroup.coe_one]), fun he => ?_, ?_⟩
    · have : mkQ 7 x = mkQ 7 1 := by rw [hxa, he, map_one, Subgroup.coe_one]
      rw [← TL4.Mdl117.eqPi_iff, h1] at this
      exact Bool.noConfusion this
    · obtain ⟨ℓ₁, ℓ₂, ℓ₃, hL⟩ := List.length_eq_three.1 hlen
      have hnd : [ℓ₁, ℓ₂, ℓ₃].Nodup := hL ▸ nodup_fanoLines.filter _
      have hmem : ∀ ℓ ∈ [ℓ₁, ℓ₂, ℓ₃], ℓ ∈ fanoLines ∧ commAll (memS ℓ) x = true := by
        intro ℓ hℓ
        rw [← hL, List.mem_filter] at hℓ
        exact hℓ
      have h12 : ℓ₁ ≠ ℓ₂ := by
        intro h12
        rw [h12] at hnd
        exact (List.nodup_cons.1 hnd).1 (List.mem_cons_self ..)
      obtain ⟨hℓ₁, hc₁⟩ := hmem ℓ₁ (by simp)
      obtain ⟨hℓ₂, hc₂⟩ := hmem ℓ₂ (by simp)
      exact ⟨ℓ₁ᶜ, ⟨ℓ₁, hℓ₁, rfl⟩, ℓ₂ᶜ, ⟨ℓ₂, hℓ₂, rfl⟩, fun he => h12 (compl_injective he),
        card_compl_fanoLines ℓ₁ hℓ₁, card_compl_fanoLines ℓ₂ hℓ₂,
        (centPair_iff hxa ℓ₁ _).2 hc₁, (centPair_iff hxa ℓ₂ _).2 hc₂⟩

theorem ncard_twinInv :
    {a : ↥e64Sub | a * a = 1 ∧ a ≠ 1 ∧ ∃ α ∈ e64Sets, ∃ β ∈ e64Sets, α ≠ β ∧
      ∃ (hα : α.card = 4) (hβ : β.card = 4), CentPair a α hα ∧ CentPair a β hβ}.ncard = 7 := by
  classical
  have himg : Subtype.val '' {a : ↥e64Sub | a * a = 1 ∧ a ≠ 1 ∧ ∃ α ∈ e64Sets, ∃ β ∈ e64Sets,
      α ≠ β ∧ ∃ (hα : α.card = 4) (hβ : β.card = 4), CentPair a α hα ∧ CentPair a β hβ} =
      ↑((a7 ()).map (mkQ 7)).toFinset := by
    ext y
    simp only [Set.mem_image, Set.mem_setOf_eq, List.coe_toFinset, List.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (twinInv_iff a).1 ha
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨mkQ 7 x, mkQ_a7_mem hx⟩, (twinInv_iff _).2 ⟨x, hx, rfl⟩, rfl⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (nodup_map_mkQ g2_spec.2.1), List.length_map]
  rfl

theorem ncard_twinInv_le :
    {a : ↥e64Sub | a * a = 1 ∧ a ≠ 1 ∧ ∃ α ∈ e64Sets, ∃ β ∈ e64Sets, α ≠ β ∧
      ∃ (hα : α.card = 4) (hβ : β.card = 4), CentPair a α hα ∧ CentPair a β hβ}.ncard ≤ 7 :=
  ncard_twinInv.le

end G2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E64F
