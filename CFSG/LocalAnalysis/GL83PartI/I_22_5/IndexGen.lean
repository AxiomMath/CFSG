module

public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Gen

public section

namespace GL83.CompFam

open CFSG.Open

variable {G : Type*} [Group G] {p : ℕ}

@[expose] def centGenI (p : ℕ) (B L : Subgroup G) : Subgroup G :=
  ⨆ E : {E : Subgroup G // E ≤ B ∧ Nat.card B ≤ p * Nat.card E},
    L ⊓ Subgroup.centralizer (E.1 : Set G)

theorem le_centGenI {B L E : Subgroup G} (hEB : E ≤ B) (hE : Nat.card B ≤ p * Nat.card E) :
    L ⊓ Subgroup.centralizer (E : Set G) ≤ centGenI p B L :=
  le_iSup (fun E : {E : Subgroup G // E ≤ B ∧ Nat.card B ≤ p * Nat.card E} =>
    L ⊓ Subgroup.centralizer (E.1 : Set G)) ⟨E, hEB, hE⟩

theorem centGenI_mono_left {B L L' : Subgroup G} (h : L ≤ L') : centGenI p B L ≤ centGenI p B L' :=
  iSup_mono fun _ => inf_le_inf_right _ h

theorem range_le_iSup_of_le_iSup {ι : Sort*} {K : Subgroup G} {S : ι → Subgroup G}
    (hS : ∀ i, S i ≤ K) (hK : K ≤ ⨆ i, S i) {H : Type*} [Group H] (f : K →* H)
    {T : ι → Subgroup H} (hT : ∀ i, ∀ x : K, (x : G) ∈ S i → f x ∈ T i) : f.range ≤ ⨆ i, T i := by
  rintro _ ⟨x, rfl⟩
  have key : ∀ g ∈ ⨆ i, S i, ∃ hg : g ∈ K, f ⟨g, hg⟩ ∈ ⨆ i, T i := by
    intro g hg
    refine Subgroup.iSup_induction S (C := fun g => ∃ hg : g ∈ K, f ⟨g, hg⟩ ∈ ⨆ i, T i) hg
      (fun i g hgi => ⟨hS i hgi, le_iSup T i (hT i ⟨g, hS i hgi⟩ hgi)⟩) ⟨K.one_mem, ?_⟩ ?_
    · have : (⟨1, K.one_mem⟩ : K) = 1 := rfl
      rw [this, map_one]
      exact one_mem _
    · rintro g g' ⟨hg, hf⟩ ⟨hg', hf'⟩
      refine ⟨K.mul_mem hg hg', ?_⟩
      have : (⟨g * g', K.mul_mem hg hg'⟩ : K) = ⟨g, hg⟩ * ⟨g', hg'⟩ := rfl
      rw [this, map_mul]
      exact mul_mem hf hf'
  obtain ⟨hx, hf⟩ := key x (hK x.2)
  exact hf

theorem normSub_congr [Fact p.Prime] {K K' : Subgroup G} {b : G} (h : K = K')
    (hc : NormComm p K b) (hc' : NormComm p K' b) : normSub hc = normSub hc' := by
  subst h
  rfl

section Equivariance

variable [Fact p.Prime]

theorem commute_normHom {K : Subgroup G} {b c : G} (hc : NormComm p K b) (hcb : c * b = b * c)
    {x : K} (hcx : c * (x : G) = x * c) : c * normHom hc x = normHom hc x * c := by
  rw [normHom_apply, normPi_apply]
  refine (Finset.noncommProd_commute _ _ _ _ fun i _ => ?_).eq
  rw [cjEmb_apply]
  have hcu : Commute c (b ^ i.val) := Commute.pow_right hcb i.val
  exact (hcu.mul_right (show Commute c (x : G) from hcx)).mul_right hcu.inv_right

variable {B : Subgroup G} {𝒦 : Set (Subgroup G)}

theorem IsFam.stab_le_stab_normSub (hF : IsFam p B 𝒦) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝒦) {b : G}
    (hb : b ∈ B) (hbA : b ∉ stab B K₀) {B' : Subgroup G} (hAB' : stab B K₀ ≤ B') :
    stab B K₀ ≤ stab B' (normSub (hF.normComm hK₀ hb hbA)) := by
  intro a ha
  obtain ⟨haB, hcj⟩ := mem_stab.1 ha
  refine mem_stab.2 ⟨hAB' ha, ?_⟩
  have hbA' : b ∉ stab B (cj a K₀) := by rw [hcj]; exact hbA
  have h1 := hF.normSub_conj hK₀ hb haB hbA hbA'
  rw [← h1]
  exact normSub_congr hcj _ _

theorem IsFam.normSub_le_centGenI (hF : IsFam p B 𝒦) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝒦) {b : G}
    (hb : b ∈ B) (hbA : b ∉ stab B K₀) (hgen : K₀ ≤ centGenI p (stab B K₀) K₀) :
    normSub (hF.normComm hK₀ hb hbA) ≤
      centGenI p (stab B K₀) (normSub (hF.normComm hK₀ hb hbA)) := by
  refine range_le_iSup_of_le_iSup (S := fun E : {E : Subgroup G //
      E ≤ stab B K₀ ∧ Nat.card (stab B K₀) ≤ p * Nat.card E} =>
      K₀ ⊓ Subgroup.centralizer (E.1 : Set G)) (fun E => inf_le_left) hgen
    (normHom (hF.normComm hK₀ hb hbA)) ?_
  intro E x hx
  refine ⟨⟨x, rfl⟩, Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
  have heA : e ∈ stab B K₀ := E.2.1 he
  exact commute_normHom (hF.normComm hK₀ hb hbA)
    (hF.mul_comm_of_mem (mem_stab.1 heA).1 hb) ((Subgroup.mem_centralizer_iff.1 hx.2) e he)

end Equivariance

section Main

variable [Finite G] [Fact p.Prime]

theorem IsFam.layer_le_centGenI : ∀ (a : ℕ) {B : Subgroup G} {𝒦 : Set (Subgroup G)},
    IsFam p B 𝒦 → ∀ {K₀ : Subgroup G}, K₀ ∈ 𝒦 →
    Nat.card B = p ^ a * Nat.card (stab B K₀) → K₀ ≤ centGenI p (stab B K₀) K₀ →
    layer 𝒦 ≤ centGenI p B (layer 𝒦) := by
  intro a
  induction a with
  | zero =>
    intro B 𝒦 hF K₀ hK₀ hcard hgen
    have hAB : stab B K₀ ≤ B := inf_le_left
    have hBA : stab B K₀ = B :=
      Subgroup.eq_of_le_of_card_ge hAB (by rw [hcard, pow_zero, one_mul])
    have hlay : layer 𝒦 ≤ K₀ := by
      refine iSup₂_le fun K hK => ?_
      obtain ⟨c, hc, rfl⟩ := hF.trans K₀ hK₀ K hK
      have hcA : c ∈ stab B K₀ := by rw [hBA]; exact hc
      exact (mem_stab.1 hcA).2.le
    refine hlay.trans (hgen.trans ?_)
    rw [hBA]
    exact centGenI_mono_left (le_layer hK₀)
  | succ a ih =>
    intro B 𝒦 hF K₀ hK₀ hcard hgen
    have hp := (Fact.out : p.Prime)
    have hCB : cen B K₀ ≤ B := inf_le_left
    have hAB : stab B K₀ ≤ B := inf_le_left
    have hCA : cen B K₀ ≤ stab B K₀ := cen_le_stab B K₀
    by_cases hA0 : stab B K₀ ≤ cen B K₀ ∧ a = 0
    · obtain ⟨hAC, rfl⟩ := hA0
      have hEq : cen B K₀ = stab B K₀ := le_antisymm hCA hAC
      have hle : Nat.card B ≤ p * Nat.card (cen B K₀) := by
        rw [hEq, hcard]
        simp
      refine le_trans ?_ (le_centGenI hCB hle)
      refine le_inf le_rfl (iSup₂_le fun K hK x hx => ?_)
      exact Subgroup.mem_centralizer_iff.2 fun b hb => hF.cen_comm hK₀ hb hK x hx
    · have hnorm : layer 𝒦 ≤ normJoin hF K₀ := by
        by_cases ha0 : a = 0
        · subst ha0
          have hnle : ¬ stab B K₀ ≤ cen B K₀ := fun h => hA0 ⟨h, rfl⟩
          exact hF.layer_le_normJoin_one hK₀ (by simpa using hcard) hnle
        · refine hF.layer_le_normJoin_two hK₀ ?_
          rw [hcard]
          exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos (by omega))
      refine hnorm.trans (iSup₂_le fun M hM => ?_)
      obtain ⟨b, hb, hbA, hMb⟩ := hM
      refine (le_layer hMb).trans ?_
      obtain ⟨B', hAB', hB'B, hbB', hsup⟩ := exists_complement hF.elem hAB hb hbA
      have hFN := hF.isFam_normFam hK₀ hb hbA hB'B hsup
      have hcardB : Nat.card B = p * Nat.card B' :=
        card_eq_of_complement hF.elem hB'B hb hbB' hsup
      have hM₀ : normSub (hF.normComm hK₀ hb hbA) ∈ normFam hF b hb :=
        normSub_mem_normFam hF hK₀ hb hbA
      have hstab : stab B' (normSub (hF.normComm hK₀ hb hbA)) = stab B K₀ :=
        le_antisymm (hF.stab_normSub_le hK₀ hb hbA hAB' hB'B hbB')
          (hF.stab_le_stab_normSub hK₀ hb hbA hAB')
      have hcard' : Nat.card B' =
          p ^ a * Nat.card (stab B' (normSub (hF.normComm hK₀ hb hbA))) := by
        rw [hstab]
        have h1 : p * Nat.card B' = p * (p ^ a * Nat.card (stab B K₀)) := by
          rw [← hcardB, hcard, pow_succ']
          ring
        exact Nat.eq_of_mul_eq_mul_left hp.pos h1
      have hgen' := hF.normSub_le_centGenI hK₀ hb hbA hgen
      rw [← hstab] at hgen'
      have hIH := ih hFN hM₀ hcard' hgen'
      refine hIH.trans (iSup_le fun E' => ?_)
      obtain ⟨hE'B', hE'i⟩ := E'.2
      have hE'B : E'.1 ≤ B := hE'B'.trans hB'B
      have hbE' : b ∉ E'.1 := fun h => hbB' (hE'B' h)
      have hcardE : Nat.card (E'.1 ⊔ Subgroup.zpowers b : Subgroup G) = p * Nat.card E'.1 :=
        card_sup_zpowers hF.elem hE'B hb hbE'
      have hEB : E'.1 ⊔ Subgroup.zpowers b ≤ B := sup_le hE'B ((Subgroup.zpowers_le).2 hb)
      have hEi : Nat.card B ≤ p * Nat.card (E'.1 ⊔ Subgroup.zpowers b : Subgroup G) := by
        rw [hcardE, hcardB]
        exact Nat.mul_le_mul_left _ hE'i
      refine le_trans ?_ (le_centGenI hEB hEi)
      rintro z ⟨hzN, hzE'⟩
      have hzN' := hF.layer_normFam_le hb hzN
      refine ⟨hzN'.1, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      have hle : E'.1 ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer ({z} : Set G) := by
        refine sup_le (fun e he => ?_) ((Subgroup.zpowers_le).2 ?_)
        · rw [Subgroup.mem_centralizer_iff]
          intro w hw
          rw [Set.mem_singleton_iff.1 hw]
          exact ((Subgroup.mem_centralizer_iff.1 hzE') e he).symm
        · rw [Subgroup.mem_centralizer_iff]
          intro w hw
          rw [Set.mem_singleton_iff.1 hw]
          exact ((Subgroup.mem_centralizer_iff.1 hzN'.2) b rfl).symm
      have := (Subgroup.mem_centralizer_iff.1 (hle hh)) z rfl
      exact this.symm

end Main

end GL83.CompFam
