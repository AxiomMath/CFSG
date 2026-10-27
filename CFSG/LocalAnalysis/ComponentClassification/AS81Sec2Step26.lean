module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step26V

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

section FrameXH

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
  {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F) {h : G} (hh : h ∈ sec2P E)
  (hhS : h ∉ sec2S A R E F) (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))
  (h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E)))

include h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'

theorem nonempty_coord_sec2 :
    Nonempty (Sec2.Coord (sec2S A R E F) (sec2Z A E F) (sec2H E F)) := by
  obtain ⟨φ, hφ, hker, S₂, S₃, ψ₂, ψ₃, hsup, hinf, hi⟩ :=
    exists_sec2V h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  obtain ⟨hZ₂, hle₂, hadd₂, hker₂, hsum₂, honto₂, hconj₂⟩ := hi (S₂, ψ₂) (Set.mem_insert _ _)
  obtain ⟨hZ₃, hle₃, hadd₃, hker₃, hsum₃, honto₃, hconj₃⟩ :=
    hi (S₃, ψ₃) (Set.mem_insert_of_mem _ rfl)
  exact ⟨⟨φ, hφ, hker, S₂, S₃, ψ₂, ψ₃, hsup, hinf, hZ₂, hZ₃, hle₂, hle₃, hadd₂, hadd₃, hker₂,
    hker₃, hsum₂, hsum₃, honto₂, honto₃, hconj₂, hconj₃⟩⟩

theorem commutator_set_eq_sec2Z {s : G} (hs : s ∈ sec2S A R E F) (hsZ : s ∉ sec2Z A E F) :
    {c | ∃ t ∈ sec2S A R E F, c = s⁻¹ * t⁻¹ * s * t} = (sec2Z A E F : Set G) := by
  have hS := special_sec2S h11 hE16 hF hL hodd
  obtain ⟨C⟩ := nonempty_coord_sec2 h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  obtain ⟨u, y, huy⟩ := exists_sec2UY h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  obtain ⟨ξ, hξo, -, hF4, hcl, -, -⟩ :=
    exists_of_sec2UY h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' huy
  have hξ3 : ξ ^ 3 = 1 := by rw [← hξo]; exact pow_orderOf_eq_one ξ
  have hHS := sec2H_le_normalizer_sec2S h11 hE16 hF hL hodd
  set Z := sec2Z A E F with hZdef
  have hcZ : ∀ t ∈ sec2S A R E F, s⁻¹ * t⁻¹ * s * t ∈ Z := fun t ht => by
    simpa using hS.comm_mem (inv_mem hs) (inv_mem ht)
  have hcmul : ∀ t ∈ sec2S A R E F, ∀ t' ∈ sec2S A R E F,
      s⁻¹ * (t * t')⁻¹ * s * (t * t') = (s⁻¹ * t⁻¹ * s * t) * (s⁻¹ * t'⁻¹ * s * t') := by
    intro t ht t' ht'
    have h1 := hS.comm_Z (hcZ t ht) (inv_mem ht')
    calc s⁻¹ * (t * t')⁻¹ * s * (t * t')
        = s⁻¹ * t'⁻¹ * s * t' * (t'⁻¹ * (s⁻¹ * t⁻¹ * s * t) * t') := by group
      _ = s⁻¹ * t'⁻¹ * s * t' * ((s⁻¹ * t⁻¹ * s * t) * t'⁻¹ * t') := by
          rw [← h1]
      _ = (s⁻¹ * t⁻¹ * s * t) * (s⁻¹ * t'⁻¹ * s * t') := by
          rw [inv_mul_cancel_right]
          exact hS.comm_Z (hcZ t' ht') (hS.le (hcZ t ht))
  refine Set.Subset.antisymm (fun c ⟨t, ht, hc⟩ => hc ▸ hcZ t ht) fun z hz => ?_
  by_contra hzI
  have hzI' : ∀ t ∈ sec2S A R E F, z ≠ s⁻¹ * t⁻¹ * s * t := fun t ht h1 => hzI ⟨t, ht, h1⟩
  obtain ⟨c, hc, hc1, hcI⟩ : ∃ c ∈ Z, c ≠ 1 ∧ ∀ t ∈ sec2S A R E F,
      s⁻¹ * t⁻¹ * s * t ∈ zpowers c := by
    by_cases hex : ∃ t ∈ sec2S A R E F, s⁻¹ * t⁻¹ * s * t ≠ 1
    · obtain ⟨t₀, ht₀, hne⟩ := hex
      refine ⟨_, hcZ t₀ ht₀, hne, fun t ht => ?_⟩
      by_contra hnot
      have hb1 : s⁻¹ * t⁻¹ * s * t ≠ 1 := fun h1 => hnot (h1 ▸ one_mem _)
      have hba : s⁻¹ * t₀⁻¹ * s * t₀ ≠ s⁻¹ * t⁻¹ * s * t := fun h1 => hnot (h1 ▸ mem_zpowers _)
      have hab1 : s⁻¹ * t₀⁻¹ * s * t₀ * (s⁻¹ * t⁻¹ * s * t) ≠ 1 := fun h1 => by
        apply hba
        have h2 := hS.inv_eq (hcZ t ht)
        rw [← h2]
        exact eq_inv_of_mul_eq_one_left h1
      have hab2 : s⁻¹ * t₀⁻¹ * s * t₀ ≠ s⁻¹ * t₀⁻¹ * s * t₀ * (s⁻¹ * t⁻¹ * s * t) := fun h1 =>
        hb1 (mul_left_cancel ((mul_one _).trans h1)).symm
      have hab3 : s⁻¹ * t⁻¹ * s * t ≠ s⁻¹ * t₀⁻¹ * s * t₀ * (s⁻¹ * t⁻¹ * s * t) := fun h1 =>
        hne (mul_right_cancel (h1.symm.trans (one_mul _).symm))
      rcases hS.eq_of_four (one_mem _) (hcZ t₀ ht₀) (hcZ t ht)
          ((sec2Z A E F).mul_mem (hcZ t₀ ht₀) (hcZ t ht)) hz (Ne.symm hne) (Ne.symm hb1)
          (Ne.symm hab1) hba hab2 hab3 with h1 | h1 | h1 | h1
      · exact hzI' 1 (one_mem _) (by rw [h1]; group)
      · exact hzI' t₀ ht₀ h1
      · exact hzI' t ht h1
      · exact hzI' (t₀ * t) (mul_mem ht₀ ht) (by rw [h1, hcmul t₀ ht₀ t ht])
    · push Not at hex
      have hZ1 : sec2Z A E F ≠ ⊥ := fun h0 => by
        have := hF.card_sec2Z hodd
        rw [h0, card_bot] at this
        omega
      obtain ⟨⟨c, hc⟩, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ1
      exact ⟨c, hc, fun h0 => hc1 (Subtype.ext h0), fun t ht => by
        rw [hex t ht]
        exact one_mem _⟩
  apply hsZ
  refine C.mem_of_comm_mem_zpowers hS hHS hF4.1 hF4.2.1 hξ3 hcl hc hc1 hs fun t ht => ?_
  have h1 := hcI t⁻¹ (inv_mem ht)
  rw [show s * t * s⁻¹ * t⁻¹ = (s * (s⁻¹ * t⁻¹⁻¹ * s * t⁻¹) * s⁻¹)⁻¹ by group,
    hS.conj_Z (hcZ _ (inv_mem ht)) hs]
  exact inv_mem h1

end FrameXH

theorem step26_of (h11 : Step11)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (h22iv : Step22iv) : Step26 := by
  intro G _ _ A R g E F hS
  have hF := hS.frame
  have hL := hS.type
  have hodd := hS.odd
  have hSc := sec2S_comm h11 hE16 hF hL hodd
  have h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)) :=
    h22iv G A R g F E ⟨hF.symm, hL, hodd, hS.below⟩
  have h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E)) := h22iv G A R g E F hS
  obtain ⟨h, hh, hhC⟩ := exists_mem_sec2P_not_mem_centralizerMod h11 hE16 hF hL hodd
  have hhS : h ∉ sec2S A R E F := fun hS' => hhC (by
    rw [← sec2S_inf_sec2P h11 hE16 hF hL hodd]
    exact ⟨hS', hh⟩)
  obtain ⟨x, hx, hxC⟩ := exists_mem_sec2P_not_mem_centralizerMod h11 hE16 hF.symm hL hodd
  have hxS : x ∉ sec2S A R E F := fun hS' => hxC (by
    rw [← sec2S_inf_sec2P h11 hE16 hF.symm hL hodd, hSc]
    exact ⟨hS', hx⟩)
  exact ⟨fun s hs hsZ => commutator_set_eq_sec2Z h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hs hsZ,
    sec2S_le_sec2H hF,
    exists_hom_alternatingGroup_ker_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4',
    sec2H_inf_centralizer_sec2S_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4',
    isSylowOf_sec2Z_centralizer_sec2S h11 hE16 hF hL hodd,
    isSylowOf_sec2S_centralizerMod h11 hE16 hF hL hodd,
    exists_sec2V h11 hE16 hF hL hodd hx hxS hh hhS h4 h4',
    sec2H_le_normalizer_sec2S h11 hE16 hF hL hodd,
    normalizer_sec2S_le_normalizer_sec2H h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'⟩

end CFSG.ComponentClassification.AS81
