module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1L3Neg
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1L3Syl
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1L3Gl2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Main

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace F1Proof

open Matrix CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3 CFSG.LargeExtraspecial.A2Mod
  CFSG.ABGLocalTools

section Complement

variable {F : Type} [Field F] [Finite F]

@[expose] noncomputable def fY {Y₁ : Subgroup (SL3 F)} (hYP : Y₁ ≤ P1) : ↥Y₁ →* GL (Fin 2) F :=
  rho1.comp (Subgroup.inclusion hYP)

theorem fY_injective {Y₁ : Subgroup (SL3 F)} (hYP : Y₁ ≤ P1) (hb : Y₁ ⊓ Q1 = ⊥) :
    Function.Injective (fY hYP) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  have hQ : ((Subgroup.inclusion hYP y : (P1 : Subgroup (SL3 F))) : SL3 F) ∈ Q1 :=
    mem_ker_rho1.mp hy
  have h1 : (y : SL3 F) ∈ Y₁ ⊓ Q1 := ⟨y.2, hQ⟩
  rw [hb, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.mpr (Subtype.ext h1)

theorem fY_surjective {Y₁ : Subgroup (SL3 F)} (hYP : Y₁ ≤ P1)
    (htop : (Y₁.subgroupOf P1).map rho1 = ⊤) : Function.Surjective (fY hYP) := by
  intro X
  have hX : X ∈ (Y₁.subgroupOf P1).map rho1 := by rw [htop]; trivial
  obtain ⟨g, hg, hgX⟩ := hX
  exact ⟨⟨g.1, Subgroup.mem_subgroupOf.mp hg⟩, hgX⟩

theorem neg_one_ne_one (h2 : (2 : F) ≠ 0) : (-1 : GL (Fin 2) F) ≠ 1 := by
  intro h
  have := congrArg (fun g : GL (Fin 2) F => ((g : Matrix (Fin 2) (Fin 2) F)) 0 0) h
  simp at this
  apply h2
  linear_combination -this

theorem normalizer_le_of_complement {W Y₁ : Subgroup (SL3 F)} (h2 : (2 : F) ≠ 0) (hYW : Y₁ ≤ W)
    (hYP : Y₁ ≤ P1) (hb : Y₁ ⊓ Q1 = ⊥) (htop : (Y₁.subgroupOf P1).map rho1 = ⊤)
    (hodd : ¬ 2 ∣ Y₁.relIndex W) {S : Subgroup (SL3 F)} (hS : IsSylowOf 2 S W) :
    Subgroup.normalizer (S : Set (SL3 F)) ≤ W := by
  have hf := fY_injective hYP hb
  have hsurj := fY_surjective hYP htop
  obtain ⟨z, hz⟩ := hsurj (-1)
  have hshape : NegShape (z : SL3 F) :=
    entries_of_rho1_eq_neg_one (g := ⟨(z : SL3 F), hYP z.2⟩) hz
  have hzcen : ∀ y : ↥Y₁, y * z = z * y := by
    intro y
    apply hf
    rw [map_mul, map_mul, hz, mul_neg, neg_mul, mul_one, one_mul]
  have hz2 : z * z = 1 := by
    apply hf
    rw [map_mul, hz, map_one, neg_mul_neg, mul_one]
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, map_one] at hz
    exact neg_one_ne_one h2 hz.symm
  refine normalizer_le_of_central_involution (z := (z : SL3 F)) hYW hodd z.2
    (congrArg Subtype.val hz2) (fun h => hz1 (Subtype.ext h))
    (fun y hy => congrArg Subtype.val (hzcen ⟨y, hy⟩)) ?_ ?_ hS
  ·
    intro n hn
    have hnP : n ∈ (P1 : Subgroup (SL3 F)) := mem_P1_of_comm h2 hshape hn
    obtain ⟨y, hy⟩ := hsurj (rho1 ⟨n, hnP⟩)
    have hyz : Commute (y : SL3 F) (z : SL3 F) := congrArg Subtype.val (hzcen y)
    have hm : (y : SL3 F)⁻¹ * n ∈ (Q1 : Subgroup (SL3 F)) := by
      have hmP : (y : SL3 F)⁻¹ * n ∈ (P1 : Subgroup (SL3 F)) :=
        P1.mul_mem (P1.inv_mem (hYP y.2)) hnP
      rw [← mem_ker_rho1 (g := ⟨_, hmP⟩)]
      have : (⟨(y : SL3 F)⁻¹ * n, hmP⟩ : (P1 : Subgroup (SL3 F))) =
          (⟨(y : SL3 F), hYP y.2⟩ : (P1 : Subgroup (SL3 F)))⁻¹ * ⟨n, hnP⟩ := rfl
      rw [this, map_mul, map_inv]
      have hy' : rho1 (⟨(y : SL3 F), hYP y.2⟩ : (P1 : Subgroup (SL3 F))) = rho1 ⟨n, hnP⟩ := hy
      rw [hy', inv_mul_cancel]
    have hcomm : ((y : SL3 F)⁻¹ * n) * (z : SL3 F) = (z : SL3 F) * ((y : SL3 F)⁻¹ * n) :=
      (Commute.mul_left (Commute.inv_left hyz) (show Commute n (z : SL3 F) from hn)).eq
    have h1 := eq_one_of_mem_Q1_of_comm h2 hshape hm hcomm
    have : n = y := (inv_mul_eq_one.mp h1).symm
    rw [this]
    exact y.2
  ·
    intro S₁ hS₁Y hS₁odd t ht htc htt
    set T : Subgroup (GL (Fin 2) F) := (S₁.subgroupOf Y₁).map (fY hYP) with hT
    have hTidx : ¬ 2 ∣ T.index := by
      have : T.index = (S₁.subgroupOf Y₁).index :=
        Subgroup.index_map_of_bijective ⟨hf, hsurj⟩ _
      rw [this]
      exact hS₁odd
    set t' : ↥Y₁ := ⟨t, hS₁Y ht⟩ with ht'
    have hZ : ((fY hYP t' : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((fY hYP t' : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Units.val_mul, ← map_mul]
      have : t' * t' = 1 := Subtype.ext htt
      rw [this, map_one]
      rfl
    have hcomm : ∀ g ∈ T, ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((fY hYP t' : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        ((fY hYP t' : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      rintro g ⟨s', hs', rfl⟩
      have : s' * t' = t' * s' := Subtype.ext (htc s'.1 (Subgroup.mem_subgroupOf.mp hs'))
      rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, this]
    rcases eq_one_or_neg_one_of_odd_index h2 hTidx hZ hcomm with h | h
    · left
      have h' : fY hYP t' = 1 := Units.ext (by rw [h]; rfl)
      exact congrArg Subtype.val (hf (h'.trans (map_one _).symm))
    · right
      have h' : fY hYP t' = fY hYP z := by
        rw [hz]
        exact Units.ext (by rw [h]; simp)
      exact congrArg Subtype.val (hf h')

end Complement

section Transitive

variable {F : Type} [Field F] [Finite F]

theorem normalizer_le_of_transitive (hq : Nat.card F % 3 = 2) (hodd : ¬ 2 ∣ Nat.card F)
    (hmax : GL2NonsplitMax F) {W : Subgroup (SL3 F)}
    (hNW : Subgroup.normalizer ((A0 : Subgroup (SL3 F)) : Set (SL3 F)) ≤ W)
    (htr : ∀ v : Fin 3 → F, v ≠ 0 → InOrbit W v) (hb : (W ⊓ P1) ⊓ Q1 = ⊥)
    {S : Subgroup (SL3 F)} (hS : IsSylowOf 2 S W) :
    Subgroup.normalizer (S : Set (SL3 F)) ≤ W := by
  have hroot := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves.sq_add_self_add_one_ne_zero hq
  have h3 := three_ne_zero_of_mod hq
  have h5 : 5 ≤ Nat.card F := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    omega
  obtain ⟨μ, hμ0, hμ6⟩ := exists_pow_six_ne_one hq h5
  have hlev : ∀ X : GL (Fin 2) F,
      (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix (Fin 2) (Fin 2) F) →
        lev X ∈ W :=
    fun X hX => hNW (lev_mem_normalizer_A0 (mem_Nt_of_comm hX))
  have hNtY : (Nt : Subgroup (GL (Fin 2) F)) ≤ ((W ⊓ P1).subgroupOf P1).map rho1 := by
    intro X hX
    exact ⟨⟨lev X, lev_mem_P1 X⟩,
      Subgroup.mem_subgroupOf.mpr ⟨hNW (lev_mem_normalizer_A0 hX), lev_mem_P1 X⟩, rho1_lev X⟩
  rcases hmax _ hNtY with h | h
  · exact (false_of_map_rho1_le_Nt hroot hμ0 hμ6 hlev htr h.le).elim
  · have htop := map_rho1_eq_top hroot h3 hNtY h
    refine normalizer_le_of_complement (two_ne_zero_of_odd_card hodd) inf_le_left inf_le_right hb
      htop ?_ hS
    have hodd' : Odd (Nat.card F ^ 2 + Nat.card F + 1) := by
      have : Even (Nat.card F ^ 2 + Nat.card F) := by
        rw [show Nat.card F ^ 2 + Nat.card F = Nat.card F * (Nat.card F + 1) by ring]
        exact Nat.even_mul_succ_self _
      exact this.add_one
    rw [Subgroup.inf_relIndex_left, relIndex_P1_of_transitive htr, index_P1]
    intro hd
    exact (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr hd)

end Transitive

end F1Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
