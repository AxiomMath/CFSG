module

public import CFSG.CGT.PushingUpLit.BHS7.Pending
public import CFSG.CGT.PushingUpLit.BHS6.SixTwelveB
public import CFSG.CGT.PushingUpLit.BHS7.BlockV
public import CFSG.CGT.PushingUpLit.BHS7.SevenThree

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem btBlocksG_conjSub {G T : Subgroup Γ} {g : Γ} (hg : g ∈ G) :
    btBlocksG G (A1b.conjSub g T) = btBlocksG G T := by
  ext E
  constructor
  · rintro ⟨h, hh, hE⟩
    exact ⟨h * g, G.mul_mem hh hg, by rwa [A1b.conjSub_mul]⟩
  · rintro ⟨h, hh, hE⟩
    refine ⟨h * g⁻¹, G.mul_mem hh (G.inv_mem hg), ?_⟩
    rwa [← A1b.conjSub_mul, mul_assoc, inv_mul_cancel, mul_one]

theorem btBlocksMax_conjSub {G T : Subgroup Γ} {g : Γ} (hg : g ∈ G) :
    btBlocksMax G (A1b.conjSub g T) = btBlocksMax G T := by
  unfold btBlocksMax
  rw [btBlocksG_conjSub hg]

theorem cStarIn_conjSub_of_mem {G T : Subgroup Γ} {g : Γ} (hg : g ∈ G) :
    cStarIn G (A1b.conjSub g T) = A1b.conjSub g (cStarIn G T) := by
  have e := cStarIn_conjSub g G T
  rwa [BHS.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hg)] at e

theorem mem_bStarG_of_mem_bStarT {G T E : Subgroup Γ} (hE : E ∈ bStarT G T) :
    E ∈ bStarG G T :=
  ⟨1, G.one_mem, by rwa [A1b.conjSub_one]⟩

theorem conjSub_mem_bStarT {G T E : Subgroup Γ} (hE : E ∈ bStarT G T) {g : Γ} (hg : g ∈ G) :
    A1b.conjSub g E ∈ bStarT G (A1b.conjSub g T) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [btBlocksMax_conjSub hg]
    exact conjSub_mem_btBlocksMax hE.1.1 hg
  · have := isBTBlock_conj g hE.1.2
    rwa [BHS.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hg)] at this
  · intro h
    apply hE.2
    rw [cStarIn_conjSub_of_mem hg] at h
    have h3 := A1b.conjSub_mono g⁻¹ h
    rwa [← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one, ← A1b.conjSub_mul,
      inv_mul_cancel, A1b.conjSub_one] at h3

theorem conjSub_mem_omegaSet {G T E : Subgroup Γ} (hE : E ∈ omegaSet G T) {g : Γ} (hg : g ∈ G) :
    A1b.conjSub g E ∈ omegaSet G T := by
  obtain ⟨⟨x, hx, hEx⟩, hsub⟩ := hE
  refine ⟨⟨g * x, G.mul_mem hg hx, ?_⟩, isSubnormal_conjSub hg hsub⟩
  rw [A1b.conjSub_mul]
  exact conjSub_mem_bStarT hEx hg

variable [Finite Γ] {G T : Subgroup Γ}

omit [Finite Γ] in
theorem mem_btBlocksMax_of_mem_bStarG {E : Subgroup Γ} (hE : E ∈ bStarG G T) :
    E ∈ btBlocksMax G T := by
  obtain ⟨x, hx, hEx⟩ := hE
  rw [← btBlocksMax_conjSub hx]
  exact hEx.1.1

theorem omega_not_le_cStarIn (h : MinCex G T) {E : Subgroup Γ} (hE : E ∈ omegaSet G T) :
    ¬ E ≤ cStarIn G T := by
  have hT : IsSylowTwoOf T G := h.sylow
  have hb0 : baum T ≠ ⊥ := fun h0 => h.ne (cStarIn_eq_of_baum_eq_bot h0)
  obtain ⟨⟨x, hx, hEx⟩, hsub⟩ := hE
  have hEG : E ∈ btBlocksG G T := (mem_btBlocksMax_of_mem_bStarG ⟨x, hx, hEx⟩).1
  obtain ⟨hEB, hBN⟩ := six_twelve_a h.charTwo h.sylow hEG hsub
  have hTx : IsSylowTwoOf (A1b.conjSub x T) G := isSylowTwoOf_conjSub_of_mem hT hx
  have hBG : baumG G T ≤ G := iSup₂_le fun y hy =>
    ((inf_le_left : baum (A1b.conjSub y T) ≤ _).trans
      (isSylowTwoOf_conjSub_of_mem hT hy).1)
  have hB1 : baum T ≤ baumG G T := by
    have := baum_conjSub_le_baumG (G := G) (T := T) (x := 1) G.one_mem
    rwa [A1b.conjSub_one] at this
  obtain ⟨c, hc, hcb⟩ := exists_conj_baum_of_le_of_le (N := baumG G T) hT hTx hBG hB1
    (baum_conjSub_le_baumG hx)
  have hcG : c ∈ G := hBG hc
  have hT'' : IsSylowTwoOf (A1b.conjSub c T) G := isSylowTwoOf_conjSub_of_mem hT hcG
  have hb'' : baum (A1b.conjSub c T) = baum (A1b.conjSub x T) := by
    rw [baum_conjSub, ← hcb]
  have hcs : cStarIn G (A1b.conjSub x T) = cStarIn G (A1b.conjSub c T) :=
    cStarIn_eq_of_baum_eq hT'' hTx hb''.symm (by
      rw [baum_conjSub]
      intro h0
      exact hb0 ((conjSub_eq_bot_iff c _).mp h0))
  intro hEC
  apply hEx.2
  rw [hcs, cStarIn_conjSub_of_mem hcG]
  have hcE : A1b.conjSub c E = E := BHS.conjSub_eq_of_mem_normalizer (hBN hc)
  intro e he
  have h1 : e ∈ A1b.conjSub c (cStarIn G T) := by
    have := A1b.conjSub_mono c hEC
    rw [hcE] at this
    exact this he
  exact h1

theorem omega_not_le_cStarIn_conj (h : MinCex G T) {E : Subgroup Γ} (hE : E ∈ omegaSet G T)
    {y : Γ} (hy : y ∈ G) : ¬ E ≤ cStarIn G (A1b.conjSub y T) := by
  intro hle
  rw [cStarIn_conjSub_of_mem hy] at hle
  have h1 := A1b.conjSub_mono y⁻¹ hle
  rw [← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one] at h1
  exact omega_not_le_cStarIn h (conjSub_mem_omegaSet hE (G.inv_mem hy)) h1

theorem omega_isBTBlock (h : MinCex G T) {E : Subgroup Γ} (hE : E ∈ omegaSet G T) :
    IsBTBlock G T E := by
  have hEG : E ∈ btBlocksG G T := (mem_btBlocksMax_of_mem_bStarG hE.1).1
  have := six_twelve_b_of_not_le_cStar h.charTwo h.sylow hEG hE.2 G.one_mem
    (by rw [A1b.conjSub_one]; exact omega_not_le_cStarIn h hE)
  rwa [A1b.conjSub_one] at this

theorem omega_comm (h : MinCex G T) {E E' : Subgroup Γ}
    (hE : E ∈ omegaSet G T) (hE' : E' ∈ omegaSet G T) (hne : E' ≠ E) : ⁅E', E⁆ = ⊥ := by
  have hEG : E ∈ btBlocksG G T := (mem_btBlocksMax_of_mem_bStarG hE.1).1
  have hE'G : E' ∈ btBlocksG G T := (mem_btBlocksMax_of_mem_bStarG hE'.1).1
  rcases six_twelve_c h.charTwo h.sylow hEG hE.2 hE'G with hle | hc
  · exact absurd ((mem_btBlocksMax_of_mem_bStarG hE'.1).2 E hEG hle).symm hne
  · exact hc

end CFSG.CGT.PushingUpLit.BHS7
