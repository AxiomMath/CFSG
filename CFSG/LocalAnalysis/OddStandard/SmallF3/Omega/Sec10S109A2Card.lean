module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10BData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109A2Ctx

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G}
  {K1 K2 : Subgroup G} {g : G}

theorem sec10A2_sylow_PC (hb : Asc82Basic10) (hctx : Sec10Ctx G t L S z K1 K2) :
    IsSylow2Of (S ⊓ L) (L ⊓ centralizer ({z} : Set G)) := by
  obtain ⟨-, -, -, -, -, hsylL⟩ := hb G t L S z hctx.toSec10Z
  have hSz : S ≤ centralizer ({z} : Set G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hctx.central s hs)
  have hPY : S ⊓ L ≤ L ⊓ centralizer ({z} : Set G) :=
    le_inf inf_le_right (le_trans inf_le_left hSz)
  refine ⟨hPY, hsylL.2.1, ?_⟩
  intro hdvd
  have hmul := Subgroup.relIndex_mul_relIndex (H := S ⊓ L)
    (K := L ⊓ centralizer ({z} : Set G)) (L := L) hPY inf_le_left
  exact hsylL.2.2 (hmul ▸ dvd_mul_of_dvd_left hdvd _)

theorem sec10A2_card_P (hf : Asc82Facts10) (hb : Asc82Basic10)
    (hctx : Sec10Ctx G t L S z K1 K2) : Nat.card ↥(S ⊓ L) = 64 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl := sec10A2_sylow_PC hb hctx
  have hpsp : IsPSp43 L := (hb G t L S z hctx.toSec10Z).1
  have hC : Nat.card ↥(L ⊓ centralizer ({z} : Set G)) = 576 :=
    hf.centZ5 G L hpsp z hctx.toSec10Z.pocket
  have h1 := Subgroup.relIndex_mul_card (H := S ⊓ L) (K := L ⊓ centralizer ({z} : Set G))
  rw [inf_of_le_left hsyl.1, hC] at h1
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hsyl.2.1
  have hdvd : 2 ^ a ∣ 576 := ⟨_, by rw [← ha, mul_comm]; exact h1.symm⟩
  have ha10 : a < 10 := by
    by_contra hge
    have h2 : 2 ^ 10 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hge)
    have h3 := Nat.le_of_dvd (by norm_num) hdvd
    norm_num at h2
    omega
  rw [ha] at h1 ⊢
  have hodd := hsyl.2.2
  interval_cases a <;> omega

theorem sec10A2_exists_swap_elem (hf : Asc82Facts10) (hb : Asc82Basic10)
    (hctx : Sec10Ctx G t L S z K1 K2) : ∃ s ∈ S ⊓ L, s ∉ K1 ⊔ K2 := by
  by_contra hcon
  have hle : S ⊓ L ≤ K1 ⊔ K2 := fun s hs => by
    by_contra hs'
    exact hcon ⟨s, hs, hs'⟩
  have hpsp : IsPSp43 L := (hb G t L S z hctx.toSec10Z).1
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [sec10A2_card_P hf hb hctx, sec10KS_card_sup hf.pockets5 hf.centZ5 hpsp hctx] at hdvd
  norm_num at hdvd

theorem sec10A2_swap (hf : Asc82Facts10) (hb : Asc82Basic10)
    (hctx : Sec10Ctx G t L S z K1 K2) :
    ∀ s ∈ L ⊓ centralizer ({z} : Set G), s ∉ K1 ⊔ K2 → ∀ k ∈ K1, s * k * s⁻¹ ∈ K2 := by
  have hpsp : IsPSp43 L := (hb G t L S z hctx.toSec10Z).1
  obtain ⟨K1', K2', -, -, -, huniq, -, -, -, hswap⟩ :=
    hf.pockets5 G L hpsp z hctx.toSec10Z.pocket
  have hmem : ∀ (s : G) (x : G), s ∈ L ⊓ centralizer ({z} : Set G) → s ∉ K1' ⊔ K2' →
      (x ∈ K2' ↔ s * x * s⁻¹ ∈ K1') := fun s x hs hn => by
    have := hswap s hs hn
    rw [← this]
    exact mem_conjugate_iff'
  have hab : ∀ s ∈ L ⊓ centralizer ({z} : Set G), s ∉ K1' ⊔ K2' →
      (∀ k ∈ K1', s * k * s⁻¹ ∈ K2') ∧ ∀ k ∈ K2', s * k * s⁻¹ ∈ K1' := by
    intro s hs hn
    refine ⟨fun k hk => ?_, fun k hk => (hmem s k hs hn).mp hk⟩
    have hs' : s⁻¹ ∈ L ⊓ centralizer ({z} : Set G) := (L ⊓ centralizer ({z} : Set G)).inv_mem hs
    have hn' : s⁻¹ ∉ K1' ⊔ K2' := fun h => hn (by simpa using (K1' ⊔ K2').inv_mem h)
    have e : s⁻¹ * (s * k * s⁻¹) * s⁻¹⁻¹ = k := by group
    exact (hmem s⁻¹ (s * k * s⁻¹) hs' hn').mpr (by rw [e]; exact hk)
  rcases huniq K1 hctx.pocket1 with rfl | rfl <;> rcases huniq K2 hctx.pocket2 with rfl | rfl
  · exact absurd rfl hctx.ne
  · intro s hs hn k hk
    exact (hab s hs hn).1 k hk
  · intro s hs hn k hk
    refine (hab s hs ?_).2 k hk
    rwa [sup_comm]
  · exact absurd rfl hctx.ne

theorem sec10A2_B_facts (hf : Asc82Facts10) (hb : Asc82Basic10)
    (hctx : Sec10Ctx G t L S z K1 K2) :
    (∀ D : Subgroup G, D ≤ S ⊓ L → CFSG.Open.IsElemAbelian 2 D → Nat.card D ≤ 16) ∧
      ∀ D : Subgroup G, D ≤ S ⊓ L → IsMulCommutative D → Nat.card D = 16 → D = secB S L := by
  obtain ⟨hpsp, -, -, -, -, hsyl⟩ := hb G t L S z hctx.toSec10Z
  obtain ⟨B, hBmax, hB16, hBuniq, -⟩ := hf.b5 G L hpsp (S ⊓ L) hsyl
  have hJ : secB S L = B := by
    refine le_antisymm ?_ ?_
    · rw [secB, JElem]
      refine (Subgroup.closure_le B).mpr ?_
      rintro x ⟨A, hAmax, hxA⟩
      have hAle : A ≤ S ⊓ L := hAmax.1
      have hAel : CFSG.Open.IsElemAbelian 2 A := hAmax.2.1
      have hcardAB : Nat.card A ≤ Nat.card B := hBmax.2.2 A hAle hAel
      have hcardBA : Nat.card B ≤ Nat.card A := hAmax.2.2 B hBmax.1 hBmax.2.1
      have hcardA : Nat.card A = 2 ^ 4 := (le_antisymm hcardAB hcardBA).trans hB16
      have hAB : A = B := hBuniq A hAle hAel.1 hcardA
      rwa [hAB] at hxA
    · rw [secB, JElem]
      intro b hb'
      exact Subgroup.subset_closure ⟨B, hBmax, hb'⟩
  refine ⟨fun D hD hDel => ?_, fun D hD hDc hD16 => ?_⟩
  · have := hBmax.2.2 D hD hDel
    rw [hB16] at this
    norm_num at this
    exact this
  · rw [hJ]
    exact hBuniq D hD hDc (by rw [hD16]; norm_num)

theorem sec10A2_isElemAbelian_mono {D E : Subgroup G} (hDE : D ≤ E)
    (hE : CFSG.Open.IsElemAbelian 2 E) : CFSG.Open.IsElemAbelian 2 D :=
  ⟨isMulCommutative_iff.mpr fun a b =>
      Subtype.ext (sec10A2_elem_comm hE (hDE a.2) (hDE b.2)),
    fun x hx => hE.2 x (hDE hx)⟩

theorem sec10A2_branch (h : Asc82Res10a) (hctx : Sec10A2Ctx G t L S z K1 K2 g) :
    ∃ A2 : Subgroup G, A2 ≤ S ∧ IsElemAb2 A2 5 ∧ IsElemAb2 (secA t S L) 5 ∧
      A2 ≠ secA t S L := by
  rcases h.l107c G t L S z K1 K2 hctx.toSec10Ctx with hJ | ⟨r, -, -, -, hne, hX⟩
  · exfalso
    apply hctx.not_M
    show g ∈ normalizer ((secA t S L : Subgroup G) : Set G)
    rw [hJ]
    exact sec10A_mem_normalizer_jElem hctx.norm
  · have hA : IsNormalE32In S (secA t S L) := (hX _).mpr (Or.inl rfl)
    have hA2 : IsNormalE32In S (secA2 t r K1 K2) := (hX _).mpr (Or.inr rfl)
    exact ⟨secA2 t r K1 K2, hA2.1, hA2.2.1, hA.2.1, hne⟩

theorem sec10A2_relIndex_ne_two (hf : Asc82Facts10) (hb : Asc82Basic10)
    (hctx : Sec10Ctx G t L S z K1 K2) {A2 : Subgroup G} (hA2S : A2 ≤ S)
    (hA2e : IsElemAb2 A2 5) (hAe : IsElemAb2 (secA t S L) 5) (hne : A2 ≠ secA t S L) :
    (S ⊓ L).relIndex S ≠ 2 := by
  intro h2
  obtain ⟨-, htC, htL, htS, -, -⟩ := hb G t L S z hctx.toSec10Z
  obtain ⟨hmax, huniq⟩ := sec10A2_B_facts hf hb hctx
  obtain ⟨hBL, -, hBC, -, -⟩ := sec10BData_of hb hf.b5 hctx.toSec10Z
  have hDel : CFSG.Open.IsElemAbelian 2 ((S ⊓ L) ⊓ A2) :=
    sec10A2_isElemAbelian_mono inf_le_right hA2e.1
  have hD16 : Nat.card ↥((S ⊓ L) ⊓ A2) ≤ 16 := hmax _ inf_le_left hDel
  have hmul : (S ⊓ L).relIndex A2 * Nat.card ↥((S ⊓ L) ⊓ A2) = 32 := by
    rw [Subgroup.relIndex_mul_card, hA2e.2]
    norm_num
  have hcardD : Nat.card ↥((S ⊓ L) ⊓ A2) = 16 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (sec10A2_relIndex_dvd_two hA2S h2) with h1 | h1
    · rw [h1] at hmul
      omega
    · rw [h1] at hmul
      omega
  have hDB : (S ⊓ L) ⊓ A2 = secB S L := huniq _ inf_le_left hDel.1 hcardD
  have hBA2 : secB S L ≤ A2 := by
    rw [← hDB]
    exact inf_le_right
  have hsub : A2 ≤ secA t S L := by
    intro x hx
    have hxc : ∀ b ∈ secB S L, b * x = x * b := fun b hb' =>
      (sec10A2_elem_comm hA2e.1 hx (hBA2 hb')).symm
    by_cases hxP : x ∈ S ⊓ L
    · have hx' : x ∈ centralizer (secB S L : Set G) ⊓ L :=
        ⟨Subgroup.mem_centralizer_iff.mpr hxc, hxP.2⟩
      rw [hBC] at hx'
      exact Subgroup.mem_sup_left hx'
    · have hp : t⁻¹ * x ∈ S ⊓ L :=
        sec10A2_idx2_mul h2 htS (hA2S hx) (fun h' => htL h'.2) hxP
      have hpc : ∀ b ∈ secB S L, b * (t⁻¹ * x) = (t⁻¹ * x) * b := by
        intro b hb'
        have hbt : Commute b t := Subgroup.mem_centralizer_iff.mp htC b (hBL hb')
        calc b * (t⁻¹ * x) = (b * t⁻¹) * x := by group
          _ = (t⁻¹ * b) * x := by rw [hbt.inv_right.eq]
          _ = t⁻¹ * (b * x) := by group
          _ = t⁻¹ * (x * b) := by rw [hxc b hb']
          _ = (t⁻¹ * x) * b := by group
      have hp' : t⁻¹ * x ∈ centralizer (secB S L : Set G) ⊓ L :=
        ⟨Subgroup.mem_centralizer_iff.mpr hpc, hp.2⟩
      rw [hBC] at hp'
      have := Subgroup.mul_mem (secA t S L) (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
        (Subgroup.mem_sup_left hp')
      simpa using this
  exact hne (Subgroup.eq_of_le_of_card_ge hsub (hAe.2.trans hA2e.2.symm).le)

theorem sec10A2_card_S (h : Asc82Res10a) (hf : Asc82Facts10) (hb : Asc82Basic10)
    (hctx : Sec10A2Ctx G t L S z K1 K2 g) : 256 ≤ Nat.card ↥S := by
  obtain ⟨A2, hA2S, hA2e, hAe, hne⟩ := sec10A2_branch h hctx
  have hne2 := sec10A2_relIndex_ne_two hf hb hctx.toSec10Ctx hA2S hA2e hAe hne
  obtain ⟨-, -, htL, htS, -, -⟩ := hb G t L S z hctx.toSec10Z
  have hP64 := sec10A2_card_P hf hb hctx.toSec10Ctx
  have h1 := Subgroup.relIndex_mul_card (H := S ⊓ L) (K := S)
  rw [inf_of_le_left (inf_le_left : S ⊓ L ≤ S), hP64] at h1
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hctx.sylow.2.1
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro 64 (h1.trans hn))
  rcases k with _ | _ | k
  · exfalso
    have h0 : (S ⊓ L).relIndex S = 1 := by simpa using hk
    exact htL ((Subgroup.relIndex_eq_one.mp h0) htS).2
  · exact absurd (by simpa using hk) hne2
  · have h4 : 4 ≤ 2 ^ (k + 1 + 1) := by
      rw [pow_succ, pow_succ]
      have := Nat.one_le_two_pow (n := k)
      omega
    rw [hk] at h1
    calc 256 = 4 * 64 := by norm_num
      _ ≤ 2 ^ (k + 1 + 1) * 64 := Nat.mul_le_mul_right 64 h4
      _ = Nat.card ↥S := h1

end CFSG.OddStandard.SmallF3.Omega
