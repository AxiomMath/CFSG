module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzEndK
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuz
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma38Core
public import CFSG.Certificates.Kernel.SporSch.SylowLab

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Suz

open Subgroup CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Fischer CFSG.KS.SylowLab
open CFSG.ComponentClassification.RankTwoSporadic.Endgame
open scoped commutatorElement

theorem fix1782_conj (g σ : Equiv.Perm (Fin 1782)) : fix1782 (g * σ * g⁻¹) = fix1782 σ := by
  rw [fix1782, fix1782]
  refine Finset.card_bij (fun x _ => g⁻¹ x) (fun x hx => ?_) (fun x _ y _ h => ?_) ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have := congrArg (fun q => g⁻¹ q) hx
    simpa [Equiv.Perm.mul_apply] using this
  · simpa using h
  · intro y hy
    refine ⟨g y, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    simp [Equiv.Perm.mul_apply, hy]

theorem fix1782_one : fix1782 (1 : Equiv.Perm (Fin 1782)) = 1782 := by simp [fix1782]

@[expose] noncomputable def suzE0e : Equiv.Perm (Fin 1782) := permOfArr 1782 suzE0[0]!

theorem suzE0e_eq : suzE0e = suzEndE 0 := rfl

theorem permsA_suzE0 : permsA 1782 suzE0 = {suzEndE 0, suzEndE 1} := by
  ext g
  simp only [permsA, Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hs : suzE0.size = 2 := rfl
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [hs] at hk
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by rw [hs]; norm_num, rfl⟩
    · exact ⟨1, by rw [hs]; norm_num, rfl⟩

theorem suzE0Sub_eq : suzE0Sub = closure {suzEndE 0, suzEndE 1} := by
  rw [suzE0Sub, permsA_suzE0]

theorem mem_suzM_of {a : Array ℕ}
    (h : suzInMA a) : permOfArr 1782 a ∈ suzM :=
  (suzInM_iff a _ (rep_permOfArr h.1).1).1 h.2

theorem suzEndFacts_of_K
    (h : SuzEndFactsK) :
    EndFacts suzT suzM suzE0Sub suzE0e (fun σ => fix1782 σ = 42) := by
  obtain ⟨he_mem, he_sq, he_comm, ⟨hf0, hf1, hf01⟩, ⟨b, x, hb, hx, hbc, hbn, hxc, htree⟩,
    ⟨l, hl, hcardL, s, hs, hcardS, hfixS⟩, ⟨σa, hσM, hσ0, hσ1⟩, ⟨c0, hc0M, hc0e⟩⟩ := h
  have hE := suzE0Sub_eq
  have hcases : ∀ e ∈ suzE0Sub, e = 1 ∨ e = suzEndE 0 ∨ e = suzEndE 1 ∨
      e = suzEndE 0 * suzEndE 1 :=
    fun e he => mem_closure_pair (he_sq 0 (by norm_num)) (he_sq 1 (by norm_num)) he_comm
      (hE ▸ he)
  have hmemE : suzEndE 0 ∈ suzE0Sub := by
    rw [hE]
    exact subset_closure (Set.mem_insert _ _)
  have hmemE1 : suzEndE 1 ∈ suzE0Sub := by
    rw [hE]
    exact subset_closure (Set.mem_insert_of_mem _ rfl)
  have hEab : ∀ y ∈ suzE0Sub, ∀ z ∈ suzE0Sub, y * z = z * y := by
    intro y hy z hz
    rw [hE] at hy hz
    refine commute_of_mem_closure ?_ hy hz
    rintro _ (rfl | rfl) _ (rfl | rfl)
    · rfl
    · exact he_comm
    · exact he_comm.symm
    · rfl
  have hE42 : ∀ e ∈ suzE0Sub, e ≠ 1 → fix1782 e = 42 ∧ e ^ 2 = 1 := by
    intro e he he1
    have h2 : ∀ f ∈ suzE0Sub, f * f = 1 := by
      intro f hf
      rcases hcases f hf with rfl | rfl | rfl | rfl
      · exact one_mul 1
      · exact he_sq 0 (by norm_num)
      · exact he_sq 1 (by norm_num)
      · calc suzEndE 0 * suzEndE 1 * (suzEndE 0 * suzEndE 1) =
            suzEndE 0 * (suzEndE 1 * suzEndE 0) * suzEndE 1 := by simp only [mul_assoc]
          _ = suzEndE 0 * (suzEndE 0 * suzEndE 1) * suzEndE 1 := by rw [he_comm]
          _ = suzEndE 0 * suzEndE 0 * (suzEndE 1 * suzEndE 1) := by simp only [mul_assoc]
          _ = 1 := by rw [he_sq 0 (by norm_num), he_sq 1 (by norm_num), one_mul]
    refine ⟨?_, by rw [sq]; exact h2 e he⟩
    rcases hcases e he with rfl | rfl | rfl | rfl
    · exact absurd rfl he1
    · exact hf0
    · exact hf1
    · exact hf01
  set bb := permOfArr 1782 b with hbb
  refine ⟨?_, hmemE, fun e he he1 => (hE42 e he he1).1, fun g _ y hy => by rw [fix1782_conj]; exact hy,
    ⟨bb, ?_, ?_, ?_, fun i => permOfArr 1782 (x i), fun i => ⟨?_, ?_⟩, htree⟩, ?_⟩
  ·
    rw [hE, closure_le]
    rintro _ (rfl | rfl)
    · exact mem_suzM_of (he_mem 0 (by norm_num))
    · exact mem_suzM_of (he_mem 1 (by norm_num))
  · exact mem_suzM_of hb
  ·
    intro e he e' he'
    set f := (MulAut.conj bb⁻¹).toMonoidHom with hf
    have hfa : ∀ g, f g = bb⁻¹ * g * bb := fun g => by simp [hf]
    have h1 := mem_map_of_mem f he'
    rw [hE, MonoidHom.map_closure] at h1
    rw [hfa] at h1
    rw [hE] at he
    refine commute_of_mem_closure ?_ he h1
    rintro _ (rfl | rfl) _ ⟨_, (rfl | rfl), rfl⟩ <;> rw [hfa]
    · exact hbc 0 (by norm_num) 0 (by norm_num)
    · exact hbc 0 (by norm_num) 1 (by norm_num)
    · exact hbc 1 (by norm_num) 0 (by norm_num)
    · exact hbc 1 (by norm_num) 1 (by norm_num)
  ·
    intro hmem
    rw [suzE0e_eq] at hmem
    apply hbn
    rcases hcases _ hmem with h | h | h | h <;> rw [h] <;> simp
  · exact mem_suzM_of (hx i)
  ·
    intro e he
    rw [hE] at he
    have hle : closure ({suzEndE 0, suzEndE 1} : Set (Equiv.Perm (Fin 1782))) ≤
        centralizer {permOfArr 1782 (x i)} := by
      rw [closure_le]
      rintro _ (rfl | rfl) <;> rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      · exact (hxc i 0 (by norm_num)).symm
      · exact (hxc i 1 (by norm_num)).symm
    exact (mem_centralizer_singleton_iff.1 (hle he)).symm
  ·
    set E₀ := suzE0Sub with hE₀
    set L := closure (permsA 1782 l) with hLdef
    have hLE : ∀ y ∈ L, ∀ z ∈ E₀, y * z = z * y := by
      intro y hy z hz
      rw [hE] at hz
      refine commute_of_mem_closure ?_ hy hz
      rintro _ ⟨k, hk, rfl⟩ _ (rfl | rfl)
      · exact (hl k hk).2 0 (by norm_num)
      · exact (hl k hk).2 1 (by norm_num)
    have hLM : L ≤ suzM := by
      rw [hLdef, closure_le]
      rintro _ ⟨k, hk, rfl⟩
      exact mem_suzM_of (hl k hk).1
    have hEM : E₀ ≤ suzM := by
      rw [hE, closure_le]
      rintro _ (rfl | rfl)
      · exact mem_suzM_of (he_mem 0 (by norm_num))
      · exact mem_suzM_of (he_mem 1 (by norm_num))
    have hLinv : ∀ z ∈ L, z ^ 2 = 1 → z ≠ 1 → fix1782 z ≠ 42 := by
      intro z hzL hz2 hz1
      have hSL : closure (permsA 1782 s) ≤ L := by
        rw [closure_le]
        rintro _ ⟨k, hk, rfl⟩
        exact hs k hk
      obtain ⟨g, -, hgS⟩ := exists_conj_mem_of_card hSL Nat.prime_two
        (hcardS.trans (by norm_num : (64 : ℕ) = 2 ^ 6)) (hcardL.trans (by norm_num :
          (20160 : ℕ) = 2 ^ 6 * 315)) (by norm_num) hzL hz2
      have hs2 : (g⁻¹ * z * g) ^ 2 = 1 := by
        have hzz : z * z = 1 := by rw [← sq]; exact hz2
        rw [sq]
        calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by
              simp only [mul_assoc, mul_inv_cancel_left]
          _ = 1 := by rw [hzz, mul_one, inv_mul_cancel]
      have hs1 : g⁻¹ * z * g ≠ 1 := by
        intro h1
        apply hz1
        calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
          _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
      have := hfixS _ hgS hs2 hs1
      rwa [show g⁻¹ * z * g = g⁻¹ * z * g⁻¹⁻¹ by rw [inv_inv], fix1782_conj] at this
    have hcardE : Nat.card E₀ = 4 := by
      have hne1 : suzEndE 0 ≠ 1 := fun h1 => by rw [h1, fix1782_one] at hf0; norm_num at hf0
      have hne2 : suzEndE 1 ≠ 1 := fun h1 => by rw [h1, fix1782_one] at hf1; norm_num at hf1
      have hne3 : suzEndE 0 * suzEndE 1 ≠ 1 := fun h1 => by
        rw [h1, fix1782_one] at hf01; norm_num at hf01
      have hne12 : suzEndE 0 ≠ suzEndE 1 := fun h1 => by
        apply hne3
        rw [h1]
        exact he_sq 1 (by norm_num)
      have hne13 : suzEndE 0 ≠ suzEndE 0 * suzEndE 1 := fun h1 => by
        apply hne2
        have := congrArg (fun g => (suzEndE 0)⁻¹ * g) h1
        simpa using this.symm
      have hne23 : suzEndE 1 ≠ suzEndE 0 * suzEndE 1 := fun h1 => by
        apply hne1
        have := congrArg (fun g => g * (suzEndE 1)⁻¹) h1
        simpa using this.symm
      have hset : (E₀ : Set (Equiv.Perm (Fin 1782))) =
          {1, suzEndE 0, suzEndE 1, suzEndE 0 * suzEndE 1} := by
        ext y
        constructor
        · intro hy
          rcases hcases y hy with rfl | rfl | rfl | rfl <;> simp
        · rintro (rfl | rfl | rfl | rfl)
          · exact E₀.one_mem
          · exact hmemE
          · exact hmemE1
          · exact E₀.mul_mem hmemE hmemE1
      have h1 : (1 : Equiv.Perm (Fin 1782)) ∉
          ({suzEndE 0, suzEndE 1, suzEndE 0 * suzEndE 1} : Set (Equiv.Perm (Fin 1782))) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hne1.symm, hne2.symm, hne3.symm⟩
      have h2 : suzEndE 0 ∉
          ({suzEndE 1, suzEndE 0 * suzEndE 1} : Set (Equiv.Perm (Fin 1782))) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hne12, hne13⟩
      have hc := Nat.card_coe_set_eq (E₀ : Set (Equiv.Perm (Fin 1782)))
      change Nat.card ↥(E₀ : Set (Equiv.Perm (Fin 1782))) = 4
      rw [hc, hset, Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
        Set.ncard_pair hne23]
    have hinf : E₀ ⊓ L = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨hyE, hyL⟩
      rw [mem_bot]
      by_contra hy1
      obtain ⟨h42, hy2⟩ := hE42 y hyE hy1
      exact hLinv y hyL hy2 hy1 h42
    have hcardH : Nat.card (E₀ ⊔ L : Subgroup (Equiv.Perm (Fin 1782))) = 80640 := by
      have hN : L ≤ normalizer (E₀ : Set (Equiv.Perm (Fin 1782))) := by
        intro y hy
        rw [mem_normalizer_iff]
        intro z
        constructor
        · intro hz
          rw [hLE y hy z hz, mul_inv_cancel_right]
          exact hz
        · intro hz
          have e1 : y * z * y⁻¹ = z := by
            have h1 := hLE y hy (y * z * y⁻¹) hz
            have h2 : y * (y * z * y⁻¹) = y * z := by rw [h1]; group
            exact mul_left_cancel h2
          rw [← e1]
          exact hz
      rw [AS76b.card_sup_eq_mul hN hinf, hcardE, hcardL]
    set t₀ := suzInv 0 with ht₀
    set c₀ := permOfArr 1782 c0 with hc₀
    have hc₀M : c₀ ∈ suzM := mem_suzM_of hc0M
    have hc₀e : c₀ * suzE0e * c₀⁻¹ = t₀ :=
      hc0e.trans (permOfArr_eq_of_rep (rep_suzInv (by norm_num)))
    have hmemE' : suzE0e ∈ E₀ := hmemE
    have hcent : (centM t₀).map (MulAut.conj c₀⁻¹).toMonoidHom =
        suzM ⊓ centralizer {suzE0e} := by
      ext y
      simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, centM,
        mem_inf, mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨w, ⟨hwt, hwM⟩, rfl⟩
        refine ⟨suzM.mul_mem (suzM.mul_mem (suzM.inv_mem hc₀M) hwM) hc₀M, ?_⟩
        have he' : suzE0e = c₀⁻¹ * t₀ * c₀ := by rw [← hc₀e]; group
        rw [he']
        calc c₀⁻¹ * w * c₀ * (c₀⁻¹ * t₀ * c₀) = c₀⁻¹ * (w * t₀) * c₀ := by group
          _ = c₀⁻¹ * (t₀ * w) * c₀ := by rw [hwt]
          _ = c₀⁻¹ * t₀ * c₀ * (c₀⁻¹ * w * c₀) := by group
      · rintro ⟨hyM, hye⟩
        refine ⟨c₀ * y * c₀⁻¹, ⟨?_, suzM.mul_mem (suzM.mul_mem hc₀M hyM) (suzM.inv_mem hc₀M)⟩,
          by group⟩
        rw [← hc₀e]
        calc c₀ * y * c₀⁻¹ * (c₀ * suzE0e * c₀⁻¹) = c₀ * (y * suzE0e) * c₀⁻¹ := by group
          _ = c₀ * (suzE0e * y) * c₀⁻¹ := by rw [hye]
          _ = c₀ * suzE0e * c₀⁻¹ * (c₀ * y * c₀⁻¹) := by group
    have hcardC : Nat.card (suzM ⊓ centralizer {suzE0e} : Subgroup (Equiv.Perm (Fin 1782))) =
        161280 := by
      rw [← hcent, card_map_of_injective (MulAut.conj c₀⁻¹).injective,
        ← CTUC_Suz_four_exact_involution_centralizers.2.2.2.2.2.2.2.2.2.2.1 0 (by norm_num) |>.2]
      exact CTUC_Suz_four_exact_involution_centralizers.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hCle : suzM ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin 1782))) ≤
        suzM ⊓ centralizer {suzE0e} :=
      inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr hmemE'))
    set σ := permOfArr 1782 σa with hσ
    have hσC : σ ∈ suzM ⊓ centralizer {suzE0e} :=
      mem_inf.mpr ⟨mem_suzM_of hσM, mem_centralizer_singleton_iff.mpr hσ0⟩
    have hσE : σ ∉ suzM ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin 1782))) := by
      intro h1
      exact hσ1 (mem_centralizer_iff.mp (mem_inf.mp h1).2 _ hmemE1).symm
    have hcardCE : Nat.card (suzM ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin 1782))) :
        Subgroup (Equiv.Perm (Fin 1782))) ≤ 80640 := by
      have hdvd := card_dvd_of_le hCle
      rw [hcardC] at hdvd
      have hne : Nat.card (suzM ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin 1782))) :
          Subgroup (Equiv.Perm (Fin 1782))) ≠ 161280 := by
        intro h1
        have := eq_of_le_of_card_ge hCle (by rw [h1, hcardC])
        rw [this] at hσE
        exact hσE hσC
      obtain ⟨k, hk⟩ := hdvd
      rcases k with _ | _ | k
      · omega
      · omega
      · nlinarith
    have hHC : E₀ ⊔ L = suzM ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin 1782))) := by
      refine eq_of_le_of_card_ge ?_ (by rw [hcardH]; exact hcardCE)
      refine sup_le (le_inf hEM ?_) (le_inf hLM ?_)
      · intro y hy
        rw [mem_centralizer_iff]
        intro z hz
        exact hEab z hz y hy
      · intro y hy
        rw [mem_centralizer_iff]
        intro z hz
        exact (hLE y hy z hz).symm
    have hder : ⁅suzM ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin 1782))),
        suzM ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin 1782)))⁆ ≤ L := by
      rw [← hHC]
      simp only [hE₀, suzE0Sub, hLdef]
      rw [← Subgroup.closure_union]
      refine commutator_closure_le ?_ ?_
      · rintro w (hw | hw) n hn
        · have hc := hLE n hn w (subset_closure hw)
          refine ⟨?_, ?_⟩
          · rw [← hc, mul_inv_cancel_right]
            exact hn
          · have e1 : w⁻¹ * n * w = n := by
              rw [mul_assoc, hc, inv_mul_cancel_left]
            rw [e1]
            exact hn
        · exact ⟨L.mul_mem (L.mul_mem (subset_closure hw) hn) (L.inv_mem (subset_closure hw)),
            L.mul_mem (L.mul_mem (L.inv_mem (subset_closure hw)) hn) (subset_closure hw)⟩
      · rintro w (hw | hw) w' (hw' | hw')
        · rw [commutatorElement_eq_one_iff_mul_comm.mpr
            (hEab w (subset_closure hw) w' (subset_closure hw'))]
          exact one_mem L
        · rw [commutatorElement_eq_one_iff_mul_comm.mpr
            (hLE w' (subset_closure hw') w (subset_closure hw)).symm]
          exact one_mem L
        · rw [commutatorElement_eq_one_iff_mul_comm.mpr
            (hLE w (subset_closure hw) w' (subset_closure hw'))]
          exact one_mem L
        · exact commElem_mem (subset_closure hw) (subset_closure hw')
    intro z hz hz2 hz1 hQ
    exact hLinv z (hder hz) hz2 hz1 hQ

end CFSG.ComponentClassification.RankTwoSporadic.Suz
