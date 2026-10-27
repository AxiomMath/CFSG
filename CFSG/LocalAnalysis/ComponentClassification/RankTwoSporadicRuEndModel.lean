module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuEndK
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRu
public import CFSG.Certificates.Kernel.SporSch.SylowLab

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Ru

open Subgroup CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Fischer CFSG.KS.SylowLab
open CFSG.ComponentClassification.RankTwoSporadic.Endgame
open scoped commutatorElement

theorem fpf_conj (g σ : Equiv.Perm (Fin 4060)) (h : ∀ p, σ p ≠ p) :
    ∀ p, (g * σ * g⁻¹) p ≠ p := by
  intro p hp
  apply h (g⁻¹ p)
  have := congrArg (fun q => g⁻¹ q) hp
  simpa [Equiv.Perm.mul_apply] using this

theorem ruA0_eq : ruA0 = ruEndE 0 := by
  have e : ruE0[0]! = ruA0A := by simp [ruE0]
  rw [ruEndE, e, ruA0A, ruA0]

theorem permsA_ruE0 : permsA 4060 ruE0 = {ruEndE 0, ruEndE 1} := by
  ext g
  simp only [permsA, Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hs : ruE0.size = 2 := rfl
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [hs] at hk
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by rw [hs]; norm_num, rfl⟩
    · exact ⟨1, by rw [hs]; norm_num, rfl⟩

theorem ruE0Sub_eq : ruE0Sub = closure {ruEndE 0, ruEndE 1} := by
  rw [ruE0Sub, permsA_ruE0]

theorem ruA0_mem_ruE0Sub : ruA0 ∈ ruE0Sub := by
  rw [ruE0Sub_eq, ruA0_eq]
  exact subset_closure (Set.mem_insert _ _)

theorem mem_ruP_of
    {a : Array ℕ} (h : ruInPA a) : permOfArr 4060 a ∈ ruP :=
  (ruInP_iff a _ (rep_permOfArr h.1).1).1 h.2

theorem sig_comm : ∀ i < 3, ∀ j < 3, ∀ a < 5,
    ruEndSig i (ruEndSig j a) = ruEndSig j (ruEndSig i a) := by decide

theorem sig_inj : ∀ i < 3, ∀ a < 5, ∀ b < 5, ruEndSig i a = ruEndSig i b → a = b := by decide

theorem lab_derived {lab : Fin 4060 → ℕ} {ι : Type*} (gens : ι → Equiv.Perm (Fin 4060))
    (σ : ι → ℕ → ℕ) (hlt : ∀ p, lab p < 5) (hsig : ∀ i p, lab (gens i p) = σ i (lab p))
    (hinj : ∀ i, ∀ a < 5, ∀ b < 5, σ i a = σ i b → a = b)
    (hcomm : ∀ i j, ∀ a < 5, σ i (σ j a) = σ j (σ i a)) :
    closure (Set.range gens) ≤ normalizer (labStab lab : Set (Equiv.Perm (Fin 4060))) ∧
      ⁅closure (Set.range gens), closure (Set.range gens)⁆ ≤ labStab lab := by
  have hpres : ∀ i, ∀ u v, lab u = lab v → lab (gens i u) = lab (gens i v) :=
    fun i u v huv => by rw [hsig, hsig, huv]
  have hpresi : ∀ i, ∀ u v, lab u = lab v → lab ((gens i)⁻¹ u) = lab ((gens i)⁻¹ v) :=
    fun i u v huv => by
      refine hinj i _ (hlt _) _ (hlt _) ?_
      rw [← hsig, ← hsig]
      simpa using huv
  refine ⟨?_, commutator_closure_le ?_ ?_⟩
  · rw [closure_le]
    rintro _ ⟨i, rfl⟩
    exact mem_normalizer_labStab (hpres i) (hpresi i)
  · rintro _ ⟨i, rfl⟩ n hn
    refine ⟨conj_mem_labStab (hpres i) hn, ?_⟩
    have := conj_mem_labStab (hpresi i) hn
    simpa using this
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    rw [mem_labStab]
    intro p
    rw [commutatorElement_def]
    simp only [Equiv.Perm.mul_apply]
    have hq : lab p = σ j (lab ((gens j)⁻¹ p)) := by
      rw [← hsig]
      simp
    have hr : lab ((gens j)⁻¹ p) = σ i (lab ((gens i)⁻¹ ((gens j)⁻¹ p))) := by
      rw [← hsig]
      simp
    rw [hsig, hsig, hq, hr, hcomm i j _ (hlt _)]

theorem ruL_eq_closure :
    ruL = closure (Set.range fun i : Fin 3 => ruLStrong i) := by
  have hgens : {g | g ∈ ruLGens} = Set.range fun i : Fin 3 => ruLStrong i := by
    ext g
    rw [← ruChainL_original, show ruChainL.original.toList = (List.range 3).map fun i =>
      permOfArr 4060 (ruField4060 5)[i]! from ofArrays_original_toList]
    simp only [Set.mem_ofPred_eq, List.mem_map, List.mem_range, Set.mem_range, ruLStrong]
    exact ⟨fun ⟨i, hi, e⟩ => ⟨⟨i, hi⟩, e⟩, fun ⟨i, e⟩ => ⟨i, i.2, e⟩⟩
  rw [ruL, hgens]

set_option maxRecDepth 100000 in
theorem ruEndFacts_of_K
    (h : RuEndFactsK) : EndFacts ruP ruP ruE0Sub ruA0 (fun σ => ∀ p, σ p ≠ p) := by
  obtain ⟨he_mem, he_sq, he_comm, he_fpf, ⟨b, x, hb, hx, hbc, hbn, hxc, htree⟩,
    ⟨lab, hlt, hsig, s, hs, hcard, hfix⟩⟩ := h
  have hE := ruE0Sub_eq
  have hcases : ∀ e ∈ ruE0Sub, e = 1 ∨ e = ruEndE 0 ∨ e = ruEndE 1 ∨ e = ruEndE 0 * ruEndE 1 :=
    fun e he => mem_closure_pair (he_sq 0 (by norm_num)) (he_sq 1 (by norm_num)) he_comm
      (hE ▸ he)
  set bb := permOfArr 4060 b with hbb
  have hmem0 := ruA0_mem_ruE0Sub
  rw [ruA0_eq] at hmem0 ⊢
  refine ⟨?_, hmem0, ?_, fun g _ y hy => fpf_conj g y hy, ⟨bb, mem_ruP_of hb, ?_, ?_,
    fun i => permOfArr 4060 (x i), fun i => ⟨mem_ruP_of (hx i), ?_⟩, htree⟩, ?_⟩
  ·
    rw [hE, closure_le]
    rintro _ (rfl | rfl)
    · exact mem_ruP_of (he_mem 0 (by norm_num))
    · exact mem_ruP_of (he_mem 1 (by norm_num))
  ·
    intro e he he1 p
    rcases hcases e he with rfl | rfl | rfl | rfl
    · exact absurd rfl he1
    · exact (he_fpf p).1
    · exact (he_fpf p).2.1
    · exact (he_fpf p).2.2
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
    apply hbn
    rcases hcases _ hmem with h | h | h | h <;> rw [h] <;> simp
  ·
    intro e he
    rw [hE] at he
    have hle : closure ({ruEndE 0, ruEndE 1} : Set (Equiv.Perm (Fin 4060))) ≤
        centralizer {permOfArr 4060 (x i)} := by
      rw [closure_le]
      rintro _ (rfl | rfl) <;> rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      · exact (hxc i 0 (by norm_num)).symm
      · exact (hxc i 1 (by norm_num)).symm
    exact (mem_centralizer_singleton_iff.1 (hle he)).symm
  ·
    intro z hz hz2 hz1 hQ
    have hle : ruP ⊓ centralizer (ruE0Sub : Set (Equiv.Perm (Fin 4060))) ≤
        ruP ⊓ centralizer {ruA0} :=
      inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr ruA0_mem_ruE0Sub))
    have hzL' := commutator_mono hle hle hz
    rw [ruCentralizer_a] at hzL'
    have hL := ruL_eq_closure
    obtain ⟨hLN, hder⟩ := lab_derived (fun i : Fin 3 => ruLStrong i) (fun i : Fin 3 => ruEndSig i)
      hlt (fun i p => hsig i i.2 p) (fun i => sig_inj i i.2) (fun i j => sig_comm i i.2 j j.2)
    rw [← hL] at hLN hder
    have hLL : ⁅ruL, ruL⁆ ≤ ruL := commutator_le.2 fun a ha c hc => by
      rw [commutatorElement_def]
      exact ruL.mul_mem (ruL.mul_mem (ruL.mul_mem ha hc) (ruL.inv_mem ha)) (ruL.inv_mem hc)
    have hSL : closure (permsA 4060 s) ≤ ruL := by
      rw [closure_le]
      rintro _ ⟨k, hk, rfl⟩
      rw [SetLike.mem_coe, ← ruCentralizer_a]
      refine ⟨mem_ruP_of (hs k hk).1, mem_centralizer_singleton_iff.2 ?_⟩
      rw [ruA0_eq]
      exact (hs k hk).2
    obtain ⟨g, hgL, hgS⟩ := exists_conj_mem_of_card hSL Nat.prime_two
      (hcard.trans (by norm_num : (256 : ℕ) = 2 ^ 8)) (card_ruL.trans (by norm_num :
        (116480 : ℕ) = 2 ^ 8 * 455)) (by norm_num) (hLL hzL') hz2
    have hsK : g⁻¹ * z * g ∈ labStab lab := by
      have hgi : g⁻¹ ∈ normalizer (labStab lab : Set (Equiv.Perm (Fin 4060))) :=
        inv_mem (hLN hgL)
      have := (mem_normalizer_iff.1 hgi z).1 (hder hzL')
      simpa using this
    have hs2 : (g⁻¹ * z * g) ^ 2 = 1 := by
      have hzz : z * z = 1 := by rw [← sq]; exact hz2
      rw [sq]
      calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by
            simp only [mul_assoc, mul_inv_cancel_left]
        _ = 1 := by rw [hzz, mul_one, inv_mul_cancel]
    obtain ⟨p, hp⟩ := hfix _ hgS hs2 (mem_labStab.1 hsK)
    apply hQ (g p)
    have := congrArg g hp
    simpa [Equiv.Perm.mul_apply] using this

end CFSG.ComponentClassification.RankTwoSporadic.Ru
