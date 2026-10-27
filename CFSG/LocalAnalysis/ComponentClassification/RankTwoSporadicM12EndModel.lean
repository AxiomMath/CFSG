module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12EndTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12EndGame
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12EndData

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M12

open Subgroup CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.RankTwoSporadic.Endgame CFSG.RankThree.PartOne
open scoped commutatorElement

theorem fpf_of_m12FpfA {t : Array ℕ} {σ : Equiv.Perm (Fin 24)} (ht : Rep 24 t σ)
    (h : m12FpfA t = true) : ∀ p, σ p ≠ p := by
  intro p hp
  have h1 := allLt_spec h p.2
  rw [bne_iff_ne, ht p, hp] at h1
  exact h1 rfl

theorem exists_fix_of_m12FpfA {t : Array ℕ} {σ : Equiv.Perm (Fin 24)} (ht : Rep 24 t σ)
    (h : m12FpfA t = false) : ∃ p, σ p = p := by
  by_contra hne
  push Not at hne
  have : m12FpfA t = true := by
    rw [m12FpfA, allLt_iff]
    intro i hi
    rw [bne_iff_ne, ht.apply hi]
    intro h1
    exact hne ⟨i, hi⟩ (Fin.ext h1)
  rw [this] at h
  exact Bool.noConfusion h

theorem fpf_conj24 (g σ : Equiv.Perm (Fin 24)) (h : ∀ p, σ p ≠ p) :
    ∀ p, (g * σ * g⁻¹) p ≠ p := by
  intro p hp
  apply h (g⁻¹ p)
  have := congrArg (fun q => g⁻¹ q) hp
  simpa [Equiv.Perm.mul_apply] using this

theorem rep_m12EndZ : Rep 24 m12EndZ (blockHom (permZ, permZ)) := by
  intro x
  revert x
  decide

theorem card_centralizerIn_z :
    Nat.card (blockGroup ⊓ centralizer {blockHom (permZ, permZ)} :
      Subgroup (Equiv.Perm (Fin 24))) = 240 := by
  have h := card_centralizerIn_blockGroup elemZ
  rw [m12EquivD_elemZ] at h
  rw [← card_centralizerIn_permZ]
  exact h

theorem m12_getElem!_mem_toList {c : ArrCert} {i : ℕ} (hi : i < c.pts.size) :
    c.pts[i]! ∈ c.pts.toList := by
  rw [getElem!_pos c.pts i hi]
  exact Array.getElem_mem_toList hi

theorem m12_centralizer_facts
    {S : Array (Array ℕ)} {Wd : Array (List ℤ)} (hk : 2 ≤ S.size)
    (hch : caseChainOK2P 24 S m12BaseArr Wd m12A1Arr m12B1Arr = true)
    {e0 : Array (Array ℕ)} {a0 : Array ℕ} {xs gL : Array (Array ℕ)} {σa c0 : Array ℕ}
    (h : m12EndCheck S e0 a0 xs gL σa c0 m12EndZ = true) :
    Nat.card (blockGroup ⊓ centralizer (closure (permsA 24 e0) : Set (Equiv.Perm (Fin 24))) :
      Subgroup (Equiv.Perm (Fin 24))) ≤ 120 ∧
    ⁅blockGroup ⊓ centralizer (closure (permsA 24 e0) : Set (Equiv.Perm (Fin 24))),
      blockGroup ⊓ centralizer (closure (permsA 24 e0) : Set (Equiv.Perm (Fin 24)))⁆ ≤
      closure (permsA 24 gL) := by
  simp only [m12EndCheck, m12EndE0OK, m12EndConjOK, m12EndDerOK, Bool.and_eq_true,
    Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hsz, hcE⟩, hE4⟩, hcom0⟩, hfpf⟩, ht2⟩, ht0P⟩,
    ⟨⟨⟨⟨ha0v, ha0P⟩, hcomm⟩, hnot⟩, ⟨hxs, htree⟩⟩⟩,
    ⟨⟨⟨⟨⟨hcL, hL⟩, hLgen⟩, hLt⟩, hinv⟩, ⟨⟨⟨⟨⟨⟨hσv, hσP⟩, hσt⟩, hσ1⟩, hc0v⟩, hc0P⟩, hc0e⟩⟩⟩ := h
  have hinP := m12InP_iff hk hch
  have hrep : ∀ k < e0.size, Rep 24 e0[k]! (permOfArr 24 e0[k]!) := fun k hk' =>
    rep_of_validA (enumOK_gens_valid hcE hk')
  have he0 : Rep 24 e0[0]! (permOfArr 24 e0[0]!) := hrep 0 (by rw [hsz]; norm_num)
  have he1 : Rep 24 e0[1]! (permOfArr 24 e0[1]!) := hrep 1 (by rw [hsz]; norm_num)
  set E₀ := closure (permsA 24 e0) with hE₀
  set t₀ := permOfArr 24 (m12T0 e0) with ht₀
  have ht₀e : t₀ = permOfArr 24 e0[0]! * permOfArr 24 e0[1]! :=
    permOfArr_eq_of_rep (rep_compA he0 he1)
  have hrt : Rep 24 (m12T0 e0) t₀ := by
    rw [ht₀e]
    exact rep_compA he0 he1
  have hmemE : ∀ k < e0.size, permOfArr 24 e0[k]! ∈ E₀ := fun k hk' =>
    subset_closure ⟨k, hk', rfl⟩
  have ht₀E : t₀ ∈ E₀ := by
    rw [ht₀e]
    exact E₀.mul_mem (hmemE 0 (by rw [hsz]; norm_num)) (hmemE 1 (by rw [hsz]; norm_num))
  have ht₀D : t₀ ∈ blockGroup := (hinP _ _ hrt).mp ht0P
  set a₀ := permOfArr 24 a0 with ha₀
  have hra : Rep 24 a0 a₀ := rep_of_validA ha0v
  set f := (MulAut.conj a₀⁻¹).toMonoidHom with hf
  have hfa : ∀ g, f g = a₀⁻¹ * g * a₀ := fun g => by simp [hf]
  have hconjE : ∀ e' ∈ E₀, a₀⁻¹ * e' * a₀ ∈ closure (f '' permsA 24 e0) := by
    intro e' he'
    have h1 := mem_map_of_mem f he'
    rw [hE₀, MonoidHom.map_closure] at h1
    rwa [hfa] at h1
  have hEab : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := by
    intro x hx y hy
    refine commute_of_mem_closure ?_ hx hy
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    exact eq_of_eqA (rep_compA (hrep i hi) (hrep j hj)) (rep_compA (hrep j hj) (hrep i hi))
      (allLt_spec (allLt_spec hcom0 hi) hj)
  have hnotE : a₀⁻¹ * t₀ * a₀ ∉ E₀ := by
    intro hmem
    obtain ⟨i, hi, hri⟩ := enumOK_exists_rep m12PS_lt hcE hmem
    have h1 : m12InEnum (enumBfs 24 e0 m12PS m12Fuel) (conjInvA 24 a0 (m12T0 e0)) = true := by
      rw [m12InEnum, List.any_eq_true]
      exact ⟨_, m12_getElem!_mem_toList hi, (eqA_iff (rep_conjInvA ha0v hrt) hri).mpr rfl⟩
    rw [h1] at hnot
    exact Bool.noConfusion hnot
  set L := closure (permsA 24 gL) with hLdef
  have hrg : ∀ j < gL.size, Rep 24 gL[j]! (permOfArr 24 gL[j]!) := fun j hj =>
    rep_of_validA (enumOK_gens_valid hcL hj)
  have hcardL : Nat.card L = 60 := by
    rw [hLdef, (enumOK_spec m12PS_lt hcL).2.1, hL]
  have hLE : ∀ x ∈ L, ∀ y ∈ E₀, x * y = y * x := by
    intro x hx y hy
    refine commute_of_mem_closure ?_ hx hy
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    have h1 := allLt_spec hLgen hi
    rw [Bool.and_eq_true] at h1
    exact eq_of_eqA (rep_compA (hrg i hi) (hrep j hj)) (rep_compA (hrep j hj) (hrg i hi))
      (allLt_spec h1.2 hj)
  have hLD : L ≤ blockGroup := by
    rw [hLdef, closure_le]
    rintro _ ⟨k, hk', rfl⟩
    have h1 := allLt_spec hLgen hk'
    rw [Bool.and_eq_true] at h1
    exact (hinP _ _ (hrg k hk')).mp h1.1
  have hrtL : t₀ ∉ L := by
    intro hmem
    obtain ⟨i, hi, hri⟩ := enumOK_exists_rep m12PS_lt hcL hmem
    have h1 : m12InEnum (enumBfs 24 gL m12PS m12Fuel) (m12T0 e0) = true := by
      rw [m12InEnum, List.any_eq_true]
      exact ⟨_, m12_getElem!_mem_toList hi, (eqA_iff hrt hri).mpr rfl⟩
    rw [h1] at hLt
    exact Bool.noConfusion hLt
  set H := closure (insert t₀ (permsA 24 gL)) with hH
  have hLH : L ≤ H := closure_mono (Set.subset_insert _ _)
  have ht₀H : t₀ ∈ H := subset_closure (Set.mem_insert _ _)
  have hcardH : 120 ≤ Nat.card H := by
    obtain ⟨k, hk'⟩ := card_dvd_of_le hLH
    have hne : Nat.card L ≠ Nat.card H := by
      intro heq
      exact hrtL ((eq_of_le_of_card_ge hLH heq.symm.le).symm ▸ ht₀H)
    rw [hcardL] at hk' hne
    have hpos : 0 < Nat.card H := Nat.card_pos
    rcases k with _ | _ | k
    · omega
    · omega
    · omega
  set c₀ := permOfArr 24 c0 with hc₀
  have hrc : Rep 24 c0 c₀ := rep_of_validA hc0v
  have hc₀D : c₀ ∈ blockGroup := (hinP _ _ hrc).mp hc0P
  have hc₀t : c₀ * t₀ * c₀⁻¹ = blockHom (permZ, permZ) :=
    eq_of_eqA (rep_conjA hc0v hrt) rep_m12EndZ hc0e
  have hcent : (blockGroup ⊓ centralizer {blockHom (permZ, permZ)} :
      Subgroup (Equiv.Perm (Fin 24))).map (MulAut.conj c₀⁻¹).toMonoidHom =
      blockGroup ⊓ centralizer {t₀} := by
    ext x
    simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, mem_inf,
      mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, ⟨hyD, hyz⟩, rfl⟩
      refine ⟨blockGroup.mul_mem (blockGroup.mul_mem (blockGroup.inv_mem hc₀D) hyD) hc₀D, ?_⟩
      have he' : t₀ = c₀⁻¹ * blockHom (permZ, permZ) * c₀ := by rw [← hc₀t]; group
      rw [he']
      calc c₀⁻¹ * y * c₀ * (c₀⁻¹ * blockHom (permZ, permZ) * c₀)
          = c₀⁻¹ * (y * blockHom (permZ, permZ)) * c₀ := by group
        _ = c₀⁻¹ * (blockHom (permZ, permZ) * y) * c₀ := by rw [hyz]
        _ = c₀⁻¹ * blockHom (permZ, permZ) * c₀ * (c₀⁻¹ * y * c₀) := by group
    · rintro ⟨hxD, hxt⟩
      refine ⟨c₀ * x * c₀⁻¹,
        ⟨blockGroup.mul_mem (blockGroup.mul_mem hc₀D hxD) (blockGroup.inv_mem hc₀D), ?_⟩,
        by group⟩
      rw [← hc₀t]
      calc c₀ * x * c₀⁻¹ * (c₀ * t₀ * c₀⁻¹) = c₀ * (x * t₀) * c₀⁻¹ := by group
        _ = c₀ * (t₀ * x) * c₀⁻¹ := by rw [hxt]
        _ = c₀ * t₀ * c₀⁻¹ * (c₀ * x * c₀⁻¹) := by group
  have hcardC : Nat.card (blockGroup ⊓ centralizer {t₀} : Subgroup (Equiv.Perm (Fin 24))) =
      240 := by
    rw [← hcent, card_map_of_injective (MulAut.conj c₀⁻¹).injective, card_centralizerIn_z]
  have hCle : blockGroup ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin 24))) ≤
      blockGroup ⊓ centralizer {t₀} :=
    inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr ht₀E))
  set σ := permOfArr 24 σa with hσ
  have hrσ : Rep 24 σa σ := rep_of_validA hσv
  have hσC : σ ∈ blockGroup ⊓ centralizer {t₀} :=
    mem_inf.mpr ⟨(hinP _ _ hrσ).mp hσP, mem_centralizer_singleton_iff.mpr
      (eq_of_eqA (rep_compA hrσ hrt) (rep_compA hrt hrσ) hσt)⟩
  have hσE : σ ∉ blockGroup ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin 24))) := by
    intro h1
    have h2 := mem_centralizer_iff.mp (mem_inf.mp h1).2 _
      (hmemE 0 (by rw [hsz]; norm_num) : permOfArr 24 e0[0]! ∈ (E₀ : Set (Equiv.Perm (Fin 24))))
    have h3 : m12CommA σa e0[0]! = true :=
      (eqA_iff (rep_compA hrσ he0) (rep_compA he0 hrσ)).mpr h2.symm
    rw [h3] at hσ1
    exact Bool.noConfusion hσ1
  have hcardCE : Nat.card (blockGroup ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin 24))) :
      Subgroup (Equiv.Perm (Fin 24))) ≤ 120 := by
    have hdvd := card_dvd_of_le hCle
    rw [hcardC] at hdvd
    have hne : Nat.card (blockGroup ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin 24))) :
        Subgroup (Equiv.Perm (Fin 24))) ≠ 240 := by
      intro h1
      have := eq_of_le_of_card_ge hCle (by rw [h1, hcardC])
      rw [this] at hσE
      exact hσE hσC
    obtain ⟨k, hk'⟩ := hdvd
    rcases k with _ | _ | k
    · omega
    · omega
    · nlinarith
  have hHC : H = blockGroup ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin 24))) := by
    refine eq_of_le_of_card_ge ?_ (hcardCE.trans hcardH)
    rw [hH, closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]
      exact mem_inf.mpr ⟨ht₀D, mem_centralizer_iff.mpr fun y hy => hEab y hy t₀ ht₀E⟩
    · have hxL : x ∈ L := subset_closure hx
      exact mem_inf.mpr ⟨hLD hxL, mem_centralizer_iff.mpr fun y hy => (hLE x hxL y hy).symm⟩
  have hder : ⁅blockGroup ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin 24))),
      blockGroup ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin 24)))⁆ ≤ L := by
    rw [← hHC, hH]
    refine commutator_closure_le ?_ ?_
    · rintro s (rfl | hs) n hn
      · have hc := hLE n hn _ ht₀E
        refine ⟨?_, ?_⟩
        · rw [← hc, mul_inv_cancel_right]
          exact hn
        · have e1 : t₀⁻¹ * n * t₀ = n := by
            rw [mul_assoc, hc, inv_mul_cancel_left]
          rw [e1]
          exact hn
      · exact ⟨L.mul_mem (L.mul_mem (subset_closure hs) hn) (L.inv_mem (subset_closure hs)),
          L.mul_mem (L.mul_mem (L.inv_mem (subset_closure hs)) hn) (subset_closure hs)⟩
    · rintro s (rfl | hs) s' (rfl | hs')
      · rw [commutatorElement_self]
        exact one_mem L
      · rw [commutatorElement_eq_one_iff_mul_comm.mpr (hLE s' (subset_closure hs') _ ht₀E).symm]
        exact one_mem L
      · rw [commutatorElement_eq_one_iff_mul_comm.mpr (hLE s (subset_closure hs) _ ht₀E)]
        exact one_mem L
      · exact commElem_mem (subset_closure hs) (subset_closure hs')
  exact ⟨hcardCE, hder⟩

theorem m12EndFacts_of_check
    {S : Array (Array ℕ)} {Wd : Array (List ℤ)} (hk : 2 ≤ S.size)
    (hch : caseChainOK2P 24 S m12BaseArr Wd m12A1Arr m12B1Arr = true)
    {e0 : Array (Array ℕ)} {a0 : Array ℕ} {xs gL : Array (Array ℕ)} {σa c0 : Array ℕ}
    (h : m12EndCheck S e0 a0 xs gL σa c0 m12EndZ = true) :
    EndFactsOut autModel blockGroup (closure (permsA 24 e0)) (permOfArr 24 (m12T0 e0))
      (fun σ => ∀ p, σ p ≠ p) := by
  have hcopy := h
  simp only [m12EndCheck, m12EndE0OK, m12EndConjOK, m12EndDerOK, Bool.and_eq_true,
    Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hsz, hcE⟩, hE4⟩, hcom0⟩, hfpf⟩, ht2⟩, ht0P⟩,
    ⟨⟨⟨⟨ha0v, ha0P⟩, hcomm⟩, hnot⟩, ⟨hxs, htree⟩⟩⟩,
    ⟨⟨⟨⟨⟨hcL, hL⟩, hLgen⟩, hLt⟩, hinv⟩, ⟨⟨⟨⟨⟨⟨hσv, hσP⟩, hσt⟩, hσ1⟩, hc0v⟩, hc0P⟩, hc0e⟩⟩⟩ := h
  have hinP := m12InP_iff hk hch
  have hrep : ∀ k < e0.size, Rep 24 e0[k]! (permOfArr 24 e0[k]!) := fun k hk' =>
    rep_of_validA (enumOK_gens_valid hcE hk')
  have he0 : Rep 24 e0[0]! (permOfArr 24 e0[0]!) := hrep 0 (by rw [hsz]; norm_num)
  have he1 : Rep 24 e0[1]! (permOfArr 24 e0[1]!) := hrep 1 (by rw [hsz]; norm_num)
  set E₀ := closure (permsA 24 e0) with hE₀
  set t₀ := permOfArr 24 (m12T0 e0) with ht₀
  have ht₀e : t₀ = permOfArr 24 e0[0]! * permOfArr 24 e0[1]! :=
    permOfArr_eq_of_rep (rep_compA he0 he1)
  have hrt : Rep 24 (m12T0 e0) t₀ := by
    rw [ht₀e]
    exact rep_compA he0 he1
  have hmemE : ∀ k < e0.size, permOfArr 24 e0[k]! ∈ E₀ := fun k hk' =>
    subset_closure ⟨k, hk', rfl⟩
  have ht₀E : t₀ ∈ E₀ := by
    rw [ht₀e]
    exact E₀.mul_mem (hmemE 0 (by rw [hsz]; norm_num)) (hmemE 1 (by rw [hsz]; norm_num))
  have ht₀D : t₀ ∈ blockGroup := (hinP _ _ hrt).mp ht0P
  set a₀ := permOfArr 24 a0 with ha₀
  have hra : Rep 24 a0 a₀ := rep_of_validA ha0v
  set f := (MulAut.conj a₀⁻¹).toMonoidHom with hf
  have hfa : ∀ g, f g = a₀⁻¹ * g * a₀ := fun g => by simp [hf]
  have hconjE : ∀ e' ∈ E₀, a₀⁻¹ * e' * a₀ ∈ closure (f '' permsA 24 e0) := by
    intro e' he'
    have h1 := mem_map_of_mem f he'
    rw [hE₀, MonoidHom.map_closure] at h1
    rwa [hfa] at h1
  have hEab : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := by
    intro x hx y hy
    refine commute_of_mem_closure ?_ hx hy
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    exact eq_of_eqA (rep_compA (hrep i hi) (hrep j hj)) (rep_compA (hrep j hj) (hrep i hi))
      (allLt_spec (allLt_spec hcom0 hi) hj)
  have hnotE : a₀⁻¹ * t₀ * a₀ ∉ E₀ := by
    intro hmem
    obtain ⟨i, hi, hri⟩ := enumOK_exists_rep m12PS_lt hcE hmem
    have h1 : m12InEnum (enumBfs 24 e0 m12PS m12Fuel) (conjInvA 24 a0 (m12T0 e0)) = true := by
      rw [m12InEnum, List.any_eq_true]
      exact ⟨_, m12_getElem!_mem_toList hi, (eqA_iff (rep_conjInvA ha0v hrt) hri).mpr rfl⟩
    rw [h1] at hnot
    exact Bool.noConfusion hnot
  refine ⟨ht₀D, ht₀E, ?_, fun g _ x hx => fpf_conj24 g x hx, ⟨a₀, ?_, ?_, hnotE, ?_⟩, ?_⟩
  ·
    intro e hE he1'
    obtain ⟨i, hi, hri⟩ := enumOK_exists_rep m12PS_lt hcE hE
    have h1 := allLt_spec hfpf hi
    rw [Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · exact absurd (eq_of_eqA hri rep_idA h1) he1'
    · exact fpf_of_m12FpfA hri h1
  · exact (hinP _ _ hra).mp ha0P
  ·
    intro e hE e' hE'
    refine commute_of_mem_closure ?_ hE (hconjE e' hE')
    rintro _ ⟨i, hi, rfl⟩ _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    have h1 := allLt_spec (allLt_spec hcomm hi) hj
    rw [hfa]
    exact eq_of_eqA (rep_compA (hrep i hi) (rep_conjInvA ha0v (hrep j hj)))
      (rep_compA (rep_conjInvA ha0v (hrep j hj)) (hrep i hi)) h1
  ·
    simp only [m12TreeOK, Bool.and_eq_true, beq_iff_eq] at htree
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hsz8, hxv⟩, h0⟩, h1⟩, h2⟩, h3⟩, hm0⟩, hm1⟩, htop⟩ := htree
    have hrx : ∀ i : Fin 8, Rep 24 xs[(i : ℕ)]! (permOfArr 24 xs[(i : ℕ)]!) := fun i =>
      rep_of_validA (allLt_spec hxv i.2)
    refine ⟨fun i => permOfArr 24 xs[(i : ℕ)]!, fun i => ⟨?_, ?_⟩, ?_⟩
    · have := allLt_spec hxs (show (i : ℕ) < xs.size by rw [hsz8]; exact i.2)
      rw [Bool.and_eq_true] at this
      exact (hinP _ _ (hrx i)).mp this.1
    · intro e hE
      have hgen : ∀ g ∈ permsA 24 e0, permOfArr 24 xs[(i : ℕ)]! * g =
          g * permOfArr 24 xs[(i : ℕ)]! := by
        rintro _ ⟨j, hj, rfl⟩
        have := allLt_spec hxs (show (i : ℕ) < xs.size by rw [hsz8]; exact i.2)
        rw [Bool.and_eq_true] at this
        exact eq_of_eqA (rep_compA (hrx i) (hrep j hj)) (rep_compA (hrep j hj) (hrx i))
          (allLt_spec this.2 hj)
      exact (commute_of_mem_closure (S := permsA 24 e0)
        (T := {permOfArr 24 xs[(i : ℕ)]!}) (fun g hg _ ht => by
          rw [Set.mem_singleton_iff] at ht
          rw [ht]
          exact (hgen g hg).symm) hE (subset_closure rfl)).symm
    · have hv : ∀ i < 8, validA 24 xs[i]! = true := fun i hi => allLt_spec hxv hi
      have e0' := permOfArr_eq_of_rep (rep_commutatorA (hv 0 (by norm_num)) (hv 1 (by norm_num)))
      have e1' := permOfArr_eq_of_rep (rep_commutatorA (hv 2 (by norm_num)) (hv 3 (by norm_num)))
      have e2' := permOfArr_eq_of_rep (rep_commutatorA (hv 4 (by norm_num)) (hv 5 (by norm_num)))
      have e3' := permOfArr_eq_of_rep (rep_commutatorA (hv 6 (by norm_num)) (hv 7 (by norm_num)))
      have f0 := permOfArr_eq_of_rep (rep_commutatorA h0 h1)
      have f1 := permOfArr_eq_of_rep (rep_commutatorA h2 h3)
      have htgt : Rep 24 (compA 24 (m12T0 e0) (conjInvA 24 a0 (m12T0 e0)))
          (t₀ * (a₀⁻¹ * t₀ * a₀)) := rep_compA hrt (rep_conjInvA ha0v hrt)
      have := eq_of_eqA (rep_commutatorA hm0 hm1) htgt htop
      rw [f0, f1, e0', e1', e2', e3'] at this
      exact this
  ·
    have hder := (m12_centralizer_facts hk hch hcopy).2
    intro z hz hz2 hz1 hQ
    obtain ⟨i, hi, hri⟩ := enumOK_exists_rep m12PS_lt hcL (hder hz)
    have h1 := allLt_spec hinv hi
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h1
    rcases h1 with (h1 | h1) | h1
    · have : eqA 24 (compA 24 (enumBfs 24 gL m12PS m12Fuel).pts[i]!
          (enumBfs 24 gL m12PS m12Fuel).pts[i]!) (idA 24) = true :=
        (eqA_iff (rep_compA hri hri) rep_idA).mpr (by rw [← sq]; exact hz2)
      rw [this] at h1
      exact Bool.noConfusion h1
    · exact absurd (eq_of_eqA hri rep_idA h1) hz1
    · obtain ⟨p, hp⟩ := exists_fix_of_m12FpfA hri h1
      exact hQ p hp

end CFSG.ComponentClassification.RankTwoSporadic.M12
