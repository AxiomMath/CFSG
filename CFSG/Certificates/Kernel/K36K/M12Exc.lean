module

public import CFSG.Certificates.Kernel.K36K.ExcSound
public import CFSG.Certificates.Kernel.K36K.PlaneOK
public import CFSG.Certificates.Kernel.K36K.M12Fix

public section

namespace CFSG.KD.K36K

open CFSG.Blueprint CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MaxD2
  CFSG.KS.K36K CFSG.KD.CoreD2K CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UCK.Spor
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Certificates.K36Spor

theorem m12_ncard_cent_le {u : Equiv.Perm (Fin 12)}
    (hu : (Finset.univ.filter fun x : Fin 12 => u x = x).card = 3) :
    Set.ncard {k | k ∈ NativeSporadic.M12 ∧ k * u = u * k} ≤ 54 := by
  classical
  set F := Finset.univ.filter fun x : Fin 12 => u x = x with hFdef
  have hmemF : ∀ x, x ∈ F ↔ u x = x := fun x => by simp [hFdef]
  obtain ⟨f1, f2, f3, h12, h13, h23, hF⟩ := Finset.card_eq_three.1 hu
  have hFc : Fᶜ.card = 9 := by
    rw [Finset.card_compl, hu]
    rfl
  obtain ⟨x0, hx0⟩ : Fᶜ.Nonempty := Finset.card_pos.1 (by omega)
  have hx0F : x0 ∉ F := Finset.mem_compl.1 hx0
  have hx0u : u x0 ≠ x0 := fun e => hx0F ((hmemF x0).2 e)
  have hux0F : u x0 ∉ F := fun h => hx0u (u.injective ((hmemF _).1 h))
  have hcomm : ∀ k : Equiv.Perm (Fin 12), k * u = u * k → ∀ x, u (k x) = k (u x) :=
    fun k hk x => by
      have := congrArg (fun g : Equiv.Perm (Fin 12) => g x) hk
      simp only [Equiv.Perm.mul_apply] at this
      exact this.symm
  have hfixk : ∀ k : Equiv.Perm (Fin 12), k * u = u * k → ∀ x, (u (k x) = k x ↔ u x = x) :=
    fun k hk x => by
      rw [hcomm k hk x]
      exact k.injective.eq_iff
  have hf1 : f1 ∈ F := by rw [hF]; simp
  have hf2 : f2 ∈ F := by rw [hF]; simp
  have hf3 : f3 ∈ F := by rw [hF]; simp
  set T : Finset ((Fin 12 × Fin 12) × Fin 12) := F.offDiag ×ˢ Fᶜ with hT
  have hTc : T.card = 54 := by
    rw [hT, Finset.card_product, Finset.offDiag_card, hu, hFc]
  rw [← hTc, ← Set.ncard_coe_finset T]
  refine Set.ncard_le_ncard_of_injOn (fun k => ((k f1, k f2), k x0)) ?_ ?_ (Set.toFinite _)
  · intro k hk
    obtain ⟨-, hk⟩ := hk
    rw [Finset.mem_coe, hT, Finset.mem_product, Finset.mem_offDiag, Finset.mem_compl]
    refine ⟨⟨(hmemF _).2 ((hfixk k hk f1).2 ((hmemF f1).1 hf1)),
      (hmemF _).2 ((hfixk k hk f2).2 ((hmemF f2).1 hf2)), fun e => h12 (k.injective e)⟩,
      fun h => hx0F ((hmemF x0).2 ((hfixk k hk x0).1 ((hmemF _).1 h)))⟩
  · rintro k ⟨hkM, hk⟩ k' ⟨hk'M, hk'⟩ e
    simp only [Prod.mk.injEq] at e
    obtain ⟨⟨e1, e2⟩, e0⟩ := e
    set d := k'⁻¹ * k with hd
    have hdM : d ∈ NativeSporadic.M12 := Subgroup.mul_mem _ (Subgroup.inv_mem _ hk'M) hkM
    have hdu : d * u = u * d := ((Commute.inv_left hk').mul_left hk).eq
    have hdx : ∀ x, k x = k' x → d x = x := fun x ex => by
      simp [hd, Equiv.Perm.mul_apply, ex]
    have d1 := hdx f1 e1
    have d2 := hdx f2 e2
    have d0 := hdx x0 e0
    have dux : d (u x0) = u x0 := by rw [← hcomm d hdu x0, d0]
    have d3 : d f3 = f3 := by
      have h3 : d f3 ∈ F := (hmemF _).2 ((hfixk d hdu f3).2 ((hmemF f3).1 hf3))
      rw [hF] at h3
      simp only [Finset.mem_insert, Finset.mem_singleton] at h3
      rcases h3 with h | h | h
      · exact absurd (d.injective (h.trans d1.symm)) (Ne.symm h13)
      · exact absurd (d.injective (h.trans d2.symm)) (Ne.symm h23)
      · exact h
    rw [hF] at hx0F hux0F
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx0F hux0F
    obtain ⟨n1, n2, n3⟩ := hx0F
    obtain ⟨m1, m2, m3⟩ := hux0F
    have hO : 5 ≤ ({f1, f2, f3, x0, u x0} : Finset (Fin 12)).card := by
      rw [Finset.card_insert_of_notMem (by simp [h12, h13, Ne.symm n1, Ne.symm m1]),
        Finset.card_insert_of_notMem (by simp [h23, Ne.symm n2, Ne.symm m2]),
        Finset.card_insert_of_notMem (by simp [Ne.symm n3, Ne.symm m3]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hx0u]), Finset.card_singleton]
    have hd1 : d = 1 := m12_eq_one_of_fix hdM hO fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact d1
      · exact d2
      · exact d3
      · exact d0
      · exact dux
    exact (inv_mul_eq_one.1 hd1).symm

variable {w : Nat}

theorem m12_exc_planeOK (hn : szOK 12 w = true) {S : SData}
    {X : Exc} {EG GP GPI CT CTI : ℕ → ℕ} {YT YTI : ℕ} {FT FYT : ℕ → ℕ}
    {T PL POS SRT SRI : ℕ → ℕ} {cnt cap len kk0 o0 : ℕ} {HW OW : List (List ℕ)} {OL : List ℕ}
    {e : ℕ → Equiv.Perm (Fin 12)} {a b : Equiv.Perm (Fin 12)}
    (hab : Subgroup.closure {a, b} = NativeSporadic.M12)
    (he : ∀ k < S.base.eW.length, PR 12 w (EG k) (e k))
    (hGP : allN 2 (fun j => permOK 12 w (mask w) (12 * w) (GP j) (GPI j)) = true)
    (ha : TabRep (unpack 12 w (GP 0)) a) (hb : TabRep (unpack 12 w (GP 1)) b)
    (hzP : PR 12 w (EG 0) (e 0)) (hvP : PR 12 w (EG (S.ys.getD X.idx 0)) (e (S.ys.getD X.idx 0)))
    (hzG : e 0 ∈ NativeSporadic.M12) (hvG : e (S.ys.getD X.idx 0) ∈ NativeSporadic.M12)
    (hz3 : e 0 ^ 3 = 1) (hv3 : e (S.ys.getD X.idx 0) ^ 3 = 1)
    (hzv : e 0 * e (S.ys.getD X.idx 0) = e (S.ys.getD X.idx 0) * e 0)
    (hexc : excWK 12 w S X EG GP GPI CT CTI YT YTI FT FYT = true)
    (hh : penumHdK (pidn 12 w) cnt cap T PL = true)
    (hsl : penumSlK 12 w (mask w) (12 * w) false CT CTI X.cW.length cnt T PL POS SRT SRI 0 len =
      true) (hlen : cnt ≤ len)
    (hN : excNK 12 w 3 54 (EG 0) (EG (S.ys.getD X.idx 0)) X.cW.length CT cnt T = true)
    (hfix3 : ∀ α < 3, ∀ β < 3, ¬(α = 0 ∧ β = 0) → (Finset.univ.filter fun x : Fin 12 =>
      pg w (mask w) (pcomp 12 w (mask w) (pw 12 w (EG 0) α) (pw 12 w (EG (S.ys.getD X.idx 0)) β))
        x = (x : ℕ)).card = 3)
    (hW : fixWK 12 w 2 FT kk0 o0 HW OL OW = true)
    (hO : 5 ≤ (Finset.univ.filter fun x : Fin 12 => (x : ℕ) ∈ OL).card)
    {A : Subgroup ↥NativeSporadic.M12}
    (hAY : ∀ x : ↥NativeSporadic.M12, x ∈ A ↔ (x : Equiv.Perm (Fin 12)) ∈
      Subgroup.closure ({e 0, e (S.ys.getD X.idx 0)} : Set (Equiv.Perm (Fin 12))))
    (hAe : IsElemAbelian 3 A) (hAc : Nat.card A = 3 ^ 2) : PlaneOK A := by
  classical
  set z := e 0 with hzdef
  set v := e (S.ys.getD X.idx 0) with hvdef
  set Y := Subgroup.closure ({z, v} : Set (Equiv.Perm (Fin 12))) with hYdef
  have hYG : Y ≤ NativeSporadic.M12 := by
    rw [hYdef, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hzG, hvG⟩
  obtain ⟨cs, y, f, f', -, hcP, hcs, hyG, hf, haC, hbC⟩ := exc_sound hn he hGP ha hb hexc
  rw [hab] at hcs hyG
  set c : ℕ → Equiv.Perm (Fin 12) := fun l => cs.getD l 1 with hcdef
  set N := Subgroup.closure {g | ∃ l < X.cW.length, c l = g} with hNdef
  obtain ⟨hsnd, hcomp, hinj⟩ := penum_facts hn hcP hh hsl hlen
  unfold excNK at hN
  obtain ⟨hnorm0, hN⟩ := band_e hN
  obtain ⟨hcent0, hcnt⟩ := band_e hN
  have hNnorm := normYK_sound hn hzP hvP hcP hnorm0
  have hNG : N ≤ NativeSporadic.M12 := by
    rw [hNdef, Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    change cs.getD l 1 ∈ NativeSporadic.M12
    by_cases hlc : l < cs.length
    · rw [List.getD_eq_getElem _ _ hlc]
      exact (hcs _ (List.getElem_mem hlc)).1
    · rw [List.getD_eq_default _ _ (by omega)]
      exact Subgroup.one_mem _
  have hCN : ∀ α < 3, ∀ β < 3, ¬(α = 0 ∧ β = 0) → ∀ k ∈ NativeSporadic.M12,
      k * (z ^ α * v ^ β) = (z ^ α * v ^ β) * k → k ∈ N := by
    intro α hα β hβ hne k hkG hk
    have huP := pr_mul (pr_pow hn hzP α) (pr_pow hn hvP β)
    have hfixu : (Finset.univ.filter fun x : Fin 12 => (z ^ α * v ^ β) x = x).card = 3 := by
      rw [← hfix3 α hα β hβ hne]
      congr 1
      refine Finset.filter_congr fun x _ => ?_
      rw [pr_pg huP x]
      exact Fin.val_inj.symm
    have hle := m12_ncard_cent_le hfixu
    have hx := PK.allN_iff.1 (PK.allN_iff.1 hcnt α hα) β hβ
    have hble : Nat.ble 54 (cntCK 12 w (pcomp 12 w (mask w) (pw 12 w (EG 0) α)
        (pw 12 w (EG (S.ys.getD X.idx 0)) β)) cnt T) = true := by
      cases hα0 : Nat.beq α 0 <;> cases hβ0 : Nat.beq β 0 <;> rw [hα0, hβ0] at hx
      · exact hx
      · exact hx
      · exact hx
      · exact absurd ⟨Nat.eq_of_beq_eq_true hα0, Nat.eq_of_beq_eq_true hβ0⟩ hne
    have hge := cntCK_sound huP hsnd hinj (Nat.le_of_ble_eq_true hble)
    have hsub : {k | k ∈ N ∧ k * (z ^ α * v ^ β) = (z ^ α * v ^ β) * k} ⊆
        {k | k ∈ NativeSporadic.M12 ∧ k * (z ^ α * v ^ β) = (z ^ α * v ^ β) * k} :=
      fun k hk => ⟨hNG hk.1, hk.2⟩
    have heq := Set.eq_of_subset_of_ncard_le hsub (hle.trans hge) (Set.toFinite _)
    have hk' : k ∈ {k | k ∈ N ∧ k * (z ^ α * v ^ β) = (z ^ α * v ^ β) * k} := by
      rw [heq]
      exact ⟨hkG, hk⟩
    exact hk'.1
  have hnorm : ∀ k ∈ NativeSporadic.M12, (∃ u ∈ Y, u ≠ 1 ∧ u * k = k * u) →
      ∀ y ∈ Y, k * y * k⁻¹ ∈ Y := by
    rintro k hkG ⟨u, hu, hu1, huk⟩ y' hy'
    obtain ⟨α, hα, β, hβ, rfl⟩ := exists_pow_mul_pow_of_mem (by norm_num) hzv hz3 hv3 hu
    have hne : ¬(α = 0 ∧ β = 0) := by
      rintro ⟨rfl, rfl⟩
      exact hu1 (by simp)
    have hkN := hCN α hα β hβ hne k hkG huk.symm
    exact (Subgroup.mem_normalizer_iff.1 (hNnorm hkN) y').1 hy'
  have hcent : ∀ k ∈ NativeSporadic.M12, (∀ y ∈ Y, k * y = y * k) → k ∈ Y := by
    intro k hkG hk
    have hkz := hk z (Subgroup.subset_closure (by simp))
    have hkv := hk v (Subgroup.subset_closure (by simp))
    have hkN := hCN 1 (by norm_num) 0 (by norm_num) (by simp) k hkG (by simpa using hkz)
    exact centYK_sound hn hzP hvP hcomp hcent0 k hkN hkz hkv
  have hcen : ∀ t ∈ NativeSporadic.M12, t * f 0 = f 0 * t → t * f 1 = f 1 * t → t = 1 := by
    intro t htG h0 h1
    refine m12_eq_one_of_fixWK (fun k hk => (hf k hk).2.2.2) hW hO htG fun k hk => ?_
    interval_cases k
    · exact h0
    · exact h1
  have hgen : NativeSporadic.M12 ≤ Subgroup.closure ({c | c ∈ cs} ∪ {y}) := by
    rw [← hab, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨haC, hbC⟩
  exact planeOK_of_exc_facts Nat.prime_three (by norm_num) hAY hYG hAe hAc hnorm hcent hcs hyG
    (fun k hk => ⟨(hf k hk).1, (hf k hk).2.1, (hf k hk).2.2.1⟩) hgen hcen

end CFSG.KD.K36K

end
