module

public import CFSG.GF2Type.Smith1979.W4C2TestComm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4C2

namespace LocalTest

open Module QuadraticMap CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

@[expose] def Wv (i : Fin 4) : Vm := vecE (ws4.getD i.val (0, 0))

theorem Wv_indep : LinearIndependent (ZMod 2) Wv := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have : ∀ g : Fin 4 → ZMod 2, ∑ i, g i • Wv i = 0 → ∀ i, g i = 0 := by decide
  exact this g hg

theorem Wv_mem (i : Fin 4) : ws4.getD i.val (0, 0) ∈ ws4 := by
  fin_cases i <;> simp [ws4]

theorem vm_add_self (b : Vm) : b + b = 0 := by
  rw [← two_smul (ZMod 2) b]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_smul]

theorem vm_sub_eq_add (a b : Vm) : a - b = a + b := by
  rw [sub_eq_add_neg, ← eq_neg_of_add_eq_zero_left (vm_add_self b)]

theorem vecE_xorV (u v : Nat × Nat) : vecE (xorV u v) = vecE u + vecE v :=
  Prod.ext (toVecD_xor 4 _ _) (toVecD_xor 4 _ _)

theorem false_of_M_aux (hv : (Hlist ()).all validE = true) (P Cl Kl : List El)
    (hPdef : P = stabL (Hlist ()) bM) (hClP : ∀ C ∈ Cl, C ∈ P) (hKlCl : ∀ k ∈ Kl, k ∈ Cl)
    (hcand : candOK P Cl = true) (hlen : Cl.length = 16)
    (hCl : Cl.all (fun c => eqE (mulE c c) idE &&
      Cl.all fun c' => Cl.any (eqE (mulE c c')) && commuteE c c') = true)
    (hinv : P.all (fun F => Cl.all fun c => Cl.any (eqE (conj F c))) = true)
    (hKl : Kl.all (fun k => P.any fun p => Cl.any fun c =>
      eqE (mulE (conj p c) c) k) = true)
    (hws : ws4.all (fun w => Kl.any fun k => (perp bM).any fun v =>
      eqV (xorV (appE k v) v) w) = true)
    (hkstar : Kl.any (fun k => !(eqE k idE) && ws4.all fun w => eqV (appE k w) w) = true)
    {L : Subgroup (Vm ≃ₗ[ZMod 2] Vm)} {D : Submodule (ZMod 2) Vm}
    (H : Hyp (vecE bM) L D) : False := by
  have hPv : ∀ E ∈ P, Valid E ∧ dec E ∈ Hm ∧ dec E (vecE bM) = vecE bM := fun E hE => by
    rw [hPdef] at hE
    exact stabL_spec hv hE
  have hClv : ∀ C ∈ Cl, Valid C := fun C hC => (hPv C (hClP C hC)).1
  classical
  set ClS : Finset (Vm ≃ₗ[ZMod 2] Vm) := (Cl.map dec).toFinset with hClS
  have hmemS : ∀ x, x ∈ ClS ↔ ∃ C ∈ Cl, dec C = x := by
    intro x
    simp [hClS]
  have hcard : ClS.card ≤ 16 := by
    calc ClS.card ≤ (Cl.map dec).length := List.toFinset_card_le _
      _ = 16 := by rw [List.length_map, hlen]
  have hcand' : candOK (stabL (Hlist ()) bM) Cl = true := by rw [← hPdef]; exact hcand
  have hLC : ∀ x ∈ L, x ∈ ClS := by
    intro x hx
    obtain ⟨C, hC, _, rfl⟩ := comm_mem_Cl hv hcand' H.LH H.Lc H.Ls H.Lb H.Ln x hx
    exact (hmemS _).mpr ⟨C, hC, rfl⟩
  have hsqS : ∀ x ∈ ClS, x * x = 1 := by
    intro x hx
    obtain ⟨C, hC, rfl⟩ := (hmemS x).mp hx
    have h1 := List.all_eq_true.mp hCl C hC
    simp only [Bool.and_eq_true] at h1
    rw [← dec_mul (hClv C hC) (hClv C hC), dec_eq_of_eqE h1.1, dec_idE]
  have hmulS : ∀ x ∈ ClS, ∀ y ∈ ClS, x * y ∈ ClS := by
    intro x hx y hy
    obtain ⟨C, hC, rfl⟩ := (hmemS x).mp hx
    obtain ⟨C', hC', rfl⟩ := (hmemS y).mp hy
    have h1 := List.all_eq_true.mp hCl C hC
    simp only [Bool.and_eq_true, List.all_eq_true] at h1
    have h2 := h1.2 C' hC'
    obtain ⟨C'', hC'', hEq⟩ := List.any_eq_true.mp h2.1
    refine (hmemS _).mpr ⟨C'', hC'', ?_⟩
    rw [← dec_eq_of_eqE hEq, dec_mul (hClv C hC) (hClv C' hC')]
  have hcommS : ∀ x ∈ ClS, ∀ y ∈ ClS, x * y = y * x := by
    intro x hx y hy
    obtain ⟨C, hC, rfl⟩ := (hmemS x).mp hx
    obtain ⟨C', hC', rfl⟩ := (hmemS y).mp hy
    have h1 := List.all_eq_true.mp hCl C hC
    simp only [Bool.and_eq_true, List.all_eq_true] at h1
    have h2 := h1.2 C' hC'
    have h3 := dec_eq_of_eqE h2.2
    rw [← dec_mul (hClv C hC) (hClv C' hC'), ← dec_mul (hClv C' hC') (hClv C hC)]
    exact h3
  have hinvS : ∀ p ∈ Hm, p (vecE bM) = vecE bM → ∀ x ∈ ClS, p * x * p⁻¹ ∈ ClS := by
    intro p hp hpb x hx
    obtain ⟨C, hC, rfl⟩ := (hmemS x).mp hx
    obtain ⟨F, hF, hFv, rfl⟩ := exists_stabL hv hp hpb
    have hF' : F ∈ P := by rw [hPdef]; exact hF
    have h1 := List.all_eq_true.mp hinv F hF'
    have h2 := List.all_eq_true.mp h1 C hC
    obtain ⟨C', hC', hEq⟩ := List.any_eq_true.mp h2
    refine (hmemS _).mpr ⟨C', hC', ?_⟩
    rw [← dec_eq_of_eqE hEq, dec_conj hFv (hClv C hC)]
  have hK : ∀ p ∈ Hm, p (vecE bM) = vecE bM → ∀ c ∈ ClS, p * c * p⁻¹ * c ∈ L := by
    intro p hp hpb c hc
    by_cases hcL : c ∈ L
    · exact L.mul_mem (H.Ln p hp hpb c hcL) hcL
    · have hc' := hinvS p hp hpb c hc
      have hc'L : p * c * p⁻¹ ∉ L := by
        intro h
        apply hcL
        have hpib : p⁻¹ (vecE bM) = vecE bM := by
          calc p⁻¹ (vecE bM) = p⁻¹ (p (vecE bM)) := by rw [hpb]
            _ = vecE bM := inv_apply_apply' p _
        have := H.Ln p⁻¹ (Hm.inv_mem hp) hpib _ h
        simpa [mul_assoc] using this
      exact coset_mem ClS hcard L H.L8 hLC hmulS hcommS hsqS hc hc' hcL hc'L
  have hKL : ∀ k ∈ Kl, dec k ∈ L := by
    intro k hk
    have hkv := hClv k (hKlCl k hk)
    have h1 := List.all_eq_true.mp hKl k hk
    obtain ⟨F, hF, h2⟩ := List.any_eq_true.mp h1
    obtain ⟨C, hC, h3⟩ := List.any_eq_true.mp h2
    obtain ⟨hFv, hFm, hFb⟩ := hPv F hF
    have hCv := hClv C hC
    have e : dec k = dec F * dec C * (dec F)⁻¹ * dec C := by
      rw [← dec_eq_of_eqE h3, dec_mul (valid_conj hFv hCv) hCv, dec_conj hFv hCv]
    rw [e]
    exact hK _ hFm hFb _ ((hmemS _).mpr ⟨C, hC, rfl⟩)
  have hWD : ∀ i, Wv i ∈ D := by
    intro i
    have h1 := List.all_eq_true.mp hws _ (Wv_mem i)
    obtain ⟨k, hk, h2⟩ := List.any_eq_true.mp h1
    obtain ⟨v, hv', h3⟩ := List.any_eq_true.mp h2
    have hkv := hClv k (hKlCl k hk)
    have hperp : polarB bM v = false := by
      have := (List.mem_filter.mp hv').2
      simpa using this
    have hpolar : polar q0 (vecE bM) (vecE v) = 0 := by
      rw [polar_q0_vecE, hperp]
      simp
    have hmem := H.LD (dec k) (hKL k hk) (vecE v) hpolar
    have e : Wv i = dec k (vecE v) - vecE v := by
      unfold Wv
      rw [← eqV_iff.mp h3, vecE_xorV, vecE_appE, dec_apply hkv, vm_sub_eq_add]
    rw [e]
    exact hmem
  obtain ⟨k, hk, hk2⟩ := List.any_eq_true.mp hkstar
  have hkv := hClv k (hKlCl k hk)
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hk2
  obtain ⟨hk1, hkfix⟩ := hk2
  have hk1' : dec k ≠ 1 := by
    intro h
    have : eqE k idE = true := eqE_of_dec_eq hkv valid_idE (by rw [h, dec_idE])
    rw [this] at hk1
    exact Bool.noConfusion hk1
  have hkfix' : ∀ i, dec k (Wv i) = Wv i := by
    intro i
    have := hkfix _ (Wv_mem i)
    unfold Wv
    rw [dec_apply hkv, ← vecE_appE]
    exact eqV_iff.mp this
  exact dim_contradiction H.L8 H.card H.faith Wv Wv_indep hWD (hKL k hk) hk1' hkfix'

theorem false_of_M (hchk : chk = true) {L : Subgroup (Vm ≃ₗ[ZMod 2] Vm)}
    {D : Submodule (ZMod 2) Vm} (H : Hyp (vecE bM) L D) : False := by
  obtain ⟨hv, ho, hN, hM⟩ := chk_parts hchk
  simp only [chkM, Bool.and_eq_true] at hM
  obtain ⟨⟨⟨⟨⟨⟨hcand, hlen⟩, hCl⟩, hinv⟩, hKl⟩, hws⟩, hkstar⟩ := hM
  refine false_of_M_aux hv (stabL (Hlist ()) bM) _ _ rfl ?_ ?_ hcand ?_ hCl hinv hKl hws hkstar H
  · intro C hC
    exact (List.mem_filter.mp hC).1
  · intro k hk
    exact (List.mem_filter.mp hk).1
  · simpa using hlen

end LocalTest

end CFSG.GF2Type.Smith1979.W4C2
