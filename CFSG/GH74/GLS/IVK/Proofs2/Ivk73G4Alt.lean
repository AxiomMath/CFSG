module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Main
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73A7Alt
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Core

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint Equiv Equiv.Perm CFSG.GH74.GLS.IVK.GHInv

theorem exists_two_involutions {G : Type*} [Group G] {E : Subgroup G} [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) : ∃ a b : G, a ∈ E ∧ b ∈ E ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧
      a * a = 1 ∧ b * b = 1 ∧ a * b = b * a := by
  classical
  have : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype E := Fintype.ofFinite E
  have hcard : 1 < (({1} : Finset ↥E)ᶜ).card := by
    rw [Finset.card_compl, Finset.card_singleton, ← Nat.card_eq_fintype_card, hE]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hcard
  have ha1 : a ≠ 1 := by simpa using ha
  have hb1 : b ≠ 1 := by simpa using hb
  have hsq : ∀ x : ↥E, x * x = 1 := fun x => by
    rw [← pow_two]
    exact (Monoid.exponent_dvd_iff_forall_pow_eq_one.1
      (IsElementaryAbelian.exponent_dvd_p 2 E)) x
  refine ⟨a, b, a.2, b.2, fun h => ha1 (Subtype.ext h), fun h => hb1 (Subtype.ext h),
    fun h => hab (Subtype.ext h), congrArg Subtype.val (hsq a), congrArg Subtype.val (hsq b), ?_⟩
  exact congrArg Subtype.val (IsMulCommutative.is_comm.comm a b)

theorem ivk73_alt : ∀ n : ℕ, 7 ≤ n → n ≤ 11 →
    Ivk73Fam (fun X _ => Nonempty (X ≃* alternatingGroup (Fin n))) := by
  intro n hn7 hn11 N _ _ L K Q h ⟨e⟩
  classical
  by_cases hK7 : Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin 7))
  ·
    obtain ⟨eK7⟩ := hK7
    obtain ⟨hQel, hQcard, hn11, hLtop⟩ :=
      ivk73_a7_alt (n := n) N L K Q h.normal h.cent_trivial e h.K_le h.K_quasi eK7
        h.Q_sylow h.Q_rank h.terminal
    refine ⟨hQel, hQcard, Or.inr (Or.inr ⟨hLtop, 7, by simp, ⟨eK7⟩, ?_⟩)⟩
    exact ⟨e.trans (Equiv.altCongrHom (finCongr (by omega : n = 7 + 4)))⟩
  ·
    have := h.normal
    obtain ⟨ι, hι, hιL⟩ := exists_perm_embedding hn7 h.cent_trivial e
    have hNA : alternatingGroup (Fin n) ≤ ι.range := by
      intro g hg
      refine ⟨((e.symm ⟨g, hg⟩ : ↥L) : N), ?_⟩
      rw [hιL]
      simp
    have hKA : K.map ι ≤ alternatingGroup (Fin n) := by
      rintro _ ⟨k, hk, rfl⟩
      rw [show ι k = ((e ⟨k, h.K_le hk⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) from
        hιL ⟨k, h.K_le hk⟩]
      exact (e _).2
    have hKp : Group.IsPerfect (K.map ι) := by
      have := h.K_quasi.1
      exact Group.IsPerfect.map ι
    have hK1 : K ≠ ⊥ := by
      intro hK
      obtain ⟨a, b, hab⟩ := h.K_quasi.2.2
      have : Subsingleton ↥K := by rw [hK]; infer_instance
      exact hab (Subsingleton.elim _ _)
    have hK1' : K.map ι ≠ ⊥ := by
      intro hK
      exact hK1 ((Subgroup.map_eq_bot_iff_of_injective K hι).1 hK)
    obtain ⟨E, hEQ, hE, hEc⟩ := h.exists_E
    obtain ⟨a, b, haE, hbE, ha1, hb1, hab, ha2, hb2, habc⟩ := exists_two_involutions hEc
    have hQ2 : IsPGroup 2 (Q.map ι) := by
      have := h.Q_sylow.isPGroup
      exact this.of_surjective (ι.subgroupMap Q) (ι.subgroupMap_surjective Q)
    have hQ4 : 4 ≤ Nat.card (Q.map ι) := by
      rw [Subgroup.card_map_of_injective hι, ← hEc]
      exact Subgroup.card_le_of_le hEQ
    have hQK : ∀ q ∈ Q.map ι, ∀ k ∈ K.map ι, q * k = k * q := by
      rintro _ ⟨q, hq, rfl⟩ _ ⟨k, hk, rfl⟩
      have := Subgroup.mem_centralizer_iff.1 (h.Q_sylow.le hq) k hk
      rw [← map_mul, ← map_mul, this]
    have hterm : Terminal ι.range (K.map ι) :=
      terminal_map ι hι hNA K (fun y hy hyk =>
        (h.terminal y hy (Subgroup.mem_centralizer_iff.2 hyk)).2.2)
    obtain ⟨F, hKF, hF5, hFcard, hNle, hQle⟩ :=
      alt_main (by rw [Fintype.card_fin]; exact hn11) hNA hKA hKp hK1' (Subgroup.map_le_range ι Q) hQK hQ2
        hQ4 (Subgroup.mem_map_of_mem ι (hEQ haE)) (Subgroup.mem_map_of_mem ι (hEQ hbE))
        (fun h1 => ha1 (hι (by rw [h1, map_one]))) (fun h1 => hb1 (hι (by rw [h1, map_one])))
        (fun h1 => hab (hι h1)) (by rw [← map_mul, ha2, map_one]) (by rw [← map_mul, hb2, map_one])
        (by rw [← map_mul, ← map_mul, habc]) hterm
    have hn' : n = F.card + 4 := by rw [Fintype.card_fin] at hFcard; omega
    have hQcard : Nat.card Q ≤ 4 := by
      rw [← Subgroup.card_map_of_injective hι]; exact hQle
    have hQE : E = Q := Subgroup.eq_of_le_of_card_ge hEQ (by omega)
    have hLtop : L = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : ι x ∈ alternatingGroup (Fin n) := hNle ⟨x, rfl⟩
      obtain ⟨l, hl⟩ : ∃ l : ↥L, ι (l : N) = ι x := ⟨e.symm ⟨ι x, hx⟩, by rw [hιL]; simp⟩
      rw [← hι hl]
      exact l.2
    let eK0 : ↥K ≃* altOn F :=
      (Subgroup.equivMapOfInjective K ι hι).trans (MulEquiv.subgroupCongr hKF)
    let eK1 : ↥K ≃* alternatingGroup (Fin F.card) :=
      eK0.trans ((altOnEquiv F).symm.trans (Equiv.altCongrHom F.equivFin))
    have hKsimple : IsSimpleGroup ↥K := eK0.isSimpleGroup_congr.2 (isSimpleGroup_altOn hF5)
    have hKeven : 2 ∣ Nat.card ↥K := by
      have hcardA : Nat.card (alternatingGroup (Fin F.card)) = F.card.factorial / 2 := by
        have : Nontrivial (Fin F.card) := Fin.nontrivial_iff_two_le.2 (by omega)
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      have hdvd : 24 ∣ F.card.factorial := by
        have := Nat.factorial_dvd_factorial (show 4 ≤ F.card by omega)
        simpa [Nat.factorial] using this
      obtain ⟨t, ht⟩ := hdvd
      rw [Nat.card_congr eK1.toEquiv, hcardA]
      exact ⟨6 * t, by omega⟩
    have hbot : pPrimeCore 2 ↥K = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥K) with h' | h'
      · exact h'
      · exfalso
        have hodd := GLS.TwoThin.odd_card_pPrimeCore ↥K
        rw [h', Subgroup.card_top] at hodd
        exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hKeven)
    let eQ : (↥K ⧸ pPrimeCore 2 ↥K) ≃* ↥K :=
      (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
    refine ⟨hQE ▸ hE, hQE ▸ hEc, Or.inr (Or.inr ⟨hLtop, F.card, ?_, ⟨eQ.trans eK1⟩,
      ⟨e.trans (Equiv.altCongrHom (finCongr hn'))⟩⟩)⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

end CFSG.GH74.GLS.IVK
