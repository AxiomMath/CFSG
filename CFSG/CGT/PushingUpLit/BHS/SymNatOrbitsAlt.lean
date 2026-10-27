module

public import CFSG.CGT.PushingUpLit.BHS.SymNatOrbitsCount
public import CFSG.CGT.PushingUpLit.BHS.SymNatMaxSwap

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Quasithin.A1b

variable {n : ℕ}

theorem setStab_le_normalizer_altOn (S : Finset (Fin n)) :
    setStab S ≤ Subgroup.normalizer (altOn S : Set (Equiv.Perm (Fin n))) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [mem_altOn, mem_altOn, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv,
    mul_right_comm, Int.units_mul_self, one_mul]
  refine and_congr_left fun _ => ⟨fun h1 x hx => ?_, fun h1 x hx => ?_⟩
  · have hx' : y⁻¹ x ∉ S := by
      intro h'
      have h2 := (mem_setStab.1 hy (y⁻¹ x)).2 h'
      rw [perm_apply_inv_self] at h2
      exact hx h2
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1 _ hx', perm_apply_inv_self]
  · have hx' : y x ∉ S := fun h' => hx ((mem_setStab.1 hy x).1 h')
    have h2 := h1 (y x) hx'
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, perm_inv_apply_self] at h2
    exact y.injective h2

theorem three_le_card_movFin {F : Subgroup (Equiv.Perm (Fin n))} (hF : opResidual 2 F = F)
    {x₀ : Fin n} (hx₀ : ∃ f ∈ F, f x₀ ≠ x₀) : 3 ≤ (movFin F).card := by
  obtain ⟨f, hf, hfx⟩ := hx₀
  obtain ⟨g, hg, hgx, hgf⟩ := exists_third_of_opResidual hF hf hfx
  have hmem : ∀ h ∈ F, h x₀ ≠ x₀ → h x₀ ∈ movFin F := fun h hh hhx =>
    mem_movFin.2 ⟨h⁻¹, F.inv_mem hh, by rw [perm_inv_apply_self]; exact hhx.symm⟩
  exact Finset.two_lt_card_iff.2 ⟨x₀, f x₀, g x₀, mem_movFin.2 ⟨f, hf, hfx⟩, hmem f hf hfx,
    hmem g hg hgx, hfx.symm, hgx.symm, hgf.symm⟩

theorem two_fourteen_b (n : ℕ) (hn : Odd n) {F Y : Subgroup (Equiv.Perm (Fin n))}
    (hF : opResidual 2 F = F)
    (hirr : IsIrrSection (F.map (coreAct n))
      (commV (F.map (coreAct n)) ⊔ fixV (F.map (coreAct n))) (fixV (F.map (coreAct n))))
    (k : ℕ) (hk : Odd k) (hAlt : IsAltNatSection (F.map (coreAct n)) (commV (F.map (coreAct n)))
      ⊥ k) (hY : IsMaxSwapGroup Y) :
    ∃ g : Equiv.Perm (Fin n), conjSub g Y ≤ Subgroup.normalizer (F : Set (Equiv.Perm (Fin n))) := by
  obtain ⟨x₀, hx₀⟩ := exists_moved_of_irr hirr
  have hsame : ∀ a, (∃ f ∈ F, f a ≠ a) → ∃ f ∈ F, f x₀ = a :=
    fun a ha => same_orbit_of_moved hn hF hirr ha hx₀
  set S := movFin F with hS
  have hm3 : 3 ≤ S.card := three_le_card_movFin hF hx₀
  have h3n : 3 ≤ n := hm3.trans ((Finset.card_le_univ S).trans_eq (Fintype.card_fin n))
  obtain ⟨-, θ, β, hβs, hβk, -⟩ := hAlt
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  have hcV : Nat.card (commV (F.map (coreAct n))) = Nat.card (coreMod k) :=
    Nat.card_eq_of_bijective β ⟨hβi, hβs⟩
  have h1 := card_commV_mul hn hx₀ hsame
  have h2 := card_coreMod_mul_two hk
  have h3 := card_movFin_add F
  rw [hcV, mul_right_comm, h2, ← pow_add] at h1
  have hkN := Nat.pow_right_injective (le_refl 2) h1
  have hSk : S.card = k := by rw [hS]; omega
  have hcardF : Nat.card F = k.factorial / 2 := by
    have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 (by omega)
    refine (Subgroup.card_map_of_injective (coreAct_injective h3n)).symm.trans
      ((Nat.card_congr θ.toEquiv).trans ?_)
    rw [nat_card_alternatingGroup, Nat.card_fin]
  have hFS : F = altOn S := Subgroup.eq_of_le_of_card_ge (le_altOn_movFin hF) (by
    rw [card_altOn (by omega), hcardF, hSk])
  obtain ⟨g, hg⟩ := exists_conjSub_le_setStab hn hY S
  refine ⟨g, hg.trans ((setStab_le_normalizer_altOn S).trans_eq ?_)⟩
  rw [← hFS]

end CFSG.CGT.PushingUpLit.BHS
