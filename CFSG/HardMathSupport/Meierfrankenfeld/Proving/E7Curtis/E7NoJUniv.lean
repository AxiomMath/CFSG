module

public import CFSG.Quasithin.Background.SmithCurtisChevType
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesWeyl

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem

section NoJUniv


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]
  [Module.Finite k V]

theorem no_J_univ_e7 {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup .E7 K) V} (hρ : IsSimpleRep ρ)
    (hinj : Function.Injective ρ) {y : V} {χ : adjointGroup .E7 K → k}
    {J : Finset (Fin Tag.E7.rank)}
    (ht : IsChevType .E7 K 2 CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_weyl_neg_E7 ρ y χ J)
    (hJ : J = Finset.univ) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hχi : ∀ i t, χ (dC .E7 K i t) = 1 := fun i t =>
    ((ht.2.2.2 i).1 (hJ ▸ Finset.mem_univ i)).1 t
  have hy1 : ∀ i t, ρ (dC .E7 K i t) y = y := fun i t => by
    rw [ht.2.2.1 _ (dC_mem_H i t), hχi, one_smul]
  have hHy : ∀ h ∈ (chevDatum .E7 K 2 CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_weyl_neg_E7).H,
      ρ h y = y := by
    intro h hh
    have hh' : (h : ModGL .E7 K) ∈ torusGroup .E7 K := hh
    have key : ∀ g ∈ torusGroup .E7 K, ∃ hg : g ∈ adjointGroup .E7 K, ρ ⟨g, hg⟩ y = y := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨⟨i, t⟩, rfl⟩ := hx
        exact ⟨torusElt_mem_adjointGroup i t, hy1 i t⟩
      | one => exact ⟨one_mem _, by show ρ 1 y = y; rw [map_one, Module.End.one_apply]⟩
      | mul a b _ _ ha hb =>
        obtain ⟨ha1, ha2⟩ := ha
        obtain ⟨hb1, hb2⟩ := hb
        refine ⟨mul_mem ha1 hb1, ?_⟩
        have : (⟨a * b, mul_mem ha1 hb1⟩ : adjointGroup .E7 K) = ⟨a, ha1⟩ * ⟨b, hb1⟩ := rfl
        rw [this, ← act_mul, hb2, ha2]
      | inv a _ ha =>
        obtain ⟨ha1, ha2⟩ := ha
        refine ⟨inv_mem ha1, ?_⟩
        have : (⟨a⁻¹, inv_mem ha1⟩ : adjointGroup .E7 K) = (⟨a, ha1⟩ : adjointGroup .E7 K)⁻¹ := rfl
        rw [this]
        have h2 : ρ (⟨a, ha1⟩ : adjointGroup .E7 K)⁻¹ (ρ ⟨a, ha1⟩ y) = y := by
          rw [act_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [ha2] at h2
    obtain ⟨hg, hρg⟩ := key _ hh'
    exact hρg
  have hχ1 : ∀ h ∈ (chevDatum .E7 K 2 CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_weyl_neg_E7).H,
      χ h = 1 := by
    intro h hh
    have h1 := ht.2.2.1 h hh
    rw [hHy h hh] at h1
    exact (smul_left_injective k ht.2.1 (show χ h • y = (1 : k) • y by rw [one_smul]; exact h1.symm))
  set ρ0 : Representation k (adjointGroup .E7 K) (Unit →₀ k) :=
    Representation.trivial k _ (Unit →₀ k) with hρ0def
  have hρ0 : IsSimpleRep ρ0 := by
    refine ⟨⟨⟨0, Finsupp.single () 1, fun h => by simpa using congrArg (fun f => f ()) h⟩⟩,
      fun W _ => ?_⟩
    by_cases hW : W = ⊥
    · exact Or.inl hW
    right
    obtain ⟨f, hfW, hf0⟩ := (Submodule.ne_bot_iff W).1 hW
    have hf : f = f () • Finsupp.single () 1 := Finsupp.ext fun u => by cases u; simp
    have hc : f () ≠ 0 := fun h => hf0 (by rw [hf, h, zero_smul])
    generalize f () = c at hf hc
    have hs : Finsupp.single () (1 : k) ∈ W := by
      have := W.smul_mem c⁻¹ hfW
      rwa [hf, smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    refine eq_top_iff.2 fun g _ => ?_
    have : g = g () • Finsupp.single () 1 := Finsupp.ext fun u => by cases u; simp
    rw [this]
    exact Submodule.smul_mem _ _ hs
  have ht0 : IsChevType .E7 K 2 CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_weyl_neg_E7 ρ0
      (Finsupp.single () (1 : k)) χ J := by
    refine ⟨fun u _ => by simp [hρ0def], fun h => by simpa using congrArg (fun f => f ()) h,
      fun h hh => ?_, fun i => ?_⟩
    · simp [hρ0def, hχ1 h hh]
    · refine ⟨fun _ => ⟨hχi i, ?_⟩, fun _ => hJ ▸ Finset.mem_univ i⟩
      let : Fintype K := Fintype.ofFinite K
      rw [heckeT_chevDatum]
      simp only [hρ0def, Representation.trivial_apply, Finset.sum_const, Finset.card_univ]
      rw [← Nat.card_eq_fintype_card, hK, ← Nat.cast_smul_eq_nsmul k]
      have h0' : ((2 ^ n : ℕ) : k) = 0 := by
        rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨m, rfl⟩
        rw [pow_succ]; push_cast; rw [CharTwo.two_eq_zero, mul_zero]
      rw [h0', zero_smul]
  obtain ⟨β, hβ⟩ := iso_of_isChevType hρ hρ0 ht ht0
  have hid : ∀ g v, ρ g v = v := fun g v => by
    apply β.injective
    rw [hβ]
    simp [hρ0def]
  have h1 : xC .E7 K ⟨0, by decide⟩ 1 = 1 :=
    hinj (by ext v; rw [hid, map_one, Module.End.one_apply])
  exact xC_ne_one ⟨0, by decide⟩ 1 h1

end NoJUniv

end CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis

end
