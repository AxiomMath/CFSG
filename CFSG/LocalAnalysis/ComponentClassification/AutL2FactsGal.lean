module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

universe u

variable (F : Type u) [Field F] [Finite F]

instance finite_ringAut : Finite (F ≃+* F) :=
  Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective

instance finite_pgl2 : Finite (PGL2 F) :=
  Finite.of_surjective _ Matrix.ProjGenLinGroup.mk_surjective

instance finite_pGammaL2 : Finite (PGammaL2 F) :=
  Finite.of_injective (fun g : PGammaL2 F => (g.left, g.right))
    (fun _ _ h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

@[expose] def ringAutEquivGal (p : ℕ) [Fact p.Prime] [CharP F p] :
    letI := ZMod.algebra F p
    (F ≃+* F) ≃* (F ≃ₐ[ZMod p] F) :=
  let := ZMod.algebra F p
  { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ) fun x =>
      DFunLike.congr_fun (RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod p) F))
        (algebraMap (ZMod p) F)) x
    invFun := fun σ => σ.toRingEquiv
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }

theorem isCyclic_ringAut : IsCyclic (F ≃+* F) := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hchar, -, hp, -⟩ := FiniteField.card' F
  have : Fact p.Prime := ⟨hp⟩
  let := ZMod.algebra F p
  exact (ringAutEquivGal F p).isCyclic.mpr inferInstance

theorem card_ringAut {p f : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ f) :
    Nat.card (F ≃+* F) = f := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  have : CharP F p := charP_of_card_eq_prime_pow hcardF
  let := ZMod.algebra F p
  rw [Nat.card_congr (ringAutEquivGal F p).toEquiv, IsGalois.card_aut_eq_finrank]
  have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := F)
  rw [hF, Nat.card_zmod] at h
  exact (Nat.pow_right_injective hp.two_le h).symm

variable {F}

theorem card_le_two_of_sq_ringAut (H : Subgroup (F ≃+* F)) (hH : ∀ σ ∈ H, σ * σ = 1) :
    Nat.card H ≤ 2 := by
  classical
  have := isCyclic_ringAut F
  have : Fintype (F ≃+* F) := Fintype.ofFinite _
  have h := IsCyclic.card_pow_eq_one_le (α := F ≃+* F) (n := 2) two_pos
  calc Nat.card H = Fintype.card H := Nat.card_eq_fintype_card
    _ = (Finset.univ.filter fun σ : F ≃+* F => σ ∈ H).card := by
        rw [← Fintype.card_subtype]
    _ ≤ (Finset.univ.filter fun σ : F ≃+* F => σ ^ 2 = 1).card := by
        apply Finset.card_le_card
        intro σ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro hσ
        rw [pow_two]
        exact hH σ hσ
    _ ≤ 2 := h

theorem eq_one_of_two_power_ringAut {p f : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ f)
    (hf : Odd f) (σ : F ≃+* F) (k : ℕ) (hσ : σ ^ 2 ^ k = 1) : σ = 1 := by
  have hdvd : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hσ
  have hdvdf : orderOf σ ∣ f := by
    rw [← card_ringAut F hp hF]
    exact orderOf_dvd_natCard σ
  have hcop : Nat.Coprime (2 ^ k) f := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hf)
  have h1 : orderOf σ = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd hdvdf
  exact orderOf_eq_one_iff.mp h1

end CFSG.ComponentClassification.AutL2Facts
