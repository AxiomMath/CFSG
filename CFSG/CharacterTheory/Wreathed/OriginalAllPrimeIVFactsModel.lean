module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeIVFactsMap
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeTIFactsModel

public section

namespace CFSG.Wreathed.OriginalAllPrime.IVFacts

open CFSG.ABGTheoremB CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.Wreathed.OriginalAllPrime.ModelSignalizers

variable {G : Type} [Group G] [Finite G]

theorem mem_modelBase_of_two_pow {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m}
    {heven : Even m} {Sigma : Subgroup (F ≃+* F)} {hSigma : ∀ τ ∈ Sigma, τ (b : F) = b}
    (hodd : Odd (Nat.card Sigma)) {g : SemilinearExtension F b m hm heven Sigma hSigma} {k : ℕ}
    (hk : g ^ 2 ^ k = 1) : g ∈ ModelSignalizers.modelBase b m hm heven Sigma hSigma := by
  rw [ModelSignalizers.modelBase, SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  set t := SemidirectProduct.rightHom g with ht
  have h1 : t ^ 2 ^ k = 1 := by rw [ht, ← map_pow, hk, map_one]
  have h2 : orderOf t ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf t ∣ Nat.card Sigma := orderOf_dvd_natCard t
  have hcop : Nat.Coprime (2 ^ k) (Nat.card Sigma) := (Nat.coprime_two_left.mpr hodd).pow_left k
  have h4 : orderOf t ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd h2 h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)

variable [IsSimpleGroup G]

theorem wreathedSetting_exists_isWModel
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ τ ∈ Sigma, τ (b : F) = b)
      (φ : (wreathedSetting n S e p f).N →* SemilinearExtension F b (2 ^ n) (wreathModulus_pos n)
        (wreathModulus_even hn) Sigma hSigma),
      IsWModel (wreathedSetting n S e p f) φ := by
  have hp2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hpodd)
  obtain ⟨F, hfield, hfinite, Sigma, b, hSigma, ρ, Ψ, hdata⟩ :=
    exists_conditionalCompatibleModelData hnonab n hn S e hfour p f hp hp2 hf hlocal
  let : Field F := hfield
  let : Finite F := hfinite
  let : Fintype F := Fintype.ofFinite F
  have hm2 := NormalComponentLift.two_pow_eq_two_part hnonab hfour hp hp2 hf hlocal
  obtain ⟨h, hh⟩ := TIFacts.exists_liftMap_eq_modelY hnonab hfour hp hpodd hf hlocal hdata
  have hφ := TIFacts.liftMap_isModelMap hnonab hfour hp hpodd hf hlocal hdata hh
  set σ := wreathedSetting n S e p f with hσ
  set φ : σ.N →* SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
    Sigma hSigma := NormalComponentLift.liftMap n hn S e Ψ h with hφdef
  have hSN : (S : Subgroup G) ≤ σ.N := sylow_le_involutionCentralizer n hn S e
  have hD : σ.D = (S : Subgroup G) := wreathedSetting_D_eq n (by omega) S e p f
  have hLN : σ.L ≤ σ.N := sup_le hφ.L₀_le hSN
  have hxN : σ.x ∈ σ.N := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  refine ⟨F, hfield, inferInstance, Sigma, b, hSigma, φ,
    { model := hφ
      p_prime := hp
      p_odd := hpodd
      one_le_f := hf
      card := hdata.card
      two_part := hm2
      sigma_odd := hdata.sigma_odd
      sigma_cyclic := hdata.sigma_cyclic
      sigma_dvd := hdata.sigma_dvd
      nonsquare := hdata.nonsquare
      x_mem := hxN
      map_x := TIFacts.liftMap_x_eq hnonab hfour hp hpodd hf hlocal hdata h hxN
      L_le_N := hLN
      mem_L_iff := fun g => ⟨fun hg => ?_, fun hg => ?_⟩
      D_le_N := hD ▸ hSN
      x_mem_D := hD ▸ (e.symm (Original.x (2 ^ n))).property
      x₂_mem_D := hD ▸ (e.symm (Original.x2 (2 ^ n))).property
      exists_swap := ?_ }⟩
  ·
    have hle : (σ.L.subgroupOf σ.N).map φ ≤ ModelSignalizers.modelBase b (2 ^ n)
        (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma := by
      rw [show σ.L = σ.L₀ ⊔ (S : Subgroup G) from rfl,
        Subgroup.subgroupOf_sup hφ.L₀_le hSN, Subgroup.map_sup, hφ.map_L₀]
      refine sup_le ?_ ?_
      · rw [modelLayer, ModelSignalizers.modelBase]
        rintro _ ⟨_, ⟨X, rfl⟩, rfl⟩
        exact ⟨_, rfl⟩
      · rintro _ ⟨s, hs, rfl⟩
        obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, Subgroup.mem_subgroupOf.mp hs⟩
        have hk' : s ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
        exact mem_modelBase_of_two_pow hdata.sigma_odd (k := k)
          (by rw [← map_pow, hk', map_one])
    exact hle ⟨g, hg, rfl⟩
  ·
    have hON : σ.ON ≤ σ.L := hφ.ON_le.trans le_sup_left
    exact hφ.mem_of_map_mem hON (TIFacts.modelBase_le_map_L hn hφ hg)
  ·
    refine ⟨wreathModelHom S e (Original.d (2 ^ n)), ?_, ?_, ?_⟩
    · rw [hD]
      exact (e.symm (Original.d (2 ^ n))).property
    · apply modelY_le_wreathedSetting_L₀ hnonab n hn S e hfour p f
      exact ⟨Original.d (2 ^ n), Subgroup.subset_closure (by simp), rfl⟩
    · have h1 := NormalComponentLift.d_conj_x2 n hn S e
      rw [← map_mul] at h1
      exact h1

end CFSG.Wreathed.OriginalAllPrime.IVFacts
