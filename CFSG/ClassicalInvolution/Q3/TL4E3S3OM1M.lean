module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1PF

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.Blueprint

namespace E3S3O

theorem model1524Twin3Om_of_centTag
    (hSF : ∀ (S : Type) [Group S] [Finite S] (t : Assembly.LowTwoRank.StatedLieTag) (n : ℕ),
      CentTag3 t n → LieModel S t n 3 1 → SigmaFixOm3 S) : Model1524Twin3Om := by
  intro W _ _ Φ K K' k k' σ hT ⟨N, _, hN, hC⟩
  have h := hT.toTwinBase3
  obtain ⟨t, n, ht, hS⟩ := centOmega3_tag_exact hC
  obtain ⟨hf, hf2, hs, hOS⟩ := quotCenter_reduction h N hN ht.classical hS
  set f := (QuotientGroup.mk' (Subgroup.center (W ⧸ N))).comp (QuotientGroup.mk' N) with hfdef
  have : Finite ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N)) := Finite.of_surjective f hf
  have hker := ker_eq_center_of_simple h f hf hf2 hs
  obtain ⟨-, hinf, -⟩ := members_of_simple h f hf hf2 hs hOS
  have hσ := map_ker_aut h f hf hf2 hs σ
  have hσb : ∀ w, descend f hf σ hσ (f w) = f (σ w) := descend_apply f hf σ hσ
  have hd := quatTwinDatum_map_of_simple h f hf hf2 hs hOS
  obtain ⟨-, ⟨c, hcK, hcr, hK'⟩, hne⟩ := twin_map_of_simple h f hf hf2 hs hOS
  have hsq : descend f hf σ hσ * descend f hf σ hσ = 1 := by
    ext y
    obtain ⟨w, rfl⟩ := hf y
    show descend f hf σ hσ (descend f hf σ hσ (f w)) = f w
    have h1 : σ (σ w) = w := by
      have := congrArg (fun τ : MulAut W => τ w) hT.sq
      simpa only [MulAut.mul_apply, MulAut.one_apply] using this
    rw [hσb, hσb, h1]
  have hfixA : ∀ a ∈ K.map f, descend f hf σ hσ a = a := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hσb, hT.fixK x hx]
  obtain ⟨Q', hQ', w, hwQ, hw4, hσw⟩ := hT.onK'
  have hK'2 : IsPGroup 2 ↥K' := hcK ▸ isPGroup_conj_of_simple h f hf hf2 hs hOS c
  have hKQ : K' = Q' := hQ'.2.2 _ le_rfl hK'2 hQ'.1
  have hwK' : w ∈ K' := hQ'.1 hwQ
  have hfw4 : orderOf (f w) = 4 := by
    have h4 : (4 : ℕ) = 2 ^ (1 + 1) := by norm_num
    rw [h4]
    apply orderOf_eq_prime_pow
    · intro h1
      have h3 : w ^ 2 ^ 1 ∈ conjSub c K ⊓ f.ker := ⟨hcK ▸ K'.pow_mem hwK' _, by
        show w ^ 2 ^ 1 ∈ f.ker
        rw [MonoidHom.mem_ker, map_pow, h1]⟩
      rw [hinf c, Subgroup.mem_bot] at h3
      have h5 := orderOf_dvd_of_pow_eq_one h3
      rw [hw4] at h5
      norm_num at h5
    · rw [← map_pow, ← h4, ← hw4, pow_orderOf_eq_one, map_one]
  have hwB : ∀ b ∈ K'.map f, descend f hf σ hσ b = f w * b * (f w)⁻¹ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hσb, hσw x (hKQ ▸ hx), map_mul, map_mul, map_inv]
  have hnn : ∀ C ∈ CoreAssembly.conjClass (K.map f), (∀ c ∈ C, descend f hf σ hσ c = c) →
      C ≠ K.map f → ¬ C ≤ Subgroup.normalizer (K.map f : Set _) := by
    rintro C ⟨s, hsC⟩ hfix hneC hle
    have hsC' : conjSub s (K.map f) = C := hsC
    subst hsC'
    obtain ⟨g, rfl⟩ := hf s
    rw [← AscQuot.map_conjSub] at hfix hneC hle
    exact hT.noNbr _ ⟨g, rfl⟩ (fix_of_fix_map h f hf hf2 hs hOS hT.perm hσ g hfix)
      (mem_omegaNbr_of_map h f hf hf2 hs hOS g hneC hle)
  obtain ⟨hLie, h3⟩ := hSF _ t n ht hS (K.map f) (K'.map f) (f k) (descend f hf σ hσ) hd
    ⟨f c, hcr, hK'.symm⟩ hne hsq hfixA ⟨f w, Subgroup.mem_map_of_mem f hwK', hfw4, hwB⟩ hnn
  have : Group.IsPerfect ↥(sigmaFixGen K σ) :=
    isPerfect_sigmaFixGen h f hf hf2 hs hOS hT.perm hσ h3
  have hY := map_sigmaFixGen h f hf hf2 hs hOS hT.perm hσ
  let η : ↥(sigmaFixGen K σ) →* ↥((sigmaFixGen K σ).map f) := f.subgroupMap _
  have hη : Function.Surjective η := MonoidHom.subgroupMap_surjective f _
  have hηker : ∀ x, x ∈ η.ker → (x : W) ∈ Subgroup.center W := fun x hx => by
    rw [← hker, MonoidHom.mem_ker]
    exact congrArg Subtype.val hx
  have hcen : η.ker ≤ Subgroup.center ↥(sigmaFixGen K σ) := fun x hx =>
    Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (Subgroup.mem_center_iff.mp (hηker x hx) y)
  have h2 : IsPGroup 2 ↥η.ker := by
    intro x
    obtain ⟨j, hj⟩ := hf2 ⟨(x : ↥(sigmaFixGen K σ)), by
      rw [hker]
      exact hηker x x.2⟩
    exact ⟨j, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hj))⟩
  have hX : LieModel ↥((sigmaFixGen K σ).map f) .PSU 3 3 1 := by
    rw [hY]
    exact hLie
  have hk := ker_eq_bot_of_psu33 η hη hcen h2 hX
  have hinj : Function.Injective η := (MonoidHom.ker_eq_bot_iff η).mp hk
  exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (MulEquiv.ofBijective η ⟨hinj, hη⟩).symm hX)

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
