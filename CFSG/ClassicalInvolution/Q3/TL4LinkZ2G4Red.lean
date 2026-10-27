module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W0
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM3T
public import CFSG.ClassicalInvolution.Q3.TL4Mdl1521Mem
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1RB
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1RD

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W.G4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.Blueprint

structure SPHyp {S : Type} [Group S] (A B : Subgroup S) (r : S) (x : MulAut S) : Prop where
  quat : QuatTwinDatum A r
  twin : ∃ q ∈ Subgroup.centralizer ({r} : Set S), conjSub q A = B
  ne : B ≠ A
  sq : x * x = 1
  fixA : ∀ a ∈ A, x a = a
  normB : ∀ b ∈ B, x b ∈ B
  cB : ∀ b ∈ B, x b = b → b * b = 1

namespace SPHyp

variable {S : Type} [Group S] {A B : Subgroup S} {r : S} {x : MulAut S}

theorem comm (h : SPHyp A B r x) : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  obtain ⟨q, hq, hqB⟩ := h.twin
  rcases h.quat.twins q hq with h1 | h1
  · exact absurd (hqB.symm.trans h1) h.ne
  · rw [← hqB]
    exact h1

theorem apply_apply (h : SPHyp A B r x) (s : S) : x (x s) = s := by
  have := congrArg (fun τ : MulAut S => τ s) h.sq
  simpa only [MulAut.mul_apply, MulAut.one_apply] using this

theorem q8B (h : SPHyp A B r x) : Nonempty (↥B ≃* QuaternionGroup 2) := by
  obtain ⟨q, -, hqB⟩ := h.twin
  obtain ⟨eA⟩ := h.quat.q8
  rw [← hqB]
  exact ⟨(A.equivMapOfInjective (MulAut.conj q).toMonoidHom (MulAut.conj q).injective).symm.trans
    eA⟩

theorem exists_moved (h : SPHyp A B r x) : ∃ b ∈ B, b * b ≠ 1 ∧ x b ≠ b := by
  obtain ⟨s, a, -, ha, -, hs1, -, has, -, -, -⟩ := E1521.quat_rel h.q8B
  refine ⟨a, ha, by rw [has]; exact hs1, fun hfix => ?_⟩
  exact hs1 (by rw [← has]; exact h.cB a ha hfix)

private theorem mem_map_equiv_apply_iff {M N : Type} [Group M] [Group N] (e : M ≃* N)
    {K : Subgroup M} {a : M} : e a ∈ K.map e.toMonoidHom ↔ a ∈ K := by
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

private theorem conj_apply_map (β x : MulAut S) (a : S) : (β * x * β⁻¹) (β a) = β (x a) := by
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]

theorem map (h : SPHyp A B r x) (β : MulAut S) :
    SPHyp (A.map β.toMonoidHom) (B.map β.toMonoidHom) (β r) (β * x * β⁻¹) where
  quat := E3S3O.OM3.quatTwinDatum_map_mulEquiv β h.quat
  twin := by
    obtain ⟨q, hq, rfl⟩ := h.twin
    refine ⟨β q, ?_, conjSub_map β.toMonoidHom q A⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hq ⊢
    rw [← map_mul, ← map_mul, hq]
  ne := fun h1 => h.ne (Subgroup.map_injective β.injective h1)
  sq := by
    have h1 : β * x * β⁻¹ * (β * x * β⁻¹) = β * (x * x) * β⁻¹ := by group
    rw [h1, h.sq]
    group
  fixA := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := hy
    show (β * x * β⁻¹) (β a) = β a
    rw [conj_apply_map, h.fixA a ha]
  normB := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := hy
    show (β * x * β⁻¹) (β b) ∈ _
    rw [conj_apply_map]
    exact (mem_map_equiv_apply_iff β).mpr (h.normB b hb)
  cB := by
    intro y hy hfix
    obtain ⟨b, hb, rfl⟩ := hy
    change (β * x * β⁻¹) (β b) = β b at hfix
    rw [conj_apply_map] at hfix
    show β b * β b = 1
    rw [← map_mul, h.cB b hb (β.injective hfix), map_one]

end SPHyp

section Reduction

variable {W : Type} [Group W] [Finite W] {Φ : Set (Subgroup W)} {K K' : Subgroup W} {k k' : W}
  {σ : MulAut W} {Q : Type} [Group Q]

theorem isPGroup_K (h : TwinBase3 Φ K K' k k') (f : W →* Q) (hf : Function.Surjective f)
    (hf2 : IsPGroup 2 ↥f.ker) (hs : IsSimpleGroup Q)
    (hOS : Balance.oddCoreIn (Subgroup.centralizer ({f k} : Set Q)) = ⊥) : IsPGroup 2 ↥K := by
  have h1 := E3S3O.isPGroup_conj_of_simple h f hf hf2 hs hOS 1
  rwa [conjSub_one] at h1

theorem fix_K (hT : TwinSProp3 Φ K K' k k' σ) (f : W →* Q) (hf : Function.Surjective f)
    (hf2 : IsPGroup 2 ↥f.ker) (hs : IsSimpleGroup Q)
    (hOS : Balance.oddCoreIn (Subgroup.centralizer ({f k} : Set Q)) = ⊥) :
    ∀ x ∈ K, σ x = x := by
  have hK2 := isPGroup_K hT.toTwinBase3 f hf hf2 hs hOS
  obtain ⟨P, hP, hPfix⟩ := hT.fixK
  have hKP : K = P := hP.2.2 _ le_rfl hK2 hP.1
  intro x hx
  exact hPfix x (hKP ▸ hx)

theorem sPHyp_of_reduction (hT : TwinSProp3 Φ K K' k k' σ) (f : W →* Q)
    (hf : Function.Surjective f) (hf2 : IsPGroup 2 ↥f.ker) (hs : IsSimpleGroup Q)
    (hOS : Balance.oddCoreIn (Subgroup.centralizer ({f k} : Set Q)) = ⊥) :
    SPHyp (K.map f) (K'.map f) (f k)
      (E3S3O.descend f hf σ (E3S3O.map_ker_aut hT.toTwinBase3 f hf hf2 hs σ)) := by
  have h := hT.toTwinBase3
  set hσ := E3S3O.map_ker_aut h f hf hf2 hs σ
  have hx : ∀ w, E3S3O.descend f hf σ hσ (f w) = f (σ w) := E3S3O.descend_apply f hf σ hσ
  obtain ⟨-, hinf, -⟩ := E3S3O.members_of_simple h f hf hf2 hs hOS
  obtain ⟨-, ⟨c, hcK, hcr, hK'⟩, hne⟩ := E3S3O.twin_map_of_simple h f hf hf2 hs hOS
  have hK'2 : IsPGroup 2 ↥K' := hcK ▸ E3S3O.isPGroup_conj_of_simple h f hf hf2 hs hOS c
  obtain ⟨Q', hQ', hQ'σ, hQ'fix⟩ := hT.onK'
  have hKQ' : K' = Q' := hQ'.2.2 _ le_rfl hK'2 hQ'.1
  have hfixK := fix_K hT f hf hf2 hs hOS
  refine ⟨E3S3O.quatTwinDatum_map_of_simple h f hf hf2 hs hOS, ⟨f c, hcr, hK'.symm⟩, hne, ?_,
    ?_, ?_, ?_⟩
  · ext y
    obtain ⟨w, rfl⟩ := hf y
    show E3S3O.descend f hf σ hσ (E3S3O.descend f hf σ hσ (f w)) = f w
    have h1 : σ (σ w) = w := by
      have := congrArg (fun τ : MulAut W => τ w) hT.sq
      simpa only [MulAut.mul_apply, MulAut.one_apply] using this
    rw [hx, hx, h1]
  · rintro _ ⟨y, hy, rfl⟩
    rw [hx, hfixK y hy]
  · rintro _ ⟨y, hy, rfl⟩
    rw [hx]
    exact ⟨σ y, hKQ' ▸ hQ'σ y (hKQ' ▸ hy), rfl⟩
  · rintro _ ⟨y, hy, rfl⟩ hfix
    rw [hx] at hfix
    have hσy : σ y ∈ K' := hKQ' ▸ hQ'σ y (hKQ' ▸ hy)
    have h4 : y⁻¹ * σ y ∈ conjSub c K ⊓ f.ker := ⟨hcK ▸ K'.mul_mem (K'.inv_mem hy) hσy, by
      show y⁻¹ * σ y ∈ f.ker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfix, inv_mul_cancel]⟩
    rw [hinf c, Subgroup.mem_bot] at h4
    have h5 : σ y = y := (inv_mul_eq_one.mp h4).symm
    have h6 := hQ'fix y (hKQ' ▸ hy) h5
    show f y * f y = 1
    rw [← map_mul, h6, map_one]

end Reduction

section Cert


theorem sPHyp_of_quotCenter {W : Type} [Group W] [Finite W] {Φ : Set (Subgroup W)}
    {K K' : Subgroup W} {k k' : W} {σ : MulAut W} (hT : TwinSProp3 Φ K K' k k' σ)
    (N : Subgroup W) [N.Normal] (hN : N = Subgroup.zpowers (k * k'))
    {t : Assembly.LowTwoRank.StatedLieTag} {n : ℕ} (ht : E3S3O.ClassicalTag3 t)
    (hS : LieModel ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N)) t n 3 1) :
    ∃ x : MulAut ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N)),
      SPHyp (K.map ((QuotientGroup.mk' (Subgroup.center (W ⧸ N))).comp (QuotientGroup.mk' N)))
        (K'.map ((QuotientGroup.mk' (Subgroup.center (W ⧸ N))).comp (QuotientGroup.mk' N)))
        (((QuotientGroup.mk' (Subgroup.center (W ⧸ N))).comp (QuotientGroup.mk' N)) k) x := by
  obtain ⟨hf, hf2, hs, hOS⟩ := E3S3O.quotCenter_reduction hT.toTwinBase3 N hN ht hS
  exact ⟨_, sPHyp_of_reduction hT _ hf hf2 hs hOS⟩

end Cert

end CFSG.ClassicalInvolution.Q3.TL4.Z2W.G4
