module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM2Q
public import CFSG.ClassicalInvolution.Q3.TL4VtxOrb

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.Blueprint

namespace E3S3O

@[expose] def E4SigmaFix (M : Type) [Group M] : Prop :=
  ∀ (A B : Subgroup M) (r : M) (x : MulAut M), QuatTwinDatum A r →
    (∃ q ∈ Subgroup.centralizer ({r} : Set M), conjSub q A = B) → B ≠ A → x * x = 1 →
      (∀ a ∈ A, x a = a) → (∃ w ∈ B, orderOf w = 4 ∧ ∀ b ∈ B, x b = w * b * w⁻¹) →
        ∃ C : Subgroup M, (∃ q ∈ Subgroup.centralizer ({r} : Set M), conjSub q A = C) ∧
          C ≠ A ∧ ∀ c ∈ C, x c = c

theorem map_eq_self_of_fix {G : Type} [Group G] {H : Subgroup G} {x : MulAut G}
    (hx : ∀ h ∈ H, x h = h) : H.map x.toMonoidHom = H := by
  ext y
  refine ⟨?_, fun hy => ⟨y, hy, hx y hy⟩⟩
  rintro ⟨z, hz, rfl⟩
  show x z ∈ H
  rw [hx z hz]
  exact hz

variable {W : Type} [Group W] [Finite W] {Φ : Set (Subgroup W)} {K K' : Subgroup W} {k k' : W}
  {σ : MulAut W}

theorem false_of_twinSigma3_twinE4
    (hfix : ∀ (M : Type) [Group M] [Finite M], PhilipHall.QuaternionBridge.ExLie M → E4SigmaFix M)
    (hT : TwinSigma3 Φ K K' k k' σ) (hE : TwinE4 W) : False := by
  obtain ⟨Q, _, f, hf, hf2, hQ⟩ := hE
  have : Finite Q := Finite.of_surjective f hf
  have h := hT.toTwinBase3
  have hcl := h.fam.hyp.conjInvariant
  have hker : f.ker = Subgroup.center W :=
    le_antisymm (ker_le_center h f hf2) (center_le_ker h f hf hf2 hQ)
  have h2 : ∀ g : W, IsPGroup 2 ↥(conjSub g K) := isPGroup_conj h f hf hf2 hQ
  have hsyl : ∀ g : W, IsSylow2In (conjSub g K) (conjSub g K) := fun g =>
    ⟨le_rfl, h2 g, fun _ hV _ hle => le_antisymm hV hle⟩
  have hquat : ∀ g : W, Nonempty (↥(conjSub g K) ≃* QuaternionGroup 2) := fun g =>
    h.fam.quat _ (hcl g K h.memK) _ (hsyl g)
  have hinf : ∀ g : W, conjSub g K ⊓ f.ker = ⊥ := fun g =>
    inf_eq_bot_of_not_mem (h.invK.conj g) hf2 (not_mem_ker h f hf2 g)
  have heq : ∀ g₁ g₂ : W, (conjSub g₁ K).map f = (conjSub g₂ K).map f →
      conjSub g₁ K = conjSub g₂ K := fun g₁ g₂ he =>
    eq_of_map_eq h.fam hker.le (hcl g₁ K h.memK) (hcl g₂ K h.memK) (hquat g₂).some he
  obtain ⟨c, hc⟩ := h.memK'
  have hc' : conjSub c K = K' := hc
  subst hc'
  have hk' : c * k * c⁻¹ = k' := (h.invK.conj c).eq h.invK'
  have hfk : f k' = f k := by
    have h1 : k * k' ∈ f.ker := by
      rw [hker]
      exact h.center
    rw [MonoidHom.mem_ker, map_mul] at h1
    have h3 : f k * f k = 1 := by rw [← map_mul, h.invK.sq, map_one]
    calc f k' = f k * f k * f k' := by rw [h3, one_mul]
      _ = f k := by rw [mul_assoc, h1, mul_one]
  have hcr : f c ∈ Subgroup.centralizer ({f k} : Set Q) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : c * k = k' * c := by rw [← hk']; group
    rw [← map_mul, e, map_mul, hfk]
  have hne : (conjSub c K).map f ≠ K.map f := by
    intro he
    have h1 : conjSub c K = K := by
      simpa only [conjSub_one] using heq c 1 (by rw [conjSub_one]; exact he)
    rcases h.invK.unique k' (h1 ▸ h.invK'.mem) h.invK'.sq with h3 | h3
    · exact h.invK'.ne_one h3
    · exact h.ne h3.symm
  have hσ : f.ker.map σ.toMonoidHom = f.ker := by
    rw [hker]
    exact Subgroup.characteristic_iff_map_eq.mp inferInstance σ
  have hσb : ∀ w, descend f hf σ hσ (f w) = f (σ w) := descend_apply f hf σ hσ
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
  have hKQ : conjSub c K = Q' := hQ'.2.2 _ le_rfl (h2 c) hQ'.1
  have hwK' : w ∈ conjSub c K := hQ'.1 hwQ
  have hfw4 : orderOf (f w) = 4 := by
    have h4 : (4 : ℕ) = 2 ^ (1 + 1) := by norm_num
    rw [h4]
    apply orderOf_eq_prime_pow
    · intro h1
      have h3 : w ^ 2 ^ 1 ∈ conjSub c K ⊓ f.ker := ⟨(conjSub c K).pow_mem hwK' _, by
        show w ^ 2 ^ 1 ∈ f.ker
        rw [MonoidHom.mem_ker, map_pow, h1]⟩
      rw [hinf c, Subgroup.mem_bot] at h3
      have h5 := orderOf_dvd_of_pow_eq_one h3
      rw [hw4] at h5
      norm_num at h5
    · rw [← map_pow, ← h4, ← hw4, pow_orderOf_eq_one, map_one]
  have hwB : ∀ b ∈ (conjSub c K).map f, descend f hf σ hσ b = f w * b * (f w)⁻¹ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hσb, hσw x (hKQ ▸ hx), map_mul, map_mul, map_inv]
  have hd := quatTwinDatum_map h f hf hf2 hQ
  obtain ⟨C, ⟨q, hq, hqC⟩, hCA, hCfix⟩ := hfix Q hQ (K.map f) ((conjSub c K).map f) (f k)
    (descend f hf σ hσ) hd ⟨f c, hcr, (AscQuot.map_conjSub f c K).symm⟩ hne hsq hfixA
    ⟨f w, Subgroup.mem_map_of_mem f hwK', hfw4, hwB⟩
  have hCN : C ≤ Subgroup.normalizer (K.map f : Set Q) := by
    rcases hd.twins q hq with h1 | h1
    · exact absurd (hqC ▸ h1) hCA
    · intro y hy
      rw [mem_normalizer_iff_conjSub_eq]
      exact Vtx.conjSub_eq_of_forall_commute fun x hx => (h1 x hx y (hqC ▸ hy)).symm
  obtain ⟨g, rfl⟩ := hf q
  have hM₀C : (conjSub g K).map f = C := by
    rw [AscQuot.map_conjSub]
    exact hqC
  have hσK : K.map σ.toMonoidHom = K := map_eq_self_of_fix hT.fixK
  have hcomp : f.comp σ.toMonoidHom = (descend f hf σ hσ).toMonoidHom.comp f := by
    ext w
    exact (hσb w).symm
  have hσM₀ : (conjSub g K).map σ.toMonoidHom = conjSub g K := by
    have h1 : (conjSub g K).map σ.toMonoidHom = conjSub (σ g) K := by
      rw [AscQuot.map_conjSub, hσK]
      rfl
    have h3 : (conjSub (σ g) K).map f = (conjSub g K).map f := by
      rw [← h1, Subgroup.map_map, hcomp, ← Subgroup.map_map, hM₀C, map_eq_self_of_fix hCfix]
    rw [h1]
    exact heq _ _ h3
  have hfixM₀ : ∀ x ∈ conjSub g K, σ x = x := by
    intro x hx
    have h1 : σ x ∈ conjSub g K := by
      have := Subgroup.mem_map_of_mem σ.toMonoidHom hx
      rw [hσM₀] at this
      exact this
    have h3 : f (σ x) = f x := by
      rw [← hσb]
      exact hCfix _ (hM₀C ▸ Subgroup.mem_map_of_mem f hx)
    have h4 : x⁻¹ * σ x ∈ conjSub g K ⊓ f.ker :=
      ⟨(conjSub g K).mul_mem ((conjSub g K).inv_mem hx) h1, by
        show x⁻¹ * σ x ∈ f.ker
        rw [MonoidHom.mem_ker, map_mul, map_inv, h3, inv_mul_cancel]⟩
    rw [hinf g, Subgroup.mem_bot] at h4
    exact (inv_mul_eq_one.mp h4).symm
  have hM₀N : conjSub g K ≤ Subgroup.normalizer (K : Set W) := by
    intro m hm
    rw [mem_normalizer_iff_conjSub_eq]
    have h1 : f m ∈ Subgroup.normalizer (K.map f : Set Q) :=
      hCN (hM₀C ▸ Subgroup.mem_map_of_mem f hm)
    rw [mem_normalizer_iff_conjSub_eq] at h1
    simpa only [conjSub_one] using heq m 1 (by rw [AscQuot.map_conjSub, conjSub_one]; exact h1)
  have hM₀K : conjSub g K ≠ K := by
    intro h1
    apply hCA
    rw [← hM₀C, h1]
  exact hT.noNbr _ ⟨g, rfl⟩ hfixM₀ ⟨hcl g K h.memK, hM₀K, conjSub g K,
    mem_RSet_of_isSylow2In (hcl g K h.memK) (hsyl g), le_rfl, hM₀N⟩

theorem model1524Twin3E4_of
    (hfix : ∀ (M : Type) [Group M] [Finite M], PhilipHall.QuaternionBridge.ExLie M →
      E4SigmaFix M) : Model1524Twin3E4 :=
  fun _ _ _ _ _ _ _ _ _ hT hE => (false_of_twinSigma3_twinE4 hfix hT hE).elim

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
