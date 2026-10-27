module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.InducedAux
import CFSG.LocalAnalysis.GLTheoremB.I2810.OmegaAux
import CFSG.LocalAnalysis.GLTheoremB.I2810.Blocks

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.OmegaFinal

variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem indHom_toBar_eq (h : Setup28 W K S) {a : X} (haS : a ∈ S) (k : ↥K)
    (hak : a * (k : X) * a⁻¹ ∈ K) :
    InducedAux.indHom W K S h.hN ⟨a, haS⟩ (toBar W K k) = toBar W K ⟨a * k * a⁻¹, hak⟩ :=
  Subtype.ext ((InducedAux.indHom_toBar S h.hN ⟨a, haS⟩ k).trans
    (InducedAux.toBar_coe (W := W) ⟨a * k * a⁻¹, hak⟩).symm)

theorem theta_ne_one {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2)
    {U₁ U₂ V : Subgroup X} (sf : SingleFactor K V U₁ U₂)
    (θ : ↥K →* ↥(StatedOmega Q))
    (hiso : ChiefFactorIso K U₁ U₂ θ
      (fun g v => Matrix.mulVec ((g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) v))
    (hθ1 : ∀ k : ↥K, θ k = 1) : False := by
  obtain ⟨k, hk, x, hx, hxk⟩ := sf.nontriv
  obtain ⟨φ, -, hφk, hφe⟩ := hiso
  have hx' : k * x * k⁻¹ ∈ U₁ := sf.inv₁ k hk x hx
  have h1 := hφe ⟨k, hk⟩ ⟨x, hx⟩ ⟨k * x * k⁻¹, hx'⟩ rfl
  rw [hθ1] at h1
  simp only [OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec, ofAdd_toAdd] at h1
  apply hxk
  have h2 : φ (⟨x, hx⟩ * ⟨k * x * k⁻¹, hx'⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  have h3 : ((⟨x, hx⟩ * ⟨k * x * k⁻¹, hx'⟩⁻¹ : ↥U₁) : X) ∈ U₂ := (hφk _).mp h2
  have e : ((⟨x, hx⟩ * ⟨k * x * k⁻¹, hx'⟩⁻¹ : ↥U₁) : X) = ⁅x, k⁆ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]; group
  rwa [e] at h3

theorem concl_of_model {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2)
    (h : Setup28 W K S) (hR : Red28 W K S) {U₁ U₂ : Subgroup X}
    (sf : SingleFactor K (vOf W K S) U₁ U₂)
    (hE : ∀ k ∈ K, ∀ w ∈ kerAct W K S, ⁅k, w⁆ ∈ vOf W K S)
    (hZ : Subgroup.center ↥(bar W K) = ⊥) (hS2 : Nat.card ↥(indAut W K S) = 2)
    (hblock : IsGLBlock (⊤ : Subgroup X) K) {a : X} (haS : a ∈ S) (hna : a ∉ kerAct W K S)
    (hΩ : OmegaModelWith Q W K a U₁ U₂) : Concl28aWith Q W K S := by
  obtain ⟨θ, t, hθs, hθW, htr, hQt, htn, hθa, hiso⟩ := hΩ
  obtain ⟨θb, hθb⟩ := OmegaAux.descend θ hθW
  have hθbk : ∀ k : ↥K, θb (toBar W K k) = θ k := fun k => by
    rw [← hθb]; rfl
  have hsurj : Function.Surjective θb := by
    intro y
    obtain ⟨k, rfl⟩ := hθs y
    exact ⟨toBar W K k, hθbk k⟩
  have hinj : Function.Injective θb := by
    rw [← MonoidHom.ker_eq_bot_iff]
    by_contra hker
    have hnc : ¬ θb.ker ≤ Subgroup.center ↥(bar W K) := by
      rw [hZ]; intro hle; exact hker (le_bot_iff.mp hle)
    have htop : θb.ker = ⊤ :=
      InducedAux.eq_top_of_quasisimple_normal hR.quasi.1.commutator_eq_top hR.quasi.2.1 _ hnc
    refine theta_ne_one Q sf θ hiso fun k => ?_
    rw [← hθbk]
    exact MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top _)
  set e : ↥(bar W K) ≃* ↥(StatedOmega Q) := MulEquiv.ofBijective θb ⟨hinj, hsurj⟩ with he
  have hee : ∀ y, e y = θb y := fun _ => rfl
  have hρ : e.toMonoidHom.comp (toBar W K) = θ := MonoidHom.ext fun k => hθbk k
  refine ⟨e, hS2, ⟨t, htn, hQt, htr, ?_⟩, hblock, fun V U hU => ?_⟩
  ·
    show (indAut W K S).map (MulAut.congr e).toMonoidHom = _
    set τ := (StatedOmega Q).normalizerMonoidHom ⟨t, htn⟩ with hτdef
    have hak : ∀ k : ↥K, a * (k : X) * a⁻¹ ∈ K := fun k =>
      (Subgroup.mem_normalizer_iff.mp (h.hN haS) k).1 k.2
    have hτ : (MulAut.congr e) (InducedAux.indHom W K S h.hN ⟨a, haS⟩) = τ := by
      ext y
      obtain ⟨k, rfl⟩ := hθs y
      have hy : e (toBar W K k) = θ k := hθbk k
      have h1 : (MulAut.congr e) (InducedAux.indHom W K S h.hN ⟨a, haS⟩) (θ k) =
          e (InducedAux.indHom W K S h.hN ⟨a, haS⟩ (toBar W K k)) := by
        rw [← hy]
        show e (InducedAux.indHom W K S h.hN ⟨a, haS⟩ (e.symm (e (toBar W K k)))) = _
        rw [MulEquiv.symm_apply_apply]
      rw [h1, indHom_toBar_eq h haS k (hak k), hee, hθbk]
      rw [hθa k ⟨a * k * a⁻¹, hak k⟩ rfl, hτdef, Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hmem : τ ∈ (indAut W K S).map (MulAut.congr e).toMonoidHom :=
      ⟨_, InducedAux.indHom_mem h haS, hτ⟩
    have hne : τ ≠ 1 := by
      intro h1
      rw [← hτ] at h1
      have : InducedAux.indHom W K S h.hN ⟨a, haS⟩ = 1 := (MulAut.congr e).injective (by
        rw [h1, map_one])
      exact hna (InducedAux.mem_kerAct_of_indHom_eq_one h haS this)
    have hcardL : Nat.card ↥((indAut W K S).map (MulAut.congr e).toMonoidHom) = 2 := by
      rw [Subgroup.card_map_of_injective (MulAut.congr e).injective]; exact hS2
    haveI : Finite ↥((indAut W K S).map (MulAut.congr e).toMonoidHom) :=
      Nat.finite_of_card_ne_zero (by rw [hcardL]; norm_num)
    have hle : Subgroup.zpowers τ ≤ (indAut W K S).map (MulAut.congr e).toMonoidHom :=
      Subgroup.zpowers_le.2 hmem
    haveI : Finite ↥(Subgroup.zpowers τ) := Finite.of_injective _ (Subgroup.inclusion_injective hle)
    have hz1 : 1 < Nat.card ↥(Subgroup.zpowers τ) := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      intro hb
      exact hne (Subgroup.zpowers_eq_bot.mp hb)
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardL]; omega)).symm
  · rw [hρ] at *
    exact chief_transfer h hR sf hE θ _ hiso hU

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.OmegaFinal
