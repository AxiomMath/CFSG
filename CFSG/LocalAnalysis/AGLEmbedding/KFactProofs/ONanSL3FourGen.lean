module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverThreeLin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGenModel
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGenLift
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGenSL3
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFourCover
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.AGLEmbedding.KFactProofs.CoverThree

open CFSG.Open TauCeti CFSG.ComponentClassification.PSL3Four CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftFour (exists_mulEquiv_specialLinear_four)

namespace SL3FourGen

def centerQuotAut (K : Type*) [Group K] : MulAut K →* MulAut (K ⧸ Subgroup.center K) where
  toFun φ := QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)
  map_one' := by ext ⟨x⟩; rfl
  map_mul' φ ψ := by ext ⟨x⟩; rfl

theorem nonempty_equiv_psl {Q : Type} [Group Q] {d : ValidLieTypeIndex}
    (hd : ∃ q : PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d.1 = .A 2 q)
    (e : Q ≃* (CFSGIndex.lie d).Group) :
    Nonempty (Q ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 2)) := by
  obtain ⟨q, hqp, hqe, hd⟩ := hd
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨p, f, hp, hf⟩ := q
  simp only at hqp hqe
  subst hqp hqe
  exact ⟨e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 ⟨2, 2, hp, hf⟩ hv)⟩

theorem exists_maps {K : Type} [Group K]
    (eQ : K ⧸ Subgroup.center K ≃* ↥S) :
    ∃ (σ : K →* Equiv.Perm (Fin 42)) (φ : MulAut K →* Equiv.Perm (Fin 42)),
      σ.ker ≤ Subgroup.center K ∧ σ.range = S ∧ (∀ e, φ e ∈ R) ∧
      ∀ (e : MulAut K) (k : K), φ e * σ k * (φ e)⁻¹ = σ (e k) := by
  obtain ⟨ε, hε, -⟩ := full_automorphism_action
  let σ : K →* Equiv.Perm (Fin 42) :=
    S.subtype.comp (eQ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)))
  let φ : MulAut K →* Equiv.Perm (Fin 42) :=
    R.subtype.comp (ε.symm.toMonoidHom.comp
      ((MulAut.congr eQ).toMonoidHom.comp (centerQuotAut K)))
  refine ⟨σ, φ, ?_, ?_, fun e => (ε.symm ((MulAut.congr eQ) (centerQuotAut K e))).2, ?_⟩
  · intro k hk
    have h1 : eQ (QuotientGroup.mk k) = 1 := Subtype.ext (MonoidHom.mem_ker.1 hk)
    have h2 : (QuotientGroup.mk k : K ⧸ Subgroup.center K) = 1 :=
      (map_eq_one_iff _ eQ.injective).1 h1
    exact (QuotientGroup.eq_one_iff k).1 h2
  · ext g
    constructor
    · rintro ⟨k, rfl⟩
      exact (eQ (QuotientGroup.mk k)).2
    · intro hg
      obtain ⟨q, hq⟩ := eQ.surjective ⟨g, hg⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨k, congrArg Subtype.val hq⟩
  · intro e k
    set r : ↥R := ε.symm ((MulAut.congr eQ) (centerQuotAut K e)) with hr
    have h1 : ε r = MulAut.congr eQ (centerQuotAut K e) := ε.apply_symm_apply _
    have h2 := hε r (eQ (QuotientGroup.mk k))
    rw [h1] at h2
    have h3 : (MulAut.congr eQ (centerQuotAut K e)) (eQ (QuotientGroup.mk k)) =
        eQ (QuotientGroup.mk (e k)) := by
      simp [MulAut.congr_apply, centerQuotAut]
    rw [h3] at h2
    exact h2.symm

theorem kGenTwoModAb_of_maps
    {K : Type} [Group K] [Finite K] (hK : commutator K = ⊤)
    (hZ : Nat.card (Subgroup.center K) = 3) {k : Type} [Field k] (hk : Nat.card k = 4)
    (ψ : Matrix.SpecialLinearGroup (Fin 3) k ≃* K) (σ : K →* Equiv.Perm (Fin 42))
    (φ : MulAut K →* Equiv.Perm (Fin 42)) (hσ : σ.ker ≤ Subgroup.center K)
    (hrange : σ.range = S) (hφR : ∀ e, φ e ∈ R)
    (hφ : ∀ (e : MulAut K) (k : K), φ e * σ k * (φ e)⁻¹ = σ (e k)) : KGenTwoModAb 3 K := by
  intro E hE hEcard hcomm
  have hEcard' : Nat.card E = 9 := by rw [hEcard]; norm_num
  have hEbot : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hEcard'
    omega
  by_cases hker : ∃ e ∈ E, e ≠ 1 ∧ φ e = 1
  ·
    obtain ⟨e₀, he₀, he₀1, he₀φ⟩ := hker
    refine gen_lift σ hσ φ hφ E hEbot ?_
    have : {s | s ∈ σ.range ∧ ∃ e ∈ E, e ≠ 1 ∧ φ e * s * (φ e)⁻¹ = s} =
        (σ.range : Set (Equiv.Perm (Fin 42))) :=
      Set.ext fun s => ⟨fun h => h.1, fun hs => ⟨hs, e₀, he₀, he₀1, by rw [he₀φ]; simp⟩⟩
    rw [this, Subgroup.closure_eq]
  · push Not at hker
    have hinj : ∀ a ∈ E, ∀ b ∈ E, φ a = φ b → a = b := by
      intro a ha b hb hab
      by_contra hne
      have h1 : a * b⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.1 h)
      exact hker _ (E.mul_mem ha (E.inv_mem hb)) h1 (by rw [map_mul, map_inv, hab, mul_inv_cancel])
    set F : Subgroup (Equiv.Perm (Fin 42)) := E.map φ with hF
    have hFR : F ≤ R := by
      rintro _ ⟨e, -, rfl⟩
      exact hφR e
    have hFcard : Nat.card F = 9 := by
      rw [← hEcard']
      refine (Nat.card_congr (Equiv.ofBijective (fun e : E => (⟨φ e, e, e.2, rfl⟩ : F))
        ⟨fun a b hab => Subtype.ext (hinj a a.2 b b.2 (congrArg Subtype.val hab)), ?_⟩)).symm
      rintro ⟨_, e, he, rfl⟩
      exact ⟨⟨e, he⟩, rfl⟩
    have hFab : IsElemAbelian 3 F := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
      · obtain ⟨_, e₁, he₁, rfl⟩ := a
        obtain ⟨_, e₂, he₂, rfl⟩ := b
        change φ e₁ * φ e₂ = φ e₂ * φ e₁
        rw [← map_mul, ← map_mul]
        exact congrArg φ (congrArg Subtype.val (hE.1.is_comm.comm ⟨e₁, he₁⟩ ⟨e₂, he₂⟩))
      · rintro _ ⟨e, he, rfl⟩
        rw [← map_pow, hE.2 e he, map_one]
    rcases perm_gen hFR hFab hFcard with hFS | hgenF
    ·
      have hin : ∀ e ∈ E, φ e ∈ σ.range := fun e he => hrange ▸ hFS ⟨e, he, rfl⟩
      obtain ⟨P, hP, hPab⟩ := exists_abelian_card_27 hK σ hσ φ hφ E hEcard' hZ hin hcomm
      obtain ⟨x, hx, y, hy, hxy⟩ := exists_noncomm_of_card_27 hk ψ hP
      exact absurd (hPab x hx y hy) hxy
    · refine gen_lift σ hσ φ hφ E hEbot ?_
      have hsub : {s | s ∈ S ∧ ∃ r ∈ F, r ≠ 1 ∧ r * s * r⁻¹ = s} ⊆
          {s | s ∈ σ.range ∧ ∃ e ∈ E, e ≠ 1 ∧ φ e * s * (φ e)⁻¹ = s} := by
        rintro s ⟨hsS, _, ⟨e, he, rfl⟩, hr1, hrs⟩
        refine ⟨hrange ▸ hsS, e, he, fun h => hr1 (by rw [h, map_one]), hrs⟩
      refine le_antisymm ((Subgroup.closure_le _).2 fun s hs => hs.1) ?_
      calc σ.range = S := hrange
        _ = Subgroup.closure {s | s ∈ S ∧ ∃ r ∈ F, r ≠ 1 ∧ r * s * r⁻¹ = s} := hgenF.symm
        _ ≤ _ := Subgroup.closure_mono hsub

end SL3FourGen

theorem sl3FourGenTwoModAb :
    SL3FourGenTwoModAb := by
  intro K _ _ hK hZ3 d hd ⟨e⟩
  have hk4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨eP⟩ := SL3FourGen.nonempty_equiv_psl hd e
  have hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 3 2 2 :=
    ⟨admissible, GaloisField 2 2, inferInstance, inferInstance, by rw [hk4]; norm_num,
      ⟨eP.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3
        (GaloisField 2 2))⟩⟩
  obtain ⟨eQ⟩ := nonempty_equiv_of_stated (K ⧸ Subgroup.center K) hm
  have hodd : Odd (Nat.card (Subgroup.center K)) := by
    rw [hZ3]
    decide
  have hz : Subgroup.center K ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZ3
    omega
  obtain ⟨ψ⟩ := exists_mulEquiv_specialLinear_four hk4 hK.1 hm
    (eP.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 (GaloisField 2 2))) hodd hz
  obtain ⟨σ, φ, hσ, hrange, hφR, hφ⟩ := SL3FourGen.exists_maps eQ
  exact SL3FourGen.kGenTwoModAb_of_maps hK.1 hZ3 hk4 ψ σ φ hσ hrange hφR hφ

end CFSG.AGLEmbedding.KFactProofs.CoverThree
