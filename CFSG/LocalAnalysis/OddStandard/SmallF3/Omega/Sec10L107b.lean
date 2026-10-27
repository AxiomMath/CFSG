module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10BData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L107bAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Statements2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10_107b_core [Finite G] (h36 : Asc82Lemma36) {t : G} {L S : Subgroup G}
    (hS : Sec3SettingLB G t L) (htC : t ∈ centralizer (L : Set G)) (hBD : Sec10BData t L S) :
    Nonempty (↥(autIn (secCMt t S L) (secA t S L)) ≃* ↥(alternatingGroup (Fin 5))) ∨
      Nonempty (↥(autIn (secCMt t S L) (secA t S L)) ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨hBL, -, -, hAL, hML, φ, ⟨hadd, hinj, himg, hact, hsurj⟩, -, -, hσ⟩ := hBD
  have hBA : secB S L ≤ secA t S L := le_sup_left
  have hcomm : ∀ b ∈ secB S L, b * t = t * b := fun b hb =>
    Subgroup.mem_centralizer_iff.1 htC b (hBL hb)
  have hCN : ∀ m ∈ secCMt t S L, m ∈ normalizer (secA t S L : Set G) := fun m hm => hm.1
  have hCNL : ∀ m ∈ secCMt t S L, m ∈ normalizer (L : Set G) := fun m hm =>
    sec4_mem_normalizer h36 hS m hm.2
  have fwd : ∀ n ∈ secCMt t S L, ∀ b ∈ secB S L, n * b * n⁻¹ ∈ secB S L := by
    intro n hn b hb
    have h1 : n * b * n⁻¹ ∈ secA t S L ⊓ L :=
      ⟨(Subgroup.mem_normalizer_iff.1 (hCN n hn) b).1 (hBA hb),
        (Subgroup.mem_normalizer_iff.1 (hCNL n hn) b).1 (hBL hb)⟩
    rwa [hAL] at h1
  have hCNB : ∀ m ∈ secCMt t S L, m ∈ normalizer (secB S L : Set G) := by
    intro m hm
    refine Subgroup.mem_normalizer_iff.2 fun b => ⟨fwd m hm b, fun h => ?_⟩
    have h2 := fwd m⁻¹ (Subgroup.inv_mem _ hm) _ h
    rwa [show m⁻¹ * (m * b * m⁻¹) * m⁻¹⁻¹ = b by group] at h2
  have hσm : ∀ m ∈ secCMt t S L, ∃ σ : Equiv.Perm (Fin 5),
      ∀ v, IsEvenVec v → m * φ v * m⁻¹ = φ (permVec σ v) := fun m hm =>
    hσ m ⟨hCNL m hm, hCNB m hm⟩
  have huniq : ∀ (m : G) (σ σ' : Equiv.Perm (Fin 5)),
      (∀ v, IsEvenVec v → m * φ v * m⁻¹ = φ (permVec σ v)) →
      (∀ v, IsEvenVec v → m * φ v * m⁻¹ = φ (permVec σ' v)) → σ = σ' := by
    intro m σ σ' h1 h2
    refine permVec_injective_five fun v hv => ?_
    exact hinj _ _ (isEvenVec_permVec σ hv) (isEvenVec_permVec σ' hv)
      ((h1 v hv).symm.trans (h2 v hv))
  let σOf : ↥(secCMt t S L) → Equiv.Perm (Fin 5) := fun m => Classical.choose (hσm m m.2)
  have σOf_spec : ∀ m : ↥(secCMt t S L), ∀ v, IsEvenVec v →
      (m : G) * φ v * (m : G)⁻¹ = φ (permVec (σOf m) v) := fun m =>
    Classical.choose_spec (hσm m m.2)
  let ρ : ↥(secCMt t S L) →* Equiv.Perm (Fin 5) :=
    { toFun := σOf
      map_one' := by
        refine huniq ((1 : ↥(secCMt t S L)) : G) _ 1 (σOf_spec 1) fun v hv => ?_
        simp [permVec_one]
      map_mul' := by
        intro m n
        refine huniq ((m * n : ↥(secCMt t S L)) : G) _ _ (σOf_spec (m * n)) fun v hv => ?_
        calc ((m * n : ↥(secCMt t S L)) : G) * φ v * ((m * n : ↥(secCMt t S L)) : G)⁻¹
            = (m : G) * ((n : G) * φ v * (n : G)⁻¹) * (m : G)⁻¹ := by
              simp only [Subgroup.coe_mul]; group
          _ = (m : G) * φ (permVec (σOf n) v) * (m : G)⁻¹ := by rw [σOf_spec n v hv]
          _ = φ (permVec (σOf m) (permVec (σOf n) v)) :=
              σOf_spec m _ (isEvenVec_permVec _ hv)
          _ = φ (permVec (σOf m * σOf n) v) := by rw [permVec_mul] }
  have hρ : ∀ m : ↥(secCMt t S L), ρ m = σOf m := fun m => rfl
  have hle : secCMt t S L ≤ normalizer (secA t S L : Set G) := fun m hm => hm.1
  let ψ : ↥(secCMt t S L) →* MulAut ↥(secA t S L) :=
    (secA t S L).normalizerMonoidHom.comp (Subgroup.inclusion hle)
  have hψ : ∀ (m : ↥(secCMt t S L)) (a : ↥(secA t S L)),
      ((ψ m a : ↥(secA t S L)) : G) = (m : G) * (a : G) * (m : G)⁻¹ := fun m a => rfl
  have hautIn : autIn (secCMt t S L) (secA t S L) = ψ.range := by
    ext α
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨m, rfl⟩
      exact ⟨Subgroup.inclusion hle m, m.2, rfl⟩
  have hmt : ∀ m : ↥(secCMt t S L), (m : G) * t = t * (m : G) := fun m =>
    (Subgroup.mem_centralizer_iff.1 m.2.2 t rfl).symm
  have hker : ψ.ker = ρ.ker := by
    ext m
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hm
      have hfix : ∀ a : G, a ∈ secA t S L → (m : G) * a * (m : G)⁻¹ = a := by
        intro a ha
        have := congrArg (fun f : MulAut ↥(secA t S L) => ((f ⟨a, ha⟩ : ↥(secA t S L)) : G)) hm
        simpa [hψ] using this
      rw [hρ]
      refine huniq (m : G) _ 1 (σOf_spec m) fun v hv => ?_
      rw [permVec_one]
      exact hfix _ (hBA ((himg _).2 ⟨v, hv, rfl⟩))
    · intro hm
      rw [hρ] at hm
      have hfixφ : ∀ v, IsEvenVec v → (m : G) * φ v * (m : G)⁻¹ = φ v := by
        intro v hv
        rw [σOf_spec m v hv, hm, permVec_one]
      refine MulEquiv.ext fun ⟨a, ha⟩ => Subtype.ext ?_
      rw [hψ]
      obtain ⟨b, hb, i, rfl⟩ := (mem_sup_zpowers_iff_of_commute hcomm).1 ha
      obtain ⟨v, hv, rfl⟩ := (himg b).1 hb
      have hti : (m : G) * t ^ i * (m : G)⁻¹ = t ^ i := by
        rw [mul_inv_eq_iff_eq_mul]
        exact ((Commute.zpow_right (show Commute (m : G) t from hmt m) i)).eq
      calc (m : G) * (φ v * t ^ i) * (m : G)⁻¹
          = ((m : G) * φ v * (m : G)⁻¹) * ((m : G) * t ^ i * (m : G)⁻¹) := by group
        _ = φ v * t ^ i := by rw [hfixφ v hv, hti]
  have hA5 : alternatingGroup (Fin 5) ≤ ρ.range := by
    intro σ hσA
    obtain ⟨h, hh, hspec⟩ := hsurj σ hσA
    have hhM : h ∈ secM t S L ⊓ L := by rw [hML]; exact hh
    have hhC : h ∈ secCMt t S L := by
      refine ⟨hhM.1, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Subgroup.mem_centralizer_iff.1 htC h hhM.2).symm
    refine ⟨⟨h, hhC⟩, ?_⟩
    rw [hρ]
    exact huniq h _ σ (σOf_spec ⟨h, hhC⟩) hspec
  have e1 : ψ.range ≃* ρ.range :=
    (QuotientGroup.quotientKerEquivRange ψ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivRange ρ))
  rcases eq_alt_or_top_five hA5 with h | h
  · exact Or.inl ⟨(MulEquiv.subgroupCongr hautIn).trans (e1.trans (MulEquiv.subgroupCongr h))⟩
  · exact Or.inr ⟨(MulEquiv.subgroupCongr hautIn).trans
      (e1.trans ((MulEquiv.subgroupCongr h).trans Subgroup.topEquiv))⟩

theorem asc82Lemma107b_of (h36 : Asc82Lemma36) (hb : Asc82Basic10) (hB5 : Asc82FactB5) :
    Asc82Lemma107b := by
  intro G _ _ t L S z K1 K2 hctx
  obtain ⟨-, htC, -, -, -, -⟩ := hb G t L S z hctx.toSec10Z
  exact sec10_107b_core h36 hctx.toSec10Z.toSec10Setting.toSec3SettingLB htC
    (sec10BData_of hb hB5 hctx.toSec10Z)

end CFSG.OddStandard.SmallF3.Omega
