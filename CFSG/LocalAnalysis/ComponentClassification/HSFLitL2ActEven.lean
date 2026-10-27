module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2ActEvenModel
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2ActAssembly

public section

namespace CFSG.ComponentClassification.HSFLit.L2Act

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer GorensteinWalter AutL2Facts
open CFSG.ComponentClassification.CatFactsSmall

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {F : Type} [Field F] [Finite F]

theorem exists_l2Data_of_even (h : Config t L) (e : L ⧸ pPrimeCore 2 L ≃* PSL2 F)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F)) (hq4 : Nat.card F % 4 = 1)
    (h3 : twoVal F = 3) (T : Sylow 2 ↥(centralizer ({t} : Set X))) :
    ∃ A : L2Data t L, A.syl = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (L : Set X) with hN
  set Φ := l2Act L e with hΦ
  set R := Config.sylowIn T ⊓ L with hR
  have hTN : Config.sylowIn T ≤ N := (Config.sylowIn_le T).trans h.le_normalizer
  set π : L →* PSL2 F := e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 L)) with hπ
  have hRp : IsPGroup 2 ((R.subgroupOf L).map π) :=
    (((Config.isPGroup_sylowIn T).to_inf_left).comap_of_injective L.subtype
      (subtype_injective L)).map π
  obtain ⟨S', hS'⟩ := hRp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (PSL2 F) (stdSylow F hodd hsq hq4) S'
  set Φ' : N →* PGammaL2 F := (MulAut.conj (incl F c)⁻¹).toMonoidHom.comp Φ with hΦ'
  have hΦ'1 : ∀ g, Φ' g = 1 ↔ (g : X) ∈ coreActionKernel L := by
    intro g
    rw [hΦ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact l2Act_eq_one_iff e g
  have hΦ'R : ∀ g : N, (g : X) ∈ R → Φ' g ∈ rStd F := by
    intro g hg
    have h1 : Φ g = incl F (π ⟨g, hg.2⟩) := l2Act_of_mem e ⟨g, hg.2⟩ g.2
    have h2 : π ⟨g, hg.2⟩ ∈ (S' : Subgroup (PSL2 F)) := hS' ⟨⟨g, hg.2⟩, hg, rfl⟩
    rw [← hc, mem_smul_sylow_iff, coe_stdSylow] at h2
    have h3' : Φ' g = (incl F c)⁻¹ * Φ g * incl F c := by
      rw [hΦ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine ⟨_, h2, ?_⟩
    rw [map_mul, map_mul, map_inv, h3', h1]
  have hRN : R.subgroupOf N ≤ (Config.sylowIn T).subgroupOf N := fun x hx => hx.1
  have hinj : Function.Injective (Φ'.comp (R.subgroupOf N).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hΦ'1] at hx
    have h1 : ((x : N) : X) ∈ (Config.sylowIn T ⊓ coreActionKernel L ⊓ L : Subgroup X) :=
      ⟨⟨x.2.1, hx⟩, x.2.2⟩
    rw [h.inf_kernel_inf_L T, mem_bot] at h1
    rw [mem_bot]
    exact Subtype.ext (Subtype.ext h1)
  have hcardR : Nat.card ((R.subgroupOf N).map Φ') = 8 := by
    rw [← Subgroup.range_subtype (R.subgroupOf N), ← MonoidHom.range_comp,
      ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hTN : R ≤ N)).toEquiv]
    exact h.card_inf_L T
  have hRstd : (R.subgroupOf N).map Φ' = rStd F := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact hΦ'R x hx
    · rw [hcardR, rStd, card_map_of_injective (incl_injective F), card_stdT hodd hsq, h3]
      norm_num
  set Q := ((Config.sylowIn T).subgroupOf N).map Φ' with hQ
  have hQp : IsPGroup 2 Q :=
    ((Config.isPGroup_sylowIn T).comap_of_injective N.subtype (subtype_injective _)).map Φ'
  have hRQ : rStd F ≤ Q := by
    rw [← hRstd]
    exact Subgroup.map_mono hRN
  have hQS : Q ≤ sylS0 F := le_sylS0_of hodd hsq hq4 (by omega) hQp hRQ
  have hTP : ∀ g : N, (g : X) ∈ Config.sylowIn T → Φ' g ∈ sylS0 F :=
    fun g hg => hQS ⟨g, hg, rfl⟩
  have hjR : ∀ (g : N) (hg : (g : X) ∈ Config.sylowIn T ⊓ L), j8 h3 ⟨Φ' g, hTP g hg.1⟩ ∈ R8 := by
    intro g hg
    obtain ⟨c', hc', ε, hce⟩ := (mem_map_stdT_iff hsq _).mp (hΦ'R g hg)
    have hx : (⟨Φ' g, hTP g hg.1⟩ : sylS0 F) = ⟨nm F c' ε 1, hce ▸ hTP g hg.1⟩ :=
      Subtype.ext hce
    rw [hx]
    exact j8_mem_R8 h3 hc' ε _
  exact exists_l2Data_of_embedding h T Φ' hΦ'1 (pairHom (deltaPGL hodd) (fbitΓ h3)) (sylS0 F)
    (j8 h3) (j8_injective hp hp2 hF h3) (j8_mem_H8 h3) (pairHom_j8 hodd hsq h3) hTP hjR

end CFSG.ComponentClassification.HSFLit.L2Act
