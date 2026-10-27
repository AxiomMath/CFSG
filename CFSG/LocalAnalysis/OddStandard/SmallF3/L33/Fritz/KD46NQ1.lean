module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46NO2

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.KD46
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv SD SDKD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {R : Subgroup X}

namespace Inst

variable (I : Inst S)

theorem index_Pre (H : Hyp S R) : (I.Pre H).index = 6 := by
  rw [Pre, index_comap_of_surjective _ (I.blockHom_surjective H)]
  have h1 := transl.card_mul_index
  have hcard : Nat.card transl = 4 := by
    have key : (transl : Set (Perm (Fin 2 × Fin 2))) =
        {σ : Perm (Fin 2 × Fin 2) | ∀ j, σ j = j + σ 0} := rfl
    rw [← SetLike.coe_sort_coe, key, Nat.card_eq_fintype_card]
    rfl
  rw [hcard, Nat.card_perm] at h1
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Nat.factorial] at h1
  omega

theorem factorization_Pre (H : Hyp S R) : (Nat.card (I.Pre H)).factorization 2 = 7 := by
  have h1 := (I.Pre H).card_mul_index
  rw [I.index_Pre H] at h1
  have h2 := I.factorization_normalizer H
  rw [← h1, Nat.factorization_mul Nat.card_pos.ne' (by norm_num), Finsupp.add_apply,
    show (6 : ℕ) = 2 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two] at h2
  have h3 : (3 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  omega

theorem centralizer_le_Pre (H : Hyp S R) :
    (centralizer (I.E : Set X)).subgroupOf (normalizer (I.E : Set X)) ≤ I.Pre H := by
  intro n hn
  show I.blockHom H n ∈ transl
  rw [I.blockHom_eq_one_of_mem H hn]
  exact one_mem _

theorem Q₁_props (H : Hyp S R) {S₁ : Subgroup X} (hS₁N : S₁ ≤ normalizer (I.E : Set X))
    (hS₁ : Nat.card S₁ = 256) (hS₁C : S₁ ⊓ centralizer (I.E : Set X) = I.E) :
    Nat.card (S₁ ⊓ A7Base.oddTwoCoreIn (normalizer (I.E : Set X)) : Subgroup X) = 128 ∧
      (S₁ ⊓ A7Base.oddTwoCoreIn (normalizer (I.E : Set X))) ⊓ centralizer (I.E : Set X) = I.E ∧
      ∀ n ∈ A7Base.oddTwoCoreIn (normalizer (I.E : Set X)),
        ∃ q ∈ S₁ ⊓ A7Base.oddTwoCoreIn (normalizer (I.E : Set X)),
        q⁻¹ * n ∈ centralizer (I.E : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (I.E : Set X) with hN
  set P := I.Pre H with hP
  have hPn := I.Pre_normal H
  set Q₁ := S₁ ⊓ A7Base.oddTwoCoreIn N with hQ₁
  have hQeq : Q₁ = S₁ ⊓ P.map N.subtype := by rw [hQ₁, I.oddTwoCoreIn_eq H]
  have hcardS : Nat.card (S₁.subgroupOf N) = 2 ^ (Nat.card N).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hS₁N).toEquiv, hS₁, I.factorization_normalizer H]
    rfl
  set Syl : Sylow 2 N := Sylow.ofCard _ hcardS with hSyl
  obtain ⟨R, hR⟩ := CFSG.Glauberman.sylow_inf_normal Syl (N := P)
  have hRcard : Nat.card R = 128 := by
    rw [Sylow.card_eq_multiplicity, I.factorization_Pre H]
    rfl
  have hQcard : Nat.card Q₁ = 128 := by
    rw [← hRcard]
    have e1 : Nat.card R = Nat.card (((Syl : Subgroup N) ⊓ P).subgroupOf P) := by rw [← hR]
    rw [e1, Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv, hQeq]
    have e2 : ((Syl : Subgroup N) ⊓ P).map N.subtype = S₁ ⊓ P.map N.subtype := by
      rw [Sylow.coe_ofCard, Subgroup.map_inf _ _ _ (subtype_injective _),
        subgroupOf_map_subtype, inf_of_le_left hS₁N]
    rw [← e2, card_map_of_injective (subtype_injective _)]
  have hES : I.E ≤ S₁ := by
    intro e he
    have : e ∈ S₁ ⊓ centralizer (I.E : Set X) := by rw [hS₁C]; exact he
    exact this.1
  have hQC : Q₁ ⊓ centralizer (I.E : Set X) = I.E := by
    apply le_antisymm
    · intro x hx
      have : x ∈ S₁ ⊓ centralizer (I.E : Set X) := ⟨hx.1.1, hx.2⟩
      rwa [hS₁C] at this
    · refine le_inf (le_inf hES ?_) I.E_le_centralizer
      · intro e he
        rw [I.oddTwoCoreIn_eq H]
        exact ⟨⟨e, I.centralizer_le_normalizer (I.E_le_centralizer he)⟩,
          I.centralizer_le_Pre H (I.E_le_centralizer he), rfl⟩
  refine ⟨hQcard, hQC, ?_⟩
  intro n hn
  set Cn := (centralizer (I.E : Set X)).subgroupOf N with hCn
  have hQN : Q₁ ≤ N := inf_le_left.trans hS₁N
  set ρ : Q₁.subgroupOf N →* N ⧸ Cn := (QuotientGroup.mk' Cn).comp (Q₁.subgroupOf N).subtype
    with hρ
  have hker : Nat.card ρ.ker = 16 := by
    have : ρ.ker.map ((Q₁.subgroupOf N).subtype) =
        (Q₁ ⊓ centralizer (I.E : Set X)).subgroupOf N := by
      ext x
      simp only [mem_map, MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.coe_subtype, mem_subgroupOf, mem_inf]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨x, h1⟩, h2, rfl⟩
    have h1 := congrArg (fun K : Subgroup N => Nat.card K) this
    simp only [card_map_of_injective (subtype_injective _)] at h1
    rw [h1, Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hQN)).toEquiv, hQC, E,
      (KD46.card_E S) I.yi_mem I.yi_sq I.yi_not_mem_B]
  have hrange : Nat.card ρ.range = 8 := by
    have h1 := Subgroup.card_ker_mul_card_range ρ
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe hQN).toEquiv, hQcard] at h1
    omega
  have hPimg : ρ.range ≤ P.map (QuotientGroup.mk' Cn) := by
    rintro _ ⟨q, rfl⟩
    refine ⟨q, ?_, rfl⟩
    have hq : (q : X) ∈ P.map N.subtype := by
      have hq2 : ((q : N) : X) ∈ A7Base.oddTwoCoreIn N := (mem_subgroupOf.mp q.2).2
      rw [I.oddTwoCoreIn_eq H] at hq2
      exact hq2
    obtain ⟨p, hp, hpq⟩ := hq
    have : (q : N) = p := Subtype.ext hpq.symm
    rw [this]
    exact hp
  have hPcard : Nat.card (P.map (QuotientGroup.mk' Cn)) = 8 := by
    have h1 := (P.map (QuotientGroup.mk' Cn)).card_mul_index
    have hk : (QuotientGroup.mk' Cn).ker ≤ P := by
      rw [QuotientGroup.ker_mk']; exact I.centralizer_le_Pre H
    have hidx : (P.map (QuotientGroup.mk' Cn)).index = 6 := by
      have := index_map_eq (H := P) (f := QuotientGroup.mk' Cn) (QuotientGroup.mk'_surjective _) hk
      rw [this, I.index_Pre H]
    rw [hidx, I.card_quot H] at h1
    omega
  have heq : ρ.range = P.map (QuotientGroup.mk' Cn) :=
    Subgroup.eq_of_le_of_card_ge hPimg (by rw [hrange, hPcard])
  rw [I.oddTwoCoreIn_eq H] at hn
  obtain ⟨n', hn', rfl⟩ := hn
  have : QuotientGroup.mk' Cn n' ∈ ρ.range := heq ▸ ⟨n', hn', rfl⟩
  obtain ⟨q, hq⟩ := this
  refine ⟨(q : N), mem_subgroupOf.mp q.2, ?_⟩
  have h2 : QuotientGroup.mk' Cn (q : N) = QuotientGroup.mk' Cn n' := hq
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h2
  exact h2

end Inst

end CFSG.OddStandard.SmallF3.L33.KD.KD46
