module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NAut

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {T₁ : Subgroup X}

namespace Inst

variable (I : S.Inst)

theorem eq_E_of_le_centralizer {P : Subgroup X} (hP : IsPGroup 2 P) (hEP : I.E ≤ P)
    (hPC : P ≤ centralizer (I.E : Set X)) : P = I.E := by
  have hPt : P ≤ centralizer ({S.t} : Set X) := fun p hp => by
    rw [mem_centralizer_singleton_iff]
    exact ((mem_centralizer_iff.mp (hPC hp)) S.t I.t_mem_E).symm
  obtain ⟨m, -, hmP⟩ := S.data.exists_conj_le_T hP hPt
  set E' : Subgroup X := I.E.map (MulAut.conj m).toMonoidHom with hE'
  have hE'P : E' ≤ P.map (MulAut.conj m).toMonoidHom := Subgroup.map_mono hEP
  have hel : ElemAbelianTwo E' := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, I.comm ha hb]
    · rintro _ ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_pow, I.sq_eq_one ha, map_one]
  have hc16 : Nat.card E' = 16 := by
    rw [hE', card_map_of_injective (MulAut.conj m).injective, E,
      S.card_E I.yi_mem I.yi_sq I.yi_not_mem_B]
  have hle : P.map (MulAut.conj m).toMonoidHom ≤ E' := by
    rintro _ ⟨p, hp, rfl⟩
    have hpT : (MulAut.conj m).toMonoidHom p ∈ S.data.T := hmP ⟨p, hp, rfl⟩
    have hcomm : ∀ e ∈ E',
        (MulAut.conj m).toMonoidHom p * e = e * (MulAut.conj m).toMonoidHom p := by
      rintro _ ⟨e, he, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp (hPC hp)) e he]
    rcases S.eq_E_of_elem (hE'P.trans hmP) hel hc16 with h | h
    · rw [h] at hcomm ⊢
      exact S.mem_E_of_commute (Or.inl rfl) hpT hcomm
    · rw [h] at hcomm ⊢
      exact S.mem_E_of_commute (Or.inr rfl) hpT hcomm
  have hcard : Nat.card P ≤ Nat.card I.E := by
    have h1 := Subgroup.card_le_of_le hle
    rwa [card_map_of_injective (MulAut.conj m).injective, hE',
      card_map_of_injective (MulAut.conj m).injective] at h1
  exact (Subgroup.eq_of_le_of_card_ge hEP hcard).symm

theorem card_quot (H : S.Sec6Hyp T₁) :
    Nat.card (normalizer (I.E : Set X) ⧸
      (centralizer (I.E : Set X)).subgroupOf (normalizer (I.E : Set X))) = 48 := by
  obtain ⟨e⟩ := I.automizer H
  calc _ = Nat.card (Equiv.Perm (Fin 4) × Multiplicative (ZMod 2)) := Nat.card_congr e.toEquiv
    _ = 48 := by rw [Nat.card_prod, Nat.card_perm]; simp [Nat.factorial]

theorem centralizer_le_normalizer : centralizer (I.E : Set X) ≤ normalizer (I.E : Set X) :=
  Subgroup.centralizer_le_normalizer _

theorem E_le_centralizer : I.E ≤ centralizer (I.E : Set X) := fun e he => by
  rw [mem_centralizer_iff]
  intro f hf
  exact I.comm hf he

theorem factorization_centralizer : (Nat.card (centralizer (I.E : Set X))).factorization 2 = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (I.E : Set X) with hC
  have hEC : (I.E.subgroupOf C).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [mem_subgroupOf] at ha ⊢
    have : (g : X) * a * (g : X)⁻¹ = a := by
      rw [← (mem_centralizer_iff.mp g.2) _ ha]
      group
    simpa using this.symm ▸ ha
  have hEp : IsPGroup 2 (I.E.subgroupOf C) := by
    refine IsPGroup.of_card (n := 4) ?_
    rw [Nat.card_congr (subgroupOfEquivOfLe I.E_le_centralizer).toEquiv, E,
      S.card_E I.yi_mem I.yi_sq I.yi_not_mem_B]
    rfl
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 C))
  have hle : I.E.subgroupOf C ≤ (P : Subgroup C) := hEp.le_sylow_of_normal P
  have hPX : (P : Subgroup C).map C.subtype = I.E := by
    refine I.eq_E_of_le_centralizer (P.isPGroup'.map _) ?_ (map_subtype_le _)
    intro e he
    exact ⟨⟨e, I.E_le_centralizer he⟩, hle he, rfl⟩
  have hcard : Nat.card P = 16 := by
    have := congrArg (fun H : Subgroup X => Nat.card H) hPX
    simp only [card_map_of_injective (subtype_injective _)] at this
    rw [this, E, S.card_E I.yi_mem I.yi_sq I.yi_not_mem_B]
  rw [Sylow.card_eq_multiplicity, show (16 : ℕ) = 2 ^ 4 by rfl] at hcard
  exact Nat.pow_right_injective le_rfl hcard

theorem factorization_normalizer (H : S.Sec6Hyp T₁) :
    (Nat.card (normalizer (I.E : Set X))).factorization 2 = 8 := by
  set N := normalizer (I.E : Set X)
  set C := (centralizer (I.E : Set X)).subgroupOf N
  have h1 : Nat.card N = Nat.card C * 48 := by
    rw [← I.card_quot H, ← Subgroup.index, Subgroup.card_mul_index]
  have h2 : Nat.card C = Nat.card (centralizer (I.E : Set X)) :=
    Nat.card_congr (subgroupOfEquivOfLe I.centralizer_le_normalizer).toEquiv
  have hpos : Nat.card (centralizer (I.E : Set X)) ≠ 0 := Nat.card_pos.ne'
  rw [h1, h2, Nat.factorization_mul hpos (by norm_num), Finsupp.add_apply,
    I.factorization_centralizer, show (48 : ℕ) = 2 ^ 4 * 3 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two]
  simp [Nat.factorization_eq_zero_of_not_dvd]

theorem exists_S₁ (H : S.Sec6Hyp T₁) : ∃ S₁ : Subgroup X, IsPGroup 2 S₁ ∧
    S₁ ≤ normalizer (I.E : Set X) ∧
    (∀ Q : Subgroup X, IsPGroup 2 Q → S₁ ≤ Q → Q ≤ normalizer (I.E : Set X) → Q = S₁) ∧
    T₁ ≤ S₁ ∧ Nat.card S₁ = 256 ∧ S₁ ⊓ centralizer (I.E : Set X) = I.E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (I.E : Set X)
  have hT₁N : T₁ ≤ N := I.T₁_le H
  have hT' : IsPGroup 2 (T₁.subgroupOf N) := H.isPGroup.comap_of_injective _ (subtype_injective _)
  obtain ⟨Q, hQ⟩ := hT'.exists_le_sylow
  set S₁ : Subgroup X := (Q : Subgroup N).map N.subtype with hS₁
  have hS₁N : S₁ ≤ N := map_subtype_le _
  have hcard : Nat.card S₁ = 256 := by
    rw [hS₁, card_map_of_injective (subtype_injective _), Sylow.card_eq_multiplicity,
      I.factorization_normalizer H]
    rfl
  have hp : IsPGroup 2 S₁ := Q.isPGroup'.map _
  have hTS : T₁ ≤ S₁ := fun g hg => ⟨⟨g, hT₁N hg⟩, hQ hg, rfl⟩
  refine ⟨S₁, hp, hS₁N, fun Q' hQ' hle hQ'N => ?_, hTS, hcard, ?_⟩
  · refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    obtain ⟨m, hm⟩ := hQ'.exists_card_eq
    have hdvd : Nat.card Q' ∣ Nat.card N := Subgroup.card_dvd_of_le hQ'N
    rw [hm] at hdvd ⊢
    rw [hcard, show (256 : ℕ) = 2 ^ 8 by rfl]
    exact Nat.pow_le_pow_right (by norm_num)
      ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd |>.trans
        (I.factorization_normalizer H).le)
  · have hEle : I.E ≤ S₁ ⊓ centralizer (I.E : Set X) :=
      le_inf ((I.E_le_T.trans H.le).trans hTS) I.E_le_centralizer
    exact I.eq_E_of_le_centralizer (hp.to_le inf_le_left) hEle inf_le_right

end Inst

end A7Base

end CFSG.ComponentClassification.HSFLit
