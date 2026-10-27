module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812PermSyl
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812PermFix
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812PermReg

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812

open Equiv Equiv.Perm Subgroup

theorem unique_of_sylData {T : Subgroup (Perm (Fin 11))} (hT : SylData T)
    {V : Subgroup (Perm (Fin 11))} (hV : IsPGroup 3 ↥V) (hAlt : V ≤ alternatingGroup (Fin 11))
    (hV1 : V ≠ ⊥) (hn : T ≤ normalizer (V : Set (Perm (Fin 11)))) : V = zpowers c3 := by
  rcases fixDichotomy_of_sylData hT V hV hV1 hn with h | h
  · exact eq_zpowers_c3_of_fix8 hAlt hV1 (fun x hx v hv => (h x).2 hx v hv)
  · exact (not_fix_two hT (fixDichotomy_of_sylData hT) hV hV1 hn h).elim

theorem card_alternatingGroup_eleven : Nat.card (alternatingGroup (Fin 11)) = 19958400 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin, Nat.factorial]

theorem factorization_card_alternatingGroup_eleven :
    (Nat.card (alternatingGroup (Fin 11))).factorization 2 = 7 := by
  rw [card_alternatingGroup_eleven, show (19958400 : ℕ) = 2 ^ 7 * 155925 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

theorem exists_conj_of_card {T T' : Subgroup (Perm (Fin 11))}
    (hT : T ≤ alternatingGroup (Fin 11)) (hT' : T' ≤ alternatingGroup (Fin 11))
    (hc : Nat.card ↥T = 2 ^ 7) (hc' : Nat.card ↥T' = 2 ^ 7) :
    ∃ c : Perm (Fin 11), ∀ x : Perm (Fin 11), x ∈ T' ↔ c⁻¹ * x * c ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := alternatingGroup (Fin 11) with hA
  have hcard : ∀ {K : Subgroup (Perm (Fin 11))}, K ≤ A → Nat.card ↥K = 2 ^ 7 →
      Nat.card ↥(K.subgroupOf A) = 2 ^ (Nat.card ↥A).factorization 2 := by
    intro K hK hK7
    rw [factorization_card_alternatingGroup_eleven, ← hK7]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
  let P : Sylow 2 ↥A := Sylow.ofCard (T.subgroupOf A) (hcard hT hc)
  let P' : Sylow 2 ↥A := Sylow.ofCard (T'.subgroupOf A) (hcard hT' hc')
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥A P P'
  have key : ∀ u : ↥A, u ∈ (P' : Subgroup ↥A) ↔ g⁻¹ * u * g ∈ (P : Subgroup ↥A) := by
    intro u
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨u0, hu0, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hu0
    · intro hm
      exact ⟨g⁻¹ * u * g, hm, by simp [MulAut.conj_apply, mul_assoc]⟩
  refine ⟨(g : Perm (Fin 11)), fun x => ?_⟩
  constructor
  · intro hx
    have := (key ⟨x, hT' hx⟩).1 hx
    simpa [P, Sylow.ofCard, Subgroup.mem_subgroupOf] using this
  · intro hx
    have hxA : x ∈ A := by
      have h1 : (g : Perm (Fin 11)) * ((g : Perm (Fin 11))⁻¹ * x * (g : Perm (Fin 11))) *
          (g : Perm (Fin 11))⁻¹ ∈ A := Subgroup.Normal.conj_mem inferInstance _ (hT hx) _
      simpa [mul_assoc] using h1
    have := (key ⟨x, hxA⟩).2 (by simpa [P, Sylow.ofCard, Subgroup.mem_subgroupOf] using hx)
    simpa [P', Sylow.ofCard, Subgroup.mem_subgroupOf] using this

@[expose] def conjBy (c : Perm (Fin 11)) (V : Subgroup (Perm (Fin 11))) :
    Subgroup (Perm (Fin 11)) :=
  V.comap (MulAut.conj c).toMonoidHom

theorem mem_conjBy {c : Perm (Fin 11)} {V : Subgroup (Perm (Fin 11))} {y : Perm (Fin 11)} :
    y ∈ conjBy c V ↔ c * y * c⁻¹ ∈ V := by
  simp [conjBy, MulAut.conj_apply]

theorem conjBy_eq_zpowers {T T₀ W : Subgroup (Perm (Fin 11))} (hT₀ : SylData T₀) (c : Perm (Fin 11))
    (hc : ∀ x : Perm (Fin 11), x ∈ T ↔ c⁻¹ * x * c ∈ T₀) (hW : IsPGroup 3 ↥W)
    (hWA : W ≤ alternatingGroup (Fin 11)) (hW1 : W ≠ ⊥)
    (hWn : T ≤ normalizer (W : Set (Perm (Fin 11)))) : conjBy c W = zpowers c3 := by
  refine unique_of_sylData hT₀ (hW.comap_of_injective _ (MulAut.conj c).injective) ?_ ?_ ?_
  · intro y hy
    have h1 : c * y * c⁻¹ ∈ alternatingGroup (Fin 11) := hWA (mem_conjBy.1 hy)
    have h2 := Subgroup.Normal.conj_mem
      (inferInstance : (alternatingGroup (Fin 11)).Normal) _ h1 c⁻¹
    simpa [mul_assoc] using h2
  · intro h
    apply hW1
    rw [eq_bot_iff]
    intro v hv
    have hm : c⁻¹ * v * c ∈ conjBy c W := mem_conjBy.2 (by simpa [mul_assoc] using hv)
    rw [h, Subgroup.mem_bot] at hm
    have := congrArg (fun z => c * z * c⁻¹) hm
    simpa [mul_assoc] using this
  · intro t ht
    rw [mem_normalizer_iff]
    intro y
    have hx : c * t * c⁻¹ ∈ T := (hc _).2 (by simpa [mul_assoc] using ht)
    have h1 := mem_normalizer_iff.1 (hWn hx) (c * y * c⁻¹)
    have h2 : c * (t * y * t⁻¹) * c⁻¹ = (c * t * c⁻¹) * (c * y * c⁻¹) * (c * t * c⁻¹)⁻¹ := by group
    rw [mem_conjBy, mem_conjBy, h2]
    exact h1

theorem three_sub_unique {T V V' : Subgroup (Perm (Fin 11))}
    (hTA : T ≤ alternatingGroup (Fin 11)) (hT : Nat.card ↥T = 2 ^ 7)
    (hV : IsPGroup 3 ↥V) (hV' : IsPGroup 3 ↥V')
    (hVA : V ≤ alternatingGroup (Fin 11)) (hV'A : V' ≤ alternatingGroup (Fin 11))
    (h1 : V ≠ ⊥) (h1' : V' ≠ ⊥)
    (hn : T ≤ normalizer (V : Set (Perm (Fin 11))))
    (hn' : T ≤ normalizer (V' : Set (Perm (Fin 11)))) :
    V = V' ∧ Nat.card ↥V = 3 := by
  obtain ⟨T₀, hT₀⟩ := exists_sylData
  have hT₀A : T₀ ≤ alternatingGroup (Fin 11) := fun t ht =>
    Equiv.Perm.mem_alternatingGroup.2 (hT₀.even t ht)
  obtain ⟨c, hc⟩ := exists_conj_of_card hT₀A hTA hT₀.card hT
  have e1 := conjBy_eq_zpowers hT₀ c hc hV hVA h1 hn
  have e2 := conjBy_eq_zpowers hT₀ c hc hV' hV'A h1' hn'
  have hVV : V = V' := by
    ext v
    have a : v ∈ V ↔ c⁻¹ * v * c ∈ conjBy c V := by simp [mem_conjBy, mul_assoc]
    have b : v ∈ V' ↔ c⁻¹ * v * c ∈ conjBy c V' := by simp [mem_conjBy, mul_assoc]
    rw [a, b, e1, e2]
  refine ⟨hVV, ?_⟩
  have hcard : Nat.card ↥V = Nat.card ↥(conjBy c V) :=
    Nat.card_congr
      { toFun := fun v => ⟨c⁻¹ * (v : Perm (Fin 11)) * c, mem_conjBy.2 (by simp [mul_assoc])⟩
        invFun := fun y => ⟨c * (y : Perm (Fin 11)) * c⁻¹, mem_conjBy.1 y.2⟩
        left_inv := fun v => by ext; simp [mul_assoc]
        right_inv := fun y => by ext; simp [mul_assoc] }
  rw [hcard, e1, card_zpowers_c3]

end CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812
