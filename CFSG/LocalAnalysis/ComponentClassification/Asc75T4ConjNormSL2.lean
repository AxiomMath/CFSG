module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Faithful

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

variable {G : Type} [Group G]

theorem centMod_sup {L O : Subgroup G} {d : G} (hLO : L ≤ normalizer (O : Set G))
    (hdO : d ∈ normalizer (O : Set G)) (hd : CentMod L O d) : CentMod (L ⊔ O) O d := by
  let S : Subgroup G :=
    { carrier := {k | k ∈ normalizer (O : Set G) ∧ d * k * d⁻¹ * k⁻¹ ∈ O}
      mul_mem' := by
        rintro a b ⟨haO, ha⟩ ⟨hbO, hb⟩
        refine ⟨mul_mem haO hbO, ?_⟩
        have h1 := (mem_normalizer_iff.mp haO _).mp hb
        have : d * (a * b) * d⁻¹ * (a * b)⁻¹ =
            (d * a * d⁻¹ * a⁻¹) * (a * (d * b * d⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [this]
        exact mul_mem ha h1
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := by
        rintro a ⟨haO, ha⟩
        refine ⟨inv_mem haO, ?_⟩
        have h1 := (mem_normalizer_iff.mp (inv_mem haO) _).mp (inv_mem ha)
        have : d * a⁻¹ * d⁻¹ * a⁻¹⁻¹ = a⁻¹ * (d * a * d⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [this]
        exact h1 }
  have hLS : L ≤ S := fun l hl => ⟨hLO hl, hd l hl⟩
  have hOS : O ≤ S := fun o ho => ⟨le_normalizer ho,
    mul_mem ((mem_normalizer_iff.mp hdO o).mp ho) (inv_mem ho)⟩
  exact fun k hk => (sup_le hLS hOS hk).2

theorem zpowers_conj_commutator_mem {O : Subgroup G} {t y : G}
    (htO : t ∈ normalizer (O : Set G)) (h : t * y * t⁻¹ * y⁻¹ ∈ O) :
    ∀ s ∈ zpowers t, s * y * s⁻¹ * y⁻¹ ∈ O := by
  let S : Subgroup G :=
    { carrier := {s | s ∈ normalizer (O : Set G) ∧ s * y * s⁻¹ * y⁻¹ ∈ O}
      mul_mem' := by
        rintro a b ⟨haO, ha⟩ ⟨hbO, hb⟩
        refine ⟨mul_mem haO hbO, ?_⟩
        have h1 := (mem_normalizer_iff.mp haO _).mp hb
        have : a * b * y * (a * b)⁻¹ * y⁻¹ =
            (a * (b * y * b⁻¹ * y⁻¹) * a⁻¹) * (a * y * a⁻¹ * y⁻¹) := by group
        rw [this]
        exact mul_mem h1 ha
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := by
        rintro a ⟨haO, ha⟩
        refine ⟨inv_mem haO, ?_⟩
        have h1 := (mem_normalizer_iff.mp (inv_mem haO) _).mp (inv_mem ha)
        have : a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ = a⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [this]
        exact h1 }
  exact fun s hs => ((zpowers_le (H := S)).mpr ⟨htO, h⟩ hs).2

theorem commute_mk_iff {D : Subgroup G} (a b : D) :
    Commute (QuotientGroup.mk' (CFSG.Assembly.oddCore D) a)
        (QuotientGroup.mk' (CFSG.Assembly.oddCore D) b) ↔
      (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ oddCoreIn D := by
  set π := QuotientGroup.mk' (CFSG.Assembly.oddCore D)
  have hiff : π (a * b * a⁻¹ * b⁻¹) = 1 ↔ (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ oddCoreIn D := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨c, hc, hce⟩
      have : c = a * b * a⁻¹ * b⁻¹ := Subtype.ext (by simpa using hce)
      rwa [← this]
  rw [← hiff, map_mul, map_mul, map_mul, map_inv, map_inv]
  constructor
  · intro h
    rw [h.eq]
    group
  · intro h
    calc π a * π b = (π a * π b * (π a)⁻¹ * (π b)⁻¹) * (π b * π a) := by group
      _ = π b * π a := by rw [h, one_mul]

theorem mk_eq_mk_iff {D : Subgroup G} (a b : D) :
    QuotientGroup.mk' (CFSG.Assembly.oddCore D) a =
        QuotientGroup.mk' (CFSG.Assembly.oddCore D) b ↔
      (a : G)⁻¹ * b ∈ oddCoreIn D := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  constructor
  · intro h
    exact ⟨_, h, by simp⟩
  · rintro ⟨c, hc, hce⟩
    have : c = a⁻¹ * b := Subtype.ext (by simpa using hce)
    rwa [← this]

theorem commute_of_mul_commute {M : Type*} [Group M] {a b c : M}
    (hab : Commute (a * b) c) (hb : Commute b c) : Commute a c := by
  rw [commute_iff_eq]
  apply mul_right_cancel (b := b)
  calc a * c * b = a * (b * c) := by rw [mul_assoc, hb.eq]
    _ = a * b * c := by rw [mul_assoc]
    _ = c * (a * b) := hab.eq
    _ = c * a * b := by rw [mul_assoc]

variable [Finite G]

omit [Finite G] in
theorem inf_le_oddCoreIn_or_le_sup {C W : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    {ψ : oUpperTwoPrime C →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    (hψ : Function.Surjective ψ) (hker : ψ.ker = (oddCoreIn C).subgroupOf (oUpperTwoPrime C))
    (hW : oUpperTwoPrime C ≤ normalizer (W : Set G)) :
    W ⊓ oUpperTwoPrime C ≤ oddCoreIn C ∨
      oUpperTwoPrime C ≤ (W ⊓ oUpperTwoPrime C) ⊔ oddCoreIn C := by
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    isSimpleGroup_sl2 hn
  have hP : ((W ⊓ oUpperTwoPrime C).subgroupOf (oUpperTwoPrime C)).Normal :=
    (normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
      ((le_inf hW le_normalizer).trans (inf_normalizer_le_normalizer_inf W (oUpperTwoPrime C)))
  have hPn : (((W ⊓ oUpperTwoPrime C).subgroupOf (oUpperTwoPrime C)).map ψ).Normal :=
    hP.map ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (((W ⊓ oUpperTwoPrime C).subgroupOf (oUpperTwoPrime C)).map ψ) with h | h
  · left
    intro w hw
    have hmem : (⟨w, hw.2⟩ : oUpperTwoPrime C) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      have : ψ ⟨w, hw.2⟩ ∈ ((W ⊓ oUpperTwoPrime C).subgroupOf (oUpperTwoPrime C)).map ψ :=
        ⟨⟨w, hw.2⟩, hw, rfl⟩
      rwa [h, mem_bot] at this
    rw [hker, mem_subgroupOf] at hmem
    exact hmem
  · right
    intro l hl
    obtain ⟨p, hp, hpl⟩ : ψ ⟨l, hl⟩ ∈
        ((W ⊓ oUpperTwoPrime C).subgroupOf (oUpperTwoPrime C)).map ψ := h ▸ mem_top _
    have hk : p⁻¹ * ⟨l, hl⟩ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hpl, inv_mul_cancel]
    rw [hker, mem_subgroupOf] at hk
    have : l = (p : G) * ((p⁻¹ * ⟨l, hl⟩ : oUpperTwoPrime C) : G) := by simp
    rw [this]
    exact mul_mem (mem_sup_left (mem_subgroupOf.mp hp)) (mem_sup_right hk)

theorem hasFourGroup_inf_of_le_sup {C W : Subgroup G} (h4 : HasFourGroup C)
    (h : oUpperTwoPrime C ≤ (W ⊓ oUpperTwoPrime C) ⊔ oddCoreIn C) :
    HasFourGroup (W ⊓ oUpperTwoPrime C) := by
  obtain ⟨E, hEC, hE, hE4⟩ := h4
  have hEL : E ≤ oUpperTwoPrime C := fun e he =>
    subset_closure ⟨hEC he, 1, by simpa using hE e he⟩
  have hCO : C ≤ normalizer (oddCoreIn C : Set G) := normalIn_le_normalizer (oddCoreIn_normalIn C)
  exact HasFourGroup.of_le_sup (odd_card_oddCoreIn C)
    ((inf_le_right.trans (oUpperTwoPrime_le C)).trans hCO)
    ((hEL.trans (oUpperTwoPrime_le C)).trans hCO) (hEL.trans h) hE hE4

theorem hasFourGroup_of_le_sup {J C : Subgroup G} (h4 : HasFourGroup (twoPrimeLayerIn J))
    (hCK : C ≤ twoPrimeLayerIn J) (hKC : twoPrimeLayerIn J ≤ C ⊔ oddCoreIn J) :
    HasFourGroup C := by
  obtain ⟨E, hEK, hE, hE4⟩ := h4
  have hKO : twoPrimeLayerIn J ≤ normalizer (oddCoreIn J : Set G) :=
    (twoPrimeLayerIn_le J).trans (normalIn_le_normalizer (oddCoreIn_normalIn J))
  exact HasFourGroup.of_le_sup (odd_card_oddCoreIn J) (hCK.trans hKO) (hEK.trans hKO)
    (hEK.trans hKC) hE hE4

theorem exists_two_element_not_centMod {Q : Subgroup G}
    (h4 : HasFourGroup (twoPrimeLayerIn Q)) :
    ∃ x ∈ twoPrimeLayerIn Q, (∃ k : ℕ, x ^ (2 ^ k) = 1) ∧
      ¬ CentMod (twoPrimeLayerIn Q) (oddCoreIn Q) x := by
  set K := twoPrimeLayerIn Q
  set L := oUpperTwoPrime K
  by_contra hcon
  push Not at hcon
  have hKO : K ≤ normalizer (oddCoreIn Q : Set G) :=
    (twoPrimeLayerIn_le Q).trans (normalIn_le_normalizer (oddCoreIn_normalIn Q))
  have hL : ∀ l ∈ L, CentMod K (oddCoreIn Q) l := by
    intro l hl
    induction hl using closure_induction with
    | mem x hx => exact hcon x hx.1 hx.2
    | one => exact CentMod.one
    | mul x y hx _ ihx ihy => exact ihx.mul ihy (hKO (oUpperTwoPrime_le K hx))
    | inv x hx ihx => exact ihx.inv (hKO (oUpperTwoPrime_le K hx))
  have hcomm : ⁅L, L⁆ ≤ oddCoreIn Q := commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact hL a ha b (oUpperTwoPrime_le K hb)
  rw [commutator_oUpperTwoPrime_eq (isSemisimpleQ_twoPrimeLayerIn Q)] at hcomm
  obtain ⟨E, hEK, hE, hE4⟩ := h4
  have hEL : E ≤ L := fun e he => subset_closure ⟨hEK he, 1, by simpa using hE e he⟩
  have h4dvd : 4 ∣ Nat.card (oddCoreIn Q) := hE4 ▸ card_dvd_of_le (hEL.trans hcomm)
  exact (odd_card_oddCoreIn Q).not_two_dvd_nat ((by norm_num : 2 ∣ 4).trans h4dvd)

end CFSG.ComponentClassification.Asc75T4
