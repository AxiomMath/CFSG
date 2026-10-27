module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuInvol
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuPlane

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII
open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ

namespace RuQCode

@[expose] def tvOf (t : Fin 8) : List Lin8 :=
  glList.filter fun r => r != linId &&
    all8.all fun s => (linApply r s ^^^ s == 0) || (linApply r s ^^^ s == t)

@[expose] def jlOf (t : Fin 8) : List Nat :=
  (List.range 256).filter fun n => (ppOf t).all fun m => bC m n == 0 || bC m n == t

@[expose] def jCheck (t : Fin 8) : Bool :=
  (tvOf t).length == 3 && (jlOf t).length == 64 && (tvOf t).all fun r => invList.contains r &&
    (let A := adMat r
     (ppOf t).all (fun m => maskApply A m == m) &&
       (jlOf t).all fun n => (0 :: ppOf t).contains (maskApply A n ^^^ n))

theorem jCheck_eq : ∀ t : Fin 8, t ≠ 0 → jCheck t = true := by
  intro t ht
  fin_cases t
  · exact absurd rfl ht
  all_goals decide +kernel

theorem mem_tvOf {t : Fin 8} {r : Lin8} : r ∈ tvOf t ↔ r ∈ glList ∧ r ≠ linId ∧
    ∀ s : Fin 8, linApply r s ^^^ s = 0 ∨ linApply r s ^^^ s = t := by
  simp [tvOf, all8]

theorem mem_jlOf {t : Fin 8} {n : Nat} :
    n ∈ jlOf t ↔ n < 256 ∧ ∀ m ∈ ppOf t, bC m n = 0 ∨ bC m n = t := by
  simp [jlOf]

theorem jCheck_parts {t : Fin 8} (ht : t ≠ 0) : (tvOf t).length = 3 ∧ (jlOf t).length = 64 ∧
    ∀ r ∈ tvOf t, r ∈ invList ∧ (∀ m ∈ ppOf t, maskApply (adMat r) m = m) ∧
      ∀ n ∈ jlOf t, maskApply (adMat r) n ^^^ n ∈ 0 :: ppOf t := by
  have h := jCheck_eq t ht
  simp only [jCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, fun r hr => ⟨(h3 r hr).1, (h3 r hr).2.1, (h3 r hr).2.2⟩⟩

theorem jlOf_nodup (t : Fin 8) : (jlOf t).Nodup :=
  List.Nodup.filter _ List.nodup_range

theorem tvOf_nodup (t : Fin 8) : (linId :: tvOf t).Nodup := by
  refine List.nodup_cons.mpr ⟨fun h => (mem_tvOf.mp h).2.1 rfl, ?_⟩
  exact List.Nodup.filter _ glList_nodup

end RuQCode

namespace Sec3.SzR.MaskCoords

variable {G : Type} [Group G] [Finite G] {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8}
  (hM : MaskCoords L T R μ ν)
include hM

omit [Finite G] in
theorem code_mem_tvOf {f : G} {g : G} {r : Lin8} (hr : r ∈ glList)
    (hrA : ∀ b ∈ gmsA L T, ν (g * b * g⁻¹) = linApply r (ν b))
    (hg : ∀ b ∈ gmsA L T, g * b * g⁻¹ * b⁻¹ = 1 ∨ g * b * g⁻¹ * b⁻¹ = f)
    (hgA : ∀ b ∈ gmsA L T, g * b * g⁻¹ ∈ gmsA L T) :
    r ∈ linId :: RuQCode.tvOf (ν f) := by
  have key : ∀ s : Fin 8, linApply r s ^^^ s = 0 ∨ linApply r s ^^^ s = ν f := by
    intro s
    obtain ⟨b, hb, rfl⟩ := hM.ν_surj s
    have h1 := hM.ν_mul _ (hgA b hb) _ (inv_mem hb)
    rw [hrA b hb, hM.ν_inv hb] at h1
    rcases hg b hb with h | h
    · left
      rw [← h1, h, hM.ν_one]
    · right
      rw [← h1, h]
  by_cases h1 : r = linId
  · rw [h1]
    exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (RuQCode.mem_tvOf.mpr ⟨hr, h1, key⟩)


omit [Finite G] in
theorem code_unique {g : G} {r r' : Lin8}
    (h : ∀ b ∈ gmsA L T, ν (g * b * g⁻¹) = linApply r (ν b))
    (h' : ∀ b ∈ gmsA L T, ν (g * b * g⁻¹) = linApply r' (ν b)) : r = r' := by
  refine RuQCode.lin8_ext fun t => ?_
  obtain ⟨b, hb, rfl⟩ := hM.ν_surj t
  rw [← h b hb, ← h' b hb]

omit [Finite G] in
theorem mem_of_code_eq_linId
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R) {g : G}
    (hg : g ∈ normalizer (R : Set G)) (h : ∀ b ∈ gmsA L T, ν (g * b * g⁻¹) = linApply linId (ν b)) :
    g ∈ R := by
  rw [← hNC]
  refine mem_inf.mpr ⟨hg, mem_centralizer_iff.mpr fun b hb => ?_⟩
  have h1 := hM.eq_of_ν_eq (hM.normA g hg b hb) hb (by rw [h b hb, RuSimCode.linApply_linId])
  calc b * g = (g * b * g⁻¹) * g := by rw [h1]
    _ = g * b := by group


theorem exists_mem_sylow_code_eq (hRp : IsPGroup 2 R)
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168) {S : Subgroup G}
    (hSN : IsSylowOf 2 S (normalizer (R : Set G))) {f : G} (hfA : f ∈ gmsA L T) (hf1 : f ≠ 1)
    (hfS : ∀ s ∈ S, s * f * s⁻¹ = f) {r : Lin8} (hr : r ∈ RuQCode.tvOf (ν f)) :
    ∃ g ∈ S, (∀ b ∈ gmsA L T, ν (g * b * g⁻¹) = linApply r (ν b)) ∧
      ∀ x ∈ R, μ (g * x * g⁻¹) = maskApply (adMat r) (μ x) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht : ν f ≠ 0 := fun h => hf1 (hM.ν_inj f hfA h)
  have hparts := RuQCode.jCheck_parts ht
  have hf2 : f * f = 1 := by
    have := (hM.sq_eq_one_iff (hM.le hfA)).mpr (by rw [(hM.ker _ (hM.le hfA)).mpr hfA]; rfl)
    rwa [pow_two] at this
  have hfix : ∀ h ∈ normalizer (R : Set G), (∀ b ∈ gmsA L T,
      h * b * h⁻¹ * b⁻¹ = 1 ∨ h * b * h⁻¹ * b⁻¹ = f) → h * f * h⁻¹ = f := by
    intro h _ hc
    rcases hc f hfA with h1 | h1
    · exact mul_inv_eq_one.mp h1
    · exfalso
      have h2 : h * f * h⁻¹ = 1 := by
        calc h * f * h⁻¹ = (h * f * h⁻¹ * f⁻¹) * f := by group
          _ = f * f := by rw [h1]
          _ = 1 := hf2
      apply hf1
      calc f = h⁻¹ * (h * f * h⁻¹) * h := by group
        _ = 1 := by rw [h2]; group
  have hcomb : ∀ c c' : G, (c = 1 ∨ c = f) → (c' = 1 ∨ c' = f) → (c * c' = 1 ∨ c * c' = f) := by
    intro c c' hc hc'
    rcases hc with hc | hc <;> rcases hc' with hc' | hc' <;> rw [hc, hc']
    · exact Or.inl (mul_one 1)
    · exact Or.inr (one_mul f)
    · exact Or.inr (mul_one f)
    · exact Or.inl hf2
  let V₀ : Subgroup G :=
    { carrier := {h | h ∈ normalizer (R : Set G) ∧ ∀ b ∈ gmsA L T,
        h * b * h⁻¹ * b⁻¹ = 1 ∨ h * b * h⁻¹ * b⁻¹ = f}
      mul_mem' := by
        rintro h h' ⟨hh, hc⟩ ⟨hh', hc'⟩
        refine ⟨mul_mem hh hh', fun b hb => ?_⟩
        have hb' := hM.normA h' hh' b hb
        have e : h * h' * b * (h * h')⁻¹ * b⁻¹ =
            (h * (h' * b * h'⁻¹ * b⁻¹) * h⁻¹) * (h * b * h⁻¹ * b⁻¹) := by group
        rw [e]
        rcases hc' b hb with h1 | h1
        · rw [h1, mul_one, mul_inv_cancel, one_mul]
          exact hc b hb
        · rw [h1, hfix h hh hc]
          exact hcomb _ _ (Or.inr rfl) (hc b hb)
      one_mem' := ⟨one_mem _, fun b _ => Or.inl (by group)⟩
      inv_mem' := by
        rintro h ⟨hh, hc⟩
        refine ⟨inv_mem hh, fun b hb => ?_⟩
        have hb' : h⁻¹ * b * h ∈ gmsA L T := by
          have := hM.normA h⁻¹ (inv_mem hh) b hb
          simpa using this
        have e : h⁻¹ * b * h⁻¹⁻¹ * b⁻¹ =
            (h * (h⁻¹ * b * h) * h⁻¹ * (h⁻¹ * b * h)⁻¹)⁻¹ := by group
        rw [e]
        rcases hc _ hb' with h1 | h1
        · left
          rw [h1, inv_one]
        · right
          rw [h1, inv_eq_of_mul_eq_one_right hf2] }
  have hV₀ : ∀ h, h ∈ V₀ ↔ h ∈ normalizer (R : Set G) ∧ ∀ b ∈ gmsA L T,
      h * b * h⁻¹ * b⁻¹ = 1 ∨ h * b * h⁻¹ * b⁻¹ = f := fun h => Iff.rfl
  have hV₀p : IsPGroup 2 V₀ := by
    rintro ⟨h, hh⟩
    obtain ⟨hhN, hc⟩ := (hV₀ h).mp hh
    obtain ⟨r', hr', hrA', -⟩ := hM.act h hhN
    have hcode := hM.code_mem_tvOf hr' hrA' hc (hM.normA h hhN)
    have hsq : h ^ 2 ∈ R := by
      refine hM.mem_of_code_eq_linId hNC (pow_mem hhN 2) fun b hb => ?_
      have hb1 := hM.normA h hhN b hb
      rw [pow_two, show h * h * b * (h * h)⁻¹ = h * (h * b * h⁻¹) * h⁻¹ by group, hrA' _ hb1,
        hrA' b hb, ← RuSimCode.linApply_linComp]
      rcases List.mem_cons.mp hcode with h1 | h1
      · rw [h1]
        simp only [linId, linComp, RuSimCode.linApply_one, RuSimCode.linApply_two,
          RuSimCode.linApply_four]
      · have hinv := (hparts.2.2 r' h1).1
        simp only [invList, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq,
          beq_iff_eq] at hinv
        rw [hinv.2.2]
    obtain ⟨k, hk⟩ := hRp ⟨h ^ 2, hsq⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' : (h ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [pow_succ', pow_mul, hk']
  have hSV₀ : S ≤ normalizer (V₀ : Set G) := by
    intro s hs
    have hsN := hSN.le hs
    refine mem_normalizer_iff.mpr fun h => ⟨fun hh => ?_, fun hh => ?_⟩
    · obtain ⟨hhN, hc⟩ := (hV₀ h).mp hh
      refine (hV₀ _).mpr ⟨mul_mem (mul_mem hsN hhN) (inv_mem hsN), fun b hb => ?_⟩
      have hb' : s⁻¹ * b * s ∈ gmsA L T := by
        have := hM.normA s⁻¹ (inv_mem hsN) b hb
        simpa using this
      have e : s * h * s⁻¹ * b * (s * h * s⁻¹)⁻¹ * b⁻¹ =
          s * (h * (s⁻¹ * b * s) * h⁻¹ * (s⁻¹ * b * s)⁻¹) * s⁻¹ := by group
      rw [e]
      rcases hc _ hb' with h1 | h1
      · left; rw [h1]; group
      · right; rw [h1, hfS s hs]
    · obtain ⟨hhN, hc⟩ := (hV₀ _).mp hh
      have hhN' : h ∈ normalizer (R : Set G) := by
        have := mul_mem (mul_mem (inv_mem hsN) hhN) hsN
        simpa [mul_assoc] using this
      refine (hV₀ h).mpr ⟨hhN', fun b hb => ?_⟩
      have hb' : s * b * s⁻¹ ∈ gmsA L T := hM.normA s hsN b hb
      have e : h * b * h⁻¹ * b⁻¹ =
          s⁻¹ * (s * h * s⁻¹ * (s * b * s⁻¹) * (s * h * s⁻¹)⁻¹ * (s * b * s⁻¹)⁻¹) * s := by group
      rw [e]
      have hsf : s⁻¹ * f * s = f := by
        calc s⁻¹ * f * s = s⁻¹ * (s * f * s⁻¹) * s := by rw [hfS s hs]
          _ = f := by group
      rcases hc _ hb' with h1 | h1
      · left; rw [h1]; group
      · right; rw [h1, hsf]
  have hle : V₀ ≤ S := by
    have hP : IsPGroup 2 (S ⊔ V₀ : Subgroup G) := hSN.isPGroup.to_sup_of_normal_right' hV₀p hSV₀
    have heq := hSN.eq_of_le le_sup_left (sup_le hSN.le fun h hh => ((hV₀ h).mp hh).1) hP
    exact le_sup_right.trans heq.le
  obtain ⟨g, hgN, hgA, hgR⟩ := hM.exists_code_eq hNC hidx (RuQCode.mem_tvOf.mp hr).1
  refine ⟨g, hle ((hV₀ g).mpr ⟨hgN, fun b hb => ?_⟩), hgA, hgR⟩
  have h1 := hM.ν_mul _ (hM.normA g hgN b hb) _ (inv_mem hb)
  rw [hgA b hb, hM.ν_inv hb] at h1
  rcases (RuQCode.mem_tvOf.mp hr).2.2 (ν b) with h2 | h2
  · left
    exact hM.ν_inj _ (mul_mem (hM.normA g hgN b hb) (inv_mem hb)) (h1.trans h2)
  · right
    exact hM.eq_of_ν_eq (mul_mem (hM.normA g hgN b hb) (inv_mem hb)) hfA (h1.trans h2)


omit [Finite G] hM in
theorem exists_J {S X : Subgroup G} {f : G} (hf2 : f * f = 1) (hfS : ∀ s ∈ S, s * f * s⁻¹ = f)
    (hSX : S ≤ normalizer (X : Set G)) :
    ∃ J : Subgroup G, ∀ v, v ∈ J ↔ v ∈ S ∧ ∀ x ∈ X,
      v * x * v⁻¹ * x⁻¹ = 1 ∨ v * x * v⁻¹ * x⁻¹ = f := by
  have hcomb : ∀ c c' : G, (c = 1 ∨ c = f) → (c' = 1 ∨ c' = f) → (c * c' = 1 ∨ c * c' = f) := by
    intro c c' hc hc'
    rcases hc with hc | hc <;> rcases hc' with hc' | hc' <;> rw [hc, hc']
    · exact Or.inl (mul_one 1)
    · exact Or.inr (one_mul f)
    · exact Or.inr (mul_one f)
    · exact Or.inl hf2
  refine ⟨{ carrier := {v | v ∈ S ∧ ∀ x ∈ X, v * x * v⁻¹ * x⁻¹ = 1 ∨ v * x * v⁻¹ * x⁻¹ = f}
            mul_mem' := ?_
            one_mem' := ⟨one_mem _, fun x _ => Or.inl (by group)⟩
            inv_mem' := ?_ }, fun v => Iff.rfl⟩
  · rintro v v' ⟨hv, hc⟩ ⟨hv', hc'⟩
    refine ⟨mul_mem hv hv', fun x hx => ?_⟩
    have hx' : v' * x * v'⁻¹ ∈ X := (mem_normalizer_iff.mp (hSX hv') x).mp hx
    have e : v * v' * x * (v * v')⁻¹ * x⁻¹ =
        (v * (v' * x * v'⁻¹ * x⁻¹) * v⁻¹) * (v * x * v⁻¹ * x⁻¹) := by group
    rw [e]
    rcases hc' x hx with h1 | h1
    · rw [h1, mul_one, mul_inv_cancel, one_mul]
      exact hc x hx
    · rw [h1, hfS v hv]
      exact hcomb _ _ (Or.inr rfl) (hc x hx)
  · rintro v ⟨hv, hc⟩
    refine ⟨inv_mem hv, fun x hx => ?_⟩
    have hx' : v⁻¹ * x * v ∈ X := by
      have := (mem_normalizer_iff.mp (hSX (inv_mem hv)) x).mp hx
      simpa using this
    have e : v⁻¹ * x * v⁻¹⁻¹ * x⁻¹ = (v * (v⁻¹ * x * v) * v⁻¹ * (v⁻¹ * x * v)⁻¹)⁻¹ := by group
    rw [e]
    rcases hc _ hx' with h1 | h1
    · left
      rw [h1, inv_one]
    · right
      rw [h1, inv_eq_of_mul_eq_one_right hf2]

theorem J_props (hRp : IsPGroup 2 R)
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168) {S : Subgroup G}
    (hSN : IsSylowOf 2 S (normalizer (R : Set G))) (hRS : R ≤ S) {f : G} (hfA : f ∈ gmsA L T)
    (hf1 : f ≠ 1) (hfS : ∀ s ∈ S, s * f * s⁻¹ = f)
    (h210 : ∀ g ∈ S, g ∉ R → g ^ 2 ∈ R → ∃ y ∈ S, y ^ 2 = 1 ∧ g⁻¹ * y ∈ R)
    {X : Subgroup G} (hX : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f))
    {J : Subgroup G} (hJ : ∀ v, v ∈ J ↔ v ∈ S ∧ ∀ x ∈ X,
      v * x * v⁻¹ * x⁻¹ = 1 ∨ v * x * v⁻¹ * x⁻¹ = f) :
    Nat.card J = 2 ^ 11 ∧ X ≤ J ∧ J ≤ S ∧ ∀ v ∈ J, v ^ 2 ∈ X := by
  classical
  have ht : ν f ≠ 0 := fun h => hf1 (hM.ν_inj f hfA h)
  have hparts := RuQCode.jCheck_parts ht
  have hXel := hM.isElemAbelian_plane hX
  have hXR : X ≤ R := plane_le hX
  have hJS : J ≤ S := fun v hv => ((hJ v).mp hv).1
  have hSN' : ∀ s ∈ S, s ∈ normalizer (R : Set G) := fun s hs => hSN.le hs
  have hXJ : X ≤ J := by
    intro x hx
    refine (hJ x).mpr ⟨hRS (hXR hx), fun x' hx' => Or.inl ?_⟩
    have h1 := congrArg Subtype.val (hXel.1.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩)
    simp only [Subgroup.coe_mul] at h1
    rw [h1]
    group
  choose! rOf hrGL hrA hrR using hM.act
  have hcodeJ : ∀ v ∈ J, rOf v ∈ linId :: RuQCode.tvOf (ν f) := by
    intro v hv
    have hvN := hSN' v (hJS hv)
    refine hM.code_mem_tvOf (hrGL v hvN) (hrA v hvN) (fun b hb => ?_) (hM.normA v hvN)
    exact ((hJ v).mp hv).2 b (hM.gmsA_le_plane hX hb)
  have hlift : ∀ r ∈ RuQCode.tvOf (ν f), ∃ y ∈ J, y ^ 2 = 1 ∧ rOf y = r := by
    intro r hr
    obtain ⟨hrinv, hrfix, -⟩ := hparts.2.2 r hr
    obtain ⟨g, hgS, hgA, hgR⟩ :=
      hM.exists_mem_sylow_code_eq hRp hNC hidx hSN hfA hf1 hfS hr
    have hgN := hSN' g hgS
    have hrne : r ≠ linId := (RuQCode.mem_tvOf.mp hr).2.1
    have hgR' : g ∉ R := by
      intro hg
      apply hrne
      refine hM.code_unique hgA fun b hb => ?_
      rw [RuSimCode.linApply_linId, hM.central g hg b hb]
      congr 1
      group
    have hrr : linComp r r = linId := by
      simp only [invList, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
        at hrinv
      exact hrinv.2.2
    have hg2 : g ^ 2 ∈ R := by
      refine hM.mem_of_code_eq_linId hNC (pow_mem hgN 2) fun b hb => ?_
      rw [pow_two, show g * g * b * (g * g)⁻¹ = g * (g * b * g⁻¹) * g⁻¹ by group,
        hgA _ (hM.normA g hgN b hb), hgA b hb, ← RuSimCode.linApply_linComp, hrr]
    obtain ⟨y, hyS, hy2, hgy⟩ := h210 g hgS hgR' hg2
    have hyN := hSN' y hyS
    have hyA : ∀ b ∈ gmsA L T, ν (y * b * y⁻¹) = linApply r (ν b) := by
      intro b hb
      have e : y * b * y⁻¹ = g * ((g⁻¹ * y) * b * (g⁻¹ * y)⁻¹) * g⁻¹ := by group
      rw [e, show (g⁻¹ * y) * b * (g⁻¹ * y)⁻¹ = b by
        rw [hM.central _ hgy b hb]; group, hgA b hb]
    have hyR : ∀ x ∈ R, μ (y * x * y⁻¹) = maskApply (adMat r) (μ x) := by
      intro x hx
      have e : y * x * y⁻¹ = g * ((g⁻¹ * y) * x * (g⁻¹ * y)⁻¹) * g⁻¹ := by group
      have hw := mul_mem (mul_mem hgy hx) (inv_mem hgy)
      rw [e, hgR _ hw, hM.mul _ (mul_mem hgy hx) _ (inv_mem hgy), hM.mul _ hgy _ hx,
        hM.μ_inv hgy]
      congr 1
      rw [Nat.xor_comm (μ (g⁻¹ * y)) (μ x), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    refine ⟨y, (hJ y).mpr ⟨hyS, fun x hx => ?_⟩, hy2, hM.code_unique (hrA y hyN) hyA⟩
    obtain ⟨hxR, hxm⟩ := (hX x).mp hx
    have hxf : maskApply (adMat r) (μ x) = μ x := by
      rcases List.mem_cons.mp hxm with h | h
      · rw [h, RuQCode.maskApply_zero]
      · exact hrfix _ h
    obtain ⟨hcA, s, hs⟩ := hM.comm_xor_sq_mem_image hyN hy2 hrinv hyA hyR hxR hxf
    have hq : qC (μ x) = 0 := (hM.sq_eq_one_iff hxR).mp (hXel.2 x hx)
    rw [hq, RuSimCode.fin8_xor_zero] at hs
    rcases (RuQCode.mem_tvOf.mp hr).2.2 s with h | h
    · left
      exact hM.ν_inj _ hcA (hs.trans h)
    · right
      exact hM.eq_of_ν_eq hcA hfA (hs.trans h)
  have hJR : ∀ v ∈ R, v ∈ J ↔ μ v ∈ RuQCode.jlOf (ν f) := by
    intro v hv
    rw [hJ, RuQCode.mem_jlOf]
    constructor
    · rintro ⟨-, h⟩
      refine ⟨hM.lt v hv, fun m hm => ?_⟩
      obtain ⟨x, hx, hxm⟩ := hM.surj m (RuQCode.ppOf_lt _ _ hm)
      have hxX : x ∈ X := (hX x).mpr ⟨hx, by rw [hxm]; exact List.mem_cons_of_mem _ hm⟩
      rw [← hxm, RuQCode.bC_comm, ← hM.comm hv hx]
      rcases h x hxX with h1 | h1
      · left
        rw [h1, hM.ν_one]
      · right
        rw [h1]
    · rintro ⟨-, h⟩
      refine ⟨hRS hv, fun x hx => ?_⟩
      obtain ⟨hxR, hxm⟩ := (hX x).mp hx
      have hc := hM.comm hv hxR
      have hcA := hM.comm_mem _ hv _ hxR
      rcases List.mem_cons.mp hxm with h' | h'
      · left
        rw [h', RuQCode.bC_zero_right] at hc
        exact hM.ν_inj _ hcA hc
      · rw [RuQCode.bC_comm] at hc
        rcases h _ h' with h1 | h1
        · left
          exact hM.ν_inj _ hcA (hc.trans h1)
        · right
          exact hM.eq_of_ν_eq hcA hfA (hc.trans h1)
  have hAJR : gmsA L T ≤ J ⊓ R := fun b hb =>
    mem_inf.mpr ⟨hXJ (hM.gmsA_le_plane hX hb), hM.le hb⟩
  have hcardJR : Nat.card (J ⊓ R : Subgroup G) = 2 ^ 9 := by
    have h := card_eq_length_mul_card hAJR μ (RuQCode.jlOf (ν f)) (RuQCode.jlOf_nodup _)
      (fun a ha => (hJR a (mem_inf.mp ha).2).mp (mem_inf.mp ha).1)
      (fun c hc => by
        obtain ⟨x, hx, hxc⟩ := hM.surj c (RuQCode.mem_jlOf.mp hc).1
        exact ⟨x, mem_inf.mpr ⟨(hJR x hx).mpr (by rw [hxc]; exact hc), hx⟩, hxc⟩)
      (fun a ha b hb => by
        have haR := (mem_inf.mp ha).2
        have hbR := (mem_inf.mp hb).2
        rw [← hM.ker _ (mul_mem (inv_mem haR) hbR), hM.mul _ (inv_mem haR) _ hbR,
          hM.μ_inv haR]
        exact ⟨fun h => by rw [h]; exact Nat.xor_self _, RuQCode.nat_eq_of_xor_eq_zero⟩)
    rw [hparts.2.1, hM.card_gmsA] at h
    rw [h]
    norm_num
  have hcodeiff : ∀ a ∈ J, ∀ b ∈ J, rOf a = rOf b ↔ a⁻¹ * b ∈ J ⊓ R := by
    intro a ha b hb
    have haN := hSN' a (hJS ha)
    have hbN := hSN' b (hJS hb)
    constructor
    · intro h
      refine mem_inf.mpr ⟨mul_mem (inv_mem ha) hb, ?_⟩
      rw [← hNC]
      refine mem_inf.mpr ⟨mul_mem (inv_mem haN) hbN, mem_centralizer_iff.mpr fun c hc => ?_⟩
      have h1 := hM.eq_of_ν_eq (hM.normA a haN c hc) (hM.normA b hbN c hc)
        (by rw [hrA a haN c hc, hrA b hbN c hc, h])
      calc c * (a⁻¹ * b) = a⁻¹ * (a * c * a⁻¹) * b := by group
        _ = a⁻¹ * (b * c * b⁻¹) * b := by rw [h1]
        _ = a⁻¹ * b * c := by group
    · intro h
      have hw := (mem_inf.mp h).2
      refine hM.code_unique (hrA a haN) fun c hc => ?_
      have e : a * c * a⁻¹ = b * ((a⁻¹ * b)⁻¹ * c * (a⁻¹ * b)) * b⁻¹ := by group
      rw [e, show (a⁻¹ * b)⁻¹ * c * (a⁻¹ * b) = c by
        rw [mul_assoc, ← hM.central _ hw c hc]; group, hrA b hbN c hc]
  have hcardJ : Nat.card J = 2 ^ 11 := by
    have h := card_eq_length_mul_card (inf_le_left : J ⊓ R ≤ J) rOf
      (linId :: RuQCode.tvOf (ν f)) (RuQCode.tvOf_nodup _) hcodeJ
      (fun c hc => by
        rcases List.mem_cons.mp hc with hc | hc
        · refine ⟨1, one_mem _, ?_⟩
          rw [hc]
          refine (hM.code_unique (hrA 1 (one_mem _)) fun b _ => ?_)
          rw [RuSimCode.linApply_linId]
          congr 1
          group
        · obtain ⟨y, hyJ, -, hyr⟩ := hlift c hc
          exact ⟨y, hyJ, hyr⟩)
      hcodeiff
    rw [List.length_cons, hparts.1, hcardJR] at h
    rw [h]
    norm_num
  refine ⟨hcardJ, hXJ, hJS, fun v hv => ?_⟩
  have hvN := hSN' v (hJS hv)
  rcases List.mem_cons.mp (hcodeJ v hv) with h | h
  · have hvR : v ∈ R := hM.mem_of_code_eq_linId hNC hvN (by rw [← h]; exact hrA v hvN)
    exact hM.gmsA_le_plane hX (hM.sq_mem v hvR)
  · obtain ⟨y, hyJ, hy2, hyr⟩ := hlift _ h
    have hyN := hSN' y (hJS hyJ)
    have hw : y⁻¹ * v ∈ J ⊓ R := (hcodeiff y hyJ v hv).mp (by rw [hyr])
    have hwR := (mem_inf.mp hw).2
    have hwJ := (mem_inf.mp hw).1
    have hyinv : y⁻¹ = y := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hy2]
    have e : v ^ 2 = (y * (y⁻¹ * v) * y⁻¹) * (y⁻¹ * v) := by
      calc v ^ 2 = v * (y ^ 2)⁻¹ * v := by rw [hy2, inv_one, mul_one, pow_two]
        _ = (y * (y⁻¹ * v) * y⁻¹) * (y⁻¹ * v) := by group
    have hyw : y * (y⁻¹ * v) * y⁻¹ ∈ R := (mem_normalizer_iff.mp hyN _).mp hwR
    rw [e]
    refine (hX _).mpr ⟨mul_mem hyw hwR, ?_⟩
    rw [hM.mul _ hyw _ hwR, hrR y hyN _ hwR, hyr]
    exact (hparts.2.2 _ h).2.2 _ ((hJR _ hwR).mp hwJ)


omit [Finite G] hM in
theorem comm_mem_X_of_mem_J {X J : Subgroup G} (hJX : J ≤ normalizer (X : Set G))
    (hsq : ∀ v ∈ J, v ^ 2 ∈ X) {u v : G} (hu : u ∈ J) (hv : v ∈ J) :
    u * v * u⁻¹ * v⁻¹ ∈ X := by
  have h1 := hsq _ (mul_mem hu hv)
  have h2 : v⁻¹ * (u ^ 2)⁻¹ * v ∈ X := by
    have := (mem_normalizer_iff.mp (hJX (inv_mem hv)) _).mp (inv_mem (hsq u hu))
    simpa using this
  have h3 := inv_mem (hsq v hv)
  have e : u * v * u⁻¹ * v⁻¹ = (u * v) ^ 2 * (v⁻¹ * (u ^ 2)⁻¹ * v) * (v ^ 2)⁻¹ := by
    simp only [pow_two]
    group
  rw [e]
  exact mul_mem (mul_mem h1 h2) h3

end Sec3.SzR.MaskCoords

end CFSG.ComponentClassification.GMS78
