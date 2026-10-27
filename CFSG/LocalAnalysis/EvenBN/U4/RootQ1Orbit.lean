module

public import CFSG.LocalAnalysis.EvenBN.U4.RootQ1
public import CFSG.LocalAnalysis.EvenBN.U4.Prelim.OrbitShape
public import CFSG.LocalAnalysis.EvenBN.U4.Model.TorusTransitive
public import CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_sup)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem t_mem_normalizer_F1 (hS : Setting h L η t Q T) :
    t ∈ normalizer (miyamotoF1G h L η t : Set G) :=
  hS.D1_le_normalizer_F1 hS.t_mem_D1

theorem normalizer_Q1_le_normalizer_F1 (hS : Setting h L η t Q T) :
    normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G) ≤
      normalizer (miyamotoF1G h L η t : Set G) := fun _ hg =>
  hS.mem_normalizer_F1_of_le le_sup_left (sup_le_sup_left hS.Q_le_T _) hg

theorem P1_le_Q1 (hS : Setting h L η t Q T) :
    miyamotoF1G h L η t ⊔ miyamotoPG h L η ≤ miyamotoF1G h L η t ⊔ Q :=
  sup_le_sup_left hS.P_le_Q _

theorem P1_le_normalizer_F1 (hS : Setting h L η t Q T) :
    miyamotoF1G h L η t ⊔ miyamotoPG h L η ≤ normalizer (miyamotoF1G h L η t : Set G) :=
  sup_le le_normalizer hS.PG_le_normalizer_F1

theorem t_not_mem_P1 (hS : Setting h L η t Q T) : t ∉ miyamotoF1G h L η t ⊔ miyamotoPG h L η := by
  intro ht
  obtain ⟨f₀, hf₀, p, hp, e⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer' hS.PG_le_normalizer_F1 ht
  have hpT : p ∈ T := (hS.P_le_Q.trans hS.Q_le_T) hp
  have hf₀T : f₀ ∈ T := by
    have := mul_mem hS.t_mem_T (inv_mem hpT)
    rwa [e, mul_inv_cancel_right] at this
  have hf₀A : f₀ ∈ miyamotoA1G h L η := hS.F1_inf_T ▸ mem_inf.2 ⟨hf₀, hf₀T⟩
  apply hS.t_not_mem_L
  rw [e]
  exact mul_mem (miyamotoPull_le h L η _ (hS.A1G_le_PG hf₀A)) (miyamotoPull_le h L η _ hp)

theorem mem_P1_or_of_mem_Q1 (hS : Setting h L η t Q T) {x : G}
    (hx : x ∈ miyamotoF1G h L η t ⊔ Q) :
    x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η ∨
      t * x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η := by
  have hQF : Q ≤ normalizer (miyamotoF1G h L η t : Set G) := hS.Q_le_T.trans hS.T_le_normalizer_F1
  obtain ⟨f₀, hf₀, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer' hQF hx
  rw [hS.Q_eq] at hq
  obtain ⟨p, hp, u, hu, rfl⟩ := exists_mul_of_mem_sup_of_commute hS.P_comm_zpowers hq
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hu
  rcases hS.zpow_t_eq k with hk | hk <;> rw [hk]
  · left
    rw [mul_one]
    exact mul_mem (mem_sup_left hf₀) (mem_sup_right hp)
  · right
    have htf : t * f₀ * t⁻¹ ∈ miyamotoF1G h L η t :=
      (mem_normalizer_iff.1 hS.t_mem_normalizer_F1 f₀).1 hf₀
    have hpt : p * t = t * p := mem_centralizer_singleton_iff.1 (hS.PG_le_C hp)
    have e : t * (f₀ * (p * t)) = (t * f₀ * t⁻¹) * p := by
      rw [hpt, hS.t_inv]
      group
    rw [e]
    exact mul_mem (mem_sup_left htf) (mem_sup_right hp)

theorem IG_le_normalizer_PG (_hS : Setting h L η t Q T) :
    miyamotoIG h L η ≤ normalizer (miyamotoPG h L η : Set G) := by
  have : CharP K 2 := h.charP
  intro x hx
  have : x ∈ L ⊓ normalizer (miyamotoPG h L η : Set G) := by
    rw [← miyamotoPull_inf_normalizer h L η (miyamotoUnipotent_le_SU h false false)]
    exact miyamotoPull_mono h L η (le_inf (miyamotoI_le_gramSU h)
      (miyamotoI_le_normalizer_unipotent h false false)) hx
  exact this.2

theorem IG_le_normalizer_Q1 (hS : Setting h L η t Q T) :
    miyamotoIG h L η ≤ normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G) := by
  intro x hx
  have hxQ : x ∈ normalizer (Q : Set G) := by
    rw [hS.Q_eq]
    exact mem_normalizer_sup (hS.IG_le_normalizer_PG hx)
      (mem_normalizer_zpowers_of_comm (mem_centralizer_singleton_iff.1 (hS.IG_le_C hx)))
  exact mem_normalizer_sup (hS.IG_le_normalizer_F1 hx) hxQ

theorem exists_IG_conj_mul_inv_mem_F1 (hS : Setting h L η t Q T) {x x' : G}
    (hx : x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η) (hxF : x ∉ miyamotoF1G h L η t)
    (hx' : x' ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η) (hx'F : x' ∉ miyamotoF1G h L η t) :
    ∃ i ∈ miyamotoIG h L η, i⁻¹ * x * i * x'⁻¹ ∈ miyamotoF1G h L η t := by
  have : CharP K 2 := h.charP
  obtain ⟨f₀, hf₀, p, hp, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer' hS.PG_le_normalizer_F1 hx
  obtain ⟨f₁, hf₁, p', hp', rfl⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer' hS.PG_le_normalizer_F1 hx'
  have hpA : p ∉ miyamotoA1G h L η := fun e => hxF (mul_mem hf₀ (hS.A1_le_F1 e))
  have hp'A : p' ∉ miyamotoA1G h L η := fun e => hx'F (mul_mem hf₁ (hS.A1_le_F1 e))
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hp
  obtain ⟨g', hg', rfl⟩ := (mem_miyamotoPull h L η).1 hp'
  have hgA : (g : GL (Fin 4) K) ∉ miyamotoA1 h := fun e =>
    hpA ((symm_mem_miyamotoPull_iff h L η).2 e)
  have hg'A : (g' : GL (Fin 4) K) ∉ miyamotoA1 h := fun e =>
    hp'A ((symm_mem_miyamotoPull_iff h L η).2 e)
  obtain ⟨D, hD, hDg⟩ := exists_miyamotoI_conj_mul_inv_mem_A1 h hg hgA hg' hg'A
  set d : gramSU h (miyamotoJ4 K) := ⟨D, miyamotoI_le_gramSU h hD⟩ with hd
  set i : G := ((η.symm d : L) : G) with hi
  have hiI : i ∈ miyamotoIG h L η := (symm_mem_miyamotoPull_iff h L η).2 hD
  refine ⟨i, hiI, ?_⟩
  have hiF := hS.IG_le_normalizer_F1 hiI
  have h1 : i⁻¹ * ((η.symm g : L) : G) * i * ((η.symm g' : L) : G)⁻¹ ∈ miyamotoA1G h L η := by
    have : ((η.symm (d⁻¹ * g * d * g'⁻¹) : L) : G) ∈ miyamotoA1G h L η :=
      (symm_mem_miyamotoPull_iff h L η).2 (by simpa only [coe_mul, coe_inv] using hDg)
    simpa only [map_mul, map_inv, coe_mul, coe_inv] using this
  have h2 : i⁻¹ * f₀ * i ∈ miyamotoF1G h L η t := by
    have := (mem_normalizer_iff.1 (inv_mem hiF) f₀).1 hf₀
    rwa [inv_inv] at this
  have e : i⁻¹ * (f₀ * ((η.symm g : L) : G)) * i * (f₁ * ((η.symm g' : L) : G))⁻¹ =
      (i⁻¹ * f₀ * i) * (i⁻¹ * ((η.symm g : L) : G) * i * ((η.symm g' : L) : G)⁻¹) * f₁⁻¹ := by
    group
  rw [e]
  exact mul_mem (mul_mem h2 (hS.A1_le_F1 h1)) (inv_mem hf₁)

theorem exists_isPGroup_gt_T1 (hS : Setting h L η t Q T) :
    ∃ X : Subgroup G, IsPGroup 2 X ∧ miyamotoF1G h L η t ⊔ T ≤ X ∧
      X ≤ normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G) ∧
      Nat.card (miyamotoF1G h L η t ⊔ T : Subgroup G) < Nat.card X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTF : T ≤ normalizer (miyamotoF1G h L η t : Set G) := hS.T_le_normalizer_F1
  have hT1p : IsPGroup 2 (miyamotoF1G h L η t ⊔ T : Subgroup G) :=
    hS.isPGroup_F1.to_sup_of_normal_left' hS.isPGroup_T hTF
  obtain ⟨S, hSp, hSc⟩ := hS.exists_two_subgroup_card_gt_T1
  obtain ⟨S₀, hTS₀⟩ := hT1p.exists_le_sylow
  obtain ⟨S₁, hSS₁⟩ := hSp.exists_le_sylow
  have hcard : Nat.card (miyamotoF1G h L η t ⊔ T : Subgroup G) < Nat.card S₀ :=
    calc _ < Nat.card S := hSc
      _ ≤ Nat.card S₁ := card_le_of_le hSS₁
      _ = Nat.card S₀ := by rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have hlt : (miyamotoF1G h L η t ⊔ T).subgroupOf (S₀ : Subgroup G) < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => ?_
    have hle : (S₀ : Subgroup G) ≤ miyamotoF1G h L η t ⊔ T := fun x hx => by
      have : (⟨x, hx⟩ : (S₀ : Subgroup G)) ∈
          (miyamotoF1G h L η t ⊔ T).subgroupOf (S₀ : Subgroup G) := by
        rw [htop]
        exact mem_top _
      exact mem_subgroupOf.1 this
    exact absurd (card_le_of_le hle) (not_le.2 hcard)
  have : Group.IsNilpotent (S₀ : Subgroup G) := S₀.isPGroup'.isNilpotent
  obtain ⟨y, hyN, hyT⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hyN' : (y : G) ∈ normalizer ((miyamotoF1G h L η t ⊔ T : Subgroup G) : Set G) :=
    mem_normalizer_fintype fun n hn =>
      mem_subgroupOf.1 ((mem_normalizer_iff.1 hyN ⟨n, hTS₀ hn⟩).1 (mem_subgroupOf.2 hn))
  have hyT' : (y : G) ∉ miyamotoF1G h L η t ⊔ T := fun e => hyT (mem_subgroupOf.2 e)
  refine ⟨(miyamotoF1G h L η t ⊔ T) ⊔ zpowers (y : G),
    S₀.isPGroup'.to_le (sup_le hTS₀ (zpowers_le.2 y.2)), le_sup_left,
    sup_le (le_normalizer.trans hS.normalizer_T1_le_normalizer_Q1)
      (zpowers_le.2 (hS.normalizer_T1_le_normalizer_Q1 hyN')), ?_⟩
  refine lt_of_not_ge fun hle => hyT' ?_
  have heq := eq_of_le_of_card_ge (le_sup_left : miyamotoF1G h L η t ⊔ T ≤ _) hle
  rw [heq]
  exact mem_sup_right (mem_zpowers _)

theorem mem_normalizer_B1_of_crossed_mem_F1 (hS : Setting h L η t Q T) {g : G}
    (hgF : g ∈ normalizer (miyamotoF1G h L η t : Set G))
    (hgt : (g * t)⁻¹ * (t * g) ∈ miyamotoF1G h L η t) :
    g ∈ normalizer (miyamotoB1 h L η t : Set G) := by
  rw [← hS.normalizer_D1_eq]
  have hu : g⁻¹ * t * g = t * ((g * t)⁻¹ * (t * g)) := by group
  have hinv : g⁻¹ ∈ normalizer (miyamotoD1 h L η t : Set G) := by
    refine mem_normalizer_fintype fun d hd => ?_
    rw [inv_inv]
    rcases hS.mem_F1_or_of_mem_D1 hd with hdF | ⟨e, he, rfl⟩
    · have := (mem_normalizer_iff.1 (inv_mem hgF) d).1 hdF
      rw [inv_inv] at this
      exact hS.F1_le_D1 this
    · have heF : g⁻¹ * e * g ∈ miyamotoF1G h L η t := by
        have := (mem_normalizer_iff.1 (inv_mem hgF) e).1 he
        rwa [inv_inv] at this
      have e1 : g⁻¹ * (e * t) * g = (g⁻¹ * e * g) * (g⁻¹ * t * g) := by group
      rw [e1, hu]
      exact mul_mem (hS.F1_le_D1 heF) (mul_mem hS.t_mem_D1 (hS.F1_le_D1 hgt))
  simpa using inv_mem hinv

noncomputable abbrev tBar (hS : Setting h L η t Q T) : Bar (miyamotoF1G h L η t) :=
  proj (miyamotoF1G h L η t) ⟨t, hS.t_mem_normalizer_F1⟩

theorem card_bar_P1 (hS : Setting h L η t Q T) :
    Nat.card (bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ miyamotoPG h L η)) =
      (2 ^ f) ^ 2 := by
  have h1 := card_bar_mul le_sup_left hS.P1_le_normalizer_F1
  rw [hS.card_P1, hS.card_F1] at h1
  refine Nat.eq_of_mul_eq_mul_right (by positivity : 0 < (2 ^ f) ^ 8) ?_
  rw [h1]
  ring

theorem orbit_shape_bar (hS : Setting h L η t Q T) :
    (∀ g ∈ bar (miyamotoF1G h L η t) (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)),
        hS.tBar * (g⁻¹ * hS.tBar * g) ∈
          bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ miyamotoPG h L η)) ∧
      bar (miyamotoF1G h L η t) (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) ≤
        normalizer (bar (miyamotoF1G h L η t) (miyamotoF1G h L η t ⊔ miyamotoPG h L η) :
          Set (Bar (miyamotoF1G h L η t))) ∧
      (centralizer ({hS.tBar} : Set (Bar (miyamotoF1G h L η t)))).relIndex
          (bar (miyamotoF1G h L η t)
            (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G))) =
        (2 ^ f) ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F₁ := miyamotoF1G h L η t with hF₁
  set Q₁ := F₁ ⊔ Q with hQ₁
  set P₁ := F₁ ⊔ miyamotoPG h L η with hP₁
  set H := normalizer ((Q₁ : Subgroup G) : Set G) with hH
  have hHN : H ≤ normalizer (F₁ : Set G) := hS.normalizer_Q1_le_normalizer_F1
  have hFQ : F₁ ≤ Q₁ := le_sup_left
  have hFP : F₁ ≤ P₁ := le_sup_left
  set tb : Bar F₁ := hS.tBar with htb
  have htQ : tb ∈ bar F₁ Q₁ := (mem_bar_iff hFQ _).2 (mem_sup_right hS.t_mem_Q)
  have htA : tb ∉ bar F₁ P₁ := fun e => hS.t_not_mem_P1 ((mem_bar_iff hFP _).1 e)
  have ht2 : tb * tb = 1 := by
    rw [htb, ← map_mul, proj_eq_one_iff]
    change t * t ∈ F₁
    rw [hS.t_mul_t]
    exact one_mem _
  have hQ : ∀ x ∈ bar F₁ Q₁, x ∈ bar F₁ P₁ ∨ tb * x ∈ bar F₁ P₁ := by
    intro x hx
    obtain ⟨y, rfl⟩ := proj_surjective x
    have hy := (mem_bar_iff hFQ y).1 hx
    rcases hS.mem_P1_or_of_mem_Q1 hy with h1 | h1
    · exact Or.inl ((mem_bar_iff hFP y).2 h1)
    · right
      rw [htb, ← map_mul, mem_bar_iff hFP]
      exact h1
  have hHQ : bar F₁ H ≤ normalizer (bar F₁ Q₁ : Set (Bar F₁)) := bar_le_normalizer_bar hFQ le_rfl
  have hCH : bar F₁ (miyamotoIG h L η) ≤ bar F₁ H ⊓ centralizer ({tb} : Set (Bar F₁)) := by
    rintro _ ⟨i, hi, rfl⟩
    have hiI := mem_subgroupOf.1 hi
    refine mem_inf.2 ⟨proj_mem_bar (hS.IG_le_normalizer_Q1 hiI),
      mem_centralizer_singleton_iff.2 ?_⟩
    rw [htb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hS.IG_le_C hiI))
  have htrans : ∀ a ∈ bar F₁ P₁, a ≠ 1 → ∀ a' ∈ bar F₁ P₁, a' ≠ 1 →
      ∃ c ∈ bar F₁ (miyamotoIG h L η), c⁻¹ * a * c = a' := by
    intro a ha ha1 a' ha' ha'1
    obtain ⟨x, rfl⟩ := proj_surjective a
    obtain ⟨x', rfl⟩ := proj_surjective a'
    have hx := (mem_bar_iff hFP x).1 ha
    have hx' := (mem_bar_iff hFP x').1 ha'
    have hxF : (x : G) ∉ F₁ := fun e => ha1 (proj_eq_one_iff.2 e)
    have hx'F : (x' : G) ∉ F₁ := fun e => ha'1 (proj_eq_one_iff.2 e)
    obtain ⟨i, hi, hix⟩ := hS.exists_IG_conj_mul_inv_mem_F1 hx hxF hx' hx'F
    have hiN : i ∈ normalizer (F₁ : Set G) := hS.IG_le_normalizer_F1 hi
    refine ⟨proj F₁ ⟨i, hiN⟩, proj_mem_bar hi, ?_⟩
    have h1 : proj F₁ (⟨i, hiN⟩⁻¹ * x * ⟨i, hiN⟩ * x'⁻¹) = 1 :=
      proj_eq_one_iff.2 (by simpa only [coe_mul, coe_inv] using hix)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one] at h1
    exact h1
  have heven : Even ((centralizer ({tb} : Set (Bar F₁))).relIndex (bar F₁ H)) := by
    obtain ⟨X, hX2, hTX, hXH, hXcard⟩ := hS.exists_isPGroup_gt_T1
    refine even_relIndex_of_isPGroup (X := bar F₁ X) (bar_mono hXH) (isPGroup_bar hX2)
      fun S hSle hS2 => ?_
    have hlift2 : IsPGroup 2 (lift S) := isPGroup_lift hS.isPGroup_F1 hS2
    have hliftB : lift S ≤ normalizer (miyamotoB1 h L η t : Set G) := fun g hg => by
      obtain ⟨hgN, hgS⟩ := mem_lift_iff.1 hg
      have hc := mem_centralizer_singleton_iff.1 (mem_inf.1 (hSle hgS)).2
      rw [htb, ← map_mul, ← map_mul, proj_eq_proj_iff] at hc
      exact hS.mem_normalizer_B1_of_crossed_mem_F1 hgN hc
    have h1 := hS.card_le_of_le_normalizer_B1 hlift2 hliftB
    rw [← hS.card_T1, card_lift] at h1
    have h2 := card_bar_mul (le_sup_left.trans hTX) (hXH.trans hHN)
    have h3 : Nat.card S * Nat.card F₁ < Nat.card (bar F₁ X) * Nat.card F₁ := by
      rw [h2]
      exact lt_of_le_of_lt h1 hXcard
    exact Nat.lt_of_mul_lt_mul_right h3
  have hA2 : 2 < Nat.card (bar F₁ P₁) := by
    rw [hS.card_bar_P1]
    have hq : 2 < 2 ^ f := by
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hS.two_le
    calc 2 < 2 ^ f := hq
      _ ≤ (2 ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
  obtain ⟨key1, key2, key3⟩ := conj_mem_of_orbit_even (bar_mono hS.P1_le_Q1) htQ htA ht2 hQ
    hHQ hCH htrans heven hA2
  exact ⟨key1, key2, key3.trans hS.card_bar_P1⟩

theorem orbit_shape (hS : Setting h L η t Q T) :
    (∀ g ∈ normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G),
        t * (g⁻¹ * t * g) ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η) ∧
      normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G) ≤
        normalizer ((miyamotoF1G h L η t ⊔ miyamotoPG h L η : Subgroup G) : Set G) := by
  obtain ⟨key1, key2, -⟩ := hS.orbit_shape_bar
  have hHN := hS.normalizer_Q1_le_normalizer_F1
  have hFP : miyamotoF1G h L η t ≤ miyamotoF1G h L η t ⊔ miyamotoPG h L η := le_sup_left
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · have := key1 (proj _ ⟨g, hHN hg⟩) (proj_mem_bar hg)
    rw [tBar, ← map_inv, ← map_mul, ← map_mul, ← map_mul, mem_bar_iff hFP] at this
    simpa only [coe_mul, coe_inv] using this
  · have hgb := key2 (proj_mem_bar (A := miyamotoF1G h L η t) (x := ⟨g, hHN hg⟩) hg)
    refine mem_normalizer_fintype fun p hp => ?_
    have hpN := hS.P1_le_normalizer_F1 hp
    have := (mem_normalizer_iff.1 hgb (proj _ ⟨p, hpN⟩)).1 ((mem_bar_iff hFP _).2 hp)
    rw [← map_inv, ← map_mul, ← map_mul, mem_bar_iff hFP] at this
    simpa only [coe_mul, coe_inv, SetLike.mem_coe] using this

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
