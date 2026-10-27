module

public import CFSG.LocalAnalysis.EvenBN.U4.RootT1

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (card_sup_mul_card_inf_eq mem_normalizer_inf
  mem_normalizer_sup)
open scoped commutatorElement

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem card_le_of_commute_of_fieldFactor (hS : Setting h L η t Q T) {x : G} (hxT : x ∈ T)
    (hσ : hS.fieldFactor ⟨x, hS.T_le hxT⟩ ≠ 1) {W : Subgroup G} (hWA : W ≤ miyamotoA1G h L η)
    (hxW : ∀ w ∈ W, x * w = w * x) : Nat.card W ≤ (2 ^ f) ^ 3 := by
  have : CharP K 2 := h.charP
  have := h.finite
  obtain ⟨p, g, hg, hact⟩ := hS.exists_act_eq_twisted hxT
  obtain ⟨M, hMS, rfl⟩ := exists_eq_miyamotoPull h L η (hWA.trans (miyamotoPull_le h L η _))
  have hMA : M ≤ miyamotoA1 h :=
    (miyamotoPull_le_miyamotoPull_iff h L η hMS).1 hWA
  have hxC : x ∈ centralizer (miyamotoPull h L η M : Set G) :=
    mem_centralizer_iff.2 fun w hw => (hxW w hw).symm
  rw [card_miyamotoPull h L η hMS]
  refine (card_le_of_le fun y hy => ?_).trans (card_miyamotoTwistedFixA1_le h _
    (hS.exists_ne_of_fieldFactor_ne_one hσ) p hg)
  refine (mem_miyamotoTwistedFixA1 h).2 ⟨hMA hy, ?_⟩
  rw [← hact ⟨y, hMS hy⟩, act_apply]
  exact congrArg Subtype.val (miyamotoAct_apply_of_mem_centralizer h L η _ hxC hy)

theorem card_A1_inf_centralizer_le_of_mem_P (_hS : Setting h L η t Q T) {x : G}
    (hx : x ∈ miyamotoPG h L η) (hxA : x ∉ miyamotoA1G h L η) :
    Nat.card (miyamotoA1G h L η ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ (2 ^ f) ^ 2 := by
  have : CharP K 2 := h.charP
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hx
  have hgA : (g : GL (Fin 4) K) ∉ miyamotoA1 h := fun e =>
    hxA ((symm_mem_miyamotoPull_iff h L η).2 e)
  have hA := miyamotoUnipotent_le_SU h true false
  have hle : miyamotoA1G h L η ⊓ centralizer ({((η.symm g : L) : G)} : Set G) ≤
      miyamotoPull h L η (miyamotoA1 h ⊓ centralizer ({(g : GL (Fin 4) K)} : Set _)) := by
    rintro y ⟨hyA, hyC⟩
    obtain ⟨k, hk, rfl⟩ := (mem_miyamotoPull h L η).1 hyA
    refine (symm_mem_miyamotoPull_iff h L η).2 ⟨hk, mem_centralizer_singleton_iff.2 ?_⟩
    have e := mem_centralizer_singleton_iff.1 hyC
    rw [← coe_mul, ← coe_mul, ← map_mul, ← map_mul] at e
    have e' := η.symm.injective (Subtype.ext e)
    exact congrArg Subtype.val e'
  refine (card_le_of_le hle).trans ?_
  rw [card_miyamotoPull h L η (inf_le_left.trans hA)]
  exact card_A1_inf_centralizer_le h hg hgA

theorem card_F1_inf_centralizer_le (hS : Setting h L η t Q T) {y : G}
    (hyt : y * t = t * y) :
    Nat.card (miyamotoF1G h L η t ⊓ centralizer ({y} : Set G) : Subgroup G) ≤
      Nat.card (miyamotoA1G h L η ⊓ centralizer ({y} : Set G) : Subgroup G) ^ 2 := by
  set X := miyamotoF1G h L η t ⊓ centralizer ({y} : Set G) with hX
  set A := miyamotoA1G h L η ⊓ centralizer ({y} : Set G) with hA
  have hXD : ∀ x ∈ X, x ∈ miyamotoD1 h L η t := fun x hx => hS.F1_le_D1 (mem_inf.1 hx).1
  let δ : X →* G := MonoidHom.mk' (fun x => (x : G)⁻¹ * t * x * t) fun a b =>
    hS.crossed_mul_D1 (hXD a a.2) (hXD b b.2)
  have hδA : ∀ x : X, δ x ∈ A := fun x => by
    obtain ⟨hxF, hxC⟩ := mem_inf.1 x.2
    refine mem_inf.2 ⟨hS.crossed_mem_A1_of_mem_D1 (hXD x x.2), ?_⟩
    have hxy : y * x * y⁻¹ = x := by
      rw [← mem_centralizer_singleton_iff.1 hxC, mul_inv_cancel_right]
    have := CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj (x := (x : G)) hyt
    rw [hxy] at this
    refine mem_centralizer_singleton_iff.2 ?_
    change (↑x)⁻¹ * t * ↑x * t * y = y * ((↑x)⁻¹ * t * ↑x * t)
    calc (↑x)⁻¹ * t * ↑x * t * y = y * ((↑x)⁻¹ * t * ↑x * t) * y⁻¹ * y := by rw [← this]
      _ = y * ((↑x)⁻¹ * t * ↑x * t) := by group
  have hrange : Nat.card δ.range ≤ Nat.card A := by
    have hle : δ.range ≤ A := by
      rintro _ ⟨x, rfl⟩
      exact hδA x
    exact card_le_of_le hle
  have hker : Nat.card δ.ker ≤ Nat.card A := by
    have hle : δ.ker.map X.subtype ≤ A := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨hxF, hxC⟩ := mem_inf.1 x.2
      exact mem_inf.2 ⟨(hS.crossed_eq_one_iff_F1 hxF).1 hx, hxC⟩
    rw [← Subgroup.card_map_of_injective X.subtype_injective]
    exact card_le_of_le hle
  have h1 := Subgroup.card_mul_index δ.ker
  rw [Subgroup.index_ker] at h1
  rw [← h1, sq]
  exact Nat.mul_le_mul hker hrange

theorem mem_Q_of_fieldFactor_eq_one (hS : Setting h L η t Q T) {y : G} (hyT : y ∈ T)
    (hσ : hS.fieldFactor ⟨y, hS.T_le hyT⟩ = 1) : y ∈ Q := by
  obtain ⟨l, hl, c, hc, hy⟩ := (hS.fieldFactor_eq_one_iff _).1 hσ
  have hy' : y = l * c := hy
  have hct : c ∈ zpowers t := by
    rw [← hS.kernel_eq_zpowers']
    exact hc
  have hcT : c ∈ T := (zpowers_le.2 hS.t_mem_T) hct
  have hlT : l ∈ T := by
    have := mul_mem hyT (inv_mem hcT)
    rwa [hy', mul_inv_cancel_right] at this
  have hlP : l ∈ miyamotoPG h L η := by
    rw [← hS.T_inf_L]
    exact ⟨hlT, hl⟩
  rw [hS.Q_eq, hy']
  exact mul_mem (mem_sup_left hlP) (mem_sup_right hct)

theorem card_T_le (hS : Setting h L η t Q T) : Nat.card T ≤ 2 * f * Nat.card Q := by
  let σT : T →* (K ≃+* K) := hS.fieldFactor.comp (Subgroup.inclusion hS.T_le)
  have h1 := Subgroup.card_mul_index σT.ker
  rw [Subgroup.index_ker] at h1
  have hker : Nat.card σT.ker ≤ Nat.card Q := by
    rw [← Subgroup.card_map_of_injective T.subtype_injective]
    refine card_le_of_le ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hS.mem_Q_of_fieldFactor_eq_one y.2 hy
  have hrange : Nat.card σT.range ≤ 2 * f := by
    have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by
      rw [card_ringAut h]; have := h.one_le; omega)
    rw [← card_ringAut h]
    exact Subgroup.card_le_card_group _
  rw [← h1, mul_comm (2 * f)]
  exact Nat.mul_le_mul hker hrange

theorem card_T_lt (hS : Setting h L η t Q T) : Nat.card T < (2 ^ f) ^ 8 := by
  have h1 := hS.card_T_le
  rw [hS.card_Q] at h1
  have hf := hS.two_le
  have h4 : 4 * f < (2 ^ f) ^ 2 := by
    rw [← pow_mul]
    calc 4 * f < 2 ^ (f + 2) := by
          have := Nat.lt_two_pow_self (n := f)
          rw [pow_add]
          omega
      _ ≤ 2 ^ (f * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc Nat.card T ≤ 2 * f * (2 * (2 ^ f) ^ 6) := h1
    _ = (4 * f) * (2 ^ f) ^ 6 := by ring
    _ < (2 ^ f) ^ 2 * (2 ^ f) ^ 6 := Nat.mul_lt_mul_of_pos_right h4 (by positivity)
    _ = (2 ^ f) ^ 8 := by ring

theorem F1_inf_PG (hS : Setting h L η t Q T) :
    miyamotoF1G h L η t ⊓ miyamotoPG h L η = miyamotoA1G h L η := by
  refine le_antisymm (fun x hx => ?_) (le_inf hS.A1_le_F1 hS.A1G_le_PG)
  obtain ⟨hxF, hxP⟩ := mem_inf.1 hx
  rw [← hS.F1_inf_B1]
  refine ⟨hxF, ?_⟩
  rw [← hS.D1_inf_C]
  exact ⟨hS.F1_le_D1 hxF, hS.PG_le_C hxP⟩

theorem card_P1 (hS : Setting h L η t Q T) :
    Nat.card (miyamotoF1G h L η t ⊔ miyamotoPG h L η : Subgroup G) = (2 ^ f) ^ 10 := by
  have : CharP K 2 := h.charP
  have key := card_sup_mul_card_inf_eq hS.PG_le_normalizer_F1
  rw [hS.F1_inf_PG, hS.card_F1, card_miyamotoA1G,
    card_miyamotoPull h L η (miyamotoUnipotent_le_SU h false false), card_miyamotoP] at key
  have : Nat.card (miyamotoF1G h L η t ⊔ miyamotoPG h L η : Subgroup G) * (2 ^ f) ^ 4 =
      (2 ^ f) ^ 10 * (2 ^ f) ^ 4 := by rw [key]; ring
  exact Nat.eq_of_mul_eq_mul_right (by positivity) this

theorem T_le_normalizer_P1 (hS : Setting h L η t Q T) :
    T ≤ normalizer ((miyamotoF1G h L η t ⊔ miyamotoPG h L η : Subgroup G) : Set G) :=
  fun _ hx => mem_normalizer_sup
    ((hS.T_le_normalizer_B1.trans hS.normalizer_B1_le_normalizer_F1) hx) (hS.T_le_normalizer_P hx)

theorem T1_le_normalizer_P1 (hS : Setting h L η t Q T) :
    miyamotoF1G h L η t ⊔ T ≤
      normalizer ((miyamotoF1G h L η t ⊔ miyamotoPG h L η : Subgroup G) : Set G) :=
  sup_le (le_sup_left.trans le_normalizer) hS.T_le_normalizer_P1

theorem T1_le_normalizer_F1 (hS : Setting h L η t Q T) :
    miyamotoF1G h L η t ⊔ T ≤ normalizer (miyamotoF1G h L η t : Set G) :=
  sup_le le_normalizer (hS.T_le_normalizer_B1.trans hS.normalizer_B1_le_normalizer_F1)

theorem P1_le_T1 (hS : Setting h L η t Q T) :
    miyamotoF1G h L η t ⊔ miyamotoPG h L η ≤ miyamotoF1G h L η t ⊔ T :=
  sup_le le_sup_left ((hS.P_le_Q.trans hS.Q_le_T).trans le_sup_right)

theorem card_Q1_le (hS : Setting h L η t Q T) :
    Nat.card (miyamotoF1G h L η t ⊔ Q : Subgroup G) ≤
      2 * Nat.card (miyamotoF1G h L η t ⊔ miyamotoPG h L η : Subgroup G) := by
  have hQ1 : miyamotoF1G h L η t ⊔ Q = (miyamotoF1G h L η t ⊔ miyamotoPG h L η) ⊔ zpowers t := by
    rw [hS.Q_eq, sup_assoc]
  have htN : zpowers t ≤ normalizer ((miyamotoF1G h L η t ⊔ miyamotoPG h L η : Subgroup G) :
      Set G) := zpowers_le.2 (hS.T_le_normalizer_P1 hS.t_mem_T)
  have key := card_sup_mul_card_inf_eq htN
  rw [← hQ1, Nat.card_zpowers, hS.t_two] at key
  have hpos : 0 < Nat.card ((miyamotoF1G h L η t ⊔ miyamotoPG h L η) ⊓ zpowers t : Subgroup G) :=
    Nat.card_pos
  calc Nat.card (miyamotoF1G h L η t ⊔ Q : Subgroup G)
      ≤ Nat.card (miyamotoF1G h L η t ⊔ Q : Subgroup G) *
          Nat.card ((miyamotoF1G h L η t ⊔ miyamotoPG h L η) ⊓ zpowers t : Subgroup G) :=
        Nat.le_mul_of_pos_right _ hpos
    _ = 2 * Nat.card (miyamotoF1G h L η t ⊔ miyamotoPG h L η : Subgroup G) := by
        rw [key, mul_comm]

theorem card_mul_le_of_le_normalizer {B X Y : Subgroup G} (hBY : B ≤ Y) (hXY : X ≤ Y)
    (hBX : B ≤ normalizer (X : Set G)) :
    Nat.card B * Nat.card X ≤ Nat.card Y * Nat.card (B ⊓ X : Subgroup G) := by
  have key := card_sup_mul_card_inf_eq hBX
  rw [inf_comm] at key
  rw [mul_comm (Nat.card B), ← key]
  exact Nat.mul_le_mul_right _ (card_le_of_le (sup_le hXY hBY))

theorem eq_F1_of_commute (hS : Setting h L η t Q T) {B : Subgroup G}
    (hBT : B ≤ miyamotoF1G h L η t ⊔ T) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hcard : (2 ^ f) ^ 8 ≤ Nat.card B) : B = miyamotoF1G h L η t := by
  set F₁ := miyamotoF1G h L η t with hF₁
  set P₁ := F₁ ⊔ miyamotoPG h L η with hP₁
  set Q₁ := F₁ ⊔ Q with hQ₁
  have hBNP : B ≤ normalizer (P₁ : Set G) := hBT.trans hS.T1_le_normalizer_P1
  have hBNF : B ≤ normalizer (F₁ : Set G) := hBT.trans hS.T1_le_normalizer_F1
  have hTF : T ≤ normalizer (F₁ : Set G) :=
    hS.T_le_normalizer_B1.trans hS.normalizer_B1_le_normalizer_F1
  by_cases hBF : B ≤ F₁
  · exact eq_of_le_of_card_ge hBF (by rw [hF₁, hS.card_F1]; exact hcard)
  exfalso
  have hTlt := hS.card_T_lt
  have hq : 0 < 2 ^ f := by positivity
  have hcen : ∀ {f₀ y : G}, f₀ ∈ F₁ → f₀ * y ∈ B →
      B ⊓ F₁ ≤ F₁ ⊓ centralizer ({y} : Set G) := by
    intro f₀ y hf₀ hx b hb
    obtain ⟨hbB, hbF⟩ := mem_inf.1 hb
    refine mem_inf.2 ⟨hbF, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := hcomm b hbB _ hx
    have h2 : b * f₀ = f₀ * b := hS.F1_comm hbF hf₀
    calc b * y = f₀⁻¹ * (f₀ * b) * y := by group
      _ = f₀⁻¹ * (b * f₀) * y := by rw [h2]
      _ = f₀⁻¹ * (b * (f₀ * y)) := by group
      _ = f₀⁻¹ * ((f₀ * y) * b) := by rw [h1]
      _ = y * b := by group
  by_cases hA : ∃ x ∈ B, x ∈ P₁ ∧ x ∉ F₁
  ·
    obtain ⟨x, hxB, hxP1, hxF⟩ := hA
    obtain ⟨f₀, hf₀, p, hp, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_normalizer' hS.PG_le_normalizer_F1 hxP1
    have hpA : p ∉ miyamotoA1G h L η := fun hpA => hxF (mul_mem hf₀ (hS.A1_le_F1 hpA))
    have hpt : p * t = t * p := mem_centralizer_singleton_iff.1 (hS.PG_le_C hp)
    have h1 := hS.card_F1_inf_centralizer_le hpt
    have h2 := hS.card_A1_inf_centralizer_le_of_mem_P hp hpA
    have hBF4 : Nat.card (B ⊓ F₁ : Subgroup G) ≤ (2 ^ f) ^ 4 := by
      refine (card_le_of_le (hcen hf₀ hxB)).trans (h1.trans ?_)
      calc _ ≤ ((2 ^ f) ^ 2) ^ 2 := Nat.pow_le_pow_left h2 2
        _ = (2 ^ f) ^ 4 := by ring
    have hk := card_mul_le_of_le_normalizer hBT le_sup_left hBNF
    rw [hS.card_F1, hS.card_T1] at hk
    have : Nat.card B * (2 ^ f) ^ 8 ≤ Nat.card T * (2 ^ f) ^ 8 :=
      calc Nat.card B * (2 ^ f) ^ 8
          ≤ (2 ^ f) ^ 4 * Nat.card T * Nat.card (B ⊓ F₁ : Subgroup G) := hk
        _ ≤ (2 ^ f) ^ 4 * Nat.card T * (2 ^ f) ^ 4 := Nat.mul_le_mul_left _ hBF4
        _ = Nat.card T * (2 ^ f) ^ 8 := by ring
    have := Nat.le_of_mul_le_mul_right this (by positivity)
    omega
  push Not at hA
  have hBP1 : B ⊓ P₁ = B ⊓ F₁ := le_antisymm
    (fun x hx => mem_inf.2 ⟨(mem_inf.1 hx).1, hA x (mem_inf.1 hx).1 (mem_inf.1 hx).2⟩)
    (inf_le_inf_left _ le_sup_left)
  by_cases hB : ∃ x ∈ B, x ∉ Q₁
  ·
    obtain ⟨x, hxB, hxQ⟩ := hB
    obtain ⟨f₀, hf₀, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer' hTF (hBT hxB)
    have hyQ : y ∉ Q := fun hyQ => hxQ (mul_mem (mem_sup_left hf₀) (mem_sup_right hyQ))
    have hσ : hS.fieldFactor ⟨y, hS.T_le hy⟩ ≠ 1 := fun e =>
      hyQ (hS.mem_Q_of_fieldFactor_eq_one hy e)
    have hyt : y * t = t * y := mem_centralizer_singleton_iff.1 (hS.T_le hy)
    have h1 := hS.card_F1_inf_centralizer_le hyt
    have h2 : Nat.card (miyamotoA1G h L η ⊓ centralizer ({y} : Set G) : Subgroup G) ≤
        (2 ^ f) ^ 3 := hS.card_le_of_commute_of_fieldFactor hy hσ inf_le_left fun w hw =>
          (mem_centralizer_singleton_iff.1 (mem_inf.1 hw).2).symm
    have hBF6 : Nat.card (B ⊓ F₁ : Subgroup G) ≤ (2 ^ f) ^ 6 := by
      refine (card_le_of_le (hcen hf₀ hxB)).trans (h1.trans ?_)
      calc _ ≤ ((2 ^ f) ^ 3) ^ 2 := Nat.pow_le_pow_left h2 2
        _ = (2 ^ f) ^ 6 := by ring
    have hk := card_mul_le_of_le_normalizer hBT hS.P1_le_T1 hBNP
    rw [hS.card_P1, hS.card_T1, hBP1] at hk
    have : Nat.card B * (2 ^ f) ^ 10 ≤ Nat.card T * (2 ^ f) ^ 10 :=
      calc Nat.card B * (2 ^ f) ^ 10 ≤ (2 ^ f) ^ 4 * Nat.card T * Nat.card (B ⊓ F₁ : Subgroup G) :=
            hk
        _ ≤ (2 ^ f) ^ 4 * Nat.card T * (2 ^ f) ^ 6 := Nat.mul_le_mul_left _ hBF6
        _ = Nat.card T * (2 ^ f) ^ 10 := by ring
    have := Nat.le_of_mul_le_mul_right this (by positivity)
    omega
  push Not at hB
  obtain ⟨x, hxB, hxP⟩ : ∃ x ∈ B, x ∉ P₁ := by
    by_contra hcon
    push Not at hcon
    exact hBF fun x hx => hA x hx (hcon x hx)
  have htN : zpowers t ≤ normalizer (P₁ : Set G) := zpowers_le.2 (hS.T_le_normalizer_P1 hS.t_mem_T)
  have hQ1 : Q₁ = P₁ ⊔ zpowers t := by rw [hQ₁, hP₁, hS.Q_eq, sup_assoc]
  obtain ⟨w, hw, u, hu, hwu⟩ := exists_mul_of_mem_sup_of_le_normalizer' htN
    (show x ∈ P₁ ⊔ zpowers t by rw [← hQ1]; exact hB x hxB)
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hu
  have hkt : t ^ k = t := by
    rcases hS.zpow_t_eq k with h1 | h1
    · exact absurd (by rw [hwu, h1, mul_one]; exact hw) hxP
    · exact h1
  rw [hkt] at hwu
  have hBE : B ⊓ miyamotoEG h L η Q ≤ miyamotoZG h L η := fun e he => by
    obtain ⟨heB, heE⟩ := mem_inf.1 he
    refine (hS.crossed_eq_one_iff_E heE).1 ?_
    have hex : e * x = x * e := hcomm e heB x hxB
    obtain ⟨f₁, hf₁, p, hp, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_normalizer' hS.PG_le_normalizer_F1 hw
    have hef : e * f₁ = f₁ * e := hS.F1_comm (hS.E_le_F1 heE) hf₁
    have hep : e * p = p * e := hS.E_comm_PG heE hp
    have hew : e * (f₁ * p) = (f₁ * p) * e := by
      rw [← mul_assoc, hef, mul_assoc, hep, mul_assoc]
    have het : e * t = t * e := by
      rw [hwu] at hex
      calc e * t = (f₁ * p)⁻¹ * ((f₁ * p) * e * t) := by group
        _ = (f₁ * p)⁻¹ * (e * (f₁ * p) * t) := by rw [hew]
        _ = (f₁ * p)⁻¹ * ((f₁ * p) * t * e) := by rw [mul_assoc e, hex, mul_assoc]
        _ = t * e := by group
    rw [mul_assoc e⁻¹, ← het, inv_mul_cancel_left, hS.t_mul_t]
  have hEN : miyamotoEG h L η Q ≤ normalizer ((B ⊓ F₁ : Subgroup G) : Set G) := fun e he =>
    mem_normalizer_fintype fun b hb => by
      rw [hS.F1_comm (hS.E_le_F1 he) (mem_inf.1 hb).2, mul_inv_cancel_right]
      exact hb
  have key := card_sup_mul_card_inf_eq hEN
  have hsupF : Nat.card ((B ⊓ F₁) ⊔ miyamotoEG h L η Q : Subgroup G) ≤ (2 ^ f) ^ 8 := by
    rw [← hS.card_F1]
    exact card_le_of_le (sup_le inf_le_right hS.E_le_F1)
  have hinfZ : Nat.card ((B ⊓ F₁) ⊓ miyamotoEG h L η Q : Subgroup G) ≤ 2 ^ f := by
    rw [← hS.card_ZP]
    exact card_le_of_le fun e he => hBE (mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 he).1).1,
      (mem_inf.1 he).2⟩)
  rw [hS.card_E] at key
  have hBF7 : Nat.card (B ⊓ F₁ : Subgroup G) ≤ (2 ^ f) ^ 7 := by
    have : Nat.card (B ⊓ F₁ : Subgroup G) * (2 ^ f) ^ 2 ≤ (2 ^ f) ^ 7 * (2 ^ f) ^ 2 :=
      calc Nat.card (B ⊓ F₁ : Subgroup G) * (2 ^ f) ^ 2
          = Nat.card ((B ⊓ F₁) ⊔ miyamotoEG h L η Q : Subgroup G) *
            Nat.card ((B ⊓ F₁) ⊓ miyamotoEG h L η Q : Subgroup G) := key.symm
        _ ≤ (2 ^ f) ^ 8 * 2 ^ f := Nat.mul_le_mul hsupF hinfZ
        _ = (2 ^ f) ^ 7 * (2 ^ f) ^ 2 := by ring
    exact Nat.le_of_mul_le_mul_right this (by positivity)
  have hk := card_mul_le_of_le_normalizer (fun x hx => hB x hx)
    (le_sup_left.trans (le_of_eq hQ1.symm)) hBNP
  rw [hBP1] at hk
  have hQ1le := hS.card_Q1_le
  have hP1pos : 0 < Nat.card P₁ := Nat.card_pos
  have : Nat.card B * Nat.card P₁ ≤ (2 * Nat.card (B ⊓ F₁ : Subgroup G)) * Nat.card P₁ :=
    calc Nat.card B * Nat.card P₁ ≤ Nat.card Q₁ * Nat.card (B ⊓ F₁ : Subgroup G) := hk
      _ ≤ (2 * Nat.card P₁) * Nat.card (B ⊓ F₁ : Subgroup G) := Nat.mul_le_mul_right _ hQ1le
      _ = (2 * Nat.card (B ⊓ F₁ : Subgroup G)) * Nat.card P₁ := by ring
  have hB2 := Nat.le_of_mul_le_mul_right this hP1pos
  have h28 : 2 * (2 ^ f) ^ 7 < (2 ^ f) ^ 8 := by
    have h4 : 2 < 2 ^ f := by
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hS.two_le
    calc 2 * (2 ^ f) ^ 7 < 2 ^ f * (2 ^ f) ^ 7 := Nat.mul_lt_mul_of_pos_right h4 (by positivity)
      _ = (2 ^ f) ^ 8 := by ring
  omega

theorem conj_mul_mem_A1 (hS : Setting h L η t Q T) {x : G} (hx : x ∈ miyamotoF1G h L η t) :
    t * x * t⁻¹ * x ∈ miyamotoA1G h L η := by
  have hxD := hS.F1_le_D1 hx
  have hc := hS.crossed_mem_A1_of_mem_D1 hxD
  have hcomm : (x⁻¹ * t * x * t) * x = x * (x⁻¹ * t * x * t) :=
    mem_centralizer_iff.1 (hS.D1_le_centralizer_A1 hxD) _ hc
  have : t * x * t⁻¹ * x = (x⁻¹ * t * x * t) * (x * x) := by
    rw [hS.t_inv]
    calc t * x * t * x = x * (x⁻¹ * t * x * t) * x := by group
      _ = (x⁻¹ * t * x * t) * x * x := by rw [← hcomm]
      _ = _ := by group
  rw [this]
  exact mul_mem hc (hS.mul_self_mem_A1_of_mem_D1 hxD)

theorem exists_E_conj_mul_ne_one (hS : Setting h L η t Q T) :
    ∃ e ∈ miyamotoEG h L η Q, t * e * t⁻¹ * e ≠ 1 := by
  have : CharP K 2 := h.charP
  obtain ⟨ω, hω⟩ := exists_add_bar_eq_one h
  have hx₀A : miyamotoXGL h 1 0 ω ω ∈ miyamotoA2 h := (miyamotoXGL_mem_A2 h).2 ⟨rfl, by
    rw [map_one, one_mul, one_mul]
    calc ω + h.bar ω + h.bar ω + ω = (ω + ω) + (h.bar ω + h.bar ω) := by ring
      _ = 0 := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]⟩
  have hx₀S := miyamotoUnipotent_le_SU h false true hx₀A
  set a₀ : G := ((η.symm ⟨_, hx₀S⟩ : L) : G) with ha₀
  have ha₀A : a₀ ∈ miyamotoA2G h L η := (symm_mem_miyamotoPull_iff h L η).2 hx₀A
  have ha₀2 : a₀ * a₀ ≠ 1 := by
    intro e
    have e1 : (⟨_, hx₀S⟩ * ⟨_, hx₀S⟩ : gramSU h (miyamotoJ4 K)) = 1 :=
      η.symm.injective (by rw [map_mul, map_one]; exact Subtype.ext e)
    have e2 := congrArg Subtype.val e1
    rw [coe_mul, coe_one, miyamotoXGL_A2_mul_self, ← miyamotoXGL_zero h, miyamotoXGL_inj] at e2
    obtain ⟨-, -, -, e3⟩ := e2
    rw [map_one, one_mul, one_mul, hω] at e3
    exact one_ne_zero e3
  obtain ⟨g, -, hg⟩ := hS.C0_surj a₀ (mem_sup_right ha₀A)
  refine ⟨_, hg, fun h1 => ha₀2 ?_⟩
  set e := a₀⁻¹ * (t⁻¹ * (g * t * g⁻¹)) with he
  have hat : a₀ * t = t * a₀ :=
    mem_centralizer_singleton_iff.1 (hS.L_le_centralizer (η.symm ⟨_, hx₀S⟩).2)
  have hea : e * a₀ = a₀ * e := hS.E_comm_PG hg (hS.A2G_le_PG ha₀A)
  have hgt : g * t * g⁻¹ = t * a₀ * e := by rw [he]; group
  have hsq : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [hS.t_mul_t, mul_one, mul_inv_cancel]
  have hexp : (t * a₀ * e) * (t * a₀ * e) = a₀ * a₀ * (t * e * t⁻¹ * e) := by
    rw [hS.t_inv]
    calc (t * a₀ * e) * (t * a₀ * e) = (t * a₀) * e * (t * a₀) * e := by group
      _ = (a₀ * t) * e * (a₀ * t) * e := by rw [← hat]
      _ = a₀ * t * (e * a₀) * t * e := by group
      _ = a₀ * t * (a₀ * e) * t * e := by rw [hea]
      _ = a₀ * (t * a₀) * e * t * e := by group
      _ = a₀ * (a₀ * t) * e * t * e := by rw [← hat]
      _ = a₀ * a₀ * (t * e * t * e) := by group
  rw [hgt, hexp, h1, mul_one] at hsq
  exact hsq

theorem mem_A1_of_conj_mul_eq_one (hS : Setting h L η t Q T) {x : G}
    (hx : x ∈ miyamotoF1G h L η t) (h1 : t * x * t⁻¹ * x = 1) : x ∈ miyamotoA1G h L η := by
  have : CharP K 2 := h.charP
  set ψ : miyamotoF1G h L η t →* G := MonoidHom.mk' (fun f => t * f * t⁻¹ * f) fun a b => by
    have htb : t * b * t⁻¹ ∈ miyamotoF1G h L η t :=
      (mem_normalizer_iff.1 (hS.D1_le_normalizer_F1 hS.t_mem_D1) b).1 b.2
    have := hS.F1_comm htb a.2
    simp only [coe_mul]
    calc t * (a * b) * t⁻¹ * (a * b) = t * a * t⁻¹ * ((t * b * t⁻¹) * a) * b := by group
      _ = t * a * t⁻¹ * (a * (t * b * t⁻¹)) * b := by rw [this]
      _ = t * a * t⁻¹ * a * (t * b * t⁻¹ * b) := by group with hψ
  have hrange : ψ.range ≤ miyamotoA1G h L η := by
    rintro _ ⟨f, rfl⟩
    exact hS.conj_mul_mem_A1 f.2
  have hinv : ∀ n ∈ miyamotoN1G h L η, ∀ y ∈ ψ.range, n⁻¹ * y * n ∈ ψ.range := by
    rintro n hn _ ⟨f, rfl⟩
    have hf' : n⁻¹ * f * n ∈ miyamotoF1G h L η t := by
      have := (mem_normalizer_iff.1 (inv_mem (hS.N1_le_normalizer_F1 hn)) f).1 f.2
      rwa [inv_inv] at this
    have hnt : n * t = t * n :=
      mem_centralizer_singleton_iff.1 (hS.L_le_centralizer (miyamotoPull_le h L η _ hn))
    have hnt' : n⁻¹ * t * n = t := by rw [mul_assoc, ← hnt, inv_mul_cancel_left]
    refine ⟨⟨_, hf'⟩, ?_⟩
    show t * (n⁻¹ * (f : G) * n) * t⁻¹ * (n⁻¹ * f * n) = n⁻¹ * (t * f * t⁻¹ * f) * n
    calc t * (n⁻¹ * (f : G) * n) * t⁻¹ * (n⁻¹ * f * n)
        = (n⁻¹ * t * n) * (n⁻¹ * f * n) * (n⁻¹ * t * n)⁻¹ * (n⁻¹ * f * n) := by rw [hnt']
      _ = n⁻¹ * (t * f * t⁻¹ * f) * n := by group
  have hAe := isElementaryAbelian_miyamotoA1G h L η
  have hA2 : ∀ a ∈ miyamotoA1G h L η, a * a = 1 := fun a ha => by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian a ha
  obtain ⟨e, he, he1⟩ := hS.exists_E_conj_mul_ne_one
  rcases miyamotoN1G_irreducible_A1G h L η hrange hinv with h0 | hA
  · have : ψ ⟨e, hS.E_le_F1 he⟩ ∈ ψ.range := ⟨_, rfl⟩
    rw [h0, mem_bot] at this
    exact absurd this he1
  have hle : (miyamotoA1G h L η).subgroupOf (miyamotoF1G h L η t) ≤ ψ.ker := fun a ha => by
    have haA := mem_subgroupOf.1 ha
    have hat : (a : G) * t = t * a :=
      mem_centralizer_singleton_iff.1 (hS.A1_le_centralizer_t haA)
    show t * (a : G) * t⁻¹ * a = 1
    rw [← hat, mul_inv_cancel_right]
    exact hA2 _ haA
  have hker : ψ.ker = (miyamotoA1G h L η).subgroupOf (miyamotoF1G h L η t) := by
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    have h1' := Subgroup.card_mul_index ψ.ker
    rw [Subgroup.index_ker, hA, card_miyamotoA1G, hS.card_F1] at h1'
    have h2 : Nat.card ((miyamotoA1G h L η).subgroupOf (miyamotoF1G h L η t)) = (2 ^ f) ^ 4 := by
      rw [← card_miyamotoA1G h L η]
      exact Nat.card_congr (subgroupOfEquivOfLe hS.A1_le_F1).toEquiv
    rw [h2]
    have hpos : 0 < (2 ^ f) ^ 4 := by positivity
    have : Nat.card ψ.ker * (2 ^ f) ^ 4 = (2 ^ f) ^ 4 * (2 ^ f) ^ 4 := by
      rw [h1']
      ring
    exact (Nat.eq_of_mul_eq_mul_right hpos this).le
  have : (⟨x, hx⟩ : miyamotoF1G h L η t) ∈ ψ.ker := h1
  rw [hker] at this
  exact mem_subgroupOf.1 this

theorem card_le_of_isSylowOf {p : ℕ} [Fact p.Prime] {P K W : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P K) (hW : IsPGroup p W) (hWK : W ≤ K) :
    Nat.card W ≤ Nat.card P := by
  obtain ⟨S, hS⟩ := (hW.comap_subtype (K := K)).exists_le_sylow
  rw [hP.card_eq, ← Sylow.card_eq_multiplicity S]
  calc Nat.card W = Nat.card (W.subgroupOf K) :=
        (Nat.card_congr (subgroupOfEquivOfLe hWK).toEquiv).symm
    _ ≤ Nat.card S := card_le_of_le hS

theorem card_le_of_le_normalizer_B1 (hS : Setting h L η t Q T) {X : Subgroup G}
    (hX : IsPGroup 2 X) (hXN : X ≤ normalizer (miyamotoB1 h L η t : Set G)) :
    Nat.card X ≤ (2 ^ f) ^ 4 * Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hND := hS.normalizer_B1_le_normalizer_D1
  have hY : IsPGroup 2 (X ⊔ miyamotoD1 h L η t : Subgroup G) :=
    hX.to_sup_of_normal_right' hS.isPGroup_D1 (hXN.trans hND)
  have hYN : X ⊔ miyamotoD1 h L η t ≤ normalizer (miyamotoB1 h L η t : Set G) :=
    sup_le hXN hS.D1_le_normalizer_B1
  set W := (X ⊔ miyamotoD1 h L η t) ⊓ centralizer ({t} : Set G) with hW
  have hWD : W ≤ normalizer (miyamotoD1 h L η t : Set G) := (inf_le_left.trans hYN).trans hND
  have hWT : Nat.card W ≤ Nat.card T :=
    card_le_of_isSylowOf hS.T_sylow (hY.to_le inf_le_left) inf_le_right
  have hYle : X ⊔ miyamotoD1 h L η t ≤ miyamotoD1 h L η t ⊔ W := fun y hy => by
    obtain ⟨c, hc, d, hd, rfl⟩ := hS.normalizer_B1_eq_mul (hYN hy)
    have hcY : c ∈ X ⊔ miyamotoD1 h L η t := by
      have := mul_mem hy (inv_mem (mem_sup_right hd : d ∈ X ⊔ miyamotoD1 h L η t))
      rwa [mul_inv_cancel_right] at this
    exact mul_mem (mem_sup_right (mem_inf.2 ⟨hcY, (mem_inf.1 hc).2⟩)) (mem_sup_left hd)
  have hinf : miyamotoD1 h L η t ⊓ W = miyamotoB1 h L η t := by
    rw [hW, ← inf_assoc, inf_eq_left.2 (le_sup_right : miyamotoD1 h L η t ≤ X ⊔ _),
      hS.D1_inf_C]
  have key := card_sup_mul_card_inf_eq hWD
  rw [hinf, hS.card_B1, hS.card_D1] at key
  have hXY : Nat.card X ≤ Nat.card (miyamotoD1 h L η t ⊔ W : Subgroup G) :=
    card_le_of_le (le_sup_left.trans hYle)
  have : Nat.card X * (2 * (2 ^ f) ^ 4) ≤ (2 ^ f) ^ 4 * Nat.card T * (2 * (2 ^ f) ^ 4) :=
    calc Nat.card X * (2 * (2 ^ f) ^ 4)
        ≤ Nat.card (miyamotoD1 h L η t ⊔ W : Subgroup G) * (2 * (2 ^ f) ^ 4) :=
          Nat.mul_le_mul_right _ hXY
      _ = 2 * (2 ^ f) ^ 8 * Nat.card W := key
      _ ≤ 2 * (2 ^ f) ^ 8 * Nat.card T := Nat.mul_le_mul_left _ hWT
      _ = (2 ^ f) ^ 4 * Nat.card T * (2 * (2 ^ f) ^ 4) := by ring
  exact Nat.le_of_mul_le_mul_right this (by positivity)

theorem F1_mul_self (hS : Setting h L η t Q T) : ∀ f ∈ miyamotoF1G h L η t, f * f = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hS.F1_elementary_or_homocyclic with hel | hhom
  · exact hel
  exfalso
  have hAe := isElementaryAbelian_miyamotoA1G h L η
  have hBe := hS.isElementaryAbelian_B1
  have hA2 : ∀ a ∈ miyamotoA1G h L η, a * a = 1 := fun a ha => by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian a ha
  have hB2 : ∀ b ∈ miyamotoB1 h L η t, b * b = 1 := fun b hb => by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian b hb
  have hAB : miyamotoA1G h L η ≤ miyamotoB1 h L η t := fun a ha => mem_sup_right ha
  have hinvD : ∀ d ∈ miyamotoD1 h L η t, d * d = 1 → d ∈ miyamotoB1 h L η t := by
    intro d hd hdd
    rcases hS.mem_F1_or_of_mem_D1 hd with hdF | ⟨e, he, rfl⟩
    · exact hAB ((hhom d hdF).1 hdd)
    · have h1 : t * e * t⁻¹ * e = 1 := by
        calc t * e * t⁻¹ * e = e⁻¹ * (e * t * (e * t)) * e := by rw [hS.t_inv]; group
          _ = 1 := by rw [hdd]; group
      exact mul_mem (hAB (hS.mem_A1_of_conj_mul_eq_one he h1)) hS.t_mem_B1
  have hTF : T ≤ normalizer (miyamotoF1G h L η t : Set G) :=
    hS.T_le_normalizer_B1.trans hS.normalizer_B1_le_normalizer_F1
  have hT1B : miyamotoF1G h L η t ⊔ T ≤ normalizer (miyamotoB1 h L η t : Set G) :=
    sup_le (hS.F1_le_D1.trans hS.D1_le_normalizer_B1) hS.T_le_normalizer_B1
  have hDT : miyamotoD1 h L η t ≤ miyamotoF1G h L η t ⊔ T := by
    rw [← hS.F1_sup_zpowers]
    exact sup_le le_sup_left (zpowers_le.2 (mem_sup_right hS.t_mem_T))
  have hNT : normalizer ((miyamotoF1G h L η t ⊔ T : Subgroup G) : Set G) ≤
      normalizer (miyamotoB1 h L η t : Set G) := by
    intro g hg
    have hgF : g ∈ normalizer (miyamotoF1G h L η t : Set G) := by
      have hB := hS.eq_F1_of_commute (B := (miyamotoF1G h L η t).map (MulAut.conj g).toMonoidHom)
        (by
          rintro _ ⟨x, hx, rfl⟩
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          exact (mem_normalizer_iff.1 hg x).1 (mem_sup_left hx))
        (by
          rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
            _ = g * (y * x) * g⁻¹ := by rw [hS.F1_comm hx hy]
            _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group)
        (le_of_eq (by
          rw [card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,
            hS.card_F1]))
      exact mem_normalizer_fintype fun x hx => by
        rw [← hB]
        exact ⟨x, hx, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    have hgA : g ∈ normalizer (miyamotoA1G h L η : Set G) := mem_normalizer_fintype fun a ha => by
      have haF : g * a * g⁻¹ ∈ miyamotoF1G h L η t :=
        (mem_normalizer_iff.1 hgF a).1 (hS.A1_le_F1 ha)
      refine (hhom _ haF).1 ?_
      calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
        _ = 1 := by rw [hA2 a ha, mul_one, mul_inv_cancel]
    have hgD : g ∈ normalizer (miyamotoD1 h L η t : Set G) := mem_normalizer_fintype fun d hd => by
      rw [hS.D1_eq]
      refine mem_inf.2 ⟨hT1B ((mem_normalizer_iff.1 hg d).1 (hDT hd)),
        mem_centralizer_iff.2 fun a ha => ?_⟩
      have ha' : g⁻¹ * a * g⁻¹⁻¹ ∈ miyamotoA1G h L η := (mem_normalizer_iff.1 (inv_mem hgA) a).1 ha
      have hDC : (g⁻¹ * a * g⁻¹⁻¹) * d = d * (g⁻¹ * a * g⁻¹⁻¹) :=
        mem_centralizer_iff.1 (hS.D1_le_centralizer_A1 hd) _ ha'
      calc a * (g * d * g⁻¹) = g * ((g⁻¹ * a * g⁻¹⁻¹) * d) * g⁻¹ := by group
        _ = g * (d * (g⁻¹ * a * g⁻¹⁻¹)) * g⁻¹ := by rw [hDC]
        _ = g * d * g⁻¹ * a := by group
    exact mem_normalizer_fintype fun b hb => by
      refine hinvD _ ((mem_normalizer_iff.1 hgD b).1 (hS.B1_le_D1 hb)) ?_
      calc g * b * g⁻¹ * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
        _ = 1 := by rw [hB2 b hb, mul_one, mul_inv_cancel]
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
  have hXp : IsPGroup 2 ((miyamotoF1G h L η t ⊔ T) ⊔ zpowers (y : G) : Subgroup G) :=
    S₀.isPGroup'.to_le (sup_le hTS₀ (zpowers_le.2 y.2))
  have hXN : (miyamotoF1G h L η t ⊔ T) ⊔ zpowers (y : G) ≤
      normalizer (miyamotoB1 h L η t : Set G) :=
    sup_le (le_normalizer.trans hNT) (zpowers_le.2 (hNT hyN'))
  have h1 := hS.card_le_of_le_normalizer_B1 hXp hXN
  rw [← hS.card_T1] at h1
  have heq := eq_of_le_of_card_ge (le_sup_left : miyamotoF1G h L η t ⊔ T ≤ _) h1
  exact hyT' (by rw [heq]; exact mem_sup_right (mem_zpowers _))

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
