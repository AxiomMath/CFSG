module

public import CFSG.LocalAnalysis.EvenBN.U4.RootR
public import CFSG.LocalAnalysis.EvenBN.U5.Prelim

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_sup mem_normalizer_inf
  exists_mem_inf_centralizer_mul_of_coprime centralizerMod mem_centralizerMod)

section Model

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem eq_zero_of_forall_commute_rootC {a : K}
    (hc : ∀ c : K, miyamotoXGL h a 0 0 0 * miyamotoXGL h 0 0 c 0 =
      miyamotoXGL h 0 0 c 0 * miyamotoXGL h a 0 0 0) : a = 0 := by
  by_contra ha
  obtain ⟨ω, hω⟩ : ∃ ω : K, ω + h.bar ω = 1 := by
    obtain ⟨ω, hω⟩ := h.traceLin_surjective 1
    exact ⟨ω, congrArg Subtype.val hω⟩
  have e := hc (a * ω)
  rw [miyamotoXGL_mul h (map_zero _), miyamotoXGL_mul h (map_zero _), miyamotoXGL_inj] at e
  have e4 := e.2.2.2
  simp only [map_zero, mul_zero, add_zero, zero_add, map_mul] at e4
  have hba : h.bar a ≠ 0 := (map_ne_zero _).2 ha
  have h1 : h.bar a * a * (ω + h.bar ω) = 0 := by
    linear_combination e4 + (h.bar a * a * h.bar ω) * CharTwo.two_eq_zero (R := K)
  rw [hω, mul_one] at h1
  exact mul_ne_zero hba ha h1

end Model

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem eq_one_of_mem_rootA_of_commute_rootC (hS : Setting h L η t Q T) {u : G}
    (hu : u ∈ miyamotoPull h L η (miyamotoRootA h))
    (hc : ∀ c ∈ miyamotoPull h L η (miyamotoRootC h), u * c = c * u) : u = 1 := by
  have : CharP K 2 := h.charP
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hu
  obtain ⟨a, ha⟩ := hg
  have key : a = 0 := by
    refine eq_zero_of_forall_commute_rootC h fun c => ?_
    have hcS : miyamotoXGL h 0 0 c 0 ∈ gramSU h (miyamotoJ4 K) := hS.rootC_le_SU ⟨c, rfl⟩
    have h1 := hc _ ((symm_mem_miyamotoPull_iff h L η (g := ⟨_, hcS⟩)).2 ⟨c, rfl⟩)
    have h2 : g * ⟨_, hcS⟩ = ⟨_, hcS⟩ * g := by
      apply η.symm.injective
      apply Subtype.ext
      rw [map_mul, map_mul, L.coe_mul, L.coe_mul]
      exact h1
    have h3 := congrArg Subtype.val h2
    simp only [coe_mul] at h3
    rw [← ha]
    exact h3
  have hg1 : g = 1 := by
    apply Subtype.ext
    rw [ha, key, miyamotoXGL_zero, OneMemClass.coe_one]
  rw [hg1, map_one, OneMemClass.coe_one]

theorem normalizer_P1_le_normalizer_E (hS : Setting h L η t Q T) :
    normalizer ((miyamotoF1G h L η t ⊔ miyamotoPG h L η : Subgroup G) : Set G) ≤
      normalizer (miyamotoEG h L η Q : Set G) := by
  rw [← hS.centerIn_P1]
  exact normalizer_le_normalizer_centerIn _

theorem RG_le_normalizer_E (hS : Setting h L η t Q T) :
    miyamotoRG h L η t Q ≤ normalizer (miyamotoEG h L η Q : Set G) :=
  hS.RG_le_normalizer_P1.trans hS.normalizer_P1_le_normalizer_E

theorem normalizer_P1_le_normalizer_F (hS : Setting h L η t Q T) :
    normalizer ((miyamotoF1G h L η t ⊔ miyamotoPG h L η : Subgroup G) : Set G) ≤
      normalizer (miyamotoFG h L η t Q : Set G) := by
  intro g hg
  have key : ∀ g ∈ normalizer ((miyamotoF1G h L η t ⊔ miyamotoPG h L η : Subgroup G) : Set G),
      ∀ φ ∈ miyamotoFG h L η t Q, g * φ * g⁻¹ ∈ miyamotoFG h L η t Q := by
    intro g hg φ hφ
    have hφP1 : φ ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η := mem_sup_left (hS.F_le_F1 hφ)
    have hgφ : g * φ * g⁻¹ ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η :=
      (mem_normalizer_iff.1 hg φ).1 hφP1
    refine hS.mem_F_of_commutator_mem_E hgφ fun y hy => ?_
    have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η :=
      (mem_normalizer_iff.1 (inv_mem hg) y).1 hy
    have h1 := hS.commutator_F_P1_mem_E hφ hy'
    have h2 := (mem_normalizer_iff.1 (hS.normalizer_P1_le_normalizer_E hg) _).1 h1
    rw [show g * (φ * (g⁻¹ * y * g⁻¹⁻¹) * φ⁻¹ * (g⁻¹ * y * g⁻¹⁻¹)⁻¹) * g⁻¹ =
      g * φ * g⁻¹ * y * (g * φ * g⁻¹)⁻¹ * y⁻¹ by group] at h2
    exact h2
  exact mem_normalizer_iff.2 fun φ => ⟨key g hg φ, fun h' => by
    have := key g⁻¹ (inv_mem hg) _ h'
    rwa [show g⁻¹ * (g * φ * g⁻¹) * g⁻¹⁻¹ = φ by group] at this⟩

theorem RG_le_normalizer_F (hS : Setting h L η t Q T) :
    miyamotoRG h L η t Q ≤ normalizer (miyamotoFG h L η t Q : Set G) :=
  hS.RG_le_normalizer_P1.trans hS.normalizer_P1_le_normalizer_F

theorem F_le_RG (hS : Setting h L η t Q T) : miyamotoFG h L η t Q ≤ miyamotoRG h L η t Q :=
  fun _ hx => hS.P1_le_miyamotoRG (mem_sup_left (hS.F_le_F1 hx))

theorem E_le_RG (hS : Setting h L η t Q T) : miyamotoEG h L η Q ≤ miyamotoRG h L η t Q :=
  hS.E_le_F.trans hS.F_le_RG

theorem RG_le_centralizer_E (hS : Setting h L η t Q T) :
    miyamotoRG h L η t Q ≤ centralizer (miyamotoEG h L η Q : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : miyamotoI2r1G h L η ≤ miyamotoIG h L η := hS.tori_le_IG.2.2.1
  have key := le_centralizer_of_yamada (p := 2) (A := miyamotoRG h L η t Q)
    (X := miyamotoI2r1G h L η) hS.isPGroup_RG
    (fun hd => Nat.not_even_iff_odd.2 hS.odd_card_S (even_iff_two_dvd.2 hd))
    (hX.trans hS.IG_le_normalizer_RG)
    (by rw [hS.RG_inf_centralizer_I2r1]; exact hS.RG_le_normalizer_E)
    (by
      rw [hS.RG_inf_centralizer_I2r1]
      exact fun c hc c' hc' => hS.F1_comm (hS.E_le_F1 hc) (hS.E_le_F1 hc'))
  rwa [hS.RG_inf_centralizer_I2r1] at key

theorem commutator_W_Yc_mem_E (hS : Setting h L η t Q T) {w y : G}
    (hw : w ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G))
    (hy : y ∈ miyamotoF1G h L η t ⊓ centralizer (miyamotoPull h L η (miyamotoI1r2 h) : Set G)) :
    w⁻¹ * y⁻¹ * w * y ∈ miyamotoEG h L η Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) with hWdef
  set J₁ := miyamotoI1G h L η
  set J₂ := miyamotoPull h L η (miyamotoI1r2 h)
  have hJ₁ : J₁ ≤ miyamotoIG h L η := hS.I1G_le_IG
  have hJ₂ : J₂ ≤ miyamotoIG h L η := hS.tori_le_IG.2.1
  have hJ : J₁ ⊔ J₂ ≤ miyamotoIG h L η := sup_le hJ₁ hJ₂
  set A := W ⊔ miyamotoFG h L η t Q with hAdef
  have hAR : A ≤ miyamotoRG h L η t Q := sup_le inf_le_left hS.F_le_RG
  have hWF : W ≤ normalizer (miyamotoFG h L η t Q : Set G) :=
    inf_le_left.trans hS.RG_le_normalizer_F
  have hIW : miyamotoIG h L η ≤ normalizer (W : Set G) := fun i hi =>
    mem_normalizer_inf (hS.IG_le_normalizer_RG hi) (hS.IG_le_normalizer_centralizer hJ₁ hi)
  have hJA : J₁ ⊔ J₂ ≤ normalizer (A : Set G) := fun j hj =>
    mem_normalizer_sup (hIW (hJ hj)) (hS.IG_le_normalizer_FG (hJ hj))
  have hERc := hS.RG_le_centralizer_E
  have hE := gomi_commutator_mem_conj (p := 2) (A := A) (N := miyamotoEG h L η Q) (J₁ := J₁)
    (J₂ := J₂) (hS.isPGroup_RG.to_le hAR)
    (fun hd => Nat.not_even_iff_odd.2 (hS.odd_card_of_le_IG hJ) (even_iff_two_dvd.2 hd))
    hJA (fun j hj => hS.IG_le_normalizer_E (hJ hj)) (hS.le_normalizer_of_le_IG hJ₁ hJ₂)
    (hS.le_normalizer_of_le_IG hJ₂ hJ₁) (hS.E_le_F.trans le_sup_right)
    (fun a ha => hS.RG_le_normalizer_E (hAR ha))
    (fun a ha => by
      have ha' : a ∈ ((W ⊔ miyamotoFG h L η t Q : Subgroup G) : Set G) := ha
      rw [Subgroup.coe_mul_of_left_le_normalizer_right W _ hWF] at ha'
      obtain ⟨w', hw', φ, hφ, rfl⟩ := ha'
      obtain ⟨e, he, y', hy', rfl⟩ := hS.exists_mul_of_mem_F hφ
      refine ⟨w', ⟨mem_sup_left hw', hw'.2⟩, y', ⟨mem_sup_right (mem_sup_right hy'), hy'.2⟩,
        e, he, ?_⟩
      have hey : e * y' = y' * e := hS.F1_comm (hS.E_le_F1 he) hy'.1
      rw [hey, mul_assoc])
    (by
      rintro x ⟨⟨hxA, hx₁⟩, ⟨-, hx₂⟩⟩
      obtain ⟨-, ⟨p, hp, hpX, hpA⟩, -⟩ := hS.exists_torusElt_weightA_ne_one
      have hxF := hS.RG_inf_centralizer_le_F1 hpX hpA (mem_inf.2 ⟨hAR hxA, hx₂⟩)
      have : x ∈ miyamotoF1G h L η t ⊓ centralizer (J₁ : Set G) := mem_inf.2 ⟨hxF, hx₁⟩
      rw [hS.F1_inf_centralizer_I1, mem_bot] at this
      rw [this]
      exact one_mem _)
  exact hE w ⟨mem_sup_left hw, hw.2⟩ y ⟨mem_sup_right (mem_sup_right hy), hy.2⟩

theorem commutator_F_RG_mem_E (hS : Setting h L η t Q T) {φ r : G}
    (hφ : φ ∈ miyamotoFG h L η t Q) (hr : r ∈ miyamotoRG h L η t Q) :
    φ * r * φ⁻¹ * r⁻¹ ∈ miyamotoEG h L η Q := by
  obtain ⟨w, hw, y, hy, rfl⟩ := hS.exists_mul_of_mem_RG hr
  obtain ⟨e, he, c, hc, rfl⟩ := hS.exists_mul_of_mem_F hφ
  have hcF : c ∈ miyamotoF1G h L η t := hc.1
  have hcR : c ∈ miyamotoRG h L η t Q := hS.P1_le_miyamotoRG (mem_sup_left hcF)
  have hwR : w ∈ miyamotoRG h L η t Q := hw.1
  have hyc : y * c = c * y := hS.F1_comm hy hcF
  have hyc' : y * c⁻¹ = c⁻¹ * y := by
    calc y * c⁻¹ = c⁻¹ * (c * y) * c⁻¹ := by group
      _ = c⁻¹ * (y * c) * c⁻¹ := by rw [hyc]
      _ = c⁻¹ * y := by group
  have hX := hS.commutator_W_Yc_mem_E hw hc
  have hz : c * w * (w⁻¹ * c⁻¹ * w * c)⁻¹ * (c * w)⁻¹ ∈ miyamotoEG h L η Q :=
    (mem_normalizer_iff.1 (hS.RG_le_normalizer_E (mul_mem hcR hwR)) _).1 (inv_mem hX)
  have hyR : y ∈ miyamotoRG h L η t Q := hS.P1_le_miyamotoRG (mem_sup_left hy)
  have hXR : c * w * y * c⁻¹ ∈ miyamotoRG h L η t Q :=
    mul_mem (mul_mem (mul_mem hcR hwR) hyR) (inv_mem hcR)
  have heX : e * (c * w * y * c⁻¹) = (c * w * y * c⁻¹) * e :=
    (mem_centralizer_iff.1 (hS.RG_le_centralizer_E hXR) e he)
  have key : e * c * (w * y) * (e * c)⁻¹ * (w * y)⁻¹ =
      c * w * (w⁻¹ * c⁻¹ * w * c)⁻¹ * (c * w)⁻¹ := by
    calc e * c * (w * y) * (e * c)⁻¹ * (w * y)⁻¹ =
        e * (c * w * y * c⁻¹) * e⁻¹ * (w * y)⁻¹ := by group
      _ = (c * w * y * c⁻¹) * e * e⁻¹ * (w * y)⁻¹ := by rw [heX]
      _ = c * w * (y * c⁻¹) * y⁻¹ * w⁻¹ := by group
      _ = c * w * (c⁻¹ * y) * y⁻¹ * w⁻¹ := by rw [hyc']
      _ = c * w * (w⁻¹ * c⁻¹ * w * c)⁻¹ * (c * w)⁻¹ := by group
  rw [key]
  exact hz

theorem exists_ne_one_commute_t (hS : Setting h L η t Q T) {X : Subgroup G} (hX2 : IsPGroup 2 X)
    (hX : X ≠ ⊥) (htX : t ∈ normalizer (X : Set G)) : ∃ x ∈ X, x ≠ 1 ∧ x * t = t * x := by
  have key := CFSG.LocalAnalysis.EvenBN.U5.Prelim.inf_centralizer_ne_bot_of_pow_mem hX2 hX
    (Y := zpowers t) (zpowers_le.2 htX) fun y hy => ⟨1, by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
      have e : (t ^ k) ^ 2 ^ 1 = 1 := by
        rcases hS.zpow_t_eq k with e | e <;> rw [e]
        · exact one_pow _
        · rw [pow_one, sq, hS.t_mul_t]
      rw [e]
      exact one_mem _⟩
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 key
  refine ⟨x, (mem_inf.1 hx).1, fun e => hx1 (Subtype.ext e), ?_⟩
  exact (mem_centralizer_iff.1 (mem_inf.1 hx).2 t (mem_zpowers t)).symm

theorem t_mem_normalizer_RG (hS : Setting h L η t Q T) :
    t ∈ normalizer (miyamotoRG h L η t Q : Set G) :=
  hS.miyamotoS_le_normalizer_RG (hS.Q1_le_miyamotoS (mem_sup_right hS.t_mem_Q))

theorem t_mem_normalizer_P1 (hS : Setting h L η t Q T) :
    t ∈ normalizer ((miyamotoF1G h L η t ⊔ miyamotoPG h L η : Subgroup G) : Set G) :=
  hS.miyamotoS_le_normalizer_P1 (hS.Q1_le_miyamotoS (mem_sup_right hS.t_mem_Q))

theorem t_mem_normalizer_centralizer_I1 (hS : Setting h L η t Q T) :
    t ∈ normalizer (centralizer (miyamotoI1G h L η : Set G) : Set G) :=
  le_normalizer (mem_centralizer_iff.2 fun _ hs => mem_centralizer_singleton_iff.1 (hS.I1_le_C hs))

theorem mem_F_of_mem_RG_of_commutator (hS : Setting h L η t Q T) {x : G}
    (hx : x ∈ miyamotoRG h L η t Q)
    (hc : ∀ r ∈ miyamotoRG h L η t Q, x * r * x⁻¹ * r⁻¹ ∈ miyamotoEG h L η Q) :
    x ∈ miyamotoFG h L η t Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := miyamotoRG h L η t Q with hRdef
  set E := miyamotoEG h L η Q with hEdef
  have hRE : ∀ g ∈ R, ∀ b ∈ E, g * b * g⁻¹ ∈ E := fun g hg b hb =>
    (mem_normalizer_iff.1 (hS.RG_le_normalizer_E hg) b).1 hb
  set Z := centralizerMod R R E (fun g hg y hy => mul_mem (mul_mem hg hy) (inv_mem hg)) hRE
    with hZdef
  have hZR : Z ≤ R := fun z hz => hz.1
  have hZ2 : IsPGroup 2 Z := hS.isPGroup_RG.to_le hZR
  have hinv : ∀ g, g ∈ normalizer (R : Set G) → g ∈ normalizer (E : Set G) →
      g ∈ normalizer (Z : Set G) := by
    intro g hgR hgE
    refine mem_normalizer_fintype fun z hz => ⟨(mem_normalizer_iff.1 hgR z).1 hz.1,
      fun r hr => ?_⟩
    have hr' : g⁻¹ * r * g⁻¹⁻¹ ∈ R := (mem_normalizer_iff.1 (inv_mem hgR) r).1 hr
    have h1 := (mem_normalizer_iff.1 hgE _).1 (hz.2 _ hr')
    rwa [show g * (z * (g⁻¹ * r * g⁻¹⁻¹) * z⁻¹ * (g⁻¹ * r * g⁻¹⁻¹)⁻¹) * g⁻¹ =
      g * z * g⁻¹ * r * (g * z * g⁻¹)⁻¹ * r⁻¹ by group] at h1
  have hIZ : miyamotoIG h L η ≤ normalizer (Z : Set G) := fun i hi =>
    hinv i (hS.IG_le_normalizer_RG hi) (hS.IG_le_normalizer_E hi)
  have htZ : t ∈ normalizer (Z : Set G) :=
    hinv t hS.t_mem_normalizer_RG (hS.normalizer_P1_le_normalizer_E hS.t_mem_normalizer_P1)
  have hY : Z ⊓ centralizer (miyamotoI1G h L η : Set G) = ⊥ := by
    by_contra hne
    obtain ⟨y, hy, hy1, hyt⟩ := hS.exists_ne_one_commute_t (hZ2.to_le inf_le_left) hne
      (mem_normalizer_inf htZ hS.t_mem_normalizer_centralizer_I1)
    obtain ⟨hyZ, hyI⟩ := mem_inf.1 hy
    have hyP : y ∈ miyamotoPG h L η := by
      rw [← hS.RG_inf_C]
      exact mem_inf.2 ⟨hyZ.1, mem_centralizer_singleton_iff.2 hyt⟩
    have hyA : y ∈ miyamotoA1G h L η := hS.mem_A1_of_commutator_mem_ZP hyP fun a ha => by
      have haP := hS.A1G_le_PG ha
      rw [← hS.E_inf_PG]
      exact mem_inf.2 ⟨hyZ.2 a (le_sup_right.trans hS.P1_le_miyamotoRG haP),
        mul_mem (mul_mem (mul_mem hyP haP) (inv_mem hyP)) (inv_mem haP)⟩
    have : y ∈ miyamotoA1G h L η ⊓ centralizer (miyamotoI1G h L η : Set G) := mem_inf.2 ⟨hyA, hyI⟩
    rw [hS.A1G_inf_centralizer_I1, mem_bot] at this
    exact hy1 this
  have hI1 : miyamotoI1G h L η ≤ miyamotoIG h L η := hS.I1G_le_IG
  have hsolv : Group.IsSolvable Z := by
    have := hZ2.isNilpotent
    infer_instance
  have hcop := coprime_of_odd_of_isPGroup (hS.odd_card_of_le_IG hI1) hZ2
  have hxZ : x ∈ Z := ⟨hx, hc⟩
  have hZP : Z ≤ normalizer ((Z ⊓ (miyamotoF1G h L η t ⊔ miyamotoPG h L η) : Subgroup G) :
      Set G) := fun z hz => mem_normalizer_inf (le_normalizer hz) (hS.RG_le_normalizer_P1 (hZR hz))
  obtain ⟨c, hc', n, hn, rfl⟩ := exists_mem_inf_centralizer_mul_of_coprime inf_le_left hZP
    (hI1.trans hIZ)
    (fun _ hs => mem_normalizer_inf (hIZ (hI1 hs)) (hS.IG_le_normalizer_P1 (hI1 hs)))
    hsolv hcop hxZ fun s hs => by
      refine mem_inf.2 ⟨mul_mem (inv_mem hxZ) ((mem_normalizer_iff.1 (hIZ (hI1 hs)) x).1 hxZ), ?_⟩
      exact hS.inv_mul_conj_mem_P1_of_mem_I1 hx hs
  have hc1 : c = 1 := by
    have : c ∈ Z ⊓ centralizer (miyamotoI1G h L η : Set G) := hc'
    rw [hY, mem_bot] at this
    exact this
  rw [hc1, one_mul]
  obtain ⟨hnZ, hnP⟩ := mem_inf.1 hn
  exact hS.mem_F_of_commutator_mem_E hnP fun y hy => hnZ.2 y (hS.P1_le_miyamotoRG hy)

theorem mem_F_iff_of_mem_RG (hS : Setting h L η t Q T) {x : G} (hx : x ∈ miyamotoRG h L η t Q) :
    x ∈ miyamotoFG h L η t Q ↔
      ∀ r ∈ miyamotoRG h L η t Q, x * r * x⁻¹ * r⁻¹ ∈ miyamotoEG h L η Q :=
  ⟨fun hxF _ hr => hS.commutator_F_RG_mem_E hxF hr, hS.mem_F_of_mem_RG_of_commutator hx⟩

theorem centerIn_RG (hS : Setting h L η t Q T) :
    CFSG.centerIn (miyamotoRG h L η t Q) = miyamotoEG h L η Q := by
  refine le_antisymm (fun z hz => ?_) fun e he => mem_inf.2 ⟨hS.E_le_RG he,
    mem_centralizer_iff.2 fun r hr => (mem_centralizer_iff.1 (hS.RG_le_centralizer_E hr) e he).symm⟩
  obtain ⟨hzR, hzC⟩ := mem_inf.1 hz
  have hzF : z ∈ miyamotoFG h L η t Q := hS.mem_F_of_mem_RG_of_commutator hzR fun r hr => by
    rw [← mem_centralizer_iff.1 hzC r hr, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  rw [← hS.centerIn_P1]
  exact mem_inf.2 ⟨mem_sup_left (hS.F_le_F1 hzF),
    centralizer_le (SetLike.coe_subset_coe.2 hS.P1_le_miyamotoRG) hzC⟩

theorem RG_inf_centralizer_F (hS : Setting h L η t Q T) :
    miyamotoRG h L η t Q ⊓ centralizer (miyamotoFG h L η t Q : Set G) = miyamotoF1G h L η t := by
  set R := miyamotoRG h L η t Q with hRdef
  have hF1C : ∀ y ∈ miyamotoF1G h L η t, y ∈ centralizer (miyamotoFG h L η t Q : Set G) :=
    fun y hy => mem_centralizer_iff.2 fun φ hφ => hS.F1_comm (hS.F_le_F1 hφ) hy
  refine le_antisymm (fun x hx => ?_)
    (le_inf (le_sup_left.trans hS.P1_le_miyamotoRG) fun y hy => hF1C y hy)
  set Y := R ⊓ centralizer (miyamotoFG h L η t Q : Set G) ⊓
    centralizer (miyamotoI1G h L η : Set G) with hYdef
  have htF : t ∈ normalizer (miyamotoFG h L η t Q : Set G) :=
    hS.normalizer_P1_le_normalizer_F hS.t_mem_normalizer_P1
  have hY : Y = ⊥ := by
    by_contra hne
    obtain ⟨y, hy, hy1, hyt⟩ := hS.exists_ne_one_commute_t
      (hS.isPGroup_RG.to_le (inf_le_left.trans inf_le_left)) hne
      (mem_normalizer_inf (mem_normalizer_inf hS.t_mem_normalizer_RG
        (mem_normalizer_centralizer htF)) hS.t_mem_normalizer_centralizer_I1)
    obtain ⟨⟨hyR, hyF⟩, hyI⟩ := hy
    have hyP : y ∈ miyamotoPG h L η := by
      rw [← hS.RG_inf_C]
      exact mem_inf.2 ⟨hyR, mem_centralizer_singleton_iff.2 hyt⟩
    have hyU : y ∈ miyamotoPull h L η (miyamotoRootA h) := by
      rw [← hS.PG_inf_centralizer_I1]
      exact mem_inf.2 ⟨hyP, hyI⟩
    exact hy1 (hS.eq_one_of_mem_rootA_of_commute_rootC hyU fun c hc =>
      (mem_centralizer_iff.1 hyF c (hS.Z2_le_F (hS.rootC_le_Z2 hc))).symm)
  obtain ⟨hxR, hxF⟩ := mem_inf.1 hx
  obtain ⟨w, hw, y, hy, rfl⟩ := hS.exists_mul_of_mem_RG hxR
  have hwY : w ∈ Y := by
    refine mem_inf.2 ⟨mem_inf.2 ⟨hw.1, ?_⟩, hw.2⟩
    have := mul_mem hxF (inv_mem (hF1C y hy))
    rwa [mul_inv_cancel_right] at this
  rw [hY, mem_bot] at hwY
  rw [hwY, one_mul]
  exact hy

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
