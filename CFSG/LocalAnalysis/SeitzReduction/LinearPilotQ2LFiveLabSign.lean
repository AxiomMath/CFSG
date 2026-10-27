module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveLabModel
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveLabLift

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

section LiftIn

variable {G : Type*} [Group G]

noncomputable def liftIn (t : G) (A : Subgroup G) (y : G) : G := by
  classical
  exact if h : ∃ x ∈ A, x * (t * x * t⁻¹) = y then h.choose else 1

theorem liftIn_spec {t : G} {A : Subgroup G} {y : G} (h : ∃ x ∈ A, x * (t * x * t⁻¹) = y) :
    liftIn t A y ∈ A ∧ liftIn t A y * (t * liftIn t A y * t⁻¹) = y := by
  classical
  unfold liftIn
  split_ifs
  exact h.choose_spec

theorem liftIn_eq {t : G} {A : Subgroup G}
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G))
    (hAA : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥) {x y : G} (hx : x ∈ A)
    (hxy : x * (t * x * t⁻¹) = y) : liftIn t A y = x := by
  obtain ⟨h1, h2⟩ := liftIn_spec ⟨x, hx, hxy⟩
  exact eq_of_mem_of_diag_eq hA hAA h1 hx (h2.trans hxy.symm)

theorem liftIn_mul {t : G} {A : Subgroup G}
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G))
    (hAA : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥) {y y' : G}
    (h : ∃ x ∈ A, x * (t * x * t⁻¹) = y) (h' : ∃ x ∈ A, x * (t * x * t⁻¹) = y') :
    liftIn t A (y * y') = liftIn t A y * liftIn t A y' := by
  obtain ⟨h1, h2⟩ := liftIn_spec h
  obtain ⟨h1', h2'⟩ := liftIn_spec h'
  apply liftIn_eq hA hAA (mul_mem h1 h1')
  rw [swapDiag_mul hA h1 h1', h2, h2']

theorem liftIn_conj {t : G} {A : Subgroup G}
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G))
    (hAA : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥) {a y : G} (ha : a ∈ A)
    (hqt : (a * (t * a * t⁻¹)) * t = t * (a * (t * a * t⁻¹)))
    (h : ∃ x ∈ A, x * (t * x * t⁻¹) = y) :
    liftIn t A ((a * (t * a * t⁻¹)) * y * (a * (t * a * t⁻¹))⁻¹) =
      (a * (t * a * t⁻¹)) * liftIn t A y * (a * (t * a * t⁻¹))⁻¹ := by
  obtain ⟨h1, h2⟩ := liftIn_spec h
  apply liftIn_eq hA hAA
  · rw [diag_conj_eq_conj hA ha h1]
    exact mul_mem (mul_mem ha h1) (inv_mem ha)
  · rw [diag_conj hqt, h2]

theorem liftIn_mul_self {t : G} {A : Subgroup G}
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G))
    (hAA : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥) {y : G} (hy : y * y = 1)
    (h : ∃ x ∈ A, x * (t * x * t⁻¹) = y) : liftIn t A y * liftIn t A y = 1 := by
  rw [← liftIn_mul hA hAA h h, hy]
  exact liftIn_eq hA hAA (one_mem A) (by group)

theorem liftIn_comm {t : G} {A : Subgroup G}
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G)) {y : G}
    (h : ∃ x ∈ A, x * (t * x * t⁻¹) = y) :
    liftIn t A y * (t * liftIn t A y * t⁻¹) = (t * liftIn t A y * t⁻¹) * liftIn t A y :=
  (conj_mul_comm_of_mem hA (liftIn_spec h).1 (liftIn_spec h).1).symm

end LiftIn

section Unique

variable {G : Type*} [Group G] [Finite G]

theorem lift_le_of_unique {t : G} {R A W : Subgroup G}
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G))
    (hAA : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥)
    (hAR : ∀ a ∈ A, a * (t * a * t⁻¹) ∈ R) (hRA : ∀ v ∈ R, ∃ a ∈ A, a * (t * a * t⁻¹) = v)
    (hR2 : ∀ v ∈ R, v * v = 1) (hRt : ∀ v ∈ R, v * t = t * v)
    (hU : ∀ E : Subgroup G, E ≤ seitzRadX R t → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      Nat.card E = Nat.card R * Nat.card R → E = W) : A ≤ W := by
  have hRc : ∀ v ∈ R, ∀ w ∈ R, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hR2 hv hw
  set δ := linearSwapDiag hA with hδ
  have hinj := linearSwapDiag_injective hA hAA
  have hδapp : ∀ a : A, (δ a : G) = a * (t * a * t⁻¹) := fun a => rfl
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have h := hinj (a₁ := ⟨a, ha⟩ * ⟨b, hb⟩) (a₂ := ⟨b, hb⟩ * ⟨a, ha⟩) (by
      rw [map_mul, map_mul, hδapp, hδapp]
      exact hRc _ (hAR a ha) _ (hAR b hb))
    exact congrArg Subtype.val h
  have hA2 : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    have h := hinj (a₁ := ⟨a, ha⟩ * ⟨a, ha⟩) (a₂ := 1) (by
      rw [map_mul, map_one, hδapp]
      exact hR2 _ (hAR a ha))
    exact congrArg Subtype.val h
  set B := A.map (MulAut.conj t).toMonoidHom with hB
  have hconjB : ∀ b ∈ B, ∃ a ∈ A, b = t * a * t⁻¹ := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  have hBA : B ≤ centralizer (A : Set G) := hA
  have hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := by
    intro b hb b' hb'
    obtain ⟨a, ha, rfl⟩ := hconjB b hb
    obtain ⟨a', ha', rfl⟩ := hconjB b' hb'
    calc t * a * t⁻¹ * (t * a' * t⁻¹) = t * (a * a') * t⁻¹ := by group
      _ = t * (a' * a) * t⁻¹ := by rw [hAc a ha a' ha']
      _ = t * a' * t⁻¹ * (t * a * t⁻¹) := by group
  have hEC : A ⊔ B ≤ centralizer ((A ⊔ B : Subgroup G) : Set G) := by
    rw [le_centralizer_iff]
    refine sup_le ?_ ?_
    · refine (le_centralizer_iff.1 (sup_le (fun a ha => mem_centralizer_iff.2 fun b hb =>
        (hAc a ha b hb).symm) hBA))
    · refine le_centralizer_iff.1 (sup_le (le_centralizer_iff.1 hBA) fun b hb =>
        mem_centralizer_iff.2 fun b' hb' => (hBc b hb b' hb').symm)
  have hEab : ∀ a ∈ A ⊔ B, ∀ b ∈ A ⊔ B, a * b = b * a := fun a ha b hb =>
    mem_centralizer_iff.1 (hEC hb) a ha
  have hcomm : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) := fun a b =>
    (mem_centralizer_iff.1 (hBA b.2) a a.2)
  have hrange := MonoidHom.noncommCoprod_range A.subtype B.subtype hcomm
  rw [range_subtype, range_subtype] at hrange
  have hinjE : Function.Injective (A.subtype.noncommCoprod B.subtype hcomm) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    rw [MonoidHom.noncommCoprod_apply] at hab
    have hb : (b : G) = (a : G)⁻¹ := eq_inv_of_mul_eq_one_right hab
    have hmem : (a : G)⁻¹ ∈ A ⊓ B := mem_inf.2 ⟨inv_mem a.2, hb ▸ b.2⟩
    rw [hAA, mem_bot, inv_eq_one] at hmem
    have hb1 : (b : G) = 1 := by rw [hb, hmem, inv_one]
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hb1)
  have hcardE : Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
    rw [← hrange, ← Nat.card_prod]
    exact (Nat.card_congr (MonoidHom.ofInjective hinjE).toEquiv).symm
  have hcardB : Nat.card B = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj t).injective
  have hcardA : Nat.card A = Nat.card R := by
    have hrangeδ : δ.range = R := by
      refine le_antisymm ?_ fun v hv => ?_
      · rintro _ ⟨a, rfl⟩
        exact hAR a a.2
      · obtain ⟨a, ha, rfl⟩ := hRA v hv
        exact ⟨⟨a, ha⟩, rfl⟩
    rw [← hrangeδ]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hAR' : A ≤ centralizer (R : Set G) := by
    intro a ha
    rw [mem_centralizer_iff]
    intro v hv
    obtain ⟨b, hb, rfl⟩ := hRA v hv
    have h1 := hAc a ha b hb
    calc b * (t * b * t⁻¹) * a = b * ((t * b * t⁻¹) * a) := by group
      _ = b * (a * (t * b * t⁻¹)) := by rw [conj_mul_comm_of_mem hA hb ha]
      _ = a * (b * (t * b * t⁻¹)) := by rw [← mul_assoc, ← h1, mul_assoc]
  have hBR : B ≤ centralizer (R : Set G) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hconjB x hx
    rw [mem_centralizer_iff]
    intro v hv
    obtain ⟨b, hb, rfl⟩ := hRA v hv
    have h1 : (t * b * t⁻¹) * (t * a * t⁻¹) = (t * a * t⁻¹) * (t * b * t⁻¹) :=
      hBc _ ⟨b, hb, rfl⟩ _ ⟨a, ha, rfl⟩
    have h2 : (t * a * t⁻¹) * b = b * (t * a * t⁻¹) := conj_mul_comm_of_mem hA ha hb
    calc b * (t * b * t⁻¹) * (t * a * t⁻¹) = b * ((t * b * t⁻¹) * (t * a * t⁻¹)) := by group
      _ = b * ((t * a * t⁻¹) * (t * b * t⁻¹)) := by rw [h1]
      _ = (t * a * t⁻¹) * (b * (t * b * t⁻¹)) := by rw [← mul_assoc, ← h2, mul_assoc]
  have hnorm : ∀ x ∈ A ⊔ B, x * t * x⁻¹ ∈ R ⊔ zpowers t →
      x ∈ centralizer (R : Set G) → x ∈ normalizer ((R ⊔ zpowers t : Subgroup G) : Set G) := by
    intro x _ hxt hxR
    have hle : (R ⊔ zpowers t).map (MulAut.conj x).toMonoidHom ≤ R ⊔ zpowers t := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      refine sup_le ?_ ?_
      · rintro _ ⟨v, hv, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [← mem_centralizer_iff.1 hxR v hv, mul_inv_cancel_right]
        exact mem_sup_left hv
      · rw [zpowers_le]
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hxt
    have heq : (R ⊔ zpowers t).map (MulAut.conj x).toMonoidHom = R ⊔ zpowers t := by
      apply Subgroup.eq_of_le_of_card_ge hle
      rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hle ⟨h, hh, rfl⟩
    · intro hh
      rw [← heq] at hh
      obtain ⟨h', hh', he⟩ := hh
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he
      have : h' = h := mul_left_cancel (mul_right_cancel he)
      rwa [← this]
  have hAc' : ∀ a ∈ A, a * (t * a * t⁻¹) = (t * a * t⁻¹) * a := fun a ha =>
    (conj_mul_comm_of_mem hA ha ha).symm
  have hAN : A ≤ normalizer ((R ⊔ zpowers t : Subgroup G) : Set G) := by
    intro a ha
    refine hnorm a (mem_sup_left ha) ?_ (hAR' ha)
    rw [conj_t_eq_of_diag (hA2 a ha) (hAc' a ha) rfl]
    exact mul_mem (inv_mem (mem_sup_left (hAR a ha))) (mem_sup_right (mem_zpowers t))
  have hBN : B ≤ normalizer ((R ⊔ zpowers t : Subgroup G) : Set G) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hconjB x hx
    refine hnorm _ (mem_sup_right hx) ?_ (hBR hx)
    have h1 := conj_t_eq_of_diag (hA2 a ha) (hAc' a ha) rfl
    have hv := hRt _ (hAR a ha)
    have h2 : t * a * t⁻¹ * t * (t * a * t⁻¹)⁻¹ = (a * (t * a * t⁻¹))⁻¹ * t := by
      calc t * a * t⁻¹ * t * (t * a * t⁻¹)⁻¹ = t * (a * t * a⁻¹) * t⁻¹ := by group
        _ = t * ((a * (t * a * t⁻¹))⁻¹ * t) * t⁻¹ := by rw [h1]
        _ = t * (a * (t * a * t⁻¹))⁻¹ := by group
        _ = (a * (t * a * t⁻¹))⁻¹ * ((a * (t * a * t⁻¹)) * t) * (a * (t * a * t⁻¹))⁻¹ := by
          group
        _ = (a * (t * a * t⁻¹))⁻¹ * (t * (a * (t * a * t⁻¹))) * (a * (t * a * t⁻¹))⁻¹ := by
          rw [hv]
        _ = (a * (t * a * t⁻¹))⁻¹ * t := by group
    rw [h2]
    exact mul_mem (inv_mem (mem_sup_left (hAR a ha))) (mem_sup_right (mem_zpowers t))
  have hEX : A ⊔ B ≤ seitzRadX R t := fun x hx =>
    mem_seitzRadX.2 ⟨(sup_le hAR' hBR) hx, (sup_le hAN hBN) hx⟩
  have hE := hU (A ⊔ B) hEX hEab (by rw [hcardE, hcardB, hcardA])
  rw [← hE]
  exact le_sup_left

end Unique

section Members

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K] [CharP K 2]

noncomputable abbrev pointParabolic (e : L ≃* LinearFlag.projectiveSL n K) (c : Fin n) : Subgroup G :=
  modelToG e (pointRadical (K := K) c) ⊔ modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n)))

omit [CharP K 2] in
theorem linTv_mem_pointParabolic (e : L ≃* LinearFlag.projectiveSL n K) {c i j : Fin n}
    (hij : i ≠ j) (hjc : j ≠ c) : linTv e hij ∈ pointParabolic e c := by
  by_cases hic : i = c
  · subst hic
    exact mem_sup_left (linTv_mem_pointRadical e hij)
  · exact mem_sup_right (linTv_mem e hij hic hjc)

theorem linTv_mem_pointParabolic_dual (e : L ≃* LinearFlag.projectiveSL n K) {c i j : Fin n}
    (hij : i ≠ j) (hic : i ≠ c) :
    linTv e hij ∈ pointParabolic (e.trans (LinearFlag.dualAut n K)) c := by
  have h := linTv_mem_pointParabolic (e.trans (LinearFlag.dualAut n K)) hij.symm hic
  rwa [linTv_trans_dualAut] at h

theorem modelToG_pointRadical_le_pointParabolic_dual (hK : Nat.card K = 2)
    (f : L ≃* LinearFlag.projectiveSL n K) {c₀ c₁ : Fin n} (hc : c₀ ≠ c₁) :
    modelToG f (pointRadical (K := K) c₁) ≤
      pointParabolic (f.trans (LinearFlag.dualAut n K)) c₀ :=
  modelToG_pointRadical_le hK f c₁ fun _ hcj => linTv_mem_pointParabolic_dual f hcj hc.symm

end Members

section Compare

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K]
  [CharP K 2]

theorem lift_eq_or_of_radical (hset : SeitzSetting G L) (hn : 4 ≤ n) (hK : Nat.card K = 2)
    (f : L ≃* LinearFlag.projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {c₀ c₁ : Fin n} (hc : c₀ ≠ c₁) {W₀ X₀ W₁ X₁ : Subgroup G}
    (h₀ : LinearTwoSwapModuleData (f.trans (LinearFlag.dualAut n K)) t c₀ W₀ X₀)
    (h₁ : LinearTwoSwapModuleData f t c₁ W₁ X₁)
    (hU : ∀ E : Subgroup G, E ≤ seitzRadX (modelToG f (pointRadical (K := K) c₁)) t →
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      Nat.card E = Nat.card (modelToG f (pointRadical (K := K) c₁)) *
        Nat.card (modelToG f (pointRadical (K := K) c₁)) → E = W₁) :
    (∀ v ∈ modelToG f (pointRadical (K := K) c₁), liftIn t X₁ v = liftIn t X₀ v) ∨
      ∀ v ∈ modelToG f (pointRadical (K := K) c₁),
        liftIn t X₁ v = t * liftIn t X₀ v * t⁻¹ := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hLt : ∀ y ∈ L, y * t = t * y := fun y hy => mem_centralizer_iff.1 htC y hy
  obtain ⟨hA₀, hAA₀, -, -⟩ := swapModuleData_split (K := K) hn hK _ htt htC h₀
  obtain ⟨hA₁, hAA₁, -, -⟩ := swapModuleData_split (K := K) hn hK f htt htC h₁
  obtain ⟨-, -, hex₀⟩ := swapModuleData_lift hset hn hK _ ht hKt h₀
  obtain ⟨-, hb₁, hex₁⟩ := swapModuleData_lift hset hn hK f ht hKt h₁
  obtain ⟨hW2, -, hWt, -, -, -, -, -, -, -, -, -⟩ := h₁
  set R := modelToG f (pointRadical (K := K) c₁) with hR
  have hRP₀ : R ≤ pointParabolic (f.trans (LinearFlag.dualAut n K)) c₀ :=
    modelToG_pointRadical_le_pointParabolic_dual hK f hc
  have hR₀ : ∀ v ∈ R, ∃ x ∈ X₀, x * (t * x * t⁻¹) = v := fun v hv => hex₀ v (hRP₀ hv)
  have hR₁ : ∀ v ∈ R, ∃ x ∈ X₁, x * (t * x * t⁻¹) = v := fun v hv => by
    obtain ⟨x, hx, hxv⟩ := hb₁ v hv
    exact ⟨x, (mem_inf.1 hx).1, hxv⟩
  have hRW : R ≤ W₁ := by rw [← hWt]; exact inf_le_left
  have hR2 : ∀ v ∈ R, v * v = 1 := fun v hv => hW2 v (hRW hv)
  have hRt : ∀ v ∈ R, v * t = t * v := fun v hv => hLt v (modelToG_le f _ hv)
  have hα₀ : ∀ v ∈ R, liftIn t X₀ v ∈ X₀ ∧ liftIn t X₀ v * (t * liftIn t X₀ v * t⁻¹) = v :=
    fun v hv => liftIn_spec (hR₀ v hv)
  have hβ₁ : ∀ v ∈ R, liftIn t X₁ v ∈ X₁ ∧ liftIn t X₁ v * (t * liftIn t X₁ v * t⁻¹) = v :=
    fun v hv => liftIn_spec (hR₁ v hv)
  have hβW : ∀ v ∈ R, liftIn t X₁ v ∈ W₁ := by
    intro v hv
    obtain ⟨x, hx, hxv⟩ := hb₁ v hv
    rw [liftIn_eq hA₁ hAA₁ (mem_inf.1 hx).1 hxv]
    exact (mem_inf.1 hx).2
  have hαW : ∀ v ∈ R, liftIn t X₀ v ∈ W₁ := by
    set A := (R.comap (linearSwapDiag hA₀)).map X₀.subtype with hAdef
    have hAX : A ≤ X₀ := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hAt : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G) :=
      (map_mono hAX).trans (hA₀.trans (centralizer_le hAX))
    have hAA : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥ :=
      eq_bot_iff.2 ((inf_le_inf hAX (map_mono hAX)).trans hAA₀.le)
    have hAR : ∀ a ∈ A, a * (t * a * t⁻¹) ∈ R := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    have hRA : ∀ v ∈ R, ∃ a ∈ A, a * (t * a * t⁻¹) = v := by
      intro v hv
      obtain ⟨x, hx, hxv⟩ := hR₀ v hv
      refine ⟨x, ⟨⟨x, hx⟩, ?_, rfl⟩, hxv⟩
      change x * (t * x * t⁻¹) ∈ R
      rw [hxv]
      exact hv
    have hle := lift_le_of_unique hAt hAA hAR hRA hR2 hRt hU
    intro v hv
    apply hle
    refine ⟨⟨liftIn t X₀ v, (hα₀ v hv).1⟩, ?_, rfl⟩
    change liftIn t X₀ v * (t * liftIn t X₀ v * t⁻¹) ∈ R
    rw [(hα₀ v hv).2]
    exact hv
  have hW₁c : ∀ v ∈ W₁, ∀ w ∈ W₁, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW2 hv hw
  have haR : ∀ v ∈ R, liftIn t X₁ v * liftIn t X₀ v ∈ R := by
    intro v hv
    have hβ2 := liftIn_mul_self hA₁ hAA₁ (hR2 v hv) (hR₁ v hv)
    have hc := inv_mul_mem_centralizer_of_diag_eq (t := t)
      (liftIn_mul_self hA₀ hAA₀ (hR2 v hv) (hR₀ v hv)) hβ2
      (liftIn_comm hA₀ (hR₀ v hv)) (liftIn_comm hA₁ (hR₁ v hv))
      ((hα₀ v hv).2.trans (hβ₁ v hv).2.symm)
    rw [inv_eq_of_mul_eq_one_right hβ2] at hc
    rw [← hWt]
    exact mem_inf.2 ⟨mul_mem (hβW v hv) (hαW v hv), hc⟩
  have ha_mul : ∀ v ∈ R, ∀ w ∈ R, liftIn t X₁ (v * w) * liftIn t X₀ (v * w) =
      (liftIn t X₁ v * liftIn t X₀ v) * (liftIn t X₁ w * liftIn t X₀ w) := by
    intro v hv w hw
    rw [liftIn_mul hA₁ hAA₁ (hR₁ v hv) (hR₁ w hw), liftIn_mul hA₀ hAA₀ (hR₀ v hv) (hR₀ w hw)]
    have hc := hW₁c _ (hβW w hw) _ (hαW v hv)
    calc liftIn t X₁ v * liftIn t X₁ w * (liftIn t X₀ v * liftIn t X₀ w)
        = liftIn t X₁ v * (liftIn t X₁ w * liftIn t X₀ v) * liftIn t X₀ w := by group
      _ = liftIn t X₁ v * (liftIn t X₀ v * liftIn t X₁ w) * liftIn t X₀ w := by rw [hc]
      _ = liftIn t X₁ v * liftIn t X₀ v * (liftIn t X₁ w * liftIn t X₀ w) := by group
  have ha_conj : ∀ q ∈ pointParabolic (f.trans (LinearFlag.dualAut n K)) c₀,
      q ∈ pointParabolic f c₁ → q ∈ L → ∀ v ∈ R,
      liftIn t X₁ (q * v * q⁻¹) * liftIn t X₀ (q * v * q⁻¹) =
        q * (liftIn t X₁ v * liftIn t X₀ v) * q⁻¹ := by
    intro q hq₀ hq₁ hqL v hv
    obtain ⟨q₀, hq₀X, hq₀q⟩ := hex₀ q hq₀
    obtain ⟨q₁, hq₁X, hq₁q⟩ := hex₁ q hq₁
    have hqt := hLt q hqL
    have e₀ := liftIn_conj hA₀ hAA₀ hq₀X (by rw [hq₀q]; exact hqt) (hR₀ v hv)
    have e₁ := liftIn_conj hA₁ hAA₁ hq₁X (by rw [hq₁q]; exact hqt) (hR₁ v hv)
    rw [hq₀q] at e₀
    rw [hq₁q] at e₁
    rw [e₀, e₁]
    group
  have hLmem : ∀ {i j : Fin n} (hij : i ≠ j), linTv f hij ∈ L := fun hij =>
    (f.symm (LinearFlag.proj n K (Matrix.SpecialLinearGroup.transvection hij (1 : K)))).2
  have huP₀ : ∀ {j : Fin n} (hj : j ≠ c₀),
      linTv f hj ∈ pointParabolic (f.trans (LinearFlag.dualAut n K)) c₀ := fun hj =>
    linTv_mem_pointParabolic_dual f hj hj
  have huP₁ : ∀ {j : Fin n} (hj : j ≠ c₀), linTv f hj ∈ pointParabolic f c₁ := fun hj =>
    linTv_mem_pointParabolic f hj hc
  have hhR : ∀ {i : Fin n} (hi : c₁ ≠ i), linTv f hi ∈ R := fun hi => linTv_mem_pointRadical f hi
  set z := linTv f hc.symm with hz
  have hzR : z ∈ R := hhR hc.symm
  have hz1 : z ≠ 1 := linTv_ne_one f hc.symm
  have hz2 : z * z = 1 := linTv_mul_self f hc.symm
  have hu_conj : ∀ {j : Fin n} (hj : j ≠ c₀) {v : G}, v ∈ R →
      linTv f hj * v * (linTv f hj)⁻¹ ∈ R →
      liftIn t X₁ (linTv f hj * v * (linTv f hj)⁻¹) * liftIn t X₀ (linTv f hj * v * (linTv f hj)⁻¹)
        = linTv f hj * (liftIn t X₁ v * liftIn t X₀ v) * (linTv f hj)⁻¹ := fun hj _ hv _ =>
    ha_conj _ (huP₀ hj) (huP₁ hj) (hLmem hj) _ hv
  have haz : liftIn t X₁ z * liftIn t X₀ z = 1 ∨ liftIn t X₁ z * liftIn t X₀ z = z := by
    obtain ⟨r, hrc, hreq, hr⟩ := exists_pointRadElem_of_mem hK f c₀ (haR z hzR)
    have hr' : ∀ j, j ≠ c₀ → r j = 0 := by
      intro j hj
      by_cases hj1 : j = c₁
      · rw [hj1]; exact hrc
      refine hr j hj1 hj ?_
      have hcomm : linTv f hj * z = z * linTv f hj :=
        linTv_commute f hj hc.symm hc (Ne.symm hj)
      have hconj : linTv f hj * z * (linTv f hj)⁻¹ = z := by rw [hcomm, mul_inv_cancel_right]
      have h1 := hu_conj hj hzR (by rw [hconj]; exact hzR)
      rw [hconj] at h1
      calc liftIn t X₁ z * liftIn t X₀ z * linTv f hj
          = linTv f hj * (liftIn t X₁ z * liftIn t X₀ z) * (linTv f hj)⁻¹ * linTv f hj := by
            rw [← h1]
        _ = linTv f hj * (liftIn t X₁ z * liftIn t X₀ z) := by group
    rw [hreq]
    exact eq_one_or_of_pointRadElem_one hK f hc.symm hr'
  have hah : ∀ {b : Fin n} (hb₀ : b ≠ c₀) (hb₁ : c₁ ≠ b),
      liftIn t X₁ (linTv f hb₁) * liftIn t X₀ (linTv f hb₁) = 1 ∨
      liftIn t X₁ (linTv f hb₁) * liftIn t X₀ (linTv f hb₁) = linTv f hb₁ ∨
      liftIn t X₁ (linTv f hb₁) * liftIn t X₀ (linTv f hb₁) = z ∨
      liftIn t X₁ (linTv f hb₁) * liftIn t X₀ (linTv f hb₁) = linTv f hb₁ * z := by
    intro b hb₀ hb₁
    obtain ⟨r, hrc, hreq, hr⟩ := exists_pointRadElem_of_mem hK f c₀ (haR _ (hhR hb₁))
    have hr' : ∀ j, j ≠ c₀ → j ≠ b → r j = 0 := by
      intro j hj hjb
      by_cases hj1 : j = c₁
      · rw [hj1]; exact hrc
      refine hr j hj1 hj ?_
      have hcomm : linTv f hj * linTv f hb₁ = linTv f hb₁ * linTv f hj :=
        linTv_commute f hj hb₁ hc (Ne.symm hjb)
      have hconj : linTv f hj * linTv f hb₁ * (linTv f hj)⁻¹ = linTv f hb₁ := by
        rw [hcomm, mul_inv_cancel_right]
      have h1 := hu_conj hj (hhR hb₁) (by rw [hconj]; exact hhR hb₁)
      rw [hconj] at h1
      calc liftIn t X₁ (linTv f hb₁) * liftIn t X₀ (linTv f hb₁) * linTv f hj
          = linTv f hj * (liftIn t X₁ (linTv f hb₁) * liftIn t X₀ (linTv f hb₁)) *
              (linTv f hj)⁻¹ * linTv f hj := by rw [← h1]
        _ = linTv f hj * (liftIn t X₁ (linTv f hb₁) * liftIn t X₀ (linTv f hb₁)) := by group
    rw [hreq]
    exact eq_one_or_of_pointRadElem hK f (Ne.symm hb₀) hc.symm hb₁ hr'
  have hsign : ∀ {b : Fin n} (hb₀ : b ≠ c₀) (hb₁ : c₁ ≠ b),
      (liftIn t X₁ z * liftIn t X₀ z = 1 →
        liftIn t X₁ (linTv f hb₁) * liftIn t X₀ (linTv f hb₁) = 1 ∨
        liftIn t X₁ (linTv f hb₁) * liftIn t X₀ (linTv f hb₁) = z) ∧
      (liftIn t X₁ z * liftIn t X₀ z = z →
        liftIn t X₁ (linTv f hb₁) * liftIn t X₀ (linTv f hb₁) = linTv f hb₁ ∨
        liftIn t X₁ (linTv f hb₁) * liftIn t X₀ (linTv f hb₁) = linTv f hb₁ * z) := by
    intro b hb₀ hb₁
    have hcomm := linTv_commutator f hb₁ hb₀ hc.symm
    have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    have huh : linTv f hb₀ * linTv f hb₁ * (linTv f hb₀)⁻¹ = z * linTv f hb₁ := by
      calc linTv f hb₀ * linTv f hb₁ * (linTv f hb₀)⁻¹
          = (linTv f hb₁ * linTv f hb₀ * (linTv f hb₁)⁻¹ * (linTv f hb₀)⁻¹)⁻¹ * linTv f hb₁ := by
            group
        _ = z * linTv f hb₁ := by rw [hcomm, hz']
    have huz : linTv f hb₀ * z = z * linTv f hb₀ := linTv_commute f hb₀ hc.symm hc (Ne.symm hb₀)
    have huzc : linTv f hb₀ * z * (linTv f hb₀)⁻¹ = z := by rw [huz, mul_inv_cancel_right]
    have key := hu_conj hb₀ (hhR hb₁) (by rw [huh]; exact mul_mem hzR (hhR hb₁))
    rw [huh, ha_mul z hzR _ (hhR hb₁)] at key
    rcases hah hb₀ hb₁ with h1 | h1 | h1 | h1 <;> rw [h1] at key
    · refine ⟨fun _ => Or.inl h1, fun h2 => absurd ?_ hz1⟩
      rw [h2] at key
      simpa using key
    · refine ⟨fun h2 => absurd ?_ hz1, fun _ => Or.inl h1⟩
      rw [h2, huh] at key
      exact (mul_right_cancel key).symm
    · refine ⟨fun _ => Or.inr h1, fun h2 => absurd ?_ hz1⟩
      rw [h2, huzc] at key
      exact mul_left_cancel (key.trans (mul_one z).symm)
    · refine ⟨fun h2 => absurd ?_ hz1, fun _ => Or.inr h1⟩
      have e : linTv f hb₀ * (linTv f hb₁ * z) * (linTv f hb₀)⁻¹ =
          (linTv f hb₀ * linTv f hb₁ * (linTv f hb₀)⁻¹) * (linTv f hb₀ * z * (linTv f hb₀)⁻¹) := by
        group
      rw [h2, e, huh, huzc, one_mul, mul_assoc] at key
      exact (mul_right_cancel ((one_mul _).trans key)).symm
  have hval : ∀ {b' : Fin n} (hb'₀ : b' ≠ c₀) (hb'₁ : c₁ ≠ b'),
      (liftIn t X₁ z * liftIn t X₀ z = 1 →
        liftIn t X₁ (linTv f hb'₁) * liftIn t X₀ (linTv f hb'₁) = 1) ∧
      (liftIn t X₁ z * liftIn t X₀ z = z →
        liftIn t X₁ (linTv f hb'₁) * liftIn t X₀ (linTv f hb'₁) = linTv f hb'₁) := by
    intro b' hb'₀ hb'₁
    obtain ⟨b, hb⟩ := exists_not_mem_of_card_lt_fin ({c₀, c₁, b'} : Finset (Fin n))
      ((Finset.card_le_three).trans_lt (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    obtain ⟨hb₀, hb₁', hbb'⟩ := hb
    have hb₁ : c₁ ≠ b := Ne.symm hb₁'
    have hd₀ := linTv_mem_pointParabolic_dual f hbb' hb₀
    have hd₁ := linTv_mem_pointParabolic f hbb' (Ne.symm hb'₁)
    have hcomm := linTv_commutator f hb₁ hbb' hb'₁
    have hinv : (linTv f hb'₁)⁻¹ = linTv f hb'₁ :=
      inv_eq_of_mul_eq_one_right (linTv_mul_self f hb'₁)
    have hdh : linTv f hbb' * linTv f hb₁ * (linTv f hbb')⁻¹ = linTv f hb'₁ * linTv f hb₁ := by
      calc linTv f hbb' * linTv f hb₁ * (linTv f hbb')⁻¹
          = (linTv f hb₁ * linTv f hbb' * (linTv f hb₁)⁻¹ * (linTv f hbb')⁻¹)⁻¹ *
              linTv f hb₁ := by group
        _ = linTv f hb'₁ * linTv f hb₁ := by rw [hcomm, hinv]
    have hdz : linTv f hbb' * z = z * linTv f hbb' :=
      linTv_commute f hbb' hc.symm (Ne.symm hb'₁) (Ne.symm hb₀)
    have hdzc : linTv f hbb' * z * (linTv f hbb')⁻¹ = z := by rw [hdz, mul_inv_cancel_right]
    have key := ha_conj _ hd₀ hd₁ (hLmem hbb') _ (hhR hb₁)
    rw [hdh, ha_mul _ (hhR hb'₁) _ (hhR hb₁)] at key
    obtain ⟨hs1, hs2⟩ := hsign hb₀ hb₁
    refine ⟨fun hz0 => ?_, fun hzz => ?_⟩
    · rcases hs1 hz0 with h1 | h1 <;> rw [h1] at key
      · simpa using key
      · rw [hdzc] at key
        exact mul_right_cancel (key.trans (one_mul z).symm)
    · rcases hs2 hzz with h1 | h1 <;> rw [h1] at key
      · rw [hdh] at key
        exact mul_right_cancel key
      · have e : linTv f hbb' * (linTv f hb₁ * z) * (linTv f hbb')⁻¹ =
            (linTv f hbb' * linTv f hb₁ * (linTv f hbb')⁻¹) *
              (linTv f hbb' * z * (linTv f hbb')⁻¹) := by group
        rw [e, hdh, hdzc, mul_assoc (linTv f hb'₁)] at key
        exact mul_right_cancel key
  have hone : liftIn t X₁ 1 * liftIn t X₀ 1 = 1 := by
    rw [liftIn_eq hA₁ hAA₁ (one_mem X₁) (by group), liftIn_eq hA₀ hAA₀ (one_mem X₀) (by group),
      one_mul]
  rcases haz with hz0 | hzz
  · left
    let H : Subgroup G :=
      { carrier := {v | v ∈ R ∧ liftIn t X₁ v * liftIn t X₀ v = 1}
        mul_mem' := fun {v w} hv hw =>
          ⟨mul_mem hv.1 hw.1, by rw [ha_mul v hv.1 w hw.1, hv.2, hw.2, one_mul]⟩
        one_mem' := ⟨one_mem R, hone⟩
        inv_mem' := fun {v} hv => by
          have hinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hR2 v hv.1)
          rw [hinv]
          exact hv }
    have hRH : R ≤ H := modelToG_pointRadical_le hK f c₁ fun j hcj => by
      by_cases hj : j = c₀
      · subst hj
        exact ⟨hhR hcj, hz0⟩
      · exact ⟨hhR hcj, (hval hj hcj).1 hz0⟩
    intro v hv
    have h1 : liftIn t X₁ v * liftIn t X₀ v = 1 := (hRH hv).2
    have hα2 := liftIn_mul_self hA₀ hAA₀ (hR2 v hv) (hR₀ v hv)
    calc liftIn t X₁ v = liftIn t X₁ v * (liftIn t X₀ v * liftIn t X₀ v) := by rw [hα2, mul_one]
      _ = (liftIn t X₁ v * liftIn t X₀ v) * liftIn t X₀ v := by group
      _ = liftIn t X₀ v := by rw [h1, one_mul]
  · right
    let H : Subgroup G :=
      { carrier := {v | v ∈ R ∧ liftIn t X₁ v * liftIn t X₀ v = v}
        mul_mem' := fun {v w} hv hw =>
          ⟨mul_mem hv.1 hw.1, by rw [ha_mul v hv.1 w hw.1, hv.2, hw.2]⟩
        one_mem' := ⟨one_mem R, hone⟩
        inv_mem' := fun {v} hv => by
          have hinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hR2 v hv.1)
          rw [hinv]
          exact hv }
    have hRH : R ≤ H := modelToG_pointRadical_le hK f c₁ fun j hcj => by
      by_cases hj : j = c₀
      · subst hj
        exact ⟨hhR hcj, hzz⟩
      · exact ⟨hhR hcj, (hval hj hcj).2 hzz⟩
    intro v hv
    have h1 : liftIn t X₁ v * liftIn t X₀ v = v := (hRH hv).2
    have h2 := (hα₀ v hv).2
    have hcv : liftIn t X₀ v * v = v * liftIn t X₀ v := hW₁c _ (hαW v hv) _ (hRW hv)
    calc liftIn t X₁ v = (liftIn t X₁ v * liftIn t X₀ v) * (liftIn t X₀ v)⁻¹ := by group
      _ = v * (liftIn t X₀ v)⁻¹ := by rw [h1]
      _ = (liftIn t X₀ v)⁻¹ * (liftIn t X₀ v * v) * (liftIn t X₀ v)⁻¹ := by group
      _ = (liftIn t X₀ v)⁻¹ * (v * liftIn t X₀ v) * (liftIn t X₀ v)⁻¹ := by rw [hcv]
      _ = (liftIn t X₀ v)⁻¹ * v := by group
      _ = (liftIn t X₀ v)⁻¹ * (liftIn t X₀ v * (t * liftIn t X₀ v * t⁻¹)) := by rw [h2]
      _ = t * liftIn t X₀ v * t⁻¹ := by group

end Compare

end CFSG.SeitzReduction.LinearPilot
