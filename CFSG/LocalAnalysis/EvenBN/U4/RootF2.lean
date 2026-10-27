module

public import CFSG.LocalAnalysis.EvenBN.U4.RootRCenter
public import CFSG.LocalAnalysis.EvenBN.U4.RootD2Two

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_sup mem_normalizer_inf
  exists_mem_inf_centralizer_mul_of_coprime card_sup_mul_card_inf_eq centralizerMod
  mem_centralizerMod)

@[expose] noncomputable def miyamotoF2G {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K)) (t : G)
    (Q : Subgroup G) : Subgroup G :=
  miyamotoD2G h L η t Q ⊓ miyamotoRG h L η t Q

section Pull

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {G : Type} [Group G]
  (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K))

theorem I2G_commute_N2G {x y : G} (hx : x ∈ miyamotoI2G h L η) (hy : y ∈ miyamotoN2G h L η) :
    x * y = y * x := by
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hx
  obtain ⟨k, hk, rfl⟩ := (mem_miyamotoPull h L η).1 hy
  have e : g * k = k * g := Subtype.ext (miyamotoI2_commute_N2 h hg hk)
  rw [← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul, e]

omit [Group G] in
theorem mem_normalizer_of_mem_centralizer' {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ centralizer (H : Set G)) : g ∈ normalizer (H : Set G) := by
  refine mem_normalizer_iff.2 fun y => ⟨fun hy => ?_, fun hy => ?_⟩
  · rw [← mem_centralizer_iff.1 hg y hy, mul_inv_cancel_right]
    exact hy
  · have e := mem_centralizer_iff.1 hg _ hy
    have hy' : y = g * y * g⁻¹ := by
      calc y = g⁻¹ * ((g * y * g⁻¹) * g) := by group
        _ = g⁻¹ * (g * (g * y * g⁻¹)) := by rw [e]
        _ = g * y * g⁻¹ := by group
    rw [hy']
    exact hy

end Pull

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem exists_rootElt_eq (hS : Setting h L η t Q T) {u : G}
    (hu : u ∈ miyamotoPull h L η (miyamotoRootA h)) : ∃ a : K, hS.rootElt a = u := by
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hu
  obtain ⟨a, ha⟩ := hg
  refine ⟨a, ?_⟩
  simp only [rootElt]
  congr 2
  exact Subtype.ext ha.symm

theorem rootElt_mem_rootA (hS : Setting h L η t Q T) (a : K) :
    hS.rootElt a ∈ miyamotoPull h L η (miyamotoRootA h) :=
  (symm_mem_miyamotoPull_iff h L η).2 ⟨a, rfl⟩

theorem rootA_le_centralizer_I1 (hS : Setting h L η t Q T) :
    miyamotoPull h L η (miyamotoRootA h) ≤ centralizer (miyamotoI1G h L η : Set G) := by
  rw [← hS.PG_inf_centralizer_I1]
  exact inf_le_right

theorem rootA_le_PG (hS : Setting h L η t Q T) :
    miyamotoPull h L η (miyamotoRootA h) ≤ miyamotoPG h L η := by
  rw [← hS.PG_inf_centralizer_I1]
  exact inf_le_left

theorem P1_inf_centralizer_I1 (hS : Setting h L η t Q T) :
    (miyamotoF1G h L η t ⊔ miyamotoPG h L η) ⊓ centralizer (miyamotoI1G h L η : Set G) =
      miyamotoPull h L η (miyamotoRootA h) := by
  refine le_antisymm (fun x hx => ?_)
    (le_inf (hS.rootA_le_PG.trans le_sup_right) hS.rootA_le_centralizer_I1)
  obtain ⟨hxP, hxC⟩ := mem_inf.1 hx
  have hu := hS.rootElt_mem_rootA (hS.coordP1 x)
  have h1 : x * (hS.rootElt (hS.coordP1 x))⁻¹ ∈
      miyamotoF1G h L η t ⊓ centralizer (miyamotoI1G h L η : Set G) :=
    mem_inf.2 ⟨hS.coordP1_spec hxP, mul_mem hxC (inv_mem (hS.rootA_le_centralizer_I1 hu))⟩
  rw [hS.F1_inf_centralizer_I1, mem_bot, mul_inv_eq_one] at h1
  rw [h1]
  exact hu

theorem rootA_le_W (hS : Setting h L η t Q T) :
    miyamotoPull h L η (miyamotoRootA h) ≤
      miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) :=
  le_inf ((hS.rootA_le_PG.trans le_sup_right).trans hS.P1_le_miyamotoRG)
    hS.rootA_le_centralizer_I1

theorem W_inf_P1 (hS : Setting h L η t Q T) :
    (miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)) ⊓
        (miyamotoF1G h L η t ⊔ miyamotoPG h L η) =
      miyamotoPull h L η (miyamotoRootA h) := by
  rw [← hS.P1_inf_centralizer_I1, inf_comm, ← inf_assoc,
    inf_eq_left.2 hS.P1_le_miyamotoRG]

theorem mul_self_mem_rootA_of_mem_W (hS : Setting h L η t Q T) {w : G}
    (hw : w ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)) :
    w * w ∈ miyamotoPull h L η (miyamotoRootA h) := by
  rw [← hS.W_inf_P1]
  exact mem_inf.2 ⟨mul_mem hw hw, hS.miyamotoS_mod_P1.1 w (hS.miyamotoRG_le_miyamotoS hw.1)⟩

theorem IG_le_normalizer_W (hS : Setting h L η t Q T) :
    miyamotoIG h L η ≤
      normalizer ((miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) :
        Subgroup G) : Set G) := fun _ hi =>
  mem_normalizer_inf (hS.IG_le_normalizer_RG hi)
    (hS.IG_le_normalizer_centralizer hS.I1G_le_IG hi)

theorem U_le_centralizer_W (hS : Setting h L η t Q T) :
    miyamotoPull h L η (miyamotoRootA h) ≤
      centralizer ((miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) :
        Subgroup G) : Set G) := by
  have : CharP K 2 := h.charP
  set W := miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) with hWdef
  set U := miyamotoPull h L η (miyamotoRootA h) with hUdef
  have hW2 : IsPGroup 2 W := hS.isPGroup_RG.to_le inf_le_left
  have hU2 : IsPGroup 2 U := hW2.to_le hS.rootA_le_W
  have hU1 : U ≠ ⊥ := by
    intro hbot
    have h1 : hS.rootElt 1 ∈ U := hS.rootElt_mem_rootA 1
    rw [hbot, mem_bot] at h1
    have h2 := (hS.rootElt_mem_F1_iff (a := 1)).1 (by rw [h1]; exact one_mem _)
    exact one_ne_zero h2
  have hWU : W ≤ normalizer (U : Set G) := by
    intro w hw
    rw [hUdef, ← hS.W_inf_P1]
    exact mem_normalizer_inf (le_normalizer hw) (hS.RG_le_normalizer_P1 hw.1)
  have key := CFSG.LocalAnalysis.EvenBN.U5.Prelim.inf_centralizer_ne_bot_of_pow_mem hU2 hU1 hWU
    fun y hy => by
      obtain ⟨k, hk⟩ := hW2 ⟨y, hy⟩
      refine ⟨k, ?_⟩
      have : y ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      rw [this]
      exact one_mem _
  obtain ⟨⟨u₀, hu₀⟩, hu₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 key
  obtain ⟨hu₀U, hu₀W⟩ := mem_inf.1 hu₀
  have hu₀1' : u₀ ≠ 1 := fun e => hu₀1 (Subtype.ext e)
  obtain ⟨a₀, rfl⟩ := hS.exists_rootElt_eq hu₀U
  have ha₀ : a₀ ≠ 0 := by
    rintro rfl
    exact hu₀1' hS.rootElt_zero
  intro u hu
  obtain ⟨a, rfl⟩ := hS.exists_rootElt_eq hu
  by_cases ha : a = 0
  · rw [ha, hS.rootElt_zero]
    exact one_mem _
  obtain ⟨p, hp, -, hpA⟩ := exists_miyamotoIParam_eq_one_weightB_eq_one h
    (Units.mk0 (a / a₀) (div_ne_zero ha ha₀))
  set i := hS.torusElt p hp with hi
  have hiW := hS.IG_le_normalizer_W (hS.torusElt_mem_IG p hp)
  have e : i⁻¹ * hS.rootElt a₀ * i = hS.rootElt a := by
    rw [hi, hS.torusElt_conj_rootElt, hpA, Units.val_mk0, div_mul_cancel₀ _ ha₀]
  rw [← e]
  refine mem_centralizer_iff.2 fun w hw => ?_
  have hw' : i * w * i⁻¹ ∈ W := (mem_normalizer_iff.1 hiW w).1 hw
  have hc := mem_centralizer_iff.1 hu₀W _ hw'
  calc w * (i⁻¹ * hS.rootElt a₀ * i) = i⁻¹ * ((i * w * i⁻¹) * hS.rootElt a₀) * i := by group
    _ = i⁻¹ * (hS.rootElt a₀ * (i * w * i⁻¹)) * i := by rw [hc]
    _ = i⁻¹ * hS.rootElt a₀ * i * w := by group

theorem exists_mul_of_mem_A2G (hS : Setting h L η t Q T) {a : G} (ha : a ∈ miyamotoA2G h L η) :
    ∃ z ∈ miyamotoPull h L η (miyamotoZ2 h), ∃ u ∈ miyamotoPull h L η (miyamotoRootA h),
      a = z * u := by
  have : CharP K 2 := h.charP
  exact exists_mul_of_mem_miyamotoPull h L η
    ((miyamotoZ2_le_A1 h).trans ((miyamotoA1_le_P h).trans (miyamotoUnipotent_le_SU h false false)))
    hS.rootA_le_SU (miyamotoZ2_mul_rootA h) ha

theorem commutator_W_EA2_mem_E (hS : Setting h L η t Q T) {w x : G}
    (hw : w ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G))
    (hx : x ∈ miyamotoEG h L η Q ⊔ miyamotoA2G h L η) :
    w * x * w⁻¹ * x⁻¹ ∈ miyamotoEG h L η Q := by
  have hA2E : miyamotoA2G h L η ≤ normalizer (miyamotoEG h L η Q : Set G) := fun a ha =>
    hS.RG_le_normalizer_E (hS.P1_le_miyamotoRG (mem_sup_right (hS.A2G_le_PG ha)))
  obtain ⟨e, he, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer' hA2E hx
  obtain ⟨z, hz, u, hu, rfl⟩ := hS.exists_mul_of_mem_A2G ha
  have hwR := hw.1
  have hwe : w * e = e * w := (mem_centralizer_iff.1 (hS.RG_le_centralizer_E hwR) e he).symm
  have hwu : w * u = u * w := mem_centralizer_iff.1 (hS.U_le_centralizer_W hu) w hw
  have hzF : z ∈ miyamotoFG h L η t Q := hS.Z2_le_F hz
  have h1 := inv_mem (hS.commutator_F_RG_mem_E hzF hwR)
  have huw : u * w⁻¹ = w⁻¹ * u := by
    calc u * w⁻¹ = w⁻¹ * (w * u) * w⁻¹ := by group
      _ = w⁻¹ * (u * w) * w⁻¹ := by rw [hwu]
      _ = w⁻¹ * u := by group
  have key : w * (e * (z * u)) * w⁻¹ * (e * (z * u))⁻¹ = e * (w * z * w⁻¹ * z⁻¹) * e⁻¹ := by
    calc w * (e * (z * u)) * w⁻¹ * (e * (z * u))⁻¹ =
        (w * e) * z * (u * w⁻¹) * u⁻¹ * z⁻¹ * e⁻¹ := by group
      _ = (e * w) * z * (w⁻¹ * u) * u⁻¹ * z⁻¹ * e⁻¹ := by rw [hwe, huw]
      _ = e * (w * z * w⁻¹ * z⁻¹) * e⁻¹ := by group
  rw [key]
  have h2 : w * z * w⁻¹ * z⁻¹ ∈ miyamotoEG h L η Q := by
    rw [show w * z * w⁻¹ * z⁻¹ = (z * w * z⁻¹ * w⁻¹)⁻¹ by group]
    exact h1
  exact mul_mem (mul_mem he h2) (inv_mem he)

theorem conj_t_mul_t_mem_rootA (hS : Setting h L η t Q T) {w : G}
    (hw : w ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)) :
    w * t * w⁻¹ * t ∈ miyamotoPull h L η (miyamotoRootA h) := by
  obtain ⟨hwR, hwC⟩ := mem_inf.1 hw
  have htQ1 : t ∈ miyamotoF1G h L η t ⊔ Q := mem_sup_right hS.t_mem_Q
  have hwN := hS.miyamotoS_le_normalizer_Q1 (hS.miyamotoRG_le_miyamotoS hwR)
  have hQ1 : w * t * w⁻¹ * t ∈ miyamotoF1G h L η t ⊔ Q :=
    mul_mem ((mem_normalizer_iff.1 hwN t).1 htQ1) htQ1
  have hR : w * t * w⁻¹ * t ∈ miyamotoRG h L η t Q := by
    have h1 : t * w⁻¹ * t⁻¹ ∈ miyamotoRG h L η t Q :=
      (mem_normalizer_iff.1 hS.t_mem_normalizer_RG _).1 (inv_mem hwR)
    rw [show w * t * w⁻¹ * t = w * (t * w⁻¹ * t⁻¹) by rw [hS.t_inv]; group]
    exact mul_mem hwR h1
  have hC : w * t * w⁻¹ * t ∈ centralizer (miyamotoI1G h L η : Set G) := by
    have htC : t ∈ centralizer (miyamotoI1G h L η : Set G) :=
      mem_centralizer_iff.2 fun s hs => mem_centralizer_singleton_iff.1 (hS.I1_le_C hs)
    exact mul_mem (mul_mem (mul_mem hwC htC) (inv_mem hwC)) htC
  rw [← hS.P1_inf_centralizer_I1, ← hS.miyamotoRG_inf_Q1]
  exact mem_inf.2 ⟨mem_inf.2 ⟨hR, hQ1⟩, hC⟩

theorem W_le_D2 (hS : Setting h L η t Q T) :
    miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) ≤ miyamotoD2G h L η t Q := by
  intro w hw
  have hwE := hS.RG_le_normalizer_E hw.1
  have hA2E : miyamotoA2G h L η ≤ normalizer (miyamotoEG h L η Q : Set G) := fun a ha =>
    hS.RG_le_normalizer_E (hS.P1_le_miyamotoRG (mem_sup_right (hS.A2G_le_PG ha)))
  have hEA : ∀ g ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G),
      ∀ x ∈ miyamotoEG h L η Q ⊔ miyamotoA2G h L η,
        g * x * g⁻¹ ∈ miyamotoEG h L η Q ⊔ miyamotoA2G h L η := fun g hg x hx => by
    have h1 := hS.commutator_W_EA2_mem_E hg hx
    rw [show g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x by group]
    exact mul_mem (mem_sup_left h1) hx
  refine (hS.mem_D2_iff).2 ⟨mem_normalizer_fintype fun y hy => ?_,
    fun x hx => hS.commutator_W_EA2_mem_E hw hx⟩
  have hy' : y ∈ (miyamotoEG h L η Q ⊔ miyamotoA2G h L η) ⊔ zpowers t := by
    have e : miyamotoEG h L η Q ⊔ miyamotoB2 h L η t =
        (miyamotoEG h L η Q ⊔ miyamotoA2G h L η) ⊔ zpowers t := by
      rw [miyamotoB2, sup_comm (zpowers t), sup_assoc]
    rw [← e]
    exact hy
  have htEA : t ∈ normalizer ((miyamotoEG h L η Q ⊔ miyamotoA2G h L η : Subgroup G) : Set G) :=
    hS.H_le_normalizer_EA2 (hS.M_le_H hS.t_mem_M)
  obtain ⟨x, hx, k, hk, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer' (zpowers_le.2 htEA) hy'
  have hwx := hEA w hw x hx
  have hwk : w * k * w⁻¹ ∈ (miyamotoEG h L η Q ⊔ miyamotoA2G h L η) ⊔ zpowers t := by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hk
    rcases hS.zpow_t_eq n with e | e <;> rw [e]
    · rw [mul_one, mul_inv_cancel]
      exact one_mem _
    · have hu := hS.conj_t_mul_t_mem_rootA hw
      rw [show w * t * w⁻¹ = (w * t * w⁻¹ * t) * t by rw [mul_assoc _ t t, hS.t_mul_t, mul_one]]
      exact mul_mem (mem_sup_left (mem_sup_right (hS.rootA_le_A2G hu)))
        (mem_sup_right (mem_zpowers t))
  have e2 : miyamotoEG h L η Q ⊔ miyamotoB2 h L η t =
      (miyamotoEG h L η Q ⊔ miyamotoA2G h L η) ⊔ zpowers t := by
    rw [miyamotoB2, sup_comm (zpowers t), sup_assoc]
  rw [SetLike.mem_coe, e2, show w * (x * k) * w⁻¹ = (w * x * w⁻¹) * (w * k * w⁻¹) by group]
  exact mul_mem (mem_sup_left hwx) hwk

theorem F_le_D2 (hS : Setting h L η t Q T) :
    miyamotoFG h L η t Q ≤ miyamotoD2G h L η t Q := by
  rw [hS.D2_eq_C0]
  exact hS.F_le_C0

theorem card_F (hS : Setting h L η t Q T) : Nat.card (miyamotoFG h L η t Q) = (2 ^ f) ^ 6 := by
  have : CharP K 2 := h.charP
  have hFD : miyamotoFG h L η t Q ≤ miyamotoD1 h L η t := hS.F_le_F1.trans hS.F1_le_D1
  set φ : miyamotoFG h L η t Q →* G := MonoidHom.mk' (fun x => (x : G)⁻¹ * t * x * t)
    (fun a b => hS.crossed_mul_D1 (hFD a.2) (hFD b.2)) with hφ
  have hφapp : ∀ x : miyamotoFG h L η t Q, φ x = (x : G)⁻¹ * t * x * t := fun _ => rfl
  have hZ2 : Nat.card (miyamotoPull h L η (miyamotoZ2 h)) = (2 ^ f) ^ 3 := by
    rw [card_miyamotoPull h L η
      ((miyamotoZ2_le_A1 h).trans ((miyamotoA1_le_P h).trans (miyamotoUnipotent_le_SU h false
        false))), card_miyamotoZ2]
  have hker : φ.ker.map (miyamotoFG h L η t Q).subtype = miyamotoPull h L η (miyamotoZ2 h) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h1 : (y : G)⁻¹ * t * y * t = 1 := by rw [← hφapp]; exact hy
      have hyA := (hS.crossed_eq_one_iff_F1 (hS.F_le_F1 y.2)).1 h1
      exact hS.mem_Z2_of_mem_F_of_mem_A1 y.2 hyA
    · intro hx
      have hxF := hS.Z2_le_F hx
      refine ⟨⟨x, hxF⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, hφapp]
      exact (hS.crossed_eq_one_iff_F1 (hS.F_le_F1 hxF)).2 (hS.Z2_le_A1 hx)
  have hrange : φ.range = miyamotoPull h L η (miyamotoZ2 h) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [hφapp]
      exact hS.crossed_mem_Z2_of_mem_F y.2
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hS.exists_F_crossed_eq hx
      exact ⟨⟨y, hy⟩, by rw [hφapp]; exact hyx⟩
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [← Subgroup.card_map_of_injective (miyamotoFG h L η t Q).subtype_injective, hker, hrange,
    hZ2] at h1
  rw [← h1]
  ring

theorem F_inf_W (hS : Setting h L η t Q T) :
    miyamotoFG h L η t Q ⊓ (miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)) =
      ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxF, -, hxC⟩ := hx
  have : x ∈ miyamotoF1G h L η t ⊓ centralizer (miyamotoI1G h L η : Set G) :=
    mem_inf.2 ⟨hS.F_le_F1 hxF, hxC⟩
  rwa [hS.F1_inf_centralizer_I1] at this

theorem card_F_sup_W (hS : Setting h L η t Q T) :
    Nat.card (miyamotoFG h L η t Q ⊔
      (miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)) : Subgroup G) =
        (2 ^ f) ^ 10 := by
  have h1 := card_sup_mul_card_inf_eq (A := miyamotoFG h L η t Q)
    (B := miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G))
    (inf_le_left.trans hS.RG_le_normalizer_F)
  rw [hS.F_inf_W, card_bot, mul_one, hS.card_F, hS.card_W] at h1
  rw [h1]
  ring

theorem card_F2_le (hS : Setting h L η t Q T) :
    Nat.card (miyamotoF2G h L η t Q) ≤ (2 ^ f) ^ 10 := by
  have htD := hS.t_mem_D2
  have htN : zpowers t ≤ normalizer (miyamotoF2G h L η t Q : Set G) :=
    zpowers_le.2 (mem_normalizer_inf (le_normalizer htD) hS.t_mem_normalizer_RG)
  have h1 := card_sup_mul_card_inf_eq htN
  have hinf : miyamotoF2G h L η t Q ⊓ zpowers t = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨⟨-, hxR⟩, hxt⟩ := hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxt
    rcases hS.zpow_t_eq k with e | e
    · rw [e]
      exact one_mem _
    · rw [e] at hxR
      exact absurd hxR hS.t_not_mem_miyamotoRG
  rw [hinf, card_bot, mul_one, hS.card_zpowers_t] at h1
  have h2 : Nat.card (miyamotoF2G h L η t Q ⊔ zpowers t : Subgroup G) ≤
      Nat.card (miyamotoD2G h L η t Q) :=
    Subgroup.card_le_of_le (sup_le inf_le_left (zpowers_le.2 htD))
  rw [hS.card_D2, h1] at h2
  omega

theorem F2_eq (hS : Setting h L η t Q T) :
    miyamotoF2G h L η t Q = miyamotoFG h L η t Q ⊔
      (miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)) := by
  have hle : miyamotoFG h L η t Q ⊔
      (miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)) ≤
        miyamotoF2G h L η t Q :=
    sup_le (le_inf hS.F_le_D2 hS.F_le_RG) (le_inf hS.W_le_D2 inf_le_left)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hS.card_F_sup_W]
  exact hS.card_F2_le

theorem card_F2 (hS : Setting h L η t Q T) :
    Nat.card (miyamotoF2G h L η t Q) = (2 ^ f) ^ 10 := by
  rw [hS.F2_eq, hS.card_F_sup_W]

theorem D2_eq_F2_sup (hS : Setting h L η t Q T) :
    miyamotoD2G h L η t Q = miyamotoF2G h L η t Q ⊔ zpowers t := by
  have htD := hS.t_mem_D2
  have hle : miyamotoF2G h L η t Q ⊔ zpowers t ≤ miyamotoD2G h L η t Q :=
    sup_le inf_le_left (zpowers_le.2 htD)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have htN : zpowers t ≤ normalizer (miyamotoF2G h L η t Q : Set G) :=
    zpowers_le.2 (mem_normalizer_inf (le_normalizer htD) hS.t_mem_normalizer_RG)
  have h1 := card_sup_mul_card_inf_eq htN
  have hinf : miyamotoF2G h L η t Q ⊓ zpowers t = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨⟨-, hxR⟩, hxt⟩ := hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxt
    rcases hS.zpow_t_eq k with e | e
    · rw [e]
      exact one_mem _
    · rw [e] at hxR
      exact absurd hxR hS.t_not_mem_miyamotoRG
  rw [hinf, card_bot, mul_one, hS.card_zpowers_t, hS.card_F2] at h1
  rw [hS.card_D2, h1]
  ring_nf
  exact le_rfl

theorem D2_le_miyamotoS (hS : Setting h L η t Q T) :
    miyamotoD2G h L η t Q ≤ miyamotoS h L η t Q := by
  rw [hS.D2_eq_F2_sup, hS.miyamotoS_eq_sup]
  exact sup_le_sup_right inf_le_right _

theorem F_inf_centralizer_I2 (hS : Setting h L η t Q T) :
    miyamotoFG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) = ⊥ := by
  have : CharP K 2 := h.charP
  have hZ2I2 : miyamotoPull h L η (miyamotoZ2 h) ⊓ centralizer (miyamotoI2G h L η : Set G) = ⊥ :=
    by
    rw [← miyamotoPull_inf_centralizer h L η _ (miyamotoI2_le_SU h)]
    have e : miyamotoZ2 h ⊓ centralizer (miyamotoI2 h : Set (GL (Fin 4) K)) = ⊥ := by
      rw [← inf_eq_left.2 ((miyamotoZ2_le_A1 h).trans (miyamotoA1_le_P h)), inf_assoc,
        miyamotoP_inf_centralizer_I2 h hS.two_le, miyamotoZ2_inf_rootB]
    rw [e, miyamotoPull_bot]
  have hI2 : miyamotoI2G h L η ≤ miyamotoIG h L η := hS.tori_le_IG.2.2.2
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxF, hxC⟩ := mem_inf.1 hx
  have hc := hS.crossed_mem_Z2_of_mem_F hxF
  have hcC := hS.crossed_mem_centralizer hI2 hxC
  have h1 : x⁻¹ * t * x * t = 1 := by
    have : x⁻¹ * t * x * t ∈ (⊥ : Subgroup G) := by
      rw [← hZ2I2]
      exact mem_inf.2 ⟨hc, hcC⟩
    exact mem_bot.1 this
  have hxA := (hS.crossed_eq_one_iff_F1 (hS.F_le_F1 hxF)).1 h1
  have hxZ := hS.mem_Z2_of_mem_F_of_mem_A1 hxF hxA
  rw [← hZ2I2]
  exact mem_inf.2 ⟨hxZ, hxC⟩

theorem F2_inf_centralizer_I2 (hS : Setting h L η t Q T) :
    miyamotoF2G h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxF2, hxC⟩ := mem_inf.1 hx
  obtain ⟨-, -, ⟨p, hp, hpX, hpA⟩⟩ := hS.exists_torusElt_weightA_ne_one
  have hxF1 := hS.RG_inf_centralizer_le_F1 hpX hpA (mem_inf.2 ⟨hxF2.2, hxC⟩)
  rw [hS.F2_eq] at hxF2
  obtain ⟨φ, hφ, w, hw, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer'
    (inf_le_left.trans hS.RG_le_normalizer_F) hxF2
  have hwF1 : w ∈ miyamotoF1G h L η t := by
    have := mul_mem (inv_mem (hS.F_le_F1 hφ)) hxF1
    rwa [inv_mul_cancel_left] at this
  have hw1 : w = 1 := by
    have : w ∈ miyamotoF1G h L η t ⊓ centralizer (miyamotoI1G h L η : Set G) :=
      mem_inf.2 ⟨hwF1, hw.2⟩
    rwa [hS.F1_inf_centralizer_I1, mem_bot] at this
  rw [hw1, mul_one] at hxC ⊢
  rw [← hS.F_inf_centralizer_I2]
  exact mem_inf.2 ⟨hφ, hxC⟩

theorem I2_le_normalizer_D2 (hS : Setting h L η t Q T) :
    miyamotoI2G h L η ≤ normalizer (miyamotoD2G h L η t Q : Set G) := fun _ hi =>
  hS.normalizer_H_inf_C_le_normalizer_D2 (hS.I2_le_H hi)

theorem F2_eq_commutator (hS : Setting h L η t Q T) :
    miyamotoF2G h L η t Q = ⁅miyamotoI2G h L η, miyamotoD2G h L η t Q⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI2 : miyamotoI2G h L η ≤ miyamotoIG h L η := hS.tori_le_IG.2.2.2
  refine le_antisymm (fun x hx => ?_) (commutator_le.2 fun i hi d hd => ?_)
  · have hF2N : miyamotoI2G h L η ≤ normalizer (miyamotoF2G h L η t Q : Set G) := fun i hi =>
      mem_normalizer_inf (hS.I2_le_normalizer_D2 hi) (hS.IG_le_normalizer_RG (hI2 hi))
    have hF2_2 : IsPGroup 2 (miyamotoF2G h L η t Q) := hS.isPGroup_RG.to_le inf_le_right
    obtain ⟨hfac, -, -⟩ := yamada_central_product (p := 2) (A := miyamotoF2G h L η t Q)
      (X := miyamotoI2G h L η) hF2_2
      (fun hd => Nat.not_even_iff_odd.2 hS.odd_card_I2 (even_iff_two_dvd.2 hd)) hF2N
      (by
        rw [hS.F2_inf_centralizer_I2]
        exact fun g _ => by
          rw [normalizer_eq_top_iff.mpr inferInstance]
          exact mem_top g)
    obtain ⟨d, hd, c, hc, rfl⟩ := hfac x hx
    rw [hS.F2_inf_centralizer_I2, mem_bot] at hc
    rw [hc, mul_one]
    exact commutator_mono le_rfl inf_le_left hd
  · refine mem_inf.2 ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.1 (hS.I2_le_normalizer_D2 hi) d).1 hd) (inv_mem hd)
    · exact mem_sup_left (commutator_mem_commutator (hI2 hi) (hS.D2_le_miyamotoS hd))

theorem N2_le_H (hS : Setting h L η t Q T) :
    miyamotoN2G h L η ≤ normalizer (CFSG.centerIn Q : Set G) := by
  intro n hn
  refine mem_normalizer_of_mem_centralizer' (mem_centralizer_iff.2 fun z hz => ?_)
  rw [hS.centerIn_Q'] at hz
  have hnC : n ∈ centralizer (miyamotoZG h L η ⊔ zpowers t : Subgroup G) :=
    mem_centralizer_sup
      (centralizer_le (SetLike.coe_subset_coe.2 hS.ZP_le_Y) (hS.N2G_le_centralizer_Y hn))
      (mem_centralizer_iff.2 fun u hu => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hu
        exact ((Commute.zpow_left (mem_centralizer_singleton_iff.1
          (hS.L_le_centralizer (miyamotoPull_le h L η _ hn))).symm k).eq))
  exact mem_centralizer_iff.1 hnC z hz

theorem I2N2_le_normalizer_F2 (hS : Setting h L η t Q T) :
    miyamotoI2G h L η ⊔ miyamotoN2G h L η ≤ normalizer (miyamotoF2G h L η t Q : Set G) := by
  have hI2 : miyamotoI2G h L η ≤ miyamotoIG h L η := hS.tori_le_IG.2.2.2
  have hgen : ∀ g, g ∈ normalizer (miyamotoI2G h L η : Set G) →
      g ∈ normalizer (miyamotoD2G h L η t Q : Set G) →
      g ∈ normalizer (miyamotoF2G h L η t Q : Set G) := by
    intro g hgI hgD
    rw [hS.F2_eq_commutator]
    refine mem_normalizer_fintype fun x hx => ?_
    have key : (⁅miyamotoI2G h L η, miyamotoD2G h L η t Q⁆).map (MulAut.conj g).toMonoidHom ≤
        ⁅miyamotoI2G h L η, miyamotoD2G h L η t Q⁆ := by
      rw [Subgroup.map_commutator]
      refine commutator_mono (fun y hy => ?_) fun y hy => ?_
      · obtain ⟨y₀, hy₀, rfl⟩ := hy
        exact (mem_normalizer_iff.1 hgI y₀).1 hy₀
      · obtain ⟨y₀, hy₀, rfl⟩ := hy
        exact (mem_normalizer_iff.1 hgD y₀).1 hy₀
    exact key ⟨x, hx, rfl⟩
  refine sup_le (fun i hi => hgen i (le_normalizer hi) (hS.I2_le_normalizer_D2 hi)) fun n hn =>
    hgen n (mem_normalizer_of_mem_centralizer' (mem_centralizer_iff.2 fun i hi =>
      I2G_commute_N2G h L η hi hn)) (hS.normalizer_H_inf_C_le_normalizer_D2 (hS.N2_le_H hn))

theorem rootA_comm (hS : Setting h L η t Q T) {u u' : G}
    (hu : u ∈ miyamotoPull h L η (miyamotoRootA h))
    (hu' : u' ∈ miyamotoPull h L η (miyamotoRootA h)) : u * u' = u' * u := by
  obtain ⟨a, rfl⟩ := hS.exists_rootElt_eq hu
  obtain ⟨a', rfl⟩ := hS.exists_rootElt_eq hu'
  rw [← hS.rootElt_add, ← hS.rootElt_add, add_comm]

theorem W_le_F2 (hS : Setting h L η t Q T) :
    miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) ≤ miyamotoF2G h L η t Q := by
  rw [hS.F2_eq]
  exact le_sup_right

theorem mul_self_mem_EU_of_mem_F2 (hS : Setting h L η t Q T) {x : G}
    (hx : x ∈ miyamotoF2G h L η t Q) :
    x * x ∈ miyamotoEG h L η Q ⊔ miyamotoPull h L η (miyamotoRootA h) := by
  rw [hS.F2_eq] at hx
  obtain ⟨φ, hφ, w, hw, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer'
    (inf_le_left.trans hS.RG_le_normalizer_F) hx
  have hc := hS.commutator_F_RG_mem_E hφ hw.1
  have hφφ : φ * φ = 1 := hS.F1_mul_self φ (hS.F_le_F1 hφ)
  have e : φ * w * (φ * w) = (φ * w * φ⁻¹ * w⁻¹) * (w * (φ * φ) * w) := by group
  rw [e, hφφ, mul_one]
  exact mul_mem (mem_sup_left hc) (mem_sup_right (hS.mul_self_mem_rootA_of_mem_W hw))

theorem I2N2_le_H (hS : Setting h L η t Q T) :
    miyamotoI2G h L η ⊔ miyamotoN2G h L η ≤ normalizer (CFSG.centerIn Q : Set G) :=
  sup_le hS.I2_le_H hS.N2_le_H

theorem I2N2_le_normalizer_A2 (_hS : Setting h L η t Q T) :
    miyamotoI2G h L η ⊔ miyamotoN2G h L η ≤ normalizer (miyamotoA2G h L η : Set G) := by
  have : CharP K 2 := h.charP
  have := (normalizer_miyamotoA2G h L η).symm.le
  exact fun g hg => (this (mem_sup_right hg)).2

theorem F2_mod_E (hS : Setting h L η t Q T) :
    (∀ x ∈ miyamotoF2G h L η t Q, x * x ∈ miyamotoEG h L η Q) ∧
      ∀ x ∈ miyamotoF2G h L η t Q, ∀ y ∈ miyamotoF2G h L η t Q,
        x * y * x⁻¹ * y⁻¹ ∈ miyamotoEG h L η Q := by
  have : CharP K 2 := h.charP
  set E := miyamotoEG h L η Q with hEdef
  set U := miyamotoPull h L η (miyamotoRootA h) with hUdef
  set F₂ := miyamotoF2G h L η t Q with hF₂def
  set Sq := closure {z : G | ∃ y ∈ F₂, z = y * y} with hSq
  set X := Sq ⊔ E with hX
  have hSqEU : Sq ≤ E ⊔ U := (closure_le _).2 fun z ⟨y, hy, hz⟩ => by
    rw [hz]
    exact hS.mul_self_mem_EU_of_mem_F2 hy
  have hXEU : X ≤ E ⊔ U := sup_le hSqEU le_sup_left
  have hUR : U ≤ miyamotoRG h L η t Q := hS.rootA_le_W.trans inf_le_left
  have hUE : U ≤ normalizer (E : Set G) := hUR.trans hS.RG_le_normalizer_E
  have hA2E : miyamotoA2G h L η ≤ normalizer (E : Set G) := fun a ha =>
    hS.RG_le_normalizer_E (hS.P1_le_miyamotoRG (mem_sup_right (hS.A2G_le_PG ha)))
  have hNX : ∀ g ∈ miyamotoI2G h L η ⊔ miyamotoN2G h L η, g ∈ normalizer (X : Set G) := by
    intro g hg
    have hgF := hS.I2N2_le_normalizer_F2 hg
    have hSqN : ∀ k ∈ normalizer (F₂ : Set G), k ∈ normalizer (Sq : Set G) := by
      intro k hk
      refine mem_normalizer_fintype fun z hz => ?_
      have key : Sq ≤ Sq.comap (MulAut.conj k).toMonoidHom := (closure_le _).2 fun z ⟨y, hy, hz⟩ =>
        by
        rw [hz]
        simp only [coe_comap, MulEquiv.coe_toMonoidHom, Set.mem_preimage, MulAut.conj_apply,
          SetLike.mem_coe]
        refine subset_closure ⟨k * y * k⁻¹, (mem_normalizer_iff.1 hk y).1 hy, by group⟩
      exact key hz
    exact mem_normalizer_sup (hSqN g hgF) (hS.H_le_normalizer_E (hS.I2N2_le_H hg))
  set B := X ⊓ miyamotoA2G h L η with hB
  have hZB : miyamotoPull h L η (miyamotoZ h) ≤ B :=
    le_inf (hS.ZP_le_E.trans le_sup_right) hS.ZP_le_A2
  have hBinv : ∀ g ∈ miyamotoI2G h L η ⊔ miyamotoN2G h L η, ∀ x ∈ B, g⁻¹ * x * g ∈ B := by
    intro g hg x hx
    have hg' := inv_mem hg
    obtain ⟨hxX, hxA⟩ := mem_inf.1 hx
    have e : g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ := by rw [inv_inv]
    rw [e]
    exact mem_inf.2 ⟨(mem_normalizer_iff.1 (hNX _ hg') x).1 hxX,
      (mem_normalizer_iff.1 (hS.I2N2_le_normalizer_A2 hg') x).1 hxA⟩
  have hBA : B ≠ miyamotoA2G h L η := by
    intro hBeq
    have ha := hS.rootA_le_A2G (hS.rootElt_mem_rootA 1)
    have haZ : hS.rootElt 1 ∉ miyamotoZG h L η := fun hz => by
      have := (hS.rootElt_mem_F1_iff (a := 1)).1 (hS.E_le_F1 (hS.ZP_le_E hz))
      exact one_ne_zero this
    obtain ⟨m₁, hm₁, -, -, hne, -, -⟩ := hS.exists_A2G_commutator_ne ha haZ
    apply hne
    have hm₁X : m₁ ∈ X := by
      rw [← hBeq] at hm₁
      exact hm₁.1
    obtain ⟨e, he, u, hu, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer' hUE (hXEU hm₁X)
    have hau := hS.rootA_comm hu (hS.rootElt_mem_rootA 1)
    have hea : e * hS.rootElt 1 = hS.rootElt 1 * e :=
      mem_centralizer_iff.1 (hS.RG_le_centralizer_E (hUR (hS.rootElt_mem_rootA 1))) e he
    rw [commutatorElement_def]
    calc e * u * hS.rootElt 1 * (e * u)⁻¹ * (hS.rootElt 1)⁻¹ =
        e * (u * hS.rootElt 1) * u⁻¹ * e⁻¹ * (hS.rootElt 1)⁻¹ := by group
      _ = (e * hS.rootElt 1) * e⁻¹ * (hS.rootElt 1)⁻¹ := by rw [hau]; group
      _ = 1 := by rw [hea]; group
  have hB : B = miyamotoPull h L η (miyamotoZ h) :=
    (miyamotoI2N2G_irreducible h L η hZB inf_le_right hBinv).resolve_right hBA
  have hXE : X ≤ E := by
    intro x hx
    have hxEA : x ∈ E ⊔ miyamotoA2G h L η := by
      have := hXEU hx
      exact (sup_le_sup_left (hS.rootA_le_A2G) E) this
    obtain ⟨e, he, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer' hA2E hxEA
    have haX : a ∈ X := by
      have := mul_mem (inv_mem (mem_sup_right he : e ∈ X)) hx
      rwa [inv_mul_cancel_left] at this
    have haB : a ∈ B := mem_inf.2 ⟨haX, ha⟩
    rw [hB] at haB
    exact mul_mem he (hS.ZP_le_E haB)
  have hsq : ∀ x ∈ F₂, x * x ∈ E := fun x hx => hXE (mem_sup_left (subset_closure ⟨x, hx, rfl⟩))
  refine ⟨hsq, fun x hx y hy => ?_⟩
  have e : x * y * x⁻¹ * y⁻¹ = (x * x) * ((x⁻¹ * y) * (x⁻¹ * y)) * (y * y)⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem (hsq x hx) (hsq _ (mul_mem (inv_mem hx) hy))) (inv_mem (hsq y hy))

theorem E_inf_W (hS : Setting h L η t Q T) :
    miyamotoEG h L η Q ⊓ (miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)) =
      ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxE, -, hxC⟩ := hx
  have : x ∈ miyamotoF1G h L η t ⊓ centralizer (miyamotoI1G h L η : Set G) :=
    mem_inf.2 ⟨hS.E_le_F1 hxE, hxC⟩
  rwa [hS.F1_inf_centralizer_I1] at this

theorem W_mul_self (hS : Setting h L η t Q T) {w : G}
    (hw : w ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)) : w * w = 1 := by
  have h1 := hS.F2_mod_E.1 w (hS.W_le_F2 hw)
  have : w * w ∈ miyamotoEG h L η Q ⊓
      (miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)) :=
    mem_inf.2 ⟨h1, mul_mem hw hw⟩
  rwa [hS.E_inf_W, mem_bot] at this

theorem W_comm (hS : Setting h L η t Q T) {w w' : G}
    (hw : w ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G))
    (hw' : w' ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)) :
    w * w' = w' * w := by
  have h1 := hS.F2_mod_E.2 w (hS.W_le_F2 hw) w' (hS.W_le_F2 hw')
  have : w * w' * w⁻¹ * w'⁻¹ ∈ miyamotoEG h L η Q ⊓
      (miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)) :=
    mem_inf.2 ⟨h1, mul_mem (mul_mem (mul_mem hw hw') (inv_mem hw)) (inv_mem hw')⟩
  rw [hS.E_inf_W, mem_bot] at this
  calc w * w' = w * w' * w⁻¹ * w'⁻¹ * (w' * w) := by group
    _ = w' * w := by rw [this, one_mul]

theorem commutator_W_RI2_mem_F (hS : Setting h L η t Q T) {w y : G}
    (hw : w ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G))
    (hy : y ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G)) :
    w⁻¹ * y⁻¹ * w * y ∈ miyamotoFG h L η t Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ₁ : miyamotoI1G h L η ≤ miyamotoIG h L η := hS.I1G_le_IG
  have hJ₂ : miyamotoI2G h L η ≤ miyamotoIG h L η := hS.tori_le_IG.2.2.2
  have hJ := sup_le hJ₁ hJ₂
  refine gomi_commutator_mem_conj (p := 2) (A := miyamotoRG h L η t Q)
    (N := miyamotoFG h L η t Q) (J₁ := miyamotoI1G h L η) (J₂ := miyamotoI2G h L η)
    hS.isPGroup_RG
    (fun hd => Nat.not_even_iff_odd.2 (hS.odd_card_of_le_IG hJ) (even_iff_two_dvd.2 hd))
    (fun j hj => hS.IG_le_normalizer_RG (hJ hj)) (fun j hj => hS.IG_le_normalizer_FG (hJ hj))
    (hS.le_normalizer_of_le_IG hJ₁ hJ₂) (hS.le_normalizer_of_le_IG hJ₂ hJ₁) hS.F_le_RG
    hS.RG_le_normalizer_F (fun a ha => ?_) ?_ w hw y hy
  · obtain ⟨w', hw', f', hf', rfl⟩ := hS.exists_mul_of_mem_RG ha
    obtain ⟨φ, hφ, c, hc, rfl⟩ := hS.exists_mul_of_mem_F1 hf'
    refine ⟨w', hw', c, mem_inf.2 ⟨hS.P1_le_miyamotoRG (mem_sup_left hc.1), hc.2⟩, φ, hφ, ?_⟩
    rw [hS.F1_comm (hS.F_le_F1 hφ) hc.1, mul_assoc]
  · rintro x ⟨⟨hxR, hx₁⟩, ⟨-, hx₂⟩⟩
    obtain ⟨-, -, ⟨p, hp, hpX, hpA⟩⟩ := hS.exists_torusElt_weightA_ne_one
    have hxF := hS.RG_inf_centralizer_le_F1 hpX hpA (mem_inf.2 ⟨hxR, hx₂⟩)
    have : x ∈ miyamotoF1G h L η t ⊓ centralizer (miyamotoI1G h L η : Set G) :=
      mem_inf.2 ⟨hxF, hx₁⟩
    rw [hS.F1_inf_centralizer_I1, mem_bot] at this
    rw [this]
    exact one_mem _

theorem commutator_F1_W_mem_F (hS : Setting h L η t Q T) {y w : G}
    (hy : y ∈ miyamotoF1G h L η t)
    (hw : w ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)) :
    y * w * y⁻¹ * w⁻¹ ∈ miyamotoFG h L η t Q := by
  obtain ⟨φ, hφ, c, hc, rfl⟩ := hS.exists_mul_of_mem_F1 hy
  have hcR : c ∈ miyamotoRG h L η t Q := hS.P1_le_miyamotoRG (mem_sup_left hc.1)
  have hφR := hS.F_le_RG hφ
  have h1 := hS.commutator_W_RI2_mem_F hw (mem_inf.2 ⟨hcR, hc.2⟩)
  have h2 : c * w * c⁻¹ * w⁻¹ ∈ miyamotoFG h L η t Q := by
    have := (mem_normalizer_iff.1 (hS.RG_le_normalizer_F (mul_mem hcR hw.1)) _).1 (inv_mem h1)
    rwa [show c * w * (w⁻¹ * c⁻¹ * w * c)⁻¹ * (c * w)⁻¹ = c * w * c⁻¹ * w⁻¹ by group] at this
  have h3 := hS.E_le_F (hS.commutator_F_RG_mem_E hφ hw.1)
  have e : φ * c * w * (φ * c)⁻¹ * w⁻¹ =
      φ * (c * w * c⁻¹ * w⁻¹) * φ⁻¹ * (φ * w * φ⁻¹ * w⁻¹) := by group
  rw [e]
  exact mul_mem ((mem_normalizer_iff.1 (hS.RG_le_normalizer_F hφR) _).1 h2) h3

theorem commutator_RG_mem_F (hS : Setting h L η t Q T) {r r' : G}
    (hr : r ∈ miyamotoRG h L η t Q) (hr' : r' ∈ miyamotoRG h L η t Q) :
    r * r' * r⁻¹ * r'⁻¹ ∈ miyamotoFG h L η t Q := by
  have hFN := hS.RG_le_normalizer_F
  obtain ⟨w, hw, y, hy, rfl⟩ := hS.exists_mul_of_mem_RG hr
  obtain ⟨w', hw', y', hy', rfl⟩ := hS.exists_mul_of_mem_RG hr'
  have hwR := hw.1
  have hw'R := hw'.1
  have hyR : y ∈ miyamotoRG h L η t Q := hS.P1_le_miyamotoRG (mem_sup_left hy)
  have hy'R : y' ∈ miyamotoRG h L η t Q := hS.P1_le_miyamotoRG (mem_sup_left hy')
  have c1 : w * w' * w⁻¹ * w'⁻¹ = 1 := by rw [hS.W_comm hw hw']; group
  have c2 : y * y' * y⁻¹ * y'⁻¹ = 1 := by rw [hS.F1_comm hy hy']; group
  have c3 := hS.commutator_F1_W_mem_F hy hw'
  have c4 : w * y' * w⁻¹ * y'⁻¹ ∈ miyamotoFG h L η t Q := by
    have := inv_mem (hS.commutator_F1_W_mem_F hy' hw)
    rwa [show (y' * w * y'⁻¹ * w⁻¹)⁻¹ = w * y' * w⁻¹ * y'⁻¹ by group] at this
  have e : w * y * (w' * y') * (w * y)⁻¹ * (w' * y')⁻¹ =
      w * (y * w' * y⁻¹ * w'⁻¹) * w⁻¹ * (w' * (w * y' * w⁻¹ * y'⁻¹) * w'⁻¹) := by
    calc w * y * (w' * y') * (w * y)⁻¹ * (w' * y')⁻¹ =
        w * ((y * w' * y⁻¹ * w'⁻¹) * (w' * (y * y' * y⁻¹ * y'⁻¹) * w'⁻¹)) * w⁻¹ *
          ((w * w' * w⁻¹ * w'⁻¹) * (w' * (w * y' * w⁻¹ * y'⁻¹) * w'⁻¹)) := by group
      _ = w * (y * w' * y⁻¹ * w'⁻¹) * w⁻¹ * (w' * (w * y' * w⁻¹ * y'⁻¹) * w'⁻¹) := by
        rw [c1, c2]; group
  rw [e]
  refine mul_mem ((mem_normalizer_iff.1 (hFN hwR) _).1 c3) ?_
  exact (mem_normalizer_iff.1 (hFN hw'R) _).1 c4

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
