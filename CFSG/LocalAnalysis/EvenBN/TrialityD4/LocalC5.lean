module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalD1Defs
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalJZeroLayerSylow

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open scoped commutatorElement Pointwise

section Defs

variable {G : Type*} [Group G] {L : Subgroup G} {q : ℕ}

@[expose] noncomputable def yamadaC₅ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  pCoreOf 2 (normalizer (yamadaC₁ d t : Set G))

@[expose] noncomputable def yamadaR₅ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaC₅ d t ⊔ d.S.map L.subtype

theorem yamadaC₅_le (d : TrialityD4Data L q) (t : G) :
    yamadaC₅ d t ≤ normalizer (yamadaC₁ d t : Set G) :=
  LieType.BorelTits.pCoreOf_le 2 _

theorem le_normalizer_yamadaC₅ (d : TrialityD4Data L q) (t : G) :
    normalizer (yamadaC₁ d t : Set G) ≤ normalizer (yamadaC₅ d t : Set G) :=
  LieType.BorelTits.le_normalizer_pCoreOf 2 _

theorem t_mem_normalizer_yamadaC₁ (d : TrialityD4Data L q) (t : G) :
    t ∈ normalizer (yamadaC₁ d t : Set G) :=
  le_normalizer_yamadaC₁ d t (le_normalizer (mem_sup_right (mem_zpowers t)))

end Defs

section Generic

variable {G : Type*} [Group G]

theorem card_sup_mul_card_inf_eq_D4 {A B : Subgroup G} (hB : B ≤ normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := normalizer (A : Set G)
  have hAN : A ≤ N := le_normalizer
  have : (A.subgroupOf N).Normal := normal_in_normalizer
  have hnorm : ∀ (X : Subgroup N) (Y : Subgroup N) [Y.Normal],
      Nat.card (X ⊔ Y : Subgroup N) * Nat.card (X ⊓ Y : Subgroup N) = Nat.card X * Nat.card Y := by
    intro X Y _
    have h1 := Subgroup.relIndex_mul_card (H := Y) (K := X ⊔ Y)
    have h2 := Subgroup.relIndex_mul_card (H := Y) (K := X)
    rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : Y ≤ X ⊔ Y)] at h1
    rw [inf_comm] at h2
    rw [← h1, ← h2]
    ring
  have h := hnorm (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ Y : Subgroup G, Y ≤ N → Nat.card (Y.subgroupOf N) = Nat.card Y := fun Y hY =>
    Nat.card_congr (subgroupOfEquivOfLe hY).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

theorem le_thompsonSubgroup_D4 {S A : Subgroup G} (hA : A ≤ S) (hc : IsMulCommutative A)
    (hmax : ∀ B : Subgroup G, B ≤ S → IsMulCommutative B → Nat.card B ≤ Nat.card A) :
    A ≤ CFSG.Open.thompsonSubgroup S := by
  rw [CFSG.Open.thompsonSubgroup_eq_iSup]
  exact le_iSup_of_le A (le_iSup_of_le hA (le_iSup_of_le hc (le_iSup_of_le hmax le_rfl)))

theorem thompsonSubgroup_le_D4 {S D : Subgroup G}
    (h : ∀ A : Subgroup G, A ≤ S → IsMulCommutative A →
      (∀ B : Subgroup G, B ≤ S → IsMulCommutative B → Nat.card B ≤ Nat.card A) → A ≤ D) :
    CFSG.Open.thompsonSubgroup S ≤ D := by
  rw [CFSG.Open.thompsonSubgroup_eq_iSup]
  exact iSup_le fun A => iSup_le fun hA => iSup_le fun hAc => iSup_le fun hAmax => h A hA hAc hAmax

variable {A : Subgroup G} {t : G}

theorem mem_sup_zpowers_iff_of_D4 (htt : t * t = 1) (htA : t ∈ normalizer (A : Set G)) {x : G} :
    x ∈ A ⊔ zpowers t ↔ x ∈ A ∨ ∃ a ∈ A, x = a * t := by
  constructor
  · intro hx
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left A (zpowers t) ((zpowers_le).2 htA),
      Set.mem_mul] at hx
    obtain ⟨a, ha, τ, hτ, rfl⟩ := hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [show m + m = 2 * m by ring, zpow_mul, zpow_two, htt, one_zpow, mul_one]
      exact ha
    · right
      refine ⟨a, ha, ?_⟩
      rw [zpow_add_one, zpow_mul, zpow_two, htt, one_zpow, one_mul]
  · rintro (hx | ⟨a, ha, rfl⟩)
    · exact mem_sup_left hx
    · exact mul_mem (mem_sup_left ha) (mem_sup_right (mem_zpowers t))

theorem le_of_mul_comm_of_le_sup_zpowers_D4 [Finite G] (htt : t * t = 1)
    (htA : t ∈ normalizer (A : Set G)) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : 2 * Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G) < Nat.card A)
    {X : Subgroup G} (hX : X ≤ A ⊔ zpowers t) (hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hXc : Nat.card A ≤ Nat.card X) : X ≤ A := by
  by_contra hn
  obtain ⟨x, hxX, hxA⟩ := Set.not_subset.1 hn
  obtain hx | ⟨a, ha, rfl⟩ := (mem_sup_zpowers_iff_of_D4 htt htA).1 (hX hxX)
  · exact hxA hx
  have hXA : X ⊓ A ≤ A ⊓ centralizer ({t} : Set G) := by
    intro y hy
    obtain ⟨hyX, hyA⟩ := Subgroup.mem_inf.1 hy
    refine Subgroup.mem_inf.2 ⟨hyA, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := hXab y hyX _ hxX
    have h2 : y * a = a * y := hAab y hyA a ha
    have h3 : a * (y * t) = a * (t * y) := by
      calc a * (y * t) = y * (a * t) := by rw [← mul_assoc, ← h2, mul_assoc]
        _ = a * t * y := h1
        _ = a * (t * y) := by rw [mul_assoc]
    exact mul_left_cancel h3
  have h1 := card_sup_mul_card_inf_eq_D4 (A := A) (B := X)
    (hX.trans (sup_le le_normalizer ((zpowers_le).2 htA)))
  have h2 : Nat.card (A ⊔ X : Subgroup G) ≤ 2 * Nat.card A := by
    have h3 := card_sup_mul_card_inf_eq_D4 (A := A) (B := zpowers t) ((zpowers_le).2 htA)
    have h4 : Nat.card (zpowers t) ≤ 2 :=
      Nat.card_zpowers t ▸ Nat.le_of_dvd (by norm_num)
        (orderOf_dvd_of_pow_eq_one (by rw [sq, htt]))
    have h5 : Nat.card (A ⊔ zpowers t : Subgroup G) ≤ 2 * Nat.card A := by
      have hpos : 0 < Nat.card (A ⊓ zpowers t : Subgroup G) := Nat.card_pos
      calc Nat.card (A ⊔ zpowers t : Subgroup G) ≤
          Nat.card (A ⊔ zpowers t : Subgroup G) * Nat.card (A ⊓ zpowers t : Subgroup G) :=
            Nat.le_mul_of_pos_right _ hpos
        _ = Nat.card A * Nat.card (zpowers t) := h3
        _ ≤ Nat.card A * 2 := Nat.mul_le_mul_left _ h4
        _ = 2 * Nat.card A := mul_comm _ _
    exact (Subgroup.card_le_of_le (sup_le le_sup_left hX)).trans h5
  have hpos : 0 < Nat.card A := Nat.card_pos
  have h3 : Nat.card A * Nat.card X ≤ Nat.card A * (2 * Nat.card (X ⊓ A : Subgroup G)) := by
    rw [← h1, inf_comm]
    calc Nat.card (A ⊔ X : Subgroup G) * Nat.card (X ⊓ A : Subgroup G) ≤
        2 * Nat.card A * Nat.card (X ⊓ A : Subgroup G) := Nat.mul_le_mul_right _ h2
      _ = _ := by ring
  have h4 := Nat.le_of_mul_le_mul_left h3 hpos
  have h5 := Subgroup.card_le_of_le hXA
  omega

theorem normalizer_sup_zpowers_le_D4 [Finite G] (htt : t * t = 1)
    (htA : t ∈ normalizer (A : Set G)) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : 2 * Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G) < Nat.card A) :
    normalizer ((A ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (A : Set G) := by
  intro g hg
  have hle : A.map (MulAut.conj g).toMonoidHom ≤ A := by
    refine le_of_mul_comm_of_le_sup_zpowers_D4 htt htA hAab hcard ?_ ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      exact (mem_normalizer_iff.1 hg u).1 (mem_sup_left hu)
    · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show g * u * g⁻¹ * (g * v * g⁻¹) = g * (u * v) * g⁻¹ by group, hAab u hu v hv]
      group
    · rw [card_map_of_injective (MulAut.conj g).injective]
  exact mem_normalizer_fintype fun u hu => hle ⟨u, hu, rfl⟩

theorem normalizer_sup_zpowers_le_inf_D4 [Finite G] (htt : t * t = 1)
    (htA : t ∈ normalizer (A : Set G)) (htA' : t ∉ A) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAe : ∀ a ∈ A, a * a = 1)
    (hcard : 2 * Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G) < Nat.card A) :
    normalizer ((A ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer (((A ⊓ centralizer ({t} : Set G)) ⊔ zpowers t : Subgroup G) : Set G) := by
  intro g hg
  have hgA := normalizer_sup_zpowers_le_D4 htt htA hAab hcard hg
  have hgt : g * t * g⁻¹ ∈ A ⊔ zpowers t :=
    (mem_normalizer_iff.1 hg t).1 (mem_sup_right (mem_zpowers t))
  obtain ⟨a, ha, hga⟩ : ∃ a ∈ A, g * t * g⁻¹ = a * t := by
    rcases (mem_sup_zpowers_iff_of_D4 htt htA).1 hgt with h1 | h1
    · exfalso
      refine htA' ?_
      have := (mem_normalizer_iff.1 (inv_mem hgA) _).1 h1
      rwa [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at this
    · exact h1
  have hat : a * t = t * a := by
    have h1 : (a * t) * (a * t) = 1 := by
      rw [← hga]
      calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
    have h2 : t * a * t = a⁻¹ := by
      calc t * a * t = a⁻¹ * (a * t * (a * t)) := by group
        _ = a⁻¹ := by rw [h1, mul_one]
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hAe a ha)
    calc a * t = t * (t * a * t) := by rw [← mul_assoc, ← mul_assoc, htt, one_mul]
      _ = t * a := by rw [h2, hainv]
  have hgC : g ∈ normalizer ((A ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) := by
    refine mem_normalizer_fintype fun w hw => ?_
    obtain ⟨hwA, hwt⟩ := Subgroup.mem_inf.1 hw
    have hz : g * w * g⁻¹ ∈ A := (mem_normalizer_iff.1 hgA w).1 hwA
    have hwt' : w * t = t * w := mem_centralizer_singleton_iff.1 hwt
    have h1 : g * w * g⁻¹ * (a * t) = a * t * (g * w * g⁻¹) := by
      rw [← hga]
      calc g * w * g⁻¹ * (g * t * g⁻¹) = g * (w * t) * g⁻¹ := by group
        _ = g * (t * w) * g⁻¹ := by rw [hwt']
        _ = g * t * g⁻¹ * (g * w * g⁻¹) := by group
    have h2 : g * w * g⁻¹ * a = a * (g * w * g⁻¹) := hAab _ hz a ha
    refine Subgroup.mem_inf.2 ⟨hz, mem_centralizer_singleton_iff.2 ?_⟩
    have h3 : a * (g * w * g⁻¹ * t) = a * (t * (g * w * g⁻¹)) := by
      calc a * (g * w * g⁻¹ * t) = g * w * g⁻¹ * (a * t) := by rw [← mul_assoc, ← h2, mul_assoc]
        _ = a * t * (g * w * g⁻¹) := h1
        _ = a * (t * (g * w * g⁻¹)) := by rw [mul_assoc]
    exact mul_left_cancel h3
  have htC : t ∈ normalizer ((A ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) :=
    Common.mem_normalizer_inf htA (le_normalizer (mem_centralizer_singleton_iff.2 rfl))
  refine mem_normalizer_fintype fun x hx => ?_
  rcases (mem_sup_zpowers_iff_of_D4 htt htC).1 hx with hx | ⟨w, hw, rfl⟩
  · exact mem_sup_left ((mem_normalizer_iff.1 hgC x).1 hx)
  · rw [show g * (w * t) * g⁻¹ = g * w * g⁻¹ * (g * t * g⁻¹) by group, hga]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.1 hgC w).1 hw))
      (mul_mem (mem_sup_left ⟨ha, mem_centralizer_singleton_iff.2 hat⟩)
        (mem_sup_right (mem_zpowers t)))

end Generic

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem commutatorElement_mem_V_of_mem_D {a b : X} (ha : a ∈ d.D) (hb : b ∈ d.D) :
    a * b * a⁻¹ * b⁻¹ ∈ d.V := by
  have := commutator_mem_commutator ha hb
  rwa [d.commutator_D_eq, commutatorElement_def] at this

theorem D_le_W_sup_conj_u : d.D ≤ d.W ⊔ d.W.map (MulAut.conj d.u).toMonoidHom := by
  have huu := d.u_mul_self
  have hU₂ : d.U₂ ≤ d.W.map (MulAut.conj d.u).toMonoidHom := by
    rintro _ ⟨a, rfl⟩
    refine ⟨d.x₅ a, d.x₅_mem_W a, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← d.u_x₂, d.u_inv]
    calc d.u * (d.u * d.x₂ a * d.u) * d.u = (d.u * d.u) * d.x₂ a * (d.u * d.u) := by group
      _ = d.x₂ a := by rw [huu, one_mul, mul_one]
  have hU₃ : d.U₃ ≤ d.W.map (MulAut.conj d.u).toMonoidHom := by
    rintro _ ⟨a, rfl⟩
    refine ⟨d.x₄ a, d.x₄_mem_W a, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← d.u_x₃, d.u_inv]
    calc d.u * (d.u * d.x₃ a * d.u) * d.u = (d.u * d.u) * d.x₃ a * (d.u * d.u) := by group
      _ = d.x₃ a := by rw [huu, one_mul, mul_one]
  show d.U₂ ⊔ (d.U₃ ⊔ d.W) ≤ _
  exact sup_le (hU₂.trans le_sup_right) (sup_le (hU₃.trans le_sup_right) le_sup_left)

theorem center_SL_two_eq_bot_D4 {K : Type*} [Field K] [CharP K 2] :
    center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  refine eq_bot_iff.2 fun A hA => ?_
  obtain ⟨r, hr, hA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have h1 : (r - 1) ^ 2 = 0 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination hr - r * h2 + h2
  have h3 : r = 1 := sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h1)
  rw [mem_bot]
  exact Subtype.ext (by rw [← hA, h3, map_one, Matrix.SpecialLinearGroup.coe_one])

theorem eq_one_of_mem_leviShort_of_trivial_D_mod_V {s : X} (hs : s ∈ d.leviShort)
    (htriv : ∀ z ∈ d.D, s * z * s⁻¹ * z⁻¹ ∈ d.V) : s = 1 := by
  have := d.finite
  set N := Common.centralizerMod d.leviShort d.D d.V
    (fun g hg y hy => (mem_normalizer_iff.1 (d.leviShort_le_normalizer_D hg) y).1 hy)
    (fun g hg b hb => (mem_normalizer_iff.1 (d.leviShort_le_normalizer_V hg) b).1 hb)
    with hNdef
  have hNn : (N.subgroupOf d.leviShort).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Common.conj_mem_centralizerMod g.2 hn⟩
  set φ := d.leviShortEquiv with hφ
  set K := (N.subgroupOf d.leviShort).comap φ.symm.toMonoidHom with hK
  have hKn : K.Normal := hNn.comap _
  have hq2 := d.two_le_q
  have hcard : 8 ≤ Nat.card d.Γ := by
    rw [d.card_Γ]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq2 3
  have hQ := CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2 d.Γ
    le_rfl (Or.inr (by omega)) (Or.inr (by omega))
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hKn with htop | hcen
  · exfalso
    have hall : ∀ g ∈ d.leviShort, ∀ z ∈ d.D, g * z * g⁻¹ * z⁻¹ ∈ d.V := fun g hg z hz => by
      have h1 : φ ⟨g, hg⟩ ∈ K := htop ▸ mem_top _
      have h2 : φ.symm (φ ⟨g, hg⟩) ∈ N.subgroupOf d.leviShort := h1
      rw [MulEquiv.symm_apply_apply, mem_subgroupOf] at h2
      exact h2.2 z hz
    have hYD : d.Y ≤ d.D := d.Y_le_W.trans (d.W_le_F.trans d.F_le_D)
    have hYn : d.leviShort ≤ normalizer (d.Y : Set X) := fun g hg =>
      mem_normalizer_fintype fun y hy => by
        rw [show g * y * g⁻¹ = g * y * g⁻¹ * y⁻¹ * y by group]
        exact mul_mem (d.V_le_Y (hall g hg y (hYD hy))) hy
    have hlt : q < q ^ 2 := by nlinarith
    have hlt' : q ^ 2 < q ^ 9 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    rcases d.leviShort_irreducible_D_mod_V d.V_le_Y hYD hYn with h1 | h1
    · have := congrArg (fun H : Subgroup X => Nat.card H) h1
      simp only [d.card_Y, d.card_V] at this
      omega
    · have := congrArg (fun H : Subgroup X => Nat.card H) h1
      simp only [d.card_Y, d.card_D] at this
      omega
  · have h1 : φ ⟨s, hs⟩ ∈ K := by
      show φ.symm (φ ⟨s, hs⟩) ∈ N.subgroupOf d.leviShort
      rw [MulEquiv.symm_apply_apply, mem_subgroupOf]
      exact ⟨hs, htriv⟩
    have h2 := hcen h1
    rw [center_SL_two_eq_bot_D4, mem_bot] at h2
    have h3 : (⟨s, hs⟩ : d.leviShort) = 1 := φ.injective (h2.trans (map_one φ).symm)
    exact congrArg Subtype.val h3

theorem mem_D_of_trivial_D_mod_V {g : X} (hg : g ∈ d.D ⊔ d.leviShort)
    (htriv : ∀ z ∈ d.D, g * z * g⁻¹ * z⁻¹ ∈ d.V) : g ∈ d.D := by
  obtain ⟨n, hn, s, hs, rfl⟩ := d.exists_mul_of_mem_D_sup_leviShort hg
  suffices s = 1 by rw [this, mul_one]; exact hn
  refine d.eq_one_of_mem_leviShort_of_trivial_D_mod_V hs fun z hz => ?_
  have h1 := htriv z hz
  have h2 := d.commutatorElement_mem_V_of_mem_D (inv_mem hn) hz
  have h3 : n⁻¹ * (n * s * z * (n * s)⁻¹ * z⁻¹) * n⁻¹⁻¹ ∈ d.V :=
    (mem_normalizer_iff.1 (d.S_le_normalizer_V (d.D_le_S (inv_mem hn))) _).1 h1
  have e : s * z * s⁻¹ * z⁻¹ =
      n⁻¹ * (n * s * z * (n * s)⁻¹ * z⁻¹) * n⁻¹⁻¹ * (n⁻¹ * z * n⁻¹⁻¹ * z⁻¹) := by group
  rw [e]
  exact mul_mem h3 h2

theorem eq_conj_of_trivial_D_mod_V {α : MulAut X} (hV : ∀ y ∈ d.V, α y ∈ d.V)
    (hD : ∀ z ∈ d.D, α z * z⁻¹ ∈ d.V) : ∃ n ∈ d.D, α = MulAut.conj n := by
  have := d.finite
  have hVs : ∀ y ∈ d.V, ∃ y' ∈ d.V, α y' = y := by
    let φV : d.V → d.V := fun y => ⟨α y, hV y y.2⟩
    have hinj : Function.Injective φV := fun a b hab =>
      Subtype.ext (α.injective (congrArg Subtype.val hab))
    intro y hy
    obtain ⟨y', hy'⟩ := Finite.surjective_of_injective hinj ⟨y, hy⟩
    exact ⟨y', y'.2, congrArg Subtype.val hy'⟩
  have hC : ∀ c ∈ centralizer (d.V : Set X), α c ∈ centralizer (d.V : Set X) := by
    intro c hc
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨y', hy'V, rfl⟩ := hVs y hy
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hc y' hy'V]
  have hlevi : ∀ s ∈ d.leviShort, α s * s⁻¹ ∈ d.D := by
    intro s hs
    have hsC : α s ∈ centralizer (d.V : Set X) := hC s (d.leviShort_le_centralizer_V hs)
    have hs' : α s ∈ d.D ⊔ d.leviShort := by rw [← d.centralizer_V_eq]; exact hsC
    have hg : s⁻¹ * α s ∈ d.D ⊔ d.leviShort := mul_mem (inv_mem (mem_sup_right hs)) hs'
    have hgD : s⁻¹ * α s ∈ d.D := by
      refine d.mem_D_of_trivial_D_mod_V hg fun z hz => ?_
      have hw : s * z * s⁻¹ ∈ d.D := (mem_normalizer_iff.1 (d.leviShort_le_normalizer_D hs) z).1 hz
      have h1 := hD _ hw
      have h2 := hD z hz
      have hαw : α (s * z * s⁻¹) = α s * α z * (α s)⁻¹ := by rw [map_mul, map_mul, map_inv]
      have hcomm : (α z * z⁻¹) * α s = α s * (α z * z⁻¹) := mem_centralizer_iff.1 hsC _ h2
      have hz' : z⁻¹ * α s * z = (α z)⁻¹ * α s * α z := by
        calc z⁻¹ * α s * z = (α z)⁻¹ * ((α z * z⁻¹) * α s) * z := by group
          _ = (α z)⁻¹ * (α s * (α z * z⁻¹)) * z := by rw [hcomm]
          _ = (α z)⁻¹ * α s * α z := by group
      have e : s⁻¹ * α s * z * (s⁻¹ * α s)⁻¹ * z⁻¹ =
          s⁻¹ * ((α z * z⁻¹)⁻¹ * (α (s * z * s⁻¹) * (s * z * s⁻¹)⁻¹)) * s⁻¹⁻¹ := by
        rw [hαw]
        calc s⁻¹ * α s * z * (s⁻¹ * α s)⁻¹ * z⁻¹ =
            s⁻¹ * (z * (z⁻¹ * α s * z) * (α s)⁻¹) * s * z⁻¹ := by group
          _ = s⁻¹ * (z * ((α z)⁻¹ * α s * α z) * (α s)⁻¹) * s * z⁻¹ := by rw [hz']
          _ = _ := by group
      rw [e]
      exact (mem_normalizer_iff.1 (d.leviShort_le_normalizer_V (inv_mem hs)) _).1
        (mul_mem (inv_mem h2) h1)
    have := (mem_normalizer_iff.1 (d.leviShort_le_normalizer_D hs) _).1 hgD
    rwa [show s * (s⁻¹ * α s) * s⁻¹ = α s * s⁻¹ by group] at this
  obtain ⟨n, hn, j, hj, hα⟩ := d.eq_conj_of_trivial_mod_D hV hlevi
  obtain ⟨⟨l, m⟩, rfl, hm⟩ := d.mem_J₁.1 hj
  dsimp only at hm
  subst hm
  have h1 := hD (d.x₂ 1) (d.x₂_mem_D 1)
  rw [hα, MulAut.conj_apply] at h1
  have hjx : d.torus (l, 1) * d.x₂ 1 * (d.torus (l, 1))⁻¹ = d.x₂ (l : d.Γ₀) := by
    rw [d.torus_x₂, mul_one]
  have h2 := d.commutatorElement_mem_V_of_mem_D hn (d.x₂_mem_D (l : d.Γ₀))
  have h3 : d.x₂ (l : d.Γ₀) * (d.x₂ 1)⁻¹ ∈ d.V := by
    have e : d.x₂ (l : d.Γ₀) * (d.x₂ 1)⁻¹ = (n * d.x₂ (l : d.Γ₀) * n⁻¹ * (d.x₂ (l : d.Γ₀))⁻¹)⁻¹ *
        (n * (d.torus (l, 1) * d.x₂ 1 * (d.torus (l, 1))⁻¹) * n⁻¹ * (d.x₂ 1)⁻¹) := by
      rw [hjx]; group
    rw [e]
    refine mul_mem (inv_mem h2) ?_
    rwa [show n * (d.torus (l, 1) * d.x₂ 1 * (d.torus (l, 1))⁻¹) * n⁻¹ * (d.x₂ 1)⁻¹ =
      n * d.torus (l, 1) * d.x₂ 1 * (n * d.torus (l, 1))⁻¹ * (d.x₂ 1)⁻¹ by group]
  rw [d.x₂_inv, ← d.x₂_add] at h3
  have h4 := d.x₂_mem_Y_iff.1 (d.V_le_Y h3)
  have hl : (l : d.Γ₀) = 1 := by
    have h5 := d.add_self_Γ₀ 1
    calc (l : d.Γ₀) = ((l : d.Γ₀) + 1) + 1 := by rw [add_assoc, h5, add_zero]
      _ = 1 := by rw [h4, zero_add]
  have hl' : l = 1 := Units.ext hl
  subst hl'
  refine ⟨n, hn, ?_⟩
  rw [hα, show ((1 : (d.Γ₀)ˣ), (1 : d.Γˣ)) = 1 from rfl, map_one, mul_one]

end TrialityD4Data

section Comm

variable {G : Type*} [Group G]

theorem mul_comm_of_mem_sup_D4 {A B : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
  have : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hA a a.2 b b.2)⟩⟩
  have : IsMulCommutative B := ⟨⟨fun a b => Subtype.ext (hB a a.2 b b.2)⟩⟩
  have := isMulCommutative_sup' hAB
  intro x hx y hy
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : (A ⊔ B : Subgroup G)) ⟨y, hy⟩)

theorem mul_comm_of_isMulCommutative_D4 {A : Subgroup G} (hA : IsMulCommutative A) :
    ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)

theorem mul_comm_of_mem_map_conj_D4 {A : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (g : G) : ∀ x ∈ A.map (MulAut.conj g).toMonoidHom, ∀ y ∈ A.map (MulAut.conj g).toMonoidHom,
      x * y = y * x := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [show g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ by group, hA x hx y hy]
  group

end Comm

section D₁Basic

variable {G : Type} [Group G] {L : Subgroup G} {q : ℕ}

theorem D_le_yamadaD₁ (d : TrialityD4Data L q) (t : G) : d.D.map L.subtype ≤ yamadaD₁ d t :=
  le_sup_right

theorem yamadaV₁_le_yamadaD₁ (d : TrialityD4Data L q) (t : G) : yamadaV₁ d t ≤ yamadaD₁ d t :=
  inf_le_left

theorem commute_of_mem_yamadaV₁ (d : TrialityD4Data L q) (t : G) {v δ : G}
    (hv : v ∈ yamadaV₁ d t) (hδ : δ ∈ yamadaD₁ d t) : δ * v = v * δ :=
  mem_centralizer_iff.1 (mem_inf.1 hv).2 δ hδ

theorem normalizer_yamadaD₁_le_normalizer_yamadaV₁ [Finite G] (d : TrialityD4Data L q) (t : G) :
    normalizer (yamadaD₁ d t : Set G) ≤ normalizer (yamadaV₁ d t : Set G) := by
  intro g hg
  refine mem_normalizer_fintype fun v hv => ?_
  obtain ⟨hvD, hvC⟩ := mem_inf.1 hv
  refine mem_inf.2 ⟨(mem_normalizer_iff.1 hg v).1 hvD, mem_centralizer_iff.2 fun δ hδ => ?_⟩
  have hδ' : g⁻¹ * δ * g ∈ yamadaD₁ d t := by
    have := (mem_normalizer_iff.1 (inv_mem hg) δ).1 hδ
    rwa [inv_inv] at this
  have e := mem_centralizer_iff.1 hvC _ hδ'
  calc δ * (g * v * g⁻¹) = g * (g⁻¹ * δ * g * v) * g⁻¹ := by group
    _ = g * (v * (g⁻¹ * δ * g)) * g⁻¹ := by rw [e]
    _ = g * v * g⁻¹ * δ := by group

end D₁Basic

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section D₁

theorem yamadaD₁_le_yamadaC₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    yamadaD₁ d t ≤ yamadaC₁ d t :=
  sup_le inf_le_left (le_sup_left.trans (h.tD_le_yamadaC₁ d))

theorem t_mem_normalizer_yamadaD₁ (h : Setup G L f t) {q : ℕ} (d : TrialityD4Data L q) :
    t ∈ normalizer (yamadaD₁ d t : Set G) := by
  have htJ : t ∈ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
    centralizer_le (map_subtype_le _) h.htL
  refine Common.mem_normalizer_sup (Common.mem_normalizer_inf (t_mem_normalizer_yamadaC₁ d t)
    (le_normalizer_jZeroLayer d htJ)) ?_
  refine mem_normalizer_fintype fun n hn => ?_
  have hnL : n ∈ L := map_subtype_le _ hn
  rw [show t * n * t⁻¹ = n by rw [← mem_centralizer_iff.1 h.htL n hnL, mul_inv_cancel_right]]
  exact hn

theorem yamadaC₁_le_normalizer_yamadaD₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (h561 : yamadaC₁ d t = yamadaD₁ d t ⊔ zpowers t ∧ t ∉ yamadaD₁ d t ∧
      (normalizer (d.V : Set L)).map L.subtype ≤ normalizer (yamadaD₁ d t : Set G)) :
    yamadaC₁ d t ≤ normalizer (yamadaD₁ d t : Set G) := by
  rw [h561.1]
  exact sup_le le_normalizer ((zpowers_le).2 (h.t_mem_normalizer_yamadaD₁ d))

theorem card_tD (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    Nat.card (d.D.map L.subtype ⊔ zpowers t : Subgroup G) = 2 * (2 ^ f) ^ 9 := by
  have hcomm : ∀ x ∈ d.D.map L.subtype, ∀ y ∈ zpowers t, x * y = y * x := fun x hx y hy => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    exact (Commute.zpow_right (mem_centralizer_iff.1 h.htL x (map_subtype_le _ hx) :
      Commute x t) k).eq
  have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  rw [inf_comm, h.zpowers_inf_L (map_subtype_le _), Subgroup.card_bot, mul_one,
    card_map_of_injective L.subtype_injective, d.card_D, h.card_zpowers_t] at h1
  rw [h1, mul_comm]

theorem card_yamadaC₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    Nat.card (yamadaC₁ d t) = 2 * (2 ^ f) ^ 10 := by
  obtain ⟨_, φ, -⟩ := h.yamada_5_3_1_module_all d
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((d.D.map L.subtype ⊔ zpowers t).subgroupOf (yamadaC₁ d t))
  rw [Nat.card_congr φ.toEquiv, card_map_of_injective L.subtype_injective, d.card_V,
    Nat.card_congr (subgroupOfEquivOfLe (h.tD_le_yamadaC₁ d)).toEquiv, h.card_tD d] at h1
  rw [h1]
  ring

theorem yamadaD₁_inf_zpowers (h : Setup G L f t) {q : ℕ} (d : TrialityD4Data L q)
    (ht : t ∉ yamadaD₁ d t) : yamadaD₁ d t ⊓ zpowers t = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxD, hxt⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxt
  rcases h.zpow_eq_one_or_eq k with hk | hk
  · rw [hk]
    exact one_mem _
  · rw [hk] at hxD
    exact absurd hxD ht

theorem card_yamadaD₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (h561 : yamadaC₁ d t = yamadaD₁ d t ⊔ zpowers t ∧ t ∉ yamadaD₁ d t ∧
      (normalizer (d.V : Set L)).map L.subtype ≤ normalizer (yamadaD₁ d t : Set G)) :
    Nat.card (yamadaD₁ d t) = (2 ^ f) ^ 10 := by
  have h1 := card_sup_mul_card_inf_eq_D4 (A := yamadaD₁ d t) (B := zpowers t)
    ((zpowers_le).2 (h.t_mem_normalizer_yamadaD₁ d))
  rw [← h561.1, h.yamadaD₁_inf_zpowers d h561.2.1, Subgroup.card_bot, mul_one, h.card_yamadaC₁ d,
    h.card_zpowers_t] at h1
  omega

omit [Finite G] in
theorem V_le_yamadaV₁ {q : ℕ} (d : TrialityD4Data L q)
    (h562 : IsElemAbelian 2 (yamadaV₁ d t) ∧ Nat.card (yamadaV₁ d t) = (2 ^ f) ^ 2 ∧
      yamadaV₁ d t ⊓ centralizer ({t} : Set G) = d.V.map L.subtype ∧
      yamadaV₁ d t ≤ yamadaF₁ d t) :
    d.V.map L.subtype ≤ yamadaV₁ d t :=
  h562.2.2.1.symm.le.trans inf_le_left

theorem yamadaV₁_inf_D (h : Setup G L f t) {q : ℕ} (d : TrialityD4Data L q)
    (h562 : IsElemAbelian 2 (yamadaV₁ d t) ∧ Nat.card (yamadaV₁ d t) = (2 ^ f) ^ 2 ∧
      yamadaV₁ d t ⊓ centralizer ({t} : Set G) = d.V.map L.subtype ∧
      yamadaV₁ d t ≤ yamadaF₁ d t) :
    yamadaV₁ d t ⊓ d.D.map L.subtype = d.V.map L.subtype := by
  refine le_antisymm (fun x hx => ?_) (le_inf (V_le_yamadaV₁ d h562)
    (map_mono (d.V_le_Y.trans (d.Y_le_W.trans (d.W_le_F.trans d.F_le_D)))))
  rw [← h562.2.2.1]
  exact mem_inf.2 ⟨(mem_inf.1 hx).1, h.L_le_centralizer (map_subtype_le _ (mem_inf.1 hx).2)⟩

theorem yamadaD₁_eq_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (h561 : yamadaC₁ d t = yamadaD₁ d t ⊔ zpowers t ∧ t ∉ yamadaD₁ d t ∧
      (normalizer (d.V : Set L)).map L.subtype ≤ normalizer (yamadaD₁ d t : Set G))
    (h562 : IsElemAbelian 2 (yamadaV₁ d t) ∧ Nat.card (yamadaV₁ d t) = (2 ^ f) ^ 2 ∧
      yamadaV₁ d t ⊓ centralizer ({t} : Set G) = d.V.map L.subtype ∧
      yamadaV₁ d t ≤ yamadaF₁ d t) :
    yamadaD₁ d t = d.D.map L.subtype ⊔ yamadaV₁ d t := by
  have hle : d.D.map L.subtype ⊔ yamadaV₁ d t ≤ yamadaD₁ d t :=
    sup_le (D_le_yamadaD₁ d t) (yamadaV₁_le_yamadaD₁ d t)
  refine (eq_of_le_of_card_ge hle ?_).symm
  have hcomm : ∀ x ∈ d.D.map L.subtype, ∀ y ∈ yamadaV₁ d t, x * y = y * x := fun x hx y hy =>
    commute_of_mem_yamadaV₁ d t hy (D_le_yamadaD₁ d t hx)
  have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  rw [inf_comm, h.yamadaV₁_inf_D d h562, card_map_of_injective L.subtype_injective, d.card_V,
    card_map_of_injective L.subtype_injective, d.card_D, h562.2.1] at h1
  rw [h.card_yamadaD₁ d h561]
  have hq : 0 < 2 ^ f := by positivity
  have h2 : Nat.card (d.D.map L.subtype ⊔ yamadaV₁ d t : Subgroup G) * 2 ^ f =
      (2 ^ f) ^ 10 * 2 ^ f := by rw [h1]; ring
  exact (Nat.eq_of_mul_eq_mul_right hq h2).ge

end D₁

section Thompson

theorem yamadaW₁_spec (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (h562 : IsElemAbelian 2 (yamadaV₁ d t) ∧ Nat.card (yamadaV₁ d t) = (2 ^ f) ^ 2 ∧
      yamadaV₁ d t ⊓ centralizer ({t} : Set G) = d.V.map L.subtype ∧
      yamadaV₁ d t ≤ yamadaF₁ d t) :
    yamadaW₁ d t ≤ yamadaD₁ d t ∧ (∀ x ∈ yamadaW₁ d t, ∀ y ∈ yamadaW₁ d t, x * y = y * x) ∧
      Nat.card (yamadaW₁ d t) = (2 ^ f) ^ 6 := by
  have hWD : d.W.map L.subtype ≤ yamadaD₁ d t :=
    (map_mono (d.W_le_F.trans d.F_le_D)).trans (D_le_yamadaD₁ d t)
  have hWc : ∀ x ∈ d.W.map L.subtype, ∀ y ∈ d.W.map L.subtype, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (d.mul_comm_of_mem_W ha hb)
  have hV₁c : ∀ x ∈ yamadaV₁ d t, ∀ y ∈ yamadaV₁ d t, x * y = y * x := fun x hx y hy =>
    commute_of_mem_yamadaV₁ d t hy (yamadaV₁_le_yamadaD₁ d t hx)
  have hcomm : ∀ x ∈ d.W.map L.subtype, ∀ y ∈ yamadaV₁ d t, x * y = y * x := fun x hx y hy =>
    commute_of_mem_yamadaV₁ d t hy (hWD hx)
  refine ⟨sup_le hWD (yamadaV₁_le_yamadaD₁ d t), mul_comm_of_mem_sup_D4 hWc hV₁c hcomm, ?_⟩
  have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  have hinf : d.W.map L.subtype ⊓ yamadaV₁ d t = d.V.map L.subtype := by
    refine le_antisymm (fun x hx => ?_)
      (le_inf (map_mono (d.V_le_Y.trans d.Y_le_W)) (V_le_yamadaV₁ d h562))
    rw [← h562.2.2.1]
    exact mem_inf.2 ⟨(mem_inf.1 hx).2, h.L_le_centralizer (map_subtype_le _ (mem_inf.1 hx).1)⟩
  rw [hinf, card_map_of_injective L.subtype_injective, d.card_V,
    card_map_of_injective L.subtype_injective, d.card_W, h562.2.1] at h1
  show Nat.card (d.W.map L.subtype ⊔ yamadaV₁ d t : Subgroup G) = _
  have hq : 0 < 2 ^ f := by positivity
  have h2 : Nat.card (d.W.map L.subtype ⊔ yamadaV₁ d t : Subgroup G) * 2 ^ f =
      (2 ^ f) ^ 6 * 2 ^ f := by rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_right hq h2

omit [Finite G] in
theorem u_mem_normalizer_yamadaD₁ (d : TrialityD4Data L (2 ^ f))
    (h561 : yamadaC₁ d t = yamadaD₁ d t ⊔ zpowers t ∧ t ∉ yamadaD₁ d t ∧
      (normalizer (d.V : Set L)).map L.subtype ≤ normalizer (yamadaD₁ d t : Set G)) :
    ((d.u : L) : G) ∈ normalizer (yamadaD₁ d t : Set G) :=
  h561.2.2 ⟨d.u, d.leviShort_le_normalizer_V d.u_mem_leviShort, rfl⟩

theorem yamadaD₁_eq_sup_yamadaW₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (h561 : yamadaC₁ d t = yamadaD₁ d t ⊔ zpowers t ∧ t ∉ yamadaD₁ d t ∧
      (normalizer (d.V : Set L)).map L.subtype ≤ normalizer (yamadaD₁ d t : Set G))
    (h562 : IsElemAbelian 2 (yamadaV₁ d t) ∧ Nat.card (yamadaV₁ d t) = (2 ^ f) ^ 2 ∧
      yamadaV₁ d t ⊓ centralizer ({t} : Set G) = d.V.map L.subtype ∧
      yamadaV₁ d t ≤ yamadaF₁ d t) :
    yamadaD₁ d t = yamadaW₁ d t ⊔ (yamadaW₁ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom := by
  have hW₁D := (h.yamadaW₁_spec d h562).1
  refine le_antisymm ?_ (sup_le hW₁D ?_)
  · rw [h.yamadaD₁_eq_sup d h561 h562]
    refine sup_le ?_ ((le_sup_right : yamadaV₁ d t ≤ yamadaW₁ d t).trans le_sup_left)
    have hD := map_mono (f := L.subtype) d.D_le_W_sup_conj_u
    rw [Subgroup.map_sup] at hD
    have heq : (d.W.map (MulAut.conj d.u).toMonoidHom).map L.subtype =
        (d.W.map L.subtype).map (MulAut.conj ((d.u : L) : G)).toMonoidHom := by
      rw [map_map, map_map]
      congr 1
    rw [heq] at hD
    exact hD.trans (sup_le_sup le_sup_left (map_mono le_sup_left))
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 (u_mem_normalizer_yamadaD₁ d h561) x).1 (hW₁D hx)

end Thompson

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
