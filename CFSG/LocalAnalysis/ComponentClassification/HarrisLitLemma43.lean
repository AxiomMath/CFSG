module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitDihedralSwap
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFacts411

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped Pointwise commutatorElement

variable {X : Type} [Group X]

@[expose] def S1 (t : X) (L S : Subgroup X) : Subgroup X :=
  closure {s : X | s ∈ S ∧ s ^ 2 ∈ zpowers t ⊔ (S ⊓ L)}

variable {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

namespace Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem commutator_mem_tD [Finite X] (hσ : Setup42 h hS w z) {a b : X} (ha : a ∈ S)
    (hb : b ∈ S) : a * b * a⁻¹ * b⁻¹ ∈ zpowers t ⊔ (S ⊓ L) := by
  have hdata := hσ.lift.data
  have hR := h.map_rho_inf_innAut hS
  have hc : a * b * a⁻¹ * b⁻¹ ∈ S := S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha))
    (S.inv_mem hb)
  have hder : ⁅(S.subgroupOf (centralizer ({t} : Set X))).map h.rho,
      (S.subgroupOf (centralizer ({t} : Set X))).map h.rho⁆ ≤
      (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L) := by
    by_cases hne : (S.subgroupOf (centralizer ({t} : Set X))).map h.rho =
        ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L)) ⊔
          zpowers (h.rho ⟨w, hS.le hσ.lift.mem⟩)
    · have h1 : ⁅(S.subgroupOf (centralizer ({t} : Set X))).map h.rho,
          (S.subgroupOf (centralizer ({t} : Set X))).map h.rho⁆ =
          ⁅(S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L),
            (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L)⁆ := by
        calc ⁅(S.subgroupOf (centralizer ({t} : Set X))).map h.rho,
              (S.subgroupOf (centralizer ({t} : Set X))).map h.rho⁆ =
            ⁅((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L)) ⊔
                zpowers (h.rho ⟨w, hS.le hσ.lift.mem⟩),
              ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L)) ⊔
                zpowers (h.rho ⟨w, hS.le hσ.lift.mem⟩)⁆ := by rw [← hne]
          _ = _ := hdata.derived
      rw [h1]
      exact commutator_self_le _
    · exact (hdata.derived_cyclic_of_ne hne).2.1
  have hmem : h.rho ⟨a * b * a⁻¹ * b⁻¹, hS.le hc⟩ ∈
      (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L) := by
    apply hder
    have : (⟨a * b * a⁻¹ * b⁻¹, hS.le hc⟩ : ↥(centralizer ({t} : Set X))) =
        ⁅(⟨a, hS.le ha⟩ : ↥(centralizer ({t} : Set X))), ⟨b, hS.le hb⟩⁆ := by
      rw [commutatorElement_def]
      rfl
    rw [this, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator ⟨⟨a, hS.le ha⟩, ha, rfl⟩ ⟨⟨b, hS.le hb⟩, hb, rfl⟩
  rw [hR] at hmem
  obtain ⟨⟨d, hdH⟩, hdD, hd⟩ := hmem
  have hdD' : d ∈ S ⊓ L := hdD
  have h1 : h.rho ⟨a * b * a⁻¹ * b⁻¹ * d⁻¹, hS.le (S.mul_mem hc (S.inv_mem hdD'.1))⟩ = 1 := by
    have : (⟨a * b * a⁻¹ * b⁻¹ * d⁻¹, hS.le (S.mul_mem hc (S.inv_mem hdD'.1))⟩ :
        ↥(centralizer ({t} : Set X))) = ⟨a * b * a⁻¹ * b⁻¹, hS.le hc⟩ * (⟨d, hdH⟩)⁻¹ := rfl
    rw [this, map_mul, map_inv, ← hd, mul_inv_cancel]
  have h2 := h.mem_zpowers_of_rho_eq_one hS (S.mul_mem hc (S.inv_mem hdD'.1)) h1
  have : a * b * a⁻¹ * b⁻¹ = (a * b * a⁻¹ * b⁻¹ * d⁻¹) * d := by group
  rw [this]
  exact mul_mem (mem_sup_left h2) (mem_sup_right hdD')

theorem mem_S1_iff [Finite X] (hσ : Setup42 h hS w z) {x : X} :
    x ∈ S1 t L S ↔ x ∈ S ∧ x ^ 2 ∈ zpowers t ⊔ (S ⊓ L) := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨one_mem _, by rw [one_pow]; exact one_mem _⟩
    | mul a b _ _ ha hb =>
      refine ⟨S.mul_mem ha.1 hb.1, ?_⟩
      have hc := hσ.commutator_mem_tD (S.inv_mem ha.1) hb.1
      have : (a * b) ^ 2 = a ^ 2 * (a⁻¹ * b * a⁻¹⁻¹ * b⁻¹) * b ^ 2 := by
        rw [sq, sq, sq]
        group
      rw [this]
      exact mul_mem (mul_mem ha.2 hc) hb.2
    | inv a _ ha =>
      refine ⟨S.inv_mem ha.1, ?_⟩
      rw [inv_pow]
      exact inv_mem ha.2
  · intro hx
    exact subset_closure hx

theorem S1_le [Finite X] (_hσ : Setup42 h hS w z) : S1 t L S ≤ S := by
  rw [S1, closure_le]
  exact fun x hx => hx.1

theorem T1_le_S1 [Finite X] (hσ : Setup42 h hS w z) :
    zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2)) ≤ S1 t L S := by
  have htD : t ∈ zpowers t ⊔ (S ⊓ L) := mem_sup_left (mem_zpowers t)
  have ht2 : t ^ 2 = 1 := by rw [← h.config.orderOf_eq, pow_orderOf_eq_one]
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [zpowers_le, hσ.mem_S1_iff]
    exact ⟨h.t_mem hS, by rw [ht2]; exact one_mem _⟩
  · intro d hd
    rw [hσ.mem_S1_iff]
    exact ⟨hd.1, mem_sup_right (pow_mem hd 2)⟩
  · rw [zpowers_le, hσ.mem_S1_iff]
    exact ⟨hσ.u_mem, by rw [hσ.lift.sq_u]; exact one_mem _⟩

theorem S1_inf_T [Finite X] (hσ : Setup42 h hS w z) :
    S1 t L S ⊓ (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) =
      zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2)) := by
  refine le_antisymm (fun x hx => ?_) (le_inf hσ.T1_le_S1 (sup_le le_sup_left
    (zpowers_le.mpr (mem_sup_right (pow_mem (mem_zpowers w) _)))))
  obtain ⟨hx1, hxT⟩ := hx
  have hx2 := ((hσ.mem_S1_iff).mp hx1).2
  have hx' : x ∈ ((zpowers t ⊔ (S ⊓ L) : Subgroup X) : Set X) * (zpowers w : Set X) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hσ.zpowers_w_le_normalizer]
    exact hxT
  obtain ⟨y, hy, _, ⟨j, rfl⟩, rfl⟩ := hx'
  beta_reduce at hx2 ⊢
  have hyN : w ^ j * y * (w ^ j)⁻¹ ∈ zpowers t ⊔ (S ⊓ L) :=
    (mem_normalizer_iff.mp (hσ.zpowers_w_le_normalizer (zpow_mem (mem_zpowers w) j)) y).mp hy
  have hw2' : w ^ (2 * j) ∈ zpowers t ⊔ (S ⊓ L) := by
    have : w ^ (2 * j) = (w ^ j * y * (w ^ j)⁻¹)⁻¹ * y⁻¹ * (y * w ^ j) ^ 2 := by
      rw [two_mul, zpow_add, sq]
      group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hyN) (inv_mem hy)) hx2
  have hw2 : w ^ (2 * j) ∈ (zpowers t ⊔ (S ⊓ L)) ⊓ zpowers w :=
    Subgroup.mem_inf.mpr ⟨hw2', zpow_mem (mem_zpowers w) _⟩
  rw [hσ.disj, mem_bot] at hw2
  have hdvd : (orderOf w : ℤ) ∣ 2 * j := orderOf_dvd_iff_zpow_eq_one.mpr hw2
  rw [hσ.orderOf_w_eq, Nat.cast_mul] at hdvd
  obtain ⟨c, hc⟩ := (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp hdvd
  have hwj : w ^ j = (w ^ (orderOf w / 2)) ^ c := by
    rw [hc, zpow_mul, zpow_natCast]
  rw [hwj]
  exact mul_mem (mem_sup_left hy) (mem_sup_right (zpow_mem (mem_zpowers _) c))

theorem relIndex_T1_S1_le [Finite X] (hσ : Setup42 h hS w z) :
    (zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2))).relIndex (S1 t L S) ≤ 2 := by
  rw [← hσ.S1_inf_T, Subgroup.inf_relIndex_left]
  refine (Subgroup.relIndex_le_of_le_right hσ.S1_le (relIndex_ne_zero_of_finite _ _)).trans ?_
  have hle := (h.lemma41_of_lift hS hσ.lift hσ.gen3).2.2.2.2.1
  have h1 := Subgroup.relIndex_mul_card (H := zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) (K := S)
  rw [inf_of_le_left hσ.T_le] at h1
  have hpos : 0 < Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) := Nat.card_pos
  by_contra hlt
  have : 3 * Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) ≤
      (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex S *
        Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem card_X [Finite X] (hσ : Setup42 h hS w z) :
    Nat.card (closure {t, w ^ (orderOf w / 2), z} : Subgroup X) = 8 := by
  classical
  have hle := hσ.card_X_le
  have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have huX : w ^ (orderOf w / 2) ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have hzX : z ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have ht1 := h.t_ne_one
  have hz1 := hσ.z_ne_one
  have htz : t ≠ z := by simpa using hσ.conj_t_ne_z 1
  have hz2 : z ^ 2 = 1 := hσ.sq_eq_one_of_mem_X hzX
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq, hz2])
  have huD := hσ.u_not_mem_tD
  have htD : t ∈ zpowers t ⊔ (S ⊓ L) := mem_sup_left (mem_zpowers t)
  have hzD : z ∈ zpowers t ⊔ (S ⊓ L) := mem_sup_right hσ.z_mem
  have hsub : ({1, t, z, t * z, w ^ (orderOf w / 2)} : Set X) ⊆
      ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx | hx | hx <;> rw [hx]
    · exact one_mem _
    · exact htX
    · exact hzX
    · exact mul_mem htX hzX
    · exact huX
  have hc5 : ({1, t, z, t * z, w ^ (orderOf w / 2)} : Set X).ncard = 5 := by
    have h1 : t * z ≠ 1 := fun h' => htz (by
      calc t = t * z * z⁻¹ := by group
        _ = z := by rw [h', one_mul, hzinv])
    have h2 : t * z ≠ t := fun h' => hz1 (by simpa using h')
    have h3 : t * z ≠ z := fun h' => ht1 (by simpa using h')
    have hu1 : w ^ (orderOf w / 2) ≠ 1 := fun h' => huD (h' ▸ one_mem _)
    have hut : w ^ (orderOf w / 2) ≠ t := fun h' => huD (h' ▸ htD)
    have huz : w ^ (orderOf w / 2) ≠ z := fun h' => huD (h' ▸ hzD)
    have hutz : w ^ (orderOf w / 2) ≠ t * z := fun h' => huD (h' ▸ mul_mem htD hzD)
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_pair (Ne.symm hutz)]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨Ne.symm h3, Ne.symm huz⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨htz, Ne.symm h2, Ne.symm hut⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨Ne.symm ht1, Ne.symm hz1, Ne.symm h1, Ne.symm hu1⟩
  have hge : 5 ≤ Nat.card (closure {t, w ^ (orderOf w / 2), z} : Subgroup X) := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hc5, ← Nat.card_coe_set_eq] at this
    exact this
  have hp : IsPGroup 2 (closure {t, w ^ (orderOf w / 2), z} : Subgroup X) :=
    hS.isPGroup.to_le (hσ.X_le_T.trans hσ.T_le)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  rw [hn] at hle hge ⊢
  rcases n with _ | _ | _ | _ | n
  · norm_num at hge
  · norm_num at hge
  · norm_num at hge
  · norm_num
  · exfalso
    have : 16 ≤ 2 ^ (n + 1 + 1 + 1 + 1) := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (n + 1 + 1 + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem mem_T1' [Finite X] (hσ : Setup42 h hS w z) {x : X}
    (hx : x ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2))) :
    ∃ a b : X, ∃ d ∈ S ⊓ L, (a = 1 ∨ a = t) ∧ (b = 1 ∨ b = w ^ (orderOf w / 2)) ∧
      x = a * d * b := by
  obtain ⟨i, d, hd, j, rfl⟩ := hσ.mem_T1 hx
  exact ⟨t ^ i, (w ^ (orderOf w / 2)) ^ j, d, hd,
    eq_one_or_eq_of_mem_zpowers h.config.orderOf_eq (zpow_mem (mem_zpowers t) i),
    eq_one_or_eq_of_mem_zpowers hσ.orderOf_u (zpow_mem (mem_zpowers _) j), rfl⟩

theorem comm_tu [Finite X] (hσ : Setup42 h hS w z) :
    (∀ d ∈ S ⊓ L, d * t = t * d) ∧
      (∀ d ∈ S ⊓ L, d * w ^ (orderOf w / 2) = w ^ (orderOf w / 2) * d) ∧
      t * w ^ (orderOf w / 2) = w ^ (orderOf w / 2) * t :=
  ⟨fun _ hd => mem_centralizer_singleton_iff.mp (hS.le hd.1), fun d hd => hσ.lift.comm_D d hd,
    (mem_centralizer_singleton_iff.mp (hS.le hσ.u_mem)).symm⟩

@[expose] def conjDihedral (hσ : Setup42 h hS w z) {m : ℕ}
    (e : ↥(S ⊓ L) ≃* DihedralGroup (2 ^ m)) {s : X} (hs : s ∈ S) :
    DihedralGroup (2 ^ m) →* DihedralGroup (2 ^ m) where
  toFun g := e ⟨s * (e.symm g : X) * s⁻¹, hσ.conj_mem_D hs (e.symm g).2⟩
  map_one' := by
    rw [show (⟨s * ((e.symm 1 : ↥(S ⊓ L)) : X) * s⁻¹, hσ.conj_mem_D hs (e.symm 1).2⟩ :
      ↥(S ⊓ L)) = 1 from Subtype.ext (by simp)]
    exact map_one e
  map_mul' g g' := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]
    group

theorem conjDihedral_apply (hσ : Setup42 h hS w z) {m : ℕ}
    (e : ↥(S ⊓ L) ≃* DihedralGroup (2 ^ m)) {s : X} (hs : s ∈ S) (g : DihedralGroup (2 ^ m)) :
    ((e.symm (hσ.conjDihedral e hs g) : ↥(S ⊓ L)) : X) = s * (e.symm g : X) * s⁻¹ := by
  simp [conjDihedral]

theorem centralizer_D_of_involution [Finite X] (hσ : Setup42 h hS w z) {τ : X} (hτS : τ ∈ S)
    (hτT : τ ∉ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) (hτ2 : τ ^ 2 = 1) :
    (∀ d ∈ S ⊓ L, τ * d * τ⁻¹ = d → d = 1 ∨ d = z) ∧
      ∃ γ₀ ∈ S ⊓ L, γ₀ ^ 2 = z ∧
        ∀ d ∈ S ⊓ L, d⁻¹ * (τ * d * τ⁻¹) = z ↔ d = γ₀ ∨ d = γ₀⁻¹ := by
  obtain ⟨m, hm, ⟨e⟩⟩ := hσ.dihedral
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right (by rw [← sq, hτ2])
  set ψ := hσ.conjDihedral e hτS with hψdef
  have hψ_apply : ∀ g, ((e.symm (ψ g) : ↥(S ⊓ L)) : X) = τ * (e.symm g : X) * τ⁻¹ :=
    hσ.conjDihedral_apply e hτS
  have hψ : ∀ g, ψ (ψ g) = g := by
    intro g
    apply e.symm.injective
    apply Subtype.ext
    rw [hψ_apply, hψ_apply]
    calc τ * (τ * ((e.symm g : ↥(S ⊓ L)) : X) * τ⁻¹) * τ⁻¹ =
        (τ * τ) * (e.symm g : X) * (τ * τ)⁻¹ := by group
      _ = (e.symm g : X) := by rw [← sq, hτ2]; group
  have hz := hσ.coe_symm_r_half hm e
  have hsw : ∀ (i : ZMod (2 ^ m)) (c : DihedralGroup (2 ^ m)),
      c⁻¹ * DihedralGroup.sr i * c ≠ ψ (DihedralGroup.sr i) := by
    intro i c hc
    have hy2 : ((e.symm (DihedralGroup.sr i) : ↥(S ⊓ L)) : X) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← map_pow, sq, DihedralGroup.sr_mul_sr, sub_self,
        DihedralGroup.r_zero, map_one, Subgroup.coe_one]
    have hyz : ((e.symm (DihedralGroup.sr i) : ↥(S ⊓ L)) : X) ∉ zpowers z := by
      intro h'
      rcases eq_one_or_eq_of_mem_zpowers hσ.z_order h' with h1 | h1
      · have : e.symm (DihedralGroup.sr i) = 1 := Subtype.ext h1
        rw [MulEquiv.map_eq_one_iff, DihedralGroup.one_def] at this
        cases this
      · rw [← hz] at h1
        exact absurd (e.symm.injective (Subtype.ext h1)) (by simp)
    apply hσ.conj_ne_of_not_mem_T hτS hτT (e.symm (DihedralGroup.sr i)).2 hy2 hyz
      (e.symm c).2
    have h1 := congrArg (fun g => ((e.symm g : ↥(S ⊓ L)) : X)) hc
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [hψ_apply] at h1
    rw [hτinv] at h1 ⊢
    exact h1.symm
  refine ⟨fun d hd hdτ => ?_, ?_⟩
  · have hfix : ψ (e ⟨d, hd⟩) = e ⟨d, hd⟩ := by
      apply e.symm.injective
      apply Subtype.ext
      rw [hψ_apply, MulEquiv.symm_apply_apply]
      exact hdτ
    rcases (dihedral_swap_fixed_iff hm ψ hψ hsw _).mp hfix with h1 | h1
    · left
      have := congrArg (fun g => ((e.symm g : ↥(S ⊓ L)) : X)) h1
      simpa using this
    · right
      have := congrArg (fun g => ((e.symm g : ↥(S ⊓ L)) : X)) h1
      rw [← hz]
      simpa using this
  · refine ⟨(e.symm (DihedralGroup.r ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))) : X),
      (e.symm _).2, ?_, fun d hd => ?_⟩
    · rw [← Subgroup.coe_pow, ← map_pow, ← hz, sq, DihedralGroup.r_mul_r, ← two_mul]
      congr 2
      rw [show (2 : ZMod (2 ^ m)) = ((2 : ℕ) : ZMod (2 ^ m)) by norm_num, ← Nat.cast_mul,
        ← pow_succ', show m - 2 + 1 = m - 1 by omega]
    · have key : d⁻¹ * (τ * d * τ⁻¹) = z ↔
          (e ⟨d, hd⟩)⁻¹ * ψ (e ⟨d, hd⟩) = DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
        constructor
        · intro h1
          apply e.symm.injective
          apply Subtype.ext
          rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hψ_apply,
            MulEquiv.symm_apply_apply, hz]
          exact h1
        · intro h1
          have := congrArg (fun g => ((e.symm g : ↥(S ⊓ L)) : X)) h1
          simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at this
          rw [hψ_apply, MulEquiv.symm_apply_apply, hz] at this
          exact this
      rw [key, dihedral_swap_twisted_iff hm ψ hψ hsw]
      constructor
      · rintro (h1 | h1)
        · left
          have := congrArg (fun g => ((e.symm g : ↥(S ⊓ L)) : X)) h1
          simpa using this
        · right
          calc d = ((e.symm (e ⟨d, hd⟩) : ↥(S ⊓ L)) : X) := by simp
            _ = ((e.symm (DihedralGroup.r (-((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)))) :
                ↥(S ⊓ L)) : X) := by rw [h1]
            _ = _ := by rw [← DihedralGroup.inv_r, map_inv, Subgroup.coe_inv]
      · rintro (h1 | h1)
        · left
          apply e.symm.injective
          apply Subtype.ext
          rw [MulEquiv.symm_apply_apply]
          exact h1
        · right
          apply e.symm.injective
          apply Subtype.ext
          rw [MulEquiv.symm_apply_apply, ← DihedralGroup.inv_r, map_inv, Subgroup.coe_inv]
          exact h1

theorem lemma43c [Finite X] (hσ : Setup42 h hS w z) {τ : X} (hτS1 : τ ∈ S1 t L S)
    (hτT1 : τ ∉ zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2))) (hτ2 : τ ^ 2 = 1) :
    (zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2))).relIndex (S1 t L S) = 2 ∧
      S1 t L S = zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2)) ⊔ zpowers τ ∧
      ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2))) ⊓ centralizer ({τ} : Set X) =
          closure {t, z} ∨
        ∃ γ ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2)), γ ^ 2 = z ∧
          (zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2))) ⊓ centralizer ({τ} : Set X) =
            zpowers t ⊔ zpowers γ) ∧
      ∀ x ∈ (zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2))) ⊓ centralizer ({τ} : Set X),
        x ^ 2 = 1 → x ∈ closure {t, z} := by
  have hτS := hσ.S1_le hτS1
  have hτT : τ ∉ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := fun h' =>
    hτT1 (hσ.S1_inf_T ▸ Subgroup.mem_inf.mpr ⟨hτS1, h'⟩)
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right (by rw [← sq, hτ2])
  have htS := h.t_mem hS
  have hτt : τ * t = t * τ := mem_centralizer_singleton_iff.mp (hS.le hτS)
  have hτz : τ * z = z * τ := hσ.z_comm hτS
  have hz2 : z ^ 2 = 1 := by rw [← hσ.z_order, pow_orderOf_eq_one]
  have hzz : z * z = 1 := by rw [← sq, hz2]
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  obtain ⟨hDt, hDu, htu⟩ := hσ.comm_tu
  have hzt : z * t = t * z := hDt z hσ.z_mem
  have hzu : z * w ^ (orderOf w / 2) = w ^ (orderOf w / 2) * z := hDu z hσ.z_mem
  obtain ⟨hfix, γ₀, hγ₀D, hγ₀2, htw⟩ := hσ.centralizer_D_of_involution hτS hτT hτ2
  have hTt : ∀ x : X, τ * x * τ⁻¹ = x ↔ x * τ = τ * x := fun x => by
    constructor
    · intro h1
      calc x * τ = (τ * x * τ⁻¹) * τ := by rw [h1]
        _ = τ * x := by group
    · intro h1
      rw [← h1]
      group
  have htτ : t * τ = τ * t := hτt.symm
  have hidx : (zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2))).relIndex (S1 t L S) = 2 := by
    have hle := hσ.relIndex_T1_S1_le
    have hne1 : (zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2))).relIndex (S1 t L S) ≠ 1 :=
      fun h' => hτT1 (Subgroup.relIndex_eq_one.mp h' hτS1)
    have hne0 := relIndex_ne_zero_of_finite
      (zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2))) (S1 t L S)
    omega
  have hS1eq : S1 t L S = zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2)) ⊔ zpowers τ := by
    have hle : zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2)) ⊔ zpowers τ ≤ S1 t L S :=
      sup_le hσ.T1_le_S1 (zpowers_le.mpr hτS1)
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    have h1 := Subgroup.relIndex_mul_card
      (H := zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2))) (K := S1 t L S)
    rw [inf_of_le_left hσ.T1_le_S1, hidx] at h1
    have h2 := Subgroup.relIndex_mul_card
      (H := zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2)))
      (K := zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2)) ⊔ zpowers τ)
    rw [inf_of_le_left (le_sup_left : zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2)) ≤
      zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2)) ⊔ zpowers τ)] at h2
    have hne1 : (zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2))).relIndex
        (zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2)) ⊔ zpowers τ) ≠ 1 := fun h' =>
      hτT1 (Subgroup.relIndex_eq_one.mp h' (mem_sup_right (mem_zpowers τ)))
    have hne0 := relIndex_ne_zero_of_finite
      (zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2)))
      (zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2)) ⊔ zpowers τ)
    have h3 : 2 * Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2)) : Subgroup X) ≤
        (zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2))).relIndex
          (zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2)) ⊔ zpowers τ) *
        Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2)) : Subgroup X) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hτD : ∀ d ∈ S ⊓ L, τ * d * τ⁻¹ ∈ S ⊓ L := fun d hd => hσ.conj_mem_D hτS hd
  have hτu : τ * w ^ (orderOf w / 2) * τ⁻¹ = w ^ (orderOf w / 2) * z ∨
      τ * w ^ (orderOf w / 2) * τ⁻¹ = t * w ^ (orderOf w / 2) * z := by
    have := hσ.conj_u_of_not_mem hτS hτT
    rw [hτinv] at this ⊢
    exact this
  have hcen : ∀ a b : X, ∀ d ∈ S ⊓ L, (a = 1 ∨ a = t) → (b = 1 ∨ b = w ^ (orderOf w / 2)) →
      τ * (a * d * b) * τ⁻¹ = a * (τ * d * τ⁻¹) * (τ * b * τ⁻¹) := by
    intro a b d hd ha hb
    have hτa : τ * a * τ⁻¹ = a := by
      rcases ha with ha | ha <;> rw [ha]
      · group
      · rw [hτt]; group
    calc τ * (a * d * b) * τ⁻¹ = (τ * a * τ⁻¹) * (τ * d * τ⁻¹) * (τ * b * τ⁻¹) := by group
      _ = _ := by rw [hτa]
  have hzX : z ∈ closure ({t, z} : Set X) := subset_closure (by simp)
  have htX : t ∈ closure ({t, z} : Set X) := subset_closure (by simp)
  have htT1 : t ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2)) :=
    mem_sup_left (mem_sup_left (mem_zpowers t))
  have hzT1 : z ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2)) :=
    mem_sup_left (mem_sup_right hσ.z_mem)
  have huT1 : w ^ (orderOf w / 2) ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2)) :=
    mem_sup_right (mem_zpowers _)
  have hadX : ∀ a d : X, (a = 1 ∨ a = t) → (d = 1 ∨ d = z) → a * d ∈ closure ({t, z} : Set X) := by
    intro a d ha hd
    refine mul_mem ?_ ?_
    · rcases ha with ha | ha <;> rw [ha]
      · exact one_mem _
      · exact htX
    · rcases hd with hd | hd <;> rw [hd]
      · exact one_mem _
      · exact hzX
  have hγ₀z : γ₀ * z = z * γ₀ := hσ.z_comm_D hγ₀D
  have hγ₀u : γ₀ * w ^ (orderOf w / 2) = w ^ (orderOf w / 2) * γ₀ := hDu γ₀ hγ₀D
  have hγ₀t : γ₀ * t = t * γ₀ := hDt γ₀ hγ₀D
  have hτγ₀ : τ * γ₀ * τ⁻¹ = γ₀ * z := by
    have := (htw γ₀ hγ₀D).mpr (Or.inl rfl)
    calc τ * γ₀ * τ⁻¹ = γ₀ * (γ₀⁻¹ * (τ * γ₀ * τ⁻¹)) := by group
      _ = γ₀ * z := by rw [this]
  have hγ₀inv : γ₀⁻¹ = γ₀ * z := by
    have h4 : γ₀ * (γ₀ * z) = 1 := by
      calc γ₀ * (γ₀ * z) = γ₀ ^ 2 * z := by rw [sq, mul_assoc]
        _ = 1 := by rw [hγ₀2, hzz]
    exact inv_eq_of_mul_eq_one_right h4
  refine ⟨hidx, hS1eq, ?_⟩
  rcases hτu with hτu | hτu
  ·
    have hγ2 : (γ₀ * w ^ (orderOf w / 2)) ^ 2 = z := by
      rw [(show Commute γ₀ (w ^ (orderOf w / 2)) from hγ₀u).mul_pow 2, hγ₀2, hσ.lift.sq_u,
        mul_one]
    have hγT1 : γ₀ * w ^ (orderOf w / 2) ∈
        zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2)) :=
      mul_mem (mem_sup_left (mem_sup_right hγ₀D)) huT1
    have hγτ : τ * (γ₀ * w ^ (orderOf w / 2)) * τ⁻¹ = γ₀ * w ^ (orderOf w / 2) := by
      calc τ * (γ₀ * w ^ (orderOf w / 2)) * τ⁻¹ =
          (τ * γ₀ * τ⁻¹) * (τ * w ^ (orderOf w / 2) * τ⁻¹) := by group
        _ = γ₀ * z * (w ^ (orderOf w / 2) * z) := by rw [hτγ₀, hτu]
        _ = γ₀ * w ^ (orderOf w / 2) * (z * z) := by
            rw [mul_assoc γ₀, ← mul_assoc z, hzu]; group
        _ = γ₀ * w ^ (orderOf w / 2) := by rw [hzz, mul_one]
    have hdesc : ∀ x ∈ (zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2))) ⊓
        centralizer ({τ} : Set X), ∃ a : X, (a = 1 ∨ a = t) ∧
          (x = a ∨ x = a * z ∨ x = a * (γ₀ * w ^ (orderOf w / 2)) ∨
            x = a * (γ₀ * w ^ (orderOf w / 2)) * z) := by
      rintro x ⟨hxT1, hxC⟩
      obtain ⟨a, b, d, hd, ha, hb, rfl⟩ := hσ.mem_T1' hxT1
      have hxτ := (hTt _).mpr (mem_centralizer_singleton_iff.mp hxC)
      rw [hcen a b d hd ha hb] at hxτ
      refine ⟨a, ha, ?_⟩
      rcases hb with hb | hb <;> rw [hb] at hxτ ⊢
      ·
        have hdτ : τ * d * τ⁻¹ = d := by
          have := hxτ
          simp only [mul_one, mul_inv_cancel] at this
          exact mul_left_cancel this
        rcases hfix d hd hdτ with h1 | h1 <;> rw [h1]
        · left
          group
        · right
          left
          group
      ·
        rw [hτu] at hxτ
        have hdτ : d⁻¹ * (τ * d * τ⁻¹) = z := by
          have h1 : (τ * d * τ⁻¹) * z = d := by
            have h2 : a * ((τ * d * τ⁻¹) * z) * w ^ (orderOf w / 2) =
                a * d * w ^ (orderOf w / 2) := by
              rw [← hxτ]
              calc a * ((τ * d * τ⁻¹) * z) * w ^ (orderOf w / 2) =
                  a * (τ * d * τ⁻¹) * (z * w ^ (orderOf w / 2)) := by group
                _ = a * (τ * d * τ⁻¹) * (w ^ (orderOf w / 2) * z) := by rw [hzu]
            exact mul_left_cancel (mul_right_cancel h2)
          calc d⁻¹ * (τ * d * τ⁻¹) = d⁻¹ * ((τ * d * τ⁻¹) * z) * z⁻¹ := by group
            _ = z := by rw [h1, hzinv]; group
        rcases (htw d hd).mp hdτ with h1 | h1 <;> rw [h1]
        · right
          right
          left
          group
        · right
          right
          right
          rw [hγ₀inv]
          calc a * (γ₀ * z) * w ^ (orderOf w / 2) = a * (γ₀ * (z * w ^ (orderOf w / 2))) := by
                group
            _ = a * (γ₀ * w ^ (orderOf w / 2)) * z := by rw [hzu]; group
    constructor
    · right
      refine ⟨γ₀ * w ^ (orderOf w / 2), hγT1, hγ2, le_antisymm (fun x hx => ?_) ?_⟩
      · obtain ⟨a, ha, hx'⟩ := hdesc x hx
        have hazX : ∀ a : X, (a = 1 ∨ a = t) → a ∈ zpowers t := by
          intro a ha
          rcases ha with ha | ha <;> rw [ha]
          · exact one_mem _
          · exact mem_zpowers t
        have hγz : z = (γ₀ * w ^ (orderOf w / 2)) ^ 2 := hγ2.symm
        rcases hx' with hx' | hx' | hx' | hx' <;> rw [hx']
        · exact mem_sup_left (hazX a ha)
        · rw [hγz]
          exact mul_mem (mem_sup_left (hazX a ha)) (mem_sup_right (pow_mem (mem_zpowers _) 2))
        · exact mul_mem (mem_sup_left (hazX a ha)) (mem_sup_right (mem_zpowers _))
        · rw [hγz]
          exact mul_mem (mul_mem (mem_sup_left (hazX a ha)) (mem_sup_right (mem_zpowers _)))
            (mem_sup_right (pow_mem (mem_zpowers _) 2))
      · refine sup_le (zpowers_le.mpr ⟨htT1, mem_centralizer_singleton_iff.mpr htτ⟩)
          (zpowers_le.mpr ⟨hγT1, mem_centralizer_singleton_iff.mpr ?_⟩)
        exact ((hTt _).mp hγτ)
    ·
      intro x hx hx2
      obtain ⟨a, ha, hx'⟩ := hdesc x hx
      have ha2 : a ^ 2 = 1 := by
        rcases ha with ha | ha <;> rw [ha]
        · rw [one_pow]
        · rw [← h.config.orderOf_eq, pow_orderOf_eq_one]
      have haγ : Commute a (γ₀ * w ^ (orderOf w / 2)) := by
        rcases ha with ha | ha <;> rw [ha]
        · exact Commute.one_left _
        · exact (show Commute t γ₀ from hγ₀t.symm).mul_right htu
      have haz : Commute a z := by
        rcases ha with ha | ha <;> rw [ha]
        · exact Commute.one_left _
        · exact hzt.symm
      have hγz' : Commute (γ₀ * w ^ (orderOf w / 2)) z :=
        (show Commute γ₀ z from hγ₀z).mul_left (show Commute (w ^ (orderOf w / 2)) z from hzu.symm)
      rcases hx' with hx' | hx' | hx' | hx' <;> rw [hx'] at hx2 ⊢
      · simpa using hadX a 1 ha (Or.inl rfl)
      · exact hadX a z ha (Or.inr rfl)
      · exfalso
        rw [haγ.mul_pow 2, ha2, hγ2, one_mul] at hx2
        exact hσ.z_ne_one hx2
      · exfalso
        rw [(haz.mul_left hγz').mul_pow 2, haγ.mul_pow 2, ha2, hγ2, hz2, one_mul, mul_one] at hx2
        exact hσ.z_ne_one hx2
  ·
    have hdesc : ∀ x ∈ (zpowers t ⊔ (S ⊓ L) ⊔ zpowers (w ^ (orderOf w / 2))) ⊓
        centralizer ({τ} : Set X), x ∈ closure ({t, z} : Set X) := by
      rintro x ⟨hxT1, hxC⟩
      obtain ⟨a, b, d, hd, ha, hb, rfl⟩ := hσ.mem_T1' hxT1
      have hxτ := (hTt _).mpr (mem_centralizer_singleton_iff.mp hxC)
      rw [hcen a b d hd ha hb] at hxτ
      rcases hb with hb | hb <;> rw [hb] at hxτ ⊢
      · have hdτ : τ * d * τ⁻¹ = d := by
          have := hxτ
          simp only [mul_one, mul_inv_cancel] at this
          exact mul_left_cancel this
        rw [mul_one]
        rcases hfix d hd hdτ with h1 | h1
        · exact hadX a d ha (Or.inl h1)
        · exact hadX a d ha (Or.inr h1)
      · exfalso
        rw [hτu] at hxτ
        have h1 : (τ * d * τ⁻¹) * (t * z) = d := by
          have h2 : a * ((τ * d * τ⁻¹) * (t * z)) * w ^ (orderOf w / 2) =
              a * d * w ^ (orderOf w / 2) := by
            rw [← hxτ]
            have hdt := hDt _ (hτD d hd)
            calc a * ((τ * d * τ⁻¹) * (t * z)) * w ^ (orderOf w / 2) =
                a * (τ * d * τ⁻¹) * (t * (z * w ^ (orderOf w / 2))) := by group
              _ = a * (τ * d * τ⁻¹) * (t * w ^ (orderOf w / 2) * z) := by rw [hzu]; group
          exact mul_left_cancel (mul_right_cancel h2)
        have htD : t ∈ S ⊓ L := by
          have : t = (τ * d * τ⁻¹)⁻¹ * d * z⁻¹ := by
            calc t = (τ * d * τ⁻¹)⁻¹ * ((τ * d * τ⁻¹) * (t * z)) * z⁻¹ := by group
              _ = (τ * d * τ⁻¹)⁻¹ * d * z⁻¹ := by rw [h1]
          rw [this]
          exact mul_mem (mul_mem (inv_mem (hτD d hd)) hd) (inv_mem hσ.z_mem)
        exact h.t_ne_one (h.eq_one_of_mem_zpowers_of_mem (mem_zpowers t) htD.2)
    constructor
    · left
      refine le_antisymm (fun x hx => hdesc x hx) ?_
      rw [closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx <;> rw [hx]
      · exact ⟨htT1, mem_centralizer_singleton_iff.mpr htτ⟩
      · exact ⟨hzT1, mem_centralizer_singleton_iff.mpr hτz.symm⟩
    · exact fun x hx _ => hdesc x hx

end Setup42

end Standing

end CFSG.ComponentClassification.HarrisLit
